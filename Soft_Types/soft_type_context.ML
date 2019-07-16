(*  Title:  soft_type_context.ML
    Author: Alexander Krauss, Joshua Chen
    Date:   Jul 2019

Context information regarding soft types.

Maintains generic data for soft types of terms.

Allows the declaration of soft types for symbols, which are then available for type checking.
Symbols are either free variables (declared in the context) or constants.

*)


structure Soft_Type_Context :
sig

val normalize: Proof.context -> thm -> thm list

val get_current_type: Proof.context -> term -> thm option
val put_current_type: term -> thm -> Context.generic -> Context.generic

val get_adjs: Proof.context -> term list -> thm list
val get_all_adjs: Proof.context -> thm list
val put_adj: term -> thm -> Context.generic -> Context.generic

val get_types: Proof.context -> term list -> thm list
val get_all_types: Proof.context -> thm list
val put_type: term -> thm -> Context.generic -> Context.generic

val declare_current_type: int option -> thm -> Context.generic -> Context.generic

end = struct

(*** Preamble ***)

(*
  Normalize typing premises into atomic typings/adjectives, then split into multiple theorems whose conclusions are the atomic components of the original conclusion.
*)
fun normalize ctxt thm =
  let
    fun dest_concl_conjs thm =
      (case Soft_Type.dest_Trueprop (Thm.concl_of thm) of
        Const (@{const_name conj}, _) $ _ $ _ =>
          dest_concl_conjs (thm RS @{thm conjunct1}) @
          dest_concl_conjs (thm RS @{thm conjunct2})
      | _ => [thm])
      handle TERM _ => [thm]

    val simpctxt = (put_simpset HOL_ss ctxt) addsimps
      @{thms Int_type_iff adjective_iff atomize_conjL}
  in
    thm
    |> Simplifier.full_simplify simpctxt
    |> Object_Logic.rulify ctxt
    |> dest_concl_conjs
  end


(*** Data slots ***)
(*
  For any given term, we hold three separate collections of typing statements:
  1. Its currently-used soft type.
  3. The collection of all its adjectives.
  2. The collection of all its non-adjective types.
*)

(** Current soft type data **)
(*
  We store the types of constant and non-constant terms in a separate tables.
*)

(** Current type data **)

structure Current_Type = Generic_Data(
  type T = thm Termtab.table * thm Symtab.table
  val empty = (Termtab.empty, Symtab.empty)
  val extend = I
  fun merge ((a1, b1), (a2, b2)) =
    (Termtab.merge Thm.eq_thm_prop (a1, a2),
     Symtab.merge Thm.eq_thm_prop (b1, b2))
)

fun get_current_type ctxt t =
  let
    fun get tabs (Const (n, _)) = Symtab.lookup (snd tabs) n
      | get tabs t = Termtab.lookup (fst tabs) t
  in
    get (Current_Type.get (Context.Proof ctxt)) t
  end

fun put_current_type t thm =
  let
    val _ =
      if Soft_Type.is_typing (Thm.prop_of thm) then () else error "put_current_type: Not a typing judgment"
    fun put (Const (n, _)) thm = apsnd (Symtab.update (n, thm))
      | put t thm = apfst (Termtab.update (t, thm))
  in
    Current_Type.map (put t thm)
  end

(** Complete type and adjective data **)

structure Adjectives = Generic_Data(
  type T = thm list Termtab.table * thm list Symtab.table
  val empty = (Termtab.empty, Symtab.empty)
  val extend = I
  fun merge ((a1, b1), (a2, b2)) =
    (Termtab.merge (eq_set Thm.eq_thm_prop) (a1, a2),
     Symtab.merge (eq_set Thm.eq_thm_prop) (b1, b2))
)

structure Types = Generic_Data(
  type T = thm list Termtab.table * thm list Symtab.table
  val empty = (Termtab.empty, Symtab.empty)
  val extend = I
  fun merge ((a1, b1), (a2, b2)) =
    (Termtab.merge (eq_set Thm.eq_thm_prop) (a1, a2),
     Symtab.merge (eq_set Thm.eq_thm_prop) (b1, b2))
)

fun get_adjs ctxt ts =
  let
    fun get_adjs' tabs (Const (n, _)) = Symtab.lookup_list (snd tabs) n
      | get_adjs' tabs t = Termtab.lookup_list (fst tabs) t
  in fold (curry (op @)) (map (get_adjs' (Adjectives.get (Context.Proof ctxt))) ts) [] end

fun get_all_adjs ctxt =
  let
    val context = Context.Proof ctxt
    val termadjs = #1 (Adjectives.get context)
    val constadjs = #2 (Adjectives.get context)
    val (termkeys, constkeys) = (Termtab.keys termadjs, Symtab.keys constadjs)
  in
    (fold (curry (op @)) (map (Termtab.lookup_list termadjs) termkeys) []) @
    (fold (curry (op @)) (map (Symtab.lookup_list constadjs) constkeys) [])
  end

fun put_adj t thm context =
  let
    fun put t thm =
      let
        val _ =
          if Soft_Type.is_adj (Thm.prop_of thm)
          then ()
          else error "put_adj: Not an adjective judgment"

        val adjs = get_adjs (Context.proof_of context) [t]
      in case t of
          (Const (n, _)) => apsnd (Symtab.update (n, insert Thm.eq_thm_prop thm adjs))
        | _ => apfst (Termtab.update (t, insert Thm.eq_thm_prop thm adjs))
      end
  in
    Adjectives.map (put t thm) context
  end

fun get_types ctxt ts =
  let
    fun get_types' tabs (Const (n, _)) = Symtab.lookup_list (snd tabs) n
      | get_types' tabs t = Termtab.lookup_list (fst tabs) t
  in fold (curry (op @)) (map (get_types' (Types.get (Context.Proof ctxt))) ts) [] end

fun get_all_types ctxt =
  let
    val context = Context.Proof ctxt
    val termtypes = #1 (Types.get context)
    val consttypes = #2 (Types.get context)
    val (termkeys, constkeys) = (Termtab.keys termtypes, Symtab.keys consttypes)
  in
    (fold (curry (op @)) (map (Termtab.lookup_list termtypes) termkeys) []) @
    (fold (curry (op @)) (map (Symtab.lookup_list consttypes) constkeys) [])
  end

fun put_type t thm context =
  let
    val _ =
      if Soft_Type.is_typing (Thm.prop_of thm)
      then ()
      else error "put_type: Not a typing judgment"

    fun put_atomic_type t thm context =
      let
        fun put t thm =
          let val types = get_types (Context.proof_of context) [t]
          in case t of
              (Const (n, _)) => apsnd (Symtab.update (n, insert Thm.eq_thm_prop thm types))
            | t => apfst (Termtab.update (t, insert Thm.eq_thm_prop thm types))
          end
      in
        Types.map (put t thm) context
      end

    fun put_type' t thm context =
      if Soft_Type.is_adj (Thm.prop_of thm) then put_adj t thm context
      else if Soft_Type.is_typing (Thm.prop_of thm) then put_atomic_type t thm context
      else (error "put_type: normalized conjunct not an adjective or typing judgment"; context)
  in
    fold (put_type' t) (normalize (Context.proof_of context) thm) context
  end


(*** The [type] attribute ***)
(*
  May optionally declare some number of implicit arguments for constant terms via
  `[type implicit: n]`.
*)

fun extract_param_names 0 _ = []
  | extract_param_names i (Const (\<^const_name>\<open>Pi_type\<close>, _) $ _ $ Abs (n, _, b)) =
      n :: extract_param_names (i - 1) b
  | extract_param_names i _ = replicate i ""

fun declare_current_type implicit thm context =
  let
    val (x, st) = Soft_Type.dest_typing (Thm.prop_of thm)
    val names = extract_param_names (the_default 0 implicit) st
  in
    context
    |> put_current_type x thm
    |> put_type x thm
    |> (if is_Const x then Implicit_Arguments.put_implicit (fst (dest_Const x)) names else I)
  end

val _ = Theory.setup (Attrib.setup \<^binding>\<open>type\<close>
  (Scan.lift
    (Scan.option (Args.$$$ "implicit" |-- Args.colon |-- Parse.int) >> (fn implicit =>
      Thm.declaration_attribute (declare_current_type implicit)))) "Declare current soft type")


end
