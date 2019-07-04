(*  Title:  soft_type_context.ML
    Author: Alexander Krauss, Joshua Chen

Context information regarding soft types.

Maintains generic data for soft types of terms.

Allows the declaration of soft types for symbols, which are then available for type checking.
Symbols are either free variables (declared in the context) or constants.

*)

open Soft_Type

structure Soft_Type_Context =
struct

(*** Preamble ***)

(* Normalize a typing judgment into a conjunction
*)
fun normalize ctxt thm =
  let
    val simpctxt = (put_simpset HOL_ss ctxt) addsimps @{thms Int_type_iff adjective_iff}
  in
    thm
    |> Simplifier.full_simplify simpctxt
    |> Object_Logic.rulify ctxt
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
      if is_typing (Thm.prop_of thm) then () else error "put_current_type: Not a typing judgment"
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

fun get_adjs ctxt t =
  let
    fun get_adjs' tabs (Const (n, _)) = Symtab.lookup (snd tabs) n
      | get_adjs' tabs t = Termtab.lookup (fst tabs) t
  in get_adjs' (Adjectives.get (Context.Proof ctxt)) t end

fun put_adj t thm context =
  let
    fun put t thm =
      let
        val _ = if is_adj (Thm.prop_of thm) then () else error "put_adj: Not an adjective judgment"
        val adjs = the_default [] (get_adjs (Context.proof_of context) t)
      in case t of
          (Const (n, _)) => apsnd (Symtab.update (n, insert Thm.eq_thm_prop thm adjs))
        | _ => apfst (Termtab.update (t, insert Thm.eq_thm_prop thm adjs))
      end
  in
    Adjectives.map (put t thm) context
  end

fun get_types ctxt t =
  let
    fun get_types' tabs (Const (n, _)) = Symtab.lookup (snd tabs) n
      | get_types' tabs t = Termtab.lookup (fst tabs) t
  in get_types' (Types.get (Context.Proof ctxt)) t end

(* Types are stored in normalized form. This means that:
    1. Intersection types are broken up.
    2. Adjectives are stored in the separate adjective data slot. *)
fun put_type t thm context =
  let
    val _ = if is_typing (Thm.prop_of thm) then () else error "put_type: Not a typing judgment"

    fun put_pure_type t thm context =
      let
        fun put t thm =
          let val types = the_default [] (get_types (Context.proof_of context) t)
          in case t of
              (Const (n, _)) => apsnd (Symtab.update (n, insert Thm.eq_thm_prop thm types))
            | t => apfst (Termtab.update (t, insert Thm.eq_thm_prop thm types))
          end
      in
        Types.map (put t thm) context
      end

    (* Expects a conjunction of adjective and/or typing judgments:
    *)
    fun put_type' t thm context =
      case (dest_Trueprop o Thm.prop_of) thm of
        Const (\<^const_name>\<open>conj\<close>, _) $ _ $ _ =>
          let
            val conjunct1 = thm RS @{thm conjunct1}
            val conjunct2 = thm RS @{thm conjunct2}
          in
            context |> put_type' t conjunct1 |> put_type' t conjunct2
          end
      | u =>
          if is_adj u then put_adj t thm context
          else if is_typing u then put_pure_type t thm context
          else (error "put_type': normalized conjunct not an adjective or typing judgment"; context)
  in
    put_type' t (normalize (Context.proof_of context) thm) context
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

fun declare_current_type implicit thm ctxt =
  let
    val (x, st) = dest_typing (Thm.prop_of thm)
    val names = extract_param_names (the_default 0 implicit) st
  in
    ctxt
    |> put_current_type x thm
    |> put_type x thm
    |> (if is_Const x then Implicit_Arguments.put_implicit (fst (dest_Const x)) names else I)
  end

val _ = Theory.setup (Attrib.setup @{binding type}
  (Scan.lift
    (Scan.option (Args.$$$ "implicit" |-- Args.colon |-- Parse.int) >> (fn implicit =>
      Thm.declaration_attribute (declare_current_type implicit)))) "Declare current soft type")


end
