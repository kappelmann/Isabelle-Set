(*  Title:      soft_type_context.ML
    Author:     Alexander Krauss, Joshua Chen
    Date:       Jul 2019

Context information for soft types.
Maintains generic data for soft types of terms.

Allows the declaration of soft types for symbols, which are then available for
type-checking. Symbols are either free variables (declared in the context) or
constants.

*)


structure Soft_Type_Context :
sig

val normalize: Proof.context -> thm -> thm list

val get_current_type: Proof.context -> term -> thm option
val put_current_type: term -> thm -> Context.generic -> Context.generic

val get_adjs: Proof.context -> term list -> thm list
val univ_adjs: Proof.context -> thm list
val put_adj: term -> thm -> Context.generic -> Context.generic
val all_adjectives: Proof.context -> thm list

val get_types: Proof.context -> term list -> thm list
val univ_types: Proof.context -> thm list
val put_type: term -> thm -> Context.generic -> Context.generic
val all_types: Proof.context -> thm list

end = struct

(*
  Normalize typing premises into atomic typings/adjectives, then split into
  multiple theorems whose conclusions are the atomic components of the original
  conclusion.
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
      @{thms has_type_type has_type_adj atomize_conjL}
  in
    thm
    |> Simplifier.full_simplify simpctxt
    |> Object_Logic.rulify ctxt
    |> dest_concl_conjs
  end

(*
  For any given term, we hold three separate collections of type knowledge:
  1. Its currently-used soft type.
  3. The collection of all its adjectives.
  2. The collection of all its types.
*)

(*** Current soft type data ***)
(*We store the types of constant and non-constant terms in a separate tables.*)

structure Current_Type = Generic_Data(
  type T = thm Termtab.table * thm Symtab.table
  val empty = (Termtab.empty, Symtab.empty)
  val extend = I
  fun merge ((T1, S1), (T2, S2)) =
    (Termtab.join (K (fn (_, t) => t)) (T1, T2),
      Symtab.join (K (fn (_, t) => t)) (S1, S2))
    (* (Termtab.merge Thm.eq_thm_prop (T1, T2),
     Symtab.merge Thm.eq_thm_prop (S1, S2)) *)
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
      if Soft_Type.is_typing (Thm.prop_of thm) then ()
      else error "Not a typing judgment"
    fun put (Const (n, _)) thm = apsnd (Symtab.update (n, thm))
      | put t thm = apfst (Termtab.update (t, thm))
  in
    Current_Type.map (put t thm)
  end


(*** Complete type and adjective data ***)

structure Adjectives = Generic_Data (
  type T = (thm list Termtab.table * thm list Symtab.table) * thm list
  val empty = ((Termtab.empty, Symtab.empty), [])
  val extend = I
  fun merge (((T1, S1), ths1), ((T2, S2), ths2)) =
    let
      val merge_thm_lists = Library.merge Thm.eq_thm_prop
    in
      ((Termtab.join (K merge_thm_lists) (T1, T2),
       Symtab.join (K merge_thm_lists) (S1, S2)),
        merge_thm_lists (ths1, ths2))
    end
)

structure Types = Generic_Data (
  type T = (thm list Termtab.table * thm list Symtab.table) * thm list
  val empty = ((Termtab.empty, Symtab.empty), [])
  val extend = I
  fun merge (((T1, S1), ths1), ((T2, S2), ths2)) =
    let
      val merge_thm_lists = Library.merge Thm.eq_thm_prop
    in
      ((Termtab.join (K merge_thm_lists) (T1, T2),
       Symtab.join (K merge_thm_lists) (S1, S2)),
        merge_thm_lists (ths1, ths2))
    end
)

fun getter data ctxt ts =
  let
    fun getter' data (Const (n, _)) = Symtab.lookup_list (snd (fst data)) n
      | getter' data t = Termtab.lookup_list (fst (fst data)) t
  in fold (curry (op @)) (map (getter' (data (Context.Proof ctxt))) ts) [] end

val get_adjs = getter Adjectives.get
val get_types = getter Types.get

(*
  "univ"ersally-applicable adjective and type judgments, i.e. those of the form
  "?x : T" or "P ?x", have their own container in the context data.
*)
fun univ_adjs ctxt = snd (Adjectives.get (Context.Proof ctxt))
fun univ_types ctxt = snd (Types.get (Context.Proof ctxt))

fun all_getter data ctxt =
  data (Context.Proof ctxt)
  |> (fn ((t1, t2), ths) =>
    map snd (Termtab.dest_list t1) @ map snd (Symtab.dest_list t2) @ ths)

val all_adjectives = all_getter Adjectives.get
val all_types = all_getter Types.get

fun put_adj t thm context =
  let
    fun put t thm =
      let
        val _ =
          if Soft_Type.is_adj (Thm.prop_of thm) then ()
          else error "Not an adjective judgment"
        val adjs = get_adjs (Context.proof_of context) [t]
      in case t of
          (Const (n, _)) =>
            apfst (apsnd (Symtab.update (n, insert Thm.eq_thm_prop thm adjs)))
        | Var _ => apsnd (insert Thm.eq_thm_prop thm)
        | _ => apfst (apfst (Termtab.update (t, insert Thm.eq_thm_prop thm adjs)))
      end
  in
    Adjectives.map (put t thm) context
  end

fun put_type t thm context =
  let
    val _ =
      if Soft_Type.is_typing (Thm.prop_of thm) then ()
      else error "Not a typing judgment"

    fun put_atomic_type t thm context =
      let
        fun put t thm =
          let val types = get_types (Context.proof_of context) [t]
          in case t of
              Const (n, _) =>
                apfst (apsnd (Symtab.update (n, insert Thm.eq_thm_prop thm types)))
            | Var _ => apsnd (insert Thm.eq_thm_prop thm)
            | _ => apfst (apfst (Termtab.update (t, insert Thm.eq_thm_prop thm types)))
          end
      in
        Types.map (put t thm) context
      end

    fun put_type' t thm context =
      if Soft_Type.is_adj (Thm.prop_of thm) then put_adj t thm context
      else if Soft_Type.is_typing (Thm.prop_of thm) then put_atomic_type t thm context
      else raise THM ("Normalization error", 0, [thm]);
  in
    fold (put_type' t) (normalize (Context.proof_of context) thm) context
  end


(* Diagnostic command to show the currently known types *)

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>print_types\<close>
    "print theorems of local theory or proof context"
    (Scan.succeed (Toplevel.keep (fn st =>
      let
        val ctxt = Toplevel.context_of st
      in
        (all_types ctxt @ all_adjectives ctxt)
        |> map (Thm.pretty_thm ctxt #> single #> Pretty.item)
        |> Pretty.chunks
        |> Pretty.writeln
      end)))

end
