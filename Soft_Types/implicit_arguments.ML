(*  Title:      implicit_arguments.ML
    Author:     Alexander Krauss

Implicit arguments represented in the pre-term structure.

An implicit argument is treated as a unification variable by the type inference algorithm.
But it must be handed correctly through layers that do not expect Vars in terms, so we
encode them as constant expressions "\<implicit>n".

Cf. Implicit_Arguments.thy.
*)

signature IMPLICIT_ARGUMENTS =
sig

val mk_iarg : string -> typ -> term
val dest_iarg : term -> string * typ
val is_iarg : term -> bool

val get_implicits : Context.generic -> string -> string list
val put_implicit : string -> string list -> Context.generic -> Context.generic


(* Inserts iarg symbols into a term. The given function maps constant names
  to lists of implicit argument names *)
val insert_iargs : (string -> string list) -> term -> term

(* Replaces the special iarg symbols with unification variables *)
val replace_iargs : term -> int -> term * int

end


structure Implicit_Arguments : IMPLICIT_ARGUMENTS =
struct

fun mk_iarg n T =
  Const (\<^const_name>\<open>implicit_arg\<close>, (propT --> propT) --> T) $ Abs (n, propT, \<^const>\<open>implicit_dummy\<close>)

fun dest_iarg (Const (\<^const_name>\<open>implicit_arg\<close>, T) $ Abs (n, _, _)) = (n, range_type T)
  | dest_iarg t = raise TERM ("dest_iarg", [t]) 

fun is_iarg (Const (\<^const_name>\<open>implicit_arg\<close>, _) $ Abs (_, _, _)) = true
  | is_iarg _ = false

fun insert_iargs f = 
  let
    fun insert (t as Const (n, _)) = list_comb (t, map (fn n => mk_iarg n dummyT) (f n))
      | insert t = t
  in
    Term.map_aterms insert
  end


(** Implicit argument declarations for a constant **)

structure Implicit_Arguments = Generic_Data(
  type T = string list Symtab.table;
  val empty = Symtab.empty;
  val extend = I;
  fun merge (a, b) = Symtab.merge (op =) (a, b);
)

fun get_implicits ctxt n = Symtab.lookup (Implicit_Arguments.get ctxt) n |> the_default []
fun put_implicit n xs = Implicit_Arguments.map (Symtab.update (n, xs))



(** Simplistic marking of terms, to ensure exactly-once operations  **)

fun do_mark m t = Const ("_mark_" ^ m, dummyT) $ t
fun is_marked m (Const (n, _) $ _) = (n = "_mark_" ^ m)
  | is_marked _ _ = false

fun mark m t = if is_marked m t then t else do_mark m t
fun unmark (Const _ $ t) = t
  | unmark t = raise TERM ("unmark", [t])



fun insert_implicit ctxt (ts : term list) =
  let
    val implicit_table = get_implicits (Context.Proof ctxt)

    fun insert_implicit_term t =
      if is_marked "implicits" t
      then insert_iargs implicit_table (unmark t)
      else t
  in
    map insert_implicit_term ts
  end;



fun replace_implicit Ts t i =
  if is_iarg t
  then let val (n, T) = dest_iarg t
    in (list_comb (Var ((n, i), Ts ---> T), map_range Bound (length Ts)), i + 1) end
  else case t of 
    (Abs (x, T, t)) =>
      let val (t', i') = replace_implicit (T :: Ts) t i
      in (Abs (x, T, t'), i') end
  | (t $ u) =>
      let
        val (t', i') = replace_implicit Ts t i;
        val (u', i'') = replace_implicit Ts u i';
      in (t' $ u', i'') end
  | a => (a, i)

val replace_iargs = replace_implicit [];


(** Term check phases **)

val _ = Context.>>
  (Syntax_Phases.term_check ~11 "implicit_args, mark" (K (map (mark "implicits")))
   #> Syntax_Phases.term_check ~10 "implicit_args, insert phase" insert_implicit
)


end
