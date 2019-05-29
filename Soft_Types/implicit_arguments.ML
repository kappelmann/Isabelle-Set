(*  Title:      implicit_arguments.ML
    Author:     Alexander Krauss

Implicit arguments represented in the pre-term structure.

An implicit argument is treated as a unification variable by the type inference algorithm.
But it must be handed correctly through layers that do not expect Vars in terms, so we must
encode them as constant expressions.
*)

signature IMPLICIT_ARGUMENTS =
sig

val mk_iarg : string -> typ -> term
val dest_iarg : term -> string * typ
val is_iarg : term -> bool

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



end
