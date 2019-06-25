(*  Title:      soft_type.ML
    Author:     Alexander Krauss

Basic syntactic operations on soft types.
*)

signature SOFT_TYPE =
sig

(* Type of soft types *)
val typeT: typ -> typ

(* Function types *)
val Pi_const: typ -> typ -> term

(* Typing judgments *)
val mk_typing: term * term -> term
val dest_typing: term -> term * term
val is_typing: term -> bool

(* Unrestricted type *)
val any: typ -> term
val mk_any_fun: typ -> term

(* Type annotations *)
val annotate: term -> term -> term
(*val get_annotations: term -> (term * term) list
val strip_annotations: term -> term*)

(* Tracing *)
val trace_soft_types: bool Config.T
val tracing: Proof.context -> string -> unit 

end


structure Soft_Type : SOFT_TYPE =
struct

fun typeT T = Type (@{type_name "type"}, [T])

fun Pi_const Ta Tb = 
  Const (
    @{const_name "Pi_type"},
    typeT Ta --> (Ta --> typeT Tb) --> typeT (Ta --> Tb)
  )


fun dest_typing t = case t of
    Const (@{const_name "has_type"}, _) $ u $ ty => (u, ty)
  | Const ("HOL.Trueprop", _) $ (Const (@{const_name has_type}, _) $ u $ ty) => (u, ty) 
  | _ => raise TERM ("dest_typing", [t])

fun mk_typing (t, ty) =
  let val T = fastype_of t in
    Const (@{const_name "has_type"}, T --> typeT T --> @{typ bool}) $ t $ ty
  end

fun is_typing (Const (@{const_name "has_type"}, _) $ _ $ _) = true
  | is_typing _ = false


fun any T = Const (@{const_name "any"}, typeT T)

fun mk_any_fun T =
  let
    val (binderTs, bodyT) = strip_type T
    val names = Name.invent_list [] "a" (length binderTs)
  in
    (any bodyT, bodyT)
    |> fold_rev (fn (n, S) => fn (t, T) => 
      (Pi_const S T $ Var ((n, 0), typeT S) $ Abs ("uu_", S, t), S --> T)) (names ~~ binderTs)
    |> fst
  end


fun with_type_const T = Const (\<^const_name>\<open>with_type\<close>, T --> typeT T --> T)

fun annotate soft_type t = with_type_const (fastype_of t) $ t $ soft_type


(* tracing, controlled by a flag *)

val trace_soft_types = Attrib.setup_config_bool \<^binding>\<open>trace_soft_types\<close> (K false)
fun tracing ctxt = if Config.get ctxt trace_soft_types then Output.tracing else K ()

end
