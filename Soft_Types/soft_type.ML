(*  Title:      soft_type.ML
    Author:     Alexander Krauss

Basic syntactic operations on soft types.
*)

signature SOFT_TYPE =
sig

(* Utility *)
val dest_Trueprop: term -> term

(* Type of soft types *)
val typeT: typ -> typ

(* Function types *)
val is_Pi: term -> bool
val Pi_const: typ -> typ -> term
val dest_Pi_type: term -> string * term * term

(* Typing judgments *)
val is_typing: term -> bool
val is_adj: term -> bool
val is_jdgmt: term -> bool
val is_subtyping: term -> bool
val mk_typing: term * term -> term
val dest_typing: term -> term * term
val dest_adj: term -> term * term
val term_of_typing: term -> term
val type_of_typing: term -> term
val term_of_jdgmt: term -> term

(* Unrestricted type *)
val any: typ -> term
val mk_any_fun: typ -> term

(* Type annotations *)
val annotate: term -> term -> term
val extract_annotations: term -> (term * term) list
val strip_annotations: term -> term

(* Tracing *)
val trace_soft_types: bool Config.T
val tracing: Proof.context -> string -> unit

end


structure Soft_Type : SOFT_TYPE =
struct

fun dest_Trueprop (Const (\<^const_name>\<open>Trueprop\<close>, _) $ P) = P
  | dest_Trueprop t = t

fun typeT T = Type (\<^type_name>\<open>type\<close>, [T])

fun is_Pi st = case Term.head_of st of
    Const (\<^const_name>\<open>Pi_type\<close>, _) => true
  | _ => false

fun Pi_const Ta Tb = 
  Const (\<^const_name>\<open>Pi_type\<close>, typeT Ta --> (Ta --> typeT Tb) --> typeT (Ta --> Tb))

fun dest_Pi_type (Const (\<^const_name>\<open>Pi_type\<close>, _) $ A $ Abs (x, _, B)) = (x, A, B)
  | dest_Pi_type t = raise TERM ("dest_Pi_type", [t])

fun is_typing t = case Term.head_of (dest_Trueprop t) of
    Const (\<^const_name>\<open>has_type\<close>, _) => true
  | _ => false

fun is_adj t = case Term.head_of (dest_Trueprop t) of
    Const (\<^const_name>\<open>has_type\<close>, _) => false
  | Const (\<^const_name>\<open>HOL.eq\<close>, _) => false
  | Const (_, T as Type ("fun", _)) => (Term.body_type T = \<^typ>\<open>bool\<close>)
  | _ => false

fun is_jdgmt t = is_typing t orelse is_adj t

fun is_subtyping t = case Term.head_of (dest_Trueprop t) of
    Const (\<^const_name>\<open>subtype\<close>, _) => true
  | _ => false

fun mk_typing (t, ty) =
  let val T = fastype_of t in
    Const (\<^const_name>\<open>has_type\<close>, T --> typeT T --> \<^typ>\<open>bool\<close>) $ t $ ty
  end

fun dest_typing t = case dest_Trueprop t of
    Const (\<^const_name>\<open>has_type\<close>, _) $ u $ ty => (u, ty)
  | _ => raise TERM ("dest_typing", [t])

fun dest_adj t = let val (adj, u) = Term.dest_comb (dest_Trueprop t) in (u, adj) end

fun term_of_jdgmt tm =
  #1 (
    if is_typing tm then dest_typing tm
    else if is_adj tm then dest_adj tm
    else error "term_of_jdgmt: not a type or adjective judgment"
  )

val term_of_typing = #1 o dest_typing
val type_of_typing = #2 o dest_typing


fun any T = Const (\<^const_name>\<open>any\<close>, typeT T)

fun mk_any_fun T =
  let
    val (binderTs, bodyT) = strip_type T
    val names = Name.invent_list [] "a" (length binderTs)
  in
    (any bodyT, bodyT)
    |> fold_rev
        (fn (n, S) => fn (t, T) => 
          (Pi_const S T $ Var ((n, 0), typeT S) $ Abs ("uu_", S, t), S --> T))
        (names ~~ binderTs)
    |> fst
  end

fun with_type_const T = Const (\<^const_name>\<open>with_type\<close>, T --> typeT T --> T)

fun annotate soft_type t = with_type_const (fastype_of t) $ t $ soft_type

fun extract_annotations t = 
  let
    fun extract t = case t of
          Const (\<^const_name>\<open>with_type\<close>, _) $ u $ A => cons (u, A) o extract u
        | s $ u => extract s o extract u
        | Abs (_, _, b) => extract b
        | _ => I
  in
    extract t []
  end

fun strip_annotations t = case t of
    Const (\<^const_name>\<open>with_type\<close>, _) $ s $ _ => strip_annotations s
  | s $ t => strip_annotations s $ strip_annotations t
  | Abs (x, T, b) => Abs (x, T, strip_annotations b)
  | _ => t


(* tracing, controlled by a flag *)

val trace_soft_types = Attrib.setup_config_bool \<^binding>\<open>trace_soft_types\<close> (K false)
fun tracing ctxt = if Config.get ctxt trace_soft_types then Output.tracing else K ()


end
