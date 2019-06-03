(*  Title:      soft_type.ML
    Author:     Alexander Krauss

Basic syntactic operations on soft types.

Soft types can be represented as Pure terms, but these terms have no logical significance.
They merely allow us to use Isabelle's syntax machinery.

A typing judgement can be converted into a proposition in Pure, which then expresses its actual
semantics.
*)

signature SOFT_TYPE =
sig

val typeT: typ -> typ

(* Constants for the term representation *)
val Pi_const: typ -> typ -> term
val any: typ -> term

val mk_any_fun: typ -> term

datatype judgement =
  Judgement of term * term

(* Convert from representation *)
val read_judgement: Proof.context -> term -> judgement
val mk_judgement: judgement -> term
val is_judgement: term -> bool

val trace_soft_types: bool Config.T
val tracing: Proof.context -> string -> unit 

end


structure Soft_Type : SOFT_TYPE =
struct

fun typeT T =
  Type (@{type_name "type"}, [T])

fun Pi_const Ta Tb = 
  Const (
    @{const_name "Pi_type"},
    typeT Ta --> (Ta --> typeT Tb) --> typeT (Ta --> Tb)
  )

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


datatype judgement =
  Judgement of term * term

fun read_judgement ctxt tm =
  case tm of 
    Const (@{const_name "has_type"}, _) $ t $ ty => Judgement (t, ty)
  | _ => error ("Invalid judgement: " ^ Syntax.string_of_term ctxt tm)

fun mk_judgement (Judgement (t, ty)) =
  let val T = fastype_of t 
  in
    Const (@{const_name "has_type"}, T --> typeT T --> @{typ prop}) $ t $ ty
  end

fun is_judgement tm = 
  case tm of 
    Const (@{const_name "has_type"}, _) $ _ $ _ => true
  | _ => false


(* tracing, controlled by a flag *)

val trace_soft_types = Attrib.setup_config_bool \<^binding>\<open>trace_soft_types\<close> (K false)
fun tracing ctxt = if Config.get ctxt trace_soft_types then Output.tracing else K ()

end
