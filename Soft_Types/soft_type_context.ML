(*  Title:  soft_type_context.ML
    Author: Alexander Krauss, Joshua Chen

Context information regarding soft types.

Allows the declaration of soft types for symbols, which are then available for type checking.
Symbols are either free variables (declared in the context) or constants.

*)

structure Soft_Type_Context =
struct

(*** Utility functions ***)

(*
Breaks a typing judgment into its term and type parts.
Accepts both pure judgement form or embedded into HOL.Trueprop.
*)
fun dest_typing tm =
  case tm of
    Const (@{const_name has_type}, _) $ t $ T => (t, T)
  | Const ("HOL.Trueprop", _) $ (Const (@{const_name has_type}, _) $ t $ T) => (t, T)
  | _ => Exn.error ("dest_typing: not a typing judgment" ^ \<^make_string> tm)


(*** Data slots ***)
(*
For any given term, we hold two separate collections of typing statements:
1. Its currently-used soft type.
2. The collection of all known (previously proven) types .
*)

(** Slot for the current soft type of a term **)

structure Current_Type = Generic_Data(
  type T = thm Termtab.table * thm Symtab.table;
  val empty = (Termtab.empty, Symtab.empty);
  val extend = I;
  fun merge ((a1, b1), (a2, b2)) =
      (Termtab.merge Thm.eq_thm_prop (a1, a2), 
       Symtab.merge Thm.eq_thm_prop (b1, b2));
);

fun put_CT (Const (n, _)) sty = apsnd (Symtab.update (n, sty))
  | put_CT t sty = apfst (Termtab.update (t, sty))

fun get_CT tabs (Const (n, _)) = Symtab.lookup (snd tabs) n
  | get_CT tabs t = Termtab.lookup (fst tabs) t

fun put_current_type t sty = Current_Type.map (put_CT t sty);
fun get_current_type ctxt t = get_CT (Current_Type.get ctxt) t;



(** All known types of a term **)

structure Known_Types = Generic_Data(
  type T = thm Item_Net.T * thm Item_Net.T
  val empty = (
    Item_Net.init Thm.eq_thm_prop (single o (#1 o dest_typing) o Thm.prop_of),
    Item_Net.init Thm.eq_thm_prop (single o (#1 o dest_typing) o Thm.prop_of)
  )
  val extend = I
  val merge = apply2 Item_Net.merge
)

(** Implicit argument declarations for a constant **)

structure Implicit_Arguments = Generic_Data(
  type T = string list Symtab.table;
  val empty = Symtab.empty;
  val extend = I;
  fun merge (a, b) = Symtab.merge (op =) (a, b);
)

fun get_implicits ctxt n = Symtab.lookup (Implicit_Arguments.get ctxt) n |> the_default []
fun put_implicit n xs = Implicit_Arguments.map (Symtab.update (n, xs))



(** attribute [type] **)

fun extract_param_names 0 _ = []
  | extract_param_names i (Const (\<^const_name>\<open>Pi_type\<close>, _) $ _ $ Abs (n, _, b)) =
      n :: extract_param_names (i - 1) b
  | extract_param_names i _ = replicate i ""

fun declare_current_type implicit thm ctxt =
  let
    val (x, st) = dest_typing (Thm.prop_of thm)
    val _ = Output.tracing ("[type] " ^ \<^make_string> st)
    val names = extract_param_names (the_default 0 implicit) st
  in
    ctxt
    |> put_current_type x thm
    |> (if is_Const x then put_implicit (fst (dest_Const x)) names else I)
  end;

val _ = Theory.setup (Attrib.setup @{binding type}
  (Scan.lift 
    (Scan.option (Args.$$$ "implicit" |-- Args.colon |-- Parse.int) >> (fn implicit =>
      Thm.declaration_attribute (declare_current_type implicit)))) "Declare current soft type")



end
