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

(*
Canonical get and put operations for the current type
*)
fun put_current_type t sty = Current_Type.map (put_CT t sty);
fun get_current_type ctxt t = get_CT (Current_Type.get ctxt) t;

fun declare_current_type thm ctxt =
  let val (x, _) = dest_typing (Thm.prop_of thm)
  in put_current_type x thm ctxt
  end;

val _ = Theory.setup (Attrib.setup @{binding type}
  (Scan.succeed (Thm.declaration_attribute declare_current_type)) "Declare current soft type")


(** Slot for all known types of a term **)

structure Known_Types = Generic_Data(
  type T = thm Item_Net.T * thm Item_Net.T
  val empty = (
    Item_Net.init Thm.eq_thm_prop (single o (#1 o dest_typing) o Thm.prop_of),
    Item_Net.init Thm.eq_thm_prop (single o (#1 o dest_typing) o Thm.prop_of)
  )
  val extend = I
  val merge = apply2 Item_Net.merge
)


end
