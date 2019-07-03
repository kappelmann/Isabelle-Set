(*  Title:  soft_type_context.ML
    Author: Alexander Krauss, Joshua Chen

Context information regarding soft types.

Allows the declaration of soft types for symbols, which are then available for type checking.
Symbols are either free variables (declared in the context) or constants.

*)

structure Soft_Type_Context =
struct

(*** Data slots ***)
(*
For any given term, we hold two separate collections of typing statements:
1. Its currently-used soft type.
2. The collection of all known (previously proven) types.
*)

(** Slot for the current soft type of a term **)
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

fun put_current_type t sty = 
  let
    fun put (Const (n, _)) sty = apsnd (Symtab.update (n, sty))
      | put t sty = apfst (Termtab.update (t, sty))
  in
    Current_Type.map (put t sty)
  end

fun get_current_type ctxt t = 
  let
    fun get tabs (Const (n, _)) = Symtab.lookup (snd tabs) n
      | get tabs t = Termtab.lookup (fst tabs) t
  in
    get (Current_Type.get ctxt) t
  end


(** Slot for all known types of a term **)

structure Known_Types = Generic_Data(
  type T = thm Item_Net.T * thm Item_Net.T
  val empty = (
    Item_Net.init Thm.eq_thm_prop (single o (#1 o Soft_Type.dest_typing) o Thm.prop_of),
    Item_Net.init Thm.eq_thm_prop (single o (#1 o Soft_Type.dest_typing) o Thm.prop_of)
  )
  val extend = I
  val merge = apply2 Item_Net.merge
)



(** The [type] attribute **)
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
    val (x, st) = Soft_Type.dest_typing (Thm.prop_of thm)
    val names = extract_param_names (the_default 0 implicit) st
  in
    ctxt
    |> put_current_type x thm
    |> (if is_Const x then Implicit_Arguments.put_implicit (fst (dest_Const x)) names else I)
  end

val _ = Theory.setup (Attrib.setup @{binding type}
  (Scan.lift 
    (Scan.option (Args.$$$ "implicit" |-- Args.colon |-- Parse.int) >> (fn implicit =>
      Thm.declaration_attribute (declare_current_type implicit)))) "Declare current soft type")



end
