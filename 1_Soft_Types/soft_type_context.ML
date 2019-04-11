(*  Title:      soft_type_context.ML
    Author:     Alexander Krauss

Context information regarding soft types.

Allows the declaration of soft types for symbols, which are then available for type checking.
Symbols are either free variables (declared in the context) or constants.
*)

structure Soft_Type_Context =
struct

(* Context data. Maps terms to soft types. *)
structure Ctxt = Generic_Data(
  type T = thm Termtab.table
  val empty = Termtab.empty
  val extend = I
  val merge = Termtab.merge Thm.eq_thm_prop
)

(* Canonical get and put operations *)
fun put t sty = Ctxt.map (Termtab.update (t, sty))
fun get ctxt t = Termtab.lookup (Ctxt.get ctxt) t

(* Break a typing judgment into its term and type parts *)
fun dest_typing tm =
  case tm of
    Const (@{const_name has_type}, _) $ t $ T => (t, T)
  | _ => Exn.error "dest_typing: not a typing judgment"

fun add_typing thm ctxt =
  let
    val (x, _) = dest_typing (Thm.prop_of thm)
  in 
    put x thm ctxt
  end

val _ = Theory.setup (Attrib.setup @{binding type}
  (Scan.succeed (Thm.declaration_attribute add_typing)) "define a soft type")


end
