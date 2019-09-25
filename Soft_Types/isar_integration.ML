(*  Title:      isar_integration.ML
    Author:     Alexander Krauss

Integration of elaboration into the Isar infrastructure.

Provides the operations "augment" and "purge" of the soft type system.
*)

signature ISAR_INTEGRATION =
sig

  val operations: Soft_Type_System.operations

  val setup: theory -> theory

end;

structure Isar_Integration : ISAR_INTEGRATION =
struct

fun declare_type thm ctxt =
  (Soft_Type.tracing ctxt ("Declaring Type: " ^ \<^make_string> thm);
   Context.proof_map (Derivation.declare_current_type NONE thm) ctxt)

(* Adds inferred types of variables to the context. *)
fun augment t ctxt =
  let
    val _ = Soft_Type.tracing ctxt ("Augment: " ^ Syntax.string_of_term ctxt t)
    val annotations = Soft_Type.extract_annotations t
    (* Ignore types of locally bound variables. These may occur when variables are bound implicitly,
    e.g., via "for" bindings. *)
    fun typing_assumption (x, A) =
      if Term.is_open x then NONE
      else SOME (Thm.cterm_of ctxt (HOLogic.mk_Trueprop (Soft_Type.mk_typing (x, A))))
  in
    ctxt
    |> Assumption.add_assumes (map_filter typing_assumption annotations)
    |-> fold declare_type
  end


val operations = {
  augment=augment,
  implicit_vars=K (K []),
  purge=K Soft_Type.strip_annotations
}

val setup = Soft_Type_System.setup operations


end
