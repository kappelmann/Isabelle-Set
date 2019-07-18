(*  Title:      isar_integration.ML
    Author:     Alexander Krauss

Experimental integration of elaboration into the Isar infrastructure.
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

fun augment t ctxt =
  let
    val _ = Soft_Type.tracing ctxt ("Augment: " ^ Syntax.string_of_term ctxt t)
    val annotations = Soft_Type.extract_annotations t
    fun typing_assumption (x, A) =
      HOLogic.mk_Trueprop (Soft_Type.mk_typing (x, A))
      |> Thm.cterm_of ctxt
  in
    ctxt
    |> Assumption.add_assumes (map typing_assumption annotations)
    |-> fold declare_type
  end


val operations = {
  augment=augment,
  implicit_vars=K (K []),
  purge=K Soft_Type.strip_annotations
}

val setup = Soft_Type_System.setup operations


end
