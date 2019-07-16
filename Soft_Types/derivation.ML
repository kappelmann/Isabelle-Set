(* Title:  derivation.ML
   Author: Joshua Chen
   Date:   Jul 2019

Management and automation of type derivation.

*)

structure Derivation =
struct

(*** Tracing ***)

val derive_debug = Attrib.setup_config_bool @{binding "derive_debug"} (K false)

fun warn ctxt msg = if Config.get ctxt derive_debug then warning msg else ()


(*** Context data for type derivation rules ***)
(*
  A type derivation rule is an implication whose premises and conclusion are typing or adjective
  judgments ("judgments").

  These are stored in normalized form: premises are broken up into atomic type/adjective judgments,
  and the conclusion is also split to yield multiple rules whose premises are the same and whose
  conclusions are the atomic components of the original.
*)

fun get_derivation_rules ctxt = Named_Theorems.get ctxt \<^named_theorems>\<open>derivation_rules\<close>

fun put_derivation_rule ctxt =
  (Soft_Type_Context.normalize ctxt) #>
  fold (Named_Theorems.add_thm \<^named_theorems>\<open>derivation_rules\<close>)


val derivation_rule_parser =
  Attrib.add_del
    (Thm.declaration_attribute (fn thm => fn context =>
      (put_derivation_rule (Context.proof_of context) thm context)))
    (Thm.declaration_attribute (fn _ =>
      (warning "Deletion of derivation rules not implemented"; I)))


(*** Type derivation ***)

(*
  Recursion depth limit for type derivation
*)
val derive_depth = Attrib.setup_config_int @{binding "derive_depth"} (K 10)

(*
  Derive all judgments for `tm` not already in `jdgmts` that are deducible from `rule` by
  instantiating the term in the conclusion of `rule` with `tm`, and discharging any premises using
  the theorems in `jdgmts`.
*)
fun term_jdgmts_from_rule ctxt tm jdgmts rule =
  let
    fun in_jdgmts thm =
      subset
        (Term.aconv)
        (map Thm.concl_of (Soft_Type_Context.normalize ctxt thm), map Thm.prop_of jdgmts)

    (*
      Recursively filter rules whose conclusions are already in `jdgmts`, and discharge the
      rightmost premise of those remaining. In each recursive call, the theorems in the argument
      `thms` have the same number of premises.
    *)
    fun rec_discharge_prems thms = case thms |> filter_out in_jdgmts of
        [] => []
      | thms as thm :: _ =>
          if Thm.no_prems thm then thms
          else rec_discharge_prems (jdgmts RLN (Thm.nprems_of thm, thms))
  in
    let
      val inst =
        (Thm.match o apply2 (Thm.cterm_of ctxt))
          ((Soft_Type.term_of_jdgmt o Thm.concl_of) rule, tm)
    in
      rec_discharge_prems [Thm.instantiate inst rule]
    end
    handle Pattern.MATCH =>
      (warn ctxt
        "term_typings_from_rule: could not match term in typing conclusion of the given rule";
      [])
  end

(*
  Derive judgments for a set of terms starting with the judgment data for those terms and using
  derivation rules available in the context.

  All derived judgments are atomic since the derivation rules are normalized.
  The returned results include judgments already in the context.
*)
fun derive_jdgmts ctxt tms =
  let
    val rules = get_derivation_rules ctxt

    fun rec_derive_jdgmts jdgmts iter =
      if iter > Config.get ctxt derive_depth
      then (warning "Type derivation depth limit reached; consider increasing derive_depth"; jdgmts)
      else
        let
          fun derive_new_jdgmts tm =
            map (term_jdgmts_from_rule ctxt tm jdgmts) rules |> flat |> distinct Thm.eq_thm_prop

          val new_jdgmts = flat (map derive_new_jdgmts tms)
        in
          if null new_jdgmts then jdgmts else rec_derive_jdgmts (jdgmts @ new_jdgmts) (iter+1)
        end
  in
    rec_derive_jdgmts (Soft_Type_Context.get_types ctxt tms @ Soft_Type_Context.get_adjs ctxt tms) 0
  end


end
