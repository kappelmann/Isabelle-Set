\<^marker>\<open>creator "Bohua Zhan"\<close>
\<^marker>\<open>contributor "Kevin Kappelmann"\<close>
theory Auto2_HOTG              
  imports Auto2_HOTG_Setup    
  keywords "@proof" :: prf_block % "proof"
    and "@have" "@case" "@obtain" "@let" "@contradiction" "@strong_induct" :: prf_decl % "proof"
    and "@unfold" :: prf_decl % "proof"                        
    and "@induct" "@fun_induct" "@case_induct" "@prop_induct" "@cases" :: prf_decl % "proof"
    and "@apply_induct_hyp" :: prf_decl % "proof"
    and "@subgoal" "@endgoal" "@end" :: prf_decl % "proof"
    and "@qed" :: qed_block % "proof"
    and "@with" "where" "arbitrary" "@rule" :: quasi_command
begin

ML_file "../auto2/util.ML"
ML_file "../auto2/util_base.ML"
ML_file "auto2_hotg.ML"              
ML_file "../auto2/util_logic.ML"
ML_file "../auto2/box_id.ML"
ML_file "../auto2/consts.ML"
ML_file "../auto2/property.ML"
ML_file "../auto2/wellform.ML"
ML_file "../auto2/wfterm.ML"
ML_file "../auto2/rewrite.ML"
ML_file "../auto2/propertydata.ML"
ML_file "../auto2/matcher.ML"
ML_file "../auto2/items.ML"
ML_file "../auto2/wfdata.ML"
ML_file "../auto2/auto2_data.ML"
ML_file "../auto2/status.ML"
ML_file "../auto2/normalize.ML"
ML_file "../auto2/proofsteps.ML"
ML_file "../auto2/auto2_state.ML"
ML_file "../auto2/logic_steps.ML"
ML_file "../auto2/auto2.ML"
ML_file "../auto2/auto2_outer.ML"

ML_file "../auto2/HOL/acdata.ML"
ML_file "../auto2/HOL/ac_steps.ML"
ML_file "../auto2/HOL/unfolding.ML"
ML_file "../auto2/HOL/induct_outer.ML"
ML_file "../auto2/HOL/extra_hol.ML"     

method_setup auto2 = \<open>Scan.succeed (SIMPLE_METHOD o Auto2.auto2_tac)\<close> "auto2 prover"

attribute_setup forward = \<open>setup_attrib add_forward_prfstep\<close>
attribute_setup backward = \<open>setup_attrib add_backward_prfstep\<close>
attribute_setup backward1 = \<open>setup_attrib add_backward1_prfstep\<close>
attribute_setup backward2 = \<open>setup_attrib add_backward2_prfstep\<close>
attribute_setup resolve = \<open>setup_attrib add_resolve_prfstep\<close>
attribute_setup rewrite = \<open>setup_attrib add_rewrite_rule\<close>
attribute_setup rewrite_back = \<open>setup_attrib add_rewrite_rule_back\<close>
attribute_setup rewrite_bidir = \<open>setup_attrib add_rewrite_rule_bidir\<close>
attribute_setup forward_arg1 = \<open>setup_attrib add_forward_arg1_prfstep\<close>
attribute_setup forward_arg = \<open>setup_attrib add_forward_arg_prfstep\<close>
attribute_setup rewrite_arg = \<open>setup_attrib add_rewrite_arg_rule\<close>

end
