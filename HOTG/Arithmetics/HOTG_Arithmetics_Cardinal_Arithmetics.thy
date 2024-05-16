\<^marker>\<open>creator "Linghan Fang"\<close>
\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Compatibility of Set Arithmetics and Cardinal Arithmetics\<close>
theory HOTG_Arithmetics_Cardinal_Arithmetics
  imports
    HOTG_Cardinals_Addition
    HOTG_Addition
begin

unbundle no_HOL_groups_syntax

lemma cardinality_lift_eq_cardinality_right [simp]: "|lift X Y| = |Y|"
proof (intro cardinality_eq_if_equipollent equipollentI)
  let ?f = "\<lambda>z. (THE y : Y. z = X + y)"
  let ?g = "((+) X)"
  from injective_on_if_inverse_on show "bijection_on (lift X Y) Y ?f ?g"
    by (urule bijection_onI dep_mono_wrt_predI where chained = insert)+
    (auto intro: pred_btheI[of "\<lambda>x. x \<in> Y"] simp: lift_eq_repl_add mem_of_eq)
qed

text\<open>The next theorem shows that set addition is compatible with cardinality addition.\<close>

theorem cardinality_add_eq_cardinal_add_cardinality: "|X + Y| = |X| \<oplus> |Y|"
  using disjoint_lift_self_right by (auto simp add:
  cardinality_bin_union_eq_cardinal_add_cardinality_if_disjoint add_eq_bin_union_lift)

text\<open>A similar theorem shows that set multiplication is compatible with cardinality multiplication,
but it is not proven here. See
\<^url>\<open>https://foss.heptapod.net/isa-afp/afp-devel/-/blob/06458dfa40c7b4aaaeb855a37ae77993cb4c8c18/thys/ZFC_in_HOL/Kirby.thy#L1431\<close>.\<close>

end

