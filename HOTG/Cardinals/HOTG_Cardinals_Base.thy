\<^marker>\<open>creator "Linghan Fang"\<close>
\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Cardinals\<close>
theory HOTG_Cardinals_Base
  imports
    Transport.Binary_Relations_Least
    HOTG_Equipollence
    HOTG_Ordinals_Base
begin

unbundle no_HOL_groups_syntax

paragraph \<open>Summary\<close>
text \<open>Translation of cardinality from HOL-Library and \<^cite>\<open>ZFC_in_HOL_AFP\<close>.

The cardinality of a set \<open>X\<close> is the smallest ordinal number \<open>\<alpha>\<close> such that there
exists a bijection between \<open>X\<close> and \<open>\<alpha>\<close>.
Further details can be found in \<^url>\<open>https://en.wikipedia.org/wiki/Cardinal_number\<close>.\<close>

definition "cardinality (X :: set) \<equiv> least_wrt_rel (\<subseteq>) (ordinal \<sqinter> ((\<approx>) X))"

bundle hotg_cardinality_syntax begin notation cardinality ("|_|") end
bundle no_hotg_cardinality_syntax begin no_notation cardinality ("|_|") end
unbundle hotg_cardinality_syntax

lemma cardinality_eq_if_equipollent_if_subset_if_ordinal:
  assumes "ordinal Y"
  and "\<And>Y'. ordinal Y' \<Longrightarrow> X \<approx> Y' \<Longrightarrow> Y \<subseteq> Y'"
  and "X \<approx> Y"
  shows "|X| = Y"
  unfolding cardinality_def using assms by (intro least_wrt_rel_eq_if_antisymmetric_onI) auto

lemma cardinality_eq_if_equipollent:
  assumes "X \<approx> Y"
  shows "|X| = |Y|"
  unfolding cardinality_def using assms transitive_equipollent symmetric_equipollent
  by (urule arg_cong2 where chained = insert) (auto 0 3 dest: symmetricD)

text\<open>The next lemma shows that \<open>X\<close> is equipollent with @{term "|X|"}
The proof requires order types, which are currently missing.  For a proof, see
\<^url>\<open>https://foss.heptapod.net/isa-afp/afp-devel/-/blob/06458dfa40c7b4aaaeb855a37ae77993cb4c8c18/thys/ZFC_in_HOL/ZFC_Cardinals.thy#L1829\<close>.\<close>

lemma cardinality_equipollent_self [iff]: "|X| \<approx> X"
  sorry

lemma cardinality_cardinality_eq_cardinality [simp]: "||X|| = |X|"
  by (intro cardinality_eq_if_equipollent cardinality_equipollent_self)

lemma cardinality_zero_eq_zero [simp]: "|0| = 0"
  by (intro cardinality_eq_if_equipollent_if_subset_if_ordinal) auto

end
