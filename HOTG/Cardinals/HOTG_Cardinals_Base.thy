\<^marker>\<open>creator "Linghan Fang"\<close>
\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Cardinals\<close>
theory HOTG_Cardinals_Base
  imports
    Transport.Binary_Relations_Least
    HOTG_Ordinals_Equipollent
    HOTG_Equipollence
    HOTG_Ordinals_Base
    HOTG_Less_Than
begin

unbundle no_HOL_groups_syntax
unbundle no_HOL_order_syntax

paragraph \<open>Summary\<close>
text \<open>Translation of cardinality from HOL-Library and \<^cite>\<open>ZFC_in_HOL_AFP\<close>.

The cardinality of a set \<open>X\<close> is the smallest ordinal number \<open>\<alpha>\<close> such that there
exists a bijection between \<open>X\<close> and \<open>\<alpha>\<close>.
Further details can be found in \<^url>\<open>https://en.wikipedia.org/wiki/Cardinal_number\<close>.\<close>

definition "cardinality (X :: set) \<equiv> least_wrt_rel (\<le>) (ordinal \<sqinter> ((\<approx>) X))"

bundle hotg_cardinality_syntax begin notation cardinality ("|_|") end
bundle no_hotg_cardinality_syntax begin no_notation cardinality ("|_|") end
unbundle hotg_cardinality_syntax

lemma cardinality_eq_if_equipollent_if_le_if_ordinal:
  assumes "ordinal Y"
  and "\<And>Y'. ordinal Y' \<Longrightarrow> X \<approx> Y' \<Longrightarrow> Y \<le> Y'"
  and "X \<approx> Y"
  shows "|X| = Y"
  unfolding cardinality_def using assms by (intro least_wrt_rel_eq_if_antisymmetric_onI) auto

lemma cardinality_eq_if_equipollent:
  assumes "X \<approx> Y"
  shows "|X| = |Y|"
  unfolding cardinality_def using assms transitive_equipollent symmetric_equipollent
  by (urule arg_cong2 where chained = insert) (auto 0 3 dest: symmetricD)

text\<open>The next lemma shows that @{term "|X|"} has the properties expected from the definition.\<close>

lemma
  ordinal_cardinality: "ordinal |X|" and
  cardinality_equipollent_self [iff]: "|X| \<approx> X" and
  cardinality_le_if_equipollent_if_ordinal: "\<And>\<alpha>. ordinal \<alpha> \<Longrightarrow> X \<approx> \<alpha> \<Longrightarrow> |X| \<le> \<alpha>"
proof -
  define P where "P \<equiv> ordinal \<sqinter> ((\<approx>) X)"
  from bex_ordinal_equipollent obtain \<alpha> where "ordinal \<alpha>" "X \<approx> \<alpha>" by blast
  then have "P \<alpha>" "\<forall>\<beta> : P. ordinal \<beta>" using P_def by auto
  then have least: "is_least_wrt_rel (\<le>) P |X|"
    using cardinality_def P_def is_least_wrt_rel_least_wrt_rel_if_le_ordinal_if_pred by auto
  then show "ordinal |X|" "|X| \<approx> X" "\<And>\<alpha>. ordinal \<alpha> \<Longrightarrow> X \<approx> \<alpha> \<Longrightarrow> |X| \<le> \<alpha>"
    using P_def symmetric_equipollent by (blast dest: symmetricD)+
qed

lemma cardinality_cardinality_eq_cardinality [simp]: "||X|| = |X|"
  by (intro cardinality_eq_if_equipollent cardinality_equipollent_self)

lemma cardinality_zero_eq_zero [simp]: "|0| = 0"
  by (intro cardinality_eq_if_equipollent_if_le_if_ordinal) (auto simp: zero_le_if_ordinal)

lemma equipollent_if_cardinality_eq:
  assumes "|X| = |Y|"
  shows "X \<approx> Y"
proof -
  have "X \<approx> |X|" using cardinality_equipollent_self symmetric_equipollent by (blast dest: symmetricD)
  also have "... = |Y|" using assms by blast
  also have "... \<approx> Y" using cardinality_equipollent_self by blast
  finally show ?thesis .
qed

corollary equipollent_iff_cardinality_eq: "X \<approx> Y \<longleftrightarrow> |X| = |Y|"
  using cardinality_eq_if_equipollent equipollent_if_cardinality_eq by blast

end
