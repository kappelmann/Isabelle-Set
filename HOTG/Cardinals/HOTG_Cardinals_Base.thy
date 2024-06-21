\<^marker>\<open>creator "Linghan Fang"\<close>
\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Cardinals\<close>
theory HOTG_Cardinals_Base
  imports
    Transport.Binary_Relations_Least
    HOTG_Equipollence
    HOTG_Ordinals_Base
    HOTG_Less_Than
    HOTG_Choice
begin

unbundle no_HOL_groups_syntax
unbundle no_HOL_order_syntax

paragraph \<open>Summary\<close>
text \<open>Translation of cardinality from HOL-Library and \<^cite>\<open>ZFC_in_HOL_AFP\<close>.

The cardinality of a set \<open>X\<close> is the smallest ordinal number \<open>\<alpha>\<close> such that there
exists a bijection between \<open>X\<close> and \<open>\<alpha>\<close>.
Further details can be found in \<^url>\<open>https://en.wikipedia.org/wiki/Cardinal_number\<close>.\<close>

(* Verwende (\<le>) statt (\<subseteq>) da (\<le>)/(\<subseteq>) auf Ordinalzahlen äquivalent sind und (\<le>) hier bequemer ist. *)
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

text\<open>The next lemma shows that \<open>X\<close> is equipollent with @{term "|X|"}
The proof requires order types, which are currently missing.  For a proof, see
\<^url>\<open>https://foss.heptapod.net/isa-afp/afp-devel/-/blob/06458dfa40c7b4aaaeb855a37ae77993cb4c8c18/thys/ZFC_in_HOL/ZFC_Cardinals.thy#L1829\<close>.\<close>

lemma least_ordinal_with_prop_welldefined_if_witness:
  assumes "P \<gamma>" and ordinal_if_P: "\<forall>\<alpha> : P. ordinal \<alpha>"
  shows "is_least_wrt_rel (\<le>) P (least_wrt_rel (\<le>) P)"
proof -
  from \<open>P \<gamma>\<close> obtain \<alpha> where "P \<alpha>" and \<alpha>_minimal: "\<And>\<beta>. \<beta> < \<alpha> \<Longrightarrow> \<not> P \<beta>" 
    using lt_minimal_set_witnessE by blast
  have \<alpha>_least: "\<alpha> \<le> \<beta>" if "P \<beta>" for \<beta>
  proof -
    have "ordinal \<alpha>" "ordinal \<beta>" using \<open>P \<alpha>\<close> \<open>P \<beta>\<close> ordinal_if_P by auto
    then show ?thesis using that \<alpha>_minimal by (cases rule: lt_eq_lt_if_ordinalE) auto
  qed
  then have "is_least_wrt_rel (\<le>) P \<alpha>" 
    using \<open>P \<alpha>\<close> by (auto intro!: is_least_wrt_rel_if_antisymmetric_onI)
  then show ?thesis using least_wrt_rel_eqI by force
qed

lemma
  ordinal_cardinality: "ordinal |X|" and
  cardinality_equipollent_self [iff]: "|X| \<approx> X" and
  cardinality_le_if_equipollent_ordinal: "\<forall>\<beta> : ordinal. X \<approx> \<beta> \<longrightarrow> |X| \<le> \<beta>"
proof -
  define P where "P \<equiv> ordinal \<sqinter> ((\<approx>) X)"
  from equipollent_some_ordinal obtain \<alpha> where "ordinal \<alpha>" "X \<approx> \<alpha>" by blast
  then have "P \<alpha>" "\<forall>\<beta> : P. ordinal \<beta>" using P_def by auto
  then have least: "is_least_wrt_rel (\<le>) P |X|" 
    using cardinality_def P_def least_ordinal_with_prop_welldefined_if_witness by auto
  then show "ordinal |X|" "|X| \<approx> X" "\<forall>\<beta> : ordinal. X \<approx> \<beta> \<longrightarrow> |X| \<le> \<beta>" 
    using P_def symmetric_equipollent 
    by (auto elim!: is_least_wrt_relE is_minimal_wrt_relE dest: symmetricD)
qed

lemma cardinality_cardinality_eq_cardinality [simp]: "||X|| = |X|"
  by (intro cardinality_eq_if_equipollent cardinality_equipollent_self)

lemma cardinality_zero_eq_zero [simp]: "|0| = 0"
  by (intro cardinality_eq_if_equipollent_if_le_if_ordinal) (auto simp: zero_le_if_ordinal)

end
