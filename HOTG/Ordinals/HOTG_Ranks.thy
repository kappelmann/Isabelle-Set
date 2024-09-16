\<^marker>\<open>creator "Niklas Krofta"\<close>
subsection \<open>Ranks\<close>
theory HOTG_Ranks
  imports
    HOTG_Ordinals_Base
    HOTG_Less_Than
    HOTG_Epsilon_Recursion
begin

unbundle no_HOL_order_syntax

definition rank :: "set \<Rightarrow> set" where
  "rank = mem_rec (\<lambda>rank X. (\<Union>x \<in> X. succ (rank x)))"

lemma rank_eq_idx_union_succ_rank: "rank X = (\<Union>x \<in> X. succ (rank x))"
  unfolding rank_def by (urule mem_rec_eq)

lemma ordinal_rank: "ordinal (rank X)"
proof (induction X rule: mem_induction)
  case (mem X)
  then show ?case using rank_eq_idx_union_succ_rank[of X] by (auto intro: ordinal_unionI)
qed

lemma rank_lt_rank_if_lt: "A < B \<Longrightarrow> rank A < rank B"
proof (induction B rule: mem_induction)
  case (mem B)
  from \<open>A < B\<close> obtain C where "C \<in> B" "A \<le> C" by (auto elim: lt_mem_leE)
  have "rank A \<le> rank C" using leE \<open>A \<le> C\<close>
  proof cases
    case lt
    then show ?thesis using mem.IH \<open>C \<in> B\<close> le_if_lt by auto
  qed auto
  moreover have "rank C < rank B"
  proof -
    have "succ (rank C) \<subseteq> rank B" using rank_eq_idx_union_succ_rank[of B] \<open>C \<in> B\<close> by auto
    then show ?thesis using succ_eq_insert_self lt_if_mem by auto
  qed
  ultimately show ?case using lt_if_le_if_lt by auto
qed

end