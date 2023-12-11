\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Empty Set\<close>
theory Empty_Set
  imports Equality
begin

lemma emptyE [elim]: "x \<in> {} \<Longrightarrow> P" by auto

lemma eq_emptyI [intro]: "\<lbrakk>\<And>y. y \<in> A \<Longrightarrow> False\<rbrakk> \<Longrightarrow> A = {}"
  by auto

lemma not_mem_if_empty [dest]: "A = {} \<Longrightarrow> a \<notin> A"
  by auto

lemma ne_empty_if_mem: "a \<in> A \<Longrightarrow> A \<noteq> {}"
  by auto

lemma ex_mem_if_ne_empty: "A \<noteq> {} \<Longrightarrow> \<exists>x. x \<in> A"
  by auto

lemma ne_emptyE:
  assumes "A \<noteq> {}"
  obtains x where "x \<in> A"
  using ex_mem_if_ne_empty[OF assms]
  by blast

lemma mem_trans_closed_empty [iff]: "mem_trans_closed {}"
  unfolding mem_trans_closed_def by blast


end
