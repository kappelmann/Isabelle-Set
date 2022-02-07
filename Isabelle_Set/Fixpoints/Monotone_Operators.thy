subsection \<open>Monotone Operators\<close>
theory Monotone_Operators
  imports
    Fixpoints_Base
    HOTG.Universes
    Sets
begin

definition monotone :: "set \<Rightarrow> (set \<Rightarrow> set) \<Rightarrow> bool"
  where "monotone D h \<equiv> (\<forall>W X. W \<subseteq> X \<longrightarrow> X \<subseteq> D \<longrightarrow> h W \<subseteq> h X)"

lemma monotone_type [type]: "monotone : (D: Set) \<Rightarrow> (Subset D \<Rightarrow> Subset D) \<Rightarrow> Bool"
  by unfold_types

lemma monotoneI [intro!]:
  assumes "\<And>W X. \<lbrakk>W \<subseteq> X; X \<subseteq> D\<rbrakk> \<Longrightarrow> h W \<subseteq> h X"
  shows "monotone D h"
  unfolding monotone_def using assms by blast

abbreviation "Monop D \<equiv> monotone D \<sqdot> (Subset D \<Rightarrow> Subset D)"

lemma MonopI:
  assumes closed_on_D: "\<And>x. x \<subseteq> D \<Longrightarrow> h x \<subseteq> D"
  and monotone_D: "monotone D h"
  shows "h : Monop D"
  by (unfold_types) (insert monotone_D, auto intro!: closed_on_D)

lemma Monop_app_subset_app_if_subset:
  "\<lbrakk>h : Monop D; X \<subseteq> D; W \<subseteq> X\<rbrakk> \<Longrightarrow> h W \<subseteq> h X"
  unfolding monotone_def by unfold_types

lemma Monop_prefixpoint: "h : Monop D \<Longrightarrow> prefixpoint D h"
  unfolding prefixpoint_def by auto

lemma Monop_app_Subset_if_Subset [derive]:
  "h : Monop D \<Longrightarrow> X : Subset D \<Longrightarrow> h X : Subset D"
  by unfold_types


subsubsection \<open>Instances\<close>

lemma id_Monop [derive]: "(\<lambda>x. x) : Monop D"
  unfolding monotone_def by unfold_types auto

lemma K_MonopI [derive]: "x : Subset D \<Longrightarrow> (\<lambda>_. x) : Monop D"
  unfolding monotone_def by unfold_types auto

lemma bin_union_Monop_app_subset_app_bin_union:
  assumes "h : Monop D" "A \<subseteq> D" "B \<subseteq> D"
  shows "h A \<union> h B \<subseteq> h (A \<union> B)"
proof -
  have "h A \<subseteq> h (A \<union> B)"
    by (rule Monop_app_subset_app_if_subset) (insert assms, auto)
  moreover have "h B \<subseteq> h (A \<union> B)"
    by (rule Monop_app_subset_app_if_subset) (insert assms, auto)
  ultimately show ?thesis by auto
qed

lemma bin_union_MonopI [derive]:
  assumes "f : Monop D" "g : Monop D"
  shows "(\<lambda>x. f x \<union> g x) : Monop D" (is "?h : Monop D")
proof (rule MonopI)
  fix X assume "X \<subseteq> D"
  with assms show "f X \<union> g X \<subseteq> D"
    by (auto intro!: Monop_prefixpoint[unfolded prefixpoint_def])
next
  show "monotone D ?h"
  proof (rule monotoneI)
    fix W X assume "W \<subseteq> X" "X \<subseteq> D"
    have "f W \<subseteq> f X" by (rule Monop_app_subset_app_if_subset) auto
    moreover have "g W \<subseteq> g X" by (rule Monop_app_subset_app_if_subset) auto
    ultimately show "f W \<union> g W \<subseteq> f X \<union> g X" by auto
  qed
qed

lemma replacement_MonopI:
  assumes "f : Monop D"
  and "\<And>X. X : Subset D \<Longrightarrow> g : Element (f X) \<Rightarrow> Element D"
  shows "(\<lambda>x. {g y | y \<in> f x}) : Monop D" (is "?h : Monop D")
proof (rule MonopI)
  fix X assume "X \<subseteq> D"
  with assms show "{g y | y \<in> f X} \<subseteq> D"
    (*TODO unfold_type directly loops*)
    by (unfold Element_def) (unfold_types, auto)
next
  show "monotone D ?h"
  proof (rule monotoneI)
    fix W X assume "W \<subseteq> X" "X \<subseteq> D"
    have "f W \<subseteq> f X" by (rule Monop_app_subset_app_if_subset) auto
    then show "{g y | y \<in> f W} \<subseteq> {g y | y \<in> f X}"
      by (rule repl_subset_repl_if_subset_dom)
  qed
qed

lemma pairs_MonopI [derive]:
  assumes "A : Monop (univ X)" "B : Monop (univ X)"
  shows "(\<lambda>x. A x \<times> B x) : Monop (univ X)" (is "?h : Monop ?D")
proof (rule MonopI)
  fix X assume "X \<subseteq> ?D"
  with subset_univ_if_subset_univ_pairs show "A X \<times> B X \<subseteq> ?D" by auto
next
  show "monotone ?D ?h"
  proof (rule monotoneI)
    fix W X assume "W \<subseteq> X" "X \<subseteq> ?D"
    have "A W \<subseteq> A X" by (rule Monop_app_subset_app_if_subset) auto
    moreover have "B W \<subseteq> B X" by (rule Monop_app_subset_app_if_subset) auto
    ultimately show "A W \<times> B W \<subseteq> A X \<times> B X" by auto
  qed
qed


end
