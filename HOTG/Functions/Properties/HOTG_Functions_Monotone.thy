\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsubsection \<open>Monotonicity\<close>
theory HOTG_Functions_Monotone
  imports
    HOTG_Functions_Base
    Transport.Functions_Monotone
begin

definition "dep_mono_wrt_set A B \<equiv> (x : mem_of A) \<Rightarrow> mem_of (B x)"
adhoc_overloading dep_mono_wrt dep_mono_wrt_set
definition "mono_wrt_set A B \<equiv> mem_of A \<Rightarrow> mem_of B"
adhoc_overloading mono_wrt mono_wrt_set

lemma dep_mono_wrt_set_eq_dep_mono_wrt_pred [simp]:
  "((x : A) \<Rightarrow> B x) = ((x : mem_of A) \<Rightarrow> mem_of (B x))"
  unfolding dep_mono_wrt_set_def by simp

lemma dep_mono_wrt_set_eq_dep_mono_wrt_pred_uhint [uhint]:
  assumes "A' \<equiv> mem_of A"
  and "\<And>x. B' x \<equiv> mem_of (B x)"
  shows "((x : A) \<Rightarrow> B x) \<equiv> ((x : A') \<Rightarrow> B' x)"
  using assms by simp

lemma dep_mono_wrt_set_iff_dep_mono_wrt_pred [iff]:
  "((x : A) \<Rightarrow> B x) f \<longleftrightarrow> ((x : mem_of A) \<Rightarrow> mem_of (B x)) f"
  by simp

lemma mono_wrt_set_eq_mono_wrt_pred [simp]:
  "(A \<Rightarrow> B) = (mem_of A \<Rightarrow> mem_of B)"
  unfolding mono_wrt_set_def by simp

lemma mono_wrt_set_eq_mono_wrt_pred_uhint [uhint]:
  assumes "A' \<equiv> mem_of A"
  and "B' \<equiv> mem_of B"
  shows "(A \<Rightarrow> B) \<equiv> (A' \<Rightarrow> B')"
  using assms by simp

lemma mono_wrt_set_iff_mono_wrt_pred [iff]: "(A \<Rightarrow> B) f \<longleftrightarrow> (mem_of A \<Rightarrow> mem_of B) f"
  by simp

definition "set_dep_mono_wrt_pred \<equiv> set_rel_dep_mono_wrt_pred"
adhoc_overloading dep_mono_wrt set_dep_mono_wrt_pred
definition "set_mono_wrt_pred \<equiv> set_rel_mono_wrt_pred"
adhoc_overloading mono_wrt set_mono_wrt_pred
definition "set_dep_mono_wrt_set \<equiv> set_rel_dep_mono_wrt_set"
adhoc_overloading dep_mono_wrt set_dep_mono_wrt_set
definition "set_mono_wrt_set \<equiv> set_rel_mono_wrt_set"
adhoc_overloading mono_wrt set_mono_wrt_set

lemma set_dep_mono_wrt_pred_eq_set_rel_dep_mono_wrt_pred [simp]:
  "set_dep_mono_wrt_pred = set_rel_dep_mono_wrt_pred"
  unfolding set_dep_mono_wrt_pred_def by simp

lemma set_dep_mono_wrt_pred_eq_set_rel_dep_mono_wrt_pred_uhint [uhint]:
  "set_dep_mono_wrt_pred \<equiv> set_rel_dep_mono_wrt_pred"
  by simp

lemma set_dep_mono_wrt_pred_iff_set_rel_dep_mono_wrt_pred [iff]:
  "((x : (A :: set \<Rightarrow> bool)) \<Rightarrow> B x) (R :: set) \<longleftrightarrow> ((x : A) \<rightarrow> B x) R"
  by simp

lemma set_mono_wrt_pred_eq_set_rel_mono_wrt_pred [simp]:
  "set_mono_wrt_pred = set_rel_mono_wrt_pred"
  unfolding set_mono_wrt_pred_def by simp

lemma set_mono_wrt_pred_eq_set_rel_mono_wrt_pred_uhint [uhint]:
  "set_mono_wrt_pred \<equiv> set_rel_mono_wrt_pred"
  by simp

lemma set_mono_wrt_pred_iff_set_rel_mono_wrt_pred [iff]:
  "((A :: set \<Rightarrow> bool) \<Rightarrow> B) (R :: set) \<longleftrightarrow> (A \<rightarrow> B) R"
  by simp

lemma set_dep_mono_wrt_set_eq_set_rel_dep_mono_wrt_set [simp]:
  "set_dep_mono_wrt_set = set_rel_dep_mono_wrt_set"
  unfolding set_dep_mono_wrt_set_def by simp

lemma set_dep_mono_wrt_set_eq_set_rel_dep_mono_wrt_set_uhint [uhint]:
  "set_dep_mono_wrt_set \<equiv> set_rel_dep_mono_wrt_set"
  by simp

lemma set_dep_mono_wrt_set_iff_set_rel_dep_mono_wrt_set [iff]:
  "((x : (A :: set)) \<Rightarrow> B x) (R :: set) \<longleftrightarrow> ((x : A) \<rightarrow> B x) R"
  by simp

lemma set_mono_wrt_set_eq_set_rel_mono_wrt_set [simp]:
  "set_mono_wrt_set = set_rel_mono_wrt_set"
  unfolding set_mono_wrt_set_def by simp

lemma set_mono_wrt_set_eq_set_rel_mono_wrt_set_uhint [uhint]:
  "set_mono_wrt_set \<equiv> set_rel_mono_wrt_set"
  by simp

lemma set_mono_wrt_set_iff_set_rel_mono_wrt_set [iff]:
  "((A :: set) \<Rightarrow> B) (R :: set) \<longleftrightarrow> (A \<rightarrow> B) R"
  by simp

end