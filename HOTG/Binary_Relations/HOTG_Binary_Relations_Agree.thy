\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Agreement\<close>
theory HOTG_Binary_Relations_Agree
  imports
    Transport.Binary_Relations_Agree
    HOTG_Binary_Relation_Functions
begin

overloading
  rel_agree_on_set \<equiv> "rel_agree_on :: set \<Rightarrow> ((set \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool) \<Rightarrow> bool"
  set_rel_agree_on_pred \<equiv> "rel_agree_on :: (set \<Rightarrow> bool) \<Rightarrow> (set \<Rightarrow> bool) \<Rightarrow> bool"
  set_rel_agree_on_set \<equiv> "rel_agree_on :: set \<Rightarrow> (set \<Rightarrow> bool) \<Rightarrow> bool"
  set_set_rel_agree_on_pred \<equiv> "rel_agree_on :: (set \<Rightarrow> bool) \<Rightarrow> set \<Rightarrow> bool"
  set_set_rel_agree_on_set \<equiv> "rel_agree_on :: set \<Rightarrow> set \<Rightarrow> bool"
begin
  definition "rel_agree_on_set (A :: set) :: ((set \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool) \<Rightarrow> bool \<equiv>
    rel_agree_on (mem_of A)"
  definition "set_rel_agree_on_pred (P :: set \<Rightarrow> bool) (\<R> :: set \<Rightarrow> bool) \<equiv> \<forall>R R' : \<R>. R\<restriction>\<^bsub>P\<^esub> = R'\<restriction>\<^bsub>P\<^esub>"
  definition "set_rel_agree_on_set (A :: set) :: (set \<Rightarrow> bool) \<Rightarrow> bool \<equiv> rel_agree_on (mem_of A)"
  definition "set_set_rel_agree_on_pred (P :: set \<Rightarrow> bool) (\<R> :: set) \<equiv> rel_agree_on P (mem_of \<R>)"
  definition "set_set_rel_agree_on_set (A :: set) :: set \<Rightarrow> bool \<equiv> rel_agree_on (mem_of A)"
end

lemma rel_agree_on_set_eq_rel_agree_on_pred [simp]:
  "(rel_agree_on (A :: set) :: ((set \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool) \<Rightarrow> bool) = rel_agree_on (mem_of A)"
  unfolding rel_agree_on_set_def by simp

lemma rel_agree_on_set_eq_rel_agree_on_pred_uhint [uhint]:
  assumes "P \<equiv> mem_of A"
  shows "rel_agree_on (A :: set) :: ((set \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool) \<Rightarrow> bool \<equiv> rel_agree_on P"
  using assms by simp

lemma rel_agree_on_set_iff_rel_agree_on_pred [iff]:
  "rel_agree_on A (\<R> :: (set \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool) \<longleftrightarrow> rel_agree_on (mem_of A) \<R>"
  by simp

lemma set_rel_agree_onI [intro]:
  assumes "\<And>R R' x y. \<R> R \<Longrightarrow> \<R> R' \<Longrightarrow> P x \<Longrightarrow> \<langle>x, y\<rangle> \<in> R \<Longrightarrow> \<langle>x, y\<rangle> \<in> R'"
  shows "rel_agree_on P \<R>"
  using assms unfolding set_rel_agree_on_pred_def by fast

lemma set_rel_agree_onE:
  assumes "rel_agree_on (P :: set \<Rightarrow> bool) (\<R> :: set \<Rightarrow> bool)"
  obtains "\<And>R R'. \<R> R \<Longrightarrow> \<R> R' \<Longrightarrow> R\<restriction>\<^bsub>P\<^esub> = R'\<restriction>\<^bsub>P\<^esub>"
  using assms unfolding set_rel_agree_on_pred_def by blast

lemma set_rel_agree_onD:
  assumes "rel_agree_on P \<R>"
  and "\<R> R" "\<R> R'"
  and "P x"
  and "\<langle>x, y\<rangle> \<in> R"
  shows "\<langle>x, y\<rangle> \<in> R'"
  using assms by (blast elim: set_rel_agree_onE)

lemma set_rel_agree_on_has_inverse_on_restrict_left_if_set_rel_agree_on:
  assumes "rel_agree_on (P :: set \<Rightarrow> bool) (\<R> :: set \<Rightarrow> bool)"
  shows "rel_agree_on P (has_inverse_on \<R> (\<lambda>R. R\<restriction>\<^bsub>P\<^esub>))"
  using assms by (intro set_rel_agree_onI) (blast dest: set_rel_agree_onD)

lemma set_rel_agree_on_if_set_rel_agree_on_has_inverse_on_restrict_left:
  assumes "rel_agree_on P (has_inverse_on \<R> (\<lambda>R. R\<restriction>\<^bsub>P\<^esub>))"
  shows "rel_agree_on (P :: set \<Rightarrow> bool) (\<R> :: set \<Rightarrow> bool)"
  using assms by (intro set_rel_agree_onI) (blast dest: set_rel_agree_onD)

corollary set_rel_agree_on_iff_set_rel_agree_on_has_inverse_on_restrict_left:
  "rel_agree_on (P :: set \<Rightarrow> bool) (\<R> :: set \<Rightarrow> bool) \<longleftrightarrow> rel_agree_on P (has_inverse_on \<R> (\<lambda>R. R\<restriction>\<^bsub>P\<^esub>))"
  using set_rel_agree_on_has_inverse_on_restrict_left_if_set_rel_agree_on
    set_rel_agree_on_if_set_rel_agree_on_has_inverse_on_restrict_left by blast

lemma rel_agree_on_has_inverse_on_rel_if_set_rel_agree_on:
  assumes "rel_agree_on (P :: set \<Rightarrow> bool) \<R>"
  shows "rel_agree_on P (has_inverse_on \<R> rel)"
  using assms by (intro rel_agree_onI) (blast dest: set_rel_agree_onD)

lemma set_rel_agree_on_if_rel_agree_on_has_inverse_on_rel:
  assumes "rel_agree_on P (has_inverse_on \<R> rel)"
  shows "rel_agree_on (P :: set \<Rightarrow> bool) \<R>"
  using assms by (blast dest: rel_agree_onD)

lemma set_rel_agree_on_pred_iff_rel_agree_on_has_inverse_on [set_to_HOL_simp]:
  "rel_agree_on (P :: set \<Rightarrow> bool) (\<R> :: set \<Rightarrow> bool) \<longleftrightarrow> rel_agree_on P (has_inverse_on \<R> rel)"
  using rel_agree_on_has_inverse_on_rel_if_set_rel_agree_on
    set_rel_agree_on_if_rel_agree_on_has_inverse_on_rel by blast

lemma set_rel_agree_on_pred_eq_rel_agree_on_has_inverse_on_uhint [uhint]:
  assumes "P \<equiv> P'"
  and "\<R>' \<equiv> has_inverse_on \<R> rel"
  shows "rel_agree_on (P :: set \<Rightarrow> bool) (\<R> :: set \<Rightarrow> bool) \<equiv> rel_agree_on P' \<R>'"
  using assms by (simp add: set_rel_agree_on_pred_iff_rel_agree_on_has_inverse_on)

lemma antimono_set_rel_agree_on:
  "((\<le>) \<Rightarrow> (\<le>) \<Rrightarrow> (\<ge>)) (rel_agree_on :: (set \<Rightarrow> bool) \<Rightarrow> (set \<Rightarrow> bool) \<Rightarrow> bool)"
  by (intro mono_wrt_relI Fun_Rel_relI) (fastforce dest: set_rel_agree_onD)

lemma set_rel_agree_on_comp_rel_if_rel_agree_on:
  assumes "rel_agree_on P \<R>"
  shows "rel_agree_on (P :: set \<Rightarrow> bool) (\<R> \<circ> rel :: set \<Rightarrow> bool)"
  using assms by (intro set_rel_agree_onI) (auto dest: rel_agree_onD)

context
  notes set_to_HOL_simp[simp]
begin

lemma set_rel_restrict_left_eq_if_set_rel_agree_onI:
  assumes "rel_agree_on (P :: set \<Rightarrow> bool) (\<R> :: set \<Rightarrow> bool)"
  and "\<R> R" "\<R> R'"
  shows "R\<restriction>\<^bsub>P\<^esub> = R'\<restriction>\<^bsub>P\<^esub>"
  by (urule rel_restrict_left_eq_if_rel_agree_onI) (urule assms has_inverse_onI)+

lemma subset_if_in_dom_le_if_set_rel_agree_onI:
  assumes [simp]: "is_bin_rel R"
  and "rel_agree_on A \<R>"
  and "\<R> R" "\<R> R'"
  and "in_dom (rel R) \<le> A"
  shows "R \<subseteq> R'"
  by (urule le_if_in_dom_le_if_rel_agree_onI) (urule assms has_inverse_onI)+

lemma eq_if_in_dom_le_if_set_rel_agree_onI:
  assumes [simp]: "is_bin_rel R" "is_bin_rel R'"
  and "rel_agree_on A \<R>"
  and "\<R> R" "\<R> R'"
  and "in_dom (rel R) \<le> A" "in_dom (rel R') \<le> A"
  shows "R = R'"
  by (urule eq_if_in_dom_le_if_rel_agree_onI) (urule assms has_inverse_onI)+

end

lemma set_rel_agree_on_set_eq_set_rel_agree_on_pred [simp]:
  "(rel_agree_on (A :: set) :: (set \<Rightarrow> bool) \<Rightarrow> bool) = rel_agree_on (mem_of A)"
  unfolding set_rel_agree_on_set_def by simp

lemma set_rel_agree_on_set_eq_set_rel_agree_on_pred_uhint [uhint]:
  assumes "P \<equiv> mem_of A"
  shows "rel_agree_on (A :: set) :: (set \<Rightarrow> bool) \<Rightarrow> bool \<equiv> rel_agree_on P"
  using assms by simp

lemma set_rel_agree_on_set_iff_set_rel_agree_on_pred [iff]:
  "rel_agree_on A (\<R> :: set \<Rightarrow> bool) \<longleftrightarrow> rel_agree_on (mem_of A) \<R>"
  by simp

lemma set_set_rel_agree_on_pred_eq_set_rel_agree_on_pred [simp]:
  "rel_agree_on (P :: set \<Rightarrow> bool) (\<R> :: set) = rel_agree_on P (mem_of \<R>)"
  unfolding set_set_rel_agree_on_pred_def by simp

lemma set_set_rel_agree_on_pred_eq_set_rel_agree_on_pred_uhint [uhint]:
  assumes "P :: set \<Rightarrow> bool \<equiv> P'"
  and "\<R>' \<equiv> mem_of \<R>"
  shows "rel_agree_on P \<R> \<equiv> rel_agree_on P' \<R>'"
  using assms by simp

lemma set_set_rel_agree_on_pred_iff_set_rel_agree_on_pred [iff]:
  "rel_agree_on (P :: set \<Rightarrow> bool) (\<R> :: set) \<longleftrightarrow> rel_agree_on P (mem_of \<R>)"
  by simp

lemma set_set_rel_agree_on_set_eq_set_set_rel_agree_on_pred [simp]:
  "(rel_agree_on (A :: set) :: set \<Rightarrow> bool) = rel_agree_on (mem_of A)"
  unfolding set_set_rel_agree_on_set_def by simp

lemma set_set_rel_agree_on_set_eq_set_set_rel_agree_on_pred_uhint [uhint]:
  assumes "P \<equiv> mem_of A"
  shows "rel_agree_on (A :: set) :: set \<Rightarrow> bool \<equiv> rel_agree_on P"
  using assms by simp

lemma set_set_rel_agree_on_set_iff_set_set_rel_agree_on_pred [iff]:
  "rel_agree_on A (\<R> :: set) \<longleftrightarrow> rel_agree_on (mem_of A) \<R>"
  by simp


end