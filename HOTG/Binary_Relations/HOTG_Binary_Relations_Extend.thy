\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Extensions\<close>
theory HOTG_Binary_Relations_Extend
  imports
    Transport.Binary_Relations_Extend
    HOTG_Binary_Relation_Functions
begin

definition "extend_set x y R \<equiv> insert \<langle>x, y\<rangle> R"
adhoc_overloading extend \<rightleftharpoons> extend_set

lemma mem_extend_leftI [iff]: "\<langle>x, y\<rangle> \<in> extend x y R"
  unfolding extend_set_def by blast

lemma mem_extendI_rightI [intro]:
  assumes "p \<in> R"
  shows "p \<in> extend x y R"
  unfolding extend_set_def using assms by blast

lemma mem_extendE [elim]:
  assumes "p \<in> extend x y R"
  obtains "p = \<langle>x, y\<rangle>" | "p \<noteq> \<langle>x, y\<rangle>" "p \<in> R"
  using assms unfolding extend_set_def by blast

lemma is_bin_rel_extend_if_is_bin_rel [intro]:
  assumes "is_bin_rel R"
  shows "is_bin_rel (extend x y R)"
  using assms by (intro is_bin_relI) auto

lemma rel_extend_eq_extend_rel [simp, set_to_HOL_simp]: "rel (extend x y R) = extend x y (rel R)"
  by (intro ext) auto

lemma extend_eq_self_if_pair_mem [simp]: "\<langle>x, y\<rangle> \<in> R \<Longrightarrow> extend x y R = R"
  by auto

lemma insert_pair_eq_extend [simp]: "insert \<langle>x, y\<rangle> R = extend x y R"
  by auto

lemma dom_extend_eq [simp]: "dom (extend x y R) = insert x (dom R)"
  by auto

lemma codom_extend_eq [simp]: "codom (extend x y R) = insert y (codom R)"
  by auto

lemma field_extend_eq [simp]: "field (extend x y R) = insert x (insert y (field R))"
  by blast


lemma mono_subset_extend_set: "((\<subseteq>) \<Rightarrow> (\<subseteq>)) (extend x y)" by fast

lemma dep_mono_set_dep_bin_rel_extend:
  "((x : A) \<Rightarrow> B x \<Rightarrow> ({\<Sum>}x : A'. B' x) \<Rightarrow> ({\<Sum>}x : A \<squnion> A'. (B \<squnion> B') x :: set \<Rightarrow> bool)) extend_set"
  by (urule (rr) dep_mono_wrt_predI set_dep_bin_relI dep_bin_relI) force+


definition "has_inverse_on_set A :: (set \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> bool \<equiv> has_inverse_on (mem_of A)"
adhoc_overloading has_inverse_on \<rightleftharpoons> has_inverse_on_set

lemma has_inverse_on_set_eq_has_inverse_on_pred [simp]:
  "(has_inverse_on_set A :: (set \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> bool) = has_inverse_on (mem_of A)"
  unfolding has_inverse_on_set_def by simp

lemma has_inverse_on_set_eq_has_inverse_on_pred_uhint [uhint]:
  assumes "P \<equiv> mem_of A"
  shows "has_inverse_on_set A :: (set \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> bool \<equiv> has_inverse_on P"
  using assms by simp

lemma has_inverse_on_set_iff_has_inverse_on_pred_uhint [iff]:
  "has_inverse_on_set A f y \<longleftrightarrow> has_inverse_on (mem_of A) f y"
  by simp

lemma mem_of_repl_eq_has_inverse_on [simp, set_to_HOL_simp]:
  "mem_of (repl A f) = has_inverse_on A f"
  by (intro ext) auto

context
  notes set_to_HOL_simp[simp]
begin

lemma has_inverse_on_empty_eq [simp]: "has_inverse_on {} = \<bottom>"
  by (urule has_inverse_on_bottom_eq)

lemma has_inverse_on_singleton_eq_eq_app [simp]: "has_inverse_on {S} f = (=) (f S)"
  by (urule has_inverse_on_eq_pred_eq_eq_app)

lemma has_inverse_on_bin_union_eq_has_inverse_on_sup_has_inverse_on [simp]:
  "has_inverse_on (A \<union> B) = has_inverse_on A \<squnion> has_inverse_on B"
  by (urule has_inverse_on_sup_eq_has_inverse_on_sup_has_inverse_on)

end


definition "glue_set (\<R> :: set) \<equiv> \<Union>\<R>"
adhoc_overloading glue \<rightleftharpoons> glue_set

lemma mem_glueI [intro]:
  assumes "R \<in> \<R>"
  and "p \<in> R"
  shows "p \<in> glue \<R>"
  using assms unfolding glue_set_def by blast

lemma mem_glueE [elim!]:
  assumes "p \<in> glue \<R>"
  obtains R where "R \<in> \<R>" "p \<in> R"
  using assms unfolding glue_set_def by blast

lemma rel_glue_eq_glue_has_inverse_on_rel [set_to_HOL_simp]:
  "rel (glue \<R>) = glue (has_inverse_on \<R> rel)"
  by auto

lemma glue_empty_eq [simp]: "glue {} = {}" by auto

lemma glue_insert_eq [simp]: "glue (insert R \<R>) = R \<union> glue \<R>" by auto

lemma glue_bin_union_eq_glue_bin_union_glue [simp]: "glue (\<R> \<union> \<R>') = glue \<R> \<union> glue \<R>'" by auto

lemma mono_glue: "((\<subseteq>) \<Rightarrow> (\<subseteq>)) glue" by auto

lemma is_bin_rel_glue_if_is_bin_rel_if_mem [intro]:
  assumes "\<And>R. R \<in> \<R> \<Longrightarrow> is_bin_rel R"
  shows "is_bin_rel (glue \<R>)"
  using assms by (intro is_bin_relI) auto

lemma mem_of_idx_union_eq_in_codom_on_has_inverse_on_if_mem_of_eq_app_rel:
  assumes "\<And>R. mem_of (f R) = g (rel R)"
  shows "mem_of (\<Union>R \<in> \<R>. f R) = in_codom_on (has_inverse_on \<R> rel) g" (is "?lhs = ?rhs")
proof (intro ext iffI)
  fix x assume "?lhs x"
  then obtain R where "g (rel R) x" "R \<in> \<R>" by (auto simp flip: assms)
  then show "?rhs x" by (intro in_codom_onI) auto
qed (fastforce simp flip: assms)

lemma set_dep_bin_rel_set_glueI:
  fixes \<R> defines "D \<equiv> \<Union>R \<in> \<R>. dom R"
  assumes "\<And>R. R \<in> \<R> \<Longrightarrow> \<exists>A. ({\<Sum>}x : A. B x) R"
  shows "({\<Sum>}x : D. B x) (glue \<R>)"
proof (urule set_dep_bin_relI)
  show "({\<Sum>}x : mem_of D. mem_of (B x)) (rel (glue \<R>))"
    supply rel_glue_eq_glue_has_inverse_on_rel[simp] D_def[simp]
      mem_of_idx_union_eq_in_codom_on_has_inverse_on_if_mem_of_eq_app_rel[of dom in_dom, simp]
    by (urule dep_bin_rel_glueI) (use assms in fast)
  from assms show "is_bin_rel (glue \<R>)" by (intro is_bin_rel_glue_if_is_bin_rel_if_mem) blast
qed


end
