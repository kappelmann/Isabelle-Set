\<^marker>\<open>creator "Alexander Krauss"\<close>
\<^marker>\<open>creator "Kevin Kappelmann"\<close>
\<^marker>\<open>creator "Larry Paulson"\<close>
section \<open>Union and Intersection\<close>
theory HOTG_Union_Intersection
  imports HOTG_Comprehension
begin

definition "inter A \<equiv> {x \<in> \<Union>A | \<forall>y : A. x \<in> y}"

open_bundle hotg_inter_syntax begin notation inter ("\<Inter>_" [90] 90) end

text \<open>Intersection is well-behaved only if the family is non-empty!\<close>

lemma mem_inter_iff [iff]: "A \<in> \<Inter>C \<longleftrightarrow> C \<noteq> {} \<and> (\<forall>x : C. A \<in> x)"
  unfolding inter_def by auto

(*LP: A "destruct" rule: every B in C contains A as an element, but A \<in> B can
  hold when B \<in> C does not! This rule is analogous to "spec".*)
lemma interD [dest]: "\<lbrakk>A \<in> \<Inter>C; B \<in> C\<rbrakk> \<Longrightarrow> A \<in> B" by auto

lemma union_empty_eq [simp]: "\<Union>{} = {}" by auto

lemma inter_empty_eq [simp]: "\<Inter>{} = {}" by auto

lemma union_eq_empty_iff: "\<Union>A = {} \<longleftrightarrow> A = {} \<or> A = {{}}"
proof
  assume "\<Union>A = {}"
  show "A = {} \<or> A = {{}}"
  proof (rule or_if_not_imp)
    assume "A \<noteq> {}"
    then obtain x where "x \<in> A" by auto
    from \<open>\<Union>A = {}\<close> have [simp]: "\<And>x. x \<in> A \<Longrightarrow> x = {}" by auto
    with \<open>x \<in> A\<close> have "x = {}" by simp
    with \<open>x \<in> A\<close> have [simp]: "{} \<in> A" by simp
    show "A = {{}}" by auto
  qed
qed auto

lemma union_eq_empty_iff': "\<Union>A = {} \<longleftrightarrow> (\<forall>B : A. B = {})" by auto

lemma union_singleton_eq [simp]: "\<Union>{b} = b" by auto

lemma inter_singleton_eq [simp]: "\<Inter>{b} = b" by auto

lemma subset_union_if_mem: "B \<in> A \<Longrightarrow> B \<subseteq> \<Union>A" by blast

lemma inter_subset_if_mem: "B \<in> A \<Longrightarrow> \<Inter>A \<subseteq> B" by blast

lemma union_subset_iff: "\<Union>A \<subseteq> C \<longleftrightarrow> (\<forall>x : A. x \<subseteq> C)" by blast

lemma subset_inter_iff_all_mem_subset_if_ne_empty:
  "A \<noteq> {} \<Longrightarrow> C \<subseteq> \<Inter>A \<longleftrightarrow> (\<forall>x : A. C \<subseteq> x)"
  by blast

lemma union_subset_if_all_mem_subset: "(\<And>x. x \<in> A \<Longrightarrow> x \<subseteq> C) \<Longrightarrow> \<Union>A \<subseteq> C" by blast

lemma subset_inter_if_all_mem_subset_if_ne_empty:
  "\<lbrakk>A \<noteq> {}; \<And>x. x \<in> A \<Longrightarrow> C \<subseteq> x\<rbrakk> \<Longrightarrow> C \<subseteq> \<Inter>A"
  using subset_inter_iff_all_mem_subset_if_ne_empty by auto

lemma mono_subset_subset_union: "((\<subseteq>) \<Rightarrow> (\<subseteq>)) union" by auto

lemma antimono_inter: "A \<noteq> {} \<Longrightarrow> A \<subseteq> A' \<Longrightarrow> \<Inter>A' \<subseteq> \<Inter>A"
  by auto


subsection \<open>Indexed Union and Intersection:\<close>

open_bundle hotg_idx_union_inter_syntax
begin
syntax
  "_idx_union" :: \<open>[pttrn, set, set \<Rightarrow> set] => set\<close> ("(3\<Union>_ \<in> _./ _)" [0, 0, 10] 10)
  "_idx_inter" :: \<open>[pttrn, set, set \<Rightarrow> set] => set\<close> ("(3\<Inter>_ \<in> _./ _)" [0, 0, 10] 10)
end
translations
  "\<Union>x \<in> A. P" \<rightleftharpoons> "\<Union>{P | x \<in> A}"
  "\<Inter>x \<in> A. P" \<rightleftharpoons> "\<Inter>{P | x \<in> A}"


lemma mem_idx_unionE [elim!]:
  assumes "b \<in> (\<Union>x \<in> A. B x)"
  obtains x where "x \<in> A" and "b \<in> B x"
  using assms by blast

lemma mem_idx_interD:
  assumes "b \<in> (\<Inter>x \<in> A. B x)" and "x \<in> A"
  shows "b \<in> B x"
  using assms by blast

lemma idx_union_cong [cong]:
  "\<lbrakk>A = B; \<And>x. x \<in> B \<Longrightarrow> C x = D x\<rbrakk> \<Longrightarrow> (\<Union>x \<in> A. C x) = (\<Union>x \<in> B. D x)"
  by simp

lemma idx_inter_cong [cong]:
  "\<lbrakk>A = B; \<And>x. x \<in> B \<Longrightarrow> C x = D x\<rbrakk> \<Longrightarrow> (\<Inter>x \<in> A. C x) = (\<Inter>x \<in> B. D x)"
  by simp

lemma idx_union_const_eq_if_ne_empty: "A \<noteq> {} \<Longrightarrow> (\<Union>x \<in> A. B) = B"
  by (rule eqI) auto

lemma idx_inter_const_eq_if_ne_empty: "A \<noteq> {} \<Longrightarrow> (\<Inter>x \<in> A. B) = B"
  by (rule eqI) auto

lemma idx_union_empty_dom_eq [simp]: "(\<Union>x \<in> {}. B x) = {}" by auto

lemma idx_inter_empty_dom_eq [simp]: "(\<Inter>x \<in> {}. B x) = {}" by auto

lemma idx_union_empty_eq [simp]: "(\<Union>x \<in> A. {}) = {}" by auto

lemma idx_inter_empty_eq [simp]: "(\<Inter>x \<in> A. {}) = {}" by blast

lemma idx_union_eq_union [simp]: "(\<Union>x \<in> A. x) = \<Union>A" by auto

lemma idx_inter_eq_inter [simp]: "(\<Inter>x \<in> A. x) = \<Inter>A" by auto

lemma idx_union_subset_iff: "(\<Union>x \<in> A. B x) \<subseteq> C \<longleftrightarrow> (\<forall>x : A. B x \<subseteq> C)" by blast

lemma subset_idx_inter_iff_if_ne_empty:
  "C \<noteq> {} \<Longrightarrow> C \<subseteq> (\<Inter>x \<in> A. B x) \<longleftrightarrow> (A \<noteq> {} \<and> (\<forall>x : A. C \<subseteq> B x))"
  by blast

lemma subset_idx_union_if_mem: "x \<in> A \<Longrightarrow> B x \<subseteq> (\<Union>x \<in> A. B x)" by blast

lemma idx_inter_subset_if_mem: "x \<in> A \<Longrightarrow> (\<Inter>x \<in> A. B x) \<subseteq> B x" by blast

lemma idx_union_subset_if_all_mem_app_subset:
  "(\<And>x. x \<in> A \<Longrightarrow> B x \<subseteq> C) \<Longrightarrow> (\<Union>x \<in> A. B x) \<subseteq> C"
  by blast

lemma subset_idx_inter_if_all_mem_subset_app_if_ne_empty:
  "\<lbrakk>A \<noteq> {}; \<And>x. x \<in> A \<Longrightarrow> C \<subseteq> B x\<rbrakk> \<Longrightarrow> C \<subseteq> (\<Inter>x \<in> A. B x)"
  by blast

lemma idx_union_singleton_eq [simp]: "(\<Union>x \<in> A. {x}) = A"
  by (rule eqI) auto

lemma idx_union_flatten [simp]:
  "(\<Union>x \<in> (\<Union>y \<in> A. B y). C x) = (\<Union>y \<in> A. \<Union>x \<in> B y. C x)"
  by (rule eqI) auto

lemma idx_union_const [simp]: "(\<Union>y \<in> A. c) = (if A = {} then {} else c)"
  by (rule eqI) (auto split: if_splits)

lemma idx_inter_const [simp]: "(\<Inter>y \<in> A. c) = (if A = {} then {} else c)"
  by (rule eqI) (auto split: if_splits)

lemma idx_union_repl_eq_idx_union [simp]: "(\<Union>y \<in> {f x | x \<in> A}. B y) = (\<Union>x \<in> A. B (f x))"
  by (rule eqI) auto

lemma idx_inter_repl_eq_idx_inter [simp]: "(\<Inter>x \<in> {f x | x \<in> A}. B x) = (\<Inter>a \<in> A. B (f a))"
  by blast

lemma idx_union_repl_eq_repl_union: "(\<Union>Y \<in> X. {f x | x \<in> Y}) = {f x | x \<in> \<Union>X}"
  by auto

lemma repl_inter_subset_idx_inter_repl: "{f x | x \<in> \<Inter>X} \<subseteq> (\<Inter>Y \<in> X. {f x | x \<in> Y})"
  by auto

lemma idx_inter_union_eq_idx_inter_idx_inter:
  "{} \<notin> A \<Longrightarrow> (\<Inter>x \<in> \<Union>A. B x) = (\<Inter>y \<in> A. \<Inter>x \<in> y. B x)"
  by (fastforce iff: union_eq_empty_iff)

lemma idx_inter_idx_union_eq_idx_inter_idx_inter:
  assumes "\<And>x. (x \<in> A \<Longrightarrow> B x \<noteq> {})"
  shows "(\<Inter>z \<in> (\<Union>x \<in> A. B x). C z) = (\<Inter>x \<in> A. \<Inter>z \<in> B x. C z)"
proof (rule eqI)
  fix x assume "x \<in> (\<Inter>z \<in> (\<Union>x \<in> A. B x). C z)"
  with assms show "x \<in> (\<Inter>x \<in> A. \<Inter>z \<in> B x. C z)" by fastforce
next
  fix x assume x_mem: "x \<in> (\<Inter>x \<in> A. \<Inter>z \<in> B x. C z)"
  then have "A \<noteq> {}" by auto
  then obtain y where "y \<in> A" by auto
  with assms have "B y \<noteq> {}" by auto
  with \<open>y \<in> A\<close> have "{B x | x \<in> A} \<noteq> {{}}" by auto
  with x_mem show "x \<in> (\<Inter>z \<in> (\<Union>x \<in> A. B x). C z)" by (fastforce simp: union_eq_empty_iff)
qed

lemma mono_idx_union:
  assumes "A \<subseteq> A'"
  and "\<And>x. x \<in> A \<Longrightarrow> B x \<subseteq> B' x"
  shows "(\<Union>x \<in> A. B x) \<subseteq> (\<Union>x \<in> A'. B' x)"
  using assms by blast

lemma mono_antimono_idx_inter:
  assumes "A \<noteq> {}"
  and "A \<subseteq> A'"
  and "\<And>x. x \<in> A \<Longrightarrow> B' x \<subseteq> B x"
  shows "(\<Inter>x \<in> A'. B' x) \<subseteq> (\<Inter>x \<in> A. B x)"
  using assms by (intro subsetI) fastforce


subsection \<open>Binary Union and Intersection\<close>

definition "bin_union A B \<equiv> \<Union>{A, B}"

open_bundle hotg_bin_union_syntax begin notation bin_union (infixl "\<union>" 70) end

definition "bin_inter A B \<equiv> \<Inter>{A, B}"

open_bundle hotg_bin_inter_syntax begin notation bin_inter (infixl "\<inter>" 70) end

lemma mem_bin_union_iff [iff]: "x \<in> A \<union> B \<longleftrightarrow> x \<in> A \<or> x \<in> B"
  unfolding bin_union_def by auto

lemma mem_bin_inter_iff [iff]: "x \<in> A \<inter> B \<longleftrightarrow> x \<in> A \<and> x \<in> B"
  unfolding bin_inter_def by auto


definition "disjoint A B \<equiv> A \<inter> B = {}"

lemma disjoint_iff_all_not_mem [iff]: "disjoint A B \<longleftrightarrow> (\<forall>a : A. a \<notin> B)"
  unfolding disjoint_def by auto

lemma disjoint_iff_bin_inter_eq_empty: "disjoint A B \<longleftrightarrow> A \<inter> B = {}"
  by auto

lemma disjoint_union_iff: "disjoint (\<Union>C) A \<longleftrightarrow> (\<forall>B : C. disjoint B A)"
  by blast

paragraph\<open>Binary Union\<close>

lemma mem_bin_union_if_mem_left [elim?]: "c \<in> A \<Longrightarrow> c \<in> A \<union> B"
  by simp

lemma mem_bin_union_if_mem_right [elim?]: "c \<in> B \<Longrightarrow> c \<in> A \<union> B"
  by simp

lemma bin_unionE [elim!]:
  assumes "c \<in> A \<union> B"
  obtains (mem_left) "c \<in> A" | (mem_right) "c \<in> B"
  using assms by auto

(*stronger version of above rule*)
lemma bin_unionE' [elim!]:
  assumes "c \<in> A \<union> B"
  obtains (mem_left) "c \<in> A" | (mem_right) "c \<in> B" and "c \<notin> A"
  using assms by auto

(*LP: Classical introduction rule: no commitment to A vs B*)
lemma mem_bin_union_if_mem_if_not_mem: "(c \<notin> B \<Longrightarrow> c \<in> A) \<Longrightarrow> c \<in> A \<union> B"
  by auto

lemma bin_union_comm: "A \<union> B = B \<union> A"
  by (rule eqI) auto

lemma bin_union_assoc: "(A \<union> B) \<union> C = A \<union> (B \<union> C)"
  by (rule eqI) auto

lemma bin_union_comm_left: "A \<union> (B \<union> C) = B \<union> (A \<union> C)" by auto

lemmas bin_union_AC_rules = bin_union_comm bin_union_assoc bin_union_comm_left

lemma empty_bin_union_eq [simp]: "{} \<union> A = A"
  by (rule eqI) auto

lemma bin_union_empty_eq [simp]: "A \<union> {} = A"
  by (rule eqI) auto

lemma singleton_bin_union_absorb [simp]: "a \<in> A \<Longrightarrow> {a} \<union> A = A"
  by auto

lemma singleton_bin_union_eq_insert[simp]: "{x} \<union> A = insert x A"
  by (rule eqI) auto

lemma bin_union_singleton_eq_insert[simp]: "A \<union> {x} = insert x A"
  using singleton_bin_union_eq_insert by (subst bin_union_comm)

lemma mem_singleton_bin_union [iff]: "a \<in> {a} \<union> B" by auto

lemma mem_bin_union_singleton [iff]: "b \<in> A \<union> {b}" by auto

lemma bin_union_subset_iff [iff]: "A \<union> B \<subseteq> C \<longleftrightarrow> A \<subseteq> C \<and> B \<subseteq> C"
  by blast

lemma bin_union_eq_left_iff [iff]: "A \<union> B = A \<longleftrightarrow> B \<subseteq> A"
  using mem_bin_union_if_mem_right[of _ B A] by (auto simp only: sym[of "A \<union> B"])

lemma bin_union_eq_right_iff [iff]: "A \<union> B = B \<longleftrightarrow> A \<subseteq> B"
  by (subst bin_union_comm) (fact bin_union_eq_left_iff)

lemma subset_bin_union_left: "A \<subseteq> A \<union> B" by blast

lemma subset_bin_union_right: "B \<subseteq> A \<union> B"
  by (subst bin_union_comm) (fact subset_bin_union_left)

lemma bin_union_subset_if_subset_if_subset: "\<lbrakk>A \<subseteq> C; B \<subseteq> C\<rbrakk> \<Longrightarrow> A \<union> B \<subseteq> C"
  by blast

lemma bin_union_self_eq_self [simp]: "A \<union> A = A"
  by (rule eqI) auto

lemma bin_union_absorb: "A \<union> (A \<union> B) = A \<union> B"
  by (rule eqI) auto

lemma bin_union_eq_right_if_subset: "A \<subseteq> B \<Longrightarrow> A \<union> B = B"
  by (rule eqI) auto

lemma bin_union_eq_left_if_subset: "B \<subseteq> A \<Longrightarrow> A \<union> B = A"
  by (rule eqI) auto

lemma bin_union_subset_bin_union_if_subset: "B \<subseteq> C \<Longrightarrow> A \<union> B \<subseteq> A \<union> C"
  by auto

lemma bin_union_subset_bin_union_if_subset': "A \<subseteq> B \<Longrightarrow> A \<union> C \<subseteq> B \<union> C"
  by auto

lemma bin_union_eq_empty_iff [iff]: "(A \<union> B = {}) \<longleftrightarrow> (A = {} \<and> B = {})"
  by auto

lemma mono_subset_bin_union: "((\<subseteq>) \<Rightarrow> (\<subseteq>) \<Rrightarrow> (\<subseteq>)) (\<union>)" by blast

lemma union_insert_eq_bin_union_union [simp]: "\<Union>(insert X Y) = X \<union> \<Union>Y" by auto

lemma mem_of_bin_union_eq_mem_of_sup_mem_of [set_to_HOL_simp]:
  "mem_of (A \<union> B) = mem_of A \<squnion> mem_of B"
  by auto


paragraph \<open>Binary Intersection\<close>

lemma mem_bin_inter_if_mem_if_mem [intro!]: "\<lbrakk>c \<in> A; c \<in> B\<rbrakk> \<Longrightarrow> c \<in> A \<inter> B"
  by simp

lemma mem_bin_inter_if_mem_left: "c \<in> A \<inter> B \<Longrightarrow> c \<in> A"
  by simp

lemma mem_bin_inter_if_mem_right: "c \<in> A \<inter> B \<Longrightarrow> c \<in> B"
  by simp

lemma mem_bin_interE [elim!]:
  assumes "c \<in> A \<inter> B"
  obtains "c \<in> A" and "c \<in> B"
  using assms by simp

lemma bin_inter_comm: "A \<inter> B = B \<inter> A"
  by auto

lemma bin_inter_assoc: "(A \<inter> B) \<inter> C = A \<inter> (B \<inter> C)"
  by auto

lemma bin_inter_comm_left: "A \<inter> (B \<inter> C) = B \<inter> (A \<inter> C)"
  by auto

lemmas bin_inter_AC_rules = bin_inter_comm bin_inter_assoc bin_inter_comm_left

lemma empty_bin_inter_eq_empty [simp]: "{} \<inter> B = {}"
  by auto

lemma bin_inter_empty_eq_empty [simp]: "A \<inter> {} = {}"
  by auto

lemma bin_inter_subset_iff [iff]: "C \<subseteq> A \<inter> B \<longleftrightarrow> C \<subseteq> A \<and> C \<subseteq> B"
  by blast

lemma bin_inter_subset_left [iff]: "A \<inter> B \<subseteq> A"
  by blast

lemma bin_inter_subset_right [iff]: "A \<inter> B \<subseteq> B"
  by blast

lemma subset_bin_inter_if_subset_if_subset: "\<lbrakk>C \<subseteq> A; C \<subseteq> B\<rbrakk> \<Longrightarrow> C \<subseteq> A \<inter> B"
  by blast

lemma bin_inter_self_eq_self [simp]: "A \<inter> A = A"
  by (rule eqI) auto

lemma bin_inter_absorb [simp]: "A \<inter> (A \<inter> B) = A \<inter> B"
  by (rule eqI) auto

lemma bin_inter_eq_right_if_subset: "B \<subseteq> A \<Longrightarrow> A \<inter> B = B"
  by (rule eqI) auto

lemma bin_inter_eq_left_if_subset: "A \<subseteq> B \<Longrightarrow> A \<inter> B = A"
  by (subst bin_inter_comm) (fact bin_inter_eq_right_if_subset)

lemma bin_inter_bin_union_distrib: "(A \<inter> B) \<union> C = (A \<union> C) \<inter> (B \<union> C)"
  by (rule eqI) auto

lemma bin_inter_bin_union_distrib': "A \<inter> (B \<union> C) = (A \<inter> B) \<union> (A \<inter> C)"
  by (rule eqI) auto

lemma bin_union_bin_inter_distrib: "(A \<union> B) \<inter> C = (A \<inter> C) \<union> (B \<inter> C)"
  by (rule eqI) auto

lemma bin_union_bin_inter_distrib': "A \<union> (B \<inter> C) = (A \<union> B) \<inter> (A \<union> C)"
  by (rule eqI) auto

lemma bin_inter_eq_left_iff_subset: "A \<subseteq> B \<longleftrightarrow> A \<inter> B = A"
  by auto

lemma bin_inter_eq_right_iff_subset: "A \<subseteq> B \<longleftrightarrow> B \<inter> A = A"
  by auto

lemma bin_inter_bin_union_assoc_iff:
  "(A \<inter> B) \<union> C = A \<inter> (B \<union> C) \<longleftrightarrow> C \<subseteq> A"
  by auto

lemma bin_inter_bin_union_swap3:
 "(A \<inter> B) \<union> (B \<inter> C) \<union> (C \<inter> A) = (A \<union> B) \<inter> (B \<union> C) \<inter> (C \<union> A)"
  by auto

lemma mono_subset_bin_inter: "((\<subseteq>) \<Rightarrow> (\<subseteq>) \<Rrightarrow> (\<subseteq>)) (\<inter>)" by fast

lemma inter_insert_eq_bin_inter_inter [simp]: "Y \<noteq> {} \<Longrightarrow> \<Inter>(insert X Y) = X \<inter> \<Inter>Y" by auto

lemma mem_of_bin_inter_eq_mem_of_inf_mem_of [set_to_HOL_simp]:
  "mem_of (A \<inter> B) = mem_of A \<sqinter> mem_of B"
  by auto


paragraph \<open>Comprehension\<close>

lemma collect_eq_bin_inter [simp]: "{a \<in> A | a \<in> A'} = A \<inter> A'" by auto

lemma collect_bin_union_eq:
  "{x \<in> A \<union> B | P x} = {x \<in> A | P x} \<union> {x \<in> B | P x}"
  by (rule eqI) auto

lemma collect_bin_inter_eq:
  "{x \<in> A \<inter> B | P x} = {x \<in> A | P x} \<inter> {x \<in> B | P x}"
  by (rule eqI) auto

lemma bin_inter_collect_absorb [simp]:
  "A \<inter> {x \<in> A | P x} = {x \<in> A | P x}"
  by (rule eqI) auto

lemma collect_idx_union_eq_union_collect [simp]:
  "{y \<in> (\<Union>x \<in> A. B x) | P y} = (\<Union>x \<in> A. {y \<in> B x | P y})"
  by (rule eqI) auto

lemma bin_inter_collect_left_eq_collect:
  "{x \<in> A | P x} \<inter> B = {x \<in> A \<inter> B | P x}"
  by (rule eqI) auto

lemma bin_inter_collect_right_eq_collect:
  "A \<inter> {x \<in> B | P x} = {x \<in> A \<inter> B | P x}"
  by (rule eqI) auto

lemma collect_and_eq_inter_collect:
  "{x \<in> A | P x \<and> Q x} = {x \<in> A | P x} \<inter> {x \<in> A | Q x}"
  by (rule eqI) auto

lemma collect_or_eq_union_collect:
  "{x \<in> A | P x \<or> Q x} = {x \<in> A | P x} \<union> {x \<in> A | Q x}"
  by (rule eqI) auto


lemma union_bin_union_eq_bin_union_union: "\<Union>(A \<union> B) = \<Union>A \<union> \<Union>B"
  by (rule eqI) auto

lemma union_bin_inter_subset_bin_inter_union: "\<Union>(A \<inter> B) \<subseteq> \<Union>A \<inter> \<Union>B"
  by blast

lemma subset_idx_union_iff_eq:
  "A \<subseteq> (\<Union>i \<in> I. B i) \<longleftrightarrow> A = (\<Union>i \<in> I. A \<inter> B i)" (is "A \<subseteq> ?lhs_union \<longleftrightarrow> A = ?rhs_union")
proof
  assume A_eq: "A = ?rhs_union"
  show "A \<subseteq> ?lhs_union"
  proof (rule subsetI)
    fix a assume "a \<in> A"
    with A_eq have "a \<in> ?rhs_union" by simp
    then obtain x where "x \<in> I" and "a \<in> A \<inter> B x" by auto
    then show "a \<in> ?lhs_union" by auto
  qed
qed (auto 5 0 intro!: eqI)

lemma bin_inter_union_eq_idx_union_inter: "\<Union>B \<inter> A = (\<Union>C \<in> B. C \<inter> A)"
  by (rule eqI) auto

lemma bin_union_inter_subset_inter_bin_inter:
  "\<lbrakk>z \<in> A; z \<in> B\<rbrakk> \<Longrightarrow> \<Inter>A \<union> \<Inter>B \<subseteq> \<Inter>(A \<inter> B)"
  by blast

lemma inter_bin_union_eq_bin_inter_inter:
  "\<lbrakk>A \<noteq> {}; B \<noteq> {}\<rbrakk> \<Longrightarrow> \<Inter>(A \<union> B) = \<Inter>A \<inter> \<Inter>B"
  by (rule eqI) auto

lemma idx_union_insert_dom_eq_bin_union_idx_union: "(\<Union>i \<in> insert A B. C i) = C A \<union> (\<Union>i \<in> B. C i)"
  by auto

lemma idx_inter_insert_dom_eq_bin_inter_idx_inter:
  assumes "B \<noteq> {}"
  shows "(\<Inter>i \<in> insert A B. C i) = C A \<inter> (\<Inter>i \<in> B. C i)"
  using assms by (intro eqI) auto

lemma idx_union_bin_union_dom_eq_bin_union_idx_union:
  "(\<Union>i \<in> A \<union> B. C i) = (\<Union>i \<in> A. C i) \<union> (\<Union>i \<in> B. C i)"
  by (rule eqI) auto

lemma idx_inter_bin_inter_dom_eq_bin_inter_idx_inter:
  "(\<Inter>i \<in> I \<union> J. A i) = (
    if I = {} then \<Inter>j \<in> J. A j
    else if J = {} then \<Inter>i \<in> I. A i
    else (\<Inter>i \<in> I. A i) \<inter> (\<Inter>j \<in> J. A j)
  )"
  by (rule eqI) (auto split: if_splits)

(*Halmos, Naive Set Theory, page 35*)
lemma idx_union_bin_inter_eq_bin_inter_idx_union [simp]:
  "(\<Union>i \<in> I. A \<inter> B i) = A \<inter> (\<Union>i \<in> I. B i)"
  by (rule eqI) auto

lemma idx_inter_bin_union_eq_bin_union_idx_inter [simp]:
  "I \<noteq> {} \<Longrightarrow> (\<Inter>i \<in> I. A \<union> B i) = A \<union> (\<Inter>i \<in> I. B i)"
  by (rule eqI) auto

lemma idx_union_idx_union_bin_inter_eq_bin_inter_idx_union [simp]:
  "(\<Union>i \<in> I. \<Union>j \<in> J. A i \<inter> B j) = (\<Union>i \<in> I. A i) \<inter> (\<Union>j \<in> J. B j)"
  by (rule eqI) auto

lemma idx_inter_idx_inter_bin_union_eq_bin_union_idx_inter [simp]:
  "\<lbrakk>I \<noteq> {}; J \<noteq> {}\<rbrakk> \<Longrightarrow>
    (\<Inter>i \<in> I. \<Inter>j \<in> J. A i \<union> B j) = (\<Inter>i \<in> I. A i) \<union> (\<Inter>j \<in> J. B j)"
  by (rule eqI) (auto elim!: ballE)

lemma idx_union_bin_union_eq_bin_union_idx_union [simp]:
  "(\<Union>i \<in> I. A i \<union> B i) = (\<Union>i \<in> I. A i) \<union> (\<Union>i \<in> I. B i)"
  by (rule eqI) auto

lemma idx_inter_bin_inter_eq_bin_inter_idx_inter [simp]:
  "I \<noteq> {} \<Longrightarrow> (\<Inter>i \<in> I. A i \<inter> B i) = (\<Inter>i \<in> I. A i) \<inter> (\<Inter>i \<in> I. B i)"
  by (rule eqI) auto

lemma idx_union_bin_inter_subset_bin_inter_idx_union:
  "(\<Union>z \<in> I \<inter> J. A z) \<subseteq> (\<Union>z \<in> I. A z) \<inter> (\<Union>z \<in> J. A z)"
  by blast

lemma idx_union_union_eq_idx_union_idx_union [simp]: "(\<Union>x \<in> \<Union>X. f x) = (\<Union>x \<in> X. \<Union>y \<in> x. f y)"
  by auto


end