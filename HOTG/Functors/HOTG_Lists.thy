theory HOTG_Lists
  imports HOTG_Functions_Monotone
begin

axiomatization
  nil :: "set" 
  and cons :: "set \<Rightarrow> set \<Rightarrow> set"
  and list_rec :: "'a \<Rightarrow> (set \<Rightarrow> set \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> set \<Rightarrow> 'a"
  and list :: "set \<Rightarrow> set \<Rightarrow> bool"
  where nil_ne_cons[iff]: "nil \<noteq> cons x xs"
  and cons_inj[iff]: "cons x xs = cons y ys \<longleftrightarrow> (x = y \<and> xs = ys)"
  and nil_type: "\<And>A. (list A) nil"
  and cons_type: "\<And>A. (mem_of A \<Rightarrow> list A \<Rightarrow> list A) cons"
  and list_rec_nil: "\<And>n c. list_rec n c nil = n"
  and list_rec_cons: "\<And>n c x xs. list_rec n c (cons x xs) = c x xs (list_rec n c xs)"
  and list_rec_type: "\<And>(P :: 'a \<Rightarrow> bool) A. 
    (P \<Rightarrow> (mem_of A \<Rightarrow> list A \<Rightarrow> P \<Rightarrow> P) \<Rightarrow> list A \<Rightarrow> P) list_rec"
  and list_induct[case_names nil cons, induct type: set, consumes 1]: "\<And>A P. list A xs \<Longrightarrow> P nil \<Longrightarrow>
    (\<And>x xs. x \<in> A \<Longrightarrow> list A xs \<Longrightarrow> P xs \<Longrightarrow>  P (cons x xs)) \<Longrightarrow> P xs"

definition "append xs ys \<equiv> list_rec ys (\<lambda>x _. cons x) xs"

lemma nil_append_eq [simp]: "append nil ys = ys"
  by (simp add: list_rec_nil append_def)

lemma cons_append_eq [simp]:
  "append (cons x xs) ys = cons x (append xs ys)"
  by (simp add: append_def list_rec_cons)

lemma append_type: "(list A \<Rightarrow> list A \<Rightarrow> list A) append"
proof -
  have "(mem_of A \<Rightarrow> list A \<Rightarrow> list A \<Rightarrow> list A) (\<lambda>x _. cons x)"
    using cons_type by blast
  with list_rec_type[where ?P="list A"] show ?thesis unfolding append_def by blast
qed

lemma append_assoc [simp]:
  assumes "list A xs" "list A ys" "list A zs"
  shows  "append (append xs ys) zs = append xs (append ys zs)"
  using assms by (induction xs rule: list_induct) auto

definition "rev \<equiv> list_rec nil (\<lambda>x _ acc. append acc (cons x nil))"

lemma rev_nil_eq [simp]: "rev nil = nil"
  by (simp add: rev_def list_rec_nil)

lemma rev_cons_eq [simp]: "rev (cons x xs) = append (rev xs) (cons x nil)"
  by (simp add: rev_def list_rec_cons)

lemma rev_type: "(list A \<Rightarrow> list A) rev"
proof -
  have "(mem_of A \<Rightarrow> list A \<Rightarrow> list A \<Rightarrow> list A) (\<lambda>x _ acc. append acc (cons x nil))"
    using append_type cons_type nil_type by (intro mono_wrt_predI) (blast dest!: mono_wrt_predD) 
  with list_rec_type[where ?P="list A"] nil_type show ?thesis unfolding rev_def 
    by blast
qed

definition "map f \<equiv> list_rec nil (\<lambda>x _. cons (f x))"

lemma map_type: 
  assumes "(mem_of A \<Rightarrow> mem_of B) f"
  shows "(list A \<Rightarrow> list B) (map f)"
proof -
  have "(mem_of A \<Rightarrow> list A \<Rightarrow> list B \<Rightarrow> list B) (\<lambda>x _. cons (f x))"
    using cons_type assms by blast
  with list_rec_type[where ?P="list B"] nil_type show ?thesis unfolding map_def by blast
qed

lemma map_nil_eq[simp]: "map f nil = nil"
  by (simp add: map_def list_rec_nil)

lemma map_cons_eq[simp]: "map f (cons x xs) = cons (f x) (map f xs)"
  by (simp add: map_def list_rec_cons)


end