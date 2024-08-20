theory Lists
  imports HOTG_Basics HOTG_Functions

begin

locale list =
  fixes nil :: "set" and cons :: "set \<Rightarrow> set \<Rightarrow> set"
  and list_rec :: "set \<Rightarrow> (set \<Rightarrow> set \<Rightarrow> set \<Rightarrow> set) \<Rightarrow> set \<Rightarrow> set"
  assumes nil_ne_cons[iff]: "nil \<noteq> cons x xs"
  and cons_inj[iff]: "cons x xs = cons y ys \<longleftrightarrow> (x = y \<and> xs = ys)"
  and list_rec_nil: "list_rec n c nil = n"
  and list_rec_cons: "list_rec n c (cons x xs) = c x xs (list_rec n c xs)"
  
begin

definition "append xs ys \<equiv> list_rec ys (\<lambda>x _. cons x) xs"

lemma nil_append_eq [simp]: "append nil ys = ys"
  by (simp add: list_rec_nil append_def)

lemma cons_append_eq [simp]:
  "append (cons x xs) ys = cons x (append xs ys)"
  by (simp add: append_def list_rec_cons)

definition "rev \<equiv> list_rec nil (\<lambda>x _ acc. append acc (cons x nil))"

lemma rev_nil_eq [simp]: "rev nil = nil"
  by (simp add: rev_def list_rec_nil)

lemma rev_cons_eq [simp]: "rev (cons x xs) = append (rev xs) (cons x nil)"
  by (simp add: rev_def list_rec_cons)
end
end