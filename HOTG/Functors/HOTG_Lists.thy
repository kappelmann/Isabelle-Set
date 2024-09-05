theory HOTG_Lists
  imports HOTG_Functions_Monotone HOTG_Ordinals_Omega ML_Unification.Unification_Attributes
begin

axiomatization
  nil :: "set" 
  and cons :: "set \<Rightarrow> set \<Rightarrow> set"
  and list_rec :: "'a \<Rightarrow> (set \<Rightarrow> set \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> set \<Rightarrow> 'a"
  and list :: "set \<Rightarrow> set \<Rightarrow> bool"
  where nil_ne_cons[iff]: "\<And>x xs. nil \<noteq> cons x xs"
  and cons_inj[iff]: "\<And>x xs y ys. cons x xs = cons y ys \<longleftrightarrow> (x = y \<and> xs = ys)"
  and nil_type: "\<And>A. (list A) nil"
  and cons_type: "\<And>A. (mem_of A \<Rightarrow> list A \<Rightarrow> list A) cons"
  and list_rec_nil: "\<And>n c. list_rec n c nil = n"
  and list_rec_cons: "\<And>n c x xs. list_rec n c (cons x xs) = c x xs (list_rec n c xs)"
  and list_rec_type: "\<And>(P :: 'a \<Rightarrow> bool) A. 
    (P \<Rightarrow> (mem_of A \<Rightarrow> list A \<Rightarrow> P \<Rightarrow> P) \<Rightarrow> list A \<Rightarrow> P) list_rec"
  and list_induct[case_names nil cons, induct type: set, consumes 1]: "\<And>A P xs. list A xs \<Longrightarrow> P nil \<Longrightarrow>
    (\<And>x xs. x \<in> A \<Longrightarrow> list A xs \<Longrightarrow> P xs \<Longrightarrow>  P (cons x xs)) \<Longrightarrow> P xs"

unbundle no_HOL_groups_syntax no_HOL_ascii_syntax no_HOL_order_syntax

definition "length \<equiv> list_rec 0 (\<lambda>_ _. succ)"

lemma length_nil_eq[simp]: "length nil = 0"
  unfolding length_def by (fact list_rec_nil)

lemma length_cons_eq_succ[simp]: "length (cons x xs) = succ (length xs)"
  unfolding length_def using list_rec_cons[of _ "\<lambda>_ _. succ"] by simp

lemma length_type: "(list A \<Rightarrow> mem_of \<omega>) length"
proof-
  have T1: "(mem_of A \<Rightarrow> list A \<Rightarrow> mem_of \<omega> \<Rightarrow> mem_of \<omega>) (\<lambda> _ _ . succ)" 
    using succ_mem_omega_if_mem by blast
  have T2: "mem_of \<omega> 0" by auto
  from list_rec_type[THEN mono_wrt_predD, THEN mono_wrt_predD, OF T2 T1]
  show ?thesis using list_rec_type unfolding length_def by blast
qed

definition "is_nil = list_rec True (\<lambda>_ _ _. False)"

lemma "is_nil nil"
  unfolding is_nil_def using list_rec_nil[of True] by blast

lemma "\<And>x xs. \<not>is_nil (cons x xs)"
  unfolding is_nil_def using list_rec_cons[of True "(\<lambda>_ _ _. False)"] by blast

definition "is_cons = list_rec False (\<lambda>_ _ _. True)"

definition "head = list_rec undefined (\<lambda>x _ _. x)"

lemma head_type: "(list A \<Rightarrow> mem_of A) head"
proof-
  have "(mem_of A \<Rightarrow> list A \<Rightarrow> mem_of A \<Rightarrow> mem_of A) (\<lambda>x _ _. x)" by blast
  with list_rec_type[where ?P="list A"] show ?thesis unfolding head_def sorry (*needs: mem_of A undefined*)
qed

definition "tail = list_rec undefined (\<lambda>_ xs _. xs)"

lemma tail_type: "(list A \<Rightarrow> list A) tail"
proof-
  have "(mem_of A \<Rightarrow> list A \<Rightarrow> list A \<Rightarrow> list A) (\<lambda>_ xs _. xs)" by blast
  with list_rec_type[where ?P="list A"] show ?thesis unfolding tail_def sorry (*needs: list A undefined*)
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

definition "index_list \<equiv> list_rec nil (\<lambda>x _ xs. cons \<langle>0,x\<rangle> (map (\<lambda>p. \<langle>succ (fst p), snd p\<rangle>) xs))"

lemma index_list_type: "(list A \<Rightarrow> list (\<omega> \<times> A)) index_list"
proof-
  have "(mem_of (\<omega> \<times> A) \<Rightarrow> mem_of (\<omega> \<times> A)) (\<lambda>p. \<langle>succ (fst p), snd p\<rangle>)" by auto
  then have "(list (\<omega> \<times> A) \<Rightarrow> list (\<omega> \<times> A)) (map (\<lambda>p. \<langle>succ (fst p), snd p\<rangle>))" using map_type by auto
  then have "(mem_of A \<Rightarrow> list A \<Rightarrow> list (\<omega> \<times> A) \<Rightarrow> list (\<omega> \<times> A)) (\<lambda>x _ xs. cons \<langle>0,x\<rangle> (map (\<lambda>p. \<langle>succ (fst p), snd p\<rangle>) xs))" using cons_type[of "\<omega> \<times> A"] by fastforce
  with list_rec_type[where ?P="list (\<omega> \<times> A)"] nil_type show ?thesis unfolding index_list_def by auto
qed

definition "nth n xs \<equiv> list_rec undefined (\<lambda>x _ res. (if (fst x = n) then snd x else res)) (index_list xs)"

lemma nth_type: "(mem_of \<omega> \<Rightarrow> list A \<Rightarrow> mem_of A) nth"
  sorry


definition "tuple Ps xs \<equiv> length Ps = length xs \<and> (\<forall>i. 0 \<le> i \<and> i < (length xs) \<longrightarrow> mem_of (nth i Ps) (nth i xs))"

lemma tuple_nil[simp]: "tuple nil nil" 
  unfolding tuple_def by auto

lemma tuple_cons: "x \<in> p \<Longrightarrow> tuple Ps xs \<Longrightarrow> tuple (cons p Ps) (cons x xs)" 
  sorry

definition "replicate n x \<equiv> omega_rec nil (cons x) n"

lemma replicate_zero[simp]: "\<And>x. replicate 0 x = nil" unfolding replicate_def by auto

lemma replicate_type: "(mem_of \<omega> \<Rightarrow> mem_of A \<Rightarrow> list A) replicate"
  sorry

lemma replicate_succ: "n \<in> \<omega> \<Longrightarrow> replicate (succ n) x = cons x (replicate n x)"
  unfolding replicate_def by (rule omega_rec_succ)

lemma replicate_nth: " \<forall>i. 0 \<le> i \<and> i < n \<longrightarrow> nth i (replicate n x) = x"
  sorry

lemma "list P xs = tuple (replicate (length xs) P) xs"
proof
  assume "list P xs"
  then show "tuple (replicate (length xs) P) xs" proof (induction xs rule: list_induct)
    case nil
    then show ?case unfolding tuple_def by auto
  next
    case (cons x xs)
    then have "replicate (length (cons x xs)) P = cons P (replicate (length xs) P)" using replicate_succ length_type by auto
    then show ?case using tuple_cons cons by auto
  qed
next 
  assume "tuple (replicate (length xs) P) xs"
  then have "\<forall> i. 0 \<le> i \<and> i < length xs \<longrightarrow> mem_of P (nth i xs)" using replicate_nth tuple_def by auto
  then show "list P xs" sorry
qed

definition "vector P n xs \<equiv> length xs = n \<and> list P xs"

definition "append xs ys \<equiv> list_rec ys (\<lambda>x _. cons x) xs"

lemma "list A (cons x xs) \<Longrightarrow> mem_of A x \<and> list A xs"
 by (induction "(cons x xs)" rule: list_induct) auto

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


end