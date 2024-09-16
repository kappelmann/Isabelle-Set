theory HOTG_Lists
  imports HOTG_Functions_Monotone HOTG_Ordinals_Omega ML_Unification.Unification_Attributes
begin
term omega_rec
lemma omega_rec_type: "mono_wrt_pred P ((P \<Rightarrow> P :: _ \<Rightarrow> bool) \<Rightarrow> mem_of \<omega> \<Rightarrow> P) omega_rec"
proof (intro mono_wrt_predI)
  fix x f n assume "P x" "(P \<Rightarrow> P :: _ \<Rightarrow> bool) f" "mem_of \<omega> n"
  then have "n \<in> \<omega>" by blast
  then show "P (omega_rec x f n)" proof (induction n)
    case zero
    with \<open>P x\<close> show ?case by auto
  next
    case (succ m)
    with \<open>(P \<Rightarrow> P :: _ \<Rightarrow> bool) f\<close> omega_rec_succ[of m x f] show ?case by auto
  qed
qed


axiomatization
  nil :: "set" 
  and cons :: "set \<Rightarrow> set \<Rightarrow> set"
  and list_rec :: "'a \<Rightarrow> (set \<Rightarrow> set \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> set \<Rightarrow> 'a"
  and list :: "(set \<Rightarrow> bool) \<Rightarrow> set \<Rightarrow> bool"
  where nil_ne_cons[iff]: "\<And>x xs. nil \<noteq> cons x xs"
  and cons_inj[iff]: "\<And>x xs y ys. cons x xs = cons y ys \<longleftrightarrow> (x = y \<and> xs = ys)"
  and nil_type: "\<And>A. (list A) nil"
  and cons_type: "\<And>A. (A \<Rightarrow> list A \<Rightarrow> list A) cons"
  and list_rec_nil: "\<And>n c. list_rec n c nil = n"
  and list_rec_cons: "\<And>n c x xs A. A x \<Longrightarrow> list A xs \<Longrightarrow>  list_rec n c (cons x xs) = c x xs (list_rec n c xs)" (*x xs type*)
  and list_rec_type: "\<And>(P :: 'a \<Rightarrow> bool) A. 
    (P \<Rightarrow> (A \<Rightarrow> list A \<Rightarrow> P \<Rightarrow> P) \<Rightarrow> list A \<Rightarrow> P) list_rec"
  and list_induct[case_names nil cons, induct type: set, consumes 1]: "\<And>A P xs. list A xs \<Longrightarrow> P nil \<Longrightarrow>
    (\<And>x xs. A x \<Longrightarrow> list A xs \<Longrightarrow> P xs \<Longrightarrow>  P (cons x xs)) \<Longrightarrow> P xs"

unbundle no_HOL_groups_syntax no_HOL_ascii_syntax no_HOL_order_syntax

lemma ne_nil_imp_cons: assumes list: "list A xs" 
      and ne_nil:"xs \<noteq> nil"
      obtains y ys where "xs = cons y ys" and "A y" and "list A ys"
  using assms by (induction xs rule: list_induct) auto

lemma list_cons_imp: "list A (cons x xs) \<Longrightarrow> A x \<and> list A xs"
 by (induction "(cons x xs)" rule: list_induct) auto

definition "length \<equiv> list_rec 0 (\<lambda>_ _. succ)"

lemma length_nil_eq[simp]: "length nil = 0"
  unfolding length_def by (fact list_rec_nil)

lemma length_cons_eq_succ[simp]: "A x \<Longrightarrow> list A xs \<Longrightarrow> length (cons x xs) = succ (length xs)"
  unfolding length_def using list_rec_cons[of _ _ _ _ "\<lambda>_ _. succ"] by simp

lemma length_type: "(list A \<Rightarrow> mem_of \<omega>) length"
proof-
  have T1: "(A \<Rightarrow> list A \<Rightarrow> mem_of \<omega> \<Rightarrow> mem_of \<omega>) (\<lambda> _ _ . succ)" 
    using succ_mem_omega_if_mem by blast
  have T2: "mem_of \<omega> 0" by auto
  from list_rec_type[THEN mono_wrt_predD, THEN mono_wrt_predD, OF T2 T1]
  show ?thesis using list_rec_type unfolding length_def by blast
qed

definition "is_nil = list_rec True (\<lambda>_ _ _. False)"

lemma is_nil_nil[simp]: "is_nil nil"
  unfolding is_nil_def using list_rec_nil[of True] by blast

lemma not_is_nil_cons[simp]: "A x \<Longrightarrow> list A xs \<Longrightarrow> \<not>is_nil (cons x xs)"
  unfolding is_nil_def using list_rec_cons[of _ _ _ True "(\<lambda>_ _ _. False)"] by blast

definition "is_cons = list_rec False (\<lambda>_ _ _. True)"

lemma not_is_cons_nil[simp]: "\<not>is_cons nil"
  unfolding is_cons_def using list_rec_nil[of False] by blast

lemma is_cons_cons[simp]: "A x \<Longrightarrow> list A xs \<Longrightarrow> is_cons (cons x xs)"
  unfolding is_cons_def using list_rec_cons[of _ _ _ False "(\<lambda>_ _ _. True)"] by blast

definition "head = list_rec undefined (\<lambda>x _ _. x)"


lemma head_cons[simp]: "A x \<Longrightarrow> list A xs \<Longrightarrow> head (cons x xs) = x" unfolding head_def using list_rec_cons[of _ _ _ undefined "\<lambda>x _ _.x"] by blast

lemma head_type:"((xs : list A | xs \<noteq> nil) \<Rightarrow> A) head"
proof (intro dep_mono_wrt_predI pred_if_if_impI)
  fix xs assume "list A xs" and "xs \<noteq> nil"
  with ne_nil_imp_cons obtain y ys where "xs = cons y ys" "A y" and "list A ys" by blast
  then show "A (head xs)" by auto
qed

definition "tail = list_rec undefined (\<lambda>_ xs _. xs)"

lemma tail_cons[simp]: "A x \<Longrightarrow> list A xs \<Longrightarrow> tail (cons x xs) = xs" unfolding tail_def using list_rec_cons[of _ _ _ undefined "\<lambda>_ xs _. xs"] by auto

lemma tail_type: "((xs : list A | xs \<noteq> nil) \<Rightarrow> list A) tail"
proof (intro dep_mono_wrt_predI pred_if_if_impI)
  fix xs assume "list A xs" and "xs \<noteq> nil"
  with ne_nil_imp_cons obtain y ys where "xs = cons y ys" "A y" and "list A ys" by blast
  then show "list A (tail xs)" by auto
qed

definition "map f \<equiv> list_rec nil (\<lambda>x _. cons (f x))"

lemma map_type: "((A \<Rightarrow> B :: _ \<Rightarrow> bool) \<Rightarrow> list A \<Rightarrow> list B) map"
proof (rule mono_wrt_predI)
  fix f :: "set \<Rightarrow> set" assume "(A \<Rightarrow> B) f"
  then have "(A \<Rightarrow> list A \<Rightarrow> list B \<Rightarrow> list B) (\<lambda>x _. cons (f x))"
    using cons_type by blast
  with list_rec_type[where ?P="list B"] nil_type show "(list A \<Rightarrow> list B) (map f)" 
    unfolding map_def by blast
qed

lemma map_nil_eq[simp]: "map f nil = nil"
  by (simp add: map_def list_rec_nil)

lemma map_cons_eq[simp]: "A x \<Longrightarrow> list A xs \<Longrightarrow> map f (cons x xs) = cons (f x) (map f xs)"
  by (simp add: map_def list_rec_cons)

definition "index_list \<equiv> list_rec nil (\<lambda>x _ xs. cons \<langle>0,x\<rangle> (map (\<lambda>p. \<langle>succ (fst p), snd p\<rangle>) xs))"

lemma index_list_type: "(list A \<Rightarrow> list (mem_of \<omega> \<times> A)) index_list"
proof-
  have "((mem_of \<omega> \<times> A) \<Rightarrow> (mem_of \<omega> \<times> A)) (\<lambda>p. \<langle>succ (fst p), snd p\<rangle>)" by auto
  then have "(list (mem_of \<omega> \<times> A) \<Rightarrow> list (mem_of \<omega> \<times> A)) (map (\<lambda>p. \<langle>succ (fst p), snd p\<rangle>))" using map_type by auto
  then have "(A \<Rightarrow> list A \<Rightarrow> list (mem_of \<omega> \<times> A) \<Rightarrow> list (mem_of \<omega> \<times> A)) (\<lambda>x _ xs. cons \<langle>0,x\<rangle> (map (\<lambda>p. \<langle>succ (fst p), snd p\<rangle>) xs))" using cons_type[of "mem_of \<omega> \<times> A"] by fastforce
  with list_rec_type[where ?P="list (mem_of \<omega> \<times> A)"] nil_type show ?thesis unfolding index_list_def by auto
qed

lemma index_list_nil: "index_list nil = nil" unfolding index_list_def using list_rec_nil by fastforce

lemma index_list_cons: "A x \<Longrightarrow> list A xs \<Longrightarrow> index_list (cons x xs) = cons \<langle>0, x\<rangle> ((map (\<lambda>p. \<langle>succ (fst p), snd p\<rangle>) (index_list xs)))"
  unfolding index_list_def using list_rec_cons[of _ _ _ nil "(\<lambda>x _ xs. cons \<langle>0,x\<rangle> (map (\<lambda>p. \<langle>succ (fst p), snd p\<rangle>) xs))"] by auto

definition "list_rec_n_aux x f \<equiv> list_rec \<langle>0, x\<rangle> (\<lambda>x xs p. \<langle>succ (fst p), f (succ (fst p)) x xs (snd p)\<rangle>)"

lemma list_rec_n_aux_type: 
  "(P \<Rightarrow> (mem_of \<omega> \<Rightarrow> A \<Rightarrow> list A \<Rightarrow> P \<Rightarrow> P :: _ \<Rightarrow> bool) \<Rightarrow> list A \<Rightarrow> mem_of \<omega> \<times> P) list_rec_n_aux"
proof (intro mono_wrt_predI)
  fix x f xs assume "P x" and "(mem_of \<omega> \<Rightarrow> A \<Rightarrow> list A \<Rightarrow> P \<Rightarrow> P) (f :: set \<Rightarrow> set \<Rightarrow> set \<Rightarrow> set \<Rightarrow> set)" and "list A xs"
  then have "(A \<Rightarrow> list A \<Rightarrow> (mem_of \<omega> \<times> P) \<Rightarrow> (mem_of \<omega> \<times> P)) (\<lambda>x xs p. \<langle>succ (fst p), f (succ (fst p)) x xs (snd p)\<rangle>)"
    by fastforce
  with \<open>list A xs\<close> list_rec_type[where ?P="(mem_of \<omega> \<times> P)" and ?A="A"] \<open>P x\<close> show "(mem_of \<omega> \<times> P) (list_rec_n_aux x f xs)"
    unfolding list_rec_n_aux_def by auto
qed

definition "list_rec_n x f xs \<equiv> snd (list_rec_n_aux x f xs)"

lemma list_rec_n_type: "(P \<Rightarrow> (mem_of \<omega> \<Rightarrow> A \<Rightarrow> list A \<Rightarrow> P \<Rightarrow> P :: _ \<Rightarrow> bool) \<Rightarrow> list A \<Rightarrow> (P :: _ \<Rightarrow> bool)) list_rec_n"
proof (intro mono_wrt_predI)
  fix x f xs assume "P x" and "(mem_of \<omega> \<Rightarrow> A \<Rightarrow> list A \<Rightarrow> P \<Rightarrow> P) (f :: set \<Rightarrow> set \<Rightarrow> set \<Rightarrow> set \<Rightarrow> set)" and "list A xs"
  then have "(mem_of \<omega> \<times> P) (list_rec_n_aux x f xs)" using list_rec_n_aux_type[of P A] by blast
  then have "P (snd (list_rec_n_aux x f xs))" using set_pairE by auto
  thus "P (list_rec_n x f xs)" unfolding list_rec_n_def by auto
qed

definition "nth xs n \<equiv> list_rec undefined (\<lambda>x _ res. (if (fst x = n) then snd x else res)) (index_list xs)"

bundle list_nth_syntax begin notation nth (infixl "!" 100) end
bundle no_list_nth_syntax begin no_notation nth (infixl "!" 100) end

unbundle list_nth_syntax

lemma nth_type:
  assumes xs_cons: "xs = cons y ys"
  and xs_type: "list A xs"
  and "n \<in> \<omega>"
  and "n < length xs"
shows "A (nth xs n)"
proof-
  have index_type:"(list (mem_of \<omega> \<times> A)) (index_list xs)" using index_list_type xs_type by auto
  have inner_type:"((mem_of \<omega> \<times> A) \<Rightarrow> list (mem_of \<omega> \<times> A) \<Rightarrow> A \<Rightarrow> A) (\<lambda>x _ res. (if (fst x = n) then snd x else res))" by fastforce
  then show ?thesis unfolding nth_def using index_type list_rec_cons xs_cons list_rec_type[of "A" "mem_of \<omega> \<times> A"] sorry
qed

definition "tuple Ps xs \<equiv> length Ps = length xs \<and> (\<forall>i. 0 \<le> i \<and> i < length xs \<longrightarrow> mem_of (Ps ! i) (xs ! i))"

lemma tuple_nil[simp]: "tuple nil nil" 
  unfolding tuple_def by auto

lemma nth_0: "A x \<Longrightarrow> list A xs \<Longrightarrow> (cons x xs) ! 0 = x" unfolding nth_def sorry

lemma zero_ne_succ: "0 \<noteq> succ n" using succ_ne_zero by blast

lemma nth_succ:
  assumes "A x" and "list A xs"
  shows "nth (cons x xs) (succ n) = nth xs n"
  sorry

lemma "(mem_of \<Rightarrow> tuple \<Rrightarrow> tuple) cons" sorry

lemma tuple_cons: assumes "x \<in> p"
  and "tuple Ps xs"
  shows "tuple (cons p Ps) (cons x xs)" 
  sorry

definition "replicate n x \<equiv> omega_rec nil (cons x) n"

lemma replicate_zero[simp]: "\<And>x. replicate 0 x = nil" unfolding replicate_def by auto

lemma replicate_type: "(mem_of \<omega> \<Rightarrow> A \<Rightarrow> list A) replicate"
proof (intro mono_wrt_predI)
  fix n x assume "mem_of \<omega> n" and "A x"
  then have "(list A \<Rightarrow> list A) (cons x)" using cons_type by auto
  with \<open>mem_of \<omega> n\<close> omega_rec_type[of "list A"] nil_type show "list A (replicate n x)" unfolding replicate_def by auto
qed

lemma replicate_succ: "n \<in> \<omega> \<Longrightarrow> replicate (succ n) x = cons x (replicate n x)"
  unfolding replicate_def by (rule omega_rec_succ)

lemma zero_lt_succ: "i \<in> \<omega> \<Longrightarrow> 0 < succ i" 
proof (induction i rule: omega_induct)
  case zero
  then show ?case by (simp add: zero_mem_succ_if_mem_omega lt_iff_mem_if_mem_omega)
next
  case (succ m)
  then have "0 \<in> succ (succ m)" using zero_mem_succ_if_mem_omega[of "succ m"] by blast
  moreover from succ have "succ (succ m) \<in> \<omega>" by blast
  ultimately show ?case using zero_mem_succ_if_mem_omega[of "succ m"] lt_iff_mem_if_mem_omega[of "succ (succ m)" 0] by blast
qed

lemma replicate_nth:
  assumes "n \<in> \<omega>"
  and "i \<in> \<omega>"
  and "0 \<le> i"
  and "i < n"
shows "nth (replicate n x) i = x"
  sorry
(*using assms proof (induction n arbitrary: i rule: omega_induct)
  case zero
  then show ?case by auto
next
  case (succ m)
  then have repl_unf:"replicate (succ m) x = cons x (replicate m x)" using replicate_succ by blast
  then have nth0:"nth (replicate (succ m) x) 0 = x" using nth_0 by auto
  from repl_unf have nthsucc: "\<And>j. nth (cons x (replicate m x)) (succ j) = nth (replicate m x) j" using nth_succ by auto
  then show ?case using assms proof (cases "i = 0")
    case True
    then show ?thesis by (auto simp add: nth0)
  next
    case False
    then obtain j where "j \<in> \<omega>" "succ j = i" using \<open>i \<in> \<omega>\<close> by (auto elim: mem_omegaE)
    then have "succ j < succ m" using succ by blast
    then have "j < m" using \<open>j \<in> \<omega>\<close> \<open>m \<in> \<omega>\<close> lt_iff_mem_if_mem_omega by blast
    from \<open>succ j = i\<close> \<open>j \<in> \<omega>\<close> have "0 < i" using zero_lt_succ by blast
    with \<open>j \<in> \<omega>\<close> have "0 \<le> j" using \<open>succ j = i\<close> False le_if_lt_succ by blast
    have "nth i (replicate (succ m) x) = nth j (replicate m x)" using \<open>succ j = i\<close> nthsucc repl_unf by auto
    also have "... = x" using succ \<open>j < m\<close> \<open>0 \<le> j\<close> \<open>j \<in> \<omega>\<close> by blast
    finally show ?thesis by blast
  qed
qed*)


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
  then have "\<forall> i. i \<in> \<omega> \<and> 0 \<le> i \<and> i < length xs \<longrightarrow> mem_of P (nth i xs)" using replicate_nth tuple_def sorry
  then show "list P xs" sorry
qed

definition "vector P n xs \<equiv> length xs = n \<and> list P xs"

definition "append xs ys \<equiv> list_rec ys (\<lambda>x _. cons x) xs"

lemma nil_append_eq [simp]: "append nil ys = ys"
  by (simp add: list_rec_nil append_def)

lemma cons_append_eq [simp]:
  "A x \<Longrightarrow> list A xs \<Longrightarrow> append (cons x xs) ys = cons x (append xs ys)"
  by (simp add: append_def list_rec_cons)

lemma append_type: "(list A \<Rightarrow> list A \<Rightarrow> list A) append"
proof -
  have "(A \<Rightarrow> list A \<Rightarrow> list A \<Rightarrow> list A) (\<lambda>x _. cons x)"
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

lemma rev_cons_eq [simp]: "A x \<Longrightarrow> list A xs \<Longrightarrow> rev (cons x xs) = append (rev xs) (cons x nil)"
  by (simp add: rev_def list_rec_cons)

lemma rev_type: "(list A \<Rightarrow> list A) rev"
proof -
  have "(A \<Rightarrow> list A \<Rightarrow> list A \<Rightarrow> list A) (\<lambda>x _ acc. append acc (cons x nil))"
    using append_type cons_type nil_type by (intro mono_wrt_predI) (blast dest!: mono_wrt_predD) 
  with list_rec_type[where ?P="list A"] nil_type show ?thesis unfolding rev_def 
    by blast
qed

definition "zipWith f xs ys \<equiv> list_rec nil (\<lambda>x _ zs.(if is_nil ys then nil else cons (f x (head ys)) zs)) xs"
(* list_rec_n *)
lemma zipWith_type:
  assumes f_type: "(A \<Rightarrow> mem_of B \<Rightarrow> mem_of C) f"
  and xs_type: "list A xs"
  and ys_type: "list B ys"
shows "list C (zipWith f xs ys)"
  sorry

lemma zipWith_nil1: "zipWith f nil ys = nil" unfolding zipWith_def using list_rec_nil[of "nil"] by blast

lemma zipWith_nil2: "zipWith f (cons x xs) nil = nil" unfolding zipWith_def using list_rec_cons[of nil "(\<lambda>x _ zs.(if is_nil nil then nil else cons (f x (head nil)) zs))"] by auto

lemma zipWith_cons: "zipWith f (cons x xs) (cons y ys) = cons (f x y) (zipWith f xs ys)" unfolding zipWith_def
  sorry


end