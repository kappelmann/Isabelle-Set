theory HOTG_Vectors
  imports HOTG_Lists HOTG_Ordinals_Omega ML_Unification.Unification_Attributes
begin

unbundle no_HOL_groups_syntax

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

definition "vector A n xs \<equiv> list A xs \<and> length xs = n"


axiomatization 
  ith :: "set \<Rightarrow> set \<Rightarrow> set"
  where ith_nil: "ith n nil = undefined"
  and ith_cons_zero: "ith 0 (cons x xs) = x"
  and ith_cons_succ: "ith (succ n) (cons x xs) = ith n xs"
  and ith_type: "(mem_of \<omega> \<Rightarrow> list A \<Rightarrow> mem_of A) ith"  
  

axiomatization
  vector_rec_2 ::  "'a \<Rightarrow> (set \<Rightarrow> set \<Rightarrow> set \<Rightarrow> set \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> set \<Rightarrow> set \<Rightarrow> 'a"
  where vector_rec_2_nil: "vector_rec_2 n c nil nil = n"
  and vector_rec_2_cons: "vector_rec_2 n c (cons x xs) (cons y ys) = c x y xs ys (vector_rec_2 n c xs ys)"
  and vector_rec_2_type: "\<And>A B (P :: 'a \<Rightarrow> bool). 
  (P \<Rightarrow> (mem_of A \<Rightarrow> mem_of B \<Rightarrow> list A \<Rightarrow> list B \<Rightarrow> P \<Rightarrow> P) \<Rightarrow> list A \<Rightarrow> list B \<Rightarrow> P) vector_rec_2"

definition "fun_vector_compose \<equiv> vector_rec_2 nil (\<lambda> (f::set) (g::set) _ _ zs . cons (g \<circ>\<circ> f) zs)"



end