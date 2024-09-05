theory HOTG_Vectors
  imports HOTG_Lists HOTG_Ordinals_Omega ML_Unification.Unification_Attributes
begin




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

(* todo: zipwith *)

end