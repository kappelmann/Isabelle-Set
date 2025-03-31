\<^marker>\<open>creator "Kevin Kappelmann"\<close>
\<^marker>\<open>creator "Niklas Krofa"\<close>
theory HOTG_Order_Isomorphisms
  imports
    HOTG_Basics
    Transport.Order_Isomorphisms
begin

definition "order_isomorphism_on_set A B \<equiv> order_isomorphism_on (mem_of A) (mem_of B)"
adhoc_overloading order_isomorphism_on \<rightleftharpoons> order_isomorphism_on_set

lemma order_isomorphism_on_set_eq_order_isomorphism_on_pred [simp]:
  "order_isomorphism_on A B = order_isomorphism_on (mem_of A) (mem_of B)"
  unfolding order_isomorphism_on_set_def by simp

lemma order_isomorphism_on_set_eq_order_isomorphism_on_pred_uhint [uhint]:
  assumes "P \<equiv> mem_of A"
  and "Q \<equiv> mem_of B"
  shows "order_isomorphism_on A B \<equiv> order_isomorphism_on P Q"
  using assms by simp

lemma order_isomorphism_on_set_iff_order_isomorphism_on_pred [iff]:
  "order_isomorphism_on A B L R l r \<longleftrightarrow> order_isomorphism_on (mem_of A) (mem_of B) L R l r"
  by simp

definition "order_isomorphic_on_set A B = order_isomorphic_on (mem_of A) (mem_of B)"
adhoc_overloading order_isomorphic_on \<rightleftharpoons> order_isomorphic_on_set

lemma order_isomorphic_on_set_eq_order_isomorphic_on_pred [simp]:
  "order_isomorphic_on A B = order_isomorphic_on (mem_of A) (mem_of B)"
  unfolding order_isomorphic_on_set_def by simp

lemma order_isomorphic_on_set_eq_order_isomorphic_on_pred_uhint [uhint]:
  assumes "P \<equiv> mem_of A"
  and "Q \<equiv> mem_of B"
  shows "order_isomorphic_on A B \<equiv> order_isomorphic_on P Q"
  using assms by simp

lemma order_isomorphic_on_set_iff_order_isomorphic_on_pred [iff]:
  "order_isomorphic_on A B L R \<longleftrightarrow> order_isomorphic_on (mem_of A) (mem_of B) L R"
  by simp

end