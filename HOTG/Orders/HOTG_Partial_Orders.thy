\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Partial Orders\<close>
theory HOTG_Partial_Orders
  imports
    HOTG_Binary_Relations_Antisymmetric
    HOTG_Preorders
    Transport.Partial_Orders
begin

lemma partial_order_on_set_eq_partial_order_on_pred [simp]:
  "(partial_order_on (S :: set) :: (set \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> bool) = partial_order_on (mem_of S)"
  unfolding partial_order_on_def by simp

lemma partial_order_on_set_eq_partial_order_on_pred_uhint [uhint]:
  assumes "P \<equiv> mem_of S"
  shows "partial_order_on (S :: set) :: (set \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> bool \<equiv> partial_order_on P"
  using assms by simp

lemma partial_order_on_set_iff_partial_order_on_pred [iff]:
  "partial_order_on (S :: set) (R :: set \<Rightarrow> set \<Rightarrow> bool) \<longleftrightarrow> partial_order_on (mem_of S) R"
  by simp

lemma set_partial_order_on_pred_iff_partial_order_on_pred [iff]:
  "partial_order_on (P :: set \<Rightarrow> bool) R \<longleftrightarrow> partial_order_on P (rel R)"
  unfolding partial_order_on_def by simp

lemma set_partial_order_on_pred_iff_partial_order_on_pred_uhint [uhint]:
  assumes "R \<equiv> rel S"
  and "P :: set \<Rightarrow> bool \<equiv> P'"
  shows "partial_order_on P S \<equiv> partial_order_on P' R"
  using assms by simp

lemma set_partial_order_on_set_eq_set_partial_order_on_pred [simp]:
  "(partial_order_on (S :: set) :: set \<Rightarrow> bool) = partial_order_on (mem_of S)"
  unfolding partial_order_on_def by simp

lemma set_partial_order_on_set_eq_set_partial_order_on_pred_uhint [uhint]:
  assumes "P \<equiv> mem_of S"
  shows "partial_order_on (S :: set) :: set \<Rightarrow> bool \<equiv> partial_order_on P"
  using assms by simp

lemma set_partial_order_on_set_iff_set_partial_order_on_pred [iff]:
  "partial_order_on (S :: set) (R :: set) \<longleftrightarrow> partial_order_on (mem_of S) R"
  by simp

overloading
  partial_order_set \<equiv> "partial_order :: set \<Rightarrow> bool"
begin
  definition "(partial_order_set :: set \<Rightarrow> bool) \<equiv> partial_order_on (\<top> :: set \<Rightarrow> bool)"
end

lemma partial_order_set_eq_partial_order_on:
  "(partial_order :: set \<Rightarrow> bool) = partial_order_on (\<top> :: set \<Rightarrow> bool)"
  unfolding partial_order_set_def ..

lemma partial_order_set_eq_partial_order_on_uhint [uhint]:
  assumes "P \<equiv> \<top> :: set \<Rightarrow> bool"
  shows "(partial_order :: set \<Rightarrow> bool) \<equiv> partial_order_on P"
  using assms by (simp add: partial_order_set_eq_partial_order_on)

lemma partial_order_set_iff_partial_order_pred [iff]: "partial_order S \<longleftrightarrow> partial_order (rel S)"
  unfolding partial_order_set_def by (urule refl)

lemma partial_order_set_iff_partial_order_pred_uhint [uhint]:
  assumes "R \<equiv> rel S"
  shows "partial_order S \<equiv> partial_order R"
  using assms by simp

end