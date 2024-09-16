\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Linear Orders\<close>
theory HOTG_Linear_Orders
  imports
    HOTG_Binary_Relations_Connected
    HOTG_Partial_Orders
    Transport.Linear_Orders
begin

lemma linear_order_on_set_eq_linear_order_on_pred [simp]:
  "(linear_order_on (S :: set) :: (set \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> bool) = linear_order_on (mem_of S)"
  unfolding linear_order_on_def by simp

lemma linear_order_on_set_eq_linear_order_on_pred_uhint [uhint]:
  assumes "P \<equiv> mem_of S"
  shows "linear_order_on (S :: set) :: (set \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> bool \<equiv> linear_order_on P"
  using assms by simp

lemma linear_order_on_set_iff_linear_order_on_pred [iff]:
  "linear_order_on (S :: set) (R :: set \<Rightarrow> set \<Rightarrow> bool) \<longleftrightarrow> linear_order_on (mem_of S) R"
  by simp

lemma set_linear_order_on_pred_iff_linear_order_on_pred [iff]:
  "linear_order_on (P :: set \<Rightarrow> bool) R \<longleftrightarrow> linear_order_on P (rel R)"
  unfolding linear_order_on_def by simp

lemma set_linear_order_on_pred_iff_linear_order_on_pred_uhint [uhint]:
  assumes "R \<equiv> rel S"
  and "P :: set \<Rightarrow> bool \<equiv> P'"
  shows "linear_order_on P S \<equiv> linear_order_on P' R"
  using assms by simp

lemma set_linear_order_on_set_eq_set_linear_order_on_pred [simp]:
  "(linear_order_on (S :: set) :: set \<Rightarrow> bool) = linear_order_on (mem_of S)"
  unfolding linear_order_on_def by simp

lemma set_linear_order_on_set_eq_set_linear_order_on_pred_uhint [uhint]:
  assumes "P \<equiv> mem_of S"
  shows "linear_order_on (S :: set) :: set \<Rightarrow> bool \<equiv> linear_order_on P"
  using assms by simp

lemma set_linear_order_on_set_iff_set_linear_order_on_pred [iff]:
  "linear_order_on (S :: set) (R :: set) \<longleftrightarrow> linear_order_on (mem_of S) R"
  by simp

overloading
  linear_order_set \<equiv> "linear_order :: set \<Rightarrow> bool"
begin
  definition "(linear_order_set :: set \<Rightarrow> bool) \<equiv> linear_order_on (\<top> :: set \<Rightarrow> bool)"
end

lemma linear_order_set_eq_linear_order_on:
  "(linear_order :: set \<Rightarrow> bool) = linear_order_on (\<top> :: set \<Rightarrow> bool)"
  unfolding linear_order_set_def ..

lemma linear_order_set_eq_linear_order_on_uhint [uhint]:
  assumes "P \<equiv> \<top> :: set \<Rightarrow> bool"
  shows "(linear_order :: set \<Rightarrow> bool) \<equiv> linear_order_on P"
  using assms by (simp add: linear_order_set_eq_linear_order_on)

lemma linear_order_set_iff_linear_order_pred [iff]: "linear_order S \<longleftrightarrow> linear_order (rel S)"
  unfolding linear_order_set_def by (urule refl)

lemma linear_order_set_iff_linear_order_pred_uhint [uhint]:
  assumes "R \<equiv> rel S"
  shows "linear_order S \<equiv> linear_order R"
  using assms by simp

end