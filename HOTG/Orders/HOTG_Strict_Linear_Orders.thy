\<^marker>\<open>creator "Kevin Kappelmann"\<close>
\<^marker>\<open>creator "Niklas Krofta"\<close>
subsection \<open>Strict Linear Orders\<close>
theory HOTG_Strict_Linear_Orders
  imports
    HOTG_Strict_Partial_Orders
    HOTG_Binary_Relations_Connected
    Transport.Strict_Linear_Orders
begin

lemma strict_linear_order_on_set_eq_strict_linear_order_on_pred [simp]:
  "(strict_linear_order_on (S :: set) :: (set \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> bool) = strict_linear_order_on (mem_of S)"
  unfolding strict_linear_order_on_def by simp

lemma strict_linear_order_on_set_eq_strict_linear_order_on_pred_uhint [uhint]:
  assumes "P \<equiv> mem_of S"
  shows "strict_linear_order_on (S :: set) :: (set \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> bool \<equiv> strict_linear_order_on P"
  using assms by simp

lemma strict_linear_order_on_set_iff_strict_linear_order_on_pred [iff]:
  "strict_linear_order_on (S :: set) (R :: set \<Rightarrow> set \<Rightarrow> bool) \<longleftrightarrow> strict_linear_order_on (mem_of S) R"
  by simp

lemma set_strict_linear_order_on_pred_iff_strict_linear_order_on_pred [iff]:
  "strict_linear_order_on (P :: set \<Rightarrow> bool) R \<longleftrightarrow> strict_linear_order_on P (rel R)"
  unfolding strict_linear_order_on_def by simp

lemma set_strict_linear_order_on_pred_iff_strict_linear_order_on_pred_uhint [uhint]:
  assumes "R \<equiv> rel S"
  and "P :: set \<Rightarrow> bool \<equiv> P'"
  shows "strict_linear_order_on P S \<equiv> strict_linear_order_on P' R"
  using assms by simp

lemma set_strict_linear_order_on_set_eq_set_strict_linear_order_on_pred [simp]:
  "(strict_linear_order_on (S :: set) :: set \<Rightarrow> bool) = strict_linear_order_on (mem_of S)"
  unfolding strict_linear_order_on_def by simp

lemma set_strict_linear_order_on_set_eq_set_strict_linear_order_on_pred_uhint [uhint]:
  assumes "P \<equiv> mem_of S"
  shows "strict_linear_order_on (S :: set) :: set \<Rightarrow> bool \<equiv> strict_linear_order_on P"
  using assms by simp

lemma set_strict_linear_order_on_set_iff_set_strict_linear_order_on_pred [iff]:
  "strict_linear_order_on (S :: set) (R :: set) \<longleftrightarrow> strict_linear_order_on (mem_of S) R"
  by simp

overloading
  strict_linear_order_set \<equiv> "strict_linear_order :: set \<Rightarrow> bool"
begin
  definition "(strict_linear_order_set :: set \<Rightarrow> bool) \<equiv> strict_linear_order_on (\<top> :: set \<Rightarrow> bool)"
end

lemma strict_linear_order_set_eq_strict_linear_order_on:
  "(strict_linear_order :: set \<Rightarrow> bool) = strict_linear_order_on (\<top> :: set \<Rightarrow> bool)"
  unfolding strict_linear_order_set_def ..

lemma strict_linear_order_set_eq_strict_linear_order_on_uhint [uhint]:
  assumes "P \<equiv> \<top> :: set \<Rightarrow> bool"
  shows "(strict_linear_order :: set \<Rightarrow> bool) \<equiv> strict_linear_order_on P"
  using assms by (simp add: strict_linear_order_set_eq_strict_linear_order_on)

lemma strict_linear_order_set_iff_strict_linear_order_pred [iff]: "strict_linear_order S \<longleftrightarrow> strict_linear_order (rel S)"
  unfolding strict_linear_order_set_def by (urule refl)

lemma strict_linear_order_set_iff_strict_linear_order_pred_uhint [uhint]:
  assumes "R \<equiv> rel S"
  shows "strict_linear_order S \<equiv> strict_linear_order R"
  using assms by simp

end