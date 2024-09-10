\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Connected\<close>
theory HOTG_Binary_Relations_Connected
  imports
    HOTG_Binary_Relations_Base
    Transport.Binary_Relations_Connected
begin

overloading
  connected_on_set \<equiv> "connected_on :: set \<Rightarrow> (set \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> bool"
  set_connected_on_pred \<equiv> "connected_on :: (set \<Rightarrow> bool) \<Rightarrow> set \<Rightarrow> bool"
  set_connected_on_set \<equiv> "connected_on :: set \<Rightarrow> set \<Rightarrow> bool"
  connected_set \<equiv> "connected :: set \<Rightarrow> bool"
begin
  definition "connected_on_set (A :: set) (R :: set \<Rightarrow> set \<Rightarrow> bool) \<equiv> connected_on (mem_of A) R"
  definition "set_connected_on_pred (P :: set \<Rightarrow> bool) (R :: set) \<equiv> connected_on P (rel R)"
  definition "set_connected_on_set (A :: set) (R :: set) \<equiv> connected_on (mem_of A) R"
  definition "connected_set :: set \<Rightarrow> bool \<equiv> connected_on (\<top> :: set \<Rightarrow> bool)"
end

lemma connected_on_set_eq_connected_on_pred [simp]:
  "(connected_on (S :: set) :: (set \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> bool) = connected_on (mem_of S)"
  unfolding connected_on_set_def by simp

lemma connected_on_set_eq_connected_on_pred_uhint [uhint]:
  assumes "P \<equiv> mem_of S"
  shows "connected_on (S :: set) :: (set \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> bool \<equiv> connected_on P"
  using assms by simp

lemma connected_on_set_iff_connected_on_pred [iff]:
  "connected_on (S :: set) (R :: set \<Rightarrow> set \<Rightarrow> bool) \<longleftrightarrow> connected_on (mem_of S) R"
  by simp

lemma set_connected_on_pred_iff_connected_on_pred [iff]:
  "connected_on (P :: set \<Rightarrow> bool) R \<longleftrightarrow> connected_on P (rel R)"
  unfolding set_connected_on_pred_def by simp

lemma set_connected_on_pred_iff_connected_on_pred_uhint [uhint]:
  assumes "R \<equiv> rel S"
  and "P :: set \<Rightarrow> bool \<equiv> P'"
  shows "connected_on P S \<equiv> connected_on P' R"
  using assms by simp

lemma set_connected_on_set_eq_set_connected_on_pred [simp]:
  "(connected_on (S :: set) :: set \<Rightarrow> bool) = connected_on (mem_of S)"
  unfolding set_connected_on_set_def by simp

lemma set_connected_on_set_eq_set_connected_on_pred_uhint [uhint]:
  assumes "P \<equiv> mem_of S"
  shows "connected_on (S :: set) :: set \<Rightarrow> bool \<equiv> connected_on P"
  using assms by simp

lemma set_connected_on_set_iff_set_connected_on_pred [iff]:
  "connected_on (S :: set) (R :: set) \<longleftrightarrow> connected_on (mem_of S) R"
  by simp

lemma connected_set_eq_set_connected_on:
  "(connected :: set \<Rightarrow> _) = connected_on (\<top> :: set \<Rightarrow> bool)"
  unfolding connected_set_def ..

lemma connected_set_eq_set_connected_on_uhint [uhint]:
  "P \<equiv> (\<top> :: set \<Rightarrow> bool) \<Longrightarrow> (connected :: set \<Rightarrow> _) \<equiv> connected_on P"
  by (simp add: connected_set_eq_set_connected_on)

lemma connected_set_iff_connected_pred [iff]:
  "connected S \<longleftrightarrow> connected (rel S)"
  unfolding connected_set_eq_set_connected_on by (urule refl)

lemma connected_set_eq_connected_pred_uhint [uhint]:
  "R \<equiv> rel A \<Longrightarrow> connected A \<equiv> connected R"
  by simp

end