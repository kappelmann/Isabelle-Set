\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Bijections\<close>
theory HOTG_Functions_Bijection
  imports
    HOTG_Functions_Injective
    HOTG_Functions_Inverse
    Transport.Functions_Bijection
begin

definition "bijection_on_set (A :: set) (B :: set) :: (set \<Rightarrow> set) \<Rightarrow> (set \<Rightarrow> set) \<Rightarrow> bool \<equiv>
  bijection_on (mem_of A) (mem_of B)"
adhoc_overloading bijection_on bijection_on_set
definition "set_bijection_on_pred (P :: set \<Rightarrow> bool) (Q :: set \<Rightarrow> bool) (f :: set) (g :: set) :: bool
  \<equiv> bijection_on P Q (eval f) (eval g)"
adhoc_overloading bijection_on set_bijection_on_pred
definition "set_bijection_on_set (A :: set) (B :: set) :: set \<Rightarrow> set \<Rightarrow> bool \<equiv>
  bijection_on (mem_of A) (mem_of B)"
adhoc_overloading bijection_on set_bijection_on_set

lemma bijection_on_set_eq_bijection_on_pred [simp]:
  "(bijection_on (A :: set) (B :: set) :: (set \<Rightarrow> set) \<Rightarrow> (set \<Rightarrow> set) \<Rightarrow> bool) =
    bijection_on (mem_of A) (mem_of B)"
  unfolding bijection_on_set_def by simp

lemma bijection_on_set_eq_bijection_on_pred_uhint [uhint]:
  assumes "P \<equiv> mem_of A"
  and "Q \<equiv> mem_of B"
  shows "bijection_on A B :: (set \<Rightarrow> set) \<Rightarrow> (set \<Rightarrow> set) \<Rightarrow> bool \<equiv> bijection_on P Q"
  using assms by simp

lemma bijection_on_set_iff_bijection_on_pred [iff]:
  "bijection_on A B (f :: set \<Rightarrow> set) (g :: set \<Rightarrow> set) \<longleftrightarrow> bijection_on (mem_of A) (mem_of B) f g"
  by simp

lemma set_bijection_on_pred_iff_bijection_on_pred [iff]:
  "bijection_on (P :: set \<Rightarrow> bool) (Q :: set \<Rightarrow> bool) (f :: set) (g :: set) \<longleftrightarrow>
    bijection_on P Q (eval f) (eval g)"
  unfolding set_bijection_on_pred_def by simp

lemma set_bijection_on_pred_eq_bijection_on_pred_uhint [uhint]:
  assumes "f' \<equiv> eval f"
  and "g' \<equiv> eval g"
  and "P \<equiv> P'"
  and "Q \<equiv> Q'"
  shows "bijection_on (P :: set \<Rightarrow> bool) (Q :: set \<Rightarrow> bool) (f :: set) (g :: set) \<equiv>
    bijection_on P' Q' f' g'"
  using assms by simp

lemma set_bijection_on_set_eq_set_bijection_on_pred [simp]:
  "(bijection_on (A :: set) (B :: set) :: set \<Rightarrow> set \<Rightarrow> bool) = bijection_on (mem_of A) (mem_of B)"
  unfolding set_bijection_on_set_def by simp

lemma set_bijection_on_set_eq_set_bijection_on_pred_uhint [uhint]:
  assumes "P \<equiv> mem_of A"
  and "Q \<equiv> mem_of B"
  shows "bijection_on (A :: set) B :: set \<Rightarrow> set \<Rightarrow> bool \<equiv> bijection_on P Q"
  using assms by simp

lemma set_bijection_on_set_iff_set_bijection_on_pred [iff]:
  "bijection_on A B (f :: set) (g :: set) \<longleftrightarrow> bijection_on (mem_of A) (mem_of B) f g"
  by simp

lemma bijection_on_image_the_inverse_on_if_injective_on:
  assumes "injective_on A f"
  shows "bijection_on A (image f A) f (the_inverse_on A f)"
  using assms by (urule bijection_on_has_inverse_on_the_inverse_on_if_injective_on)

end