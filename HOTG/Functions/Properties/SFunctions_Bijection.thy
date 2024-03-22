\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Bijections\<close>
theory SFunctions_Bijection
  imports
    SFunctions_Base
    ML_Unification.ML_Unification_Hints
    Transport.Functions_Bijection
begin

overloading
  bijection_on_set \<equiv> "bijection_on :: set \<Rightarrow> set \<Rightarrow> (set \<Rightarrow> set) \<Rightarrow> (set \<Rightarrow> set) \<Rightarrow> bool"
  set_bijection_on_pred \<equiv> "bijection_on :: (set \<Rightarrow> bool) \<Rightarrow> (set \<Rightarrow> bool) \<Rightarrow> set \<Rightarrow> set \<Rightarrow> bool"
  set_bijection_on_set \<equiv> "bijection_on :: set \<Rightarrow> set \<Rightarrow> set \<Rightarrow> set \<Rightarrow> bool"
begin
  definition "bijection_on_set (A :: set) (B :: set) :: (set \<Rightarrow> set) \<Rightarrow> (set \<Rightarrow> set) \<Rightarrow> bool \<equiv>
    bijection_on (mem_of A) (mem_of B)"
  definition "set_bijection_on_pred (P :: set \<Rightarrow> bool) (Q :: set \<Rightarrow> bool) f g :: bool \<equiv>
    bijection_on P Q (eval f) (eval g)"
  definition "set_bijection_on_set (A :: set) (B :: set) :: set \<Rightarrow> set \<Rightarrow> bool \<equiv>
    bijection_on (mem_of A) (mem_of B)"
end

lemma bijection_on_set_eq_bijection_on_pred [simp]:
  "(bijection_on (A :: set) (B :: set) :: (set \<Rightarrow> set) \<Rightarrow> (set \<Rightarrow> set) \<Rightarrow> bool) =
    bijection_on (mem_of A) (mem_of B)"
  unfolding bijection_on_set_def by simp

lemma bijection_on_set_eq_bijection_on_pred_uhint [uhint]:
  "P \<equiv> mem_of A \<Longrightarrow> Q \<equiv> mem_of B \<Longrightarrow> R \<equiv> bijection_on P Q \<Longrightarrow>
    (bijection_on (A :: set) (B :: set) :: (set \<Rightarrow> set) \<Rightarrow> (set \<Rightarrow> set) \<Rightarrow> bool) \<equiv> R"
  by simp

lemma bijection_on_set_iff_bijection_on_pred [iff]:
  "bijection_on (A :: set) (B :: set) (f :: set \<Rightarrow> set) (g :: set \<Rightarrow> set) \<longleftrightarrow>
    bijection_on (mem_of A) (mem_of B) f g"
  by simp

lemma set_bijection_on_pred_iff_bijection_on_pred [iff]:
  "bijection_on (P :: set \<Rightarrow> bool) (Q :: set \<Rightarrow> bool) f g \<longleftrightarrow> bijection_on P Q (eval f) (eval g)"
  unfolding set_bijection_on_pred_def by simp

lemma set_bijection_on_set_eq_set_bijection_on_pred [simp]:
  "(bijection_on (A :: set) (B :: set) :: set \<Rightarrow> set \<Rightarrow> bool) = bijection_on (mem_of A) (mem_of B)"
  unfolding set_bijection_on_set_def by simp

lemma set_bijection_on_set_iff_set_bijection_on_pred [iff]:
  "bijection_on (A :: set) (B :: set) (f :: set) (g :: set) \<longleftrightarrow>
    bijection_on (mem_of A) (mem_of B) f g"
  by simp


end