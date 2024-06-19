\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Well-Founded\<close>
theory HOTG_Binary_Relations_Wellfounded
  imports
    HOTG_Binary_Relations_Base
    Transport.Binary_Relations_Wellfounded
begin

overloading
  wellfounded_set \<equiv> "wellfounded :: set \<Rightarrow> bool"
begin
  definition "wellfounded_set (R :: set) \<equiv> wellfounded (rel R)"
end

lemma wellfounded_set_iff_wellfounded_rel [iff]:
  "wellfounded R \<longleftrightarrow> wellfounded (rel R)"
  unfolding wellfounded_set_def by simp

lemma set_wellfounded_pred_iff_wellfounded_pred_uhint [uhint]:
  assumes "R \<equiv> rel S"
  shows "wellfounded S \<equiv> wellfounded R"
  using assms by simp

end
