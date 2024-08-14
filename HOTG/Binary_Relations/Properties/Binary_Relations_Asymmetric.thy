theory Binary_Relations_Asymmetric
  imports 
    Transport.Binary_Relations_Irreflexive 
    Transport.Binary_Relations_Transitive
    Transport.Binary_Relations_Antisymmetric
begin

definition asymmetric_on :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
"asymmetric_on P R \<longleftrightarrow> (\<forall>x y. P x \<longrightarrow> P y \<longrightarrow> R x y \<longrightarrow> \<not> R y x)"

lemma asymmetric_onD [dest]:
  assumes "asymmetric_on P R" "P x" "P y" "R x y"
  shows "\<not> R y x"
  using assms unfolding asymmetric_on_def by blast

lemma asymmetric_onI [intro]:
  assumes "\<And>x y. P x \<Longrightarrow> P y \<Longrightarrow> R x y \<Longrightarrow> \<not> R y x"
  shows "asymmetric_on P R"
  using assms unfolding asymmetric_on_def by blast

lemma irreflexive_on_if_asymmetric_on:
  assumes "asymmetric_on P R"
  shows "irreflexive_on P R"
  using assms by blast

lemma antisymmetric_on_if_asymmetric_on:
  assumes "asymmetric_on P R"
  shows "antisymmetric_on P R"
  using assms by blast

end