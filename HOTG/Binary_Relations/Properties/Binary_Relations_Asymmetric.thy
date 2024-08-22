theory Binary_Relations_Asymmetric
  imports 
    Transport.Binary_Relations_Irreflexive 
    Transport.Binary_Relations_Transitive
    Transport.Binary_Relations_Antisymmetric
begin

consts asymmetric_on :: "'a \<Rightarrow> 'b \<Rightarrow> bool"

overloading
  asymmetric_on_pred \<equiv> "asymmetric_on :: ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
begin
  definition "asymmetric_on_pred (D :: 'a \<Rightarrow> bool) (R :: 'a \<Rightarrow> 'a \<Rightarrow> bool) 
    \<equiv> \<forall>x y : D. R x y \<longrightarrow> \<not> R y x"
end

lemma asymmetric_onI [intro]:
  assumes "\<And>x y. D x \<Longrightarrow> D y \<Longrightarrow> R x y \<Longrightarrow> \<not> R y x"
  shows "asymmetric_on D R"
  using assms unfolding asymmetric_on_pred_def by blast

lemma asymmetric_onD [dest]:
  assumes "asymmetric_on D R" "D x" "D y" "R x y"
  shows "\<not> R y x"
  using assms unfolding asymmetric_on_pred_def by blast

lemma irreflexive_on_if_asymmetric_on:
  fixes D :: "'a \<Rightarrow> bool" and R :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes "asymmetric_on D R"
  shows "irreflexive_on D R"
  using assms by blast

lemma antisymmetric_on_if_asymmetric_on:
  fixes D :: "'a \<Rightarrow> bool" and R :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes "asymmetric_on D R"
  shows "antisymmetric_on D R"
  using assms by blast

lemma asymmetric_on_pullback:
  fixes A :: "'a \<Rightarrow> bool" and R :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes "asymmetric_on A R" "(B \<Rightarrow> A) f"
  shows "asymmetric_on B (rel_map f R)"
  using assms by fastforce

lemma asymmetric_on_subdomain:
  fixes A :: "'a \<Rightarrow> bool" and R :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes "asymmetric_on A R" "B \<le> A"
  shows "asymmetric_on B R"
  using assms by blast

end