theory Binary_Relations_Strict_Linear_Order
  imports 
    Binary_Relations_Asymmetric
    Transport.Binary_Relations_Transitive
    Transport.Binary_Relations_Connected
    Transport.Functions_Injective
begin

definition strict_linear_order_on :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
"strict_linear_order_on P R \<longleftrightarrow> asymmetric_on P R \<and> transitive_on P R \<and> connected_on P R"

lemma strict_linear_order_onI [intro]:
  assumes "asymmetric_on P R" "transitive_on P R" "connected_on P R"
  shows "strict_linear_order_on P R" 
  using assms strict_linear_order_on_def by blast

lemma strict_linear_order_onD [dest]: 
  assumes "strict_linear_order_on P R"
  shows "asymmetric_on P R" "transitive_on P R" "connected_on P R"
  using assms strict_linear_order_on_def by auto

lemma asymmetric_on_if_strict_linear_order_onE:
  assumes "strict_linear_order_on P R"
  shows "asymmetric_on P R"
  using assms strict_linear_order_on_def by blast

lemma transitive_on_if_strict_linear_order_onE:
  assumes "strict_linear_order_on P R"
  shows "transitive_on P R"
  using assms strict_linear_order_on_def by blast

lemma strict_linear_order_pullback:
  assumes order: "strict_linear_order_on P R" 
  assumes embedding: "(Q \<Rightarrow> P) f" "injective_on Q f"
  shows "strict_linear_order_on Q (\<lambda>x y. Q x \<and> Q y \<and> R (f x) (f y))"
proof -
  let ?S = "\<lambda>x y. R (f x) (f y)"
  have "\<not> ?S y x" if "Q x" "Q y" "R (f x) (f y)" for x y 
    using that \<open>(Q \<Rightarrow> P) f\<close> order by blast
  moreover have "?S x z" if "Q x" "Q y" "Q z" "?S x y" "?S y z" for x y z
    using that \<open>(Q \<Rightarrow> P) f\<close> order by (blast dest!: transitive_onD)
  moreover have "?S x y \<or> ?S y x" if "Q x" "Q y" "x \<noteq> y" for x y 
    using that embedding strict_linear_order_onD[OF order] by (auto dest: injective_onD)
  ultimately show ?thesis by blast
qed

end