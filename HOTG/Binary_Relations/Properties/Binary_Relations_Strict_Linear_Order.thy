theory Binary_Relations_Strict_Linear_Order
  imports
    Binary_Relations_Asymmetric
    Transport.Binary_Relations_Transitive
    Transport.Binary_Relations_Connected
    Transport.Functions_Injective
begin

consts strict_linear_order_on :: "'a \<Rightarrow> 'b \<Rightarrow> bool"

overloading
  strict_linear_order_on_pred \<equiv> "strict_linear_order_on :: ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
begin
  definition "strict_linear_order_on_pred (D :: 'a \<Rightarrow> bool) (R :: 'a \<Rightarrow> 'a \<Rightarrow> bool) 
    \<equiv> asymmetric_on D R \<and> transitive_on D R \<and> connected_on D R"
end

lemma strict_linear_order_onI [intro]:
  fixes D :: "'a \<Rightarrow> bool" and R :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes "asymmetric_on D R" "transitive_on D R" "connected_on D R"
  shows "strict_linear_order_on D R" 
  using assms unfolding strict_linear_order_on_pred_def by blast

lemma strict_linear_order_onE [elim]: 
  fixes D :: "'a \<Rightarrow> bool" and R :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes "strict_linear_order_on D R"
  obtains "asymmetric_on D R" "transitive_on D R" "connected_on D R"
  using assms unfolding strict_linear_order_on_pred_def by blast

lemma transitive_on_pullback:
  fixes A :: "'a \<Rightarrow> bool" and R :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes "transitive_on A R" "(B \<Rightarrow> A) f"
  shows "transitive_on B (rel_map f R)"
  using assms by (fastforce intro!: transitive_onI dest!: transitive_onD)

lemma connected_on_pullback:
  fixes A :: "'a \<Rightarrow> bool" and R :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes "connected_on A R" "(B \<Rightarrow> A) f" "injective_on B f"
  shows "connected_on B (rel_map f R)"
  using assms by (fastforce dest: injective_onD)

lemma strict_linear_order_on_pullback:
  fixes A :: "'a \<Rightarrow> bool" and R :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes "strict_linear_order_on A R" "(B \<Rightarrow> A) f" "injective_on B f"
  shows "strict_linear_order_on B (rel_map f R)"
  using assms asymmetric_on_pullback transitive_on_pullback connected_on_pullback
  by (auto intro!: strict_linear_order_onI elim!: strict_linear_order_onE)

lemma transitive_on_subdomain [intro]:
  fixes A :: "'a \<Rightarrow> bool" and R :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes "transitive_on A R" "B \<le> A"
  shows "transitive_on B R"
  using assms by (blast dest: transitive_onD)

lemma connected_on_subdomain [intro]:
  fixes A :: "'a \<Rightarrow> bool" and R :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes "connected_on A R" "B \<le> A"
  shows "connected_on B R"
  using assms by blast

lemma strict_linear_order_on_subdomain:
  fixes A :: "'a \<Rightarrow> bool" and R :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes "strict_linear_order_on A R" "B \<le> A"
  shows "strict_linear_order_on B R"
  using assms by blast

end