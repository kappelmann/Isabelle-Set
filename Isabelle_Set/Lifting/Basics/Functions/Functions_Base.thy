theory Functions_Base
  imports HOL.HOL
begin

subsection \<open>Basic Functions\<close>

definition "id x \<equiv> x"

lemma id_eq_self [simp]: "id x = x"
  unfolding id_def ..

definition "comp f g x \<equiv> f (g x)"

bundle notation_comp begin notation comp (infixl "\<circ>" 55) end
bundle no_notation_comp begin no_notation comp (infixl "\<circ>" 55) end
unbundle notation_comp

lemma comp_eq [simp]: "(f \<circ> g) x = f (g x)"
  unfolding comp_def ..

lemma id_comp_eq [simp]: "id \<circ> f = f"
  by (rule ext) simp

lemma comp_id_eq [simp]: "f \<circ> id = f"
  by (rule ext) simp

definition "dep_fun_map f g h x \<equiv> g x (f x) (h (f x))"

lemma dep_fun_map_eq: "dep_fun_map f g h x = g x (f x) (h (f x))"
  unfolding dep_fun_map_def ..

definition "fun_map f g h \<equiv> dep_fun_map f (\<lambda>_ _. g) h"

lemma fun_map_eq_comp: "fun_map f g h = g \<circ> h \<circ> f"
  unfolding fun_map_def dep_fun_map_eq by fastforce

lemma fun_map_eq: "fun_map f g h x = g (h (f x))"
  unfolding fun_map_eq_comp by simp


subsection \<open>Basic Properties\<close>

consts injective_on :: "'a \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> bool"

overloading
  injective_on_pred \<equiv> "injective_on :: ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool"
begin
  definition "injective_on_pred P f \<equiv> \<forall>x x'. P x \<longrightarrow> P x' \<longrightarrow> f x = f x' \<longrightarrow> x = x'"
end

lemma injective_onI:
  assumes "\<And>x x'. P x \<Longrightarrow> P x' \<Longrightarrow> f x = f x' \<Longrightarrow> x = x'"
  shows "injective_on P f"
  unfolding injective_on_pred_def using assms by blast

lemma injective_onD:
  assumes "injective_on P f"
  and "P x" "P x'"
  and "f x = f x'"
  shows "x = x'"
  using assms unfolding injective_on_pred_def by blast

definition "injective (f :: 'a \<Rightarrow> _) \<equiv> injective_on (\<lambda>x :: 'a. True) f"

lemma injective_eq_injective_on:
  "injective (f :: 'a \<Rightarrow> _) = injective_on (\<lambda>x :: 'a. True) f"
  unfolding injective_def ..

lemma injectiveI:
  assumes "\<And>x x'. f x = f x' \<Longrightarrow> x = x'"
  shows "injective f"
  unfolding injective_eq_injective_on using assms by (intro injective_onI)

lemma injectiveD:
  assumes "injective f"
  and "f x = f x'"
  shows "x = x'"
  using assms unfolding injective_eq_injective_on by (blast dest: injective_onD)

lemma injective_on_if_injective:
  fixes P :: "'a \<Rightarrow> bool" and f :: "'a \<Rightarrow> _"
  assumes "injective f"
  shows "injective_on P f"
  using assms by (intro injective_onI) (blast dest: injectiveD)

consts surjective_at :: "'a \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> bool"

overloading
  surjective_at_pred \<equiv> "surjective_at :: ('a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool"
begin
  definition "surjective_at_pred P f \<equiv> \<forall>y. P y \<longrightarrow> (\<exists>x. f x = y)"
end

lemma surjective_atI:
  assumes "\<And>y. P y \<Longrightarrow> \<exists>x. f x = y"
  shows "surjective_at P f"
  unfolding surjective_at_pred_def using assms by blast

lemma surjective_atE:
  assumes "surjective_at P f"
  and "P y"
  obtains x where "f x = y"
  using assms unfolding surjective_at_pred_def by blast

definition "surjective (f :: _ \<Rightarrow> 'a) \<equiv> surjective_at (\<lambda>x :: 'a. True) f"

lemma surjective_eq_surjective_at:
  "surjective (f :: _ \<Rightarrow> 'a) = surjective_at (\<lambda>x :: 'a. True) f"
  unfolding surjective_def ..

lemma surjectiveI:
  assumes "\<And>y. \<exists>x. f x = y"
  shows "surjective f"
  unfolding surjective_eq_surjective_at using assms by (intro surjective_atI)

lemma surjectiveE:
  assumes "surjective f"
  obtains x where "f x = y"
  using assms unfolding surjective_eq_surjective_at by (blast elim: surjective_atE)

lemma surjective_at_if_surjective:
  fixes P :: "'a \<Rightarrow> bool" and f :: "_ \<Rightarrow> 'a"
  assumes "surjective f"
  shows "surjective_at P f"
  using assms by (intro surjective_atI) (blast elim: surjectiveE)

consts inverse_on :: "'a \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> ('c \<Rightarrow> 'b) \<Rightarrow> bool"

overloading
  inverse_on_pred \<equiv> "inverse_on :: ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool"
begin
  definition "inverse_on_pred P f g \<equiv> \<forall>x. P x \<longrightarrow> g (f x) = x"
end

lemma inverse_onI:
  assumes "\<And>x. P x \<Longrightarrow> g (f x) = x"
  shows "inverse_on P f g"
  unfolding inverse_on_pred_def using assms by blast

lemma inverse_onD:
  assumes "inverse_on P f g"
  and "P x"
  shows "g (f x) = x"
  using assms unfolding inverse_on_pred_def by blast

lemma injective_on_if_inverse_on:
  assumes inv: "inverse_on (P :: 'a \<Rightarrow> bool) (f :: 'a \<Rightarrow> _) g"
  shows "injective_on P f"
proof (rule injective_onI)
  fix x x'
  assume Px: "P x" and Px': "P x'" and f_x_eq_f_x': "f x = f x'"
  have "x = g (f x)" using inv Px by (intro inverse_onD[symmetric])
  also have "... = g (f x')" by (simp only: f_x_eq_f_x')
  also have "... = x'" using inv Px' by (intro inverse_onD)
  finally show "x = x'" .
qed

definition "inverse (f :: 'a \<Rightarrow> _) \<equiv> inverse_on (\<lambda>x :: 'a. True) f"

lemma inverse_eq_inverse_on:
  "inverse (f :: 'a \<Rightarrow> _) = inverse_on (\<lambda>x :: 'a. True) f"
  unfolding inverse_def ..

lemma inverseI:
  assumes "\<And>x. g (f x) = x"
  shows "inverse f g"
  unfolding inverse_eq_inverse_on using assms by (intro inverse_onI)

lemma inverseD:
  assumes "inverse f g"
  shows "g (f x) = x"
  using assms unfolding inverse_eq_inverse_on by (blast dest: inverse_onD)

lemma inverse_on_if_inverse:
  fixes P :: "'a \<Rightarrow> bool" and f :: "'a \<Rightarrow> 'b"
  assumes "inverse f g"
  shows "inverse_on P f g"
  using assms by (intro inverse_onI) (blast dest: inverseD)

definition "has_fun_type P P' f \<equiv> \<forall>x. P x \<longrightarrow> P' (f x)"

lemma has_fun_typeI:
  assumes "\<And>x. P x \<Longrightarrow> P' (f x)"
  shows "has_fun_type P P' f"
  unfolding has_fun_type_def using assms by blast

lemma has_fun_typeD:
  assumes "has_fun_type P P' f"
  and "P x"
  shows "P' (f x)"
  using assms unfolding has_fun_type_def by blast

lemma has_fun_typeE:
  assumes "has_fun_type P P' f"
  and "P x"
  obtains "P' (f x)"
  using assms unfolding has_fun_type_def by blast

consts bijection_on :: "'a \<Rightarrow> 'b \<Rightarrow> ('c \<Rightarrow> 'd) \<Rightarrow> ('d \<Rightarrow> 'c) \<Rightarrow> bool"

overloading
  bijection_on_pred \<equiv> "bijection_on :: ('a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> ('c \<Rightarrow> 'd) \<Rightarrow> ('d \<Rightarrow> 'c) \<Rightarrow> bool"
begin
  definition "bijection_on_pred P P' f g \<equiv>
    has_fun_type P P' f \<and>
    has_fun_type P' P g \<and>
    inverse_on P f g \<and>
    inverse_on P' g f"
end

lemma bijection_onI:
  assumes "has_fun_type P P' f"
  and "has_fun_type P' P g"
  and "inverse_on P f g"
  and "inverse_on P' g f"
  shows "bijection_on P P' f g"
  using assms unfolding bijection_on_pred_def by blast

context
  fixes P :: "'a \<Rightarrow> bool"
  and P' :: "'b \<Rightarrow> bool"
  and f :: "'a \<Rightarrow> 'b"
begin

lemma has_fun_type_if_bijection_on:
  assumes "bijection_on P P' f g"
  shows "has_fun_type P P' f"
  using assms unfolding bijection_on_pred_def by blast

lemma has_fun_type_if_bijection_on':
  assumes "bijection_on P P' f g"
  shows "has_fun_type P' P g"
  using assms unfolding bijection_on_pred_def by blast

lemma bijection_on_prop_right:
  assumes "bijection_on P P' f g"
  and "P x"
  shows "P' (f x)"
  using assms by (blast intro: has_fun_typeD dest: has_fun_type_if_bijection_on)

lemma bijection_on_prop_left:
  assumes "bijection_on P P' f g"
  and "P' y"
  shows "P (g y)"
  using assms by (blast intro: has_fun_typeD dest: has_fun_type_if_bijection_on')

lemma inverse_on_if_bijection_on:
  assumes "bijection_on P P' f g"
  shows "inverse_on P f g"
  using assms unfolding bijection_on_pred_def by blast

lemma inverse_on_if_bijection_on':
  assumes "bijection_on P P' f g"
  shows "inverse_on P' g f"
  using assms unfolding bijection_on_pred_def by blast

lemma app_app_eq_self_if_bijection_on:
  assumes "bijection_on P P' f g"
  and "P x"
  shows "g (f x) = x"
  using assms inverse_on_if_bijection_on by (intro inverse_onD)

lemma app_app_eq_self_if_bijection_on':
  assumes "bijection_on P P' f g"
  and "P' y"
  shows "f (g y) = y"
  using assms inverse_on_if_bijection_on' by (intro inverse_onD)

lemma bijection_on_if_bijection_on:
  assumes "bijection_on P P' f g"
  shows "bijection_on P' P g f"
  using assms
  by (intro bijection_onI)
    (blast dest: inverse_on_if_bijection_on inverse_on_if_bijection_on'
    has_fun_type_if_bijection_on has_fun_type_if_bijection_on')+

lemma injective_on_if_bijection_on:
  assumes "bijection_on P P' f g"
  shows "injective_on P f"
  using assms by (intro injective_on_if_inverse_on inverse_on_if_bijection_on)

lemma injective_on_if_bijection_on':
  assumes "bijection_on P P' f g"
  shows "injective_on P' g"
  by (intro injective_on_if_inverse_on) (fact inverse_on_if_bijection_on'[OF assms])

end


definition "bijection (f :: 'a \<Rightarrow> 'b) \<equiv> bijection_on (\<lambda>x :: 'a. True) (\<lambda>x :: 'b. True) f"

lemma bijection_eq_bijection_on:
  "bijection (f :: 'a \<Rightarrow> 'b) = bijection_on (\<lambda>x :: 'a. True) (\<lambda>x :: 'b. True) f"
  unfolding bijection_def ..

lemma bijectionI:
  assumes "inverse f g"
  and "inverse g f"
  shows "bijection f g"
  unfolding bijection_def using assms
  by (intro bijection_onI inverse_on_if_inverse has_fun_typeI)

lemma inverse_if_bijection:
  assumes "bijection f g"
  shows "inverse f g"
  using assms unfolding bijection_def by (intro inverseI)
  (blast intro: app_app_eq_self_if_bijection_on)

lemma inverse_if_bijection':
  assumes "bijection f g"
  shows "inverse g f"
  using assms unfolding bijection_def by (intro inverseI)
  (blast intro: app_app_eq_self_if_bijection_on')

lemma bijection_if_bijection:
  assumes "bijection f g"
  shows "bijection g f"
  using assms by (intro bijectionI)
    (blast dest: inverse_if_bijection inverse_if_bijection')+


subsection \<open>Instantiations\<close>

lemma injective_id: "injective id"
  by (rule injectiveI) simp

lemma bijection_on_self_id:
  fixes P :: "'a \<Rightarrow> bool"
  shows "bijection_on P P (id :: 'a \<Rightarrow> _) id"
  by (intro bijection_onI inverse_onI has_fun_typeI) simp_all


end