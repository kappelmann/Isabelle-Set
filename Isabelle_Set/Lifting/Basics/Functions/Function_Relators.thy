subsection \<open>Relators\<close>
theory Function_Relators
  imports
    Binary_Relations_Base
    Functions_Base
begin

definition "Dep_Fun_Rel R S f g \<equiv> \<forall>x y. R x y \<longrightarrow> S x y (f x) (g y)"

abbreviation "Fun_Rel R S \<equiv> Dep_Fun_Rel R (\<lambda>_ _. S)"

syntax
  "_Fun_Rel" :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('c \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow> (('a \<Rightarrow> 'c) \<Rightarrow>
    ('b \<Rightarrow> 'd) \<Rightarrow> bool)" ("(_) \<Rrightarrow> (_)" [101, 100] 100)
  "_Dep_Fun_Rel" :: "idt \<Rightarrow> idt \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('c \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow>
    (('a \<Rightarrow> 'c) \<Rightarrow> ('b \<Rightarrow> 'd) \<Rightarrow> bool)" ("[_/ _/ \<Colon>/ _] \<Rrightarrow> (_)" [101, 101, 101, 100] 100)
translations
  "R \<Rrightarrow> S" \<rightleftharpoons> "CONST Fun_Rel R S"
  "[x y \<Colon> R] \<Rrightarrow> S" \<rightleftharpoons> "CONST Dep_Fun_Rel R (\<lambda>x y. S)"

lemma Dep_Fun_RelI:
  assumes "\<And>x y. R x y \<Longrightarrow> S x y (f x) (g y)"
  shows "([x y \<Colon> R] \<Rrightarrow> S x y) f g"
  unfolding Dep_Fun_Rel_def using assms by blast

lemma Dep_Fun_RelD:
  assumes "([x y \<Colon> R] \<Rrightarrow> S x y) f g"
  and "R x y"
  shows "S x y (f x) (g y)"
  using assms unfolding Dep_Fun_Rel_def by blast

lemma Dep_Fun_RelE:
  assumes "([x y \<Colon> R] \<Rrightarrow> S x y) f g"
  and "R x y"
  obtains "S x y (f x) (g y)"
  using assms unfolding Dep_Fun_Rel_def by blast

lemma Dep_Fun_Rel_inv_if_Dep_Fun_Rel:
  assumes "([x y \<Colon> R] \<Rrightarrow> S x y) f g"
  shows "([y x \<Colon> (rel_inv R)] \<Rrightarrow> (rel_inv (S x y))) g f"
  using assms
  by (intro Dep_Fun_RelI) (blast intro: rel_invI dest: rel_invD Dep_Fun_RelD)

lemma Dep_Fun_Rel_compI:
  assumes Dep_Fun_Rel1: "([x y \<Colon> R] \<Rrightarrow> S x y) f g"
  and Dep_Fun_Rel2: "\<And>x y. R x y \<Longrightarrow> ([x' y' \<Colon> T x y] \<Rrightarrow> U x y x' y') f' g'"
  and finer: "\<And>x y. S x y (f x) (g y) \<Longrightarrow> T x y (f x) (g y)"
  shows "([x y \<Colon> R] \<Rrightarrow> U x y (f x) (g y)) (f' \<circ> f) (g' \<circ> g)"
proof (rule Dep_Fun_RelI)
  fix x y assume "R x y"
  with Dep_Fun_Rel1 have "S x y (f x) (g y)" by (rule Dep_Fun_RelD)
  then have "T x y (f x) (g y)" by (rule finer)
  with Dep_Fun_Rel2 \<open>R x y\<close> show "U x y (f x) (g y) ((f' \<circ> f) x) ((g' \<circ> g) y)"
    by (fastforce dest: Dep_Fun_RelD)
qed

lemma Dep_Fun_Rel_compI':
  assumes "([x y \<Colon> R] \<Rrightarrow> S x y) f g"
  and "\<And>x y. R x y \<Longrightarrow> ([x' y' \<Colon> S x y] \<Rrightarrow> T x y x' y') f' g'"
  shows "([x y \<Colon> R] \<Rrightarrow> T x y (f x) (g y)) (f' \<circ> f) (g' \<circ> g)"
  using assms by (rule Dep_Fun_Rel_compI)


end