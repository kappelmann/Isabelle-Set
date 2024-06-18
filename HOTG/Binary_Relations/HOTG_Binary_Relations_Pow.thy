\<^marker>\<open>creator "Kevin Kappelmann"\<close>
\<^marker>\<open>creator "Niklas Krofta"\<close>
subsection \<open>Power of Relations\<close>
theory HOTG_Binary_Relations_Pow
  imports
    HOTG_Transfinite_Recursion
    Transport.Binary_Relations_Transitive_Closure
begin

paragraph \<open>Summary\<close>
text \<open>The n-th composition of a relation with itself:\<close>

definition "rel_pow R = transfrec (\<lambda>r_pow n x y. R x y \<or> (\<exists>m : n. \<exists>z. r_pow m x z \<and> R z y))"

lemma rel_pow_iff: "rel_pow R n x y \<longleftrightarrow> R x y \<or> (\<exists>m : n. \<exists>z. rel_pow R m x z \<and> R z y)"
  using transfrec_eq[of "\<lambda>r_pow n x y. R x y \<or> (\<exists>m : n. \<exists>z. r_pow m x z \<and> R z y)" n]
  unfolding rel_pow_def by auto

lemma rel_pow_if_rel:
  assumes "R x y"
  shows "rel_pow R n x y"
  using assms rel_pow_iff by fast

lemma rel_pow_if_rel_if_mem_if_rel_pow:
  assumes "rel_pow R m x z"
  and "m \<in> n"
  and "R z y"
  shows "rel_pow R n x y"
  using assms rel_pow_iff by fast

lemma rel_powE:
  assumes "rel_pow R n x y"
  obtains (rel) "R x y" | (step) m z where "m \<in> n" "rel_pow R m x z" "R z y"
  using assms unfolding rel_pow_iff[where ?n=n] by blast


end