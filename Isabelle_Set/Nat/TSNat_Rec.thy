\<^marker>\<open>creator "Alexander Krauss"\<close>
\<^marker>\<open>creator "Josh Chen"\<close>
\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Recursion\<close>
theory TSNat_Rec
  imports
    TSNat_Ranges
    TSPairs
begin

unbundle no HOL_groups_syntax

text \<open>Recursion on Nat. Axiomatized, for now.\<close>

axiomatization nat_rec :: "set \<Rightarrow> set \<Rightarrow> (set \<Rightarrow> set)  \<Rightarrow> set" where
  nat_rec_zero [iff]: "nat_rec 0 x\<^sub>0 f = x\<^sub>0" and
  nat_rec_succ [simp]: "n \<Ztypecolon> Nat \<Longrightarrow> nat_rec (succ n) x\<^sub>0 f = f (nat_rec n x\<^sub>0 f)"

lemma nat_rec_type [type]: "nat_rec \<Ztypecolon> Nat \<Rightarrow> A \<Rightarrow> (A \<Rightarrow> A) \<Rightarrow> A"
proof (rule Dep_funI)+
  fix n x f
  show "n \<Ztypecolon> Nat \<Longrightarrow> x \<Ztypecolon> A \<Longrightarrow> f \<Ztypecolon> A \<Rightarrow> A \<Longrightarrow> nat_rec n x f \<Ztypecolon> A"
    by (induct n rule: Nat_induct) auto
qed

text \<open>Recursion on Nat with index\<close>
definition "nat_rec' n x\<^sub>0 f \<equiv> snd (
  nat_rec n \<langle>0, x\<^sub>0\<rangle> (\<lambda>p. \<langle>succ (fst p), f (succ (fst p)) (snd p)\<rangle>)
)"

lemma nat_rec'_zero [iff]: "nat_rec' 0 x\<^sub>0 f = x\<^sub>0"
  unfolding nat_rec'_def by simp

lemma nat_rec'_succ [simp]:
  assumes "n \<Ztypecolon> Nat"
  shows "nat_rec' (succ n) x\<^sub>0 f = f (succ n) (nat_rec' n x\<^sub>0 f)"
proof -
  have "\<And>m. m \<Ztypecolon> Nat \<Longrightarrow>
    fst (nat_rec m \<langle>0, x\<^sub>0\<rangle> (\<lambda>p. \<langle>succ (fst p), f (succ (fst p)) (snd p)\<rangle>)) = m"
    by (rule Nat_induct) auto
  then show ?thesis unfolding nat_rec'_def by auto
qed

(*TODO: type derivator is not able to handle this automatically yet.*)
lemma nat_rec'_type [type]:
  "nat_rec' \<Ztypecolon> Nat \<Rightarrow> A \<Rightarrow> (Nat \<Rightarrow> A \<Rightarrow> A) \<Rightarrow> A"
proof (intro Dep_funI)
  fix n x\<^sub>0 f
  assume  "n \<Ztypecolon> Nat" "x\<^sub>0 \<Ztypecolon> A" "f \<Ztypecolon> Nat \<Rightarrow> A \<Rightarrow> A"
  have "(\<lambda>p. \<langle>succ (fst p), f (succ (fst p)) (snd p)\<rangle>) \<Ztypecolon> Nat \<times> A \<Rightarrow> Nat \<times> A"
    using Pair_iff_Dep_pair[THEN iffD2, derive] [[type_derivation_depth=3]]
    by auto
  then show "nat_rec' n x\<^sub>0 f \<Ztypecolon> A"
    unfolding nat_rec'_def supply [[type_derivation_depth=5]]
    by discharge_types
qed

lemma nat_rec'_dep_type [type]:
  "nat_rec' \<Ztypecolon> (n : Nat) \<Rightarrow> A \<Rightarrow> (Element [1,\<dots>,n] \<Rightarrow> A \<Rightarrow> A) \<Rightarrow> A"
proof (intro Dep_funI)+
  fix n x\<^sub>0 f assume  "n \<Ztypecolon> Nat" "x\<^sub>0 \<Ztypecolon> A" "f \<Ztypecolon> Element [1,\<dots>,n] \<Rightarrow> A \<Rightarrow> A"
  then show "nat_rec' n x\<^sub>0 f \<Ztypecolon> A"
  proof (induction n rule: Nat_induct)
    case (succ n)
    from this(4) have "f \<Ztypecolon> Element [1,\<dots>,n] \<Rightarrow> A \<Rightarrow> A"
      by (rule Dep_fun_contravariant_dom[where ?A="Element [1,\<dots>,succ n]"])
      (unfold_types, auto intro: lt_succ_if_lt elim!: mem_range_incl_exclE)
    have "succ n \<Ztypecolon> Element [1,\<dots>,succ n]"
      by unfold_types auto
    from succ.prems show ?case by auto
  qed simp
qed


end
