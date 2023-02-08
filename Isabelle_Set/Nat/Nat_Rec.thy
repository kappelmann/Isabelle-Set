\<^marker>\<open>creator "Alexander Krauss"\<close>
\<^marker>\<open>creator "Josh Chen"\<close>
\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Recursion\<close>
theory Nat_Rec
  imports
    Nat_Ranges
    TSPairs
begin

text \<open>Recursion on Nat. Axiomatized, for now.\<close>

axiomatization nat_rec :: "set \<Rightarrow> set \<Rightarrow> (set \<Rightarrow> set)  \<Rightarrow> set" where
  nat_rec_zero [iff]: "nat_rec 0 x\<^sub>0 f = x\<^sub>0" and
  nat_rec_succ [simp]: "n : Nat \<Longrightarrow> nat_rec (succ n) x\<^sub>0 f = f (nat_rec n x\<^sub>0 f)"

lemma nat_rec_type [type]: "nat_rec: Nat \<Rightarrow> A \<Rightarrow> (A \<Rightarrow> A) \<Rightarrow> A"
proof (rule Dep_fun_typeI)+
  fix n x f
  show "n : Nat \<Longrightarrow> x : A \<Longrightarrow> f : A \<Rightarrow> A \<Longrightarrow> nat_rec n x f : A"
    by (induct n rule: Nat_induct) auto
qed

text \<open>Recursion on Nat with index\<close>
definition "nat_rec' n x\<^sub>0 f \<equiv> snd (
  nat_rec n \<langle>0, x\<^sub>0\<rangle> (\<lambda>p. \<langle>succ (fst p), f (succ (fst p)) (snd p)\<rangle>)
)"

lemma nat_rec'_zero [iff]: "nat_rec' 0 x\<^sub>0 f = x\<^sub>0"
  unfolding nat_rec'_def by simp

lemma nat_rec'_succ [simp]:
  assumes "n : Nat"
  shows "nat_rec' (succ n) x\<^sub>0 f = f (succ n) (nat_rec' n x\<^sub>0 f)"
proof -
  have "\<And>m. m : Nat \<Longrightarrow>
    fst (nat_rec m \<langle>0, x\<^sub>0\<rangle> (\<lambda>p. \<langle>succ (fst p), f (succ (fst p)) (snd p)\<rangle>)) = m"
    by (rule Nat_induct) auto
  then show ?thesis unfolding nat_rec'_def by auto
qed

(*TODO: type derivator is not able to handle this automatically yet.*)
lemma nat_rec'_type [type]:
  "nat_rec' : Nat \<Rightarrow> A \<Rightarrow> (Nat \<Rightarrow> A \<Rightarrow> A) \<Rightarrow> A"
proof (intro Dep_fun_typeI)
  fix n x\<^sub>0 f
  assume  "n : Nat" "x\<^sub>0 : A" "f : Nat \<Rightarrow> A \<Rightarrow> A"
  have "(\<lambda>p. \<langle>succ (fst p), f (succ (fst p)) (snd p)\<rangle>) : Nat \<times> A \<Rightarrow> Nat \<times> A"
    by auto
  then show "nat_rec' n x\<^sub>0 f : A"
    unfolding nat_rec'_def using [[type_derivation_depth=4]]
    by discharge_types
qed

lemma nat_rec'_dep_type [type]: "nat_rec' : (n : Nat) \<Rightarrow> A \<Rightarrow>
  (Element [1,\<dots>,n] \<Rightarrow> A \<Rightarrow> A) \<Rightarrow> A"
proof (intro Dep_fun_typeI)+
  fix n x\<^sub>0 f assume  "n : Nat" "x\<^sub>0 : A" "f : Element [1,\<dots>,n] \<Rightarrow> A \<Rightarrow> A"
  then show "nat_rec' n x\<^sub>0 f : A"
  proof (induction n rule: Nat_induct)
    case (succ n)
    have "f : Element [1,\<dots>,n] \<Rightarrow> A \<Rightarrow> A"
      by (rule Dep_fun_contravariant_dom[where ?A="Element [1,\<dots>,succ n]"])
        (unfold_types, auto simp: range_incl_excl_def intro: lt_succ_if_lt)
    have "succ n : Element [1,\<dots>,succ n]"
      unfolding nat_one_def by unfold_types auto
    from succ.prems show ?case by auto
  qed simp
qed


end
