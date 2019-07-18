section\<open>Least and Greatest Fixed Points; the Knaster-Tarski Theorem\<close>

theory Fixed_Points imports Set_Theory begin

text \<open>
  Most of this material was ported from Isabelle/ZF.

  We try to make the definitions "more typed" by having a type of monotone operators over
  a set.

  Work in progress and field of experiments.
\<close>

subsection\<open>Monotone Operators\<close>

definition
  monotone :: "set \<Rightarrow> (set \<Rightarrow> set) \<Rightarrow> bool"  where
     "monotone D h == (\<forall>W X. W\<subseteq>X \<longrightarrow> X\<subseteq>D \<longrightarrow> h W \<subseteq> h X)"


lemma monotone_type[type]: 
  "monotone : (D : set) \<Rightarrow> (subset D \<Rightarrow> subset D) \<Rightarrow> bool"
  by (intro Pi_typeI) (rule any_typeI)

abbreviation
  "monop D == monotone D\<cdot>(subset D \<Rightarrow> subset D)"

lemma monotoneI:
  assumes b: "\<And>W X. [| W\<subseteq>D;  X\<subseteq>D;  W\<subseteq>X |] ==> h(W) \<subseteq> h(X)"
  shows "monotone D h"
  unfolding monotone_def
proof (intro conjI allI impI)
  fix W X assume h: "W \<subseteq> X" "X \<subseteq> D"
  then have "W\<subseteq>D" by auto
  from this `X \<subseteq> D` `W \<subseteq> X` show "h W \<subseteq> h X" by (rule b)
qed


lemma monopD1: "h : monop D ==> h(D) \<subseteq> D"
  unfolding monotone_def by squash_types auto

lemma monopD2: "[| h : monop D;  X : subset D; W \<subseteq> X |] ==> h W \<subseteq> h X"
  unfolding monotone_def by squash_types

(* just typing *)

lemma monop_h_type: "h : monop D \<Longrightarrow> X : subset D ==> h X : subset D"
  by (drule type_spec) (drule Pi_typeE)
   
lemma monop_Un:
  assumes [type]: "h : monop D" "A : subset D" "B : subset D"
  shows "h A \<union> h B \<subseteq> h (A \<union> B)"
proof -

  have 1: "A \<union> B : subset D" using assms by squash_types auto (* typing *)
  have A2: "A \<subseteq> A \<union> B" by auto
  have B2: "B \<subseteq> A \<union> B" by auto

  from assms(1) 1 A2 have "h A \<subseteq> h (A \<union> B)" by (rule monopD2)
  moreover
  from assms(1) 1 B2 have "h B \<subseteq> h (A \<union> B)" by (rule monopD2)
  ultimately show ?thesis by auto
qed

subsection\<open>Proof of Knaster-Tarski Theorem using least fixed-points.\<close>

definition 
  lfp      :: "set \<Rightarrow> (set \<Rightarrow> set) \<Rightarrow> set"  where
     "lfp D h == \<Inter>({X\<in> Pow(D). h X \<subseteq> X})"

lemma lfp_type[type]:
  "lfp : (D : set) \<Rightarrow> monop D \<Rightarrow> subset D"
  unfolding lfp_def by squash_types auto

(* explicitly set the context for now. This can actually be inferred *)
context
  fixes D h
  assumes D_type[type]: "D : set"
  and h_type[type]: "h : monop D"
begin

lemma lfp_lowerbound: 
    "A : subset D \<Longrightarrow> h A \<subseteq> A  ==> lfp D h \<subseteq> A"
  unfolding lfp_def subset_type_iff by blast

lemma lfp_greatest: "(\<And>X. X : subset D \<Longrightarrow> h X \<subseteq> X \<Longrightarrow> A \<subseteq> X) \<Longrightarrow> A \<subseteq> lfp D h"
  using monopD1[OF h_type] unfolding lfp_def by squash_types auto

lemma lfp_unfold: "lfp D h = h (lfp D h)"
proof (rule extensionality)

  show 1: "h (lfp D h) \<subseteq> lfp D h"
  proof (rule lfp_greatest)
    fix A assume A_type [type]: "A : subset D" and "h A \<subseteq> A"
    then have "lfp D h \<subseteq> A" by (rule lfp_lowerbound)
    then have "h (lfp D h) \<subseteq> h A" by (rule monopD2[OF h_type A_type])
    with `h A \<subseteq> A` show "h (lfp D h) \<subseteq> A" by blast
  qed

  print_types
  note [[derive_debug]]
  ML_prf \<open>
    Derivation.get_derivation_rules \<^context>
    |> map (Syntax.string_of_term \<^context> o Thm.prop_of)
    |> cat_lines
    |> Output.writeln;

    Derivation.derive_jdgmts \<^context> [\<^term>\<open>lfp D h\<close>, \<^term>\<open>D\<close>, \<^term>\<open>h\<close>]
  \<close>

  (* just three rules, but typing assumptions account for the ugly rule manipulations *)
  show "lfp D h \<subseteq> h (lfp D h)"
    apply (rule lfp_lowerbound[OF monop_h_type[OF h_type lfp_type[THEN Pi_typeE, THEN Pi_typeE, OF D_type h_type]]])
    apply (rule monopD2[OF h_type lfp_type[THEN Pi_typeE, THEN Pi_typeE, OF D_type h_type]])
    apply (rule 1)
    done
qed


(*Definition form, to control unfolding*)
lemma def_lfp_unfold: "A \<equiv> lfp D h \<Longrightarrow> A = h A"
  by (simp, rule lfp_unfold)

subsection\<open>General Induction Rule for Least Fixedpoints\<close>

lemma Collect_is_pre_fixedpt:
  assumes a: "\<And>x. x \<in> h (Collect (lfp D h) P) \<Longrightarrow> P(x)"
  shows "h (Collect (lfp D h) P) \<subseteq> Collect (lfp D h) P"
proof -
  have lfpt: "lfp D h : subset D" using lfp_type D_type h_type by squash_types auto

  (* just a few rules, but typing assumptions must be discharged *)
  have "Collect (lfp D h) P \<subseteq> lfp D h" by (rule Collect_subset)
  then have "h (Collect (lfp D h) P) \<subseteq> h (lfp D h)" by (rule monopD2[OF h_type lfpt])
  moreover have "... = lfp D h" by (simp only: lfp_unfold[symmetric])
  ultimately show ?thesis using a by auto
qed  

lemma induct:
  assumes hyp: "a \<in> lfp D h"
  assumes IH: "!!x. x \<in> h (Collect (lfp D h) P) ==> P x"
  shows "P a"
proof -
  have "lfp D h \<subseteq> Collect (lfp D h) P"
  proof (rule lfp_lowerbound)
    from IH
    show "h (Collect (lfp D h) P) \<subseteq> Collect (lfp D h) P"
      by (rule Collect_is_pre_fixedpt)

    show "Collect (lfp D h) P : subset D" (* just typing *)
      using Collect_subset lfp_type[THEN Pi_typeE, THEN Pi_typeE, OF D_type h_type]
      by squash_types auto
  qed
  with hyp show "P a" by auto
qed

(*Definition form, to control unfolding*)
lemma def_induct:
    "[| A = lfp D h;  a\<in>A;    
        !!x. x \<in> h (Collect A P) ==> P x  
     |] ==> P a"
by (rule induct, blast+)

lemma lfp_cong:
  assumes D: "D = D'"
  assumes h: "\<And>X. X \<subseteq> D' \<Longrightarrow> h X = h' X"
  shows "lfp D h = lfp D' h'"
proof -
  have "{x \<in> Pow D | h x \<subseteq> x} = {x \<in> Pow D' | h' x \<subseteq> x}" unfolding D
    by (rule Collect_cong) (auto simp: h)
  then show ?thesis by  (simp add: lfp_def)
qed

end



end
