section\<open>Least and Greatest Fixed Points; the Knaster-Tarski Theorem\<close>

theory Fixed_Points imports Set_Theory begin

text \<open>Most of this material was ported from Isabelle/ZF.\<close>

subsection\<open>Monotone Operators\<close>

definition 
  (*monotone operator from Pow(D) to itself*)
  bnd_mono :: "set \<Rightarrow> (set \<Rightarrow> set) \<Rightarrow> bool"  where
     "bnd_mono D h == (h D \<subseteq> D \<and> (\<forall>W X. W\<subseteq>X \<longrightarrow> X\<subseteq>D \<longrightarrow> h(W) \<subseteq> h(X)))"

lemma bnd_monoI:
  assumes a: "h(D)\<subseteq>D"
  assumes b: "\<And>W X. [| W\<subseteq>D;  X\<subseteq>D;  W\<subseteq>X |] ==> h(W) \<subseteq> h(X)"
  shows "bnd_mono D h"
  unfolding bnd_mono_def
proof (intro conjI allI impI a)
  fix W X assume h: "W \<subseteq> X" "X \<subseteq> D"
  then have "W\<subseteq>D" by auto
  from this `X \<subseteq> D` `W \<subseteq> X` show "h W \<subseteq> h X" by (rule b)
qed

lemma bnd_monoD1: "bnd_mono D h ==> h(D) \<subseteq> D"
  unfolding bnd_mono_def by (rule conjunct1)

lemma bnd_monoD2: "[| bnd_mono D h;  W\<subseteq>X;  X\<subseteq>D |] ==> h(W) \<subseteq> h(X)"
  unfolding bnd_mono_def by blast

lemma bnd_mono_subset:
    "[| bnd_mono D h;  X\<subseteq>D |] ==> h(X) \<subseteq> D"
  unfolding bnd_mono_def by blast

lemma bnd_mono_Un:
     "[| bnd_mono D h;  A \<subseteq> D;  B \<subseteq> D |] ==> h(A) \<union> h(B) \<subseteq> h(A \<union> B)"
  unfolding bnd_mono_def by blast

subsection\<open>Proof of Knaster-Tarski Theorem using least fixed-points.\<close>

definition 
  lfp      :: "set \<Rightarrow> (set \<Rightarrow> set) \<Rightarrow> set"  where
     "lfp D h == \<Inter>({X\<in> Pow(D). h X \<subseteq> X})"

(*lfp is contained in each pre-fixedpoint*)
lemma lfp_lowerbound: 
    "[| h(A) \<subseteq> A;  A\<subseteq>D |] ==> lfp D h \<subseteq> A"
by (unfold lfp_def, blast)

(*Unfolding the defn of Inter dispenses with the premise bnd_mono(D,h)!*)
lemma lfp_subset: "lfp D h \<subseteq> D"
by (unfold lfp_def Inter_def, blast)

(*Used in datatype package*)
lemma def_lfp_subset:  "A == lfp D h ==> A \<subseteq> D"
apply simp
apply (rule lfp_subset)
done

lemma lfp_greatest:  
    "[| h(D) \<subseteq> D;  !!X. [| h(X) \<subseteq> X;  X\<subseteq>D |] ==> A\<subseteq>X |] ==> A \<subseteq> lfp D h"
by (unfold lfp_def, blast) 

lemma lfp_lemma1:  
    "[| bnd_mono D h;  h(A)\<subseteq>A;  A\<subseteq>D |] ==> h(lfp D h) \<subseteq> A"
apply (erule bnd_monoD2 [THEN subset_trans])
apply (rule lfp_lowerbound, assumption+)
done

lemma lfp_lemma2: "bnd_mono D h ==> h(lfp D h) \<subseteq> lfp D h"
apply (rule bnd_monoD1 [THEN lfp_greatest])
apply (rule_tac [2] lfp_lemma1)
apply (assumption+)
done

lemma lfp_lemma3: 
    "bnd_mono D h ==> lfp D h \<subseteq> h(lfp D h)"
apply (rule lfp_lowerbound)
apply (rule bnd_monoD2, assumption)
apply (rule lfp_lemma2, assumption)
apply (erule_tac [2] bnd_mono_subset)
apply (rule lfp_subset)+
done

lemma lfp_unfold: "bnd_mono D h ==> lfp D h = h(lfp D h)"
apply (rule extensionality) 
apply (erule lfp_lemma3) 
apply (erule lfp_lemma2) 
done

(*Definition form, to control unfolding*)
lemma def_lfp_unfold:
    "[| A==lfp D h;  bnd_mono D h |] ==> A = h(A)"
apply simp
apply (erule lfp_unfold)
done

subsection\<open>General Induction Rule for Least Fixedpoints\<close>

lemma Collect_is_pre_fixedpt:
  assumes mono: "bnd_mono D h"
  assumes a: "!!x. x \<in> h(Collect(lfp D h) P) ==> P(x)"
  shows "h(Collect(lfp D h) P) \<subseteq> Collect(lfp D h)P"
  using a lfp_lemma2[OF mono] bnd_monoD2[OF mono] lfp_subset[of D h]
  by blast

(*This rule yields an induction hypothesis in which the components of a
  data structure may be assumed to be elements of lfp D h*)
lemma induct:
  assumes mono: "bnd_mono D h"
  assumes hyp: "a \<in> lfp D h"
  assumes IH: "!!x. x \<in> h (Collect (lfp D h) P) ==> P x"
  shows "P a"
proof -
  have "lfp D h \<subseteq> Collect (lfp D h) P"
  proof (rule lfp_lowerbound)
    from mono IH
    show "h (Collect (lfp D h) P) \<subseteq> Collect (lfp D h) P"
      by (rule Collect_is_pre_fixedpt)

    show "Collect (lfp D h) P \<subseteq> D"
      by (rule subset_trans, rule Collect_subset, rule lfp_subset)
  qed
  with hyp show "P a" by auto
qed

(*Definition form, to control unfolding*)
lemma def_induct:
    "[| A == lfp D h;  bnd_mono D h;  a\<in>A;    
        !!x. x \<in> h(Collect A P) ==> P(x)  
     |] ==> P(a)"
by (rule induct, blast+)

(*This version is useful when "A" is not a subset of D
  second premise could simply be h(D \<inter> A) \<subseteq> D or !!X. X\<subseteq>D ==> h(X)\<subseteq>D *)
lemma lfp_Int_lowerbound:
    "[| h(D \<inter> A) \<subseteq> A;  bnd_mono D h |] ==> lfp D h \<subseteq> A" 
apply (rule lfp_lowerbound [THEN subset_trans])
apply (erule bnd_mono_subset [THEN Int_greatest], blast+)
done

(*Monotonicity of lfp, where h precedes i under a domain-like partial order
  monotonicity of h is not strictly necessary; h must be bounded by D*)
lemma lfp_mono:
  assumes hmono: "bnd_mono D h"
      and imono: "bnd_mono E i"
      and subhi: "!!X. X\<subseteq>D ==> h(X) \<subseteq> i(X)"
    shows "lfp D h \<subseteq> lfp E i"
apply (rule bnd_monoD1 [THEN lfp_greatest])
apply (rule imono)
apply (rule hmono [THEN [2] lfp_Int_lowerbound])
apply (rule Int_lower1 [THEN subhi, THEN subset_trans])
apply (rule imono [THEN bnd_monoD2, THEN subset_trans], auto) 
done

(*This (unused) version illustrates that monotonicity is not really needed,
  but both lfp's must be over the SAME set D;  Inter is anti-monotonic!*)
lemma lfp_mono2:
    "[| i(D) \<subseteq> D;  !!X. X\<subseteq>D ==> h(X) \<subseteq> i(X)  |] ==> lfp D h \<subseteq> lfp D i"
apply (rule lfp_greatest, assumption)
apply (rule lfp_lowerbound, blast, assumption)
done

lemma lfp_cong:
  assumes D: "D = D'"
  assumes h: "\<And>X. X \<subseteq> D' \<Longrightarrow> h X = h' X"
  shows "lfp D h = lfp D' h'"
proof -
  have "{x \<in> Pow D | h x \<subseteq> x} = {x \<in> Pow D' | h' x \<subseteq> x}" unfolding D
    by (rule Collect_cong) (auto simp: h)
  then show ?thesis by  (simp add: lfp_def)
qed


subsection\<open>Proof of Knaster-Tarski Theorem using greatest fixed-points.\<close>

definition 
  gfp      :: "set \<Rightarrow> (set \<Rightarrow> set) \<Rightarrow> set"  where
     "gfp D h == \<Union>({X\<in> Pow(D). X \<subseteq> h(X)})"

(*gfp contains each post-fixedpoint that is contained in D*)
lemma gfp_upperbound: "[| A \<subseteq> h(A);  A\<subseteq>D |] ==> A \<subseteq> gfp D h"
  unfolding gfp_def by blast

lemma gfp_subset: "gfp D h \<subseteq> D"
  unfolding gfp_def by blast

(*Used in datatype package*)
lemma def_gfp_subset: "A==gfp D h ==> A \<subseteq> D"
  using gfp_subset by blast

lemma gfp_least: 
    "[| bnd_mono D h;  !!X. [| X \<subseteq> h(X);  X\<subseteq>D |] ==> X\<subseteq>A |] ==>  
     gfp D h \<subseteq> A"
  unfolding gfp_def by blast

lemma gfp_lemma1: 
    "[| bnd_mono D h;  A\<subseteq>h(A);  A\<subseteq>D |] ==> A \<subseteq> h(gfp D h)"
apply (rule subset_trans, assumption)
apply (erule bnd_monoD2)
apply (rule_tac [2] gfp_subset)
apply (simp add: gfp_upperbound)
done

lemma gfp_lemma2: "bnd_mono D h ==> gfp D h \<subseteq> h(gfp D h)"
apply (rule gfp_least)
apply (rule_tac [2] gfp_lemma1)
apply (assumption+)
done

lemma gfp_lemma3: 
    "bnd_mono D h ==> h(gfp D h) \<subseteq> gfp D h"
apply (rule gfp_upperbound)
apply (rule bnd_monoD2, assumption)
apply (rule gfp_lemma2, assumption)
apply (erule bnd_mono_subset, rule gfp_subset)+
done

lemma gfp_unfold: "bnd_mono D h ==> gfp D h = h (gfp D h)"
apply (rule extensionality) 
apply (erule gfp_lemma2) 
apply (erule gfp_lemma3) 
done

(*Definition form, to control unfolding*)
lemma def_gfp_unfold:
    "[| A==gfp D h;  bnd_mono D h |] ==> A = h(A)"
apply simp
apply (erule gfp_unfold)
done


subsection\<open>Coinduction Rules for Greatest Fixed Points\<close>

(*weak version*)
lemma weak_coinduct: "a \<in> X \<Longrightarrow> X \<subseteq> h X \<Longrightarrow> X \<subseteq> D \<Longrightarrow> a \<in> gfp D h"
  using gfp_upperbound[of X h D] by auto


lemma coinduct_lemma:
    "[| X \<subseteq> h(X \<union> gfp D h);  X \<subseteq> D;  bnd_mono D h |] ==>   
     X \<union> gfp D h \<subseteq> h(X \<union> gfp D h)"
apply (erule Un_least)
apply (rule gfp_lemma2 [THEN subset_trans], assumption)
apply (rule Un_upper2 [THEN subset_trans])
apply (rule bnd_mono_Un, assumption+) 
apply (rule gfp_subset)
done

(*strong version*)
lemma coinduct:
     "[| bnd_mono D h;  a\<in> X;  X \<subseteq> h(X \<union> gfp D h);  X \<subseteq> D |]
      ==> a \<in> gfp D h"
apply (rule weak_coinduct)
apply (erule_tac [2] coinduct_lemma)
apply (simp_all add: gfp_subset Un_subset_iff) 
done

(*Definition form, to control unfolding*)
lemma def_coinduct:
    "[| A == gfp D h;  bnd_mono D h;  a\<in> X;  X \<subseteq> h(X \<union> A);  X \<subseteq> D |] ==>  
     a \<in> A"
apply simp
apply (rule coinduct, assumption+)
done

(*The version used in the induction/coinduction package*)
lemma def_Collect_coinduct:
    "[| A == gfp D (%w. Collect D (P w));  bnd_mono D (%w. Collect D (P w));   
        a\<in> X;  X \<subseteq> D;  !!z. z\<in> X ==> P(X \<union> A) z |] ==>  
     a \<in> A"
apply (rule def_coinduct, assumption+, blast+)
done

(*Monotonicity of gfp!*)
lemma gfp_mono:
    "[| bnd_mono D h;  D \<subseteq> E;                  
        !!X. X\<subseteq>D ==> h(X) \<subseteq> i(X)  |] ==> gfp D h \<subseteq> gfp E i"
    apply (rule gfp_upperbound)
apply (rule gfp_lemma2 [THEN subset_trans], assumption)
apply (blast del: subsetI intro: gfp_subset) 
apply (blast del: subsetI intro: subset_trans gfp_subset) 
done

end
