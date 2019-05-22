section \<open>Ordered Pairs\<close>

text \<open>
Based heavily on code copied directly from the theory file ZF/pair.thy
of the Isabelle/ZF object logic.

Modified 2019 Alexander Krauss (QAware GmbH) and Joshua Chen (University of Innsbruck).

Original ZF/Pair.thy by Lawrence C Paulson, Cambridge University Computer Laboratory,
Copyright 1992 University of Cambridge.
\<close>

theory Pair
imports Set_Theory 

begin

simproc_setup defined_Bex ("\<exists>x \<in> A. P x \<and> Q x") = \<open>
  fn _ => Quantifier1.rearrange_bex
    (fn ctxt =>
      unfold_tac ctxt @{thms Bex_def} THEN
      Quantifier1.prove_one_point_ex_tac ctxt)
\<close>

simproc_setup defined_Ball ("\<forall>x \<in> A. P x \<longrightarrow> Q x") = \<open>
  fn _ => Quantifier1.rearrange_ball
    (fn ctxt =>
      unfold_tac ctxt @{thms Ball_def} THEN
      Quantifier1.prove_one_point_all_tac ctxt)
\<close>


subsection \<open>Ordered pairs and tuples\<close>

text \<open>
It is easier to define the basic pair "symmetrically" as @{term "{{a, a}, {a, b}}"}, which makes proofs easier, and then show equality with the Kuratowski pair.
\<close>

definition Pair :: "set \<Rightarrow> set \<Rightarrow> set"
  where "Pair a b \<equiv> {{a, a}, {a, b}}"

definition fst :: "set \<Rightarrow> set"
  where "fst p \<equiv> THE a. \<exists>b. p = Pair a b"

definition snd :: "set \<Rightarrow> set"
  where "snd p \<equiv> THE b. \<exists>a. p = Pair a b"

syntax
  "_Tuple" :: "args \<Rightarrow> set" ("\<langle>(_)\<rangle>")
translations
  "\<langle>x, y, z\<rangle>" \<rightleftharpoons> "\<langle>x, \<langle>y, z\<rangle>\<rangle>"
  "\<langle>x, y\<rangle>" \<rightleftharpoons> "CONST Pair x y"


lemma Pair_iff [simp]: "\<langle>a, b\<rangle> = \<langle>c, d\<rangle> \<longleftrightarrow> a = c \<and> b = d"
  by (simp add: Pair_def doubleton_eq_iff) blast

lemmas Pair_inject = Pair_iff [THEN iffD1, THEN conjE, elim!]
lemmas Pair_inject1 = Pair_iff [THEN iffD1, THEN conjunct1]
lemmas Pair_inject2 = Pair_iff [THEN iffD1, THEN conjunct2]

lemma Pair_not_empty: "\<langle>a,b\<rangle> \<noteq> {}"
  apply (unfold Pair_def)
  apply (blast elim: equalityE)
  done

lemmas Pair_neq_empty = Pair_not_empty [THEN notE, elim!]

declare sym [THEN Pair_neq_empty, elim!]

lemma Pair_neq_fst: "\<langle>a, b\<rangle> = a \<Longrightarrow> P"
proof (unfold Pair_def)
  assume eq: "{{a, a}, {a, b}} = a"
  have "{a, a} \<in> {{a, a}, {a, b}}" by (rule consI1)
  hence "{a, a} \<in> a" by (simp add: eq)
  moreover have "a \<in> {a, a}" by (rule consI1)
  ultimately show "P" by (rule elem_asymE)
qed

lemma Pair_neq_snd: "\<langle>a,b\<rangle> = b \<Longrightarrow> P"
proof (unfold Pair_def)
  assume eq: "{{a, a}, {a, b}} = b"
  have "{a, b} \<in> {{a, a}, {a, b}}" by blast
  hence "{a, b} \<in> b" by (simp add: eq)
  moreover have "b \<in> {a, b}" by blast
  ultimately show "P" by (rule elem_asymE)
qed


lemma fst_conv [simp]: "fst(\<langle>a,b\<rangle>) = a"
  by (simp add: fst_def)

lemma snd_conv [simp]: "snd(\<langle>a,b\<rangle>) = b"
  by (simp add: snd_def)


text \<open>The definition above is equivalent to this more standard one:\<close>

lemma Kuratowski_Pair_def: "Pair a b = {{a}, {a, b}}"
  unfolding Pair_def by extensionality


subsection \<open>Disjoint union of a set-indexed family of sets\<close>

text \<open>Generalizes Cartesian product\<close>

definition Disj_Union :: "set \<Rightarrow> (set \<Rightarrow> set) \<Rightarrow> set"
  where "Disj_Union A B \<equiv> \<Union>x \<in> A. \<Union>y \<in> B x. {\<langle>x,y\<rangle>}"

abbreviation (input) "Sigma \<equiv> Disj_Union" \<comment> \<open>For Isabelle/ZF compatibility\<close>

syntax
  "_Disj_UNION" :: "[pttrn, set, set \<Rightarrow> set] \<Rightarrow> set" ("\<Coprod>_ \<in> _./ _" [0, 0, 100])
translations
  "\<Coprod>x \<in> A. B" \<rightleftharpoons> "CONST Disj_Union A (\<lambda>x. B)"

abbreviation cart_prod :: "set \<Rightarrow> set \<Rightarrow> set" (infixr "\<times>" 80)
  where "A \<times> B \<equiv> \<Coprod>_ \<in> A. B"

lemma Disj_Union_iff [simp]: "\<langle>a, b\<rangle> \<in> \<Coprod>x \<in> A. (B x) \<longleftrightarrow> a \<in> A \<and> b \<in> B a"
  by (auto simp: Disj_Union_def)

lemma Disj_UnionI [intro!]: "\<lbrakk>a \<in> A; b \<in> B a\<rbrakk> \<Longrightarrow> \<langle>a, b\<rangle> \<in> \<Coprod>x \<in> A. (B x)"
  by simp

lemmas Disj_UnionD1 = Disj_Union_iff [THEN iffD1, THEN conjunct1]
lemmas Disj_UnionD2 = Disj_Union_iff [THEN iffD1, THEN conjunct2]

(* The general elimination rule *)
lemma Disj_UnionE [elim!]:
  "\<lbrakk>c \<in> \<Coprod>x \<in> A. (B x); \<And>x y. \<lbrakk>x \<in> A; y \<in> B x; c = \<langle>x, y\<rangle>\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (unfold Disj_Union_def, blast)

lemma Disj_UnionE2 [elim!]:
  "\<lbrakk>\<langle>a, b\<rangle> \<in> \<Coprod>x \<in> A. (B x); \<lbrakk>a \<in> A; b \<in> B a\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (unfold Disj_Union_def, blast)

lemma Disj_Union_cong:
  "\<lbrakk>A = A'; \<And>x. x \<in> A' \<Longrightarrow> B x = B' x\<rbrakk> \<Longrightarrow> \<Coprod>x \<in> A. (B x) = \<Coprod>x \<in> A'. (B' x)"
  by (simp add: Disj_Union_def)

lemma Disj_Union_empty1 [simp]: "\<Coprod>x \<in> {}. (B x) = {}"
  by extensionality

lemma Disj_Union_empty2 [simp]: "A \<times> {} = {}"
  by extensionality

lemma Disj_Union_empty_iff: "A \<times> B = {} \<longleftrightarrow> A = {} \<or> B = {}"
  by (auto intro!: equality_iffI)


subsection \<open>Projections @{term fst} and @{term snd} for disjoint unions\<close>

lemma Disj_Union_fst: "p \<in> \<Coprod>x \<in> A. (B x) \<Longrightarrow> fst p \<in> A"
  by auto

lemma Disj_Union_snd: "p \<in> \<Coprod>x \<in> A. (B x) \<Longrightarrow> snd p \<in> B(fst p)"
  by auto

lemma Disj_Union_pair: "a \<in> \<Coprod>x \<in> A. (B x) \<Longrightarrow> \<langle>fst a, snd a\<rangle> = a"
  by auto


subsection \<open>Disjoint union as sigma type\<close>

definition split :: "(set \<Rightarrow> set \<Rightarrow> 'a) \<Rightarrow> set \<Rightarrow> 'a" \<comment>\<open>for pattern-matching\<close>
  where "split f \<equiv> \<lambda>p. f (fst p) (snd p)"

(* Patterns -- extends pre-defined type "pttrn" used in abstractions *)
nonterminal patterns
syntax
  "_pattern"  :: "patterns => pttrn" ("\<langle>_\<rangle>")
  ""          :: "pttrn => patterns" ("_")
  "_patterns" :: "[pttrn, patterns] => patterns" ("_,/ _")
translations
  "\<lambda>\<langle>x, y, zs\<rangle>. b" \<rightleftharpoons> "CONST split (\<lambda>x \<langle>y, zs\<rangle>. b)"
  "\<lambda>\<langle>x, y\<rangle>. b" \<rightleftharpoons> "CONST split (\<lambda>x y. b)"


lemma split [simp]: "split f \<langle>a, b\<rangle> \<equiv> f a b"
  by (simp add: split_def)

lemma split_type:
  "\<lbrakk>p \<in> \<Coprod>x \<in> A. (B x); \<And>x y.\<lbrakk>x \<in> A; y \<in> B x\<rbrakk> \<Longrightarrow> c x y \<in> C \<langle>x,y\<rangle>
    \<rbrakk> \<Longrightarrow> split c p \<in> C p"
  by (erule Disj_UnionE, auto)

lemma expand_split:
  "u \<in> A \<times> B \<Longrightarrow> R (split c u) \<longleftrightarrow> (\<forall>x \<in> A. \<forall>y \<in> B. u = \<langle>x,y\<rangle> \<longrightarrow> R (c x y))"
  by (force simp add: split_def)

lemma splitI: "R a b \<Longrightarrow> split R \<langle>a,b\<rangle>"
  by (simp add: split_def)

lemma splitE:
  "\<lbrakk>split R z; z \<in> \<Coprod>x \<in> A. (B x); \<And>x y. \<lbrakk>z = \<langle>x, y\<rangle>; R x y\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (auto simp add: split_def)

lemma splitD: "split R \<langle>a, b\<rangle> \<Longrightarrow> R a b"
  by (simp add: split_def)

text \<open>Complex rules for disjoint union.\<close>

lemma split_paired_Bex_Disj_Union [simp]:
  "(\<exists>z \<in> \<Coprod>x \<in> A. (B x). P z) \<longleftrightarrow> (\<exists>x \<in> A. \<exists>y \<in> B x. P \<langle>x, y\<rangle>)"
  by blast

lemma split_paired_Ball_Disj_Union [simp]:
  "(\<forall>z \<in> \<Coprod>x \<in> A. (B x). P z) \<longleftrightarrow> (\<forall>x \<in> A. \<forall>y \<in> B x. P \<langle>x,y\<rangle>)"
  by blast


subsection \<open>Typing rules\<close>

lemma Pair_type[type]: "Pair : [x: element A] \<Rightarrow> element (B x) \<Rightarrow> element (Disj_Union A B)"
proof (intro Pi_typeI)
  fix x y assume x: "x : element A" and y: "y : element (B x)"
  from x have "x \<in> A" by (rule element_typeE)
  moreover from y have "y \<in> B x" by (rule element_typeE)
  ultimately have "\<langle>x, y\<rangle> \<in> Disj_Union A B" by (rule Disj_UnionI)
  then show "\<langle>x, y\<rangle> : element (Disj_Union A B)" by (rule element_typeI)
qed





end
