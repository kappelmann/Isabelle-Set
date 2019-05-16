(*  Title:      ZF/pair.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge
*)

section\<open>Ordered Pairs\<close>

theory Ordered_Pair imports Unordered_Pair 
begin

ML_file "simpdata.ML"

setup \<open>
  map_theory_simpset
    (Simplifier.set_mksimps (fn ctxt => map mk_eq o ZF_atomize o Variable.gen_all ctxt)
      #> Simplifier.add_cong @{thm if_weak_cong})
\<close>

ML \<open>val ZF_ss = simpset_of @{context}\<close>

simproc_setup defined_Bex ("\<exists>x\<in>A. P(x) & Q(x)") = \<open>
  fn _ => Quantifier1.rearrange_bex
    (fn ctxt =>
      unfold_tac ctxt @{thms Bex_def} THEN
      Quantifier1.prove_one_point_ex_tac ctxt)
\<close>

simproc_setup defined_Ball ("\<forall>x\<in>A. P(x) \<longrightarrow> Q(x)") = \<open>
  fn _ => Quantifier1.rearrange_ball
    (fn ctxt =>
      unfold_tac ctxt @{thms Ball_def} THEN
      Quantifier1.prove_one_point_all_tac ctxt)
\<close>

subsection \<open>Ordered Pairing\<close>

(* this "symmetric" definition works better than {{a}, {a,b}} *)
definition Pair :: "[i, i] => i"
  where "Pair a b == {{a,a}, {a,b}}"

definition fst :: "i \<Rightarrow> i"
  where "fst(p) == THE a. \<exists>b. p = Pair a b"

definition snd :: "i \<Rightarrow> i"
  where "snd(p) == THE b. \<exists>a. p = Pair a b"

definition split :: "[[i, i] \<Rightarrow> 'a, i] \<Rightarrow> 'a::{}"  \<comment> \<open>for pattern-matching\<close>
  where "split(c) == \<lambda>p. c (fst p) (snd p)"

(* Patterns -- extends pre-defined type "pttrn" used in abstractions *)
nonterminal patterns
syntax
  "_pattern"  :: "patterns => pttrn"         ("\<langle>_\<rangle>")
  ""          :: "pttrn => patterns"         ("_")
  "_patterns" :: "[pttrn, patterns] => patterns"  ("_,/_")
  "_Tuple"    :: "[i, is] => i"              ("\<langle>(_,/ _)\<rangle>")
translations
  "\<langle>x, y, z\<rangle>"   == "\<langle>x, \<langle>y, z\<rangle>\<rangle>"
  "\<langle>x, y\<rangle>"      == "CONST Pair x y"
  "\<lambda>\<langle>x,y,zs\<rangle>.b" == "CONST split(\<lambda>x \<langle>y,zs\<rangle>.b)"
  "\<lambda>\<langle>x,y\<rangle>.b"    == "CONST split(\<lambda>x y. b)"

definition Sigma :: "[i, i \<Rightarrow> i] \<Rightarrow> i"
  where "Sigma A B == \<Union>x\<in>A. \<Union>y\<in>B(x). {\<langle>x,y\<rangle>}"

abbreviation cart_prod :: "[i, i] => i"  (infixr "\<times>" 80)  \<comment> \<open>Cartesian product\<close>
  where "A \<times> B \<equiv> Sigma A (\<lambda>_. B)"





(** Lemmas for showing that <a,b> uniquely determines a and b **)

lemma singleton_eq_iff [iff]: "{a} = {b} \<longleftrightarrow> a=b"
by (rule extension [THEN iff_trans], blast)

lemma doubleton_eq_iff: "{a,b} = {c,d} \<longleftrightarrow> (a=c & b=d) | (a=d & b=c)"
by (rule extension [THEN iff_trans], blast)

lemma Pair_iff [simp]: "\<langle>a,b\<rangle> = \<langle>c,d\<rangle> \<longleftrightarrow> a=c & b=d"
by (simp add: Pair_def doubleton_eq_iff, blast)

lemmas Pair_inject = Pair_iff [THEN iffD1, THEN conjE, elim!]

lemmas Pair_inject1 = Pair_iff [THEN iffD1, THEN conjunct1]
lemmas Pair_inject2 = Pair_iff [THEN iffD1, THEN conjunct2]

lemma Pair_not_0: "\<langle>a,b\<rangle> \<noteq> {}"
apply (unfold Pair_def)
apply (blast elim: equalityE)
done

lemmas Pair_neq_0 = Pair_not_0 [THEN notE, elim!]

declare sym [THEN Pair_neq_0, elim!]

lemma Pair_neq_fst: "\<langle>a,b\<rangle>=a \<Longrightarrow> P"
proof (unfold Pair_def)
  assume eq: "{{a, a}, {a, b}} = a"
  have  "{a, a} \<in> {{a, a}, {a, b}}" by (rule consI1)
  hence "{a, a} \<in> a" by (simp add: eq)
  moreover have "a \<in> {a, a}" by (rule consI1)
  ultimately show "P" by (rule mem_asym)
qed

lemma Pair_neq_snd: "\<langle>a,b\<rangle>=b ==> P"
proof (unfold Pair_def)
  assume eq: "{{a, a}, {a, b}} = b"
  have  "{a, b} \<in> {{a, a}, {a, b}}" by blast
  hence "{a, b} \<in> b" by (simp add: eq)
  moreover have "b \<in> {a, b}" by blast
  ultimately show "P" by (rule mem_asym)
qed


subsection\<open>Sigma: Disjoint Union of a Family of Sets\<close>

text\<open>Generalizes Cartesian product\<close>

lemma Sigma_iff [simp]: "\<langle>a,b\<rangle>\<in> Sigma A B \<longleftrightarrow> a \<in> A & b \<in> B(a)"
by (simp add: Sigma_def)

lemma SigmaI [TC,intro!]: "[| a \<in> A;  b \<in> B(a) |] ==> \<langle>a,b\<rangle> \<in> Sigma A B"
by simp

lemmas SigmaD1 = Sigma_iff [THEN iffD1, THEN conjunct1]
lemmas SigmaD2 = Sigma_iff [THEN iffD1, THEN conjunct2]

(*The general elimination rule*)
lemma SigmaE [elim!]:
    "[| c \<in> Sigma A B;
        !!x y.[| x \<in> A;  y \<in> B(x);  c=\<langle>x,y\<rangle> |] ==> P
     |] ==> P"
by (unfold Sigma_def, blast)

lemma SigmaE2 [elim!]:
    "[| \<langle>a,b\<rangle> \<in> Sigma A B;
        [| a \<in> A;  b \<in> B(a) |] ==> P
     |] ==> P"
by (unfold Sigma_def, blast)

lemma Sigma_cong:
    "[| A=A';  !!x. x \<in> A' ==> B(x)=B'(x) |] ==>
     Sigma A B = Sigma A' B'"
by (simp add: Sigma_def)

(*Sigma_cong, Pi_cong NOT given to Addcongs: they cause
  flex-flex pairs and the "Check your prover" error.  Most
  Sigmas and Pis are abbreviated as * or -> *)

lemma Sigma_empty1 [simp]: "Sigma {} B = {}"
by blast

lemma Sigma_empty2 [simp]: "A \<times> {} = {}"
by blast

lemma Sigma_empty_iff: "A \<times> B = {} \<longleftrightarrow> A={} | B={}"
by blast


subsection\<open>Projections @{term fst} and @{term snd}\<close>

lemma fst_conv [simp]: "fst(\<langle>a,b\<rangle>) = a"
by (simp add: fst_def)

lemma snd_conv [simp]: "snd(\<langle>a,b\<rangle>) = b"
by (simp add: snd_def)

lemma fst_type [TC]: "p \<in> Sigma A B ==> fst(p) \<in> A"
by auto

lemma snd_type [TC]: "p \<in> Sigma A B ==> snd(p) \<in> B(fst(p))"
by auto

lemma Pair_fst_snd_eq: "a \<in> Sigma A B ==> \<langle>fst(a),snd(a)\<rangle> = a"
by auto


subsection\<open>The Eliminator, @{term split}\<close>

(*A META-equality, so that it applies to higher types as well...*)
lemma split [simp]: "split (%x y. c x y) \<langle>a,b\<rangle> == c a b"
by (simp add: split_def)

lemma split_type [TC]:
    "[|  p \<in> Sigma A B;
         !!x y.[| x \<in> A; y \<in> B(x) |] ==> c x y \<in> C \<langle>x,y\<rangle>
     |] ==> split (%x y. c x y) p \<in> C p"
by (erule SigmaE, auto)

lemma expand_split:
  "u \<in> A\<times>B ==>
        R (split c u) \<longleftrightarrow> (\<forall>x\<in>A. \<forall>y\<in>B. u = \<langle>x,y\<rangle> \<longrightarrow> R (c x y))"
by (auto simp add: split_def)


subsection\<open>A version of @{term split} for Formulae: Result Type @{typ o}\<close>

lemma splitI: "R a b ==> split R \<langle>a,b\<rangle>"
by (simp add: split_def)

lemma splitE:
    "[| split R z;  z \<in> Sigma A B;
        !!x y. [| z = \<langle>x,y\<rangle>;  R x y |] ==> P
     |] ==> P"
by (auto simp add: split_def)

lemma splitD: "split R \<langle>a,b\<rangle> ==> R a b"
by (simp add: split_def)

text \<open>
  \bigskip Complex rules for Sigma.
\<close>

lemma split_paired_Bex_Sigma [simp]:
     "(\<exists>z \<in> Sigma A B. P(z)) \<longleftrightarrow> (\<exists>x \<in> A. \<exists>y \<in> B(x). P(\<langle>x,y\<rangle>))"
by blast

lemma split_paired_Ball_Sigma [simp]:
     "(\<forall>z \<in> Sigma A B. P(z)) \<longleftrightarrow> (\<forall>x \<in> A. \<forall>y \<in> B(x). P(\<langle>x,y\<rangle>))"
by blast

end


