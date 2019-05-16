(*  Title:      ZF/ZF_Base.thy
    Author:     Lawrence C Paulson and Martin D Coen, CU Computer Laboratory
    Copyright   1993  University of Cambridge
*)

section \<open>Base of Zermelo-Fraenkel Set Theory\<close>

theory Set_Theory
  imports Set_Theory_Axioms
  keywords "print_tcset" :: diag
begin



(* Functional form of replacement -- analgous to ML's map functional *)

definition RepFun :: "[i, i \<Rightarrow> i] \<Rightarrow> i"
  where "RepFun A f == {y . x\<in>A, y=f(x)}"

syntax
  "_RepFun" :: "[i, pttrn, i] => i"  ("(1{_ ./ _ \<in> _})" [51,0,51])
translations
  "{b. x\<in>A}" \<rightleftharpoons> "CONST RepFun A (\<lambda>x. b)"




subsection\<open>Bounded universal quantifier\<close>

lemma ballI [intro!]: "[| !!x. x\<in>A ==> P(x) |] ==> \<forall>x\<in>A. P(x)"
by (simp add: Ball_def)

lemmas strip = impI allI ballI

lemma bspec [dest?]: "[| \<forall>x\<in>A. P(x);  x\<in> A |] ==> P(x)"
by (simp add: Ball_def)

(*Instantiates x first: better for automatic theorem proving?*)
lemma rev_ballE [elim]:
    "[| \<forall>x\<in>A. P(x);  x\<notin>A ==> Q;  P(x) ==> Q |] ==> Q"
by (simp add: Ball_def, blast)

lemma ballE: "[| \<forall>x\<in>A. P(x);  P(x) ==> Q;  x\<notin>A ==> Q |] ==> Q"
by blast

(*Used in the datatype package*)
lemma rev_bspec: "[| x\<in> A;  \<forall>x\<in>A. P(x) |] ==> P(x)"
by (simp add: Ball_def)

(*Trival rewrite rule;   @{term"(\<forall>x\<in>A.P)<->P"} holds only if A is nonempty!*)
lemma ball_triv [simp]: "(\<forall>x\<in>A. P) <-> ((\<exists>x. x\<in>A) \<longrightarrow> P)"
by (simp add: Ball_def)

(*Congruence rule for rewriting*)
lemma ball_cong [cong]:
    "[| A=A';  !!x. x\<in>A' ==> P(x) <-> P'(x) |] ==> (\<forall>x\<in>A. P(x)) <-> (\<forall>x\<in>A'. P'(x))"
by (simp add: Ball_def)

lemma atomize_ball:
    "(!!x. x \<in> A ==> P(x)) == Trueprop (\<forall>x\<in>A. P(x))"
  by (simp only: Ball_def atomize_all atomize_imp)

lemmas [symmetric, rulify] = atomize_ball
  and [symmetric, defn] = atomize_ball


subsection\<open>Bounded existential quantifier\<close>

lemma bexI [intro]: "[| P(x);  x\<in> A |] ==> \<exists>x\<in>A. P(x)"
by (simp add: Bex_def, blast)

(*The best argument order when there is only one @{term"x\<in>A"}*)
lemma rev_bexI: "[| x\<in>A;  P(x) |] ==> \<exists>x\<in>A. P(x)"
by blast

(*Not of the general form for such rules. The existential quanitifer becomes universal. *)
lemma bexCI: "[| \<forall>x\<in>A. ~P(x) ==> P(a);  a\<in> A |] ==> \<exists>x\<in>A. P(x)"
by blast

lemma bexE [elim!]: "[| \<exists>x\<in>A. P(x);  !!x. [| x\<in>A; P(x) |] ==> Q |] ==> Q"
by (simp add: Bex_def, blast)

(*We do not even have @{term"(\<exists>x\<in>A. True) <-> True"} unless @{term"A" is nonempty!!*)
lemma bex_triv [simp]: "(\<exists>x\<in>A. P) <-> ((\<exists>x. x\<in>A) & P)"
by (simp add: Bex_def)

lemma bex_cong [cong]:
    "[| A=A';  !!x. x\<in>A' ==> P(x) <-> P'(x) |]
     ==> (\<exists>x\<in>A. P(x)) <-> (\<exists>x\<in>A'. P'(x))"
by (simp add: Bex_def cong: conj_cong)



subsection\<open>Rules for subsets\<close>

lemma subsetI [intro!]:
    "(!!x. x\<in>A ==> x\<in>B) ==> A \<subseteq> B"
by (simp add: subset_def)

(*Rule in Modus Ponens style [was called subsetE] *)
lemma subsetD [elim]: "[| A \<subseteq> B;  c\<in>A |] ==> c\<in>B"
apply (unfold subset_def)
apply (erule bspec, assumption)
done

(*Classical elimination rule*)
lemma subsetCE [elim]:
    "[| A \<subseteq> B;  c\<notin>A ==> P;  c\<in>B ==> P |] ==> P"
by (simp add: subset_def, blast)

(*Sometimes useful with premises in this order*)
lemma rev_subsetD: "[| c\<in>A; A\<subseteq>B |] ==> c\<in>B"
by blast

lemma contra_subsetD: "[| A \<subseteq> B; c \<notin> B |] ==> c \<notin> A"
by blast

lemma rev_contra_subsetD: "[| c \<notin> B;  A \<subseteq> B |] ==> c \<notin> A"
by blast

lemma subset_refl [simp]: "A \<subseteq> A"
by blast

lemma subset_trans: "[| A\<subseteq>B;  B\<subseteq>C |] ==> A\<subseteq>C"
by blast

(*Useful for proving A<=B by rewriting in some cases*)
lemma subset_iff:
     "A\<subseteq>B <-> (\<forall>x. x\<in>A \<longrightarrow> x\<in>B)"
apply (unfold subset_def Ball_def)
apply (rule iff_refl)
done

text\<open>For calculations\<close>
declare subsetD [trans] rev_subsetD [trans] subset_trans [trans]


subsection\<open>Rules for equality\<close>

(*Anti-symmetry of the subset relation*)
lemma equalityI [intro]: "[| A \<subseteq> B;  B \<subseteq> A |] ==> A = B"
by (rule extension [THEN iffD2], rule conjI)


lemma equality_iffI: "(!!x. x\<in>A <-> x\<in>B) ==> A = B"
by (rule equalityI, blast+)

lemmas equalityD1 = extension [THEN iffD1, THEN conjunct1]
lemmas equalityD2 = extension [THEN iffD1, THEN conjunct2]

lemma equalityE: "[| A = B;  [| A\<subseteq>B; B\<subseteq>A |] ==> P |]  ==>  P"
by (blast dest: equalityD1 equalityD2)

lemma equalityCE:
    "[| A = B;  [| c\<in>A; c\<in>B |] ==> P;  [| c\<notin>A; c\<notin>B |] ==> P |]  ==>  P"
by (erule equalityE, blast)

lemma equality_iffD:
  "A = B ==> (!!x. x \<in> A <-> x \<in> B)"
  by auto


subsection\<open>Rules for Replace -- the derived form of replacement\<close>

lemma Replace_iff:
    "b \<in> {y. x\<in>A, P x y}  <->  (\<exists>x\<in>A. P x b & (\<forall>y. P x y \<longrightarrow> y=b))"
apply (unfold Replace_def)
apply (rule replacement [THEN iff_trans], blast+)
done

(*Introduction; there must be a unique y such that P(x,y), namely y=b. *)
lemma ReplaceI [intro]:
    "[| P x b;  x\<in> A;  !!y. P x y ==> y=b |] ==>
     b \<in> {y. x\<in>A, P x y}"
by (rule Replace_iff [THEN iffD2], blast)

(*Elimination; may asssume there is a unique y such that P(x,y), namely y=b. *)
lemma ReplaceE:
    "[| b \<in> {y. x\<in>A, P x y};
        !!x. [| x\<in> A;  P x b;  \<forall>y. P x y \<longrightarrow> y=b |] ==> R
     |] ==> R"
by (rule Replace_iff [THEN iffD1, THEN bexE], simp+)

(*As above but without the (generally useless) 3rd assumption*)
lemma ReplaceE2 [elim!]:
    "[| b \<in> {y. x\<in>A, P x y};
        !!x. [| x\<in> A;  P x b |] ==> R
     |] ==> R"
by (erule ReplaceE, blast)

lemma Replace_cong [cong]:
    "[| A=B;  !!x y. x\<in>B ==> P x y <-> Q x y |] ==>
     Replace A P = Replace B Q"
apply (rule equality_iffI)
apply (simp add: Replace_iff)
done


subsection\<open>Rules for RepFun\<close>

lemma RepFunI: "a \<in> A ==> f(a) \<in> {f(x). x\<in>A}"
by (simp add: RepFun_def Replace_iff, blast)

(*Useful for coinduction proofs*)
lemma RepFun_eqI [intro]: "[| b=f(a);  a \<in> A |] ==> b \<in> {f(x). x\<in>A}"
apply (erule ssubst)
apply (erule RepFunI)
done

lemma RepFunE [elim!]:
    "[| b \<in> {f(x). x\<in>A};
        !!x.[| x\<in>A;  b=f(x) |] ==> P |] ==>
     P"
by (simp add: RepFun_def Replace_iff, blast)

lemma RepFun_cong [cong]:
    "[| A=B;  !!x. x\<in>B ==> f(x)=g(x) |] ==> RepFun A f = RepFun B g"
by (simp add: RepFun_def)

lemma RepFun_iff [simp]: "b \<in> {f(x). x\<in>A} <-> (\<exists>x\<in>A. b=f(x))"
by (unfold Bex_def, blast)

lemma triv_RepFun [simp]: "{x. x\<in>A} = A"
by blast


subsection\<open>Rules for Collect -- forming a subset by separation\<close>

(*Separation is derivable from Replacement*)
lemma separation [simp]: "a \<in> {x\<in>A. P(x)} <-> a\<in>A & P(a)"
by (unfold Collect_def, blast)

lemma CollectI [intro!]: "[| a\<in>A;  P(a) |] ==> a \<in> {x\<in>A. P(x)}"
by simp

lemma CollectE [elim!]: "[| a \<in> {x\<in>A. P(x)};  [| a\<in>A; P(a) |] ==> R |] ==> R"
by simp

lemma CollectD1: "a \<in> {x\<in>A. P(x)} ==> a\<in>A"
by (erule CollectE, assumption)

lemma CollectD2: "a \<in> {x\<in>A. P(x)} ==> P(a)"
by (erule CollectE, assumption)

lemma Collect_cong [cong]:
    "[| A=B;  !!x. x\<in>B ==> P(x) <-> Q(x) |]
     ==> Collect A (%x. P(x)) = Collect B (%x. Q(x))"
by (simp add: Collect_def)


subsection\<open>Rules for Unions\<close>

declare Union_iff [simp]

(*The order of the premises presupposes that C is rigid; A may be flexible*)
lemma UnionI [intro]: "[| B\<in> C;  A\<in> B |] ==> A\<in> \<Union>(C)"
by (simp, blast)

lemma UnionE [elim!]: "[| A \<in> \<Union>(C);  !!B.[| A\<in> B;  B\<in> C |] ==> R |] ==> R"
by (simp, blast)








subsection\<open>Rules for the empty set\<close>


lemma not_mem_empty [simp]: "a \<notin> {}"
apply (cut_tac foundation)
apply (best dest: equalityD2)
done

lemmas emptyE [elim!] = not_mem_empty [THEN notE]


lemma empty_subsetI [simp]: "{} \<subseteq> A"
by blast

lemma equals0I: "[| !!y. y\<in>A ==> False |] ==> A={}"
by blast

lemma equals0D [dest]: "A={} ==> a \<notin> A"
by blast

declare sym [THEN equals0D, dest]

lemma not_emptyI: "a\<in>A ==> A \<noteq> {}"
by blast

lemma not_emptyE:  "[| A \<noteq> {};  !!x. x\<in>A ==> R |] ==> R"
by blast








subsection \<open>General union and intersection\<close>

definition Inter :: "i => i"  ("\<Inter>_" [90] 90)
  where "\<Inter>(A) == { x\<in>\<Union>(A) . \<forall>y\<in>A. x\<in>y}"

definition Diff :: "[i, i] \<Rightarrow> i"  (infixl "-" 65)  \<comment> \<open>set difference\<close>
  where "A - B == { x\<in>A . ~(x\<in>B) }"

definition Int :: "[i, i] \<Rightarrow> i"  (infixl "\<inter>" 70)  \<comment> \<open>binary intersection\<close>
  where "A \<inter> B == \<Inter>(Upair A B)"


syntax
  "_UNION" :: "[pttrn, i, i] => i"  ("(3\<Union>_\<in>_./ _)" 10)
  "_INTER" :: "[pttrn, i, i] => i"  ("(3\<Inter>_\<in>_./ _)" 10)
translations
  "\<Union>x\<in>A. B" == "CONST Union {B. x\<in>A}"
  "\<Inter>x\<in>A. B" == "CONST Inter {B. x\<in>A}"


subsection\<open>Rules for Unions of families\<close>
(* @{term"\<Union>x\<in>A. B(x)"} abbreviates @{term"\<Union>({B(x). x\<in>A})"} *)

lemma UN_iff [simp]: "b \<in> (\<Union>x\<in>A. B(x)) <-> (\<exists>x\<in>A. b \<in> B(x))"
by (simp add: Bex_def, blast)

(*The order of the premises presupposes that A is rigid; b may be flexible*)
lemma UN_I: "[| a\<in> A;  b\<in> B(a) |] ==> b\<in> (\<Union>x\<in>A. B(x))"
by (simp, blast)


lemma UN_E [elim!]:
    "[| b \<in> (\<Union>x\<in>A. B(x));  !!x.[| x\<in> A;  b\<in> B(x) |] ==> R |] ==> R"
by blast

lemma UN_cong:
    "[| A=B;  !!x. x\<in>B ==> C(x)=D(x) |] ==> (\<Union>x\<in>A. C(x)) = (\<Union>x\<in>B. D(x))"
by simp




lemma Inter_iff: "A \<in> \<Inter>(C) <-> (\<forall>x\<in>C. A\<in> x) & C\<noteq>{}"
by (simp add: Inter_def Ball_def, blast)

(* Intersection is well-behaved only if the family is non-empty! *)
lemma InterI [intro!]:
    "[| !!x. x\<in> C ==> A\<in> x;  C\<noteq>{} |] ==> A \<in> \<Inter>(C)"
by (simp add: Inter_iff)

(*A "destruct" rule -- every B in C contains A as an element, but
  A\<in>B can hold when B\<in>C does not!  This rule is analogous to "spec". *)
lemma InterD [elim, Pure.elim]: "[| A \<in> \<Inter>(C);  B \<in> C |] ==> A \<in> B"
by (unfold Inter_def, blast)

(*"Classical" elimination rule -- does not require exhibiting @{term"B\<in>C"} *)
lemma InterE [elim]:
    "[| A \<in> \<Inter>(C);  B\<notin>C ==> R;  A\<in>B ==> R |] ==> R"
by (simp add: Inter_def, blast)




(* @{term"\<Inter>x\<in>A. B(x)"} abbreviates @{term"\<Inter>({B(x). x\<in>A})"} *)

lemma INT_iff: "b \<in> (\<Inter>x\<in>A. B(x)) <-> (\<forall>x\<in>A. b \<in> B(x)) & A\<noteq>{}"
by (force simp add: Inter_def)

lemma INT_I: "[| !!x. x\<in> A ==> b\<in> B(x);  A\<noteq>{} |] ==> b\<in> (\<Inter>x\<in>A. B(x))"
by blast

lemma INT_E: "[| b \<in> (\<Inter>x\<in>A. B(x));  a\<in> A |] ==> b \<in> B(a)"
by blast

lemma INT_cong:
    "[| A=B;  !!x. x\<in>B ==> C(x)=D(x) |] ==> (\<Inter>x\<in>A. C(x)) = (\<Inter>x\<in>B. D(x))"
by simp





subsection\<open>Rules for Powersets\<close>

lemma PowI: "A \<subseteq> B ==> A \<in> Pow(B)"
by (erule Pow_iff [THEN iffD2])

lemma PowD: "A \<in> Pow(B)  ==>  A\<subseteq>B"
by (erule Pow_iff [THEN iffD1])

declare Pow_iff [iff]

lemmas Pow_bottom = empty_subsetI [THEN PowI]    \<comment>\<open>@{term"{} \<in> Pow(B)"}\<close>
lemmas Pow_top = subset_refl [THEN PowI]         \<comment>\<open>@{term"A \<in> Pow(A)"}\<close>



subsection\<open>Unordered Pairs: constant @{term Upair}\<close>

lemma Upair_iff [simp]: "c \<in> Upair a b \<longleftrightarrow> (c=a | c=b)"
  by (unfold Upair_def, blast)

lemma UpairI1: "a \<in> Upair a b"
by simp

lemma UpairI2: "b \<in> Upair a b"
by simp

lemma UpairE: "[| a \<in> Upair b c;  a=b ==> P;  a=c ==> P |] ==> P"
by (simp, blast)

subsection\<open>Rules for Binary Union, Defined via @{term Upair}\<close>

lemma Un_iff [simp]: "c \<in> A \<union> B \<longleftrightarrow> (c \<in> A | c \<in> B)"
apply (simp add: Un_def)
apply (blast intro: UpairI1 UpairI2 elim: UpairE)
done

lemma UnI1 [elim?]: "c \<in> A ==> c \<in> A \<union> B"
by simp

lemma UnI2 [elim?]: "c \<in> B ==> c \<in> A \<union> B"
by simp

lemma UnE [elim!]: "[| c \<in> A \<union> B;  c \<in> A ==> P;  c \<in> B ==> P |] ==> P"
by (simp, blast)

(*Stronger version of the rule above*)
lemma UnE': "[| c \<in> A \<union> B;  c \<in> A ==> P;  [| c \<in> B;  c\<notin>A |] ==> P |] ==> P"
by (simp, blast)

(*Classical introduction rule: no commitment to A vs B*)
lemma UnCI [intro!]: "(c \<notin> B ==> c \<in> A) ==> c \<in> A \<union> B"
by (simp, blast)

subsection\<open>Rules for Binary Intersection, Defined via @{term Upair}\<close>

lemma Int_iff [simp]: "c \<in> A \<inter> B \<longleftrightarrow> (c \<in> A & c \<in> B)"
apply (unfold Int_def)
apply (blast intro: UpairI1 UpairI2 elim: UpairE)
done

lemma IntI [intro!]: "[| c \<in> A;  c \<in> B |] ==> c \<in> A \<inter> B"
by simp

lemma IntD1: "c \<in> A \<inter> B ==> c \<in> A"
by simp

lemma IntD2: "c \<in> A \<inter> B ==> c \<in> B"
by simp

lemma IntE [elim!]: "[| c \<in> A \<inter> B;  [| c \<in> A; c \<in> B |] ==> P |] ==> P"
by simp


subsection\<open>Rules for Set Difference, Defined via @{term Upair}\<close>

lemma Diff_iff [simp]: "c \<in> A-B \<longleftrightarrow> (c \<in> A & c\<notin>B)"
by (unfold Diff_def, blast)

lemma DiffI [intro!]: "[| c \<in> A;  c \<notin> B |] ==> c \<in> A - B"
by simp

lemma DiffD1: "c \<in> A - B ==> c \<in> A"
by simp

lemma DiffD2: "c \<in> A - B ==> c \<notin> B"
by simp

lemma DiffE [elim!]: "[| c \<in> A - B;  [| c \<in> A; c\<notin>B |] ==> P |] ==> P"
by simp


subsection\<open>Rules for @{term cons}\<close>

lemma cons_iff [simp]: "a \<in> cons b A \<longleftrightarrow> (a=b | a \<in> A)"
apply (unfold cons_def)
apply (blast intro: UpairI1 UpairI2 elim: UpairE)
done

lemma consI1 [simp]: "a \<in> cons a B"
by simp


lemma consI2: "a \<in> B ==> a \<in> cons b B"
by simp

lemma consE [elim!]: "[| a \<in> cons b A;  a=b ==> P;  a \<in> A ==> P |] ==> P"
by (simp, blast)

(*Stronger version of the rule above*)
lemma consE':
    "[| a \<in> cons b A;  a=b ==> P;  [| a \<in> A;  a\<noteq>b |] ==> P |] ==> P"
by (simp, blast)

(*Classical introduction rule*)
lemma consCI [intro!]: "(a\<notin>B ==> a=b) ==> a \<in> cons b B"
by (simp, blast)

lemma cons_not_0 [simp]: "cons a B \<noteq> {}"
by (blast elim: equalityE)

lemmas cons_neq_0 = cons_not_0 [THEN notE]

declare cons_not_0 [THEN not_sym, simp]



subsection \<open> Finite set syntax \<close>

nonterminal "is"
syntax
  "" :: "i \<Rightarrow> is"  ("_")
  "_Enum" :: "[i, is] \<Rightarrow> is"  ("_,/ _")
  "_Finset" :: "is \<Rightarrow> i"  ("{(_)}")
translations
  "{x, xs}" == "CONST cons x {xs}"
  "{x}" == "CONST cons x {}"


subsection\<open>Consequences of Foundation\<close>

(*was called mem_anti_sym*)
lemma mem_asym: "[| a \<in> b;  ~P ==> b \<in> a |] ==> P"
apply (rule classical)
apply (rule_tac A1 = "{a,b}" in foundation [THEN disjE])
apply (blast elim!: equalityE)+
done

(*was called mem_anti_refl*)
lemma mem_irrefl: "a \<in> a ==> P"
by (blast intro: mem_asym)

(*mem_irrefl should NOT be added to default databases:
      it would be tried on most goals, making proofs slower!*)

lemma mem_not_refl: "a \<notin> a"
apply (rule notI)
apply (erule mem_irrefl)
done

(*Good for proving inequalities by rewriting*)
lemma mem_imp_not_eq: "a \<in> A ==> a \<noteq> A"
by (blast elim!: mem_irrefl)

lemma eq_imp_not_mem: "a=A ==> a \<notin> A"
by (blast intro: elim: mem_irrefl)

subsection\<open>Rules for Successor\<close>

lemma succ_iff: "i \<in> succ(j) \<longleftrightarrow> i=j | i \<in> j"
by (unfold succ_def, blast)

lemma succI1 [simp]: "i \<in> succ(i)"
by (simp add: succ_iff)

lemma succI2: "i \<in> j ==> i \<in> succ(j)"
by (simp add: succ_iff)

lemma succE [elim!]:
    "[| i \<in> succ(j);  i=j ==> P;  i \<in> j ==> P |] ==> P"
apply (simp add: succ_iff, blast)
done

(*Classical introduction rule*)
lemma succCI [intro!]: "(i\<notin>j ==> i=j) ==> i \<in> succ(j)"
by (simp add: succ_iff, blast)

lemma succ_not_0 [simp]: "succ(n) \<noteq> {}"
by (blast elim!: equalityE)

lemmas succ_neq_0 = succ_not_0 [THEN notE, elim!]

declare succ_not_0 [THEN not_sym, simp]
declare sym [THEN succ_neq_0, elim!]

(* @{term"succ(c) \<subseteq> B ==> c \<in> B"} *)
lemmas succ_subsetD = succI1 [THEN [2] subsetD]

(* @{term"succ(b) \<noteq> b"} *)
lemmas succ_neq_self = succI1 [THEN mem_imp_not_eq, THEN not_sym]

lemma succ_inject_iff [simp]: "succ(m) = succ(n) \<longleftrightarrow> m=n"
by (blast elim: mem_asym elim!: equalityE)

lemmas succ_inject = succ_inject_iff [THEN iffD1, dest!]



subsection \<open>Definite descriptions -- via Replace over the set "1"\<close>

definition The :: "(i \<Rightarrow> o) \<Rightarrow> i"  (binder "THE " 10)
  where the_def: "The(P)    == \<Union>({y . x \<in> {{}}, P(y)})"


(*No congruence rule is necessary: if @{term"\<forall>y.P(y)\<longleftrightarrow>Q(y)"} then
  @{term "THE x.P(x)"}  rewrites to @{term "THE x.Q(x)"} *)

(*If it's "undefined", it's zero!*)
lemma the_0: "~ (\<exists>!x. P(x)) ==> (THE x. P(x))={}"
apply (unfold the_def)
apply (blast elim!: ReplaceE)
  done


lemma the_eq_0 [simp]: "(THE x. False) = {}"
by (blast intro: the_0)


lemma the_equality [intro]:
    "[| P(a);  !!x. P(x) ==> x=a |] ==> (THE x. P(x)) = a"
apply (unfold the_def)
apply (fast dest: subst)
done

(* Only use this if you already know \<exists>!x. P(x) *)
lemma the_equality2: "[| \<exists>!x. P(x);  P(a) |] ==> (THE x. P(x)) = a"
by blast

lemma theI: "\<exists>!x. P(x) ==> P(THE x. P(x))"
apply (erule ex1E)
apply (subst the_equality)
apply (blast+)
done


(*Easier to apply than theI: conclusion has only one occurrence of P*)
lemma theI2:
    assumes p1: "~ Q({}) ==> \<exists>!x. P(x)"
        and p2: "!!x. P(x) ==> Q(x)"
    shows "Q(THE x. P(x))"
apply (rule classical)
apply (rule p2)
apply (rule theI)
apply (rule classical)
apply (rule p1)
apply (erule the_0 [THEN subst], assumption)
done

lemma the_eq_trivial [simp]: "(THE x. x = a) = a"
by blast

lemma the_eq_trivial2 [simp]: "(THE x. a = x) = a"
by blast


subsection \<open> If-then-else \<close>

definition If :: "[o, i, i] \<Rightarrow> i"  ("(if (_)/ then (_)/ else (_))" [10] 10)
  where if_def: "if P then a else b == THE z. P & z=a | ~P & z=b"

lemma if_true [simp]: "(if True then a else b) = a"
by (unfold if_def, blast)

lemma if_false [simp]: "(if False then a else b) = b"
by (unfold if_def, blast)

(*Never use with case splitting, or if P is known to be true or false*)
lemma if_cong:
    "[| P\<longleftrightarrow>Q;  Q ==> a=c;  ~Q ==> b=d |]
     ==> (if P then a else b) = (if Q then c else d)"
by (simp add: if_def cong add: conj_cong)

(*Prevents simplification of x and y \<in> faster and allows the execution
  of functional programs. NOW THE DEFAULT.*)
lemma if_weak_cong: "P\<longleftrightarrow>Q ==> (if P then x else y) = (if Q then x else y)"
by simp

(*Not needed for rewriting, since P would rewrite to True anyway*)
lemma if_P: "P ==> (if P then a else b) = a"
by (unfold if_def, blast)

(*Not needed for rewriting, since P would rewrite to False anyway*)
lemma if_not_P: "~P ==> (if P then a else b) = b"
by (unfold if_def, blast)

lemma split_if [split]:
     "P(if Q then x else y) \<longleftrightarrow> ((Q \<longrightarrow> P(x)) & (~Q \<longrightarrow> P(y)))"
by (case_tac Q, simp_all)

(** Rewrite rules for boolean case-splitting: faster than split_if [split]
**)

lemmas split_if_eq1 = split_if [of "%x. x = b"] for b
lemmas split_if_eq2 = split_if [of "%x. a = x"] for a

lemmas split_if_mem1 = split_if [of "%x. x \<in> b"] for b
lemmas split_if_mem2 = split_if [of "%x. a \<in> x"] for a

lemmas split_ifs = split_if_eq1 split_if_eq2 split_if_mem1 split_if_mem2

(*Logically equivalent to split_if_mem2*)
lemma if_iff: "a\<in> (if P then x else y) \<longleftrightarrow> P & a \<in> x | ~P & a \<in> y"
by simp

lemma if_type:
    "[| P ==> a \<in> A;  ~P ==> b \<in> A |] ==> (if P then a else b)\<in> A"
by simp

(** Splitting IFs in the assumptions **)

lemma split_if_asm: "P(if Q then x else y) \<longleftrightarrow> (~((Q & ~P(x)) | (~Q & ~P(y))))"
by simp

lemmas if_splits = split_if split_if_asm




subsection\<open>Miniscoping of the Bounded Universal Quantifier\<close>

lemma ball_simps1:
     "(\<forall>x\<in>A. P(x) & Q)   \<longleftrightarrow> (\<forall>x\<in>A. P(x)) & (A={} | Q)"
     "(\<forall>x\<in>A. P(x) | Q)   \<longleftrightarrow> ((\<forall>x\<in>A. P(x)) | Q)"
     "(\<forall>x\<in>A. P(x) \<longrightarrow> Q) \<longleftrightarrow> ((\<exists>x\<in>A. P(x)) \<longrightarrow> Q)"
     "(~(\<forall>x\<in>A. P(x))) \<longleftrightarrow> (\<exists>x\<in>A. ~P(x))"
     "(\<forall>x\<in>{}.P(x)) \<longleftrightarrow> True"
     "(\<forall>x\<in>succ i. P(x)) \<longleftrightarrow> P(i) & (\<forall>x\<in>i. P x)"
     "(\<forall>x\<in>cons a B. P(x)) \<longleftrightarrow> P(a) & (\<forall>x\<in>B. P x)"
     "(\<forall>x\<in>RepFun A f. P(x)) \<longleftrightarrow> (\<forall>y\<in>A. P (f y))"
     "(\<forall>x\<in>\<Union>(A).P x) \<longleftrightarrow> (\<forall>y\<in>A. \<forall>x\<in>y. P x)"
by blast+

lemma ball_simps2:
     "(\<forall>x\<in>A. P & Q(x))   \<longleftrightarrow> (A={} | P) & (\<forall>x\<in>A. Q(x))"
     "(\<forall>x\<in>A. P | Q(x))   \<longleftrightarrow> (P | (\<forall>x\<in>A. Q(x)))"
     "(\<forall>x\<in>A. P \<longrightarrow> Q(x)) \<longleftrightarrow> (P \<longrightarrow> (\<forall>x\<in>A. Q(x)))"
by blast+

lemma ball_simps3:
     "(\<forall>x\<in>Collect A Q. P(x)) \<longleftrightarrow> (\<forall>x\<in>A. Q(x) \<longrightarrow> P(x))"
by blast+

lemmas ball_simps [simp] = ball_simps1 ball_simps2 ball_simps3

lemma ball_conj_distrib:
    "(\<forall>x\<in>A. P(x) & Q(x)) \<longleftrightarrow> ((\<forall>x\<in>A. P(x)) & (\<forall>x\<in>A. Q(x)))"
by blast


subsection\<open>Miniscoping of the Bounded Existential Quantifier\<close>

lemma bex_simps1:
     "(\<exists>x\<in>A. P(x) & Q) \<longleftrightarrow> ((\<exists>x\<in>A. P(x)) & Q)"
     "(\<exists>x\<in>A. P(x) | Q) \<longleftrightarrow> (\<exists>x\<in>A. P(x)) | (A\<noteq>{} & Q)"
     "(\<exists>x\<in>A. P(x) \<longrightarrow> Q) \<longleftrightarrow> ((\<forall>x\<in>A. P(x)) \<longrightarrow> (A\<noteq>{} & Q))"
     "(\<exists>x\<in>{}.P(x)) \<longleftrightarrow> False"
     "(\<exists>x\<in>succ(i).P(x)) \<longleftrightarrow> P(i) | (\<exists>x\<in>i. P(x))"
     "(\<exists>x\<in>cons a B. P(x)) \<longleftrightarrow> P(a) | (\<exists>x\<in>B. P(x))"
     "(\<exists>x\<in>RepFun A f. P(x)) \<longleftrightarrow> (\<exists>y\<in>A. P(f(y)))"
     "(\<exists>x\<in>\<Union>(A).P(x)) \<longleftrightarrow> (\<exists>y\<in>A. \<exists>x\<in>y.  P(x))"
     "(~(\<exists>x\<in>A. P(x))) \<longleftrightarrow> (\<forall>x\<in>A. ~P(x))"
by blast+

lemma bex_simps2:
     "(\<exists>x\<in>A. P & Q(x)) \<longleftrightarrow> (P & (\<exists>x\<in>A. Q(x)))"
     "(\<exists>x\<in>A. P | Q(x)) \<longleftrightarrow> (A\<noteq>{} & P) | (\<exists>x\<in>A. Q(x))"
     "(\<exists>x\<in>A. P \<longrightarrow> Q(x)) \<longleftrightarrow> ((A={} | P) \<longrightarrow> (\<exists>x\<in>A. Q(x)))"
by blast+

lemma bex_simps3:
     "(\<exists>x\<in>Collect A Q. P(x)) \<longleftrightarrow> (\<exists>x\<in>A. Q(x) & P(x))"
by blast

lemmas bex_simps [simp] = bex_simps1 bex_simps2 bex_simps3

lemma bex_disj_distrib:
    "(\<exists>x\<in>A. P(x) | Q(x)) \<longleftrightarrow> ((\<exists>x\<in>A. P(x)) | (\<exists>x\<in>A. Q(x)))"
by blast


(** One-point rule for bounded quantifiers: see HOL/Set.ML **)

lemma bex_triv_one_point1 [simp]: "(\<exists>x\<in>A. x=a) \<longleftrightarrow> (a \<in> A)"
by blast

lemma bex_triv_one_point2 [simp]: "(\<exists>x\<in>A. a=x) \<longleftrightarrow> (a \<in> A)"
by blast

lemma bex_one_point1 [simp]: "(\<exists>x\<in>A. x=a & P(x)) \<longleftrightarrow> (a \<in> A & P(a))"
by blast

lemma bex_one_point2 [simp]: "(\<exists>x\<in>A. a=x & P(x)) \<longleftrightarrow> (a \<in> A & P(a))"
by blast

lemma ball_one_point1 [simp]: "(\<forall>x\<in>A. x=a \<longrightarrow> P(x)) \<longleftrightarrow> (a \<in> A \<longrightarrow> P(a))"
by blast

lemma ball_one_point2 [simp]: "(\<forall>x\<in>A. a=x \<longrightarrow> P(x)) \<longleftrightarrow> (a \<in> A \<longrightarrow> P(a))"
by blast


subsection\<open>Miniscoping of the Replacement Operator\<close>

text\<open>These cover both @{term Replace} and @{term Collect}\<close>
lemma Rep_simps [simp]:
     "{x. y \<in> {}, R x y} = {}"
     "{x \<in> {}. P(x)} = {}"
     "{x \<in> A. Q} = (if Q then A else {})"
     "RepFun {} f = {}"
     "RepFun (succ i) f = cons (f i) (RepFun i f)"
     "RepFun (cons a B) f = cons (f a) (RepFun B f)"
by (simp_all, blast+)


subsection\<open>Miniscoping of Unions\<close>

lemma UN_simps1:
     "(\<Union>x\<in>C. cons a (B x)) = (if C={} then {} else cons a (\<Union>x\<in>C. B(x)))"
     "(\<Union>x\<in>C. A(x) \<union> B')   = (if C={} then {} else (\<Union>x\<in>C. A(x)) \<union> B')"
     "(\<Union>x\<in>C. A' \<union> B(x))   = (if C={} then {} else A' \<union> (\<Union>x\<in>C. B(x)))"
     "(\<Union>x\<in>C. A(x) \<inter> B')  = ((\<Union>x\<in>C. A(x)) \<inter> B')"
     "(\<Union>x\<in>C. A' \<inter> B(x))  = (A' \<inter> (\<Union>x\<in>C. B(x)))"
     "(\<Union>x\<in>C. A(x) - B')    = ((\<Union>x\<in>C. A(x)) - B')"
     "(\<Union>x\<in>C. A' - B(x))    = (if C={} then {} else A' - (\<Inter>x\<in>C. B(x)))"
apply (simp_all add: Inter_def)
apply (blast intro!: equalityI )+
done

lemma UN_simps2:
      "(\<Union>x\<in>\<Union>(A). B(x)) = (\<Union>y\<in>A. \<Union>x\<in>y. B(x))"
      "(\<Union>z\<in>(\<Union>x\<in>A. B(x)). C(z)) = (\<Union>x\<in>A. \<Union>z\<in>B(x). C(z))"
      "(\<Union>x\<in>RepFun A f. B(x)) = (\<Union>a\<in>A. B(f(a)))"
by blast+

lemmas UN_simps [simp] = UN_simps1 UN_simps2

text\<open>Opposite of miniscoping: pull the operator out\<close>

lemma UN_extend_simps1:
     "(\<Union>x\<in>C. A(x)) \<union> B   = (if C={} then B else (\<Union>x\<in>C. A(x) \<union> B))"
     "((\<Union>x\<in>C. A(x)) \<inter> B) = (\<Union>x\<in>C. A(x) \<inter> B)"
     "((\<Union>x\<in>C. A(x)) - B) = (\<Union>x\<in>C. A(x) - B)"
apply simp_all
apply blast+
done

lemma UN_extend_simps2:
     "cons a (\<Union>x\<in>C. B(x)) = (if C={} then {a} else (\<Union>x\<in>C. cons a (B x)))"
     "A \<union> (\<Union>x\<in>C. B(x))   = (if C={} then A else (\<Union>x\<in>C. A \<union> B(x)))"
     "(A \<inter> (\<Union>x\<in>C. B(x))) = (\<Union>x\<in>C. A \<inter> B(x))"
     "A - (\<Inter>x\<in>C. B(x))    = (if C={} then A else (\<Union>x\<in>C. A - B(x)))"
     "(\<Union>y\<in>A. \<Union>x\<in>y. B(x)) = (\<Union>x\<in>\<Union>(A). B(x))"
     "(\<Union>a\<in>A. B(f(a))) = (\<Union>x\<in>RepFun A f. B(x))"
apply (simp_all add: Inter_def)
apply (blast intro!: equalityI)+
done

lemma UN_UN_extend:
     "(\<Union>x\<in>A. \<Union>z\<in>B(x). C(z)) = (\<Union>z\<in>(\<Union>x\<in>A. B(x)). C(z))"
by blast

lemmas UN_extend_simps = UN_extend_simps1 UN_extend_simps2 UN_UN_extend


subsection\<open>Miniscoping of Intersections\<close>

lemma INT_simps1:
     "(\<Inter>x\<in>C. A(x) \<inter> B) = (\<Inter>x\<in>C. A(x)) \<inter> B"
     "(\<Inter>x\<in>C. A(x) - B)   = (\<Inter>x\<in>C. A(x)) - B"
     "(\<Inter>x\<in>C. A(x) \<union> B)  = (if C={} then {} else (\<Inter>x\<in>C. A(x)) \<union> B)"
by (simp_all add: Inter_def, blast+)

lemma INT_simps2:
     "(\<Inter>x\<in>C. A \<inter> B(x)) = A \<inter> (\<Inter>x\<in>C. B(x))"
     "(\<Inter>x\<in>C. A - B(x))   = (if C={} then {} else A - (\<Union>x\<in>C. B(x)))"
     "(\<Inter>x\<in>C. cons a (B x)) = (if C={} then {} else cons a (\<Inter>x\<in>C. B(x)))"
     "(\<Inter>x\<in>C. A \<union> B(x))  = (if C={} then {} else A \<union> (\<Inter>x\<in>C. B(x)))"
  by (auto simp add: Inter_def)

lemmas INT_simps [simp] = INT_simps1 INT_simps2

text\<open>Opposite of miniscoping: pull the operator out\<close>


lemma INT_extend_simps1:
     "(\<Inter>x\<in>C. A(x)) \<inter> B = (\<Inter>x\<in>C. A(x) \<inter> B)"
     "(\<Inter>x\<in>C. A(x)) - B = (\<Inter>x\<in>C. A(x) - B)"
     "(\<Inter>x\<in>C. A(x)) \<union> B  = (if C={} then B else (\<Inter>x\<in>C. A(x) \<union> B))"
  by (auto simp add: Inter_def)

lemma INT_extend_simps2:
     "A \<inter> (\<Inter>x\<in>C. B(x)) = (\<Inter>x\<in>C. A \<inter> B(x))"
     "A - (\<Union>x\<in>C. B(x))   = (if C={} then A else (\<Inter>x\<in>C. A - B(x)))"
     "cons a (\<Inter>x\<in>C. B(x)) = (if C={} then {a} else (\<Inter>x\<in>C. cons a (B x)))"
     "A \<union> (\<Inter>x\<in>C. B(x))  = (if C={} then A else (\<Inter>x\<in>C. A \<union> B(x)))"
  by (auto simp add: Inter_def)

lemmas INT_extend_simps = INT_extend_simps1 INT_extend_simps2


subsection\<open>Other simprules\<close>


(*** Miniscoping: pushing in big Unions, Intersections, quantifiers, etc. ***)

lemma misc_simps [simp]:
     "{} \<union> A = A"
     "A \<union> {} = A"
     "{} \<inter> A = {}"
     "A \<inter> {} = {}"
     "{} - A = {}"
     "A - {} = A"
     "\<Union>({}) = {}"
     "\<Union>(cons b A) = b \<union> \<Union>(A)"
     "\<Inter>({b}) = b"
by blast+

subsection\<open>Bounded Quantifiers\<close>
text \<open>\medskip

  The following are not added to the default simpset because
  (a) they duplicate the body and (b) there are no similar rules for \<open>Int\<close>.\<close>

lemma ball_Un: "(\<forall>x \<in> A\<union>B. P(x)) \<longleftrightarrow> (\<forall>x \<in> A. P(x)) & (\<forall>x \<in> B. P(x))"
  by blast

lemma bex_Un: "(\<exists>x \<in> A\<union>B. P(x)) \<longleftrightarrow> (\<exists>x \<in> A. P(x)) | (\<exists>x \<in> B. P(x))"
  by blast

lemma ball_UN: "(\<forall>z \<in> (\<Union>x\<in>A. B(x)). P(z)) \<longleftrightarrow> (\<forall>x\<in>A. \<forall>z \<in> B(x). P(z))"
  by blast

lemma bex_UN: "(\<exists>z \<in> (\<Union>x\<in>A. B(x)). P(z)) \<longleftrightarrow> (\<exists>x\<in>A. \<exists>z\<in>B(x). P(z))"
  by blast



subsection\<open>Singletons\<close>

lemma singleton_iff: "a \<in> {b} \<longleftrightarrow> a=b"
by simp

lemma singletonI [intro!]: "a \<in> {a}"
by (rule consI1)

lemmas singletonE = singleton_iff [THEN iffD1, elim_format, elim!]






subsection\<open>Cantor's Theorem: There is no surjection from a set to its powerset.\<close>


lemma cantor: "\<exists>S \<in> Pow(A). \<forall>x\<in>A. b(x) \<noteq> S" (is "\<exists>S\<in>Pow(A). ?P S")
proof
  let ?S = "{x\<in>A. x \<notin> b x}"
  show "?S \<in> Pow A" by auto

  show "\<forall>x\<in>A. b x \<noteq> ?S"
  proof
    fix x assume x: "x \<in> A"
    show "b x \<noteq> ?S"
    proof (cases "x \<in> b x")
      case True
      with x have "x \<notin> ?S" by auto 
      with True show ?thesis by (auto elim: equalityCE) 
    next
      case False
      with x have "x \<in> ?S" by auto 
      with False show ?thesis by (auto elim: equalityCE)
    qed
  qed
qed


subsection \<open>Misc\<close>

(*Useful examples:  singletonI RS subst_elem,  subst_elem RSN (2,IntI) *)
lemma subst_elem: "[| b\<in>A;  a=b |] ==> a\<in>A"
by (erule ssubst, assumption)

lemma in_mono: "A\<subseteq>B ==> x\<in>A \<longrightarrow> x\<in>B"
by blast


subsection \<open>Simple type checking\<close>

ML_file "Tools/typechk.ML"

lemmas [TC] = consI1 if_type

end
