(*  Title:      ZF/ZF_Base.thy
    Author:     Lawrence C Paulson and Martin D Coen, CU Computer Laboratory
    Copyright   1993  University of Cambridge
*)

section \<open>Axiomatic Base of Zermelo-Fraenkel Set Theory\<close>

theory Set_Theory_Axioms
imports First_Order_Logic
begin

subsection \<open>Signature\<close>

declare [[eta_contract = false]]

typedecl i
instance i :: "term" ..

axiomatization mem :: "i \<Rightarrow> i \<Rightarrow> o"  (infixl "\<in>" 50)  \<comment> \<open>membership relation\<close>
  and empty :: "i"  ("{}")  \<comment> \<open>the empty set\<close>
  and Pow :: "i \<Rightarrow> i"  \<comment> \<open>power sets\<close>
  and Inf :: "i"  \<comment> \<open>infinite set\<close>
  and Union :: "i \<Rightarrow> i"  ("\<Union>_" [90] 90)
  and PrimReplace :: "i \<Rightarrow> (i \<Rightarrow> i \<Rightarrow> o) \<Rightarrow> i"

abbreviation not_mem :: "[i, i] \<Rightarrow> o"  (infixl "\<notin>" 50)  \<comment> \<open>negated membership relation\<close>
  where "x \<notin> y \<equiv> \<not> (x \<in> y)"


subsection \<open>Bounded Quantifiers\<close>

definition Ball :: "[i, i \<Rightarrow> o] \<Rightarrow> o"
  where "Ball A P \<equiv> (\<forall>x. x\<in>A \<longrightarrow> P x)"

definition Bex :: "[i, i \<Rightarrow> o] \<Rightarrow> o"
  where "Bex A P \<equiv> \<exists>x. x\<in>A \<and> P(x)"

syntax
  "_Ball" :: "[pttrn, i, o] \<Rightarrow> o"  ("(3\<forall>_\<in>_./ _)" 10)
  "_Bex" :: "[pttrn, i, o] \<Rightarrow> o"  ("(3\<exists>_\<in>_./ _)" 10)
translations
  "\<forall>x\<in>A. P" \<rightleftharpoons> "CONST Ball A (\<lambda>x. P)"
  "\<exists>x\<in>A. P" \<rightleftharpoons> "CONST Bex A (\<lambda>x. P)"


subsection \<open>Variations on Replacement\<close>

(* Derived form of replacement, restricting P to its functional part.
   The resulting set (for functional P) is the same as with
   PrimReplace, but the rules are simpler. *)
definition Replace :: "[i, [i, i] \<Rightarrow> o] \<Rightarrow> i"
  where "Replace A P == PrimReplace A (%x y. (\<exists>!z. P x z) & P x y)"

syntax
  "_Replace"  :: "[pttrn, pttrn, i, o] => i"  ("(1{_ ./ _ \<in> _, _})")
translations
  "{y. x\<in>A, Q}" \<rightleftharpoons> "CONST Replace A (\<lambda>x y. Q)"



(* Separation and Pairing can be derived from the Replacement
   and Powerset Axioms using the following definitions. *)
definition Collect :: "[i, i \<Rightarrow> o] \<Rightarrow> i"
  where "Collect A P == {y . x\<in>A, x=y & P x}"

syntax
  "_Collect" :: "[pttrn, i, o] \<Rightarrow> i"  ("(1{_ \<in> _ ./ _})")
translations
  "{x\<in>A. P}" \<rightleftharpoons> "CONST Collect A (\<lambda>x. P)"


subsection \<open>Finite sets and binary operations\<close>

(*Unordered pairs (Upair) express binary union/intersection and cons;
  set enumerations translate as {a,...,z} = cons(a,...,cons(z,{})...)*)

definition Upair :: "[i, i] => i"
  where "Upair a b == {y. x\<in>Pow(Pow({})), (x={} & y=a) | (x=Pow({}) & y=b)}"

definition Subset :: "[i, i] \<Rightarrow> o"  (infixl "\<subseteq>" 50)  \<comment> \<open>subset relation\<close>
  where subset_def: "A \<subseteq> B \<equiv> \<forall>x\<in>A. x\<in>B"

definition Un :: "[i, i] \<Rightarrow> i"  (infixl "\<union>" 65)  \<comment> \<open>binary union\<close>
  where "A \<union> B == \<Union>(Upair A B)"

definition cons :: "[i, i] => i"
  where "cons a A == Upair a a \<union> A"

definition succ :: "i => i"
  where "succ i == cons i i"



subsection \<open>Axioms\<close>

(* ZF axioms -- see Suppes p.238
   Axioms for Union, Pow and Replace state existence only,
   uniqueness is derivable using extensionality. *)

axiomatization
where
  extension:     "A = B \<longleftrightarrow> A \<subseteq> B \<and> B \<subseteq> A" and
  Union_iff:     "A \<in> \<Union>(C) \<longleftrightarrow> (\<exists>B\<in>C. A\<in>B)" and
  Pow_iff:       "A \<in> Pow(B) \<longleftrightarrow> A \<subseteq> B" and

  (*We may name this set, though it is not uniquely defined.*)
  infinity:      "{} \<in> Inf \<and> (\<forall>y\<in>Inf. succ(y) \<in> Inf)" and

  (*This formulation facilitates case analysis on A.*)
  foundation:    "A = {} \<or> (\<exists>x\<in>A. \<forall>y\<in>x. y\<notin>A)" and

  (*Schema axiom since predicate P is a higher-order variable*)
  replacement:   "(\<forall>x\<in>A. \<forall>y z. P x y \<and> P x z \<longrightarrow> y = z) \<Longrightarrow>
                         b \<in> PrimReplace A P \<longleftrightarrow> (\<exists>x\<in>A. P x b)"



end