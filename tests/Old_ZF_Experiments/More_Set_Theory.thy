(*  Title:      ZF/ZF_Base.thy
    Author:     Lawrence C Paulson and Martin D Coen, CU Computer Laboratory
    Copyright   1993  University of Cambridge
*)


theory More_Set_Theory
  imports Set_Theory Ordered_Pair Relation
begin



definition "function" :: "i \<Rightarrow> o"  \<comment> \<open>recognizes functions; can have non-pairs\<close>
  where "function(r) == \<forall>x y. \<langle>x,y\<rangle> \<in> r \<longrightarrow> (\<forall>y'. \<langle>x,y'\<rangle> \<in> r \<longrightarrow> y = y')"

definition Image :: "[i, i] \<Rightarrow> i"  (infixl "``" 90)  \<comment> \<open>image\<close>
  where image_def: "r `` A  == {y \<in> range(r). \<exists>x\<in>A. \<langle>x,y\<rangle> \<in> r}"

definition vimage :: "[i, i] \<Rightarrow> i"  (infixl "-``" 90)  \<comment> \<open>inverse image\<close>
  where vimage_def: "r -`` A == converse(r)``A"

(* Restrict the relation r to the domain A *)
definition restrict :: "[i, i] \<Rightarrow> i"
  where "restrict r A == {z \<in> r. \<exists>x\<in>A. \<exists>y. z = \<langle>x,y\<rangle>}"


(* Abstraction, application and Cartesian product of a family of sets *)

definition Lambda :: "[i, i \<Rightarrow> i] \<Rightarrow> i"
  where lam_def: "Lambda A b == {\<langle>x,b(x)\<rangle>. x\<in>A}"

definition "apply" :: "[i, i] \<Rightarrow> i"  (infixl "`" 90)  \<comment> \<open>function application\<close>
  where "f`a == \<Union>(f``{a})"

definition Pi :: "[i, i \<Rightarrow> i] \<Rightarrow> i"
  where "Pi A B == {f\<in>Pow(Sigma A B). A\<subseteq>domain(f) & function(f)}"

abbreviation function_space :: "[i, i] \<Rightarrow> i"  (infixr "->" 60)  \<comment> \<open>function space\<close>
  where "A -> B \<equiv> Pi A (\<lambda>_. B)"


(* binder syntax *)

syntax
  "_PROD"     :: "[pttrn, i, i] => i"        ("(3\<Prod>_\<in>_./ _)" 10)
  "_SUM"      :: "[pttrn, i, i] => i"        ("(3\<Sum>_\<in>_./ _)" 10)
  "_lam"      :: "[pttrn, i, i] => i"        ("(3\<lambda>_\<in>_./ _)" 10)
translations
  "\<Prod>x\<in>A. B"   == "CONST Pi A (\<lambda>x. B)"
  "\<Sum>x\<in>A. B"   == "CONST Sigma A (\<lambda>x. B)"
  "\<lambda>x\<in>A. f"    == "CONST Lambda A (\<lambda>x. f)"



end
