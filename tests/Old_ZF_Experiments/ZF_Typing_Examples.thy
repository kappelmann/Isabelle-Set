theory ZF_Typing_Examples
  imports Nat_ZF "../../1_Soft_Types/Soft_Types"
begin


subsection \<open> Type of sets \<close>
definition Set :: "i type"
  where "Set \<equiv> Type (\<lambda>x::i. (x == x))"

lemma Set_TypeI: "(x::i) ::: Set"
  unfolding Set_def has_type_Type .


subsection \<open> Type of elements of a given set \<close>

definition set :: "i \<Rightarrow> i type"
  where "set A == Type (%x. Trueprop (x \<in> A))"

lemma set_typeI: "x \<in> A \<Longrightarrow> x ::: set A"
  unfolding set_def has_type_Type .

lemma set_typeE: "x ::: set A \<Longrightarrow> x \<in> A"
  unfolding set_def has_type_Type .

lemma set_type_iff: "(x ::: set A) == Trueprop (x \<in> A)"
  unfolding set_def has_type_Type .


subsection \<open> Type of object-level propositions \<close>

definition o :: "o type"
  where "o \<equiv> Type (\<lambda>x::o. (x == x))"

lemma o_TypeI: "(P::o) ::: o"
  unfolding o_def has_type_Type .


subsection \<open> Type of subsets of a given set \<close>

abbreviation subset :: "i \<Rightarrow> i type"
  where "subset A == set (Pow A)"



subsection \<open> Type declarations for basic material \<close>

lemma eq_type[type]: "((=)::(i \<Rightarrow> i \<Rightarrow> o)) ::: (x: A) \<Rightarrow> (y: A) \<Rightarrow> o"
  by (intro Pi_typeI o_TypeI)

lemma iff_type[type]: "((\<longleftrightarrow>)::(o \<Rightarrow> o \<Rightarrow> o)) ::: (x: o) \<Rightarrow> (y: o) \<Rightarrow> o"
  by (intro Pi_typeI o_TypeI)

lemma Lambda_type[type]: 
  "Lambda ::: (A : Set) \<Rightarrow> (f: (x : set A) \<Rightarrow> set (B x)) \<Rightarrow> set (Pi A B)"
proof (intro Pi_typeI)
  fix A f assume f: "f ::: (x : set A) \<Rightarrow> set (B x)"
  
  show "Lambda A f ::: set (Pi A B)"
    unfolding set_type_iff
  proof (rule lam_type)
    fix x assume "x \<in> A"
    then have "x ::: set A" unfolding set_type_iff .
    then have "f x ::: set (B x)"
      by (rule Pi_typeE[OF f])
    then show "f x \<in> B x" unfolding set_type_iff .
  qed
qed

lemma vimage_type[type]: "vimage ::: (R: subset (A \<times> B)) \<Rightarrow> (X: subset B) \<Rightarrow> subset A"
  apply (intro Pi_typeI)
  apply (unfold set_type_iff Pow_iff)
  by (rule vimage_subset)

lemma cons_type[type]: "cons ::: (x: set A) \<Rightarrow> (B: subset A) \<Rightarrow> subset A"
  by (intro Pi_typeI, unfold set_type_iff Pow_iff) auto

lemma empty_type[type]: "{} ::: subset A"
  unfolding set_type_iff Pow_iff by auto

lemma trans_type[type]: "trans ::: (r : set (A * A)) \<Rightarrow> o"
  by (rule Pi_typeI, rule o_TypeI)

lemma All_type[type]: "First_Order_Logic.All ::: (P: ((x::i): A) \<Rightarrow> o) \<Rightarrow> o"
  by (rule Pi_typeI, rule o_TypeI)

lemma imp_type[type]: "(\<longrightarrow>) ::: (l: o) \<Rightarrow> (r: o) \<Rightarrow> o"
  by (intro Pi_typeI o_TypeI)

lemma mem_type[type]: "(\<in>) ::: (x: set A) \<Rightarrow> (S: subset A) \<Rightarrow> o"
  by (intro Pi_typeI o_TypeI)

lemma succ_type[type]: "succ ::: (n: set nat) \<Rightarrow> set nat"
  by (intro Pi_typeI, unfold set_type_iff) auto

lemma Pair_type[type]: "Pair ::: (x: set A) \<Rightarrow> (y: set (B x)) \<Rightarrow> set (Sigma A B)"
proof (intro Pi_typeI)
  fix x y assume x: "x ::: set A" and y: "y ::: set (B x)"
  from x have "x \<in> A" by (rule set_typeE)
  moreover from y have "y \<in> B x" by (rule set_typeE)
  ultimately have "<x, y> \<in> Sigma A B" by (rule SigmaI)
  then show "<x, y> ::: set (Sigma A B)" by (rule set_typeI)
qed





text \<open> Example: Inferring types for list append \<close>

context
  fixes List :: "i \<Rightarrow> i"
    and Nil :: "i \<Rightarrow> i"
    and Cons :: "i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i"
    and append :: "i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i"
  assumes [type]: "Nil ::: (A: Set) \<Rightarrow> set (List A)"
    and [type]: "Cons ::: (A: Set) \<Rightarrow> (x: set A) \<Rightarrow> (xs : set (List A)) \<Rightarrow> set (List A)" 
    and [type]: "append ::: (A: Set) \<Rightarrow> (xs: set (List A)) \<Rightarrow> (ys : set (List A)) \<Rightarrow> set (List A)"
begin


ML \<open>Soft_Type_Inference.print_inferred_types @{context} [
  @{term "Nil A = B"}
]\<close>

ML \<open>Soft_Type_Inference.print_inferred_types @{context} [
  @{term_pattern "Cons _ x xs"}
]\<close>

ML \<open>Soft_Type_Inference.print_inferred_types @{context} [
  @{term "%A. Nil A"}
]\<close>

ML \<open>Soft_Type_Inference.print_inferred_types @{context} [
  @{term "%A x xs. Cons A x xs = Cons A x xs"}
]\<close>

ML \<open>

fun should_throw (P : exn -> bool) (f: unit -> 'a) =
  let
    val res = Exn.capture f ()
    fun check (Exn.Exn exn) = if P exn then () else raise Match
      | check (Exn.Res r) = error ("Expected exception but got result: " ^ @{make_string} r)
  in
    ((check res)
     handle Match => error ("Not the expected exception: " ^ @{make_string} (the (Exn.get_exn res))))
  end 
\<close>

ML \<open>
fun starts_with prefix str = is_prefix (op =) (raw_explode prefix) (raw_explode str)
\<close>

ML \<open>
  (fn _ => Soft_Type_Inference.print_inferred_types @{context} [
     @{term "%A x. Cons A x xs = Cons A x xs"} ])
  |> should_throw (fn ERROR msg => starts_with "Equation is not a pattern" msg)
\<close>

ML \<open>
  (fn _ => Soft_Type_Inference.print_inferred_types @{context} [
       @{term "%A x. Cons A x xs = Cons A x xs"} ])
  |> should_throw (fn ERROR msg => starts_with "Equation is not a pattern" msg)
\<close>

ML \<open>

Soft_Type_Inference.print_inferred_types @{context} [
  @{term "append A (Cons A x xs) ys = Cons A x (append A xs ys)"},
  @{term "append A (Nil A) ys = ys"} 
]
\<close>

ML \<open>

Soft_Type_Inference.print_inferred_types @{context} [
  @{term_pattern "append _ (Cons _ x xs) ys = Cons _ x (append _ xs ys)"},
  @{term_pattern "append _ (Nil _) ys = ys"} 
]
\<close>

end






text \<open> Example: Inferring types for vectors of given length \<close>

context
  fixes Vec :: "i \<Rightarrow> i \<Rightarrow> i"
    and VNil :: "i \<Rightarrow> i"
    and VCons :: "i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i"
    and add :: "i \<Rightarrow> i \<Rightarrow> i"
    and vappend :: "i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i"
  assumes [type]: "Vec ::: (A: Set) \<Rightarrow> (n: set nat) \<Rightarrow> Set"
    and [type]: "VNil ::: (A: Set) \<Rightarrow> set (Vec A 0)"
    and [type]: "VCons ::: (A: Set) \<Rightarrow> (n: set nat) \<Rightarrow> (x: set A) \<Rightarrow> (xs : set (Vec A n)) \<Rightarrow> set (Vec A (succ n))"
    and [type]: "add ::: (n : set nat) \<Rightarrow> (m : set nat) \<Rightarrow> set nat"
    and [type]: "succ ::: (n : set nat) \<Rightarrow> set nat"
    and [type]: "0 ::: set nat"
    and [type]: "vappend ::: (A: Set) \<Rightarrow> (n: set nat) \<Rightarrow> (m: set nat) \<Rightarrow> (xs: set (Vec A n)) 
\<Rightarrow> (ys: set (Vec A m)) \<Rightarrow> set (Vec A (add n m))"
    and [type_simp]: "add (succ n) m = succ (add n m)"
begin




ML \<open> Soft_Type_Inference.print_inferred_types @{context} [
  @{term_pattern "vappend _ _ _ (VCons _ _ x xs) ys
   = VCons _ _ x (vappend _ _ _ xs ys)"}
]\<close>



end

subsection \<open> Further examples \<close>

ML \<open> Soft_Type_Inference.print_inferred_types @{context} [
  \<^term_pattern>\<open>\<lambda>x. Pair\<close>
]\<close>

ML \<open> Soft_Type_Inference.print_inferred_types @{context} [
  @{term_pattern "{{}}"}
]\<close>

(* This one is pretty underconstrained, since the type of y is not clear *)
ML \<open> Soft_Type_Inference.print_inferred_types @{context} [
  @{term_pattern "\<lambda>y. Pair {} y"}
]\<close>
ML \<open> Soft_Type_Inference.print_inferred_types @{context} [
  @{term "\<lambda>x. Pair x"}
]\<close>


ML \<open> Soft_Type_Inference.print_inferred_types @{context} [
  @{term "\<lambda>x y. <x,y>"}
]\<close>


text \<open> Transitivity of a relation \<close>

ML \<open> Soft_Type_Inference.print_inferred_types @{context} [
  @{term "\<forall>x y z. <x,y>\<in> r \<longrightarrow> <y,z>\<in> r \<longrightarrow> <x,z>\<in> r"}
]\<close>



text \<open> Well-foundedness of a function definition \<close>

(*
ML \<open>
Soft_Type_Inference.print_inferred_types @{context} [
  @{term "(f = (\<lambda>x\<in>r-``{a}. H x (restrict f (r-``{x}))))"}
]\<close>
*)




end
