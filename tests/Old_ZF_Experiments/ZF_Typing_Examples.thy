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
  @{term "%A. Nil A"}
]\<close>

ML \<open>Soft_Type_Inference.print_inferred_types @{context} [
  @{term "%A x xs. Cons A x xs = Cons A x xs"}
]\<close>

ML \<open>

fun should_throw (P : exn -> unit) (f: unit -> 'a) =
  case Exn.capture f () of
    Exn.Exn exn => (P exn
                    handle Match => error ("Not the expected exception: " ^ @{make_string} exn))
  | Exn.Res _ => error "Expected exception"                 

\<close>

ML \<open>
  (fn _ => Soft_Type_Inference.print_inferred_types @{context} [
     @{term "%A x. Cons A x xs = Cons A x xs"} ])
  |> should_throw (fn ERROR "Unsolvalbe bound variable in equation." => ())
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

(*
ML \<open>

Soft_Type_Inference.print_inferred_types @{context} [
  @{term "\<And>A x xs ys. append A (Cons A x xs) ys = Cons A x (append A xs ys)"},
  @{term "\<And>A ys. append A (Nil A) ys = ys"} 
]
\<close>
*)


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

text \<open> Relations examples \<close>





lemma trans_type[type]: "trans ::: (r : set (A * A)) \<Rightarrow> o"
  by (rule Pi_typeI, rule o_TypeI)


lemma All_type[type]: "First_Order_Logic.All ::: (P: ((x::i): A) \<Rightarrow> o) \<Rightarrow> o"
  by (rule Pi_typeI, rule o_TypeI)

lemma imp_type[type]: "(\<longrightarrow>) ::: (l: o) \<Rightarrow> (r: o) \<Rightarrow> o"
  by (intro Pi_typeI o_TypeI)

lemma mem_type[type]: "(\<in>) ::: (x: set A) \<Rightarrow> (S: subset A) \<Rightarrow> o"
  by (intro Pi_typeI o_TypeI)

lemma Pair_type[type]: "Pair ::: (x: set A) \<Rightarrow> (y: set (B x)) \<Rightarrow> set (Sigma A B)"
proof (intro Pi_typeI)
  fix x y assume x: "x ::: set A" and y: "y ::: set (B x)"
  from x have "x \<in> A" by (rule set_typeE)
  moreover from y have "y \<in> B x" by (rule set_typeE)
  ultimately have "<x, y> \<in> Sigma A B" by (rule SigmaI)
  then show "<x, y> ::: set (Sigma A B)" by (rule set_typeI)
qed

context

begin


ML \<open> Soft_Type_Context.get (Context.Proof @{context}) \<close>

(*
ML \<open> Soft_Type_Inference.print_inferred_types @{context} [
  @{term "\<forall>x y z. <x,y>: r \<longrightarrow> <y,z>: r \<longrightarrow> <x,z>: r"}
]\<close>
*)



end



end
