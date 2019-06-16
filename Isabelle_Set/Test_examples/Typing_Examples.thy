theory Typing_Examples
  imports "../Pair"
begin

lemma empty_type[type]: "{} : subset A"
  by stauto

text \<open>
  The following typing rules are less general than what could be proved, since the \<open>bool\<close> soft
  type is trivial. But their formulation reflects the way we want to use the quantifier and
  and the membership relation in well-typed terms. (* Josh -- outdated comment? *)

  The rule for HOL.All currently needs to be restricted due to a deficiency in the 
  type inference algorithm.
\<close>
lemma All_type[type]: "HOL.All : ((A::set type) \<Rightarrow> bool) \<Rightarrow> bool"
  by (intro Pi_typeI any_typeI)

lemma mem_type[type]: "(\<in>) : element A \<Rightarrow> subset A \<Rightarrow> bool"
  by (intro Pi_typeI any_typeI)

lemma Cons_type[type]: "Set_Theory.Cons : element A \<Rightarrow> subset A \<Rightarrow> subset A"
  by (intro Pi_typeI, unfold element_type_iff Pow_rule) stauto


text \<open>The following statements are also provable, but not helpful:\<close>

lemma "HOL.All : (Type1 \<Rightarrow> Type2) \<Rightarrow> any"
  by (intro Pi_typeI any_typeI)

lemma "(\<in>) : Type1 \<Rightarrow> Type2 \<Rightarrow> any"
  by (intro Pi_typeI any_typeI)

declare [[ trace_soft_types ]]



text \<open> Example: Inferring types for list append \<close>

context
  fixes List :: "set \<Rightarrow> set"
    and Nil :: "set \<Rightarrow> set"
    and Cons :: "set \<Rightarrow> set \<Rightarrow> set \<Rightarrow> set"
    and append :: "set \<Rightarrow> set \<Rightarrow> set \<Rightarrow> set"
  assumes [type]: "Nil : (A: set) \<Rightarrow> element (List A)"
    and [type]: "Cons : (A: set) \<Rightarrow> element A \<Rightarrow> element (List A) \<Rightarrow> element (List A)" 
    and [type]: "append : (A: set) \<Rightarrow> element (List A) \<Rightarrow> element (List A) \<Rightarrow> element (List A)"
begin


ML \<open>Elaboration.print_inferred_types @{context} [
  @{term "Nil A = B"}
]\<close>

ML \<open>Elaboration.print_inferred_types @{context} [
  @{term_dummies "Cons _ x xs"}
]\<close>

ML \<open>Elaboration.print_inferred_types @{context} [
  @{term "%A. Nil A"}
]\<close>

ML \<open>Elaboration.print_inferred_types @{context} [
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
  (fn _ => Elaboration.print_inferred_types @{context} [
     @{term "%A x. Cons A x xs = Cons A x xs"} ])
  |> should_throw (fn ERROR msg => starts_with "Equation is not a pattern" msg)
\<close>

ML \<open>
  (fn _ => Elaboration.print_inferred_types @{context} [
       @{term "%A x. Cons A x xs = Cons A x xs"} ])
  |> should_throw (fn ERROR msg => starts_with "Equation is not a pattern" msg)
\<close>

ML \<open>

Elaboration.print_inferred_types @{context} [
  @{term "append A (Cons A x xs) ys = Cons A x (append A xs ys)"},
  @{term "append A (Nil A) ys = ys"} 
]
\<close>

ML \<open>

Elaboration.print_inferred_types @{context} [
  @{term_dummies "append _ (Cons _ x xs) ys = Cons _ x (append _ xs ys)"},
  @{term_dummies "append _ (Nil _) ys = ys"} 
]
\<close>

end






text \<open> Example: Inferring types for vectors of given length \<close>

(* just uninterpreted for the moment until we have defined them properly *)
consts
  nat :: "set"
  zero :: "set" ("0")
  Suc :: "set \<Rightarrow> set"
  add :: "set \<Rightarrow> set \<Rightarrow> set"
 

context
  fixes Vec :: "set \<Rightarrow> set \<Rightarrow> set"
    and VNil :: "set \<Rightarrow> set"
    and VCons :: "set \<Rightarrow> set \<Rightarrow> set \<Rightarrow> set \<Rightarrow> set"
    and vappend :: "set \<Rightarrow> set \<Rightarrow> set \<Rightarrow> set \<Rightarrow> set \<Rightarrow> set"
  assumes [type]: "Vec : Set \<Rightarrow> element nat \<Rightarrow> Set"
    and [type]: "VNil : (A: Set) \<Rightarrow> element (Vec A 0)"
    and [type]: "VCons : (A: Set) \<Rightarrow> (n: element nat) \<Rightarrow>
          element A \<Rightarrow> element (Vec A n) \<Rightarrow> element (Vec A (Suc n))"
    and [type]: "add : element nat \<Rightarrow> element nat \<Rightarrow> element nat"
    and [type]: "Suc : element nat \<Rightarrow> element nat"
    and [type]: "0 : element nat"
    and [type]: "vappend : (A: Set) \<Rightarrow> (n: element nat) \<Rightarrow> (m: element nat) \<Rightarrow> 
          element (Vec A n) \<Rightarrow> element (Vec A m) \<Rightarrow> element (Vec A (add n m))"
    and [type_simp]: "add (succ n) m = succ (add n m)"
begin




ML \<open> Elaboration.print_inferred_types @{context} [
  @{term_dummies "vappend _ _ _ (VCons _ _ x xs) ys
   = VCons _ _ x (vappend _ _ _ xs ys)"}
]\<close>



end

subsection \<open> Further examples \<close>

ML \<open> Elaboration.print_inferred_types @{context} [
  \<^term_dummies>\<open>\<lambda>(x::set). Pair\<close>
]\<close>

ML \<open> Elaboration.print_inferred_types @{context} [
  @{term_dummies "{{}}"}
]\<close>

ML \<open> Elaboration.print_inferred_types @{context} [
  @{term_dummies "{x, y}"}
]\<close>

(* This one is pretty underconstrained, since the type of y is not clear *)
ML \<open> Elaboration.print_inferred_types @{context} [
  @{term_dummies "\<lambda>y. Pair {} y"}
]\<close>
ML \<open> Elaboration.print_inferred_types @{context} [
  @{term "\<lambda>x. Pair x"}
]\<close>


ML \<open> Elaboration.print_inferred_types @{context} [
  @{term "\<lambda>x y. \<langle>x,y\<rangle>"}
]\<close>


text \<open> Transitivity of a relation \<close>

ML \<open> Elaboration.print_inferred_types @{context} [
  @{term "\<forall>x y z. \<langle>x,y\<rangle>\<in> r \<longrightarrow> \<langle>y,z\<rangle>\<in> r \<longrightarrow> \<langle>x,z\<rangle>\<in> r"}
]\<close>




end
