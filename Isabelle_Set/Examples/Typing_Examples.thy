theory Typing_Examples
  imports "../Pair"
begin

lemma empty_type[type]: "{} : subset A"
  unfolding element_typedef by auto

text \<open>
  This currently needs to be restricted due to a deficiency in the 
  type inference algorithm.
\<close>
lemma All_type[type]: "HOL.All : ((A::type) \<Rightarrow> prop) \<Rightarrow> bool"
  by (intro Pi_typeI all_formulas_bool)

lemma mem_type[type]: "(\<in>) : subset A \<Rightarrow> element A \<Rightarrow> bool"
  by (intro Pi_typeI all_formulas_bool)

(* Note also: *)
lemma All_type_triv: "HOL.All : (Type1 \<Rightarrow> Type2) \<Rightarrow> bool"
  by (intro Pi_typeI all_formulas_bool)
(* and *)
lemma mem_type_triv: "(\<in>) : Type1 \<Rightarrow> Type2 \<Rightarrow> bool"
  by (intro Pi_typeI all_formulas_bool)


lemma Cons_type[type]: "Set_Theory.Cons : element A \<Rightarrow> subset A \<Rightarrow> subset A"
  by (intro Pi_typeI, unfold element_type_iff Pow_rule) auto



text \<open> Example: Inferring types for list append \<close>

context
  fixes List :: "set \<Rightarrow> set"
    and Nil :: "set \<Rightarrow> set"
    and Cons :: "set \<Rightarrow> set \<Rightarrow> set \<Rightarrow> set"
    and append :: "set \<Rightarrow> set \<Rightarrow> set \<Rightarrow> set"
  assumes [type]: "Nil : [A: set] \<Rightarrow> element (List A)"
    and [type]: "Cons : [A: set] \<Rightarrow> element A \<Rightarrow> element (List A) \<Rightarrow> element (List A)" 
    and [type]: "append : [A: set] \<Rightarrow> element (List A) \<Rightarrow> element (List A) \<Rightarrow> element (List A)"
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
    and [type]: "VNil : [A: Set] \<Rightarrow> element (Vec A 0)"
    and [type]: "VCons : [A: Set] \<Rightarrow> [n: element nat] \<Rightarrow>
          element A \<Rightarrow> element (Vec A n) \<Rightarrow> element (Vec A (Suc n))"
    and [type]: "add : element nat \<Rightarrow> element nat \<Rightarrow> element nat"
    and [type]: "Suc : element nat \<Rightarrow> element nat"
    and [type]: "0 : element nat"
    and [type]: "vappend : [A: Set] \<Rightarrow> [n: element nat] \<Rightarrow> [m: element nat] \<Rightarrow> 
          element (Vec A n) \<Rightarrow> element (Vec A m) \<Rightarrow> element (Vec A (add n m))"
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

ML \<open> Soft_Type_Inference.print_inferred_types @{context} [
  @{term_pattern "{x, y}"}
]\<close>

(* This one is pretty underconstrained, since the type of y is not clear *)
ML \<open> Soft_Type_Inference.print_inferred_types @{context} [
  @{term_pattern "\<lambda>y. Pair {} y"}
]\<close>
ML \<open> Soft_Type_Inference.print_inferred_types @{context} [
  @{term "\<lambda>x. Pair x"}
]\<close>


ML \<open> Soft_Type_Inference.print_inferred_types @{context} [
  @{term "\<lambda>x y. \<langle>x,y\<rangle>"}
]\<close>


text \<open> Transitivity of a relation \<close>

ML \<open> Soft_Type_Inference.print_inferred_types @{context} [
  @{term "\<forall>x y z. \<langle>x,y\<rangle>\<in> r \<longrightarrow> \<langle>y,z\<rangle>\<in> r \<longrightarrow> \<langle>x,z\<rangle>\<in> r"}
]\<close>




end