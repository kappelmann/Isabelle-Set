theory Typing_Examples
  imports "../Ordered_Pairs"
begin

lemma "{} : empty \<sqdot> set" unfolding empty_def by unfold_types
lemma "{a} : non-empty \<sqdot> set" unfolding non_def empty_def by unfold_types auto


declare [[ trace_soft_types ]]


subsection \<open> Example: Basic type inference with lists. \<close>

text \<open>
  Compared to HOL, the type argument becomes an explicit set argument here:
\<close>

axiomatization
  List :: "set \<Rightarrow> set"
    and Nil :: "set \<Rightarrow> set"
    and Cons :: "set \<Rightarrow> set \<Rightarrow> set \<Rightarrow> set"
    and append :: "set \<Rightarrow> set \<Rightarrow> set \<Rightarrow> set"
    where
      Nil_type[type]: "Nil : (A: set) \<Rightarrow> element (List A)"
    and List_Cons_type[type]: "Cons : (A: set) \<Rightarrow> element A \<Rightarrow> element (List A) \<Rightarrow> element (List A)" 
    and append[type]: "append : (A: set) \<Rightarrow> element (List A) \<Rightarrow> element (List A) \<Rightarrow> element (List A)"

text \<open>
  Currently, these are mostly test cases, as there is no way to insert the inferred pieces into
  the context.
\<close>

ML \<open>
  [\<^term>\<open>Nil A = B\<close>]
  |> Elaboration.assert_result \<^context>
    [\<^term>\<open>Nil (A :> set) = (B :> element (List A))\<close>]
\<close>


ML \<open>
  [\<^term>\<open>Cons \<implicit>A x xs\<close>]
  |> Elaboration.assert_result \<^context>
    [\<^term>\<open>Cons (A :> set) (x :> element A) (xs :> element (List A))\<close>]
\<close>

ML \<open>
  [\<^term>\<open>\<lambda>A. Nil A\<close>]
  |> Elaboration.assert_result \<^context>
    [\<^term>\<open>\<lambda>A. Nil A\<close>]
\<close>

ML \<open>
  [\<^term>\<open>\<lambda>A. Nil A\<close>]
  |> Elaboration.assert_result \<^context>
    [\<^term>\<open>\<lambda>A. Nil A\<close>]
\<close>

ML \<open>

fun should_throw (P : exn -> bool) (f: unit -> 'a) =
  let
    val res = Exn.capture f ()
    fun check (Exn.Exn exn) = if P exn then () else raise Match
      | check (Exn.Res r) = error ("Expected exception but got result: " ^ \<^make_string> r)
  in
    ((check res)
     handle Match => error ("Not the expected exception: " ^ \<^make_string> (the (Exn.get_exn res))))
  end 
\<close>

ML \<open>
fun starts_with prefix str = is_prefix (op =) (raw_explode prefix) (raw_explode str)
\<close>

ML \<open>
  (fn _ => Elaboration.elaborate_terms \<^context> [
     \<^term>\<open>%A x. Cons A x xs = Cons A x xs\<close> ])
  |> should_throw (fn ERROR msg => starts_with "Equation is not a pattern" msg)
\<close>

ML \<open>
  (fn _ => Elaboration.elaborate_terms \<^context> [
       \<^term>\<open>%A x. Cons A x xs = Cons A x xs\<close> ])
  |> should_throw (fn ERROR msg => starts_with "Equation is not a pattern" msg)
\<close>

ML \<open>
  [\<^term>\<open>append A (Cons A x xs) ys = Cons A x (append A xs ys)\<close>,
   \<^term>\<open>append A (Nil A) ys = ys\<close>]
  |> Elaboration.assert_result \<^context>
    [\<^term>\<open>append (A :> set) (Cons A (x :> element A) (xs :> element (List A))) (ys :> element (List A)) =
          Cons A x (append A xs ys)\<close>,
     \<^term>\<open>append A (Nil A) ys = ys\<close>
     ]
\<close>

ML \<open>
Elaboration.elaborate_terms \<^context> [
  \<^term>\<open>append ? (Cons ? x xs) ys = Cons ? x (append ? xs ys)\<close>,
  \<^term>\<open>append ? (Nil ?) ys = ys\<close> 
]
\<close>




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
  assumes [type]: "Vec : set \<Rightarrow> element nat \<Rightarrow> set"
    and [type]: "VNil : (A: set) \<Rightarrow> element (Vec A 0)"
    and [type]: "VCons : (A: set) \<Rightarrow> (n: element nat) \<Rightarrow>
          element A \<Rightarrow> element (Vec A n) \<Rightarrow> element (Vec A (Suc n))"
    and [type]: "add : element nat \<Rightarrow> element nat \<Rightarrow> element nat"
    and [type]: "Suc : element nat \<Rightarrow> element nat"
    and [type]: "0 : element nat"
    and [type]: "vappend : (A: set) \<Rightarrow> (n: element nat) \<Rightarrow> (m: element nat) \<Rightarrow>
          element (Vec A n) \<Rightarrow> element (Vec A m) \<Rightarrow> element (Vec A (add n m))"
    and [type_simp]: "add (succ n) m = succ (add n m)"
begin


text \<open>
  The base set of the vector and the dimensions are completely inferred:
\<close>

ML \<open> Elaboration.elaborate_terms \<^context> [
  \<^term>\<open>vappend ? ? ? (VCons ? ? x xs) ys = VCons ? ? x (vappend ? ? ? xs ys)\<close>
]\<close>



end

subsection \<open> Further tests \<close>

ML \<open>
  [\<^term>\<open>\<lambda>(x::set). opair\<close>]
  |> Elaboration.assert_result \<^context>
    [\<^term>\<open>\<lambda>(x::set). opair\<close>]
\<close>
ML \<open> Elaboration.elaborate_terms \<^context> [
  \<^term>\<open>{{}}\<close>
]\<close>

ML \<open>
  [\<^term>\<open>{x, y}\<close>]
  |> Elaboration.assert_result \<^context>
    [\<^term>\<open>{x :> element A, y :> element A}\<close>]
\<close>

(* This one is pretty underconstrained, since the type of y is not clear *)
ML \<open> Elaboration.elaborate_terms \<^context> [
  \<^term>\<open>\<lambda>y. opair {} y\<close>
]\<close>

ML \<open> Elaboration.elaborate_terms \<^context> [
  \<^term>\<open>\<lambda>x. opair x\<close>
]\<close>


ML \<open> Elaboration.elaborate_terms \<^context> [
  \<^term>\<open>\<lambda>x y. \<langle>x,y\<rangle>\<close>
]\<close>

ML \<open>
  [\<^term>\<open>\<langle>x,y\<rangle> = \<langle>y,x\<rangle>\<close>]
  |> Elaboration.assert_result \<^context>
    [\<^term>\<open>\<langle>x :> element B,y :> element B\<rangle> = \<langle>y,x\<rangle>\<close>]
\<close>


text \<open> Transitivity of a relation \<close>

ML \<open>
  [\<^term>\<open>\<forall>x y z. \<langle>x,y\<rangle> \<in> r \<longrightarrow> \<langle>y,z\<rangle> \<in> r \<longrightarrow> \<langle>x,z\<rangle> \<in> r\<close>]
  |> Elaboration.assert_result \<^context>
    [\<^term>\<open>\<forall>x y z. \<langle>x,y\<rangle> \<in> (r :> subset (B \<times> B)) \<longrightarrow> \<langle>y,z\<rangle> \<in> r \<longrightarrow> \<langle>x,z\<rangle> \<in> r\<close>]
\<close>


end
