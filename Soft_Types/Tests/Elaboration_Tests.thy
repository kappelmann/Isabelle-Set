section \<open>Elaboration Tests\<close>
theory Elaboration_Tests
imports "Soft_Types.Soft_Types_HOL"
begin

declare [[trace_soft_types]]
typedecl set

subsection \<open>Example: Basic type inference with lists.\<close>

text \<open>Compared to HOL, the type argument becomes an explicit set argument here:\<close>

experiment
  fixes Element :: "set \<Rightarrow> set type"
  and Set :: "set type"
  and list :: "set \<Rightarrow> set"
  and nil :: "set \<Rightarrow> set"
  and cons :: "set \<Rightarrow> set \<Rightarrow> set \<Rightarrow> set"
  and append :: "set \<Rightarrow> set \<Rightarrow> set \<Rightarrow> set"
  assumes nil_type [type]: "nil \<Ztypecolon> (A : Set) \<Rightarrow> Element (list A)"
  and list_cons_type [type]: "cons \<Ztypecolon> (A : Set) \<Rightarrow> Element A \<Rightarrow> Element (list A) \<Rightarrow> Element (list A)"
  and append [type]: "append \<Ztypecolon> (A : Set) \<Rightarrow> Element (list A) \<Rightarrow> Element (list A) \<Rightarrow> Element (list A)"

begin

ML \<open>
  [\<^term>\<open>nil A = B\<close>]
  |> Elaboration.assert_result \<^context>
    [\<^term>\<open>nil (A :> Set) = (B :> Element (list A))\<close>]
\<close>

ML \<open>
  [\<^term>\<open>cons \<implicit>A x xs\<close>]
  |> Elaboration.assert_result \<^context>
    [\<^term>\<open>cons (A :> Set) (x :> Element A) (xs :> Element (list A))\<close>]
\<close>

ML \<open>
  [\<^term>\<open>\<lambda>A. nil A\<close>]
  |> Elaboration.assert_result \<^context>
    [\<^term>\<open>\<lambda>A. nil A\<close>]
\<close>

ML \<open>
  fun should_throw (P: exn -> bool) (f: unit -> 'a) =
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
     \<^term>\<open>%A x. cons A x xs = cons A x xs\<close> ])
  |> should_throw (fn ERROR msg => starts_with "Equation is not a pattern" msg)
\<close>

ML \<open>
  [\<^term>\<open>append A (cons A x xs) ys = cons A x (append A xs ys)\<close>,
   \<^term>\<open>append A (nil A) ys = ys\<close>]
  |> Elaboration.assert_result \<^context>
    [\<^term>\<open>append (A :> Set) (cons A (x :> Element A) (xs :> Element (list A)))
      (ys :> Element (list A)) = cons A x (append A xs ys)\<close>,
     \<^term>\<open>append A (nil A) ys = ys\<close>
     ]
\<close>

ML \<open>
Elaboration.elaborate_terms \<^context> [
  \<^term>\<open>append ? (cons ? x xs) ys = cons ? x (append ? xs ys)\<close>,
  \<^term>\<open>append ? (nil ?) ys = ys\<close>
]
\<close>

end

text \<open>Example: Inferring types for vectors of given length \<close>

experiment
  fixes Element :: "set \<Rightarrow> set type"
  and nat :: "set"
  and zero :: "set" ("0")
  and succ :: "set \<Rightarrow> set"
  and add :: "set \<Rightarrow> set \<Rightarrow> set"
  and vec :: "set \<Rightarrow> set \<Rightarrow> set"
  and vnil :: "set \<Rightarrow> set"
  and vcons :: "set \<Rightarrow> set \<Rightarrow> set \<Rightarrow> set \<Rightarrow> set"
  and vappend :: "set \<Rightarrow> set \<Rightarrow> set \<Rightarrow> set \<Rightarrow> set \<Rightarrow> set"

  and negint :: "set"
  and vinitneg :: "set \<Rightarrow> set \<Rightarrow> set"
  assumes [type]: "vec \<Ztypecolon> Set \<Rightarrow> Element nat \<Rightarrow> Set"
  and [type]: "vnil \<Ztypecolon> (A : Set) \<Rightarrow> Element (vec A 0)"
  and [type]: "vcons \<Ztypecolon> (A : Set) \<Rightarrow> (n : Element nat) \<Rightarrow>
    Element A \<Rightarrow> Element (vec A n) \<Rightarrow> Element (vec A (succ n))"
  and [type]: "add \<Ztypecolon> Element nat \<Rightarrow> Element nat \<Rightarrow> Element nat"
  and [type]: "succ \<Ztypecolon> Element nat \<Rightarrow> Element nat"
  and [type]: "0 \<Ztypecolon> Element nat"
  and [type]: "vappend \<Ztypecolon> (A : Set) \<Rightarrow> (n : Element nat) \<Rightarrow> (m : Element nat) \<Rightarrow>
    Element (vec A n) \<Rightarrow> Element (vec A m) \<Rightarrow> Element (vec A (add n m))"
  and [type_simp]: "add (succ n) m = succ (add n m)"

  and [type]: "vinitneg \<Ztypecolon> (A : Set) \<Rightarrow> (x : Element negint) \<Rightarrow> Element (vec A x)"
begin

text \<open>The base set of the vector and the dimensions are completely inferred:\<close>

ML \<open> Elaboration.elaborate_terms \<^context> [
  \<^term>\<open>vappend ? ? ? (vcons ? ? x xs) ys = vcons ? ? x (vappend ? ? ? xs ys)\<close>
]\<close>

(*Problem: does not keep type assertions for compound term, leading to ill-typed
elaborations*)
ML \<open> Elaboration.elaborate_terms \<^context> [
  \<^term>\<open>vcons ? ? x (vinitneg ? ?)\<close>
]\<close>

end


end
