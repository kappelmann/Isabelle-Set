theory Manual_Type_Checks
  imports "Soft_Types.Soft_Types_HOL"
begin

subsection \<open>Traditional Function Application Types with Subtyping\<close>

lemma app_type:
  assumes "t : A \<Rightarrow> B"
  and "u : A"
  shows "t u : B"
  by simp

(*subtyping in domain*)
lemma app_type':
  assumes "t : A \<Rightarrow> B"
  and "u : A'"
  (*subtyping*)
  and "u : A' \<Longrightarrow> u : A"
  shows "t u : B"
  by simp

(*subtyping in domain and codomain*)
lemma app_type'':
  assumes "t : A \<Rightarrow> B'"
  and "t : A \<Rightarrow> B' \<Longrightarrow> u : A'"
  (*subtyping*)
  and "t u : B' \<Longrightarrow> t u : B"
  and "t : A \<Rightarrow> B' \<Longrightarrow> u : A' \<Longrightarrow> u : A"
  shows "t u : B"
  using assms by simp

lemma app_dep_type:
  assumes "t : (x : A) \<Rightarrow> B x"
  and "t : (x : A) \<Rightarrow> B x \<Longrightarrow> u : A"
  shows "t u : B u"
  using assms by simp

(*subtyping in domain*)
lemma app_dep_type':
  assumes "t : (x : A) \<Rightarrow> B x"
  and "t : (x : A) \<Rightarrow> B x \<Longrightarrow> u : A'"
  (*subtyping*)
  and "t : (x : A) \<Rightarrow> B x \<Longrightarrow> u : A' \<Longrightarrow> u : A"
  shows "t u : B u"
  using assms by simp

(*subtyping in domain and codomain*)
lemma app_dep_type'':
  assumes "t : (x : A) \<Rightarrow> B' x"
  and "t : (x : A) \<Rightarrow> B' x \<Longrightarrow> u : A'"
  (*subtyping*)
  and "t u : B' u \<Longrightarrow> t u : B u"
  and "t : (x : A) \<Rightarrow> B' x \<Longrightarrow> u : A' \<Longrightarrow> u : A"
  shows "t u : B u"
  using assms by simp

lemma app_type2:
  assumes "t : A \<Rightarrow> B"
  and "u : A"
  shows "t u : B"
  using assms by simp

lemma app_dep_type2:
  assumes "t : (x : A) \<Rightarrow> B x"
  and "S \<equiv> B u"
  and "u : A"
  shows "t u : S"
  using assms by simp


subsection \<open>Lambda Abstractions\<close>

experiment
begin

lemma
  assumes f_type: "f : (A \<Rightarrow> C) \<Rightarrow> C"
  and c_type: "c : A \<Rightarrow> Bool \<Rightarrow> C"
  shows "f (\<lambda> a. c a True) : C"
  apply (rule app_type'[where ?t=f])
    apply (rule f_type)
    (*problem: have to guess at this point*)
    (*safeguard: HOL types restrict the number of times we can apply Dep_fun_typeI
      to some term*)
    apply (rule Dep_fun_typeI)
    apply (rule app_type'[where ?t="c a" for a])
      apply (rule app_type'[where ?t="c" for a])
        apply (rule c_type)
        apply assumption
        defer
      apply (rule Any_typeI)
      defer
    defer
  (*subtyping*)
  apply assumption+
  done

end

subsection \<open>Traditional Type Checking with Subtyping\<close>

axiomatization
  Nat :: "'a type"
  and Int :: "'a type"
  and add :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
where
  Int_if_Nat: "x : Nat \<Longrightarrow> x : Int"
  and add_type: "add : A \<Rightarrow> A \<Rightarrow> A"

experiment
begin

(*no subtyping*)
schematic_goal
  assumes n_type: "n : Nat" and i_type: "i : Nat"
  shows "add n i : ?T"
  apply (rule app_type[where ?t="add n"])
    apply (rule app_type[where ?t=add])
      apply (rule add_type)
      apply (rule n_type)
    apply (rule i_type)
  done

(*subtyping in domain*)
schematic_goal
  assumes n_type: "n : Nat" and i_type: "i : Int"
  shows "add n i : ?T"
  apply (rule app_type'[where ?t="add n"])
    apply (rule app_type'[where ?t=add])
      apply (rule add_type)
      apply (rule n_type)
      defer
    apply (rule i_type)
    defer
  (*subtyping*)
  apply (rule Int_if_Nat)
  apply assumption+
  done

(*subtyping in domain and codomain*)
schematic_goal
  assumes n_type: "n : Nat" and i_type: "i : Int"
  shows "add n i : ?T"
  apply (rule app_type''[where ?t="add n"])
    apply (rule app_type''[where ?t=add])
      apply (rule add_type)
      apply (rule n_type)
      defer
      defer
    apply (rule i_type)
    defer
    defer
  (*subtyping*)
  apply assumption
  apply (rule Int_if_Nat)
  apply assumption
  (*could further widen the codomain here*)
  apply assumption
  apply assumption
  done

(*compound arguments with subtyping in domain; backtracking needed*)
schematic_goal
  assumes n_type: "n : Nat" and i_type: "i : Int"
  shows "add (add n n) i : ?T"
  apply (rule app_type[where ?t="add (add n n)"])
    apply (rule app_type[where ?t=add])
      apply (rule add_type)
      apply (rule app_type[where ?t="add n"])
        apply (rule app_type''[where ?t="add"])
          apply (rule add_type)
          apply (rule n_type)
          defer
        apply (rule n_type)
      defer
    apply (rule i_type)
  (*subtyping*)
  apply (rule app_type[where ?t="add"])
    apply (rule add_type)
    apply (rule Int_if_Nat)
    apply (rule n_type)
  apply (rule Int_if_Nat)
  apply (rule n_type)
  done

end

subsection \<open>Higher-Order Functions\<close>

experiment
begin

lemma
  assumes f_type: "f : Nat \<Rightarrow> Int \<Rightarrow> Nat" and g_type: "g : Nat \<Rightarrow> Nat \<Rightarrow> Int"
  shows "add f g : Nat \<Rightarrow> Nat \<Rightarrow> Int"
  apply (rule app_type'[where ?t="add f" and ?u="g"])
    apply (rule app_type'[where ?t=add and ?u=f])
      apply (rule add_type)
      apply (rule f_type)
      defer
    apply (rule g_type)
    defer
  (*subtyping*)
  apply (rule Dep_fun_typeI)+
  apply (rule app_type''[where ?t="f x" and ?u=y for x y])
    apply (rule app_type'[where ?t="f" and ?u=x for x])
      apply assumption
      apply assumption
      defer
    apply assumption
    defer
    defer
  (*subtyping*)
  apply assumption
  apply assumption
  apply (rule Int_if_Nat)
  apply assumption
  apply (rule Int_if_Nat)
  apply assumption
  done

lemma
  assumes f_type: "f : Nat \<Rightarrow> Int \<Rightarrow> Nat" and g_type: "g : Nat \<Rightarrow> Nat \<Rightarrow> Int"
  shows "add f g : Nat \<Rightarrow> Nat \<Rightarrow> Int"
  apply (rule Dep_fun_typeI)+
  apply (rule app_type'[where ?t="add f g x" and ?u="y" for x y])
    apply (rule app_type'[where ?t="add f g" and ?u=x for x])
      apply (rule app_type'[where ?t="add f" and ?u=g])
        apply (rule app_type'[where ?t="add" and ?u=f])
          apply (rule add_type)
          apply (rule f_type)
          defer
        apply (rule g_type)
        defer
      apply assumption
      defer
    apply assumption
    defer
  (*subtyping*)
  apply (rule Dep_fun_typeI)+
  apply (rule app_type''[where ?t="f x" and ?u=y for x y])
    apply (rule app_type'[where ?t="f" and ?u=x for x])
      apply assumption
      apply assumption
      defer
    apply assumption
    defer
  (*subtyping*)
  apply (rule Int_if_Nat)
  apply assumption
  apply assumption
  apply assumption
  apply assumption
  apply assumption
  apply (rule Int_if_Nat)
  apply assumption
  done

end

subsection \<open>Transitive Subtyping\<close>

experiment
begin

lemma
  assumes n_type: "n : A & (B & Nat)" and i_type: "i : Int & B"
  shows "add n i : Int & B"
  apply (rule app_type'[where ?t="add n"])
    apply (rule app_type'[where ?t=add])
      apply (rule add_type)
      apply (rule n_type)
      defer
    apply (rule i_type)
    defer
  (*subtyping*)
  apply (rule Int_typeI)
  apply (erule Int_typeE)+
  apply (rule Int_if_Nat)
  apply assumption
  apply (erule Int_typeE)+
  apply assumption
  apply assumption
  done

lemma
  assumes n_type: "n : Nat" and i_type: "i : Int"
  shows "add n i : Int \<bar> B"
  apply (rule app_type'[where ?t="add n"])
    apply (rule app_type'[where ?t=add])
      apply (rule add_type)
      apply (rule n_type)
      defer
    apply (rule i_type)
    defer
  (*subtyping*)
  apply (rule Union_type_leftI)
  apply (rule Int_if_Nat)
  apply assumption
  apply (rule Union_type_leftI)
  apply assumption
  done

lemma
  assumes n_type: "\<And>x. x : A \<Longrightarrow> n x : B x" and n_type': "\<And>x. x : A \<Longrightarrow> n x : B' x"
  and x_type: "x : A"
  and f_type: "\<And>C. f : (x : A) \<Rightarrow> C x \<Rightarrow> C x"
  shows "f x (n x) : B x & B' x"
  apply (rule app_dep_type'[where ?t="f x"])
    apply (rule app_dep_type'[where ?t=f])
      apply (rule f_type)
      apply (rule x_type)
      defer
    apply (rule n_type)
    defer
  (*subtyping*)
  apply (rule Int_typeI)
  apply assumption
  apply (rule n_type')
  apply (rule x_type)
  apply assumption
  apply (rule x_type)
  done

end


subsection \<open>Type Simplification and Equivalences\<close>

experiment
  fixes Vec :: "'a \<Rightarrow> 'a type"
  and pos :: "'a \<Rightarrow> bool"
  assumes Nat_if_pos_Int: "i : Int \<Longrightarrow> pos i \<Longrightarrow> i : Nat"
begin

lemma
  assumes v_type: "v : Vec n" and v'_type: "v' : Vec m"
  and n_eq_m: "n = m"
  shows "add v v' : Vec m"
  apply (rule app_type'[where ?t="add v"])
    apply (rule app_type'[where ?t=add])
      apply (rule add_type)
      apply (rule v_type)
      defer
    apply (rule v'_type)
    defer
  (*subtyping*)
  defer
  apply assumption
  (*left to the user; solvable with integration in simplifier*)
  oops

lemma
  assumes n_type: "n : Nat" and i_type: "i : Int"
  and "pos i"
  shows "add n i : Nat"
  apply (rule app_type'[where ?t="add n"])
    apply (rule app_type'[where ?t=add])
      apply (rule add_type)
      apply (rule n_type)
      defer
    apply (rule i_type)
    defer
  (*subtyping*)
  apply assumption
  apply (rule Nat_if_pos_Int)
  apply assumption
  apply (rule assms)
  done

lemma
  assumes n_type: "n : Nat" and i_type: "i : Int"
  and "pos i"
  shows "add n i : Int & type pos"
  apply (rule app_type'[where ?t="add n"])
    apply (rule app_type'[where ?t=add])
      apply (rule add_type)
      apply (rule n_type)
      defer
    apply (rule i_type)
    defer
  (*subtyping*)
  apply (rule Int_typeI)
  apply (rule Int_if_Nat)
  apply assumption
  defer
  apply (rule Int_typeI)
  apply assumption
  apply (rule has_typeI)
  apply (rule assms)
  apply (rule has_typeI)
  (*left to the user; solvable with integration in simplifier*)
  oops

lemma
  assumes f_type: "f : (x : A) \<Rightarrow> (y : B x) \<Rightarrow> C x y"
  and A_eq_B: "\<And>x. x : A \<Longrightarrow> B x = B' x"
  shows "add f : ((x : A) \<Rightarrow> (y : B' x) \<Rightarrow> C x y) \<Rightarrow> (x : A) \<Rightarrow> (y : B' x) \<Rightarrow> C x y"
  apply (rule app_dep_type''[where ?t="add" and ?u="f"])
    apply (rule add_type)
    apply (rule f_type)
  (*subtyping*)
  apply assumption
  apply (rule Dep_fun_typeI)+
    apply (rule app_dep_type'[where ?t="f x" and ?u=y for x y])
      apply (rule app_dep_type'[where ?t="f" and ?u=x for x])
        apply assumption
        apply assumption
        defer
      apply assumption
      defer
    apply assumption
  apply (subst A_eq_B)
  apply assumption
  apply assumption
  done

end


subsection \<open>Implicit Arguments\<close>

experiment
  fixes List :: "'a type \<Rightarrow> 'a type"
  and nil :: "'a type \<Rightarrow> 'a"
  and cons :: "'a type \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes nil_type: "nil : (A : Any) \<Rightarrow> List A"
  and cons_type: "cons : (A : Any) \<Rightarrow> A \<Rightarrow> List A \<Rightarrow> List A"
begin

(*When introducing implicits below binders, we need to apply them to
all binders*)
schematic_goal "(\<lambda>x y. ?X) = (\<lambda>x y. x y y)"
  apply (rule refl | succeed)
  oops

schematic_goal "(\<lambda>x y. ?X x y) = (\<lambda>x y. x y y)"
  by (rule refl)

schematic_goal
  "?A : ?TA \<Longrightarrow> x : ?TX \<Longrightarrow> ?B : ?TB \<Longrightarrow> cons ?A x (nil ?B) : ?T"
  apply (rule app_dep_type'[where ?t="cons A x" and ?u="nil B" for A B])
    apply (rule app_dep_type'[where ?t="cons A" and ?u="x" for A])
      apply (rule app_dep_type'[where ?t="cons" and ?u="A" for A])
        apply (rule cons_type)
        apply assumption
        defer
      apply assumption
      defer
    apply (rule app_dep_type'[where ?t=nil and ?u=B for B])
      apply (rule nil_type)
      apply assumption
      defer
    defer
  (*subtyping*)
  apply (rule Any_typeI)
  defer
  apply (rule Any_typeI)
  apply assumption
  apply assumption
  done

schematic_goal
  "?A : ?TA \<Longrightarrow> x : ?TX \<Longrightarrow> ?B : ?TB \<Longrightarrow> cons ?A x (nil ?B) : ?T"
  apply (rule app_dep_type[where ?t="cons A x" and ?u="nil B" for A B])
    apply (rule app_dep_type[where ?t="cons A" and ?u="x" for A])
      apply (rule app_dep_type[where ?t="cons" and ?u="A" for A])
        apply (rule cons_type)
        apply (rule Any_typeI)
      apply assumption
    apply (rule app_dep_type[where ?t=nil])
      (*Problem: when matching `nil ?B : List ?A = nil ?B : ?C ?B`,
        the higher-order unifier picks `?C=\<lambda>x. ?x` and `?B = List ?A`*)
    back
      apply (rule nil_type)
      apply (rule Any_typeI)
  done

schematic_goal
  "?A : ?TA \<Longrightarrow> x : ?TX \<Longrightarrow> ?B : ?TB \<Longrightarrow> cons ?A x (nil ?B) : ?T"
  apply (rule app_dep_type2[where ?t="cons A x" and ?u="nil B" for A B])
    apply (rule app_dep_type2[where ?t="cons A" and ?u="x" for A])
      apply (rule app_dep_type2[where ?t="cons" and ?u="A" for A])
        apply (rule cons_type)
        apply (rule reflexive)
        apply (rule Any_typeI)
      apply (rule reflexive)
      apply (assumption)
    apply (rule reflexive)
    apply (rule app_dep_type2[where ?t=nil])
      (*solution: delay flex-rigid pair*)
      apply (rule nil_type)
      apply (rule reflexive)
      apply (rule Any_typeI)
   done

schematic_goal "?A : ?TA \<Longrightarrow> B : ?TB \<Longrightarrow> nil ?A = B : ?T"
  apply (rule app_dep_type'[where ?t="(=) (nil A)" for A])
    apply (rule app_dep_type'[where ?t="(=)"])
      apply (rule eq_type)
      apply (rule app_dep_type'[where ?t="nil"])
        apply (rule nil_type)
        apply assumption
        defer
      defer
    apply assumption
    defer
  (*subtyping*)
  apply (rule Any_typeI)
  apply assumption
  apply assumption
  done

end

axiomatization
  nat_rec :: "'b \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b"
  and zero :: 'a ("0")
  and succ :: "'a \<Rightarrow> 'a"
where
  nat_rec_type: "nat_rec : A 0 \<Rightarrow> ((n : Nat) \<Rightarrow> A n \<Rightarrow> A (succ n)) \<Rightarrow> (n : Nat) \<Rightarrow> A n"
  and zero_type: "0 : Nat"
  and succ_type: "succ : Nat \<Rightarrow> Nat"

axiomatization
  Element :: "'a \<Rightarrow> 'a type"
  and nat :: "'a"
  and vec :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  and vnil :: "'a \<Rightarrow> 'a"
  and vcons :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"
  and vappend :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"
where
  vec_type: "vec : Any \<Rightarrow> Element nat \<Rightarrow> Any"
  and vnil_type: "vnil : (A : Any) \<Rightarrow> Element (vec A 0)"
  and vcons_type: "vcons: (A : Any) \<Rightarrow> (n : Element nat) \<Rightarrow>
    Element A \<Rightarrow> Element (vec A n) \<Rightarrow> Element (vec A (succ n))"
  and succ_type': "succ : Element nat \<Rightarrow> Element nat"
  and zero_type': "0 : Element nat"
  and vappend_type: "vappend: (A : Any) \<Rightarrow> (n : Element nat) \<Rightarrow> (m : Element nat) \<Rightarrow>
    Element (vec A n) \<Rightarrow> Element (vec A m) \<Rightarrow> Element (vec A (add n m))"
  and add_succ_eq_succ_add: "add (succ (n :: 'a)) m = succ (add n m)"

experiment
begin

schematic_goal
  "?A1 : ?TA1 \<Longrightarrow> ?A2 : ?TA2 \<Longrightarrow> ?A3 : ?TA3 \<Longrightarrow> ?A4 : ?TA4 \<Longrightarrow>
  ?n1 : ?Tn1 \<Longrightarrow> ?n2 : ?Tn2 \<Longrightarrow> ?n3 : ?Tn3 \<Longrightarrow> ?n4 : ?Tn4 \<Longrightarrow>
  ?m1 : ?Tm1 \<Longrightarrow> ?m2 : ?Tm2 \<Longrightarrow> ys : ?Tys \<Longrightarrow> x : ?Tx \<Longrightarrow> xs : ?Txs \<Longrightarrow>
  vappend ?A1 ?n1 ?m1 (vcons ?A2 ?n2 x xs) ys = vcons ?A3 ?n3 x (vappend ?A4 ?n4 ?m2 xs ys) : ?T"
  apply (rule app_dep_type'[where ?t="(=) (vappend A1 n1 m1 (vcons A2 n2 x xs) ys)" for A1 n1 m1 A2 n2])
    apply (rule app_dep_type'[where ?t="(=)"])
      apply (rule eq_type)
      apply (rule app_dep_type'[where ?t="vappend A1 n1 m1 (vcons A2 n2 x xs)" for A1 n1 m1 A2 n2])
        apply (rule app_dep_type'[where ?t="vappend A1 n1 m1" for A1 n1 m1])
          apply (rule app_dep_type'[where ?t="vappend A1 n1" for A1 n1])
            apply (rule app_dep_type'[where ?t="vappend A1" for A1])
              apply (rule app_dep_type'[where ?t="vappend"])
                apply (rule vappend_type)
                apply (assumption)
                defer
              (*unify constraints for matching meta variables*)
              apply (tactic \<open>rotate_tac 4 1\<close>, assumption)
              defer
            apply (tactic \<open>rotate_tac 8 1\<close>, assumption)
            defer
          apply (rule app_dep_type'[where ?t="vcons A2 n2 x" for A2 n2])
            apply (rule app_dep_type'[where ?t="vcons A2 n2" for A2 n2])
              apply (rule app_dep_type'[where ?t="vcons A2" for A2])
                apply (rule app_dep_type'[where ?t="vcons"])
                  apply (rule vcons_type)
                  apply (tactic \<open>rotate_tac 1 1\<close>, assumption)
                  defer
                apply (tactic \<open>rotate_tac 5 1\<close>, assumption)
                defer
              apply (tactic \<open>rotate_tac 10 1\<close>, assumption)
              defer
            apply (tactic \<open>rotate_tac 11 1\<close>, assumption)
            defer
          defer
        apply (tactic \<open>rotate_tac 10 1\<close>, assumption)
        defer
      defer
    apply (rule app_dep_type'[where ?t="vcons A3 n3 x" for A3 n3])
      apply (rule app_dep_type'[where ?t="vcons A3 n3" for A3 n3])
        apply (rule app_dep_type'[where ?t="vcons A3" for A3])
          apply (rule app_dep_type'[where ?t="vcons"])
            apply (rule vcons_type)
            apply (tactic \<open>rotate_tac 2 1\<close>, assumption)
            defer
          apply (tactic \<open>rotate_tac 6 1\<close>, assumption)
          defer
        apply (tactic \<open>rotate_tac 11 1\<close>, assumption)
        defer
      apply (rule app_dep_type'[where ?t="vappend A4 n4 m2 xs" for A4 n4 m2])
        apply (rule app_dep_type'[where ?t="vappend A4 n4 m2" for A4 n4 m2])
          apply (rule app_dep_type'[where ?t="vappend A4 n4" for A4 n4])
            apply (rule app_dep_type'[where ?t="vappend A4" for A4])
              apply (rule app_dep_type'[where ?t="vappend"])
                apply (rule vappend_type)
                apply (tactic \<open>rotate_tac 3 1\<close>, assumption)
                defer
              apply (tactic \<open>rotate_tac 7 1\<close>, assumption)
              defer
            apply (tactic \<open>rotate_tac 9 1\<close>, assumption)
            defer
          apply (tactic \<open>rotate_tac 12 1\<close>, assumption)
          defer
        apply (tactic \<open>rotate_tac 10 1\<close>, assumption)
        defer
      defer
    defer
  (*subtyping*)
  apply (rule Any_typeI)
  apply (tactic \<open>rotate_tac 4 1\<close>, assumption)
  apply (tactic \<open>rotate_tac 8 1\<close>, assumption)
  apply (rule Any_typeI)
  apply (tactic \<open>rotate_tac 5 1\<close>, assumption)
  apply (tactic \<open>rotate_tac 11 1\<close>, assumption)
  apply (tactic \<open>rotate_tac 12 1\<close>, assumption)
  apply (tactic \<open>rotate_tac 15 1\<close>, assumption)
  apply (tactic \<open>rotate_tac 10 1\<close>, assumption)
  apply (tactic \<open>rotate_tac 14 1\<close>, assumption)
  apply (rule Any_typeI)
  apply (tactic \<open>rotate_tac 6 1\<close>, assumption)
  apply (tactic \<open>rotate_tac 11 1\<close>, assumption)
  apply (rule Any_typeI)
  apply (tactic \<open>rotate_tac 7 1\<close>, assumption)
  apply (tactic \<open>rotate_tac 9 1\<close>, assumption)
  apply (tactic \<open>rotate_tac 12 1\<close>, assumption)
  apply (tactic \<open>rotate_tac 10 1\<close>, assumption)
  apply (tactic \<open>rotate_tac 15 1\<close>, assumption)
  apply (tactic \<open>rotate_tac 14 1\<close>)
  apply (simp only: add_succ_eq_succ_add)
  done
  (*assumptions can be cleaned by merging assumptions for meta variables
    and discharging remaining assumptions by type-checker.*)

schematic_goal "g : ?Tg \<Longrightarrow> ?y1 : ?Ty1 \<Longrightarrow> ?y2 : ?Ty2 \<Longrightarrow> x : ?Tx \<Longrightarrow> xs : ?Txs
  \<Longrightarrow> g (vcons ?y1 ?y2 x xs) : ?T"
  apply (rule app_type[where ?t=g])
    apply assumption
    apply (rule app_dep_type[where ?t="vcons y1 y2 x" for y1 y2])
      apply (rule app_dep_type[where ?t="vcons y1 y2" for y1 y2])
        apply (rule app_dep_type[where ?t="vcons y1" for y1])
          apply (rule app_dep_type[where ?t="vcons"])
            apply (rule vcons_type)
            apply (rule Any_typeI)
          apply (tactic \<open>rotate_tac 2 1\<close>, assumption)
        apply (tactic \<open>rotate_tac 3 1\<close>, assumption)
      apply (tactic \<open>rotate_tac 4 1\<close>, assumption)
   done

end

experiment
  fixes Id
  and refl
  and J
  assumes Id_type: "Id : (A : U) \<Rightarrow> A \<Rightarrow> A \<Rightarrow> U"
  and refl_type: "refl: (A : U) \<Rightarrow> (x: A) \<Rightarrow> Id A x x"
  and J_type: "J: (A : U) \<Rightarrow> (C: (x: A) \<Rightarrow> (y: A) \<Rightarrow>
    (p: Id A x y) \<Rightarrow> U) \<Rightarrow> ((x: A) \<Rightarrow> C x x (refl A x)) \<Rightarrow> (a: A) \<Rightarrow> (b: A)
    \<Rightarrow> (p: Id A a b) \<Rightarrow> C a b p"
begin

text \<open>The proof term for reflexivity of equality:\<close>

schematic_goal
  "?A1 : ?TA1 \<Longrightarrow> ?C1 : ?TC1 \<Longrightarrow> ?A2 : ?TA2 \<Longrightarrow> a : ?Ta \<Longrightarrow> b : ?Tb \<Longrightarrow>
    p : ?Tp \<Longrightarrow> J ?A1 ?C1 (refl ?A2) a b p : ?T"
  apply (rule app_dep_type[where ?t="J A1 C1 (\<lambda>x. refl A2 x) a b" for A1 C1 A2])
    apply (rule app_dep_type[where ?t="J A1 C1 (\<lambda>x. refl A2 x) a" for A1 C1 A2])
      apply (rule app_dep_type[where ?t="J A1 C1 (\<lambda>x. refl A2 x)" for A1 C1 A2])
        apply (rule app_dep_type[where ?t="J A1 C1" for A1 C1])
          apply (rule app_dep_type[where ?t="J A1" for A1])
            apply (rule app_dep_type[where ?t="J"])
              apply (rule J_type)
              apply assumption
            apply (tactic \<open>rotate_tac 1 1\<close>, assumption)
          apply (rule Dep_fun_typeI)
          apply (rule app_dep_type[where ?t="refl A2" for A2])
            apply (rule app_dep_type[where ?t="refl"])
              apply (rule refl_type)
              apply (tactic \<open>rotate_tac 2 1\<close>, assumption)
            apply (tactic \<open>rotate_tac 7 1\<close>, assumption)
          apply (tactic \<open>rotate_tac 3 1\<close>, assumption)
        apply (tactic \<open>rotate_tac 4 1\<close>, assumption)
      apply (tactic \<open>rotate_tac 5 1\<close>, assumption)
  done

end

subsubsection \<open>Implicits requiring Higher-Order Unification\<close>

experiment
begin

schematic_goal "nat_rec 0 (\<lambda>n h. 0) 0 : Nat"
  apply (rule app_type[where ?t="nat_rec 0 (\<lambda>n h. 0)"])
    apply (rule app_type[where ?t="nat_rec 0"])
      apply (rule app_type[where ?t="nat_rec"])
        apply (rule nat_rec_type)
        apply (rule zero_type)
      apply (rule Dep_fun_typeI)+
      apply (rule zero_type)
    apply (rule zero_type)
  done

schematic_goal "nat_rec 0 (\<lambda>n h. 0) 0 : ?T"
  apply (rule app_type[where ?t="nat_rec 0 (\<lambda>n h. 0)"])
    apply (rule app_type[where ?t="nat_rec 0"])
      apply (rule app_type[where ?t="nat_rec"])
        apply (rule nat_rec_type)
        apply (rule zero_type)
      apply (rule Dep_fun_typeI)+
      apply (rule zero_type)
    apply (rule zero_type)
  done

schematic_goal "nat_rec (\<lambda>x. x) (\<lambda>n h x. x) 0 : ?T"
  apply (rule app_type[where ?t="nat_rec (\<lambda>x. x) (\<lambda>n h x. x)"])
    apply (rule app_type[where ?t="nat_rec (\<lambda>x. x)"])
      apply (rule app_type[where ?t="nat_rec"])
        apply (rule nat_rec_type)
        apply (rule Dep_fun_typeI)
        apply assumption
      apply (rule Dep_fun_typeI)+
      apply assumption
    apply (rule zero_type)
  done

lemma nat_rec_type':
  "nat_rec : A 0 \<Rightarrow> ((n : Element nat) \<Rightarrow> A n \<Rightarrow> A (succ n)) \<Rightarrow> (n : Element nat) \<Rightarrow> A n"
  sorry

lemma zero_type': "0 : Element nat"
  sorry

(*Problem: too much guessing*)
schematic_goal "?T1 : ?TT1 \<Longrightarrow> ?T2 : ?TT2 \<Longrightarrow> ?n : ?Tn \<Longrightarrow>
  nat_rec (vnil ?T1) (\<lambda>n v. vcons (?T2 n v) (?n n v) n v) 0 : Element (vec nat 0)"
  apply (rule app_dep_type[where ?t="nat_rec (vnil T1) (\<lambda>n v. vcons (T2 n v) (m n v) n v)" for T1 T2 m])
    apply (rule app_type[where ?t="nat_rec (vnil T1)" for T1])
      apply (rule app_type[where ?t="nat_rec"])
        apply (rule nat_rec_type')
        (*problem: need to help unifier*)
        apply (rule app_dep_type[where ?t="vnil" and ?B="\<lambda>A. Element (vec A 0)"])
          apply (rule vnil_type)
          apply (rule Any_typeI)
      apply (rule Dep_fun_typeI)
      apply (rule Dep_fun_typeI)
      apply (rule app_type[where ?t="vcons _ _ _"])
        apply (rule app_type[where ?t="vcons _ _"])
          (*problem: need to help unifier*)
          apply (rule app_dep_type[where ?t="vcons T2" and
          ?B="\<lambda>n. Element nat \<Rightarrow> Element (vec nat n) \<Rightarrow> Element (vec nat (succ n))" for T2])
            apply (rule app_dep_type[where ?t="vcons"])
              apply (rule vcons_type)
              apply (rule Any_typeI)
            apply assumption
          apply assumption
        apply assumption
    apply (rule zero_type')
  done

schematic_goal "?T1 : ?TT1 \<Longrightarrow> ?T2 : ?TT2 \<Longrightarrow> ?n : ?Tn \<Longrightarrow>
  nat_rec (vnil ?T1) (\<lambda>n v. vcons (?T2 n v) (?n n v) n v) 0 : Element (vec nat 0)"
  apply (rule app_dep_type2[where ?t="nat_rec (vnil T1) (\<lambda>n v. vcons (T2 n v) (m n v) n v)" for T1 T2 m])
    apply (rule app_dep_type2[where ?t="nat_rec (vnil T1)" for T1])
      apply (rule app_dep_type2[where ?t="nat_rec"])
        apply (rule nat_rec_type')
        apply (rule reflexive)
        apply (rule app_dep_type2[where ?t="vnil"])
          apply (rule vnil_type)
          apply (rule reflexive)
          apply (rule Any_typeI)
      apply (rule reflexive)
      apply (rule Dep_fun_typeI)
      apply (rule Dep_fun_typeI)
      apply (rule app_dep_type2[where ?t="vcons _ _ _"])
        apply (rule app_dep_type2[where ?t="vcons _ _"])
          apply (rule app_dep_type2[where ?t="vcons T2" for T2])
            apply (rule app_dep_type2[where ?t="vcons"])
              apply (rule vcons_type)
              apply (rule reflexive)
              apply (rule Any_typeI)
            apply (rule reflexive)
            apply (tactic \<open>rotate_tac 2 1\<close>, assumption)
          apply (rule reflexive)
          apply assumption
        apply (rule reflexive)
        apply (assumption)
    apply (rule reflexive)
    apply (rule zero_type')
  done

schematic_goal "n : ?Tn \<Longrightarrow> ?m : ?Tm \<Longrightarrow> v : ?Tv \<Longrightarrow>
  vcons nat n 0 v : Element (vec nat ?m)"
  apply (rule app_dep_type2[where t="vcons nat m 0" for m])
    apply (rule app_dep_type2[where t="vcons nat m" for m])
      apply (rule app_dep_type2[where t="vcons nat"])
        apply (rule app_dep_type2[where t="vcons"])
          apply (rule vcons_type)
          apply (rule reflexive)
          apply (rule Any_typeI)
        apply (rule reflexive)
        apply (assumption)
      apply (rule reflexive)
      apply (rule zero_type')
    apply (rule reflexive)
    apply assumption
  done

end


subsection \<open>Common subterms\<close>

lemma
  shows "add (succ 0) (succ 0) : Nat"
  apply (rule app_type'[where ?t="add (succ 0)"])
    apply (rule app_type'[where ?t=add])
      apply (rule add_type)
      apply (rule app_type'[where ?t="succ"])
        apply (rule succ_type)
        apply (rule zero_type)
        defer
      defer
    (*here we whould be able to re-use that we already proved "succ 0 : Nat" above*)
    (*this cannot be encoded in the lemmas but must be done by the type checker instead*)
    apply (rule app_type'[where ?t="succ"])
      apply (rule succ_type)
      apply (rule zero_type)
      defer
    defer
  (*subtyping*)
  apply assumption+
  done


subsection\<open>Typeclasses\<close>

abbreviation "Type \<equiv> (Any :: 'a type)"

experiment
  fixes Monoid :: "'a type \<Rightarrow> 'a type"
  and Monoid_add :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"
  and Nat_Monoid :: "'a"
  and Int_Monoid :: "'a"
  and Pair :: "'a type \<Rightarrow> 'a type \<Rightarrow> 'a type"
  and pair :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  and Pair_Monoid :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes Monoid_add_type: "Monoid_add : Monoid A \<Rightarrow> A \<Rightarrow> A \<Rightarrow> A"
  and Nat_Monoid_type: "Nat_Monoid : Monoid Nat"
  and Int_Monoid_type: "Int_Monoid : Monoid Int"
  and pair_type: "pair : A \<Rightarrow> B \<Rightarrow> Pair A B"
  and Pair_Monoid_type: "Pair_Monoid : Monoid A \<Rightarrow> Monoid B \<Rightarrow> Monoid (Pair A B)"
begin

schematic_goal "?A : ?TA \<Longrightarrow> ?B : ?TB \<Longrightarrow> Pair_Monoid ?A ?B : Monoid (Pair Nat Int)"
  apply (rule app_dep_type[where ?t="Pair_Monoid A" for A])
    apply (rule app_dep_type[where ?t="Pair_Monoid"])
      apply (rule Pair_Monoid_type)
      apply assumption
    apply assumption
  (*remaining assumption could be discharged by typeclass mechanism*)
  done

definition "annot t a \<equiv> t"
notation annot (infix ":a" 50)

definition "Typeclass x A \<equiv> x : A"

lemma annot_Typeclass:
  assumes "Typeclass x A"
  shows "(x :a Typeclass) : A"
  using assms unfolding annot_def Typeclass_def by simp

schematic_goal "Monoid_add (?A :a Typeclass) 0 0 : ?T"
  apply (rule app_dep_type[where ?t="Monoid_add A 0" for A])
    apply (rule app_dep_type[where ?t="Monoid_add A" for A])
      apply (rule app_dep_type[where ?t="Monoid_add"])
        apply (rule Monoid_add_type)
        apply (rule annot_Typeclass)
          defer
      apply (rule zero_type)
    apply (rule zero_type)
  (*could be discharged by typeclass mechanism*)
  oops

schematic_goal "?p : ?Tp \<Longrightarrow> Monoid_add (?A :a Typeclass) (pair 0 0) ?p : ?T"
  apply (rule app_dep_type[where ?t="Monoid_add A (pair 0 0)" for A])
    apply (rule app_dep_type[where ?t="Monoid_add A" for A])
      apply (rule app_dep_type[where ?t="Monoid_add"])
        apply (rule Monoid_add_type)
        apply (rule annot_Typeclass)
          defer
      apply (rule app_dep_type[where ?t="pair 0"])
        apply (rule app_dep_type[where ?t="pair"])
          apply (rule pair_type)
          apply (rule zero_type)
        apply (rule zero_type)
      apply assumption
  (*could be discharged by typeclass mechanism*)
  oops

text \<open>Discharging typeclass assumptions\<close>

schematic_goal "?M : Monoid (Pair Nat Int)"
(*Problem: We cannot use Pair_Monoid_type directly but need to derive an intro
rule from it where `Monoid (Pair A B)` is the conclusion.
*)
  oops

subsubsection \<open>Typeclasses in Types\<close>

schematic_goal "n : ?Tn \<Longrightarrow> m : ?Tm \<Longrightarrow> v : ?Tv \<Longrightarrow> ?M : ?TM \<Longrightarrow>
  vcons nat n 0 v : Element (vec nat (Monoid_add (?M :a Typeclass) n (succ 0)))"
  apply (rule app_dep_type2[where t="vcons nat n 0"])
    apply (rule app_dep_type2[where t="vcons nat n"])
      apply (rule app_dep_type2[where t="vcons nat"])
        apply (rule app_dep_type2[where t="vcons"])
          apply (rule vcons_type)
          apply (rule reflexive)
          apply (rule Any_typeI)
        apply (rule reflexive)
        apply (assumption)
      apply (rule reflexive)
      apply (rule zero_type')
    (* apply (rule reflexive) *)
    defer
    apply assumption
  (*missing typeclass goal for M blocks further simplification*)
  oops

lemma has_type_type: "(:) : A \<Rightarrow> B \<Rightarrow> Bool"
  by unfold_types

(*we also need to check the type of T*)
lemma typestart:
  assumes "T : TT"
  and "x : T"
  shows "(x : T) : Bool"
  using assms by auto

lemma typestart':
  assumes "T : TT"
  and "x : T"
  shows "x : T"
  using assms by auto

lemma Element_type: "Element : A \<Rightarrow> Type"
  by unfold_types

lemma Dep_fun_type_type: "Dep_fun_type : A \<Rightarrow> B \<Rightarrow> Type"
  by unfold_types

lemma Dep_fun_typeI':
  assumes "A : TA"
  and "\<And>x. x : A \<Longrightarrow> f x : B x"
  shows "f : (x : A) \<Rightarrow> B x"
  unfolding Dep_fun_type_def meaning_of_type by auto

lemma "0 : Nat"
  apply (rule typestart')
    apply (rule typestart')
    apply (rule app_dep_type2[where t="(:)"])
    apply (rule has_type_type)
    apply (rule reflexive)
    apply (rule app_dep_type2[where t="(:) 0"])
    oops

schematic_goal "?n : ?Tn \<Longrightarrow> m : ?Tm \<Longrightarrow> v : ?Tv \<Longrightarrow> ?T : ?TT \<Longrightarrow> ?M : ?TM \<Longrightarrow>
  (vcons ?T ?n 0 v : Element (vec nat (Monoid_add (?M :a Typeclass) ?m (succ 0)))) : Any"
  apply (rule typestart)
    apply (rule app_dep_type2[where t=Element])
      apply (rule Element_type)
      apply (rule reflexive)
      apply (rule app_dep_type2[where t="vec nat"])
        apply (rule app_dep_type2[where t="vec"])
          apply (rule vec_type)
          apply (rule reflexive)
          apply (rule Any_typeI)
        apply (rule reflexive)
        apply (rule app_dep_type2[where t="Monoid_add _ _"])
          apply (rule app_dep_type2[where t="Monoid_add _"])
            apply (rule app_dep_type2[where t="Monoid_add"])
              apply (rule Monoid_add_type)
              apply (rule reflexive)
              apply (rule annot_Typeclass)
                defer
            apply (rule reflexive)
            apply assumption
          apply (rule reflexive)
          apply (rule app_dep_type2[where ?t=succ])
            apply (rule succ_type')
            apply (rule reflexive)
            apply (rule zero_type')
    apply (rule app_dep_type2[where t="vcons nat _ 0"])
      apply (rule app_dep_type2[where t="vcons nat _"])
        apply (rule app_dep_type2[where t="vcons nat"])
          apply (rule app_dep_type2[where t="vcons"])
            apply (rule vcons_type)
            apply (rule reflexive)
            apply (rule Any_typeI)
          apply (rule reflexive)
          apply (assumption)
        apply (rule reflexive)
        apply (rule zero_type')
      (* apply (rule reflexive) *)
      defer
      apply assumption
    (*solvable by first applying typeclass mechanism and then simplifying*)
    oops


end

subsection \<open>From Papers\<close>

experiment
  fixes lt :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
begin

(*cf. https://arxiv.org/pdf/1202.4905.pdf*)
schematic_goal "c1 : Nat \<Longrightarrow> c2 : P1 c1 \<Longrightarrow> c3 : P2 c1 c2 \<Longrightarrow> (\<lambda>f. f c1 c2 c3) : ?T"
  apply (rule Dep_fun_typeI)
  apply (rule app_dep_type[where ?t="x c1 c2" and ?u="c3" for x])
    apply (rule app_dep_type[where ?t="x c1" and ?u=c2 for x])
      apply (rule app_dep_type[where ?t="x" and ?u=c1 for x])
        apply assumption
        apply (assumption)
      apply (assumption)
    apply (assumption)
  done

schematic_goal "c1 : Nat \<Longrightarrow> c2 : P1 c1 \<Longrightarrow> c3 : P2 c1 c2 \<Longrightarrow> (\<lambda>f. f c1 c2 c3) : ?T"
  apply (rule Dep_fun_typeI)
  apply (rule app_dep_type2[where ?t="x c1 c2" and ?u="c3" for x])
    apply (rule app_dep_type2[where ?t="x c1" and ?u=c2 for x])
      apply (rule app_dep_type2)
        apply assumption
        apply (rule reflexive)
        apply (assumption)
      apply (rule reflexive)
      apply (assumption)
    apply (rule reflexive)
    apply (assumption)
  done

schematic_goal "o : Nat \<Longrightarrow> p : gt o 0 \<Longrightarrow> ?T : ?TT \<Longrightarrow> ?P : ?TP \<Longrightarrow> ?x : ?Tx \<Longrightarrow>
  Ex_intro : (T : Any) \<Rightarrow> (P : T \<Rightarrow> Prop) \<Rightarrow> (x : T) \<Rightarrow> P x \<Rightarrow> Exi T P \<Longrightarrow>
  Ex_intro ?T ?P ?x p : Exi Nat (\<lambda>x. gt x 0)"
  apply (rule app_dep_type2[where ?t="Ex_intro T P x" for T P x])
    apply (rule app_dep_type2[where ?t="Ex_intro T P" for T P])
      apply (rule app_dep_type2[where ?t="Ex_intro T" for T])
        apply (rule app_dep_type2[where ?t="Ex_intro"])
          apply assumption
          apply (rule reflexive)
          apply (rule Any_typeI)
        apply (rule reflexive)
        apply assumption
      apply (rule reflexive)
      apply (tactic \<open>rotate_tac 4 1\<close>, assumption)
    apply (rule reflexive)
    apply assumption
  done


end


subsection \<open>Meeting Notes\<close>

(* lemma appl_type:
  assumes "t : (x : A) \<Rightarrow> B x"
  and "u : A"
  shows [p=100]: "t u : B u"
  sorry

(*subtyping in domain*)
lemma appl_type':
  assumes "t : (x : A) \<Rightarrow> B x"
  and "u : A'"
  (*subtyping*)
  and [p=0, s=subtyping]: "u : A' \<Longrightarrow> u : A"
  shows [p=50]: "t u : B u"
  (*Question: specify unifier for individual lemmas?*)
  sorry

(*subtyping in domain and codomain*)
lemma appl_type'':
  assumes "t : (x : A) \<Rightarrow> B' x"
  and "u : A'"
  (*subtyping*)
  and [p=0, s=subtyping]: "t u : B' u \<Longrightarrow> t u : B u"
  and [p=0, s=subtyping]: "u : A' \<Longrightarrow> u : A"
  shows [p=25]: "t u : B u"
  sorry

lemma Nat_if_pos_Int:
  assumes "i : Int"
  and [p=25, s=auto]: "0 \<le> i"
  shows "i : Nat"
  sorry

lemma NonEmptyListI:
  assumes "l : List A"
  and "l' : List A"
  and [p=25, s=auto]: "l \<noteq> [] \<or> l' \<noteq> []"
  shows "l @ l' : NonEmptyList A"
  sorry *)

(*
Meeting notes:
1. What's the "selling point"?
2. Automatic inference of priorities
*)

(*
Kevin's notes:
-1. When inserting implicit arguments, pass all bound variables to meta variables
0. Specify solvers for assumptions of a lemma
1. Priority of rules
  - maybe priorities based on shape useful with update whenever a meta variables is instantiated?
    -> mapping from meta variables to goals
2. Priority of assumptions
3. Use first-order unifier (in most or all cases?)
  - Specification of unification algorithm for rules?
4. Postponing zero-priority rules (e.g. subtype conditions, additional assumptions)
5. consolidate remaining assumptions for variables using unification hints
6. Problem: guessing when applying Dep_fun_typeI
  - Idea: Types by HOL as a safeguard
7. Problem: how to discharge typeclass assumptions
  - Idea: Typeclasses are always defined as functions too and as such,
    we can automatically create a backward rule from the type rule when appropriately tagged
  - Note: typeclasses are like "canonical terms of a given type"
8. Notation and rules for type classes and implicits, i.e. {}, [] parameters
  - add pre-run to insert missing arguments
  - annotations for type classes can be added with app_dep_type2
9. Store proved theorems for follow-up goals and pass as assumptions?
  - caching of types for subterms
  - caching of derived typeclasses;
  - problem: need to keep track of context and check for diffs
10. use bidirectional breadth-first search for subtyping
11. compare with Mizar approach
12. compare with Lean approach
  - type classes use caching and suspended nodes with notifier for new solutions
  - reduction is taken into consideration, e.g. `B (snd \<langle>a, b\<rangle>)` and `B b` match)
  - lean does prioritise based on structure of constraints, e.g. flex flex, rigid,
    choice, etc. rather than priority;
    however, their constraints are unique (except for choice constraints) and
    hence whenever a, e.g. flex-flex pair, arises, they safely may be postponed
    because there is no other choice on the current goal. In our case, however,
    there may be other rules to complete the current goal.
13. subsume transfer and autoref?
14. Problem: how to stop applying rules recursively to meta-variables, e.g. app_type
  to `?X : ?TX`?
    Solutions:
  a. priorities that are recalculated whenever meta-variable is instantiated
     problem: should be solved immediately if solvable by assumption
  b. create delay rules
  c. use matching instead of unification
15. elaborating t : {x : A} \<rightarrow> B will result in \<lambda>{x} \<rightarrow> t, where {x} binds an implicit
argument
  - cf https://arxiv.org/pdf/1609.09709.pdf
*)


end