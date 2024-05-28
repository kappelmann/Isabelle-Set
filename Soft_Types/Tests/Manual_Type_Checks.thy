theory Manual_Type_Checks
  imports "Soft_Types.Soft_Types_HOL"
begin

subsection \<open>Greedy Instantiations and Subtyping\<close>

consts Nat :: "'a type"
consts Int :: "'a type"
consts add :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"

lemma Int_if_Nat: "x \<Ztypecolon> Nat \<Longrightarrow> x \<Ztypecolon> Int"
  sorry

lemma add_type: "add \<Ztypecolon> A \<Rightarrow> A \<Rightarrow> A"
  sorry

lemma app_type:
  assumes "t \<Ztypecolon> A \<Rightarrow> B"
  and "t \<Ztypecolon> A \<Rightarrow> B \<Longrightarrow> u \<Ztypecolon> A"
  shows "t u \<Ztypecolon> B"
  sorry

(*subtyping in domain and codomain*)
lemma app_type':
  assumes "t \<Ztypecolon> A \<Rightarrow> B'"
  and "t \<Ztypecolon> A \<Rightarrow> B' \<Longrightarrow> u \<Ztypecolon> A'"
  (*subtyping*)
  and "t u \<Ztypecolon> B' \<Longrightarrow> t u \<Ztypecolon> B"
  and "t \<Ztypecolon> A \<Rightarrow> B' \<Longrightarrow> u \<Ztypecolon> A' \<Longrightarrow> u \<Ztypecolon> A"
  shows "t u \<Ztypecolon> B"
  sorry

(*subtyping in domain*)
lemma app_type'':
  assumes "t \<Ztypecolon> A \<Rightarrow> B"
  and "t \<Ztypecolon> A \<Rightarrow> B \<Longrightarrow> u \<Ztypecolon> A'"
  (*subtyping*)
  and "t \<Ztypecolon> A \<Rightarrow> B \<Longrightarrow> u \<Ztypecolon> A' \<Longrightarrow> u \<Ztypecolon> A"
  shows "t u \<Ztypecolon> B"
  sorry

(*loops if above rules are tagged with intro *)
(* schematic_goal
  assumes n_type: "n \<Ztypecolon> Nat" and i_type: "i \<Ztypecolon> Int"
  shows "add n i \<Ztypecolon> ?T"
  using assms by (-) auto *)

lemma app_dep_type:
  assumes "t \<Ztypecolon> (x : A) \<Rightarrow> B x"
  and "t \<Ztypecolon> (x : A) \<Rightarrow> B x \<Longrightarrow> u \<Ztypecolon> A"
  shows "t u \<Ztypecolon> B u"
  sorry

(*subtyping in domain and codomain*)
lemma app_dep_type':
  assumes "t \<Ztypecolon> (x : A) \<Rightarrow> B' x"
  and "t \<Ztypecolon> (x : A) \<Rightarrow> B' x \<Longrightarrow> u \<Ztypecolon> A'"
  (*subtyping*)
  and "t u \<Ztypecolon> B' u \<Longrightarrow> t u \<Ztypecolon> B u"
  and "t \<Ztypecolon> (x : A) \<Rightarrow> B' x \<Longrightarrow> u \<Ztypecolon> A' \<Longrightarrow> u \<Ztypecolon> A"
  shows "t u \<Ztypecolon> B u"
  sorry

(*subtyping in domain*)
lemma app_dep_type'':
  assumes "t \<Ztypecolon> (x : A) \<Rightarrow> B x"
  and "t \<Ztypecolon> (x : A) \<Rightarrow> B x \<Longrightarrow> u \<Ztypecolon> A'"
  (*subtyping*)
  and "t \<Ztypecolon> (x : A) \<Rightarrow> B x \<Longrightarrow> u \<Ztypecolon> A' \<Longrightarrow> u \<Ztypecolon> A"
  shows "t u \<Ztypecolon> B u"
  sorry

lemma
  assumes f_type: "f \<Ztypecolon> (A \<Rightarrow> C) \<Rightarrow> C"
  and c_type: "c \<Ztypecolon> A \<Rightarrow> Bool \<Rightarrow> C"
  shows "f (\<lambda> a. c a True) \<Ztypecolon> C"
  using assms
  apply -
  apply (rule app_type''[where ?t=f])
    apply (rule f_type)
    apply (rule Dep_funI)
    apply (rule app_type''[where ?t="c a" for a])
      apply (rule app_type''[where ?t="c" for a])
        apply (rule c_type)
        apply assumption
        defer
      apply (rule AnyI)
      defer
    defer
  (*subtyping*)
  apply assumption+
  done

(*subtyping in domain and codomain*)
schematic_goal
  assumes n_type: "n \<Ztypecolon> Nat" and i_type: "i \<Ztypecolon> Int"
  shows "add n i \<Ztypecolon> ?T"
  using assms
  apply -
  apply (rule app_type'[where ?t="add n" and ?u="i"])
    apply (rule app_type'[where ?t=add and ?u=n])
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
  apply assumption
  apply assumption
  done

(*subtyping in domain*)
schematic_goal
  assumes n_type: "n \<Ztypecolon> Nat" and i_type: "i \<Ztypecolon> Int"
  shows "add n i \<Ztypecolon> ?T"
  using assms
  apply -
  apply (rule app_type''[where ?t="add n" and ?u="i"])
    apply (rule app_type''[where ?t=add and ?u=n])
      apply (rule add_type)
      apply (rule n_type)
      defer
    apply (rule i_type)
    defer
  (*subtyping*)
  apply (rule Int_if_Nat)
  apply assumption
  apply assumption
  done


subsection \<open>Higher-Order Functions\<close>

consts mynat :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"

lemma mynat_type: "mynat \<Ztypecolon> Nat \<Rightarrow> Nat \<Rightarrow> Nat"
  sorry

(*compound arguments with subtyping in domain*)
schematic_goal
  assumes n_type: "n \<Ztypecolon> Nat" and i_type: "i \<Ztypecolon> Int"
  shows "add (mynat n n) i \<Ztypecolon> ?T"
  using assms
  apply -
  apply (rule app_type''[where ?t="add (mynat n n)" and ?u="i"])
    apply (rule app_type''[where ?t=add and ?u="mynat n n"])
      apply (rule add_type)
      apply (rule app_type''[where ?t="mynat n" and ?u="n"])
        apply (rule app_type''[where ?t="mynat" and ?u="n"])
          apply (rule mynat_type)
          apply (rule n_type)
          defer
        apply (rule n_type)
        defer
      defer
    apply (rule i_type)
    defer
  (*subtyping*)
  apply assumption
  apply assumption
  apply (rule app_type''[where ?t="mynat n" and ?u=n])
    apply (rule app_type'[where ?t="mynat" and ?u=n])
      apply (rule mynat_type)
      apply (rule n_type)
      defer
    apply assumption
    defer
  (*subtyping*)
  apply assumption
  defer
  apply (rule app_type'[where ?t="mynat" and ?u=n])
    apply (rule mynat_type)
    apply (rule n_type)
    defer
  apply assumption
  defer
  defer
  (*loops; subtyping goals must be solved by user instead*)
  oops

schematic_goal
  assumes f_type: "f \<Ztypecolon> Nat \<Rightarrow> Int \<Rightarrow> Nat" and g_type: "g \<Ztypecolon> Nat \<Rightarrow> Nat \<Rightarrow> Int"
  shows "add f g \<Ztypecolon> Nat \<Rightarrow> Nat \<Rightarrow> Int"
  apply (rule app_type''[where ?t="add f" and ?u="g"])
    apply (rule app_type''[where ?t=add and ?u=f])
      apply (rule add_type)
      apply (rule f_type)
      defer
    apply (rule g_type)
    defer
  (*subtyping*)
  apply (rule Dep_funI)+
  apply (rule app_type'[where ?t="f x" and ?u=y for x y])
    apply (rule app_type''[where ?t="f" and ?u=x for x])
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

schematic_goal
  assumes f_type: "f \<Ztypecolon> Nat \<Rightarrow> Int \<Rightarrow> Nat" and g_type: "g \<Ztypecolon> Nat \<Rightarrow> Nat \<Rightarrow> Int"
  shows "add f g \<Ztypecolon> Nat \<Rightarrow> Nat \<Rightarrow> Int"
  apply (rule Dep_funI)+
  apply (rule app_type''[where ?t="add f g x" and ?u="y" for x y])
    apply (rule app_type''[where ?t="add f g" and ?u=x for x])
      apply (rule app_type''[where ?t="add f" and ?u=g])
        apply (rule app_type''[where ?t="add" and ?u=f])
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
  apply (rule Dep_funI)+
  apply (rule app_type'[where ?t="f x" and ?u=y for x y])
    apply (rule app_type''[where ?t="f" and ?u=x for x])
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


subsection \<open>Non-Immediate Subtyping\<close>

schematic_goal
  assumes n_type: "n \<Ztypecolon> A & (B & Nat)" and i_type: "i \<Ztypecolon> Int & B"
  shows "add n i \<Ztypecolon> Int & B"
  using assms
  apply -
  apply (rule app_type''[where ?t="add n" and ?u="i"])
    apply (rule app_type''[where ?t=add and ?u=n])
      apply (rule add_type)
      apply (rule n_type)
      defer
    apply (rule i_type)
    defer
  (*subtyping*)
  (* apply (assumption | (rule InterI | rule Int_if_Nat) | erule InterE)+ *)
  apply (rule InterI)
  apply (erule InterE)+
  apply (rule Int_if_Nat)
  apply assumption
  apply (erule InterE)+
  apply assumption
  apply assumption
  done

schematic_goal
  assumes n_type: "n \<Ztypecolon> Nat" and i_type: "i \<Ztypecolon> Int"
  shows "add n i \<Ztypecolon> Int \<bar> B"
  using assms
  apply -
  apply (rule app_type''[where ?t="add n" and ?u="i"])
    apply (rule app_type''[where ?t=add and ?u=n])
      apply (rule add_type)
      apply (rule n_type)
      defer
    apply (rule i_type)
    defer
  (*subtyping*)
  apply (rule Union_leftI)
  apply (rule Int_if_Nat)
  apply assumption
  apply (rule Union_leftI)
  apply assumption
  done

schematic_goal
  assumes n_type: "\<And>x. x \<Ztypecolon> A \<Longrightarrow> n x \<Ztypecolon> B x" and n_type': "\<And>x. x \<Ztypecolon> A \<Longrightarrow> n x \<Ztypecolon> B' x"
  and x_type: "x \<Ztypecolon> A"
  and f_type: "\<And>C. f \<Ztypecolon> (x : A) \<Rightarrow> C x \<Rightarrow> C x"
  shows "f x (n x) \<Ztypecolon> B x & B' x"
  using assms
  apply -
  apply (rule app_dep_type''[where ?t="f x" and ?u="n x"])
    apply (rule app_dep_type''[where ?t=f and ?u=x])
      apply (rule f_type)
      apply (rule x_type)
      defer
    apply (rule n_type)
    defer
  (*subtyping*)
  apply (rule InterI)
  apply assumption
  apply assumption
  apply assumption
  apply assumption
  done


subsection \<open>Type Simplification and Equivalences\<close>

consts Vec :: "'a \<Rightarrow> 'a type"

schematic_goal
  assumes v_type: "v \<Ztypecolon> Vec n" and v'_type: "v' \<Ztypecolon> Vec m"
  and n_eq_m: "n = m"
  shows "add v v' \<Ztypecolon> Vec m"
  using assms
  apply -
  apply (rule app_type''[where ?t="add v" and ?u="v'"])
    apply (rule app_type''[where ?t=add and ?u=v])
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
  (* done *)

consts pos :: "'a \<Rightarrow> bool"

lemma Nat_if_pos_Int:
  assumes "i \<Ztypecolon> Int"
  and "pos i"
  shows "i \<Ztypecolon> Nat"
  sorry

schematic_goal
  assumes n_type: "n \<Ztypecolon> Nat" and i_type: "i \<Ztypecolon> Int"
  and "pos i"
  shows "add n i \<Ztypecolon> Nat"
  using assms
  apply -
  apply (rule app_type''[where ?t="add n" and ?u="i"])
    apply (rule app_type''[where ?t=add and ?u=n])
      apply (rule add_type)
      apply (rule n_type)
      defer
    apply (rule i_type)
    defer
  (*subtyping*)
  apply assumption
  apply (rule Nat_if_pos_Int)
  apply assumption
  apply assumption
  done

lemma Int_pos_iff_Nat:
  shows "i \<Ztypecolon> Int & type pos \<longleftrightarrow> i \<Ztypecolon> Nat"
  sorry

schematic_goal
  assumes n_type: "n \<Ztypecolon> Nat" and i_type: "i \<Ztypecolon> Int"
  and "pos i"
  shows "add n i \<Ztypecolon> Int & type pos"
  using assms
  apply -
  apply (rule app_type''[where ?t="add n" and ?u="i"])
    apply (rule app_type''[where ?t=add and ?u=n])
      apply (rule add_type)
      apply (rule n_type)
      defer
    apply (rule i_type)
    defer
  (*subtyping*)
  apply (rule InterI)
  apply (rule Int_if_Nat)
  apply assumption
  defer
  apply (rule InterI)
  apply assumption
  apply (rule type_of_typeI)
  apply assumption
  apply (rule type_of_typeI)
  (*left to the user; solvable with integration in simplifier*)
  oops

lemma
  assumes f_type: "f \<Ztypecolon> (x : A) \<Rightarrow> (y : B x) \<Rightarrow> C x y"
  and A_eq_B: "\<And>x. x \<Ztypecolon> A \<Longrightarrow> B x = B' x"
  shows "add f \<Ztypecolon> ((x : A) \<Rightarrow> (y : B' x) \<Rightarrow> C x y) \<Rightarrow> (x : A) \<Rightarrow> (y : B' x) \<Rightarrow> C x y"
  apply (rule app_dep_type'[where ?t="add" and ?u="f"])
    apply (rule add_type)
    apply (rule f_type)
  (*subtyping*)
  apply assumption
  apply (rule Dep_funI)+
    apply (rule app_dep_type''[where ?t="f x" and ?u=y for x y])
      apply (rule app_dep_type''[where ?t="f" and ?u=x for x])
        apply assumption
        apply assumption
        defer
        defer
      apply assumption
      defer
      defer
    apply assumption
  apply (subst A_eq_B)
  apply assumption
  apply assumption
  done


subsection \<open>Implicit Arguments\<close>

consts List :: "'a type \<Rightarrow> 'a type"
consts nil :: "'a type \<Rightarrow> 'a"
consts cons :: "'a type \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"

lemma nil_type: "nil \<Ztypecolon> (A : Any) \<Rightarrow> List A"
  sorry

lemma cons_type: "cons \<Ztypecolon> (A : Any) \<Rightarrow> A \<Rightarrow> List A \<Rightarrow> List A"
  sorry

schematic_goal
  "?A \<Ztypecolon> ?TA \<Longrightarrow> x \<Ztypecolon> ?TX \<Longrightarrow> ?B \<Ztypecolon> ?TB \<Longrightarrow> cons ?A x (nil ?B) \<Ztypecolon> ?T"
  apply (rule app_dep_type''[where ?t="cons A x" and ?u="nil B" for A B])
    apply (rule app_dep_type''[where ?t="cons A" and ?u="x" for A])
      apply (rule app_dep_type''[where ?t="cons" and ?u="A" for A])
        apply (rule cons_type)
        apply assumption
        defer
      apply assumption
      defer
    apply (rule app_dep_type''[where ?t=nil and ?u=B for B])
      apply (rule nil_type)
      apply assumption
      defer
    defer
  (*subtyping*)
  apply (rule AnyI)
  defer
  apply (rule AnyI)
  apply assumption
  apply assumption
  done

schematic_goal
  "?A \<Ztypecolon> ?TA \<Longrightarrow> x \<Ztypecolon> ?TX \<Longrightarrow> ?B \<Ztypecolon> ?TB \<Longrightarrow> cons ?A x (nil ?B) \<Ztypecolon> ?T"
  apply (rule app_dep_type[where ?t="cons A x" and ?u="nil B" for A B])
    apply (rule app_dep_type[where ?t="cons A" and ?u="x" for A])
      apply (rule app_dep_type[where ?t="cons" and ?u="A" for A])
        apply (rule cons_type)
        apply (rule AnyI)
      apply assumption
    apply (rule app_dep_type[where ?t=nil and ?u=B for B])
      (*Problem: when matching `nil ?B : List ?A = nil ?B : ?C ?B`,
        the higher-order unifier picks `?C=\<lambda>x. ?x` and `?B = List ?A`*)
      apply (rule nil_type)
      apply (rule AnyI)
   oops

schematic_goal "?A \<Ztypecolon> ?TA \<Longrightarrow> B \<Ztypecolon> ?TB \<Longrightarrow> nil ?A = B \<Ztypecolon> ?T"
  apply (rule app_dep_type''[where ?t="(=) (nil A)" for A])
    apply (rule app_dep_type''[where ?t="(=)"])
      apply (rule eq_type)
      apply (rule app_dep_type''[where ?t="nil"])
        apply (rule nil_type)
        apply assumption
        defer
      defer
    apply assumption
    defer
  (*subtyping*)
  apply (rule AnyI)
  apply assumption
  apply assumption
  done

experiment
  fixes Element :: "'a \<Rightarrow> 'a type"
  and nat :: "'a"
  and zero :: "'a" ("0")
  and succ :: "'a \<Rightarrow> 'a"
  and add :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  and vec :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  and vnil :: "'a \<Rightarrow> 'a"
  and vcons :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"
  and vappend :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes vec_type: "vec \<Ztypecolon> Any \<Rightarrow> Element nat \<Rightarrow> Any"
  and vnil_type: "vnil \<Ztypecolon> (A : Any) \<Rightarrow> Element (vec A 0)"
  and vcons_type: "vcons \<Ztypecolon> (A : Any) \<Rightarrow> (n : Element nat) \<Rightarrow>
    Element A \<Rightarrow> Element (vec A n) \<Rightarrow> Element (vec A (succ n))"
  and add_type: "add \<Ztypecolon> Element nat \<Rightarrow> Element nat \<Rightarrow> Element nat"
  and succ_type: "succ \<Ztypecolon> Element nat \<Rightarrow> Element nat"
  and zero_type: "0 \<Ztypecolon> Element nat"
  and vappend_type: "vappend \<Ztypecolon> (A : Any) \<Rightarrow> (n : Element nat) \<Rightarrow> (m : Element nat) \<Rightarrow>
    Element (vec A n) \<Rightarrow> Element (vec A m) \<Rightarrow> Element (vec A (add n m))"
  and add_succ_eq_succ_add: "add (succ n) m = succ (add n m)"
begin

text \<open>The base 'a of the vector and the dimensions are completely inferred:\<close>

schematic_goal
  "?A1 \<Ztypecolon> ?TA1 \<Longrightarrow> ?A2 \<Ztypecolon> ?TA2 \<Longrightarrow> ?A3 \<Ztypecolon> ?TA3 \<Longrightarrow> ?A4 \<Ztypecolon> ?TA4 \<Longrightarrow>
  ?n1 \<Ztypecolon> ?Tn1 \<Longrightarrow> ?n2 \<Ztypecolon> ?Tn2 \<Longrightarrow> ?n3 \<Ztypecolon> ?Tn3 \<Longrightarrow> ?n4 \<Ztypecolon> ?Tn4 \<Longrightarrow>
  ?m1 \<Ztypecolon> ?Tm1 \<Longrightarrow> ?m2 \<Ztypecolon> ?Tm2 \<Longrightarrow> ys \<Ztypecolon> ?Tys \<Longrightarrow> x \<Ztypecolon> ?Tx \<Longrightarrow> xs \<Ztypecolon> ?Txs \<Longrightarrow>
  vappend ?A1 ?n1 ?m1 (vcons ?A2 ?n2 x xs) ys = vcons ?A3 ?n3 x (vappend ?A4 ?n4 ?m2 xs ys) \<Ztypecolon> ?T"
  apply (rule app_dep_type''[where ?t="(=) (vappend A1 n1 m1 (vcons A2 n2 x xs) ys)" for A1 n1 m1 A2 n2])
    apply (rule app_dep_type''[where ?t="(=)"])
      apply (rule eq_type)
      apply (rule app_dep_type''[where ?t="vappend A1 n1 m1 (vcons A2 n2 x xs)" for A1 n1 m1 A2 n2])
        apply (rule app_dep_type''[where ?t="vappend A1 n1 m1" for A1 n1 m1])
          apply (rule app_dep_type''[where ?t="vappend A1 n1" for A1 n1])
            apply (rule app_dep_type''[where ?t="vappend A1" for A1])
              apply (rule app_dep_type''[where ?t="vappend"])
                apply (rule vappend_type)
                apply (assumption)
                defer
              (*unify constraints for matching meta variables*)
              apply (tactic \<open>rotate_tac 4 1\<close>, assumption)
              defer
            apply (tactic \<open>rotate_tac 8 1\<close>, assumption)
            defer
          apply (rule app_dep_type''[where ?t="vcons A2 n2 x" for A2 n2])
            apply (rule app_dep_type''[where ?t="vcons A2 n2" for A2 n2])
              apply (rule app_dep_type''[where ?t="vcons A2" for A2])
                apply (rule app_dep_type''[where ?t="vcons"])
                  apply (rule vcons_type)
                  apply (tactic \<open>rotate_tac 1 1\<close>, assumption)
                  defer
                apply (tactic \<open>rotate_tac 5 1\<close>, assumption)
                defer
              apply (tactic \<open>rotate_tac 10 1\<close>, assumption) defer
            apply (tactic \<open>rotate_tac 11 1\<close>, assumption)
            defer
          defer
        apply (tactic \<open>rotate_tac 10 1\<close>, assumption)
        defer
      defer
    apply (rule app_dep_type''[where ?t="vcons A3 n3 x" for A3 n3])
      apply (rule app_dep_type''[where ?t="vcons A3 n3" for A3 n3])
        apply (rule app_dep_type''[where ?t="vcons A3" for A3])
          apply (rule app_dep_type''[where ?t="vcons"])
            apply (rule vcons_type)
            apply (tactic \<open>rotate_tac 2 1\<close>, assumption)
            defer
          apply (tactic \<open>rotate_tac 6 1\<close>, assumption)
          defer
        apply (tactic \<open>rotate_tac 11 1\<close>, assumption)
        defer
      apply (rule app_dep_type''[where ?t="vappend A4 n4 m2 xs" for A4 n4 m2])
        apply (rule app_dep_type''[where ?t="vappend A4 n4 m2" for A4 n4 m2])
          apply (rule app_dep_type''[where ?t="vappend A4 n4" for A4 n4])
            apply (rule app_dep_type''[where ?t="vappend A4" for A4])
              apply (rule app_dep_type''[where ?t="vappend"])
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
  apply (rule AnyI)
  apply (tactic \<open>rotate_tac 4 1\<close>, assumption)
  apply (tactic \<open>rotate_tac 8 1\<close>, assumption)
  apply (rule AnyI)
  apply (tactic \<open>rotate_tac 5 1\<close>, assumption)
  apply (tactic \<open>rotate_tac 11 1\<close>, assumption)
  apply (tactic \<open>rotate_tac 12 1\<close>, assumption)
  apply (tactic \<open>rotate_tac 15 1\<close>, assumption)
  apply (tactic \<open>rotate_tac 10 1\<close>, assumption)
  apply (tactic \<open>rotate_tac 14 1\<close>, assumption)
  apply (rule AnyI)
  apply (tactic \<open>rotate_tac 6 1\<close>, assumption)
  apply (tactic \<open>rotate_tac 11 1\<close>, assumption)
  apply (rule AnyI)
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

schematic_goal "g \<Ztypecolon> ?Tg \<Longrightarrow> ?y1 \<Ztypecolon> ?Ty1 \<Longrightarrow> ?y2 \<Ztypecolon> ?Ty2 \<Longrightarrow> x \<Ztypecolon> ?Tx \<Longrightarrow> xs \<Ztypecolon> ?Txs
  \<Longrightarrow> g (vcons ?y1 ?y2 x xs) \<Ztypecolon> ?T"
  apply (rule app_type[where ?t=g])
    apply assumption
    apply (rule app_dep_type[where ?t="vcons y1 y2 x" for y1 y2])
      apply (rule app_dep_type[where ?t="vcons y1 y2" for y1 y2])
        apply (rule app_dep_type[where ?t="vcons y1" for y1])
          apply (rule app_dep_type[where ?t="vcons"])
            apply (rule vcons_type)
            apply (rule AnyI)
          apply (tactic \<open>rotate_tac 2 1\<close>, assumption)
        apply (tactic \<open>rotate_tac 3 1\<close>, assumption)
      apply (tactic \<open>rotate_tac 4 1\<close>, assumption)
   done

end

experiment
  fixes Id
  and refl
  and J
  and U
  assumes Id_type: "Id \<Ztypecolon> ((A : U) \<Rightarrow> A \<Rightarrow> A \<Rightarrow> U)"
  and refl_type: "refl \<Ztypecolon> ((A : U) \<Rightarrow> (x : A) \<Rightarrow> Id A x x)"
  assumes J_type: "J \<Ztypecolon> ((A : U) \<Rightarrow>
    (C : (x : A) \<Rightarrow> (y: A) \<Rightarrow> (p : Id A x y) \<Rightarrow> U) \<Rightarrow>
    ((x: A) \<Rightarrow> C x x (refl A x)) \<Rightarrow> (a : A) \<Rightarrow> (b : A) \<Rightarrow> (p : Id A a b) \<Rightarrow> C a b p)"
begin

text \<open>The proof term for reflexivity of equality:\<close>

schematic_goal
  "?A1 \<Ztypecolon> ?TA1 \<Longrightarrow> ?C1 \<Ztypecolon> ?TC1 \<Longrightarrow> ?A2 \<Ztypecolon> ?TA2 \<Longrightarrow> a \<Ztypecolon> ?Ta \<Longrightarrow> b \<Ztypecolon> ?Tb \<Longrightarrow>
    p \<Ztypecolon> ?Tp \<Longrightarrow> J ?A1 ?C1 (refl ?A2) a b p \<Ztypecolon> ?T"
  apply (rule app_dep_type[where ?t="J A1 C1 (\<lambda>x. refl A2 x) a b" for A1 C1 A2])
    apply (rule app_dep_type[where ?t="J A1 C1 (\<lambda>x. refl A2 x) a" for A1 C1 A2])
      apply (rule app_dep_type[where ?t="J A1 C1 (\<lambda>x. refl A2 x)" for A1 C1 A2])
        apply (rule app_dep_type[where ?t="J A1 C1" for A1 C1])
          apply (rule app_dep_type[where ?t="J A1" for A1])
            apply (rule app_dep_type[where ?t="J"])
              apply (rule J_type)
              apply assumption
            apply (tactic \<open>rotate_tac 1 1\<close>, assumption)
          apply (rule Dep_funI)
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


(*
Notes:
1. Priority of rules
2. Priority of assumptions
3. Specification of unification algorithm for rules?
4. Postponing zero-priority rules (e.g. subtype conditions, additional assumptions)
*)

end