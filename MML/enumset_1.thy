theory enumset_1
imports xboole_0
begin

mdef enumset1_def_1("{_, _, _}") where
  mlet "x1 be object", "x2 be object", "x3 be object"
  "func {x1, x2, x3} \<rightarrow> set means \<lambda>it. (for x being object holds x in it \<longleftrightarrow> (x = x1 \<or> x = x2 \<or> x = x3))"
proof
  auto[1]
  have "for x being object holds x in {x1,x2}\<union>{x3} \<longleftrightarrow> (x = x1 \<or> x = x2 \<or> x = x3)"
    using tarski_def_1 tarski_def_2 xboole_0_def_3[of "{x1, x2}" "{x3}"] by infer_auto
    thus "ex X be set st for x being object holds x in X \<longleftrightarrow> (x = x1 \<or> x = x2 \<or> x = x3)" using bexI[of _ "{x1,x2}\<union>{x3}"] by infer_auto
next
  fix IT1 IT2
  assume [ty]: "IT1 be set" and A1: "for x being object holds (x in IT1 \<longleftrightarrow> (x = x1 \<or> x = x2 \<or> x = x3))"
          and [ty]:"IT2 be set" and A2: "for x being object holds (x in IT2 \<longleftrightarrow> (x = x1 \<or> x = x2 \<or> x = x3))"
  {
    fix x
    assume "x be object"
    have "x in IT1 \<longleftrightarrow> (x = x1 \<or> x = x2 \<or> x = x3)" using A1 by auto
    hence "x in IT1 \<longleftrightarrow> x in IT2" using A2 by auto
  }
  thus "IT1 = IT2" using A1 A2 by (intro tarski_th_2) infer_auto
qed

mdef enumset1_def_2("{_, _, _, _}") where
  mlet "x1 be object","x2 be object", "x3 be object","x4 be object"
  "func {x1, x2, x3, x4} \<rightarrow> set means \<lambda>it. (for x being object holds x in it \<longleftrightarrow> (x = x1 \<or> x = x2 \<or> x = x3 \<or> x = x4))"
proof -
  have "for x being object holds x in {x1,x2}\<union>{x3,x4} \<longleftrightarrow> (x = x1 \<or> x = x2 \<or> x = x3 \<or> x=x4)"
      using xboole_0_def_3[of "{x1, x2}" "{x3, x4}"] tarski_def_2 by infer_auto
    thus "ex X be set st for x being object holds x in X \<longleftrightarrow> (x = x1 \<or> x = x2 \<or> x = x3 \<or> x=x4)" using all_set[of "{x1,x2}\<union>{x3,x4}"]
      using bexI by auto
next
  fix IT1 IT2
  assume [ty]: "IT1 be set" and A1: "for x being object holds (x in IT1 \<longleftrightarrow> (x = x1 \<or> x = x2 \<or> x = x3 \<or> x=x4))"
         and
         [ty]: "IT2 be set" and A2: "for x being object holds (x in IT2 \<longleftrightarrow> (x = x1 \<or> x = x2 \<or> x = x3 \<or> x=x4))"
  {
    fix x
    assume Z1: "x be object"
    have "x in IT1 \<longleftrightarrow> (x = x1 \<or> x = x2 \<or> x = x3 \<or> x=x4)" using A1 by auto
    hence "x in IT1 \<longleftrightarrow> x in IT2" using A2 by auto
  }
  thus "IT1 = IT2" using A1 A2 by (intro tarski_th_2) infer_auto
qed infer_auto


reserve x1 for object

mtheorem enumset1_th_29:
  "{ x1,x1 } = { x1 }"
proof-
  have A1: "x1 be set" using tarski_0_1 by simp
  {
    fix x
    have "x in { x1,x1 } \<longleftrightarrow> x = x1" using tarski_def_2 by auto
    hence "x in { x1,x1 } \<longleftrightarrow> x in { x1 }" using tarski_def_1 by auto
  }
  thus "{ x1,x1 } = { x1 }" by (intro tarski_th_2) infer_auto
qed

end
