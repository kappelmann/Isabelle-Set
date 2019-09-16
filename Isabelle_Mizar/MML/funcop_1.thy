theory funcop_1
imports funct_1
begin

mdef funcop_1_def_2 (infix "\<midarrow>>" 90) where
  mlet "X be set", "y be object"
  "func X \<midarrow>> y \<rightarrow> set equals [:X,{y}:]"
proof -
  show "[:X,{y}:] be set" by mauto
qed

mtheorem funcop_1_cl_1:
  mlet "X be set", "y be object"
   "cluster X \<midarrow>>y \<rightarrow> Function_like \<bar>Relation_like"
proof(standard)
  have A[ty]:"[:X,{y}:] be Subset-of [:X,{y}:]" using Subset_of_rule tarski_def_3 by mauto
  have "for a,b,c be object st [a,b] in [:X,{y}:] \<and> [a,c] in [:X,{y}:] holds b=c"
  proof(intro ballI impI)
    fix a b c assume " [a,b] in [:X,{y}:] \<and> [a,c] in [:X,{y}:] "
    hence "b in {y}" "c in {y}" using zfmisc_1_th_87 by mauto
    thus "b=c" using tarski_def_1 by auto
  qed simp_all
  hence A: "[:X,{y}:] is Function_like" using funct_1_def_1 by mauto
  thus "(X \<midarrow>>y) is Function_like \<bar> Relation_like" using A funcop_1_def_2[of X y] by mauto
qed

reserve A for set

mtheorem funcop_1_th_7:
  "x in A \<longrightarrow> (A \<midarrow>> y).x = y"
proof
  have Z:"y in {y}" using tarski_def_1 by auto
  have T0:"(A \<midarrow>> y) be Function" by mauto
  assume "x in A"
  hence "[x,y] in [:A,{y}:]" using Z zfmisc_1_th_87 by mauto
  hence "[x,y] in A \<midarrow>> y" using funcop_1_def_2 by mauto
  thus "(A \<midarrow>> y).x = y" using funct_1_th_1[OF T0] by auto
qed

mtheorem funcop_1_th_13:
  "dom (A \<midarrow>> y) = A \<and> rng (A \<midarrow>>y) c= {y}"
proof
  have W0[ty]:"[:A,{y}:] be Subset-of [:A,{y}:]" using tarski_def_3 Subset_of_rule by mauto
  have W2: "[:A,{y}:] is A-defined \<bar> {y}-valued" by mauto
  have W3: "[:A,{y}:] = A \<midarrow>>y" using funcop_1_def_2 by mauto
  have A1: "dom [:A,{y}:] c= A" using relat_1_def_18 by mauto
  have "A c= dom (A \<midarrow>>y)"
  proof(standard,auto)
    have Z:"y in {y}" using tarski_def_1 by auto
    fix x assume "x in A"
    hence "[x,y] in [:A,{y}:]" using Z zfmisc_1_th_87 by mauto
    thus "x in dom (A \<midarrow>>y)" using W3 xtuple_0_def_12 by mauto
  qed mauto
  thus "dom (A \<midarrow>>y) = A" using A1 xboole_0_def_10 W3 by mauto
  show "rng (A \<midarrow>>y) c= {y}" using W3 relat_1_def_19[THEN iffD1,simplified,rule_format] by mauto
qed

mdef funcop_1_def_9 (infix ".\<midarrow>>" 300) where
  mlet "x be object", "y be object"
  "func x .\<midarrow>> y \<rightarrow> set equals {x}\<midarrow>> y"
  by mauto

mtheorem funcop_1_cl:
  mlet "x be object", "y be object"
  "cluster x .\<midarrow>>y \<rightarrow> Function_like \<bar>Relation_like"
proof
  have "x .\<midarrow>> y = {x}\<midarrow>> y" using funcop_1_def_9 by auto
  thus "x .\<midarrow>> y is Function_like \<bar>Relation_like" by mauto
qed

end
