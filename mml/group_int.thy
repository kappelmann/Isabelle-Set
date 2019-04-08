theory group_int
  imports group_2 binop_2
begin

definition Zgroup ("\<int>-group") where
  "\<int>-group \<equiv>
     [#carrier\<mapsto>INT ; multF\<mapsto> addint#]"

mtheorem 
 "cluster \<int>-group \<rightarrow> strict(multMagma)" unfolding Zgroup_def by mty auto

mtheorem
  "cluster \<rightarrow> integer for Element-of-struct \<int>-group"
proof(standard,standard)
  have "[carrier,INT] in \<int>-group" unfolding Zgroup_def using  aggr by auto
  hence E1: "the carrier of \<int>-group = INT" using the_selector_of_1[of "\<int>-group" "carrier" INT] aggr Zgroup_def by mty auto 
  fix it assume [ty]: "it be Element-of-struct \<int>-group"
  hence "it in INT" using E1 Element(7) by mty auto
  then show "it is integer" using int_1_def_2 by auto
qed mauto

mtheorem
  "cluster \<rightarrow> Element-of-struct \<int>-group for Integer"
proof(standard,standard)
  have "[carrier,INT] in \<int>-group" unfolding Zgroup_def using  aggr by auto
  hence E1: "the carrier of \<int>-group = INT" using the_selector_of_1[of "\<int>-group" "carrier" INT] aggr Zgroup_def by mty auto 
  fix x assume "x be Integer"
  hence "x in the carrier of \<int>-group" using E1 int_1_def_2 by auto
  then show "x is Element-of-struct \<int>-group" using Element(6) by auto
qed mauto

reserve i1,i2 for Integer

mtheorem g_int_th_1:
  "i1 +\<int> i2 = i1 \<otimes>\<^sub>\<int>-group i2"
proof-
  have "[multF,addint] in \<int>-group" unfolding Zgroup_def using aggr by auto
  hence E1: "the multF of \<int>-group = addint" using the_selector_of_1[of "\<int>-group" multF addint] aggr Zgroup_def by mty auto 
  hence "i1 \<otimes>\<^sub>\<int>-group i2 = addint.\<lparr> i1,i2 \<rparr>" using algstr_0_def_18[of "\<int>-group" i1 i2,simplified] by mty auto
  then show "i1 +\<int> i2 = i1 \<otimes>\<^sub>\<int>-group i2" using binop_2_def_20 by auto
qed

mtheorem 
  " cluster \<int>-group \<rightarrow> Group-like \<bar> associative \<bar>  non empty-struct"
proof(standard,standard,standard)
  have [ty]: "{} is Element-of-struct \<int>-group" by mty auto
  show "\<int>-group is Group-like"
  proof(standard,simp,rule bexI[of _ "{}"],intro ballI conjI)
    fix h assume [ty]: "h be Element-of-struct \<int>-group"
    have "h \<otimes>\<^sub>\<int>-group {} = h +\<int> {}" "{} \<otimes>\<^sub>\<int>-group h = {} +\<int> h" using g_int_th_1  by mty auto
    then show "h \<otimes>\<^sub>\<int>-group {} = h" "{} \<otimes>\<^sub>\<int>-group h = h" using int_1_th_2[of h] by mty auto
    obtain g where [ty]: "g be Integer" and
       A1: "g  +\<int> h = {}" "h +\<int> g = {}" using int_1_th_4[of h] by mty auto
    show " ex g be Element-of-struct \<int>-group st h \<otimes>\<^sub>\<int>-group g = {} \<and> g \<otimes>\<^sub>\<int>-group h = {}"
    proof (rule bexI[of _ g],mauto)
      have "g \<otimes>\<^sub>\<int>-group h = g +\<int> h" "h \<otimes>\<^sub>\<int>-group g = h +\<int> g" using g_int_th_1  by mty auto
      then show "h \<otimes>\<^sub>\<int>-group g = {}" "g \<otimes>\<^sub>\<int>-group h = {}" using A1 by auto 
    qed
  qed mauto
  show "\<int>-group is associative"
  proof(standard,mauto)
    fix x y z assume [ty]: "x is Element-of-struct \<int>-group" 
      "y is Element-of-struct \<int>-group" "z is Element-of-struct \<int>-group"
    have "(x \<otimes>\<^sub>\<int>-group y) \<otimes>\<^sub>\<int>-group z = (x +\<int> y) +\<int> z" using g_int_th_1  by mty auto
    also have "\<dots>=x +\<int> (y +\<int> z)" using int_1_th_9 by mty auto 
    also have "\<dots>=x \<otimes>\<^sub>\<int>-group (y \<otimes>\<^sub>\<int>-group z)" using g_int_th_1  by mty auto
    finally show "(x \<otimes>\<^sub>\<int>-group y) \<otimes>\<^sub>\<int>-group z=x \<otimes>\<^sub>\<int>-group (y \<otimes>\<^sub>\<int>-group z)" by auto
  qed
  show "\<int>-group is non empty-struct"
  proof(standard,simp)
    have "[carrier,INT] in \<int>-group" unfolding Zgroup_def using  aggr by auto
    hence "the carrier of \<int>-group = INT" using the_selector_of_1[of "\<int>-group" "carrier" INT] aggr Zgroup_def by mty auto 
    hence "{} in the carrier of \<int>-group" using int_1_def_2[of "{}"] by mty auto
    then show "not the carrier of \<int>-group is empty" using xboole_0_def_1 by mty auto
  qed
qed

mtheorem g_int_th_2:
   "1.\<^sub>\<int>-group = {}"
proof-
  have "for h being Element-of-struct \<int>-group holds
         h \<otimes>\<^sub>\<int>-group {} = h \<and> {} \<otimes>\<^sub>\<int>-group h = h"
  proof
 fix h assume [ty]: "h be Element-of-struct \<int>-group"
    have "h \<otimes>\<^sub>\<int>-group {} = h +\<int> {}" "{} \<otimes>\<^sub>\<int>-group h = {} +\<int> h" using g_int_th_1  by mty auto
    then show "h \<otimes>\<^sub>\<int>-group {} = h &{} \<otimes>\<^sub>\<int>-group h = h" using int_1_th_2[of h] by mty auto
  qed mauto
  then show "1.\<^sub>\<int>-group = {}" 
    using group_1_def_4_uniq[of "\<int>-group" "{}"] by mty auto
qed


mtheorem g_int_th_3:
  "i1\<^sup>-\<^sup>1\<^sub>\<int>-group = -\<int> i1"
proof-
  have "i1 \<otimes>\<^sub>\<int>-group (-\<int> i1) = i1 +\<int> (-\<int> i1)" using g_int_th_1 by auto
  also have "\<dots>= {}" using int_1_def_4[of i1] int_1_th_5 by mty auto
  finally have "i1 \<otimes>\<^sub>\<int>-group (-\<int> i1) = 1.\<^sub>\<int>-group" using g_int_th_2 by auto
  hence "i1 \<otimes>\<^sub>\<int>-group (-\<int> i1) = 1.\<^sub>\<int>-group"
       "(-\<int> i1) \<otimes>\<^sub>\<int>-group i1 = 1.\<^sub>\<int>-group" using int_1_th_5[of i1 "-\<int> i1"] g_int_th_1 by mty auto
  thus ?thesis using group_1_def_5_uniq[of "\<int>-group" i1 "-\<int> i1"] by simp
qed

end