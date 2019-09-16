theory z2
imports algstr_0
begin

definition A: "ZERO \<equiv> {}"
definition B: "ONE \<equiv> {ZERO}"

lemma [simp]: "ZERO \<noteq> ONE" using tarski_def_1[of ONE ZERO] prefix_in_irreflexive all_set B A by auto
lemma [simp]: "[ZERO,ZERO]\<noteq>[ZERO,ONE]" "[ZERO,ZERO]\<noteq>[ONE,ZERO]" "[ZERO,ZERO]\<noteq>[ONE,ONE]"
      "[ZERO,ONE]\<noteq>[ONE,ZERO]" "[ZERO,ONE]\<noteq>[ONE,ONE]" "[ONE,ZERO]\<noteq>[ONE,ONE]"
  using xtuple_0_th_1[of ZERO ZERO ZERO ONE] xtuple_0_th_1[of ZERO ZERO ONE ZERO] xtuple_0_th_1[of ZERO ZERO ONE ONE]
        xtuple_0_th_1[of ZERO ONE ONE ZERO] xtuple_0_th_1[of ZERO ONE ONE ONE] xtuple_0_th_1[of ONE ZERO ONE ONE]by simp+

theorem DomZ2: "{[ZERO,ZERO]}\<union>{[ZERO,ONE]}\<union>{[ONE,ZERO]}\<union>{[ONE,ONE]} = [:{ZERO,ONE},{ZERO,ONE}:]"
  proof(unfold xboole_0_def_10[OF all_set all_set],rule conjI)
    show "{[ZERO,ZERO]}\<union>{[ZERO,ONE]}\<union>{[ONE,ZERO]}\<union>{[ONE,ONE]} \<subseteq> [:{ZERO,ONE},{ZERO,ONE}:]"
    proof(standard,auto)
      fix xy assume A: "xy in {[ZERO,ZERO]}\<union>{[ZERO,ONE]}\<union>{[ONE,ZERO]}\<union>{[ONE,ONE]}"
      hence A:"xy=[ZERO,ZERO] \<or> xy=[ZERO,ONE] \<or> xy = [ONE,ZERO] \<or> xy=[ONE,ONE]" using xboole_0_def_3 tarski_def_1 by mauto
      have B: "ZERO in {ZERO,ONE} \<and> ONE in {ZERO,ONE}" using tarski_def_2 by auto
      thus "xy in [:{ZERO,ONE},{ZERO,ONE}:]" using xboole_0_def_3 A zfmisc_1_def_2 by mty auto
   qed mauto
    show "[:{ZERO,ONE},{ZERO,ONE}:] \<subseteq> {[ZERO,ZERO]}\<union>{[ZERO,ONE]}\<union>{[ONE,ZERO]}\<union>{[ONE,ONE]} "
    proof(standard,auto)
      fix xy assume "xy in [:{ZERO,ONE},{ZERO,ONE}:]"
      then obtain x y where
        A1: "xy=[x,y]" "x in {ZERO,ONE} \<and> y in {ZERO,ONE}" using zfmisc_1_def_2 by mty auto
      thus "xy in {[ZERO,ZERO]}\<union>{[ZERO,ONE]}\<union>{[ONE,ZERO]}\<union>{[ONE,ONE]}" using tarski_def_1 tarski_def_2 xboole_0_def_3 by mty auto
    qed mauto
  qed

theorem Rng_1:
  "rng {[s,D]}={D}"
proof-
  have "{[s,D]} be Relation" using relat_1_cl_7 by mauto
  thus ?thesis using relat_1_th_3[of D s "{[s,D]}"] by auto
qed

theorem Rng_2:
  "rng ({[s1,D1]} \<union> {[s2,D2]}) = {D1}\<union>{D2}"
proof-
  have A1:"{[s1,D1]} be Relation \<and> {[s2,D2]} be Relation" using relat_1_cl_7 by mauto
  have "({[s1,D1]} \<union> {[s2,D2]}) be Relation" using relat_1_cl_5 A1 by mauto
  hence "rng ({[s1,D1]} \<union> {[s2,D2]}) = (rng {[s1,D1]}) \<union> (rng {[s2,D2]})" using xtuple_th_24 relat_1_def_1E by mauto
  thus ?thesis using Rng_1 by auto
qed

theorem Rng_3:
  "rng ({[s1,D1]} \<union> {[s2,D2]}\<union>{[s3,D3]}) = {D1}\<union>{D2}\<union>{D3}"
proof-
(*  have A2:"{[s1,D1]} be Relation \<and> {[s2,D2]} be Relation" using relat_1_cl_7 by mauto
    have A3: "({[s1,D1]} \<union> {[s2,D2]}) be Relation \<and>  {[s3,D3]} be Relation" using relat_1_cl_7 relat_1_cl_5 A2 by mauto
  have A4: "({[s1,D1]} \<union> {[s2,D2]}\<union>{[s3,D3]}) be Relation" using relat_1_cl_7 relat_1_cl_5 A3 by mauto
  hence "({[s1,D1]} \<union> {[s2,D2]}\<union>{[s3,D3]}) be Relation"
    using relat_1_cl_5[of "{[s1,D1]} \<union> {[s2,D2]}" "{[s3,D3]}"] by simp*)
  have "rng ({[s1,D1]} \<union> {[s2,D2]}\<union>{[s3,D3]}) = (rng ({[s1,D1]}\<union>{[s2,D2]})) \<union> (rng {[s3,D3]})"
    using xtuple_th_24 by mty auto
  thus ?thesis using Rng_1 Rng_2 by auto
qed

theorem Rng_4:
  "rng ({[s1,D1]} \<union> {[s2,D2]}\<union>{[s3,D3]}\<union>{[s4,D4]}) = {D1}\<union>{D2}\<union>{D3}\<union>{D4}"
proof-
(*  have A2:"{[s1,D1]} be Relation \<and> {[s2,D2]} be Relation" using relat_1_cl_7 by mauto
  have A3: "({[s1,D1]} \<union> {[s2,D2]}) be Relation \<and>  {[s3,D3]} be Relation" using relat_1_cl_7 relat_1_cl_5 A2 by mauto
   have A4: "({[s1,D1]} \<union> {[s2,D2]}\<union>{[s3,D3]}) be Relation \<and>  {[s4,D4]} be Relation " using relat_1_cl_7 relat_1_cl_5 A3 by mauto
  have A5: "({[s1,D1]} \<union> {[s2,D2]}\<union>{[s3,D3]}\<union>{[s4,D4]}) be Relation " using relat_1_cl_7 relat_1_cl_5 A4 by mauto*)
  have "rng ({[s1,D1]} \<union> {[s2,D2]}\<union>{[s3,D3]}\<union>{[s4,D4]}) = (rng ({[s1,D1]}\<union>{[s2,D2]}\<union>{[s3,D3]})) \<union> (rng {[s4,D4]})"
    using xtuple_th_24 relat_1_def_1I by mty auto
  thus ?thesis using Rng_1 Rng_3 by auto
qed

definition addZ2 ("addZ2") where
  "addZ2 \<equiv>
     {[[ZERO,ZERO],ZERO]}\<union>{[[ZERO,ONE],ONE]}\<union>{[[ONE,ZERO],ONE]}\<union>{[[ONE,ONE],ZERO]}"

mtheorem
  "cluster addZ2 \<rightarrow> BinOp-of {ZERO,ONE}"
proof
  have T1:"addZ2 be Function" unfolding addZ2_def using Struct_4[of "[ZERO,ZERO]" ] Struct_def sel_t_def aggr_def by auto
  have T2:"dom addZ2 = [:{ZERO,ONE},{ZERO,ONE}:]" unfolding addZ2_def using DomZ2 Dom_4 sel_t_def aggr_def by auto
  have "rng addZ2 = {ZERO}\<union>{ONE}\<union>{ONE}\<union>{ZERO}" unfolding addZ2_def using Rng_4 by auto
  hence "rng addZ2 = {ZERO,ONE}" using xboole_0_def_3 tarski_def_1 tarski_def_2 by (intro tarski_0_2a) mauto
  thus "addZ2 be BinOp-of {ZERO,ONE}" using funct_2_th_2[OF T1] T2 by auto
qed

definition multZ2 ("multZ2") where
  "multZ2 \<equiv>
     {[[ZERO,ZERO],ZERO]}\<union>{[[ZERO,ONE],ZERO]}\<union>{[[ONE,ZERO],ZERO]}\<union>{[[ONE,ONE],ONE]}"

mtheorem 
  "cluster multZ2 \<rightarrow> BinOp-of {ZERO,ONE}"
proof
  have T1:"multZ2 be Function" unfolding multZ2_def using Struct_4[of "[ZERO,ZERO]" ] Struct_def aggr_def sel_t_def by auto
  have T2:"dom multZ2 = [:{ZERO,ONE},{ZERO,ONE}:]"  unfolding multZ2_def using DomZ2 Dom_4 aggr_def sel_t_def by auto
  have "rng multZ2 = {ZERO,ONE}"  unfolding multZ2_def using Rng_4 xboole_0_def_3 tarski_def_1 tarski_def_2 by (intro tarski_0_2a,simp_all) mauto
  thus "multZ2 be BinOp-of {ZERO,ONE}" using funct_2_th_2[OF T1] T2 by simp
qed

abbreviation Z ("Z") where
  "Z \<equiv>
     [#carrier\<mapsto>{ZERO,ONE} ; addF\<mapsto> addZ2;ZeroF\<mapsto>ZERO;multF\<mapsto>multZ2;OneF\<mapsto>ONE#]"

mtheorem 
 "cluster Z \<rightarrow> strict(doubleLoopStr)"
proof
  have [ty]: "ZERO be Element-of {ZERO,ONE}" "ONE be Element-of {ZERO,ONE}" using Element_of_rule3 tarski_def_2 by mauto
  thus T1: "Z be strict(doubleLoopStr)" by mauto
qed

theorem Z2d:
  shows "ZERO be Element-of-struct Z"
        "ONE be Element-of-struct Z"
        "x be Element-of-struct Z \<Longrightarrow> x = ONE \<or> x = ZERO"
        "0\<^sub>Z = ZERO" "1\<^sub>Z = ONE"
        "ZERO\<oplus>\<^sub>Z ZERO = ZERO" "ZERO\<oplus>\<^sub>Z ONE = ONE" "ONE\<oplus>\<^sub>Z ZERO = ONE" "ONE\<oplus>\<^sub>Z ONE = ZERO"
        "ZERO\<otimes>\<^sub>Z ZERO = ZERO" "ZERO\<otimes>\<^sub>Z ONE = ZERO" "ONE\<otimes>\<^sub>Z ZERO = ZERO" "ONE\<otimes>\<^sub>Z ONE = ONE"
        "the carrier of Z={ZERO,ONE}"
proof-
  have [ty]:"Z be doubleLoopStr" by mauto
  have T0: "Z be doubleLoopStr" "Z be Struct" "Z be 1-sorted" "Z be ZeroStr" "Z be OneStr" "Z be addMagma" "Z be multMagma"
        by auto
  have T1: "the carrier of Z={ZERO,ONE}" "the ZeroF of Z=ZERO" "the OneF of Z=ONE" "the multF of Z=multZ2" "the addF of Z=addZ2" using
     the_selector_of_1[of Z carrier "{ZERO,ONE}"] the_selector_of_1[of Z ZeroF ZERO]
     the_selector_of_1[of Z OneF ONE] the_selector_of_1[of Z multF multZ2]
     the_selector_of_1[of Z addF addZ2] aggr by auto
  thus T2[ty]: "ZERO be Element-of-struct Z" "ONE be Element-of-struct Z"
    using Element(6) tarski_def_2 by mty auto (* CK: slow "mty" *)
  have[ty]: "the carrier of Z is non empty" using T1(1) tarski_def_2 xboole_0_def_1 by mauto
  show "x be Element-of-struct Z \<Longrightarrow> x = ONE \<or> x = ZERO"
  proof-
    assume A1: "x be Element-of-struct Z"
    have "x in the carrier of Z" using A1 Element(7)[of "the carrier of Z" x] by auto
    thus ?thesis using T1(1) tarski_def_2 by auto
  qed
  show "0\<^sub>Z = ZERO" "1\<^sub>Z = ONE" using struct_0_def_6 struct_0_def_7 T1(2-3) by auto
  have A0[ty]:"addZ2 be Function" using relset_1_cl_1[of "[:{ZERO,ONE},{ZERO,ONE}:]" "{ZERO,ONE}"]  by mty auto
          (* !?! CK !?!*)
  let ?A =" {[[ZERO , ZERO] , ZERO]} \<union> {[[ZERO , ONE] , ONE]} \<union> {[[ONE , ZERO] , ONE]} \<union> {[[ONE , ONE] , ZERO]}"
  have A1: "addZ2 = ?A" using addZ2_def by simp
  have "[[ZERO , ZERO] , ZERO] in ?A" using tarski_def_1 string by auto
  hence "[[ZERO , ZERO] , ZERO] in addZ2" using A1 by auto+
  hence "addZ2. [ZERO , ZERO] = ZERO" using funct_1_th_1[OF A0] by auto
  thus "ZERO\<oplus>\<^sub>Z ZERO = ZERO" using algstr_0_def_1[of Z ZERO ZERO] binop_0_def_1[of addZ2] T1(5) by auto

  have "[[ZERO , ONE] , ONE] in ?A" using tarski_def_1 string by auto
  hence "[[ZERO , ONE] , ONE] in addZ2" using A1 by auto+
  hence "addZ2. [ZERO , ONE] = ONE" using funct_1_th_1[OF A0] by auto
  thus "ZERO\<oplus>\<^sub>Z ONE = ONE" using algstr_0_def_1[of Z ZERO ONE] binop_0_def_1[of addZ2] T1(5) by auto
  have "[[ONE , ZERO] , ONE] in ?A" using tarski_def_1 string by auto
  hence "[[ONE , ZERO] , ONE] in addZ2" using A1 by auto+
  hence "addZ2. [ONE , ZERO] = ONE" using funct_1_th_1[OF A0] by auto
  thus "ONE \<oplus>\<^sub>Z ZERO = ONE" using algstr_0_def_1[of Z ONE ZERO] binop_0_def_1[of addZ2] T1(5) by auto
  have "[[ONE , ONE] , ZERO] in ?A" using tarski_def_1 string by auto
  hence "[[ONE , ONE] , ZERO] in addZ2" using A1 by auto+
  hence "addZ2. [ONE , ONE] = ZERO" using funct_1_th_1[OF A0] by auto
  thus "ONE \<oplus>\<^sub>Z ONE = ZERO" using algstr_0_def_1[of Z ONE ONE] binop_0_def_1[of addZ2] T1(5) by auto
  have A0[ty]:"multZ2 be Function" using relset_1_cl_1[of "[:{ZERO,ONE},{ZERO,ONE}:]" "{ZERO,ONE}"]  by mty auto
          (* !?! CK !?!*)
  let ?M =" {[[ZERO , ZERO] , ZERO]} \<union> {[[ZERO , ONE] , ZERO]} \<union> {[[ONE , ZERO] , ZERO]} \<union> {[[ONE , ONE] , ONE]}"
  have A1: "multZ2 = ?M" using multZ2_def by simp
  have "[[ZERO , ZERO] , ZERO] in ?M" using tarski_def_1 string by auto
  hence "[[ZERO , ZERO] , ZERO] in multZ2" using A1 by auto+
  hence "multZ2. [ZERO , ZERO] = ZERO" using funct_1_th_1[OF A0] by auto
  thus "ZERO\<otimes>\<^sub>Z ZERO = ZERO" using algstr_0_def_18[of Z ZERO ZERO] binop_0_def_1[of multZ2] T1(4) by auto
  have "[[ZERO , ONE] , ZERO] in ?M" using tarski_def_1 string by auto
  hence "[[ZERO , ONE] , ZERO] in multZ2" using A1 by auto+
  hence "multZ2. [ZERO , ONE] = ZERO" using funct_1_th_1[OF A0] by auto
  thus "ZERO\<otimes>\<^sub>Z ONE = ZERO" using algstr_0_def_18[of Z ZERO ONE] binop_0_def_1[of multZ2] T1(4) by auto
  have "[[ONE , ZERO] , ZERO] in ?M" using tarski_def_1 string by auto
  hence "[[ONE , ZERO] , ZERO] in multZ2" using A1 by auto+
  hence "multZ2. [ONE , ZERO] = ZERO" using funct_1_th_1[OF A0] by auto
  thus "ONE \<otimes>\<^sub>Z ZERO = ZERO" using algstr_0_def_18[of Z ONE ZERO] binop_0_def_1[of multZ2] T1(4) by auto
  have "[[ONE , ONE] , ONE] in ?M" using tarski_def_1 string by auto
  hence "[[ONE , ONE] , ONE] in multZ2" using A1 by auto+
  hence "multZ2. [ONE , ONE] = ONE" using funct_1_th_1[OF A0] by auto
  thus "ONE \<otimes>\<^sub>Z ONE = ONE" using algstr_0_def_18[of Z ONE ONE] binop_0_def_1[of multZ2] T1(4) by auto
  show "the carrier of Z={ZERO,ONE}" using T1(1) by auto
qed

end
