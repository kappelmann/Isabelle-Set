theory rlvect_1
imports algstr_0
begin

mdef rlvect_1_def_2 ("Abelian")where
   "attr Abelian for addMagma means (\<lambda> M. (for v,w be Element-of-struct M holds v \<oplus>\<^sub>M w = w \<oplus>\<^sub>M v))"..

mdef rlvect_1_def_3 ("add-associative")where
   "attr add-associative for addMagma means (\<lambda> M. (for u,v,w be Element-of-struct M holds (u \<oplus>\<^sub>M v) \<oplus>\<^sub>M w = u \<oplus>\<^sub>M (v \<oplus>\<^sub>M w)))"..

mdef rlvect_1_def_4 ("right-zeroed")where
   "attr right-zeroed for addLoopStr means (\<lambda> M.  (for v be Element-of-struct M holds v \<oplus>\<^sub>M 0\<^sub>M = v))"..

mtheorem rlvect_cl_1:
   "cluster Trivial-addLoopStr \<rightarrow> add-associative\<bar>right-zeroed"
proof(standard,auto)
  let ?T = "Trivial-addLoopStr"
  have [ty]:"?T be addLoopStr" by mauto
  show "?T be add-associative"
  proof(intro rlvect_1_def_3I ballI)
    fix u v w assume [ty]: "u be Element-of-struct ?T"  "v be Element-of-struct ?T" "w be Element-of-struct ?T"
    show "(u \<oplus>\<^sub>?T v) \<oplus>\<^sub>?T w = u \<oplus>\<^sub>?T (v \<oplus>\<^sub>?T w)" using  struct_0_def_10E[THEN bspec,THEN bspec,of ?T "(u \<oplus>\<^sub>?T v) \<oplus>\<^sub>?T w" "u \<oplus>\<^sub>?T (v \<oplus>\<^sub>?T w)"] 
        by mty auto
  qed simp_all
  show "?T be right-zeroed"
  proof(intro rlvect_1_def_4I ballI)
    fix u v w assume [ty]: "v be Element-of-struct ?T"
    show "v \<oplus>\<^sub>?T 0\<^sub>?T = v" 
       using struct_0_def_10E[THEN bspec,THEN bspec,of ?T "v \<oplus>\<^sub>?T 0\<^sub>?T " " v" ] 
        by mty auto
  qed simp_all
qed

mtheorem rlvect_cl_2:
   "cluster non empty-struct\<bar>right-complementable\<bar>add-associative\<bar>right-zeroed for addLoopStr"
proof (standard,standard)
  show "Trivial-addLoopStr is non empty-struct\<bar>right-complementable\<bar>add-associative\<bar>right-zeroed\<bar> addLoopStr"
     using algstr_0_cl_14[of "{{}}"] by mauto
qed

mtheorem rlvect_cl_3:
   "cluster add-associative\<bar>right-zeroed\<bar>right-complementable for addLoopStr"
proof(standard,standard)
  show "Trivial-addLoopStr is add-associative\<bar>right-zeroed\<bar>right-complementable\<bar> addLoopStr" by mauto
qed

theorem rlvect_1_lm_1[THEN bspec,THEN bspec,THEN bspec,THEN mp,simplified,rule_format]:
  "for V be non empty-struct\<bar>right-complementable\<bar>add-associative\<bar>right-zeroed\<bar>addLoopStr,
       v, w be Element-of-struct V st v \<oplus>\<^sub>V w = 0\<^sub>V holds
       w \<oplus>\<^sub>V v = 0\<^sub>V"
proof(intro ballI impI)
  fix V assume T0[ty]:"V be non empty-struct\<bar>right-complementable\<bar>add-associative\<bar>right-zeroed\<bar>addLoopStr"
  fix v w assume [ty]:  "v be Element-of-struct V" "w be Element-of-struct V"
  assume A1: "v \<oplus>\<^sub>V w = 0\<^sub>V"
  obtain u where
    T1[ty]:"u be Element-of-struct V" and
    A2: "w \<oplus>\<^sub>V u = 0\<^sub>V" using algstr_0_def_11E[of V w] by mauto
  have "w \<oplus>\<^sub>V v = w \<oplus>\<^sub>V (v \<oplus>\<^sub>V (w \<oplus>\<^sub>V u))" using A2 rlvect_1_def_4E by auto
  also have "\<dots> = w \<oplus>\<^sub>V ((v \<oplus>\<^sub>V w) \<oplus>\<^sub>V u)" using rlvect_1_def_3E by auto
  also have "\<dots> =  (w \<oplus>\<^sub>V (v \<oplus>\<^sub>V w)) \<oplus>\<^sub>V u" using rlvect_1_def_3E by mty auto
  also have "\<dots> = w \<oplus>\<^sub>V u" using A1 rlvect_1_def_4E by mauto
  finally show "w \<oplus>\<^sub>V v = 0\<^sub>V" using A2 by auto
qed auto

mtheorem rlvect_1_th_3:
  "for V being add-associative\<bar>right-zeroed \<bar>right-complementable\<bar>
  addLoopStr holds V is right-add-cancelable"
proof(intro algstr_0_def_7I ballI)
  fix V assume T0[ty]:"V be add-associative\<bar>right-zeroed \<bar>right-complementable\<bar>
            addLoopStr"
  show "V is addMagma" by mauto
  fix v assume [ty]:"v be Element-of-struct V"
  obtain v1 where
    T1[ty]:"v1 be Element-of-struct V" and
    A1: "v \<oplus>\<^sub>V v1 = 0\<^sub>V" using algstr_0_def_11E[of V v] by mauto
  show "v is right-add-cancelable\<^sub>V"
  proof(intro algstr_0_def_4I ballI,auto)
    fix u w assume T2[ty]: "u be Element-of-struct V" "w be Element-of-struct V"
    assume A2: "u \<oplus>\<^sub>V v = w \<oplus>\<^sub>V v"
    have "u = u \<oplus>\<^sub>V 0\<^sub>V" using rlvect_1_def_4E T0 by auto
    also have "\<dots> =  (u \<oplus>\<^sub>V v) \<oplus>\<^sub>V v1" using A1 rlvect_1_def_3E by auto
    also have "\<dots> =  w \<oplus>\<^sub>V 0\<^sub>V" using A1 A2 rlvect_1_def_3E by auto
    also have "\<dots> =  w" using rlvect_1_def_4E by auto
    finally show "u = w" by auto
  qed
qed mauto


theorem rlvect_1_th_4[THEN bspec,simplified,rule_format,THEN bspec,rule_format]:
  "for V being non empty-struct\<bar>right-complementable\<bar>add-associative\<bar>right-zeroed \<bar> addLoopStr,
       v being Element-of-struct V holds v \<oplus>\<^sub>V 0\<^sub>V = v \<and> 0\<^sub>V \<oplus>\<^sub>V v = v"
proof(intro ballI conjI)
  fix V v assume [ty]:
     "V be non empty-struct\<bar>right-complementable\<bar>add-associative\<bar>right-zeroed\<bar>addLoopStr"
     "v be Element-of-struct V"
     thm ty
  obtain w where
    T1[ty]:"w be Element-of-struct V" and
    A1: "v \<oplus>\<^sub>V w = 0\<^sub>V" using algstr_0_def_16E[of V ] algstr_0_def_11E[of V v] by auto
  show A2: "v \<oplus>\<^sub>V 0\<^sub>V = v" using rlvect_1_def_4E by simp
  have "w \<oplus>\<^sub>V v = 0\<^sub>V" using A1 rlvect_1_lm_1[of V v w] by mauto
  thus "0\<^sub>V \<oplus>\<^sub>V v = v" using rlvect_1_def_3E[THEN bspec,THEN bspec,of V v w ] A1 A2 by auto
qed auto

mtheorem rlvect_1_reduce_1:
  mlet "V be non empty-struct\<bar>right-complementable\<bar>add-associative\<bar>right-zeroed\<bar> addLoopStr",
      "v1 be Zero \<^sub>V \<bar>Element-of-struct V",
      "v2 be Element-of-struct V"
   "reduce (v1 \<oplus>\<^sub>V v2) to v2"
proof
  have "v1 = 0\<^sub>V" using struct_0_def_12E[of V v1] by auto
  thus "v1 \<oplus>\<^sub>V v2 = v2" using rlvect_1_th_4 by auto
qed

mtheorem rlvect_1_reduce_2:
  mlet "V be non empty-struct\<bar>right-complementable\<bar>add-associative\<bar>right-zeroed\<bar> addLoopStr",
      "v1 be Zero \<^sub>V \<bar>Element-of-struct V",
      "v2 be Element-of-struct V"
   "reduce v2 \<oplus>\<^sub>V v1 to v2"
proof
  have "v1 = 0\<^sub>V" using struct_0_def_12E[of V v1] by auto
  thus "v2 \<oplus>\<^sub>V v1 = v2" using rlvect_1_th_4 by auto
qed

mtheorem rlvect_1_def_10:
  mlet "V be non empty-struct \<bar>addLoopStr",
       "v be Element-of-struct V"
   "assume  V be add-associative\<bar>right-zeroed\<bar>right-complementable redefine func \<ominus>\<^sub>V v \<rightarrow> Element-of-struct V means
      (\<lambda> it. v \<oplus>\<^sub>V it = 0\<^sub>V)"
proof
  show T: "(\<ominus>\<^sub>V v) be Element-of-struct V" by mauto
  fix IT assume [ty]:"V is add-associative \<bar> right-zeroed \<bar> right-complementable\<and>IT be Element-of-struct V"

  show "IT = \<ominus>\<^sub>V v \<longleftrightarrow> v \<oplus>\<^sub>V IT = 0\<^sub>V"
  proof(rule iffI3)
    obtain v1 where
      T1[ty]:"v1 be Element-of-struct V" and
      A2: "v \<oplus>\<^sub>V v1 = 0\<^sub>V" using algstr_0_def_16E[of V ] algstr_0_def_11E[of V v]  by auto
    have A3[ty]: "V is right-add-cancelable" using rlvect_1_th_3 by auto
    have A4: "v is left-complementable\<^sub>V"
    proof(intro algstr_0_def_10I)
      show "ex y be Element-of-struct V st y \<oplus>\<^sub>V v = 0\<^sub>V"
      proof(rule bexI[of _ v1])
        show "v1 be Element-of-struct V" by simp
        have T3: "(v1 \<oplus>\<^sub>V v) be Element-of-struct V" using algstr_0_def_1[of V v1 v]  by mty auto
        have "(v1 \<oplus>\<^sub>V v) \<oplus>\<^sub>V v1 = v1 \<oplus>\<^sub>V 0\<^sub>V" using rlvect_1_def_3E[THEN bspec,THEN bspec,THEN bspec,of V v1 v v1] A2 by simp
        also have "\<dots> = 0\<^sub>V \<oplus>\<^sub>V v1" using rlvect_1_reduce_1[of V "0\<^sub>V" v1] rlvect_1_reduce_2[of V "0\<^sub>V" v1] by mauto
        finally have "(v1 \<oplus>\<^sub>V v) \<oplus>\<^sub>V v1 =  0\<^sub>V \<oplus>\<^sub>V v1" by auto
        thus "v1 \<oplus>\<^sub>V v = 0\<^sub>V" using algstr_0_def_7E[THEN bspec,of V v1] 
          algstr_0_def_4E[THEN bspec,THEN bspec,of V v1 "v1 \<oplus>\<^sub>V v" "0\<^sub>V"] A3 by mauto
      qed simp_all
    qed simp_all
    have "v \<oplus>\<^sub>V \<ominus>\<^sub>V v \<oplus>\<^sub>V v = v \<oplus>\<^sub>V (\<ominus>\<^sub>V v \<oplus>\<^sub>V v)" using rlvect_1_def_3E[THEN bspec,THEN bspec,THEN bspec,of V v "\<ominus>\<^sub>V v" v]  A2 by mauto
    also have "\<dots> = v \<oplus>\<^sub>V 0\<^sub>V" using algstr_0_def_7E[of V ] algstr_0_def_13[of V ]  A4 by mty auto
    also have "\<dots> = 0\<^sub>V \<oplus>\<^sub>V v" using rlvect_1_reduce_1[of V "0\<^sub>V" v] rlvect_1_reduce_2[of V "0\<^sub>V" v] by mauto
    finally show "IT =\<ominus>\<^sub>V v \<longrightarrow> v \<oplus>\<^sub>V IT = 0\<^sub>V" using algstr_0_def_4E[THEN bspec,THEN bspec,of V v "v \<oplus>\<^sub>V \<ominus>\<^sub>V v" "0\<^sub>V"] 
             algstr_0_def_7E[of V] by mauto
    assume A5: "v \<oplus>\<^sub>V IT = 0\<^sub>V"
    have "IT = 0\<^sub>V \<oplus>\<^sub>V IT" using rlvect_1_reduce_1[of V "0\<^sub>V" IT] by mty auto
    also have "\<dots> = \<ominus>\<^sub>V v \<oplus>\<^sub>V v \<oplus>\<^sub>V IT" using algstr_0_def_7E[ of V ] algstr_0_def_13[of V v] A4 by mauto
    also have "\<dots> = \<ominus>\<^sub>V v \<oplus>\<^sub>V 0\<^sub>V" using rlvect_1_def_3E[THEN bspec,THEN bspec,THEN bspec,of V "\<ominus>\<^sub>V v" v IT] A2 A5 by mauto
    also have "\<dots> = \<ominus>\<^sub>V v" using rlvect_1_reduce_2[of V "0\<^sub>V" "\<ominus>\<^sub>V v" ] by mty auto
    finally show "IT = \<ominus>\<^sub>V v" by auto
   qed
qed

theorem rlvect_1_th_5[THEN bspec,simplified,rule_format,THEN bspec,rule_format]:
  "for V be non empty-struct\<bar>right-complementable\<bar>add-associative\<bar>right-zeroed \<bar> addLoopStr,
   v being Element-of-struct V holds v \<oplus>\<^sub>V \<ominus>\<^sub>V v = 0\<^sub>V \<and> \<ominus>\<^sub>V v \<oplus>\<^sub>V v = 0\<^sub>V"
proof(intro ballI conjI)
  fix V v assume T0[ty]:"V be non empty-struct\<bar>right-complementable\<bar>add-associative\<bar>right-zeroed \<bar> addLoopStr"
       "v be Element-of-struct V"
  thus A1: "v \<oplus>\<^sub>V \<ominus>\<^sub>V v = 0\<^sub>V" using rlvect_1_def_10 by auto
  have " (\<ominus>\<^sub>V v) be Element-of-struct V" by mauto
  thus "\<ominus>\<^sub>V v \<oplus>\<^sub>V v = 0\<^sub>V" using rlvect_1_lm_1[of V v] A1 by mby auto
qed auto


theorem rlvect_1_th_6[THEN bspec,simplified,rule_format,THEN bspec,THEN bspec,rule_format]:
  "for V be non empty-struct\<bar>right-complementable\<bar>add-associative\<bar>right-zeroed \<bar> addLoopStr,
   v,w being Element-of-struct V st v \<oplus>\<^sub>V w = 0\<^sub>V holds v = \<ominus>\<^sub>V w"
proof(intro ballI impI)
  fix V v w assume T0[ty]:"V be non empty-struct\<bar>right-complementable\<bar>add-associative\<bar>right-zeroed \<bar> addLoopStr"
       "v be Element-of-struct V" "w be Element-of-struct V"
  assume A1: "v \<oplus>\<^sub>V w = 0\<^sub>V"
  have "w \<oplus>\<^sub>V v = 0\<^sub>V" by (rule rlvect_1_lm_1) (mauto A1)
  thus "v = \<ominus>\<^sub>V w" using rlvect_1_def_10_uniq by mauto 
qed auto

theorem rlvect_1_th_7[THEN bspec,simplified,rule_format,THEN bspec,THEN bspec,rule_format]:
  "for V be non empty-struct\<bar>right-complementable\<bar>add-associative\<bar>right-zeroed \<bar> addLoopStr,
   v,u being Element-of-struct V holds
   ex w be Element-of-struct V st v \<oplus>\<^sub>V w = u"
proof(intro ballI)
  fix V v u assume T0[ty]:"V be non empty-struct\<bar>right-complementable\<bar>add-associative\<bar>right-zeroed \<bar> addLoopStr"
       "v be Element-of-struct V" "u be Element-of-struct V"
  show "ex w be Element-of-struct V st v \<oplus>\<^sub>V w = u"
    proof(rule bexI[of _ "\<ominus>\<^sub>V v \<oplus>\<^sub>V u"])
      have "v \<oplus>\<^sub>V (\<ominus>\<^sub>V v \<oplus>\<^sub>V u) = v \<oplus>\<^sub>V \<ominus>\<^sub>V v \<oplus>\<^sub>V u" using rlvect_1_def_3E by mty auto
      also have "\<dots> = 0\<^sub>V \<oplus>\<^sub>V u" using rlvect_1_def_10 by simp
      also have "\<dots> = u" using rlvect_1_reduce_1[of V "0\<^sub>V" u] by mauto
      finally show "v \<oplus>\<^sub>V (\<ominus>\<^sub>V v \<oplus>\<^sub>V u) = u" by auto
    qed mauto
qed mauto

theorem rlvect_1_th_8[THEN bspec,simplified,rule_format,THEN bspec,THEN bspec,THEN bspec,rule_format]:
  "for V be non empty-struct\<bar>right-complementable\<bar>add-associative\<bar>right-zeroed \<bar> addLoopStr,
   w,v1,v2 being Element-of-struct V st
      (w \<oplus>\<^sub>V v1 = w \<oplus>\<^sub>V v2 \<or> v1 \<oplus>\<^sub>V w = v2 \<oplus>\<^sub>V w) holds v1 = v2"
proof(intro ballI impI)
  fix V w v1 v2 assume T0[ty]:"V be non empty-struct\<bar>right-complementable\<bar>add-associative\<bar>right-zeroed\<bar> addLoopStr" "w be Element-of-struct V" "v1 be Element-of-struct V"
            "v2 be Element-of-struct V"

  assume Z: "w \<oplus>\<^sub>V v1 = w \<oplus>\<^sub>V v2 \<or> v1 \<oplus>\<^sub>V w = v2 \<oplus>\<^sub>V w"
  show "v1 = v2"
  proof (cases "v1 \<oplus>\<^sub>V w = v2 \<oplus>\<^sub>V w")
    case A1: True
      have "v1 = v1 \<oplus>\<^sub>V 0\<^sub>V" using rlvect_1_def_4E T0 by auto
      also have "\<dots> =  v1 \<oplus>\<^sub>V (w \<oplus>\<^sub>V \<ominus>\<^sub>V w)" using rlvect_1_th_5 by auto
      also have "\<dots> =  (v1 \<oplus>\<^sub>V w) \<oplus>\<^sub>V \<ominus>\<^sub>V w" using rlvect_1_def_3E by mty auto
      also have "\<dots> =  v2 \<oplus>\<^sub>V (w \<oplus>\<^sub>V \<ominus>\<^sub>V w)" using A1 rlvect_1_def_3E by mty auto
      also have "\<dots> =  v2 \<oplus>\<^sub>V 0\<^sub>V" using rlvect_1_th_5 by auto
      also have "\<dots> =  v2" using rlvect_1_def_4E by auto
      finally show "v1 = v2" by auto
    next
      case A1: False
      have "v1 = 0\<^sub>V \<oplus>\<^sub>V v1" using rlvect_1_reduce_1[of V "0\<^sub>V" v1]  by mauto
      also have "\<dots> =  (\<ominus>\<^sub>V w \<oplus>\<^sub>V w) \<oplus>\<^sub>V v1 " using rlvect_1_th_5 by auto
      also have "\<dots> =  \<ominus>\<^sub>V w \<oplus>\<^sub>V ( w \<oplus>\<^sub>V v1)" using rlvect_1_def_3E[THEN bspec,THEN bspec,THEN bspec,of V "\<ominus>\<^sub>V w" w v1 ] by mauto
      also have "\<dots> =  \<ominus>\<^sub>V w \<oplus>\<^sub>V w \<oplus>\<^sub>V v2" using A1 Z rlvect_1_def_3E[THEN bspec,THEN bspec,THEN bspec,of V "\<ominus>\<^sub>V w" w v2] by mauto
      also have "\<dots> =  0\<^sub>V \<oplus>\<^sub>V v2" using rlvect_1_th_5 by auto
      also have "\<dots> =  v2" using rlvect_1_reduce_1[of V "0\<^sub>V" v2]  by mauto
      finally show "v1 = v2" by auto
  qed
qed auto

theorem rlvect_1_th_17[THEN bspec,simplified,rule_format,THEN bspec,rule_format]:
  "for V be non empty-struct\<bar>right-complementable\<bar>add-associative\<bar>right-zeroed \<bar> addLoopStr,
   v being Element-of-struct V holds \<ominus>\<^sub>V \<ominus>\<^sub>V v = v"
proof(intro ballI)
  fix V v assume T0[ty]:"V be non empty-struct\<bar>right-complementable\<bar>add-associative\<bar>right-zeroed\<bar> addLoopStr" "v be Element-of-struct V"
  have "v \<oplus>\<^sub>V \<ominus>\<^sub>V v = 0\<^sub>V" using rlvect_1_def_10 by auto
  thus "\<ominus>\<^sub>V \<ominus>\<^sub>V v = v" using rlvect_1_th_6[of V v] by mty auto
qed auto

end
