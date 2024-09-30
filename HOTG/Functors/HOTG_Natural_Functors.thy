theory HOTG_Natural_Functors 
  imports HOTG_Functions_Composition Transport.LBinary_Relations Transport.LFunctions
begin


(* with 't/'f pairs for the relator are quite a pain *)
type_synonym t = "set" 
type_synonym f = "set"

text \<open>Indexed identity function\<close>

definition "iid \<equiv> (\<lambda>_. id)"

lemma iid_eq_id [simp]: "iid = (\<lambda>_. id)"
  unfolding iid_def by simp

text \<open>Indexed composition\<close>

definition "comp_ifun (f :: 'i \<Rightarrow> 'b \<Rightarrow> 'c) (g :: 'i \<Rightarrow> 'a \<Rightarrow> 'b) i \<equiv> f i \<circ> g i"
adhoc_overloading comp comp_ifun

lemma comp_ifun_eq [simp]: "((f :: 'i \<Rightarrow> 'b \<Rightarrow> 'c) \<circ> g) i = f i \<circ> g i"
  unfolding comp_ifun_def by simp

lemma comp_assoc: "(f :: 'i \<Rightarrow> 'c \<Rightarrow> 'd) \<circ> (g :: 'i \<Rightarrow> 'b \<Rightarrow> 'c) \<circ> (h :: 'i \<Rightarrow> 'a \<Rightarrow> 'b) = f \<circ> (g \<circ> h)" 
  unfolding comp_ifun_def by (auto simp add: fun_eq_iff)

(*copied from HOL*)
definition "fun_upd f i y = (\<lambda>x. if x = i then y else f x)"

nonterminal updbinds and updbind
syntax
  "_updbind" :: "'a \<Rightarrow> 'a \<Rightarrow> updbind"             ("(2_ :=/ _)")
  ""         :: "updbind \<Rightarrow> updbinds"             ("_")
  "_updbinds":: "updbind \<Rightarrow> updbinds \<Rightarrow> updbinds" ("_,/ _")
  "_Update"  :: "'a \<Rightarrow> updbinds \<Rightarrow> 'a"            ("_/'((_)')" [1000, 0] 900)
syntax_consts
  "_updbind" "_updbinds" "_Update" \<rightleftharpoons> fun_upd
translations
  "_Update f (_updbinds b bs)" \<rightleftharpoons> "_Update (_Update f b) bs"
  "f(x:=y)" \<rightleftharpoons> "CONST fun_upd f x y"

lemma fun_upd_apply [simp]: "(f(x := y)) z = (if z = x then y else f z)"
  unfolding fun_upd_def by simp

lemma fun_upd_triv [simp]: "f(x := f x) = f"
  by (intro ext) simp

(*end of copy*)

locale HOTG_Functor =
  fixes F :: "('i \<Rightarrow> t \<Rightarrow> bool) \<Rightarrow> f \<Rightarrow> bool"
  and I :: "'i \<Rightarrow> bool"
  \<comment>\<open>The type parameters of a functor are specified by a function from a given index type \<open>'i\<close>
    subject to a restriction predicate @{term I}. In particular, a functor may have an infinite
    number of type parameters.\<close>
  and Fmap :: "('i \<Rightarrow> t \<Rightarrow> t) \<Rightarrow> f \<Rightarrow> f"
  assumes Fmap_type: "\<And>iIn iOut. (((i : I) \<Rightarrow> iIn i \<Rightarrow> iOut i) \<Rightarrow> F iIn \<Rightarrow> F iOut) Fmap"
  and Fmap_id: "\<And>(iT :: 'i \<Rightarrow> t \<Rightarrow> bool) (ig :: 'i \<Rightarrow> t \<Rightarrow> t).
    ((i : I) \<Rrightarrow> iT i \<Rrightarrow> (=)) ig iid \<Longrightarrow>
    (F iT \<Rrightarrow> (=)) (Fmap ig) id"
  and Fmap_comp: "\<And>ig ih iIn iMid iOut.
    ((i : I) \<Rightarrow> iIn i \<Rightarrow> iMid i) ig \<Longrightarrow>
    ((i : I) \<Rightarrow> iMid i \<Rightarrow> iOut i) ih \<Longrightarrow>
    (F iIn \<Rrightarrow> (=)) (Fmap (ih \<circ> ig)) (Fmap ih \<circ> Fmap ig)"
begin

lemma Fmap_id_comp: "((i : I) \<Rightarrow> iIn i \<Rightarrow> iMid i) ig \<Longrightarrow> (F iIn \<Rrightarrow> (=)) (Fmap (comp_ifun iid ig)) (Fmap ig)"
proof-
  have "comp_ifun iid ig = ig" by auto
  then show ?thesis by auto
qed

lemma Fmap_comp_id: "((i : I) \<Rightarrow> iIn i \<Rightarrow> iMid i) ig \<Longrightarrow> (F iIn \<Rrightarrow> (=)) (Fmap (comp_ifun ig iid)) (Fmap ig)"
proof-
  have "comp_ifun ig iid = ig" by auto
  then show ?thesis by auto
qed
definition "test \<equiv> \<emptyset>"
end


definition "image_pred (f :: 'a \<Rightarrow> 'b) (P :: 'a \<Rightarrow> bool) \<equiv> has_inverse_on P f"

lemma image_pred_eq_has_inverse_on [simp]: "image_pred f P = has_inverse_on P f"
  unfolding image_pred_def by simp

term "inverse"

(*unbundle HOL_order_syntax
  no_hotg_le_syntax*)

locale HOTG_Natural_Functor = HOTG_Functor +
  fixes Fpred :: "'i \<Rightarrow> f \<Rightarrow> t \<Rightarrow> bool"
  assumes Fpred_type: "\<And>iT. ((i : I) \<Rightarrow> F iT \<Rightarrow> (\<ge>) (iT i)) Fpred"
  and Fpred_natural: "\<And>iIn iOut ig i.
    \<comment> \<open>maybe \<open>(iIn i \<Rightarrow> iOut i) (ig i)\<close> is enough?\<close>
    ((i : I) \<Rightarrow> iIn i \<Rightarrow> iOut i) ig \<Longrightarrow>
    I i \<Longrightarrow>
    (F iIn \<Rrightarrow> (=)) (Fpred i \<circ> Fmap ig) (image_pred (ig i) \<circ> Fpred i)"
  and Fmap_cong: "\<And>iIn iOut1 iOut2 ig ih x.
    F iIn x \<Longrightarrow>
    \<comment> \<open>maybe we do not need the types of \<open>ig\<close> and \<open>ih\<close>?\<close>
    ((i : I) \<Rightarrow> iIn i \<Rightarrow> iOut1 i) ig \<Longrightarrow>
    ((i : I) \<Rightarrow> iIn i \<Rightarrow> iOut2 i) ih \<Longrightarrow>
    ((i : I) \<Rrightarrow> Fpred i x \<Rrightarrow> (=)) ig ih \<Longrightarrow>
    Fmap ig x = Fmap ih x"
  
begin

lemma Fmap_Fmap_eq_Fmap_comp_update_if_eq_id:
  assumes x_type: "F iIn x"
  and ig_type: "((i : I) \<Rightarrow> iIn i \<Rightarrow> iMid i) ig"
  and ih_type: "((i : I) \<Rightarrow> iMid i \<Rightarrow> iOut i) ih"
  and "I i"
  and ig_id: "(iIn i \<Rrightarrow> (=)) (ig i) id"
  shows "Fmap ih (Fmap ig x) = Fmap ((ih \<circ> ig)(i := ih i)) x"
proof -
  from assms Fmap_comp have "Fmap ih (Fmap ig x) = Fmap (ih \<circ> ig) x" by fastforce
  also from x_type have "... = Fmap ((ih \<circ> ig)(i := ih i)) x"
  proof (rule Fmap_cong)
    from ig_type ih_type show comp_type: "((i : I) \<Rightarrow> iIn i \<Rightarrow> iOut i) (ih \<circ> ig)" by fastforce
    moreover show "((i : I) \<Rightarrow> iIn i \<Rightarrow> iOut i) ((ih \<circ> ig)(i := ih i))"
    proof (urule (rr) dep_mono_wrt_predI)
      fix j y assume prems: "I j" "iIn j y"
      show "iOut j (((ih \<circ> ig)(i := ih i)) j y)"
      proof (cases "i = j")
        case False
        with prems comp_type have "iOut j ((ih \<circ> ig) j y)" by blast
        moreover from False have "iOut j (((ih \<circ> ig)(i := ih i)) j y) \<longleftrightarrow> iOut j ((ih \<circ> ig) j y)"
          by auto
        ultimately show ?thesis by simp
      next
        case True
        with ig_id prems have "ig j y = y" by auto
        with prems ig_type have "iMid j y" by fastforce
        with prems ih_type have "iOut j (ih j y)" by blast
        with True show ?thesis by simp
      qed
    qed
    show "((i : I) \<Rrightarrow> Fpred i x \<Rrightarrow> (=)) (ih \<circ> ig) ((ih \<circ> ig)(i := ih i))"
    proof (urule (rr) Dep_Fun_Rel_predI)
      fix j y assume prems: "I j" "Fpred j x y"
      show "(ih \<circ> ig) j y = ((ih \<circ> ig)(i := ih i)) j y"
      proof (cases "i = j")
        case True
        have "(ih \<circ> ig) j y = ih j (ig j y)" by simp
        moreover have "ig j y = y"
        proof -
          from \<open>I j\<close> x_type Fpred_type have "Fpred j x \<le> iIn j" by blast
          with prems have "iIn j y" by blast
          with True \<open>I j\<close> ig_id show "ig j y = y" by auto
        qed
        then show ?thesis by auto
      qed simp
    qed
  qed
  finally show ?thesis by simp
qed

lemma Fmap_eq_Fmap_update_if_eq:
  assumes x_type: "F iIn x"
  and ig_type: "((i : I) \<Rightarrow> iIn i \<Rightarrow> iOut i) ig"
  and ih_type: "((i : I) \<Rightarrow> iIn i \<Rightarrow> iOut i) ih"
  and "I i"
  and ig_eq: "(iIn i \<Rrightarrow> (=)) (ih i) (ig i)"
  shows "Fmap ig x = Fmap (ig(i := ih i)) x"
proof -
  have upd_type: "((i : I) \<Rightarrow> iIn i \<Rightarrow> iOut i) (ig(i := ih i))" proof (urule (rr) dep_mono_wrt_predI)
    fix j y assume "I j" "iIn j y"
    then show "iOut j ((ig(i := ih i)) j y)" using ig_type ih_type by auto
  qed
  have "((i : I) \<Rrightarrow> Fpred i x \<Rrightarrow> (=)) (ig) (ig(i := ih i))"
  proof (urule (rr) Dep_Fun_Rel_predI)
    fix j y assume "I j" "Fpred j x y"
    show "(ig) j y = (ig(i := ih i)) j y" proof (cases "i = j")
      case True
      with \<open>I j\<close> x_type Fpred_type \<open>Fpred j x y\<close> ig_eq True show "ig j y = (ig(i := ih i)) j y" by fastforce
    qed auto
  qed
    with assms upd_type Fmap_cong show "Fmap ig x = Fmap (ig(i := ih i)) x" by auto
  qed

lemma Fmap_comp_decomp:
  assumes x_type: "F iIn x"
  and ig_type: "((i : I) \<Rightarrow> iIn i \<Rightarrow> iMid1 i) ig"
  and ih_type: "((i : I) \<Rightarrow> iMid1 i \<Rightarrow> iMid2 i) ih"
  and ii_type: "((i : I) \<Rightarrow> iMid2 i \<Rightarrow> iOut i) ii"
  and "I i"
shows "Fmap (ii \<circ> ih \<circ> ig) x = Fmap ii (Fmap ih (Fmap ig x))"
proof-
  have comp_type: "((i : I) \<Rightarrow> iIn i \<Rightarrow> iMid2 i) (ih \<circ> ig)" using assms by fastforce
    have "Fmap ii (Fmap ih (Fmap ig x)) = Fmap ii (Fmap (ih \<circ> ig) x)" using Fmap_comp[of iIn iMid1 ig iMid2 ih] assms by auto
    also have "... = Fmap (ii \<circ> ih \<circ> ig) x" using comp_type Fmap_comp[of iIn iMid2 "(ih \<circ> ig)" iOut ii] assms comp_assoc[of ii ih ig] by auto
    finally show "Fmap (ii \<circ> ih \<circ> ig) x = Fmap ii (Fmap ih (Fmap ig x))" ..
  qed

(*definition "Frel (iR :: 'i \<Rightarrow> set \<Rightarrow> set \<Rightarrow> bool) Fx Fy = (\<exists>Fz. (((i : I) \<Rrightarrow> (\<lambda>x. True) \<Rrightarrow> (\<le>)) (Fpred i Fz) (\<lambda>a. \<exists>x y. a = \<langle>x,y\<rangle> \<and> iR i x y)) \<and> (Fmap (\<lambda>_. fst) Fz = Fx)
            \<and> (Fmap (\<lambda>_. snd) Fz = Fy))"*)

definition "Frel (iR :: 'i \<Rightarrow> set \<Rightarrow> set \<Rightarrow> bool) Fx Fy = (\<exists>Fz. (\<forall>i. I i \<longrightarrow> (Fpred i Fz) \<le> (\<lambda>a. \<exists>x y. a = \<langle>x,y\<rangle> \<and> iR i x y)) \<and> (Fmap (\<lambda>_. fst) Fz = Fx)
            \<and> (Fmap (\<lambda>_. snd) Fz = Fy))"


lemma FrelI:
  assumes "\<And>i. I i \<Longrightarrow> (Fpred i Fz) \<le> (\<lambda>a.\<exists>x y. a = \<langle>x,y\<rangle> \<and> iR i x y)"
  and "Fmap (\<lambda>_. fst) Fz = Fx"
  and "Fmap (\<lambda>_. snd) Fz = Fy"
  shows "Frel iR Fx Fy"
  using assms Frel_def by auto

lemma FrelE:
  assumes "Frel iR Fx Fy"
  obtains z where "\<And>i. I i \<Longrightarrow> (Fpred i z) \<le> (\<lambda>a. \<exists>x y. a = \<langle>x,y\<rangle> \<and> iR i x y)" and "Fmap (\<lambda>_. fst) z = Fx" and "Fmap (\<lambda>_. snd) z = Fy" 
  using assms Frel_def by auto

definition "Grp A f \<equiv> (\<lambda>a b. b = f a \<and> A a)"

lemma GrpI: "\<lbrakk>f x = y; A x\<rbrakk> \<Longrightarrow> Grp A f x y"
  unfolding Grp_def by auto

lemma GrpE: "Grp A f x y \<Longrightarrow> (\<lbrakk>f x = y; A x\<rbrakk> \<Longrightarrow> R) \<Longrightarrow> R"
  unfolding Grp_def by auto

definition "convol f g \<equiv> \<lambda>(a::set). \<langle>f a, g a\<rangle>"

lemma convol_type: assumes f_type: "(a \<Rightarrow> b) f" and g_type: "(a \<Rightarrow> c) g"
  shows "((a :: set \<Rightarrow> bool) \<Rightarrow> (b \<times> c)) (convol f g)"
  using assms unfolding convol_def by auto

lemma fst_comp_convol_eq: "fst \<circ> (convol f g) = f" using convol_def by auto
lemma snd_comp_convol_eq: "snd \<circ> (convol f g) = g" using convol_def by auto

lemma Grp_top_eq_eq_comp: "Grp \<top> f = (=) \<circ> f"
  by(intro ext) (auto elim: GrpE intro: GrpI)

lemma Grp_top_Fmap_eq_Frel_Grp: 
  assumes ig_type: "((i : I) \<Rightarrow> (iin i) \<Rightarrow> (iout i)) ig"
  shows "((F iin) \<Rrightarrow> (F iout) \<Rrightarrow> (=)) (Grp \<top> (Fmap ig)) (Frel (\<lambda>i. Grp \<top> (ig i)))"
proof (intro Fun_Rel_predI iffI)
  fix Fx Fy assume "F iin Fx" and "F iout Fy"
  assume "Grp \<top> (Fmap ig) Fx Fy"
  then have Fy_eq:"(Fmap ig) Fx = Fy" by (elim GrpE)
  have inner_type: "((i : I) \<Rightarrow> iin i \<Rightarrow> (iin i \<times> iout i)) (\<lambda>i. convol id (ig i))" proof (intro dep_mono_wrt_predI) 
    fix i assume "I i" then show "(iin i \<Rightarrow> iin i \<times> iout i) (convol id (ig i))" 
      using ig_type convol_type[of "iin i" "iin i" "id" "iout i" "ig i"] mono_wrt_pred_self_id by auto
    qed
  show "Frel (\<lambda>i. Grp \<top> (ig i)) Fx Fy" proof (intro FrelI[of "Fmap (\<lambda>i. convol id (ig i)) _"])
    fix i x assume "I i"
    then have "(F iin \<Rrightarrow> (=)) (Fpred i \<circ> Fmap (\<lambda>i. convol id (ig i))) ((image_pred (convol id (ig i))) \<circ> Fpred i)" using inner_type
         Fpred_natural[of iin "\<lambda>i. iin i \<times> iout i" "(\<lambda>i. convol id (ig i))"] by auto
    then have 1:"(Fpred i \<circ> Fmap (\<lambda>i. convol id (ig i))) Fx = ((image_pred (convol id (ig i))) \<circ> Fpred i) Fx" using \<open>F iin Fx\<close> by auto
    have "((image_pred (convol id (ig i))) \<circ> Fpred i) Fx \<le> (\<lambda>a. \<exists>xa y. a = \<langle>xa, y\<rangle> \<and> Grp \<top> (ig i) xa y)" proof
      fix x
      have "((image_pred (convol id (ig i))) \<circ> Fpred i) Fx x \<Longrightarrow> (\<exists>xa y. x = \<langle>xa, y\<rangle> \<and> Grp \<top> (ig i) xa y)" proof-
        assume "((image_pred (convol id (ig i))) \<circ> Fpred i) Fx x"
        then obtain A where "(Fpred i Fx) A" and "convol id (ig i) A = x" by auto
        then have "x = \<langle>A, ig i A\<rangle>" using convol_def by auto
        moreover have "Grp \<top> (ig i) A (ig i A)" using Grp_def[of \<top> "ig i"] by auto
        ultimately show "\<exists>A y. x = \<langle>A, y\<rangle> \<and> Grp \<top> (ig i) A y" by auto
      qed
        then show "(image_pred (convol id (ig i)) \<circ> Fpred i) Fx x \<le> (\<exists>xa y. x = \<langle>xa, y\<rangle> \<and> Grp \<top> (ig i) xa y)" by auto
      qed
      with 1 show "Fpred i (Fmap (\<lambda>i. convol id (ig i)) Fx) \<le> (\<lambda>a. \<exists>xa y. a = \<langle>xa, y\<rangle> \<and> Grp \<top> (ig i) xa y)" 
        by (auto simp: Grp_top_eq_eq_comp)
  next
    have "((i : I) \<Rightarrow> (iin i \<times> iout i) \<Rightarrow> iin i) (\<lambda>_. fst)" apply (intro dep_mono_wrt_predI) by auto
    with inner_type have "(F iin \<Rrightarrow> (=)) (Fmap (comp_ifun (\<lambda>_. fst) (\<lambda>i. convol id (ig i)))) 
      (Fmap (\<lambda>_. fst) \<circ> Fmap (\<lambda>i. convol id (ig i)))" (* needs type-checking to use Fmap_comp!*)
      using Fmap_comp[of iin "\<lambda>i. (iin i) \<times> (iout i)" "(\<lambda>i. convol id (ig i))" "iin" "(\<lambda>_. fst)"] by blast
    moreover with \<open>F iin Fx\<close> have "Fmap (comp_ifun (\<lambda>_. fst) (\<lambda>i. convol id (ig i))) Fx = 
                                  (Fmap (\<lambda>_. fst) \<circ> Fmap (\<lambda>i. convol id (ig i))) Fx" by blast
    moreover have "(comp_ifun (\<lambda>_. fst) (\<lambda>i. convol id (ig i))) = (\<lambda>i. (\<lambda>_. fst) i \<circ> (\<lambda>i.(convol id (ig i))) i)"
      using comp_ifun_eq[of "\<lambda>_. fst" "\<lambda>i. convol id (ig i)"] by auto
    moreover then have "Fmap (comp_ifun (\<lambda>_. fst) (\<lambda>i. convol id (ig i))) Fx = Fmap iid Fx" using fst_comp_convol_eq by auto
    moreover then have "... = Fx" using Fmap_id[of iin iid] \<open>F iin Fx\<close> by (fastforce elim!: Dep_Fun_Rel_relE)
    ultimately show "Fmap (\<lambda>_. fst) (Fmap (\<lambda>i. convol id (ig i)) Fx) = Fx"  by auto
    have "((i : I) \<Rightarrow> (iin i \<times> iout i) \<Rightarrow> iout i) (\<lambda>_. snd)" apply (intro dep_mono_wrt_predI) by auto
    with inner_type have "(F iin \<Rrightarrow> (=)) (Fmap (comp_ifun (\<lambda>_. snd) (\<lambda>i. convol id (ig i)))) 
      (Fmap (\<lambda>_. snd) \<circ> Fmap (\<lambda>i. convol id (ig i)))" (* needs type-checking to use Fmap_comp!*)
      using Fmap_comp[of iin "\<lambda>i. (iin i) \<times> (iout i)" "(\<lambda>i. convol id (ig i))" "iout" "(\<lambda>_. snd)"] by blast
    moreover with \<open>F iin Fx\<close> have "Fmap (comp_ifun (\<lambda>_. snd) (\<lambda>i. convol id (ig i))) Fx = 
                                  (Fmap (\<lambda>_. snd) \<circ> Fmap (\<lambda>i. convol id (ig i))) Fx" by blast
    moreover have "(comp_ifun (\<lambda>_. snd) (\<lambda>i. convol id (ig i))) = (\<lambda>i. (\<lambda>_. snd) i \<circ> (\<lambda>i.(convol id (ig i))) i)"
      using comp_ifun_eq[of "\<lambda>_. fst" "\<lambda>i. convol id (ig i)"] by auto
    moreover then have "Fmap (comp_ifun (\<lambda>_. snd) (\<lambda>i. convol id (ig i))) Fx = Fmap ig Fx" using snd_comp_convol_eq by auto
    moreover then have "... = Fy" using Fy_eq by blast
    ultimately show "Fmap (\<lambda>_. snd) (Fmap (\<lambda>i. convol id (ig i)) Fx) = Fy" by auto
  qed
next
  fix Fx Fy assume "F iin Fx" and "F iout Fy"
  assume FrelFxFy: "Frel (\<lambda>i. Grp \<top> (ig i)) Fx Fy"
  then obtain z where Fpred_leq:"\<And>i. I i \<Longrightarrow> (Fpred i z) \<le> (\<lambda>a. \<exists>x y. a = \<langle>x,y\<rangle> \<and> (\<lambda>i. Grp \<top> (ig i)) i x y)" and Fx_eq: "Fmap (\<lambda>_. fst) z = Fx"
    and Fy_eq: "Fmap (\<lambda>_. snd) z = Fy" by (auto elim: FrelE)
  then have "\<And>a i. I i \<Longrightarrow> (Fpred i z) a \<Longrightarrow> Grp \<top> (ig i) (fst a) (snd a)" by fastforce
  have z_type: "F (\<lambda>i. iin i \<times> iout i) z" sorry
  show "Grp \<top> (Fmap ig) Fx Fy" proof (subst Grp_top_eq_eq_comp)
    from FrelFxFy Fx_eq Fpred_leq Fy_eq have eq_comp:"((=) \<circ> Fmap ig) Fx Fy = (Fmap ig (Fmap (\<lambda>_. fst) z) = Fmap (\<lambda>_. snd) z)" by auto
    have eq:"((i : I) \<Rrightarrow> Fpred i z \<Rrightarrow> (=)) (ig \<circ> (\<lambda>_.fst)) (\<lambda>_. snd)" apply (intro Dep_Fun_Rel_predI Fun_Rel_predI) using Fpred_leq GrpE by fastforce
    have fst_type: "((i : I) \<Rightarrow> (iin i \<times> iout i) \<Rightarrow> iin i) (\<lambda>_. fst)" apply (intro dep_mono_wrt_predI) by fastforce
    have ig_fst_type:"((i : I) \<Rightarrow> (iin i \<times> iout i) \<Rightarrow> iout i) (ig \<circ> (\<lambda>_. fst))" apply (intro dep_mono_wrt_predI) using ig_type by fastforce
    have snd_type:"((i : I) \<Rightarrow> (iin i \<times> iout i) \<Rightarrow> iout i) (\<lambda>_. snd)" apply (intro dep_mono_wrt_predI) by auto
    from eq ig_fst_type snd_type z_type have "Fmap (ig \<circ> (\<lambda>_.fst)) z = Fmap (\<lambda>_.snd) z" using Fmap_cong[of "\<lambda>i. iin i \<times> iout i" z iout "ig \<circ> (\<lambda>_. fst)" iout "\<lambda>_.snd"] by auto
    then have "Fmap ig (Fmap (\<lambda>_.fst) z) = Fmap (\<lambda>_.snd) z" using ig_type Fmap_comp[of "\<lambda>i. iin i \<times> iout i" iin "\<lambda>_. fst" iout ig] z_type fst_type by auto
    then show "((=) \<circ> Fmap ig) Fx Fy" using Fx_eq Fy_eq by auto
  qed
qed

  

lemma Frel_Grp_top_Fmap:
  assumes ig_type: "((i : I) \<Rightarrow> iin i \<Rightarrow> iout i) ig"
  and "F iin x"
  shows "Frel (\<lambda>i. Grp \<top> (ig i)) x (Fmap ig x)"
  sorry

end

end