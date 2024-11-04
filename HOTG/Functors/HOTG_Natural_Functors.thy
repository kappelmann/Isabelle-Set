theory HOTG_Natural_Functors
  imports
    HOTG_Functions_Composition
    Transport.LBinary_Relations
    Transport.LFunctions
    Hilbert_Eps
begin

definition "K x \<equiv> \<lambda>_. x"

lemma K_eq [simp]: "K = (\<lambda>x _. x)"
  unfolding K_def by simp

lemma mono_K: "((A :: 'a \<Rightarrow> bool) \<Rightarrow> B \<Rightarrow> A) K" by fastforce

text \<open>Indexed identity function\<close>

definition "iid \<equiv> K id"

lemma iid_eq_id [simp]: "iid = K id"
  unfolding iid_def by simp

lemma mono_iid: "((i : (I :: 'i \<Rightarrow> bool)) \<Rightarrow> (iT i :: 'a \<Rightarrow> bool) \<Rightarrow> iT i) iid" by fastforce


text \<open>Indexed composition\<close>

definition "comp_ifun (f :: 'i \<Rightarrow> 'b \<Rightarrow> 'c) (g :: 'i \<Rightarrow> 'a \<Rightarrow> 'b) i \<equiv> f i \<circ> g i"
adhoc_overloading comp comp_ifun

lemma comp_ifun_eq [simp]: "((f :: 'i \<Rightarrow> 'b \<Rightarrow> 'c) \<circ> g) i = f i \<circ> g i"
  unfolding comp_ifun_def by simp

lemma comp_ifun_assoc: "(f :: 'i \<Rightarrow> 'c \<Rightarrow> 'd) \<circ> (g :: 'i \<Rightarrow> 'b \<Rightarrow> 'c) \<circ> (h :: 'i \<Rightarrow> 'a \<Rightarrow> 'b) = f \<circ> (g \<circ> h)"
  unfolding comp_ifun_def by (auto simp add: fun_eq_iff)

lemma mono_mono_wrt_mono_wrt_comp_ifun:
  "(((I :: 'i \<Rightarrow> bool) \<Rightarrow> (B :: 'b \<Rightarrow> bool) \<Rightarrow> C) \<Rightarrow> (I \<Rightarrow> A \<Rightarrow> B) \<Rightarrow> I \<Rightarrow> A \<Rightarrow> C) (\<circ>)"
  by force

definition "rel_comp_irel (R :: 'i \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool) (S :: 'i \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> bool) i \<equiv> R i \<circ>\<circ> S i"
adhoc_overloading rel_comp rel_comp_irel

lemma rel_comp_irel_eq [simp]: "((R :: 'i \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool) \<circ>\<circ> S) i = R i \<circ>\<circ> S i"
  unfolding rel_comp_irel_def by simp

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




(* with 't/'f pairs for the relator are quite a pain *)
type_synonym t = "set"
type_synonym f = "set"

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

lemma mono_upd_iid:
  assumes "((T::set \<Rightarrow> bool) \<Rightarrow> T') f"
  and "((i : I) \<Rrightarrow> (\<le>)) iT ((K \<top>)(irec := T))"
  shows "((i : I) \<Rightarrow> iT i \<Rightarrow> (iT(irec := T')) i) (iid(irec:=f))"
proof(intro dep_mono_wrt_predI mono_wrt_predI)
  fix i x assume i_type: "I i" and x_type: "iT i x"
  show "(iT(irec := T')) i ((iid(irec := f)) i x)"
  proof (cases "i = irec")                         
    case True
    with assms x_type i_type show ?thesis by fastforce
  next
    case False
    with x_type show ?thesis by auto
  qed
qed

lemma Fmap_iid_comp: "((i : I) \<Rightarrow> iIn i \<Rightarrow> iMid i) ig \<Longrightarrow> (F iIn \<Rrightarrow> (=)) (Fmap (comp_ifun iid ig)) (Fmap ig)"
proof -
  have "comp_ifun iid ig = ig" by auto
  then show ?thesis by auto
qed

lemma Fmap_comp_iid: "((i : I) \<Rightarrow> iIn i \<Rightarrow> iMid i) ig \<Longrightarrow> (F iIn \<Rrightarrow> (=)) (Fmap (comp_ifun ig iid)) (Fmap ig)"
proof -
  have "comp_ifun ig iid = ig" by auto
  then show ?thesis by auto
qed


lemma F_type_if_leq:
  assumes x_type:"F iT x"
    and iT_leq_iS:"(I \<Rrightarrow> (\<le>)) iT iS"
  shows "F iS x"
proof-
  from iT_leq_iS have "((i : I) \<Rightarrow> (iT i) \<Rightarrow> (iS i)) iid" by fastforce
  with x_type Fmap_type have "F iS (Fmap iid x)" by auto
  with x_type Fmap_id show "F iS x" by fastforce
qed


end

definition "image_pred (f :: 'a \<Rightarrow> 'b) (P :: 'a \<Rightarrow> bool) \<equiv> has_inverse_on P f"

lemma image_pred_eq_has_inverse_on [simp]: "image_pred f P = has_inverse_on P f"
  unfolding image_pred_def by simp

locale HOTG_Natural_Functor = HOTG_Functor +
  fixes Fpred :: "'i \<Rightarrow> f \<Rightarrow> t \<Rightarrow> bool"
  assumes Fpred_type: "\<And>iT. ((i : I) \<Rightarrow> F iT \<Rightarrow> (\<ge>) (iT i)) Fpred"
  and Fpred_natural: "\<And>iIn iOut ig i.
    \<comment> \<open>maybe \<open>(iIn i \<Rightarrow> iOut i) (ig i)\<close> is enough?\<close>
    ((i : I) \<Rightarrow> iIn i \<Rightarrow> iOut i) ig \<Longrightarrow>
    I i \<Longrightarrow>
    (F iIn \<Rrightarrow> (=)) (Fpred i \<circ> Fmap ig) (image_pred (ig i) \<circ> Fpred i)"
  (* ToDo: needed? *)
  (*and Fmap_type_Fpred: "\<And>iIn iOut x ig.
    ((i : I) \<Rightarrow> Fpred i x \<Rightarrow> iOut i) ig \<Longrightarrow> F iIn x \<Longrightarrow> F iOut (Fmap ig x)"*)
  and Fmap_cong: "\<And>iIn ig ih x.
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
    and ig_id: "(iIn i \<Rrightarrow> (=)) (ig i) id"
  shows "Fmap ih (Fmap ig x) = Fmap ((ih \<circ> ig)(i := ih i)) x"
proof -
  from assms Fmap_comp have "Fmap ih (Fmap ig x) = Fmap (ih \<circ> ig) x" by fastforce
  also from x_type have "... = Fmap ((ih \<circ> ig)(i := ih i)) x"
  proof (rule Fmap_cong)
    from ig_type ih_type show comp_type: "((i : I) \<Rightarrow> iIn i \<Rightarrow> iOut i) (ih \<circ> ig)" by fastforce
    show "((i : I) \<Rightarrow> iIn i \<Rightarrow> iOut i) ((ih \<circ> ig)(i := ih i))"
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
  finally show ?thesis .
qed

lemma Fmap_eq_Fmap_update_if_eq:
  assumes x_type: "F iIn x"
    and ig_type: "((i : I) \<Rightarrow> iIn i \<Rightarrow> iOut i) ig"
    and ih_type: "((i : I) \<Rightarrow> iIn i \<Rightarrow> iOut i) ih"
    and ig_eq: "(iIn i \<Rrightarrow> (=)) (ih i) (ig i)"
  shows "Fmap ig x = Fmap (ig(i := ih i)) x"
proof -
  have upd_type: "((i : I) \<Rightarrow> iIn i \<Rightarrow> iOut i) (ig(i := ih i))"
  proof (urule (rr) dep_mono_wrt_predI)
    fix j y assume "I j" "iIn j y"
    then show "iOut j ((ig(i := ih i)) j y)" using ig_type ih_type by auto
  qed
  have "((i : I) \<Rrightarrow> Fpred i x \<Rrightarrow> (=)) (ig) (ig(i := ih i))"
  proof (urule (rr) Dep_Fun_Rel_predI)
    fix j y assume "I j" "Fpred j x y"
    show "ig j y = (ig(i := ih i)) j y"
    proof (cases "i = j")
      case True
      with \<open>I j\<close> x_type Fpred_type \<open>Fpred j x y\<close> ig_eq True show "ig j y = (ig(i := ih i)) j y"
        by fastforce
    qed auto
  qed
  with assms upd_type Fmap_cong show "Fmap ig x = Fmap (ig(i := ih i)) x" by auto
qed

lemma Fmap_comp_comp_eq_Fmap_Fmap_Fmap:
  assumes "F iIn x"
    and "((i : I) \<Rightarrow> iIn i \<Rightarrow> iMid1 i) ig"
    and "((i : I) \<Rightarrow> iMid1 i \<Rightarrow> iMid2 i) ih"
  shows "Fmap (ii \<circ> ih \<circ> ig) x = Fmap ii (Fmap ih (Fmap ig x))"
proof -
  have comp_type: "((i : I) \<Rightarrow> iIn i \<Rightarrow> iMid2 i) (ih \<circ> ig)" using assms by fastforce
  from Fmap_comp have "Fmap ii (Fmap ih (Fmap ig x)) = Fmap ii (Fmap (ih \<circ> ig) x)"
    using assms by fastforce
  also from Fmap_comp have "... = Fmap (ii \<circ> ih \<circ> ig) x"
    using comp_type assms comp_ifun_assoc[of ii ih ig] by fastforce
  finally show "Fmap (ii \<circ> ih \<circ> ig) x = Fmap ii (Fmap ih (Fmap ig x))" ..
qed

paragraph \<open>Relator\<close>
  (* locale 't 'f set *)
definition "Frel (iR :: 'i \<Rightarrow> f \<Rightarrow> f \<Rightarrow> bool) x y \<equiv> \<exists>z.
  F (\<lambda>i. is_pair \<sqinter> uncurry (iR i)) z
  \<and> Fmap (K fst) z = x
  \<and> Fmap (K snd) z = y"

lemma FrelI:
  assumes "F (\<lambda>i. is_pair \<sqinter> uncurry (iR i)) z"
    and "Fmap (K fst) z = x"
    and "Fmap (K snd) z = y"
  shows "Frel iR x y"
  unfolding Frel_def using assms by force

lemma FrelE:
  assumes "Frel iR x y"
  obtains z where "F (\<lambda>i. is_pair \<sqinter> uncurry (iR i)) z"
    and "Fmap (K fst) z = x" and "Fmap (K snd) z = y"
  using assms Frel_def by fastforce

definition "Graph_on P f \<equiv> \<lambda>x y. y = f x \<and> P x"

lemma Graph_onI [intro]: "\<lbrakk>y = f x; P x\<rbrakk> \<Longrightarrow> Graph_on P f x y"
  unfolding Graph_on_def by auto

lemma Graph_onE [elim]:
  assumes "Graph_on P f x y"
  obtains "P x" "y = f x"
  using assms unfolding Graph_on_def by auto

definition "Graph \<equiv> Graph_on \<top>"

lemma Graph_eq_Graph_on: "Graph = Graph_on \<top>"
  unfolding Graph_def ..

lemma Graph_eq_Graph_on_uhint [uhint]:
  assumes "P \<equiv> (\<top> :: 'a \<Rightarrow> bool)"
  shows "Graph :: ('a \<Rightarrow> 'b) \<Rightarrow> _ \<equiv> Graph_on P"
  using assms by (simp add: Graph_eq_Graph_on)

lemma GraphI [intro]:
  assumes "y = f x"
  shows "Graph f x y"
  using assms by (urule Graph_onI) simp

lemma GraphD [dest]:
  assumes "Graph f x y"
  shows "y = f x"
  using assms by (urule (e) Graph_onE)

lemma Graph_eq_eq_comp [simp]: "Graph f = (=) \<circ> f"
  by (intro ext) auto

lemma Graph_id_eq_eq [simp]: "Graph id = (=)"
  by auto

definition "convol f g \<equiv> \<lambda>x. \<langle>f x, g x\<rangle>"

lemma convol_eq [simp]: "convol f g \<equiv> \<lambda>x. \<langle>f x, g x\<rangle>"
  unfolding convol_def by simp

lemma mono_mono_wrt_mono_wrt_convol: "((A \<Rightarrow> B) \<Rightarrow> (A \<Rightarrow> C) \<Rightarrow> (A :: 'a \<Rightarrow> bool) \<Rightarrow> B \<times> C) convol"
  unfolding convol_def by fastforce

lemma fst_comp_convol_eq [simp]: "fst \<circ> (convol f g) = f" by auto
lemma snd_comp_convol_eq [simp]: "snd \<circ> (convol f g) = g" by auto

lemma Fx_imp_F_in_dom_Graph_x:
  assumes x_type: "F iIn x"
  shows "F (\<lambda>i. in_dom (Graph (ig i))) x"
proof-
  have "(I \<Rrightarrow> (\<le>)) iIn (\<lambda>i. in_dom (Graph (ig i)))" by fastforce
  with F_type_if_leq x_type show "F (\<lambda>i. in_dom (Graph (ig i))) x" by auto
qed


lemma Graph_Fmap_eq_Frel_GraphI:
  assumes ig_type: "((i : I) \<Rightarrow> iIn i \<Rightarrow> iOut i) ig"
  shows "(F iIn \<Rrightarrow> F iOut \<Rrightarrow> (=)) (Graph (Fmap ig)) (Frel (\<lambda>i. Graph (ig i)))"
proof (intro Fun_Rel_predI iffI)
  fix x y assume  "F iIn x" and "Graph (Fmap ig) x y"
  then have y_eq: "y = Fmap ig x" by simp
  from \<open>F iIn x\<close> Fx_imp_F_in_dom_Graph_x have x_type: "F (\<lambda>i. in_dom (Graph (ig i))) x" by blast
  have convol_type:"((i : I) \<Rightarrow> in_dom (Graph (ig i)) \<Rightarrow> is_pair \<sqinter> uncurry (Graph (ig i))) (\<lambda>i. convol id (ig i))" by fastforce
  show "Frel (\<lambda>i. Graph (ig i)) x y"
  proof (intro FrelI[where z="Fmap (\<lambda>i. convol id (ig i)) x"])
    from convol_type x_type show "F (\<lambda>i. is_pair \<sqinter> uncurry (Graph (ig i))) (Fmap (\<lambda>i. convol id (ig i)) x)" using Fmap_type by fastforce
  next
    have map_convol_eq: "Fmap (K f) (Fmap (\<lambda>i. convol id (ig i)) x) =
      Fmap ((\<lambda>(_ :: 'i). f) \<circ> (\<lambda>i. convol id (ig i))) x" for f
      using Fmap_comp x_type convol_type by fastforce
    moreover have "Fmap ((\<lambda>(_ :: 'i). fst) \<circ> (\<lambda>i. convol id (ig i))) x = Fmap (\<lambda>(_ :: 'i). id) x"
      using x_type by (intro Fmap_cong Dep_Fun_Rel_predI) auto
    ultimately show "Fmap (K fst) (Fmap (\<lambda>i. convol id (ig i)) x) = x" using Fmap_id x_type by fastforce
    have "Fmap ((\<lambda>(_ :: 'i). snd) \<circ> (\<lambda>i. convol id (ig i))) x = y"
      unfolding y_eq using x_type by (intro Fmap_cong Dep_Fun_Rel_predI) auto
    with map_convol_eq show "Fmap (K snd) (Fmap (\<lambda>i. convol id (ig i)) x) = y" by auto
  qed
next
  fix x y assume "F iIn x"
  assume Frel_x_y: "Frel (\<lambda>i. Graph (ig i)) x y"
  then obtain z
    where z_type: "F (\<lambda>i. is_pair \<sqinter> uncurry (Graph (ig i))) z"
      and x_eq: "Fmap (K fst) z = x"
      and y_eq: "Fmap (K snd) z = y" by (blast elim: FrelE)
  from \<open>F iIn x\<close> Fx_imp_F_in_dom_Graph_x have x_type: "F (\<lambda>i. in_dom (Graph (ig i))) x" by blast
  have ig_comp_fst_eq_snd:"Fmap (ig \<circ> K fst) z = Fmap (K snd) z"
  proof (intro Fmap_cong)
    show "F (\<lambda>i. is_pair \<sqinter> uncurry (Graph (ig i))) z" using z_type by blast
    show "((i : I) \<Rightarrow> is_pair \<sqinter> uncurry (Graph (ig i)) \<Rightarrow> in_dom (Graph (ig i))) (ig \<circ> K fst)" by fastforce
    show "((i : I) \<Rightarrow> is_pair \<sqinter> uncurry (Graph (ig i)) \<Rightarrow> in_codom (Graph (ig i))) (K snd)" by fastforce
    show "((i : I) \<Rrightarrow> Fpred i z \<Rrightarrow> (=)) (ig \<circ> K fst) (K snd)" proof
      fix i assume "I i"
      then show "(Fpred i z \<Rrightarrow> (=)) ((ig \<circ> K fst) i) (K snd i)"
      proof(intro Fun_Rel_predI)
        fix p assume "Fpred i z p"
        have "Fpred i z \<le> is_pair \<sqinter> uncurry (Graph (ig i))" 
          using \<open>I i\<close> Fpred_type[of "\<lambda>i. is_pair \<sqinter> uncurry (Graph (ig i))"] z_type by auto
        with \<open>Fpred i z p\<close> have "(is_pair \<sqinter> uncurry (Graph (ig i))) p" using Frel_x_y z_type by blast
        then show "(ig \<circ> K fst) i p = (K snd) i p" by auto
      qed
    qed
  qed
  have "((i : I) \<Rightarrow> is_pair \<sqinter> uncurry (Graph (ig i)) \<Rightarrow> in_dom (Graph (ig i))) (K fst)" by fastforce
  then have "Fmap ig (Fmap (K fst) z) = Fmap (ig \<circ> (K fst)) z"
    using Fmap_comp[of "\<lambda>i. is_pair \<sqinter> uncurry (Graph (ig i))" "\<lambda>i. in_dom (Graph (ig i))" "K fst" "\<lambda>i. in_codom (Graph (ig i))" ig] z_type by fastforce
  with ig_comp_fst_eq_snd have "Fmap ig (Fmap (K fst) z) = Fmap (K snd) z" by blast
  with x_eq y_eq show "Graph (Fmap ig) x y" by simp
qed

corollary Frel_Graph_FmapI:
  assumes "((i : I) \<Rightarrow> iIn i \<Rightarrow> iOut i) ig"
    and "F iIn x"
  shows "Frel (\<lambda>i. Graph (ig i)) x (Fmap ig x)"
  using assms Fmap_type Graph_Fmap_eq_Frel_GraphI by fastforce

lemma Graph_Fmap_eq_Graph_idI:
  assumes "(F iT \<Rrightarrow> (=)) (Fmap ig) id"
  shows "(F iT \<Rrightarrow> F iT \<Rrightarrow> (=)) (Graph (Fmap ig)) (Graph id)"
  using assms by fastforce

lemma Frel_K_eq_eq_eq: "(F iT \<Rrightarrow> F iT \<Rrightarrow> (=)) (Frel (K (=))) (=)"
proof -
  from Graph_Fmap_eq_Frel_GraphI have "(F iT \<Rrightarrow> F iT \<Rrightarrow> (=)) (Graph (Fmap iid)) (Frel (K (Graph id)))"
    using mono_iid by fastforce
  then have "(F iT \<Rrightarrow> F iT \<Rrightarrow> (=)) (Graph id) (Frel (K (=)))"
    using Fmap_id[where ig=iid] Graph_Fmap_eq_Graph_idI by fastforce
  then show ?thesis by auto
qed

lemma mono_mono_wrt_le_le_Frel: "((I \<Rrightarrow> (\<le>)) \<Rightarrow> (\<le>)) Frel"
proof (intro mono_wrt_relI le_relI)
  fix iR iS assume iR_iS:"(I \<Rrightarrow> (\<le>)) (iR::'i \<Rightarrow> set \<Rightarrow> set \<Rightarrow> bool) iS"
  fix x y assume "Frel iR x y"
  then obtain z where z_type:"F (\<lambda>i. is_pair \<sqinter> uncurry (iR i)) z"
    and "Fmap (K fst) z = x" and "Fmap (K snd) z = y" by (elim FrelE)
  then show "Frel iS x y" proof(intro FrelI[where z=z])
    from iR_iS have "(I \<Rrightarrow> (\<le>)) (\<lambda>i. is_pair \<sqinter> uncurry (iR i)) (\<lambda>i. is_pair \<sqinter> uncurry (iS i))"
      by fastforce
    then show "F (\<lambda>i. is_pair \<sqinter> uncurry (iS i)) z" using z_type F_type_if_leq by auto
  qed auto
qed

end

definition "pick_middlep P Q a c \<equiv> SOME b. P a b \<and> Q b c"

lemma pick_middlep_and_pick_middlep_if_rel_comp:
  "(P \<circ>\<circ> Q) a c \<Longrightarrow> P a (pick_middlep P Q a c) \<and> Q (pick_middlep P Q a c) c"
  unfolding pick_middlep_def by (rule someI_ex) auto

lemma pick_middlep_and_pick_middlep_if_rel_compE:
  assumes "(P \<circ>\<circ> Q) a c"
  obtains "P a (pick_middlep P Q a c)" "Q (pick_middlep P Q a c) c"
  using assms pick_middlep_and_pick_middlep_if_rel_comp by force

definition "fstOp P Q p \<equiv> \<langle>fst p, pick_middlep P Q (fst p) (snd p)\<rangle>"
definition "sndOp P Q p \<equiv> \<langle>pick_middlep P Q (fst p) (snd p), (snd p)\<rangle>"

lemma fst_comp_fstOp_eq_fst: "fst \<circ> fstOp P Q = fst"
  unfolding fstOp_def by (intro ext) simp

lemma snd_comp_sndOp_eq_snd: "snd \<circ> sndOp P Q = snd"
  unfolding sndOp_def by (intro ext) simp

locale HOTG_Natural_Functor_Subdist = HOTG_Natural_Functor +
  assumes Frel_comp_Frel_le_Frel_comp:
    "\<And>iT1 iT2 iR iS. (F iT1 \<Rrightarrow> F iT2 \<Rrightarrow> (\<le>)) (Frel iR \<circ>\<circ> Frel iS) (Frel (iR \<circ>\<circ> iS))"
begin


lemma Frel_comp_le_Frel_comp_Frel: "(F iT1 \<Rrightarrow> F iT2 \<Rrightarrow> (\<le>)) (Frel (iR \<circ>\<circ> iS)) (Frel iR \<circ>\<circ> Frel iS)"
proof (intro Fun_Rel_predI le_boolI)
  fix x y assume "F iT1 x" "F iT2 y" "Frel (iR \<circ>\<circ> iS) x y"
  then obtain z where z_type: "F (\<lambda>i. is_pair \<sqinter> uncurry (iR i \<circ>\<circ> iS i)) z"
    and x_eq: "Fmap (K fst) z = x" and y_eq:"Fmap (K snd) z = y" by (elim FrelE) auto
  show "(Frel iR \<circ>\<circ> Frel iS) x y"
  proof (rule rel_compI, rule FrelI)
    have fst_op_type: "((i : I) \<Rightarrow> (is_pair \<sqinter> uncurry (iR i \<circ>\<circ> iS i)) \<Rightarrow>
        (is_pair \<sqinter> uncurry (iR i))) (\<lambda>i. fstOp (iR i) (iS i))"
      unfolding fstOp_def by (fastforce elim: pick_middlep_and_pick_middlep_if_rel_compE)   
    have fst_type: "((i : I) \<Rightarrow> (is_pair \<sqinter> uncurry (iR i)) \<Rightarrow> in_dom (iR i)) (K fst)"
      by (intro dep_mono_wrt_predI mono_wrt_predI) auto
    have snd_type: "((i : I) \<Rightarrow> (is_pair \<sqinter> uncurry (iR i)) \<Rightarrow> in_codom (iR i)) (K snd)"
      by (intro dep_mono_wrt_predI mono_wrt_predI) auto
    from fst_op_type z_type show "F (\<lambda>i. is_pair \<sqinter> uncurry (iR i)) (Fmap (\<lambda>i. fstOp (iR i) (iS i)) z)"
      using Fmap_type by fast
    from fst_type z_type fst_op_type fst_comp_fstOp_eq_fst have
      "Fmap (K fst) (Fmap (\<lambda>i. fstOp (iR i) (iS i)) z) = Fmap (comp_ifun (K fst) (\<lambda>i. fstOp (iR i) (iS i))) z"
      using Fmap_comp[where ig="\<lambda>i. fstOp (iR i) (iS i)" and ih="K fst"] by fastforce
    also have "... = Fmap (K fst) z" using z_type fst_comp_fstOp_eq_fst by (intro Fmap_cong) fastforce+
    finally show "Fmap (K fst) (Fmap (\<lambda>i. fstOp (iR i) (iS i)) z) = x" using x_eq by blast
    from snd_type z_type fst_op_type have "Fmap (K snd) (Fmap (\<lambda>i. fstOp (iR i) (iS i)) z) = 
           Fmap (comp_ifun (K snd) (\<lambda>i. fstOp (iR i) (iS i))) z"
      using Fmap_comp[where ig="\<lambda>i. fstOp (iR i) (iS i)"] by fastforce
    also have "... = Fmap (\<lambda>i. snd \<circ> fstOp (iR i) (iS i)) z" unfolding fstOp_def
      using z_type pick_middlep_and_pick_middlep_if_rel_comp 
      by (intro Fmap_cong[where iIn="\<lambda>i. is_pair \<sqinter> uncurry (iR i \<circ>\<circ> iS i)"]) fastforce+
    finally show "Fmap (K snd) (Fmap (\<lambda>i. fstOp (iR i) (iS i)) z) = Fmap (\<lambda>i. snd \<circ> fstOp (iR i) (iS i)) z" .
  next
    show "Frel iS (Fmap (\<lambda>i. snd \<circ> fstOp (iR i) (iS i)) z) y"
    proof(intro FrelI[where z="Fmap (\<lambda>i. sndOp (iR i) (iS i)) z"])
      have snd_type:"((i : I) \<Rightarrow> (is_pair \<sqinter> uncurry (iR i)) \<Rightarrow> in_codom (iR i)) (K snd)"
        by fastforce
      have snd_op_type: "((i : I) \<Rightarrow> (is_pair \<sqinter> uncurry (iR i \<circ>\<circ> iS i)) \<Rightarrow>
         (is_pair \<sqinter> uncurry (iS i))) (\<lambda>i. sndOp (iR i) (iS i))"
        unfolding sndOp_def by(fastforce elim: pick_middlep_and_pick_middlep_if_rel_compE)
      with z_type show "F (\<lambda>i. is_pair \<sqinter> uncurry (iS i)) (Fmap (\<lambda>i. sndOp (iR i) (iS i)) z)"
        using Fmap_type by fast
      have fst_type: "((i : I) \<Rightarrow> is_pair \<sqinter> uncurry (iS i) \<Rightarrow> in_dom (iS i)) (K fst)"
        by fastforce
      with snd_op_type z_type have "Fmap (K fst) (Fmap (\<lambda>i. sndOp (iR i) (iS i)) z) =
          Fmap (comp_ifun (K fst) (\<lambda>i. sndOp (iR i) (iS i))) z"
        using Fmap_comp by fastforce
      also have "... = Fmap (\<lambda>i. snd \<circ> fstOp (iR i) (iS i)) z" unfolding fstOp_def
        using z_type sndOp_def by(intro Fmap_cong) fastforce+
      finally show "Fmap (K fst) (Fmap (\<lambda>i. sndOp (iR i) (iS i)) z) = Fmap (\<lambda>i. snd \<circ> fstOp (iR i) (iS i)) z" .
      have "Fmap (K snd) (Fmap (\<lambda>i. sndOp (iR i) (iS i)) z) = Fmap (comp_ifun (K snd) (\<lambda>i. sndOp (iR i) (iS i))) z"
        using z_type Fmap_comp by fastforce
      also have "... = Fmap (\<lambda>i. snd \<circ> sndOp (iR i) (iS i)) z" using z_type
        by (intro Fmap_cong[where iIn="\<lambda>i. is_pair \<sqinter> uncurry (iR i \<circ>\<circ> iS i)"]) fastforce+
      finally show "Fmap (K snd) (Fmap (\<lambda>i. sndOp (iR i) (iS i)) z) = y"
        using snd_comp_sndOp_eq_snd y_eq by auto
    qed
  qed
qed

corollary Frel_comp_eq_Frel_comp_Frel: "(F iT1 \<Rrightarrow> F iT2 \<Rrightarrow> (=)) (Frel (iR \<circ>\<circ> iS)) (Frel iR \<circ>\<circ> Frel iS)"
  using Frel_comp_le_Frel_comp_Frel Frel_comp_Frel_le_Frel_comp by fast

end

context HOTG_Natural_Functor
begin


definition "algebra irec T s \<equiv> \<forall>iT. (I \<Rrightarrow> (=)) iT ((K \<top>)(irec := T)) \<longrightarrow> (F iT \<Rightarrow> T) s"

lemma algebraI:
  assumes "\<forall>iT. (I \<Rrightarrow> (=)) iT ((K \<top>)(irec := T)) \<longrightarrow> (F iT \<Rightarrow> T) s"
  shows "algebra irec T s"
  unfolding algebra_def using assms .

lemma algebraE:
  assumes "algebra irec T s"
  shows "\<forall>iT. (I \<Rrightarrow> (=)) iT ((K \<top>)(irec := T)) \<longrightarrow> (F iT \<Rightarrow> T) s"
  using assms unfolding algebra_def .

lemma algebra_fpred:
  assumes "algebra irec T s"
  assumes "F ((K \<top>)(irec := T)) x"
  shows "T (s x)"
  using assms algebraE by fastforce

(* needed?
lemma algebra_not_empty:
  assumes "algebra irec T s"
  shows "T \<noteq> \<bottom>"
  sorry
*)

definition "morphism irec T T' s s' f = (((T \<Rightarrow> T') f) \<and> (\<forall>iT. (I \<Rrightarrow> (=)) iT ((K \<top>)(irec := T)) \<longrightarrow>
          (F iT \<Rrightarrow> (=)) (f \<circ> s) (s' \<circ> (Fmap (iid(irec := f))))))"

lemma morphismI:
  assumes "((T \<Rightarrow> T') f)"
    and   "\<And>iT. (I \<Rrightarrow> (=)) iT ((K \<top>)(irec := T)) \<Longrightarrow>
          (F iT \<Rrightarrow> (=)) (f \<circ> s) (s' \<circ> (Fmap (iid(irec := f))))"
  shows "morphism irec T T' s s' f"
  using assms unfolding morphism_def by blast

lemma morphismE:
  assumes "morphism irec T T' s s' f"
  shows  "(T \<Rightarrow> T') f" and "(\<forall>iT. (I \<Rrightarrow> (=)) iT ((K \<top>)(irec := T)) \<longrightarrow>
          (F iT \<Rrightarrow> (=)) (f \<circ> s) (s' \<circ> (Fmap (iid(irec := f)))))"
  using assms unfolding morphism_def by auto

lemma morphismE_alt:
  assumes "((T \<Rightarrow> T') f)"
    and "(I \<Rrightarrow> (=)) iT ((K \<top>)(irec := T))"
    and "F iT z"
    and "morphism irec T T' s s' f"
  shows "f (s z) = s' (Fmap (iid(irec := f)) z)"
  using assms morphismE by fastforce

lemma morphism_inclusion:
  assumes "T \<le> T'"
  shows "morphism irec T T' s s id"
proof (intro morphismI)
  from assms show "(T \<Rightarrow> T') id" by fastforce
  fix iT assume "(I \<Rrightarrow> (=)) iT ((K \<top>)(irec := T))"
  show "(F iT \<Rrightarrow> (=)) (id \<circ> s) (s \<circ> Fmap (iid(irec := id)))"
  proof
    fix x assume "F iT x"
    have "((i : I) \<Rrightarrow> iT i \<Rrightarrow> (=)) (iid(irec:=id)) iid" by fastforce
    with \<open>F iT x\<close> show "(id \<circ> s) x = (s \<circ> Fmap (iid(irec := id))) x" using Fmap_id by fastforce
  qed
qed

lemma morphism_composition:
  assumes "morphism irec T1 T2 s1 s2 f"
    and "morphism irec T2 T3 s2 s3 g"
  shows "morphism irec T1 T3 s1 s3 (g \<circ> f)"
proof (intro morphismI)
  have "(T1 \<Rightarrow> T2) f" using assms morphismE by fastforce
  moreover have "(T2 \<Rightarrow> T3) g" using assms morphismE by fastforce
  ultimately show "(T1 \<Rightarrow> T3) (g \<circ> f)" by fastforce
  fix iT assume iT_eq: "(I \<Rrightarrow> (=)) iT ((K \<top>)(irec := T1))"
  show "(F iT \<Rrightarrow> (=)) (g \<circ> f \<circ> s1) (s3 \<circ> Fmap (iid(irec := g \<circ> f)))"
  proof
    fix x assume "F iT x"
    with iT_eq assms(1) morphismE have "(f \<circ> s1) x = (s2 \<circ> (Fmap (iid(irec := f)))) x" by fastforce
    then have gfs1:"(g \<circ> f \<circ> s1) x = (g \<circ> s2 \<circ> (Fmap (iid(irec := f)))) x" by auto
    have f_type:"((i : I) \<Rightarrow> iT i \<Rightarrow> (iT(irec := T2)) i) (iid(irec:=f))"
    proof (intro dep_mono_wrt_predI mono_wrt_predI)
      fix i x assume "I i" and "iT i x"
      show "(iT(irec := T2)) i ((iid(irec := f)) i x)" proof (cases "i = irec")
        case True
        from assms morphismE \<open>iT i x\<close> True \<open>I i\<close> iT_eq show ?thesis by fastforce
      next
        case False
        with \<open>iT i x\<close> show ?thesis by auto
      qed
    qed
    with Fmap_type \<open>F iT x\<close> have "F (iT(irec := T2)) (Fmap (iid(irec := f)) x)" by fastforce
    moreover from iT_eq have "(I \<Rrightarrow> (=)) (iT(irec := T2)) ((K \<top>)(irec := T2))" by fastforce
    ultimately have gs2f: "g (s2 (Fmap (iid(irec := f)) x)) =
          s3 (Fmap (iid(irec := g)) (Fmap (iid(irec := f)) x))" using assms(2) morphismE by fastforce
    have g_type:"((i : I) \<Rightarrow> (iT(irec := T2)) i\<Rightarrow> (iT(irec := T3)) i) (iid(irec := g))"
      using mono_upd_iid assms morphismE by fastforce
    with Fmap_comp \<open>F iT x\<close> f_type have "Fmap (iid(irec := g)) (Fmap (iid(irec := f)) x) =
           Fmap (iid(irec := g) \<circ> iid(irec := f)) x" by fastforce
    with \<open>F iT x\<close> f_type g_type
      Fmap_cong[of _ _ _ "iid(irec := g) \<circ> iid(irec := f)" "(iT(irec := T3))" "iid(irec := g \<circ> f)"]
    also have "... = Fmap (iid(irec := g \<circ> f)) x" by fastforce
    ultimately have "Fmap (iid(irec := g)) (Fmap (iid(irec := f)) x) = Fmap (iid(irec := g \<circ> f)) x" by blast
    with gs2f gfs1 show "(g \<circ> f \<circ> s1) x = (s3 \<circ> Fmap (iid(irec := g \<circ> f))) x" by fastforce
  qed
qed



lemma morphism_cong:
  assumes "(T \<Rrightarrow> (=)) f f'"
    and "morphism irec T T' s s' f"
  shows "morphism irec T T' s s' f'"
proof (intro morphismI)
  show "(T \<Rightarrow> T') f'" using assms morphismE by fastforce
  fix iT assume iT_eq:"(I \<Rrightarrow> (=)) iT ((K \<top>)(irec := T))"
  show "(F iT \<Rrightarrow> (=)) (f' \<circ> s) (s' \<circ> Fmap (iid(irec := f')))"
  proof
    fix x assume "F iT x"
      (* this step needs type information about s *)
    from assms morphismE have "T (s x)" sorry
    with assms have f_eq:"f' (s x) = f (s x)" by auto
    moreover have maps_eq:"Fmap (iid(irec := f)) x = Fmap (iid(irec := f')) x"
    proof (intro Fmap_cong[where iIn=iT and ?iOut1.0="(iT(irec := T'))" and ?iOut2.0="(iT(irec := T'))"])
      show "F iT x" using \<open>F iT x\<close> by auto
      show "((i : I) \<Rightarrow> iT i \<Rightarrow> (iT(irec := T')) i) (iid(irec := f))" using mono_upd_iid iT_eq assms morphismE(1) by fastforce
      show "((i : I) \<Rightarrow> iT i \<Rightarrow> (iT(irec := T')) i) (iid(irec := f'))" using mono_upd_iid iT_eq assms morphismE(1) by fastforce
      show "((i : I) \<Rrightarrow> Fpred i x \<Rrightarrow> (=)) (iid(irec := f)) (iid(irec := f'))"
      proof (intro Dep_Fun_Rel_predI Fun_Rel_predI)
        fix i y assume "I i"  "Fpred i x y"
        show "(iid(irec := f)) i y = (iid(irec := f')) i y"
        proof (cases "i = irec")
          case True
          then have "Fpred i x \<le> T" using Fpred_type \<open>F iT x\<close> iT_eq \<open>I i\<close> by fastforce
          with assms \<open>Fpred i x y\<close> show ?thesis by fastforce
        next
          case False
          then show ?thesis by auto
        qed
      qed
    qed
    from f_eq maps_eq[symmetric] \<open>F iT x\<close> assms morphismE iT_eq show "(f' \<circ> s) x = (s' \<circ> Fmap (iid(irec := f'))) x" by fastforce
  qed
qed
end

end