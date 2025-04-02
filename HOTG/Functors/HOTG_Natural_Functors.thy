\<^marker>\<open>creator "Kevin Kappelmann"\<close>
\<^marker>\<open>creator "Nils Harmsen"\<close>
subsection \<open>Locales and Constructions\<close>
theory HOTG_Natural_Functors
  imports
    Hilbert_Epsilon_Choice
    HOTG_Functors_Base
    HOTG_Functions_Lambda
    Transport.Binary_Relations_Graph
begin

paragraph \<open>Summary\<close>
text \<open>Functors and natural functors following the construction outlined in \<^cite>\<open>cardinals_in_hol\<close>
and \<^cite>\<open>"BNF_Operations-AFP"\<close>.\<close>

unbundle no HOL_ascii_syntax

paragraph \<open>Basic functors\<close>

locale Functor =
  fixes F :: "('i \<Rightarrow> 't \<Rightarrow> bool) \<Rightarrow> 'f \<Rightarrow> bool"
  and I :: "'i \<Rightarrow> bool"
  \<comment>\<open>The type parameters of a functor are specified by a function from a given index type \<open>'i\<close>
  subject to a restriction predicate @{term I}. In particular, a functor may have an infinite
  number of type parameters.\<close>
  and Fmap :: "('i \<Rightarrow> 't \<Rightarrow> 't) \<Rightarrow> 'f \<Rightarrow> 'f"
  assumes Fmap_type: "\<And>iIn iOut. (((i : I) \<Rightarrow> iIn i \<Rightarrow> iOut i) \<Rightarrow> F iIn \<Rightarrow> F iOut) Fmap"
  and Fmap_id: "\<And>(iT :: 'i \<Rightarrow> 't \<Rightarrow> bool) (ig :: 'i \<Rightarrow> 't \<Rightarrow> 't).
    ((i : I) \<Rrightarrow> iT i \<Rrightarrow> (=)) ig iid \<Longrightarrow> (F iT \<Rrightarrow> (=)) (Fmap ig) id"
  and Fmap_comp: "\<And>ig ih. (F (K \<top>) \<Rrightarrow> (=)) (Fmap (ih \<circ> ig)) (Fmap ih \<circ> Fmap ig)"
begin

lemma Fmap_iid_eq_selfI [simp]:
  assumes "F iT x"
  shows "Fmap iid x = id x"
  using assms Fmap_id by blast

lemma F_if_le_if_F:
  assumes x_type: "F iT x"
  and iT_leq_iS: "(I \<Rrightarrow> (\<le>)) iT iS"
  shows "F iS x"
proof -
  from iT_leq_iS have "((i : I) \<Rightarrow> iT i \<Rightarrow> iS i) iid" by fastforce
  with x_type Fmap_type show ?thesis by fastforce
qed

corollary mono_Fun_Rel_le_le_F: "((I \<Rrightarrow> (\<le>)) \<Rightarrow> (\<le>)) F"
  using F_if_le_if_F by fastforce

corollary F_K_top_if_F [intro]:
  assumes "F iT x"
  shows "F (K \<top>) x"
  using assms by (rule F_if_le_if_F) auto

lemma Fmap_comp_eq_Fmap_Fmap [simp]:
  assumes "F iT x"
  shows "Fmap (ih \<circ> ig) x = Fmap ih (Fmap ig x)"
  using assms Fmap_comp by fastforce

lemma Fmap_comp_comp_eq_Fmap_Fmap_Fmap:
  assumes "F iT x"
  shows "Fmap (ii \<circ> ih \<circ> ig) x = Fmap ii (Fmap ih (Fmap ig x))"
proof -
  from assms have "Fmap ii (Fmap ih (Fmap ig x)) = Fmap ii (Fmap (ih \<circ> ig) x)" by auto
  also from assms have "... = Fmap (ii \<circ> ih \<circ> ig) x" using comp_ifun_assoc[of ii ih ig] by fastforce
  finally show ?thesis ..
qed

end


definition "pick_middlep R S a c \<equiv> SOME b. R a b \<and> S b c"

lemma pick_middlep_and_pick_middlep_if_rel_comp:
  "(R \<circ>\<circ> S) a c \<Longrightarrow> R a (pick_middlep R S a c) \<and> S (pick_middlep R S a c) c"
  unfolding pick_middlep_def by (rule someI_ex) auto

lemma pick_middlep_pick_middlepE:
  assumes "(R \<circ>\<circ> S) a c"
  obtains "R a (pick_middlep R S a c)" "S (pick_middlep R S a c) c"
  using assms pick_middlep_and_pick_middlep_if_rel_comp by force

definition "fst_pick_middlep R S p \<equiv> \<langle>fst p, uncurry (pick_middlep R S) p\<rangle>"
definition "snd_pick_middlep R S p \<equiv> \<langle>uncurry (pick_middlep R S) p, snd p\<rangle>"

lemma fst_pick_middlep_eq: "fst_pick_middlep R S p \<equiv> \<langle>fst p, uncurry (pick_middlep R S) p\<rangle>"
  unfolding fst_pick_middlep_def by simp

lemma snd_pick_middlep_eq: "snd_pick_middlep R S p \<equiv> \<langle>uncurry (pick_middlep R S) p, snd p\<rangle>"
  unfolding snd_pick_middlep_def by simp

corollary fst_fst_pick_middlep_eq_fst [simp]: "fst (fst_pick_middlep R S p) = fst p"
  unfolding fst_pick_middlep_eq by simp

lemma fst_comp_fst_pick_middlep_eq_fst: "fst \<circ> fst_pick_middlep R S = fst"
  by (intro ext) auto

lemma snd_snd_pick_middlep_eq_snd [simp]: "snd (snd_pick_middlep R S p) = snd p"
  unfolding snd_pick_middlep_eq by simp

lemma snd_comp_snd_pick_middlep_eq_snd: "snd \<circ> snd_pick_middlep R S = snd"
  by (intro ext) simp

lemma snd_comp_fst_pick_middlep_eq_fst_comp_snd_pick_middlep:
  "snd \<circ> fst_pick_middlep R S = fst \<circ> snd_pick_middlep R S"
  unfolding fst_pick_middlep_eq snd_pick_middlep_eq by (intro ext) simp

subsubsection \<open>Set Functors\<close>

locale HOTG_Functor = Functor _ _ "Fmap :: ('i \<Rightarrow> set \<Rightarrow> set) \<Rightarrow> set \<Rightarrow> set" for Fmap
begin

type_synonym t = set
type_synonym f = set

paragraph \<open>Relator\<close>

definition "Frel (iR :: 'i \<Rightarrow> t \<Rightarrow> t \<Rightarrow> bool) x y \<equiv>
  \<exists>z :  F (\<lambda>i. is_pair \<sqinter> uncurry (iR i)). x = Fmap (K fst) z \<and> y = Fmap (K snd) z"

lemma FrelI:
  assumes "F (\<lambda>i. is_pair \<sqinter> uncurry (iR i)) z"
  and "x = Fmap (K fst) z"
  and "y = Fmap (K snd) z"
  shows "Frel iR x y"
  unfolding Frel_def using assms by force

lemma FrelE:
  assumes "Frel iR x y"
  obtains z where "F (\<lambda>i. is_pair \<sqinter> uncurry (iR i)) z" and "x = Fmap (K fst) z" "y = Fmap (K snd) z"
  using assms Frel_def by fastforce

lemma FrelE':
  assumes "Frel iR x y"
  obtains z where "F (\<lambda>i. is_pair \<sqinter> uncurry (iR i)) z"
  and "F (\<lambda>i. in_dom (iR i)) x" "F (\<lambda>i. in_codom (iR i)) y"
  and "x = Fmap (K fst) z" "y = Fmap (K snd) z"
proof -
  let ?pair_iR = "\<lambda>i. is_pair \<sqinter> uncurry (iR i)"
  have fst_snd: "((i : I) \<Rightarrow> ?pair_iR i \<Rightarrow> in_dom (iR i)) (K fst)"
    "((i : I) \<Rightarrow> ?pair_iR i \<Rightarrow> in_codom (iR i)) (K snd)" by fastforce+
  from assms obtain z where "F ?pair_iR z" "x = Fmap (K fst) z" "y = Fmap (K snd) z"
    by (auto elim: FrelE)
  moreover with fst_snd Fmap_type have "F (\<lambda>i. in_dom (iR i)) x" "F (\<lambda>i. in_codom (iR i)) y"
    by fastforce+
  ultimately show ?thesis using that by blast
qed

lemma mono_Fun_Rel_le_le_Frel: "((I \<Rrightarrow> (\<le>)) \<Rightarrow> (\<le>)) Frel"
  by (intro mono_wrt_relI le_relI, elim FrelE, intro FrelI)
  (fastforce intro: F_if_le_if_F)+

lemma Frel_Graph_on_if_Graph_on_Fmap:
  assumes "Graph_on (F iT) (Fmap ig) x y"
  shows "Frel (\<lambda>i. Graph_on (iT i) (ig i)) x y" (is "Frel ?iGraph _ _")
proof (rule FrelI)
  let ?pair_Graph = "\<lambda>i. is_pair \<sqinter> uncurry (?iGraph i)"
  let ?convol = "\<lambda>i. convol id (ig i)"
  have x_type: "F (\<lambda>i. in_dom (?iGraph i)) x" using assms by auto
  have "((i : I) \<Rightarrow> in_dom (?iGraph i) \<Rightarrow> ?pair_Graph i) ?convol" by fastforce
  then show "F ?pair_Graph (Fmap ?convol x)" using x_type Fmap_type by fastforce
  have map_convol_eq: "Fmap (K f) (Fmap ?convol x) = Fmap (comp_ifun (K f) ?convol) x" for f
    using x_type by fastforce
  moreover have "Fmap (comp_ifun (K fst) ?convol) x = Fmap iid x" (is "Fmap ?f x = Fmap ?g x")
  proof -
    have "?f = ?g" by fastforce
    then show ?thesis by simp
  qed
  moreover have "... = x" using x_type by simp
  ultimately show "x = Fmap (K fst) (Fmap ?convol x)" by simp
  have "Fmap (comp_ifun (K snd) ?convol) x = y" (is "Fmap ?f x = y")
  proof -
    have "?f = ig" by fastforce
    moreover from assms have "y = Fmap ig x" by auto
    ultimately show ?thesis by simp
  qed
  with map_convol_eq show "y = Fmap (K snd) (Fmap ?convol x)" by simp
qed

corollary Frel_Graph_on_Fmap_if_F:
  assumes "F iT x"
  shows "Frel (\<lambda>i. Graph_on (iT i) (ig i)) x (Fmap ig x)"
  using assms Frel_Graph_on_if_Graph_on_Fmap by fastforce

lemma Frel_eq_restrict_if_eq_restrict_F:
  assumes "x =\<^bsub>F iT\<^esub> y"
  shows "Frel (\<lambda>i. (=\<^bsub>iT i\<^esub>)) x y"
proof -
  from assms have "Graph_on (F iT) (Fmap iid) x y" by fastforce
  with Frel_Graph_on_if_Graph_on_Fmap have "Frel (\<lambda>i. Graph_on (iT i) (iid i)) x y" by auto
  then show ?thesis unfolding iid_eq_K_id by simp
qed

corollary Frel_K_eq_if_eq_if_F:
  assumes "F iT x"
  and "x = y"
  shows "Frel (K (=)) x y"
proof -
  from assms Frel_eq_restrict_if_eq_restrict_F have "Frel (\<lambda>i. (=\<^bsub>iT i\<^esub>)) x y" by blast
  moreover have "(I \<Rrightarrow> (\<le>)) (\<lambda>i. (=\<^bsub>iT i\<^esub>)) (K (=))" by fastforce
  ultimately show ?thesis using mono_Fun_Rel_le_le_Frel by blast
qed

lemma Frel_comp_le_Frel_comp_Frel: "(F iT1 \<Rrightarrow> F iT2 \<Rrightarrow> (\<le>)) (Frel (iR \<circ>\<circ> iS)) (Frel iR \<circ>\<circ> Frel iS)"
proof (intro Fun_Rel_predI le_boolI)
  let ?fpm = "\<lambda>i. fst_pick_middlep (iR i) (iS i)" and ?spm = "\<lambda>i. snd_pick_middlep (iR i) (iS i)"
  fix x y assume "F iT1 x" "F iT2 y" "Frel (iR \<circ>\<circ> iS) x y"
  then obtain z where z_type: "F (\<lambda>i. is_pair \<sqinter> uncurry (iR i \<circ>\<circ> iS i)) z"
    and x_eq: "x = Fmap (K fst) z" and y_eq: "y = Fmap (K snd) z" by (auto elim: FrelE)
  show "(Frel iR \<circ>\<circ> Frel iS) x y"
  proof (intro rel_compI FrelI)
    let ?z = "Fmap ?fpm z"
    have "((i : I) \<Rightarrow> (is_pair \<sqinter> uncurry (iR i \<circ>\<circ> iS i)) \<Rightarrow> (is_pair \<sqinter> uncurry (iR i))) ?fpm"
      unfolding fst_pick_middlep_eq by (fastforce elim: pick_middlep_pick_middlepE)
    then show "F (\<lambda>i. is_pair \<sqinter> uncurry (iR i)) ?z" using z_type Fmap_type by fast
    have K_fst_comp_fpm_eq: "comp_ifun (K fst) ?fpm = K fst" by fastforce
    moreover have "Fmap (K fst) ?z = Fmap (comp_ifun (K fst) ?fpm) z"
      using z_type by fastforce
    ultimately show "x = Fmap (K fst) ?z" using x_eq by simp
    have "Fmap (K snd) ?z = Fmap (comp_ifun (K snd) ?fpm) z" using z_type by fastforce
    moreover have "... = Fmap (\<lambda>i. snd \<circ> ?fpm i) z" unfolding comp_ifun_eq by simp
    ultimately show "Fmap (\<lambda>i. snd \<circ> ?fpm i) z = Fmap (K snd) ?z" by simp
  next
    let ?z = "Fmap ?spm z"
    have "((i : I) \<Rightarrow> (is_pair \<sqinter> uncurry (iR i \<circ>\<circ> iS i)) \<Rightarrow> (is_pair \<sqinter> uncurry (iS i))) ?spm"
      unfolding snd_pick_middlep_eq by (fastforce elim: pick_middlep_pick_middlepE)
    then show "F (\<lambda>i. is_pair \<sqinter> uncurry (iS i)) ?z" using z_type Fmap_type by fast
    have K_snd_comp_spm_eq: "comp_ifun (K snd) ?spm = K snd" by fastforce
    then have "Fmap (K fst) ?z = Fmap (comp_ifun (K fst) ?spm) z" using z_type by fastforce
    moreover have "... = Fmap (\<lambda>i. fst \<circ> ?spm i) z" unfolding comp_ifun_eq by simp
    moreover have "... = Fmap (\<lambda>i. snd \<circ> ?fpm i) z"
      unfolding snd_comp_fst_pick_middlep_eq_fst_comp_snd_pick_middlep by simp
    ultimately show "Fmap (\<lambda>i. snd \<circ> ?fpm i) z = Fmap (K fst) ?z" by simp
    have "Fmap (K snd) ?z = Fmap (comp_ifun (K snd) ?spm) z" using z_type by fastforce
    with K_snd_comp_spm_eq y_eq show "y = Fmap (K snd) ?z" using z_type by auto
  qed
qed

end

locale HOTG_Functor_Subdist = HOTG_Functor +
  assumes Frel_comp_Frel_le_Frel_comp:
    "\<And>iT1 iT2 iR iS. (F iT1 \<Rrightarrow> F iT2 \<Rrightarrow> (\<le>)) (Frel iR \<circ>\<circ> Frel iS) (Frel (iR \<circ>\<circ> iS))"
begin

lemma Frel_comp_eq_Frel_comp_Frel: "(F iT1 \<Rrightarrow> F iT2 \<Rrightarrow> (=)) (Frel (iR \<circ>\<circ> iS)) (Frel iR \<circ>\<circ> Frel iS)"
  using Frel_comp_le_Frel_comp_Frel Frel_comp_Frel_le_Frel_comp by fast

end

paragraph \<open>Functors with congruence\<close>

locale Functor_Cong = Functor _ _ Fmap
  for Fmap :: "('i \<Rightarrow> 't \<Rightarrow> 't) \<Rightarrow> 'f \<Rightarrow> 'f" +
  assumes Fun_Rel_eq_Fmap_Fmap: "\<And>iT. (((i : I) \<Rrightarrow> iT i \<Rrightarrow> (=)) \<Rrightarrow> F iT \<Rrightarrow> (=)) Fmap Fmap"
begin

lemma Fmap_cong:
  assumes "F iT x"
  and "\<And>i x. I i \<Longrightarrow> iT i x \<Longrightarrow> ig i x = ih i x"
  shows "Fmap ig x = Fmap ih x"
  using assms Fun_Rel_eq_Fmap_Fmap by blast

lemma Fmap_Fmap_eq_Fmap_comp_fun_upd_if_eq_idI:
  assumes x_type: "F iT x"
  and ig_id: "(iT i \<Rrightarrow> (=)) (ig i) id"
  shows "Fmap ih (Fmap ig x) = Fmap ((ih \<circ> ig)(i := ih i)) x"
proof -
  from assms have "Fmap ih (Fmap ig x) = Fmap (ih \<circ> ig) x" by fastforce
  also from x_type have "... = Fmap ((ih \<circ> ig)(i := ih i)) x"
  proof (rule Fmap_cong)
    fix j y assume "I j" "iT j y"
    with ig_id show "(ih \<circ> ig) j y = ((ih \<circ> ig)(i := ih i)) j y"
    by (cases "i = j") auto
  qed
  finally show ?thesis .
qed

lemma Fmap_eq_Fmap_fun_upd_if_eqI:
  assumes "F iT x"
  and ig_eq: "(iT i \<Rrightarrow> (=)) (ih i) (ig i)"
  shows "Fmap ig x = Fmap (ig(i := ih i)) x"
proof (rule Fmap_cong)
  fix j y assume "I j" "iT j y"
  with ig_eq show "ig j y = (ig(i := ih i)) j y" by (cases "i = j") auto
qed (intro assms)

end

locale HOTG_Functor_Cong = Functor_Cong F I Fmap + HOTG_Functor F I Fmap
  for F I and Fmap :: "('i \<Rightarrow> set \<Rightarrow> set) \<Rightarrow> set \<Rightarrow> set"
begin

lemma Graph_on_Fmap_if_Frel_Graph_on:
  assumes Frel_xy: "Frel (\<lambda>i. Graph_on (iT i) (ig i)) x y" (is "Frel ?iGraph _ _")
  shows "Graph_on (F iT) (Fmap ig) x y"
proof (rule Graph_on_if_eq_if_pred)
  let ?pair_Graph = "\<lambda>i. is_pair \<sqinter> uncurry (?iGraph i)"
  from Frel_xy obtain z where z_type: "F ?pair_Graph z" and x_eq: "x = Fmap (K fst) z"
    and y_eq: "y = Fmap (K snd) z" and "F iT x" by (fastforce elim: FrelE')
  then show "F iT x" by simp
  from x_eq have "Fmap ig x = Fmap ig (Fmap (K fst) z)" by simp
  also have "... = Fmap (ig \<circ> (K fst)) z" using z_type by fastforce
  also have "... = Fmap (K snd) z" using z_type by (rule Fmap_cong) auto
  also have "... = y" using y_eq by simp
  finally show "y = Fmap ig x" by simp
qed

corollary Graph_on_Fmap_eq_Frel_Graph_on:
  "Graph_on (F iT) (Fmap ig) = Frel (\<lambda>i. Graph_on (iT i) (ig i))"
  using Frel_Graph_on_if_Graph_on_Fmap Graph_on_Fmap_if_Frel_Graph_on by blast

lemma eq_restrict_F_if_Frel_eq_restrict:
  assumes "Frel (\<lambda>i. (=\<^bsub>iT i\<^esub>)) x y"
  shows "x =\<^bsub>F iT\<^esub> y"
proof -
  from assms have "Frel (\<lambda>i. Graph_on (iT i) (iid i)) x y" unfolding iid_eq_K_id by simp
  with Graph_on_Fmap_if_Frel_Graph_on have "Graph_on (F iT) (Fmap iid) x y" by auto
  moreover have "Graph_on (F iT) (Fmap iid) = Graph_on (F iT) id"
    by (rule Graph_on_eq_Graph_on_if_mono_eq) auto
  ultimately show ?thesis by simp
qed

corollary Frel_eq_restrict_iff_eq_restrict_F: "Frel (\<lambda>i. (=\<^bsub>iT i\<^esub>)) x y \<longleftrightarrow> x =\<^bsub>F iT\<^esub> y"
  using Frel_eq_restrict_if_eq_restrict_F eq_restrict_F_if_Frel_eq_restrict by blast

corollary Frel_eq_restrict_eq_eq_restrict_F: "Frel (\<lambda>i. (=\<^bsub>iT i\<^esub>)) = (=\<^bsub>F iT\<^esub>)"
  by (intro ext Frel_eq_restrict_iff_eq_restrict_F)

corollary eq_restrict_F_if_Frel_K_eq:
  assumes "Frel (K (=)) x y"
  shows "x =\<^bsub>F \<top>\<^esub> y"
  using assms by (urule eq_restrict_F_if_Frel_eq_restrict)

corollary Frel_K_eq_iff_eq_restrict_F: "Frel (K (=)) x y \<longleftrightarrow> x =\<^bsub>F \<top>\<^esub> y"
  by (urule Frel_eq_restrict_iff_eq_restrict_F)

corollary Frel_K_eq_eq_restrict_F: "Frel (K (=)) = (=\<^bsub>F \<top>\<^esub>)"
  by (urule Frel_eq_restrict_eq_eq_restrict_F)

corollary Frel_K_eq_iff_eq_if_F:
  assumes "F iT x"
  shows "Frel (K (=)) x y \<longleftrightarrow> x = y"
proof -
  have "(I \<Rrightarrow> (\<le>)) iT \<top>" by auto
  then have "F iT \<le> F \<top>" using F_if_le_if_F by auto
  with assms have "x =\<^bsub>F \<top>\<^esub> y \<longleftrightarrow> x = y" by auto
  with Frel_K_eq_iff_eq_restrict_F show ?thesis by auto
qed

end

context Functor
begin

paragraph \<open>Algebras\<close>

definition "algebra ia T (s :: 'f \<Rightarrow> 't) \<equiv> (F ((K \<top>)(ia := T)) \<Rightarrow> T) s"

lemma algebraI:
  assumes "\<And>iT. iT ia = T \<Longrightarrow> (F iT \<Rightarrow> T) s"
  shows "algebra ia T s"
  unfolding algebra_def using assms by auto

lemma algebraE:
  assumes "algebra ia T s"
  obtains "\<And>iT. iT ia = T \<Longrightarrow> (F iT \<Rightarrow> T) s"
proof -
  have "(I \<Rrightarrow> (\<le>)) iT ((K \<top>)(ia := T))" if "iT ia = T" for iT using that by auto
  with assms F_if_le_if_F show ?thesis using that unfolding algebra_def by (force del: F_K_top_if_F)
qed

lemma algebraD:
  assumes "algebra ia T s"
  and "iT ia = T"
  and "F iT x"
  shows "T (s x)"
  using assms by (auto elim: algebraE)

text \<open>Morphisms between algebras\<close>

definition "algebra_morph ia T T' s s' f \<equiv> (T \<Rightarrow> T') f \<and> \<comment> \<open>@{term ia} is the index of the algebra\<close>
  (F ((K \<top>)(ia := T)) \<Rrightarrow> (=)) (f \<circ> s) (s' \<circ> Fmap (iid(ia := f)))"

lemma algebra_morphI:
  assumes f_type: "(T \<Rightarrow> T') f"
  and comm: "\<And>iT x. iT ia = T \<Longrightarrow> F iT x \<Longrightarrow> f (s x) = s' (Fmap (iid(ia := f)) x)"
  shows "algebra_morph ia T T' s s' f"
proof -
  have "(F ((K \<top>)(ia := T)) \<Rrightarrow> (=)) (f \<circ> s) (s' \<circ> Fmap (iid(ia := f)))"
    by (urule (rr) Fun_Rel_predI comm) auto
  with f_type show ?thesis unfolding algebra_morph_def by auto
qed

lemma algebra_morphE:
  assumes "algebra_morph ia T T' s s' f"
  obtains "(T \<Rightarrow> T') f"
  and "\<And>iT. iT ia = T \<Longrightarrow> (F iT \<Rrightarrow> (=)) (f \<circ> s) (s' \<circ> Fmap (iid(ia := f)))"
proof -
  from assms obtain "(T \<Rightarrow> T') f"
    and comm: "(F ((K \<top>)(ia := T)) \<Rrightarrow> (=)) (f \<circ> s) (s' \<circ> Fmap (iid(ia := f)))"
    unfolding algebra_morph_def by auto
  moreover have "(F iT \<Rrightarrow> (=)) (f \<circ> s) (s' \<circ> Fmap (iid(ia := f)))" if "iT ia = T" for iT
  proof (rule Fun_Rel_predI)
    fix x assume "F iT x"
    from that have "(I \<Rrightarrow> (\<le>)) iT ((K \<top>)(ia := T))" by fastforce
    with \<open>F iT x\<close> F_if_le_if_F comm show "(f \<circ> s) x = (s' \<circ> Fmap (iid(ia := f))) x" by fast
  qed
  ultimately show ?thesis using that by blast
qed

lemma eq_app_Fmap_iid_fun_upd_if_algebra_morphI:
  assumes "algebra_morph ia T T' s s' f"
  and "F iT z"
  and "iT ia = T"
  shows "f (s z) = s' (Fmap (iid(ia := f)) z)"
  using assms by (fastforce elim: algebra_morphE)

lemma algebra_morph_id_if_le:
  assumes "T \<le> T'"
  shows "algebra_morph ia T T' s s id"
proof (intro algebra_morphI)
  from assms show "(T \<Rightarrow> T') id" by fastforce
  fix iT x assume "F iT x"
  have "((i : I) \<Rrightarrow> iT i \<Rrightarrow> (=)) (iid(ia := id)) iid" by fastforce
  with \<open>F iT x\<close> show "id (s x) = s (Fmap (iid(ia := id)) x)" using Fmap_id by fastforce
qed

corollary algebra_morph_id: "algebra_morph ia T T s s id"
  by (rule algebra_morph_id_if_le) auto

lemma algebra_morph_compI:
  assumes morph1: "algebra_morph ia T1 T2 s1 s2 f"
  and morph2: "algebra_morph ia T2 T3 s2 s3 g"
  shows "algebra_morph ia T1 T3 s1 s3 (g \<circ> f)"
proof (intro algebra_morphI)
  from assms show "(T1 \<Rightarrow> T3) (g \<circ> f)" by (fastforce elim: algebra_morphE)
  fix iT x assume iT_eq: "iT ia = T1" "F iT x"
  with morph1 have "(f \<circ> s1) x = (s2 \<circ> Fmap (iid(ia := f))) x" by (blast elim: algebra_morphE)
  then have gfs1: "(g \<circ> f \<circ> s1) x = (g \<circ> s2 \<circ> Fmap (iid(ia := f))) x" by simp
  have f_type: "((i : I) \<Rightarrow> iT i \<Rightarrow> (iT(ia := T2)) i) (iid(ia := f))"
  proof (intro dep_mono_wrt_predI mono_wrt_predI)
    fix i x assume "I i" "iT i x"
    then show "(iT(ia := T2)) i ((iid(ia := f)) i x)"
    proof (cases "i = ia")
      case True
      with assms \<open>iT i x\<close> iT_eq show ?thesis by (fastforce elim: algebra_morphE)
    qed auto
  qed
  with Fmap_type \<open>F iT x\<close> have "F (iT(ia := T2)) (Fmap (iid(ia := f)) x)" by fastforce
  moreover from iT_eq have "(iT(ia := T2)) ia = T2" by fastforce
  ultimately have gs2f: "g (s2 (Fmap (iid(ia := f)) x)) =
    s3 (Fmap (iid(ia := g)) (Fmap (iid(ia := f)) x))"
    using morph2 by (fastforce elim: algebra_morphE)
  have g_type: "((i : I) \<Rightarrow> (iT(ia := T2)) i\<Rightarrow> (iT(ia := T3)) i) (iid(ia := g))"
    using assms by (fastforce elim: algebra_morphE)
  with Fmap_comp[of "iid(ia := g)" "iid(ia := f)"] \<open>F iT x\<close> f_type have
    "Fmap (iid(ia := g)) (Fmap (iid(ia := f)) x) = Fmap (iid(ia := g) \<circ> iid(ia := f)) x"
    by fastforce
  moreover have "... = Fmap (iid(ia := g \<circ> f)) x" by simp
  finally have "Fmap (iid(ia := g)) (Fmap (iid(ia := f)) x) = Fmap (iid(ia := g \<circ> f)) x" by blast
  with gs2f gfs1 show "(g \<circ> f) (s1 x) = s3 (Fmap (iid(ia := g \<circ> f)) x)" by fastforce
qed

end

context Functor_Cong
begin

lemma algebra_morph_cong:
  assumes morph: "algebra_morph ia T T' s s' f"
  and alg: "algebra ia T s"
  and feq_T: "(T \<Rrightarrow> (=)) f f'"
  shows "algebra_morph ia T T' s s' f'"
proof (intro algebra_morphI)
  from morph feq_T show "(T \<Rightarrow> T') f'" by (fastforce elim: algebra_morphE)
  fix iT x assume iT_eq: "iT ia = T" and x_type: "F iT x"
  with alg have "T (s x)" by (auto dest: algebraD)
  with feq_T have "f' (s x) = f (s x)" by auto
  also from iT_eq x_type morph have "... = s' (Fmap (iid(ia := f)) x)"
    by (intro eq_app_Fmap_iid_fun_upd_if_algebra_morphI) auto
  also have "... = s' (Fmap (iid(ia := f')) x)"
  proof -
    have "Fmap (iid(ia := f)) x = Fmap (iid(ia := f')) x" using x_type
      by (rule Fmap_cong) (use feq_T iT_eq in auto)
    then show ?thesis by simp
  qed
  finally show "f' (s x) = s' (Fmap (iid(ia := f')) x)" .
qed

lemma (in HOTG_Functor) algebra_morph_top_iid_self: "algebra_morph ia \<top> \<top> (Fmap (iid(ia := s))) s s"
  by (intro algebra_morphI) auto

end

context Functor
begin

definition "is_subalgebra ia T s T' \<equiv> T' \<le> T \<and> algebra ia T' s"

lemma is_subalgebraI:
  assumes "T' \<le> T"
  and "algebra ia T' s"
  shows "is_subalgebra ia T s T'"
  unfolding is_subalgebra_def using assms by blast

lemma is_subalgebraE:
  assumes "is_subalgebra ia T s T'"
  obtains "T' \<le> T" "algebra ia T' s"
  using assms unfolding is_subalgebra_def by blast

paragraph \<open>Initial Algebra\<close>

definition "is_weakly_initial_algebra ia T s \<equiv> algebra ia T s \<and>
  (\<forall>T'. \<forall>s' : algebra ia T'. \<exists>h. algebra_morph ia T T' s s' h)"

lemma is_weakly_initial_algebraI:
  assumes "algebra ia T s"
  and "\<And>T' s'. algebra ia T' s' \<Longrightarrow> \<exists>h. algebra_morph ia T T' s s' h"
  shows "is_weakly_initial_algebra ia T s"
  unfolding is_weakly_initial_algebra_def using assms by blast

lemma is_weakly_initial_algebraE:
  assumes "is_weakly_initial_algebra ia T s"
  obtains "algebra ia T s" and "\<And>T' s'. algebra ia T' s' \<Longrightarrow> \<exists>h. algebra_morph ia T T' s s' h"
  using assms unfolding is_weakly_initial_algebra_def by blast

definition "is_initial_algebra ia T s \<equiv> is_weakly_initial_algebra ia T s \<and>
  (\<forall>T'. \<forall>s' : algebra ia T'. \<forall>h h' : algebra_morph ia T T' s s'. (T \<Rrightarrow> (=)) h h')"

lemma is_initial_algebraI:
  assumes "is_weakly_initial_algebra ia T s"
  and "\<And>T' s' h h'. algebra ia T' s' \<Longrightarrow> algebra_morph ia T T' s s' h \<Longrightarrow>
    algebra_morph ia T T' s s' h' \<Longrightarrow> (T \<Rrightarrow> (=)) h h'"
  shows "is_initial_algebra ia T s"
  unfolding is_initial_algebra_def using assms by (fastforce intro: is_weakly_initial_algebraI)

lemma is_initial_algebraE:
  assumes "is_initial_algebra ia T s"
  obtains "is_weakly_initial_algebra ia T s"
  and "\<And>T' s' h h'. algebra ia T' s' \<Longrightarrow> algebra_morph ia T T' s s' h \<Longrightarrow>
    algebra_morph ia T T' s s' h' \<Longrightarrow> (T \<Rrightarrow> (=)) h h'"
  using assms unfolding is_initial_algebra_def by (fastforce elim: is_weakly_initial_algebraE)

text \<open>The construction of an initial algebra follows the outline from \<^cite>\<open>cardinals_in_hol\<close>.\<close>

definition "min_algebra_obj ia s \<equiv> \<lambda>x. (\<forall>T'. algebra ia T' s \<longrightarrow> T' x)"

context
  fixes ia s obj
  defines [simp]: "obj \<equiv> min_algebra_obj ia s"
begin

lemma min_algebra_objI:
  assumes "\<And>T'. algebra ia T' s \<Longrightarrow> T' x"
  shows "obj x"
  using assms unfolding min_algebra_obj_def obj_def by blast

lemma min_algebra_objE:
  assumes "obj x"
  obtains "\<And>T'. algebra ia T' s \<Longrightarrow> T' x"
  using assms unfolding min_algebra_obj_def obj_def by blast

lemma min_algebra_obj_le_if_algebra:
  assumes "algebra ia T s"
  shows "obj \<le> T"
  using assms by (blast elim: min_algebra_objE)

text \<open>The minimal algebra is an algebra.\<close>

lemma algebra_min_algebra: "algebra ia obj s"
proof (intro algebraI mono_wrt_predI)
  fix iT x assume iT_obj: "iT ia = obj" and x_type: "F iT x"
  show "obj (s x)"
  proof (intro min_algebra_objI)
    fix T' assume alg: "algebra ia T' s"
    with iT_obj have "iT i \<le> (iT(ia := T')) i" for i
      using min_algebra_obj_le_if_algebra by (cases "i = ia") auto
    with x_type have "F (iT(ia := T')) x" by (blast intro: F_if_le_if_F)
    then show "T' (s x)" by (intro algebraD[OF alg]) auto
  qed
qed

corollary is_subalgebra_min_algebraI:
  assumes "algebra ia T s"
  shows "is_subalgebra ia T s obj"
  by (intro is_subalgebraI min_algebra_obj_le_if_algebra assms algebra_min_algebra)

text \<open>There is a morphism from the minimal algebra to every algebra that has the same morphism.\<close>

corollary algebra_morph_min_algebraI:
  assumes "algebra ia T s"
  shows "algebra_morph ia obj T s s id"
  by (intro algebra_morph_id_if_le min_algebra_obj_le_if_algebra assms)

corollary ex_algebra_morph_min_algebraI:
  assumes "algebra ia T s"
  shows "\<exists>f. algebra_morph ia obj T s s f"
  using assms algebra_morph_min_algebraI by blast

end
end

context Functor_Cong
begin

context
  fixes ia s obj
  defines [simp]: "obj \<equiv> min_algebra_obj ia s"
begin

lemma min_algebra_obj_le_equaliser_if_morphs:
  assumes morph1: "algebra_morph ia obj T s s' f"
  and morph2: "algebra_morph ia obj T s s' g"
shows "obj \<le> equaliser f g"
proof -
  have "obj \<le> obj \<sqinter> equaliser f g" (is "_ \<le> ?obj_eq")
  proof (urule (rr) min_algebra_obj_le_if_algebra algebraI mono_wrt_predI)
    fix iT x assume "iT ia = ?obj_eq" and "F iT x"
    then have x_type: "F (iT(ia := obj)) x"
      and x_type_eq: "F (iT(ia := equaliser f g)) x" by (fastforce intro: F_if_le_if_F)+
    from x_type morph1 have "f (s x) = s' (Fmap (iid(ia := f)) x)"
      by (intro eq_app_Fmap_iid_fun_upd_if_algebra_morphI) auto
    also have "... = s' (Fmap (iid(ia := g)) x)"
    proof -
      have "Fmap (iid(ia := f)) x = Fmap (iid(ia := g)) x" using x_type_eq by (rule Fmap_cong) auto
      then show ?thesis by simp
    qed
    also have "... = g (s x)"
      using morph2 x_type by (intro eq_app_Fmap_iid_fun_upd_if_algebra_morphI[symmetric]) auto
    finally have "f (s x) = g (s x)" .
    moreover have "obj (s x)" using algebra_min_algebra by (urule algebraD) (use x_type in auto)
    ultimately show "?obj_eq (s x)" by auto
  qed
  then show ?thesis by auto
qed

corollary algebra_morph_min_algebra_unique:
  assumes "algebra_morph ia obj T s s' f"
  and "algebra_morph ia obj T s s' g"
  shows "(obj \<Rrightarrow> (=)) f g"
  using assms min_algebra_obj_le_equaliser_if_morphs by blast

corollary eq_if_algebra_morphs_min_algebraI:
  assumes "algebra_morph ia obj T s s' f"
  and "algebra_morph ia obj T s s' g"
  and "obj x"
  shows "f x = g x"
  using assms algebra_morph_min_algebra_unique by blast

text \<open>Morphisms from the minimal algebra are unique (however, there may not be any morphism at all).
To get an initial algebra, it hence suffices to find a minimal algebra that has at least one morphism
to any other algebra.\<close>

end
end

context HOTG_Functor
begin

text \<open>Algebra Product\<close>

definition "algebra_prod_obj ia J iT :: t \<Rightarrow> bool \<equiv> ((j : mem_of J) \<rightarrow> iT j)"
definition "algebra_prod_morph ia J is :: f \<Rightarrow> t \<equiv> \<lambda>x. \<lambda>j : J. is j (Fmap (iid(ia := \<lambda>pr. pr`j)) x)"

context
  fixes ia J iT "is" obj morph
  defines [simp]: "obj \<equiv> algebra_prod_obj ia J iT"
  and [simp]: "morph \<equiv> algebra_prod_morph ia J is"
  notes algebra_prod_obj_def[simp] algebra_prod_morph_def[simp]
begin

lemma algebra_algebra_prodI:
  assumes "\<And>j. j \<in> J \<Longrightarrow> algebra ia (iT j) (is j)"
  shows "algebra ia obj morph"
proof (intro algebraI mono_wrt_predI)
  fix x iS assume iS_obj: "iS ia = obj" and x_type: "F iS x"
  show "obj (morph x)"
  proof (urule (rr) rel_dep_mono_wrt_predI dep_mono_wrt_predI)
    fix j presume jmem: "j \<in> J"
    with assms iS_obj have is_type: "(F (iS(ia := iT j)) \<Rightarrow> iT j) (is j)"
      by (fastforce elim: algebraE)
    from jmem have "((i : I) \<Rightarrow> iS i \<Rightarrow> (iS(ia := iT j)) i) (iid(ia := \<lambda>pr. pr`j))"
      by (fastforce simp: iS_obj)
    with x_type have "F (iS(ia := iT j)) (Fmap (iid(ia := \<lambda>pr. pr`j)) x)"
      using Fmap_type by fastforce
    with is_type jmem show "iT j ((\<lambda>j : mem_of J. is j (Fmap (iid(ia := \<lambda>pr. rel pr`j)) x))`j)"
      by fastforce
  qed auto
qed

lemma algebra_morph_algebra_prodI:
  assumes "j \<in> J"
  shows "algebra_morph ia obj (iT j) morph (is j) (\<lambda>pr. pr`j)"
  using assms by (fastforce intro: algebra_morphI)

context
  fixes min_obj
  defines [simp]: "min_obj \<equiv> min_algebra_obj ia morph"
begin

lemma algebra_morph_min_algebra_algebra_prod:
  assumes algebras: "\<And>j. j \<in> J \<Longrightarrow> algebra ia (iT j) (is j)"
  and "j \<in> J"
  shows "algebra_morph ia min_obj (iT j) morph (is j) (\<lambda>pr. pr`j)"
supply comp_id_eq[uhint]
proof (urule algebra_morph_compI)
  from algebras algebra_algebra_prodI have "algebra ia obj morph" by auto
  with algebra_morph_min_algebraI show "algebra_morph ia min_obj obj morph morph id" by auto
  from \<open>j \<in> J\<close> algebra_morph_algebra_prodI
    show "algebra_morph ia obj (iT j) morph (is j) (\<lambda>pr. rel pr`j)" by auto
qed

text \<open>There is a morphism from the product to any algebra of the product.\<close>

lemma ex_algebra_morph_min_algebra_algebra_prod:
  assumes "\<And>j. j \<in> J \<Longrightarrow> algebra ia (iT j) (is j)"
  and "j \<in> J"
  shows "\<exists>f. algebra_morph ia min_obj (iT j) morph (is j) f"
  using assms algebra_morph_min_algebra_algebra_prod by blast

end
end
end

locale HOTG_Weakly_Initial_Algebra_Generator = HOTG_Functor _ _ Fmap for Fmap :: "('i \<Rightarrow> _) \<Rightarrow> _" +
  fixes ia :: "'i"
  fixes J :: set
  and giT :: "set \<Rightarrow> set \<Rightarrow> bool"
  and "gis" :: "set \<Rightarrow> set \<Rightarrow> set"
  assumes every_alg_has_index_min:
    "\<And>T s. algebra ia T s \<Longrightarrow> \<exists>j : J. giT j = min_algebra_obj ia s \<and> gis j = s" (*TODO: restrict equality to min_alg_obj?*)
  and every_index_is_algebra: "\<And>j. j \<in> J \<Longrightarrow> algebra ia (giT j) (gis j)"
begin

definition "initial_algebra_morph \<equiv> algebra_prod_morph ia J gis"
definition "initial_algebra_obj \<equiv> min_algebra_obj ia initial_algebra_morph"

context
  notes initial_algebra_obj_def[simp] and initial_algebra_morph_def[simp]
begin

corollary algebra_initial_algebra: "algebra ia initial_algebra_obj initial_algebra_morph"
  by (urule algebra_min_algebra)

corollary ex_algebra_morph_min_algebra_if_mem:
  assumes "j \<in> J"
  shows "\<exists>f. algebra_morph ia initial_algebra_obj (giT j) initial_algebra_morph (gis j) f"
  by (urule ex_algebra_morph_min_algebra_algebra_prod) (use every_index_is_algebra assms in auto)

lemma ex_algebra_morph_if_algebra:
  assumes "algebra ia T s"
  shows "\<exists>f. algebra_morph ia initial_algebra_obj T initial_algebra_morph s f"
proof -
  from assms every_alg_has_index_min obtain j where "j \<in> J"
    and iTis: "giT j = min_algebra_obj ia s" "gis j = s" by blast
  with ex_algebra_morph_min_algebra_if_mem obtain f
    where "algebra_morph ia initial_algebra_obj (giT j) initial_algebra_morph s f" by fastforce
  moreover from assms algebra_morph_min_algebraI iTis have "algebra_morph ia (giT j) T s s id"
    by fastforce
  ultimately show ?thesis by (blast intro: algebra_morph_compI)
qed

corollary is_weakly_initial_algebra_initial_algebra:
  "is_weakly_initial_algebra ia initial_algebra_obj initial_algebra_morph"
  using algebra_initial_algebra ex_algebra_morph_if_algebra by (intro is_weakly_initial_algebraI)

end
end

locale HOTG_Initial_Algebra_Generator = HOTG_Weakly_Initial_Algebra_Generator F I Fmap +
  HOTG_Functor_Cong F I Fmap
  for F I and Fmap :: "('i \<Rightarrow> _) \<Rightarrow> _"
begin

theorem is_initial_algebra_initial_algebra:
  "is_initial_algebra ia initial_algebra_obj initial_algebra_morph"
  using is_weakly_initial_algebra_initial_algebra algebra_morph_min_algebra_unique
  unfolding initial_algebra_obj_def by (rule is_initial_algebraI)

end

paragraph \<open>Fold and Recursor\<close>

context HOTG_Weakly_Initial_Algebra_Generator
begin

definition "is_fold T s f \<equiv> algebra_morph ia initial_algebra_obj T initial_algebra_morph s f"

lemma is_foldI:
  assumes "algebra_morph ia initial_algebra_obj T initial_algebra_morph s f"
  shows "is_fold T s f"
  using assms unfolding is_fold_def by blast

lemma is_foldE [elim]:
  assumes "is_fold T s f"
  shows "algebra_morph ia initial_algebra_obj T initial_algebra_morph s f"
  using assms unfolding is_fold_def by blast

lemma is_fold_initial_algebra_obj_id: "is_fold initial_algebra_obj initial_algebra_morph id"
  using algebra_morph_id by (intro is_foldI) blast

lemma fold_type:
  assumes "is_fold T s f"
  shows "(initial_algebra_obj \<Rightarrow> T) f"
  using assms is_foldE by (auto elim: algebra_morphE)

lemma fold_eq_app_Fmap_iid_fun_updI:
  assumes "is_fold T s f"
  and "F ((K \<top>)(ia := initial_algebra_obj)) x"
  shows "f (initial_algebra_morph x) = s (Fmap (iid(ia := f)) x)"
  using assms by (intro eq_app_Fmap_iid_fun_upd_if_algebra_morphI) auto

definition "fold T s \<equiv> SOME f. is_fold T s f"

lemma is_fold_fold_if_algebra:
  assumes "algebra ia T s"
  shows "is_fold T s (fold T s)"
  unfolding fold_def using assms ex_algebra_morph_if_algebra
  by (urule someI_ex where chained = insert) (blast intro: is_foldI)

end

context HOTG_Initial_Algebra_Generator
begin

lemma fold_unique:
  assumes "is_fold T s f" "is_fold T s g"
  shows "(initial_algebra_obj \<Rrightarrow> (=)) f g"
proof -
  from assms have "algebra_morph ia initial_algebra_obj T initial_algebra_morph s f"
    and "algebra_morph ia initial_algebra_obj T initial_algebra_morph s g" by auto
  then show ?thesis using algebra_morph_min_algebra_unique unfolding initial_algebra_obj_def by auto
qed

end

context HOTG_Weakly_Initial_Algebra_Generator
begin

definition "rec_obj T \<equiv> initial_algebra_obj \<times> T"
definition "rec_morph s \<equiv> convol (initial_algebra_morph \<circ> Fmap (iid(ia := fst))) s"
definition "rec_fold T s \<equiv> fold (rec_obj T) (rec_morph s)"
definition "rec T s \<equiv> snd \<circ> rec_fold T s"

lemma fst_rec_morph_eq: "fst (rec_morph s x) = initial_algebra_morph (Fmap (iid(ia := fst)) x)"
  unfolding rec_morph_def by simp
lemma snd_rec_morph_eq: "snd (rec_morph s x) = s x"
  unfolding rec_morph_def by simp

lemma is_fold_rec_obj_rec_morph_rec_foldI:
  assumes "(F ((K \<top>)(ia := rec_obj T)) \<Rightarrow> T) s"
  shows "is_fold (rec_obj T) (rec_morph s) (rec_fold T s)"
unfolding rec_fold_def
proof (intro is_fold_fold_if_algebra algebraI mono_wrt_predI)
  fix iT x assume iT_ia_eq: "iT ia = rec_obj T" and "F iT x"
  show "rec_obj T (rec_morph s x)" unfolding rec_obj_def rec_morph_def
  proof (urule set_pair_mk_pairI)
    from iT_ia_eq have "((i : I) \<Rightarrow> iT i \<Rightarrow> (iT(ia := initial_algebra_obj)) i) (iid(ia := fst))"
      unfolding rec_obj_def by (intro dep_mono_wrt_predI) auto
    with \<open>F iT x\<close> iT_ia_eq have "F (iT(ia := initial_algebra_obj)) (Fmap (iid(ia := fst)) x)"
      using Fmap_type by blast
    then have "F ((K \<top>)(ia := initial_algebra_obj)) (Fmap (iid(ia := fst)) x)"
      by (rule F_if_le_if_F) auto
    with algebra_initial_algebra
      show "initial_algebra_obj (initial_algebra_morph (Fmap (iid(ia := fst)) x))"
      by (auto dest: algebraD[where ?iT="_(ia := _)"])
    from iT_ia_eq have "(I \<Rrightarrow> (\<le>)) iT ((K \<top>)(ia := rec_obj T))" by auto
    with assms \<open>F iT x\<close> F_if_le_if_F show "T (s x)" by auto
  qed
qed

lemma rec_fold_eq_rec_morph_Fmap_iid_rec_foldI:
  assumes "(F ((K \<top>)(ia := rec_obj T)) \<Rightarrow> T) s"
  and "F ((K \<top>)(ia := initial_algebra_obj)) x"
  shows "rec_fold T s (initial_algebra_morph x) = rec_morph s (Fmap (iid(ia := rec_fold T s)) x)"
  using assms is_fold_rec_obj_rec_morph_rec_foldI fold_eq_app_Fmap_iid_fun_updI by blast

lemma rec_eq_app_Fmap_iid_rec_foldI:
  assumes "(F ((K \<top>)(ia := rec_obj T)) \<Rightarrow> T) s"
  and "F ((K \<top>)(ia := initial_algebra_obj)) x"
  shows "rec T s (initial_algebra_morph x) = s (Fmap (iid(ia := rec_fold T s)) x)"
  using assms rec_fold_eq_rec_morph_Fmap_iid_rec_foldI fst_rec_morph_eq snd_rec_morph_eq
  unfolding rec_def by auto

end

context HOTG_Initial_Algebra_Generator
begin

lemma fst_comp_rec_fold_eq_idI:
  assumes s_type: "(F ((K \<top>)(ia := rec_obj T)) \<Rightarrow> T) s"
  shows "(initial_algebra_obj \<Rrightarrow> (=)) (fst \<circ> rec_fold T s) id"
unfolding initial_algebra_obj_def
proof (rule algebra_morph_min_algebra_unique, fold initial_algebra_obj_def)
  show "algebra_morph ia initial_algebra_obj initial_algebra_obj
    initial_algebra_morph initial_algebra_morph id"
    by (fact algebra_morph_id)
  show "algebra_morph ia initial_algebra_obj initial_algebra_obj
    initial_algebra_morph initial_algebra_morph (fst \<circ> rec_fold T s)"
  proof (intro algebra_morphI)
    show "(initial_algebra_obj \<Rightarrow> initial_algebra_obj) (fst \<circ> rec_fold T s)"
      using fold_type is_fold_rec_obj_rec_morph_rec_foldI s_type unfolding rec_obj_def by fastforce
    fix iT x assume "iT ia = initial_algebra_obj" and "F iT x"
    then have "F ((K \<top>)(ia := initial_algebra_obj)) x" by (fastforce intro: F_if_le_if_F)
    with s_type have
      "rec_fold T s (initial_algebra_morph x) = rec_morph s (Fmap (iid(ia := rec_fold T s)) x)"
      by (auto intro: fold_eq_app_Fmap_iid_fun_updI is_fold_rec_obj_rec_morph_rec_foldI)
    then have "fst (rec_fold T s (initial_algebra_morph x)) =
      initial_algebra_morph (Fmap (iid(ia := fst)) (Fmap (iid(ia := rec_fold T s)) x))"
      by (simp add: fst_rec_morph_eq)
    also have "... = initial_algebra_morph (Fmap (iid(ia := fst \<circ> rec_fold T s)) x)"
      supply Fmap_comp_eq_Fmap_Fmap[uhint] \<open>F iT x\<close>[uhint] by (urule refl)
    finally show "(fst \<circ> rec_fold T s) (initial_algebra_morph x) =
      initial_algebra_morph (Fmap (iid(ia := fst \<circ> rec_fold T s)) x)" by simp
  qed
qed

corollary fst_rec_fold_eq_selfI:
  assumes "(F ((K \<top>)(ia := rec_obj T)) \<Rightarrow> T) s"
  and "initial_algebra_obj x"
  shows "fst (rec_fold T s x) = x"
  using assms fst_comp_rec_fold_eq_idI by fastforce

lemma rec_fold_eq_convol_recI:
  assumes "(F ((K \<top>)(ia := rec_obj T)) \<Rightarrow> T) s"
  shows "(initial_algebra_obj \<Rrightarrow> (=)) (rec_fold T s) (convol id (rec T s))"
proof (intro Fun_Rel_predI)
  fix x assume x_type: "initial_algebra_obj x"
  with fst_rec_fold_eq_selfI have "fst (rec_fold T s x) = x" using assms by auto
  moreover have "snd (rec_fold T s x) = rec T s x" unfolding rec_def by simp
  moreover from is_fold_rec_obj_rec_morph_rec_foldI have "is_pair (rec_fold T s x)"
    using x_type assms fold_type by (force simp: rec_obj_def)
  ultimately show "rec_fold T s x = convol id (rec T s) x" by fastforce
qed

corollary rec_fold_eq_mk_pair_recI:
  assumes "(F ((K \<top>)(ia := rec_obj T)) \<Rightarrow> T) s"
  and "initial_algebra_obj x"
  shows "rec_fold T s x = \<langle>x, rec T s x\<rangle>"
  using assms rec_fold_eq_convol_recI by auto

lemma rec_eq_app_Fmap_iid_convol_recI:
  assumes "(F ((K \<top>)(ia := rec_obj T)) \<Rightarrow> T) s"
  and "F ((K \<top>)(ia := initial_algebra_obj)) x"
  shows "rec T s (initial_algebra_morph x) = s (Fmap (iid(ia := convol id (rec T s))) x)"
proof -
  from rec_eq_app_Fmap_iid_rec_foldI have
    "rec T s (initial_algebra_morph x) = s (Fmap (iid(ia := rec_fold T s)) x)" using assms by auto
  also have "... = s (Fmap (iid(ia := convol id (rec T s))) x)"
  proof (subst Fmap_cong)
    fix i x assume "I i" "((K \<top>)(ia := initial_algebra_obj)) i x"
    then show "(iid(ia := rec_fold T s)) i x = (iid(ia := convol id (rec T s))) i x"
      using assms rec_fold_eq_mk_pair_recI by auto
  qed (simp_all only: assms)
  finally show ?thesis  .
qed

end

locale Natural_Functor = Functor _ _ Fmap for Fmap :: "('i \<Rightarrow> 't \<Rightarrow> _) \<Rightarrow> 'f \<Rightarrow> _" +
  fixes Fpred :: "'i \<Rightarrow> 'f \<Rightarrow> 't \<Rightarrow> bool"
  assumes Fpred_type: "\<And>iT. ((i : I) \<Rightarrow> F iT \<Rightarrow> (\<ge>) (iT i)) Fpred"
  and Fpred_natural: "\<And>iT ig i. I i \<Longrightarrow>
    (F iT \<Rrightarrow> (=)) (Fpred i \<circ> Fmap ig) (image_pred (ig i) \<circ> Fpred i)"
  (* TODO: needed? *)
  (*and Fmap_type_Fpred: "\<And>iIn iOut x ig.
    ((i : I) \<Rightarrow> Fpred i x \<Rightarrow> iOut i) ig \<Longrightarrow> F iIn x \<Longrightarrow> F iOut (Fmap ig x)"*)
  and Fmap_cong: "\<And>iIn ig ih x.
    F iIn x \<Longrightarrow>
    ((i : I) \<Rrightarrow> iIn i \<Rrightarrow> (=)) ig ih \<Longrightarrow>
    Fmap ig x = Fmap ih x"
begin

end


end