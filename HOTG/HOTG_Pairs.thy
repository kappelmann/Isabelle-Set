\<^marker>\<open>creator "Alexander Krauss"\<close>
\<^marker>\<open>creator "Kevin Kappelmann"\<close>
\<^marker>\<open>creator "Larry Paulson"\<close>
section \<open>Pairs (\<open>\<Sum>\<close>-types)\<close>
theory HOTG_Pairs
  imports
    HOTG_Foundation
    Transport.Dependent_Binary_Relations
begin

unbundle no HOL_ascii_syntax

subsection \<open>Dependent Pair Type\<close>

consts dep_pair :: "'a \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> 'd"
consts pair :: "'a \<Rightarrow> 'b \<Rightarrow> 'c"

open_bundle pair_syntax
begin
syntax "_dep_pair" :: \<open>idt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'c\<close> ("\<Sum>_ : _./ _" [52, 51, 51] 52)
notation pair (infixr "\<times>" 51)
end
syntax_consts "_dep_pair" \<rightleftharpoons> dep_pair
translations
  "\<Sum>x : A. B" \<rightleftharpoons> "CONST dep_pair A (\<lambda>x. B)"


subsection \<open>Set-Theoretic Pairs\<close>

definition mk_pair :: \<open>set \<Rightarrow> set \<Rightarrow> set\<close>
  where "mk_pair x y \<equiv> {{x}, {x, y}}"

open_bundle hotg_mk_pair_syntax
begin
syntax "_mk_pair" :: \<open>args \<Rightarrow> set\<close> ("\<langle>_\<rangle>")
end
syntax_consts "_mk_pair" \<rightleftharpoons> mk_pair
translations
  "\<langle>x, y, z\<rangle>" \<rightleftharpoons> "\<langle>x, \<langle>y, z\<rangle>\<rangle>"
  "\<langle>x, y\<rangle>" \<rightleftharpoons> "CONST mk_pair x y"

definition fst :: \<open>set \<Rightarrow> set\<close>
  where "fst p \<equiv> THE x. \<exists>y. p = \<langle>x, y\<rangle>"

definition snd :: \<open>set \<Rightarrow> set\<close>
  where "snd p \<equiv> THE y. \<exists>x. p = \<langle>x, y\<rangle>"

lemma mk_pair_eq_iff [iff]: "\<langle>x, y\<rangle> = \<langle>x', y'\<rangle> \<longleftrightarrow> x = x' \<and> y = y'"
  supply not_mem_self[iff del] insert_ne_self[iff del] unfolding mk_pair_def
  by (intro iffI; cases "x = y"; cases "x' = y'") (auto elim: eqE)

lemma eq_if_mk_pair_eq_left: "\<langle>x, y\<rangle> = \<langle>x', y'\<rangle> \<Longrightarrow> x = x'" by simp

lemma eq_if_mk_pair_eq_right: "\<langle>x, y\<rangle> = \<langle>x', y'\<rangle> \<Longrightarrow> y = y'" by simp

lemma fst_mk_pair_eq [simp]: "fst \<langle>x, y\<rangle> = x"
  by (simp add: fst_def)

lemma snd_mk_pair_eq [simp]: "snd \<langle>x, y\<rangle> = y"
  by (simp add: snd_def)

lemma mk_pair_ne_empty [iff]: "\<langle>x, y\<rangle> \<noteq> {}"
  unfolding mk_pair_def by blast

lemma mk_pair_ne_fst [iff]: "\<langle>x, y\<rangle> \<noteq> x"
  unfolding mk_pair_def using not_mem_if_mem
  by (intro ne_if_ex_mem_not_mem, intro exI[where x="{x}"]) auto

lemma mk_pair_ne_snd [iff]: "\<langle>x, y\<rangle> \<noteq> y"
  unfolding mk_pair_def using not_mem_if_mem
  by (intro ne_if_ex_mem_not_mem, intro exI[where x="{x, y}"]) auto

lemma mk_pair_not_mem_fst [iff]: "\<langle>x, y\<rangle> \<notin> x"
  unfolding mk_pair_def using not_mem_if_mem_if_mem by auto

lemma mk_pair_not_mem_snd [iff]: "\<langle>x, y\<rangle> \<notin> y"
  unfolding mk_pair_def by (auto dest: not_mem_if_mem_if_mem)


definition "is_pair p \<equiv> \<exists>x y. p = \<langle>x, y\<rangle>"

lemma is_pairI [intro]: "p = \<langle>x, y\<rangle> \<Longrightarrow> is_pair p"
  unfolding is_pair_def by blast

lemma is_pairE [elim!]:
  assumes "is_pair p"
  obtains x y where "p = \<langle>x, y\<rangle>"
  using assms unfolding is_pair_def by blast

lemma mk_pair_fst_snd_eq_if_is_pair [simp]: "is_pair p \<Longrightarrow> \<langle>fst p, snd p\<rangle> = p"
  by auto

definition "set_dep_pair_pred A B p \<equiv> is_pair p \<and> A (fst p) \<and> B (fst p) (snd p)"
adhoc_overloading dep_pair \<rightleftharpoons> set_dep_pair_pred

definition "set_dep_pair_set A B :: set \<Rightarrow> bool \<equiv> \<Sum>x : mem_of A. mem_of (B x)"
adhoc_overloading dep_pair \<rightleftharpoons> set_dep_pair_set

definition "set_pair_pred (A :: set \<Rightarrow> bool) B \<equiv> \<Sum>(_ :: set) : A. B"
adhoc_overloading pair \<rightleftharpoons> set_pair_pred

definition "set_pair_set A B \<equiv> mem_of A \<times> mem_of B"
adhoc_overloading pair \<rightleftharpoons> set_pair_set

lemma set_dep_pair_set_eq_set_dep_pair_pred [simp]: "(\<Sum>x : A. B x) = \<Sum>x : mem_of A. mem_of (B x)"
  unfolding set_dep_pair_set_def by simp

lemma set_dep_pair_set_eq_set_dep_pair_pred_uhint [uhint]:
  assumes "A' \<equiv> mem_of A"
  and "\<And>x. B' x \<equiv> mem_of (B x)"
  shows "\<Sum>x : A. B x \<equiv> \<Sum>x : A'. B' x"
  using assms by simp

lemma set_dep_pair_set_iff_set_dep_pair_pred [iff]:
  "(\<Sum>x : A. B x) p \<longleftrightarrow> (\<Sum>x : mem_of A. mem_of (B x)) p"
  by simp

lemma set_pair_set_eq_set_pair_pred [simp]: "A \<times> B = mem_of A \<times> mem_of B"
  unfolding set_pair_set_def by simp

lemma set_pair_set_eq_set_pair_pred_uhint [uhint]:
  assumes "A' \<equiv> mem_of A"
  and "B' \<equiv> mem_of B"
  shows "A \<times> B \<equiv> A' \<times> B'"
  using assms by simp

lemma set_pair_set_iff_set_pair_pred [iff]: "(A \<times> B) p \<longleftrightarrow> (mem_of A \<times> mem_of B) p"
  by simp

lemma set_pair_pred_eq_set_dep_pair_pred: "(A :: set \<Rightarrow> bool) \<times> B = \<Sum>_ : A. B"
  unfolding set_pair_pred_def by auto

lemma set_pair_pred_eq_set_dep_pair_pred_uhint [uhint]:
  assumes "A :: set \<Rightarrow> bool \<equiv> A'"
  and "\<And>x. B \<equiv> B' x"
  shows "A \<times> B = \<Sum>x : A'. B' x"
  using assms by (simp add: set_pair_pred_eq_set_dep_pair_pred)

lemma set_pair_pred_iff_set_dep_pair_pred: "((A :: set \<Rightarrow> bool) \<times> B) p \<longleftrightarrow> (\<Sum>_ : A. B) p"
  unfolding set_pair_pred_eq_set_dep_pair_pred by simp

lemma set_dep_pairI:
  assumes "is_pair p"
  and "A (fst p)"
  and "B (fst p) (snd p)"
  shows "(\<Sum>x : A. B x) p"
  using assms unfolding set_dep_pair_pred_def by auto

lemma set_dep_pair_mk_pairI [intro!]:
  assumes "A x"
  and "B x y"
  shows "(\<Sum>x : A. B x) \<langle>x, y\<rangle>"
  using assms by (auto intro: set_dep_pairI)

lemma set_dep_pairE [elim!]:
  assumes "(\<Sum>x : A. B x) p"
  obtains x y where "A x" "B x y" "p = \<langle>x, y\<rangle>"
  using assms unfolding set_dep_pair_pred_def by auto

lemma set_dep_pair_cong [cong]: "\<lbrakk>A = A'; \<And>x. A' x \<Longrightarrow> B x = B' x\<rbrakk> \<Longrightarrow> (\<Sum>x : A. B x) = \<Sum>x : A'. B' x"
  by auto

lemma set_pairI:
  assumes "is_pair p"
  and "A (fst p)"
  and "B (snd p)"
  shows "(A \<times> B) p"
  by (urule set_dep_pairI) (urule assms)+

lemma set_pair_mk_pairI [intro!]:
  assumes "A x"
  and "B y"
  shows "(A \<times> B) \<langle>x, y\<rangle>"
  by (urule set_dep_pair_mk_pairI) (urule assms)+

lemma set_pairE [elim!]:
  assumes "(A \<times> B) p"
  obtains x y where "A x" "B y" "p = \<langle>x, y\<rangle>"
  by (urule set_dep_pairE) (urule assms)+

lemma set_dep_pair_mk_pair_iff: "(\<Sum>x : A. B x) \<langle>x, y\<rangle> \<longleftrightarrow> A x \<and> B x y" by blast

lemma pred_fst_if_set_dep_pair_mk_pair: "(\<Sum>x : A. B x) \<langle>x, y\<rangle> \<Longrightarrow> A x" by auto
lemma pred_snd_if_set_dep_pair_mk_pair: "(\<Sum>x : A. B x) \<langle>x, y\<rangle> \<Longrightarrow> B x y" by auto

lemma pred_fst_if_set_dep_pair: "(\<Sum>x : A. B x) p \<Longrightarrow> A (fst p)" by auto
lemma pred_snd_if_set_dep_pair: "(\<Sum>x : A. B x) p \<Longrightarrow> B (fst p) (snd p)" by auto

lemma is_pair_if_set_dep_pair: "(\<Sum>x : (A :: set \<Rightarrow> bool). B x) p \<Longrightarrow> is_pair p"
  by auto

lemma pair_fst_snd_if_is_pair: "is_pair p \<Longrightarrow> ({fst p} \<times> {snd p}) p"
  by auto

lemma set_pair_if_is_pairE:
  assumes "is_pair p"
  obtains A :: "set \<Rightarrow> bool" and B where "(A \<times> B) p"
  using assms by (blast dest: pair_fst_snd_if_is_pair)

corollary is_pair_iff_ex_set_dep_pair: "is_pair p \<longleftrightarrow> (\<exists>(A :: set \<Rightarrow> bool) B. (\<Sum>x : A. B x) p)"
  using is_pair_if_set_dep_pair pair_fst_snd_if_is_pair by blast

lemma set_dep_pair_bottom_dom_eq_bottom [simp]: "(\<Sum>x : \<bottom>. B x) = \<bottom>"
  by auto

lemma set_dep_pair_bottom_codom_eq_bottom [simp]: "(\<Sum>x : A. \<bottom>) = \<bottom>"
  by auto

lemma set_pair_eq_bottom_iff_eq_bottom_or [iff]: "A \<times> B = \<bottom> \<longleftrightarrow> A = \<bottom> \<or> B = \<bottom>"
proof -
  have "A = \<bottom>" if "A \<times> B = \<bottom>" "B \<noteq> \<bottom>"
  proof (intro ext iffI)
    fix x assume "A x"
    moreover from that obtain y where "B y" by force
    ultimately have "(A \<times> B) \<langle>x, y\<rangle>" by auto
    with that show "\<bottom> x" by auto
  qed auto
  then show ?thesis by auto
qed

lemma eq_set_pair_eq_eq_eq_mk_pair [simp]: "((=) x) \<times> ((=) y) = (=) \<langle>x, y\<rangle>"
  by auto

lemma set_dep_pair_le_set_pair_idx_union: "(\<Sum>x : A. B x) \<le> A \<times> (\<Union>x \<in> A. B x)"
  by auto


paragraph \<open>Splitting quantifiers:\<close>

lemma bex_set_dep_pair_iff_bex_bex [iff]:
  "(\<exists>p : \<Sum>x : (A :: set \<Rightarrow> bool). B x. P p) \<longleftrightarrow> (\<exists>x : A. \<exists>y : B x. P \<langle>x, y\<rangle>)"
  by blast

lemma ball_set_dep_pair_iff_ball_ball [iff]:
  "(\<forall>p : \<Sum>x : (A :: set \<Rightarrow> bool). B x. P p) \<longleftrightarrow> (\<forall>x : A. \<forall>y : B x. P \<langle>x, y\<rangle>)"
  by blast

lemma bex_set_pair_iff_bex_bex [iff]:
  "(\<exists>p : (A :: set \<Rightarrow> bool) \<times> B. P p) \<longleftrightarrow> (\<exists>x : A. \<exists>y : B. P \<langle>x, y\<rangle>)"
  by blast

lemma ball_set_pair_iff_ball_ball [iff]:
  "(\<forall>p : (A :: set \<Rightarrow> bool) \<times> B. P p) \<longleftrightarrow> (\<forall>x : A. \<forall>y : B. P \<langle>x, y\<rangle>)"
  by blast

paragraph \<open>Monotonicity\<close>

lemma set_dep_pair_le_if_le_dom:
  assumes "A \<le> A'"
  shows "(\<Sum>x : A. B x) \<le> (\<Sum>x : A'. B x)"
  using assms by auto

lemma set_dep_pair_covariant_codom:
  assumes "\<And>x. A x \<Longrightarrow> B x \<le> B' x"
  shows "(\<Sum>x : A. B x) \<le> (\<Sum>x : A. (B' x))"
  using assms by auto

lemma mono_set_pair: "mono (\<times>)" by fast

lemma mono_set_dep_pair_mk_pair: "((x : (A :: set \<Rightarrow> bool)) \<Rightarrow> B x \<Rightarrow> \<Sum>x : A. B x) mk_pair" by auto

lemma mono_set_dep_pair_fst: "((p : \<Sum>x : (A :: set \<Rightarrow> bool). B x) \<Rightarrow> A) fst" by auto

lemma mono_set_dep_pair_snd: "((p : \<Sum>x : (A :: set \<Rightarrow> bool). B x) \<Rightarrow> B (fst p)) snd" by auto


subsection \<open>Functions on Pairs\<close>

definition "uncurry f p \<equiv> f (fst p) (snd p)"

open_bundle hotg_uncurry_syntax
begin
syntax "_tuple_args"  :: "args => pttrn" ("\<langle>_\<rangle>")
end
translations
  "\<lambda>\<langle>x, y, zs\<rangle>. b" \<rightleftharpoons> "CONST uncurry (\<lambda>x \<langle>y, zs\<rangle>. b)"
  "\<lambda>\<langle>x, y\<rangle>. b" \<rightleftharpoons> "CONST uncurry (\<lambda>x y. b)"

lemma uncurry_pair_eq_app [simp]: "uncurry f \<langle>x, y\<rangle> = f x y"
  unfolding uncurry_def by simp

definition "curry f x y \<equiv> f \<langle>x, y\<rangle>"

lemma curry_eq_app_pair [simp]: "curry f x y = f \<langle>x, y\<rangle>"
  unfolding curry_def by simp

lemma curry_uncurry_eq [simp]: "curry (uncurry f) = f"
  by (intro ext) auto

lemma uncurry_curry_eq_if_is_pair [simp]: "is_pair p \<Longrightarrow> uncurry (curry f) p = f p"
  by auto

lemma mono_set_dep_pair_curry:
  "(((p : \<Sum>x : A. (B x)) \<Rightarrow> C p) \<Rightarrow> (x : (A :: set \<Rightarrow> bool)) \<Rightarrow> (y : B x) \<Rightarrow> C \<langle>x, y\<rangle>) curry"
  by fastforce

lemma mono_set_dep_pair_uncurry:
  "(((x : (A :: set \<Rightarrow> bool)) \<Rightarrow> (y : B x) \<Rightarrow> C \<langle>x, y\<rangle>) \<Rightarrow> (p : \<Sum>x : A. (B x)) \<Rightarrow> C p) uncurry"
  by fastforce

definition "swap p = \<langle>snd p, fst p\<rangle>"

lemma swap_pair_eq [simp]: "swap \<langle>x, y\<rangle> = \<langle>y, x\<rangle>" unfolding swap_def by simp

lemma swap_pair_eq' [simp]: "is_pair p \<Longrightarrow> swap p = \<langle>snd p, fst p\<rangle>"
  unfolding swap_def by simp

lemma mono_set_pair_curry: "((A :: set \<Rightarrow> bool) \<times> B \<Rightarrow> B \<times> A) swap"
  by auto


subsection \<open>Sets of Pairs\<close>

definition "set_set_dep_pair_set A B \<equiv> \<Union>a \<in> A. \<Union>y \<in> B a. {\<langle>a, y\<rangle>}"
adhoc_overloading dep_pair \<rightleftharpoons> set_set_dep_pair_set

definition "set_set_pair_set (A :: set) (B :: set) :: set \<equiv> \<Sum>(_ :: set) : A. B"
adhoc_overloading pair \<rightleftharpoons> set_set_pair_set

lemma set_set_pair_eq_set_set_dep_pair: "(A \<times> B :: set) = \<Sum>_ : A. B"
  unfolding set_set_pair_set_def by auto

lemma set_set_pair_eq_set_set_dep_pair_uhint [uhint]:
  assumes "A :: set \<equiv> A'"
  and "\<And>x. B \<equiv> B' x"
  shows "A \<times> B :: set \<equiv> \<Sum>x : A'. B' x"
  using assms by (simp add: set_set_pair_eq_set_set_dep_pair)

lemma mem_set_pair_iff_mem_set_dep_pair: "p \<in> A \<times> B \<longleftrightarrow> p \<in> (\<Sum>_ : A. B)"
  unfolding set_set_pair_eq_set_set_dep_pair by auto

lemma mem_dep_pair_if_set_dep_pair_set:
  assumes "(\<Sum>x : A. B x) p"
  shows "p \<in> \<Sum>x : A. B x"
  using assms unfolding set_set_dep_pair_set_def by fastforce

lemma set_dep_pair_set_if_mem_dep_pair:
  assumes "p \<in> \<Sum>x : A. B x"
  shows "(\<Sum>x : A. B x) p"
  using assms unfolding set_set_dep_pair_set_def by blast

lemma mem_of_dep_pair_eq_set_dep_pair_set [simp, set_to_HOL_simp]:
  "mem_of (\<Sum>x : A. B x) = (\<Sum>x : A. B x)"
  using mem_dep_pair_if_set_dep_pair_set set_dep_pair_set_if_mem_dep_pair
  by (intro ext) (auto simp: mem_of_eq)

corollary mem_dep_pair_iff_set_dep_pair_set [iff]: "p \<in> (\<Sum>x : A. B x) \<longleftrightarrow> (\<Sum>x : A. B x) p"
  by (simp flip: mem_of_iff)

lemma mem_pair_if_set_pair_set:
  assumes "(A \<times> B) p"
  shows "p \<in> A \<times> B"
  by (urule mem_dep_pair_if_set_dep_pair_set) (urule assms)

lemma set_pair_set_if_mem_pair:
  assumes "p \<in> A \<times> B"
  shows "(A \<times> B) p"
  using assms by (urule set_dep_pair_set_if_mem_dep_pair)

lemma mem_of_pair_eq_set_pair_set [simp, set_to_HOL_simp]: "mem_of (A \<times> B) = A \<times> B"
  by (urule mem_of_dep_pair_eq_set_dep_pair_set)

corollary mem_pair_iff_set_pair_set [iff]: "p \<in> (A \<times> B) \<longleftrightarrow> (A \<times> B) p"
  by (urule mem_dep_pair_iff_set_dep_pair_set)

context
  notes set_to_HOL_simp[simp, symmetric, simp del]
begin

lemma set_dep_pair_empty_dom_eq_empty [simp]: "(\<Sum>x : {}. B x) = {}"
  by (urule set_dep_pair_bottom_dom_eq_bottom)

lemma set_dep_pair_empty_codom_eq_empty [simp]: "(\<Sum>x : A. {}) = {}"
  by (urule set_dep_pair_bottom_codom_eq_bottom)

lemma pair_eq_empty_iff_eq_empty_or [iff]: "A \<times> B = {} \<longleftrightarrow> A = {} \<or> B = {}"
  by (urule set_pair_eq_bottom_iff_eq_bottom_or)

lemma singleton_pair_singleton_eq_singleton [simp]: "{a} \<times> {b} = {\<langle>a, b\<rangle>}"
  by (urule eq_set_pair_eq_eq_eq_mk_pair)

lemma dep_pair_subset_pair_idx_union: "(\<Sum>x : A. B x) \<subseteq> (A \<times> (\<Union>x \<in> A. B x))"
  by (urule set_dep_pair_le_set_pair_idx_union)

lemma bex_set_set_dep_pair_iff_bex_bex [iff]:
  "(\<exists>z : (\<Sum>x : A. B x :: set). P z) \<longleftrightarrow> (\<exists>x : A. \<exists>y : B x. P \<langle>x, y\<rangle>)"
  by (urule bex_set_dep_pair_iff_bex_bex)

lemma ball_set_set_dep_pair_iff_ball_ball [iff]:
  "(\<forall>z : (\<Sum>x : A. B x :: set). P z) \<longleftrightarrow> (\<forall>x : A. \<forall>y : B x. P \<langle>x, y\<rangle>)"
  by (urule ball_set_dep_pair_iff_ball_ball)

lemma dep_pair_subset_if_subset_dom:
  assumes "A \<subseteq> A'"
  shows "(\<Sum>x : A. B x) \<subseteq> (\<Sum>x : A'. B x)"
  using assms by (urule set_dep_pair_le_if_le_dom)

lemma set_set_dep_pair_covariant_codom:
  assumes "\<And>x. x \<in> A \<Longrightarrow> B x \<subseteq> B' x"
  shows "(\<Sum>x : A. B x) \<subseteq> (\<Sum>x : A. (B' x))"
  using assms by (urule set_dep_pair_covariant_codom) simp

end

lemma mono_subset_pair: "((\<subseteq>) \<Rightarrow> (\<subseteq>) \<Rrightarrow> (\<subseteq>)) (\<times>)" by fast

end