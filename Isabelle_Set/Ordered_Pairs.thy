section \<open>Ordered pairs and \<Sigma>-type\<close>

theory Ordered_Pairs
imports Set_Theory

begin

definition opair :: \<open>set \<Rightarrow> set \<Rightarrow> set\<close>
  where "opair a b \<equiv> {{a}, {a, b}}"

definition fst :: \<open>set \<Rightarrow> set\<close>
  where "fst p \<equiv> THE a. \<exists>b. p = opair a b"

definition snd :: \<open>set \<Rightarrow> set\<close>
  where "snd p \<equiv> THE b. \<exists>a. p = opair a b"

syntax
  "_tuple" :: \<open>args \<Rightarrow> set\<close> ("\<langle>(_)\<rangle>")
translations
  "\<langle>x, y, z\<rangle>" \<rightleftharpoons> "\<langle>x, \<langle>y, z\<rangle>\<rangle>"
  "\<langle>x, y\<rangle>" \<rightleftharpoons> "CONST opair x y"

lemma opair_eq_iff [simp]: "\<langle>a, b\<rangle> = \<langle>c, d\<rangle> \<longleftrightarrow> a = c \<and> b = d"
  unfolding opair_def
  by
    (subst singleton_dup[of a], subst singleton_dup[of c])
    (auto simp: pair_eq_iff)

lemmas opair_inject = opair_eq_iff [THEN iffD1, THEN conjE, elim!]
lemmas opair_inject1 = opair_eq_iff [THEN iffD1, THEN conjunct1]
lemmas opair_inject2 = opair_eq_iff [THEN iffD1, THEN conjunct2]

lemma opair_nonempty: "\<langle>a, b\<rangle> \<noteq> {}"
  unfolding opair_def by (blast elim: equalityE)

lemmas opair_emptyD = opair_nonempty [THEN notE, elim!]

declare sym [THEN opair_emptyD, elim!]

lemma opair_neq_fst: "\<langle>a, b\<rangle> = a \<Longrightarrow> P"
  unfolding opair_def by (auto intro: mem_asymE)

lemma opair_neq_snd: "\<langle>a, b\<rangle> = b \<Longrightarrow> P"
unfolding opair_def
proof (subst (asm) singleton_dup[of a])
  assume *: "{{a, a}, {a, b}} = b"
  have "{a, b} \<in> {{a, a}, {a, b}}" by auto
  hence "{a, b} \<in> b" by (simp add: *)
  moreover have "b \<in> {a, b}" by auto
  ultimately show "P" by (rule mem_asymE)
qed

lemma fst_conv [simp]: "fst \<langle>a,b\<rangle> = a"
  by (simp add: fst_def)

lemma snd_conv [simp]: "snd \<langle>a,b\<rangle> = b"
  by (simp add: snd_def)

lemma opair_conv [simp]: "p = \<langle>a, b\<rangle> \<Longrightarrow> \<langle>fst p, snd p\<rangle> = p"
  by simp

lemma opair_not_in_fst: "\<langle>a, b\<rangle> \<notin> a"
  unfolding opair_def by (auto intro: mem_cycle3)

lemma opair_not_in_snd: "\<langle>a, b\<rangle> \<notin> b"
  unfolding opair_def by (auto intro: equalityI' dest: mem_cycle3)


subsection \<open>Dependent pairs aka \<Sigma>-type\<close>

definition Pair :: \<open>set \<Rightarrow> (set \<Rightarrow> set) \<Rightarrow> set\<close>
  where "Pair A B \<equiv> \<Union>x \<in> A. \<Union>y \<in> B x. {\<langle>x, y\<rangle>}"

syntax
  "_Pair" :: \<open>[pttrn, set, set \<Rightarrow> set] \<Rightarrow> set\<close> ("\<Sum>_\<in> _./ _" [0, 0, 100])
translations
  "\<Sum>x\<in> A. B" \<rightleftharpoons> "CONST Pair A (\<lambda>x. B)"

abbreviation prod :: \<open>set \<Rightarrow> set \<Rightarrow> set\<close> (infixr "\<times>" 80)
  where "A \<times> B \<equiv> \<Sum>_\<in> A. B"

lemma Pair_iff [simp]: "\<langle>a, b\<rangle> \<in> \<Sum>x\<in> A. (B x) \<longleftrightarrow> a \<in> A \<and> b \<in> B a"
  by (auto simp: Pair_def)

lemma PairI [intro!]: "\<lbrakk>a \<in> A; b \<in> B a\<rbrakk> \<Longrightarrow> \<langle>a, b\<rangle> \<in> \<Sum>x\<in> A. (B x)"
  by simp

lemma PairI2 [elim]: "\<lbrakk>p = \<langle>a, b\<rangle>; a \<in> A; b \<in> B a\<rbrakk> \<Longrightarrow> p \<in> \<Sum>x\<in> A. (B x)"
  by simp

lemmas PairD1 = Pair_iff [THEN iffD1, THEN conjunct1]
lemmas PairD2 = Pair_iff [THEN iffD1, THEN conjunct2]

(* LP: The general elimination rule *)
lemma PairE [elim!]:
  "\<lbrakk>c \<in> \<Sum>x\<in> A. (B x); \<And>x y. \<lbrakk>x \<in> A; y \<in> B x; c = \<langle>x, y\<rangle>\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (unfold Pair_def, blast)

lemma PairE2 [elim!]:
  "\<lbrakk>\<langle>a, b\<rangle> \<in> \<Sum>x\<in> A. (B x); \<lbrakk>a \<in> A; b \<in> B a\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (unfold Pair_def, blast)

lemma Pair_cong:
  "\<lbrakk>A = A'; \<And>x. x \<in> A' \<Longrightarrow> B x = B' x\<rbrakk> \<Longrightarrow> \<Sum>x\<in> A. (B x) = \<Sum>x\<in> A'. (B' x)"
  by (simp add: Pair_def)

lemma Pair_empty_index [simp]: "\<Sum>x\<in> {}. (B x) = {}"
  by (rule extensionality) auto

lemma Pair_empty_sets [simp]: "\<Sum>x\<in> A. {} = {}"
  by (rule extensionality) auto

lemma Pair_empty_iff: "A \<times> B = {} \<longleftrightarrow> A = {} \<or> B = {}"
  by (auto intro!: equalityI')

lemma prod_singletons [simp]: "{a} \<times> {b} = {\<langle>a, b\<rangle>}"
  by (rule equalityI) auto

lemma Pair_subset_prod: "\<Sum>x\<in> A. (B x) \<subseteq> A \<times> (\<Union>x\<in> A. (B x))"
  by auto

lemma Pair_fst: "p \<in> \<Sum>x\<in> A. (B x) \<Longrightarrow> fst p \<in> A"
  by auto

lemma Pair_snd: "p \<in> \<Sum>x\<in> A. (B x) \<Longrightarrow> snd p \<in> B (fst p)"
  by auto

lemma Pair_elem [simp]: "p \<in> \<Sum>x\<in> P. (B x) \<Longrightarrow> p = \<langle>fst p, snd p\<rangle>"
  by auto

lemma Pair_subset_elem [simp]:
  "\<lbrakk>p \<in> R; R \<subseteq> \<Sum>x\<in> A. (B x)\<rbrakk> \<Longrightarrow> p = \<langle>fst p, snd p\<rangle>"
  by auto

lemma Pair_subset_elemE:
  "\<lbrakk>p \<in> R; R \<subseteq> \<Sum>x\<in> A. (B x); \<And>a b. \<lbrakk>a \<in> A; b \<in> B a; p = \<langle>a, b\<rangle>\<rbrakk> \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q"
  by auto


subsection \<open>Monotonicity\<close>

lemma prod_monotone: "A \<subseteq> A' \<Longrightarrow> B \<subseteq> B' \<Longrightarrow> A \<times> B \<subseteq> A' \<times> B'" by auto
lemma prod_monotone1: "A \<subseteq> A' \<Longrightarrow> A \<times> B \<subseteq> A' \<times> B" by auto
lemma prod_monotone2: "B \<subseteq> B' \<Longrightarrow> A \<times> B \<subseteq> A \<times> B'" by auto


subsection \<open>Functions on \<Sigma>-type\<close>

definition split :: "(set \<Rightarrow> set \<Rightarrow> 'a) \<Rightarrow> set \<Rightarrow> 'a" \<comment>\<open>for pattern-matching\<close>
  where "split f \<equiv> \<lambda>p. f (fst p) (snd p)"

(*Larry: Patterns—extends pre-defined type "pttrn" used in abstractions*)
nonterminal patterns
syntax
  "_pattern"  :: "patterns => pttrn" ("\<langle>_\<rangle>")
  ""          :: "pttrn => patterns" ("_")
  "_patterns" :: "[pttrn, patterns] => patterns" ("_,/ _")
translations
  "\<lambda>\<langle>x, y, zs\<rangle>. b" \<rightleftharpoons> "CONST split (\<lambda>x \<langle>y, zs\<rangle>. b)"
  "\<lambda>\<langle>x, y\<rangle>. b" \<rightleftharpoons> "CONST split (\<lambda>x y. b)"

lemma split [simp]: "split f \<langle>a, b\<rangle> \<equiv> f a b"
  by (simp add: split_def)

lemma split_type:
  "\<lbrakk>p \<in> \<Sum>x\<in> A. (B x); \<And>x y. \<lbrakk>x \<in> A; y \<in> B x\<rbrakk> \<Longrightarrow> c x y \<in> C \<langle>x,y\<rangle>\<rbrakk> \<Longrightarrow> split c p \<in> C p"
  by (erule PairE) auto

lemma expand_split:
  "u \<in> A \<times> B \<Longrightarrow> R (split c u) \<longleftrightarrow> (\<forall>x \<in> A. \<forall>y \<in> B. u = \<langle>x,y\<rangle> \<longrightarrow> R (c x y))"
  by (force simp add: split_def)

lemma splitI: "R a b \<Longrightarrow> split R \<langle>a,b\<rangle>"
  by (simp add: split_def)

lemma splitE:
  "\<lbrakk>split R z; z \<in> \<Sum>x\<in> A. (B x); \<And>x y. \<lbrakk>z = \<langle>x, y\<rangle>; R x y\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (auto simp add: split_def)

lemma splitD: "split R \<langle>a, b\<rangle> \<Longrightarrow> R a b"
  by (simp add: split_def)

text \<open>Splitting quantifiers:\<close>

lemma split_paired_Bex_Pair [simp]:
  "(\<exists>z \<in> \<Sum>x\<in> A. (B x). P z) \<longleftrightarrow> (\<exists>x \<in> A. \<exists>y \<in> B x. P \<langle>x, y\<rangle>)"
  by blast

lemma split_paired_Ball_Pair [simp]:
  "(\<forall>z \<in> \<Sum>x\<in> A. (B x). P z) \<longleftrightarrow> (\<forall>x \<in> A. \<forall>y \<in> B x. P \<langle>x,y\<rangle>)"
  by blast

lemma split_paired_Ball: (*this should be unnecessary with the soft type translation*)
  "(\<forall>x : element (A \<times> B). P x) \<longleftrightarrow> (\<forall>a : element A. \<forall>b : element B. P \<langle>a, b\<rangle>)"
  by unfold_types auto


subsection \<open>Universes\<close>

lemma Univ_Pair_closed [intro]:
  assumes
    "A \<in> Univ U"
    "\<And>x. x \<in> A \<Longrightarrow> B x \<in> Univ U"
  shows
    "\<Sum>x \<in> A. (B x) \<in> Univ U"

  unfolding Pair_def opair_def
  by (auto intro: Univ_transitive assms
    intro!: Univ_union_closed Univ_replacement_closed Univ_cons_closed)

lemma Univ_opair_closed [intro]:
  "x \<in> Univ A \<Longrightarrow> y \<in> Univ A \<Longrightarrow> \<langle>x, y\<rangle> \<in> Univ A"
  unfolding opair_def by auto

lemma prod_Univ_subset_Univ:
  "X \<subseteq> Univ A \<times> Univ A \<Longrightarrow> X \<subseteq> Univ A"
  by auto

lemma Univ_prod_subset_closed [intro]:
  "X \<subseteq> Univ A \<Longrightarrow> Y \<subseteq> Univ A \<Longrightarrow> X \<times> Y \<subseteq> Univ A"
  by auto


subsection \<open>Typing rules\<close>

lemma
  prod_type [type]: "(\<times>) : subset A \<Rightarrow> subset B \<Rightarrow> subset (A \<times> B)" and
  opair_type [type]: "opair : element A \<Rightarrow> element B \<Rightarrow> element (A \<times> B)" and
  fst_type [type]: "fst : element (A \<times> B) \<Rightarrow> element A" and
  snd_type [type]: "snd : element (A \<times> B) \<Rightarrow> element B"
  by unfold_types auto

text \<open>
  The following are more general but also makes elaboration more complex, so we
  don't declare them by default for now.
\<close>

lemma opair_dep_type:
  "opair : (x : element A) \<Rightarrow> element (B x) \<Rightarrow> element (\<Sum>x\<in> A. (B x))"
  by unfold_types auto

lemma fst_dep_type:
  "fst : element (\<Sum>x\<in> A. (B x)) \<Rightarrow> element A"
  by unfold_types auto

lemma snd_dep_type:
  "snd : (p : element (\<Sum>x\<in> A. (B x))) \<Rightarrow> element (B (fst p))"
  by unfold_types auto


end
