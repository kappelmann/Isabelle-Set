section \<open>Ordered pairs and dependent pair type/indexed disjoint unions\<close>

theory Ordered_Pair
imports Set_Theory

begin


subsection \<open>Ordered pairs, tuples\<close>

text \<open>
  Defining the ordered pair "symmetrically" as @{term "{{a, a}, {a, b}}"} simplifies
  proofs.
\<close>

definition opair :: \<open>set \<Rightarrow> set \<Rightarrow> set\<close>
  where "opair a b \<equiv> {{a, a}, {a, b}}"

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
  by (simp add: opair_def pair_eq_iff) blast

lemmas opair_inject = opair_eq_iff [THEN iffD1, THEN conjE, elim!]
lemmas opair_inject1 = opair_eq_iff [THEN iffD1, THEN conjunct1]
lemmas opair_inject2 = opair_eq_iff [THEN iffD1, THEN conjunct2]

lemma opair_nonempty: "\<langle>a, b\<rangle> \<noteq> {}"
  apply (unfold opair_def)
  apply (blast elim: equalityE)
  done

lemmas opair_emptyD = opair_nonempty [THEN notE, elim!]

declare sym [THEN opair_emptyD, elim!]

lemma opair_neq_fst: "\<langle>a, b\<rangle> = a \<Longrightarrow> P"
  unfolding opair_def by (auto intro: mem_asymE)

lemma opair_neq_snd: "\<langle>a, b\<rangle> = b \<Longrightarrow> P"
proof (unfold opair_def)
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
  unfolding opair_def by (auto intro: equalityI dest: mem_cycle3)


subsection \<open>Indexed disjoint unions, aka \<Sigma>-types\<close>

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
  by (auto intro!: equalityI)

lemma prod_singletons [simp]: "{a} \<times> {b} = {\<langle>a, b\<rangle>}"
  by (rule extensionality) auto


subsection \<open>Projections @{term fst} and @{term snd}\<close>

lemma Pair_fst: "p \<in> \<Sum>x\<in> A. (B x) \<Longrightarrow> fst p \<in> A"
  by auto

lemma Pair_snd: "p \<in> \<Sum>x\<in> A. (B x) \<Longrightarrow> snd p \<in> B (fst p)"
  by auto

lemma Pair_mem_conv [simp]: "p \<in> \<Sum>x\<in> P. (B x) \<Longrightarrow> \<langle>fst p, snd p\<rangle> = p"
  by auto

corollary prod_mem_conv [simp]: "p \<in> A \<times> B \<Longrightarrow> \<langle>fst p, snd p\<rangle> = p"
  by (fact Pair_mem_conv)

lemma prod_subset_mem_conv [simp]: "\<lbrakk>p \<in> R; R \<subseteq> A \<times> B\<rbrakk> \<Longrightarrow> \<langle>fst p, snd p\<rangle> = p"
  by auto

lemma prod_subset_mem_elim:
  "\<lbrakk>p \<in> R; R \<subseteq> A \<times> B; \<And>a b. \<lbrakk>a \<in> A; b \<in> B; p = \<langle>a, b\<rangle>\<rbrakk> \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q"
  by auto


subsection \<open>Monotonicity\<close>

lemma prod_monotone: "A \<subseteq> A' \<Longrightarrow> B \<subseteq> B' \<Longrightarrow> A \<times> B \<subseteq> A' \<times> B'"
  by auto

lemma prod_monotone1T [derive]:
  "A : subset A' \<Longrightarrow> x : element (A \<times> B) \<Longrightarrow> x : element (A' \<times> B)"
  by squash_types auto

lemma prod_monotone2T [derive]:
  "B : subset B' \<Longrightarrow> x : element (A \<times> B) \<Longrightarrow> x : element (A \<times> B')"
  by squash_types auto


subsection \<open>Functions on \<Sigma>-type\<close>

definition split :: "(set \<Rightarrow> set \<Rightarrow> 'a) \<Rightarrow> set \<Rightarrow> 'a" \<comment>\<open>for pattern-matching\<close>
  where "split f \<equiv> \<lambda>p. f (fst p) (snd p)"

(* LP: Patterns - extends pre-defined type "pttrn" used in abstractions *)
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
  "\<lbrakk>p \<in> \<Sum>x\<in> A. (B x); \<And>x y.\<lbrakk>x \<in> A; y \<in> B x\<rbrakk> \<Longrightarrow> c x y \<in> C \<langle>x,y\<rangle>\<rbrakk> \<Longrightarrow> split c p \<in> C p"
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

text \<open>Complex rules for disjoint union.\<close>

lemma split_paired_Bex_Pair [simp]:
  "(\<exists>z \<in> \<Sum>x\<in> A. (B x). P z) \<longleftrightarrow> (\<exists>x \<in> A. \<exists>y \<in> B x. P \<langle>x, y\<rangle>)"
  by blast

lemma split_paired_Ball_Pair [simp]:
  "(\<forall>z \<in> \<Sum>x\<in> A. (B x). P z) \<longleftrightarrow> (\<forall>x \<in> A. \<forall>y \<in> B x. P \<langle>x,y\<rangle>)"
  by blast


subsection \<open>Typing rules\<close>

lemma
  opair_type [type]: "opair : element A \<Rightarrow> element B \<Rightarrow> element (A \<times> B)" and
  fst_type [type]: "fst : element (A \<times> B) \<Rightarrow> element A" and
  snd_type [type]: "snd : element (A \<times> B) \<Rightarrow> element B"

  by squash_types auto

text \<open>
  The following is more general but also makes elaboration more complex, so we do not
  declare it by default for now.
\<close>

lemma opair_dependent_type:
  "opair : (x : element A) \<Rightarrow> element (B x) \<Rightarrow> element (Pair A B)"
  by squash_types auto

lemma prod_subset [derive]: "A : subset U \<Longrightarrow> B : subset V \<Longrightarrow> A \<times> B : subset (U \<times> V)"
  by squash_types auto

lemma split_paired_Ball:
  "(\<forall>x: element (A \<times> B). P x) \<longleftrightarrow> (\<forall>a : element A. \<forall>b : element B. P \<langle>a, b\<rangle>)"
  by squash_types auto

lemma Univ_closed_opairT [derive]:
  "x : element (Univ A) \<Longrightarrow> y : element (Univ A) \<Longrightarrow> \<langle>x, y\<rangle> : element (Univ A)"
  unfolding opair_def by discharge_types

lemma Univ_prod_subset [derive]:
  "x : subset (Univ A \<times> Univ A) \<Longrightarrow> x : subset (Univ A)"
  using Univ_closed_opairT
  by squash_types auto

lemma Univ_subset_closed_prod [derive]:
  "X : subset (Univ A) \<Longrightarrow> Y : subset (Univ A) \<Longrightarrow> X \<times> Y : subset (Univ A)"
  by discharge_types


end
