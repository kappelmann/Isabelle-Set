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
  by (subst singleton_dup[of a], subst singleton_dup[of c])
    (auto simp: pair_eq_iff)

lemmas opair_inject = opair_eq_iff [THEN iffD1, THEN conjE, elim!]
lemmas opair_inject1 = opair_eq_iff [THEN iffD1, THEN conjunct1]
lemmas opair_inject2 = opair_eq_iff [THEN iffD1, THEN conjunct2]

lemma opair_nonempty: "\<langle>a, b\<rangle> \<noteq> {}"
  unfolding opair_def by (blast elim: equalityE)

lemmas opair_emptyE = opair_nonempty [THEN notE, elim!]

declare sym [THEN opair_emptyE, elim!]

lemma opair_ne_fst: "\<langle>a, b\<rangle> = a \<Longrightarrow> P"
  unfolding opair_def by (auto intro: mem_asymE)

lemma opair_ne_snd: "\<langle>a, b\<rangle> = b \<Longrightarrow> P"
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

lemma opair_conv [simp]: "p = \<langle>a, b\<rangle> \<Longrightarrow> p = \<langle>fst p, snd p\<rangle>"
  by simp

lemma opair_not_in_fst: "\<langle>a, b\<rangle> \<notin> a"
  unfolding opair_def by (auto intro: mem_3_cycle)

lemma opair_not_in_snd: "\<langle>a, b\<rangle> \<notin> b"
  unfolding opair_def by (auto intro: equalityI' dest: mem_3_cycle)


subsection \<open>Set theoretic dependent pair\<close>

definition pairset :: \<open>set \<Rightarrow> (set \<Rightarrow> set) \<Rightarrow> set\<close>
  where "pairset A B \<equiv> \<Union>x \<in> A. \<Union>y \<in> B x. {\<langle>x, y\<rangle>}"

syntax
  "_pairset" :: \<open>[pttrn, set, set \<Rightarrow> set] \<Rightarrow> set\<close> ("\<Sum>_\<in> _./ _" [0, 0, 100])
translations
  "\<Sum>x\<in> A. B" \<rightleftharpoons> "CONST pairset A (\<lambda>x. B)"

abbreviation prodset :: \<open>set \<Rightarrow> set \<Rightarrow> set\<close> (infixr "\<times>" 80)
  where "A \<times> B \<equiv> \<Sum>_\<in> A. B"

lemma pairset_iff [simp]: "\<langle>a, b\<rangle> \<in> \<Sum>x\<in> A. (B x) \<longleftrightarrow> a \<in> A \<and> b \<in> B a"
  by (auto simp: pairset_def)

lemma pairsetI [intro!]: "\<lbrakk>a \<in> A; b \<in> B a\<rbrakk> \<Longrightarrow> \<langle>a, b\<rangle> \<in> \<Sum>x\<in> A. (B x)"
  by simp

lemma pairsetI2 [elim]: "\<lbrakk>p = \<langle>a, b\<rangle>; a \<in> A; b \<in> B a\<rbrakk> \<Longrightarrow> p \<in> \<Sum>x\<in> A. (B x)"
  by simp

lemmas pairsetD1 = pairset_iff [THEN iffD1, THEN conjunct1]
lemmas pairsetD2 = pairset_iff [THEN iffD1, THEN conjunct2]

lemma pairsetE [elim!]:
  "\<lbrakk>c \<in> \<Sum>x\<in> A. (B x); \<And>x y. \<lbrakk>x \<in> A; y \<in> B x; c = \<langle>x, y\<rangle>\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (unfold pairset_def, blast)

lemma pairsetE2 [elim!]:
  "\<lbrakk>\<langle>a, b\<rangle> \<in> \<Sum>x\<in> A. (B x); \<lbrakk>a \<in> A; b \<in> B a\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (unfold pairset_def, blast)

lemma pairset_cong:
  "\<lbrakk>A = A'; \<And>x. x \<in> A' \<Longrightarrow> B x = B' x\<rbrakk> \<Longrightarrow> \<Sum>x\<in> A. (B x) = \<Sum>x\<in> A'. (B' x)"
  by (simp add: pairset_def)

lemma pairset_fst: "p \<in> \<Sum>x\<in> A. (B x) \<Longrightarrow> fst p \<in> A"
  by auto

lemma pairset_snd: "p \<in> \<Sum>x\<in> A. (B x) \<Longrightarrow> snd p \<in> B (fst p)"
  by auto

lemma pairset_elem [simp]: "p \<in> \<Sum>x\<in> P. (B x) \<Longrightarrow> p = \<langle>fst p, snd p\<rangle>"
  by auto

lemma pairset_subset_elem [simp]:
  "\<lbrakk>p \<in> R; R \<subseteq> \<Sum>x\<in> A. (B x)\<rbrakk> \<Longrightarrow> p = \<langle>fst p, snd p\<rangle>"
  by auto

lemma pairset_subset_elemE:
  "\<lbrakk>p \<in> R; R \<subseteq> \<Sum>x\<in> A. (B x); \<And>a b. \<lbrakk>a \<in> A; b \<in> B a; p = \<langle>a, b\<rangle>\<rbrakk> \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q"
  by auto

lemma pairset_empty_index [simp]: "\<Sum>x\<in> {}. (B x) = {}"
  by (rule extensionality) auto

lemma pairset_empty_sets [simp]: "\<Sum>x\<in> A. {} = {}"
  by (rule extensionality) auto

lemma pairset_empty_iff: "A \<times> B = {} \<longleftrightarrow> A = {} \<or> B = {}"
  by (auto intro!: equalityI')

lemma setprod_singletons [simp]: "{a} \<times> {b} = {\<langle>a, b\<rangle>}"
  by (rule equalityI) auto

lemma pairset_subset_setprod: "\<Sum>x\<in> A. (B x) \<subseteq> A \<times> (\<Union>x\<in> A. (B x))"
  by auto


subsection \<open>Monotonicity\<close>

lemma setprod_monotone: "A \<subseteq> A' \<Longrightarrow> B \<subseteq> B' \<Longrightarrow> A \<times> B \<subseteq> A' \<times> B'" by auto
lemma setprod_monotone1: "A \<subseteq> A' \<Longrightarrow> A \<times> B \<subseteq> A' \<times> B" by auto
lemma setprod_monotone2: "B \<subseteq> B' \<Longrightarrow> A \<times> B \<subseteq> A \<times> B'" by auto


subsection \<open>Functions on dependent pairs\<close>

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
  by (erule pairsetE) auto

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

lemma split_paired_bex_pair [simp]:
  "(\<exists>z \<in> \<Sum>x\<in> A. (B x). P z) \<longleftrightarrow> (\<exists>x \<in> A. \<exists>y \<in> B x. P \<langle>x, y\<rangle>)"
  by blast

lemma split_paired_ball_pair [simp]:
  "(\<forall>z \<in> \<Sum>x\<in> A. (B x). P z) \<longleftrightarrow> (\<forall>x \<in> A. \<forall>y \<in> B x. P \<langle>x,y\<rangle>)"
  by blast


subsection \<open>Universes\<close>

lemma univ_pairset_closed [intro]:
  assumes
    "A \<in> univ U"
    "\<And>x. x \<in> A \<Longrightarrow> B x \<in> univ U"
  shows
    "\<Sum>x \<in> A. (B x) \<in> univ U"
  unfolding pairset_def opair_def
  by (auto intro: univ_transitive assms
      intro!: univ_union_closed univ_replacement_closed univ_cons_closed)

lemma univ_opair_closed [intro]:
  "x \<in> univ A \<Longrightarrow> y \<in> univ A \<Longrightarrow> \<langle>x, y\<rangle> \<in> univ A"
  unfolding opair_def by auto

lemma setprod_univ_subset_univ:
  "X \<subseteq> univ A \<times> univ A \<Longrightarrow> X \<subseteq> univ A"
  by auto

lemma univ_setprod_subset_closed [intro]:
  "X \<subseteq> univ A \<Longrightarrow> Y \<subseteq> univ A \<Longrightarrow> X \<times> Y \<subseteq> univ A"
  by auto

lemma [derive]:
  "\<lbrakk>A: Element (univ U); B: Element (univ U)\<rbrakk> \<Longrightarrow> A \<times> B: Element (univ U)"
  "\<lbrakk>A: Subset (univ U); B: Subset (univ U)\<rbrakk> \<Longrightarrow> A \<times> B: Subset (univ U)"
  by unfold_types auto


subsection \<open>Soft types\<close>

lemma
  prod_type [type]: "(\<times>): Subset A \<Rightarrow> Subset B \<Rightarrow> Subset (A \<times> B)" and
  opair_type [type]: "opair: Element A \<Rightarrow> Element B \<Rightarrow> Element (A \<times> B)" and
  fst_type [type]: "fst: Element (A \<times> B) \<Rightarrow> Element A" and
  snd_type [type]: "snd: Element (A \<times> B) \<Rightarrow> Element B"
  by unfold_types auto

lemma setprod_nonempty [derive]:
  "non-empty A \<Longrightarrow> non-empty B \<Longrightarrow> non-empty (A \<times> B)"
  unfolding non_def empty_def by auto

text \<open>
The following are more general but also makes elaboration more complex, so we
don't declare them by default for now.
\<close>

lemma opair_dep_type:
  "opair: (x: Element A) \<Rightarrow> Element (B x) \<Rightarrow> Element (\<Sum>x\<in> A. (B x))"
  by unfold_types auto

lemma fst_dep_type:
  "fst: Element (\<Sum>x\<in> A. (B x)) \<Rightarrow> Element A"
  by unfold_types auto

lemma snd_dep_type:
  "snd: (p: Element (\<Sum>x\<in> A. (B x))) \<Rightarrow> Element (B (fst p))"
  by unfold_types auto


end
