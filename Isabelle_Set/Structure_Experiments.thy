theory Structure_Experiments
imports Function Ordered_Pairs

begin

text \<open>
  Experiments with alternative implementations of structures, possibly on top of
  the locale infrastructure.
\<close>

section \<open>Structures\<close>

text \<open>
  The underlying locale-ic implementation of structures might look something
  like this:
\<close>

locale Pointed_Set_Impl =
  fixes
    carrier and
    point ("*")
  assumes
    point: "* \<in> carrier"

locale Binop_Set_Impl =
  fixes
    carrier and
    op (infixl "\<cdot>" 80)
  assumes
    closure: "(\<cdot>) : element carrier \<Rightarrow> element carrier \<Rightarrow> element carrier"

locale Monoid_Impl = Pointed_Set_Impl _ id + Binop_Set_Impl for id +
  assumes
    assoc: "\<forall>x \<in> carrier. \<forall>y \<in> carrier. \<forall>z \<in> carrier. x \<cdot> (y \<cdot> z) = x \<cdot> y \<cdot> z" and
    idl: "\<forall>x \<in> carrier. id \<cdot> x = x" and
    idr: "\<forall>x \<in> carrier. x \<cdot> id = x"
  begin
    lemmas id = point
  end

print_locale! Monoid_Impl

text \<open>
  On top of this, we'd like to define the soft type of monoids parametrized by
  the carrier set, with the monoid operation and identity bundled.

  This involves us starting to think about a choice of encoding for structures:
  tuples or functions?...
\<close>

text \<open>
  We want the statement \<open>M : Monoid A\<close> to mean
    \<open>Monoid_Impl (carrier M) (id M) (op M) \<and> carrier M = A\<close>.
\<close>

lemma "Monoid_Impl M op id"
  proof
  oops

definition [typedef]: "Monoid A =
  type (\<lambda>M.
    fst M = A \<and>
    Monoid_Impl A (fst (snd M)) (snd (snd M)))"
  \<comment>\<open>M = \<langle>carrier, \<langle>op, id\<rangle>\<rangle>\<close>


section \<open>Functions\<close>

text \<open>
  Conversions between set-theoretic and HOL functions.

  Every HOL function \<open>f\<close> can be cast to a set-theoretic one by wrapping \<open>f\<close> in
  \<open>lambda A\<close> for a suitable domain \<open>A\<close>.

  To interface set-theoretic structures with locales we maybe want the following:

  Given a set-theoretic function \<open>f : A \<rightarrow> B\<close> (a component of some set-theoretic
  structure), we can form a HOL function by mapping values outside A to some
  default value, say the empty set.

  Then we want to coerce set-theoretic lambdas to HOL lambdas to work back in
  the localic implementation of structures.

  So we want something like a wrapper of type \<open>set \<Rightarrow> ('a \<Rightarrow> 'b)\<close> in order to
  cast set-theoretic functions to HOL ones.
\<close>

term "lambda A (\<lambda>x. b x)"

term "\<lambda>x \<in> A. \<lambda>y \<in> B x. \<langle>x, y\<rangle>"


end
