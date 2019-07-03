theory Structure_Examples
imports "../Structure"
begin


subsection \<open>Some structure declarations\<close>

struct magma = "\<lparr> (carrier A) (op op).
  A : non-empty\<cdot>set
  \<and> op : element(A \<rightarrow> A \<rightarrow> A) \<rparr>"

thm magma_typedef
thm carrier_lbldef


subsection \<open>Monoids\<close>

struct monoid = "\<lparr> (carrier A) (op op) (neut e).
  A: non-empty\<cdot>set \<and>
  op: element (A \<rightarrow> A \<rightarrow> A) \<and>
  e: element A \<and>

  (\<forall>x \<in> A. op`x`e = x \<and> op`e`x = x) \<and>
  (\<forall>x \<in> A. \<forall>y \<in> A. \<forall>z \<in> A. op`x`(op`y`z) = op`(op`x`y)`z)
\<rparr>"


text \<open>Define the additive monoid Z2:\<close>

definition zero ("0") where "0 \<equiv> {}"
definition one ("1") where "1 \<equiv> Succ 0"
definition "Z2 \<equiv> \<lparr>
  carrier = {0, 1},
  op = \<lambda>x \<in> {0, 1}. if x = 0 then \<lambda>y \<in> {0, 1}. y else \<lambda>y \<in> {0,1}. if y = 0 then 1 else 0,
  neut = 0
\<rparr>"


lemma "Z2 : monoid"
unfolding monoid_typedef adjective_def
  oops


end
