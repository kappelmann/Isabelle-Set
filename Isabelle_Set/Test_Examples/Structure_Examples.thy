theory Structure_Examples
imports "../Isabelle_Set"

begin

definition a where "a \<equiv> {}"

term "(;; x. carrier: non-empty\<cdot>set ;;)"

term "(;; m. carrier: non-empty\<cdot>set, op: element(m`carrier \<rightarrow> m`carrier \<rightarrow> m`carrier) ;;)"

term "(;; it.
  carrier: non-empty\<cdot>set,
  op: element(it`carrier \<rightarrow> it`carrier \<rightarrow> it`carrier),
  e: element(it`carrier) where
    \<forall>x \<in> it`carrier. op`x`e = x \<and> op`e`x = x \<and>
    (\<forall>x \<in> it`carrier. \<forall>y \<in> it`carrier. \<forall>z \<in> it`carrier. op`x`(op`y`z) = op`(op`x`y)`z)
  ;;)"


struct magma = "(;; it.
  carrier: non-empty\<cdot>set,
  op: element (it`carrier \<rightarrow> it`carrier \<rightarrow> it`carrier)
;;)"

thm magma_typedef
thm carrier_lbldef

struct group = "(;; it.
  carrier: non-empty\<cdot>set,
  op: element(it`carrier \<rightarrow> it`carrier \<rightarrow> it`carrier),
  e: element(it`carrier) where
    \<forall>x \<in> it`carrier. op`x`e = x \<and> op`e`x = x \<and>
    (\<forall>x \<in> it`carrier. \<forall>y \<in> it`carrier. \<forall>z \<in> it`carrier. op`x`(op`y`z) = op`(op`x`y)`z)
  ;;)"

lemma "G : group"
  unfolding group_typedef
  oops


end
