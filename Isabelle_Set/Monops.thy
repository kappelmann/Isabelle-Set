section \<open>More monotone operators\<close>

theory Monops
imports Ordered_Pairs Subset

begin

lemma monop_prodI [derive]:
  assumes
    A: "A: monop (univ X)" and
    B: "B: monop (univ X)"
  shows
    "(\<lambda>x. A x \<times> B x): monop (univ X)"
  by (intro monopI univ_prod_subset_closed) (auto dest: monopE[OF A] monopE[OF B])


end
