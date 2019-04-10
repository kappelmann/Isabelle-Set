theory xfamily
imports xboole_0
begin

theorem xfamily_sch_3:
  assumes[ty]: "X1 be set" "X2 be set" and
    "for x being set holds x in X1 \<longleftrightarrow> P(x)"
    "for x being set holds x in X2 \<longleftrightarrow> P(x)"
  shows "X1 = X2" using xboole_0_sch_3[OF assms(1) assms(2),of P] assms (3-4) tarski_0_1 by auto

(* KP: Jak bym zrobił mtheorem, to to drugie jest słabsze? *)
thm xboole_0_sch_3 xfamily_sch_3

end
