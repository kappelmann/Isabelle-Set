theory tarski_a
imports tarski

\<comment>\<open> Tarski's Axiom A \<close>

begin

reserve x,y,z,u for object
reserve N,M,X,Y,Z for set

axiomatization where
tarski_a_th_1:
  "ex M st N in M \<and>
      (for X,Y holds X in M \<and> Y \<subseteq> X \<longrightarrow> Y in M) \<and>
      (for X st X in M ex Z st Z in M \<and> (for Y st Y \<subseteq> X holds Y in Z)) \<and>
      (for X holds X \<subseteq> M \<longrightarrow> X,M are_equipotent \<or> X in M)"


end
