### from Isabelle code

$$
T \rightarrow [V\ V :: R \mid P] \\
T \rightarrow [P \longrightarrow R] \\
T \rightarrow [P \longrightarrow V\ V :: R \mid P] \\
T \rightarrow T \Rrightarrow T \\
T \rightarrow [V\ V :: R] \Rrightarrow T \\
T \rightarrow [V\ V :: R \mid P] \Rrightarrow T \\
T \rightarrow [P \longrightarrow V\ V :: R] \Rrightarrow T \\
T \rightarrow [P \longrightarrow V\ V :: R \mid P] \Rrightarrow T
$$

### simplified

$$
T \rightarrow R \\
T \rightarrow [V\ V :: R \mid P] \\
T \rightarrow [P \longrightarrow R] \\
T \rightarrow [P \longrightarrow V\ V :: R \mid P] \\
T \rightarrow T \Rrightarrow T \\
T \rightarrow [V\ V :: R] \Rrightarrow T
$$

### semantics

$$
[x\ y :: R \mid P] \leadsto \lambda a\ b\ldotp R\ a\ b \land P[x\backslash{}a, y\backslash{}b] \\
[P \longrightarrow R] \leadsto \lambda a\ b\ldotp P \longrightarrow R\ a\ b \\
[P \longrightarrow x\ y :: R \mid P] \leadsto \lambda a\ b\ldotp P \longrightarrow R\ a\ b \land P[x\backslash{}a, y\backslash{}b] \\
R \Rrightarrow S \leadsto \lambda a\ b\ldotp \forall x\ y\ldotp R\ x\ y \longrightarrow S\ (a\ x)\ (b\ y) \\
[x\ y :: R] \Rrightarrow S \leadsto \lambda a\ b\ldotp \forall x\ y\ldotp R\ x\ y \longrightarrow S[x\backslash{}a, y\backslash{}b]\ (a\ x)\ (b\ y) \\
[x\ y :: R \mid P] \Rrightarrow S \leadsto \lambda f\ g\ldotp \forall a\ b\ldotp (R\ a\ b \land P[x\backslash{}a, y\backslash{}b] \longrightarrow S[x\backslash{}a, y\backslash{}b]\ (f\ a)\ (g\ b)) \\
[P \longrightarrow x\ y :: R] \Rrightarrow S \leadsto \lambda f\ g\ldotp \forall a\ b\ldotp (P \longrightarrow R\ a\ b) \longrightarrow S[x\backslash{}a, y\backslash{}b]\ (f\ a)\ (g\ b) \\
[P \longrightarrow x\ y :: R \mid Q] \Rrightarrow S \leadsto \lambda f\ g\ldotp \forall a\ b\ldotp (P \longrightarrow R\ a\ b \land Q[x\backslash{}a, y\backslash{}b]) \longrightarrow S[x\backslash{}a, y\backslash{}b]\ (f\ a)\ (g\ b)
$$

