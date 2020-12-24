theory mutdata imports symmetric 
begin
section{*Main definitions*}
definition I::"scalrValueType" where [simp]: "I\<equiv> enum ''control'' ''I''"
definition  T::"scalrValueType" where [simp]: " T\<equiv> enum ''control'' '' T''"
definition  C::"scalrValueType" where [simp]: " C\<equiv> enum ''control'' '' C''"
definition  E::"scalrValueType" where [simp]: " E\<equiv> enum ''control'' '' E''"
definition true::"scalrValueType" where [simp]: "true\<equiv> boolV True"
definition false::"scalrValueType" where [simp]: "false\<equiv> boolV False"

definition n_Try::"nat \<Rightarrow> rule" where [simp]:
"n_Try  i\<equiv>
let g = (eqn (Ivar (Para (''n.st'') i) (Const I))) in
let s = (parallelList [(assign (Ivar (Para (''n.st'') i), (Const T)))]) in
guard g s"

definition n_Crit::"nat \<Rightarrow> rule" where [simp]:
"n_Crit  i\<equiv>
let g = (andForm (eqn (Ivar (Para (''n.st'') i) (Const T))) (eqn (IVar (Ident ''x'')) (Const true)) in
let s = (parallelList [(assign (Ivar (Para (''n.st'') i), (Const C))), (assign ((Ident ''x''), (Const false))), (assign (Ivar (Para (''n.data'') i), (Const memDATA)))]) in
guard g s"

definition n_Exit::"nat \<Rightarrow> rule" where [simp]:
"n_Exit  i\<equiv>
let g = (eqn (Ivar (Para (''n.st'') i) (Const C))) in
let s = (parallelList [(assign (Ivar (Para (''n.st'') i), (Const E)))]) in
guard g s"

definition n_Idle::"nat \<Rightarrow> rule" where [simp]:
"n_Idle  i\<equiv>
let g = (eqn (Ivar (Para (''n.st'') i) (Const E))) in
let s = (parallelList [(assign (Ivar (Para (''n.st'') i), (Const I))), (assign ((Ident ''memDATA''), (IVar (Para (''n.data'') i))))]) in
guard g s"

definition n_Store::"nat \<Rightarrow> rule" where [simp]:
"n_Store  i\<equiv>
let g = (eqn (Ivar (Para (''n.st'') i) (Const C))) in
let s = (parallelList [(assign ((Ident ''auxDATA''), (Const data))), (assign (Ivar (Para (''n.data'') i), (Const data)))]) in
guard g s"

definition rules::"nat \<Rightarrow> rule set" where [simp]:
"rules N \<equiv> {r.
(\<exists> i. i\<le>N\<and>r=n_Try  i) \<or>
(\<exists> i. i\<le>N\<and>r=n_Crit  i) \<or>
(\<exists> i. i\<le>N\<and>r=n_Exit  i) \<or>
(\<exists> i. i\<le>N\<and>r=n_Idle  i) \<or>
(\<exists> i. i\<le>N\<and>r=n_Store  i)
}"

definition initSpec0::"nat \<Rightarrow> formula" where [simp]:
"initSpec0 N (forallSent (down N) (\<lambda>i. (eqn (Ivar (Para (''n.st'') i) (Const I))) ))"

definition initSpec1::"nat \<Rightarrow> formula" where [simp]:
"initSpec1 N (forallSent (down N) (\<lambda>i. (eqn (Ivar (Para (''n.data'') i) (Const d))) ))"

definition initSpec2::"nat \<Rightarrow> formula" where [simp]:
"initSpec2 N \<equiv> (eqn (IVar (Ident ''x'')) (Const true)) "

definition initSpec3::"nat \<Rightarrow> formula" where [simp]:
"initSpec3 N \<equiv> (eqn (IVar (Ident ''auxDATA'')) (Const d)) "

definition initSpec4::"nat \<Rightarrow> formula" where [simp]:
"initSpec4 N \<equiv> (eqn (IVar (Ident ''memDATA'')) (Const d)) "

definition allInitSpecs::"nat \<Rightarrow> formula list" where [simp]:
"allInitSpecs N \<equiv> [
(initSpec0 N),
(initSpec1 N),
(initSpec2 N),
(initSpec3 N),
(initSpec4 N)
]"

end