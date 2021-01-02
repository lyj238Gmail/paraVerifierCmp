theory nMutualExBase2
  imports Symmetric
begin

text \<open>Represents four states: idle, try, critical, exit\<close>

definition I :: scalrValueType where [simp]: "I \<equiv> enum ''control'' ''I''"
definition T :: scalrValueType where [simp]: "T \<equiv> enum ''control'' ''T''"
definition C :: scalrValueType where [simp]: "C \<equiv> enum ''control'' ''C''"
definition E :: scalrValueType where [simp]: "E \<equiv> enum ''control'' ''E''"

definition true :: scalrValueType where [simp]: "true \<equiv> boolV True"
definition false :: scalrValueType where [simp]: "false \<equiv> boolV False"


subsection \<open>Definitions of Parameterized Rules\<close>

text \<open>If currently idle, can move to try
  n[i] = I \<rightarrow> n[i] := T
\<close>
definition n_Try :: "nat \<Rightarrow> rule" where [simp]:
  "n_Try i \<equiv>
    let g = (eqn (IVar (Para ( ''n'') i)) (Const I)) in
    let s = (parallelList [(assign ((Para ( ''n'') i), (Const T)))]) in
      guard g s"

text \<open>Enter critical region
  n[i] = T \<and> x = True \<rightarrow> n[i] := C; x := False
\<close>
definition n_Crit :: "nat \<Rightarrow> rule" where [simp]:
  "n_Crit i \<equiv>
    let g = (andForm (eqn (IVar (Para ( ''n'') i)) (Const T)) (eqn (IVar (Ident ''x'')) (Const true))) in
    let s = (parallelList [(assign ((Para ( ''n'') i), (Const C))), (assign ((Ident ''x''), (Const false)))]) in
      guard g s"

text \<open>Exit critical region
  n[i] = C \<rightarrow> n[i] := E
\<close>
definition n_Exit::"nat \<Rightarrow> rule" where [simp]:
  "n_Exit i \<equiv>
    let g = (eqn (IVar (Para ( ''n'') i)) (Const C)) in
    let s = (parallelList [(assign ((Para ( ''n'') i), (Const E)))]) in
      guard g s"

text \<open>Move to idle
  n[i] = E \<rightarrow> n[i] := I; x := True
\<close>
definition n_Idle :: "nat \<Rightarrow> rule" where [simp]:
  "n_Idle i \<equiv>
    let g = (eqn (IVar (Para ( ''n'') i)) (Const E)) in
    let s = (parallelList [(assign ((Para ( ''n'') i), (Const I))), (assign ((Ident ''x''), (Const true)))]) in
      guard g s"


definition rules :: "nat \<Rightarrow> rule set" where [simp]:
  "rules N \<equiv> {r.
    (\<exists>i. i \<le> N \<and> r = n_Try i) \<or>
    (\<exists>i. i \<le> N \<and> r = n_Crit i) \<or>
    (\<exists>i. i \<le> N \<and> r = n_Exit i) \<or>
    (\<exists>i. i \<le> N \<and> r = n_Idle i) 
   }"

definition rules_i :: "nat \<Rightarrow> rule set" where
  "rules_i i = {n_Try i, n_Crit i, n_Exit i, n_Idle i}"

lemma rules_i_same:
  "rulesOverDownN N (rules_i) = rules N"
  unfolding rules_def rules_i_def rulesOverDownN_def
  by auto

lemma rule_i_symmetric:
  "symmetricParamRules N rules_i"
  unfolding symmetricParamRules_def rules_i_def
  by auto

theorem rulesSymmetric:
  "symProtRules N (rules N)"
  unfolding rules_i_same[symmetric]
  apply (rule symProtFromSymmetricParam)
  by (rule rule_i_symmetric)

lemma rule_i_symmetric':
  "symmetricParamRules' N rules_i"
  unfolding symmetricParamRules'_def rules_i_def
  
  using alphaEqRuleSet_def by auto

text \<open>No two processes can be in the exit state in the same time.
  i \<noteq> j \<longrightarrow> n[i] = E \<longrightarrow> n[j] \<noteq> E
\<close>
definition inv_7 :: "nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
  "inv_7 i j \<equiv>
    implyForm (andForm (neg (eqn (Const (index i)) (Const (index j)))) (eqn (IVar (Para ''n'' i)) (Const E))) 
      (neg (eqn (IVar (Para ''n'' j)) (Const E)))"

text \<open>There cannot be one state in exit and another in critical.
  i \<noteq> j \<longrightarrow> n[i] = E \<longrightarrow> n[j] \<noteq> C
\<close>
definition inv_5 :: "nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
  "inv_5 i j \<equiv>
    implyForm (andForm (neg (eqn (Const (index i)) (Const (index j))))  
      (eqn (IVar (Para ''n'' i)) (Const E))) (neg (eqn (IVar (Para ''n'' j)) (Const C)))"

definition inv_57 :: "nat \<Rightarrow> nat \<Rightarrow> formula" where
  "inv_57 i j = andForm (inv_5 i j) (inv_7 i j)"

lemma inv_57_symmetric2:
  "symmetricParamFormulas2 N inv_57"
  unfolding symmetricParamFormulas2_def inv_57_def by auto

subsection \<open>Strengthened rules\<close>

definition rules2 :: "nat \<Rightarrow> rule set" where
  "rules2 N = rulesOverDownN N (\<lambda>i. strengthenProt N rules_i inv_57 i)"

theorem rules2_symmetric:
  "symProtRules' N (rules2 N)"
  unfolding rules2_def
  apply (rule symProtFromSymmetricParam')
  apply (rule strengthenProtSymmetric)
   apply (rule rule_i_symmetric)
  by (rule inv_57_symmetric2)

(*definition I::"scalrValueType" where [simp]: "I\<equiv> enum ''control1'' ''I''"*)
definition S::"scalrValueType" where [simp]: "S\<equiv> enum ''control'' ''S''"
(*definition E::"scalrValueType" where [simp]: "E\<equiv> enum ''control1'' ''E''"*)
definition Empty::"scalrValueType" where [simp]: "Empty\<equiv> enum ''control'' ''Empty''"
definition ReqS::"scalrValueType" where [simp]: "ReqS\<equiv> enum ''control'' ''ReqS''"
definition ReqE::"scalrValueType" where [simp]: "ReqE\<equiv> enum ''control'' ''ReqE''"
definition Inv::"scalrValueType" where [simp]: "Inv\<equiv> enum ''control'' ''Inv''"
definition InvAck::"scalrValueType" where [simp]: "InvAck\<equiv> enum ''control'' ''InvAck''"
definition GntS::"scalrValueType" where [simp]: "GntS\<equiv> enum ''control'' ''GntS''"
definition GntE::"scalrValueType" where [simp]: "GntE\<equiv> enum ''control'' ''GntE''" 

definition n_SendReqS15::"nat \<Rightarrow> rule" where [simp]:
"n_SendReqS15  i\<equiv>
let g = (andForm (eqn (IVar (Para (''Chan1.Cmd'') i)) (Const Empty))
   (eqn (IVar (Para (''Cache.State'') i)) (Const I))) in
let s = (parallelList [(assign ( (Para (''Chan1.Cmd'') i), (Const ReqS)))]) in
guard g s"


definition n_SendGntE3::"nat\<Rightarrow> nat\<Rightarrow> rule" where [simp]:
"n_SendGntE3 N  i\<equiv>
let g = andList [ (eqn (IVar (Ident ''CurCmd'')) (Const ReqE)),
 (eqn (IVar (Ident ''CurPtr''))(Const (index i))),
 (eqn (IVar (Para (''Chan2.Cmd'') i)) (Const Empty)),
 (eqn (IVar (Ident ''ExGntd'')) (Const false)), 
  andList (map  (\<lambda>j. (eqn (IVar (Para (''ShrSet'') j)) (Const false))) (down N)) 
] in
let s = (parallelList [assign  ((Para (''Chan2.Cmd'') i), (Const GntE)), 
assign ( (Para (''Chan2.Data'') i),(IVar (Ident ''MemData''))),
assign ( (Para (''ShrSet'') i), (Const true)),
assign ((Ident ''ExGntd''), (Const true)),
assign ((Ident ''CurCmd''), (Const Empty))]) in
guard g s"

(*(forallForm (down N) (\<lambda>j. (eqn (IVar (Para (''ShrSet'') j)) (Const false))) )*)
definition rules_i1 :: "nat\<Rightarrow>nat \<Rightarrow> rule set" where
  "rules_i1 N i = {n_Try i, n_Crit i, n_Exit i, n_Idle i,n_SendReqS15  i,n_SendGntE3 N  i}"

(*lemma rules_i_same:
  "rulesOverDownN N (rules_i) = rules N"
  unfolding rules_def rules_i_def rulesOverDownN_def
  by auto
*)

(*lemma andListSym:
  assumes a1:"\<forall>f. f \<in>set fl \<longrightarrow> (\<exists>f'. f'\<in>set fl' \<longrightarrow>alphaEqForm (applySym2Form p f)  f') " and
  a2:"\<forall>f'. f' \<in>set fl' \<longrightarrow> (\<exists>f. f\<in>set fl \<longrightarrow>alphaEqForm (applySym2Form p f)  f')"
  and a3:"p permutes {x. x \<le> N}"
  shows "alphaEqForm (applySym2Form p (andList fl)) (andList fl') "
  sorry 
*)
(*
(forallForm (down N) (\<lambda>j. (eqn (IVar (Para (''ShrSet'') j)) (Const false))) ))
   
  (forallForm (down N) (\<lambda>j. (eqn (IVar (Para (''ShrSet'') j)) (Const false))) )*)

lemma for1:assumes  a2:"p permutes {x. x \<le> N}"
  shows
  "and2ListF 
  (andList (map  (\<lambda>j. (eqn (IVar (Para (''ShrSet'') j)) (Const false))) (down N))) =
  and2ListF (applySym2Form p  
  (andList (map  (\<lambda>j. (eqn (IVar (Para (''ShrSet'') j)) (Const false))) (down N))))"
  (is "?P (applySym2Form p  (andList ?fl)) (andList ?fl')") 
  apply(rule wellFormAndlistIsSym1)
   apply auto
  by(cut_tac a2,auto)
(*  by (metis alphaEqForm_def andListApplySym0 andListSym empty_iff list.set(1) permutes_def) 
proof(rule andListSym)
  show "\<forall>f. f \<in>set ?fl \<longrightarrow> (\<exists>f'. f'\<in>set ?fl' \<longrightarrow>alphaEqForm (applySym2Form p f)  f') "
    using alphaEqForm_def by blast
next
  show "\<forall>f'. f' \<in>set ?fl' \<longrightarrow> (\<exists>f. f\<in>set ?fl \<longrightarrow>alphaEqForm (applySym2Form p f)  f')"
    sorry
next
  show "p permutes {x. x \<le> N}"
    using assms by blast
  
qed*)

lemma r1:
  assumes  a2:"p permutes {x. x \<le> N}"
  shows a1:"alphaEqForm   (applySym2Form p (pre(n_SendGntE3 N  i))) (pre(n_SendGntE3 N  (p i)))"
proof -
  have a1:"and2ListF 
  (andList (map  (\<lambda>j. (eqn (IVar (Para (''ShrSet'') j)) (Const false))) (down N))) =
  and2ListF (applySym2Form p  
  (andList (map  (\<lambda>j. (eqn (IVar (Para (''ShrSet'') j)) (Const false))) (down N))))"
    using assms for1 by auto
  show "alphaEqForm (applySym2Form p (pre (n_SendGntE3 N i))) (pre (n_SendGntE3 N (p i))) " 
    apply(simp,auto)
    apply(cut_tac  a1)  
     apply force
    apply(cut_tac  a1)  
    apply force
   done
qed
 (* apply(simp,auto)
   apply(cut_tac for1 a2)  
    apply force
  
   apply(cut_tac for1 a2)  
  apply force
  apply (metis (no_types, lifting) Collect_cong alphaEqForm_def andListSym applySym2FormList assms empty_iff list.set(1) map_map onMapAndListF)
  apply (metis (no_types, lifting) Collect_cong alphaEqForm_def andListSym applySym2FormList assms empty_iff list.set(1) map_map onMapAndListF)
  done*)

  (*using andListSym apply force
  apply(simp del:andCons alphaEqForm_def)
  apply(rule andListSym)
   apply (metis (mono_tags, hide_lams) a1 a2 alphaEqForm_def andListForm2 andListForm3 andListSym empty_iff formEval.simps(3) insert_iff list.set(1) list.set(2)
 list.set_intros(1) stFormSymCorrespondence)
  apply(rule allI,auto)
  using andListSym for1 apply force
  
  using andListSym apply force
  done*)
  

lemma rule_i1_symmetric:
  "symmetricParamRules' N (rules_i1 N)"
  unfolding symmetricParamRules'_def rules_i1_def
  using r1 alphaEqRuleSet_def by auto
  


end
