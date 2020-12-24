theory german
  imports Symmetric
begin
section{*Main definitions*}
definition I::"scalrValueType" where [simp]: "I\<equiv> enum ''control'' ''I''"
definition S::"scalrValueType" where [simp]: "S\<equiv> enum ''control'' ''S''"
definition E::"scalrValueType" where [simp]: "E\<equiv> enum ''control'' ''E''"
definition Empty::"scalrValueType" where [simp]: "Empty\<equiv> enum ''control'' ''Empty''"
definition ReqS::"scalrValueType" where [simp]: "ReqS\<equiv> enum ''control'' ''ReqS''"
definition ReqE::"scalrValueType" where [simp]: "ReqE\<equiv> enum ''control'' ''ReqE''"
definition Inv::"scalrValueType" where [simp]: "Inv\<equiv> enum ''control'' ''Inv''"
definition InvAck::"scalrValueType" where [simp]: "InvAck\<equiv> enum ''control'' ''InvAck''"
definition GntS::"scalrValueType" where [simp]: "GntS\<equiv> enum ''control'' ''GntS''"
definition GntE::"scalrValueType" where [simp]: "GntE\<equiv> enum ''control'' ''GntE''"
definition true::"scalrValueType" where [simp]: "true\<equiv> boolV True"
definition false::"scalrValueType" where [simp]: "false\<equiv> boolV False"

definition n_RecvGntE1::"nat \<Rightarrow> rule" where [simp]:
"n_RecvGntE1  i\<equiv>
let g = (eqn (IVar (Para (''Chan2.Cmd'') i)) (Const GntE)) in

let s = (parallelList [(assign ( (Para (''Cache.State'') i), (Const E))),
 (assign ( (Para (''Cache.Data'') i), (IVar (Para (''Chan2.Data'') i)))),
 (assign ( (Para (''Chan2.Cmd'') i), (Const Empty)))]) in
guard g s"

definition n_RecvGntS2::"nat \<Rightarrow> rule" where [simp]:
"n_RecvGntS2  i\<equiv>
let g = (eqn (Ivar (Para (''Chan2.Cmd'') i) (Const GntS))) in
let s = (parallelList [(assign (Ivar (Para (''Cache.State'') i)
(Const S))), (assign (Ivar (Para (''Cache.Data'') i), (IVar (Para (''Chan2.Data'') i))))
 (assign (Ivar (Para (''Chan2.Cmd'') i), (Const Empty)))]) in
guard g s"

definition n_SendGntE3::"nat \<Rightarrow> rule" where [simp]:
"n_SendGntE3  i\<equiv>
let g = (andForm (eqn (IVar (Ident ''CurCmd'')) (Const ReqE)) (eqn (IVar (Ident ''CurPtr''))
 (Const i)) (eqn (Ivar (Para (''Chan2.Cmd'') i) (Const Empty)))
 (eqn (IVar (Ident ''ExGntd'')) (Const false)) 
(forallForm (down N) (\<lambda>j. (eqn (Ivar (Para (''ShrSet'') j) (Const false))) ))in
let s = (parallelList [(assign (Ivar (Para (''Chan2.Cmd'') i), (Const GntE))), 
(assign (Ivar (Para (''Chan2.Data'') i),
 (Const MemData))),
 (assign (Ivar (Para (''ShrSet'') i), (Const true))),
 (assign ((Ident ''ExGntd''), (Const true))),
 (assign ((Ident ''CurCmd''), (Const Empty)))]) in
guard g s"

definition n_SendGntS4::"nat \<Rightarrow> rule" where [simp]:
"n_SendGntS4  i\<equiv>
let g = (andForm (eqn (IVar (Ident ''CurCmd'')) (Const ReqS)) (eqn (IVar (Ident ''CurPtr'')) (Const i)) (eqn (Ivar (Para (''Chan2.Cmd'') i) (Const Empty))) (eqn (IVar (Ident ''ExGntd'')) (Const false)) in
let s = (parallelList [(assign (Ivar (Para (''Chan2.Cmd'') i), (Const GntS))), (assign (Ivar (Para (''Chan2.Data'') i), (Const MemData))), (assign (Ivar (Para (''ShrSet'') i), (Const true))), (assign ((Ident ''CurCmd''), (Const Empty)))]) in
guard g s"

definition n_RecvInvAck5::"nat \<Rightarrow> rule" where [simp]:
"n_RecvInvAck5  i\<equiv>
let g = (andForm (eqn (Ivar (Para (''Chan3.Cmd'') i) (Const InvAck))) (neg (eqn (IVar (Ident ''CurCmd'')) (Const Empty))) (eqn (IVar (Ident ''ExGntd'')) (Const true)) in
let s = (parallelList [(assign (Ivar (Para (''Chan3.Cmd'') i), (Const Empty))), (assign (Ivar (Para (''ShrSet'') i), (Const false))), (assign ((Ident ''ExGntd''), (Const false))), (assign ((Ident ''MemData''), (IVar (Para (''Chan3.Data'') i))))]) in
guard g s"

definition n_RecvInvAck6::"nat \<Rightarrow> rule" where [simp]:
"n_RecvInvAck6  i\<equiv>
let g = (andForm (eqn (Ivar (Para (''Chan3.Cmd'') i) (Const InvAck))) (neg (eqn (IVar (Ident ''CurCmd'')) (Const Empty))) (neg (eqn (IVar (Ident ''ExGntd'')) (Const true))) in
let s = (parallelList [(assign (Ivar (Para (''Chan3.Cmd'') i), (Const Empty))), (assign (Ivar (Para (''ShrSet'') i), (Const false)))]) in
guard g s"

definition n_SendInvAck7::"nat \<Rightarrow> rule" where [simp]:
"n_SendInvAck7  i\<equiv>
let g = (andForm (eqn (Ivar (Para (''Chan2.Cmd'') i) (Const Inv))) (eqn (Ivar (Para (''Chan3.Cmd'') i) (Const Empty))) (eqn (Ivar (Para (''Cache.State'') i) (Const E))) in
let s = (parallelList [(assign (Ivar (Para (''Chan2.Cmd'') i), (Const Empty))), (assign (Ivar (Para (''Chan3.Cmd'') i), (Const InvAck))), (assign (Ivar (Para (''Chan3.Data'') i), (IVar (Para (''Cache.Data'') i)))), (assign (Ivar (Para (''Cache.State'') i), (Const I)))]) in
guard g s"

definition n_SendInvAck8::"nat \<Rightarrow> rule" where [simp]:
"n_SendInvAck8  i\<equiv>
let g = (andForm (eqn (Ivar (Para (''Chan2.Cmd'') i) (Const Inv))) (eqn (Ivar (Para (''Chan3.Cmd'') i) (Const Empty))) (neg (eqn (Ivar (Para (''Cache.State'') i) (Const E)))) in
let s = (parallelList [(assign (Ivar (Para (''Chan2.Cmd'') i), (Const Empty))), (assign (Ivar (Para (''Chan3.Cmd'') i), (Const InvAck))), (assign (Ivar (Para (''Cache.State'') i), (Const I)))]) in
guard g s"

definition n_SendInv9::"nat \<Rightarrow> rule" where [simp]:
"n_SendInv9  i\<equiv>
let g = (andForm (eqn (Ivar (Para (''Chan2.Cmd'') i) (Const Empty))) (eqn (Ivar (Para (''InvSet'') i) (Const true))) (eqn (IVar (Ident ''CurCmd'')) (Const ReqE)) in
let s = (parallelList [(assign (Ivar (Para (''Chan2.Cmd'') i), (Const Inv))), (assign (Ivar (Para (''InvSet'') i), (Const false)))]) in
guard g s"

definition n_SendInv10::"nat \<Rightarrow> rule" where [simp]:
"n_SendInv10  i\<equiv>
let g = (andForm (eqn (Ivar (Para (''Chan2.Cmd'') i) (Const Empty))) (eqn (Ivar (Para (''InvSet'') i) (Const true))) (eqn (IVar (Ident ''CurCmd'')) (Const ReqS)) (eqn (IVar (Ident ''ExGntd'')) (Const true)) in
let s = (parallelList [(assign (Ivar (Para (''Chan2.Cmd'') i), (Const Inv))), (assign (Ivar (Para (''InvSet'') i), (Const false)))]) in
guard g s"

definition n_RecvReqE11::"nat \<Rightarrow> rule" where [simp]:
"n_RecvReqE11  i\<equiv>
let g = (andForm (eqn (IVar (Ident ''CurCmd'')) (Const Empty)) (eqn (Ivar (Para (''Chan1.Cmd'') i) (Const ReqE))) in
let s = (parallelList [(assign ((Ident ''CurCmd''), (Const ReqE))), (assign ((Ident ''CurPtr''), (Const i))), (assign (Ivar (Para (''Chan1.Cmd'') i), (Const Empty))), (forallSent (down N) (\<lambda>j. (eqn (Ivar (Para (''InvSet'') j) (IVar (Para (''ShrSet'') j)))) ))]) in
guard g s"

definition n_RecvReqS12::"nat \<Rightarrow> rule" where [simp]:
"n_RecvReqS12  i\<equiv>
let g = (andForm (eqn (IVar (Ident ''CurCmd'')) (Const Empty)) (eqn (Ivar (Para (''Chan1.Cmd'') i) (Const ReqS))) in
let s = (parallelList [(assign ((Ident ''CurCmd''), (Const ReqS))), (assign ((Ident ''CurPtr''), (Const i))), (assign (Ivar (Para (''Chan1.Cmd'') i), (Const Empty))), (forallSent (down N) (\<lambda>j. (eqn (Ivar (Para (''InvSet'') j) (IVar (Para (''ShrSet'') j)))) ))]) in
guard g s"

definition n_SendReqE13::"nat \<Rightarrow> rule" where [simp]:
"n_SendReqE13  i\<equiv>
let g = (andForm (eqn (Ivar (Para (''Chan1.Cmd'') i) (Const Empty))) (eqn (Ivar (Para (''Cache.State'') i) (Const I))) in
let s = (parallelList [(assign (Ivar (Para (''Chan1.Cmd'') i), (Const ReqE)))]) in
guard g s"

definition n_SendReqE14::"nat \<Rightarrow> rule" where [simp]:
"n_SendReqE14  i\<equiv>
let g = (andForm (eqn (Ivar (Para (''Chan1.Cmd'') i) (Const Empty))) (eqn (Ivar (Para (''Cache.State'') i) (Const S))) in
let s = (parallelList [(assign (Ivar (Para (''Chan1.Cmd'') i), (Const ReqE)))]) in
guard g s"

definition n_SendReqS15::"nat \<Rightarrow> rule" where [simp]:
"n_SendReqS15  i\<equiv>
let g = (andForm (eqn (Ivar (Para (''Chan1.Cmd'') i) (Const Empty))) (eqn (Ivar (Para (''Cache.State'') i) (Const I))) in
let s = (parallelList [(assign (Ivar (Para (''Chan1.Cmd'') i), (Const ReqS)))]) in
guard g s"

definition n_Store16::"nat \<Rightarrow> rule" where [simp]:
"n_Store16  i\<equiv>
let g = (eqn (Ivar (Para (''Cache.State'') i) (Const E))) in
let s = (parallelList [(assign (Ivar (Para (''Cache.Data'') i), (Const d))), (assign ((Ident ''AuxData''), (Const d)))]) in
guard g s"

definition rules::"nat \<Rightarrow> rule set" where [simp]:
"rules N \<equiv> {r.
(\<exists> i. i\<le>N\<and>r=n_RecvGntE1  i) \<or>
(\<exists> i. i\<le>N\<and>r=n_RecvGntS2  i) \<or>
(\<exists> i. i\<le>N\<and>r=n_SendGntE3  i) \<or>
(\<exists> i. i\<le>N\<and>r=n_SendGntS4  i) \<or>
(\<exists> i. i\<le>N\<and>r=n_RecvInvAck5  i) \<or>
(\<exists> i. i\<le>N\<and>r=n_RecvInvAck6  i) \<or>
(\<exists> i. i\<le>N\<and>r=n_SendInvAck7  i) \<or>
(\<exists> i. i\<le>N\<and>r=n_SendInvAck8  i) \<or>
(\<exists> i. i\<le>N\<and>r=n_SendInv9  i) \<or>
(\<exists> i. i\<le>N\<and>r=n_SendInv10  i) \<or>
(\<exists> i. i\<le>N\<and>r=n_RecvReqE11  i) \<or>
(\<exists> i. i\<le>N\<and>r=n_RecvReqS12  i) \<or>
(\<exists> i. i\<le>N\<and>r=n_SendReqE13  i) \<or>
(\<exists> i. i\<le>N\<and>r=n_SendReqE14  i) \<or>
(\<exists> i. i\<le>N\<and>r=n_SendReqS15  i) \<or>
(\<exists> i. i\<le>N\<and>r=n_Store16  i)
}"

definition initSpec0::"nat \<Rightarrow> formula" where [simp]:
"initSpec0 N (forallSent (down N) (\<lambda>i. (eqn (Ivar (Para (''Chan1.Cmd'') i) (Const Empty))) ))"

definition initSpec1::"nat \<Rightarrow> formula" where [simp]:
"initSpec1 N (forallSent (down N) (\<lambda>i. (eqn (Ivar (Para (''Chan2.Cmd'') i) (Const Empty))) ))"

definition initSpec2::"nat \<Rightarrow> formula" where [simp]:
"initSpec2 N (forallSent (down N) (\<lambda>i. (eqn (Ivar (Para (''Chan3.Cmd'') i) (Const Empty))) ))"

definition initSpec3::"nat \<Rightarrow> formula" where [simp]:
"initSpec3 N (forallSent (down N) (\<lambda>i. (eqn (Ivar (Para (''Cache.State'') i) (Const I))) ))"

definition initSpec4::"nat \<Rightarrow> formula" where [simp]:
"initSpec4 N (forallSent (down N) (\<lambda>i. (eqn (Ivar (Para (''InvSet'') i) (Const false))) ))"

definition initSpec5::"nat \<Rightarrow> formula" where [simp]:
"initSpec5 N (forallSent (down N) (\<lambda>i. (eqn (Ivar (Para (''ShrSet'') i) (Const false))) ))"

definition initSpec6::"nat \<Rightarrow> formula" where [simp]:
"initSpec6 N \<equiv> (eqn (IVar (Ident ''ExGntd'')) (Const false)) "

definition initSpec7::"nat \<Rightarrow> formula" where [simp]:
"initSpec7 N \<equiv> (eqn (IVar (Ident ''CurCmd'')) (Const Empty)) "

definition initSpec8::"nat \<Rightarrow> formula" where [simp]:
"initSpec8 N \<equiv> (eqn (IVar (Ident ''MemData'')) (Const d)) "

definition initSpec9::"nat \<Rightarrow> formula" where [simp]:
"initSpec9 N \<equiv> (eqn (IVar (Ident ''AuxData'')) (Const d)) "

definition allInitSpecs::"nat \<Rightarrow> formula list" where [simp]:
"allInitSpecs N \<equiv> [
(initSpec0 N),
(initSpec1 N),
(initSpec2 N),
(initSpec3 N),
(initSpec4 N),
(initSpec5 N),
(initSpec6 N),
(initSpec7 N),
(initSpec8 N),
(initSpec9 N)
]"

end