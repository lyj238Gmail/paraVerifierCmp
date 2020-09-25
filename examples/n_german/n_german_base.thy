(*  Title:      HOL/Auth/n_german_base.thy
    Author:     Yongjian Li and Kaiqiang Duan, State Key Lab of Computer Science, Institute of Software, Chinese Academy of Sciences
    Copyright    2016 State Key Lab of Computer Science, Institute of Software, Chinese Academy of Sciences
*)

(*header{*The n_german Protocol Case Study*} *)

theory n_german_base imports paraTheory
begin

section{*Main definitions*}

subsection{* Definitions of Constants*}
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



subsection{*  Definitions of Parameterized Rules *}

definition  NC::"nat " where [simp]: "NC==1"

 
definition VF::"varType set" where [simp]: 
"VF \<equiv>{(Ident ''AuxData''),(Field (Para (Ident ''Cache'') 0) ''Data''),(Field (Para (Ident ''Cache'') 0) ''State''),(Field (Para (Ident ''Cache'') 1) ''Data''),(Field (Para (Ident ''Cache'') 1) ''State''),(Field (Para (Ident ''Chan1'') 0) ''Cmd''),(Field (Para (Ident ''Chan1'') 1) ''Cmd''),(Field (Para (Ident ''Chan2'') 0) ''Cmd''),(Field (Para (Ident ''Chan2'') 0) ''Data''),(Field (Para (Ident ''Chan2'') 1) ''Cmd''),(Field (Para (Ident ''Chan2'') 1) ''Data''),(Field (Para (Ident ''Chan3'') 0) ''Cmd''),(Field (Para (Ident ''Chan3'') 0) ''Data''),(Field (Para (Ident ''Chan3'') 1) ''Cmd''),(Field (Para (Ident ''Chan3'') 1) ''Data''),(Ident ''CurCmd''),(Ident ''ExGntd''),(Para (Ident ''InvSet'') 0),(Para (Ident ''InvSet'') 1),(Ident ''MemData''),(Para (Ident ''ShrSet'') 0),(Para (Ident ''ShrSet'') 1)}"


definition VF'::"varType set" where [simp]: 
"VF' \<equiv>{(Ident ''CurPtr'')}"

definition n_RecvGntE1::"nat \<Rightarrow> rule" where [simp]:
"n_RecvGntE1  i\<equiv>
let g = (eqn (IVar (Field (Para (Ident ''Chan2'') i) ''Cmd'')) (Const GntE)) in
let s = (parallelList [(assign ((Field (Para (Ident ''Cache'') i) ''State''), (Const E))), (assign ((Field (Para (Ident ''Cache'') i) ''Data''), (IVar (Field (Para (Ident ''Chan2'') i) ''Data'')))), (assign ((Field (Para (Ident ''Chan2'') i) ''Cmd''), (Const Empty)))]) in
guard g s"

definition n_RecvGntS2::"nat \<Rightarrow> rule" where [simp]:
"n_RecvGntS2  i\<equiv>
let g = (eqn (IVar (Field (Para (Ident ''Chan2'') i) ''Cmd'')) (Const GntS)) in
let s = (parallelList [(assign ((Field (Para (Ident ''Cache'') i) ''State''), (Const S))), (assign ((Field (Para (Ident ''Cache'') i) ''Data''), (IVar (Field (Para (Ident ''Chan2'') i) ''Data'')))), (assign ((Field (Para (Ident ''Chan2'') i) ''Cmd''), (Const Empty)))]) in
guard g s"

definition n_SendGntE3::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_SendGntE3 N i\<equiv>
let g = (andForm (andForm (andForm (andForm (eqn (IVar (Ident ''CurCmd'')) (Const ReqE)) (eqn (IVar (Ident ''CurPtr'')) (Const (index i)))) (eqn (IVar (Field (Para (Ident ''Chan2'') i) ''Cmd'')) (Const Empty))) (eqn (IVar (Ident ''ExGntd'')) (Const false))) (forallForm (down N) (\<lambda>j. (eqn (IVar (Para (Ident ''ShrSet'') j)) (Const false))))) in
let s = (parallelList [(assign ((Field (Para (Ident ''Chan2'') i) ''Cmd''), (Const GntE))), (assign ((Field (Para (Ident ''Chan2'') i) ''Data''), (IVar (Ident ''MemData'')))), (assign ((Para (Ident ''ShrSet'') i), (Const true))), (assign ((Ident ''ExGntd''), (Const true))), (assign ((Ident ''CurCmd''), (Const Empty)))]) in
guard g s"

definition n_SendGntS4::"nat \<Rightarrow> rule" where [simp]:
"n_SendGntS4  i\<equiv>
let g = (andForm (andForm (andForm (eqn (IVar (Ident ''CurCmd'')) (Const ReqS)) (eqn (IVar (Ident ''CurPtr'')) (Const (index i)))) (eqn (IVar (Field (Para (Ident ''Chan2'') i) ''Cmd'')) (Const Empty))) (eqn (IVar (Ident ''ExGntd'')) (Const false))) in
let s = (parallelList [(assign ((Field (Para (Ident ''Chan2'') i) ''Cmd''), (Const GntS))), (assign ((Field (Para (Ident ''Chan2'') i) ''Data''), (IVar (Ident ''MemData'')))), (assign ((Para (Ident ''ShrSet'') i), (Const true))), (assign ((Ident ''CurCmd''), (Const Empty)))]) in
guard g s"

definition n_RecvInvAck5::"nat \<Rightarrow> rule" where [simp]:
"n_RecvInvAck5  i\<equiv>
let g = (andForm (eqn (IVar (Field (Para (Ident ''Chan3'') i) ''Cmd'')) (Const InvAck)) (eqn (IVar (Ident ''ExGntd'')) (Const true))) in
let s = (parallelList [(assign ((Field (Para (Ident ''Chan3'') i) ''Cmd''), (Const Empty))), (assign ((Para (Ident ''ShrSet'') i), (Const false))), (assign ((Ident ''ExGntd''), (Const false))), (assign ((Ident ''MemData''), (IVar (Field (Para (Ident ''Chan3'') i) ''Data''))))]) in
guard g s"

definition n_RecvInvAck6::"nat \<Rightarrow> rule" where [simp]:
"n_RecvInvAck6  i\<equiv>
let g = (andForm (eqn (IVar (Field (Para (Ident ''Chan3'') i) ''Cmd'')) (Const InvAck)) (neg (eqn (IVar (Ident ''ExGntd'')) (Const true)))) in
let s = (parallelList [(assign ((Field (Para (Ident ''Chan3'') i) ''Cmd''), (Const Empty))), (assign ((Para (Ident ''ShrSet'') i), (Const false)))]) in
guard g s"

definition n_SendInvAck7::"nat \<Rightarrow> rule" where [simp]:
"n_SendInvAck7  i\<equiv>
let g = (andForm (andForm (eqn (IVar (Field (Para (Ident ''Chan2'') i) ''Cmd'')) (Const Inv)) (eqn (IVar (Field (Para (Ident ''Chan3'') i) ''Cmd'')) (Const Empty))) (eqn (IVar (Field (Para (Ident ''Cache'') i) ''State'')) (Const E))) in
let s = (parallelList [(assign ((Field (Para (Ident ''Chan2'') i) ''Cmd''), (Const Empty))), (assign ((Field (Para (Ident ''Chan3'') i) ''Cmd''), (Const InvAck))), (assign ((Field (Para (Ident ''Chan3'') i) ''Data''), (IVar (Field (Para (Ident ''Cache'') i) ''Data'')))), (assign ((Field (Para (Ident ''Cache'') i) ''State''), (Const I)))]) in
guard g s"

definition n_SendInvAck8::"nat \<Rightarrow> rule" where [simp]:
"n_SendInvAck8  i\<equiv>
let g = (andForm (andForm (eqn (IVar (Field (Para (Ident ''Chan2'') i) ''Cmd'')) (Const Inv)) (eqn (IVar (Field (Para (Ident ''Chan3'') i) ''Cmd'')) (Const Empty))) (neg (eqn (IVar (Field (Para (Ident ''Cache'') i) ''State'')) (Const E)))) in
let s = (parallelList [(assign ((Field (Para (Ident ''Chan2'') i) ''Cmd''), (Const Empty))), (assign ((Field (Para (Ident ''Chan3'') i) ''Cmd''), (Const InvAck))), (assign ((Field (Para (Ident ''Cache'') i) ''State''), (Const I)))]) in
guard g s"

definition n_SendInv9::"nat \<Rightarrow> rule" where [simp]:
"n_SendInv9  i\<equiv>
let g = (andForm (andForm (eqn (IVar (Field (Para (Ident ''Chan2'') i) ''Cmd'')) (Const Empty)) (eqn (IVar (Para (Ident ''InvSet'') i)) (Const true))) (eqn (IVar (Ident ''CurCmd'')) (Const ReqE))) in
let s = (parallelList [(assign ((Field (Para (Ident ''Chan2'') i) ''Cmd''), (Const Inv))), (assign ((Para (Ident ''InvSet'') i), (Const false)))]) in
guard g s"

definition n_SendInv10::"nat \<Rightarrow> rule" where [simp]:
"n_SendInv10  i\<equiv>
let g = (andForm (andForm (andForm (eqn (IVar (Field (Para (Ident ''Chan2'') i) ''Cmd'')) (Const Empty)) (eqn (IVar (Para (Ident ''InvSet'') i)) (Const true))) (eqn (IVar (Ident ''CurCmd'')) (Const ReqS))) (eqn (IVar (Ident ''ExGntd'')) (Const true))) in
let s = (parallelList [(assign ((Field (Para (Ident ''Chan2'') i) ''Cmd''), (Const Inv))), (assign ((Para (Ident ''InvSet'') i), (Const false)))]) in
guard g s"

definition n_RecvReqE11::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_RecvReqE11 N i\<equiv>
let g = (andForm (eqn (IVar (Ident ''CurCmd'')) (Const Empty)) (eqn (IVar (Field (Para (Ident ''Chan1'') i) ''Cmd'')) (Const ReqE))) in
let s = (parallelList [(assign ((Ident ''CurCmd''), (Const ReqE))), (assign ((Ident ''CurPtr''), (Const (index i)))), (assign ((Field (Para (Ident ''Chan1'') i) ''Cmd''), (Const Empty))), (forallSent (down N) (\<lambda>j. (assign ((Para (Ident ''InvSet'') j), (IVar (Para (Ident ''ShrSet'') j))))))]) in
guard g s"

definition n_RecvReqS12::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_RecvReqS12 N i\<equiv>
let g = (andForm (eqn (IVar (Ident ''CurCmd'')) (Const Empty)) (eqn (IVar (Field (Para (Ident ''Chan1'') i) ''Cmd'')) (Const ReqS))) in
let s = (parallelList [(assign ((Ident ''CurCmd''), (Const ReqS))), (assign ((Ident ''CurPtr''), (Const (index i)))), (assign ((Field (Para (Ident ''Chan1'') i) ''Cmd''), (Const Empty))), (forallSent (down N) (\<lambda>j. (assign ((Para (Ident ''InvSet'') j), (IVar (Para (Ident ''ShrSet'') j))))))]) in
guard g s"

definition n_SendReqE13::"nat \<Rightarrow> rule" where [simp]:
"n_SendReqE13  i\<equiv>
let g = (andForm (eqn (IVar (Field (Para (Ident ''Chan1'') i) ''Cmd'')) (Const Empty)) (eqn (IVar (Field (Para (Ident ''Cache'') i) ''State'')) (Const I))) in
let s = (parallelList [(assign ((Field (Para (Ident ''Chan1'') i) ''Cmd''), (Const ReqE)))]) in
guard g s"

definition n_SendReqE14::"nat \<Rightarrow> rule" where [simp]:
"n_SendReqE14  i\<equiv>
let g = (andForm (eqn (IVar (Field (Para (Ident ''Chan1'') i) ''Cmd'')) (Const Empty)) (eqn (IVar (Field (Para (Ident ''Cache'') i) ''State'')) (Const S))) in
let s = (parallelList [(assign ((Field (Para (Ident ''Chan1'') i) ''Cmd''), (Const ReqE)))]) in
guard g s"

definition n_SendReqS15::"nat \<Rightarrow> rule" where [simp]:
"n_SendReqS15  i\<equiv>
let g = (andForm (eqn (IVar (Field (Para (Ident ''Chan1'') i) ''Cmd'')) (Const Empty)) (eqn (IVar (Field (Para (Ident ''Cache'') i) ''State'')) (Const I))) in
let s = (parallelList [(assign ((Field (Para (Ident ''Chan1'') i) ''Cmd''), (Const ReqS)))]) in
guard g s"

definition n_Store::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_Store  i d\<equiv>
let g = (eqn (IVar (Field (Para (Ident ''Cache'') i) ''State'')) (Const E)) in
let s = (parallelList [(assign ((Field (Para (Ident ''Cache'') i) ''Data''), (Const (index d)))), (assign ((Ident ''AuxData''), (Const (index d))))]) in
guard g s"

definition n_SendGntE3_i_3::"rule" where [simp]:
"n_SendGntE3_i_3  \<equiv>
let g = (andForm (andForm (andForm (andForm (andForm (andForm (eqn (IVar (Ident ''CurCmd'')) (Const ReqE)) (eqn (IVar (Ident ''CurPtr'')) (Const (index 3)))) (eqn (IVar (Ident ''ExGntd'')) (Const false))) (forallForm (down NC) (\<lambda>j. (eqn (IVar (Para (Ident ''ShrSet'') j)) (Const false))))) (forallForm (down NC) (\<lambda>p__Inv2. (neg (eqn (IVar (Field (Para (Ident ''Chan2'') p__Inv2) ''Cmd'')) (Const GntE)))))) (forallForm (down NC) (\<lambda>p__Inv2. (neg (eqn (IVar (Field (Para (Ident ''Cache'') p__Inv2) ''State'')) (Const E)))))) (neg (neg (eqn (IVar (Ident ''MemData'')) (IVar (Ident ''AuxData'')))))) in
let s = (parallelList [(assign ((Ident ''ExGntd''), (Const true))), (assign ((Ident ''CurCmd''), (Const Empty)))]) in
guard g s"

definition n_SendGntS4_i_3::"rule" where [simp]:
"n_SendGntS4_i_3  \<equiv>
let g = (andForm (andForm (andForm (andForm (andForm (andForm (andForm (eqn (IVar (Ident ''CurCmd'')) (Const ReqS)) (eqn (IVar (Ident ''CurPtr'')) (Const (index 3)))) (eqn (IVar (Ident ''ExGntd'')) (Const false))) (forallForm (down NC) (\<lambda>p__Inv2. (neg (eqn (IVar (Field (Para (Ident ''Chan2'') p__Inv2) ''Cmd'')) (Const GntE)))))) (forallForm (down NC) (\<lambda>p__Inv2. (neg (eqn (IVar (Field (Para (Ident ''Cache'') p__Inv2) ''State'')) (Const E)))))) (neg (neg (eqn (IVar (Ident ''MemData'')) (IVar (Ident ''AuxData'')))))) (forallForm (down NC) (\<lambda>p__Inv2. (neg (eqn (IVar (Field (Para (Ident ''Chan3'') p__Inv2) ''Cmd'')) (Const InvAck)))))) (forallForm (down NC) (\<lambda>p__Inv2. (neg (eqn (IVar (Field (Para (Ident ''Chan2'') p__Inv2) ''Cmd'')) (Const Inv)))))) in
let s = (parallelList [(assign ((Ident ''CurCmd''), (Const Empty)))]) in
guard g s"

definition n_RecvInvAck5_i_3::"rule" where [simp]:
"n_RecvInvAck5_i_3  \<equiv>
let g = (andForm (andForm (andForm (andForm (andForm (andForm (andForm (andForm (eqn (IVar (Ident ''ExGntd'')) (Const true)) (forallForm (down NC) (\<lambda>p__Inv2. (neg (eqn (IVar (Field (Para (Ident ''Chan2'') p__Inv2) ''Cmd'')) (Const GntS)))))) (neg (eqn (IVar (Ident ''CurCmd'')) (Const Empty)))) (forallForm (down NC) (\<lambda>p__Inv1. (neg (eqn (IVar (Field (Para (Ident ''Chan2'') p__Inv1) ''Cmd'')) (Const GntE)))))) (forallForm (down NC) (\<lambda>p__Inv1. (neg (eqn (IVar (Field (Para (Ident ''Cache'') p__Inv1) ''State'')) (Const E)))))) (forallForm (down NC) (\<lambda>p__Inv2. (neg (eqn (IVar (Field (Para (Ident ''Chan2'') p__Inv2) ''Cmd'')) (Const GntE)))))) (forallForm (down NC) (\<lambda>p__Inv2. (neg (eqn (IVar (Field (Para (Ident ''Cache'') p__Inv2) ''State'')) (Const E)))))) (forallForm (down NC) (\<lambda>p__Inv2. (neg (eqn (IVar (Para (Ident ''ShrSet'') p__Inv2)) (Const true)))))) (forallForm (down NC) (\<lambda>p__Inv1. (neg (eqn (IVar (Para (Ident ''ShrSet'') p__Inv1)) (Const true)))))) in
let s = (parallelList [(assign ((Ident ''ExGntd''), (Const false))), (assign ((Ident ''MemData''), (IVar (Ident ''AuxData''))))]) in
guard g s"

definition n_RecvReqE11_i_3::"rule" where [simp]:
"n_RecvReqE11_i_3  \<equiv>
let g = (andForm (andForm (eqn (IVar (Ident ''CurCmd'')) (Const Empty)) (forallForm (down NC) (\<lambda>p__Inv2. (neg (eqn (IVar (Field (Para (Ident ''Chan3'') p__Inv2) ''Cmd'')) (Const InvAck)))))) (forallForm (down NC) (\<lambda>p__Inv2. (neg (eqn (IVar (Field (Para (Ident ''Chan2'') p__Inv2) ''Cmd'')) (Const Inv)))))) in
let s = (parallelList [(assign ((Ident ''CurCmd''), (Const ReqE))), (assign ((Ident ''CurPtr''), (Const (index 3)))), (forallSent (down NC) (\<lambda>j. (assign ((Para (Ident ''InvSet'') j), (IVar (Para (Ident ''ShrSet'') j))))))]) in
guard g s"

definition n_RecvReqS12_i_3::"rule" where [simp]:
"n_RecvReqS12_i_3  \<equiv>
let g = (andForm (andForm (eqn (IVar (Ident ''CurCmd'')) (Const Empty)) (forallForm (down NC) (\<lambda>p__Inv2. (neg (eqn (IVar (Field (Para (Ident ''Chan3'') p__Inv2) ''Cmd'')) (Const InvAck)))))) (forallForm (down NC) (\<lambda>p__Inv2. (neg (eqn (IVar (Field (Para (Ident ''Chan2'') p__Inv2) ''Cmd'')) (Const Inv)))))) in
let s = (parallelList [(assign ((Ident ''CurCmd''), (Const ReqS))), (assign ((Ident ''CurPtr''), (Const (index 3)))), (forallSent (down NC) (\<lambda>j. (assign ((Para (Ident ''InvSet'') j), (IVar (Para (Ident ''ShrSet'') j))))))]) in
guard g s"

definition n_Store_i_3::"nat \<Rightarrow> rule" where [simp]:
"n_Store_i_3  d\<equiv>
let g = (andForm (andForm (andForm (andForm (andForm (andForm (andForm (andForm (andForm (andForm (andForm (andForm (andForm (andForm (forallForm (down NC) (\<lambda>p__Inv1. (neg (eqn (IVar (Para (Ident ''ShrSet'') p__Inv1)) (Const true))))) (forallForm (down NC) (\<lambda>p__Inv2. (neg (eqn (IVar (Para (Ident ''InvSet'') p__Inv2)) (Const true)))))) (neg (eqn (IVar (Ident ''ExGntd'')) (Const false)))) (forallForm (down NC) (\<lambda>p__Inv2. (neg (eqn (IVar (Field (Para (Ident ''Chan3'') p__Inv2) ''Cmd'')) (Const InvAck)))))) (forallForm (down NC) (\<lambda>p__Inv1. (neg (eqn (IVar (Field (Para (Ident ''Chan2'') p__Inv1) ''Cmd'')) (Const Inv)))))) (forallForm (down NC) (\<lambda>p__Inv2. (neg (eqn (IVar (Field (Para (Ident ''Chan2'') p__Inv2) ''Cmd'')) (Const GntS)))))) (forallForm (down NC) (\<lambda>p__Inv2. (neg (eqn (IVar (Field (Para (Ident ''Chan2'') p__Inv2) ''Cmd'')) (Const GntE)))))) (forallForm (down NC) (\<lambda>p__Inv1. (neg (neg (eqn (IVar (Field (Para (Ident ''Cache'') p__Inv1) ''State'')) (Const I))))))) (forallForm (down NC) (\<lambda>p__Inv1. (neg (eqn (IVar (Field (Para (Ident ''Chan2'') p__Inv1) ''Cmd'')) (Const GntE)))))) (forallForm (down NC) (\<lambda>p__Inv2. (neg (eqn (IVar (Field (Para (Ident ''Cache'') p__Inv2) ''State'')) (Const E)))))) (forallForm (down NC) (\<lambda>p__Inv2. (neg (eqn (IVar (Field (Para (Ident ''Chan2'') p__Inv2) ''Cmd'')) (Const GntE)))))) (forallForm (down NC) (\<lambda>p__Inv2. (neg (eqn (IVar (Field (Para (Ident ''Cache'') p__Inv2) ''State'')) (Const E)))))) (forallForm (down NC) (\<lambda>p__Inv2. (neg (eqn (IVar (Para (Ident ''ShrSet'') p__Inv2)) (Const true)))))) (forallForm (down NC) (\<lambda>p__Inv2. (neg (eqn (IVar (Field (Para (Ident ''Chan2'') p__Inv2) ''Cmd'')) (Const GntS)))))) (forallForm (down NC) (\<lambda>p__Inv1. (neg (eqn (IVar (Para (Ident ''ShrSet'') p__Inv1)) (Const true)))))) in
let s = (parallelList [(assign ((Ident ''AuxData''), (Const (index d))))]) in
guard g s"

subsection{*The set of All actual Rules w.r.t. a Protocol Instance with Size $N$*}
definition rules::"nat \<Rightarrow> rule set" where [simp]:
"rules N \<equiv> {r.
(\<exists> i. i\<le>N\<and>r=n_RecvGntE1  i) \<or>
(\<exists> i. i\<le>N\<and>r=n_RecvGntS2  i) \<or>
(\<exists> i. i\<le>N\<and>r=n_SendGntE3 N i) \<or>
(\<exists> i. i\<le>N\<and>r=n_SendGntS4  i) \<or>
(\<exists> i. i\<le>N\<and>r=n_RecvInvAck5  i) \<or>
(\<exists> i. i\<le>N\<and>r=n_RecvInvAck6  i) \<or>
(\<exists> i. i\<le>N\<and>r=n_SendInvAck7  i) \<or>
(\<exists> i. i\<le>N\<and>r=n_SendInvAck8  i) \<or>
(\<exists> i. i\<le>N\<and>r=n_SendInv9  i) \<or>
(\<exists> i. i\<le>N\<and>r=n_SendInv10  i) \<or>
(\<exists> i. i\<le>N\<and>r=n_RecvReqE11 N i) \<or>
(\<exists> i. i\<le>N\<and>r=n_RecvReqS12 N i) \<or>
(\<exists> i. i\<le>N\<and>r=n_SendReqE13  i) \<or>
(\<exists> i. i\<le>N\<and>r=n_SendReqE14  i) \<or>
(\<exists> i. i\<le>N\<and>r=n_SendReqS15  i) \<or>
(\<exists> i d. i\<le>N\<and>d\<le>N\<and>r=n_Store  i d) \<or>
(r=n_SendGntE3_i_3  ) \<or>
(r=n_SendGntS4_i_3  ) \<or>
(r=n_RecvInvAck5_i_3  ) \<or>
(r=n_RecvReqE11_i_3  ) \<or>
(r=n_RecvReqS12_i_3  ) \<or>
(\<exists> d. d\<le>N\<and>r=n_Store_i_3  d)\<or> r=skipRule
}"



subsection{*Definitions of a Formally Parameterized Invariant Formulas*}

definition inv_inv__511::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv_inv__511 p__Inv1 p__Inv2 \<equiv>
(implyForm (neg (eqn (Const (index p__Inv1)) (Const (index p__Inv2)))) (implyForm (andForm (eqn (IVar (Ident ''ExGntd'')) (Const true)) (eqn (IVar (Para (Ident ''ShrSet'') p__Inv2)) (Const true))) (neg (eqn (IVar (Para (Ident ''ShrSet'') p__Inv1)) (Const true)))))"

definition inv_inv__513::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv_inv__513 p__Inv1 p__Inv2 \<equiv>
(implyForm (neg (eqn (Const (index p__Inv1)) (Const (index p__Inv2)))) (implyForm (andForm (eqn (IVar (Para (Ident ''ShrSet'') p__Inv1)) (Const true)) (eqn (IVar (Ident ''ExGntd'')) (Const true))) (neg (eqn (IVar (Para (Ident ''ShrSet'') p__Inv2)) (Const true)))))"

definition inv_inv__4422::"nat \<Rightarrow> formula" where [simp]:
"inv_inv__4422 p__Inv2 \<equiv>
(implyForm (andForm (eqn (IVar (Ident ''CurCmd'')) (Const ReqS)) (eqn (IVar (Ident ''ExGntd'')) (Const false))) (neg (eqn (IVar (Field (Para (Ident ''Chan3'') p__Inv2) ''Cmd'')) (Const InvAck))))"

definition inv_inv__4325::"nat \<Rightarrow> formula" where [simp]:
"inv_inv__4325 p__Inv2 \<equiv>
(implyForm (eqn (IVar (Ident ''CurCmd'')) (Const Empty)) (neg (eqn (IVar (Field (Para (Ident ''Chan3'') p__Inv2) ''Cmd'')) (Const InvAck))))"

definition inv_inv__4326::"nat \<Rightarrow> formula" where [simp]:
"inv_inv__4326 p__Inv2 \<equiv>
(implyForm (eqn (IVar (Field (Para (Ident ''Chan3'') p__Inv2) ''Cmd'')) (Const InvAck)) (neg (eqn (IVar (Ident ''CurCmd'')) (Const Empty))))"

definition inv_inv__4227::"nat \<Rightarrow> formula" where [simp]:
"inv_inv__4227 p__Inv2 \<equiv>
(implyForm (andForm (eqn (IVar (Ident ''CurCmd'')) (Const ReqS)) (eqn (IVar (Ident ''ExGntd'')) (Const false))) (neg (eqn (IVar (Field (Para (Ident ''Chan2'') p__Inv2) ''Cmd'')) (Const Inv))))"

definition inv_inv__4130::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv_inv__4130 p__Inv1 p__Inv2 \<equiv>
(implyForm (neg (eqn (Const (index p__Inv1)) (Const (index p__Inv2)))) (implyForm (eqn (IVar (Para (Ident ''ShrSet'') p__Inv1)) (Const true)) (neg (eqn (IVar (Field (Para (Ident ''Chan2'') p__Inv2) ''Cmd'')) (Const GntE)))))"

definition inv_inv__4032::"nat \<Rightarrow> formula" where [simp]:
"inv_inv__4032 p__Inv2 \<equiv>
(implyForm (eqn (IVar (Field (Para (Ident ''Chan3'') p__Inv2) ''Cmd'')) (Const InvAck)) (neg (eqn (IVar (Field (Para (Ident ''Chan2'') p__Inv2) ''Cmd'')) (Const GntS))))"

definition inv_inv__3934::"nat \<Rightarrow> formula" where [simp]:
"inv_inv__3934 p__Inv2 \<equiv>
(implyForm (eqn (IVar (Field (Para (Ident ''Chan3'') p__Inv2) ''Cmd'')) (Const InvAck)) (neg (eqn (IVar (Para (Ident ''InvSet'') p__Inv2)) (Const true))))"

definition inv_inv__3837::"nat \<Rightarrow> formula" where [simp]:
"inv_inv__3837 p__Inv2 \<equiv>
(implyForm (eqn (IVar (Ident ''CurCmd'')) (Const Empty)) (neg (eqn (IVar (Field (Para (Ident ''Chan2'') p__Inv2) ''Cmd'')) (Const Inv))))"

definition inv_inv__3738::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv_inv__3738 p__Inv1 p__Inv2 \<equiv>
(implyForm (neg (eqn (Const (index p__Inv1)) (Const (index p__Inv2)))) (implyForm (eqn (IVar (Para (Ident ''ShrSet'') p__Inv1)) (Const true)) (neg (eqn (IVar (Field (Para (Ident ''Cache'') p__Inv2) ''State'')) (Const E)))))"

definition inv_inv__3739::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv_inv__3739 p__Inv1 p__Inv2 \<equiv>
(implyForm (neg (eqn (Const (index p__Inv1)) (Const (index p__Inv2)))) (implyForm (eqn (IVar (Field (Para (Ident ''Cache'') p__Inv2) ''State'')) (Const E)) (neg (eqn (IVar (Para (Ident ''ShrSet'') p__Inv1)) (Const true)))))"

definition inv_inv__3543::"nat \<Rightarrow> formula" where [simp]:
"inv_inv__3543 p__Inv2 \<equiv>
(implyForm (eqn (IVar (Para (Ident ''ShrSet'') p__Inv2)) (Const false)) (neg (eqn (IVar (Field (Para (Ident ''Chan2'') p__Inv2) ''Cmd'')) (Const GntE))))"

definition inv_inv__3444::"nat \<Rightarrow> formula" where [simp]:
"inv_inv__3444 p__Inv2 \<equiv>
(implyForm (eqn (IVar (Field (Para (Ident ''Chan3'') p__Inv2) ''Cmd'')) (Const InvAck)) (neg (neg (eqn (IVar (Field (Para (Ident ''Cache'') p__Inv2) ''State'')) (Const I)))))"

definition inv_inv__3445::"nat \<Rightarrow> formula" where [simp]:
"inv_inv__3445 p__Inv2 \<equiv>
(implyForm (neg (eqn (IVar (Field (Para (Ident ''Cache'') p__Inv2) ''State'')) (Const I))) (neg (eqn (IVar (Field (Para (Ident ''Chan3'') p__Inv2) ''Cmd'')) (Const InvAck))))"

definition inv_inv__3346::"nat \<Rightarrow> formula" where [simp]:
"inv_inv__3346 p__Inv2 \<equiv>
(implyForm (eqn (IVar (Para (Ident ''ShrSet'') p__Inv2)) (Const false)) (neg (eqn (IVar (Field (Para (Ident ''Chan2'') p__Inv2) ''Cmd'')) (Const GntS))))"

definition inv_inv__3248::"nat \<Rightarrow> formula" where [simp]:
"inv_inv__3248 p__Inv2 \<equiv>
(implyForm (eqn (IVar (Field (Para (Ident ''Chan3'') p__Inv2) ''Cmd'')) (Const InvAck)) (neg (eqn (IVar (Field (Para (Ident ''Chan2'') p__Inv2) ''Cmd'')) (Const Inv))))"

definition inv_inv__3151::"nat \<Rightarrow> formula" where [simp]:
"inv_inv__3151 p__Inv2 \<equiv>
(implyForm (eqn (IVar (Ident ''ExGntd'')) (Const true)) (neg (eqn (IVar (Field (Para (Ident ''Chan2'') p__Inv2) ''Cmd'')) (Const GntS))))"

definition inv_inv__3052::"nat \<Rightarrow> formula" where [simp]:
"inv_inv__3052 p__Inv2 \<equiv>
(implyForm (eqn (IVar (Para (Ident ''ShrSet'') p__Inv2)) (Const false)) (neg (eqn (IVar (Para (Ident ''InvSet'') p__Inv2)) (Const true))))"

definition inv_inv__2762::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv_inv__2762 p__Inv1 p__Inv2 \<equiv>
(implyForm (neg (eqn (Const (index p__Inv1)) (Const (index p__Inv2)))) (implyForm (eqn (IVar (Field (Para (Ident ''Cache'') p__Inv1) ''State'')) (Const E)) (neg (eqn (IVar (Para (Ident ''InvSet'') p__Inv2)) (Const true)))))"

definition inv_inv__2467::"nat \<Rightarrow> formula" where [simp]:
"inv_inv__2467 p__Inv2 \<equiv>
(implyForm (eqn (IVar (Para (Ident ''ShrSet'') p__Inv2)) (Const false)) (neg (neg (eqn (IVar (Field (Para (Ident ''Cache'') p__Inv2) ''State'')) (Const I)))))"

definition inv_inv__2468::"nat \<Rightarrow> formula" where [simp]:
"inv_inv__2468 p__Inv2 \<equiv>
(implyForm (neg (eqn (IVar (Field (Para (Ident ''Cache'') p__Inv2) ''State'')) (Const I))) (neg (eqn (IVar (Para (Ident ''ShrSet'') p__Inv2)) (Const false))))"

definition inv_inv__2271::"nat \<Rightarrow> formula" where [simp]:
"inv_inv__2271 p__Inv2 \<equiv>
(implyForm (eqn (IVar (Para (Ident ''ShrSet'') p__Inv2)) (Const false)) (neg (eqn (IVar (Field (Para (Ident ''Chan2'') p__Inv2) ''Cmd'')) (Const Inv))))"

definition inv_inv__2078::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv_inv__2078 p__Inv1 p__Inv2 \<equiv>
(implyForm (neg (eqn (Const (index p__Inv1)) (Const (index p__Inv2)))) (implyForm (eqn (IVar (Field (Para (Ident ''Cache'') p__Inv2) ''State'')) (Const E)) (neg (eqn (IVar (Field (Para (Ident ''Chan2'') p__Inv1) ''Cmd'')) (Const Inv)))))"

definition inv_inv__1979::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv_inv__1979 p__Inv1 p__Inv2 \<equiv>
(implyForm (neg (eqn (Const (index p__Inv1)) (Const (index p__Inv2)))) (implyForm (eqn (IVar (Field (Para (Ident ''Chan3'') p__Inv2) ''Cmd'')) (Const InvAck)) (neg (eqn (IVar (Field (Para (Ident ''Chan2'') p__Inv1) ''Cmd'')) (Const GntE)))))"

definition inv_inv__1881::"nat \<Rightarrow> formula" where [simp]:
"inv_inv__1881 p__Inv2 \<equiv>
(implyForm (eqn (IVar (Field (Para (Ident ''Chan3'') p__Inv2) ''Cmd'')) (Const InvAck)) (neg (eqn (IVar (Field (Para (Ident ''Chan2'') p__Inv2) ''Cmd'')) (Const GntE))))"

definition inv_inv__1783::"nat \<Rightarrow> formula" where [simp]:
"inv_inv__1783 p__Inv2 \<equiv>
(implyForm (eqn (IVar (Field (Para (Ident ''Cache'') p__Inv2) ''State'')) (Const E)) (neg (eqn (IVar (Field (Para (Ident ''Chan2'') p__Inv2) ''Cmd'')) (Const GntE))))"

definition inv_inv__1685::"nat \<Rightarrow> formula" where [simp]:
"inv_inv__1685 p__Inv2 \<equiv>
(implyForm (eqn (IVar (Field (Para (Ident ''Cache'') p__Inv2) ''State'')) (Const E)) (neg (eqn (IVar (Field (Para (Ident ''Chan2'') p__Inv2) ''Cmd'')) (Const GntS))))"

definition inv_inv__1588::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv_inv__1588 p__Inv1 p__Inv2 \<equiv>
(implyForm (neg (eqn (Const (index p__Inv1)) (Const (index p__Inv2)))) (implyForm (eqn (IVar (Field (Para (Ident ''Cache'') p__Inv1) ''State'')) (Const E)) (neg (eqn (IVar (Field (Para (Ident ''Chan2'') p__Inv2) ''Cmd'')) (Const GntE)))))"

definition inv_inv__1490::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv_inv__1490 p__Inv1 p__Inv2 \<equiv>
(implyForm (neg (eqn (Const (index p__Inv1)) (Const (index p__Inv2)))) (implyForm (neg (eqn (IVar (Field (Para (Ident ''Cache'') p__Inv2) ''State'')) (Const I))) (neg (eqn (IVar (Field (Para (Ident ''Chan2'') p__Inv1) ''Cmd'')) (Const GntE)))))"

definition inv_inv__1392::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv_inv__1392 p__Inv1 p__Inv2 \<equiv>
(implyForm (neg (eqn (Const (index p__Inv1)) (Const (index p__Inv2)))) (implyForm (eqn (IVar (Field (Para (Ident ''Cache'') p__Inv1) ''State'')) (Const E)) (neg (eqn (IVar (Field (Para (Ident ''Chan2'') p__Inv2) ''Cmd'')) (Const GntS)))))"

definition inv_inv__1293::"nat \<Rightarrow> formula" where [simp]:
"inv_inv__1293 p__Inv2 \<equiv>
(implyForm (eqn (IVar (Para (Ident ''ShrSet'') p__Inv2)) (Const false)) (neg (eqn (IVar (Field (Para (Ident ''Chan3'') p__Inv2) ''Cmd'')) (Const InvAck))))"

definition inv_inv__1294::"nat \<Rightarrow> formula" where [simp]:
"inv_inv__1294 p__Inv2 \<equiv>
(implyForm (eqn (IVar (Field (Para (Ident ''Chan3'') p__Inv2) ''Cmd'')) (Const InvAck)) (neg (eqn (IVar (Para (Ident ''ShrSet'') p__Inv2)) (Const false))))"

definition inv_inv__1197::"nat \<Rightarrow> formula" where [simp]:
"inv_inv__1197 p__Inv2 \<equiv>
(implyForm (andForm (eqn (IVar (Ident ''ExGntd'')) (Const true)) (neg (eqn (IVar (Field (Para (Ident ''Cache'') p__Inv2) ''State'')) (Const E)))) (neg (eqn (IVar (Field (Para (Ident ''Chan2'') p__Inv2) ''Cmd'')) (Const Inv))))"

definition inv_inv__1099::"nat \<Rightarrow> formula" where [simp]:
"inv_inv__1099 p__Inv2 \<equiv>
(implyForm (eqn (IVar (Ident ''ExGntd'')) (Const false)) (neg (eqn (IVar (Field (Para (Ident ''Chan2'') p__Inv2) ''Cmd'')) (Const GntE))))"

definition inv_inv__9100::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv_inv__9100 p__Inv1 p__Inv2 \<equiv>
(implyForm (neg (eqn (Const (index p__Inv1)) (Const (index p__Inv2)))) (implyForm (eqn (IVar (Field (Para (Ident ''Chan3'') p__Inv2) ''Cmd'')) (Const InvAck)) (neg (eqn (IVar (Field (Para (Ident ''Cache'') p__Inv1) ''State'')) (Const E)))))"

definition inv_inv__9101::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv_inv__9101 p__Inv1 p__Inv2 \<equiv>
(implyForm (neg (eqn (Const (index p__Inv1)) (Const (index p__Inv2)))) (implyForm (eqn (IVar (Field (Para (Ident ''Cache'') p__Inv1) ''State'')) (Const E)) (neg (eqn (IVar (Field (Para (Ident ''Chan3'') p__Inv2) ''Cmd'')) (Const InvAck)))))"

definition inv_inv__8102::"nat \<Rightarrow> formula" where [simp]:
"inv_inv__8102 p__Inv2 \<equiv>
(implyForm (eqn (IVar (Field (Para (Ident ''Chan3'') p__Inv2) ''Cmd'')) (Const InvAck)) (neg (eqn (IVar (Field (Para (Ident ''Cache'') p__Inv2) ''State'')) (Const E))))"

definition inv_inv__8103::"nat \<Rightarrow> formula" where [simp]:
"inv_inv__8103 p__Inv2 \<equiv>
(implyForm (eqn (IVar (Field (Para (Ident ''Cache'') p__Inv2) ''State'')) (Const E)) (neg (eqn (IVar (Field (Para (Ident ''Chan3'') p__Inv2) ''Cmd'')) (Const InvAck))))"

definition inv_inv__5108::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv_inv__5108 p__Inv1 p__Inv2 \<equiv>
(implyForm (neg (eqn (Const (index p__Inv1)) (Const (index p__Inv2)))) (implyForm (eqn (IVar (Field (Para (Ident ''Cache'') p__Inv2) ''State'')) (Const E)) (neg (neg (eqn (IVar (Field (Para (Ident ''Cache'') p__Inv1) ''State'')) (Const I))))))"

definition inv_inv__5109::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv_inv__5109 p__Inv1 p__Inv2 \<equiv>
(implyForm (neg (eqn (Const (index p__Inv1)) (Const (index p__Inv2)))) (implyForm (neg (eqn (IVar (Field (Para (Ident ''Cache'') p__Inv1) ''State'')) (Const I))) (neg (eqn (IVar (Field (Para (Ident ''Cache'') p__Inv2) ''State'')) (Const E)))))"

definition inv_inv__4110::"nat \<Rightarrow> formula" where [simp]:
"inv_inv__4110 p__Inv2 \<equiv>
(implyForm (andForm (eqn (IVar (Ident ''ExGntd'')) (Const true)) (eqn (IVar (Field (Para (Ident ''Chan3'') p__Inv2) ''Cmd'')) (Const InvAck))) (neg (neg (eqn (IVar (Field (Para (Ident ''Chan3'') p__Inv2) ''Data'')) (IVar (Ident ''AuxData''))))))"

definition inv_inv__3113::"nat \<Rightarrow> formula" where [simp]:
"inv_inv__3113 p__Inv2 \<equiv>
(implyForm (eqn (IVar (Field (Para (Ident ''Cache'') p__Inv2) ''State'')) (Const E)) (neg (eqn (IVar (Ident ''ExGntd'')) (Const false))))"

definition inv_inv__3114::"nat \<Rightarrow> formula" where [simp]:
"inv_inv__3114 p__Inv2 \<equiv>
(implyForm (eqn (IVar (Ident ''ExGntd'')) (Const false)) (neg (eqn (IVar (Field (Para (Ident ''Cache'') p__Inv2) ''State'')) (Const E))))"

definition inv_inv__2116::"nat \<Rightarrow> formula" where [simp]:
"inv_inv__2116 p__Inv2 \<equiv>
(implyForm (neg (eqn (IVar (Field (Para (Ident ''Cache'') p__Inv2) ''State'')) (Const I))) (neg (neg (eqn (IVar (Field (Para (Ident ''Cache'') p__Inv2) ''Data'')) (IVar (Ident ''AuxData''))))))"

definition inv_inv__1118::"formula" where [simp]:
"inv_inv__1118  \<equiv>
(implyForm (eqn (IVar (Ident ''ExGntd'')) (Const false)) (neg (neg (eqn (IVar (Ident ''MemData'')) (IVar (Ident ''AuxData''))))))"

subsection{*Definitions of  the Set of Invariant Formula Instances in a $N$-protocol Instance*}
definition invariants::"nat \<Rightarrow> formula set" where [simp]:
"invariants N \<equiv> {f.
(\<exists> p__Inv1 p__Inv2. p__Inv1\<le>N\<and>p__Inv2\<le>N\<and>p__Inv1~=p__Inv2\<and>f=inv_inv__511  p__Inv1 p__Inv2) \<or>
(\<exists> p__Inv1 p__Inv2. p__Inv1\<le>N\<and>p__Inv2\<le>N\<and>p__Inv1~=p__Inv2\<and>f=inv_inv__513  p__Inv1 p__Inv2) \<or>
(\<exists> p__Inv2. p__Inv2\<le>N\<and>f=inv_inv__4422  p__Inv2) \<or>
(\<exists> p__Inv2. p__Inv2\<le>N\<and>f=inv_inv__4325  p__Inv2) \<or>
(\<exists> p__Inv2. p__Inv2\<le>N\<and>f=inv_inv__4326  p__Inv2) \<or>
(\<exists> p__Inv2. p__Inv2\<le>N\<and>f=inv_inv__4227  p__Inv2) \<or>
(\<exists> p__Inv1 p__Inv2. p__Inv1\<le>N\<and>p__Inv2\<le>N\<and>p__Inv1~=p__Inv2\<and>f=inv_inv__4130  p__Inv1 p__Inv2) \<or>
(\<exists> p__Inv2. p__Inv2\<le>N\<and>f=inv_inv__4032  p__Inv2) \<or>
(\<exists> p__Inv2. p__Inv2\<le>N\<and>f=inv_inv__3934  p__Inv2) \<or>
(\<exists> p__Inv2. p__Inv2\<le>N\<and>f=inv_inv__3837  p__Inv2) \<or>
(\<exists> p__Inv1 p__Inv2. p__Inv1\<le>N\<and>p__Inv2\<le>N\<and>p__Inv1~=p__Inv2\<and>f=inv_inv__3738  p__Inv1 p__Inv2) \<or>
(\<exists> p__Inv1 p__Inv2. p__Inv1\<le>N\<and>p__Inv2\<le>N\<and>p__Inv1~=p__Inv2\<and>f=inv_inv__3739  p__Inv1 p__Inv2) \<or>
(\<exists> p__Inv2. p__Inv2\<le>N\<and>f=inv_inv__3543  p__Inv2) \<or>
(\<exists> p__Inv2. p__Inv2\<le>N\<and>f=inv_inv__3444  p__Inv2) \<or>
(\<exists> p__Inv2. p__Inv2\<le>N\<and>f=inv_inv__3445  p__Inv2) \<or>
(\<exists> p__Inv2. p__Inv2\<le>N\<and>f=inv_inv__3346  p__Inv2) \<or>
(\<exists> p__Inv2. p__Inv2\<le>N\<and>f=inv_inv__3248  p__Inv2) \<or>
(\<exists> p__Inv2. p__Inv2\<le>N\<and>f=inv_inv__3151  p__Inv2) \<or>
(\<exists> p__Inv2. p__Inv2\<le>N\<and>f=inv_inv__3052  p__Inv2) \<or>
(\<exists> p__Inv1 p__Inv2. p__Inv1\<le>N\<and>p__Inv2\<le>N\<and>p__Inv1~=p__Inv2\<and>f=inv_inv__2762  p__Inv1 p__Inv2) \<or>
(\<exists> p__Inv2. p__Inv2\<le>N\<and>f=inv_inv__2467  p__Inv2) \<or>
(\<exists> p__Inv2. p__Inv2\<le>N\<and>f=inv_inv__2468  p__Inv2) \<or>
(\<exists> p__Inv2. p__Inv2\<le>N\<and>f=inv_inv__2271  p__Inv2) \<or>
(\<exists> p__Inv1 p__Inv2. p__Inv1\<le>N\<and>p__Inv2\<le>N\<and>p__Inv1~=p__Inv2\<and>f=inv_inv__2078  p__Inv1 p__Inv2) \<or>
(\<exists> p__Inv1 p__Inv2. p__Inv1\<le>N\<and>p__Inv2\<le>N\<and>p__Inv1~=p__Inv2\<and>f=inv_inv__1979  p__Inv1 p__Inv2) \<or>
(\<exists> p__Inv2. p__Inv2\<le>N\<and>f=inv_inv__1881  p__Inv2) \<or>
(\<exists> p__Inv2. p__Inv2\<le>N\<and>f=inv_inv__1783  p__Inv2) \<or>
(\<exists> p__Inv2. p__Inv2\<le>N\<and>f=inv_inv__1685  p__Inv2) \<or>
(\<exists> p__Inv1 p__Inv2. p__Inv1\<le>N\<and>p__Inv2\<le>N\<and>p__Inv1~=p__Inv2\<and>f=inv_inv__1588  p__Inv1 p__Inv2) \<or>
(\<exists> p__Inv1 p__Inv2. p__Inv1\<le>N\<and>p__Inv2\<le>N\<and>p__Inv1~=p__Inv2\<and>f=inv_inv__1490  p__Inv1 p__Inv2) \<or>
(\<exists> p__Inv1 p__Inv2. p__Inv1\<le>N\<and>p__Inv2\<le>N\<and>p__Inv1~=p__Inv2\<and>f=inv_inv__1392  p__Inv1 p__Inv2) \<or>
(\<exists> p__Inv2. p__Inv2\<le>N\<and>f=inv_inv__1293  p__Inv2) \<or>
(\<exists> p__Inv2. p__Inv2\<le>N\<and>f=inv_inv__1294  p__Inv2) \<or>
(\<exists> p__Inv2. p__Inv2\<le>N\<and>f=inv_inv__1197  p__Inv2) \<or>
(\<exists> p__Inv2. p__Inv2\<le>N\<and>f=inv_inv__1099  p__Inv2) \<or>
(\<exists> p__Inv1 p__Inv2. p__Inv1\<le>N\<and>p__Inv2\<le>N\<and>p__Inv1~=p__Inv2\<and>f=inv_inv__9100  p__Inv1 p__Inv2) \<or>
(\<exists> p__Inv1 p__Inv2. p__Inv1\<le>N\<and>p__Inv2\<le>N\<and>p__Inv1~=p__Inv2\<and>f=inv_inv__9101  p__Inv1 p__Inv2) \<or>
(\<exists> p__Inv2. p__Inv2\<le>N\<and>f=inv_inv__8102  p__Inv2) \<or>
(\<exists> p__Inv2. p__Inv2\<le>N\<and>f=inv_inv__8103  p__Inv2) \<or>
(\<exists> p__Inv1 p__Inv2. p__Inv1\<le>N\<and>p__Inv2\<le>N\<and>p__Inv1~=p__Inv2\<and>f=inv_inv__5108  p__Inv1 p__Inv2) \<or>
(\<exists> p__Inv1 p__Inv2. p__Inv1\<le>N\<and>p__Inv2\<le>N\<and>p__Inv1~=p__Inv2\<and>f=inv_inv__5109  p__Inv1 p__Inv2) \<or>
(\<exists> p__Inv2. p__Inv2\<le>N\<and>f=inv_inv__4110  p__Inv2) \<or>
(\<exists> p__Inv2. p__Inv2\<le>N\<and>f=inv_inv__3113  p__Inv2) \<or>
(\<exists> p__Inv2. p__Inv2\<le>N\<and>f=inv_inv__3114  p__Inv2) \<or>
(\<exists> p__Inv2. p__Inv2\<le>N\<and>f=inv_inv__2116  p__Inv2) \<or>
(f=inv_inv__1118  )
}" 

subsection{*Definitions of  the Set of Abs Invariant Formula Instances *}
definition invariantsAbs  ::"  formula list" where [simp]:
"invariantsAbs   \<equiv> [
inv_inv__511 0 1 ,
inv_inv__511 1 0 ,
inv_inv__513 0 1 ,
inv_inv__513 1 0 ,
inv_inv__4422 0 ,
inv_inv__4422 1 ,
inv_inv__4325 0 ,
inv_inv__4325 1 ,
inv_inv__4326 0 ,
inv_inv__4326 1 ,
inv_inv__4227 0 ,
inv_inv__4227 1 ,
inv_inv__4130 0 1 ,
inv_inv__4130 1 0 ,
inv_inv__4032 0 ,
inv_inv__4032 1 ,
inv_inv__3934 0 ,
inv_inv__3934 1 ,
inv_inv__3837 0 ,
inv_inv__3837 1 ,
inv_inv__3738 0 1 ,
inv_inv__3738 1 0 ,
inv_inv__3739 0 1 ,
inv_inv__3739 1 0 ,
inv_inv__3543 0 ,
inv_inv__3543 1 ,
inv_inv__3444 0 ,
inv_inv__3444 1 ,
inv_inv__3445 0 ,
inv_inv__3445 1 ,
inv_inv__3346 0 ,
inv_inv__3346 1 ,
inv_inv__3248 0 ,
inv_inv__3248 1 ,
inv_inv__3151 0 ,
inv_inv__3151 1 ,
inv_inv__3052 0 ,
inv_inv__3052 1 ,
inv_inv__2762 0 1 ,
inv_inv__2762 1 0 ,
inv_inv__2467 0 ,
inv_inv__2467 1 ,
inv_inv__2468 0 ,
inv_inv__2468 1 ,
inv_inv__2271 0 ,
inv_inv__2271 1 ,
inv_inv__2078 0 1 ,
inv_inv__2078 1 0 ,
inv_inv__1979 0 1 ,
inv_inv__1979 1 0 ,
inv_inv__1881 0 ,
inv_inv__1881 1 ,
inv_inv__1783 0 ,
inv_inv__1783 1 ,
inv_inv__1685 0 ,
inv_inv__1685 1 ,
inv_inv__1588 0 1 ,
inv_inv__1588 1 0 ,
inv_inv__1490 0 1 ,
inv_inv__1490 1 0 ,
inv_inv__1392 0 1 ,
inv_inv__1392 1 0 ,
inv_inv__1293 0 ,
inv_inv__1293 1 ,
inv_inv__1294 0 ,
inv_inv__1294 1 ,
inv_inv__1197 0 ,
inv_inv__1197 1 ,
inv_inv__1099 0 ,
inv_inv__1099 1 ,
inv_inv__9100 0 1 ,
inv_inv__9100 1 0 ,
inv_inv__9101 0 1 ,
inv_inv__9101 1 0 ,
inv_inv__8102 0 ,
inv_inv__8102 1 ,
inv_inv__8103 0 ,
inv_inv__8103 1 ,
inv_inv__5108 0 1 ,
inv_inv__5108 1 0 ,
inv_inv__5109 0 1 ,
inv_inv__5109 1 0 ,
inv_inv__4110 0 ,
inv_inv__4110 1 ,
inv_inv__3113 0 ,
inv_inv__3113 1 ,
inv_inv__3114 0 ,
inv_inv__3114 1 ,
inv_inv__2116 0 ,
inv_inv__2116 1 ,
inv_inv__1118
]"

definition initSpec0::"nat \<Rightarrow> formula" where [simp]:
"initSpec0 N \<equiv> (forallForm (down N) (% i . (eqn (IVar (Field (Para (Ident ''Chan1'') i) ''Cmd'')) (Const Empty))))"

definition initSpec1::"nat \<Rightarrow> formula" where [simp]:
"initSpec1 N \<equiv> (forallForm (down N) (% i . (eqn (IVar (Field (Para (Ident ''Chan2'') i) ''Cmd'')) (Const Empty))))"

definition initSpec2::"nat \<Rightarrow> formula" where [simp]:
"initSpec2 N \<equiv> (forallForm (down N) (% i . (eqn (IVar (Field (Para (Ident ''Chan3'') i) ''Cmd'')) (Const Empty))))"

definition initSpec3::"nat \<Rightarrow> formula" where [simp]:
"initSpec3 N \<equiv> (forallForm (down N) (% i . (eqn (IVar (Field (Para (Ident ''Cache'') i) ''State'')) (Const I))))"

definition initSpec4::"nat \<Rightarrow> formula" where [simp]:
"initSpec4 N \<equiv> (forallForm (down N) (% i . (eqn (IVar (Para (Ident ''InvSet'') i)) (Const false))))"

definition initSpec5::"nat \<Rightarrow> formula" where [simp]:
"initSpec5 N \<equiv> (forallForm (down N) (% i . (eqn (IVar (Para (Ident ''ShrSet'') i)) (Const false))))"

definition initSpec6::"formula" where [simp]:
"initSpec6  \<equiv> (eqn (IVar (Ident ''ExGntd'')) (Const false))"

definition initSpec7::"formula" where [simp]:
"initSpec7  \<equiv> (eqn (IVar (Ident ''CurCmd'')) (Const Empty))"

definition initSpec8::"formula" where [simp]:
"initSpec8  \<equiv> (eqn (IVar (Ident ''MemData'')) (Const (index 1)))"

definition initSpec9::"formula" where [simp]:
"initSpec9  \<equiv> (eqn (IVar (Ident ''AuxData'')) (Const (index 1)))"

definition allInitSpecs::"nat \<Rightarrow> formula list" where [simp]:
"allInitSpecs N \<equiv> [
(initSpec0 N),
(initSpec1 N),
(initSpec2 N),
(initSpec3 N),
(initSpec4 N),
(initSpec5 N),
(initSpec6 ),
(initSpec7 ),
(initSpec8 ),
(initSpec9 )
]"

axiomatization  where axiomOnf2 [simp,intro]:
   "s \<in> reachableSet (set (allInitSpecs N )) (rules N)   \<Longrightarrow>i\<noteq>j \<Longrightarrow> 
   formEval (f 0 1) s \<Longrightarrow> formEval (f i j) s"
axiomatization  where axiomOnf1 [simp,intro]:
   "s \<in> reachableSet (set (allInitSpecs N )) (rules N)  \<Longrightarrow>formEval (f 0 ) s \<Longrightarrow> formEval (f i) s"

lemma usThm1:
  assumes a1:"f \<in> (set invariantsAbs)" and a4:"\<forall>f.  f \<in>(set invariantsAbs) \<longrightarrow>  formEval f s"
  shows "formEval f  s"
  using a4 local.a1 by blast 




subsection{*Definitions of initial states*}

lemma lemmaOnn_RecvGntE1Gt_i:
  assumes a1:"NC<i" and a2:"s \<in> reachableSet (set (allInitSpecs N)) (rules N)"  and  
  a4:"\<forall>f.  f \<in>(set invariantsAbs) \<longrightarrow>  formEval f s" 
shows "trans_sim_on3 (n_RecvGntE1  i  ) skipRule VF  VF' NC s" (is "trans_sim_on3 ?r ?r' VF VF' NC s")
proof(unfold trans_sim_on3_def,(rule allI)+,(rule impI)+,rule disjI2)
  fix s2 
  assume b0:"state_sim_on3 s s2 VF VF' NC "
  show "state_sim_on3 (trans (act (?r)) s) s2 VF VF' NC"
  proof(cut_tac a1,unfold state_sim_on3_def,rule conjI)
    show "\<forall>v. v \<in> VF \<longrightarrow> trans (act ?r) s v = s2 v"
    proof(rule allI,rule impI)
    fix f v
    assume b1:" v \<in>  VF"  
    
    have b5:"trans (act (?r)) s v = s v" 
      by (cut_tac a1  b1,auto) 

    have b6:"s v =s2 v "
      using b0 b1 state_sim_on3_def by blast  
    show "trans (act (?r)) s v= s2 v"
      using b5 b6 by auto 
  qed
next
  show "\<forall>v. v \<in> VF' \<longrightarrow> scalar2Nat (trans (act ?r) s v) \<le> NC \<longrightarrow> trans (act ?r) s v = s2 v" 
    by(cut_tac b0, auto)
  
qed
qed
lemma lemmaOnn_RecvGntE1LeNc_:
  assumes a1:"i\<le>NC"  and a3:"NC\<le>N" 
  shows "trans_sim_on3 (n_RecvGntE1  i) (n_RecvGntE1  i) VF VF' NC s" (is "trans_sim_on3 ?r ?r' VF VF' NC  s")
proof(rule ruleSimCond3)
     from a3 show " formEval (pre ?r) s \<longrightarrow>formEval (pre ?r') s" (is "?A \<longrightarrow>?B")  
       apply (auto simp del:evalEqn)done
   next 
	show "(\<forall>  v. v \<in>  varOfSent (act  ?r')  \<longrightarrow> formEval (pre ?r) s \<longrightarrow> 
    expEval (substExpByStatement (IVar v)  (act ?r')) s = expEval (substExpByStatement (IVar v)  (act ?r)) s)"
   proof(rule allI,(rule impI)+)
      fix  v
      assume b1:"formEval (pre ?r) s" and b2:"v \<in>varOfSent (act ?r')"
  
  show "expEval (substExpByStatement (IVar v)  (act ?r')) s = expEval (substExpByStatement (IVar v)  (act ?r)) s"  
       apply (cut_tac  a1 a3 b1 b2 ,auto) done
   qed
 next
   show "\<forall>  v. v \<in>  varOfSent (act ?r) \<longrightarrow>  v \<in> VF \<longrightarrow> v \<in>  varOfSent (act ?r')" 
		by(cut_tac a1 a3, auto)
 next
   from a1 show "\<forall>v. v \<in> varOfForm (pre (?r')) \<longrightarrow>
     formEval (pre (?r)) s  \<longrightarrow>
 v \<in> VF  \<or> v \<in> VF' \<and> scalar2Nat (s v) \<le> NC" 
		apply(cut_tac a1 a3, auto) done
  
next 
  show "\<forall>v. v \<in> varOfSent (act ?r)\<longrightarrow>
        v \<in> VF'\<longrightarrow>         
        formEval (pre (?r)) s \<longrightarrow>
       scalar2Nat (expEval (substExpByStatement (IVar v) (act ?r)) s) \<le> NC
       \<longrightarrow> v \<in> varOfSent (act ?r')"
    	apply(cut_tac a1 a3, auto) done
next
  show "\<forall> v va. v \<in> varOfSent (act ?r') \<longrightarrow> 
  va\<in>varOfExp ( substExpByStatement (IVar v)  (act ?r')) \<longrightarrow>
   va \<in> VF \<or> (va \<in> VF' \<and> (scalar2Nat (s va))\<le> NC)  "
     apply(cut_tac a1 a3, auto) done
qed
lemma lemmaOnn_RecvGntE1: 
  assumes   a2:"s \<in> reachableSet (set (allInitSpecs N)) (rules N)"  and  
  a4:"\<forall>f.  f \<in>(set invariantsAbs) \<longrightarrow>  formEval f s" and a5:"\<exists> i. i\<le>N\<and>r=n_RecvGntE1  i"  and
  a6:"NC \<le> N"
  shows "\<exists> r'. r' \<in> rules NC\<and> trans_sim_on3 r r' VF VF' NC s" (is "\<exists>r'.?P1 r' \<and> ?P2 r'")
proof -
  from a5 obtain i where d0:"i\<le>N\<and>r=n_RecvGntE1  i"  by blast
  have "i>NC|i\<le> NC" by auto
  moreover{
       assume a1:"i>NC" 
        have "\<exists>r'. ?P1 r' \<and> ?P2 r'"
        proof(rule_tac x="(skipRule)" in exI,rule conjI)
          show  "?P1 (skipRule) " 
           by(cut_tac a1, auto) 
          next
          show  "?P2 (skipRule) "
           using lemmaOnn_RecvGntE1Gt_i local.a1 a2 a4 a6 d0 by blast 
        qed
       }
moreover{
       assume a1:"i\<le> NC" 
        have "\<exists>r'. ?P1 r' \<and> ?P2 r'"
        proof(rule_tac x="(n_RecvGntE1  i)" in exI,rule conjI)
          show  "?P1 (n_RecvGntE1  i) " 
           by(cut_tac a1, auto) 
          next
          show  "?P2 (n_RecvGntE1  i) "
           using lemmaOnn_RecvGntE1LeNc_ local.a1 a2 a4 a6 d0 by blast 
        qed
       }
  ultimately show "\<exists>r'.?P1 r' \<and> ?P2 r'" 
    by satx
qed

lemma lemmaOnn_RecvGntS2Gt_i:
  assumes a1:"NC<i" and a2:"s \<in> reachableSet (set (allInitSpecs N)) (rules N)"  and  
  a4:"\<forall>f.  f \<in>(set invariantsAbs) \<longrightarrow>  formEval f s" 
shows "trans_sim_on3 (n_RecvGntS2  i  ) skipRule VF  VF' NC s" (is "trans_sim_on3 ?r ?r' VF VF' NC s")
proof(unfold trans_sim_on3_def,(rule allI)+,(rule impI)+,rule disjI2)
  fix s2 
  assume b0:"state_sim_on3 s s2 VF VF' NC "
  show "state_sim_on3 (trans (act (?r)) s) s2 VF VF' NC"
  proof(cut_tac a1,unfold state_sim_on3_def,rule conjI)
    show "\<forall>v. v \<in> VF \<longrightarrow> trans (act ?r) s v = s2 v"
    proof(rule allI,rule impI)
    fix f v
    assume b1:" v \<in>  VF"  
    
    have b5:"trans (act (?r)) s v = s v" 
      by (cut_tac a1  b1,auto) 

    have b6:"s v =s2 v "
      using b0 b1 state_sim_on3_def by blast  
    show "trans (act (?r)) s v= s2 v"
      using b5 b6 by auto 
  qed
next
  show "\<forall>v. v \<in> VF' \<longrightarrow> scalar2Nat (trans (act ?r) s v) \<le> NC \<longrightarrow> trans (act ?r) s v = s2 v" 
    by(cut_tac b0, auto)
  
qed
qed
lemma lemmaOnn_RecvGntS2LeNc_:
  assumes a1:"i\<le>NC"  and a3:"NC\<le>N" 
  shows "trans_sim_on3 (n_RecvGntS2  i) (n_RecvGntS2  i) VF VF' NC s" (is "trans_sim_on3 ?r ?r' VF VF' NC  s")
proof(rule ruleSimCond3)
     from a3 show " formEval (pre ?r) s \<longrightarrow>formEval (pre ?r') s" (is "?A \<longrightarrow>?B")  
       apply (auto simp del:evalEqn)done
   next 
	show "(\<forall>  v. v \<in>  varOfSent (act  ?r')  \<longrightarrow> formEval (pre ?r) s \<longrightarrow> 
    expEval (substExpByStatement (IVar v)  (act ?r')) s = expEval (substExpByStatement (IVar v)  (act ?r)) s)"
   proof(rule allI,(rule impI)+)
      fix  v
      assume b1:"formEval (pre ?r) s" and b2:"v \<in>varOfSent (act ?r')"
  
  show "expEval (substExpByStatement (IVar v)  (act ?r')) s = expEval (substExpByStatement (IVar v)  (act ?r)) s"  
       apply (cut_tac  a1 a3 b1 b2 ,auto) done
   qed
 next
   show "\<forall>  v. v \<in>  varOfSent (act ?r) \<longrightarrow>  v \<in> VF \<longrightarrow> v \<in>  varOfSent (act ?r')" 
		by(cut_tac a1 a3, auto)
 next
   from a1 show "\<forall>v. v \<in> varOfForm (pre (?r')) \<longrightarrow>
     formEval (pre (?r)) s  \<longrightarrow>
 v \<in> VF  \<or> v \<in> VF' \<and> scalar2Nat (s v) \<le> NC" 
		apply(cut_tac a1 a3, auto) done
  
next 
  show "\<forall>v. v \<in> varOfSent (act ?r)\<longrightarrow>
        v \<in> VF'\<longrightarrow>         
        formEval (pre (?r)) s \<longrightarrow>
       scalar2Nat (expEval (substExpByStatement (IVar v) (act ?r)) s) \<le> NC
       \<longrightarrow> v \<in> varOfSent (act ?r')"
    	apply(cut_tac a1 a3, auto) done
next
  show "\<forall> v va. v \<in> varOfSent (act ?r') \<longrightarrow> 
  va\<in>varOfExp ( substExpByStatement (IVar v)  (act ?r')) \<longrightarrow>
   va \<in> VF \<or> (va \<in> VF' \<and> (scalar2Nat (s va))\<le> NC)  "
     apply(cut_tac a1 a3, auto) done
qed
lemma lemmaOnn_RecvGntS2: 
  assumes   a2:"s \<in> reachableSet (set (allInitSpecs N)) (rules N)"  and  
  a4:"\<forall>f.  f \<in>(set invariantsAbs) \<longrightarrow>  formEval f s" and a5:"\<exists> i. i\<le>N\<and>r=n_RecvGntS2  i"  and
  a6:"NC \<le> N"
  shows "\<exists> r'. r' \<in> rules NC\<and> trans_sim_on3 r r' VF VF' NC s" (is "\<exists>r'.?P1 r' \<and> ?P2 r'")
proof -
  from a5 obtain i where d0:"i\<le>N\<and>r=n_RecvGntS2  i"  by blast
  have "i>NC|i\<le> NC" by auto
  moreover{
       assume a1:"i>NC" 
        have "\<exists>r'. ?P1 r' \<and> ?P2 r'"
        proof(rule_tac x="(skipRule)" in exI,rule conjI)
          show  "?P1 (skipRule) " 
           by(cut_tac a1, auto) 
          next
          show  "?P2 (skipRule) "
           using lemmaOnn_RecvGntS2Gt_i local.a1 a2 a4 a6 d0 by blast 
        qed
       }
moreover{
       assume a1:"i\<le> NC" 
        have "\<exists>r'. ?P1 r' \<and> ?P2 r'"
        proof(rule_tac x="(n_RecvGntS2  i)" in exI,rule conjI)
          show  "?P1 (n_RecvGntS2  i) " 
           by(cut_tac a1, auto) 
          next
          show  "?P2 (n_RecvGntS2  i) "
           using lemmaOnn_RecvGntS2LeNc_ local.a1 a2 a4 a6 d0 by blast 
        qed
       }
  ultimately show "\<exists>r'.?P1 r' \<and> ?P2 r'" 
    by satx
qed

lemma lemmaOnn_SendGntE3Gt_i:
  assumes a1:"i>NC" and 
  a2:"s \<in> reachableSet (set (allInitSpecs N)) (rules N)"  and a3:"NC\<le>N" and  
  a4:"\<forall>f.  f \<in>(set invariantsAbs) \<longrightarrow>  formEval f s" 
  shows "trans_sim_on3 (n_SendGntE3 N i)  (n_SendGntE3_i_3 )  VF VF' NC s" (is "trans_sim_on3 ?r ?r' VF VF' NC s")
  proof(rule ruleSimCond3)
    show " formEval (pre ?r) s \<longrightarrow>formEval (pre ?r') s" (is "?A \<longrightarrow>?B")
    proof(rule impI)+
      assume b0:"?A"
  have tmp:"formEval (inv_inv__3052 0)  s"   
            by(rule usThm1, simp del:inv_inv__3052_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__3052 0  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c0:"formEval  (conclude (inv_inv__3052 0)) s" by auto
have tmp:"formEval (inv_inv__3052 0)  s"   
            by(rule usThm1, simp del:inv_inv__3052_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__3052 1  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c1:"formEval  (conclude (inv_inv__3052 1)) s" by auto
have tmp:"formEval (inv_inv__1293 0)  s"   
            by(rule usThm1, simp del:inv_inv__1293_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__1293 0  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c2:"formEval  (conclude (inv_inv__1293 0)) s" by auto
have tmp:"formEval (inv_inv__1293 0)  s"   
            by(rule usThm1, simp del:inv_inv__1293_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__1293 1  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c3:"formEval  (conclude (inv_inv__1293 1)) s" by auto
have tmp:"formEval (inv_inv__2271 0)  s"   
            by(rule usThm1, simp del:inv_inv__2271_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__2271 0  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c4:"formEval  (conclude (inv_inv__2271 0)) s" by auto
have tmp:"formEval (inv_inv__2271 0)  s"   
            by(rule usThm1, simp del:inv_inv__2271_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__2271 1  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c5:"formEval  (conclude (inv_inv__2271 1)) s" by auto
have tmp:"formEval (inv_inv__3346 0)  s"   
            by(rule usThm1, simp del:inv_inv__3346_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__3346 0  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c6:"formEval  (conclude (inv_inv__3346 0)) s" by auto
have tmp:"formEval (inv_inv__3346 0)  s"   
            by(rule usThm1, simp del:inv_inv__3346_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__3346 1  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c7:"formEval  (conclude (inv_inv__3346 1)) s" by auto
have tmp:"formEval (inv_inv__3543 0)  s"   
            by(rule usThm1, simp del:inv_inv__3543_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__3543 0  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c8:"formEval  (conclude (inv_inv__3543 0)) s" by auto
have tmp:"formEval (inv_inv__3543 0)  s"   
            by(rule usThm1, simp del:inv_inv__3543_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__3543 1  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c9:"formEval  (conclude (inv_inv__3543 1)) s" by auto
have tmp:"formEval (inv_inv__2467 0)  s"   
            by(rule usThm1, simp del:inv_inv__2467_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__2467 0  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c10:"formEval  (conclude (inv_inv__2467 0)) s" by auto
have tmp:"formEval (inv_inv__2467 0)  s"   
            by(rule usThm1, simp del:inv_inv__2467_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__2467 1  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c11:"formEval  (conclude (inv_inv__2467 1)) s" by auto
have tmp:"formEval (inv_inv__1099 0)  s"   
            by(rule usThm1, simp del:inv_inv__1099_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__1099 0  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c12:"formEval  (conclude (inv_inv__1099 0)) s" by auto
have tmp:"formEval (inv_inv__1099 0)  s"   
            by(rule usThm1, simp del:inv_inv__1099_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__1099 1  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c13:"formEval  (conclude (inv_inv__1099 1)) s" by auto
have tmp:"formEval (inv_inv__1099 0)  s"   
            by(rule usThm1, simp del:inv_inv__1099_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__1099 i  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c14:"formEval  (conclude (inv_inv__1099 i)) s" by auto
have tmp:"formEval (inv_inv__1099 0)  s"   
            by(rule usThm1, simp del:inv_inv__1099_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__1099 3  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c15:"formEval  (conclude (inv_inv__1099 3)) s" by auto
have tmp:"formEval (inv_inv__3114 0)  s"   
            by(rule usThm1, simp del:inv_inv__3114_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__3114 0  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c16:"formEval  (conclude (inv_inv__3114 0)) s" by auto
have tmp:"formEval (inv_inv__3114 0)  s"   
            by(rule usThm1, simp del:inv_inv__3114_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__3114 1  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c17:"formEval  (conclude (inv_inv__3114 1)) s" by auto
have tmp:"formEval (inv_inv__3114 0)  s"   
            by(rule usThm1, simp del:inv_inv__3114_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__3114 i  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c18:"formEval  (conclude (inv_inv__3114 i)) s" by auto
have tmp:"formEval (inv_inv__3114 0)  s"   
            by(rule usThm1, simp del:inv_inv__3114_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__3114 3  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c19:"formEval  (conclude (inv_inv__3114 3)) s" by auto
have tmp:"formEval (inv_inv__1118)  s"  
        		by(rule usThm1, simp del:inv_inv__1118_def,cut_tac a4,assumption )
        	 with b0 a1 have c20:"formEval  (conclude (inv_inv__1118)) s" by auto

      from a1 a3 b0 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 show "formEval (pre ?r') s" 
       by (auto simp del:evalEqn)
     qed
   next 
	show "(\<forall>  v. v \<in>  varOfSent (act  ?r')   \<longrightarrow> formEval (pre ?r) s \<longrightarrow> 
    expEval (substExpByStatement (IVar v)  (act ?r')) s = expEval (substExpByStatement (IVar v)  (act ?r)) s)"
   proof(rule allI,(rule impI)+)
      fix  v
     assume b1:"v \<in>varOfSent (act ?r')"  and b2:"formEval (pre ?r) s" 
  
  show "expEval (substExpByStatement (IVar v)  (act ?r')) s = expEval (substExpByStatement (IVar v)  (act ?r)) s"  
       apply (cut_tac  a1 a3 b1 b2 ,auto ) done
   qed
  next
   show "\<forall>  v. v \<in>  varOfSent (act ?r) \<longrightarrow>  v \<in> VF \<longrightarrow> v \<in>  varOfSent (act ?r')" 
		by(cut_tac a1 a3, auto)
 next
   from a1 show "\<forall>v. v \<in> varOfForm (pre (?r')) \<longrightarrow>
     formEval (pre (?r)) s \<longrightarrow> v \<in> VF  \<or> v \<in> VF' \<and> scalar2Nat (s v) \<le> NC" 
		by(cut_tac a1 a3, auto)
  
next 
  show "\<forall>v. v \<in> varOfSent (act ?r)\<longrightarrow>       
    v \<in> VF'\<longrightarrow> formEval (pre (?r)) s  \<longrightarrow> scalar2Nat (expEval (substExpByStatement (IVar v) (act ?r)) s) 
\<le> NC  \<longrightarrow> v \<in> varOfSent (act ?r')"
    	by(cut_tac a1 a3, auto)
next
  show "\<forall> v va. v \<in> varOfSent (act ?r') \<longrightarrow> 
  va\<in>varOfExp ( substExpByStatement (IVar v)  (act ?r')) \<longrightarrow>
   va \<in> VF \<or> (va \<in> VF' \<and> (scalar2Nat (s va))\<le> NC)  "
     apply(cut_tac a1 a3, auto) done
  
qed
lemma lemmaOnn_SendGntE3LeNc_:
  assumes a1:"i\<le>NC"  and a3:"NC\<le>N" 
  shows "trans_sim_on3 (n_SendGntE3 N i) (n_SendGntE3 NC i) VF VF' NC s" (is "trans_sim_on3 ?r ?r' VF VF' NC  s")
proof(rule ruleSimCond3)
     from a3 show " formEval (pre ?r) s \<longrightarrow>formEval (pre ?r') s" (is "?A \<longrightarrow>?B")  
       apply (auto simp del:evalEqn)done
   next 
	show "(\<forall>  v. v \<in>  varOfSent (act  ?r')  \<longrightarrow> formEval (pre ?r) s \<longrightarrow> 
    expEval (substExpByStatement (IVar v)  (act ?r')) s = expEval (substExpByStatement (IVar v)  (act ?r)) s)"
   proof(rule allI,(rule impI)+)
      fix  v
      assume b1:"formEval (pre ?r) s" and b2:"v \<in>varOfSent (act ?r')"
  
  show "expEval (substExpByStatement (IVar v)  (act ?r')) s = expEval (substExpByStatement (IVar v)  (act ?r)) s"  
       apply (cut_tac  a1 a3 b1 b2 ,auto) done
   qed
 next
   show "\<forall>  v. v \<in>  varOfSent (act ?r) \<longrightarrow>  v \<in> VF \<longrightarrow> v \<in>  varOfSent (act ?r')" 
		by(cut_tac a1 a3, auto)
 next
   from a1 show "\<forall>v. v \<in> varOfForm (pre (?r')) \<longrightarrow>
     formEval (pre (?r)) s  \<longrightarrow>
 v \<in> VF  \<or> v \<in> VF' \<and> scalar2Nat (s v) \<le> NC" 
		apply(cut_tac a1 a3, auto) done
  
next 
  show "\<forall>v. v \<in> varOfSent (act ?r)\<longrightarrow>
        v \<in> VF'\<longrightarrow>         
        formEval (pre (?r)) s \<longrightarrow>
       scalar2Nat (expEval (substExpByStatement (IVar v) (act ?r)) s) \<le> NC
       \<longrightarrow> v \<in> varOfSent (act ?r')"
    	apply(cut_tac a1 a3, auto) done
next
  show "\<forall> v va. v \<in> varOfSent (act ?r') \<longrightarrow> 
  va\<in>varOfExp ( substExpByStatement (IVar v)  (act ?r')) \<longrightarrow>
   va \<in> VF \<or> (va \<in> VF' \<and> (scalar2Nat (s va))\<le> NC)  "
     apply(cut_tac a1 a3, auto) done
qed
lemma lemmaOnn_SendGntE3: 
  assumes   a2:"s \<in> reachableSet (set (allInitSpecs N)) (rules N)"  and  
  a4:"\<forall>f.  f \<in>(set invariantsAbs) \<longrightarrow>  formEval f s" and a5:"\<exists> i. i\<le>N\<and>r=n_SendGntE3 N i"  and
  a6:"NC \<le> N"
  shows "\<exists> r'. r' \<in> rules NC\<and> trans_sim_on3 r r' VF VF' NC s" (is "\<exists>r'.?P1 r' \<and> ?P2 r'")
proof -
  from a5 obtain i where d0:"i\<le>N\<and>r=n_SendGntE3 N i"  by blast
  have "i>NC|i\<le> NC" by auto
  moreover{
       assume a1:"i>NC" 
        have "\<exists>r'. ?P1 r' \<and> ?P2 r'"
        proof(rule_tac x="(n_SendGntE3_i_3 )" in exI,rule conjI)
          show  "?P1 (n_SendGntE3_i_3 ) " 
           by(cut_tac a1, auto) 
          next
          show  "?P2 (n_SendGntE3_i_3 ) "
           using lemmaOnn_SendGntE3Gt_i local.a1 a2 a4 a6 d0 by blast 
        qed
       }
moreover{
       assume a1:"i\<le> NC" 
        have "\<exists>r'. ?P1 r' \<and> ?P2 r'"
        proof(rule_tac x="(n_SendGntE3 NC i)" in exI,rule conjI)
          show  "?P1 (n_SendGntE3 NC i) " 
           by(cut_tac a1, auto) 
          next
          show  "?P2 (n_SendGntE3 NC i) "
           using lemmaOnn_SendGntE3LeNc_ local.a1 a2 a4 a6 d0 by blast 
        qed
       }
  ultimately show "\<exists>r'.?P1 r' \<and> ?P2 r'" 
    by satx
qed

lemma lemmaOnn_SendGntS4Gt_i:
  assumes a1:"i>NC" and 
  a2:"s \<in> reachableSet (set (allInitSpecs N)) (rules N)"  and a3:"NC\<le>N" and  
  a4:"\<forall>f.  f \<in>(set invariantsAbs) \<longrightarrow>  formEval f s" 
  shows "trans_sim_on3 (n_SendGntS4  i)  (n_SendGntS4_i_3 )  VF VF' NC s" (is "trans_sim_on3 ?r ?r' VF VF' NC s")
  proof(rule ruleSimCond3)
    show " formEval (pre ?r) s \<longrightarrow>formEval (pre ?r') s" (is "?A \<longrightarrow>?B")
    proof(rule impI)+
      assume b0:"?A"
  have tmp:"formEval (inv_inv__1099 0)  s"   
            by(rule usThm1, simp del:inv_inv__1099_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__1099 0  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c0:"formEval  (conclude (inv_inv__1099 0)) s" by auto
have tmp:"formEval (inv_inv__1099 0)  s"   
            by(rule usThm1, simp del:inv_inv__1099_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__1099 1  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c1:"formEval  (conclude (inv_inv__1099 1)) s" by auto
have tmp:"formEval (inv_inv__1099 0)  s"   
            by(rule usThm1, simp del:inv_inv__1099_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__1099 i  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c2:"formEval  (conclude (inv_inv__1099 i)) s" by auto
have tmp:"formEval (inv_inv__1099 0)  s"   
            by(rule usThm1, simp del:inv_inv__1099_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__1099 3  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c3:"formEval  (conclude (inv_inv__1099 3)) s" by auto
have tmp:"formEval (inv_inv__3114 0)  s"   
            by(rule usThm1, simp del:inv_inv__3114_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__3114 0  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c4:"formEval  (conclude (inv_inv__3114 0)) s" by auto
have tmp:"formEval (inv_inv__3114 0)  s"   
            by(rule usThm1, simp del:inv_inv__3114_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__3114 1  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c5:"formEval  (conclude (inv_inv__3114 1)) s" by auto
have tmp:"formEval (inv_inv__3114 0)  s"   
            by(rule usThm1, simp del:inv_inv__3114_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__3114 i  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c6:"formEval  (conclude (inv_inv__3114 i)) s" by auto
have tmp:"formEval (inv_inv__3114 0)  s"   
            by(rule usThm1, simp del:inv_inv__3114_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__3114 3  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c7:"formEval  (conclude (inv_inv__3114 3)) s" by auto
have tmp:"formEval (inv_inv__1118)  s"  
        		by(rule usThm1, simp del:inv_inv__1118_def,cut_tac a4,assumption )
        	 with b0 a1 have c8:"formEval  (conclude (inv_inv__1118)) s" by auto
have tmp:"formEval (inv_inv__4422 0)  s"   
            by(rule usThm1, simp del:inv_inv__4422_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__4422 0  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c9:"formEval  (conclude (inv_inv__4422 0)) s" by auto
have tmp:"formEval (inv_inv__4422 0)  s"   
            by(rule usThm1, simp del:inv_inv__4422_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__4422 1  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c10:"formEval  (conclude (inv_inv__4422 1)) s" by auto
have tmp:"formEval (inv_inv__4422 0)  s"   
            by(rule usThm1, simp del:inv_inv__4422_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__4422 i  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c11:"formEval  (conclude (inv_inv__4422 i)) s" by auto
have tmp:"formEval (inv_inv__4422 0)  s"   
            by(rule usThm1, simp del:inv_inv__4422_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__4422 3  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c12:"formEval  (conclude (inv_inv__4422 3)) s" by auto
have tmp:"formEval (inv_inv__4227 0)  s"   
            by(rule usThm1, simp del:inv_inv__4227_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__4227 0  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c13:"formEval  (conclude (inv_inv__4227 0)) s" by auto
have tmp:"formEval (inv_inv__4227 0)  s"   
            by(rule usThm1, simp del:inv_inv__4227_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__4227 1  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c14:"formEval  (conclude (inv_inv__4227 1)) s" by auto
have tmp:"formEval (inv_inv__4227 0)  s"   
            by(rule usThm1, simp del:inv_inv__4227_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__4227 i  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c15:"formEval  (conclude (inv_inv__4227 i)) s" by auto
have tmp:"formEval (inv_inv__4227 0)  s"   
            by(rule usThm1, simp del:inv_inv__4227_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__4227 3  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c16:"formEval  (conclude (inv_inv__4227 3)) s" by auto

      from a1 a3 b0 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 show "formEval (pre ?r') s" 
       by (auto simp del:evalEqn)
     qed
   next 
	show "(\<forall>  v. v \<in>  varOfSent (act  ?r')   \<longrightarrow> formEval (pre ?r) s \<longrightarrow> 
    expEval (substExpByStatement (IVar v)  (act ?r')) s = expEval (substExpByStatement (IVar v)  (act ?r)) s)"
   proof(rule allI,(rule impI)+)
      fix  v
     assume b1:"v \<in>varOfSent (act ?r')"  and b2:"formEval (pre ?r) s" 
  
  show "expEval (substExpByStatement (IVar v)  (act ?r')) s = expEval (substExpByStatement (IVar v)  (act ?r)) s"  
       apply (cut_tac  a1 a3 b1 b2 ,auto ) done
   qed
  next
   show "\<forall>  v. v \<in>  varOfSent (act ?r) \<longrightarrow>  v \<in> VF \<longrightarrow> v \<in>  varOfSent (act ?r')" 
		by(cut_tac a1 a3, auto)
 next
   from a1 show "\<forall>v. v \<in> varOfForm (pre (?r')) \<longrightarrow>
     formEval (pre (?r)) s \<longrightarrow> v \<in> VF  \<or> v \<in> VF' \<and> scalar2Nat (s v) \<le> NC" 
		by(cut_tac a1 a3, auto)
  
next 
  show "\<forall>v. v \<in> varOfSent (act ?r)\<longrightarrow>       
    v \<in> VF'\<longrightarrow> formEval (pre (?r)) s  \<longrightarrow> scalar2Nat (expEval (substExpByStatement (IVar v) (act ?r)) s) 
\<le> NC  \<longrightarrow> v \<in> varOfSent (act ?r')"
    	by(cut_tac a1 a3, auto)
next
  show "\<forall> v va. v \<in> varOfSent (act ?r') \<longrightarrow> 
  va\<in>varOfExp ( substExpByStatement (IVar v)  (act ?r')) \<longrightarrow>
   va \<in> VF \<or> (va \<in> VF' \<and> (scalar2Nat (s va))\<le> NC)  "
     apply(cut_tac a1 a3, auto) done
  
qed
lemma lemmaOnn_SendGntS4LeNc_:
  assumes a1:"i\<le>NC"  and a3:"NC\<le>N" 
  shows "trans_sim_on3 (n_SendGntS4  i) (n_SendGntS4  i) VF VF' NC s" (is "trans_sim_on3 ?r ?r' VF VF' NC  s")
proof(rule ruleSimCond3)
     from a3 show " formEval (pre ?r) s \<longrightarrow>formEval (pre ?r') s" (is "?A \<longrightarrow>?B")  
       apply (auto simp del:evalEqn)done
   next 
	show "(\<forall>  v. v \<in>  varOfSent (act  ?r')  \<longrightarrow> formEval (pre ?r) s \<longrightarrow> 
    expEval (substExpByStatement (IVar v)  (act ?r')) s = expEval (substExpByStatement (IVar v)  (act ?r)) s)"
   proof(rule allI,(rule impI)+)
      fix  v
      assume b1:"formEval (pre ?r) s" and b2:"v \<in>varOfSent (act ?r')"
  
  show "expEval (substExpByStatement (IVar v)  (act ?r')) s = expEval (substExpByStatement (IVar v)  (act ?r)) s"  
       apply (cut_tac  a1 a3 b1 b2 ,auto) done
   qed
 next
   show "\<forall>  v. v \<in>  varOfSent (act ?r) \<longrightarrow>  v \<in> VF \<longrightarrow> v \<in>  varOfSent (act ?r')" 
		by(cut_tac a1 a3, auto)
 next
   from a1 show "\<forall>v. v \<in> varOfForm (pre (?r')) \<longrightarrow>
     formEval (pre (?r)) s  \<longrightarrow>
 v \<in> VF  \<or> v \<in> VF' \<and> scalar2Nat (s v) \<le> NC" 
		apply(cut_tac a1 a3, auto) done
  
next 
  show "\<forall>v. v \<in> varOfSent (act ?r)\<longrightarrow>
        v \<in> VF'\<longrightarrow>         
        formEval (pre (?r)) s \<longrightarrow>
       scalar2Nat (expEval (substExpByStatement (IVar v) (act ?r)) s) \<le> NC
       \<longrightarrow> v \<in> varOfSent (act ?r')"
    	apply(cut_tac a1 a3, auto) done
next
  show "\<forall> v va. v \<in> varOfSent (act ?r') \<longrightarrow> 
  va\<in>varOfExp ( substExpByStatement (IVar v)  (act ?r')) \<longrightarrow>
   va \<in> VF \<or> (va \<in> VF' \<and> (scalar2Nat (s va))\<le> NC)  "
     apply(cut_tac a1 a3, auto) done
qed
lemma lemmaOnn_SendGntS4: 
  assumes   a2:"s \<in> reachableSet (set (allInitSpecs N)) (rules N)"  and  
  a4:"\<forall>f.  f \<in>(set invariantsAbs) \<longrightarrow>  formEval f s" and a5:"\<exists> i. i\<le>N\<and>r=n_SendGntS4  i"  and
  a6:"NC \<le> N"
  shows "\<exists> r'. r' \<in> rules NC\<and> trans_sim_on3 r r' VF VF' NC s" (is "\<exists>r'.?P1 r' \<and> ?P2 r'")
proof -
  from a5 obtain i where d0:"i\<le>N\<and>r=n_SendGntS4  i"  by blast
  have "i>NC|i\<le> NC" by auto
  moreover{
       assume a1:"i>NC" 
        have "\<exists>r'. ?P1 r' \<and> ?P2 r'"
        proof(rule_tac x="(n_SendGntS4_i_3 )" in exI,rule conjI)
          show  "?P1 (n_SendGntS4_i_3 ) " 
           by(cut_tac a1, auto) 
          next
          show  "?P2 (n_SendGntS4_i_3 ) "
           using lemmaOnn_SendGntS4Gt_i local.a1 a2 a4 a6 d0 by blast 
        qed
       }
moreover{
       assume a1:"i\<le> NC" 
        have "\<exists>r'. ?P1 r' \<and> ?P2 r'"
        proof(rule_tac x="(n_SendGntS4  i)" in exI,rule conjI)
          show  "?P1 (n_SendGntS4  i) " 
           by(cut_tac a1, auto) 
          next
          show  "?P2 (n_SendGntS4  i) "
           using lemmaOnn_SendGntS4LeNc_ local.a1 a2 a4 a6 d0 by blast 
        qed
       }
  ultimately show "\<exists>r'.?P1 r' \<and> ?P2 r'" 
    by satx
qed

lemma lemmaOnn_RecvInvAck5Gt_i:
  assumes a1:"i>NC" and 
  a2:"s \<in> reachableSet (set (allInitSpecs N)) (rules N)"  and a3:"NC\<le>N" and  
  a4:"\<forall>f.  f \<in>(set invariantsAbs) \<longrightarrow>  formEval f s" 
  shows "trans_sim_on3 (n_RecvInvAck5  i)  (n_RecvInvAck5_i_3 )  VF VF' NC s" (is "trans_sim_on3 ?r ?r' VF VF' NC s")
  proof(rule ruleSimCond3)
    show " formEval (pre ?r) s \<longrightarrow>formEval (pre ?r') s" (is "?A \<longrightarrow>?B")
    proof(rule impI)+
      assume b0:"?A"
  have tmp:"formEval (inv_inv__3052 0)  s"   
            by(rule usThm1, simp del:inv_inv__3052_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__3052 0  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c0:"formEval  (conclude (inv_inv__3052 0)) s" by auto
have tmp:"formEval (inv_inv__3052 0)  s"   
            by(rule usThm1, simp del:inv_inv__3052_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__3052 1  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c1:"formEval  (conclude (inv_inv__3052 1)) s" by auto
have tmp:"formEval (inv_inv__3052 0)  s"   
            by(rule usThm1, simp del:inv_inv__3052_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__3052 3  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c2:"formEval  (conclude (inv_inv__3052 3)) s" by auto
have tmp:"formEval (inv_inv__1293 0)  s"   
            by(rule usThm1, simp del:inv_inv__1293_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__1293 0  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c3:"formEval  (conclude (inv_inv__1293 0)) s" by auto
have tmp:"formEval (inv_inv__1293 0)  s"   
            by(rule usThm1, simp del:inv_inv__1293_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__1293 1  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c4:"formEval  (conclude (inv_inv__1293 1)) s" by auto
have tmp:"formEval (inv_inv__1293 0)  s"   
            by(rule usThm1, simp del:inv_inv__1293_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__1293 3  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c5:"formEval  (conclude (inv_inv__1293 3)) s" by auto
have tmp:"formEval (inv_inv__2271 0)  s"   
            by(rule usThm1, simp del:inv_inv__2271_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__2271 0  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c6:"formEval  (conclude (inv_inv__2271 0)) s" by auto
have tmp:"formEval (inv_inv__2271 0)  s"   
            by(rule usThm1, simp del:inv_inv__2271_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__2271 1  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c7:"formEval  (conclude (inv_inv__2271 1)) s" by auto
have tmp:"formEval (inv_inv__2271 0)  s"   
            by(rule usThm1, simp del:inv_inv__2271_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__2271 3  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c8:"formEval  (conclude (inv_inv__2271 3)) s" by auto
have tmp:"formEval (inv_inv__3346 0)  s"   
            by(rule usThm1, simp del:inv_inv__3346_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__3346 0  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c9:"formEval  (conclude (inv_inv__3346 0)) s" by auto
have tmp:"formEval (inv_inv__3346 0)  s"   
            by(rule usThm1, simp del:inv_inv__3346_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__3346 1  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c10:"formEval  (conclude (inv_inv__3346 1)) s" by auto
have tmp:"formEval (inv_inv__3346 0)  s"   
            by(rule usThm1, simp del:inv_inv__3346_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__3346 3  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c11:"formEval  (conclude (inv_inv__3346 3)) s" by auto
have tmp:"formEval (inv_inv__3543 0)  s"   
            by(rule usThm1, simp del:inv_inv__3543_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__3543 0  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c12:"formEval  (conclude (inv_inv__3543 0)) s" by auto
have tmp:"formEval (inv_inv__3543 0)  s"   
            by(rule usThm1, simp del:inv_inv__3543_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__3543 1  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c13:"formEval  (conclude (inv_inv__3543 1)) s" by auto
have tmp:"formEval (inv_inv__3543 0)  s"   
            by(rule usThm1, simp del:inv_inv__3543_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__3543 3  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c14:"formEval  (conclude (inv_inv__3543 3)) s" by auto
have tmp:"formEval (inv_inv__2467 0)  s"   
            by(rule usThm1, simp del:inv_inv__2467_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__2467 0  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c15:"formEval  (conclude (inv_inv__2467 0)) s" by auto
have tmp:"formEval (inv_inv__2467 0)  s"   
            by(rule usThm1, simp del:inv_inv__2467_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__2467 1  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c16:"formEval  (conclude (inv_inv__2467 1)) s" by auto
have tmp:"formEval (inv_inv__2467 0)  s"   
            by(rule usThm1, simp del:inv_inv__2467_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__2467 3  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c17:"formEval  (conclude (inv_inv__2467 3)) s" by auto
have tmp:"formEval (inv_inv__4130 0 1)  s"   
            by(rule usThm1, simp del:inv_inv__4130_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__4130 i 0  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf2,force+)qed
        with b0 a1 have c18:"formEval  (conclude (inv_inv__4130 i 0)) s" by auto
have tmp:"formEval (inv_inv__4130 0 1)  s"   
            by(rule usThm1, simp del:inv_inv__4130_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__4130 i 1  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf2,force+)qed
        with b0 a1 have c19:"formEval  (conclude (inv_inv__4130 i 1)) s" by auto
have tmp:"formEval (inv_inv__4130 0 1)  s"   
            by(rule usThm1, simp del:inv_inv__4130_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__4130 i 3  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf2,force+)qed
        with b0 a1 have c20:"formEval  (conclude (inv_inv__4130 i 3)) s" by auto
have tmp:"formEval (inv_inv__3738 0 1)  s"   
            by(rule usThm1, simp del:inv_inv__3738_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__3738 i 0  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf2,force+)qed
        with b0 a1 have c21:"formEval  (conclude (inv_inv__3738 i 0)) s" by auto
have tmp:"formEval (inv_inv__3738 0 1)  s"   
            by(rule usThm1, simp del:inv_inv__3738_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__3738 i 1  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf2,force+)qed
        with b0 a1 have c22:"formEval  (conclude (inv_inv__3738 i 1)) s" by auto
have tmp:"formEval (inv_inv__3738 0 1)  s"   
            by(rule usThm1, simp del:inv_inv__3738_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__3738 i 3  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf2,force+)qed
        with b0 a1 have c23:"formEval  (conclude (inv_inv__3738 i 3)) s" by auto
have tmp:"formEval (inv_inv__513 0 1)  s"   
            by(rule usThm1, simp del:inv_inv__513_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__513 i 0  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf2,force+)qed
        with b0 a1 have c24:"formEval  (conclude (inv_inv__513 i 0)) s" by auto
have tmp:"formEval (inv_inv__513 0 1)  s"   
            by(rule usThm1, simp del:inv_inv__513_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__513 i 1  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf2,force+)qed
        with b0 a1 have c25:"formEval  (conclude (inv_inv__513 i 1)) s" by auto
have tmp:"formEval (inv_inv__513 0 1)  s"   
            by(rule usThm1, simp del:inv_inv__513_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__513 i 3  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf2,force+)qed
        with b0 a1 have c26:"formEval  (conclude (inv_inv__513 i 3)) s" by auto
have tmp:"formEval (inv_inv__511 0 1)  s"   
            by(rule usThm1, simp del:inv_inv__511_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__511 0 i  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf2,force+)qed
        with b0 a1 have c27:"formEval  (conclude (inv_inv__511 0 i)) s" by auto
have tmp:"formEval (inv_inv__511 0 1)  s"   
            by(rule usThm1, simp del:inv_inv__511_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__511 1 i  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf2,force+)qed
        with b0 a1 have c28:"formEval  (conclude (inv_inv__511 1 i)) s" by auto
have tmp:"formEval (inv_inv__511 0 1)  s"   
            by(rule usThm1, simp del:inv_inv__511_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__511 3 i  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf2,force+)qed
        with b0 a1 have c29:"formEval  (conclude (inv_inv__511 3 i)) s" by auto
have tmp:"formEval (inv_inv__1197 0)  s"   
            by(rule usThm1, simp del:inv_inv__1197_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__1197 0  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c30:"formEval  (conclude (inv_inv__1197 0)) s" by auto
have tmp:"formEval (inv_inv__1197 0)  s"   
            by(rule usThm1, simp del:inv_inv__1197_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__1197 1  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c31:"formEval  (conclude (inv_inv__1197 1)) s" by auto
have tmp:"formEval (inv_inv__1197 0)  s"   
            by(rule usThm1, simp del:inv_inv__1197_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__1197 i  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c32:"formEval  (conclude (inv_inv__1197 i)) s" by auto
have tmp:"formEval (inv_inv__1197 0)  s"   
            by(rule usThm1, simp del:inv_inv__1197_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__1197 3  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c33:"formEval  (conclude (inv_inv__1197 3)) s" by auto
have tmp:"formEval (inv_inv__3151 0)  s"   
            by(rule usThm1, simp del:inv_inv__3151_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__3151 0  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c34:"formEval  (conclude (inv_inv__3151 0)) s" by auto
have tmp:"formEval (inv_inv__3151 0)  s"   
            by(rule usThm1, simp del:inv_inv__3151_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__3151 1  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c35:"formEval  (conclude (inv_inv__3151 1)) s" by auto
have tmp:"formEval (inv_inv__3151 0)  s"   
            by(rule usThm1, simp del:inv_inv__3151_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__3151 i  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c36:"formEval  (conclude (inv_inv__3151 i)) s" by auto
have tmp:"formEval (inv_inv__3151 0)  s"   
            by(rule usThm1, simp del:inv_inv__3151_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__3151 3  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c37:"formEval  (conclude (inv_inv__3151 3)) s" by auto
have tmp:"formEval (inv_inv__4110 0)  s"   
            by(rule usThm1, simp del:inv_inv__4110_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__4110 i  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c38:"formEval  (conclude (inv_inv__4110 i)) s" by auto
have tmp:"formEval (inv_inv__1294 0)  s"   
            by(rule usThm1, simp del:inv_inv__1294_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__1294 i  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c39:"formEval  (conclude (inv_inv__1294 i)) s" by auto
have tmp:"formEval (inv_inv__3934 0)  s"   
            by(rule usThm1, simp del:inv_inv__3934_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__3934 i  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c40:"formEval  (conclude (inv_inv__3934 i)) s" by auto
have tmp:"formEval (inv_inv__4326 0)  s"   
            by(rule usThm1, simp del:inv_inv__4326_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__4326 i  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c41:"formEval  (conclude (inv_inv__4326 i)) s" by auto
have tmp:"formEval (inv_inv__3248 0)  s"   
            by(rule usThm1, simp del:inv_inv__3248_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__3248 i  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c42:"formEval  (conclude (inv_inv__3248 i)) s" by auto
have tmp:"formEval (inv_inv__4032 0)  s"   
            by(rule usThm1, simp del:inv_inv__4032_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__4032 i  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c43:"formEval  (conclude (inv_inv__4032 i)) s" by auto
have tmp:"formEval (inv_inv__1881 0)  s"   
            by(rule usThm1, simp del:inv_inv__1881_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__1881 i  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c44:"formEval  (conclude (inv_inv__1881 i)) s" by auto
have tmp:"formEval (inv_inv__1979 0 1)  s"   
            by(rule usThm1, simp del:inv_inv__1979_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__1979 0 i  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf2,force+)qed
        with b0 a1 have c45:"formEval  (conclude (inv_inv__1979 0 i)) s" by auto
have tmp:"formEval (inv_inv__1979 0 1)  s"   
            by(rule usThm1, simp del:inv_inv__1979_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__1979 1 i  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf2,force+)qed
        with b0 a1 have c46:"formEval  (conclude (inv_inv__1979 1 i)) s" by auto
have tmp:"formEval (inv_inv__1979 0 1)  s"   
            by(rule usThm1, simp del:inv_inv__1979_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__1979 3 i  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf2,force+)qed
        with b0 a1 have c47:"formEval  (conclude (inv_inv__1979 3 i)) s" by auto
have tmp:"formEval (inv_inv__8102 0)  s"   
            by(rule usThm1, simp del:inv_inv__8102_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__8102 i  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c48:"formEval  (conclude (inv_inv__8102 i)) s" by auto
have tmp:"formEval (inv_inv__9100 0 1)  s"   
            by(rule usThm1, simp del:inv_inv__9100_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__9100 0 i  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf2,force+)qed
        with b0 a1 have c49:"formEval  (conclude (inv_inv__9100 0 i)) s" by auto
have tmp:"formEval (inv_inv__9100 0 1)  s"   
            by(rule usThm1, simp del:inv_inv__9100_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__9100 1 i  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf2,force+)qed
        with b0 a1 have c50:"formEval  (conclude (inv_inv__9100 1 i)) s" by auto
have tmp:"formEval (inv_inv__9100 0 1)  s"   
            by(rule usThm1, simp del:inv_inv__9100_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__9100 3 i  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf2,force+)qed
        with b0 a1 have c51:"formEval  (conclude (inv_inv__9100 3 i)) s" by auto
have tmp:"formEval (inv_inv__3444 0)  s"   
            by(rule usThm1, simp del:inv_inv__3444_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__3444 i  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c52:"formEval  (conclude (inv_inv__3444 i)) s" by auto

      from a1 a3 b0 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 c29 c30 c31 c32 c33 c34 c35 c36 c37 c38 c39 c40 c41 c42 c43 c44 c45 c46 c47 c48 c49 c50 c51 c52 show "formEval (pre ?r') s" 
       by (auto simp del:evalEqn)
     qed
   next 
	show "(\<forall>  v. v \<in>  varOfSent (act  ?r')   \<longrightarrow> formEval (pre ?r) s \<longrightarrow> 
    expEval (substExpByStatement (IVar v)  (act ?r')) s = expEval (substExpByStatement (IVar v)  (act ?r)) s)"
   proof(rule allI,(rule impI)+)
      fix  v
     assume b1:"v \<in>varOfSent (act ?r')"  and b2:"formEval (pre ?r) s" 
  
  show "expEval (substExpByStatement (IVar v)  (act ?r')) s = expEval (substExpByStatement (IVar v)  (act ?r)) s"  
       apply (cut_tac  a1 a3 b1 b2 ,auto ) done
   qed
  next
   show "\<forall>  v. v \<in>  varOfSent (act ?r) \<longrightarrow>  v \<in> VF \<longrightarrow> v \<in>  varOfSent (act ?r')" 
		by(cut_tac a1 a3, auto)
 next
   from a1 show "\<forall>v. v \<in> varOfForm (pre (?r')) \<longrightarrow>
     formEval (pre (?r)) s \<longrightarrow> v \<in> VF  \<or> v \<in> VF' \<and> scalar2Nat (s v) \<le> NC" 
		by(cut_tac a1 a3, auto)
  
next 
  show "\<forall>v. v \<in> varOfSent (act ?r)\<longrightarrow>       
    v \<in> VF'\<longrightarrow> formEval (pre (?r)) s  \<longrightarrow> scalar2Nat (expEval (substExpByStatement (IVar v) (act ?r)) s) 
\<le> NC  \<longrightarrow> v \<in> varOfSent (act ?r')"
    	by(cut_tac a1 a3, auto)
next
  show "\<forall> v va. v \<in> varOfSent (act ?r') \<longrightarrow> 
  va\<in>varOfExp ( substExpByStatement (IVar v)  (act ?r')) \<longrightarrow>
   va \<in> VF \<or> (va \<in> VF' \<and> (scalar2Nat (s va))\<le> NC)  "
     apply(cut_tac a1 a3, auto) done
  
qed
lemma lemmaOnn_RecvInvAck5LeNc_:
  assumes a1:"i\<le>NC"  and a3:"NC\<le>N" 
  shows "trans_sim_on3 (n_RecvInvAck5  i) (n_RecvInvAck5  i) VF VF' NC s" (is "trans_sim_on3 ?r ?r' VF VF' NC  s")
proof(rule ruleSimCond3)
     from a3 show " formEval (pre ?r) s \<longrightarrow>formEval (pre ?r') s" (is "?A \<longrightarrow>?B")  
       apply (auto simp del:evalEqn)done
   next 
	show "(\<forall>  v. v \<in>  varOfSent (act  ?r')  \<longrightarrow> formEval (pre ?r) s \<longrightarrow> 
    expEval (substExpByStatement (IVar v)  (act ?r')) s = expEval (substExpByStatement (IVar v)  (act ?r)) s)"
   proof(rule allI,(rule impI)+)
      fix  v
      assume b1:"formEval (pre ?r) s" and b2:"v \<in>varOfSent (act ?r')"
  
  show "expEval (substExpByStatement (IVar v)  (act ?r')) s = expEval (substExpByStatement (IVar v)  (act ?r)) s"  
       apply (cut_tac  a1 a3 b1 b2 ,auto) done
   qed
 next
   show "\<forall>  v. v \<in>  varOfSent (act ?r) \<longrightarrow>  v \<in> VF \<longrightarrow> v \<in>  varOfSent (act ?r')" 
		by(cut_tac a1 a3, auto)
 next
   from a1 show "\<forall>v. v \<in> varOfForm (pre (?r')) \<longrightarrow>
     formEval (pre (?r)) s  \<longrightarrow>
 v \<in> VF  \<or> v \<in> VF' \<and> scalar2Nat (s v) \<le> NC" 
		apply(cut_tac a1 a3, auto) done
  
next 
  show "\<forall>v. v \<in> varOfSent (act ?r)\<longrightarrow>
        v \<in> VF'\<longrightarrow>         
        formEval (pre (?r)) s \<longrightarrow>
       scalar2Nat (expEval (substExpByStatement (IVar v) (act ?r)) s) \<le> NC
       \<longrightarrow> v \<in> varOfSent (act ?r')"
    	apply(cut_tac a1 a3, auto) done
next
  show "\<forall> v va. v \<in> varOfSent (act ?r') \<longrightarrow> 
  va\<in>varOfExp ( substExpByStatement (IVar v)  (act ?r')) \<longrightarrow>
   va \<in> VF \<or> (va \<in> VF' \<and> (scalar2Nat (s va))\<le> NC)  "
     apply(cut_tac a1 a3, auto) done
qed
lemma lemmaOnn_RecvInvAck5: 
  assumes   a2:"s \<in> reachableSet (set (allInitSpecs N)) (rules N)"  and  
  a4:"\<forall>f.  f \<in>(set invariantsAbs) \<longrightarrow>  formEval f s" and a5:"\<exists> i. i\<le>N\<and>r=n_RecvInvAck5  i"  and
  a6:"NC \<le> N"
  shows "\<exists> r'. r' \<in> rules NC\<and> trans_sim_on3 r r' VF VF' NC s" (is "\<exists>r'.?P1 r' \<and> ?P2 r'")
proof -
  from a5 obtain i where d0:"i\<le>N\<and>r=n_RecvInvAck5  i"  by blast
  have "i>NC|i\<le> NC" by auto
  moreover{
       assume a1:"i>NC" 
        have "\<exists>r'. ?P1 r' \<and> ?P2 r'"
        proof(rule_tac x="(n_RecvInvAck5_i_3 )" in exI,rule conjI)
          show  "?P1 (n_RecvInvAck5_i_3 ) " 
           by(cut_tac a1, auto) 
          next
          show  "?P2 (n_RecvInvAck5_i_3 ) "
           using lemmaOnn_RecvInvAck5Gt_i local.a1 a2 a4 a6 d0 by blast 
        qed
       }
moreover{
       assume a1:"i\<le> NC" 
        have "\<exists>r'. ?P1 r' \<and> ?P2 r'"
        proof(rule_tac x="(n_RecvInvAck5  i)" in exI,rule conjI)
          show  "?P1 (n_RecvInvAck5  i) " 
           by(cut_tac a1, auto) 
          next
          show  "?P2 (n_RecvInvAck5  i) "
           using lemmaOnn_RecvInvAck5LeNc_ local.a1 a2 a4 a6 d0 by blast 
        qed
       }
  ultimately show "\<exists>r'.?P1 r' \<and> ?P2 r'" 
    by satx
qed

lemma lemmaOnn_RecvInvAck6Gt_i:
  assumes a1:"NC<i" and a2:"s \<in> reachableSet (set (allInitSpecs N)) (rules N)"  and  
  a4:"\<forall>f.  f \<in>(set invariantsAbs) \<longrightarrow>  formEval f s" 
shows "trans_sim_on3 (n_RecvInvAck6  i  ) skipRule VF  VF' NC s" (is "trans_sim_on3 ?r ?r' VF VF' NC s")
proof(unfold trans_sim_on3_def,(rule allI)+,(rule impI)+,rule disjI2)
  fix s2 
  assume b0:"state_sim_on3 s s2 VF VF' NC "
  show "state_sim_on3 (trans (act (?r)) s) s2 VF VF' NC"
  proof(cut_tac a1,unfold state_sim_on3_def,rule conjI)
    show "\<forall>v. v \<in> VF \<longrightarrow> trans (act ?r) s v = s2 v"
    proof(rule allI,rule impI)
    fix f v
    assume b1:" v \<in>  VF"  
    
    have b5:"trans (act (?r)) s v = s v" 
      by (cut_tac a1  b1,auto) 

    have b6:"s v =s2 v "
      using b0 b1 state_sim_on3_def by blast  
    show "trans (act (?r)) s v= s2 v"
      using b5 b6 by auto 
  qed
next
  show "\<forall>v. v \<in> VF' \<longrightarrow> scalar2Nat (trans (act ?r) s v) \<le> NC \<longrightarrow> trans (act ?r) s v = s2 v" 
    by(cut_tac b0, auto)
  
qed
qed
lemma lemmaOnn_RecvInvAck6LeNc_:
  assumes a1:"i\<le>NC"  and a3:"NC\<le>N" 
  shows "trans_sim_on3 (n_RecvInvAck6  i) (n_RecvInvAck6  i) VF VF' NC s" (is "trans_sim_on3 ?r ?r' VF VF' NC  s")
proof(rule ruleSimCond3)
     from a3 show " formEval (pre ?r) s \<longrightarrow>formEval (pre ?r') s" (is "?A \<longrightarrow>?B")  
       apply (auto simp del:evalEqn)done
   next 
	show "(\<forall>  v. v \<in>  varOfSent (act  ?r')  \<longrightarrow> formEval (pre ?r) s \<longrightarrow> 
    expEval (substExpByStatement (IVar v)  (act ?r')) s = expEval (substExpByStatement (IVar v)  (act ?r)) s)"
   proof(rule allI,(rule impI)+)
      fix  v
      assume b1:"formEval (pre ?r) s" and b2:"v \<in>varOfSent (act ?r')"
  
  show "expEval (substExpByStatement (IVar v)  (act ?r')) s = expEval (substExpByStatement (IVar v)  (act ?r)) s"  
       apply (cut_tac  a1 a3 b1 b2 ,auto) done
   qed
 next
   show "\<forall>  v. v \<in>  varOfSent (act ?r) \<longrightarrow>  v \<in> VF \<longrightarrow> v \<in>  varOfSent (act ?r')" 
		by(cut_tac a1 a3, auto)
 next
   from a1 show "\<forall>v. v \<in> varOfForm (pre (?r')) \<longrightarrow>
     formEval (pre (?r)) s  \<longrightarrow>
 v \<in> VF  \<or> v \<in> VF' \<and> scalar2Nat (s v) \<le> NC" 
		apply(cut_tac a1 a3, auto) done
  
next 
  show "\<forall>v. v \<in> varOfSent (act ?r)\<longrightarrow>
        v \<in> VF'\<longrightarrow>         
        formEval (pre (?r)) s \<longrightarrow>
       scalar2Nat (expEval (substExpByStatement (IVar v) (act ?r)) s) \<le> NC
       \<longrightarrow> v \<in> varOfSent (act ?r')"
    	apply(cut_tac a1 a3, auto) done
next
  show "\<forall> v va. v \<in> varOfSent (act ?r') \<longrightarrow> 
  va\<in>varOfExp ( substExpByStatement (IVar v)  (act ?r')) \<longrightarrow>
   va \<in> VF \<or> (va \<in> VF' \<and> (scalar2Nat (s va))\<le> NC)  "
     apply(cut_tac a1 a3, auto) done
qed
lemma lemmaOnn_RecvInvAck6: 
  assumes   a2:"s \<in> reachableSet (set (allInitSpecs N)) (rules N)"  and  
  a4:"\<forall>f.  f \<in>(set invariantsAbs) \<longrightarrow>  formEval f s" and a5:"\<exists> i. i\<le>N\<and>r=n_RecvInvAck6  i"  and
  a6:"NC \<le> N"
  shows "\<exists> r'. r' \<in> rules NC\<and> trans_sim_on3 r r' VF VF' NC s" (is "\<exists>r'.?P1 r' \<and> ?P2 r'")
proof -
  from a5 obtain i where d0:"i\<le>N\<and>r=n_RecvInvAck6  i"  by blast
  have "i>NC|i\<le> NC" by auto
  moreover{
       assume a1:"i>NC" 
        have "\<exists>r'. ?P1 r' \<and> ?P2 r'"
        proof(rule_tac x="(skipRule)" in exI,rule conjI)
          show  "?P1 (skipRule) " 
           by(cut_tac a1, auto) 
          next
          show  "?P2 (skipRule) "
           using lemmaOnn_RecvInvAck6Gt_i local.a1 a2 a4 a6 d0 by blast 
        qed
       }
moreover{
       assume a1:"i\<le> NC" 
        have "\<exists>r'. ?P1 r' \<and> ?P2 r'"
        proof(rule_tac x="(n_RecvInvAck6  i)" in exI,rule conjI)
          show  "?P1 (n_RecvInvAck6  i) " 
           by(cut_tac a1, auto) 
          next
          show  "?P2 (n_RecvInvAck6  i) "
           using lemmaOnn_RecvInvAck6LeNc_ local.a1 a2 a4 a6 d0 by blast 
        qed
       }
  ultimately show "\<exists>r'.?P1 r' \<and> ?P2 r'" 
    by satx
qed

lemma lemmaOnn_SendInvAck7Gt_i:
  assumes a1:"NC<i" and a2:"s \<in> reachableSet (set (allInitSpecs N)) (rules N)"  and  
  a4:"\<forall>f.  f \<in>(set invariantsAbs) \<longrightarrow>  formEval f s" 
shows "trans_sim_on3 (n_SendInvAck7  i  ) skipRule VF  VF' NC s" (is "trans_sim_on3 ?r ?r' VF VF' NC s")
proof(unfold trans_sim_on3_def,(rule allI)+,(rule impI)+,rule disjI2)
  fix s2 
  assume b0:"state_sim_on3 s s2 VF VF' NC "
  show "state_sim_on3 (trans (act (?r)) s) s2 VF VF' NC"
  proof(cut_tac a1,unfold state_sim_on3_def,rule conjI)
    show "\<forall>v. v \<in> VF \<longrightarrow> trans (act ?r) s v = s2 v"
    proof(rule allI,rule impI)
    fix f v
    assume b1:" v \<in>  VF"  
    
    have b5:"trans (act (?r)) s v = s v" 
      by (cut_tac a1  b1,auto) 

    have b6:"s v =s2 v "
      using b0 b1 state_sim_on3_def by blast  
    show "trans (act (?r)) s v= s2 v"
      using b5 b6 by auto 
  qed
next
  show "\<forall>v. v \<in> VF' \<longrightarrow> scalar2Nat (trans (act ?r) s v) \<le> NC \<longrightarrow> trans (act ?r) s v = s2 v" 
    by(cut_tac b0, auto)
  
qed
qed
lemma lemmaOnn_SendInvAck7LeNc_:
  assumes a1:"i\<le>NC"  and a3:"NC\<le>N" 
  shows "trans_sim_on3 (n_SendInvAck7  i) (n_SendInvAck7  i) VF VF' NC s" (is "trans_sim_on3 ?r ?r' VF VF' NC  s")
proof(rule ruleSimCond3)
     from a3 show " formEval (pre ?r) s \<longrightarrow>formEval (pre ?r') s" (is "?A \<longrightarrow>?B")  
       apply (auto simp del:evalEqn)done
   next 
	show "(\<forall>  v. v \<in>  varOfSent (act  ?r')  \<longrightarrow> formEval (pre ?r) s \<longrightarrow> 
    expEval (substExpByStatement (IVar v)  (act ?r')) s = expEval (substExpByStatement (IVar v)  (act ?r)) s)"
   proof(rule allI,(rule impI)+)
      fix  v
      assume b1:"formEval (pre ?r) s" and b2:"v \<in>varOfSent (act ?r')"
  
  show "expEval (substExpByStatement (IVar v)  (act ?r')) s = expEval (substExpByStatement (IVar v)  (act ?r)) s"  
       apply (cut_tac  a1 a3 b1 b2 ,auto) done
   qed
 next
   show "\<forall>  v. v \<in>  varOfSent (act ?r) \<longrightarrow>  v \<in> VF \<longrightarrow> v \<in>  varOfSent (act ?r')" 
		by(cut_tac a1 a3, auto)
 next
   from a1 show "\<forall>v. v \<in> varOfForm (pre (?r')) \<longrightarrow>
     formEval (pre (?r)) s  \<longrightarrow>
 v \<in> VF  \<or> v \<in> VF' \<and> scalar2Nat (s v) \<le> NC" 
		apply(cut_tac a1 a3, auto) done
  
next 
  show "\<forall>v. v \<in> varOfSent (act ?r)\<longrightarrow>
        v \<in> VF'\<longrightarrow>         
        formEval (pre (?r)) s \<longrightarrow>
       scalar2Nat (expEval (substExpByStatement (IVar v) (act ?r)) s) \<le> NC
       \<longrightarrow> v \<in> varOfSent (act ?r')"
    	apply(cut_tac a1 a3, auto) done
next
  show "\<forall> v va. v \<in> varOfSent (act ?r') \<longrightarrow> 
  va\<in>varOfExp ( substExpByStatement (IVar v)  (act ?r')) \<longrightarrow>
   va \<in> VF \<or> (va \<in> VF' \<and> (scalar2Nat (s va))\<le> NC)  "
     apply(cut_tac a1 a3, auto) done
qed
lemma lemmaOnn_SendInvAck7: 
  assumes   a2:"s \<in> reachableSet (set (allInitSpecs N)) (rules N)"  and  
  a4:"\<forall>f.  f \<in>(set invariantsAbs) \<longrightarrow>  formEval f s" and a5:"\<exists> i. i\<le>N\<and>r=n_SendInvAck7  i"  and
  a6:"NC \<le> N"
  shows "\<exists> r'. r' \<in> rules NC\<and> trans_sim_on3 r r' VF VF' NC s" (is "\<exists>r'.?P1 r' \<and> ?P2 r'")
proof -
  from a5 obtain i where d0:"i\<le>N\<and>r=n_SendInvAck7  i"  by blast
  have "i>NC|i\<le> NC" by auto
  moreover{
       assume a1:"i>NC" 
        have "\<exists>r'. ?P1 r' \<and> ?P2 r'"
        proof(rule_tac x="(skipRule)" in exI,rule conjI)
          show  "?P1 (skipRule) " 
           by(cut_tac a1, auto) 
          next
          show  "?P2 (skipRule) "
           using lemmaOnn_SendInvAck7Gt_i local.a1 a2 a4 a6 d0 by blast 
        qed
       }
moreover{
       assume a1:"i\<le> NC" 
        have "\<exists>r'. ?P1 r' \<and> ?P2 r'"
        proof(rule_tac x="(n_SendInvAck7  i)" in exI,rule conjI)
          show  "?P1 (n_SendInvAck7  i) " 
           by(cut_tac a1, auto) 
          next
          show  "?P2 (n_SendInvAck7  i) "
           using lemmaOnn_SendInvAck7LeNc_ local.a1 a2 a4 a6 d0 by blast 
        qed
       }
  ultimately show "\<exists>r'.?P1 r' \<and> ?P2 r'" 
    by satx
qed

lemma lemmaOnn_SendInvAck8Gt_i:
  assumes a1:"NC<i" and a2:"s \<in> reachableSet (set (allInitSpecs N)) (rules N)"  and  
  a4:"\<forall>f.  f \<in>(set invariantsAbs) \<longrightarrow>  formEval f s" 
shows "trans_sim_on3 (n_SendInvAck8  i  ) skipRule VF  VF' NC s" (is "trans_sim_on3 ?r ?r' VF VF' NC s")
proof(unfold trans_sim_on3_def,(rule allI)+,(rule impI)+,rule disjI2)
  fix s2 
  assume b0:"state_sim_on3 s s2 VF VF' NC "
  show "state_sim_on3 (trans (act (?r)) s) s2 VF VF' NC"
  proof(cut_tac a1,unfold state_sim_on3_def,rule conjI)
    show "\<forall>v. v \<in> VF \<longrightarrow> trans (act ?r) s v = s2 v"
    proof(rule allI,rule impI)
    fix f v
    assume b1:" v \<in>  VF"  
    
    have b5:"trans (act (?r)) s v = s v" 
      by (cut_tac a1  b1,auto) 

    have b6:"s v =s2 v "
      using b0 b1 state_sim_on3_def by blast  
    show "trans (act (?r)) s v= s2 v"
      using b5 b6 by auto 
  qed
next
  show "\<forall>v. v \<in> VF' \<longrightarrow> scalar2Nat (trans (act ?r) s v) \<le> NC \<longrightarrow> trans (act ?r) s v = s2 v" 
    by(cut_tac b0, auto)
  
qed
qed
lemma lemmaOnn_SendInvAck8LeNc_:
  assumes a1:"i\<le>NC"  and a3:"NC\<le>N" 
  shows "trans_sim_on3 (n_SendInvAck8  i) (n_SendInvAck8  i) VF VF' NC s" (is "trans_sim_on3 ?r ?r' VF VF' NC  s")
proof(rule ruleSimCond3)
     from a3 show " formEval (pre ?r) s \<longrightarrow>formEval (pre ?r') s" (is "?A \<longrightarrow>?B")  
       apply (auto simp del:evalEqn)done
   next 
	show "(\<forall>  v. v \<in>  varOfSent (act  ?r')  \<longrightarrow> formEval (pre ?r) s \<longrightarrow> 
    expEval (substExpByStatement (IVar v)  (act ?r')) s = expEval (substExpByStatement (IVar v)  (act ?r)) s)"
   proof(rule allI,(rule impI)+)
      fix  v
      assume b1:"formEval (pre ?r) s" and b2:"v \<in>varOfSent (act ?r')"
  
  show "expEval (substExpByStatement (IVar v)  (act ?r')) s = expEval (substExpByStatement (IVar v)  (act ?r)) s"  
       apply (cut_tac  a1 a3 b1 b2 ,auto) done
   qed
 next
   show "\<forall>  v. v \<in>  varOfSent (act ?r) \<longrightarrow>  v \<in> VF \<longrightarrow> v \<in>  varOfSent (act ?r')" 
		by(cut_tac a1 a3, auto)
 next
   from a1 show "\<forall>v. v \<in> varOfForm (pre (?r')) \<longrightarrow>
     formEval (pre (?r)) s  \<longrightarrow>
 v \<in> VF  \<or> v \<in> VF' \<and> scalar2Nat (s v) \<le> NC" 
		apply(cut_tac a1 a3, auto) done
  
next 
  show "\<forall>v. v \<in> varOfSent (act ?r)\<longrightarrow>
        v \<in> VF'\<longrightarrow>         
        formEval (pre (?r)) s \<longrightarrow>
       scalar2Nat (expEval (substExpByStatement (IVar v) (act ?r)) s) \<le> NC
       \<longrightarrow> v \<in> varOfSent (act ?r')"
    	apply(cut_tac a1 a3, auto) done
next
  show "\<forall> v va. v \<in> varOfSent (act ?r') \<longrightarrow> 
  va\<in>varOfExp ( substExpByStatement (IVar v)  (act ?r')) \<longrightarrow>
   va \<in> VF \<or> (va \<in> VF' \<and> (scalar2Nat (s va))\<le> NC)  "
     apply(cut_tac a1 a3, auto) done
qed
lemma lemmaOnn_SendInvAck8: 
  assumes   a2:"s \<in> reachableSet (set (allInitSpecs N)) (rules N)"  and  
  a4:"\<forall>f.  f \<in>(set invariantsAbs) \<longrightarrow>  formEval f s" and a5:"\<exists> i. i\<le>N\<and>r=n_SendInvAck8  i"  and
  a6:"NC \<le> N"
  shows "\<exists> r'. r' \<in> rules NC\<and> trans_sim_on3 r r' VF VF' NC s" (is "\<exists>r'.?P1 r' \<and> ?P2 r'")
proof -
  from a5 obtain i where d0:"i\<le>N\<and>r=n_SendInvAck8  i"  by blast
  have "i>NC|i\<le> NC" by auto
  moreover{
       assume a1:"i>NC" 
        have "\<exists>r'. ?P1 r' \<and> ?P2 r'"
        proof(rule_tac x="(skipRule)" in exI,rule conjI)
          show  "?P1 (skipRule) " 
           by(cut_tac a1, auto) 
          next
          show  "?P2 (skipRule) "
           using lemmaOnn_SendInvAck8Gt_i local.a1 a2 a4 a6 d0 by blast 
        qed
       }
moreover{
       assume a1:"i\<le> NC" 
        have "\<exists>r'. ?P1 r' \<and> ?P2 r'"
        proof(rule_tac x="(n_SendInvAck8  i)" in exI,rule conjI)
          show  "?P1 (n_SendInvAck8  i) " 
           by(cut_tac a1, auto) 
          next
          show  "?P2 (n_SendInvAck8  i) "
           using lemmaOnn_SendInvAck8LeNc_ local.a1 a2 a4 a6 d0 by blast 
        qed
       }
  ultimately show "\<exists>r'.?P1 r' \<and> ?P2 r'" 
    by satx
qed

lemma lemmaOnn_SendInv9Gt_i:
  assumes a1:"NC<i" and a2:"s \<in> reachableSet (set (allInitSpecs N)) (rules N)"  and  
  a4:"\<forall>f.  f \<in>(set invariantsAbs) \<longrightarrow>  formEval f s" 
shows "trans_sim_on3 (n_SendInv9  i  ) skipRule VF  VF' NC s" (is "trans_sim_on3 ?r ?r' VF VF' NC s")
proof(unfold trans_sim_on3_def,(rule allI)+,(rule impI)+,rule disjI2)
  fix s2 
  assume b0:"state_sim_on3 s s2 VF VF' NC "
  show "state_sim_on3 (trans (act (?r)) s) s2 VF VF' NC"
  proof(cut_tac a1,unfold state_sim_on3_def,rule conjI)
    show "\<forall>v. v \<in> VF \<longrightarrow> trans (act ?r) s v = s2 v"
    proof(rule allI,rule impI)
    fix f v
    assume b1:" v \<in>  VF"  
    
    have b5:"trans (act (?r)) s v = s v" 
      by (cut_tac a1  b1,auto) 

    have b6:"s v =s2 v "
      using b0 b1 state_sim_on3_def by blast  
    show "trans (act (?r)) s v= s2 v"
      using b5 b6 by auto 
  qed
next
  show "\<forall>v. v \<in> VF' \<longrightarrow> scalar2Nat (trans (act ?r) s v) \<le> NC \<longrightarrow> trans (act ?r) s v = s2 v" 
    by(cut_tac b0, auto)
  
qed
qed
lemma lemmaOnn_SendInv9LeNc_:
  assumes a1:"i\<le>NC"  and a3:"NC\<le>N" 
  shows "trans_sim_on3 (n_SendInv9  i) (n_SendInv9  i) VF VF' NC s" (is "trans_sim_on3 ?r ?r' VF VF' NC  s")
proof(rule ruleSimCond3)
     from a3 show " formEval (pre ?r) s \<longrightarrow>formEval (pre ?r') s" (is "?A \<longrightarrow>?B")  
       apply (auto simp del:evalEqn)done
   next 
	show "(\<forall>  v. v \<in>  varOfSent (act  ?r')  \<longrightarrow> formEval (pre ?r) s \<longrightarrow> 
    expEval (substExpByStatement (IVar v)  (act ?r')) s = expEval (substExpByStatement (IVar v)  (act ?r)) s)"
   proof(rule allI,(rule impI)+)
      fix  v
      assume b1:"formEval (pre ?r) s" and b2:"v \<in>varOfSent (act ?r')"
  
  show "expEval (substExpByStatement (IVar v)  (act ?r')) s = expEval (substExpByStatement (IVar v)  (act ?r)) s"  
       apply (cut_tac  a1 a3 b1 b2 ,auto) done
   qed
 next
   show "\<forall>  v. v \<in>  varOfSent (act ?r) \<longrightarrow>  v \<in> VF \<longrightarrow> v \<in>  varOfSent (act ?r')" 
		by(cut_tac a1 a3, auto)
 next
   from a1 show "\<forall>v. v \<in> varOfForm (pre (?r')) \<longrightarrow>
     formEval (pre (?r)) s  \<longrightarrow>
 v \<in> VF  \<or> v \<in> VF' \<and> scalar2Nat (s v) \<le> NC" 
		apply(cut_tac a1 a3, auto) done
  
next 
  show "\<forall>v. v \<in> varOfSent (act ?r)\<longrightarrow>
        v \<in> VF'\<longrightarrow>         
        formEval (pre (?r)) s \<longrightarrow>
       scalar2Nat (expEval (substExpByStatement (IVar v) (act ?r)) s) \<le> NC
       \<longrightarrow> v \<in> varOfSent (act ?r')"
    	apply(cut_tac a1 a3, auto) done
next
  show "\<forall> v va. v \<in> varOfSent (act ?r') \<longrightarrow> 
  va\<in>varOfExp ( substExpByStatement (IVar v)  (act ?r')) \<longrightarrow>
   va \<in> VF \<or> (va \<in> VF' \<and> (scalar2Nat (s va))\<le> NC)  "
     apply(cut_tac a1 a3, auto) done
qed
lemma lemmaOnn_SendInv9: 
  assumes   a2:"s \<in> reachableSet (set (allInitSpecs N)) (rules N)"  and  
  a4:"\<forall>f.  f \<in>(set invariantsAbs) \<longrightarrow>  formEval f s" and a5:"\<exists> i. i\<le>N\<and>r=n_SendInv9  i"  and
  a6:"NC \<le> N"
  shows "\<exists> r'. r' \<in> rules NC\<and> trans_sim_on3 r r' VF VF' NC s" (is "\<exists>r'.?P1 r' \<and> ?P2 r'")
proof -
  from a5 obtain i where d0:"i\<le>N\<and>r=n_SendInv9  i"  by blast
  have "i>NC|i\<le> NC" by auto
  moreover{
       assume a1:"i>NC" 
        have "\<exists>r'. ?P1 r' \<and> ?P2 r'"
        proof(rule_tac x="(skipRule)" in exI,rule conjI)
          show  "?P1 (skipRule) " 
           by(cut_tac a1, auto) 
          next
          show  "?P2 (skipRule) "
           using lemmaOnn_SendInv9Gt_i local.a1 a2 a4 a6 d0 by blast 
        qed
       }
moreover{
       assume a1:"i\<le> NC" 
        have "\<exists>r'. ?P1 r' \<and> ?P2 r'"
        proof(rule_tac x="(n_SendInv9  i)" in exI,rule conjI)
          show  "?P1 (n_SendInv9  i) " 
           by(cut_tac a1, auto) 
          next
          show  "?P2 (n_SendInv9  i) "
           using lemmaOnn_SendInv9LeNc_ local.a1 a2 a4 a6 d0 by blast 
        qed
       }
  ultimately show "\<exists>r'.?P1 r' \<and> ?P2 r'" 
    by satx
qed

lemma lemmaOnn_SendInv10Gt_i:
  assumes a1:"NC<i" and a2:"s \<in> reachableSet (set (allInitSpecs N)) (rules N)"  and  
  a4:"\<forall>f.  f \<in>(set invariantsAbs) \<longrightarrow>  formEval f s" 
shows "trans_sim_on3 (n_SendInv10  i  ) skipRule VF  VF' NC s" (is "trans_sim_on3 ?r ?r' VF VF' NC s")
proof(unfold trans_sim_on3_def,(rule allI)+,(rule impI)+,rule disjI2)
  fix s2 
  assume b0:"state_sim_on3 s s2 VF VF' NC "
  show "state_sim_on3 (trans (act (?r)) s) s2 VF VF' NC"
  proof(cut_tac a1,unfold state_sim_on3_def,rule conjI)
    show "\<forall>v. v \<in> VF \<longrightarrow> trans (act ?r) s v = s2 v"
    proof(rule allI,rule impI)
    fix f v
    assume b1:" v \<in>  VF"  
    
    have b5:"trans (act (?r)) s v = s v" 
      by (cut_tac a1  b1,auto) 

    have b6:"s v =s2 v "
      using b0 b1 state_sim_on3_def by blast  
    show "trans (act (?r)) s v= s2 v"
      using b5 b6 by auto 
  qed
next
  show "\<forall>v. v \<in> VF' \<longrightarrow> scalar2Nat (trans (act ?r) s v) \<le> NC \<longrightarrow> trans (act ?r) s v = s2 v" 
    by(cut_tac b0, auto)
  
qed
qed
lemma lemmaOnn_SendInv10LeNc_:
  assumes a1:"i\<le>NC"  and a3:"NC\<le>N" 
  shows "trans_sim_on3 (n_SendInv10  i) (n_SendInv10  i) VF VF' NC s" (is "trans_sim_on3 ?r ?r' VF VF' NC  s")
proof(rule ruleSimCond3)
     from a3 show " formEval (pre ?r) s \<longrightarrow>formEval (pre ?r') s" (is "?A \<longrightarrow>?B")  
       apply (auto simp del:evalEqn)done
   next 
	show "(\<forall>  v. v \<in>  varOfSent (act  ?r')  \<longrightarrow> formEval (pre ?r) s \<longrightarrow> 
    expEval (substExpByStatement (IVar v)  (act ?r')) s = expEval (substExpByStatement (IVar v)  (act ?r)) s)"
   proof(rule allI,(rule impI)+)
      fix  v
      assume b1:"formEval (pre ?r) s" and b2:"v \<in>varOfSent (act ?r')"
  
  show "expEval (substExpByStatement (IVar v)  (act ?r')) s = expEval (substExpByStatement (IVar v)  (act ?r)) s"  
       apply (cut_tac  a1 a3 b1 b2 ,auto) done
   qed
 next
   show "\<forall>  v. v \<in>  varOfSent (act ?r) \<longrightarrow>  v \<in> VF \<longrightarrow> v \<in>  varOfSent (act ?r')" 
		by(cut_tac a1 a3, auto)
 next
   from a1 show "\<forall>v. v \<in> varOfForm (pre (?r')) \<longrightarrow>
     formEval (pre (?r)) s  \<longrightarrow>
 v \<in> VF  \<or> v \<in> VF' \<and> scalar2Nat (s v) \<le> NC" 
		apply(cut_tac a1 a3, auto) done
  
next 
  show "\<forall>v. v \<in> varOfSent (act ?r)\<longrightarrow>
        v \<in> VF'\<longrightarrow>         
        formEval (pre (?r)) s \<longrightarrow>
       scalar2Nat (expEval (substExpByStatement (IVar v) (act ?r)) s) \<le> NC
       \<longrightarrow> v \<in> varOfSent (act ?r')"
    	apply(cut_tac a1 a3, auto) done
next
  show "\<forall> v va. v \<in> varOfSent (act ?r') \<longrightarrow> 
  va\<in>varOfExp ( substExpByStatement (IVar v)  (act ?r')) \<longrightarrow>
   va \<in> VF \<or> (va \<in> VF' \<and> (scalar2Nat (s va))\<le> NC)  "
     apply(cut_tac a1 a3, auto) done
qed
lemma lemmaOnn_SendInv10: 
  assumes   a2:"s \<in> reachableSet (set (allInitSpecs N)) (rules N)"  and  
  a4:"\<forall>f.  f \<in>(set invariantsAbs) \<longrightarrow>  formEval f s" and a5:"\<exists> i. i\<le>N\<and>r=n_SendInv10  i"  and
  a6:"NC \<le> N"
  shows "\<exists> r'. r' \<in> rules NC\<and> trans_sim_on3 r r' VF VF' NC s" (is "\<exists>r'.?P1 r' \<and> ?P2 r'")
proof -
  from a5 obtain i where d0:"i\<le>N\<and>r=n_SendInv10  i"  by blast
  have "i>NC|i\<le> NC" by auto
  moreover{
       assume a1:"i>NC" 
        have "\<exists>r'. ?P1 r' \<and> ?P2 r'"
        proof(rule_tac x="(skipRule)" in exI,rule conjI)
          show  "?P1 (skipRule) " 
           by(cut_tac a1, auto) 
          next
          show  "?P2 (skipRule) "
           using lemmaOnn_SendInv10Gt_i local.a1 a2 a4 a6 d0 by blast 
        qed
       }
moreover{
       assume a1:"i\<le> NC" 
        have "\<exists>r'. ?P1 r' \<and> ?P2 r'"
        proof(rule_tac x="(n_SendInv10  i)" in exI,rule conjI)
          show  "?P1 (n_SendInv10  i) " 
           by(cut_tac a1, auto) 
          next
          show  "?P2 (n_SendInv10  i) "
           using lemmaOnn_SendInv10LeNc_ local.a1 a2 a4 a6 d0 by blast 
        qed
       }
  ultimately show "\<exists>r'.?P1 r' \<and> ?P2 r'" 
    by satx
qed

lemma lemmaOnn_RecvReqE11Gt_i:
  assumes a1:"i>NC" and 
  a2:"s \<in> reachableSet (set (allInitSpecs N)) (rules N)"  and a3:"NC\<le>N" and  
  a4:"\<forall>f.  f \<in>(set invariantsAbs) \<longrightarrow>  formEval f s" 
  shows "trans_sim_on3 (n_RecvReqE11 N i)  (n_RecvReqE11_i_3 )  VF VF' NC s" (is "trans_sim_on3 ?r ?r' VF VF' NC s")
  proof(rule ruleSimCond3)
    show " formEval (pre ?r) s \<longrightarrow>formEval (pre ?r') s" (is "?A \<longrightarrow>?B")
    proof(rule impI)+
      assume b0:"?A"
  have tmp:"formEval (inv_inv__4325 0)  s"   
            by(rule usThm1, simp del:inv_inv__4325_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__4325 0  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c0:"formEval  (conclude (inv_inv__4325 0)) s" by auto
have tmp:"formEval (inv_inv__4325 0)  s"   
            by(rule usThm1, simp del:inv_inv__4325_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__4325 1  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c1:"formEval  (conclude (inv_inv__4325 1)) s" by auto
have tmp:"formEval (inv_inv__4325 0)  s"   
            by(rule usThm1, simp del:inv_inv__4325_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__4325 i  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c2:"formEval  (conclude (inv_inv__4325 i)) s" by auto
have tmp:"formEval (inv_inv__4325 0)  s"   
            by(rule usThm1, simp del:inv_inv__4325_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__4325 3  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c3:"formEval  (conclude (inv_inv__4325 3)) s" by auto
have tmp:"formEval (inv_inv__3837 0)  s"   
            by(rule usThm1, simp del:inv_inv__3837_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__3837 0  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c4:"formEval  (conclude (inv_inv__3837 0)) s" by auto
have tmp:"formEval (inv_inv__3837 0)  s"   
            by(rule usThm1, simp del:inv_inv__3837_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__3837 1  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c5:"formEval  (conclude (inv_inv__3837 1)) s" by auto
have tmp:"formEval (inv_inv__3837 0)  s"   
            by(rule usThm1, simp del:inv_inv__3837_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__3837 i  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c6:"formEval  (conclude (inv_inv__3837 i)) s" by auto
have tmp:"formEval (inv_inv__3837 0)  s"   
            by(rule usThm1, simp del:inv_inv__3837_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__3837 3  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c7:"formEval  (conclude (inv_inv__3837 3)) s" by auto

      from a1 a3 b0 c0 c1 c2 c3 c4 c5 c6 c7 show "formEval (pre ?r') s" 
       by (auto simp del:evalEqn)
     qed
   next 
	show "(\<forall>  v. v \<in>  varOfSent (act  ?r')   \<longrightarrow> formEval (pre ?r) s \<longrightarrow> 
    expEval (substExpByStatement (IVar v)  (act ?r')) s = expEval (substExpByStatement (IVar v)  (act ?r)) s)"
   proof(rule allI,(rule impI)+)
      fix  v
     assume b1:"v \<in>varOfSent (act ?r')"  and b2:"formEval (pre ?r) s" 
  
  show "expEval (substExpByStatement (IVar v)  (act ?r')) s = expEval (substExpByStatement (IVar v)  (act ?r)) s"  
       apply (cut_tac  a1 a3 b1 b2 ,auto ) done
   qed
  next
   show "\<forall>  v. v \<in>  varOfSent (act ?r) \<longrightarrow>  v \<in> VF \<longrightarrow> v \<in>  varOfSent (act ?r')" 
		by(cut_tac a1 a3, auto)
 next
   from a1 show "\<forall>v. v \<in> varOfForm (pre (?r')) \<longrightarrow>
     formEval (pre (?r)) s \<longrightarrow> v \<in> VF  \<or> v \<in> VF' \<and> scalar2Nat (s v) \<le> NC" 
		by(cut_tac a1 a3, auto)
  
next 
  show "\<forall>v. v \<in> varOfSent (act ?r)\<longrightarrow>       
    v \<in> VF'\<longrightarrow> formEval (pre (?r)) s  \<longrightarrow> scalar2Nat (expEval (substExpByStatement (IVar v) (act ?r)) s) 
\<le> NC  \<longrightarrow> v \<in> varOfSent (act ?r')"
    	by(cut_tac a1 a3, auto)
next
  show "\<forall> v va. v \<in> varOfSent (act ?r') \<longrightarrow> 
  va\<in>varOfExp ( substExpByStatement (IVar v)  (act ?r')) \<longrightarrow>
   va \<in> VF \<or> (va \<in> VF' \<and> (scalar2Nat (s va))\<le> NC)  "
     apply(cut_tac a1 a3, auto) done
  
qed
lemma lemmaOnn_RecvReqE11LeNc_:
  assumes a1:"i\<le>NC"  and a3:"NC\<le>N" 
  shows "trans_sim_on3 (n_RecvReqE11 N i) (n_RecvReqE11 NC i) VF VF' NC s" (is "trans_sim_on3 ?r ?r' VF VF' NC  s")
proof(rule ruleSimCond3)
     from a3 show " formEval (pre ?r) s \<longrightarrow>formEval (pre ?r') s" (is "?A \<longrightarrow>?B")  
       apply (auto simp del:evalEqn)done
   next 
	show "(\<forall>  v. v \<in>  varOfSent (act  ?r')  \<longrightarrow> formEval (pre ?r) s \<longrightarrow> 
    expEval (substExpByStatement (IVar v)  (act ?r')) s = expEval (substExpByStatement (IVar v)  (act ?r)) s)"
   proof(rule allI,(rule impI)+)
      fix  v
      assume b1:"formEval (pre ?r) s" and b2:"v \<in>varOfSent (act ?r')"
  
  show "expEval (substExpByStatement (IVar v)  (act ?r')) s = expEval (substExpByStatement (IVar v)  (act ?r)) s"  
       apply (cut_tac  a1 a3 b1 b2 ,auto) done
   qed
 next
   show "\<forall>  v. v \<in>  varOfSent (act ?r) \<longrightarrow>  v \<in> VF \<longrightarrow> v \<in>  varOfSent (act ?r')" 
		by(cut_tac a1 a3, auto)
 next
   from a1 show "\<forall>v. v \<in> varOfForm (pre (?r')) \<longrightarrow>
     formEval (pre (?r)) s  \<longrightarrow>
 v \<in> VF  \<or> v \<in> VF' \<and> scalar2Nat (s v) \<le> NC" 
		apply(cut_tac a1 a3, auto) done
  
next 
  show "\<forall>v. v \<in> varOfSent (act ?r)\<longrightarrow>
        v \<in> VF'\<longrightarrow>         
        formEval (pre (?r)) s \<longrightarrow>
       scalar2Nat (expEval (substExpByStatement (IVar v) (act ?r)) s) \<le> NC
       \<longrightarrow> v \<in> varOfSent (act ?r')"
    	apply(cut_tac a1 a3, auto) done
next
  show "\<forall> v va. v \<in> varOfSent (act ?r') \<longrightarrow> 
  va\<in>varOfExp ( substExpByStatement (IVar v)  (act ?r')) \<longrightarrow>
   va \<in> VF \<or> (va \<in> VF' \<and> (scalar2Nat (s va))\<le> NC)  "
     apply(cut_tac a1 a3, auto) done
qed
lemma lemmaOnn_RecvReqE11: 
  assumes   a2:"s \<in> reachableSet (set (allInitSpecs N)) (rules N)"  and  
  a4:"\<forall>f.  f \<in>(set invariantsAbs) \<longrightarrow>  formEval f s" and a5:"\<exists> i. i\<le>N\<and>r=n_RecvReqE11 N i"  and
  a6:"NC \<le> N"
  shows "\<exists> r'. r' \<in> rules NC\<and> trans_sim_on3 r r' VF VF' NC s" (is "\<exists>r'.?P1 r' \<and> ?P2 r'")
proof -
  from a5 obtain i where d0:"i\<le>N\<and>r=n_RecvReqE11 N i"  by blast
  have "i>NC|i\<le> NC" by auto
  moreover{
       assume a1:"i>NC" 
        have "\<exists>r'. ?P1 r' \<and> ?P2 r'"
        proof(rule_tac x="(n_RecvReqE11_i_3 )" in exI,rule conjI)
          show  "?P1 (n_RecvReqE11_i_3 ) " 
           by(cut_tac a1, auto) 
          next
          show  "?P2 (n_RecvReqE11_i_3 ) "
           using lemmaOnn_RecvReqE11Gt_i local.a1 a2 a4 a6 d0 by blast 
        qed
       }
moreover{
       assume a1:"i\<le> NC" 
        have "\<exists>r'. ?P1 r' \<and> ?P2 r'"
        proof(rule_tac x="(n_RecvReqE11 NC i)" in exI,rule conjI)
          show  "?P1 (n_RecvReqE11 NC i) " 
           by(cut_tac a1, auto) 
          next
          show  "?P2 (n_RecvReqE11 NC i) "
           using lemmaOnn_RecvReqE11LeNc_ local.a1 a2 a4 a6 d0 by blast 
        qed
       }
  ultimately show "\<exists>r'.?P1 r' \<and> ?P2 r'" 
    by satx
qed

lemma lemmaOnn_RecvReqS12Gt_i:
  assumes a1:"i>NC" and 
  a2:"s \<in> reachableSet (set (allInitSpecs N)) (rules N)"  and a3:"NC\<le>N" and  
  a4:"\<forall>f.  f \<in>(set invariantsAbs) \<longrightarrow>  formEval f s" 
  shows "trans_sim_on3 (n_RecvReqS12 N i)  (n_RecvReqS12_i_3 )  VF VF' NC s" (is "trans_sim_on3 ?r ?r' VF VF' NC s")
  proof(rule ruleSimCond3)
    show " formEval (pre ?r) s \<longrightarrow>formEval (pre ?r') s" (is "?A \<longrightarrow>?B")
    proof(rule impI)+
      assume b0:"?A"
  have tmp:"formEval (inv_inv__4325 0)  s"   
            by(rule usThm1, simp del:inv_inv__4325_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__4325 0  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c0:"formEval  (conclude (inv_inv__4325 0)) s" by auto
have tmp:"formEval (inv_inv__4325 0)  s"   
            by(rule usThm1, simp del:inv_inv__4325_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__4325 1  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c1:"formEval  (conclude (inv_inv__4325 1)) s" by auto
have tmp:"formEval (inv_inv__4325 0)  s"   
            by(rule usThm1, simp del:inv_inv__4325_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__4325 i  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c2:"formEval  (conclude (inv_inv__4325 i)) s" by auto
have tmp:"formEval (inv_inv__4325 0)  s"   
            by(rule usThm1, simp del:inv_inv__4325_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__4325 3  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c3:"formEval  (conclude (inv_inv__4325 3)) s" by auto
have tmp:"formEval (inv_inv__3837 0)  s"   
            by(rule usThm1, simp del:inv_inv__3837_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__3837 0  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c4:"formEval  (conclude (inv_inv__3837 0)) s" by auto
have tmp:"formEval (inv_inv__3837 0)  s"   
            by(rule usThm1, simp del:inv_inv__3837_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__3837 1  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c5:"formEval  (conclude (inv_inv__3837 1)) s" by auto
have tmp:"formEval (inv_inv__3837 0)  s"   
            by(rule usThm1, simp del:inv_inv__3837_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__3837 i  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c6:"formEval  (conclude (inv_inv__3837 i)) s" by auto
have tmp:"formEval (inv_inv__3837 0)  s"   
            by(rule usThm1, simp del:inv_inv__3837_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__3837 3  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c7:"formEval  (conclude (inv_inv__3837 3)) s" by auto

      from a1 a3 b0 c0 c1 c2 c3 c4 c5 c6 c7 show "formEval (pre ?r') s" 
       by (auto simp del:evalEqn)
     qed
   next 
	show "(\<forall>  v. v \<in>  varOfSent (act  ?r')   \<longrightarrow> formEval (pre ?r) s \<longrightarrow> 
    expEval (substExpByStatement (IVar v)  (act ?r')) s = expEval (substExpByStatement (IVar v)  (act ?r)) s)"
   proof(rule allI,(rule impI)+)
      fix  v
     assume b1:"v \<in>varOfSent (act ?r')"  and b2:"formEval (pre ?r) s" 
  
  show "expEval (substExpByStatement (IVar v)  (act ?r')) s = expEval (substExpByStatement (IVar v)  (act ?r)) s"  
       apply (cut_tac  a1 a3 b1 b2 ,auto ) done
   qed
  next
   show "\<forall>  v. v \<in>  varOfSent (act ?r) \<longrightarrow>  v \<in> VF \<longrightarrow> v \<in>  varOfSent (act ?r')" 
		by(cut_tac a1 a3, auto)
 next
   from a1 show "\<forall>v. v \<in> varOfForm (pre (?r')) \<longrightarrow>
     formEval (pre (?r)) s \<longrightarrow> v \<in> VF  \<or> v \<in> VF' \<and> scalar2Nat (s v) \<le> NC" 
		by(cut_tac a1 a3, auto)
  
next 
  show "\<forall>v. v \<in> varOfSent (act ?r)\<longrightarrow>       
    v \<in> VF'\<longrightarrow> formEval (pre (?r)) s  \<longrightarrow> scalar2Nat (expEval (substExpByStatement (IVar v) (act ?r)) s) 
\<le> NC  \<longrightarrow> v \<in> varOfSent (act ?r')"
    	by(cut_tac a1 a3, auto)
next
  show "\<forall> v va. v \<in> varOfSent (act ?r') \<longrightarrow> 
  va\<in>varOfExp ( substExpByStatement (IVar v)  (act ?r')) \<longrightarrow>
   va \<in> VF \<or> (va \<in> VF' \<and> (scalar2Nat (s va))\<le> NC)  "
     apply(cut_tac a1 a3, auto) done
  
qed
lemma lemmaOnn_RecvReqS12LeNc_:
  assumes a1:"i\<le>NC"  and a3:"NC\<le>N" 
  shows "trans_sim_on3 (n_RecvReqS12 N i) (n_RecvReqS12 NC i) VF VF' NC s" (is "trans_sim_on3 ?r ?r' VF VF' NC  s")
proof(rule ruleSimCond3)
     from a3 show " formEval (pre ?r) s \<longrightarrow>formEval (pre ?r') s" (is "?A \<longrightarrow>?B")  
       apply (auto simp del:evalEqn)done
   next 
	show "(\<forall>  v. v \<in>  varOfSent (act  ?r')  \<longrightarrow> formEval (pre ?r) s \<longrightarrow> 
    expEval (substExpByStatement (IVar v)  (act ?r')) s = expEval (substExpByStatement (IVar v)  (act ?r)) s)"
   proof(rule allI,(rule impI)+)
      fix  v
      assume b1:"formEval (pre ?r) s" and b2:"v \<in>varOfSent (act ?r')"
  
  show "expEval (substExpByStatement (IVar v)  (act ?r')) s = expEval (substExpByStatement (IVar v)  (act ?r)) s"  
       apply (cut_tac  a1 a3 b1 b2 ,auto) done
   qed
 next
   show "\<forall>  v. v \<in>  varOfSent (act ?r) \<longrightarrow>  v \<in> VF \<longrightarrow> v \<in>  varOfSent (act ?r')" 
		by(cut_tac a1 a3, auto)
 next
   from a1 show "\<forall>v. v \<in> varOfForm (pre (?r')) \<longrightarrow>
     formEval (pre (?r)) s  \<longrightarrow>
 v \<in> VF  \<or> v \<in> VF' \<and> scalar2Nat (s v) \<le> NC" 
		apply(cut_tac a1 a3, auto) done
  
next 
  show "\<forall>v. v \<in> varOfSent (act ?r)\<longrightarrow>
        v \<in> VF'\<longrightarrow>         
        formEval (pre (?r)) s \<longrightarrow>
       scalar2Nat (expEval (substExpByStatement (IVar v) (act ?r)) s) \<le> NC
       \<longrightarrow> v \<in> varOfSent (act ?r')"
    	apply(cut_tac a1 a3, auto) done
next
  show "\<forall> v va. v \<in> varOfSent (act ?r') \<longrightarrow> 
  va\<in>varOfExp ( substExpByStatement (IVar v)  (act ?r')) \<longrightarrow>
   va \<in> VF \<or> (va \<in> VF' \<and> (scalar2Nat (s va))\<le> NC)  "
     apply(cut_tac a1 a3, auto) done
qed
lemma lemmaOnn_RecvReqS12: 
  assumes   a2:"s \<in> reachableSet (set (allInitSpecs N)) (rules N)"  and  
  a4:"\<forall>f.  f \<in>(set invariantsAbs) \<longrightarrow>  formEval f s" and a5:"\<exists> i. i\<le>N\<and>r=n_RecvReqS12 N i"  and
  a6:"NC \<le> N"
  shows "\<exists> r'. r' \<in> rules NC\<and> trans_sim_on3 r r' VF VF' NC s" (is "\<exists>r'.?P1 r' \<and> ?P2 r'")
proof -
  from a5 obtain i where d0:"i\<le>N\<and>r=n_RecvReqS12 N i"  by blast
  have "i>NC|i\<le> NC" by auto
  moreover{
       assume a1:"i>NC" 
        have "\<exists>r'. ?P1 r' \<and> ?P2 r'"
        proof(rule_tac x="(n_RecvReqS12_i_3 )" in exI,rule conjI)
          show  "?P1 (n_RecvReqS12_i_3 ) " 
           by(cut_tac a1, auto) 
          next
          show  "?P2 (n_RecvReqS12_i_3 ) "
           using lemmaOnn_RecvReqS12Gt_i local.a1 a2 a4 a6 d0 by blast 
        qed
       }
moreover{
       assume a1:"i\<le> NC" 
        have "\<exists>r'. ?P1 r' \<and> ?P2 r'"
        proof(rule_tac x="(n_RecvReqS12 NC i)" in exI,rule conjI)
          show  "?P1 (n_RecvReqS12 NC i) " 
           by(cut_tac a1, auto) 
          next
          show  "?P2 (n_RecvReqS12 NC i) "
           using lemmaOnn_RecvReqS12LeNc_ local.a1 a2 a4 a6 d0 by blast 
        qed
       }
  ultimately show "\<exists>r'.?P1 r' \<and> ?P2 r'" 
    by satx
qed

lemma lemmaOnn_SendReqE13Gt_i:
  assumes a1:"NC<i" and a2:"s \<in> reachableSet (set (allInitSpecs N)) (rules N)"  and  
  a4:"\<forall>f.  f \<in>(set invariantsAbs) \<longrightarrow>  formEval f s" 
shows "trans_sim_on3 (n_SendReqE13  i  ) skipRule VF  VF' NC s" (is "trans_sim_on3 ?r ?r' VF VF' NC s")
proof(unfold trans_sim_on3_def,(rule allI)+,(rule impI)+,rule disjI2)
  fix s2 
  assume b0:"state_sim_on3 s s2 VF VF' NC "
  show "state_sim_on3 (trans (act (?r)) s) s2 VF VF' NC"
  proof(cut_tac a1,unfold state_sim_on3_def,rule conjI)
    show "\<forall>v. v \<in> VF \<longrightarrow> trans (act ?r) s v = s2 v"
    proof(rule allI,rule impI)
    fix f v
    assume b1:" v \<in>  VF"  
    
    have b5:"trans (act (?r)) s v = s v" 
      by (cut_tac a1  b1,auto) 

    have b6:"s v =s2 v "
      using b0 b1 state_sim_on3_def by blast  
    show "trans (act (?r)) s v= s2 v"
      using b5 b6 by auto 
  qed
next
  show "\<forall>v. v \<in> VF' \<longrightarrow> scalar2Nat (trans (act ?r) s v) \<le> NC \<longrightarrow> trans (act ?r) s v = s2 v" 
    by(cut_tac b0, auto)
  
qed
qed
lemma lemmaOnn_SendReqE13LeNc_:
  assumes a1:"i\<le>NC"  and a3:"NC\<le>N" 
  shows "trans_sim_on3 (n_SendReqE13  i) (n_SendReqE13  i) VF VF' NC s" (is "trans_sim_on3 ?r ?r' VF VF' NC  s")
proof(rule ruleSimCond3)
     from a3 show " formEval (pre ?r) s \<longrightarrow>formEval (pre ?r') s" (is "?A \<longrightarrow>?B")  
       apply (auto simp del:evalEqn)done
   next 
	show "(\<forall>  v. v \<in>  varOfSent (act  ?r')  \<longrightarrow> formEval (pre ?r) s \<longrightarrow> 
    expEval (substExpByStatement (IVar v)  (act ?r')) s = expEval (substExpByStatement (IVar v)  (act ?r)) s)"
   proof(rule allI,(rule impI)+)
      fix  v
      assume b1:"formEval (pre ?r) s" and b2:"v \<in>varOfSent (act ?r')"
  
  show "expEval (substExpByStatement (IVar v)  (act ?r')) s = expEval (substExpByStatement (IVar v)  (act ?r)) s"  
       apply (cut_tac  a1 a3 b1 b2 ,auto) done
   qed
 next
   show "\<forall>  v. v \<in>  varOfSent (act ?r) \<longrightarrow>  v \<in> VF \<longrightarrow> v \<in>  varOfSent (act ?r')" 
		by(cut_tac a1 a3, auto)
 next
   from a1 show "\<forall>v. v \<in> varOfForm (pre (?r')) \<longrightarrow>
     formEval (pre (?r)) s  \<longrightarrow>
 v \<in> VF  \<or> v \<in> VF' \<and> scalar2Nat (s v) \<le> NC" 
		apply(cut_tac a1 a3, auto) done
  
next 
  show "\<forall>v. v \<in> varOfSent (act ?r)\<longrightarrow>
        v \<in> VF'\<longrightarrow>         
        formEval (pre (?r)) s \<longrightarrow>
       scalar2Nat (expEval (substExpByStatement (IVar v) (act ?r)) s) \<le> NC
       \<longrightarrow> v \<in> varOfSent (act ?r')"
    	apply(cut_tac a1 a3, auto) done
next
  show "\<forall> v va. v \<in> varOfSent (act ?r') \<longrightarrow> 
  va\<in>varOfExp ( substExpByStatement (IVar v)  (act ?r')) \<longrightarrow>
   va \<in> VF \<or> (va \<in> VF' \<and> (scalar2Nat (s va))\<le> NC)  "
     apply(cut_tac a1 a3, auto) done
qed
lemma lemmaOnn_SendReqE13: 
  assumes   a2:"s \<in> reachableSet (set (allInitSpecs N)) (rules N)"  and  
  a4:"\<forall>f.  f \<in>(set invariantsAbs) \<longrightarrow>  formEval f s" and a5:"\<exists> i. i\<le>N\<and>r=n_SendReqE13  i"  and
  a6:"NC \<le> N"
  shows "\<exists> r'. r' \<in> rules NC\<and> trans_sim_on3 r r' VF VF' NC s" (is "\<exists>r'.?P1 r' \<and> ?P2 r'")
proof -
  from a5 obtain i where d0:"i\<le>N\<and>r=n_SendReqE13  i"  by blast
  have "i>NC|i\<le> NC" by auto
  moreover{
       assume a1:"i>NC" 
        have "\<exists>r'. ?P1 r' \<and> ?P2 r'"
        proof(rule_tac x="(skipRule)" in exI,rule conjI)
          show  "?P1 (skipRule) " 
           by(cut_tac a1, auto) 
          next
          show  "?P2 (skipRule) "
           using lemmaOnn_SendReqE13Gt_i local.a1 a2 a4 a6 d0 by blast 
        qed
       }
moreover{
       assume a1:"i\<le> NC" 
        have "\<exists>r'. ?P1 r' \<and> ?P2 r'"
        proof(rule_tac x="(n_SendReqE13  i)" in exI,rule conjI)
          show  "?P1 (n_SendReqE13  i) " 
           by(cut_tac a1, auto) 
          next
          show  "?P2 (n_SendReqE13  i) "
           using lemmaOnn_SendReqE13LeNc_ local.a1 a2 a4 a6 d0 by blast 
        qed
       }
  ultimately show "\<exists>r'.?P1 r' \<and> ?P2 r'" 
    by satx
qed

lemma lemmaOnn_SendReqE14Gt_i:
  assumes a1:"NC<i" and a2:"s \<in> reachableSet (set (allInitSpecs N)) (rules N)"  and  
  a4:"\<forall>f.  f \<in>(set invariantsAbs) \<longrightarrow>  formEval f s" 
shows "trans_sim_on3 (n_SendReqE14  i  ) skipRule VF  VF' NC s" (is "trans_sim_on3 ?r ?r' VF VF' NC s")
proof(unfold trans_sim_on3_def,(rule allI)+,(rule impI)+,rule disjI2)
  fix s2 
  assume b0:"state_sim_on3 s s2 VF VF' NC "
  show "state_sim_on3 (trans (act (?r)) s) s2 VF VF' NC"
  proof(cut_tac a1,unfold state_sim_on3_def,rule conjI)
    show "\<forall>v. v \<in> VF \<longrightarrow> trans (act ?r) s v = s2 v"
    proof(rule allI,rule impI)
    fix f v
    assume b1:" v \<in>  VF"  
    
    have b5:"trans (act (?r)) s v = s v" 
      by (cut_tac a1  b1,auto) 

    have b6:"s v =s2 v "
      using b0 b1 state_sim_on3_def by blast  
    show "trans (act (?r)) s v= s2 v"
      using b5 b6 by auto 
  qed
next
  show "\<forall>v. v \<in> VF' \<longrightarrow> scalar2Nat (trans (act ?r) s v) \<le> NC \<longrightarrow> trans (act ?r) s v = s2 v" 
    by(cut_tac b0, auto)
  
qed
qed
lemma lemmaOnn_SendReqE14LeNc_:
  assumes a1:"i\<le>NC"  and a3:"NC\<le>N" 
  shows "trans_sim_on3 (n_SendReqE14  i) (n_SendReqE14  i) VF VF' NC s" (is "trans_sim_on3 ?r ?r' VF VF' NC  s")
proof(rule ruleSimCond3)
     from a3 show " formEval (pre ?r) s \<longrightarrow>formEval (pre ?r') s" (is "?A \<longrightarrow>?B")  
       apply (auto simp del:evalEqn)done
   next 
	show "(\<forall>  v. v \<in>  varOfSent (act  ?r')  \<longrightarrow> formEval (pre ?r) s \<longrightarrow> 
    expEval (substExpByStatement (IVar v)  (act ?r')) s = expEval (substExpByStatement (IVar v)  (act ?r)) s)"
   proof(rule allI,(rule impI)+)
      fix  v
      assume b1:"formEval (pre ?r) s" and b2:"v \<in>varOfSent (act ?r')"
  
  show "expEval (substExpByStatement (IVar v)  (act ?r')) s = expEval (substExpByStatement (IVar v)  (act ?r)) s"  
       apply (cut_tac  a1 a3 b1 b2 ,auto) done
   qed
 next
   show "\<forall>  v. v \<in>  varOfSent (act ?r) \<longrightarrow>  v \<in> VF \<longrightarrow> v \<in>  varOfSent (act ?r')" 
		by(cut_tac a1 a3, auto)
 next
   from a1 show "\<forall>v. v \<in> varOfForm (pre (?r')) \<longrightarrow>
     formEval (pre (?r)) s  \<longrightarrow>
 v \<in> VF  \<or> v \<in> VF' \<and> scalar2Nat (s v) \<le> NC" 
		apply(cut_tac a1 a3, auto) done
  
next 
  show "\<forall>v. v \<in> varOfSent (act ?r)\<longrightarrow>
        v \<in> VF'\<longrightarrow>         
        formEval (pre (?r)) s \<longrightarrow>
       scalar2Nat (expEval (substExpByStatement (IVar v) (act ?r)) s) \<le> NC
       \<longrightarrow> v \<in> varOfSent (act ?r')"
    	apply(cut_tac a1 a3, auto) done
next
  show "\<forall> v va. v \<in> varOfSent (act ?r') \<longrightarrow> 
  va\<in>varOfExp ( substExpByStatement (IVar v)  (act ?r')) \<longrightarrow>
   va \<in> VF \<or> (va \<in> VF' \<and> (scalar2Nat (s va))\<le> NC)  "
     apply(cut_tac a1 a3, auto) done
qed
lemma lemmaOnn_SendReqE14: 
  assumes   a2:"s \<in> reachableSet (set (allInitSpecs N)) (rules N)"  and  
  a4:"\<forall>f.  f \<in>(set invariantsAbs) \<longrightarrow>  formEval f s" and a5:"\<exists> i. i\<le>N\<and>r=n_SendReqE14  i"  and
  a6:"NC \<le> N"
  shows "\<exists> r'. r' \<in> rules NC\<and> trans_sim_on3 r r' VF VF' NC s" (is "\<exists>r'.?P1 r' \<and> ?P2 r'")
proof -
  from a5 obtain i where d0:"i\<le>N\<and>r=n_SendReqE14  i"  by blast
  have "i>NC|i\<le> NC" by auto
  moreover{
       assume a1:"i>NC" 
        have "\<exists>r'. ?P1 r' \<and> ?P2 r'"
        proof(rule_tac x="(skipRule)" in exI,rule conjI)
          show  "?P1 (skipRule) " 
           by(cut_tac a1, auto) 
          next
          show  "?P2 (skipRule) "
           using lemmaOnn_SendReqE14Gt_i local.a1 a2 a4 a6 d0 by blast 
        qed
       }
moreover{
       assume a1:"i\<le> NC" 
        have "\<exists>r'. ?P1 r' \<and> ?P2 r'"
        proof(rule_tac x="(n_SendReqE14  i)" in exI,rule conjI)
          show  "?P1 (n_SendReqE14  i) " 
           by(cut_tac a1, auto) 
          next
          show  "?P2 (n_SendReqE14  i) "
           using lemmaOnn_SendReqE14LeNc_ local.a1 a2 a4 a6 d0 by blast 
        qed
       }
  ultimately show "\<exists>r'.?P1 r' \<and> ?P2 r'" 
    by satx
qed

lemma lemmaOnn_SendReqS15Gt_i:
  assumes a1:"NC<i" and a2:"s \<in> reachableSet (set (allInitSpecs N)) (rules N)"  and  
  a4:"\<forall>f.  f \<in>(set invariantsAbs) \<longrightarrow>  formEval f s" 
shows "trans_sim_on3 (n_SendReqS15  i  ) skipRule VF  VF' NC s" (is "trans_sim_on3 ?r ?r' VF VF' NC s")
proof(unfold trans_sim_on3_def,(rule allI)+,(rule impI)+,rule disjI2)
  fix s2 
  assume b0:"state_sim_on3 s s2 VF VF' NC "
  show "state_sim_on3 (trans (act (?r)) s) s2 VF VF' NC"
  proof(cut_tac a1,unfold state_sim_on3_def,rule conjI)
    show "\<forall>v. v \<in> VF \<longrightarrow> trans (act ?r) s v = s2 v"
    proof(rule allI,rule impI)
    fix f v
    assume b1:" v \<in>  VF"  
    
    have b5:"trans (act (?r)) s v = s v" 
      by (cut_tac a1  b1,auto) 

    have b6:"s v =s2 v "
      using b0 b1 state_sim_on3_def by blast  
    show "trans (act (?r)) s v= s2 v"
      using b5 b6 by auto 
  qed
next
  show "\<forall>v. v \<in> VF' \<longrightarrow> scalar2Nat (trans (act ?r) s v) \<le> NC \<longrightarrow> trans (act ?r) s v = s2 v" 
    by(cut_tac b0, auto)
  
qed
qed
lemma lemmaOnn_SendReqS15LeNc_:
  assumes a1:"i\<le>NC"  and a3:"NC\<le>N" 
  shows "trans_sim_on3 (n_SendReqS15  i) (n_SendReqS15  i) VF VF' NC s" (is "trans_sim_on3 ?r ?r' VF VF' NC  s")
proof(rule ruleSimCond3)
     from a3 show " formEval (pre ?r) s \<longrightarrow>formEval (pre ?r') s" (is "?A \<longrightarrow>?B")  
       apply (auto simp del:evalEqn)done
   next 
	show "(\<forall>  v. v \<in>  varOfSent (act  ?r')  \<longrightarrow> formEval (pre ?r) s \<longrightarrow> 
    expEval (substExpByStatement (IVar v)  (act ?r')) s = expEval (substExpByStatement (IVar v)  (act ?r)) s)"
   proof(rule allI,(rule impI)+)
      fix  v
      assume b1:"formEval (pre ?r) s" and b2:"v \<in>varOfSent (act ?r')"
  
  show "expEval (substExpByStatement (IVar v)  (act ?r')) s = expEval (substExpByStatement (IVar v)  (act ?r)) s"  
       apply (cut_tac  a1 a3 b1 b2 ,auto) done
   qed
 next
   show "\<forall>  v. v \<in>  varOfSent (act ?r) \<longrightarrow>  v \<in> VF \<longrightarrow> v \<in>  varOfSent (act ?r')" 
		by(cut_tac a1 a3, auto)
 next
   from a1 show "\<forall>v. v \<in> varOfForm (pre (?r')) \<longrightarrow>
     formEval (pre (?r)) s  \<longrightarrow>
 v \<in> VF  \<or> v \<in> VF' \<and> scalar2Nat (s v) \<le> NC" 
		apply(cut_tac a1 a3, auto) done
  
next 
  show "\<forall>v. v \<in> varOfSent (act ?r)\<longrightarrow>
        v \<in> VF'\<longrightarrow>         
        formEval (pre (?r)) s \<longrightarrow>
       scalar2Nat (expEval (substExpByStatement (IVar v) (act ?r)) s) \<le> NC
       \<longrightarrow> v \<in> varOfSent (act ?r')"
    	apply(cut_tac a1 a3, auto) done
next
  show "\<forall> v va. v \<in> varOfSent (act ?r') \<longrightarrow> 
  va\<in>varOfExp ( substExpByStatement (IVar v)  (act ?r')) \<longrightarrow>
   va \<in> VF \<or> (va \<in> VF' \<and> (scalar2Nat (s va))\<le> NC)  "
     apply(cut_tac a1 a3, auto) done
qed
lemma lemmaOnn_SendReqS15: 
  assumes   a2:"s \<in> reachableSet (set (allInitSpecs N)) (rules N)"  and  
  a4:"\<forall>f.  f \<in>(set invariantsAbs) \<longrightarrow>  formEval f s" and a5:"\<exists> i. i\<le>N\<and>r=n_SendReqS15  i"  and
  a6:"NC \<le> N"
  shows "\<exists> r'. r' \<in> rules NC\<and> trans_sim_on3 r r' VF VF' NC s" (is "\<exists>r'.?P1 r' \<and> ?P2 r'")
proof -
  from a5 obtain i where d0:"i\<le>N\<and>r=n_SendReqS15  i"  by blast
  have "i>NC|i\<le> NC" by auto
  moreover{
       assume a1:"i>NC" 
        have "\<exists>r'. ?P1 r' \<and> ?P2 r'"
        proof(rule_tac x="(skipRule)" in exI,rule conjI)
          show  "?P1 (skipRule) " 
           by(cut_tac a1, auto) 
          next
          show  "?P2 (skipRule) "
           using lemmaOnn_SendReqS15Gt_i local.a1 a2 a4 a6 d0 by blast 
        qed
       }
moreover{
       assume a1:"i\<le> NC" 
        have "\<exists>r'. ?P1 r' \<and> ?P2 r'"
        proof(rule_tac x="(n_SendReqS15  i)" in exI,rule conjI)
          show  "?P1 (n_SendReqS15  i) " 
           by(cut_tac a1, auto) 
          next
          show  "?P2 (n_SendReqS15  i) "
           using lemmaOnn_SendReqS15LeNc_ local.a1 a2 a4 a6 d0 by blast 
        qed
       }
  ultimately show "\<exists>r'.?P1 r' \<and> ?P2 r'" 
    by satx
qed

lemma lemmaOnn_StoreGt_i:
  assumes a1:"i>NC" and 
  a2:"s \<in> reachableSet (set (allInitSpecs N)) (rules N)"  and a3:"NC\<le>N" and  
  a4:"\<forall>f.  f \<in>(set invariantsAbs) \<longrightarrow>  formEval f s" and a5:"d\<le> NC"
  shows "trans_sim_on3 (n_Store  i d)  (n_Store_i_3 d)  VF VF' NC s" (is "trans_sim_on3 ?r ?r' VF VF' NC s")
  proof(rule ruleSimCond3)
    show " formEval (pre ?r) s \<longrightarrow>formEval (pre ?r') s" (is "?A \<longrightarrow>?B")
    proof(rule impI)+
      assume b0:"?A"
  have tmp:"formEval (inv_inv__4130 0 1)  s"   
            by(rule usThm1, simp del:inv_inv__4130_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__4130 i 0  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf2,force+)qed
        with b0 a1 have c0:"formEval  (conclude (inv_inv__4130 i 0)) s" by auto
have tmp:"formEval (inv_inv__4130 0 1)  s"   
            by(rule usThm1, simp del:inv_inv__4130_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__4130 i 1  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf2,force+)qed
        with b0 a1 have c1:"formEval  (conclude (inv_inv__4130 i 1)) s" by auto
have tmp:"formEval (inv_inv__4130 0 1)  s"   
            by(rule usThm1, simp del:inv_inv__4130_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__4130 i d  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf2,force+)qed
        with b0 a1 have c2:"formEval  (conclude (inv_inv__4130 i d)) s" by auto
have tmp:"formEval (inv_inv__3738 0 1)  s"   
            by(rule usThm1, simp del:inv_inv__3738_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__3738 i 0  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf2,force+)qed
        with b0 a1 have c3:"formEval  (conclude (inv_inv__3738 i 0)) s" by auto
have tmp:"formEval (inv_inv__3738 0 1)  s"   
            by(rule usThm1, simp del:inv_inv__3738_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__3738 i 1  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf2,force+)qed
        with b0 a1 have c4:"formEval  (conclude (inv_inv__3738 i 1)) s" by auto
have tmp:"formEval (inv_inv__3738 0 1)  s"   
            by(rule usThm1, simp del:inv_inv__3738_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__3738 i d  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf2,force+)qed
        with b0 a1 have c5:"formEval  (conclude (inv_inv__3738 i d)) s" by auto
have tmp:"formEval (inv_inv__513 0 1)  s"   
            by(rule usThm1, simp del:inv_inv__513_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__513 i 0  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf2,force+)qed
        with b0 a1 have c6:"formEval  (conclude (inv_inv__513 i 0)) s" by auto
have tmp:"formEval (inv_inv__513 0 1)  s"   
            by(rule usThm1, simp del:inv_inv__513_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__513 i 1  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf2,force+)qed
        with b0 a1 have c7:"formEval  (conclude (inv_inv__513 i 1)) s" by auto
have tmp:"formEval (inv_inv__513 0 1)  s"   
            by(rule usThm1, simp del:inv_inv__513_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__513 i d  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf2,force+)qed
        with b0 a1 have c8:"formEval  (conclude (inv_inv__513 i d)) s" by auto
have tmp:"formEval (inv_inv__3052 0)  s"   
            by(rule usThm1, simp del:inv_inv__3052_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__3052 0  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c9:"formEval  (conclude (inv_inv__3052 0)) s" by auto
have tmp:"formEval (inv_inv__3052 0)  s"   
            by(rule usThm1, simp del:inv_inv__3052_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__3052 1  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c10:"formEval  (conclude (inv_inv__3052 1)) s" by auto
have tmp:"formEval (inv_inv__3052 0)  s"   
            by(rule usThm1, simp del:inv_inv__3052_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__3052 d  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c11:"formEval  (conclude (inv_inv__3052 d)) s" by auto
have tmp:"formEval (inv_inv__1293 0)  s"   
            by(rule usThm1, simp del:inv_inv__1293_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__1293 0  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c12:"formEval  (conclude (inv_inv__1293 0)) s" by auto
have tmp:"formEval (inv_inv__1293 0)  s"   
            by(rule usThm1, simp del:inv_inv__1293_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__1293 1  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c13:"formEval  (conclude (inv_inv__1293 1)) s" by auto
have tmp:"formEval (inv_inv__1293 0)  s"   
            by(rule usThm1, simp del:inv_inv__1293_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__1293 d  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c14:"formEval  (conclude (inv_inv__1293 d)) s" by auto
have tmp:"formEval (inv_inv__2271 0)  s"   
            by(rule usThm1, simp del:inv_inv__2271_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__2271 0  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c15:"formEval  (conclude (inv_inv__2271 0)) s" by auto
have tmp:"formEval (inv_inv__2271 0)  s"   
            by(rule usThm1, simp del:inv_inv__2271_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__2271 1  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c16:"formEval  (conclude (inv_inv__2271 1)) s" by auto
have tmp:"formEval (inv_inv__2271 0)  s"   
            by(rule usThm1, simp del:inv_inv__2271_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__2271 d  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c17:"formEval  (conclude (inv_inv__2271 d)) s" by auto
have tmp:"formEval (inv_inv__3346 0)  s"   
            by(rule usThm1, simp del:inv_inv__3346_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__3346 0  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c18:"formEval  (conclude (inv_inv__3346 0)) s" by auto
have tmp:"formEval (inv_inv__3346 0)  s"   
            by(rule usThm1, simp del:inv_inv__3346_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__3346 1  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c19:"formEval  (conclude (inv_inv__3346 1)) s" by auto
have tmp:"formEval (inv_inv__3346 0)  s"   
            by(rule usThm1, simp del:inv_inv__3346_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__3346 d  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c20:"formEval  (conclude (inv_inv__3346 d)) s" by auto
have tmp:"formEval (inv_inv__3543 0)  s"   
            by(rule usThm1, simp del:inv_inv__3543_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__3543 0  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c21:"formEval  (conclude (inv_inv__3543 0)) s" by auto
have tmp:"formEval (inv_inv__3543 0)  s"   
            by(rule usThm1, simp del:inv_inv__3543_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__3543 1  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c22:"formEval  (conclude (inv_inv__3543 1)) s" by auto
have tmp:"formEval (inv_inv__3543 0)  s"   
            by(rule usThm1, simp del:inv_inv__3543_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__3543 d  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c23:"formEval  (conclude (inv_inv__3543 d)) s" by auto
have tmp:"formEval (inv_inv__2467 0)  s"   
            by(rule usThm1, simp del:inv_inv__2467_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__2467 0  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c24:"formEval  (conclude (inv_inv__2467 0)) s" by auto
have tmp:"formEval (inv_inv__2467 0)  s"   
            by(rule usThm1, simp del:inv_inv__2467_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__2467 1  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c25:"formEval  (conclude (inv_inv__2467 1)) s" by auto
have tmp:"formEval (inv_inv__2467 0)  s"   
            by(rule usThm1, simp del:inv_inv__2467_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__2467 d  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c26:"formEval  (conclude (inv_inv__2467 d)) s" by auto
have tmp:"formEval (inv_inv__3151 0)  s"   
            by(rule usThm1, simp del:inv_inv__3151_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__3151 0  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c27:"formEval  (conclude (inv_inv__3151 0)) s" by auto
have tmp:"formEval (inv_inv__3151 0)  s"   
            by(rule usThm1, simp del:inv_inv__3151_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__3151 1  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c28:"formEval  (conclude (inv_inv__3151 1)) s" by auto
have tmp:"formEval (inv_inv__3151 0)  s"   
            by(rule usThm1, simp del:inv_inv__3151_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__3151 i  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c29:"formEval  (conclude (inv_inv__3151 i)) s" by auto
have tmp:"formEval (inv_inv__3151 0)  s"   
            by(rule usThm1, simp del:inv_inv__3151_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__3151 d  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c30:"formEval  (conclude (inv_inv__3151 d)) s" by auto
have tmp:"formEval (inv_inv__511 0 1)  s"   
            by(rule usThm1, simp del:inv_inv__511_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__511 0 i  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf2,force+)qed
        with b0 a1 have c31:"formEval  (conclude (inv_inv__511 0 i)) s" by auto
have tmp:"formEval (inv_inv__511 0 1)  s"   
            by(rule usThm1, simp del:inv_inv__511_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__511 1 i  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf2,force+)qed
        with b0 a1 have c32:"formEval  (conclude (inv_inv__511 1 i)) s" by auto
have tmp:"formEval (inv_inv__511 0 1)  s"   
            by(rule usThm1, simp del:inv_inv__511_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__511 d i  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf2,force+)qed
        with b0 a1 have c33:"formEval  (conclude (inv_inv__511 d i)) s" by auto
have tmp:"formEval (inv_inv__1197 0)  s"   
            by(rule usThm1, simp del:inv_inv__1197_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__1197 0  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c34:"formEval  (conclude (inv_inv__1197 0)) s" by auto
have tmp:"formEval (inv_inv__1197 0)  s"   
            by(rule usThm1, simp del:inv_inv__1197_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__1197 1  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c35:"formEval  (conclude (inv_inv__1197 1)) s" by auto
have tmp:"formEval (inv_inv__1197 0)  s"   
            by(rule usThm1, simp del:inv_inv__1197_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__1197 d  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c36:"formEval  (conclude (inv_inv__1197 d)) s" by auto
have tmp:"formEval (inv_inv__3739 0 1)  s"   
            by(rule usThm1, simp del:inv_inv__3739_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__3739 0 i  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf2,force+)qed
        with b0 a1 have c37:"formEval  (conclude (inv_inv__3739 0 i)) s" by auto
have tmp:"formEval (inv_inv__3739 0 1)  s"   
            by(rule usThm1, simp del:inv_inv__3739_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__3739 1 i  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf2,force+)qed
        with b0 a1 have c38:"formEval  (conclude (inv_inv__3739 1 i)) s" by auto
have tmp:"formEval (inv_inv__3739 0 1)  s"   
            by(rule usThm1, simp del:inv_inv__3739_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__3739 d i  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf2,force+)qed
        with b0 a1 have c39:"formEval  (conclude (inv_inv__3739 d i)) s" by auto
have tmp:"formEval (inv_inv__2762 0 1)  s"   
            by(rule usThm1, simp del:inv_inv__2762_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__2762 i 0  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf2,force+)qed
        with b0 a1 have c40:"formEval  (conclude (inv_inv__2762 i 0)) s" by auto
have tmp:"formEval (inv_inv__2762 0 1)  s"   
            by(rule usThm1, simp del:inv_inv__2762_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__2762 i 1  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf2,force+)qed
        with b0 a1 have c41:"formEval  (conclude (inv_inv__2762 i 1)) s" by auto
have tmp:"formEval (inv_inv__2762 0 1)  s"   
            by(rule usThm1, simp del:inv_inv__2762_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__2762 i d  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf2,force+)qed
        with b0 a1 have c42:"formEval  (conclude (inv_inv__2762 i d)) s" by auto
have tmp:"formEval (inv_inv__3113 0)  s"   
            by(rule usThm1, simp del:inv_inv__3113_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__3113 i  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c43:"formEval  (conclude (inv_inv__3113 i)) s" by auto
have tmp:"formEval (inv_inv__8103 0)  s"   
            by(rule usThm1, simp del:inv_inv__8103_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__8103 i  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c44:"formEval  (conclude (inv_inv__8103 i)) s" by auto
have tmp:"formEval (inv_inv__9101 0 1)  s"   
            by(rule usThm1, simp del:inv_inv__9101_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__9101 i 0  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf2,force+)qed
        with b0 a1 have c45:"formEval  (conclude (inv_inv__9101 i 0)) s" by auto
have tmp:"formEval (inv_inv__9101 0 1)  s"   
            by(rule usThm1, simp del:inv_inv__9101_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__9101 i 1  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf2,force+)qed
        with b0 a1 have c46:"formEval  (conclude (inv_inv__9101 i 1)) s" by auto
have tmp:"formEval (inv_inv__9101 0 1)  s"   
            by(rule usThm1, simp del:inv_inv__9101_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__9101 i d  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf2,force+)qed
        with b0 a1 have c47:"formEval  (conclude (inv_inv__9101 i d)) s" by auto
have tmp:"formEval (inv_inv__1685 0)  s"   
            by(rule usThm1, simp del:inv_inv__1685_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__1685 i  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c48:"formEval  (conclude (inv_inv__1685 i)) s" by auto
have tmp:"formEval (inv_inv__1783 0)  s"   
            by(rule usThm1, simp del:inv_inv__1783_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__1783 i  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c49:"formEval  (conclude (inv_inv__1783 i)) s" by auto
have tmp:"formEval (inv_inv__2078 0 1)  s"   
            by(rule usThm1, simp del:inv_inv__2078_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__2078 0 i  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf2,force+)qed
        with b0 a1 have c50:"formEval  (conclude (inv_inv__2078 0 i)) s" by auto
have tmp:"formEval (inv_inv__2078 0 1)  s"   
            by(rule usThm1, simp del:inv_inv__2078_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__2078 1 i  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf2,force+)qed
        with b0 a1 have c51:"formEval  (conclude (inv_inv__2078 1 i)) s" by auto
have tmp:"formEval (inv_inv__2078 0 1)  s"   
            by(rule usThm1, simp del:inv_inv__2078_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__2078 d i  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf2,force+)qed
        with b0 a1 have c52:"formEval  (conclude (inv_inv__2078 d i)) s" by auto
have tmp:"formEval (inv_inv__1392 0 1)  s"   
            by(rule usThm1, simp del:inv_inv__1392_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__1392 i 0  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf2,force+)qed
        with b0 a1 have c53:"formEval  (conclude (inv_inv__1392 i 0)) s" by auto
have tmp:"formEval (inv_inv__1392 0 1)  s"   
            by(rule usThm1, simp del:inv_inv__1392_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__1392 i 1  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf2,force+)qed
        with b0 a1 have c54:"formEval  (conclude (inv_inv__1392 i 1)) s" by auto
have tmp:"formEval (inv_inv__1392 0 1)  s"   
            by(rule usThm1, simp del:inv_inv__1392_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__1392 i d  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf2,force+)qed
        with b0 a1 have c55:"formEval  (conclude (inv_inv__1392 i d)) s" by auto
have tmp:"formEval (inv_inv__1588 0 1)  s"   
            by(rule usThm1, simp del:inv_inv__1588_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__1588 i 0  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf2,force+)qed
        with b0 a1 have c56:"formEval  (conclude (inv_inv__1588 i 0)) s" by auto
have tmp:"formEval (inv_inv__1588 0 1)  s"   
            by(rule usThm1, simp del:inv_inv__1588_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__1588 i 1  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf2,force+)qed
        with b0 a1 have c57:"formEval  (conclude (inv_inv__1588 i 1)) s" by auto
have tmp:"formEval (inv_inv__1588 0 1)  s"   
            by(rule usThm1, simp del:inv_inv__1588_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__1588 i d  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf2,force+)qed
        with b0 a1 have c58:"formEval  (conclude (inv_inv__1588 i d)) s" by auto
have tmp:"formEval (inv_inv__5108 0 1)  s"   
            by(rule usThm1, simp del:inv_inv__5108_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__5108 0 i  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf2,force+)qed
        with b0 a1 have c59:"formEval  (conclude (inv_inv__5108 0 i)) s" by auto
have tmp:"formEval (inv_inv__5108 0 1)  s"   
            by(rule usThm1, simp del:inv_inv__5108_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__5108 1 i  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf2,force+)qed
        with b0 a1 have c60:"formEval  (conclude (inv_inv__5108 1 i)) s" by auto
have tmp:"formEval (inv_inv__5108 0 1)  s"   
            by(rule usThm1, simp del:inv_inv__5108_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__5108 d i  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf2,force+)qed
        with b0 a1 have c61:"formEval  (conclude (inv_inv__5108 d i)) s" by auto
have tmp:"formEval (inv_inv__2468 0)  s"   
            by(rule usThm1, simp del:inv_inv__2468_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__2468 i  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c62:"formEval  (conclude (inv_inv__2468 i)) s" by auto
have tmp:"formEval (inv_inv__3445 0)  s"   
            by(rule usThm1, simp del:inv_inv__3445_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__3445 i  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c63:"formEval  (conclude (inv_inv__3445 i)) s" by auto
have tmp:"formEval (inv_inv__1490 0 1)  s"   
            by(rule usThm1, simp del:inv_inv__1490_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__1490 0 i  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf2,force+)qed
        with b0 a1 have c64:"formEval  (conclude (inv_inv__1490 0 i)) s" by auto
have tmp:"formEval (inv_inv__1490 0 1)  s"   
            by(rule usThm1, simp del:inv_inv__1490_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__1490 1 i  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf2,force+)qed
        with b0 a1 have c65:"formEval  (conclude (inv_inv__1490 1 i)) s" by auto
have tmp:"formEval (inv_inv__1490 0 1)  s"   
            by(rule usThm1, simp del:inv_inv__1490_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__1490 d i  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf2,force+)qed
        with b0 a1 have c66:"formEval  (conclude (inv_inv__1490 d i)) s" by auto
have tmp:"formEval (inv_inv__5109 0 1)  s"   
            by(rule usThm1, simp del:inv_inv__5109_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__5109 i 0  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf2,force+)qed
        with b0 a1 have c67:"formEval  (conclude (inv_inv__5109 i 0)) s" by auto
have tmp:"formEval (inv_inv__5109 0 1)  s"   
            by(rule usThm1, simp del:inv_inv__5109_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__5109 i 1  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf2,force+)qed
        with b0 a1 have c68:"formEval  (conclude (inv_inv__5109 i 1)) s" by auto
have tmp:"formEval (inv_inv__5109 0 1)  s"   
            by(rule usThm1, simp del:inv_inv__5109_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__5109 i d  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf2,force+)qed
        with b0 a1 have c69:"formEval  (conclude (inv_inv__5109 i d)) s" by auto
have tmp:"formEval (inv_inv__2116 0)  s"   
            by(rule usThm1, simp del:inv_inv__2116_def,cut_tac a4,assumption )
        have tmp1:"formEval (inv_inv__2116 i  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c70:"formEval  (conclude (inv_inv__2116 i)) s" by auto

      from a1 a3 b0 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 c29 c30 c31 c32 c33 c34 c35 c36 c37 c38 c39 c40 c41 c42 c43 c44 c45 c46 c47 c48 c49 c50 c51 c52 c53 c54 c55 c56 c57 c58 c59 c60 c61 c62 c63 c64 c65 c66 c67 c68 c69 c70 show "formEval (pre ?r') s" 
       by (auto simp del:evalEqn)
     qed
   next 
	show "(\<forall>  v. v \<in>  varOfSent (act  ?r')   \<longrightarrow> formEval (pre ?r) s \<longrightarrow> 
    expEval (substExpByStatement (IVar v)  (act ?r')) s = expEval (substExpByStatement (IVar v)  (act ?r)) s)"
   proof(rule allI,(rule impI)+)
      fix  v
     assume b1:"v \<in>varOfSent (act ?r')"  and b2:"formEval (pre ?r) s" 
  
  show "expEval (substExpByStatement (IVar v)  (act ?r')) s = expEval (substExpByStatement (IVar v)  (act ?r)) s"  
       apply (cut_tac  a1 a3 b1 b2 ,auto ) done
   qed
  next
   show "\<forall>  v. v \<in>  varOfSent (act ?r) \<longrightarrow>  v \<in> VF \<longrightarrow> v \<in>  varOfSent (act ?r')" 
		by(cut_tac a1 a3, auto)
 next
   from a1 show "\<forall>v. v \<in> varOfForm (pre (?r')) \<longrightarrow>
     formEval (pre (?r)) s \<longrightarrow> v \<in> VF  \<or> v \<in> VF' \<and> scalar2Nat (s v) \<le> NC" 
		by(cut_tac a1 a3, auto)
  
next 
  show "\<forall>v. v \<in> varOfSent (act ?r)\<longrightarrow>       
    v \<in> VF'\<longrightarrow> formEval (pre (?r)) s  \<longrightarrow> scalar2Nat (expEval (substExpByStatement (IVar v) (act ?r)) s) 
\<le> NC  \<longrightarrow> v \<in> varOfSent (act ?r')"
    	by(cut_tac a1 a3, auto)
next
  show "\<forall> v va. v \<in> varOfSent (act ?r') \<longrightarrow> 
  va\<in>varOfExp ( substExpByStatement (IVar v)  (act ?r')) \<longrightarrow>
   va \<in> VF \<or> (va \<in> VF' \<and> (scalar2Nat (s va))\<le> NC)  "
     apply(cut_tac a1 a3, auto) done
  
qed
lemma lemmaOnn_StoreLeNc_:
  assumes a1:"i\<le>NC & d\<le>NC"  and a3:"NC\<le>N" 
  shows "trans_sim_on3 (n_Store  i d) (n_Store  i d) VF VF' NC s" (is "trans_sim_on3 ?r ?r' VF VF' NC  s")
proof(rule ruleSimCond3)
     from a3 show " formEval (pre ?r) s \<longrightarrow>formEval (pre ?r') s" (is "?A \<longrightarrow>?B")  
       apply (auto simp del:evalEqn)done
   next 
	show "(\<forall>  v. v \<in>  varOfSent (act  ?r')  \<longrightarrow> formEval (pre ?r) s \<longrightarrow> 
    expEval (substExpByStatement (IVar v)  (act ?r')) s = expEval (substExpByStatement (IVar v)  (act ?r)) s)"
   proof(rule allI,(rule impI)+)
      fix  v
      assume b1:"formEval (pre ?r) s" and b2:"v \<in>varOfSent (act ?r')"
  
  show "expEval (substExpByStatement (IVar v)  (act ?r')) s = expEval (substExpByStatement (IVar v)  (act ?r)) s"  
       apply (cut_tac  a1 a3 b1 b2 ,auto) done
   qed
 next
   show "\<forall>  v. v \<in>  varOfSent (act ?r) \<longrightarrow>  v \<in> VF \<longrightarrow> v \<in>  varOfSent (act ?r')" 
		by(cut_tac a1 a3, auto)
 next
   from a1 show "\<forall>v. v \<in> varOfForm (pre (?r')) \<longrightarrow>
     formEval (pre (?r)) s  \<longrightarrow>
 v \<in> VF  \<or> v \<in> VF' \<and> scalar2Nat (s v) \<le> NC" 
		apply(cut_tac a1 a3, auto) done
  
next 
  show "\<forall>v. v \<in> varOfSent (act ?r)\<longrightarrow>
        v \<in> VF'\<longrightarrow>         
        formEval (pre (?r)) s \<longrightarrow>
       scalar2Nat (expEval (substExpByStatement (IVar v) (act ?r)) s) \<le> NC
       \<longrightarrow> v \<in> varOfSent (act ?r')"
    	apply(cut_tac a1 a3, auto) done
next
  show "\<forall> v va. v \<in> varOfSent (act ?r') \<longrightarrow> 
  va\<in>varOfExp ( substExpByStatement (IVar v)  (act ?r')) \<longrightarrow>
   va \<in> VF \<or> (va \<in> VF' \<and> (scalar2Nat (s va))\<le> NC)  "
     apply(cut_tac a1 a3, auto) done
qed
lemma lemmaOnn_Store: 
  assumes   a2:"s \<in> reachableSet (set (allInitSpecs N)) (rules N)"  and  
  a4:"\<forall>f.  f \<in>(set invariantsAbs) \<longrightarrow>  formEval f s" and a5:"\<exists> i d. i\<le>N\<and>d\<le>N\<and>r=n_Store  i d"  and
  a6:"NC \<le> N"
  shows "\<exists> r'. r' \<in> rules NC\<and> trans_sim_on3 r r' VF VF' NC s" (is "\<exists>r'.?P1 r' \<and> ?P2 r'")
proof -
  from a5 obtain i d where d0:"i\<le>N\<and>d\<le>N\<and>r=n_Store  i d"  by blast
  have "i>NC|i\<le> NC" by auto
  moreover{
       assume a1:"i>NC" 
        have "\<exists>r'. ?P1 r' \<and> ?P2 r'"
        proof(rule_tac x="(n_Store_i_3 d)" in exI,rule conjI)
          show  "?P1 (n_Store_i_3 d) " 
           by(cut_tac a1, auto) 
          next
          show  "?P2 (n_Store_i_3 d) "
           using lemmaOnn_StoreGt_i local.a1 a2 a4 a6 d0 by blast 
        qed
       }
moreover{
       assume a1:"i\<le> NC" 
        have "\<exists>r'. ?P1 r' \<and> ?P2 r'"
        proof(rule_tac x="(n_Store  i d)" in exI,rule conjI)
          show  "?P1 (n_Store  i d) " 
           by(cut_tac a1, auto) 
          next
          show  "?P2 (n_Store  i d) "
           using lemmaOnn_StoreLeNc_ local.a1 a2 a4 a6 d0 by blast 
        qed
       }
  ultimately show "\<exists>r'.?P1 r' \<and> ?P2 r'" 
    by satx
qed


end
