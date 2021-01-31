theory ABS_german_1
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
let s = (parallelList [(assign (Para (''Cache.State'') i, (Const E))), (assign (Para (''Cache.Data'') i, (IVar (Para (''Chan2.Data'') i)))), (assign (Para (''Chan2.Cmd'') i, (Const Empty)))]) in
guard g s"

definition n_RecvGntS2::"nat \<Rightarrow> rule" where [simp]:
"n_RecvGntS2  i\<equiv>
let g = (eqn (IVar (Para (''Chan2.Cmd'') i)) (Const GntS)) in
let s = (parallelList [(assign (Para (''Cache.State'') i, (Const S))), (assign (Para (''Cache.Data'') i, (IVar (Para (''Chan2.Data'') i)))), (assign (Para (''Chan2.Cmd'') i, (Const Empty)))]) in
guard g s"

definition n_SendGntE3::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_SendGntE3  i N\<equiv>
let g = (andList [(eqn (IVar (Ident ''CurCmd'')) (Const ReqE)) , (eqn (IVar (Ident ''CurPtr'')) (Const (index i))) , (eqn (IVar (Para (''Chan2.Cmd'') i)) (Const Empty)) , (eqn (IVar (Ident ''ExGntd'')) (Const false)) , (forallForm (down N) (\<lambda>j. (eqn (IVar (Para (''ShrSet'') j)) (Const false)) ))])in
let s = (parallelList [(assign (Para (''Chan2.Cmd'') i, (Const GntE))), (assign (Para (''Chan2.Data'') i, (IVar (Ident ''MemData'')))), (assign (Para (''ShrSet'') i, (Const true))), (assign ((Ident ''ExGntd''), (Const true))), (assign ((Ident ''CurCmd''), (Const Empty)))]) in
guard g s"

definition n_SendGntS4::"nat \<Rightarrow> rule" where [simp]:
"n_SendGntS4  i\<equiv>
let g = (andList [(eqn (IVar (Ident ''CurCmd'')) (Const ReqS)) , (eqn (IVar (Ident ''CurPtr'')) (Const (index i))) , (eqn (IVar (Para (''Chan2.Cmd'') i)) (Const Empty)) , (eqn (IVar (Ident ''ExGntd'')) (Const false)) ])in
let s = (parallelList [(assign (Para (''Chan2.Cmd'') i, (Const GntS))), (assign (Para (''Chan2.Data'') i, (IVar (Ident ''MemData'')))), (assign (Para (''ShrSet'') i, (Const true))), (assign ((Ident ''CurCmd''), (Const Empty)))]) in
guard g s"

definition n_RecvInvAck5::"nat \<Rightarrow> rule" where [simp]:
"n_RecvInvAck5  i\<equiv>
let g = (andList [(eqn (IVar (Para (''Chan3.Cmd'') i)) (Const InvAck)) , (eqn (IVar (Ident ''CurCmd !'')) (Const Empty)) , (eqn (IVar (Ident ''ExGntd'')) (Const true)) ])in
let s = (parallelList [(assign (Para (''Chan3.Cmd'') i, (Const Empty))), (assign (Para (''ShrSet'') i, (Const false))), (assign ((Ident ''ExGntd''), (Const false))), (assign ((Ident ''MemData''), (IVar (Para (''Chan3.Data'') i))))]) in
guard g s"

definition n_RecvInvAck6::"nat \<Rightarrow> rule" where [simp]:
"n_RecvInvAck6  i\<equiv>
let g = (andList [(eqn (IVar (Para (''Chan3.Cmd'') i)) (Const InvAck)) , (eqn (IVar (Ident ''CurCmd !'')) (Const Empty)) , (eqn (IVar (Ident ''ExGntd !'')) (Const true)) ])in
let s = (parallelList [(assign (Para (''Chan3.Cmd'') i, (Const Empty))), (assign (Para (''ShrSet'') i, (Const false)))]) in
guard g s"

definition n_SendInvAck7::"nat \<Rightarrow> rule" where [simp]:
"n_SendInvAck7  i\<equiv>
let g = (andList [(eqn (IVar (Para (''Chan2.Cmd'') i)) (Const Inv)) , (eqn (IVar (Para (''Chan3.Cmd'') i)) (Const Empty)) , (eqn (IVar (Para (''Cache.State'') i)) (Const E)) ])in
let s = (parallelList [(assign (Para (''Chan2.Cmd'') i, (Const Empty))), (assign (Para (''Chan3.Cmd'') i, (Const InvAck))), (assign (Para (''Chan3.Data'') i, (IVar (Para (''Cache.Data'') i)))), (assign (Para (''Cache.State'') i, (Const I)))]) in
guard g s"

definition n_SendInvAck8::"nat \<Rightarrow> rule" where [simp]:
"n_SendInvAck8  i\<equiv>
let g = (andList [(eqn (IVar (Para (''Chan2.Cmd'') i)) (Const Inv)) , (eqn (IVar (Para (''Chan3.Cmd'') i)) (Const Empty)) , (eqn (IVar (Para (''Cache.State !'') i)) (Const E)) ])in
let s = (parallelList [(assign (Para (''Chan2.Cmd'') i, (Const Empty))), (assign (Para (''Chan3.Cmd'') i, (Const InvAck))), (assign (Para (''Cache.State'') i, (Const I)))]) in
guard g s"

definition n_SendInv9::"nat \<Rightarrow> rule" where [simp]:
"n_SendInv9  i\<equiv>
let g = (andList [(eqn (IVar (Para (''Chan2.Cmd'') i)) (Const Empty)) , (eqn (IVar (Para (''InvSet'') i)) (Const true)) , (eqn (IVar (Ident ''CurCmd'')) (Const ReqE)) ])in
let s = (parallelList [(assign (Para (''Chan2.Cmd'') i, (Const Inv))), (assign (Para (''InvSet'') i, (Const false)))]) in
guard g s"

definition n_SendInv10::"nat \<Rightarrow> rule" where [simp]:
"n_SendInv10  i\<equiv>
let g = (andList [(eqn (IVar (Para (''Chan2.Cmd'') i)) (Const Empty)) , (eqn (IVar (Para (''InvSet'') i)) (Const true)) , (eqn (IVar (Ident ''CurCmd'')) (Const ReqS)) , (eqn (IVar (Ident ''ExGntd'')) (Const true)) ])in
let s = (parallelList [(assign (Para (''Chan2.Cmd'') i, (Const Inv))), (assign (Para (''InvSet'') i, (Const false)))]) in
guard g s"

definition n_RecvReqE11::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_RecvReqE11  i N\<equiv>
let g = (andList [(eqn (IVar (Ident ''CurCmd'')) (Const Empty)) , (eqn (IVar (Para (''Chan1.Cmd'') i)) (Const ReqE)) ])in
let s = (parallelList [(assign ((Ident ''CurCmd''), (Const ReqE))), (assign ((Ident ''CurPtr''), (Const (index i)))), (assign (Para (''Chan1.Cmd'') i, (Const Empty))), (parallelList (map (\<lambda>j. (assign (Para (''InvSet'') j, (IVar (Para (''ShrSet'') j))))) (down N)))]) in
guard g s"

definition n_RecvReqS12::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_RecvReqS12  i N\<equiv>
let g = (andList [(eqn (IVar (Ident ''CurCmd'')) (Const Empty)) , (eqn (IVar (Para (''Chan1.Cmd'') i)) (Const ReqS)) ])in
let s = (parallelList [(assign ((Ident ''CurCmd''), (Const ReqS))), (assign ((Ident ''CurPtr''), (Const (index i)))), (assign (Para (''Chan1.Cmd'') i, (Const Empty))), (parallelList (map (\<lambda>j. (assign (Para (''InvSet'') j, (IVar (Para (''ShrSet'') j))))) (down N)))]) in
guard g s"

definition n_SendReqE13::"nat \<Rightarrow> rule" where [simp]:
"n_SendReqE13  i\<equiv>
let g = (andList [(eqn (IVar (Para (''Chan1.Cmd'') i)) (Const Empty)) , (eqn (IVar (Para (''Cache.State'') i)) (Const I)) ])in
let s = (parallelList [(assign (Para (''Chan1.Cmd'') i, (Const ReqE)))]) in
guard g s"

definition n_SendReqE14::"nat \<Rightarrow> rule" where [simp]:
"n_SendReqE14  i\<equiv>
let g = (andList [(eqn (IVar (Para (''Chan1.Cmd'') i)) (Const Empty)) , (eqn (IVar (Para (''Cache.State'') i)) (Const S)) ])in
let s = (parallelList [(assign (Para (''Chan1.Cmd'') i, (Const ReqE)))]) in
guard g s"

definition n_SendReqS15::"nat \<Rightarrow> rule" where [simp]:
"n_SendReqS15  i\<equiv>
let g = (andList [(eqn (IVar (Para (''Chan1.Cmd'') i)) (Const Empty)) , (eqn (IVar (Para (''Cache.State'') i)) (Const I)) ])in
let s = (parallelList [(assign (Para (''Chan1.Cmd'') i, (Const ReqS)))]) in
guard g s"

definition n_Store16::"nat \<Rightarrow> rule" where [simp]:
"n_Store16  i\<equiv>
let g = (eqn (IVar (Para (''Cache.State'') i)) (Const E)) in
let s = (parallelList [(assign (Para (''Cache.Data'') i, (IVar(Ident ''d'')))), (assign ((Ident ''AuxData''), (IVar(Ident ''d''))))]) in
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
"initSpec0 N\<equiv> (andList (map (\<lambda>i. (eqn (IVar (Para (''Chan1.Cmd :'') i)) (Const Empty)) ) (down N) ))"

definition initSpec1::"nat \<Rightarrow> formula" where [simp]:
"initSpec1 N\<equiv> (andList (map (\<lambda>i. (eqn (IVar (Para (''Chan2.Cmd :'') i)) (Const Empty)) ) (down N) ))"

definition initSpec2::"nat \<Rightarrow> formula" where [simp]:
"initSpec2 N\<equiv> (andList (map (\<lambda>i. (eqn (IVar (Para (''Chan3.Cmd :'') i)) (Const Empty)) ) (down N) ))"

definition initSpec3::"nat \<Rightarrow> formula" where [simp]:
"initSpec3 N\<equiv> (andList (map (\<lambda>i. (eqn (IVar (Para (''Cache.State :'') i)) (Const I)) ) (down N) ))"

definition initSpec4::"nat \<Rightarrow> formula" where [simp]:
"initSpec4 N\<equiv> (andList (map (\<lambda>i. (eqn (IVar (Para (''InvSet'') i)) (Const false)) ) (down N) ))"

definition initSpec5::"nat \<Rightarrow> formula" where [simp]:
"initSpec5 N\<equiv> (andList (map (\<lambda>i. (eqn (IVar (Para (''ShrSet'') i)) (Const false)) ) (down N) ))"

definition initSpec6::"nat \<Rightarrow> formula" where [simp]:
"initSpec6 N \<equiv> (eqn (IVar (Ident ''ExGntd :'')) (Const false)) "

definition initSpec7::"nat \<Rightarrow> formula" where [simp]:
"initSpec7 N \<equiv> (eqn (IVar (Ident ''CurCmd :'')) (Const Empty)) "

definition initSpec8::"nat \<Rightarrow> formula" where [simp]:
"initSpec8 N \<equiv> (eqn (IVar (Ident ''MemData :'')) (IVar(Ident ''d''))) "

definition initSpec9::"nat \<Rightarrow> formula" where [simp]:
"initSpec9 N \<equiv> (eqn (IVar (Ident ''AuxData :'')) (IVar(Ident ''d''))) "

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


definition inv_0 :: "nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
	"inv_0 i j \<equiv>
		implyForm (andList [(neg (eqn (Const (index i)) (Const (index j)))), (eqn (IVar (Para (''Chan2.Cmd'') i)) (Const Inv)) , (eqn (IVar (Para (''Cache.State!'') i)) (Const E)) ])
(eqn (IVar (Ident ''ExGntd'')) (Const false)) "

definition inv_1 :: "nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
	"inv_1 i j \<equiv>
		implyForm (andForm (neg (eqn (Const (index i)) (Const (index j)))) (eqn (IVar (Para (''Cache.State'') i)) (Const S)) )
(eqn (IVar (Ident ''MemData'')) (IVar (Ident ''AuxData''))) "

definition inv_2 :: "nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
	"inv_2 i j \<equiv>
		implyForm (andForm (neg (eqn (Const (index i)) (Const (index j)))) (eqn (IVar (Para (''Chan2.Cmd'') i)) (Const GntS)) )
(eqn (IVar (Ident ''ExGntd'')) (Const false)) "

definition inv_3 :: "nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
	"inv_3 i j \<equiv>
		implyForm (andList [(neg (eqn (Const (index i)) (Const (index j)))), (eqn (IVar (Para (''Chan2.Cmd'') i)) (Const Inv)) , (eqn (IVar (Para (''Cache.State!'') i)) (Const E)) ])
(eqn (IVar (Ident ''CurCmd!'')) (Const ReqS)) "

definition inv_4 :: "nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
	"inv_4 i j \<equiv>
		implyForm (andForm (neg (eqn (Const (index i)) (Const (index j)))) (eqn (IVar (Para (''Chan2.Cmd'') i)) (Const GntE)) )
(eqn (IVar (Ident ''ExGntd'')) (Const true)) "

definition inv_5 :: "nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
	"inv_5 i j \<equiv>
		implyForm (andList [(neg (eqn (Const (index i)) (Const (index j)))), (eqn (IVar (Ident ''ExGntd'')) (Const true)) , (eqn (IVar (Para (''Chan3.Cmd'') i)) (Const InvAck)) ])
(eqn (IVar (Para (''Chan3.Data'') i)) (IVar (Ident ''AuxData''))) "

definition inv_6 :: "nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
	"inv_6 i j \<equiv>
		implyForm (andList [(neg (eqn (Const (index i)) (Const (index j)))), (eqn (IVar (Para (''Chan2.Cmd'') i)) (Const Inv)) , (eqn (IVar (Para (''Cache.State!'') i)) (Const E)) ])
(eqn (IVar (Ident ''MemData'')) (IVar (Ident ''AuxData''))) "

definition inv_7 :: "nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
	"inv_7 i j \<equiv>
		implyForm (andList [(neg (eqn (Const (index i)) (Const (index j)))), (eqn (IVar (Para (''InvSet'') i)) (Const true)) , (eqn (IVar (Ident ''ExGntd'')) (Const true)) ])
(eqn (IVar (Ident ''CurCmd!'')) (Const Empty)) "

definition inv_8 :: "nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
	"inv_8 i j \<equiv>
		implyForm (andForm (neg (eqn (Const (index i)) (Const (index j)))) (eqn (IVar (Para (''Cache.State'') i)) (Const S)) )
(eqn (IVar (Ident ''ExGntd'')) (Const false)) "

definition inv_9 :: "nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
	"inv_9 i j \<equiv>
		implyForm (andForm (neg (eqn (Const (index i)) (Const (index j)))) (eqn (IVar (Para (''Chan2.Cmd'') i)) (Const Inv)) )
(eqn (IVar (Ident ''CurCmd!'')) (Const Empty)) "

definition inv_10 :: "nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
	"inv_10 i j \<equiv>
		implyForm (andForm (neg (eqn (Const (index i)) (Const (index j)))) (eqn (IVar (Para (''Chan2.Cmd'') i)) (Const GntE)) )
(eqn (IVar (Ident ''MemData'')) (IVar (Ident ''AuxData''))) "

definition inv_11 :: "nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
	"inv_11 i j \<equiv>
		implyForm (andForm (neg (eqn (Const (index i)) (Const (index j)))) (eqn (IVar (Para (''Cache.State'') i)) (Const E)) )
(eqn (IVar (Ident ''ExGntd'')) (Const true)) "

definition inv_12 :: "nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
	"inv_12 i j \<equiv>
		implyForm (andForm (neg (eqn (Const (index i)) (Const (index j)))) (eqn (IVar (Para (''Chan2.Cmd'') i)) (Const GntS)) )
(eqn (IVar (Ident ''MemData'')) (IVar (Ident ''AuxData''))) "

definition inv_13 :: "nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
	"inv_13 i j \<equiv>
		implyForm (andList [(neg (eqn (Const (index i)) (Const (index j)))), (eqn (IVar (Para (''Chan2.Cmd'') i)) (Const Inv)) , (eqn (IVar (Para (''Cache.State!'') i)) (Const E)) ])
(eqn (IVar (Ident ''CurCmd'')) (Const ReqE)) "

definition inv_14 :: "nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
	"inv_14 i j \<equiv>
		implyForm (andForm (neg (eqn (Const (index i)) (Const (index j)))) (eqn (IVar (Para (''Chan3.Cmd'') i)) (Const InvAck)) )
(eqn (IVar (Para (''Cache.State !'') j)) (Const E)) "

definition inv_15 :: "nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
	"inv_15 i j \<equiv>
		implyForm (andForm (neg (eqn (Const (index i)) (Const (index j)))) (eqn (IVar (Para (''InvSet'') i)) (Const true)) )
(eqn (IVar (Para (''Cache.State !'') j)) (Const E)) "

definition inv_16 :: "nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
	"inv_16 i j \<equiv>
		implyForm (andList [(neg (eqn (Const (index i)) (Const (index j)))), (eqn (IVar (Para (''InvSet'') i)) (Const true)) , (eqn (IVar (Ident ''CurCmd'')) (Const ReqS)) ])
(eqn (IVar (Para (''Chan3.Cmd'') j)) (Const Empty)) "

definition inv_17 :: "nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
	"inv_17 i j \<equiv>
		implyForm (andList [(neg (eqn (Const (index i)) (Const (index j)))), (eqn (IVar (Para (''InvSet'') i)) (Const true)) , (eqn (IVar (Ident ''ExGntd'')) (Const true)) ])
(eqn (IVar (Para (''Cache.State'') j)) (Const I)) "

definition inv_18 :: "nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
	"inv_18 i j \<equiv>
		implyForm (andForm (neg (eqn (Const (index i)) (Const (index j)))) (eqn (IVar (Para (''Cache.State'') i)) (Const E)) )
(eqn (IVar (Para (''Chan2.Cmd'') j)) (Const Empty)) "

definition inv_19 :: "nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
	"inv_19 i j \<equiv>
		implyForm (andList [(neg (eqn (Const (index i)) (Const (index j)))), (eqn (IVar (Para (''InvSet'') i)) (Const true)) , (eqn (IVar (Ident ''ExGntd'')) (Const true)) ])
(eqn (IVar (Para (''InvSet'') j)) (Const false)) "

definition inv_20 :: "nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
	"inv_20 i j \<equiv>
		implyForm (andForm (neg (eqn (Const (index i)) (Const (index j)))) (eqn (IVar (Para (''Chan2.Cmd'') i)) (Const GntE)) )
(eqn (IVar (Para (''InvSet'') j)) (Const false)) "

definition inv_21 :: "nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
	"inv_21 i j \<equiv>
		implyForm (andForm (neg (eqn (Const (index i)) (Const (index j)))) (eqn (IVar (Para (''Cache.State'') i)) (Const E)) )
(eqn (IVar (Para (''Cache.State !'') j)) (Const S)) "

definition inv_22 :: "nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
	"inv_22 i j \<equiv>
		implyForm (andList [(neg (eqn (Const (index i)) (Const (index j)))), (eqn (IVar (Para (''InvSet'') i)) (Const true)) , (eqn (IVar (Ident ''ExGntd'')) (Const true)) ])
(eqn (IVar (Para (''ShrSet'') j)) (Const false)) "

definition inv_23 :: "nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
	"inv_23 i j \<equiv>
		implyForm (andForm (neg (eqn (Const (index i)) (Const (index j)))) (eqn (IVar (Para (''Chan2.Cmd'') i)) (Const GntE)) )
(eqn (IVar (Para (''Cache.State !'') j)) (Const E)) "

definition inv_24 :: "nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
	"inv_24 i j \<equiv>
		implyForm (andForm (neg (eqn (Const (index i)) (Const (index j)))) (eqn (IVar (Para (''Cache.State'') i)) (Const E)) )
(eqn (IVar (Para (''Cache.State'') j)) (Const I)) "

definition inv_25 :: "nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
	"inv_25 i j \<equiv>
		implyForm (andForm (neg (eqn (Const (index i)) (Const (index j)))) (eqn (IVar (Para (''Cache.State'') i)) (Const E)) )
(eqn (IVar (Para (''Chan2.Cmd !'') j)) (Const GntS)) "

definition inv_26 :: "nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
	"inv_26 i j \<equiv>
		implyForm (andForm (neg (eqn (Const (index i)) (Const (index j)))) (eqn (IVar (Para (''Chan2.Cmd'') i)) (Const GntE)) )
(eqn (IVar (Para (''Chan2.Cmd'') j)) (Const Empty)) "

definition inv_27 :: "nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
	"inv_27 i j \<equiv>
		implyForm (andList [(neg (eqn (Const (index i)) (Const (index j)))), (eqn (IVar (Ident ''ExGntd'')) (Const true)) , (eqn (IVar (Para (''Chan3.Cmd'') i)) (Const InvAck)) ])
(eqn (IVar (Para (''Cache.State'') j)) (Const I)) "

definition inv_28 :: "nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
	"inv_28 i j \<equiv>
		implyForm (andForm (neg (eqn (Const (index i)) (Const (index j)))) (eqn (IVar (Para (''Chan2.Cmd'') i)) (Const GntE)) )
(eqn (IVar (Para (''Chan2.Cmd !'') j)) (Const GntS)) "

definition inv_29 :: "nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
	"inv_29 i j \<equiv>
		implyForm (andList [(neg (eqn (Const (index i)) (Const (index j)))), (eqn (IVar (Para (''InvSet'') i)) (Const true)) , (eqn (IVar (Ident ''ExGntd'')) (Const true)) ])
(eqn (IVar (Para (''Chan3.Cmd'') j)) (Const Empty)) "

definition inv_30 :: "nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
	"inv_30 i j \<equiv>
		implyForm (andForm (neg (eqn (Const (index i)) (Const (index j)))) (eqn (IVar (Para (''Chan2.Cmd'') i)) (Const GntE)) )
(eqn (IVar (Para (''Chan3.Cmd !'') j)) (Const InvAck)) "

definition inv_31 :: "nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
	"inv_31 i j \<equiv>
		implyForm (andForm (neg (eqn (Const (index i)) (Const (index j)))) (eqn (IVar (Para (''InvSet'') i)) (Const true)) )
(eqn (IVar (Para (''Chan2.Cmd !'') j)) (Const GntE)) "

definition inv_32 :: "nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
	"inv_32 i j \<equiv>
		implyForm (andForm (neg (eqn (Const (index i)) (Const (index j)))) (eqn (IVar (Para (''Cache.State'') i)) (Const E)) )
(eqn (IVar (Para (''InvSet'') j)) (Const false)) "

definition inv_33 :: "nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
	"inv_33 i j \<equiv>
		implyForm (andList [(neg (eqn (Const (index i)) (Const (index j)))), (eqn (IVar (Para (''InvSet'') i)) (Const true)) , (eqn (IVar (Ident ''ExGntd'')) (Const true)) ])
(eqn (IVar (Para (''Chan2.Cmd'') j)) (Const Empty)) "

definition inv_34 :: "nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
	"inv_34 i j \<equiv>
		implyForm (andForm (neg (eqn (Const (index i)) (Const (index j)))) (eqn (IVar (Para (''Cache.State'') i)) (Const S)) )
(eqn (IVar (Para (''Chan2.Cmd !'') j)) (Const GntE)) "

definition inv_35 :: "nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
	"inv_35 i j \<equiv>
		implyForm (andList [(neg (eqn (Const (index i)) (Const (index j)))), (eqn (IVar (Ident ''ExGntd'')) (Const true)) , (eqn (IVar (Para (''Chan3.Cmd'') i)) (Const InvAck)) ])
(eqn (IVar (Para (''Chan3.Cmd'') j)) (Const Empty)) "

definition inv_36 :: "nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
	"inv_36 i j \<equiv>
		implyForm (andForm (neg (eqn (Const (index i)) (Const (index j)))) (eqn (IVar (Para (''Chan2.Cmd'') i)) (Const Inv)) )
(eqn (IVar (Para (''Chan2.Cmd !'') j)) (Const GntE)) "

definition inv_37 :: "nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
	"inv_37 i j \<equiv>
		implyForm (andForm (neg (eqn (Const (index i)) (Const (index j)))) (eqn (IVar (Para (''Chan2.Cmd'') i)) (Const GntE)) )
(eqn (IVar (Para (''Chan3.Cmd'') j)) (Const Empty)) "

definition inv_38 :: "nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
	"inv_38 i j \<equiv>
		implyForm (andForm (neg (eqn (Const (index i)) (Const (index j)))) (eqn (IVar (Para (''Cache.State'') i)) (Const E)) )
(eqn (IVar (Para (''Chan3.Cmd'') j)) (Const Empty)) "

definition inv_39 :: "nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
	"inv_39 i j \<equiv>
		implyForm (andForm (neg (eqn (Const (index i)) (Const (index j)))) (eqn (IVar (Para (''Chan2.Cmd'') i)) (Const GntE)) )
(eqn (IVar (Para (''ShrSet'') j)) (Const false)) "

definition inv_40 :: "nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
	"inv_40 i j \<equiv>
		implyForm (andForm (neg (eqn (Const (index i)) (Const (index j)))) (eqn (IVar (Para (''Cache.State'') i)) (Const S)) )
(eqn (IVar (Para (''Cache.State !'') j)) (Const E)) "

definition inv_41 :: "nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
	"inv_41 i j \<equiv>
		implyForm (andList [(neg (eqn (Const (index i)) (Const (index j)))), (eqn (IVar (Ident ''ExGntd'')) (Const true)) , (eqn (IVar (Para (''Chan3.Cmd'') i)) (Const InvAck)) ])
(eqn (IVar (Para (''Chan2.Cmd'') j)) (Const Empty)) "

definition inv_42 :: "nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
	"inv_42 i j \<equiv>
		implyForm (andList [(neg (eqn (Const (index i)) (Const (index j)))), (eqn (IVar (Para (''InvSet'') i)) (Const true)) , (eqn (IVar (Ident ''CurCmd'')) (Const ReqS)) ])
(eqn (IVar (Para (''Chan2.Cmd !'') j)) (Const Inv)) "

definition inv_43 :: "nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
	"inv_43 i j \<equiv>
		implyForm (andList [(neg (eqn (Const (index i)) (Const (index j)))), (eqn (IVar (Ident ''ExGntd'')) (Const true)) , (eqn (IVar (Para (''Chan3.Cmd'') i)) (Const InvAck)) ])
(eqn (IVar (Para (''InvSet'') j)) (Const false)) "

definition inv_44 :: "nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
	"inv_44 i j \<equiv>
		implyForm (andForm (neg (eqn (Const (index i)) (Const (index j)))) (eqn (IVar (Para (''Chan2.Cmd'') i)) (Const Inv)) )
(eqn (IVar (Para (''Cache.State !'') j)) (Const E)) "

definition inv_45 :: "nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
	"inv_45 i j \<equiv>
		implyForm (andList [(neg (eqn (Const (index i)) (Const (index j)))), (eqn (IVar (Para (''InvSet'') i)) (Const true)) , (eqn (IVar (Ident ''ExGntd'')) (Const true)) ])
(eqn (IVar (Para (''Chan3.Cmd !'') j)) (Const InvAck)) "

definition inv_46 :: "nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
	"inv_46 i j \<equiv>
		implyForm (andForm (neg (eqn (Const (index i)) (Const (index j)))) (eqn (IVar (Para (''Chan2.Cmd'') i)) (Const GntS)) )
(eqn (IVar (Para (''Cache.State !'') j)) (Const E)) "

definition inv_47 :: "nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
	"inv_47 i j \<equiv>
		implyForm (andList [(neg (eqn (Const (index i)) (Const (index j)))), (eqn (IVar (Ident ''ExGntd'')) (Const true)) , (eqn (IVar (Para (''Chan3.Cmd'') i)) (Const InvAck)) ])
(eqn (IVar (Para (''ShrSet'') j)) (Const false)) "

definition inv_48 :: "nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
	"inv_48 i j \<equiv>
		implyForm (andForm (neg (eqn (Const (index i)) (Const (index j)))) (eqn (IVar (Para (''Chan3.Cmd'') i)) (Const InvAck)) )
(eqn (IVar (Para (''Chan2.Cmd !'') j)) (Const GntE)) "

definition inv_49 :: "nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
	"inv_49 i j \<equiv>
		implyForm (andForm (neg (eqn (Const (index i)) (Const (index j)))) (eqn (IVar (Para (''Chan2.Cmd'') i)) (Const GntS)) )
(eqn (IVar (Para (''Chan2.Cmd !'') j)) (Const GntE)) "

definition inv_50 :: "nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
	"inv_50 i j \<equiv>
		implyForm (andList [(neg (eqn (Const (index i)) (Const (index j)))), (eqn (IVar (Para (''InvSet'') i)) (Const true)) , (eqn (IVar (Ident ''CurCmd'')) (Const ReqS)) ])
(eqn (IVar (Para (''Chan3.Cmd !'') j)) (Const InvAck)) "

definition inv_51 :: "nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
	"inv_51 i j \<equiv>
		implyForm (andForm (neg (eqn (Const (index i)) (Const (index j)))) (eqn (IVar (Para (''Chan2.Cmd'') i)) (Const GntE)) )
(eqn (IVar (Para (''Cache.State !'') j)) (Const S)) "

definition inv_52 :: "nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
	"inv_52 i j \<equiv>
		implyForm (andForm (neg (eqn (Const (index i)) (Const (index j)))) (eqn (IVar (Para (''Cache.State'') i)) (Const E)) )
(eqn (IVar (Para (''Chan3.Cmd !'') j)) (Const InvAck)) "

definition inv_53 :: "nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
	"inv_53 i j \<equiv>
		implyForm (andList [(neg (eqn (Const (index i)) (Const (index j)))), (eqn (IVar (Ident ''ExGntd'')) (Const true)) , (eqn (IVar (Para (''Chan3.Cmd'') i)) (Const InvAck)) ])
(eqn (IVar (Para (''Chan3.Cmd !'') j)) (Const InvAck)) "

definition inv_54 :: "nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
	"inv_54 i j \<equiv>
		implyForm (andForm (neg (eqn (Const (index i)) (Const (index j)))) (eqn (IVar (Para (''Cache.State'') i)) (Const E)) )
(eqn (IVar (Para (''ShrSet'') j)) (Const false)) "

definition inv_55 :: "nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
	"inv_55 i j \<equiv>
		implyForm (andList [(neg (eqn (Const (index i)) (Const (index j)))), (eqn (IVar (Ident ''ExGntd'')) (Const true)) , (eqn (IVar (Para (''Chan3.Cmd'') i)) (Const InvAck)) ])
(eqn (IVar (Para (''Chan2.Cmd !'') j)) (Const Inv)) "

definition inv_56 :: "nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
	"inv_56 i j \<equiv>
		implyForm (andForm (neg (eqn (Const (index i)) (Const (index j)))) (eqn (IVar (Para (''Cache.State'') i)) (Const E)) )
(eqn (IVar (Para (''Chan2.Cmd !'') j)) (Const Inv)) "

definition inv_57 :: "nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
	"inv_57 i j \<equiv>
		implyForm (andForm (neg (eqn (Const (index i)) (Const (index j)))) (eqn (IVar (Para (''Chan2.Cmd'') i)) (Const GntE)) )
(eqn (IVar (Para (''Cache.State'') j)) (Const I)) "

definition inv_58 :: "nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
	"inv_58 i j \<equiv>
		implyForm (andForm (neg (eqn (Const (index i)) (Const (index j)))) (eqn (IVar (Para (''Cache.State'') i)) (Const E)) )
(eqn (IVar (Para (''Chan2.Cmd !'') j)) (Const GntE)) "

definition inv_59 :: "nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
	"inv_59 i j \<equiv>
		implyForm (andForm (neg (eqn (Const (index i)) (Const (index j)))) (eqn (IVar (Para (''Chan2.Cmd'') i)) (Const GntE)) )
(eqn (IVar (Para (''Chan2.Cmd !'') j)) (Const GntE)) "

definition inv_60 :: "nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
	"inv_60 i j \<equiv>
		implyForm (andList [(neg (eqn (Const (index i)) (Const (index j)))), (eqn (IVar (Para (''InvSet'') i)) (Const true)) , (eqn (IVar (Ident ''ExGntd'')) (Const true)) ])
(eqn (IVar (Para (''Chan2.Cmd !'') j)) (Const Inv)) "

definition inv_61 :: "nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
	"inv_61 i j \<equiv>
		implyForm (andForm (neg (eqn (Const (index i)) (Const (index j)))) (eqn (IVar (Para (''Chan2.Cmd'') i)) (Const GntE)) )
(eqn (IVar (Para (''Chan2.Cmd !'') j)) (Const Inv)) "

definition inv_62 :: "nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
	"inv_62 i j \<equiv>
		implyForm (andForm (neg (eqn (Const (index i)) (Const (index j)))) (eqn (IVar (Para (''Cache.State'') i)) (Const E)) )
(eqn (IVar (Para (''Cache.State !'') j)) (Const E)) "

subsection{*Definitions of each abstracted rule*}

definition  NC::"nat " where [simp]: "NC==1"

definition n_SendGntE3_i::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_SendGntE3_i  i N\<equiv>
let g = (andList [(eqn (IVar (Ident ''CurCmd'')) (Const ReqE)) , (eqn (IVar (Ident ''CurPtr'')) (IVar (Ident '' Other''))) , (eqn (IVar (Ident ''ExGntd'')) (Const false)) , (forallForm (down N) (\<lambda>j. (eqn (IVar (Para (''ShrSet'') i)) (Const false)) ))])in
let s = (parallelList [(assign ((Ident ''ExGntd''), (Const true ))), (assign ((Ident ''	CurCmd''), (Const Empty)))]) in
guard g s"

definition n_SendGntS4_i::"nat \<Rightarrow> rule" where [simp]:
"n_SendGntS4_i  i\<equiv>
let g = (andList [(eqn (IVar (Ident ''CurCmd'')) (Const ReqS)) , (eqn (IVar (Ident ''CurPtr'')) (IVar (Ident '' Other''))) , (eqn (IVar (Ident ''ExGntd'')) (Const false)) ])in
let s = (parallelList [(assign ((Ident ''CurCmd''), (Const Empty)))]) in
guard g s"

definition n_RecvInvAck5_i::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_RecvInvAck5_i  i N\<equiv>
let g = (andList [(eqn (IVar (Ident ''CurCmd !'')) (Const Empty)) , (eqn (IVar (Ident ''ExGntd'')) (Const true)) , (forallForm (down N) (\<lambda>j. (eqn (IVar (Para (''InvSet'') i)) (Const false)) )), (eqn (IVar (Para (''ShrSet'') i)) (Const false)) , (eqn (IVar (Para (''Chan3.Cmd'') i)) (Const Empty)) , (eqn (IVar (Para (''Chan2.Cmd !'') i)) (Const Inv)) , (eqn (IVar (Para (''Chan3.Cmd !'') i)) (Const InvAck)) , (eqn (IVar (Para (''Chan2.Cmd'') i)) (Const Empty)) , (eqn (IVar (Para (''Cache.State !'') i)) (Const E)) , (eqn (IVar (Para (''Cache.State'') i)) (Const I)) , (eqn (IVar (Para (''Chan2.Cmd !'') i)) (Const GntE)) ])in
let s = (parallelList [(assign ((Ident ''ExGntd''), (Const false ))), (assign ((Ident ''	MemData''), (IVar (Ident ''AuxData''))))]) in
guard g s"

definition n_RecvReqE11_i::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_RecvReqE11_i  i N\<equiv>
let g = (eqn (IVar (Ident ''CurCmd'')) (Const Empty)) in
let s = (parallelList [(assign ((Ident ''CurCmd''), (Const ReqE ))), (assign ((Ident ''	CurPtr''), (IVar (Ident '' Other'')))), (parallelList (map (\<lambda>j. (assign (Para (''		InvSet'') i, (IVar (Para (''ShrSet'') i))))) (down N)))]) in
guard g s"

definition n_RecvReqS12_i::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_RecvReqS12_i  i N\<equiv>
let g = (eqn (IVar (Ident ''CurCmd'')) (Const Empty)) in
let s = (parallelList [(assign ((Ident ''CurCmd''), (Const ReqS ))), (assign ((Ident ''	CurPtr''), (IVar (Ident '' Other'')))), (parallelList (map (\<lambda>j. (assign (Para (''		InvSet'') i, (IVar (Para (''ShrSet'') i))))) (down N)))]) in
guard g s"

definition n_Store16_i::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_Store16_i  i N\<equiv>
let g = (andList [(forallForm (down N) (\<lambda>j. (eqn (IVar (Para (''InvSet'') i)) (Const false)) )), (eqn (IVar (Para (''ShrSet'') i)) (Const false)) , (eqn (IVar (Para (''Chan3.Cmd'') i)) (Const Empty)) , (eqn (IVar (Para (''Chan2.Cmd !'') i)) (Const Inv)) , (eqn (IVar (Para (''Chan2.Cmd !'') i)) (Const GntS)) , (eqn (IVar (Para (''Chan3.Cmd !'') i)) (Const InvAck)) , (eqn (IVar (Para (''Cache.State !'') i)) (Const S)) , (eqn (IVar (Para (''Chan2.Cmd'') i)) (Const Empty)) , (eqn (IVar (Para (''Cache.State !'') i)) (Const E)) , (eqn (IVar (Para (''Cache.State'') i)) (Const I)) , (eqn (IVar (Ident ''ExGntd'')) (Const true)) , (eqn (IVar (Para (''Chan2.Cmd !'') i)) (Const GntE)) ])in
let s = (parallelList [(assign ((Ident ''AuxData''), (IVar (Ident ''['DATA_1']''))))]) in
guard g s"



end