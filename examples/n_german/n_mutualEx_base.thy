(*  Title:      HOL/Auth/n_mutualEx_base.thy
    Author:     Yongjian Li and Kaiqiang Duan, State Key Lab of Computer Science, Institute of Software, Chinese Academy of Sciences
    Copyright    2016 State Key Lab of Computer Science, Institute of Software, Chinese Academy of Sciences
*)

(*header{*The n_mutualEx Protocol Case Study*} *)

theory n_mutualEx_base imports paraTheoryCmpzb
begin

section{*Main definitions*}

subsection{* Definitions of Constants*}
definition I::"scalrValueType" where [simp]: "I\<equiv> enum ''control'' ''I''"
definition T::"scalrValueType" where [simp]: "T\<equiv> enum ''control'' ''T''"
definition C::"scalrValueType" where [simp]: "C\<equiv> enum ''control'' ''C''"
definition E::"scalrValueType" where [simp]: "E\<equiv> enum ''control'' ''E''"
definition true::"scalrValueType" where [simp]: "true\<equiv> boolV True"
definition false::"scalrValueType" where [simp]: "false\<equiv> boolV False"



subsection{*  Definitions of Parameterized Rules *}

definition  NC::"nat " where [simp]: "NC==1"

 definition VF::"varType set" where [simp]: 
"VF \<equiv>{(Para ( ''n'') 0),(Para ( ''n'') 1),(Ident ''x'')}"
definition n_Try::"nat \<Rightarrow> rule" where [simp]:
"n_Try  i\<equiv>
let g = (eqn (IVar (Para ( ''n'') i)) (Const I)) in
let s = (parallelList [(assign ((Para ( ''n'') i), (Const T)))]) in
guard g s"

definition n_Crit::"nat \<Rightarrow> rule" where [simp]:
"n_Crit  i\<equiv>
let g = (andForm (eqn (IVar (Para ( ''n'') i)) (Const T)) (eqn (IVar (Ident ''x'')) (Const true))) in
let s = (parallelList [(assign ((Para ( ''n'') i), (Const C))), (assign ((Ident ''x''), (Const false)))]) in
guard g s"

definition n_Exit::"nat \<Rightarrow> rule" where [simp]:
"n_Exit  i\<equiv>
let g = (eqn (IVar (Para ( ''n'') i)) (Const C)) in
let s = (parallelList [(assign ((Para ( ''n'') i), (Const E)))]) in
guard g s"

definition n_Idle::"nat \<Rightarrow> rule" where [simp]:
"n_Idle  i\<equiv>
let g = (eqn (IVar (Para ( ''n'') i)) (Const E)) in
let s = (parallelList [(assign ((Para ( ''n'') i), (Const I))), (assign ((Ident ''x''), (Const true)))]) in
guard g s"

definition n_Crit_i_3::"rule" where [simp]:
"n_Crit_i_3  \<equiv>
let g = (eqn (IVar (Ident ''x'')) (Const true)) in
let s = (parallelList [(assign ((Ident ''x''), (Const false)))]) in
guard g s"

definition n_Idle_i_3::"rule" where [simp]:
"n_Idle_i_3  \<equiv>
let g = (andForm (andForm (eqn (IVar (Ident ''x'')) (Const false)) 
(forallForm (down NC) (\<lambda>j. (neg (eqn (IVar (Para ( ''n'') j)) (Const E))))))
 (forallForm (down NC) (\<lambda>j. (neg (eqn (IVar (Para ( ''n'') j)) (Const C)))))) in
let s = (parallelList [(assign ((Ident ''x''), (Const true)))]) in
guard g s"

definition n_Idle_i_3PP::"nat \<Rightarrow> rule" where [simp]:
"n_Idle_i_3PP i \<equiv>
let g = andForm (eqn (IVar (Para ( ''n'') i)) (Const E)) (andForm (andForm (eqn (IVar (Ident ''x'')) (Const false)) 
(forallForm (down NC) (\<lambda>j. (neg (eqn (IVar (Para ( ''n'') j)) (Const E))))))
 (forallForm (down NC) (\<lambda>j. (neg (eqn (IVar (Para ( ''n'') j)) (Const C)))))) in
let s = (parallelList [(assign ((Ident ''x''), (Const true)))]) in
guard g s"

subsection{*The set of All actual Rules w.r.t. a Protocol Instance with Size $N$*}
definition rules::"nat \<Rightarrow> rule set" where [simp]:
"rules N \<equiv> {r.
(\<exists> i. i\<le>N\<and>r=n_Try  i) \<or>
(\<exists> i. i\<le>N\<and>r=n_Crit  i) \<or>
(\<exists> i. i\<le>N\<and>r=n_Exit  i) \<or>
(\<exists> i. i\<le>N\<and>r=n_Idle  i) \<or>
(r=n_Crit_i_3  ) \<or>
(r=n_Idle_i_3  )\<or> r=skipRule
}"



subsection{*Definitions of a Formally Parameterized Invariant Formulas*}

definition inv_27::"nat \<Rightarrow> formula" where [simp]:
"inv_27 i \<equiv>
(implyForm (eqn (IVar (Para ( ''n'') i)) (Const E)) (eqn (IVar (Ident ''x'')) (Const false)))"

definition inv_7::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv_7 i j \<equiv>
(implyForm (neg (eqn (Const (index i)) (Const (index j)))) (implyForm (eqn (IVar (Para ( ''n'') i)) (Const E)) (neg (eqn (IVar (Para ( ''n'') j)) (Const E)))))"

definition inv_5::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv_5 i j \<equiv>
(implyForm (neg (eqn (Const (index i)) (Const (index j)))) (implyForm (eqn (IVar (Para ( ''n'') i)) (Const E)) (neg (eqn (IVar (Para ( ''n'') j)) (Const C)))))"

subsection{*Definitions of  the Set of Invariant Formula Instances in a $N$-protocol Instance*}
definition invariants::"nat \<Rightarrow> formula set" where [simp]:
"invariants N \<equiv> {f.
(\<exists> i. i\<le>N\<and>f=inv_27  i) \<or>
(\<exists> i j. i\<le>N\<and>j\<le>N\<and>i~=j\<and>f=inv_7  i j) \<or>
(\<exists> i j. i\<le>N\<and>j\<le>N\<and>i~=j\<and>f=inv_5  i j)
}" 

subsection{*Definitions of  the Set of Abs Invariant Formula Instances *}
definition invariantsAbs  ::"  formula list" where [simp]:
"invariantsAbs   \<equiv> [
inv_27 0 ,
inv_7 0 1 ,
inv_7 1 0 ,
inv_5 0 1 ,
inv_5 1 0
]"

definition initSpec0::"nat \<Rightarrow> formula" where [simp]:
"initSpec0 N \<equiv> (forallForm (down N) (% i . (eqn (IVar (Para ( ''n'') i)) (Const I))))"

definition initSpec1::"formula" where [simp]:
"initSpec1  \<equiv> (eqn (IVar (Ident ''x'')) (Const true))"

definition allInitSpecs::"nat \<Rightarrow> formula list" where [simp]:
"allInitSpecs N \<equiv> [
(initSpec0 N),
(initSpec1 )
]"
axiomatization  where axiomOnf2 [simp,intro]:
   "s ∈ reachableSet (set (allInitSpecs N )) (rules N) ⟹  1 < N ⟹ 1 < i ⟹ j<2 ⟹  formEval (f 0 1) s ⟹ formEval (f i j) s"

axiomatization  where axiomOnf1 [simp,intro]:
   "s ∈ reachableSet (set (allInitSpecs N )) (rules N) ⟹ 1 < N ⟹ 1 < i ⟹formEval (f 0 ) s ⟹ formEval (f i) s"




subsection{*Definitions of initial states*}

lemma lemmaOnn_TryGt_i:
  assumes a1:"NC<i" and a2:"s ∈ reachableSet (set (allInitSpecs N)) (rules N)"  and  
  a4:"∀f.  f ∈(set invariantsAbs) ⟶  formEval f s" 
shows "trans_sim_on2 (n_Try  i  ) skipRule VF (set invariantsAbs) s" (is "trans_sim_on2 ?r ?r' VF ?F s")
proof(unfold trans_sim_on2_def,(rule allI)+,(rule impI)+,rule disjI2)
  fix s2 
  assume b0:"state_sim_on2 s s2 VF "
  show "state_sim_on2 (trans (act (n_Try  i)) s) s2  VF"
  proof(cut_tac a1,unfold state_sim_on2_def,
    (rule allI)+,(rule impI)+)
    fix f v
    assume b1:" v ∈  VF"  
    
    have b5:"trans (act (n_Try  i)) s v = s v" 
      by (cut_tac a1  b1,auto) 

    have b6:"s v =s2 v "
      using b0 b1 state_sim_on2_def by blast  
    show "trans (act (n_Try  i)) s v= s2 v"
      using b5 b6 by auto 
  qed
qed
lemma lemmaOnn_TryLeNc_:
  assumes a1:"i\<le>NC" 
  shows "trans_sim_on2 (n_Try  i) (n_Try  i) VF  (set invariantsAbs) s" (is "trans_sim_on2 ?r ?r VF ?F s")
proof(rule ruleSimId2)
  show  "∀v. v∈varOfForm (pre ?r) ⟶  v ∈ VF "
    by(cut_tac a1, auto) 
    
next
  show  b1: "∀v a. a ∈ set (statement2Assigns (act ?r)) ⟶ v∈varOfExp ( substExpByStatement (IVar (fst a))  (act ?r))⟶v ∈VF "
   proof(cut_tac a1,(rule allI)+,(rule impI)+,auto) qed
    
 qed
lemma lemmaOnn_Try: 
  assumes   a2:"s ∈ reachableSet (set (allInitSpecs N)) (rules N)"  and  
  a4:"∀f.  f ∈(set invariantsAbs) ⟶  formEval f s" and a5:"\<exists> i. i\<le>N\<and>r=n_Try  i"  and
  a6:"NC<N"
  shows "∃ r'. r' ∈ rules NC∧ trans_sim_on2 r r' VF (set invariantsAbs) s" (is "∃r'.?P1 r' ∧ ?P2 r'")
proof -
  from a5 obtain i where d0:"i\<le>N\<and>r=n_Try  i"  by blast
  have "i>NC|i\<le> NC" by auto
  moreover{
       assume a1:"i>NC" 
        have "∃r'. ?P1 r' ∧ ?P2 r'"
        proof(rule_tac x="(skipRule)" in exI,rule conjI)
          show  "?P1 (skipRule) " 
           by(cut_tac a1, auto) 
          next
          show  "?P2 (skipRule) "
           using lemmaOnn_TryGt_i local.a1 a2 a4 a6 d0 by blast 
        qed
       }
moreover{
       assume a1:"i\<le> NC" 
        have "∃r'. ?P1 r' ∧ ?P2 r'"
        proof(rule_tac x="(n_Try  i)" in exI,rule conjI)
          show  "?P1 (n_Try  i) " 
           by(cut_tac a1, auto) 
          next
          show  "?P2 (n_Try  i) "
           using lemmaOnn_TryLeNc_ local.a1 a2 a4 a6 d0 by blast 
        qed
       }
  ultimately show "∃r'.?P1 r' ∧ ?P2 r'" 
    by satx
qed

lemma lemmaOnn_CritGt_i:
  assumes a1:"i>NC" and 
  a2:"s ∈ reachableSet (set (allInitSpecs N)) (rules N)"  and a3:"NC<N" and  
  a4:"∀f.  f ∈(set invariantsAbs) ⟶  formEval f s" 
  shows "trans_sim_on2 (n_Crit  i)  (n_Crit_i_3 ) VF (set invariantsAbs) s" (is "trans_sim_on2 ?r ?r' VF (set ?F) s")
  proof(rule ruleSimCond2)
    show " formEval (pre ?r) s ⟶formEval (pre ?r') s" (is "?A ⟶?B")
    proof(rule impI)+
      assume b0:"?A"
  
      from b0  show "formEval (pre ?r') s" 
       by auto
     qed
   next 
	show "(∀  v. v ∈  varOfSent (act  ?r') ⟶  v ∈ VF ⟶ formEval (pre ?r) s ⟶ 
    expEval (substExpByStatement (IVar v)  (act ?r')) s = expEval (substExpByStatement (IVar v)  (act ?r)) s)"
   proof(rule allI,(rule impI)+)
      fix  v
     assume b1:"v∈ VF"  and b2:"formEval (pre ?r) s" and b3:"v ∈varOfSent (act ?r')"
  
  show "expEval (substExpByStatement (IVar v)  (act ?r')) s = expEval (substExpByStatement (IVar v)  (act ?r)) s"  
       apply (cut_tac  a1 b1 b2 ,auto) done
   qed
 next
   show "∀  v. v ∈  varOfSent (act ?r) ⟶  v ∈ VF ⟶ v ∈  varOfSent (act ?r')" by(cut_tac a1, auto)

  
 next 
   show "∀ v va. v ∈ varOfSent (act ?r') ⟶va∈varOfExp ( substExpByStatement (IVar v)  (act ?r'))⟶ va ∈ VF "
     by auto  
 next
   show "∀v. v ∈ varOfForm (pre (?r')) ⟶ v ∈ VF" by auto
qed
lemma lemmaOnn_CritLeNc_:
  assumes a1:"i\<le>NC" 
  shows "trans_sim_on2 (n_Crit  i) (n_Crit  i) VF  (set invariantsAbs) s" (is "trans_sim_on2 ?r ?r VF ?F s")
proof(rule ruleSimId2)
  show  "∀v. v∈varOfForm (pre ?r) ⟶  v ∈ VF "
    by(cut_tac a1, auto) 
    
next
  show  b1: "∀v a. a ∈ set (statement2Assigns (act ?r)) ⟶ v∈varOfExp ( substExpByStatement (IVar (fst a))  (act ?r))⟶v ∈VF "
   proof(cut_tac a1,(rule allI)+,(rule impI)+,auto) qed
    
 qed
lemma lemmaOnn_Crit: 
  assumes   a2:"s ∈ reachableSet (set (allInitSpecs N)) (rules N)"  and  
  a4:"∀f.  f ∈(set invariantsAbs) ⟶  formEval f s" and a5:"\<exists> i. i\<le>N\<and>r=n_Crit  i"  and
  a6:"NC<N"
  shows "∃ r'. r' ∈ rules NC∧ trans_sim_on2 r r' VF (set invariantsAbs) s" (is "∃r'.?P1 r' ∧ ?P2 r'")
proof -
  from a5 obtain i where d0:"i\<le>N\<and>r=n_Crit  i"  by blast
  have "i>NC|i\<le> NC" by auto
  moreover{
       assume a1:"i>NC" 
        have "∃r'. ?P1 r' ∧ ?P2 r'"
        proof(rule_tac x="(n_Crit_i_3 )" in exI,rule conjI)
          show  "?P1 (n_Crit_i_3 ) " 
           by(cut_tac a1, auto) 
          next
          show  "?P2 (n_Crit_i_3 ) "
           using lemmaOnn_CritGt_i local.a1 a2 a4 a6 d0 by blast 
        qed
       }
moreover{
       assume a1:"i\<le> NC" 
        have "∃r'. ?P1 r' ∧ ?P2 r'"
        proof(rule_tac x="(n_Crit  i)" in exI,rule conjI)
          show  "?P1 (n_Crit  i) " 
           by(cut_tac a1, auto) 
          next
          show  "?P2 (n_Crit  i) "
           using lemmaOnn_CritLeNc_ local.a1 a2 a4 a6 d0 by blast 
        qed
       }
  ultimately show "∃r'.?P1 r' ∧ ?P2 r'" 
    by satx
qed

lemma lemmaOnn_ExitGt_i:
  assumes a1:"NC<i" and a2:"s ∈ reachableSet (set (allInitSpecs N)) (rules N)"  and  
  a4:"∀f.  f ∈(set invariantsAbs) ⟶  formEval f s" 
shows "trans_sim_on2 (n_Exit  i  ) skipRule VF (set invariantsAbs) s" (is "trans_sim_on2 ?r ?r' VF ?F s")
proof(unfold trans_sim_on2_def,(rule allI)+,(rule impI)+,rule disjI2)
  fix s2 
  assume b0:"state_sim_on2 s s2 VF "
  show "state_sim_on2 (trans (act (n_Exit  i)) s) s2  VF"
  proof(cut_tac a1,unfold state_sim_on2_def,
    (rule allI)+,(rule impI)+)
    fix f v
    assume b1:" v ∈  VF"  
    
    have b5:"trans (act (n_Exit  i)) s v = s v" 
      by (cut_tac a1  b1,auto) 

    have b6:"s v =s2 v "
      using b0 b1 state_sim_on2_def by blast  
    show "trans (act (n_Exit  i)) s v= s2 v"
      using b5 b6 by auto 
  qed
qed
lemma lemmaOnn_ExitLeNc_:
  assumes a1:"i\<le>NC" 
  shows "trans_sim_on2 (n_Exit  i) (n_Exit  i) VF  (set invariantsAbs) s" (is "trans_sim_on2 ?r ?r VF ?F s")
proof(rule ruleSimId2)
  show  "∀v. v∈varOfForm (pre ?r) ⟶  v ∈ VF "
    by(cut_tac a1, auto) 
    
next
  show  b1: "∀v a. a ∈ set (statement2Assigns (act ?r)) ⟶ v∈varOfExp ( substExpByStatement (IVar (fst a))  (act ?r))⟶v ∈VF "
   proof(cut_tac a1,(rule allI)+,(rule impI)+,auto) qed
    
 qed
lemma lemmaOnn_Exit: 
  assumes   a2:"s ∈ reachableSet (set (allInitSpecs N)) (rules N)"  and  
  a4:"∀f.  f ∈(set invariantsAbs) ⟶  formEval f s" and a5:"\<exists> i. i\<le>N\<and>r=n_Exit  i"  and
  a6:"NC<N"
  shows "∃ r'. r' ∈ rules NC∧ trans_sim_on2 r r' VF (set invariantsAbs) s" (is "∃r'.?P1 r' ∧ ?P2 r'")
proof -
  from a5 obtain i where d0:"i\<le>N\<and>r=n_Exit  i"  by blast
  have "i>NC|i\<le> NC" by auto
  moreover{
       assume a1:"i>NC" 
        have "∃r'. ?P1 r' ∧ ?P2 r'"
        proof(rule_tac x="(skipRule)" in exI,rule conjI)
          show  "?P1 (skipRule) " 
           by(cut_tac a1, auto) 
          next
          show  "?P2 (skipRule) "
           using lemmaOnn_ExitGt_i local.a1 a2 a4 a6 d0 by blast 
        qed
       }
moreover{
       assume a1:"i\<le> NC" 
        have "∃r'. ?P1 r' ∧ ?P2 r'"
        proof(rule_tac x="(n_Exit  i)" in exI,rule conjI)
          show  "?P1 (n_Exit  i) " 
           by(cut_tac a1, auto) 
          next
          show  "?P2 (n_Exit  i) "
           using lemmaOnn_ExitLeNc_ local.a1 a2 a4 a6 d0 by blast 
        qed
       }
  ultimately show "∃r'.?P1 r' ∧ ?P2 r'" 
    by satx
qed

lemma lemmaOnn_IdleGt_i:
  assumes a1:"i>NC" and 
  a2:"s ∈ reachableSet (set (allInitSpecs N)) (rules N)"  and a3:"NC<N" and  
  a4:"∀f.  f ∈(set invariantsAbs) ⟶  formEval f s" 
  shows "trans_sim_on2 (n_Idle  i)  (n_Idle_i_3 ) VF (set invariantsAbs) s" (is "trans_sim_on2 ?r ?r' VF (set ?F) s")
  proof(rule ruleSimCond2)
    show " formEval (pre ?r) s ⟶formEval (pre ?r') s" (is "?A ⟶?B")
    proof(rule impI)+
      assume b0:"?A"
  from a4  have tmp:"formEval (inv_27 0)  s"   
            by (force simp del:inv_27_def) 
        have tmp1:"formEval (inv_27 i  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf1,force+)qed
        with b0 a1 have c0:"formEval  (conclude (inv_27 i)) s" by auto
from a4  have tmp:"formEval (inv_7 0 1)  s"   
            by (force simp del:inv_7_def) 
        have tmp1:"formEval (inv_7 i 0  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf2,force+)qed
        with b0 a1 have c1:"formEval  (conclude (inv_7 i 0)) s" by auto
from a4  have tmp:"formEval (inv_7 0 1)  s"   
            by (force simp del:inv_7_def) 
        have tmp1:"formEval (inv_7 i 1  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf2,force+)qed
        with b0 a1 have c2:"formEval  (conclude (inv_7 i 1)) s" by auto
from a4  have tmp:"formEval (inv_5 0 1)  s"   
            by (force simp del:inv_5_def) 
        have tmp1:"formEval (inv_5 i 0  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf2,force+)qed
        with b0 a1 have c3:"formEval  (conclude (inv_5 i 0)) s" by auto
from a4  have tmp:"formEval (inv_5 0 1)  s"   
            by (force simp del:inv_5_def) 
        have tmp1:"formEval (inv_5 i 1  ) s" 
        proof(cut_tac a1 a2 a3 tmp,rule axiomOnf2,force+)qed
        with b0 a1 have c4:"formEval  (conclude (inv_5 i 1)) s" by auto

      from b0 c0 c1 c2 c3 c4 show "formEval (pre ?r') s" 
       by auto
     qed
   next 
	show "(∀  v. v ∈  varOfSent (act  ?r') ⟶  v ∈ VF ⟶ formEval (pre ?r) s ⟶ 
    expEval (substExpByStatement (IVar v)  (act ?r')) s = expEval (substExpByStatement (IVar v)  (act ?r)) s)"
   proof(rule allI,(rule impI)+)
      fix  v
     assume b1:"v∈ VF"  and b2:"formEval (pre ?r) s" and b3:"v ∈varOfSent (act ?r')"
  
  show "expEval (substExpByStatement (IVar v)  (act ?r')) s = expEval (substExpByStatement (IVar v)  (act ?r)) s"  
       apply (cut_tac  a1 b1 b2 ,auto) done
   qed
 next
   show "∀  v. v ∈  varOfSent (act ?r) ⟶  v ∈ VF ⟶ v ∈  varOfSent (act ?r')" by(cut_tac a1, auto)

  
 next 
   show "∀ v va. v ∈ varOfSent (act ?r') ⟶va∈varOfExp ( substExpByStatement (IVar v)  (act ?r'))⟶ va ∈ VF "
     by auto  
 next
   show "∀v. v ∈ varOfForm (pre (?r')) ⟶ v ∈ VF" by auto
qed
lemma lemmaOnn_IdleLeNc_:
  assumes a1:"i\<le>NC" 
  shows "trans_sim_on2 (n_Idle  i) (n_Idle  i) VF  (set invariantsAbs) s" (is "trans_sim_on2 ?r ?r VF ?F s")
proof(rule ruleSimId2)
  show  "∀v. v∈varOfForm (pre ?r) ⟶  v ∈ VF "
    by(cut_tac a1, auto) 
    
next
  show  b1: "∀v a. a ∈ set (statement2Assigns (act ?r)) ⟶ v∈varOfExp ( substExpByStatement (IVar (fst a))  (act ?r))⟶v ∈VF "
   proof(cut_tac a1,(rule allI)+,(rule impI)+,auto) qed
    
 qed
lemma lemmaOnn_Idle: 
  assumes   a2:"s ∈ reachableSet (set (allInitSpecs N)) (rules N)"  and  
  a4:"∀f.  f ∈(set invariantsAbs) ⟶  formEval f s" and a5:"\<exists> i. i\<le>N\<and>r=n_Idle  i"  and
  a6:"NC<N"
  shows "∃ r'. r' ∈ rules NC∧ trans_sim_on2 r r' VF (set invariantsAbs) s" (is "∃r'.?P1 r' ∧ ?P2 r'")
proof -
  from a5 obtain i where d0:"i\<le>N\<and>r=n_Idle  i"  by blast
  have "i>NC|i\<le> NC" by auto
  moreover{
       assume a1:"i>NC" 
        have "∃r'. ?P1 r' ∧ ?P2 r'"
        proof(rule_tac x="(n_Idle_i_3 )" in exI,rule conjI)
          show  "?P1 (n_Idle_i_3 ) " 
           by(cut_tac a1, auto) 
          next
          show  "?P2 (n_Idle_i_3 ) "
           using lemmaOnn_IdleGt_i local.a1 a2 a4 a6 d0 by blast 
        qed
       }
moreover{
       assume a1:"i\<le> NC" 
        have "∃r'. ?P1 r' ∧ ?P2 r'"
        proof(rule_tac x="(n_Idle  i)" in exI,rule conjI)
          show  "?P1 (n_Idle  i) " 
           by(cut_tac a1, auto) 
          next
          show  "?P2 (n_Idle  i) "
           using lemmaOnn_IdleLeNc_ local.a1 a2 a4 a6 d0 by blast 
        qed
       }
  ultimately show "∃r'.?P1 r' ∧ ?P2 r'" 
    by satx
qed


end
