(*proof(induct_tac e and f)
  fix x
  show "?Pe (IVar x) s"
  proof(case_tac "x")
    fix x1
    assume a1:"x=Ident x1"
    show "?Pe (IVar x) s"
    proof(case_tac "EX n. (  (s (Ident x1))=(index n) )\<and> n>M")
      assume b1:"\<exists>n.  (s (Ident x1)) = index n \<and> M < n "
      show "?Pe (IVar x) s"
        by(cut_tac a1 b1 ,auto)
    next
      assume b1:"\<not>(\<exists>n.  (s (Ident x1)) = index n \<and> M < n )"
      show "?Pe (IVar x) s"
      proof(cut_tac  a1 b1, case_tac "(s (Ident x1))",auto)qed
    qed
  next
  fix x21 x22
    assume a1:"x = Para x21 x22"
    show "?Pe (IVar x) s"
    proof(case_tac "x22 >M")
      assume b1:"x22>M "
      show "?Pe (IVar x) s"
        by(cut_tac a b1 a1,auto)
    next
      assume b1:"~x22>M "
      show "?Pe (IVar x) s"
      proof(case_tac "EX n. (  (s x)=(index n) )\<and> n>M",cut_tac a b1 a1,force)
        assume c1:"\<nexists>n. s x = index n \<and> M < n"
        have c2:" expEval (absTransfExp M (IVar x)) (abs1 M s) =s (Para x21 x22)"
        proof(cut_tac a b1 a1 c1,case_tac "s (Para x21 x22)",auto)qed
        have c3:"absTransfConst M (expEval (IVar x) s)=s (Para x21 x22)"
          apply(cut_tac a b1 a1 c1,case_tac "s x",auto) done
        show "?Pe (IVar x) s"
          using c3 local.a1 by auto 
      qed
    qed
  next
    assume a1:"x=dontCareVar"
    show "?Pe (IVar x) s"
      by (simp add: a1)

  qed
next
  fix c
  show "?Pe (Const c) s"   
  proof(case_tac c,auto)qed
next
  fix b e1 e2
  assume a1:"?Pe e1 s" and a2:"?Pe e2 s"
  and a3:"?Pf b s"
  show "?Pe (iteForm b e1 e2) s"
  
  proof(rule impI)+
    assume b1:"isBoundExp s i M (iteForm b e1 e2)" and b2:" M < i" 
    let ?Q="\<lambda>s e. absTransfExp M e = dontCareExp \<or>
    expEval (absTransfExp M e) (abs1 M s) =
     absTransfConst M (expEval e s)"
    let ?R="\<lambda>s f.(absTransfForm  M f=dontCareForm |
  formEval f s =formEval (absTransfForm  M f) (abs1 M s))"
    have b4:"isBoundFormula s i M b\<and> b\<noteq>dontCareForm"
      using b1 isBoundExp.simps(4) isBoundFormula.simps(7) by blast
    have b5:"isBoundExp s i M e1\<and> e1\<noteq>dontCareExp"
      using b1 isBoundExp.simps(3) isBoundExp.simps(4) by blast 
    have b6:"isBoundExp s i M e2\<and> e2\<noteq>dontCareExp"
      using b1 isBoundExp.simps(3) isBoundExp.simps(4) by blast 
    have b7:"?Q s e1"
      using b2 b5 local.a1 by blast
    have b8:"?Q s e2"
      using a2 b2 b6 by blast 
    have b9:"?R s b"
      using a3 b2 b4 by blast
    show "?Q s  (iteForm b e1 e2)"
      using a3 absTransfExp.simps(3) b2 b4 b7 b8 evalITE expType.distinct(11) by presburger
    
  qed
next
  show "?Pe (dontCareExp) s"
    by auto
next 
  fix e1 e2 
  assume a1:"?Pe e1 s"  and a2:"?Pe e2 s" 
  show "?Pf (eqn e1 e2) s"
  proof(rule impI)+
  assume b1:"i>M" and
    b0:"isBoundFormula s i M (eqn e1 e2) " 
  have b2:"isBoundExp s i M e1\<and> e1\<noteq>dontCareExp"
    using b0 isBoundExp.simps(3) isBoundFormula.simps(1) by blast
  have b3:"isBoundExp s i M e2\<and> e2\<noteq>dontCareExp"
    using b0 isBoundExp.simps(3) isBoundFormula.simps(1) by blast
  let ?Q="\<lambda>s e. absTransfExp M e = dontCareExp \<or>
    expEval (absTransfExp M e) (abs1 M s) =
     absTransfConst M (expEval e s)"
  have b4:"?Q s e1"
    using b1 b2 local.a1 by blast 
  have b5:"?Q s e2"
    using a2 b1 b3 by blast
  have b6:   "absTransfForm M (eqn e1 e2) = dontCareForm \<or>
    formEval (eqn e1 e2) s = formEval (absTransfForm M (eqn e1 e2)) (abs1 M s)"  
    proof-       
      have c2:"isBoolVal s e1 \<or> isEnumVal s e1 \<or> isIndexVal s e1 \<or>isDontCareVal s e1"
        apply(unfold isBoolVal_def isEnumVal_def isIndexVal_def  typeOf_def  getValueType_def)
        apply(cut_tac b2 ,case_tac "expEval  e1 s",auto)
        done 
      moreover
      {assume c2:"isBoolVal s e1"
        have c3:"isBoolVal s e2"
          using b0 c2 by auto  
        have c4:"absTransfConst M (expEval e1 s) = (expEval e1 s)"
          using c2 boolExpEvalAbs by auto
        have c5:"absTransfConst M (expEval e2 s) = (expEval e2 s)"
          using c3 boolExpEvalAbs by auto
        have "absTransfForm M (eqn e1 e2) = dontCareForm \<or>
    formEval (eqn e1 e2) s = formEval (absTransfForm M (eqn e1 e2)) (abs1 M s)"
          apply (simp add: a2 b1 b2 b3 c4 c5 local.a1)
          using b4 b5 c4 c5 by auto
         
        
      }  

      moreover
      {assume c2:"isEnumVal s e1"
        have c3:"isEnumVal s e2"
           using b0 c2 by auto    
        have c4:"absTransfConst M (expEval e1 s) = (expEval e1 s)"
          using c2 enumExpEvalAbs by auto
        have c5:"absTransfConst M (expEval e2 s) = (expEval e2 s)"
          using c3 enumExpEvalAbs by auto
        have "absTransfForm M (eqn e1 e2) = dontCareForm \<or>
    formEval (eqn e1 e2) s = formEval (absTransfForm M (eqn e1 e2)) (abs1 M s)"
          apply (simp add: b4 b5 c4 c5)
          using b4 b5 c4 c5 by auto
         
      }  
      moreover
      {assume c2:"isIndexVal s e1"
        have c3:"isIndexVal s e2"
          using b0 c2 by auto
        have c4:"(the (scalar2Nat (expEval e1 s))\<le>M \<or> the (scalar2Nat (expEval e2 s))\<le>M)"
          using b0 c2 isBoundFormula.simps(1) by blast
        moreover
        {assume c4:"the (scalar2Nat (expEval e1 s))\<le>M "
        have c5:"absTransfConst M (expEval e1 s) = (expEval e1 s)  "
          using c2 c4 indexExpEvalAbsLe by auto 
        have c6:"absTransfForm M (eqn e1 e2) = dontCareForm \<or>
    formEval (eqn e1 e2) s = formEval (absTransfForm M (eqn e1 e2)) (abs1 M s)"
          apply(cut_tac b0 c2,auto)
          using b4 b5 apply auto[1]
          using b4 b5 c5 indexExpEvalAbsInv apply fastforce
          using b4 b5 apply auto[1]
          using b4 b5 c5 indexExpEvalAbsLe by auto 
      }  
      moreover
        {assume c4:"the (scalar2Nat (expEval e2 s))\<le>M "
        have c5:"absTransfConst M (expEval e2 s) = (expEval e2 s)  "
          using c3 c4 indexExpEvalAbsLe by auto  
        have "absTransfForm M (eqn e1 e2) = dontCareForm \<or>
        formEval (eqn e1 e2) s = formEval (absTransfForm M (eqn e1 e2)) (abs1 M s)"
          using b4 b5 c2 c4 c5 indexExpEvalAbsInv by auto
          
         
      }  
      ultimately  have "absTransfForm M (eqn e1 e2) = dontCareForm \<or>
    formEval (eqn e1 e2) s = formEval (absTransfForm M (eqn e1 e2)) (abs1 M s)"
        by blast
    }
   moreover
   {assume c2:"isDontCareVal s e1"
     have c3:"isDontCareVal s e2"
       using b0 c2 by auto
     have c6:"absTransfForm M (eqn e1 e2) = dontCareForm \<or>
    formEval (eqn e1 e2) s = formEval (absTransfForm M (eqn e1 e2)) (abs1 M s)"*)
(*       using b4 b5 c3 dontCareExpEvalAbsGe apply auto
proof -
  assume a1: "dontCare = absTransfConst M (expEval e1 s)"
  assume a2: "getValueType (expEval e2 s) = ''any''"
  assume a3: "\<And>e1 s M. getValueType (expEval e1 s) = ''any'' \<longrightarrow> absTransfConst M (expEval e1 s) = dontCare"
  have f4: "CHR ''n'' \<noteq> CHR ''a''"
    by simp
  have f5: "\<forall>s. (\<exists>cs csa. s = enum cs csa) \<or> (\<exists>n. s = index n) \<or> (\<exists>b. s = boolV b) \<or> s = dontCare"
    by (meson scalrValueType.exhaust)
  obtain bb :: "scalrValueType \<Rightarrow> bool" where
    f6: "\<forall>x0. (\<exists>v1. x0 = boolV v1) = (x0 = boolV (bb x0))"
    by moura
  obtain ccs :: "scalrValueType \<Rightarrow> char list" and ccsa :: "scalrValueType \<Rightarrow> char list" where
    "\<forall>x0. (\<exists>v1 v2. x0 = enum v1 v2) = (x0 = enum (ccs x0) (ccsa x0))"
by moura
  then obtain nn :: "scalrValueType \<Rightarrow> nat" where
    f7: "\<forall>s. s = enum (ccs s) (ccsa s) \<or> s = index (nn s) \<or> s = boolV (bb s) \<or> s = dontCare"
    using f6 f5 by moura
  have "absTransfConst M (expEval e2 s) = dontCare"
    using a3 a2 by presburger
  then show "expEval e1 s = expEval e2 s"
    using f7 f4 a2 a1 by (metis (no_types) absTransfConst.simps(1) absTransfConst.simps(3) b0 getValueType.simps(2) isBoundFormula.simps(1) list.inject sameType_def typeOf_def)
qed 
*)
(*sorry
     }
  ultimately  
    show  "absTransfForm M (eqn e1 e2) = dontCareForm \<or>
    formEval (eqn e1 e2) s = formEval (absTransfForm M (eqn e1 e2)) (abs1 M s)"
    by blast

   
qed
  then show  "absTransfForm M (eqn e1 e2) = dontCareForm \<or>
    formEval (eqn e1 e2) s = formEval (absTransfForm M (eqn e1 e2)) (abs1 M s)"
    by blast
qed
next
  fix f1 f2
  assume a1:"?Pf f1 s" and a2:"?Pf f2 s"
  show "?Pf (andForm f1 f2) s"
    apply(cut_tac a1 a2 ,auto)
  qed

next 
  fix f
  assume a1:"?Pf f s" 
  
   show "?Pf (neg f) s"
   proof(rule impI)+
     assume b1:"isBoundFormula s i M (neg f)" and b2:"i \<le>M"
     have b3:"isBoundFormula s i M f"
       using b1 isBoundFormula.simps(2) by blast
     let ?R="\<lambda>s f.(absTransfForm  M f\<noteq>dontCareForm \<and>
    absTransfForm M f \<noteq> eqn (Const (index (Suc M))) (Const (index (Suc M))) \<and>
      formEval f s =formEval (absTransfForm  M f) (abs1 M s))"  
     have b4:"?R s f"
       using b2 b3 isBoundFormula.simps(7) local.a1 by blast
     
      
     show "?R s (neg f)"
      by (cut_tac b3 b4,auto) 
      
  qed

next
  fix f1 f2
  assume a1:"?Pf f1 s" and a2:"?Pf f2 s"
  show "?Pf (orForm f1 f2) s"
  proof(cut_tac a1 a2 ,auto)
  qed


next
  fix f1 f2
  assume a1:"?Pf f1 s" and a2:"?Pf f2 s"
  show "?Pf (implyForm f1 f2) s"
    by(cut_tac a1 a2 ,auto)
qed(auto)
 

lemma absBoundExpForm:
  assumes a:"s dontCareVar =dontCare"  
  shows "(isBoundExp s i M e \<longrightarrow>i\<le>M\<longrightarrow>(absTransfExp  M e\<noteq>dontCareExp\<and>
  expEval (absTransfExp  M e) (abs1 M s)  =absTransfConst M (expEval e s))) \<and>
  (isBoundFormula s i M f \<longrightarrow>i\<le>M\<longrightarrow>(absTransfForm  M f\<noteq>dontCareForm \<and>
   absTransfForm  M f\<noteq>eqn (Const (index (Suc M))) (Const (index (Suc M))) \<and>
  formEval f s =formEval (absTransfForm  M f) (abs1 M s)))"
   (is "?Pe e s \<and>   ?Pf f s") 
proof(induct_tac e and f)
  fix x
  show "?Pe (IVar x) s"
  proof(case_tac "x")
    fix x1
    assume a1:"x=Ident x1"
    show "?Pe (IVar x) s"
    proof(case_tac "EX n. (  (s (Ident x1))=(index n) )\<and> n>M")
      assume b1:"\<exists>n.  (s (Ident x1)) = index n \<and> M < n "
      show "?Pe (IVar x) s"
        by(cut_tac a1 b1 ,auto)
    next
      assume b1:"\<not>(\<exists>n.  (s (Ident x1)) = index n \<and> M < n )"
      show "?Pe (IVar x) s"
      proof(cut_tac  a1 b1, case_tac "(s (Ident x1))",auto)qed
    qed
  next
  fix x21 x22
    assume a1:"x = Para x21 x22"
    show "?Pe (IVar x) s"
    proof(case_tac "x22 >M")
      assume b1:"x22>M "
      show "?Pe (IVar x) s"
        by(cut_tac a b1 a1,auto)
    next
      assume b1:"~x22>M "
      show "?Pe (IVar x) s"
      proof(case_tac "EX n. (  (s x)=(index n) )\<and> n>M",cut_tac a b1 a1,force)
        assume c1:"\<nexists>n. s x = index n \<and> M < n"
        have c2:" expEval (absTransfExp M (IVar x)) (abs1 M s) =s (Para x21 x22)"
        proof(cut_tac a b1 a1 c1,case_tac "s (Para x21 x22)",auto)qed
        have c3:"absTransfConst M (expEval (IVar x) s)=s (Para x21 x22)"
          apply(cut_tac a b1 a1 c1,case_tac "s x",auto) done
        show "?Pe (IVar x) s"
          using c3 local.a1 by auto 
      qed
    qed
  next
    assume a1:"x=dontCareVar"
    show "?Pe (IVar x) s"
      by (simp add: a1)

  qed
next
  fix c
  show "?Pe (Const c) s"   
  proof(case_tac c,auto)qed
next
  fix b e1 e2
  assume a1:"?Pe e1 s" and a2:"?Pe e2 s"
  and a3:"?Pf b s"
  show "?Pe (iteForm b e1 e2) s"
  
  proof(rule impI)+
    assume b1:"isBoundExp s i M (iteForm b e1 e2)" and b2:"i\<le>M" 
    let ?Q="\<lambda>s e. absTransfExp M e \<noteq> dontCareExp \<and>
    expEval (absTransfExp M e) (abs1 M s) = absTransfConst M (expEval e s)"
    let ?R="\<lambda>s f.(absTransfForm  M f\<noteq>dontCareForm \<and>
  formEval f s =formEval (absTransfForm  M f) (abs1 M s))"
    have b4:"isBoundFormula s i M b\<and> b\<noteq>dontCareForm"
      using b1 isBoundExp.simps(4) isBoundFormula.simps(7) by blast
    have b5:"isBoundExp s i M e1\<and> e1\<noteq>dontCareExp"
      using b1 isBoundExp.simps(3) isBoundExp.simps(4) by blast 
    have b6:"isBoundExp s i M e2\<and> e2\<noteq>dontCareExp"
      using b1 isBoundExp.simps(3) isBoundExp.simps(4) by blast 
    have b7:"?Q s e1"
      using b2 b5 local.a1 by blast
    have b8:"?Q s e2"
      using a2 b2 b6 by blast 
    have b9:"?R s b"
      using a3 b2 b4 by blast
    show "?Q s  (iteForm b e1 e2)"
      using a3 absTransfExp.simps(3) b2 b4 b7 b8 evalITE expType.distinct(11) by presburger
    
  qed
next
  show "?Pe (dontCareExp) s"
    by auto
next 
  fix e1 e2 
  assume a1:"?Pe e1 s"  and a2:"?Pe e2 s" 
  show "?Pf (eqn e1 e2) s"
  proof(rule impI)+
  assume b1:"i\<le>M" and
    b0:"isBoundFormula s i M (eqn e1 e2) " 
  have b2:"isBoundExp s i M e1\<and> e1\<noteq>dontCareExp"
    using b0 isBoundExp.simps(3) isBoundFormula.simps(1) by blast
  have b3:"isBoundExp s i M e2\<and> e2\<noteq>dontCareExp"
    using b0 isBoundExp.simps(3) isBoundFormula.simps(1) by blast
  let ?Q="\<lambda>s e. absTransfExp M e \<noteq> dontCareExp \<and>
    expEval (absTransfExp M e) (abs1 M s) = absTransfConst M (expEval e s)"
  have b4:"?Q s e1"
    using b1 b2 local.a1 by blast 
  have b5:"?Q s e2"
    using a2 b1 b3 by blast
  have b6:   "absTransfForm M (eqn e1 e2) \<noteq> dontCareForm \<and>
    absTransfForm M (eqn e1 e2) \<noteq> eqn (Const (index (Suc M))) (Const (index (Suc M))) \<and>
    formEval (eqn e1 e2) s = formEval (absTransfForm M (eqn e1 e2)) (abs1 M s)"  
    proof-       
      have c2:"isBoolVal s e1 \<or> isEnumVal s e1 \<or> isIndexVal s e1 \<or>isDontCareVal s e1"
        apply(unfold isBoolVal_def isEnumVal_def isIndexVal_def  typeOf_def  getValueType_def)
        apply(cut_tac b2 ,case_tac "expEval  e1 s",auto)
        done 
      moreover
      {assume c2:"isBoolVal s e1"
        have c3:"isBoolVal s e2"
          using b0 c2 by auto  
        have c4:"absTransfConst M (expEval e1 s) = (expEval e1 s)"
          using c2 boolExpEvalAbs by auto
        have c5:"absTransfConst M (expEval e2 s) = (expEval e2 s)"
          using c3 boolExpEvalAbs by auto
        have "absTransfForm M (eqn e1 e2) \<noteq> dontCareForm \<and>
    absTransfForm M (eqn e1 e2) \<noteq> eqn (Const (index (Suc M))) (Const (index (Suc M))) \<and>
    formEval (eqn e1 e2) s = formEval (absTransfForm M (eqn e1 e2)) (abs1 M s)"
          apply (simp add: a2 b1 b2 b3 c4 c5 local.a1)
        proof -
          have "CHR ''n'' \<noteq> CHR ''b''"
            by force
          then show "absTransfExp M e1 = Const (index (Suc M)) \<longrightarrow> 
        absTransfExp M e2 \<noteq> Const (index (Suc M))"
            by (metis (no_types) b4 c2 c4 evalConst getValueType.simps(2) isBoolVal_def list.inject typeOf_def)
        qed 
        
      }  

      moreover
      {assume c2:"isEnumVal s e1"
        have c3:"isEnumVal s e2"
           using b0 c2 by auto    
        have c4:"absTransfConst M (expEval e1 s) = (expEval e1 s)"
          using c2 enumExpEvalAbs by auto
        have c5:"absTransfConst M (expEval e2 s) = (expEval e2 s)"
          using c3 enumExpEvalAbs by auto
        have "absTransfForm M (eqn e1 e2) \<noteq> dontCareForm \<and>
    absTransfForm M (eqn e1 e2) \<noteq> eqn (Const (index (Suc M))) (Const (index (Suc M))) \<and>formEval (eqn e1 e2) s = formEval (absTransfForm M (eqn e1 e2)) (abs1 M s)"
          apply (simp add: b4 b5 c4 c5)
        proof -
          have "''nat'' \<noteq> typeOf s e1"
            using c2 by auto
          then show "absTransfExp M e1 = Const (index (Suc M)) \<longrightarrow>
           absTransfExp M e2 \<noteq> Const (index (Suc M))"
            by (metis (no_types) b4 c4 evalConst getValueType.simps(2) typeOf_def)
        qed 
      }  
      moreover
      {assume c2:"isIndexVal s e1"
        have c3:"isIndexVal s e2"
          using b0 c2 by auto
        have c4:"(the (scalar2Nat (expEval e1 s))\<le>M \<or> the (scalar2Nat (expEval e2 s))\<le>M)"
          using b0 c2 isBoundFormula.simps(1) by blast
        moreover
        {assume c4:"the (scalar2Nat (expEval e1 s))\<le>M "
        have c5:"absTransfConst M (expEval e1 s) = (expEval e1 s)  "
          using c2 c4 indexExpEvalAbsLe by auto 
        have c6:"absTransfForm M (eqn e1 e2) \<noteq> dontCareForm \<and>
          absTransfForm M (eqn e1 e2) \<noteq> eqn (Const (index (Suc M))) (Const (index (Suc M)))"
          apply(cut_tac b0 c2,auto)
          using b4 apply blast
          using b5 apply blast
          apply (metis b4 c5 eq_iff evalConst not_less_eq_eq option.sel scalar2Nat.simps(1))
          using b4 apply blast
          using b5 apply blast
          by (metis Suc_n_not_le_n b4 c4 c5 evalConst option.sel scalar2Nat.simps(1))  
        have "formEval (eqn e1 e2) s = formEval (absTransfForm M (eqn e1 e2)) (abs1 M s)"
        proof
          assume c1:"formEval (eqn e1 e2) s "
          show "formEval (absTransfForm M (eqn e1 e2)) (abs1 M s)"
            using b4 b5 c1 by auto 
          
        next
          assume d1:"formEval (absTransfForm M (eqn e1 e2)) (abs1 M s) "
          have d2:"(absTransfForm M (eqn e1 e2)) =eqn (absTransfExp M (e1)) (absTransfExp M (e2))"
            by (simp add: b4 b5) 
          have c3:"expEval (absTransfExp M (e1)) (abs1 M s) = expEval (absTransfExp M (e2)) (abs1 M s)"
            using d1 d2 by auto
          have c4:"the (scalar2Nat (expEval (absTransfExp M (e2)) (abs1 M s))) \<le> M"
            using b4 c3 c4 c5 by auto 
          
            
          have c5:"expEval e2 s=(expEval (absTransfExp M (e2)) (abs1 M s))  "
            using b0 b5 c2 c4 indexExpEvalAbsInv by auto 
           
          show " formEval (eqn e1 e2) s"
            using b4 c2 c3 c4 c5 indexExpEvalAbsInv by auto 
             
        qed 

        with c6 have "absTransfForm M (eqn e1 e2) \<noteq> dontCareForm \<and>
      absTransfForm M (eqn e1 e2) \<noteq> eqn (Const (index (Suc M))) (Const (index (Suc M))) \<and>
      formEval (eqn e1 e2) s = formEval (absTransfForm M (eqn e1 e2)) (abs1 M s)"
          by blast
      }  
      moreover
        {assume c4:"the (scalar2Nat (expEval e2 s))\<le>M "
        have c5:"absTransfConst M (expEval e2 s) = (expEval e2 s)  "
          using c3 c4 indexExpEvalAbsLe by auto 
        have c6:"absTransfForm M (eqn e1 e2) \<noteq> dontCareForm \<and>
          absTransfForm M (eqn e1 e2) \<noteq> eqn (Const (index (Suc M))) (Const (index (Suc M)))"
          sorry
        have "formEval (eqn e1 e2) s = formEval (absTransfForm M (eqn e1 e2)) (abs1 M s)"
        proof
          assume d1:"formEval (eqn e1 e2) s "
          show "formEval (absTransfForm M (eqn e1 e2)) (abs1 M s)"
            using c4 calculation(2) d1 by auto 
          
        next
          assume d1:"formEval (absTransfForm M (eqn e1 e2)) (abs1 M s) "
          have d2:"(absTransfForm M (eqn e1 e2)) =eqn (absTransfExp M (e1)) (absTransfExp M (e2))"
            by (simp add: b4 b5) 
          have c3:"expEval (absTransfExp M (e1)) (abs1 M s) = expEval (absTransfExp M (e2)) (abs1 M s)"
            using d1 d2 by auto
          have c4:"the (scalar2Nat (expEval (absTransfExp M (e1)) (abs1 M s))) \<le> M"
            by (simp add: b5 c3 c4 c5) 
          have c5:"expEval e1 s=(expEval (absTransfExp M (e1)) (abs1 M s))  "
            using b4 c2 c4 indexExpEvalAbsInv by auto
            
          show " formEval (eqn e1 e2) s"
            using c4 c5 calculation(2) d1 by auto 
        qed    

        with c6 have "absTransfForm M (eqn e1 e2) \<noteq> dontCareForm \<and>
          absTransfForm M (eqn e1 e2) \<noteq> eqn (Const (index (Suc M))) (Const (index (Suc M)))
          \<and>formEval (eqn e1 e2) s = formEval (absTransfForm M (eqn e1 e2)) (abs1 M s)"
          by blast
      }  
      ultimately  have "absTransfForm M (eqn e1 e2) \<noteq> dontCareForm \<and>
          absTransfForm M (eqn e1 e2) \<noteq> eqn (Const (index (Suc M))) (Const (index (Suc M)))
          \<and>formEval (eqn e1 e2) s = formEval (absTransfForm M (eqn e1 e2)) (abs1 M s)"
        by blast
    }
   moreover
   {assume c2:"isDontCareVal s e1"
     have c3:"isDontCareVal s e2"
       using b0 c2 by auto
     have c6:"absTransfForm M (eqn e1 e2) \<noteq> dontCareForm \<and>
          absTransfForm M (eqn e1 e2) \<noteq> eqn (Const (index (Suc M))) (Const (index (Suc M)))"
       using b4 b5 c3 dontCareExpEvalAbsGe by auto 
     have "formEval (eqn e1 e2) s = formEval (absTransfForm M (eqn e1 e2)) (abs1 M s)" 
       apply(cut_tac c2,auto)
       using b4 apply blast
       using b5 apply blast
       apply (simp add: b4 b5)+
     proof -
       assume a1: "getValueType (expEval e1 s) = ''any''"
       have "\<forall>n. getValueType (index n) \<noteq> getValueType dontCare"
         by simp
       then show "expEval e1 s = expEval e2 s"
         using a1 by (metis absTransfConst.simps(1) absTransfConst.simps(3) c3 dontCareExpEvalAbsGe getValueType.simps(4) isDontCareVal_def scalrValueType.exhaust typeOf_def)
     qed
     
    with c6 have "absTransfForm M (eqn e1 e2) \<noteq> dontCareForm \<and>
          absTransfForm M (eqn e1 e2) \<noteq> eqn (Const (index (Suc M))) (Const (index (Suc M)))
          \<and>formEval (eqn e1 e2) s = formEval (absTransfForm M (eqn e1 e2)) (abs1 M s)"
        by blast  
     }
  ultimately  have "absTransfForm M (eqn e1 e2) \<noteq> dontCareForm \<and>
          absTransfForm M (eqn e1 e2) \<noteq> eqn (Const (index (Suc M))) (Const (index (Suc M)))
          \<and>formEval (eqn e1 e2) s = formEval (absTransfForm M (eqn e1 e2)) (abs1 M s)"
    by blast

  then show "absTransfForm M (eqn e1 e2) \<noteq> dontCareForm \<and>
    absTransfForm M (eqn e1 e2) \<noteq> eqn (Const (index (Suc M))) (Const (index (Suc M))) \<and>
    formEval (eqn e1 e2) s = formEval (absTransfForm M (eqn e1 e2)) (abs1 M s)"
    by blast
    
    qed
    show "absTransfForm M (eqn e1 e2) \<noteq> dontCareForm \<and>
    absTransfForm M (eqn e1 e2) \<noteq> eqn (Const (index (Suc M))) (Const (index (Suc M))) \<and>
    formEval (eqn e1 e2) s = formEval (absTransfForm M (eqn e1 e2)) (abs1 M s) "
    using b4 b5 b6 apply auto
    done
qed

next
  fix f1 f2
  assume a1:"?Pf f1 s" and a2:"?Pf f2 s"
  show "?Pf (andForm f1 f2) s"
  proof(cut_tac a1 a2 ,auto)
  qed

next 
  fix f
  assume a1:"?Pf f s" 
  
   show "?Pf (neg f) s"
   proof(rule impI)+
     assume b1:"isBoundFormula s i M (neg f)" and b2:"i \<le>M"
     have b3:"isBoundFormula s i M f"
       using b1 isBoundFormula.simps(2) by blast
     let ?R="\<lambda>s f.(absTransfForm  M f\<noteq>dontCareForm \<and>
    absTransfForm M f \<noteq> eqn (Const (index (Suc M))) (Const (index (Suc M))) \<and>
      formEval f s =formEval (absTransfForm  M f) (abs1 M s))"  
     have b4:"?R s f"
       using b2 b3 isBoundFormula.simps(7) local.a1 by blast
     
      
     show "?R s (neg f)"
      by (cut_tac b3 b4,auto) 
      
  qed

next
  fix f1 f2
  assume a1:"?Pf f1 s" and a2:"?Pf f2 s"
  show "?Pf (orForm f1 f2) s"
  proof(cut_tac a1 a2 ,auto)
  qed


next
  fix f1 f2
  assume a1:"?Pf f1 s" and a2:"?Pf f2 s"
  show "?Pf (implyForm f1 f2) s"
    by(cut_tac a1 a2 ,auto)
qed(auto)
