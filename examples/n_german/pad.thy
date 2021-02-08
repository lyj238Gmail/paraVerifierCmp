(*proof(induct_tac e and f)
  fix x
  show "?Pe (IVar x) s"15210180295
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


(*definition wellFormedParallel::"state\<Rightarrow>nat\<Rightarrow>nat\<Rightarrow>nat \<Rightarrow> statement list \<Rightarrow>bool " where [simp]:
"wellFormedParallel s i M N SL\<equiv>  
( \<forall>S'. S' \<in>set SL \<longrightarrow> 
 ((\<exists>a. isBoundAssign s a i M  S') \<or> 
  globalAssignment S' \<or>
  (\<exists> f a SL'. S'=parallelList SL' \<and> wellDefinedForStatement s a N M f SL') ) )"


definition wellFormedAndList11::"state\<Rightarrow>nat \<Rightarrow> nat\<Rightarrow>formula list\<Rightarrow>bool " where [simp]:
"wellFormedAndList11 s N M fs\<equiv> (\<exists> fg. fs= (map (\<lambda>i. fg i) (down N)) \<and>
( \<forall>i.  (isBoundFormula s i M (fg i)) ))"

definition wellFormedAndList21::"state\<Rightarrow>nat \<Rightarrow> nat\<Rightarrow>nat\<Rightarrow>formula list\<Rightarrow>bool " where [simp]:
"wellFormedAndList21 s N M i fs\<equiv> (\<exists> fg. fs=
   (map (\<lambda>j. implyForm (neg (eqn (Const (index i)) (Const (index j)))) (fg j)) (down N)) \<and>
( \<forall>i. (isBoundFormula s i M (fg i)) ))"

definition wellFormedGuard::"state \<Rightarrow>nat \<Rightarrow> nat\<Rightarrow>nat \<Rightarrow>formula list\<Rightarrow>bool" where [simp]:
"wellFormedGuard s N M i fs \<equiv>
  ( (\<forall>g. g\<in>set fs \<longrightarrow>
  (isBoundFormula s i M g \<or> 
  (\<exists>gs. g=andList gs \<and>wellFormedAndList11 s  N M gs )\<or>
  (\<exists>gs. g=andList gs \<and>wellFormedAndList21 s  N M i gs ) \<or> 
  (\<exists>e1 e2. g=neg(eqn e1 e2)\<and>absTransfExp M e1=(Const (index (Suc M))) 
  \<and>absTransfExp M e2=(Const (index (Suc M)))))))"

primrec wellFormedGuardList::"state \<Rightarrow>nat \<Rightarrow> nat\<Rightarrow>nat \<Rightarrow>formula list\<Rightarrow>bool" where [simp]:
"wellFormedGuardList s N M i [] = True"|
"wellFormedGuardList s N M i (g#ls) = (wellFormedGuardList s N M i (ls)\<and>
  (isBoundFormula s i M g \<or>
  (\<exists>gs. g=andList gs \<and>wellFormedAndList11 s  N M gs )\<or>
  (\<exists>gs. g=andList gs \<and>wellFormedAndList21 s  N M i gs ) \<or> 
  (\<exists>e1 e2. g=neg(eqn e1 e2)\<and>absTransfExp M e1=(Const (index (Suc M))) 
  \<and>absTransfExp M e2=(Const (index (Suc M)))))) "*)


(*  by (smt absBoundExpFormLe absSafeExpFormGe absTransfForm.simps(8) b1 evalDontCareForm evalForall not_le)
    using onWellAndList1 by blast*)
  
(*definition wellFormedGuard1::"state \<Rightarrow>nat \<Rightarrow> nat\<Rightarrow> nat \<Rightarrow>formula list\<Rightarrow>bool" where [simp]:
"wellFormedGuard1 s N M i fs \<equiv>
  ( (\<forall>g. g\<in>set fs \<longrightarrow>
  (isBoundFormula s i M g \<or> wellFormedAndList1  N g 
  \<or>wellFormedAndList2  N i g \<or> 
  (\<exists>e1 e2. g=neg(eqn e1 e2)\<and>  ))))"*)

(*lemma gloablAssign1:
"globalAssignment  (assign as)\<longrightarrow>
trans1 (boundIn M (assign as)) (abs1 M s) x =
               absTransfConst M (expEval  (snd as) s) " *)

(*proof(induct_tac S,simp)
  fix as
  show "?P (assign as)"
  proof
    assume a1:"isBoundAssign s a i M (assign as)"
    have a2:" (  (fst as) =Para a i \<and> isBoundExp s i M (snd as)) "
      by(cut_tac a1,auto)

    then obtain a where a2:"(fst as) =Para a i \<and> isBoundExp s i M (snd as)"
      by blast

    show "abs1 M (trans1 (assign as) s) = trans1 (boundIn M (assign as)) (abs1 M s)"
    proof
      fix x
      show "abs1 M (trans1 (assign as) s) x =
         trans1 (boundIn M (assign as)) (abs1 M s) x "
      proof(case_tac "(fst as \<noteq>x)")
        assume b1:"fst as \<noteq> x"
        show "abs1 M (trans1 (assign as) s) x =
         trans1 (boundIn M (assign as)) (abs1 M s) x "
          by(cut_tac b1,auto)
      next
        assume b1:"\<not> fst as \<noteq> x"
        show "abs1 M (trans1 (assign as) s) x =
         trans1 (boundIn M (assign as)) (abs1 M s) x "
        proof(case_tac "i>M")
          assume c1:"i>M"
          show "abs1 M (trans1 (assign as) s) x =
          trans1 (boundIn M (assign as)) (abs1 M s) x "
            by(cut_tac c1 b1 a2,auto)
        next  
          assume c1:"~i>M"
          have c2:"absTransfConst M (expEval (snd as) s)
             =expEval (absTransfExp M (snd as)) (abs1 M s)"
            using a2 absBoundExpForm assms c1 by fastforce 
            
          have c3:"abs1 M (trans1 (assign as) s) x=
            absTransfConst M ((trans1 (assign as) s) x)"
            apply(cut_tac a2 c1 b1,auto) 
            done
          show "abs1 M (trans1 (assign as) s) x =
          trans1 (boundIn M (assign as)) (abs1 M s) x "
            using a2 b1 c2 c3 by auto 
        qed
      qed
    qed
  qed
qed(auto)
*)
  
primrec varOfSents:: "statement list \<Rightarrow> varType set" where
"varOfSents [] = {}"|
"varOfSents (S#SL) = (varOfSent S) \<union> (varOfSents SL)"

(*primrec mutualDiffDefinedStm::"statement \<Rightarrow> bool" where
"mutualDiffDefinedStm skip =True" |
"mutualDiffDefinedStm (assign as) =True"|
"mutualDiffDefinedStm (parallel as P) = (mutualDiffDefinedStm P \<and> (fst as )\<notin>(varOfSent P))"*)

primrec mutualDiffDefinedStmList::"statement list \<Rightarrow> bool" where
"mutualDiffDefinedStmList [] =True" |
"mutualDiffDefinedStmList (S#LS) =
  (( (varOfSent S) \<inter>  (varOfSents  ( LS)) = {}) \<and>
  ( mutualDiffDefinedStmList LS) \<and>
   mutualDiffDefinedStm S)"

lemma notAffect1:
  shows "x \<notin>varOfSent S \<longrightarrow>trans1 (boundIn M S) s x =s x"
  sorry

lemma stateAbsAux1:
  assumes a1:"mutualDiffDefinedStm S" and a2:"mutualDiffDefinedStmList (S # LS)"
  and a3:"x \<in> varOfSent S"
shows "mutualDiffDefinedStm S \<longrightarrow> 
  mutualDiffDefinedStmList (S # LS)\<longrightarrow>
  x \<in> varOfSent S \<longrightarrow>
  abs1 M (trans1 (parallelList (S # LS)) s) x=
  abs1 M (trans1 S  s) x" (is "?ant1 S \<longrightarrow> ?ant2 S\<longrightarrow>?ant3 S\<longrightarrow>?LHS S=?RHS S")
  sorry
(*proof(induct_tac S)
  let ?S="skip" 
  show "?ant1 ?S \<longrightarrow> ?ant2 ?S\<longrightarrow>?ant3 ?S\<longrightarrow>?LHS ?S=?RHS ?S"
  proof(cut_tac  a3,auto)
  qed
next
  fix x2
  let ?S="assign x2"
  
  show "?ant1 ?S \<longrightarrow> ?ant2 ?S\<longrightarrow>?ant3 ?S\<longrightarrow>?LHS ?S=?RHS ?S"
  proof(cut_tac  a3,auto)
  qed
next
  fix x1 S
  let  ?S = "parallel x1 S"
  assume b0:"?ant1 S \<longrightarrow> ?ant2 S\<longrightarrow>?ant3 S\<longrightarrow>?LHS S=?RHS S"
  show "?ant1 ?S \<longrightarrow> ?ant2 ?S\<longrightarrow>?ant3 ?S\<longrightarrow>?LHS ?S=?RHS ?S"
  proof(rule impI)+
    assume b1:"?ant1 ?S " and b2:"?ant2 ?S" and b3:"?ant3 ?S"
    have c1:"fst x1=x |fst x1\<noteq>x" by blast
    moreover
    {assume c1:"fst x1=x"
      have "?LHS ?S=?RHS ?S"
      proof(cut_tac c1,auto)qed
    }
    moreover
    {assume c1:"fst x1\<noteq>x"
      have c2:"mutualDiffDefinedStm ( S)"
        using b1 mutualDiffDefinedStm.simps(3) by blast
      have c3:"?ant2 S"
        apply(cut_tac b2,auto)done
      have c4:"?ant3 S"
        apply(cut_tac c1 b3,auto)done
      have c5:"?LHS S=?RHS S"
        using b0 c2 c3 c4 by blast 

      have c6:"?LHS ?S=?LHS S"
        using c1 parallelList.simps(2) by auto
      have c7:"?RHS ?S=?RHS S"
        using c1 by auto  
        
      have "?LHS ?S=?RHS ?S"
        using c5 c6 c7 by auto
         
     
    }
    ultimately show "?LHS ?S=?RHS ?S"
      by blast
  qed
qed
*)  
lemma stateAbsAux2:
  assumes a1:"mutualDiffDefinedStm S" and a2:"mutualDiffDefinedStmList (S # LS)"
  and a3:"x \<in> varOfSent S"
shows "mutualDiffDefinedStm S \<longrightarrow> 
  mutualDiffDefinedStmList (S # LS)\<longrightarrow>
  x \<in> varOfSent S \<longrightarrow>trans1 (boundIn M (parallelList (S # LS))) (abs1 M s) x=
        trans1 (boundIn M (  (S ))) (abs1 M s) x"
(is "?ant1 S \<longrightarrow> ?ant2 S\<longrightarrow>?ant3 S\<longrightarrow>?LHS S=?RHS S")
(*proof(induct_tac S)
  let ?S="skip" 
  show "?ant1 ?S \<longrightarrow> ?ant2 ?S\<longrightarrow>?ant3 ?S\<longrightarrow>?LHS ?S=?RHS ?S"
  proof(cut_tac  a3,auto)
  qed
next
  fix x2
  let ?S="assign x2"
  
  show "?ant1 ?S \<longrightarrow> ?ant2 ?S\<longrightarrow>?ant3 ?S\<longrightarrow>?LHS ?S=?RHS ?S"
  proof(case_tac "fst x2",cut_tac  a3,force)
    fix x21 x22
    assume b1:"fst x2 = Para x21 x22"
    show "?ant1 ?S \<longrightarrow> ?ant2 ?S\<longrightarrow>?ant3 ?S\<longrightarrow>?LHS ?S=?RHS ?S"
      apply(cut_tac b1,simp)
      apply(subgoal_tac "x \<notin>varOfSent (parallelList LS)")
      using notAffect1 apply auto[1] 
      sorry
  next
    assume b1:"fst x2=dontCareVar"
    show "?ant1 ?S \<longrightarrow> ?ant2 ?S\<longrightarrow>?ant3 ?S\<longrightarrow>?LHS ?S=?RHS ?S"
      apply(cut_tac b1,simp)
      apply(subgoal_tac "x \<notin>varOfSent (parallelList LS)")
      using notAffect1 apply auto[1] 
      sorry
  qed
next
  fix x1 S
  let  ?S = "parallel x1 S"
  assume b0:"?ant1 S \<longrightarrow> ?ant2 S\<longrightarrow>?ant3 S\<longrightarrow>?LHS S=?RHS S"
  show "?ant1 ?S \<longrightarrow> ?ant2 ?S\<longrightarrow>?ant3 ?S\<longrightarrow>?LHS ?S=?RHS ?S"
  proof(rule impI)+
    assume b1:"?ant1 ?S " and b2:"?ant2 ?S" and b3:"?ant3 ?S"
    have c1:"fst x1=x |fst x1\<noteq>x" by blast
    moreover
    {assume c1:"fst x1=x"
      have c2:"x \<notin> varOfSent S"
        using b1 c1 mutualDiffDefinedStm.simps(3) by blast 
      have c2:"x \<notin> varOfSent (cat S (parallelList LS))"
        sorry
      have "?LHS ?S=?RHS ?S"
        apply(cut_tac c1,case_tac "fst x1",force)
         apply(case_tac "x22>M",auto)
        using c2 notAffect1 apply auto[1]
        using c2 notAffect1 by auto 
    }
    moreover
    {assume c1:"fst x1\<noteq>x"
      have c2:"mutualDiffDefinedStm ( S)"
        using b1 mutualDiffDefinedStm.simps(3) by blast
      have c3:"?ant2 S"
        apply(cut_tac b2,auto)done
      have c4:"?ant3 S"
        apply(cut_tac c1 b3,auto)done
      have c5:"?LHS S=?RHS S"
        using b0 c2 c3 c4 by blast 

      have c6:"?LHS ?S=?LHS S"
        using c1 parallelList.simps(2) by auto
      have c7:"?RHS ?S=?RHS S"
        using c1 by auto  
        
      have "?LHS ?S=?RHS ?S"
        using c5 c6 c7 by auto
         
     
    }
    ultimately show "?LHS ?S=?RHS ?S"
      by blast
  qed
qed
*)
sorry
lemma stateAbsAux3:
  assumes a1:"mutualDiffDefinedStm S" and a2:"mutualDiffDefinedStmList (S # LS)"
  and a3:"x \<notin> varOfSent S"
shows "mutualDiffDefinedStm S \<longrightarrow> 
  mutualDiffDefinedStmList (S # LS)\<longrightarrow>
  x \<notin> varOfSent S \<longrightarrow>abs1 M (trans1 (parallelList (S # LS)) s) x=
      abs1 M (trans1 (parallelList (  LS))  s) x"
(is "?ant1 S \<longrightarrow> ?ant2 S\<longrightarrow>?ant3 S\<longrightarrow>?LHS S=?RHS S")
sorry
(*proof(induct_tac S)
  let ?S="skip" 
  show "?ant1 ?S \<longrightarrow> ?ant2 ?S\<longrightarrow>?ant3 ?S\<longrightarrow>?LHS ?S=?RHS ?S"
  proof(cut_tac  a3,auto)
  qed
next
  fix x2
  let ?S="assign x2"
  
  show "?ant1 ?S \<longrightarrow> ?ant2 ?S\<longrightarrow>?ant3 ?S\<longrightarrow>?LHS ?S=?RHS ?S"
  proof(case_tac "fst x2",cut_tac  a3,force)
    fix x21 x22
    assume b1:"fst x2 = Para x21 x22"
    show "?ant1 ?S \<longrightarrow> ?ant2 ?S\<longrightarrow>?ant3 ?S\<longrightarrow>?LHS ?S=?RHS ?S"
      apply(cut_tac b1,simp)
      by blast
       
  next
    assume b1:"fst x2=dontCareVar"
    show "?ant1 ?S \<longrightarrow> ?ant2 ?S\<longrightarrow>?ant3 ?S\<longrightarrow>?LHS ?S=?RHS ?S"
      apply(cut_tac b1,simp)
      by blast
      
  qed
next
  fix x1 S
  let  ?S = "parallel x1 S"
  assume b0:"?ant1 S \<longrightarrow> ?ant2 S\<longrightarrow>?ant3 S\<longrightarrow>?LHS S=?RHS S"
  show "?ant1 ?S \<longrightarrow> ?ant2 ?S\<longrightarrow>?ant3 ?S\<longrightarrow>?LHS ?S=?RHS ?S"
  proof(rule impI)+
    assume b1:"?ant1 ?S " and b2:"?ant2 ?S" and b3:"?ant3 ?S"
    have c1:"fst x1=x |fst x1\<noteq>x" by blast
    moreover
    {assume c1:"fst x1=x"
      have c2:"False"
        using b3 c1 by auto
       
      have "?LHS ?S=?RHS ?S"
        
        using c2 notAffect1 by auto 
    }
    moreover
    {assume c1:"fst x1\<noteq>x"
      have c2:"mutualDiffDefinedStm ( S)"
        using b1 mutualDiffDefinedStm.simps(3) by blast
      have c3:"?ant2 S"
        apply(cut_tac b2,auto)done
      have c4:"?ant3 S"
        apply(cut_tac c1 b3,auto)done
      have c5:"?LHS S=?RHS S"
        using b0 c2 c3 c4 by blast 

      have c6:"?LHS ?S=?LHS S"
        using c1 parallelList.simps(2) by auto
      have c7:"?RHS ?S=?RHS S"
        using c1 by auto  
        
      have "?LHS ?S=?RHS ?S"
        using c5 c6 c7 by auto
         
     
    }
    ultimately show "?LHS ?S=?RHS ?S"
      by blast
  qed
qed
*)
   
 
lemma stateAbsAux4:
  assumes a1:"mutualDiffDefinedStm S" and a2:"mutualDiffDefinedStmList (S # LS)"
  and a3:"x \<notin> varOfSent S"
shows "mutualDiffDefinedStm S \<longrightarrow> 
  mutualDiffDefinedStmList (S # LS)\<longrightarrow>
  x \<notin> varOfSent S \<longrightarrow>trans1 (boundIn M (parallelList (S # LS))) (abs1 M s) x=
        trans1 (boundIn M (parallelList  LS)) (abs1 M s) x"

(is "?ant1 S \<longrightarrow> ?ant2 S\<longrightarrow>?ant3 S\<longrightarrow>?LHS S=?RHS S")
  sorry
(*proof(induct_tac S)
  let ?S="skip" 
  show "?ant1 ?S \<longrightarrow> ?ant2 ?S\<longrightarrow>?ant3 ?S\<longrightarrow>?LHS ?S=?RHS ?S"
  proof(cut_tac  a3,auto)
  qed
next
  fix x2
  let ?S="assign x2"
  
  show "?ant1 ?S \<longrightarrow> ?ant2 ?S\<longrightarrow>?ant3 ?S\<longrightarrow>?LHS ?S=?RHS ?S"
  proof(case_tac "fst x2",cut_tac  a3,force)
    fix x21 x22
    assume b1:"fst x2 = Para x21 x22"
    show "?ant1 ?S \<longrightarrow> ?ant2 ?S\<longrightarrow>?ant3 ?S\<longrightarrow>?LHS ?S=?RHS ?S"
      apply(cut_tac b1,simp)
      done
       
  next
    assume b1:"fst x2=dontCareVar"
    show "?ant1 ?S \<longrightarrow> ?ant2 ?S\<longrightarrow>?ant3 ?S\<longrightarrow>?LHS ?S=?RHS ?S"
      apply(cut_tac b1,simp)
     done
      
  qed
next
  fix x1 S
  let  ?S = "parallel x1 S"
  assume b0:"?ant1 S \<longrightarrow> ?ant2 S\<longrightarrow>?ant3 S\<longrightarrow>?LHS S=?RHS S"
  show "?ant1 ?S \<longrightarrow> ?ant2 ?S\<longrightarrow>?ant3 ?S\<longrightarrow>?LHS ?S=?RHS ?S"
  proof(rule impI)+
    assume b1:"?ant1 ?S " and b2:"?ant2 ?S" and b3:"?ant3 ?S"
    have c1:"fst x1=x |fst x1\<noteq>x" by blast
    moreover
    {assume c1:"fst x1=x"
      have c2:"False"
        using b3 c1 by auto
       
      have "?LHS ?S=?RHS ?S"
        
        using c2 notAffect1 by auto 
    }
    moreover
    {assume c1:"fst x1\<noteq>x"
      have c2:"mutualDiffDefinedStm ( S)"
        using b1 mutualDiffDefinedStm.simps(3) by blast
      have c3:"?ant2 S"
        apply(cut_tac b2,auto)done
      have c4:"?ant3 S"
        apply(cut_tac c1 b3,auto)done
      have c5:"?LHS S=?RHS S"
        using b0 c2 c3 c4 by blast 

      have c6:"?LHS ?S=?LHS S"
        using c1 parallelList.simps(2) by auto
      have c7:"?RHS ?S=?RHS S"
        using c1 by auto  
        
      have "?LHS ?S=?RHS ?S"
        using c5 c6 c7 by auto
         
     
    }
    ultimately show "?LHS ?S=?RHS ?S"
      by blast
  qed
qed
*)s

boundIn M skip =skip"|
"boundIn M (assign as) = 
  (if absTransfVar M (fst as) = dontCareVar 
  then skip else (assign  ((fst as), (absTransfExp M (snd as)))))" |
"boundIn M (parallel as S) =
   parallel  (boundIn M as) (boundIn M S)" |
"boundIn M (forallStm PS N) =
   forallStm (\<lambda>i. boundIn M (PS i)) M" 

lemma absStmIsSkip:
  assumes a1:"s dontCareVar =dontCare"
  shows "(absTransfStatement M S) =skip\<longrightarrow>
 abs1 M (trans1 S s) = trans1 (absTransfStatement M S) (abs1 M s)"
(is "?P S") \<Rightarrow> nat
  sorry
(*
proof(induct_tac S)
  let ?S="skip"
  show "?P ?S"
  proof(rule impI, rule ext)
    fix x
    show " abs1 M (trans1 skip s) x = trans1 (absTransfStatement M skip) (abs1 M s) x "
      by auto
  qed
next
  fix as
  let ?S="assign as"
  show "?P ?S"
  proof(rule impI, rule ext)
    fix x
    assume b1:" absTransfStatement M (assign as) = skip" 
    show " abs1 M (trans1 ?S s) x = trans1 (absTransfStatement M ?S) (abs1 M s) x "
      apply(cut_tac a1 b1,case_tac "fst as=x",auto,case_tac "fst as",auto)done
  qed
next
  fix as P
  let ?S="parallel as P"
  assume b1:"?P P"
  show "?P ?S"
  proof(rule impI, rule ext)
    fix x
    assume c1:" absTransfStatement M ?S = skip" 
    show " abs1 M (trans1 ?S s) x = trans1 (absTransfStatement M ?S) (abs1 M s) x "
    proof(case_tac "absTransfVar M (fst as) = dontCareVar ")
      assume d1:"absTransfVar M (fst as) = dontCareVar"
      show "abs1 M (trans1 (parallel as P) s) x =
      trans1 (absTransfStatement M (parallel as P)) (abs1 M s) x"
      
      proof -
        have f1: "\<And>v. abs1 M (trans1 P s) v = trans1 skip (abs1 M s) v"
          using absTransfStatement.simps(3) b1 c1 d1 by presburger
        obtain nn :: "varType \<Rightarrow> nat \<Rightarrow> nat" and ccs :: "varType \<Rightarrow> nat \<Rightarrow> char list" where
          f2: "\<And>v n f na nb va cs fa fb fc fd. (v \<noteq> dontCareVar \<or> n < nn v n \<or> abs1 n f v = dontCare) \<and> (\<not> na < nb \<or> va \<noteq> Para cs nb \<or> abs1 na fa va = dontCare) \<and> (v = dontCareVar \<or> n < nn v n \<or> abs1 n fb v = absTransfConst n (fb v)) \<and> (v \<noteq> dontCareVar \<or> Para (ccs v n) (nn v n) = v \<or> abs1 n fc v = dontCare) \<and> (v = dontCareVar \<or> Para (ccs v n) (nn v n) = v \<or> abs1 n fd v = absTransfConst n (fd v))"
          by moura
        moreover
        { assume "dontCareVar \<noteq> x"
          have "fst as \<noteq> x \<and> dontCareVar \<noteq> x \<and> fst as \<noteq> x \<and> dontCareVar \<noteq> x \<or> abs1 M (trans1 (parallel as P) s) x = trans1 skip (abs1 M s) x"
            using f2 f1 by (metis absTransfVar.simps(1) absTransfVar.simps(2) d1 varType.exhaust)
          then have "abs1 M (trans1 (parallel as P) s) x = trans1 skip (abs1 M s) x"
            using f2 f1 by (metis (full_types) trans1.simps(3)) }
        ultimately show ?thesis
          using f1 by (metis (full_types) c1)
      qed
    next
      assume d1:"absTransfVar M (fst as) \<noteq> dontCareVar"
      have False
        using c1 d1 by auto
      then show   ?thesis 
        by auto
    qed
  qed
qed
*)
   

lemma stateAbs:
   assumes a0:"s dontCareVar =dontCare" 
   shows "(mutualDiffDefinedStmList LS \<and>
  (\<forall>S. (S \<in>set LS) \<longrightarrow>   ((absTransfStatement M S) =skip \<or> 
    abs1 M (trans1 S s) = trans1 (absTransfStatement M S) (abs1 M s)))) \<longrightarrow>
    abs1 M (trans1 (parallelList LS) s) = 
    trans1 (absTransfStatement M (parallelList LS)) (abs1 M s) " (is "?P LS")
  sorry
(*proof(induct_tac LS)
  show "?P []"
    by auto
next
  fix S LS
  assume a1:"?P LS" (is "?ant1 LS \<and>?ant2 LS  \<longrightarrow>?cons LS")
  show "?P (S#LS)" 
  proof((rule impI)+)
    assume b0:"?ant1 (S#LS) \<and>?ant2 (S#LS)"
    show "?cons (S#LS)"
    proof(case_tac "S")
      assume b1:"S=skip"
      have b2:"parallelList (S # LS) =parallelList LS"
        by (simp add: b1)
      have b3:"?ant1 LS"
        by(cut_tac b0,auto)
      have b3a:"?ant2 LS"
        by(cut_tac b0,auto)
      have b4:"?cons LS"
        using b3 b3a local.a1 by blast
        
      show " abs1 M (trans1 (parallelList (S # LS)) s)  =
         trans1 (absTransfStatement M (parallelList (S # LS))) (abs1 M s)  "
        using b2 b4 by presburger 
    next
      fix as2
      assume b1:"S=assign as2 "
      show " abs1 M (trans1 (parallelList (S # LS)) s)  =
         trans1 (absTransfStatement M (parallelList (S # LS))) (abs1 M s)  "
      proof -
      have b2:"parallelList (S # LS) =parallel as2 (parallelList LS)"
        by (simp add: b1)
      have b3:"?ant1 LS"
        by(cut_tac b0,auto)
      have b3a:"?ant2 LS"
        by(cut_tac b0,auto)
      have b4:"?cons LS"
        using b3 b3a local.a1 by blast
      have b5:" abs1 M (trans1 (parallel as2 (parallelList LS)) s)  =
         trans1 (absTransfStatement M (parallel as2 (parallelList LS))) (abs1 M s)  "
      proof
        fix x
        show "abs1 M (trans1 (parallel as2 (parallelList LS)) s) x =
         trans1 (absTransfStatement M (parallel as2 (parallelList LS))) (abs1 M s) x"
        proof -
        have c0:"(fst as2\<noteq>x) \<or> ~(fst as2\<noteq>x)"
          by auto

        moreover
        {assume c1:"fst as2\<noteq>x"
         
          have d1:" abs1 M (trans1 (parallel as2 (parallelList LS)) s) x =
          trans1 (absTransfStatement M (parallel as2 (parallelList LS))) (abs1 M s) x "
            apply(cut_tac  c1,auto)
            apply (metis abs1_def b4)
            apply (metis One_nat_def abs1_def add.right_neutral add_Suc_right b3 
                  b3a local.a1)
            by (metis abs1_def b3 b3a local.a1)
            
             
        }

        {assume c1:"~(fst as2\<noteq>x)"
          have c1:"fst as2=x" by(cut_tac c1,auto)
          have c2:"fst as2\<noteq>dontCareVar" sorry
          have c3:"abs1 M (trans1 (parallel as2 (parallelList LS)) s) x =
                (abs1 M ((trans1 (assign as2) s)) x)"
            apply(cut_tac c1,auto)done 
          have c4:"(EX v n. x=Para v n \<and> n>M) | \<not>(EX v n. x=Para v n \<and> n>M)"
            by blast

          moreover
          {assume c4:"(EX v n. x=Para v n \<and> n>M)"
           have c5:"abs1 M ((trans1 (assign as2) s)) x= dontCare
                  "
             apply(cut_tac c1 c4,auto)  done

           have c6:"x \<notin>varOfSents LS" sorry
           have c7:"x \<notin>varOfSent (absTransfStatement M (parallelList LS))" sorry

           have c7:"trans1 (absTransfStatement M (parallel as2 (parallelList LS)))
             (abs1 M s) x =dontCare" 
              
             apply(cut_tac c1 c4 c7,auto)
             by (metis abs1_def b4)   

           have c8:" abs1 M (trans1 (parallel as2 (parallelList LS)) s) x =
            trans1 (absTransfStatement M (parallel as2 (parallelList LS))) (abs1 M s) x "
             (is "?LHS =?RHS")
             using c3 c5 c7 by auto
          }
          moreover
          {assume c4:"~(EX v n. x=Para v n \<and> n>M)"
            have "x=dontCareVar \<or> ~x=dontCareVar"
              by blast
            moreover
            {assume c41:"~x=dontCareVar"
            have c5:"abs1 M ((trans1 (assign as2) s)) x= 
              absTransfConst M (expEval (snd as2) s)"       
              apply(cut_tac c1 c4 c41,auto)  done 

            have c7:"trans1 (absTransfStatement M (parallel as2 (parallelList LS)))
             (abs1 M s) x = absTransfConst M (expEval (snd as2) s)" 
              
             apply(cut_tac c1 c2 c4 ,auto)
             apply (metis absTransfVar.simps(1) absTransfVar.simps(2) varType.exhaust)
              by (metis absTransfStatement.simps(2) b0 b1 c5 fst_conv list.set_intros(1)
                  snd_conv statement.distinct(1) trans1.simps(2))
            have c8:" abs1 M (trans1 (parallel as2 (parallelList LS)) s) x =
            trans1 (absTransfStatement M (parallel as2 (parallelList LS))) (abs1 M s) x "
             (is "?LHS =?RHS")
              using c3 c5 c7 by auto 
          }
           moreover
           {assume c41:"x=dontCareVar"
             
             have c11:" abs1 M (trans1 (parallel as2 (parallelList LS)) s) x =
            trans1 (absTransfStatement M (parallel as2 (parallelList LS))) (abs1 M s) x "
             (is "?LHS =?RHS")
               using c1 c2 c41 by blast
          }
          ultimately have d1:"abs1 M (trans1 (parallel as2 (parallelList LS)) s) x =
            trans1 (absTransfStatement M (parallel as2 (parallelList LS))) (abs1 M s) x"
            by blast
        }
       ultimately have "abs1 M (trans1 (parallel as2 (parallelList LS)) s) x =
            trans1 (absTransfStatement M (parallel as2 (parallelList LS))) (abs1 M s) x"
         
         using \<open>fst as2 \<noteq> x \<Longrightarrow>
     abs1 M (trans1 (parallel as2 (parallelList LS)) s) x =
     trans1 (absTransfStatement M (parallel as2 (parallelList LS))) (abs1 M s) x\<close> by blast
     }
    ultimately show "abs1 M (trans1 (parallel as2 (parallelList LS)) s) x =
            trans1 (absTransfStatement M (parallel as2 (parallelList LS))) (abs1 M s) x"
      using \<open>fst as2 \<noteq> x \<Longrightarrow> abs1 M (trans1 (parallel as2 (parallelList LS)) s) x = 
      trans1 (absTransfStatement M (parallel as2 (parallelList LS))) (abs1 M s) x\<close> by blast
      
     qed
   qed
       show " abs1 M (trans1 (parallelList (S # LS)) s) =
          trans1 (absTransfStatement M (parallelList (S # LS))) (abs1 M s)"
     using b2 b5 by auto
      qed
    next
      fix x31 x32
      assume b1:"S = parallel x31 x32"
      show " abs1 M (trans1 (parallelList (S # LS)) s)  =
         trans1 (absTransfStatement M (parallelList (S # LS))) (abs1 M s)  "
      proof 
        fix x
        show "abs1 M (trans1 (parallelList (S # LS)) s) x =
         trans1 (absTransfStatement M (parallelList (S # LS))) (abs1 M s) x "
        proof(case_tac "x \<in> varOfSent S")
          assume c1:"x \<in> varOfSent S"
           show "abs1 M (trans1 (parallelList (S # LS)) s) x =
            trans1 (absTransfStatement M (parallelList (S # LS))) (abs1 M s) x "
           proof -
             have c2:"abs1 M (trans1 (parallelList (S # LS)) s) x =
                    abs1 M (trans1 S  s) x"
               using b0 c1 stateAbsAux1 mutualDiffDefinedStmList.simps(2) by blast
             have c3:"trans1 (absTransfStatement M (parallelList (S # LS))) (abs1 M s) x=
                trans1 (absTransfStatement M (  (S ))) (abs1 M s) x"
               using b0 c1 stateAbsAux2 mutualDiffDefinedStmList.simps(2) by blast 
             have c4:"abs1 M (trans1 S  s) x=
                 trans1 (absTransfStatement M (  (S ))) (abs1 M s) x"
             proof(case_tac "absTransfStatement M (  (S )) = skip ")
               assume d1: "absTransfStatement M (  (S )) = skip"
               show "abs1 M (trans1 S s) x = trans1 (absTransfStatement M S) (abs1 M s) x"
                 by (simp add: absStmIsSkip assms d1) 
             next
               assume d1:"\<not>absTransfStatement M (  (S )) = skip"
               show "abs1 M (trans1 S s) x = trans1 (absTransfStatement M S) (abs1 M s) x"
                 by (meson b0 d1 list.set_intros(1)) 
             qed
            show "abs1 M (trans1 (parallelList (S # LS)) s) x =
            trans1 (absTransfStatement M (parallelList (S # LS))) (abs1 M s) x "
              using c2 c3 c4 by auto
          qed
        next
          assume c1:"x \<notin> varOfSent S"
           show "abs1 M (trans1 (parallelList (S # LS)) s) x =
            trans1 (absTransfStatement M (parallelList (S # LS))) (abs1 M s) x "
           proof -
            have c2:"abs1 M (trans1 (parallelList (S # LS)) s) x =
                    abs1 M (trans1 (parallelList ( LS))  s) x"
            
              using b0 c1 stateAbsAux3 mutualDiffDefinedStmList.simps(2) by blast

             have c3:"trans1 (absTransfStatement M (parallelList (S # LS))) (abs1 M s) x=
                trans1 (absTransfStatement M (parallelList  (LS ))) (abs1 M s) x"
               using b0 c1 stateAbsAux4 mutualDiffDefinedStmList.simps(2) by blast 

             have c4:"abs1 M (trans1 (parallelList ( LS))  s) x=
                     trans1 (absTransfStatement M (parallelList  (LS ))) (abs1 M s) x "
               by (meson b0 list.set_intros(2) local.a1 mutualDiffDefinedStmList.simps(2))
              show "abs1 M (trans1 (parallelList (S # LS)) s) x =
            trans1 (absTransfStatement M (parallelList (S # LS))) (abs1 M s) x "
              using c2 c3 c4 by auto
          qed   
        qed
      qed
    qed
  qed
qed
*)

lemma wellDefinedForStatementIsmutualDiffDefinedStmList:
  assumes a1:"wellDefinedForStatement s a N M f (  LS)"  
  shows "mutualDiffDefinedStmList LS" sorry
(*proof -
  have a1:" LS=map f (down N) \<and> (\<forall>i. (isBoundAssign s a i M (f i)))"
    apply(cut_tac a1,unfold wellDefinedForStatement_def,auto)
    done
  have "\<forall>N. (LS=map f (down N) \<and> (\<forall>i. (isBoundAssign  s a i M (f i))))
   \<longrightarrow>mutualDiffDefinedStmList LS" (is "?P LS")
  proof(induct_tac LS)
    show "?P []"
      apply(unfold isBoundAssign_def,auto)done
    next
      fix l L
      assume b1:"?P L"
      show "?P (l#L)"
      proof(rule allI,rule impI)
        fix N
        assume c1:"l # L = map f (down N) \<and> (\<forall>i. isBoundAssign s a i M (f i))"
        show "mutualDiffDefinedStmList (l # L) "
        proof(simp)
          have "(\<exists>N'.  N=Suc N')|N=0" apply arith done 
          moreover
          {assume d1:"N=0"
            have "varOfSent l \<inter> varOfSents L = {} \<and> 
            mutualDiffDefinedStmList L \<and> mutualDiffDefinedStm l"
              apply(cut_tac c1 d1, auto) thm spec
              apply(drule_tac x="0" in spec) 
              apply(case_tac "f 0",auto)
              done
          }
          moreover
          {assume d1:"(\<exists>N'.  N=Suc N')"
            from d1 obtain N' where d1:"N = Suc N'"
              by blast
            from c1 have d2:"l=f (Suc N') \<and> L=map f (down N')"
              using d1 by auto
            have d3:"\<exists>v. varOfSent l= { Para v (Suc N')}"
              apply(cut_tac c1 d1 d2)
              apply(erule conjE)
              apply(drule_tac x="Suc N'" in spec,case_tac "f (Suc N')",auto)
              done
            have d4:"L=map f (down N')\<longrightarrow>
              (\<forall>i. isBoundAssign s a i M (f i))\<longrightarrow>
                varOfSents L = {x. \<exists> i. x=Para a i \<and> i \<le>N'}" (is "?R N'")
            proof(induct_tac N')
              show "?R 0"
              proof( simp,(rule impI)+)
                assume e1:"\<forall>i. isBoundAssign s a i M (f i) "
                have e2:"isBoundAssign s a 0 M (f 0) "
                  using e1 by blast
                have e3:"\<exists>  e. (f 0) = assign ((Para a 0), e)" 
                  apply(cut_tac e2,case_tac "f 0",auto) done
                then obtain  e where e3:"(f 0) = assign ((Para a 0), e)" 
                  by blast
                show "varOfSent (f 0) = { Para a 0}"
                  apply(cut_tac e3,simp)
                  done
              qed
            next
              fix n
              assume b1:"?R n"
              show "?R (Suc n)"
                sorry
            qed

            have "varOfSent l \<inter> varOfSents L = {} \<and> 
            mutualDiffDefinedStmList L \<and> mutualDiffDefinedStm l"
              apply(cut_tac c1 d2, auto) thm spec
              apply(drule_tac x="z" in spec) 
              apply(case_tac "f z",force+)
              using c1 d3 d4 apply auto[1]
                apply force
              apply (metis b1)
              by (metis isBoundAssign.simps(3) mutualDiffDefinedStm.simps(1) mutualDiffDefinedStm.simps(2) statement.exhaust) 
               
          }
          ultimately   
          show "varOfSent l \<inter> varOfSents L = {} \<and>
           mutualDiffDefinedStmList L \<and> mutualDiffDefinedStm l"
            by blast
        qed
      qed
    qed
    show "mutualDiffDefinedStmList LS"
      using \<open>\<forall>N. LS = map f (down N) \<and>
 (\<forall>i. isBoundAssign s a i M (f i)) \<longrightarrow> mutualDiffDefinedStmList LS\<close> local.a1 by blast
  qed
*)
lemma stateAbsAnother:
   assumes a0:"s dontCareVar =dontCare" 
   shows "(mutualDiffDefinedStm LS ) \<longrightarrow>
    abs1 M (trans1 ( LS) s) = 
    trans1 (absTransfStatement M ( LS)) (abs1 M s) " (is "?P LS")
  sorry
(*lemma statementSim:
  assumes a1:"wellFormedParallel s i M N S"  
  shows "abs1 M (trans1 S s) = trans1 (absTransfStatement M S) s"*)

lemma topAbsSafeExpForm:
   
  shows "(safeExp s i M e \<longrightarrow>i>M \<longrightarrow>((topTransfExp (absTransfExp  M e))=dontCareExp  \<or>
   (topTransfExp (absTransfExp  M e))   =(absTransfExp  M e))) \<and>
  (safeFormula s i M f  \<longrightarrow>i>M\<longrightarrow>(((topTransfForm (absTransfForm  M f)=chaos ) \<or>
  ((absTransfForm  M f) =  (topTransfForm (absTransfForm  M f))  ))))"
   (is "?Pe e s \<and>   ?Pf f s") 
  sorry

lemma wellForallForm1:
  assumes a1:"safeFormula s i M g " and a2:"formEval    ( (forallForm fg N)) s "
  shows "  formEval  ( topTransfForm (absTransfForm M (forallForm fg N))) s"
  sorry


(*theorem protSimLemma:
  assumes 
protSim I I1 rs rs1 M*)
(*inductive_set simpleFormedExpSet :: "nat \<Rightarrow> expType set" and
simpleFormedFormulaSet::"nat\<Rightarrow>formula set" 
  for i::"nat"  where

  simpleGlobalVarExp: "IVar ((Ident) x )\<in> simpleFormedExpSet i" |

  simplelocalVarExp: "IVar (Para n i)  \<in> simpleFormedExpSet i" |

  simpleIteExp: "\<lbrakk>e1 \<in> simpleFormedExpSet i;e2 \<in> simpleFormedExpSet i;
             f \<in> simpleFormedFormula i\<rbrakk> \<Longrightarrow>
             iteForm f e1 e2 \<in> simpleFormedExpSet i" |

  simpleChaosForm: "chaos \<in> simpleFormedFormulaSet i"|

  simpleMiracleForm:"miracle \<in> simpleFormedExpSet i"|
  simpleEqnForm:" \<lbrakk>e1 \<in> simpleFormedExpSet i;e2 \<in> simpleFormedExpSet i\<rbrakk>\<Longrightarrow>
          eqn e1 e2  \<in> simpleFormedFormulaSet i"|

  simpleNegForm:" \<lbrakk>f1 \<in> simpleFormedFormulaSet i \<rbrakk>\<Longrightarrow>
          neg f1  \<in> simpleFormedFormulaSet i" | 

  simpleAndForm:" \<lbrakk>f1 \<in> simpleFormedFormulaSet i; f2 \<in> simpleFormedFormulaSet i \<rbrakk>\<Longrightarrow>
          andForm f1 f2 \<in> simpleFormedFormulaSet i" |

  simpleOrForm:" \<lbrakk>f1 \<in> simpleFormedFormulaSet i; f2 \<in> simpleFormedFormulaSet i \<rbrakk>\<Longrightarrow>
          orForm f1 f2 \<in> simpleFormedFormulaSet i"|

  simpleImplyForm:" \<lbrakk>f1 \<in> simpleFormedFormulaSet i; f2 \<in> simpleFormedFormulaSet i \<rbrakk>\<Longrightarrow>
          implyForm f1 f2 \<in> simpleFormedFormulaSet i"

definition wellFormedAndList1::"nat \<Rightarrow> formula \<Rightarrow>bool " where
"wellFormedAndList1  N f\<equiv> (\<exists>N fg. f=andList (map (\<lambda>i. fg i) (down N)) \<and>
( \<forall>i. (fg i)\<in> (simpleFormedFormulaSet i)))"

definition wellFormedAndList2::"nat \<Rightarrow> nat\<Rightarrow>formula \<Rightarrow>bool " where
"wellFormedAndList2  N i f\<equiv> (\<exists>N fg. f=
  andList (map (\<lambda>j. implyForm (neg (eqn (Const (index i)) (Const (index j)))) (fg j)) (down N)) \<and>
( \<forall>i. (fg i)\<in> (simpleFormedFormulaSet i)))"

definition  wellForm::"nat \<Rightarrow> nat\<Rightarrow>formula \<Rightarrow>bool" where
"wellForm N i f \<equiv> \<exists> fs. f=andList fs \<and> 
  (\<forall>f. f \<in> set fs \<longrightarrow>
  ((wellFormedAndList1  N f) \<or> (wellFormedAndList2  N i f) \<or>  (f \<in> simpleFormedFormulaSet i)))"

definition wellFormedIteExp::"nat \<Rightarrow>expType \<Rightarrow> bool" where
"wellFormedIteExp i  e\<equiv> \<exists> e1 e2 f. (e=iteForm f e1 e2) 
  \<and> e1 \<in> simpleFormedExpSet i \<and> e2 \<in> simpleFormedExpSet i"*)
(*(neg (eqn (Const (index i)) (Const (index j))))*)
(*
definition simpleAssignment::"nat \<Rightarrow> statement \<Rightarrow>bool" where
"simpleAssignment i as \<equiv>
\<exists> v e.  (IVar v \<in>simpleFormedExpSet i)
 \<and>(e \<in>simpleFormedExpSet i) \<and>as= assign (v, e)"

definition wellAssignment::"nat\<Rightarrow>statement \<Rightarrow>bool" where
"wellAssignment j  as \<equiv>
\<exists> v e.  (IVar v \<in>simpleFormedExpSet j)
 \<and>(wellFormedIteExp  j e) \<and>as= assign (v, e)"

definition wellFormedParallelStatement::"nat \<Rightarrow> nat \<Rightarrow> statement \<Rightarrow>bool" where
"wellFormedParallelStatement N i S \<equiv>\<exists> ps.  (S=parallelList (map ps (down N) ) 
\<and>((\<forall>i. simpleAssignment i (ps i) )| (\<forall>j. wellAssignment  j (ps j)) ))"
*)
(*inductive_set reachableSet :: "formula set \<Rightarrow> rule set \<Rightarrow> state set" 
  for inis::"formula set" and rules::"rule set" where

  initState: "\<lbrakk>formEval ini s; ini \<in> inis\<rbrakk> \<Longrightarrow> s \<in> reachableSet inis rules" |

  oneStep: "\<lbrakk>s \<in> reachableSet inis rules;
             r \<in> rules;
             formEval (pre r) s\<rbrakk> \<Longrightarrow>
             trans (act r) s \<in> reachableSet inis rules"*)
(*
lemma absExpForm:
  assumes a:"s dontCareVar =dontCare" and a2:"
  e \<in>simpleFormedExpSet i" and a3:"f \<in>simpleFormedFormulaSet i"
  shows "((absTransfExp  M e\<noteq>dontCareExp\<longrightarrow>
  expEval (absTransfExp  M e) (abs1 M s)  =absTransfConst M (expEval e s))) \<and>
  ((absTransfForm  M f\<noteq>dontCareForm \<longrightarrow>formEval f s 
\<longrightarrow>formEval (absTransfForm  M f) (abs1 M s)))"
   (is "?Pe e s \<and>   ?Pf f s")
  using a2 and a3
proof(induct )

  fix x
  show "?Pe (IVar (Ident x)) s"
  proof(case_tac "EX n. (  (s (Ident x))=(index n) )\<and> n>M")
      assume b1:"\<exists>n.  (s (Ident x)) = index n \<and> M < n "
      show "?Pe (IVar (Ident x)) s"
        by(cut_tac b1 ,auto)
    next
      assume b1:"\<not>(\<exists>n.  (s (Ident x)) = index n \<and> M < n )"
      show "?Pe (IVar (Ident x)) s"
      proof(cut_tac  b1, case_tac "(s (Ident x))",auto)qed
  qed
    by auto
  show "?Pe (IVar x) s"
  proof(case_tac x) 
    fix x1
    assume a1:"x=Ident x1"
    show "?Pe (IVar x) s"
    proof(case_tac "EX n. (  (s x)=(index n) )\<and> n>M")
      assume b1:"\<exists>n.  (s x) = index n \<and> M < n "
      show "?Pe (IVar x) s"
        by(cut_tac b1 a1,auto)
    next
      assume b1:"\<not>(\<exists>n.  (s x) = index n \<and> M < n )"
      show "?Pe (IVar x) s"
      proof(cut_tac a1 b1, case_tac "(s x)",auto)qed
    qed
  next
    fix x21 x22
    assume a1:"x = Para x21 x22"
    show "?Pe (IVar x) s"
    proof(case_tac "x22 >M")
      assume b1:"x22>M "
      show "?Pe (IVar x) s"
        by(cut_tac a b1 a1,simp)
    next
      assume b1:"~x22>M "
      show "?Pe (IVar x) s"
      proof(case_tac "EX n. (  (s x)=(index n) )\<and> n>M",cut_tac a b1 a1,force)
        assume c1:"\<nexists>n. s x = index n \<and> M < n"
        have c2:" expEval (absTransfExp M (IVar x)) (abs1 M s) =s (Para x21 x22)"
        proof(cut_tac a b1 a1 c1,force)qed
        have c3:"absTransfConst M (expEval (IVar x) s)=s (Para x21 x22)"
          apply(cut_tac a b1 a1 c1,case_tac "s x",auto) done
        show "?Pe (IVar x) s"
          using c2 c3 by presburger
      qed
    qed
  next
    assume a1:"x=dontCareVar"
    show "?Pe (IVar x) s"
      by (simp add: a1)

  qed
next
  fix x
  show "?Pe (Const x) s"
  proof(case_tac x,auto)qed
next
  fix b e1 e2
  assume a1:"?Pe e1 s" and a2:"?Pe e2 s"
  and a3:"?Pf b s"
  show "?Pe (iteForm b e1 e2) s"
  proof(cut_tac a1 a2 a3,case_tac "((absTransfForm M b) \<noteq> dontCareForm 
  \<and>(absTransfExp M e1) \<noteq> dontCareExp \<and>
  (absTransfExp M e2) \<noteq> dontCareExp)",auto)
  qed
next
  show "?Pe (dontCareExp) s"
    by auto
next
  fix e1 e2
  assume  a1:"?Pe e1 s" and a2:"?Pe e2 s"
  show "?Pf (eqn e1 e2) s"
  proof(cut_tac a1 a2 ,case_tac "( 
  (absTransfExp M e1) = dontCareExp \<or>
  (absTransfExp M e2) = dontCareExp)",auto)

(*
inductive isBoolVal::"state \<Rightarrow> expType \<Rightarrow> bool" where
"s(v) =boolV b\<Longrightarrow>isBoolVal s (IVar v) " | 
"  c =(boolV b) \<Longrightarrow>isBoolVal s (Const c)" | 
"
  ( (isBoolVal s e1)\<and> (isBoolVal s e2)) \<Longrightarrow>isBoolVal s (iteForm f e1 e2)   "|
"s(v) =(enum tn vn) \<Longrightarrow>\<not>isBoolVal s (IVar v) "

inductive isEnumVal::"state \<Rightarrow> expType \<Rightarrow> bool" where
"s(v) =(enum tn vn) \<Longrightarrow>isEnumVal s (IVar v) " | 
" c =(enum tn vn) \<Longrightarrow> isEnumVal s (Const c)  " | 
"
  ( (isEnumVal s e1) \<and> (isEnumVal s e2)) \<Longrightarrow>isEnumVal s (iteForm f e1 e2) "

inductive isIndexVal::"state \<Rightarrow> expType \<Rightarrow> bool" where
"s(v) =(index vn) \<Longrightarrow>isIndexVal s (IVar v) " | 
" c =(index vn) \<Longrightarrow> isIndexVal s (Const c)  " | 

"
  ( (isIndexVal s e1) \<and> (isIndexVal s e2)) \<Longrightarrow>isIndexVal s (iteForm f e1 e2) "

primrec isBoolVal::"state \<Rightarrow> expType \<Rightarrow> bool" where
"isBoolVal s (IVar v) = (if (\<exists>b. s(v) =(boolV b)) then True else False)" | 
"isBoolVal s (Const c) = (if (\<exists>b. c =(boolV b)) then True else False)" | 
"isBoolVal s (iteForm f e1 e2) = 
  ( (isBoolVal s e1)\<and> (isBoolVal s e2))"

primrec isEnumVal::"state \<Rightarrow> expType \<Rightarrow> bool" where
"isEnumVal s (IVar v) = (if (\<exists>tn vn. s(v) =(enum tn vn)) then True else False)" | 
"isEnumVal s (Const c) = (if (\<exists>tn vn. c =(enum tn vn)) then True else False)" | 
"isEnumVal s (iteForm f e1 e2) = 
  ( (isEnumVal s e1) \<and> (isEnumVal s e2))"

primrec isIndexVal::"state \<Rightarrow> expType \<Rightarrow> bool" where
"isIndexVal s (IVar v) = (if (\<exists> vn. s(v) =(index vn)) then True else False)" | 
"isIndexVal s (Const c) = (if (\<exists> vn. c =(index vn)) then True else False)" | 
"isIndexVal s (iteForm f e1 e2) = 
  ( (isIndexVal s e1) \<and> (isIndexVal s e2))"*)
*)