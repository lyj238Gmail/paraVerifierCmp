theory nMutual1
  imports CMP
begin


subsection \<open>Definitions\<close>

text \<open>Represents the four states: idle, try, critical, exit\<close>

definition I :: scalrValueType where [simp]: "I \<equiv> enum ''control'' ''I''"
definition T :: scalrValueType where [simp]: "T \<equiv> enum ''control'' ''T''"
definition C :: scalrValueType where [simp]: "C \<equiv> enum ''control'' ''C''"
definition E :: scalrValueType where [simp]: "E \<equiv> enum ''control'' ''E''"

definition true :: scalrValueType where [simp]: "true \<equiv> boolV True"
definition false :: scalrValueType where [simp]: "false \<equiv> boolV False"

text \<open>Initial condition: all processes in idle.
  \<forall>i. n[i] = I
\<close>
definition initSpec0 :: "nat \<Rightarrow> formula" where
  "initSpec0 N \<equiv> (\<forall>\<^sub>fi. IVar (Para ''n'' i) =\<^sub>f Const I) N"

text \<open>Initial condition: x is True
  x = True
\<close>
definition initSpec1 :: formula where
  "initSpec1 \<equiv> IVar (Ident ''x'') =\<^sub>f Const true"

text \<open>There cannot be one state in exit and another in critical or exit.
  n[i] = E \<longrightarrow> (\<forall>j. i \<noteq> j \<longrightarrow> n[j] \<noteq> C \<and> n[j] \<noteq> E)
\<close>
definition invAux :: "nat \<Rightarrow> nat \<Rightarrow> formula" where
"invAux N i \<equiv> IVar (Para ''n'' i) =\<^sub>f Const E \<longrightarrow>\<^sub>f
                forallFormExcl 
          (\<lambda>j. \<not>\<^sub>f IVar (Para ''n'' j) =\<^sub>f Const C  \<and>\<^sub>f \<not>\<^sub>f IVar (Para ''n'' j) =\<^sub>f Const E) i N"  
 (* "invAux N i \<equiv> IVar (Para ''n'' i) =\<^sub>f Const E \<longrightarrow>\<^sub>f
                forallFormExcl (\<lambda>j. \<not>\<^sub>f IVar (Para ''n'' j) =\<^sub>f Const C) i N \<and>\<^sub>f
                forallFormExcl (\<lambda>j. \<not>\<^sub>f IVar (Para ''n'' j) =\<^sub>f Const E) i N"*)

text \<open>Try enter critical region
  n[i] = I \<rightarrow> n[i] := T
\<close>
definition n_Try :: "nat \<Rightarrow> rule" where
  "n_Try i \<equiv>
    IVar (Para ''n'' i) =\<^sub>f Const I
   \<triangleright>
    assign (Para ''n'' i, Const T)"

text \<open>Enter critical region
  n[i] = T \<and> x = True \<rightarrow> n[i] := C; x := False
\<close>
definition n_Crit :: "nat \<Rightarrow> rule" where
  "n_Crit i \<equiv>
    IVar (Para ''n'' i) =\<^sub>f Const T \<and>\<^sub>f
    IVar (Ident ''x'') =\<^sub>f Const true
   \<triangleright>
    assign (Para ''n'' i, Const C) ||
    assign (Ident ''x'', Const false)"

text \<open>Exit critical region
  n[i] = C \<rightarrow> n[i] := E
\<close>
definition n_Exit :: "nat \<Rightarrow> rule" where
  "n_Exit i \<equiv>
    IVar (Para ''n'' i) =\<^sub>f Const C
   \<triangleright>
    assign (Para ''n'' i, Const E)"

text \<open>Move to idle
  n[i] = E \<rightarrow> n[i] := I; x := True
\<close>
definition n_Idle :: "nat \<Rightarrow> rule" where
  "n_Idle i \<equiv>
    IVar (Para ''n'' i) =\<^sub>f Const E
   \<triangleright>
    assign (Para ''n'' i, Const I) ||
    assign (Ident ''x'', Const true)"

subsection \<open>References\<close>

definition n_Crit_abs :: rule where
  "n_Crit_abs \<equiv>
    IVar (Ident ''x'') =\<^sub>f Const (boolV True)
   \<triangleright>
    assign (Ident ''x'', Const (boolV False))"

definition n_Idle_abs1 :: rule where
  "n_Idle_abs1 \<equiv>
    chaos \<triangleright> assign (Ident ''x'', Const true)"

definition n_Idle_abs2 :: "nat \<Rightarrow> rule" where
"n_Idle_abs2 M \<equiv>
    (\<forall>\<^sub>fj. ((\<not>\<^sub>f IVar (Para ''n'' j) =\<^sub>f Const (enum ''control'' ''C''))\<and>\<^sub>f
      (\<not>\<^sub>f IVar (Para ''n'' j) =\<^sub>f Const (enum ''control'' ''E'')))) M 
   \<triangleright>
    assign (Ident ''x'', Const (boolV True))"
  

subsection \<open>Individual tests\<close>

lemma absInitSpec:
  assumes "M \<le> N"
  shows "absTransfForm M (initSpec0 N) = initSpec0 M"
        "absTransfForm M initSpec1 = initSpec1"
  unfolding initSpec0_def initSpec1_def using assms by auto

lemma symInvAux:
  "symParamForm N (invAux N)"
  unfolding invAux_def
  apply (auto intro!: symParamFormImply symParamFormAnd symParamFormForall symParamFormForallExcl)
  unfolding symParamForm_def symParamForm2_def equivForm_def by auto

lemma symTry:
  "symParamRule N n_Try"
  "wellFormedStatement N (act (n_Try i))"
  "absTransfRule M (n_Try i) = (if i \<le> M then n_Try i else chaos \<triangleright> skip)"
  unfolding n_Try_def symParamRule_def by auto

lemma symCrit:
  "symParamRule N n_Crit"
  "wellFormedStatement N (act (n_Crit i))"
  "absTransfRule M (n_Crit i) = (if i \<le> M then n_Crit i else n_Crit_abs)"
  unfolding n_Crit_def n_Crit_abs_def symParamRule_def by auto

lemma symExit:
  "symParamRule N n_Exit"
  "wellFormedStatement N (act (n_Exit i))"
  "absTransfRule M (n_Exit i) = (if i \<le> M then n_Exit i else chaos \<triangleright> skip)"
  unfolding n_Exit_def symParamRule_def by auto

lemma symIdle:
  "symParamRule N n_Idle"
  "wellFormedStatement N (act (n_Idle i))"
  "absTransfRule M (n_Idle i) = (if i \<le> M then n_Idle i else n_Idle_abs1)"
  unfolding n_Idle_def n_Idle_abs1_def symParamRule_def by auto

text \<open>Move to idle, strengthened:
  n[i] = E \<and>
  (\<forall>j. i \<noteq> j \<longrightarrow> n[j] \<noteq> C) \<and>
  (\<forall>j. i \<noteq> j \<longrightarrow> n[j] \<noteq> E) \<rightarrow> n[i] := I; x := True
\<close>
definition n_Idle2_ref :: "nat \<Rightarrow> nat \<Rightarrow> rule" where
  "n_Idle2_ref N i \<equiv>
    IVar (Para ''n'' i) =\<^sub>f Const E \<and>\<^sub>f
    forallFormExcl (\<lambda>j.( \<not>\<^sub>f IVar (Para ''n'' j) =\<^sub>f Const C)  \<and>\<^sub>f
       \<not>\<^sub>f IVar (Para ''n'' j) =\<^sub>f Const E) i N
   \<triangleright>
    assign (Para ''n'' i, Const I) ||
    assign (Ident ''x'', Const true)"
 
lemma n_Idle2Eq:
  "strengthenRule2 (invAux N i) (n_Idle i) = n_Idle2_ref N i"
  by (auto simp add: invAux_def n_Idle_def n_Idle2_ref_def)

lemma wellFormedIdle2:
  "symParamRule N (n_Idle2_ref N)"
  "wellFormedStatement N (act (n_Idle2_ref N i))"
  unfolding n_Idle2_ref_def
   apply (auto intro!: symParamRuleI symParamFormAnd symParamFormForallExcl)
  unfolding symParamForm_def symParamForm2_def symParamStatement_def by auto

lemma absIdle2:
  "M \<le> N \<Longrightarrow> absTransfRule M (n_Idle2_ref N i) = (if i \<le> M then n_Idle i else n_Idle_abs2 M)"
  unfolding n_Idle_def n_Idle_abs2_def n_Idle2_ref_def by auto

 


definition n_Trys::" nat\<Rightarrow>rule set" where [simp]:
  "n_Trys N== oneParamCons N  n_Try"

definition n_Crits::" nat\<Rightarrow>rule set" where [simp]:
  "n_Crits N== oneParamCons N  n_Crit"

definition n_Exits::" nat\<Rightarrow>rule set" where [simp]:
  "n_Exits N== oneParamCons N  n_Exit"

definition n_Idles::" nat\<Rightarrow>rule set" where [simp]:
  "n_Idles N== oneParamCons N  n_Idle"

definition rules' :: "nat \<Rightarrow> rule set" where [simp]:
  "rules' N \<equiv>  (n_Trys N) \<union> (n_Crits N)  \<union>
    (n_Exits N) \<union>
    (n_Idles N) 
   "
lemma n_TrysIsSym:
  "symProtRules' N (n_Trys N)"
  using symTry(1) n_Trys_def symParaRuleInfSymRuleSet by auto

lemma n_CritsIsSym:
  "symProtRules' N (n_Crits N)"
  using n_Crits_def symCrit(1) symParaRuleInfSymRuleSet by auto 

lemma n_ExitsIsSym:
  "symProtRules' N (n_Exits N)"
  using n_Exits_def symExit(1) symParaRuleInfSymRuleSet by auto 

lemma n_IdlesIsSym:
  "symProtRules' N (n_Idles N)"
  using n_Idles_def symIdle(1) symParaRuleInfSymRuleSet by auto

lemma rulesSym':
  shows "symProtRules' N (rules' N)"
  using n_CritsIsSym n_ExitsIsSym n_IdlesIsSym n_TrysIsSym rules'_def symProtRulesUnion by presburger
    
 
definition pair1:: "((nat\<Rightarrow>formula)\<times>(nat\<Rightarrow>formula))" where [simp]:
 "pair1 ==(%i. IVar (Para ''n'' i) =\<^sub>f Const E,
               (%j.  \<not>\<^sub>f IVar (Para ''n'' j) =\<^sub>f Const C  \<and>\<^sub>f \<not>\<^sub>f IVar (Para ''n'' j) =\<^sub>f Const E) )"

definition F::"((nat\<Rightarrow>formula)\<times>(nat\<Rightarrow>formula)) set" where [simp]:
"F \<equiv> {pair1}"

  
definition n_Idle2s::" nat \<Rightarrow>rule set" where [simp]:
  "n_Idle2s N==
  (oneParamCons N  (%i. (strengthenRule2  (constrInvByExcl pair1 i N) (n_Idle i))))"

  
definition rules2' :: "nat \<Rightarrow> rule set" where [simp]:
  "rules2' N \<equiv>  (n_Trys N) \<union> (n_Crits N)  \<union>
    (n_Exits N) \<union>
    (n_Idle2s N) "

 

lemma n_Idle2sIsSym:
  "symProtRules' N (n_Idle2s N)"
  apply(unfold n_Idle2s_def)
  apply(rule symParaRuleInfSymRuleSet)
  using invAux_def n_Idle2Eq wellFormedIdle2(1) by auto 
 
lemma rule2'IsSym:
  shows " symProtRules' N (rules2' N)"
  using n_CritsIsSym n_ExitsIsSym n_Idle2sIsSym n_TrysIsSym rules2'_def symProtRulesUnion by presburger 
   
lemma invOnStateOfN' [simp,intro]:
  assumes a:"  reachableUpTo fs 
  rs k s"
  shows "  fs=({initSpec0 N} Un { initSpec1}) \<longrightarrow>rs=(rules2' N)\<longrightarrow>i\<le>N \<longrightarrow>
  (s  (Para ( ''n'') i) = I \<or> s  (Para ( ''n'') i) = T
  \<or>s  (Para ( ''n'') i) = C \<or>s  (Para ( ''n'') i) = E)" (is "?P\<longrightarrow>?Q\<longrightarrow>?Q1\<longrightarrow>?R s")
  using  a
proof( induct)
  case (reachableSet0 fs s rs)
  then show ?case 
    apply(unfold initSpec1_def initSpec0_def, auto)
    done
next
  case (reachableSetNext fs rs n s g a)
  
  
  show ?case 
  proof((rule impI)+)
    assume b1:"fs = {initSpec0 N} \<union> {initSpec1}" and
    b2:"rs = rules2' N " and b4:"i\<le>N"
    let ?r="(g \<triangleright> a)"
    have b3:"(\<exists>i. i \<le> N \<and> ?r =   (n_Try i)) \<or>
     (\<exists>i. i \<le> N \<and> ?r =   (n_Crit i)) \<or>
      (\<exists>i. i \<le> N \<and> ?r =   (n_Exit i)) \<or> 
      (\<exists> f i. f \<in> F  \<and> i \<le> N \<and> ?r =   (strengthenRule2  (constrInvByExcl f i N) (n_Idle i))) "
      using b2 reachableSetNext.hyps(3) by auto
    moreover
    {assume c1:"\<exists> i. i\<le>N\<and>?r=n_Try  i"
     from c1 obtain i where c1:"i\<le>N\<and>?r=n_Try  i"
       by blast
     have "?R (trans1 a s)"
       apply(cut_tac c1, unfold n_Try_def,auto)
       by (metis C_def E_def I_def T_def b1 b2 b4 reachableSetNext.hyps(2))
   }
  moreover
    {assume c1:"\<exists> i. i\<le>N\<and>?r=n_Crit  i"
     from c1 obtain i where c1:"i\<le>N\<and>?r=n_Crit  i"
       by blast
     have "?R (trans1 a s)"
       apply(cut_tac c1, unfold n_Crit_def,auto)
       by (metis C_def E_def I_def T_def b1 b2 b4 reachableSetNext.hyps(2))
   }
  moreover
    {assume c1:"\<exists> i. i\<le>N\<and>?r=n_Crit  i"
     from c1 obtain i where c1:"i\<le>N\<and>?r=n_Crit  i"
       by blast
     have "?R (trans1 a s)"
       apply(cut_tac c1, unfold n_Crit_def,auto)
       by (metis C_def E_def I_def T_def b1 b2 b4 reachableSetNext.hyps(2))
   }
  moreover
    {assume c1:"\<exists> i. i\<le>N\<and>?r=n_Exit  i"
     from c1 obtain i where c1:"i\<le>N\<and>?r=n_Exit  i"
       by blast
     have "?R (trans1 a s)"
       apply(cut_tac c1, unfold n_Exit_def,auto)
       by (metis C_def E_def I_def T_def b1 b2 b4 reachableSetNext.hyps(2))
   }
   moreover
    {assume c1:"\<exists> f i. f \<in> F  \<and> i \<le> N \<and>?r= (strengthenRule2  (constrInvByExcl f i N) (n_Idle i))"
     from c1 obtain f i where c1:"f\<in>F \<and>i\<le>N\<and>?r= (strengthenRule2  (constrInvByExcl f i N) (n_Idle i))"
       by blast
     have "?R (trans1 a s)"
       apply(cut_tac c1, unfold n_Idle_def,auto)
       by (metis C_def E_def I_def T_def b1 b2 b4 reachableSetNext.hyps(2))
   }
   ultimately show "?R (trans1 a s)"
     by satx
 qed 
qed
 
lemma symPreds:
  shows "symPredSet' N ({initSpec0 N} Un { initSpec1})"
proof -
  let ?f="\<lambda> j . (\<forall>\<^sub>fi. IVar (Para ''n'' i) =\<^sub>f Const I) N"
  let ?S1="oneParamFormCons N ?f"
  have "{initSpec0 N}=?S1"
    
    using initSpec0_def oneParamFormCons_def  by auto

  have "symPredSet' N ?S1" thm symParamFormForall
    apply(rule  symParaFormInfSymFormSet) 
    apply(rule symParamFormForall)
    apply(unfold symParamForm2_def)
    apply(unfold  equivForm_def,auto)
    done
    
  have "symPredSet' N ({initSpec0 N})"
    using \<open>symPredSet' N (oneParamFormCons N (\<lambda>j. (\<forall>\<^sub>fi. IVar (Para ''n'' i) =\<^sub>f Const I) N))\<close>
      \<open>{initSpec0 N} = oneParamFormCons N (\<lambda>j. (\<forall>\<^sub>fi. IVar (Para ''n'' i) =\<^sub>f Const I) N)\<close> by auto

  let ?f="\<lambda> j. IVar (Ident ''x'') =\<^sub>f Const true"
  let ?S1="oneParamFormCons N ?f" 
  have "{initSpec1 }=?S1"
    
    using initSpec1_def oneParamFormCons_def  by auto

  have "symPredSet' N ?S1" thm symParamFormForall
    apply(rule  symParaFormInfSymFormSet)  
    apply(unfold symParamForm_def)
    apply(unfold  equivForm_def,auto)
    done

  have "symPredSet' N ({initSpec1})"
    using \<open>symPredSet' N (oneParamFormCons N (\<lambda>j. IVar (Ident ''x'') =\<^sub>f Const true))\<close> 
      \<open>{initSpec1} = oneParamFormCons N (\<lambda>j. IVar (Ident ''x'') =\<^sub>f Const true)\<close> by auto
  show "symPredSet' N ({initSpec0 N} \<union> {initSpec1})"
    using \<open>symPredSet' N {initSpec0 N}\<close> \<open>symPredSet' N {initSpec1}\<close> symPredsUnion by blast
qed

definition absRules :: " rule set" where [simp]:
  "absRules \<equiv> {r.
    (\<exists>i. i \<le> 1 \<and> r = n_Try i) \<or>
    (\<exists>i. i \<le> 1 \<and> r = n_Crit i) \<or>
    (\<exists>i. i \<le> 1 \<and> r = n_Exit i) \<or>
    (\<exists>i. i \<le> 1 \<and> r = n_Idle i) 
   }\<union>{n_Idle_abs2 1}\<union>{n_Crit_abs } \<union> {chaos \<triangleright> skip} "

 
lemma absTrys:
  assumes a:"1 <N" and b:"M=1"
  shows " (%i. absTransfRule M (n_Try i))`{i. i\<le>N} =(n_Try`{i. i\<le>M})  \<union> {(chaos \<triangleright> skip)} "
proof -
  have c1:"{i. i\<le>N} =({i. i\<le>M} \<union> {i. M<i\<and>i\<le>N})"
    apply (cut_tac a b,auto) done
  have c2:"(%i. absTransfRule M (n_Try i))`{i. i\<le>N} =
      (%i. absTransfRule M (n_Try i))`{i. i\<le>M} Un  (%i. absTransfRule M (n_Try i))`{i. M<i\<and>i\<le>N}"
    using c1 by blast 
  have c3:" (%i. absTransfRule M (n_Try i))`{i. i\<le>M} =(n_Try`{i. i\<le>M})"
    apply (cut_tac a b,auto)
    using symTry(3) apply auto[1]
    by (simp add: symTry(3)) 

  have c4:" (%i. absTransfRule M (n_Try i))`{i. M<i\<and>i\<le>N} =  {(chaos \<triangleright> skip)}"
     apply (cut_tac a b,auto)
    using symTry(3) apply auto[1]
    using symTry(3) by auto 
  show ?thesis
    by (simp add: c2 c3 c4)
qed   

lemma absExits:
  assumes a:"1 <N" and b:"M=1"
  shows " (%i. absTransfRule M (n_Exit i))`{i. i\<le>N} =(n_Exit`{i. i\<le>M})  \<union> {(chaos \<triangleright> skip)} "
proof -
  have c1:"{i. i\<le>N} =({i. i\<le>M} \<union> {i. M<i\<and>i\<le>N})"
    apply (cut_tac a b,auto) done
  have c2:"(%i. absTransfRule M (n_Exit i))`{i. i\<le>N} =
      (%i. absTransfRule M (n_Exit i))`{i. i\<le>M} Un  (%i. absTransfRule M (n_Exit i))`{i. M<i\<and>i\<le>N}"
    using c1 by blast 
  have c3:" (%i. absTransfRule M (n_Exit i))`{i. i\<le>M} =(n_Exit`{i. i\<le>M})"
    apply (cut_tac a b,auto)
    using symExit(3) apply auto[1]
    by (simp add: symExit(3)) 

  have c4:" (%i. absTransfRule M (n_Exit i))`{i. M<i\<and>i\<le>N} =  {(chaos \<triangleright> skip)}"
     apply (cut_tac a b,auto)
    using symExit(3) apply auto[1]
    using symExit(3) by auto 
  show ?thesis
    by (simp add: c2 c3 c4)
qed 

lemma absCrits:
  assumes a:"1 <N" and b:"M=1"
  shows " (%i. absTransfRule M (n_Crit i))`{i. i\<le>N} =(n_Crit`{i. i\<le>M})  \<union> {n_Crit_abs} "
proof -
  have c1:"{i. i\<le>N} =({i. i\<le>M} \<union> {i. M<i\<and>i\<le>N})"
    apply (cut_tac a b,auto) done
  have c2:"(%i. absTransfRule M (n_Crit i))`{i. i\<le>N} =
      (%i. absTransfRule M (n_Crit i))`{i. i\<le>M} Un  (%i. absTransfRule M (n_Crit i))`{i. M<i\<and>i\<le>N}"
    using c1 by blast 
  have c3:" (%i. absTransfRule M (n_Crit i))`{i. i\<le>M} =(n_Crit`{i. i\<le>M})"
    apply (cut_tac a b,auto)
    using symCrit(3) apply auto[1]
    by (simp add: symCrit(3)) 

  have c4:" (%i. absTransfRule M (n_Crit i))`{i. M<i\<and>i\<le>N} =  {n_Crit_abs}"
     apply (cut_tac a b,auto)
    using symCrit(3) apply auto[1]
    using symCrit(3) by auto 
  show ?thesis
    using c2 c3 c4 by auto 
qed    
  
lemma absIdle2s:
  assumes a:"1 <N" and b:"M=1"
  shows " (%i. absTransfRule M  (strengthenRule2  (constrInvByExcl pair1 i N) (n_Idle i)))`{i. i\<le>N} 
  =(n_Idle`{i. i\<le>M})  \<union> {n_Idle_abs2 M} "
proof -
  have c1:"{i. i\<le>N} =({i. i\<le>M} \<union> {i. M<i\<and>i\<le>N})"
    apply (cut_tac a b,auto) done
  have c2:"(%i. absTransfRule M (strengthenRule2  (constrInvByExcl pair1 i N) (n_Idle i)))`{i. i\<le>N} =
      (%i. absTransfRule M (strengthenRule2  (constrInvByExcl pair1 i N) (n_Idle i)))`{i. i\<le>M} Un 
       (%i. absTransfRule M (strengthenRule2  (constrInvByExcl pair1 i N) (n_Idle i)))`{i. M<i\<and>i\<le>N}"
    using c1 by blast 
  have c3:" (%i. absTransfRule M (strengthenRule2  (constrInvByExcl pair1 i N) (n_Idle i)))`{i. i\<le>M}
   =(n_Idle`{i. i\<le>M})"
    apply (cut_tac a b,rule)
    using absIdle2 invAux_def n_Idle2Eq apply auto[1]
    
   by (auto simp add: symIdle(3) n_Idle_def) 
  
  have c4:" (%i. absTransfRule M (strengthenRule2  (constrInvByExcl pair1 i N) (n_Idle i)))`{i. M<i\<and>i\<le>N}
   =  {n_Idle_abs2 M}"
     apply (cut_tac a b,rule) 
    using absIdle2 invAux_def n_Idle2Eq nat_le_linear not_less apply auto[1]
    apply auto
    by (auto simp add: symIdle(3) n_Idle_def n_Idle_abs2_def) 
  show ?thesis
    using c2 c3 c4 by auto 
qed      


definition absRules' :: " rule set" where [simp]:
  "absRules' \<equiv> (n_Idle`{i. i\<le>1}) \<union>(n_Crit`{i. i\<le>1})\<union>(n_Try`{i. i\<le>1})Un(n_Exit`{i. i\<le>1})
   \<union>{n_Idle_abs2 1}\<union>{n_Crit_abs } \<union> {chaos \<triangleright> skip} "

lemma absRulesRef':
  assumes a:"1 <N" and b:"M=1"
  shows "absRules' = {r'. \<exists>r. r \<in> rules2' N \<and> r' = absTransfRule M r}"
proof -
  have c1:"((%i. absTransfRule M (n_Try i))`{i. i\<le>N}\<union>
        (%i. absTransfRule M (n_Crit i))`{i. i\<le>N}\<union>
        (%i. absTransfRule M (n_Exit i))`{i. i\<le>N}\<union>
        (%i. absTransfRule M  (strengthenRule2  (constrInvByExcl pair1 i N) (n_Idle i)))`{i. i\<le>N})=
         {r'. \<exists>r. r \<in> rules2' N \<and> r' = absTransfRule M r}"
    by auto 
  have c2:"(((%i. absTransfRule M (n_Try i))`{i. i\<le>N}\<union>
        (%i. absTransfRule M (n_Crit i))`{i. i\<le>N}\<union>
        (%i. absTransfRule M (n_Exit i))`{i. i\<le>N}\<union>
        (%i. absTransfRule M  (strengthenRule2  (constrInvByExcl pair1 i N) (n_Idle i)))`{i. i\<le>N}))=
      absRules'"
    using absExits absCrits absIdle2s absTrys a b apply auto done
    
  show ?thesis
    using c1 c2     by auto
qed
axiomatization  where axiomOnAbsProt [simp,intro]:
   "\<forall>i f s.
       f \<in> F \<longrightarrow>
       reachableUpTo {f'. \<exists>f. f \<in> {initSpec0 N} \<union> {initSpec1} \<and> f' = absTransfForm M f}
        absRules' i s \<longrightarrow>
       formEval (constrInv f 0 1) s"
 

lemma absProtSim':
  assumes  a2:"M<N" and a3:"M=1"
  shows "\<forall>f s. f\<in>constrInvByExcls F  N \<longrightarrow> 
  reachableUpTo  ({initSpec0 N} Un { initSpec1}) (rules' N) i s \<longrightarrow> formEval f s"
proof(rule_tac ?rs2.0="rules2' N" in   CMP)
  show " \<And>r. r \<in> rules' N \<longrightarrow> wellFormedRule N r"
  proof(rule impI)
    fix r
    assume b1:"r \<in> rules' N"
    have " (\<exists>i. i \<le> N \<and> r= n_Try i)\<or>(\<exists>i. i \<le> N  \<and> r= n_Crit i)\<or>
      (\<exists>i. i \<le> N \<and>r= n_Exit i)\<or>(\<exists>i. i \<le> N \<and>r=n_Idle i)"
      apply(cut_tac b1,auto)done
    moreover
    {assume b1:"\<exists>i. i \<le> N \<and> r= n_Try i"
      from b1 obtain i where b1:"i \<le> N \<and> r= n_Try i"
        by blast
        have "wellFormedRule N r"
          by (metis symTry(2) act.simps b1 wellFormedRule.elims(3))
      }  

    moreover
    {assume b1:"\<exists>i. i \<le> N \<and> r= n_Crit i"
      from b1 obtain i where b1:"i \<le> N \<and> r= n_Crit i"
        by blast
       have "wellFormedRule N r"
         by (metis act.simps b1 symCrit(2) wellFormedRule.elims(3)) 
     } 

    moreover
    {assume b1:"\<exists>i. i \<le> N \<and> r= n_Idle i"
      from b1 obtain i where b1:"i \<le> N \<and> r= n_Idle i"
        by blast
       have "wellFormedRule N r"
               
         by (metis act.simps b1 symIdle(2) wellFormedRule.elims(3))
     }  

     moreover
    {assume b1:"\<exists>i. i \<le> N \<and> r= n_Exit i"
      from b1 obtain i where b1:"i \<le> N \<and> r= n_Exit i"
        by blast
       have "wellFormedRule N r"
         by (metis act.simps b1 symExit(2) wellFormedRule.elims(3))
               
     
     }  
     ultimately show "wellFormedRule N r"
       by auto
   qed
 next
   show "\<forall>f. f \<in> F \<longrightarrow> symPair f N"
   proof(rule allI,rule impI)
     fix f
     assume c1:"f \<in> F"
     show "symPair f N"
       apply(cut_tac a1 c1,simp) 
       apply(rule conjI)
       apply(unfold symParamForm_def)
       apply((rule allI)+,(rule impI)+)
        apply(unfold equivForm_def,force)
       apply((rule allI)+,(rule impI)+)
       apply(force)
       done
   qed
 next
 
next
  show "symProtRules' N (rules' N)"
    using rulesSym' by blast
next
  show "symPredSet' N ({initSpec0 N} \<union> {initSpec1})"
    using symPreds by blast

next
  show "M \<le> N"
    apply (cut_tac  a2,arith) done
next
  show " \<forall>s i f.  reachableUpTo ({initSpec0 N} \<union> {initSpec1}) (rules2' N) i s \<longrightarrow>
  f \<in> F \<longrightarrow> (\<forall>v. v \<in> varOfForm (constrInv f 0 1) \<longrightarrow> s v = abs1 M s v)"
    apply(cut_tac  a3,  auto simp del:initSpec0_def initSpec1_def rules2'_def )
     
    apply (smt C_def E_def I_def T_def Un_insert_right a2 absTransfConstEnum invOnStateOfN' less_imp_le sup_bot.comm_neutral)
    by (smt C_def E_def I_def T_def Un_insert_right a2 absTransfConstEnum invOnStateOfN' le_Suc_eq less_imp_le not_less sup_bot.comm_neutral)
 
   
next
  show "\<forall>r'. r' \<in> rules2' N \<longrightarrow>
         (\<exists>r f i. f \<in> F \<and> r \<in> rules' N \<and> i \<le> N  \<and> r' = strengthenRule2 (constrInvByExcl f i N) r) \<or>
         r' \<in> rules' N"
    apply(unfold rules2'_def rules'_def)
    apply auto
    done
next
  show " symProtRules' N (rules2' N)"
    using rule2'IsSym by blast 
next
  show " \<forall>r. r \<in> rules' N \<longrightarrow> (\<exists>f. f \<in> constrInvByExcls F N \<and> strengthenRule2 f r \<in> rules2' N)
   \<or> r \<in> rules2' N"
  apply(unfold rules2'_def rules'_def)
    apply auto
    done
next 
  show "1 \<le> N"
    using a2 a3 by arith
  
next 
  show "\<forall>i f s.
       f \<in> F \<longrightarrow>
       reachableUpTo {f'. \<exists>f. f \<in> {initSpec0 N} \<union> {initSpec1} \<and> f' = absTransfForm M f}
        {r'. \<exists>r. r \<in> rules2' N \<and> r' = absTransfRule M r} i s \<longrightarrow>
       formEval (constrInv f 0 1) s"
  
    using a2 a3 absRulesRef' axiomOnAbsProt by auto
qed
end
