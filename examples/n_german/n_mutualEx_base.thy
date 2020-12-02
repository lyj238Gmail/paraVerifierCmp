(*  Title:      HOL/Auth/n_mutualEx_base.thy
    Author:     Yongjian Li and Kaiqiang Duan, State Key Lab of Computer Science, Institute of Software, Chinese Academy of Sciences
    Copyright    2016 State Key Lab of Computer Science, Institute of Software, Chinese Academy of Sciences
*)

(*header{*The n_mutualEx Protocol Case Study*} *)

theory n_mutualEx_base
  imports paraTheoryCmpzb
begin

section \<open>Main definitions\<close>

subsection \<open>Definitions of Constants\<close>

text \<open>Represents four states: idle, try, critical, exit\<close>
definition I :: scalrValueType where [simp]: "I \<equiv> enum ''control'' ''I''"
definition T :: scalrValueType where [simp]: "T \<equiv> enum ''control'' ''T''"
definition C :: scalrValueType where [simp]: "C \<equiv> enum ''control'' ''C''"
definition E :: scalrValueType where [simp]: "E \<equiv> enum ''control'' ''E''"

definition true :: scalrValueType where [simp]: "true \<equiv> boolV True"
definition false :: scalrValueType where [simp]: "false \<equiv> boolV False"

axiomatization  where axiomOnf2 [simp,intro]:
   "s  (Para ( ''n'') i) = I \<or> s  (Para ( ''n'') i) = T
  \<or>s  (Para ( ''n'') i) = C \<or>s  (Para ( ''n'') i) = E"

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


subsection \<open>The set of all actual rules w.r.t. a protocol instance with size $N$\<close>

definition rules :: "nat \<Rightarrow> rule set" where [simp]:
  "rules N \<equiv> {r.
    (\<exists>i. i \<le> N \<and> r = n_Try i) \<or>
    (\<exists>i. i \<le> N \<and> r = n_Crit i) \<or>
    (\<exists>i. i \<le> N \<and> r = n_Exit i) \<or>
    (\<exists>i. i \<le> N \<and> r = n_Idle i) 
   }"

lemma rulesIsSym:
  shows "symProtRules N (rules N)"
proof (simp only: symProtRules_def, (rule allI)+, rule impI)
  fix p r
  assume a1: "p permutes {x.   x \<le> N} \<and> r \<in> rules N"
  show "applySym2Rule p r \<in> rules N"
  proof -
    have b1:
     "(\<exists>i. i \<le> N \<and> r = n_Try i) \<or>
      (\<exists>i. i \<le> N \<and> r = n_Crit i) \<or>
      (\<exists>i. i \<le> N \<and> r = n_Exit i) \<or>
      (\<exists>i. i \<le> N \<and> r = n_Idle i) "
      using local.a1 by auto
    moreover
    {assume b1:"\<exists> i. i\<le>N\<and>r=n_Try  i"
      from b1 obtain i where b1:"i\<le>N\<and>r=n_Try  i"
        by blast
      from a1 have b2:"p i \<le> N"
        by (metis (mono_tags, lifting) b1 mem_Collect_eq permutes_def permutes_in_image)
      from b1 have b3:"applySym2Rule p r= n_Try  ( p i)" 
        by auto
      have "applySym2Rule p r \<in> rules N "
        by (simp add: b2 b3)
    }
    moreover
    {assume b1:"\<exists> i. i\<le>N\<and>r=n_Crit  i"
      from b1 obtain i where b1:"i\<le>N\<and>r=n_Crit  i"
        by blast
      from a1 have b2:"p i \<le> N"
        by (metis (mono_tags, lifting) b1 mem_Collect_eq permutes_def permutes_in_image)
      from b1 have b3:"applySym2Rule p r= n_Crit  ( p i)" 
        by auto
      have "applySym2Rule p r \<in> rules N "
        by (simp add: b2 b3)
    }
    moreover
    {assume b1:"\<exists> i. i\<le>N\<and>r=n_Idle  i"
      from b1 obtain i where b1:"i\<le>N\<and>r=n_Idle  i"
        by blast
      from a1 have b2:"p i \<le> N"
        by (metis (mono_tags, lifting) b1 mem_Collect_eq permutes_def permutes_in_image)
      from b1 have b3:"applySym2Rule p r= n_Idle  ( p i)" 
        by auto
      have "applySym2Rule p r \<in> rules N "
        by (simp add: b2 b3)
    }
    moreover
    {assume b1:"\<exists> i. i\<le>N\<and>r=n_Exit  i"
      from b1 obtain i where b1:"i\<le>N\<and>r=n_Exit  i"
        by blast
      from a1 have b2:"p i \<le> N"
        by (metis (mono_tags, lifting) b1 mem_Collect_eq permutes_def permutes_in_image)
      from b1 have b3:"applySym2Rule p r= n_Exit  ( p i)" 
        by auto
      have "applySym2Rule p r \<in> rules N "
        by (simp add: b2 b3)
    }
    ultimately show "applySym2Rule p r \<in> rules N"
      by blast
  qed
qed

(*definition rules'::"nat \<Rightarrow> rule set" where [simp]:
"rules' N \<equiv> {r.
(\<exists> p. p permutes {x. 1 \<le> x \<and> x \<le> N} \<and>r=n_Try  (p 1)) \<or>
(\<exists> p. p permutes {x. 1 \<le> x \<and> x \<le> N} \<and>r=n_Crit  (p 1)) \<or>
(\<exists> p. p permutes {x. 1 \<le> x \<and> x \<le> N} \<and>r=n_Exit  (p 1)) \<or>
(\<exists> p. p permutes {x. 1 \<le> x \<and> x \<le> N} \<and>r=n_Idle  (p 1)) 
}"

lemma rules'IsSym:
  shows "symProtRules N (rules' N)"

proof(simp only:symProtRules_def,(rule allI)+,rule impI)  *)

subsection \<open>Definitions of a formally parameterized invariant formulas\<close>

text \<open>If any process is in exit state, x must be False.
  n[i] = E \<longrightarrow> x = False
\<close>
definition inv_27 :: "nat \<Rightarrow> formula" where [simp]:
  "inv_27 i \<equiv>
    (implyForm (eqn (IVar (Para ''n'' i)) (Const E)) (eqn (IVar (Ident ''x'')) (Const false)))"

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


subsection \<open>Definitions of the set of invariant formula instances in a $N$-protocol instance\<close>

definition invariants :: "nat \<Rightarrow> formula set" where [simp]:
  "invariants N \<equiv> {f.
    
    (\<exists>i j. i \<le> N \<and> j \<le> N \<and> i \<noteq> j \<and> f = inv_7 i j) \<or>
    (\<exists>i j. i \<le> N \<and> j \<le> N \<and> i \<noteq> j \<and> f = inv_5 i j)
   }" 
(*(\<exists>i.   i \<le> N \<and> f = inv_27 i) \<or>*)
text \<open>Initial condition: all processes in idle.
  \<forall>i. n[i] = I
\<close>
definition initSpec0 :: "nat \<Rightarrow> formula" where [simp]:
  "initSpec0 N \<equiv> forallForm (down N) (\<lambda>i. eqn (IVar (Para ''n'' i)) (Const I))"

text \<open>Initial condition: x is True\<close>
definition initSpec1 :: formula where [simp]:
  "initSpec1 \<equiv> eqn (IVar (Ident ''x'')) (Const true)"

definition allInitSpecs::"nat \<Rightarrow> formula list" where [simp]:
  "allInitSpecs N \<equiv> [initSpec0 N, initSpec1]"

subsection \<open>Definitions of the set of invariant formula used in each rule
and each rule in middle protocol protPP\<close>

definition n_Idle_Ls :: "nat \<Rightarrow> nat\<Rightarrow> formula list" where [simp]:
  "n_Idle_Ls N i\<equiv> 
  (map (\<lambda>j. if (i=j) then chaos else inv_7 i j) (down N)) @
  (map (\<lambda>j. if (i=j) then chaos else inv_5 i j) (down N))"

definition n_Idle_Ls1 :: "nat \<Rightarrow> nat\<Rightarrow> formula list" where [simp]:
  "n_Idle_Ls1 N i\<equiv> 
  (map (\<lambda>j.   inv_7 i j) (down N)) @
  (map (\<lambda>j.   inv_5 i j) (down N))"
(*{f.
    (\<exists> j.   j \<le> N \<and> i \<noteq> j \<and> f = inv_7 i j) \<or>
    (\<exists> j.   j \<le> N \<and> i \<noteq> j \<and> f = inv_5 i j)}"*)

definition n_Idle_PP :: "nat \<Rightarrow> nat\<Rightarrow>rule" where [simp]:
  "n_Idle_PP N i\<equiv> strengthenR (n_Idle_Ls N i) [] (n_Idle i)"

definition n_Idle_PP1 :: "nat \<Rightarrow> nat\<Rightarrow>rule" where [simp]:
  "n_Idle_PP1 N i\<equiv> strengthenR1 (n_Idle_Ls1 N i) [] (n_Idle i)"

definition n_Idle_PP2 :: "nat \<Rightarrow> nat\<Rightarrow>rule" where [simp]:
  "n_Idle_PP2 N i\<equiv> strengthenR2 (n_Idle_Ls1 N i) [] (n_Idle i)"

definition rulesOfPP :: "nat \<Rightarrow> rule set" where [simp]:
  "rulesOfPP N \<equiv> {r.
    (\<exists>i. i \<le> N \<and> r = n_Try i) \<or>
    (\<exists>i. i \<le> N \<and> r = n_Crit i) \<or>
    (\<exists>i. i \<le> N \<and> r = n_Exit i) \<or>
    (\<exists>i. i \<le> N \<and> r = n_Idle_PP N i) 
   }"

definition rulesOfPP1 :: "nat \<Rightarrow> rule set" where [simp]:
  "rulesOfPP1 N \<equiv> {r.
    (\<exists>i. i \<le> N \<and> r = n_Try i) \<or>
    (\<exists>i. i \<le> N \<and> r = n_Crit i) \<or>
    (\<exists>i. i \<le> N \<and> r = n_Exit i) \<or>
    (\<exists>i. i \<le> N \<and> r = n_Idle_PP1 N i) 
   }"

definition rulesOfPP2 :: "nat \<Rightarrow> rule set" where [simp]:
  "rulesOfPP2 N \<equiv> {r.
    (\<exists>i. i \<le> N \<and> r = n_Try i) \<or>
    (\<exists>i. i \<le> N \<and> r = n_Crit i) \<or>
    (\<exists>i. i \<le> N \<and> r = n_Exit i) \<or>
    (\<exists>i. i \<le> N \<and> r = n_Idle_PP2 N i) 
   }"

lemma n_Idle_PP2_Pre:
"pre (n_Idle_PP2 N i) =andForm (pre (n_Idle i)) (andList ((map (\<lambda>j. if (j=i) then chaos else (conclude   (inv_7 i j))) (down N)) @
  (map (\<lambda>j. if (j=i) then chaos else (conclude   (inv_5 i j))) (down N))))"
proof(simp del:inv_7_def inv_5_def  )
  have b1:"((\<lambda>g. strengthenForm g (eqn (IVar (Para ''n'' i)) (Const (enum ''control'' ''E'')))) \<circ> inv_7 i) =
      (\<lambda>j. if j = i then chaos else conclude (inv_7 i j)) "
  proof
    fix j
    show "((\<lambda>g. strengthenForm g (eqn (IVar (Para ''n'' i)) (Const (enum ''control'' ''E'')))) \<circ> inv_7 i) j =
      (  if j = i then chaos else conclude (inv_7 i j)) "
      by auto
  qed
   have b2:"((\<lambda>g. strengthenForm g (eqn (IVar (Para ''n'' i)) (Const (enum ''control'' ''E'')))) \<circ> inv_5 i) =
      (\<lambda>j. if j = i then chaos else conclude (inv_5 i j)) "
  proof
    fix j
    show "((\<lambda>g. strengthenForm g (eqn (IVar (Para ''n'' i)) (Const (enum ''control'' ''E'')))) \<circ> inv_5 i) j =
      (  if j = i then chaos else conclude (inv_5 i j)) "
      by auto
  qed
  with b1 b2 show "andList (map ((\<lambda>g. strengthenForm g (eqn (IVar (Para ''n'' i)) (Const (enum ''control'' ''E'')))) \<circ> inv_7 i) (down N) @
             map ((\<lambda>g. strengthenForm g (eqn (IVar (Para ''n'' i)) (Const (enum ''control'' ''E'')))) \<circ> inv_5 i) (down N)) =
    andList (map (\<lambda>j. if j = i then chaos else conclude (inv_7 i j)) (down N) @ map (\<lambda>j. if j = i then chaos else conclude (inv_5 i j)) (down N))"
    by auto
qed


lemma rulesOfPPIsSym:
  shows "symProtRules' N (rulesOfPP N)"
proof (simp only: symProtRules'_def, (rule allI)+, rule impI)
  fix p r
  assume a1:"p permutes {x.   x \<le> N} \<and> r \<in> rulesOfPP N "
  show "\<exists>r'. alphaEqRule r' (applySym2Rule p r) \<and> r' \<in> rulesOfPP N"
  proof -
    have b1: 
     "(\<exists>i. i \<le> N \<and> r = n_Try i) \<or>
      (\<exists>i. i \<le> N \<and> r = n_Crit i) \<or>
      (\<exists>i. i \<le> N \<and> r = n_Exit i) \<or>
      (\<exists>i. i \<le> N \<and> r = n_Idle_PP N i)"
      using local.a1 by auto
    moreover
    {assume b1:"\<exists> i. i\<le>N\<and>r=n_Try  i"
      from b1 obtain i where b1:"i\<le>N\<and>r=n_Try  i"
        by blast
      from a1 have b2:"p i \<le> N"
        by (metis (mono_tags, lifting) b1 mem_Collect_eq permutes_def permutes_in_image)
      from b1 have b3:"applySym2Rule p r= n_Try  ( p i)" 
        by auto
      have "applySym2Rule p r \<in> rules N "
        by (simp add: b2 b3)
      then have "\<exists>r'. alphaEqRule r' (applySym2Rule p r) \<and> r' \<in> rulesOfPP N"
        apply(rule_tac x="applySym2Rule p r" in exI)
        by (simp add: b3)
    }   
    moreover
    {assume b1:"\<exists> i. i\<le>N\<and>r=n_Crit  i"
      from b1 obtain i where b1:"i\<le>N\<and>r=n_Crit  i"
        by blast
      from a1 have b2:"p i \<le> N"
        by (metis (mono_tags, lifting) b1 mem_Collect_eq permutes_def permutes_in_image)
      from b1 have b3:"applySym2Rule p r= n_Crit  ( p i)" 
        by auto
      have "applySym2Rule p r \<in> rules N "
        by (simp add: b2 b3)
      then have "\<exists>r'. alphaEqRule r' (applySym2Rule p r) \<and> r' \<in> rulesOfPP N"
        apply(rule_tac x="applySym2Rule p r" in exI)
        by (simp add: b3)
    }
    moreover
    {assume b1:"\<exists> i. i\<le>N\<and>r=n_Idle_PP N  i"
      from b1 obtain i where b1:"i\<le>N\<and>r=n_Idle_PP N i"
        by blast
      from a1 have b2:"p i \<le> N"
        by (metis (mono_tags, lifting) b1 mem_Collect_eq permutes_def permutes_in_image)
      have b3:"p permutes {x.   x \<le> N}" sorry
      (*have b4:"and2ListF (pre ( n_Idle_PP N (p i))) =
               and2ListF ((strengthen (n_Idle_Ls N i)  (pre (n_Idle i))))" sorry*)
      have b5:" and2ListF ((strengthen (n_Idle_Ls N (p i))  (pre (n_Idle (p i))))) =
            { eqn (IVar (Para ''n'' (p i))) (Const (enum ''control'' ''E''))} \<union>
               {f. \<exists>j. j\<le>N \<and> j\<noteq>p i \<and>f=conclude (inv_7 (p i) j)}\<union>
               {f. \<exists>j. j\<le>N \<and> j\<noteq>p i \<and>f=conclude (inv_5 (p i) j)}"         
        apply(   simp add:n_Idle_PP_def n_Idle_Ls_def n_Idle_def onMapStrenghthEn 
                      onMapStrenghthEnUn del:strengthen_def,auto
                      )
        apply force
        by (smt Collect_cong)

(*
{ eqn (IVar (Para ''n'' (p i))) (Const (enum ''control'' ''E''))} \<union>
               {f. \<exists>j. j\<le>N \<and> j\<noteq>p i \<and>f=conclude (inv_7 (p i) j)}\<union>
               {f. \<exists>j. j\<le>N \<and> j\<noteq>p i \<and>f=conclude (inv_5 (p i) j)}
                
              "*)
      have b6:"and2ListF (pre (applySym2Rule p (n_Idle_PP N i))) =
          { eqn (IVar (Para ''n'' (p i))) (Const (enum ''control'' ''E''))} \<union>
               {f. \<exists>j. j\<le>N \<and> j\<noteq>p i \<and>f=conclude (inv_7 (p i) j)}\<union>
               {f. \<exists>j. j\<le>N \<and> j\<noteq>p i \<and>f=conclude (inv_5 (p i) j)}
                
              "

         apply(cut_tac b3,  simp add:n_Idle_PP_def n_Idle_Ls_def n_Idle_def onMapStrenghthEn 
                      onMapStrenghthEnUn  onMapStrenghthEnSymApp
                     del:strengthen_def,auto   )
        apply (metis mem_Collect_eq permutes_def)
        using permutes_in_image apply fastforce
        apply auto[1]
        apply (metis mem_Collect_eq permutes_def)
        apply auto[1]
        by (metis mem_Collect_eq permutes_def)
         
       
      have b7:"alphaEqForm (pre ( n_Idle_PP N (p i))) (pre (applySym2Rule p (n_Idle_PP N i)))"
      proof(cut_tac b5 b6, simp) qed

      then have "\<exists>r'. alphaEqRule r' (applySym2Rule p r) \<and> r' \<in> rulesOfPP N"
        apply(rule_tac x="( n_Idle_PP N (p i))" in exI)
        apply(simp only:alphaEqRule_def)
        apply (auto simp only:b1 b3)
         apply simp
        by (simp add: b2)
        
       
    }
    moreover
    {assume b1:"\<exists> i. i\<le>N\<and>r=n_Exit  i"
      from b1 obtain i where b1:"i\<le>N\<and>r=n_Exit  i"
        by blast
      from a1 have b2:"p i \<le> N"
        by (metis (mono_tags, lifting) b1 mem_Collect_eq permutes_def permutes_in_image)
      from b1 have b3:"applySym2Rule p r= n_Exit  ( p i)" 
        by auto
      have "applySym2Rule p r \<in> rules N "
        by (simp add: b2 b3)

     then have "\<exists>r'. alphaEqRule r' (applySym2Rule p r) \<and> r' \<in> rulesOfPP N"
        apply(rule_tac x="applySym2Rule p r" in exI)
        by (simp add: b3)
    }
    ultimately show "\<exists>r'. alphaEqRule r' (applySym2Rule p r) \<and> r' \<in> rulesOfPP N"
      by blast
  qed
qed

lemma onAnd2ListFUn:
  "and2ListF (andList  (xs@ys) ) =
  (and2ListF (andList (xs) )) \<union> (and2ListF (andList ys ))"  (is "?P xs ys")
proof(induct_tac xs)
  show "?P [] ys"
  proof(simp)qed
next
  fix x xs

  assume a1:"?P xs ys"
  show "?P (x#xs) ys"
    using a1 by auto
qed

lemma onAnd2ListAppSym:
  "and2ListF (applySym2Form p (andList  (xs) )) =
  (and2ListF (andList (map (applySym2Form p) xs) )) "  (is "?P xs")
proof(induct_tac xs)
  show "?P [] "
  proof(simp)qed
next
  fix x xs

  assume a1:"?P xs "
  show "?P (x#xs) "
    using a1 by auto
qed


lemma rulesOfPP1IsSym:
  shows "symProtRules' N (rulesOfPP1 N)"
proof (simp only: symProtRules'_def, (rule allI)+, rule impI)
  fix p r
  assume a1:"p permutes {x.   x \<le> N} \<and> r \<in> rulesOfPP1 N "
  show "\<exists>r'. alphaEqRule r' (applySym2Rule p r) \<and> r' \<in> rulesOfPP1 N"
  proof -
    have b1: 
     "(\<exists>i. i \<le> N \<and> r = n_Try i) \<or>
      (\<exists>i. i \<le> N \<and> r = n_Crit i) \<or>
      (\<exists>i. i \<le> N \<and> r = n_Exit i) \<or>
      (\<exists>i. i \<le> N \<and> r = n_Idle_PP1 N i)"
      using local.a1 by auto
    moreover
    {assume b1:"\<exists> i. i\<le>N\<and>r=n_Try  i"
      from b1 obtain i where b1:"i\<le>N\<and>r=n_Try  i"
        by blast
      from a1 have b2:"p i \<le> N"
        by (metis (mono_tags, lifting) b1 mem_Collect_eq permutes_def permutes_in_image)
      from b1 have b3:"applySym2Rule p r= n_Try  ( p i)" 
        by auto
      have "applySym2Rule p r \<in> rules N "
        by (simp add: b2 b3)
      then have "\<exists>r'. alphaEqRule r' (applySym2Rule p r) \<and> r' \<in> rulesOfPP1 N"
        apply(rule_tac x="applySym2Rule p r" in exI)
        by (simp add: b3)
    }   
    moreover
    {assume b1:"\<exists> i. i\<le>N\<and>r=n_Crit  i"
      from b1 obtain i where b1:"i\<le>N\<and>r=n_Crit  i"
        by blast
      from a1 have b2:"p i \<le> N"
        by (metis (mono_tags, lifting) b1 mem_Collect_eq permutes_def permutes_in_image)
      from b1 have b3:"applySym2Rule p r= n_Crit  ( p i)" 
        by auto
      have "applySym2Rule p r \<in> rules N "
        by (simp add: b2 b3)
      then have "\<exists>r'. alphaEqRule r' (applySym2Rule p r) \<and> r' \<in> rulesOfPP1 N"
        apply(rule_tac x="applySym2Rule p r" in exI)
        by (simp add: b3)
    }
    moreover
    {assume b1:"\<exists> i. i\<le>N\<and>r=n_Idle_PP1 N  i"
      from b1 obtain i where b1:"i\<le>N\<and>r=n_Idle_PP1 N i"
        by blast
      from a1 have b2:"p i \<le> N"
        by (metis (mono_tags, lifting) b1 mem_Collect_eq permutes_def permutes_in_image)
      (*have b3:"p permutes {x.   x \<le> N}" sorry*)
      
      have b4:"pre ( n_Idle_PP1 N (p i)) =andForm (pre (n_Idle (p i))) 
        (andList (n_Idle_Ls1 N (p i)) )"
        by simp

      have b5:"pre ((applySym2Rule p (n_Idle_PP1 N i))) =andForm (pre (n_Idle (p i))) 
        (applySym2Form p (andList (n_Idle_Ls1 N  i) ))"
        by simp
      have b6:"\<forall>i j. applySym2Form p (inv_7 i j) = inv_7 (p i) (p j)" 
        apply auto done
      have b7:"\<forall>i j. applySym2Form p (inv_5 i j) = inv_5 (p i) (p j)" 
        apply auto done
      have b8:"and2ListF (andList (n_Idle_Ls1 N (p i))) =
            and2ListF (andList (map (inv_7 (p i)) (down N))) 
            \<union> and2ListF (andList (map (inv_5 (p i)) (down N)))
          "
        by(cut_tac a1 b1 b6 b7,   
            simp add:  n_Idle_Ls1_def   onAnd2ListFUn   onAnd2ListAppSym  del:inv_5_def inv_7_def   )

      have b80:"and2ListF (applySym2Form p (andList (n_Idle_Ls1 N  i) )) =
            and2ListF (applySym2Form p (andList (map (inv_7 ( i)) (down N)))) 
            \<union> and2ListF (applySym2Form p (andList (map (inv_5 ( i)) (down N))))
          "
       by(cut_tac a1 b1 b6 b7,   
            simp add:  n_Idle_Ls1_def   onAnd2ListFUn  
            onAnd2ListAppSym  del:inv_5_def inv_7_def   )

     have b9:"and2ListF (andList (map (inv_7 (p i)) (down N))) =
        and2ListF (applySym2Form p (andList (map (inv_7 ( i)) (down N)))) "
       using b1 b6 local.a1 wellFormAndlistIsSym2 by presburger
     thm wellFormAndlistIsSym2
     have b10:"and2ListF (andList (map (inv_5 (p i)) (down N))) =
        and2ListF (applySym2Form p (andList (map (inv_5 ( i)) (down N)))) "
       using b1 b7 local.a1 wellFormAndlistIsSym2 by presburger 

     thm wellFormAndlistIsSym2
     from b7 b80 b9 b10 have b11:"and2ListF (andList (n_Idle_Ls1 N (p i))) =
        and2ListF (applySym2Form p (andList (n_Idle_Ls1 N  i) )) "
       by (metis b10 b80 b9 n_Idle_Ls1_def onAnd2ListFUn)
        thm 
             wellFormAndlistIsSym2  

      
      have b11:"alphaEqForm (pre ( n_Idle_PP1 N (p i))) (pre (applySym2Rule p (n_Idle_PP1 N i)))"
      proof(cut_tac b11, simp) qed

      then have "\<exists>r'. alphaEqRule r' (applySym2Rule p r) \<and> r' \<in> rulesOfPP1 N"
        apply(rule_tac x="( n_Idle_PP1 N (p i))" in exI)
        apply(simp only:alphaEqRule_def)
        apply (auto simp only:b1 a1)
         apply simp
        by (simp add: b2)
        
       
    }
    moreover
    {assume b1:"\<exists> i. i\<le>N\<and>r=n_Exit  i"
      from b1 obtain i where b1:"i\<le>N\<and>r=n_Exit  i"
        by blast
      from a1 have b2:"p i \<le> N"
        by (metis (mono_tags, lifting) b1 mem_Collect_eq permutes_def permutes_in_image)
      from b1 have b3:"applySym2Rule p r= n_Exit  ( p i)" 
        by auto
      have "applySym2Rule p r \<in> rules N "
        by (simp add: b2 b3)

     then have "\<exists>r'. alphaEqRule r' (applySym2Rule p r) \<and> r' \<in> rulesOfPP1 N"
        apply(rule_tac x="applySym2Rule p r" in exI)
        by (simp add: b3)
    }
    ultimately show "\<exists>r'. alphaEqRule r' (applySym2Rule p r) \<and> r' \<in> rulesOfPP1 N"
      by blast
  qed
qed


lemma rulesOfPP2IsSym:
  shows "symProtRules' N (rulesOfPP2 N)"
proof (simp only: symProtRules'_def, (rule allI)+, rule impI)
  fix p r
  assume a1:"p permutes {x.   x \<le> N} \<and> r \<in> rulesOfPP2 N "
  show "\<exists>r'. alphaEqRule r' (applySym2Rule p r) \<and> r' \<in> rulesOfPP2 N"
  proof -
    have b1: 
     "(\<exists>i. i \<le> N \<and> r = n_Try i) \<or>
      (\<exists>i. i \<le> N \<and> r = n_Crit i) \<or>
      (\<exists>i. i \<le> N \<and> r = n_Exit i) \<or>
      (\<exists>i. i \<le> N \<and> r = n_Idle_PP2 N i)"
      using local.a1 by auto
    moreover
    {assume b1:"\<exists> i. i\<le>N\<and>r=n_Try  i"
      from b1 obtain i where b1:"i\<le>N\<and>r=n_Try  i"
        by blast
      from a1 have b2:"p i \<le> N"
        by (metis (mono_tags, lifting) b1 mem_Collect_eq permutes_def permutes_in_image)
      from b1 have b3:"applySym2Rule p r= n_Try  ( p i)" 
        by auto
      have "applySym2Rule p r \<in> rules N "
        by (simp add: b2 b3)
      then have "\<exists>r'. alphaEqRule r' (applySym2Rule p r) \<and> r' \<in> rulesOfPP2 N"
        apply(rule_tac x="applySym2Rule p r" in exI)
        by (simp add: b3)
    }   
    moreover
    {assume b1:"\<exists> i. i\<le>N\<and>r=n_Crit  i"
      from b1 obtain i where b1:"i\<le>N\<and>r=n_Crit  i"
        by blast
      from a1 have b2:"p i \<le> N"
        by (metis (mono_tags, lifting) b1 mem_Collect_eq permutes_def permutes_in_image)
      from b1 have b3:"applySym2Rule p r= n_Crit  ( p i)" 
        by auto
      have "applySym2Rule p r \<in> rules N "
        by (simp add: b2 b3)
      then have "\<exists>r'. alphaEqRule r' (applySym2Rule p r) \<and> r' \<in> rulesOfPP2 N"
        apply(rule_tac x="applySym2Rule p r" in exI)
        by (simp add: b3)
    }
    moreover
    {assume b1:"\<exists> i. i\<le>N\<and>r=n_Idle_PP2 N  i"
      from b1 obtain i where b1:"i\<le>N\<and>r=n_Idle_PP2 N i"
        by blast
      from a1 have b2:"p i \<le> N"
        by (metis (mono_tags, lifting) b1 mem_Collect_eq permutes_def permutes_in_image)

      have b4:"pre ( n_Idle_PP2 N (p i)) =andForm (pre (n_Idle (p i))) 
        (andList (map (\<lambda>g. strengthenForm g (pre (n_Idle (p i))) ) (n_Idle_Ls1 N (p i)) ))"
        by simp

      have b5:"pre ((applySym2Rule p (n_Idle_PP2 N i))) =andForm (pre (n_Idle (p i))) 
        (applySym2Form p 
      (andList (map (\<lambda>g. strengthenForm g (pre (n_Idle ( i))) ) (n_Idle_Ls1 N ( i)) ) ))"
        by simp

      have b6:"\<forall>i j. (i=j \<longrightarrow>and2ListF
                  (strengthenForm (inv_7 ( i) j)
                    (eqn (IVar (Para ''n'' ( i))) (Const (enum ''control'' ''E'')))) ={}) \<and>
                (i\<noteq>j \<longrightarrow>and2ListF
                  (strengthenForm (inv_7 ( i) j)
                    (eqn (IVar (Para ''n'' ( i))) (Const (enum ''control'' ''E'')))) =
              {conclude (inv_7 ( i) j)})" 
        apply auto done
      have b7:"\<forall>i j. (i=j \<longrightarrow>and2ListF
                  (strengthenForm (inv_5 ( i) j)
                    (eqn (IVar (Para ''n'' ( i))) (Const (enum ''control'' ''E'')))) ={}) \<and>
                (i\<noteq>j \<longrightarrow>and2ListF
                  (strengthenForm (inv_5 ( i) j)
                    (eqn (IVar (Para ''n'' ( i))) (Const (enum ''control'' ''E'')))) =
              {conclude (inv_5 ( i) j)})" 
        apply auto done
      have b8:"and2ListF ( (andList (map (\<lambda>g. strengthenForm g (pre (n_Idle (p i))) )
                 (n_Idle_Ls1 N (p i)) ))) =
            and2ListF (andList (map (\<lambda>j. if (p i=j) then chaos else (conclude (inv_7 (p i) j) )) (down N))) 
            \<union> and2ListF (andList (map (\<lambda>j. if (p i=j) then chaos else (conclude (inv_5 (p i) j) )) (down N)))
          "
        by(cut_tac a1 b1  ,   
             auto simp add:  n_Idle_Ls1_def   onAnd2ListFUn   onAnd2ListAppSym onMapAndListF 
            del:inv_5_def inv_7_def   )

      have b6:"\<forall>i j.  (i\<noteq>j \<longrightarrow>(applySym2Form p
                    (strengthenForm (inv_7 i j)
                      (eqn (IVar (Para ''n'' i)) (Const (enum ''control'' ''E''))))) = 
                    conclude (inv_7 (p i) (p j))) \<and>
            (i=j) \<longrightarrow> (applySym2Form p
                    (strengthenForm (inv_7 i j)
                      (eqn (IVar (Para ''n'' i)) (Const (enum ''control'' ''E''))))) = chaos" 
        apply auto done
      have b7:"\<forall>i j.  (i\<noteq>j \<longrightarrow>(applySym2Form p
                    (strengthenForm (inv_5 i j)
                      (eqn (IVar (Para ''n'' i)) (Const (enum ''control'' ''E''))))) = 
                  conclude (inv_5 (p i) (p j))) \<and>
            (i=j) \<longrightarrow> (applySym2Form p
                    (strengthenForm (inv_5 i j)
                      (eqn (IVar (Para ''n'' i)) (Const (enum ''control'' ''E''))))) = chaos" 
        apply auto done
(* and2ListF (applySym2Form p (andList (map (inv_7 ( i)) (down N)))) 
            \<union> and2ListF (applySym2Form p (andList (map (inv_5 ( i)) (down N))))*)
      have b9:"and2ListF (applySym2Form p  
      (andList (map (\<lambda>g. strengthenForm g (pre (n_Idle ( i))) ) (n_Idle_Ls1 N ( i)) ) )) =
            and2ListF (applySym2Form p  (andList
             (map (\<lambda>j. if ( i= j) then chaos else (conclude (inv_7 ( i) ( j)) )) (down N)))) 
            \<union> and2ListF (applySym2Form p  (andList 
          (map(\<lambda>j. if (  i=  j) then chaos else (conclude (inv_5 ( i) ( j)) )) (down N))))
          "
        by(cut_tac a1 b1 b6 b7,   
             simp add:  n_Idle_Ls1_def   onAnd2ListFUn  onMapAndListF 
            onAnd2ListAppSym  del:inv_5_def inv_7_def,auto  )
      thm wellFormAndlistIsSym2
      have b10:" and2ListF 
  (andList (map (\<lambda>j. if (p i=j) then chaos else (conclude (inv_7 (p i) j) )) (down N))) =
       and2ListF (applySym2Form p  (andList
             (map (\<lambda>j. if ( i= j) then chaos else (conclude (inv_7 ( i) ( j)) )) (down N)))) "
        apply(cut_tac a1 b1,rule  wellFormAndlistIsSym2,simp )
        
        by (metis permutes_def,auto)  
     have b11:"and2ListF 
  (andList (map (\<lambda>j. if (p i=j) then chaos else (conclude (inv_5 (p i) j) )) (down N))) =
       and2ListF (applySym2Form p  (andList
             (map (\<lambda>j. if ( i= j) then chaos else (conclude (inv_5 ( i) ( j)) )) (down N)))) "
        apply(cut_tac a1 b1,rule  wellFormAndlistIsSym2,simp )
        
        by (metis permutes_def,auto)  

     thm wellFormAndlistIsSym2
     from b8  b9 b10 b11 have b12:" 
      and2ListF (andList (map (\<lambda>g. strengthenForm g (pre (n_Idle (p i))) ) (n_Idle_Ls1 N (p i)) )) =
      and2ListF (applySym2Form p 
      (andList (map (\<lambda>g. strengthenForm g (pre (n_Idle ( i))) ) (n_Idle_Ls1 N ( i)) ) ))  "
       by blast  


      

      have b11:"alphaEqForm (pre ( n_Idle_PP2 N (p i))) (pre (applySym2Rule p (n_Idle_PP2 N i)))"
      proof(cut_tac b12, simp) qed

      then have "\<exists>r'. alphaEqRule r' (applySym2Rule p r) \<and> r' \<in> rulesOfPP2 N"
        apply(rule_tac x="( n_Idle_PP2 N (p i))" in exI)
        apply(simp only:alphaEqRule_def)
        apply (auto simp only:b1 a1)
         apply simp
        by (simp add: b2) 
        
       
    }
    moreover
    {assume b1:"\<exists> i. i\<le>N\<and>r=n_Exit  i"
      from b1 obtain i where b1:"i\<le>N\<and>r=n_Exit  i"
        by blast
      from a1 have b2:"p i \<le> N"
        by (metis (mono_tags, lifting) b1 mem_Collect_eq permutes_def permutes_in_image)
      from b1 have b3:"applySym2Rule p r= n_Exit  ( p i)" 
        by auto
      have "applySym2Rule p r \<in> rules N "
        by (simp add: b2 b3)

     then have "\<exists>r'. alphaEqRule r' (applySym2Rule p r) \<and> r' \<in> rulesOfPP2 N"
        apply(rule_tac x="applySym2Rule p r" in exI)
        by (simp add: b3)
    }
    ultimately show "\<exists>r'. alphaEqRule r' (applySym2Rule p r) \<and> r' \<in> rulesOfPP2 N"
      by blast
  qed
qed

(*lemma transSimOnAbsRules:
  "trans_sim_on1 r (absTransfRule r M) M"

axiomatization  where axiomOnf2 [simp,intro]:
   "s \<in> reachableSet (set (allInitSpecs N )) (rules N) \<Longrightarrow> 
 1 < N \<Longrightarrow> 1 < i \<Longrightarrow> j<2 \<Longrightarrow>  formEval (f 0 1) s \<Longrightarrow> formEval (f i j) s"


subsection{*Definitions of  the Set of Abs Invariant Formula Instances *}
definition invariantsAbs  ::"  nat \<Rightarrow> formula list" where [simp]:
"invariantsAbs  i \<equiv> [
inv_27 i ,
inv_7 i 1 ,
inv_7 i 0 ,
inv_5 i 0 ,
inv_5 i 1
]"*)

(*lemma mutualExPPSimmutualEx:
  assumes a1:"\<forall>r. r \<in> rs \<longrightarrow>(\<exists> Ls . set Ls \<subseteq> set S \<and>  strengthenR Ls r \<in> rs')" and
  a2:"\<forall>i s f. s \<in>reachableSetUpTo I rs' i \<longrightarrow> f \<in>set S \<longrightarrow>formEval f s" 
shows "\<forall>s f. s \<in>reachableSetUpTo I rs i \<longrightarrow>
   f \<in>set S \<longrightarrow>(s \<in>reachableSetUpTo I rs' i \<and>formEval f s)" (is "?P i")*)
subsection{*Definitions of each abstracted rule*}

definition  NC::"nat " where [simp]: "NC==1"

definition n_Idle_abs::"rule" where [simp]:
"n_Idle_abs  \<equiv>
let g = (andForm (andForm (eqn (IVar (Ident ''x'')) (Const false)) 
(forallForm (down NC) (\<lambda>j. (neg (eqn (IVar (Para ( ''n'') j)) (Const E))))))
 (forallForm (down NC) (\<lambda>j. (neg (eqn (IVar (Para ( ''n'') j)) (Const C)))))) in
let s = (parallelList [(assign ((Ident ''x''), (Const true)))]) in
guard g s"



 

definition n_Crit_abs::"rule" where [simp]:
"n_Crit_abs  \<equiv>
let g = (eqn (IVar (Ident ''x'')) (Const true)) in
let s = (parallelList [(assign ((Ident ''x''), (Const false)))]) in
guard g s"



subsection{*The set of All actual Rules w.r.t. a Protocol Instance with Size $N$*}
definition rulesAbs::"nat \<Rightarrow> rule set" where [simp]:
"rulesAbs N \<equiv> {r.
(\<exists> i. i\<le>N\<and>r=n_Try  i) \<or>
(\<exists> i. i\<le>N\<and>r=n_Crit  i) \<or>
(\<exists> i. i\<le>N\<and>r=n_Exit  i) \<or>
(\<exists> i. i\<le>N\<and>r=n_Idle  i) \<or>
(r=n_Crit_abs  ) \<or>
(r=n_Idle_abs )\<or> r=skipRule
}"







axiomatization  where axiomOnReachOfAbsMutual [simp,intro]:
   "s \<in> reachableSet (set (allInitSpecs NC )) (rulesAbs NC) \<Longrightarrow>  f \<in> invariants NC \<Longrightarrow>  formEval f s "

axiomatization  where axiomOnf1 [simp,intro]:
   "s \<in> reachableSet (set (allInitSpecs N )) (rules N) \<Longrightarrow> 1 < N \<Longrightarrow> 1 < i \<Longrightarrow>formEval (f 0 ) s \<Longrightarrow> formEval (f i) s"




subsection\<open>Definitions of initial states
1.abs protocol can simulate mutualPP2\<close> 

lemma absMutualSimmutualPP2:
  assumes a1:"s \<in> reachableSetUpTo (andList (allInitSpecs N)) (rulesOfPP2 N) i" and a2:"N>1"
  shows "s \<in> reachableSetUpTo (andList (allInitSpecs NC)) (rulesAbs NC) i \<and> (\<forall>f. f \<in> invariants NC \<longrightarrow> formEval f s)"
  sorry
text \<open>
1.mutualPP1 can simulate mutualPP2\<close> 

lemma mutualPP2SimMutualPP1:
  assumes a1:"s \<in> reachableSetUpTo (andList (allInitSpecs N)) (rulesOfPP1 N) i"
  shows "s \<in> reachableSetUpTo (andList (allInitSpecs N)) (rulesOfPP2 N) i \<and> (\<forall>f. f \<in> invariants NC \<longrightarrow> formEval f s)"
  sorry

lemma mutualPP1SatAllForm:
  assumes a1:"s \<in> reachableSetUpTo (andList (allInitSpecs N)) (rulesOfPP1 N) i" and a2:"N>1"
  shows " (\<forall>f. f \<in> invariants N \<longrightarrow> formEval f s)"

lemma mutualPP1Simmutual:
  assumes a1:"s \<in> reachableSetUpTo (andList (allInitSpecs N)) (rules N) i"
  shows "s \<in> reachableSetUpTo (andList (allInitSpecs N)) (rulesOfPP1 N) i \<and> (\<forall>f. f \<in> invariants N \<longrightarrow> formEval f s)"
proof -
  have b1:"\<forall>r. r \<in> rs \<longrightarrow>(\<exists> Ls ss. set Ls \<subseteq> set S \<and>  set ss \<subseteq> set S \<and> strengthenR1 Ls ss r \<in> rs')" and
  a2:"\<forall>i s f. s \<in>reachableSetUpTo I rs' i \<longrightarrow> f \<in>set S \<longrightarrow>formEval f s" 
lemma lemmaOnn_TryGt_i:
  assumes a1:"NC<i" and a2:"s \<in> reachableSet (set (allInitSpecs N)) (rules N)"  and  
  a4:"\<forall>f.  f \<in>(set invariantsAbs) \<longrightarrow>  formEval f s" 
shows "trans_sim_on2 (n_Try  i  ) skipRule VF (set invariantsAbs) s" (is "trans_sim_on2 ?r ?r' VF ?F s")
proof(unfold trans_sim_on2_def,(rule allI)+,(rule impI)+,rule disjI2)
  fix s2 
  assume b0:"state_sim_on2 s s2 VF "
  show "state_sim_on2 (trans (act (n_Try  i)) s) s2  VF"
  proof(cut_tac a1,unfold state_sim_on2_def,
    (rule allI)+,(rule impI)+)
    fix f v
    assume b1:" v \<in>  VF"  
    
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
  show  "\<forall>v. v\<in>varOfForm (pre ?r) \<longrightarrow>  v \<in> VF "
    by(cut_tac a1, auto) 
    
next
  show  b1: "\<forall>v a. a \<in> set (statement2Assigns (act ?r)) \<longrightarrow> v\<in>varOfExp ( substExpByStatement (IVar (fst a))  (act ?r))\<longrightarrow>v \<in>VF "
   proof(cut_tac a1,(rule allI)+,(rule impI)+,auto) qed
    
 qed
lemma lemmaOnn_Try: 
  assumes   a2:"s \<in> reachableSet (set (allInitSpecs N)) (rules N)"  and  
  a4:"\<forall>f.  f \<in>(set invariantsAbs) \<longrightarrow>  formEval f s" and a5:"\<exists> i. i\<le>N\<and>r=n_Try  i"  and
  a6:"NC<N"
  shows "\<exists> r'. r' \<in> rules NC\<and> trans_sim_on2 r r' VF (set invariantsAbs) s" (is "\<exists>r'.?P1 r' \<and> ?P2 r'")
proof -
  from a5 obtain i where d0:"i\<le>N\<and>r=n_Try  i"  by blast
  have "i>NC|i\<le> NC" by auto
  moreover{
       assume a1:"i>NC" 
        have "\<exists>r'. ?P1 r' \<and> ?P2 r'"
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
        have "\<exists>r'. ?P1 r' \<and> ?P2 r'"
        proof(rule_tac x="(n_Try  i)" in exI,rule conjI)
          show  "?P1 (n_Try  i) " 
           by(cut_tac a1, auto) 
          next
          show  "?P2 (n_Try  i) "
           using lemmaOnn_TryLeNc_ local.a1 a2 a4 a6 d0 by blast 
        qed
       }
  ultimately show "\<exists>r'.?P1 r' \<and> ?P2 r'" 
    by satx
qed

lemma lemmaOnn_CritGt_i:
  assumes a1:"i>NC" and 
  a2:"s \<in> reachableSet (set (allInitSpecs N)) (rules N)"  and a3:"NC<N" and  
  a4:"\<forall>f.  f \<in>(set invariantsAbs) \<longrightarrow>  formEval f s" 
  shows "trans_sim_on2 (n_Crit  i)  (n_Crit_i_3 ) VF (set invariantsAbs) s" (is "trans_sim_on2 ?r ?r' VF (set ?F) s")
  proof(rule ruleSimCond2)
    show " formEval (pre ?r) s \<longrightarrow>formEval (pre ?r') s" (is "?A \<longrightarrow>?B")
    proof(rule impI)+
      assume b0:"?A"
  
      from b0  show "formEval (pre ?r') s" 
       by auto
     qed
   next 
	show "(\<forall>  v. v \<in>  varOfSent (act  ?r') \<longrightarrow>  v \<in> VF \<longrightarrow> formEval (pre ?r) s \<longrightarrow> 
    expEval (substExpByStatement (IVar v)  (act ?r')) s = expEval (substExpByStatement (IVar v)  (act ?r)) s)"
   proof(rule allI,(rule impI)+)
      fix  v
     assume b1:"v\<in> VF"  and b2:"formEval (pre ?r) s" and b3:"v \<in>varOfSent (act ?r')"
  
  show "expEval (substExpByStatement (IVar v)  (act ?r')) s = expEval (substExpByStatement (IVar v)  (act ?r)) s"  
       apply (cut_tac  a1 b1 b2 ,auto) done
   qed
 next
   show "\<forall>  v. v \<in>  varOfSent (act ?r) \<longrightarrow>  v \<in> VF \<longrightarrow> v \<in>  varOfSent (act ?r')" by(cut_tac a1, auto)

  
 next 
   show "\<forall> v va. v \<in> varOfSent (act ?r') \<longrightarrow>va\<in>varOfExp ( substExpByStatement (IVar v)  (act ?r'))\<longrightarrow> va \<in> VF "
     by auto  
 next
   show "\<forall>v. v \<in> varOfForm (pre (?r')) \<longrightarrow> v \<in> VF" by auto
qed
lemma lemmaOnn_CritLeNc_:
  assumes a1:"i\<le>NC" 
  shows "trans_sim_on2 (n_Crit  i) (n_Crit  i) VF  (set invariantsAbs) s" (is "trans_sim_on2 ?r ?r VF ?F s")
proof(rule ruleSimId2)
  show  "\<forall>v. v\<in>varOfForm (pre ?r) \<longrightarrow>  v \<in> VF "
    by(cut_tac a1, auto) 
    
next
  show  b1: "\<forall>v a. a \<in> set (statement2Assigns (act ?r)) \<longrightarrow> v\<in>varOfExp ( substExpByStatement (IVar (fst a))  (act ?r))\<longrightarrow>v \<in>VF "
   proof(cut_tac a1,(rule allI)+,(rule impI)+,auto) qed
    
 qed
lemma lemmaOnn_Crit: 
  assumes   a2:"s \<in> reachableSet (set (allInitSpecs N)) (rules N)"  and  
  a4:"\<forall>f.  f \<in>(set invariantsAbs) \<longrightarrow>  formEval f s" and a5:"\<exists> i. i\<le>N\<and>r=n_Crit  i"  and
  a6:"NC<N"
  shows "\<exists> r'. r' \<in> rules NC\<and> trans_sim_on2 r r' VF (set invariantsAbs) s" (is "\<exists>r'.?P1 r' \<and> ?P2 r'")
proof -
  from a5 obtain i where d0:"i\<le>N\<and>r=n_Crit  i"  by blast
  have "i>NC|i\<le> NC" by auto
  moreover{
       assume a1:"i>NC" 
        have "\<exists>r'. ?P1 r' \<and> ?P2 r'"
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
        have "\<exists>r'. ?P1 r' \<and> ?P2 r'"
        proof(rule_tac x="(n_Crit  i)" in exI,rule conjI)
          show  "?P1 (n_Crit  i) " 
           by(cut_tac a1, auto) 
          next
          show  "?P2 (n_Crit  i) "
           using lemmaOnn_CritLeNc_ local.a1 a2 a4 a6 d0 by blast 
        qed
       }
  ultimately show "\<exists>r'.?P1 r' \<and> ?P2 r'" 
    by satx
qed

lemma lemmaOnn_ExitGt_i:
  assumes a1:"NC<i" and a2:"s \<in> reachableSet (set (allInitSpecs N)) (rules N)"  and  
  a4:"\<forall>f.  f \<in>(set invariantsAbs) \<longrightarrow>  formEval f s" 
shows "trans_sim_on2 (n_Exit  i  ) skipRule VF (set invariantsAbs) s" (is "trans_sim_on2 ?r ?r' VF ?F s")
proof(unfold trans_sim_on2_def,(rule allI)+,(rule impI)+,rule disjI2)
  fix s2 
  assume b0:"state_sim_on2 s s2 VF "
  show "state_sim_on2 (trans (act (n_Exit  i)) s) s2  VF"
  proof(cut_tac a1,unfold state_sim_on2_def,
    (rule allI)+,(rule impI)+)
    fix f v
    assume b1:" v \<in>  VF"  
    
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
  show  "\<forall>v. v\<in>varOfForm (pre ?r) \<longrightarrow>  v \<in> VF "
    by(cut_tac a1, auto) 
    
next
  show  b1: "\<forall>v a. a \<in> set (statement2Assigns (act ?r)) \<longrightarrow> v\<in>varOfExp ( substExpByStatement (IVar (fst a))  (act ?r))\<longrightarrow>v \<in>VF "
   proof(cut_tac a1,(rule allI)+,(rule impI)+,auto) qed
    
 qed
lemma lemmaOnn_Exit: 
  assumes   a2:"s \<in> reachableSet (set (allInitSpecs N)) (rules N)"  and  
  a4:"\<forall>f.  f \<in>(set invariantsAbs) \<longrightarrow>  formEval f s" and a5:"\<exists> i. i\<le>N\<and>r=n_Exit  i"  and
  a6:"NC<N"
  shows "\<exists> r'. r' \<in> rules NC\<and> trans_sim_on2 r r' VF (set invariantsAbs) s" (is "\<exists>r'.?P1 r' \<and> ?P2 r'")
proof -
  from a5 obtain i where d0:"i\<le>N\<and>r=n_Exit  i"  by blast
  have "i>NC|i\<le> NC" by auto
  moreover{
       assume a1:"i>NC" 
        have "\<exists>r'. ?P1 r' \<and> ?P2 r'"
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
        have "\<exists>r'. ?P1 r' \<and> ?P2 r'"
        proof(rule_tac x="(n_Exit  i)" in exI,rule conjI)
          show  "?P1 (n_Exit  i) " 
           by(cut_tac a1, auto) 
          next
          show  "?P2 (n_Exit  i) "
           using lemmaOnn_ExitLeNc_ local.a1 a2 a4 a6 d0 by blast 
        qed
       }
  ultimately show "\<exists>r'.?P1 r' \<and> ?P2 r'" 
    by satx
qed

lemma lemmaOnn_IdleGt_i:
  assumes a1:"i>NC" and 
  a2:"s \<in> reachableSet (set (allInitSpecs N)) (rules N)"  and a3:"NC<N" and  
  a4:"\<forall>f.  f \<in>(set invariantsAbs) \<longrightarrow>  formEval f s" 
  shows "trans_sim_on2 (n_Idle  i)  (n_Idle_i_3 ) VF (set invariantsAbs) s" (is "trans_sim_on2 ?r ?r' VF (set ?F) s")
  proof(rule ruleSimCond2)
    show " formEval (pre ?r) s \<longrightarrow>formEval (pre ?r') s" (is "?A \<longrightarrow>?B")
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
	show "(\<forall>  v. v \<in>  varOfSent (act  ?r') \<longrightarrow>  v \<in> VF \<longrightarrow> formEval (pre ?r) s \<longrightarrow> 
    expEval (substExpByStatement (IVar v)  (act ?r')) s = expEval (substExpByStatement (IVar v)  (act ?r)) s)"
   proof(rule allI,(rule impI)+)
      fix  v
     assume b1:"v\<in> VF"  and b2:"formEval (pre ?r) s" and b3:"v \<in>varOfSent (act ?r')"
  
  show "expEval (substExpByStatement (IVar v)  (act ?r')) s = expEval (substExpByStatement (IVar v)  (act ?r)) s"  
       apply (cut_tac  a1 b1 b2 ,auto) done
   qed
 next
   show "\<forall>  v. v \<in>  varOfSent (act ?r) \<longrightarrow>  v \<in> VF \<longrightarrow> v \<in>  varOfSent (act ?r')" by(cut_tac a1, auto)

  
 next 
   show "\<forall> v va. v \<in> varOfSent (act ?r') \<longrightarrow>va\<in>varOfExp ( substExpByStatement (IVar v)  (act ?r'))\<longrightarrow> va \<in> VF "
     by auto  
 next
   show "\<forall>v. v \<in> varOfForm (pre (?r')) \<longrightarrow> v \<in> VF" by auto
qed
lemma lemmaOnn_IdleLeNc_:
  assumes a1:"i\<le>NC" 
  shows "trans_sim_on2 (n_Idle  i) (n_Idle  i) VF  (set invariantsAbs) s" (is "trans_sim_on2 ?r ?r VF ?F s")
proof(rule ruleSimId2)
  show  "\<forall>v. v\<in>varOfForm (pre ?r) \<longrightarrow>  v \<in> VF "
    by(cut_tac a1, auto) 
    
next
  show  b1: "\<forall>v a. a \<in> set (statement2Assigns (act ?r)) \<longrightarrow> v\<in>varOfExp ( substExpByStatement (IVar (fst a))  (act ?r))\<longrightarrow>v \<in>VF "
   proof(cut_tac a1,(rule allI)+,(rule impI)+,auto) qed
    
 qed
lemma lemmaOnn_Idle: 
  assumes   a2:"s \<in> reachableSet (set (allInitSpecs N)) (rules N)"  and  
  a4:"\<forall>f.  f \<in>(set invariantsAbs) \<longrightarrow>  formEval f s" and a5:"\<exists> i. i\<le>N\<and>r=n_Idle  i"  and
  a6:"NC<N"
  shows "\<exists> r'. r' \<in> rules NC\<and> trans_sim_on2 r r' VF (set invariantsAbs) s" (is "\<exists>r'.?P1 r' \<and> ?P2 r'")
proof -
  from a5 obtain i where d0:"i\<le>N\<and>r=n_Idle  i"  by blast
  have "i>NC|i\<le> NC" by auto
  moreover{
       assume a1:"i>NC" 
        have "\<exists>r'. ?P1 r' \<and> ?P2 r'"
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
        have "\<exists>r'. ?P1 r' \<and> ?P2 r'"
        proof(rule_tac x="(n_Idle  i)" in exI,rule conjI)
          show  "?P1 (n_Idle  i) " 
           by(cut_tac a1, auto) 
          next
          show  "?P2 (n_Idle  i) "
           using lemmaOnn_IdleLeNc_ local.a1 a2 a4 a6 d0 by blast 
        qed
       }
  ultimately show "\<exists>r'.?P1 r' \<and> ?P2 r'" 
    by satx
qed

definition n_Idle_PP::"nat \<Rightarrow> rule" where [simp]:
"n_Idle_i_3PP i \<equiv> 
let g = andForm (eqn (IVar (Para ( ''n'') i)) (Const E)) (andForm (andForm (eqn (IVar (Ident ''x'')) (Const false)) 
(forallForm (down NC) (\<lambda>j. (neg (eqn (IVar (Para ( ''n'') j)) (Const E))))))
 (forallForm (down NC) (\<lambda>j. (neg (eqn (IVar (Para ( ''n'') j)) (Const C)))))) in
let s = (parallelList [(assign ((Ident ''x''), (Const true)))]) in
guard g s"

definition  NC::"nat " where [simp]: "NC==1"

lemma wellFormAndlistIsSym:
  assumes a1:"p permutes {i. i\<le> N}" and a2:"(fg i)\<in> (simpleFormedFormulaSet i)"

shows "and2ListF (applySym2Form p (andList (map (\<lambda>i. fg i) (down N)))) =
      and2ListF (andList (map (applySym2Form p) (map (\<lambda>i. fg i) (down N))))" (is "?P N")
proof(induct_tac N)
  show "?P 0"
    by auto
next
  fix N
  assume b1:"?P N"
  show "?P (Suc N) "
    by (simp add: b1)
qed

lemma wellFormAndlistIsSym1:
  assumes a1:"p permutes {i. i\<le> N}" and a2:"(fg i)\<in> (simpleFormedFormulaSet i)"

shows "and2ListF 
  (applySym2Form p (andList (map (\<lambda>j. implyForm (neg (eqn (Const (index i)) (Const (index j))))  (fg j)) (down N)))) =
      and2ListF (andList (map (applySym2Form p) (map (\<lambda>j. implyForm (neg (eqn (Const (index i)) (Const (index j))))  (fg j)) (down N))))" (is "?P N")
proof(induct_tac N)
  show "?P 0"
    by auto
next
  fix N
  assume b1:"?P N"
  show "?P (Suc N) "
    by (simp add: b1)
qed
end
