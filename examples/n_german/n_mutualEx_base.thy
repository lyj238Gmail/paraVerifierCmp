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
    (\<exists>i.   i \<le> N \<and> f = inv_27 i) \<or>
    (\<exists>i j. i \<le> N \<and> j \<le> N \<and> i \<noteq> j \<and> f = inv_7 i j) \<or>
    (\<exists>i j. i \<le> N \<and> j \<le> N \<and> i \<noteq> j \<and> f = inv_5 i j)
   }" 

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
(*{f.
    (\<exists> j.   j \<le> N \<and> i \<noteq> j \<and> f = inv_7 i j) \<or>
    (\<exists> j.   j \<le> N \<and> i \<noteq> j \<and> f = inv_5 i j)}"*)

definition n_Idle_PP :: "nat \<Rightarrow> nat\<Rightarrow>rule" where [simp]:
  "n_Idle_PP N i\<equiv> strengthenR (n_Idle_Ls N i) [] (n_Idle i)"

definition rulesOfPP :: "nat \<Rightarrow> rule set" where [simp]:
  "rulesOfPP N \<equiv> {r.
    (\<exists>i. i \<le> N \<and> r = n_Try i) \<or>
    (\<exists>i. i \<le> N \<and> r = n_Crit i) \<or>
    (\<exists>i. i \<le> N \<and> r = n_Exit i) \<or>
    (\<exists>i. i \<le> N \<and> r = n_Idle_PP N i) 
   }"
lemma onMapSetDown:
  "set (map f (down N)) ={g. \<exists>j.  j\<le>N \<and> g= f j}"
(*proof(induct_tac N,simp,auto) *)
  sorry 
lemma onMapStrenghthEnCat:
  "and2ListF (strengthen (x#xs) g) = and2ListF (strengthenForm x g) \<union> (and2ListF (strengthen xs g))"
  by (simp add: sup_left_commute)
    
lemma onMapStrenghthEnUn:
  "and2ListF (strengthen (xs@ys) g) =
  (and2ListF (strengthen (xs) g)) \<union> (and2ListF (strengthen ys g))"  (is "?P xs ys")
proof(induct_tac xs)
  show "?P [] ys"
  proof(simp)qed
next
  fix x xs

  assume a1:"?P xs ys"
  show "?P (x#xs) ys"
    using a1 by auto
qed

lemma onMapStrenghthEn:
  "  and2ListF ( strengthen (map f (down N)) g) =
  (and2ListF g) Un {g'. \<exists>j. j\<le>N   \<and> g' \<in> (and2ListF (strengthenForm (f j) g))  }" (is "?P N")
proof(induct_tac N)
  show "?P 0" 
    by simp
next
  fix N
  assume a1:"?P N"
  show "?P (Suc N)"
  proof -
    have b1:"(map f (down (Suc N))) =map f ([Suc N]@(down N))"
      by simp 
    from b1  show  "?P (Suc N)"
    proof( simp add:onMapStrenghthEnUn)  
      show "and2ListF g \<union> (and2ListF (strengthenForm (f (Suc N)) g) \<union> and2ListF (strengthenFormByForms (map f (down N)) g)) = and2ListF g \<union> {g'. \<exists>j\<le>Suc N. g' \<in> and2ListF (strengthenForm (f j) g)}"
        (is "?LHS = ?RHS")
      proof
        show "?LHS \<subseteq> ?RHS"
        proof
          fix x
          assume c1:"x \<in> ?LHS "
          show "x \<in> ?RHS"
          proof -
            have c2:"x \<in> and2ListF g | x \<in>(and2ListF (strengthenForm (f (Suc N)) g)) | x \<in>and2ListF (strengthenFormByForms (map f (down N)) g)  "
              using c1 by blast
            moreover
            {assume d1:"x \<in> and2ListF g"
              have "x \<in> ?RHS"
                using d1  by blast
            }
            moreover
            {assume d1:"x \<in>(and2ListF (strengthenForm (f (Suc N)) g))"
              have "x \<in> ?RHS"
                using d1  by blast
            }
            moreover
            {assume d1:"x \<in>and2ListF (strengthenFormByForms (map f (down N)) g)"
              have "x \<in> (and2ListF g) Un {g'. \<exists>j. j\<le>N   \<and> g' \<in> (and2ListF (strengthenForm (f j) g))  }"
                apply(cut_tac a1,simp)
                using a1 d1  by blast
              then    have "x \<in> ?RHS"
                by auto 
            }
            ultimately show "x \<in> ?RHS"
              by blast
          qed
        qed
      next
        show "?RHS \<subseteq> ?LHS"
        proof
          fix x
          assume c1:"x \<in> ?RHS "
          show "x \<in> ?LHS"
          proof -
            have d1:" x \<in> and2ListF g | x \<in> {g'. \<exists>j\<le>Suc N. g' \<in> and2ListF (strengthenForm (f j) g)}"
              using c1 by auto
            moreover
            {assume d1:"x \<in> and2ListF g "
              have  "x \<in> ?LHS"
                using d1 by blast
            }
            moreover
            {assume d1:"x \<in> {g'. \<exists>j\<le>Suc N. g' \<in> and2ListF (strengthenForm (f j) g)} "
              have  "x \<in> {g'.  g' \<in> and2ListF (strengthenForm (f (Suc N)) g)} | x \<in> {g'. \<exists>j\<le> N. g' \<in> and2ListF (strengthenForm (f j) g)}"
                using d1 le_Suc_eq by force 
              moreover
              {assume d1:"x \<in> {g'.  g' \<in> and2ListF (strengthenForm (f (Suc N)) g)} "
                have "x \<in> ?LHS"
                  using d1 by auto
              }
              moreover
              {assume d1:"  x \<in> {g'. \<exists>j\<le> N. g' \<in> and2ListF (strengthenForm (f j) g)} "
                have "x \<in> ?LHS"
                  using a1 calculation(1) by auto 
              }
            ultimately have "x \<in> ?LHS"
              by blast
          }
          ultimately show "x \<in> ?LHS"
              by blast
          qed
        qed
      qed
    qed
  qed
qed

lemma tautSYm: assumes a1:"p permutes {i.  i \<le> N}"
  shows "taut f= taut (applySym2Form p f)"
proof
  assume b1:"taut f"
  show "taut (applySym2Form p (f))"
  proof(unfold taut_def,rule allI)
    fix s
    have b2:"formEval f ( (applySym2State (inv p) s))"
      by(cut_tac b1,auto) 
    have b3:"formEval (applySym2Form  p f) (applySym2State p (applySym2State (inv p) s)) = formEval f ( (applySym2State (inv p) s))"
      using stFormSymCorrespondence a1 by auto
    have b4:"bij p"
      using a1 permutes_bij by blast
      
    have b5:"applySym2State p (applySym2State (inv p) s) =s "
    proof
      fix x
      show "applySym2State p (applySym2State (inv p) s) x  =s x"
        using b4  applySym2StateInv by blast 
    qed
    with b2 b5 b3 show "formEval (applySym2Form  p f) s"
      by auto
  qed
next
  assume b1:"taut (applySym2Form p (f)) "
  show "taut f"
  proof(unfold taut_def,rule allI)
    fix s
    have b2:"formEval (applySym2Form p (f)) ( (applySym2State p s))"
      by(cut_tac b1,auto) 
    have b4:"bij p"
      using a1 permutes_bij by blast
    then show "formEval f s"
      using assms b2 stFormSymCorrespondence by auto
  qed
qed

lemma onStrengthenFormSymApp:
  assumes a1:"p permutes {i. i \<le> N}"
  shows "applySym2Form p (strengthenForm x g) = strengthenForm (applySym2Form p x) (applySym2Form p g)"
  (is "?LHS=?RHS")
proof(case_tac x)
  fix ant0 cons0
  assume b1:"x=implyForm ant0 cons0"  
  have "taut (implyForm g ant0) | \<not> taut (implyForm g ant0)" 
    by blast
  moreover
  {assume b2:"taut (implyForm g ant0)"
    have b3:"applySym2Form p (strengthenForm x g) =applySym2Form p (cons0)"  
       by(cut_tac b1 b2, simp)
     from b2 have b4:"taut (applySym2Form p (implyForm g ant0))"
       using a1 tautSYm by blast
     then have b5:"taut (implyForm (applySym2Form p g) (applySym2Form p ant0))"
       by simp
     with b1  have "strengthenForm (applySym2Form p x) (applySym2Form p g) =
          applySym2Form p (cons0)"
       by simp
     with b3 have "?LHS=?RHS"
       by simp
   }
  moreover
  {assume b2:"\<not>taut (implyForm g ant0)"
    have b3:"applySym2Form p (strengthenForm x g) =chaos"
      by(cut_tac b1 b2, auto)
    from b2 have b4:"\<not>taut (applySym2Form p (implyForm g ant0))"
       using a1 tautSYm by blast
     then have b5:"~taut (implyForm (applySym2Form p g) (applySym2Form p ant0))"
       by simp  
    with b1  have "strengthenForm (applySym2Form p x) (applySym2Form p g) =
          chaos"
      by auto 
     with b3 have "?LHS=?RHS"
       by simp
   }
   ultimately show "?LHS=?RHS"
     by blast
 qed(auto)


lemma  onMapStrenghthEnSymApp:
  assumes a1:"p permutes {i. i \<le> N}"
  shows
  "and2ListF (applySym2Form p (strengthen Fs g) ) =
  and2ListF (strengthen (map (applySym2Form p) Fs) (applySym2Form p g))" (is "?P Fs")
proof(induct_tac Fs)
  show "?P []"
    by auto
next
  fix x xs
  assume a1:"?P (xs)"
  show "?P (x#xs)"  (is "?LHS = ?RHS")
  proof-
    have b1:"?LHS = and2ListF (applySym2Form p g) \<union> 
    (and2ListF (applySym2Form p (strengthenForm x g)) \<union> 
    and2ListF (applySym2Form p (strengthenFormByForms xs g))) "
      by simp
    have b2:"?RHS= and2ListF (applySym2Form p g) \<union> 
    (and2ListF (strengthenForm (applySym2Form p x) (applySym2Form p g)) \<union> 
    and2ListF (strengthenFormByForms (map (applySym2Form p) xs) (applySym2Form p g)))"
      apply(simp add:onMapStrenghthEnUn onMapStrenghthEn)
      done
    have b3:"(applySym2Form p (strengthenForm x g)) =
       (strengthenForm (applySym2Form p x) (applySym2Form p g)) "
      using assms onStrengthenFormSymApp by auto
      
    show "?LHS =?RHS"
      using b1 b2 b3 a1 onStrengthenFormSymApp by auto
  qed
qed

lemma and2ListForall:
  "(\<forall>f. f \<in>and2ListF g \<longrightarrow> formEval f s) = formEval g s"
  
lemma and2ListFCong:
  shows a1:"and2ListF g1=and2ListF g2 \<longrightarrow> formEval  g1 s=formEval  g2 s"
   
  sorry


lemma reachSymLemma':
  assumes a1: "symPredList N fs"
    and a2: "symProtRules' N rs" 
      (*a3:"s \<in> reachableSetUpTo (andList fs) rs i " and*)
    and a4: "p permutes {x.   x \<le> N}"
  shows
    "\<forall>s. s \<in> reachableSetUpTo (andList fs) rs i \<longrightarrow>
         applySym2State p s \<in> reachableSetUpTo (andList fs) rs i" (is "?P i")
proof (induct_tac i)
  show "?P 0"
  proof (rule allI,simp,rule impI,rule andListForm2,rule allI,rule impI)
    fix s f
    assume b1:"formEval (andList fs) s " and
    b2:"f \<in> set fs"
    have "(applySym2Form (inv p) f) \<in> set fs "
      by (meson a1 a4 b2 permutes_inv symPredList_def)
    then have b3:" formEval (applySym2Form (inv p) f) s"
      using b1 by blast 
    show "formEval f (applySym2State p s)"
      by (metis (no_types, lifting) 
          Collect_cong a4 applySym2ExpFormInv b3 bij_def permutes_inj 
          permutes_inv_o(1) stFormSymCorrespondence surj_iff)
  qed
next
  fix n
  assume b1:"?P n"
  show "?P (Suc n)"
  proof
    fix s
    show "s \<in> reachableSetUpTo (andList fs) rs (Suc n) \<longrightarrow> applySym2State p s \<in> reachableSetUpTo (andList fs) rs (Suc n)"
    proof
    assume c1:"s \<in> reachableSetUpTo (andList fs) rs (Suc n)"
    from c1 have c2:"s \<in> reachableSetUpTo (andList fs) rs ( n) \<or>
      (\<exists> s0 r. s0 \<in> reachableSetUpTo (andList fs)  rs n \<and> r \<in> rs \<and> 
        formEval (pre r) s0 \<and>s = trans1 (act r) s0)"
      by auto
    moreover
    {assume c2:"s \<in> reachableSetUpTo (andList fs) rs ( n)"
      have c3:"applySym2State p s \<in> reachableSetUpTo (andList fs) rs ( n)"
        using b1 c2 by blast
      have "
    applySym2State p s \<in> reachableSetUpTo (andList fs) rs (Suc n)"
        by (simp add: c3)
    }
    moreover
    {assume c2:" (\<exists> s0 r. s0 \<in> reachableSetUpTo (andList fs)  rs n \<and> r \<in> rs \<and> 
        formEval (pre r) s0 \<and>s = trans1 (act r) s0)"
      then obtain s0 r where c2:"s0 \<in> reachableSetUpTo (andList fs)  rs n \<and> r \<in> rs \<and> 
        formEval (pre r) s0 \<and>s = trans1 (act r) s0"
        by blast

      from b1 c1 have c3:"applySym2State p s0 \<in> reachableSetUpTo (andList fs) rs ( n)"
        using b1 c2 by blast
      have c4:"formEval (applySym2Form p (pre  r)) (applySym2State p s0)"
        using a4 c2 stFormSymCorrespondence by auto
       
      have c5:" applySym2Form p (pre  r) = pre (applySym2Rule p r)"
        apply(case_tac "r",auto) done
      with c4 have c6:"formEval ( pre (applySym2Rule p r)) (applySym2State p s0)"
        by simp
      
      have c7:"\<exists>r'. alphaEqRule r'( applySym2Rule p r) \<and>r' \<in> rs"
        using a2 a4 c2 symProtRules'_def by blast
      then obtain r' where c7:" alphaEqRule r'( applySym2Rule p r) \<and>r' \<in> rs"
        by blast

      from c6 c7 have c7a:"formEval ( pre r') (applySym2State p s0)"
        by (simp add: c6 and2ListFCong)
        
      have c8:"applySym2State p (trans1 (act r) s0) =
          trans1 (act (applySym2Rule p r)) (applySym2State p s0)"
        by (metis a4 act.simps applySym2Rule.simps rule.exhaust transSym)

      have c9:"trans1 (act r' ) (applySym2State p s0) \<in>  reachableSetUpTo (andList fs) rs (Suc n)"
        using c3 c7 c7a  by fastforce 

       have c9a:"trans1 (act r' ) (applySym2State p s0) = trans1 (act (applySym2Rule p r)) (applySym2State p s0)"
        using c3 c7 c7a  by fastforce 

      have "applySym2State p s \<in> reachableSetUpTo (andList fs) rs (Suc n)"
        using c2 c8 c9 c9a by auto 
    } 
    ultimately show "applySym2State p s \<in> reachableSetUpTo (andList fs) rs (Suc n)"
      by blast
  qed
qed
qed


lemma SymLemma':
  assumes a1: "symPredList N fs"
    and a2: "symProtRules' N rs"
    and a3: "\<forall>s i. s \<in> reachableSetUpTo (andList fs) rs i \<longrightarrow> formEval f s"
    and a4: "p permutes {x.   x \<le> N}"
  shows
    "\<forall>s i. s \<in> reachableSetUpTo (andList fs) rs i \<longrightarrow> formEval (applySym2Form p f) s" (is "?P i")
  sorry
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
]"

lemma mutualExPPSimmutualEx:
  assumes a1:"\<forall>r. r \<in> rs \<longrightarrow>(\<exists> Ls . set Ls \<subseteq> set S \<and>  strengthenR Ls r \<in> rs')" and
  a2:"\<forall>i s f. s \<in>reachableSetUpTo I rs' i \<longrightarrow> f \<in>set S \<longrightarrow>formEval f s" 
shows "\<forall>s f. s \<in>reachableSetUpTo I rs i \<longrightarrow>
   f \<in>set S \<longrightarrow>(s \<in>reachableSetUpTo I rs' i \<and>formEval f s)" (is "?P i")
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
definition rules::"nat \<Rightarrow> rule set" where [simp]:
"rules N \<equiv> {r.
(\<exists> i. i\<le>N\<and>r=n_Try  i) \<or>
(\<exists> i. i\<le>N\<and>r=n_Crit  i) \<or>
(\<exists> i. i\<le>N\<and>r=n_Exit  i) \<or>
(\<exists> i. i\<le>N\<and>r=n_Idle  i) \<or>
(r=n_Crit_i_3  ) \<or>
(r=n_Idle_i_3  )\<or> r=skipRule
}"







axiomatization  where axiomOnf2 [simp,intro]:
   "s \<in> reachableSet (set (allInitSpecs N )) (rules N) \<Longrightarrow>  1 < N \<Longrightarrow> 1 < i \<Longrightarrow> j<2 \<Longrightarrow>  formEval (f 0 1) s \<Longrightarrow> formEval (f i j) s"

axiomatization  where axiomOnf1 [simp,intro]:
   "s \<in> reachableSet (set (allInitSpecs N )) (rules N) \<Longrightarrow> 1 < N \<Longrightarrow> 1 < i \<Longrightarrow>formEval (f 0 ) s \<Longrightarrow> formEval (f i) s"




subsection{*Definitions of initial states*}

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
end
