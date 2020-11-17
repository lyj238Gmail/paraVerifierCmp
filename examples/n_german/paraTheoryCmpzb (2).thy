(*  Title:     paraTheory.thy
    Author:    Yongjian Li, State Key Laboratory of Computer Science, Institute of Software,
Chinese Academy of Sciences
    Copyright   2016  State Key Laboratory of Computer Science, Institute of Software,
Chinese Academy of Sciences

A mechanical theory for verification of parameterized protocols like cache coherence protocols
*)

theory paraTheoryCmpzb
  imports Main "HOL-Library.Permutations"
begin

section \<open>Datatypes to define variables, values, expressions, and formulas\<close>


datatype varType =
  Ident string | Para string nat | dontCareVar
  (* | Field varType string *)

text \<open>
Three kinds of variables are used in the protocols:
1. simple identifiers to define global variables 
2. array variables ---- arr[i]
3. record variables ---- rcd.f
\<close>

datatype scalrValueType =
  enum string string | index nat | boolV bool | dontCare

text \<open>
Three kinds of values used in the protocols.
1. enumerating values
2. natural numbers 
3. Boolean values
\<close>

datatype expType =
  IVar varType | Const scalrValueType | iteForm formula expType expType |dontCareExp
and
  formula = eqn expType expType |
            andForm formula formula |
            neg formula |
            orForm formula formula |
            implyForm formula formula |
            chaos |
            dontCareForm

primrec andList::"formula list \<Rightarrow> formula" where
  "andList [] = chaos" |
  "andList (frm#frms) = andForm frm (andList frms)" 

primrec orList::"formula list \<Rightarrow> formula" where
  "orList [] = chaos" |
  "orList (frm#frms) = orForm frm (andList frms)" 

text \<open>
$Experssions$ and $formulas$ are defined mutually recursively.
$Experssions$ can be simple or compound. 
A simple expression is either a variable or a constant, 
while a compound expression is constructed with the ite(if-then-else) form. 
A $formula$ can be an atomic formula or a compound formula.
An atomic formula can be a boolean variable or constant, 
or in the equivalence forms. A $formula$ can also be constructed by 
using the logic connectives, including negation, conjunction, 
disjunction, implication.
\<close>
              
section \<open>Datatypes to define assignments, statements, rules\<close>

type_synonym assignType = "varType \<times> expType"

datatype statement = 
  skip | assign assignType | parallel assignType statement

text \<open>A statement is is just a lists of assignments,
but these assignments are executed in parallel, 
\emph{not} in a sequential order\<close>

type_synonym paraStatement = "nat \<Rightarrow> statement"

text \<open>A parameterized statement is just a function from a
parameter to a statement.\<close>


primrec cat :: "statement \<Rightarrow> statement \<Rightarrow> statement" where
  cat1: "cat (assign a) S = parallel a S" |
  cat2: "cat (parallel a S1) S = parallel a (cat S1 S)"|
  cat3: "cat skip S = S"

text \<open>For conveniece, we also define the concatenation of statements.\<close>

primrec parallelList :: "statement list \<Rightarrow> statement" where
  "parallelList [] = skip"|
  "parallelList (S1#SL) = cat S1 (parallelList (SL))" 

fun forallSent::"nat list \<Rightarrow> paraStatement \<Rightarrow> statement" where
  oneSent: "forallSent [i] paraS = paraS i"|
  moreSent:" forallSent (i#xs) paraS = cat (paraS i) (forallSent xs paraS)" 
 

type_synonym paraFormula = "nat \<Rightarrow> formula"

text \<open>Similarly, a parameterized formula is a function from
a parameter to a formula. We also define the $\mathsf{forall}$ 
and $mathsf{exists}$ formulas$.\<close>

fun forallForm :: "nat list \<Rightarrow> paraFormula \<Rightarrow> formula" where
  oneAllForm: "forallForm [i] forms = forms i" |
  moreAllForm: "forallForm (i#j#xs) forms = andForm (forms i) (forallForm (j#xs) forms)"

fun existsForm :: "nat list \<Rightarrow> paraFormula \<Rightarrow> formula" where
  oneExForm: "existsForm [i] forms = forms i"|
  moreExForm: "existsForm (i#j#xs) forms = orForm (forms i) (forallForm (j#xs) forms)"


datatype rule = guard formula statement

text \<open>With the formalizatiion of formula and statement,
it is natural to define a rule. A guard and
statement of a rule are also defined for convenience.\<close>


primrec pre :: "rule \<Rightarrow> formula" where
  "pre (guard f a) = f"

primrec act :: "rule \<Rightarrow> statement" where
  "act (guard f a) = a"


type_synonym paraRule = "nat \<Rightarrow> rule"
text \<open>A parameterized rule is just from a natural number to a rule.\<close>



section \<open>Semantics of a protocol\<close>


type_synonym state = "varType \<Rightarrow> scalrValueType"

text \<open>A state of a protocol is an instantaneous snapshot of its
behaviour given by an assignment of values to variables of
the circuit.\<close>

text \<open>The formal semantics of an expression and a formula is 
formalized as follows:\<close>

primrec expEval :: "expType \<Rightarrow> state \<Rightarrow> scalrValueType" and
        formEval :: "formula \<Rightarrow> state \<Rightarrow> bool" where
  evalVar:   "expEval (IVar ie) s = s ie" |
  evalConst: "expEval (Const i) s = i" |
  evalITE:   "expEval (iteForm f e1 e2) s = 
               (if formEval f s then expEval e1 s else expEval e2 s)" |
  evalDontCareExp: "expEval (dontCareExp) s = dontCare" |

  evalEqn: "formEval (eqn e1 e2) s = ((expEval e1 s) = (expEval e2 s))" |
  evalAnd: "formEval (andForm f1 f2) s = ((formEval f1 s) \<and> (formEval f2 s))" |
  evalNeg: "formEval (neg f1) s = (\<not>(formEval f1 s))" |
  evalOr:  "formEval (orForm f1 f2) s = ((formEval f1 s) \<or> (formEval f2 s))" |
  evalImp: "formEval (implyForm f1 f2) s = ((formEval f1 s) \<longrightarrow> (formEval f2 s))" |
  evalDontCareForm: "formEval dontCareForm s = True" |
  evalChaos: "formEval chaos s = True"

definition taut::"formula \<Rightarrow> bool" where [simp]:
  "taut f \<equiv> \<forall>s. formEval f s"

text \<open>A state transition from a state to another state, which is caused by
an execution of a statement, is defined as follows:\<close>

primrec statement2Assigns :: "statement \<Rightarrow> assignType list" where
  "statement2Assigns (assign asgn) = [asgn]" |
  "statement2Assigns (parallel a S) = a # statement2Assigns S" |
  "statement2Assigns skip = []"

definition wellformedAssgnList :: "assignType list \<Rightarrow> bool" where
  "wellformedAssgnList asgns = distinct (map fst asgns)"

text \<open>Condition wellformedAssgnList guarantees that asgns assign different
  variables to values\<close>

primrec transAux :: "assignType list \<Rightarrow> state \<Rightarrow> state" where
  "transAux [] s v= s v" |
  "transAux (pair#asgns) s v = 
    (if fst pair = v then expEval (snd pair) s
     else transAux asgns s v)"

definition trans:: "statement \<Rightarrow> state \<Rightarrow> state" where [simp]:
  "trans S s = transAux (statement2Assigns S) s"

fun trans1 :: "statement \<Rightarrow> state \<Rightarrow> state" where
  "trans1 skip s v = s v" |
  "trans1 (assign as) s v = (if fst as = v then expEval (snd as) s else s v)" |
  "trans1 (parallel as S) s v = (if fst as = v then expEval (snd as) s else trans1 S s v)"

text \<open>Here we must point out the fact that the assignments in a 
parallel assignment is executed in parallel, and the statement can be 
transformed into a wellformedAssgnList, 
therefore we always assign an evaluation of an expression in 
the state $s$ to the corresponding variable.\<close>


text \<open>The reachable state set of a protocol, 
which is described by a set of initial formulas and a set of rules,
can be formalized inductively as follows:\<close>

inductive_set reachableSet :: "formula set \<Rightarrow> rule set \<Rightarrow> state set" 
  for inis::"formula set" and rules::"rule set" where

  initState: "\<lbrakk>formEval ini s; ini \<in> inis\<rbrakk> \<Longrightarrow> s \<in> reachableSet inis rules" |

  oneStep: "\<lbrakk>s \<in> reachableSet inis rules;
             r \<in> rules;
             formEval (pre r) s\<rbrakk> \<Longrightarrow>
             trans (act r) s \<in> reachableSet inis rules"

primrec reachableSetUpTo :: "formula \<Rightarrow> rule set \<Rightarrow> nat \<Rightarrow> state set" where
  reachableSet0: "reachableSetUpTo I rs 0 = {s. formEval I s}" |
  reachableSetNext: "reachableSetUpTo I rs (Suc i) =
    (reachableSetUpTo I rs i) \<union>
    {s. \<exists>s0 r. s0 \<in> reachableSetUpTo I rs i \<and> r \<in> rs \<and> 
               formEval (pre r) s0 \<and> s = trans1 (act r) s0}"

(*inductive_set reachableSetUpTo::" formula \<Rightarrow> rule set \<Rightarrow>nat\<Rightarrow>state set" 
  for  ini::"formula "  and rules::"rule set"  and i::"nat"  where

initStateUpTo:  "\<lbrakk>formEval  ini s; i=0\<rbrakk>  \<Longrightarrow>(  s \<in>  ( reachableSetUpTo ini rules i))" |

oneStepUpTo:    " \<lbrakk>s \<in>  reachableSetUpTo ini rules i;
               r \<in>   rules ;formEval (pre r ) s \<rbrakk> \<Longrightarrow>  
  trans  (act r ) s  \<in>  reachableSetUpTo ini rules (i+1)"
*)

text \<open>The rule $\mathsf{initState}$ says that a state $s$ is
in $\mathsf{reachableSet}~inis~ rules$ if
there exists a formula $ini$ that is true in state $s$.
Next rule $\mathsf{oneStep}$ says that 
$$\mathsf{ trans}~  ($\mathsf{act}~ r )~ s $ is also in
$\mathsf{reachableSet}~inis~ rules$ if $s$ already is in 
$\mathsf{reachableSet}~inis~ rules$ and $r \<in> rules$.
\<close>

section \<open>Substitions and preconditions\<close>

primrec valOf :: "assignType list \<Rightarrow> varType \<Rightarrow> expType" where
  "valOf [] v = IVar v" |
  "valOf (x#xs) v = (if fst x = v then snd x else valOf xs v)"
text \<open>Let $asgn\!=\![(v_1,e_1),\ldots,(v_n,e_n)]$ be an assignment,
 valOf asgn $x_i$ is the expression $e_i$ assigned to $v_i$\<close>

lemma lemmaOnValOf:
  "expEval (valOf (statement2Assigns S) v) s = transAux (statement2Assigns S) s v" 
  (is "?LHS1 S = ?RHS1 S")
proof(induct_tac S)
  let ?S="skip"
  show "?LHS1 ?S=?RHS1 ?S"
    by auto
next
  fix x
  let ?S="assign x"
  show "?LHS1 ?S=?RHS1 ?S"
    by auto
  next
  fix assign S2
  let ?S="parallel assign S2"
  assume  b1:"?LHS1 S2 =?RHS1 S2"
  show "?LHS1 ?S =?RHS1 ?S"
  proof(case_tac "fst assign =v",force)
  assume c1:"fst assign \<noteq> v"
  show "?LHS1 ?S =?RHS1 ?S"
    apply(cut_tac b1 c1,simp) done
  qed
qed

text \<open>This lemma says that the value of (statement2Assigns S) assigned to variable v,
which is evaluated at the state s, is the same as that of v at the result state after
execution of S from state s\<close>

primrec substExp :: "expType \<Rightarrow> assignType list \<Rightarrow> expType"
  and
  substForm :: "formula \<Rightarrow> assignType list \<Rightarrow> formula" where

  substExpVar:   "substExp (IVar v') asgns = valOf asgns v'" |
  substExpConst: "substExp (Const i) asgns = Const i" |
  substExpite:   "substExp (iteForm f e1 e2) asgns =
                   iteForm (substForm f asgns) (substExp e1 asgns) (substExp e2 asgns)" |
  substDontCare: "substExp (dontCareExp) asgns = dontCareExp"|
  substFormEqn:  "substForm (eqn l r) asgns = eqn (substExp l asgns) (substExp r asgns)"  |
  substFormAnd:  "substForm (andForm f1 f2) asgns = andForm (substForm f1 asgns) (substForm f2 asgns)" |
  substFormNeg:  "substForm (neg f1) asgns = neg (substForm f1 asgns)" |
  substFormOr:   "substForm (orForm f1 f2) asgns = orForm (substForm f1 asgns) (substForm f2 asgns)" |
  substFormImp:  "substForm (implyForm f1 f2) asgns = implyForm (substForm f1 asgns) (substForm f2 asgns)" |
  substDontCareForm: "substForm (dontCareForm) asgns = dontCareForm" |
  substFormChaos: "substForm chaos asgns = chaos"

section \<open>Permutations\<close>

type_synonym nat2nat = "nat \<Rightarrow> nat"

primrec applySym2Const :: "nat2nat \<Rightarrow> scalrValueType \<Rightarrow> scalrValueType" where
  "applySym2Const f (index n) = index (f n)" |
  "applySym2Const f (boolV b) = boolV b" |
  "applySym2Const f (enum t e) = enum t e" |
  "applySym2Const f (dontCare) = dontCare"

lemma applySym2ConstInv [simp]:
  assumes "bij p"
  shows "applySym2Const p (applySym2Const (inv p) v) = v"
proof (cases v)
  case (index x2)
  then show ?thesis
    using assms bij_is_surj surj_iff_all by fastforce
qed (auto)

lemma applySym2ConstInj [simp]:
  assumes "bij p"
  shows "(applySym2Const p a = applySym2Const p b) \<longleftrightarrow> a = b"
  by (metis applySym2ConstInv assms bij_imp_bij_inv inv_inv_eq)


primrec applySym2Var :: "nat2nat \<Rightarrow> varType \<Rightarrow> varType" where
  "applySym2Var f (Ident n) = Ident n" |
  "applySym2Var f (Para v i) = Para v (f i)" |
  "applySym2Var f dontCareVar = dontCareVar"
  (*"applySym2Var f (Field v n)=Field (applySym2Var f v) n "*)

lemma applySym2VarInv [simp]:
  assumes "bij p"
  shows "applySym2Var p (applySym2Var (inv p) v) = v"
proof (cases v)
  case (Ident x2)
  then show ?thesis
    using assms bij_is_surj surj_iff_all by fastforce
next
  case (Para x21 x22)
  then show ?thesis
    using assms bij_betw_inv_into_right by fastforce 
qed (auto)

lemma invinvpIsp [simp]:
  assumes a1: "bij p"
  shows "inv (inv p) = p"
  using assms inv_inv_eq by blast

primrec applySym2Exp :: "nat2nat \<Rightarrow> expType \<Rightarrow> expType"
  and
  applySym2Form :: "nat2nat \<Rightarrow> formula \<Rightarrow> formula" where

  "applySym2Exp f (IVar v) = IVar (applySym2Var f v)" |
  "applySym2Exp f (Const c) = Const (applySym2Const f c)" |
  "applySym2Exp f (iteForm f1 e1 e2) =
    iteForm (applySym2Form f f1) (applySym2Exp f e1) (applySym2Exp f e2)" |
  "applySym2Exp f dontCareExp =dontCareExp" | 
  "applySym2Form f (eqn l r) = eqn (applySym2Exp f l) (applySym2Exp f r)" |
  "applySym2Form f (andForm f1 f2) = andForm (applySym2Form f f1) (applySym2Form f f2)" |
  "applySym2Form f (neg f1) = neg (applySym2Form f f1)" |
  "applySym2Form f (orForm f1 f2) = orForm (applySym2Form f f1) (applySym2Form f f2)" |
  "applySym2Form f (implyForm f1 f2) = implyForm (applySym2Form f f1) (applySym2Form f f2)" |
  "applySym2Form f dontCareForm = dontCareForm" | 
  "applySym2Form f chaos = chaos"

lemma applySym2ExpFormInv [simp]:
  assumes "bij p"
  shows "applySym2Exp p (applySym2Exp (inv p) e) = e \<and>
         applySym2Form p (applySym2Form (inv p) f) = f"
proof (induction rule: expType_formula.induct)
  case (IVar x)
  show ?case
    by (simp add: assms)
next
  case (Const x)
  show ?case
    by (simp add: assms)
qed (auto)

primrec applySym2Statement :: "nat2nat \<Rightarrow> statement \<Rightarrow> statement" where
  "applySym2Statement f skip = skip" |
  "applySym2Statement f (assign as) = assign (applySym2Var f (fst as), applySym2Exp f (snd as))" |
  "applySym2Statement f (parallel as S) =
    parallel (applySym2Var f (fst as), applySym2Exp f (snd as)) (applySym2Statement f S)"

primrec applySym2Rule::"nat2nat \<Rightarrow> rule \<Rightarrow> rule" where
  "applySym2Rule f (guard g a) = guard (applySym2Form f g) (applySym2Statement f a)"

text \<open>Applying a permutation to a state\<close>
fun applySym2State :: "nat2nat \<Rightarrow> state \<Rightarrow> state" where
  "applySym2State p s (Ident sn) = applySym2Const p (s (Ident sn))" |
  "applySym2State p s (Para sn i) = applySym2Const p (s (Para sn ((inv p) i)))"|
  "applySym2State p s dontCareVar=applySym2Const p (s dontCareVar)"

lemma applySym2statementInv[simp]:
  assumes "bij p"
  shows "applySym2Statement p (applySym2Statement (inv p) S) = S" (is "?P S")
proof(induct_tac S)
  show "?P skip"
    by auto
next
  fix x
  let ?S="assign x"
  show "?P ?S"
    apply auto
    by (simp add: assms)
next
  fix as S
  let ?S="parallel as S"
  assume a1:"?P S"
  show "?P ?S"
    by (simp add: a1 assms)
qed 

lemma applySym2StateInv[simp]:
  assumes "bij p"
  shows "applySym2State p (applySym2State (inv p) s) v = s v" (is "?P s")
proof -
  show "applySym2State p (applySym2State (inv p) s) v = s v" (is "?P s v")
  proof (induct_tac v)
    fix x
    let ?v="Ident x"
    show "?P s ?v"
      by (metis applySym2ConstInv applySym2State.simps(1) assms) 
  next
    fix n i
    let ?v="Para n i"
    show "?P s ?v"
      by (metis (mono_tags, hide_lams)
          applySym2ConstInv applySym2State.simps(2) 
          assms bijection.bij_inv bijection.inv_left bijection_def)
  next
    let ?v="dontCareVar"
    show "?P s ?v"
      by (simp add: assms)
  qed 
qed


text \<open>A set of rules is symmetric\<close>
definition symProtRules :: "nat \<Rightarrow> rule set \<Rightarrow> bool" where [simp]:
  "symProtRules N rs = (\<forall>p r. p permutes {x. 1 \<le> x \<and> x \<le> N} \<and> r \<in> rs \<longrightarrow> applySym2Rule p r \<in> rs)"

text \<open>A list of formulas is symmetric\<close>
definition symPredList :: "nat \<Rightarrow> formula list \<Rightarrow> bool" where [simp]:
  "symPredList N fs = (\<forall>p f. p permutes {x. 1 \<le> x \<and> x \<le> N} \<and> f \<in> set fs \<longrightarrow> applySym2Form p f \<in> set fs)"

lemma stFormSymCorrespondence:
  assumes a1: "p permutes {x. 1 \<le> x \<and> x \<le> N}"
  shows "expEval (applySym2Exp p e) (applySym2State p s) = applySym2Const p (expEval e s) \<and>
         formEval (applySym2Form p f) (applySym2State p s) = formEval f s"
    (is "?Pe p e \<and> ?Pf p f")
proof (induction rule: expType_formula.induct)
  case (IVar x)
  have "bij p"
    using a1 by (simp add: permutes_bij)
  then show ?case
    apply (cases x)
    by (auto simp add: bijection.intro bijection.inv_left)
next
  case (eqn x1 x2)
  have "bij p"
    using a1 by (simp add: permutes_bij)
  show ?case by (auto simp add: eqn \<open>bij p\<close>)
qed (auto)

lemma andListFormAux1:
  "set fs \<subseteq> fs' \<longrightarrow> (\<forall>inv. inv \<in> fs' \<longrightarrow> formEval inv s) \<longrightarrow> formEval (andList fs) s"
  by (induct_tac fs, auto)
  
lemma andListForm1 [simp,intro]:
  "set fs \<subseteq> invs \<Longrightarrow> \<forall>inv. inv \<in> invs \<longrightarrow> formEval inv s \<Longrightarrow> formEval (andList fs) s"
  by (metis andListFormAux1)  

lemma andListForm2 [simp,intro]:
  "\<forall>inv. inv \<in> set fs \<longrightarrow> formEval inv s \<Longrightarrow> formEval (andList fs) s"
  by blast

lemma andListForm3Aux:
  "f \<in> set fs \<longrightarrow> formEval (andList fs) s \<longrightarrow> formEval f s "
  by (induct_tac fs, auto)

lemma andListForm3 [simp,intro]:
  assumes a1: "f \<in> set fs"
    and a2: "formEval (andList fs) s"
  shows "formEval f s"
  using a1 a2 andListForm3Aux by blast

lemma transSym:
  (*assumes a1:"formEval (pre r) s0"  formEval (pre  (applySym2Rule p r)) s0 \<and>*)
  assumes a1: "p permutes {x. 1 \<le> x \<and> x \<le> N}"
  shows "applySym2State p (trans1 S s0) =
         trans1 (applySym2Statement p S) (applySym2State p s0)" (is "?P S")
proof (induction S)
  case skip
  then show ?case by auto
next
  case (assign x)
  have "applySym2State p (trans1 (assign x) s0) v =
        trans1 (applySym2Statement p (assign x)) (applySym2State p s0) v" for v
  proof (cases v)
    case (dontCareVar)
      have *: "applySym2Var p (fst x) = dontCareVar\<Longrightarrow> fst x =dontCareVar"
      apply (cases "fst x") by auto
     show ?thesis
       using "*" assms dontCareVar stFormSymCorrespondence by auto
    next
     case (Ident x1)
    have *: "applySym2Var p (fst x) = Ident x1 \<Longrightarrow> fst x = Ident x1"
      apply (cases "fst x") by auto
    show ?thesis
      apply (simp only: Ident)
      apply (simp add: stFormSymCorrespondence[OF a1])
      using * by auto
  next
    case (Para x21 x22)
    have "bij p"
      using a1 by (auto simp add: permutes_bij)
    have *: "p (inv p x22) = x22"
      by (meson \<open>bij p\<close> bij_inv_eq_iff)
    have **: "applySym2Var p (fst x) = Para x21 x22 \<Longrightarrow> fst x = Para x21 (inv p x22)"
      apply (cases "fst x")
      by (auto simp add: \<open>bij p\<close> bij_inv_eq_iff)
    show ?thesis
      apply (simp only: Para)
      by (auto simp add: stFormSymCorrespondence[OF a1] * **)
  qed
  then show ?case by blast
next
  fix as S
  let ?s="parallel as S"
  assume b1:"?P S"
  have " applySym2State p (trans1 (parallel as S) s0) v= trans1 (applySym2Statement p (parallel as S)) (applySym2State p s0) v" for v
  proof (cases v)
    case (dontCareVar)
      have *: "applySym2Var p (fst as) = dontCareVar\<Longrightarrow> fst as =dontCareVar"
      apply (cases "fst as") by auto
      show ?thesis
        apply (simp only: dontCareVar)
        apply (simp add: stFormSymCorrespondence[OF a1])
        by (metis "*" applySym2State.simps(3) b1)
  next    
    case (Ident x1)
    have *: "applySym2Var p (fst as) = Ident x1 \<Longrightarrow> fst as = Ident x1"
      apply (cases "fst as") by auto
    show ?thesis
      apply (simp only: Ident)
      apply (simp add: stFormSymCorrespondence[OF a1])
      by (metis "*" applySym2State.simps(1) b1)
  next
    case (Para x21 x22)
    have "bij p"
      using a1 by (auto simp add: permutes_bij)
    have *: "p (inv p x22) = x22"
      by (meson \<open>bij p\<close> bij_inv_eq_iff)
    have **: "applySym2Var p (fst as) = Para x21 x22 \<Longrightarrow> fst as = Para x21 (inv p x22)"
      apply (cases "fst as")
      by (auto simp add: \<open>bij p\<close> bij_inv_eq_iff)
    show ?thesis
      apply (simp only: Para)
      apply (simp add: stFormSymCorrespondence[OF a1] )
      by (metis "*" "**" applySym2State.simps(2) b1)
  qed
  then show "?P ?s" by blast 
qed

lemma reachSymLemma:
  assumes a1: "symPredList N fs"
    and a2: "symProtRules N rs" 
      (*a3:"s \<in> reachableSetUpTo (andList fs) rs i " and*)
    and a4: "p permutes {x. 1 \<le> x \<and> x \<le> N}"
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
      have c7:"(applySym2Rule p r) \<in> rs"
        using a2 a4 c2 symProtRules_def by blast

      have c8:"applySym2State p (trans1 (act r) s0) =
          trans1 (act (applySym2Rule p r)) (applySym2State p s0)"
        by (metis a4 act.simps applySym2Rule.simps rule.exhaust transSym)

      have c9:"trans1 (act (applySym2Rule p r)) (applySym2State p s0) \<in>  reachableSetUpTo (andList fs) rs (Suc n)"
        using c3 c6 c7 by auto
      have "applySym2State p s \<in> reachableSetUpTo (andList fs) rs (Suc n)"
        using c2 c8 c9 by auto  
    }
    ultimately show "applySym2State p s \<in> reachableSetUpTo (andList fs) rs (Suc n)"
      by blast
  qed
qed
qed

lemma SymLemma:
  assumes a1: "symPredList N fs"
    and a2: "symProtRules N rs"
    and a3: "\<forall>s i. s \<in> reachableSetUpTo (andList fs) rs i \<longrightarrow> formEval f s"
    and a4: "p permutes {x. 1 \<le> x \<and> x \<le> N}"
  shows
    "\<forall>s i. s \<in> reachableSetUpTo (andList fs) rs i \<longrightarrow> formEval (applySym2Form p f) s" (is "?P i")
proof ((rule allI)+,rule impI)
  fix s i
  assume b1:"s \<in> reachableSetUpTo (andList fs) rs i "
  show  "formEval (applySym2Form p f) s "
  proof -
    have c1:"s= applySym2State ( p) (applySym2State (inv p) s)"
      using a4 permutes_bij by fastforce

    have c2:"(inv p) permutes {x. 1\<le> x & x \<le> N}"
      using a4 permutes_inv by auto
      
    have c3:"(applySym2State (inv p) s) \<in> reachableSetUpTo (andList fs) rs i"
      using a1 a2 b1 c2 reachSymLemma by blast

    have c4:"formEval f (applySym2State (inv p) s)"
      using a3 c3 by blast
    show    "formEval (applySym2Form p f) s "
      by (metis a4 c1 c4 stFormSymCorrespondence)
  qed
qed

text\<open>$\mathsf{substExp}~asgn~e$ ($\mathsf{substForm}~asgn~f$)
  have applySym2State p s \<in> reachableSetUpTo (andList fs) rs (Suc n)"
        by (simp add: c3)
 denotes the expression $e$ (formula $f$) in which the occurrence of variable
  $x_i$ is replaced by $e_i$.*cartouche\<close>

definition substExpByStatement :: "expType \<Rightarrow> statement \<Rightarrow> expType" where [simp]:
  "substExpByStatement e S \<equiv> substExp e (statement2Assigns S)" 

definition substFormByStatement :: "formula \<Rightarrow> statement \<Rightarrow> formula" where [simp]:
  "substFormByStatement f S \<equiv> substForm f (statement2Assigns S)" 


text{*A statement $S$ can be transformed into an assignment to some variables
 $x_i$,  which is formalized by $\mathsf{statement2Assigns}~ S$.  
we use substExpByStatement e S and  substFormByStatement f S to denote the 
formula transformed from $f$  by substituting each $x_i$ with $e_i$. 
Furthermore, substFormByStatement f S  can be regarded as the weakest 
precondition of formula $f$ w.r.t. statement $S$. As Hoare logics specifies, *}


lemma preCondOnExp:  
  "expEval (substExpByStatement e S) s = expEval e (trans S s) \<and>
   formEval (substFormByStatement f S) s = formEval f (trans S s)"
  (is "?LHS e S = ?RHS e S \<and> ?LHS1 f S = ?RHS1 f S")
proof (induct_tac e and f)
  fix v
  let ?e="(IVar v)"
  show  "?LHS ?e S=?RHS ?e S"
  by (simp add: lemmaOnValOf)      
next 
  fix n
  let ?e="(Const n)"
  show "?LHS ?e S=?RHS ?e S"
    by simp
next
  fix f e1 e2
  assume a1:" ( ?LHS1 f S=?RHS1 f S)" and
  a2:"?LHS e1 S=?RHS e1 S" and a3:"?LHS e2 S=?RHS e2 S"
  let ?e="iteForm f e1 e2"
  show "?LHS ?e S=?RHS ?e S"
  using a1 a2 a3 by auto
next
  fix e1 e2
  assume a1:"?LHS e1 S=?RHS e1 S" and a2:"?LHS e2 S=?RHS e2 S"
  let ?f="eqn e1 e2"
  show "( ?LHS1 ?f S=?RHS1 ?f S)"
   using a1 a2 by auto 
next
  fix f1 f2
  assume a1:" ( ?LHS1 f1 S=?RHS1 f1 S)" and  a2:" ( ?LHS1 f2 S=?RHS1 f2 S)"
  let ?f="andForm f1 f2"
  show "( ?LHS1 ?f S=?RHS1 ?f S)"
   using a1 a2 by auto  
next
  fix f1
  assume a1:" ( ?LHS1 f1 S=?RHS1 f1 S)"
  let ?f="neg f1"
  show "( ?LHS1 ?f S=?RHS1 ?f S)"
   using a1 by auto
next   
  fix f1 f2
  assume a1:" ( ?LHS1 f1 S=?RHS1 f1 S)" and  a2:" ( ?LHS1 f2 S=?RHS1 f2 S)"
  let ?f="implyForm f1 f2"
  show "( ?LHS1 ?f S=?RHS1 ?f S)"
  using a1 a2 by auto
next
  fix f1 f2
  assume a1:" ( ?LHS1 f1 S=?RHS1 f1 S)" and  a2:" ( ?LHS1 f2 S=?RHS1 f2 S)"
  let ?f="orForm f1 f2"
  show "( ?LHS1 ?f S=?RHS1 ?f S)"
  using a1 a2 by auto
next
  let ?f="chaos"
  show "( ?LHS1 ?f S=?RHS1 ?f S)"
  by auto
qed (auto)


section \<open>Miscellaneous definitions and lemmas\<close>

text \<open>Variables of a variable, an expression, a formula, and a statement is defined by
varsOfVar, varOfExp, varOfForm and varOfSent respectively\<close>

definition varsOfVar :: "varType \<Rightarrow> varType set" where [simp]:
  "varsOfVar x = set [x]" 

primrec varOfExp :: "expType \<Rightarrow> varType set" and
  varOfForm :: "formula \<Rightarrow> varType set"
  where
  "varOfExp  (IVar v)  = varsOfVar v" |
  "varOfExp  (Const j) = set []" |
  "varOfExp  (iteForm f e1 e2) = varOfForm f \<union> varOfExp e1 \<union> varOfExp  e2" |

  "varOfForm (eqn e1 e2) = varOfExp e1 \<union> varOfExp  e2" |
  "varOfForm (andForm f1 f2) = varOfForm f1 \<union> varOfForm f2" |
  "varOfForm (neg f1) = varOfForm f1" |
  "varOfForm (orForm f1 f2) = varOfForm f1 \<union> varOfForm f2" |
  "varOfForm (implyForm f1 f2) = varOfForm f1 \<union> varOfForm f2" |
  "varOfForm (chaos) = {}"

primrec varOfSent :: "statement \<Rightarrow> varType set" where
  "varOfSent (assign a) = varsOfVar (fst a)" |
  "varOfSent skip = {}" |
  "varOfSent (parallel a sent2) = varsOfVar (fst a) \<union> varOfSent sent2"

primrec varOfFormList :: "formula list \<Rightarrow> varType set" where
  "varOfFormList [] = {}" |
  "varOfFormList (f#fs) = varOfForm f \<union> varOfFormList fs"

lemma varsOfSent1:
  "varOfSent S = set (map fst (statement2Assigns S))"
  by (induct_tac S, auto)

primrec down :: "nat \<Rightarrow> nat list" where
  "down 0 = [0]" |
  "down (Suc n) = Suc n # down n"

lemma simpDown: "down 5 = [5,4,3,2,1,0]"
  by (simp add: eval_nat_numeral(2) eval_nat_numeral(3))

lemma downNIsNotEmpty:
  "\<exists>j xs. down N = j#xs" (is "?P N")
  by (induct_tac N, auto)


text \<open>Definitions and lemmas on forallForm formula constructor\<close>

lemma forall1:
  "\<forall>i. i \<le> N \<longrightarrow> formEval (forallForm (down N) pf) s \<longrightarrow> formEval (pf i) s" (is "?P N")  
proof (induct_tac N)
  show "?P 0"
    by simp
next
  fix N
  assume b1: "?P N"
  show "?P (Suc N)"
  proof (case_tac "N = 0")
    assume c1:"N=0"
    show "?P  (Suc N)"
      by (cut_tac c1, auto,case_tac "i=0", auto,case_tac "i=1",auto)
  next
    assume c1:"N\<noteq>0"
    have "0<N " 
      by(cut_tac c1, arith)
   then have c2:"\<exists> N'. down (Suc N)=(Suc N)#N#down N'"
     by (metis down.simps(2) gr0_conv_Suc)
   then obtain N' where c2:"down (Suc N)=(Suc N)#N#down N'"
     by blast
   then have c3:"(N#down N')=down N"
     by simp
   show "?P  (Suc N)"      
   proof(rule allI,(rule impI)+,cut_tac c2,simp)
     fix i
     assume d1:"i\<le> Suc N" and d2:" formEval (pf (Suc N)) s \<and> formEval (forallForm (N # down N') pf) s"
     have "i=Suc N \<or> i<Suc N" 
       by (cut_tac d1, arith)
     moreover
     {assume e1:"i=Suc N"
       have " formEval (pf i) s"
         by (metis (lifting) d2 e1)
     }
     moreover
     {assume e1:"i<Suc N"           
       have " formEval (pf i) s"
         by (metis b1 c3 d1 d2 le_Suc_eq)
     }
     ultimately show "formEval (pf i) s"
       by blast
   qed
 qed
qed

lemma forall2Aux:
  "(\<forall>i. i \<le> N \<longrightarrow> formEval (pf i) s) \<longrightarrow> formEval (forallForm (down N) pf) s" (is "?P N")  
proof (induct_tac N)
  show "?P 0"
    by simp
  next
    fix N
    assume b0:"?P N"
    show "?P  (Suc N)"
    proof( rule impI)
      assume b1:"(\<forall> i. i \<le> (Suc N) \<longrightarrow>formEval (pf i) s)"
      have b2:"formEval (pf (Suc N)) s"
        by (simp add: b1)
       have b20:"(\<forall> i. i \<le> ( N) \<longrightarrow>formEval (pf i) s)"
        by (simp add: b1)
      have b3:"formEval (forallForm (down N) pf ) s"
        using b0 b20 by blast  
      with b2 show "formEval (forallForm (down (Suc N)) pf ) s"
        by (metis down.simps(2) downNIsNotEmpty evalAnd moreAllForm)
    qed   
  qed     

lemma forall2:
  "\<forall>i. i \<le> N \<longrightarrow> formEval (pf i) s \<Longrightarrow> formEval (forallForm (down N) pf) s"
  by (simp add: forall2Aux)

lemma forallLemma [simp,intro]:
  assumes a1: "i \<le> N"
    and a2: "formEval (forallForm (down N) pf) s"
  shows "formEval (pf i) s"
  using a1 a2 forall1 less_imp_le by blast

lemma forallLemma1:
  assumes a1: "i \<le> N"
    and a2: "formEval (forallForm (down N) pf) s"
    and a3: "formEval (pf i) s \<longrightarrow> A"
  shows "A"
  using a1 a2 a3 by blast

lemma forallMono[intro,simp]:
  assumes a1: "formEval (forallForm (down N) f) s"
    and a2: "N' < N"
  shows "formEval (forallForm (down N') f) s"
proof (rule forall2)
  show "\<forall>i. i \<le> N' \<longrightarrow> formEval (f i) s"
    by (meson Suc_leI a1 a2 forall1 le_SucI le_trans) 
qed  

subsection \<open>Lemmas on varsOf\<close>

lemma varsOnCat[simp]:
  "varOfSent (cat S1 S2) = varOfSent S1 \<union> varOfSent S2"
  by (induct_tac S1; simp)

lemma forallVars:
  assumes a1: "\<forall>i. varOfSent (paraForm i) \<inter> varSet = {}"
  shows "varOfSent (forallSent (down N) paraForm) \<inter> varSet = {}"
proof (induct_tac N)
  show "varOfSent (forallSent (down 0) paraForm) \<inter> varSet = {}"
    by (cut_tac a1,force) 
  next
    fix n
    assume b1:"varOfSent (forallSent (down n) paraForm) \<inter> varSet = {}"
    have " (varOfSent (forallSent (down (Suc n)) paraForm) )  =
      (varOfSent ( paraForm (Suc n)) ) \<union>
      (varOfSent (forallSent (down  n ) paraForm) )"
      by (metis (hide_lams, no_types) add_0_right moreSent down.simps(1) down.simps(2) nat.exhaust varsOnCat)
      then show "  varOfSent (forallSent (down (Suc n)) paraForm) \<inter> varSet = {}"
      apply(-,cut_tac a1,simp )
      by (metis (lifting) Int_Un_distrib2 Un_empty_left b1) 
  qed

lemma forallVars1[simp,intro!]:
  assumes a1: "\<forall>i. v \<notin> varOfSent (paraForm i)"
  shows "v \<notin> varOfSent (forallSent (down N) paraForm)" (is "?P N")
proof(induct_tac N)
  show "?P 0"
    by (cut_tac a1,force) 
  next
    fix n
    assume b1:"?P n"
    have " (varOfSent (forallSent (down (Suc n)) paraForm) )  =
      (varOfSent ( paraForm (Suc n)) ) \<union>
      (varOfSent (forallSent (down  n ) paraForm) )"
      by (metis (hide_lams, no_types) add_0_right moreSent down.simps(1) down.simps(2) nat.exhaust varsOnCat)
      then show "?P (Suc n) "
      apply(-,cut_tac a1,simp )
      by (metis (lifting) b1)
  qed
      
lemma varsOfForallSentIn[simp]:
  "i \<le> N \<longrightarrow> v \<in> varOfSent (paraForm i) \<longrightarrow> v \<in> varOfSent (forallSent (down N) paraForm)"
  (is "?P N")
proof (induct_tac N)
  show "?P 0"
   by auto
next
  fix N
  assume a1:"?P N" 
  show "?P (Suc N)"
  proof (rule impI)+
    assume b0:"i \<le> Suc N" and b1:"  v \<in> varOfSent (paraForm i)"  
    have b2:"  varOfSent  (forallSent (down (Suc N)) paraForm) = varOfSent (paraForm (Suc N)) \<union>   varOfSent (forallSent (down N) paraForm)"
     by (metis down.simps(2) downNIsNotEmpty moreSent varsOnCat) 
     have "i \<le> N | i=Suc N" by(cut_tac b0,auto)
    moreover
    {assume c1:"i \<le> N"
     have c2:" v \<in>varOfSent (forallSent (down N) paraForm)" 
     apply(cut_tac c1 b1 a1,auto) done
     then have "v \<in> varOfSent (forallSent (down (Suc N)) paraForm)" by(cut_tac c1 c2 b2,auto)
     }
     moreover
    {assume c1:"i =Suc N"
     from c1  have "v \<in> varOfSent (forallSent (down (Suc N)) paraForm)" by(cut_tac c1 b1 b2,auto) 
     }
    ultimately show "v \<in> varOfSent (forallSent (down (Suc N)) paraForm)" by blast
  qed
qed

lemma varsOfNot [simp,dest!]:
  "v \<notin> set (map fst (statement2Assigns S)) \<Longrightarrow>
   v \<in> set (map fst (statement2Assigns (cat S S'))) \<longleftrightarrow> v \<in> set (map fst (statement2Assigns S'))"
  by (metis Un_iff varsOfSent1 varsOnCat)

lemma ForallSentForm [simp]:
  "statement2Assigns (forallSent (down N) (\<lambda>i. assign (Para n i, e' i))) =
   map (\<lambda>i. (Para n i, e' i)) (down N)" (is "?P N")
proof (induct_tac N)
  show "?P 0" by simp
next
  fix N
  assume b1:"?P N"
  show "?P (Suc N )"
  proof (cut_tac b1, simp)
    have b2:"\<exists>j xs. down N = j#xs"
      by (metis downNIsNotEmpty) 
  then obtain j xs where b2:"down N=j#xs" by blast
  show "statement2Assigns (forallSent (Suc N # down N) (\<lambda>i. assign (Para n i, e' i))) = 
        (Para n (Suc N), e' (Suc N)) # map (\<lambda>i. (Para n i, e' i)) (down N)"
    by (cut_tac b1 b2, simp)
  qed
qed

subsection \<open>More lemmas on valOf operator\<close>

lemma valOfLemma [simp]:
  "i \<le> N \<longrightarrow> valOf (map (\<lambda>i. (Para v i, e i)) (down N)) (Para v i) = e i"
  by (induct_tac N, auto)

lemma valOfLemma2Aux [simp]:
  "var' \<notin> set (map fst xs) \<longrightarrow> valOf xs var' = IVar var'"
  by (induct_tac xs, auto)

lemma valOfLemma2 [simp,intro]:
  "var' \<notin> set (map fst xs) \<Longrightarrow> valOf xs var' = IVar var'"
  by (metis (lifting) valOfLemma2Aux)

lemma valOfLemma3 [simp]:
  "\<forall>i. var' \<noteq> Para v i \<Longrightarrow> valOf (map (\<lambda>i. (Para v i, e i)) (down N)) var' = IVar var'"
  apply (rule valOfLemma2)
  by (induction N, auto)

lemma valOfLemma4Aux:
  "v \<notin> set (map fst (statement2Assigns S)) \<longrightarrow>
   valOf (statement2Assigns (cat S S')) v = valOf (statement2Assigns S') v"
  by (induct_tac S, auto)

lemma valOfLemma4 [simp,intro]:
  "v \<notin> set (map fst (statement2Assigns S)) \<Longrightarrow>
   valOf (statement2Assigns (cat S S')) v = valOf (statement2Assigns S') v"
  by (metis valOfLemma4Aux)

lemma valOfLemma5Aux:
  "valOf (statement2Assigns S) v = IVar v \<and> valOf (statement2Assigns S') v = IVar v \<longrightarrow>
   valOf (statement2Assigns (cat S S')) v = IVar v"
  by (induct_tac S, auto)

lemma valOfLemma5 [simp,intro]:
  "valOf (statement2Assigns S) v = IVar v \<and> valOf (statement2Assigns S') v = IVar v \<Longrightarrow>
   valOf (statement2Assigns (cat S S')) v = IVar v"
  by (metis valOfLemma5Aux)
  
lemma valOfLemma6Aux:
  "valOf (statement2Assigns S) v = IVar v \<and> valOf (statement2Assigns S') v = IVar v \<longrightarrow>
   valOf (statement2Assigns (cat S S')) v = IVar v"
  by (induct_tac S, auto)

lemma valOfLemma7Aux:
  "v \<notin> varOfSent S \<longrightarrow> valOf (statement2Assigns (cat S S')) v = valOf (statement2Assigns S') v"
  by (induct_tac S, auto)

lemma valOfLemma7 [simp,intro]:
  "v \<notin> varOfSent S \<Longrightarrow> valOf (statement2Assigns (cat S S')) v = valOf (statement2Assigns S') v"
  by (metis valOfLemma7Aux)

lemma valOfLemma8Aux:
  "v \<in> varOfSent S \<longrightarrow> valOf (statement2Assigns (cat S S')) v = valOf (statement2Assigns S) v"
  by (induct_tac S, auto)

lemma valOfLemma8A [simp,intro]:
  "v \<in> varOfSent S \<Longrightarrow> valOf (statement2Assigns (cat S S')) v = valOf (statement2Assigns S) v"
  by (metis valOfLemma8Aux)

lemma noEffectValOfStatementAux [intro]:
  "v \<notin> varOfSent S \<longrightarrow> valOf (statement2Assigns S) v = IVar v" (is "?P N") 
  by (induct_tac S, auto)
 
lemma noEffectValOfStatement [simp,intro]:
  assumes "v \<notin> varOfSent S"
  shows "valOf (statement2Assigns S) v = IVar v" (is "?P N")
  by (metis assms valOfLemma2Aux varsOfSent1) 

lemma noEffectValOfForallStatementAux [intro]:
  "(\<forall>i. v \<notin> varOfSent (ps i)) \<longrightarrow> valOf (statement2Assigns (forallSent (down N) ps)) v = IVar v"
  (is "?P N")
proof(induct_tac N)
  show "?P 0"
    by simp
next
  fix N
  assume b1:"?P N"
  show "?P (Suc N)"
  proof(rule impI)
    assume c1:" \<forall>i. v \<notin> varOfSent (ps i)"
    show "valOf (statement2Assigns (forallSent (down (Suc N)) ps)) v = IVar v"
    proof(rule noEffectValOfStatement)
      have "   varOfSent (forallSent (down (Suc N)) ps) \<inter>{v} = {}"  thm forallVars
      proof(rule  forallVars,cut_tac c1,auto)qed
      then show   " v \<notin> varOfSent (forallSent (down (Suc N)) ps)"
      by (metis c1 forallVars1) 
    qed
  qed 
qed

lemma valOfLemma9 [intro,simp]:
  "valOf (statement2Assigns (cat St skip)) v = valOf (statement2Assigns St) v" (is "?P St") 
  by (induct_tac St, auto)

text \<open>Definitions and lemmas on andList formula constructor\<close>

lemma andList2Aux:
  "formEval (neg frm) s \<longrightarrow> frm \<in> set frms \<longrightarrow> formEval (neg (andList frms)) s"
  by (induct_tac frms, auto)

lemma andList2:
  "formEval (neg frm) s \<Longrightarrow> frm \<in> set frms \<Longrightarrow> formEval (neg (andList frms)) s"
  by (metis andList2Aux)
 
lemma andList1Aux:
  "formEval (andList frms) s  \<longrightarrow> frm \<in> set frms \<longrightarrow> formEval frm s "
  by (induct_tac frms,auto)
   
lemma andList1:
  "formEval (andList frms) s \<Longrightarrow> frm \<in> set frms \<Longrightarrow> formEval frm s " 
  by (metis andList1Aux)

lemma resAux1:
  assumes b: "formEval frm s" and c: "formEval (neg (andList (frm#frms))) s"
  shows "formEval (neg (andList frms)) s"
  apply (cut_tac b c) by auto

(*lemma andListMono[simp,intro]: 
  " (\<forall> inv. inv \<in>set invs \<longrightarrow>(\<exists>inv'. inv'\<in>set invs'\<and> (formEval inv' s \<longrightarrow> formEval inv s)))\<longrightarrow>
  formEval (andList invs') s \<longrightarrow> formEval (andList invs) s" (is "?P invs invs'")
proof(induct_tac invs,simp)
  fix a list
  assume a1:" ?P list invs'"
  show "?P (a#list) invs'" (is "?P1 (a#list) invs' \<longrightarrow> ?P2 invs'\<longrightarrow>?P3 (a#list)")
  proof( (rule impI)+)
    assume b1:"?P1 (a#list) invs'" and b2:"?P2 invs'"
    have b3:"\<exists>inv'. inv'\<in>set invs'\<and> (formEval inv' s \<longrightarrow> formEval a s)"
      by (simp add: b1)
    then obtain inv' where b3:"inv'\<in>set invs'\<and> (formEval inv' s \<longrightarrow> formEval a s)"
      by blast
    have b4:"formEval inv' s"
    proof(rule_tac ?frms="invs'" in andList1) 
      show "formEval (andList invs') s"  
        by(cut_tac b2,simp)
    next
      show "inv' \<in> set invs'" by(cut_tac b3,blast)
    qed

    have b5:"formEval (andList list) s" sorry
    with b3 show "?P3 (a#list)"
      by (simp add: b4) 
  qed
qed*)


text \<open>If $asgns$ does not assign any variable in $E$ to any value, then
evaluation of $E$ at the state $s$ is the same as that of $E$ at the state
$transAux~ asgns~ s$\<close>
lemma noEffectOnExpAux: 
  "(\<forall>s. varOfExp E \<inter> set (map fst asgns) = {} \<longrightarrow> expEval E s = expEval E (transAux asgns s)) \<and>
   (\<forall>s. varOfForm f \<inter> set (map fst asgns) = {} \<longrightarrow> formEval f s = formEval f (transAux asgns s))"
  (is "(\<forall>s. ?P asgns s E) \<and> (\<forall>s. ?Q asgns s f)")
proof (induct_tac E and f)
  fix varType
  let ?E = "IVar varType"
  show "(\<forall>s. ?P asgns s ?E)" (is "\<forall>s. ?R s asgns")
  proof(rule allI)
  fix s
  show "?R s asgns"
  proof (induct_tac asgns)
    show "?R s []" by simp
  next 
    fix a asgns  
    assume a1:"?R s asgns"
    show "?R s (a#asgns)"    
    proof
      assume c1: "varOfExp (?E) \<inter> set (map fst (a # asgns)) = {}"
      have d1: "\<exists>v val0. a=(v,val0)"
        by auto 
      then obtain var val0 where d2:"a=(var,val0)"
        by blast
      have f1: "expEval ?E s = expEval ?E (transAux ( asgns) s)"
        apply (cut_tac a1 c1)
        by auto
      have f2: "expEval ?E (transAux (a # asgns) s)= expEval ?E (transAux ( asgns) s)"
        by (cut_tac a1 c1,simp)
      show "expEval ?E s = expEval ?E (transAux (a # asgns) s)"
        by (cut_tac f1 f2, simp)
     qed
   qed
  qed
next
  fix frm e1 e2 
   let ?E="iteForm frm e1 e2"
  assume a1:"( \<forall>  s. ?Q asgns s frm)" and a2:"(\<forall>  s. ?P asgns s e1)" and a3:"(\<forall>  s. ?P asgns s e2)"
  show "(\<forall>  s. ?P asgns s ?E)" (is "\<forall>s. ?R s asgns")  
  proof(rule allI,rule impI)
  fix s
   assume c1:" varOfExp (?E) \<inter> set (map fst ( asgns)) = {}"
   show "expEval (iteForm frm e1 e2) s = expEval (iteForm frm e1 e2) (transAux asgns s)"
   apply(cut_tac a1 a2 a3 c1)
     by auto
   qed  
next
  fix e1 e2
  let ?f="eqn e1 e2" 
  assume a1:"(\<forall>  s. ?P asgns s e1)" and a2:"(\<forall>  s. ?P asgns s e2)"  
  show "(\<forall>  s. ?Q asgns s ?f)" (is "\<forall>s. ?R s asgns")  
    by (rule allI,rule impI,cut_tac a1 a2,auto) 
next
  fix f1 f2
  let ?f="andForm f1 f2"
  assume a1:"( \<forall>  s. ?Q asgns s f1)" and  a2:"( \<forall>  s. ?Q asgns s f2)"
  show "( \<forall>  s. ?Q asgns s ?f)"
    by(rule allI,rule impI,cut_tac a1 a2,auto) 
next
  fix f1 
  let ?f="neg f1 "
  assume a1:"( \<forall>  s. ?Q asgns s f1)"
  show "( \<forall>  s. ?Q asgns s ?f)"
    by (rule allI, rule impI, cut_tac a1, auto)
next
  fix f1 f2
  let ?f="orForm f1 f2"
  assume a1:"( \<forall>  s. ?Q asgns s f1)" and  a2:"( \<forall>  s. ?Q asgns s f2)"
  show "( \<forall>  s. ?Q asgns s ?f)"
    by (rule allI,rule impI,cut_tac a1 a2,auto)
next
  fix f1 f2
  let ?f="implyForm f1 f2"
  assume a1:"( \<forall>  s. ?Q asgns s f1)" and  a2:"( \<forall>  s. ?Q asgns s f2)"
  show "( \<forall>  s. ?Q asgns s ?f)"
    by (rule allI,rule impI,cut_tac a1 a2,auto)
qed (auto)
 

lemma noEffect:
  "(\<forall>s. varOfExp E \<inter> varOfSent S = {} \<longrightarrow> expEval E s = expEval E (trans S s)) \<and> 
   (\<forall>s. varOfForm f \<inter> varOfSent S = {} \<longrightarrow> formEval f s = formEval f (trans S s))"
  apply(cut_tac f="f" and E="E" and asgns="statement2Assigns S" in noEffectOnExpAux) 
  apply(unfold trans_def)
  apply(cut_tac S="S" in varsOfSent1)
  apply metis
  done

lemma noEffectOnExp: 
  assumes a1: "varOfExp E \<inter> varOfSent S = {}"
  shows "expEval E s = expEval E (trans S s)"
  by (metis assms noEffect) 

lemma noEffectOnFormula: 
  assumes a1: "varOfForm f \<inter> varOfSent S = {}"
  shows "formEval f s = formEval f (trans S s)"
  by (metis assms noEffect)


text \<open>If variables occurring in an expression e (or a formula f) is disjoint
  with that in a statement S, then substExpByStatement e S (or substFormByStatement f S)
  is the same as e (or f)\<close>

lemma noEffectSubstAux:
  "(varOfExp e \<inter> varOfSent S = {} \<longrightarrow> substExpByStatement e S = e) \<and>
   (varOfForm f \<inter> varOfSent S = {} \<longrightarrow> substFormByStatement f S = f)"
  (is "((?condOne e S \<longrightarrow> ?LHS e S = ?RHS e S) \<and> (?condOnf f S \<longrightarrow> ?LHS1 f S = ?RHS1 f S))")
proof(induct_tac e and f)
    fix v
    let ?e="(IVar v)"
    show  "?condOne ?e S\<longrightarrow>?LHS ?e S=?RHS ?e S"
    proof(induct_tac S)
      let ?S="skip"
      show "?condOne ?e ?S \<longrightarrow>?LHS ?e ?S=?RHS ?e ?S"
        by auto
    next
      fix prod
      let ?S="assign prod"
      show "?condOne ?e ?S \<longrightarrow>?LHS ?e ?S=?RHS ?e ?S"
        by (unfold substExpByStatement_def trans_def, auto)
  next
     fix prod S
     let ?S="parallel prod S"
     assume b1:"?condOne ?e S \<longrightarrow>?LHS ?e S=?RHS ?e S"
     show "?condOne ?e ?S \<longrightarrow> ?LHS ?e ?S=?RHS ?e ?S"
     proof (unfold substExpByStatement_def trans_def, case_tac "fst prod =v", force)
     assume d1:"fst prod \<noteq> v"
     show "varOfExp (IVar v) \<inter> varOfSent (parallel prod S) = {} \<longrightarrow> (substExp (IVar v) (statement2Assigns (parallel prod S))) =
             (IVar v)"
       by (cut_tac d1,simp)
    qed 
  qed 
next 
  fix n
  let ?e="(Const n)"
  show  "?condOne ?e S \<longrightarrow>?LHS ?e S=?RHS ?e S"
    by simp
next
  fix f e1 e2
  assume a1:" (?condOnf f S \<longrightarrow> ?LHS1 f S=?RHS1 f S)" and
  a2:"?condOne e1 S \<longrightarrow>?LHS e1 S=?RHS e1 S" and a3:"?condOne e2 S \<longrightarrow>?LHS e2 S=?RHS e2 S"
  let ?e="iteForm f e1 e2"
  show "?condOne ?e S \<longrightarrow>?LHS ?e S=?RHS ?e S"  
  proof(rule impI)
  assume b1:"?condOne ?e S"
  have c1:"?condOnf f S "
  apply(cut_tac b1,simp)
  by (metis bot_eq_sup_iff inf_sup_distrib2)
  have c2:"?condOne e1 S "
   apply(cut_tac b1,simp)
   by (metis c1 inf_bot_right inf_sup_absorb inf_sup_distrib2 sup_bot.left_neutral)
  have c3:"?condOne e2 S "
   apply(cut_tac b1,simp)
   by (metis c1 inf_bot_right inf_sup_absorb inf_sup_distrib2 sup_bot.left_neutral)
 with c1 c2 c3 a1 a2 a3
 show "?LHS ?e S=?RHS ?e S"
 by (metis substExpByStatement_def substExpite substFormByStatement_def)  
 qed 
next
  fix e1 e2
  assume a1:"?condOne e1 S \<longrightarrow>?LHS e1 S=?RHS e1 S" and a2:"?condOne e2 S \<longrightarrow>?LHS e2 S=?RHS e2 S"
  let ?f="eqn e1 e2"
  show "(?condOnf ?f S \<longrightarrow> ?LHS1 ?f S=?RHS1 ?f S)"
  proof(rule impI)
    assume b1:"?condOnf ?f S"
    have c1:"?condOne e1 S"
      apply(cut_tac b1,simp)
      by (metis Int_Un_distrib2 sup_eq_bot_iff)
    have c2:"?condOne e2 S"
      apply(cut_tac b1,simp)
      by (metis Int_Un_distrib2 sup_eq_bot_iff)
    with a1 a2 c1 c2 
    show "?LHS1 ?f S=?RHS1 ?f S"
      by simp
  qed
next
  fix f1 f2
  assume a1:" (?condOnf f1 S \<longrightarrow> ?LHS1 f1 S=?RHS1 f1 S)" and  a2:" (?condOnf f2 S \<longrightarrow> ?LHS1 f2 S=?RHS1 f2 S)"
  let ?f="andForm f1 f2"
  show "(?condOnf ?f S \<longrightarrow> ?LHS1 ?f S=?RHS1 ?f S)"
  proof(rule impI)
    assume b1:"?condOnf ?f S"
    have c1:"?condOnf f1 S"
      apply(cut_tac b1,simp)
      by (metis Int_assoc inf_bot_right inf_sup_absorb)
    have c2:"?condOnf f2  S"
      apply(cut_tac b1,simp)
      by (metis Int_Un_distrib2 c1 sup_bot_left)
    with a1 a2 c1 c2 
    show "?LHS1 ?f S=?RHS1 ?f S"
      by auto
    qed
next
  fix f1
  assume a1:" (?condOnf f1 S \<longrightarrow> ?LHS1 f1 S=?RHS1 f1 S)"
  let ?f="neg f1"
  show "( ?condOnf ?f S \<longrightarrow>?LHS1 ?f S=?RHS1 ?f S)"
  proof(rule impI)
  assume b1:"?condOnf ?f S"
  have c1:"?condOnf f1 S"
  by(cut_tac b1,simp)
  
   with a1 c1
   show "?LHS1 ?f S=?RHS1 ?f S"
   by auto
qed
next   
  fix f1 f2
  assume a1:" (?condOnf f1 S \<longrightarrow> ?LHS1 f1 S=?RHS1 f1 S)" and  a2:" (?condOnf f2 S \<longrightarrow> ?LHS1 f2 S=?RHS1 f2 S)"
  let ?f="implyForm f1 f2"
  show "(?condOnf ?f S \<longrightarrow> ?LHS1 ?f S=?RHS1 ?f S)"
  proof(rule impI)
  assume b1:"?condOnf ?f S"
  have c1:"?condOnf f1 S"
  apply(cut_tac b1,simp)
  by (metis Int_assoc inf_bot_right inf_sup_absorb)
   have c2:"?condOnf f2  S"
  apply(cut_tac b1,simp)
  by (metis Int_Un_distrib2 c1 sup_bot_left)
  with a1 a2 c1 c2 
   show "?LHS1 ?f S=?RHS1 ?f S"
   by auto
qed
next
  let ?f="chaos"
  show "( ?condOnf ?f S \<longrightarrow> ?LHS1 ?f S=?RHS1 ?f S)"
  by auto
next
  next   
  fix f1 f2
  assume a1:" (?condOnf f1 S \<longrightarrow> ?LHS1 f1 S=?RHS1 f1 S)" and  a2:" (?condOnf f2 S \<longrightarrow> ?LHS1 f2 S=?RHS1 f2 S)"
  let ?f="orForm f1 f2"
  show "(?condOnf ?f S \<longrightarrow> ?LHS1 ?f S=?RHS1 ?f S)"
  proof(rule impI)
  assume b1:"?condOnf ?f S"
  have c1:"?condOnf f1 S"
  apply(cut_tac b1,simp)
  by (metis Int_assoc inf_bot_right inf_sup_absorb)
   have c2:"?condOnf f2  S"
  apply(cut_tac b1,simp)
  by (metis Int_Un_distrib2 c1 sup_bot_left)
  with a1 a2 c1 c2 
   show "?LHS1 ?f S=?RHS1 ?f S"
   by auto
  qed
qed (auto)

lemma noEffectSubstExp [intro!]:
  "varOfExp e \<inter> varOfSent S = {} \<Longrightarrow> substExpByStatement e S = e"
  by (metis noEffectSubstAux)

lemma noEffectSubstForm [intro!]:
  "varOfForm f \<inter> varOfSent S = {} \<Longrightarrow> substFormByStatement f S = f"
  by (metis noEffectSubstAux) 

lemma noEffectValOfForallStatement [simp,intro]:
  "\<forall>i. v \<notin> varOfSent (ps i) \<Longrightarrow> valOf (statement2Assigns (forallSent (down N) ps)) v = IVar v" 
  by (metis noEffectValOfForallStatementAux)
  
lemma noEffectValOfForallStatement1 [simp,intro]:
  "\<forall>i. v \<notin> varOfSent (ps i) \<Longrightarrow> expEval (valOf (statement2Assigns (forallSent (down N) ps)) v) s = s v"
  by auto

section \<open>On CMP theoretical foundation\<close>

primrec isGlobal :: "varType \<Rightarrow> bool" where
  "isGlobal (Ident v) = True" |
  "isGlobal (Para n i) = False"

primrec scalar2Nat :: "scalrValueType \<Rightarrow> nat" where
  "scalar2Nat (index n) = n"

definition state_sim_on3 :: "state \<Rightarrow> state \<Rightarrow> varType set \<Rightarrow> varType set \<Rightarrow> nat \<Rightarrow> bool" where [simp]:
  "state_sim_on3 s s' V V' N \<equiv>
    (\<forall>v. v \<in> V \<longrightarrow> s v = s' v) \<and>
    (\<forall>v. v \<in> V' \<longrightarrow> scalar2Nat (s v) \<le> N \<longrightarrow> s v = s' v)\<and>
    (\<forall>v. v \<in> V' \<longrightarrow> scalar2Nat (s v) > N \<longrightarrow> scalar2Nat (s' v) = N+1)"



definition abs1 :: "nat \<Rightarrow> state \<Rightarrow> state" where [simp]:
  "abs1 M s v \<equiv>
    if \<exists>vn i. v = Para vn i \<and> i > M
    then dontCare
    else if scalar2Nat (s v) > M
    then index (M + 1)
    else s v"

definition pred_sim_on :: "formula \<Rightarrow> formula \<Rightarrow> nat \<Rightarrow> bool" where [simp]:
  "pred_sim_on f1 f2 M \<equiv>
    \<forall>s. formEval f1 s \<longrightarrow> formEval f2 (abs1 M s)"



definition trans_sim_on1 :: "rule \<Rightarrow> rule \<Rightarrow> nat \<Rightarrow> bool" where [simp]:
  "trans_sim_on1 r1 r2 M \<equiv>
    \<forall>s. formEval (pre r1) s \<longrightarrow>
        formEval (pre r2) (abs1 M s) \<and>
        abs1 M (trans1 (act r1) s) = trans1 (act r2) (abs1 M s)"


definition protSim :: "formula \<Rightarrow> formula \<Rightarrow> rule set \<Rightarrow> rule set \<Rightarrow> nat \<Rightarrow> bool" where [simp]:
  "protSim I I1 rs rs1 M \<equiv>
    pred_sim_on I I1 M \<and>
    (\<forall>r. r \<in> rs \<longrightarrow> (\<exists>r'. r' \<in> rs1 \<and> trans_sim_on1 r r' M))"

(*definition protSim'::"formula \<Rightarrow> formula \<Rightarrow>rule set \<Rightarrow> rule set \<Rightarrow> nat \<Rightarrow>varType set\<Rightarrow>
  varType set \<Rightarrow> bool"  where [simp]:
  "protSim' I I1 rs rs1 M indV obV \<equiv>
   pred_sim_on I I1 indV M \<and>
   (\<forall>r. r \<in> rs\<longrightarrow>(\<exists> r'. r' \<in> rs1 \<and> trans_sim_on' r r'  obV))"*)

lemma sim3:
  assumes a1: "protSim I I' rs rs' M"
  (*and a2:"indV \<inter> obsV'={}"
  and a7:"\<forall>r' v. r' \<in>rs' \<longrightarrow> v \<in>varOfSent (act r')\<longrightarrow> v' \<in> indV \<union> obsV' "
  and a3:"\<forall>r v. r \<in>rs \<longrightarrow> v \<in>varOfForm (pre r)\<longrightarrow> v \<in> indV \<union> obsV' "
  and a4:"s \<in>reachableSetUpTo I rs i" *)
  (*and a5:"\<forall>s. formEval I s \<longrightarrow>formEval I' (abs obsV' indV M s)"*)
 (* and a6:"\<forall> s. formEval I' s \<longrightarrow> (\<forall>f'. f' \<in>F \<longrightarrow> formEval  f' s)   "
  and a7:"\<forall>s s'. formEval I s \<longrightarrow>  stSimOn (abs  obsV' indV M s) s' (obsV' \<union> indV )
   \<longrightarrow> formEval I' s'"*)
  shows "\<forall>s. s \<in> reachableSetUpTo I rs i \<longrightarrow> abs1 M s \<in> reachableSetUpTo I' rs' i"
  (is "\<forall>s. ?P s i \<longrightarrow>?Q s i")
  (*(\<exists>s'. s' \<in>reachableSetUpTo I' rs' i \<and> stSimOn (abs indV M s) s' (obsV' \<union> indV ) )*)
proof (induct_tac i)  
  show "\<forall>s. ?P s 0 \<longrightarrow> ?Q s 0"
  proof (rule allI,rule impI)
    fix s
    let ?s="abs1 M s"
    assume b1: "s \<in> reachableSetUpTo I rs 0"
    show "?Q s 0" 
    proof -
      have c1:"formEval I s"
        using b1 by auto
      show "?s \<in> reachableSetUpTo I' rs' 0"
        by (cut_tac c1 a1,simp)
    qed
  qed
next
  fix n
  assume b1:"\<forall>s. ?P s n \<longrightarrow>?Q s n"
  show "\<forall>s. ?P s (Suc n) \<longrightarrow>?Q s (Suc n)" 
  proof(rule allI, rule impI)
    fix s
    assume c1:" s \<in> reachableSetUpTo I rs (Suc n) "
    (*show "?Q s (Suc n)" *)
    from c1 have c2:" s \<in> reachableSetUpTo I rs ( n) | 
      (\<exists>s0 r. r \<in>rs \<and> formEval (pre r) s0 \<and> s=trans1 (act r) s0)" 
      by auto
    moreover
    {assume c2:"s \<in> reachableSetUpTo I rs ( n)"
      have c3:"?Q s n"
        using b1 c2 by blast 
      have "?Q s (Suc n)"
        using c3 by auto  
     }
     moreover
     {assume c2:" (\<exists>s0 r. s0 \<in> reachableSetUpTo I  rs n \<and> r \<in>rs \<and> formEval (pre r) s0 \<and> s=trans1 (act r) s0)"
       from c2 obtain s0 and r where 
          c3:"s0 \<in> reachableSetUpTo I  rs n \<and> r \<in>rs \<and> formEval (pre r) s0 \<and> s=trans1 (act r) s0" 
         by blast
        from b1 c3 have c4:"?Q s0 n" 
          by blast
        from c3 c4 a1 have c5:"\<exists>r2. r2 \<in> rs' \<and> formEval (pre r2) (abs1   M s0) 
           \<and> (abs1    M (trans1 (act r) s0)) = (trans1 (act r2) (abs1    M s0)) "
          
          by (meson protSim_def trans_sim_on1_def   )
        then obtain r2 where c5:" r2 \<in> rs' \<and> formEval (pre r2) (abs1  M s0) 
            \<and> (abs1   M (trans1 (act r) s0)) = trans1 (act r2) (abs1    M s0) "
          by blast

        have c6:"trans1 (act r2) (abs1   M s0) \<in> reachableSetUpTo I'  rs' (Suc n)"
          by (metis (mono_tags, lifting) Un_iff c4 c5 mem_Collect_eq reachableSetNext)
            
        have "?Q s (Suc n)"
          using c3 c5 c6 by auto
      }
      ultimately show "?Q s (Suc n)"
        using c1 by auto 
    qed
  qed

lemma simMeansInvHold:
  assumes a1: "protSim I I' rs rs' M"
  (*and a2:"indV \<inter> obsV'={}"
  and a7:"\<forall>r' v. r' \<in>rs' \<longrightarrow> v \<in>varOfSent (act r')\<longrightarrow> v' \<in> indV \<union> obsV' "
  and a3:"\<forall>r v. r \<in>rs \<longrightarrow> v \<in>varOfForm (pre r)\<longrightarrow> v \<in> indV \<union> obsV' "
  and a4:"s \<in>reachableSetUpTo I rs i" *)
  (*and a5:"\<forall>s. formEval I s \<longrightarrow>formEval I' (abs obsV' indV M s)"*)
 (* and a6:"\<forall> s. formEval I' s \<longrightarrow> (\<forall>f'. f' \<in>F \<longrightarrow> formEval  f' s)   "
  and a7:"\<forall>s s'. formEval I s \<longrightarrow>  stSimOn (abs  obsV' indV M s) s' (obsV' \<union> indV )
   \<longrightarrow> formEval I' s'"*)
  and a6: "\<forall>s. s \<in> reachableSetUpTo I' rs' i \<longrightarrow> formEval f s "
  and a7: "\<forall>s. s \<in> reachableSetUpTo I rs i \<longrightarrow> (formEval f s = formEval f (abs1 M s))"
  shows "\<forall>s. s \<in> reachableSetUpTo I rs i \<longrightarrow> formEval f s" 
  (is "\<forall>s. ?P s i \<longrightarrow>?Q s i")
  using a6 a7 local.a1 sim3 by blast

primrec strengthenForm :: "formula \<Rightarrow> formula \<Rightarrow> formula" where
  "strengthenForm (implyForm a c) g = 
    (if taut (implyForm g a) then c else chaos)" |
  "strengthenForm (andForm a c) g = chaos" |
  "strengthenForm (orForm a c) g = chaos" |
  "strengthenForm (eqn a c) g = chaos" |
  "strengthenForm (neg a) g = chaos" |
  "strengthenForm (chaos) g = chaos" | 
  "strengthenForm (dontCareForm) g = chaos"

primrec strengthenFormByForms :: "formula list \<Rightarrow> formula \<Rightarrow> formula"  where
  "strengthenFormByForms [] g = chaos" |
  "strengthenFormByForms (g#gs) f = andForm (strengthenForm g f) (strengthenFormByForms gs f)"
 
definition strengthenFormByFormSet :: "formula set \<Rightarrow> formula \<Rightarrow> formula set"  where
" strengthenFormByFormSet FS g \<equiv>
  {g'. \<exists>f. f \<in>FS \<and> g'=strengthenForm f g }"

definition strengthen :: "formula list \<Rightarrow> formula \<Rightarrow> formula" where [simp]:
  "strengthen fs f \<equiv> andForm f (strengthenFormByForms fs f)"

primrec leftEq :: "formula \<Rightarrow> expType" where
  "leftEq (eqn e1 e2) = e2"

primrec strengthenStm :: "formula \<Rightarrow> statement \<Rightarrow> statement" where
  "strengthenStm g skip = skip" |

  "strengthenStm g (assign a) =
    (if (\<exists>e1 e2 n i Id. g = eqn e1 e2 \<and> e1 = IVar (Para n i) \<and> e2 = IVar (Ident Id) \<and>
                        snd a = IVar (Para n i)) 
     then assign (fst a, leftEq g) 
     else assign a)" |

  "strengthenStm g (parallel a S) =
    (if (\<exists>e1 e2 n i Id. g = eqn e1 e2 \<and> e1 = IVar (Para n i) \<and> e2 = IVar (Ident Id) \<and>
                        snd a = IVar (Para n i))
     then parallel (fst a, leftEq g) (strengthenStm g S)
     else parallel a (strengthenStm g S))" 

primrec strengthenStmByForms :: "formula list \<Rightarrow> statement \<Rightarrow> statement" where
  "strengthenStmByForms [] S = S" |
  "strengthenStmByForms (g#gs) S = (strengthenStm g (strengthenStmByForms gs S))"

primrec strengthenR :: "formula list \<Rightarrow> rule \<Rightarrow> rule" where
  "strengthenR fs (guard g S) = 
    guard (strengthen fs g) (strengthenStmByForms fs S)"

lemma strengthenByForm:
  "formEval f s \<longrightarrow> formEval g s \<longrightarrow> formEval (strengthenForm g f) s"
  by (case_tac g, auto)

lemma strengthenByForms:
  "(\<forall>f. f \<in> set F \<longrightarrow> formEval f s) \<longrightarrow> formEval f s \<longrightarrow> formEval (strengthenFormByForms  F f) s"
  (is "?P F")
proof(induct_tac F)
  show "?P []"
    by auto
next
  fix a list
  assume b1:"?P list"
  show "?P (a#list)"
    by (simp add: b1 strengthenByForm)
qed

lemma strengthTransSimEn:
  assumes a2: "formEval f s"
  shows "(\<forall>f. f \<in> set S \<longrightarrow> formEval f s) \<longrightarrow> formEval (strengthen S f) s"
    (is "?P S")
proof (induct_tac S)
  show "?P []"
    by (simp add: a2)
next
  fix a list
  assume b1:"?P list"
  show "?P (a#list)"
    using assms evalAnd strengthenByForms strengthen_def by presburger
qed

lemma strengthTransSimEffect0:
  "formEval f s \<longrightarrow> trans1 (strengthenStm f Stm) s = trans1 Stm s"
  (is "?P f  Stm s")
proof (induct_tac Stm)
  show "?P f skip s" by auto
next
  fix a
  show "?P f (assign a) s"
    by (case_tac f, auto)
next
  fix a S
  assume a0:"?P f S s" 
  show "?P f (parallel a S) s"
    by (cut_tac a0,case_tac f,auto) 
qed

lemma strengthTransSimEffect:
  "(\<forall>f. f \<in> set S \<longrightarrow> formEval f s) \<longrightarrow> trans1 (strengthenStmByForms S Stm) s = trans1 Stm s"
  (is "?P S  Stm s")
proof (induct_tac S)
  show "?P [] Stm s" by auto
next
  fix a list
  assume a0:"?P (list) Stm s"
  show "?P (a#list) Stm s"
  proof(rule impI )
    assume a1:"\<forall>f. f \<in> set (a # list) \<longrightarrow> formEval f s"
    have a2:"trans1 (strengthenStmByForms list Stm) s=trans1 Stm s "
      by (simp add: a0 local.a1)
    have a3:"trans1 (strengthenStmByForms (a # list) Stm) s =trans1 (strengthenStmByForms list Stm) s"
      by (simp add: local.a1 strengthTransSimEffect0) 
      
    show "trans1 (strengthenStmByForms (a # list) Stm) s = trans1 Stm s "
      using a2 a3 by auto
      
    qed
 
qed

lemma strengthenProtSimProt:
  assumes a1:"\<forall>r. r \<in> rs \<longrightarrow>(\<exists> Ls . set Ls \<subseteq> set S \<and>  strengthenR Ls r \<in> rs')" and
  a2:"\<forall>i s f. s \<in>reachableSetUpTo I rs' i \<longrightarrow> f \<in>set S \<longrightarrow>formEval f s" 
shows "\<forall>s f. s \<in>reachableSetUpTo I rs i \<longrightarrow>
   f \<in>set S \<longrightarrow>(s \<in>reachableSetUpTo I rs' i \<and>formEval f s)" (is "?P i")
proof(induct_tac i)  
  show "?P 0"
    by (metis a2 reachableSet0)
next
  fix n
  assume b0:"?P n"
  show "?P (Suc n)"
  proof((rule allI)+,(rule impI)+)
    fix s f
    assume b1:"s \<in> reachableSetUpTo I rs (Suc n)" and
          b2:" f \<in> set S "
    have "s \<in> reachableSetUpTo I rs n |
        (\<exists>s0 r. r \<in>rs \<and>   s0 \<in>reachableSetUpTo I rs n\<and> formEval (pre r) s0 \<and> trans1 (act r) s0=s) "
      using b1 by auto
    moreover
    {assume b1:"s \<in> reachableSetUpTo I rs n "
      have "s \<in>reachableSetUpTo I rs' n \<and> formEval f s"
        using b0 b1 b2 by blast
    }
    moreover
    {assume c1:"(\<exists>s0 r. r \<in>rs \<and>   s0 \<in>reachableSetUpTo I rs n\<and> 
      formEval (pre r) s0 \<and> trans1 (act r) s0=s) "
      from c1 obtain s0 r where c1:"r \<in>rs \<and>   s0 \<in>reachableSetUpTo I rs n\<and> 
      formEval (pre r) s0 \<and> trans1 (act r) s0=s"
        by blast
      have c2:" (\<exists> Ls . set Ls \<subseteq> set S \<and>  strengthenR Ls r \<in> rs') "
        by (simp add: c1 local.a1)

      from c2 obtain Ls where c2:"set Ls \<subseteq> set S \<and>  strengthenR Ls r \<in> rs'"
        by blast
      from b0 c1 c2 have c3:"\<forall>f. f \<in> set Ls \<longrightarrow> formEval f s0"
        by auto
      have c4:"formEval (strengthenFormByForms  Ls (pre r)) s0"
        using c1 c3 strengthenByForms by blast

      
      have c5:"trans1 (strengthenStmByForms Ls (act r)) s0 = trans1 (act r) s0"
        using c3 strengthTransSimEffect by blast
      have c6:"trans1  (act (strengthenR Ls r)) s0 = trans1 (act r) s0"
        by (metis act.simps c5 rule.exhaust strengthenR.simps)
      have c7:"s0 \<in> reachableSetUpTo I rs' n"
        using b0 b2 c1 by blast
      have c8:"formEval (pre (strengthenR Ls r)) s0"
        by (metis c1 c4 evalAnd pre.simps rule.exhaust strengthenR.simps strengthen_def) 
        
      have c8:"trans1  (act (strengthenR Ls r)) s0 \<in> reachableSetUpTo I rs' (Suc n)"
        using c2 c7 c8 by auto

      
      have "s \<in>reachableSetUpTo I rs' (Suc n) \<and> formEval f s"
        using a2 b2 c1 c6 c8 by presburger
    }
    ultimately show "s \<in>reachableSetUpTo I rs' (Suc n) \<and> formEval f s"
      by auto 
  qed
qed


primrec absTransfConst::"nat \<Rightarrow> scalrValueType \<Rightarrow>scalrValueType " where [simp]:
" absTransfConst M (enum t n) = enum t n"
|"absTransfConst M (index n) = (if (n>M) then (index (M+1)) else index n)"
|"absTransfConst M (boolV b) =boolV b"
|"absTransfConst M dontCare = dontCare"

primrec absTransfVar::"nat \<Rightarrow>varType \<Rightarrow>varType" where 
"absTransfVar M (Ident n) =Ident n" |
"absTransfVar M (Para n i) =
  (if i>M then dontCareVar else (Para n i))" |
"absTransfVar M dontCareVar =dontCareVar"

primrec absTransfExp::"nat \<Rightarrow> expType \<Rightarrow>expType"  and
absTransfForm::"nat \<Rightarrow>formula \<Rightarrow>formula" where
"absTransfExp M (Const i) =Const ( absTransfConst M i)" |

"absTransfExp M (IVar v) =IVar ( absTransfVar M v)" |

"absTransfExp M (iteForm b e1 e2) = 
  (if (absTransfForm M b) = dontCareForm then dontCareExp
   else (iteForm b (absTransfExp M e1) (absTransfExp M e2)))"|

"absTransfForm M (eqn e1 e2) =
 (if (absTransfExp M e1) = dontCareExp | (absTransfExp M e2) = dontCareExp
  then dontCareForm 
  else (eqn (absTransfExp M e1) (absTransfExp M e2)))" |

"absTransfForm M (neg f) =
  (if (absTransfForm M f) = dontCareForm then dontCareForm else (neg (absTransfForm M f)))" |

"absTransfForm M (andForm f1 f2) =
  (if (absTransfForm M f1) = dontCareForm then  (absTransfForm M f2)
   else if (absTransfForm M f2) = dontCareForm then (absTransfForm M f1)
   else andForm (absTransfForm M f1) (absTransfForm M f2))" |

"absTransfForm M (orForm f1 f2) =
  (if (absTransfForm M f1) = dontCareForm then  (absTransfForm M f2)
   else if (absTransfForm M f2) = dontCareForm then (absTransfForm M f1)
   else orForm (absTransfForm M f1) (absTransfForm M f2))" |


"absTransfForm M (implyForm f1 f2) =
  (if (absTransfForm M f1) = dontCareForm then  (absTransfForm M f1)
   else if (absTransfForm M f2) = dontCareForm then neg (absTransfForm M f1)
   else implyForm (absTransfForm M f1) (absTransfForm M f2))" |

"absTransfForm M chaos= chaos" |

"absTransfForm M dontCareForm= dontCareForm" |

"absTransfExp M dontCareExp= dontCareExp"

primrec absTransfStatement:: "nat \<Rightarrow> statement \<Rightarrow> statement"  where
"absTransfStatement M skip =skip"|
"absTransfStatement M (assign as) = 
  (if absTransfVar M (fst as) = dontCareVar 
  then skip else (assign  ((fst as), (absTransfExp M (snd as)))))" |
"absTransfStatement M (parallel as S) =
  (if absTransfVar M (fst as) = dontCareVar 
  then (absTransfStatement M S)
  else parallel  ( ((fst as), (absTransfExp M (snd as)))) (absTransfStatement M S))"

primrec absTransfRule::" nat \<Rightarrow> rule \<Rightarrow> rule" where
"absTransfRule M (guard g a) =guard (absTransfForm M g) (absTransfStatement M a)"

definition indexedVar::"varType \<Rightarrow> bool" where [simp]:
"indexedVar v \<equiv> \<forall>s. \<exists> n. s v = index n"

(*lemma absRuleSim: 
  "trans_sim_on r1 (absTransfRule M r1)  
    ({v. \<exists>v0. v0 \<in>(varOfSent (act r)\<union> varOfForm (pre r))\<and>v=absTransfVar M v0 
       \<and> v\<noteq> dontCareVar \<and> indexedVar v }) M 
    ({v. \<exists>v0. v0 \<in>varOfSent (act r) \<and>v=absTransfVar M v0 \<and> v\<noteq> dontCareVar})"
*)
lemma agreeOnVars:
  shows "((\<forall>v. v \<in> (varOfExp e) \<longrightarrow>s1(v) = s2(v)) \<longrightarrow>(expEval e s1=expEval e s2))\<and>
((\<forall>v. v \<in> (varOfForm f) \<longrightarrow>s1(v) = s2(v))\<longrightarrow>  (formEval f s1 =formEval f s2))"
 (is "(( ?condOne e \<longrightarrow> ?LHS e =?RHS e )\<and> (?condOnf f \<longrightarrow> ?LHS1 f =?RHS1 f ))")
proof(induct_tac e and f)
  fix x
  let ?e="IVar x"
  show "( ?condOne ?e \<longrightarrow> ?LHS ?e = ?RHS ?e)"
    by simp
next
  fix x
  let ?e="Const x"
  show "( ?condOne ?e \<longrightarrow> ?LHS ?e = ?RHS ?e)"
    by simp
next
  fix f1 e1 e2 
  let ?e="iteForm f1 e1 e2 "
  assume a1:" ?condOne e1 \<longrightarrow> ?LHS e1 =?RHS e1" and
  a2:"?condOne e2 \<longrightarrow> ?LHS e2 =?RHS e2" and
  a3:"?condOnf f1 \<longrightarrow> ?LHS1 f1 =?RHS1 f1 " 
  show "( ?condOne ?e \<longrightarrow> ?LHS ?e = ?RHS ?e)"
  proof 
    assume b1:"?condOne ?e"
    have b2:"?condOne e1" 
    proof(rule allI,rule impI)
      fix v
      assume c1:"v \<in> (varOfExp e1) " 
      have c2:"v  \<in> (varOfExp ?e)"
        by (simp add: c1)
      then show "s1(v) = s2(v)"
        by (simp add: b1) 
    qed
    then have b3:"?LHS e1 =?RHS e1"
      using local.a1 by blast
   have b2':"?condOne e2" 
    proof(rule allI,rule impI)
      fix v
      assume c1:"v \<in> (varOfExp e2) " 
      have c2:"v  \<in> (varOfExp ?e)"
        by (simp add: c1)
      then show "s1(v) = s2(v)"
        by (simp add: b1) 
    qed
    then have b3':"?LHS e2 =?RHS e2" 
      using local.a2 by blast
   have b2'':"?condOnf f1" 
    proof(rule allI,rule impI)
      fix v
      assume c1:"v \<in> (varOfForm f1) " 
      have c2:"v  \<in> (varOfExp ?e)"
        by (simp add: c1)
      then show "s1(v) = s2(v)"
        by (simp add: b1) 
    qed
    then have b3'':"?LHS1 f1 =?RHS1 f1"
      using local.a3 by blast 
    show "?LHS ?e = ?RHS ?e"
      by (simp add: b3 b3' b3'')
  qed
next
  fix e1 e2
   let ?f="eqn e1 e2 "
  assume a1:" ?condOne e1 \<longrightarrow> ?LHS e1 =?RHS e1" and
  a2:"?condOne e2 \<longrightarrow> ?LHS e2 =?RHS e2"  
  show "( ?condOnf ?f \<longrightarrow> ?LHS1 ?f = ?RHS1 ?f)"
  proof 
    assume b1:"?condOnf ?f"
    have b2:"?condOne e1" 
    proof(rule allI,rule impI)
      fix v
      assume c1:"v \<in> (varOfExp e1) " 
      have c2:"v  \<in> (varOfForm ?f)"
        by (simp add: c1)
      then show "s1(v) = s2(v)"
        by (simp add: b1) 
    qed
    then have b3:"?LHS e1 =?RHS e1"
      using local.a1 by blast
   have b2':"?condOne e2" 
    proof(rule allI,rule impI)
      fix v
      assume c1:"v \<in> (varOfExp e2) " 
      have c2:"v  \<in> (varOfForm ?f)"
        by (simp add: c1)
      then show "s1(v) = s2(v)"
        by (simp add: b1) 
    qed
    then have b3':"?LHS e2 =?RHS e2" 
      using local.a2 by blast
    show " ?LHS1 ?f = ?RHS1 ?f"
      by (simp add: b3 b3')  
  qed
next
  fix f1 f2
   let ?f="andForm f1 f2 "
  assume a1:" ?condOnf f1 \<longrightarrow> ?LHS1 f1 =?RHS1 f1" and
  a2:"?condOnf f2 \<longrightarrow> ?LHS1 f2 =?RHS1 f2"  
  show "( ?condOnf ?f \<longrightarrow> ?LHS1 ?f = ?RHS1 ?f)"
  proof 
    assume b1:"?condOnf ?f"
    have b2:"?condOnf f1" 
    proof(rule allI,rule impI)
      fix v
      assume c1:"v \<in> (varOfForm f1) " 
      have c2:"v  \<in> (varOfForm ?f)"
        by (simp add: c1)
      then show "s1(v) = s2(v)"
        by (simp add: b1) 
    qed
    then have b3:"?LHS1 f1 =?RHS1 f1"
      using local.a1 by blast
   have b2':"?condOnf f2" 
    proof(rule allI,rule impI)
      fix v
      assume c1:"v \<in> (varOfForm f2) " 
      have c2:"v  \<in> (varOfForm ?f)"
        by (simp add: c1)
      then show "s1(v) = s2(v)"
        by (simp add: b1) 
    qed
    then have b3':"?LHS1 f2 =?RHS1 f2" 
      using local.a2 by blast
    show " ?LHS1 ?f = ?RHS1 ?f"
      by (simp add: b3 b3')  
  qed
next
  fix f1 
   let ?f="neg f1  "
  assume a1:" ?condOnf f1 \<longrightarrow> ?LHS1 f1 =?RHS1 f1" 
  show "( ?condOnf ?f \<longrightarrow> ?LHS1 ?f = ?RHS1 ?f)"
  proof 
    assume b1:"?condOnf ?f"
    have b2:"?condOnf f1" 
    proof(rule allI,rule impI)
      fix v
      assume c1:"v \<in> (varOfForm f1) " 
      have c2:"v  \<in> (varOfForm ?f)"
        by (simp add: c1)
      then show "s1(v) = s2(v)"
        by (simp add: b1) 
    qed
    then have b3:"?LHS1 f1 =?RHS1 f1"
      using local.a1 by blast
   
    show " ?LHS1 ?f = ?RHS1 ?f"
      by (simp add: b3 )  
  qed
next
  fix f1 f2
   let ?f="orForm f1 f2 "
  assume a1:" ?condOnf f1 \<longrightarrow> ?LHS1 f1 =?RHS1 f1" and
  a2:"?condOnf f2 \<longrightarrow> ?LHS1 f2 =?RHS1 f2"  
  show "( ?condOnf ?f \<longrightarrow> ?LHS1 ?f = ?RHS1 ?f)"
  proof 
    assume b1:"?condOnf ?f"
    have b2:"?condOnf f1" 
    proof(rule allI,rule impI)
      fix v
      assume c1:"v \<in> (varOfForm f1) " 
      have c2:"v  \<in> (varOfForm ?f)"
        by (simp add: c1)
      then show "s1(v) = s2(v)"
        by (simp add: b1) 
    qed
    then have b3:"?LHS1 f1 =?RHS1 f1"
      using local.a1 by blast
   have b2':"?condOnf f2" 
    proof(rule allI,rule impI)
      fix v
      assume c1:"v \<in> (varOfForm f2) " 
      have c2:"v  \<in> (varOfForm ?f)"
        by (simp add: c1)
      then show "s1(v) = s2(v)"
        by (simp add: b1) 
    qed
    then have b3':"?LHS1 f2 =?RHS1 f2" 
      using local.a2 by blast
    show " ?LHS1 ?f = ?RHS1 ?f"
      by (simp add: b3 b3')  
  qed
next
  fix f1 f2
   let ?f="implyForm f1 f2 "
  assume a1:" ?condOnf f1 \<longrightarrow> ?LHS1 f1 =?RHS1 f1" and
  a2:"?condOnf f2 \<longrightarrow> ?LHS1 f2 =?RHS1 f2"  
  show "( ?condOnf ?f \<longrightarrow> ?LHS1 ?f = ?RHS1 ?f)"
  proof 
    assume b1:"?condOnf ?f"
    have b2:"?condOnf f1" 
    proof(rule allI,rule impI)
      fix v
      assume c1:"v \<in> (varOfForm f1) " 
      have c2:"v  \<in> (varOfForm ?f)"
        by (simp add: c1)
      then show "s1(v) = s2(v)"
        by (simp add: b1) 
    qed
    then have b3:"?LHS1 f1 =?RHS1 f1"
      using local.a1 by blast
   have b2':"?condOnf f2" 
    proof(rule allI,rule impI)
      fix v
      assume c1:"v \<in> (varOfForm f2) " 
      have c2:"v  \<in> (varOfForm ?f)"
        by (simp add: c1)
      then show "s1(v) = s2(v)"
        by (simp add: b1) 
    qed
    then have b3':"?LHS1 f2 =?RHS1 f2" 
      using local.a2 by blast
    show " ?LHS1 ?f = ?RHS1 ?f"
      by (simp add: b3 b3')  
  qed
next
  let ?f="chaos"
  show "( ?condOnf ?f \<longrightarrow> ?LHS1 ?f = ?RHS1 ?f)"
    by auto
qed(auto)



definition skipRule::" rule" where [simp]:
" skipRule\<equiv>
let g = chaos in
let s = skip in
guard g s" 

lemma andListMono2Aux: 
  assumes a1:"formEval a1 s \<longrightarrow> formEval b1 s" and a2:"formEval (andList A) s \<longrightarrow>formEval (andList B) s"
  shows "formEval (andList (a1#A)) s \<longrightarrow> formEval (andList (b1#B)) s"
  by (simp add: a2 local.a1)
  
lemma andListMono2[intro]: 
  assumes a1:"formEval a1 s \<longrightarrow> formEval b1 s" and a2:"formEval (andList A) s \<longrightarrow>formEval (andList B) s"
  and a3:"formEval (andList (a1#A)) s "
  shows " formEval (andList (b1#B)) s"
  using a2 a3 local.a1 by auto 

primrec assumption::"formula \<Rightarrow>formula" where
"assumption (implyForm a b) = b"

primrec conclude::"formula \<Rightarrow>formula" where
"conclude (implyForm a b) = b" 

primrec and2ListF ::"formula \<Rightarrow>formula set" where
" and2ListF (andForm f1 f2) = (and2ListF f1) \<union> (and2ListF f2)"|
"and2ListF (implyForm a c)  = {(implyForm a c)}" | 
  "and2ListF (orForm a c)  ={(orForm a c)}" |
  "and2ListF (eqn a c)  = {(eqn a c)}" |
  "and2ListF (neg a)  = {(neg a)}" |
  "and2ListF (chaos)  = {}" | 
  "and2ListF (dontCareForm)  = {(dontCareForm)}"

definition alphaEqForm  ::"formula \<Rightarrow> formula  \<Rightarrow>bool" where [simp]:
"alphaEqForm f1 f2  = ( (and2ListF f1) = (and2ListF f2))"

(*definition alphaEqExp  ::"expType \<Rightarrow> expType  \<Rightarrow>bool" where [simp]:
"alphaEqForm e1 e2  = ( (and2ListF f1) = (and2ListF f2))"*)

definition abs :: "varType set \<Rightarrow> varType set \<Rightarrow> nat \<Rightarrow> state \<Rightarrow> state" where [simp]:
  "abs OBV INDV M s v \<equiv>
    if v \<in> INDV \<and> scalar2Nat (s v) > M
    then index (M+1)
    else if v \<in> OBV then s v
    else dontCare"

definition stSimOn :: "state \<Rightarrow> state \<Rightarrow> varType set \<Rightarrow> bool" where [simp]:
  "stSimOn s1 s2 obV \<equiv> \<forall>v. v \<in> obV \<longrightarrow> s1 v = s2 v"

definition trans_sim_on :: "rule \<Rightarrow> rule \<Rightarrow> varType set \<Rightarrow> nat \<Rightarrow> varType set \<Rightarrow> bool" where [simp]:
  "trans_sim_on r1 r2 indV M obv \<equiv>
    \<forall>s. formEval (pre r1) s \<longrightarrow>
        formEval (pre r2) (abs obv indV M s) \<and>
        abs obv indV M (trans1 (act r1) s) = trans1 (act r2) (abs obv indV M s)"

definition trans_sim_on' :: "rule \<Rightarrow> rule \<Rightarrow> varType set \<Rightarrow> bool" where [simp]:
  "trans_sim_on' r1 r2 obV \<equiv>
    \<forall>s s'. stSimOn s s' obV \<longrightarrow>
           formEval (pre r1) s  \<longrightarrow>
           formEval (pre r2) s' \<and>
           stSimOn (trans1 (act r1) s) (trans1 (act r2) s') obV"

end
