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
            dontCareForm|
            forallForm "nat\<Rightarrow>formula" nat

primrec andList::"formula list \<Rightarrow> formula" where
andNil:  "andList [] = chaos" |
andCons:   "andList (frm#frms) = andForm frm (andList frms)" 

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
  skip | assign assignType | parallel statement statement|
forallStm "nat\<Rightarrow>statement" nat

text \<open>A statement is is just a lists of assignments,
but these assignments are executed in parallel, 
\emph{not} in a sequential order\<close>

type_synonym paraStatement = "nat \<Rightarrow> statement"

text \<open>A parameterized statement is just a function from a
parameter to a statement.\<close>


(*primrec cat :: "statement \<Rightarrow> statement \<Rightarrow> statement" where
  cat1: "cat (assign a) S = parallel a S" |
  cat2: "cat (parallel S0 S1) S = parallel  (parallel S0 S1) S"|
  cat3: "cat skip S = S"

text \<open>For conveniece, we also define the concatenation of statements.\<close>

primrec parallelList :: "statement list \<Rightarrow> statement" where
  "parallelList [] = skip"|
  "parallelList (S1#SL) = cat S1 (parallelList (SL))" 

fun forallSent::"nat list \<Rightarrow> paraStatement \<Rightarrow> statement" where
  oneSent: "forallSent [i] paraS = paraS i"|
  moreSent:" forallSent (i#xs) paraS = cat (paraS i) (forallSent xs paraS)" 
*) 

primrec parallelList :: "statement list \<Rightarrow> statement" where
  "parallelList [] = skip"|
  "parallelList (S1#SL) = parallel S1 (parallelList (SL))" 

type_synonym paraFormula = "nat \<Rightarrow> formula"

text \<open>Similarly, a parameterized formula is a function from
a parameter to a formula. We also define the $\mathsf{forall}$ 
and $mathsf{exists}$ formulas$.\<close>

(*fun forallForm :: "nat list \<Rightarrow> paraFormula \<Rightarrow> formula" where
  oneAllForm: "forallForm [i] forms = forms i" |
  moreAllForm: "forallForm (i#j#xs) forms = andForm (forms i) (forallForm (j#xs) forms)"*)

(*fun existsForm :: "nat list \<Rightarrow> paraFormula \<Rightarrow> formula" where
  oneExForm: "existsForm [i] forms = forms i"|
  moreExForm: "existsForm (i#j#xs) forms = orForm (forms i) (forallForm (j#xs) forms)"*)


datatype rule = guard formula statement

text \<open>With the formalizatiion of formula and statement,
it is natural to define a rule. A guard and
statement of a rule are also defined for convenience.\<close>


primrec pre :: "rule \<Rightarrow> formula" where
  "pre (guard f a) = f"

primrec act :: "rule \<Rightarrow> statement" where
act_def:  "act (guard f a) = a"


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
  evalForall:"formEval (forallForm ffun N) s =(\<forall>i\<le>N. formEval (ffun i) s)"|

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

primrec down :: "nat \<Rightarrow> nat list" where
  "down 0 = [0]" |
  "down (Suc n) = Suc n # down n"

primrec statement2Assigns :: "statement \<Rightarrow> assignType list" where
  "statement2Assigns (assign asgn) = [asgn]" |
  "statement2Assigns (parallel a S) =(statement2Assigns a) @ (statement2Assigns S)" |
  "statement2Assigns skip = []"|
  "statement2Assigns (forallStm ps N) = fold (\<lambda>a b. a@b)
  (map (\<lambda>i. statement2Assigns  (ps i)) (down N)) []"

definition wellformedAssgnList :: "assignType list \<Rightarrow> bool" where
  "wellformedAssgnList asgns = distinct (map fst asgns)"



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
  "varOfForm (chaos) = {}"|
  "varOfForm (forallForm pf N) = \<Union>{S. \<exists>i. i \<le> N \<and> S = varOfForm (pf i)}"

primrec unList::"varType set list \<Rightarrow>varType set" where
"unList [] ={}"|
"unList (a#as) = a \<union> unList (as)"

primrec varOfSent :: "statement \<Rightarrow> varType set" where
  "varOfSent (assign a) = {fst a}" |
  "varOfSent skip = {}" |
  "varOfSent (parallel sent1 sent2) = varOfSent sent1 \<union> varOfSent sent2"|
  "varOfSent (forallStm ps N) = \<Union>{S. \<exists>i. i \<le> N \<and> S = varOfSent (ps i)}"

lemma eqVarSent1:"v \<in> varOfSent (forallStm ps N) \<longleftrightarrow> (\<exists>i. i \<le> N \<and> v \<in> varOfSent (ps i))"
  by auto


primrec mutualDiffDefinedStm::"statement \<Rightarrow> bool" where
"mutualDiffDefinedStm skip =True" |
"mutualDiffDefinedStm (assign as) =True"|
"mutualDiffDefinedStm (parallel P0 P) = (mutualDiffDefinedStm P0 \<and> mutualDiffDefinedStm P\<and> 
 varOfSent P0 \<inter> varOfSent P={})"|
"mutualDiffDefinedStm (forallStm ps N) =
  ((\<forall>i j. i\<le>N \<longrightarrow>j\<le>N \<longrightarrow>i\<noteq>j\<longrightarrow>varOfSent (ps i) \<inter> varOfSent (ps j)={})\<and>
  (\<forall>i. i\<le>N \<longrightarrow>mutualDiffDefinedStm (ps i)))"

(*(fold \<union> ( ( map varOfSent (map ps (down N)))) {} )"*)
inductive isVarStm::"varType \<Rightarrow> statement \<Rightarrow>bool" where
" (x =fst a) \<Longrightarrow>isVarStm  x (assign a) " |  
"isVarStm  x   sent1 \<Longrightarrow>isVarStm  x   (parallel sent1 sent2)  "|
"isVarStm  x   sent2 \<Longrightarrow>isVarStm  x   (parallel sent1 sent2)  "|
" isVarStm  x    (ps 0) \<Longrightarrow>isVarStm  x   (forallStm ps N) " |
" \<lbrakk>n\<le>N; isVarStm  x    (ps (n))\<rbrakk>  \<Longrightarrow>isVarStm   x   (forallStm ps N) "

primrec varOfFormList :: "formula list \<Rightarrow> varType set" where
  "varOfFormList [] = {}" |
  "varOfFormList (f#fs) = varOfForm f \<union> varOfFormList fs"

text \<open>Condition wellformedAssgnList guarantees that asgns assign different
  variables to values\<close>
(*x:=e1||x=e2 is to be avoided**)
primrec transAux :: "assignType list \<Rightarrow> state \<Rightarrow> state" where
  "transAux [] s v= s v" |
  "transAux (pair#asgns) s v = 
    (if fst pair = v then expEval (snd pair) s
     else transAux asgns s v)"

definition trans:: "statement \<Rightarrow> state \<Rightarrow> state" where [simp]:
  "trans S s = transAux (statement2Assigns S) s"

primrec leastInd::"varType \<Rightarrow>nat \<Rightarrow> paraStatement \<Rightarrow>nat option" where
"leastInd v 0 ps =(if v\<in> varOfSent (ps 0) then Some(0) else None)"|
"leastInd v (Suc N) ps = (if (v\<in> varOfSent (ps (Suc N))) then Some(Suc N) else leastInd v N ps)"

primrec trans1 :: "statement \<Rightarrow> state \<Rightarrow> state" where
  "trans1 skip s v = s v" |
  "trans1 (assign as) s v = (if fst as = v then expEval (snd as) s else s v)" |
  "trans1 (parallel S1 S) s v = (if (v\<in> varOfSent S1) then trans1 S1 s v else trans1 S s v)"|
  "trans1  (forallStm ps N) s v = (if (leastInd v N  ps=None) then s v 
                                else trans1  ( ps (the (leastInd v N  ps))) s v)"

(*inductive transRel1 :: "statement \<Rightarrow> state\<Rightarrow> varType\<Rightarrow>scalrValueType\<Rightarrow>bool" where
  "transRel1 skip s v (s v)" |
  "fst as = v \<Longrightarrow> transRel1 (assign as) s v (expEval (snd as) s)"|
  "\<lbrakk>transRel1  S1  s v a1; isVarStm  v   S1\<rbrakk>\<Longrightarrow>transRel1 (parallel S1 S) s v a1" |
  
  "\<lbrakk>transRel1  S  s v a1; \<not>isVarStm  v   S1\<rbrakk>\<Longrightarrow>transRel1 (parallel S1 S) s v a1" |
  "\<lbrakk> i\<le>N; transRel1  (ps i)  s v a1\<rbrakk>\<Longrightarrow>transRel1 ((forallStm ps N)) s v a1"*)

(*inductive transRel1' :: "statement \<Rightarrow> state\<Rightarrow> state\<Rightarrow>bool" where
  "transRel1' skip s s" |

  "  transRel1' (assign as) s  (s'(fst a:=expEval (snd as) s))"|
  "\<lbrakk>transRel1'  S1  s s'; transRel1'  S  s' s''\<rbrakk>\<Longrightarrow>transRel1' (parallel S1 S) s s''" |
  
  "\<lbrakk>transRel1'  S  s s'; \<not>isVarStm  v   S1\<rbrakk>\<Longrightarrow>transRel1 (parallel S1 S) s v a1" |
  "\<lbrakk> transRel1'  (ps 0)  s v a1\<rbrakk>\<Longrightarrow>transRel1 ((forallStm ps N)) s v a1"*)

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
               formEval (pre r) s0 \<and>  ( s=trans1 (act r) s0 )}"

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

(*primrec valOf :: "assignType list \<Rightarrow> varType \<Rightarrow> expType" where
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
qed*)

text \<open>This lemma says that the value of (statement2Assigns S) assigned to variable v,
which is evaluated at the state s, is the same as that of v at the result state after
execution of S from state s\<close>

(*primrec substExp :: "expType \<Rightarrow> assignType list \<Rightarrow> expType"
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
*)
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
  "applySym2Form f chaos = chaos" |
   "applySym2Form f  (forallForm fp N) =( forallForm (\<lambda>i. applySym2Form f  (fp i)) N)"

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
  "applySym2Statement f (parallel S1 S) =
    parallel (applySym2Statement f S1) (applySym2Statement f S)"|
  "applySym2Statement f (forallStm  ps N) =  (forallStm (\<lambda>i. applySym2Statement f (ps i))  N)"


primrec applySym2Rule::"nat2nat \<Rightarrow> rule \<Rightarrow> rule" where
  "applySym2Rule f (guard g a) = guard (applySym2Form f g) (applySym2Statement f a)"

text \<open>Applying a permutation to a state\<close>
fun applySym2State :: "nat2nat \<Rightarrow> state \<Rightarrow> state" where
  "applySym2State p s (Ident sn) = applySym2Const p (s (Ident sn))" |
  "applySym2State p s (Para sn i) = applySym2Const p (s (Para sn ((inv p) i)))"|
  "applySym2State p s dontCareVar=applySym2Const p (s dontCareVar)"

primrec and2ListF ::"formula \<Rightarrow>formula set" where
" and2ListF (andForm f1 f2) = (and2ListF f1) \<union> (and2ListF f2)"|
"and2ListF (implyForm a c)  = {(implyForm a c)}" | 
  "and2ListF (orForm a c)  ={(orForm a c)}" |
  "and2ListF (eqn a c)  = {(eqn a c)}" |
  "and2ListF (neg a)  = {(neg a)}" |
  "and2ListF (chaos)  = {}" | 
  "and2ListF (dontCareForm)  = {(dontCareForm)}" |
  "and2ListF (forallForm pf N)  =  {g. \<exists>i. i \<le> N \<and> g\<in> and2ListF (pf i)}"

primrec parallel2Assigns::"statement \<Rightarrow> statement set" where
"parallel2Assigns skip={}"|

"parallel2Assigns (assign a) ={assign a}"|

"parallel2Assigns (parallel a S) =parallel2Assigns a \<union> (parallel2Assigns S)" |

"parallel2Assigns (forallStm ps N) = \<Union>{S. \<exists>i. i \<le> N \<and> S = parallel2Assigns (ps i)}"

definition alphaEqForm  ::"formula \<Rightarrow> formula  \<Rightarrow>bool" where [simp]:
"alphaEqForm f1 f2  = ( (and2ListF f1) = (and2ListF f2))"

definition alphaEqStm  ::"statement \<Rightarrow> statement  \<Rightarrow>bool" where [simp]:
"alphaEqStm f1 f2  = ( (parallel2Assigns f1) = (parallel2Assigns f2))"

definition alphaEqRule::"rule \<Rightarrow> rule \<Rightarrow>bool" where [simp]:
" alphaEqRule r1 r2 \<equiv>
  (alphaEqForm (pre r1) (pre r2)) \<and> alphaEqStm (act r1)  (act r2)"

lemma alphaForEq[intro]:
"alphaEqRule r r" by auto

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
  assume a1:"?P S" and a2:"?P as"
  show "?P ?S"
    by (simp add: a1 a2 assms)
qed (auto)

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
  "symProtRules N rs = (\<forall>p r. p permutes {x.   x \<le> N} \<and> r \<in> rs \<longrightarrow> applySym2Rule p r \<in> rs)"

text \<open>A list of formulas is symmetric\<close>
definition symPredList :: "nat \<Rightarrow> formula list \<Rightarrow> bool" where [simp]:
  "symPredList N fs = (\<forall>p f. p permutes {x.   x \<le> N} \<and> f \<in> set fs \<longrightarrow> applySym2Form p f \<in> set fs)"

lemma stFormSymCorrespondence:
  assumes a1: "p permutes {x.   x \<le> N}"
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
  assumes a1: "p permutes {x.   x \<le> N}"
  shows  (*"transRel1 S s0 u v =
         transRel1 (applySym2Statement p S) (applySym2State p s0) u v" (is "?P S")*)

"applySym2State p (trans1 S s0) =
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
  (*proof (cases v)
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
  *) sorry
  then show "?P ?s" by blast
next
  case (forallStm ps N)
  show ?case
    sorry
  (*fix x1 x2a 
  assume b1:"(\<And>x1a. x1a \<in> range x1 \<Longrightarrow>
               applySym2State p (trans1 x1a s0) =
               trans1 (applySym2Statement p x1a) (applySym2State p s0))"
  show " applySym2State p (trans1 (forallStm x1  x2a) s0) =
       trans1 (applySym2Statement p (forallStm x1 x2a)) (applySym2State p s0) "*)
qed

lemma reachSymLemma:
  assumes a1: "symPredList N fs"
    and a2: "symProtRules N rs" 
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
    and a4: "p permutes {x.   x \<le> N}"
  shows
    "\<forall>s i. s \<in> reachableSetUpTo (andList fs) rs i \<longrightarrow> formEval (applySym2Form p f) s" (is "?P i")
proof ((rule allI)+,rule impI)
  fix s i
  assume b1:"s \<in> reachableSetUpTo (andList fs) rs i "
  show  "formEval (applySym2Form p f) s "
  proof -
    have c1:"s= applySym2State ( p) (applySym2State (inv p) s)"
      using a4 permutes_bij by fastforce

    have c2:"(inv p) permutes {x.   x \<le> N}"
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

(*definition substExpByStatement :: "expType \<Rightarrow> statement \<Rightarrow> expType" where [simp]:
  "substExpByStatement e S \<equiv> substExp e (statement2Assigns S)" 

definition substFormByStatement :: "formula \<Rightarrow> statement \<Rightarrow> formula" where [simp]:
  "substFormByStatement f S \<equiv> substForm f (statement2Assigns S)" *)


text{*A statement $S$ can be transformed into an assignment to some variables
 $x_i$,  which is formalized by $\mathsf{statement2Assigns}~ S$.  
we use substExpByStatement e S and  substFormByStatement f S to denote the 
formula transformed from $f$  by substituting each $x_i$ with $e_i$. 
Furthermore, substFormByStatement f S  can be regarded as the weakest 
precondition of formula $f$ w.r.t. statement $S$. As Hoare logics specifies, *}


(*lemma preCondOnExp:  
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
*)

section \<open>Miscellaneous definitions and lemmas\<close>

(*text \<open>Variables of a variable, an expression, a formula, and a statement is defined by
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
*)
lemma simpDown: "down 5 = [5,4,3,2,1,0]"
  by (simp add: eval_nat_numeral(2) eval_nat_numeral(3))

lemma downNIsNotEmpty:
  "\<exists>j xs. down N = j#xs" (is "?P N")
  by (induct_tac N, auto)


text \<open>Definitions and lemmas on forallForm formula constructor\<close>

lemma forall1:
  (*"\<forall>i. i \<le> N \<longrightarrow> formEval (forallForm (down N) pf) s \<longrightarrow> formEval (pf i) s" (is "?P N") *) 
  "\<forall>i. i \<le> N \<longrightarrow> formEval (forallForm   pf N) s \<longrightarrow> formEval (pf i) s" (is "?P N")
  using evalForall by blast 
lemma forall2Aux:
  "(\<forall>i. i \<le> N \<longrightarrow> formEval (pf i) s) \<longrightarrow> formEval (forallForm  pf N) s" (is "?P N")
  using evalForall by blast 
  
lemma forall2:
  "\<forall>i. i \<le> N \<longrightarrow> formEval (pf i) s \<Longrightarrow> formEval (forallForm   pf N) s"
  by (simp add: forall2Aux)

lemma forallLemma [simp,intro]:
  assumes a1: "i \<le> N"
    and a2: "formEval (forallForm  pf N) s"
  shows "formEval (pf i) s"
  using a1 a2 forall1 less_imp_le by blast

lemma forallLemma1:
  assumes a1: "i \<le> N"
    and a2: "formEval (forallForm  pf N) s"
    and a3: "formEval (pf i) s \<longrightarrow> A"
  shows "A"
  using a1 a2 a3 by blast

lemma forallMono[intro,simp]:
  assumes a1: "formEval (forallForm   f N) s"
    and a2: "N' \<le> N"
  shows "formEval (forallForm   f N') s"
proof (rule forall2)
  show "\<forall>i. i \<le> N' \<longrightarrow> formEval (f i) s"
    by (meson Suc_leI a1 a2 forall1 le_SucI le_trans) 
qed  

subsection \<open>Lemmas on varsOf\<close>

lemma varsOnCat[simp]:
  "varOfSent (parallel S1 S2) = varOfSent S1 \<union> varOfSent S2"
  by (induct_tac S1; simp)

lemma forallVars:
  assumes a1: "\<forall>i. varOfSent (paraForm i) \<inter> varSet = {}"
  shows "varOfSent (forallStm   paraForm N) \<inter> varSet = {}"
  using assms by auto
 

lemma forallVars1[simp,intro!]:
  assumes a1: "\<forall>i. v \<notin> varOfSent (paraForm i)"
  shows "v \<notin> varOfSent (forallStm   paraForm N)" (is "?P N")
   using assms by auto
 
      
lemma varsOfForallSentIn[simp]:
  "i \<le> N \<longrightarrow> v \<in> varOfSent (paraForm i) \<longrightarrow> v \<in> varOfSent (forallStm   paraForm N)"
  (is "?P N")
  using eqVarSent1 by blast
  
(*lemma varsOfNot [simp,dest!]:
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
*)
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
  sorry (*proof (induct_tac E and f)
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
next
  case 
qed (auto)
*) 

lemma noEffect:
  "(\<forall>s. varOfExp E \<inter> varOfSent S = {} \<longrightarrow> expEval E s = expEval E (trans S s)) \<and> 
   (\<forall>s. varOfForm f \<inter> varOfSent S = {} \<longrightarrow> formEval f s = formEval f (trans S s))"
  sorry
 (* apply(cut_tac f="f" and E="E" and asgns="statement2Assigns S" in noEffectOnExpAux) 
  apply(unfold trans_def)
  apply(cut_tac S="S" in varsOfSent1)
  apply metis
  done*)

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
  sorry
(*proof(induct_tac e and f)
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
  by auto*)

section \<open>On CMP theoretical foundation\<close>

primrec isGlobal :: "varType \<Rightarrow> bool" where
  "isGlobal (Ident v) = True" |
  "isGlobal (Para n i) = False"

primrec scalar2Nat :: "scalrValueType \<Rightarrow> nat option" where
  "scalar2Nat (index n) = Some n"|
  "scalar2Nat (enum t v) =None "|
  "scalar2Nat (boolV b) =None " |
  "scalar2Nat (dontCare) =None"

(*definition state_sim_on3 :: "state \<Rightarrow> state \<Rightarrow> varType set \<Rightarrow> varType set \<Rightarrow> nat \<Rightarrow> bool" where [simp]:
  "state_sim_on3 s s' V V' N \<equiv>
    (\<forall>v. v \<in> V \<longrightarrow> s v = s' v) \<and>
    (\<forall>v. v \<in> V' \<longrightarrow> scalar2Nat (s v) \<le> N \<longrightarrow> s v = s' v)\<and>
    (\<forall>v. v \<in> V' \<longrightarrow> scalar2Nat (s v) > N \<longrightarrow> scalar2Nat (s' v) = N+1)"*)


primrec absTransfConst :: "nat \<Rightarrow> scalrValueType \<Rightarrow> scalrValueType" where [simp]:
  "absTransfConst M (enum t n) = enum t n"
| "absTransfConst M (index n) = (if n > M then index (M+1) else index n)"
| "absTransfConst M (boolV b) = boolV b"
| "absTransfConst M dontCare = dontCare"

definition abs1 :: "nat \<Rightarrow> state \<Rightarrow> state" where [simp]:
  "abs1 M s v \<equiv>
   
    (if \<exists>vn i. v = Para vn i \<and> i > M
    then dontCare
    else( if (v=dontCareVar)
      then dontCare
      else absTransfConst M ( s v)))"


(*else if \<exists>n.  (s v) = index n \<and> n > M
    then index (M + 1)
    else s v)"*)
(** if (v=dontCareVar) then dontCare
    else*)
definition pred_sim_on :: "formula \<Rightarrow> formula \<Rightarrow> nat \<Rightarrow> bool" where [simp]:
  "pred_sim_on f1 f2 M \<equiv>
    \<forall>s. formEval f1 s \<longrightarrow> formEval f2 (abs1 M s)"



definition trans_sim_on1 :: "rule \<Rightarrow> rule \<Rightarrow> nat \<Rightarrow>state\<Rightarrow> bool" where [simp]:
  "trans_sim_on1 r1 r2 M s\<equiv>
     formEval (pre r1) s \<longrightarrow>
        formEval (pre r2) (abs1 M s) \<and>
        abs1 M (trans1 (act r1) s) = trans1 (act r2) (abs1 M s)"


definition trans_sim_onRules :: "rule set\<Rightarrow> rule set\<Rightarrow> nat \<Rightarrow>state\<Rightarrow> bool" where [simp]:
  "trans_sim_onRules rs1 rs2 M s\<equiv>
      (\<forall> r. r \<in> rs1 \<longrightarrow> (\<exists>r'. r' \<in> rs2 \<and> trans_sim_on1 r r' M s))"


definition protSim :: "formula \<Rightarrow> formula \<Rightarrow> rule set \<Rightarrow> rule set \<Rightarrow> nat \<Rightarrow> bool" where [simp]:
  "protSim I I1 rs rs1 M \<equiv>
    pred_sim_on I I1 M \<and>
   (\<forall>s. trans_sim_onRules rs rs1 M s)"

lemma tranSimOnrulesUn:
  assumes a1:"trans_sim_onRules rs rs' M  s" and a2:"trans_sim_onRules rs1 rs1' M s" 
  shows "trans_sim_onRules (rs Un rs1) (rs' Un rs1') M s"
proof(unfold trans_sim_onRules_def)
  show "
      (\<forall> r. r \<in> (rs Un rs1) \<longrightarrow> (\<exists>r'. r' \<in> (rs' Un rs1') \<and> trans_sim_on1 r r' M s))"
  proof((rule allI)+,rule impI)
    fix  r
    assume b1:"r \<in> (rs Un rs1)"
    from b1 have b2:"r\<in> rs \<or> r \<in>rs1" by auto
    moreover
    {assume b2:"r \<in> rs"
     
      have "(\<exists>r'. r' \<in> (rs' Un rs1') \<and> trans_sim_on1 r r' M s)"
        using a1 b2 by(unfold trans_sim_onRules_def, auto)
    }
    moreover
    {assume b2:"r \<in> rs1"
      have "(\<exists>r'. r' \<in> (rs' Un rs1') \<and> trans_sim_on1 r r' M s)"
        using assms(2) b2 by fastforce
    }    
    ultimately show "(\<exists>r'. r' \<in> (rs' Un rs1') \<and> trans_sim_on1 r r' M s)"
      by blast
  qed
qed
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
          by (meson protSim_def trans_sim_on1_def trans_sim_onRules_def) 
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
  "strengthenForm (andForm a c) g =andForm (strengthenForm a g) 
    (strengthenForm c g) " |
  "strengthenForm (orForm a c) g = chaos" |
  "strengthenForm (eqn a c) g = chaos" |
  "strengthenForm (neg a) g = chaos" |
  "strengthenForm (chaos) g = chaos" | 
  "strengthenForm (dontCareForm) g = chaos"|
  "strengthenForm (forallForm ps N) g =  (forallForm (\<lambda>i. strengthenForm (ps i) g)  N)"
  
primrec strengthenFormByForms :: "formula list \<Rightarrow> formula \<Rightarrow> formula"  where
  "strengthenFormByForms [] g = chaos" |
  "strengthenFormByForms (g#gs) f = andForm (strengthenForm g f) (strengthenFormByForms gs f)"

primrec strengthenFormsByForms1::"formula list \<Rightarrow> formula \<Rightarrow> formula"  where
  "strengthenFormsByForms1 [] g = chaos" |
  "strengthenFormsByForms1 (g#gs) f = andForm g (strengthenFormsByForms1 gs f)"

definition strengthenFormByFormSet :: "formula set \<Rightarrow> formula \<Rightarrow> formula set"  where
" strengthenFormByFormSet FS g \<equiv>
  {g'. \<exists>f. f \<in>FS \<and> g'=strengthenForm f g }"

definition strengthen :: "formula list \<Rightarrow> formula \<Rightarrow> formula" where [simp]:
  "strengthen fs f \<equiv> andForm f (strengthenFormByForms fs f)"

definition strengthen1 :: "formula list \<Rightarrow> formula \<Rightarrow> formula" where [simp]:
 
"strengthen1 fs f=  andForm f (andList fs )"

definition strengthen2 :: "formula list \<Rightarrow> formula \<Rightarrow> formula" where [simp]:
  "strengthen2 fs f \<equiv> andForm f (andList (map (\<lambda>g. strengthenForm g f) fs) )"

definition strengthen2' :: "nat \<Rightarrow> paraFormula  \<Rightarrow> formula\<Rightarrow>formula" where [simp]:
  "strengthen2' N pf f \<equiv>  (forallForm (\<lambda>j. strengthenForm (pf j) f) N  )"

primrec leftEq :: "formula \<Rightarrow> expType" where
  "leftEq (eqn e1 e2) = e2"

primrec strengthenStm :: "formula \<Rightarrow> statement \<Rightarrow> statement" where
  "strengthenStm g skip = skip" |

  "strengthenStm g (assign a) =
    (if (\<exists>e1 e2 n i Id. g = eqn e1 e2 \<and> e1 = IVar (Para n i) \<and> e2 = IVar (Ident Id) \<and>
                        snd a = IVar (Para n i)) 
     then assign (fst a, leftEq g) 
     else assign a)" |

  "strengthenStm g (parallel S1 S2) =
   parallel (strengthenStm g S1 ) (strengthenStm g S2) " |

  "strengthenStm g (forallStm ps N) = forallStm (\<lambda>i. strengthenStm g (ps i)) N"

primrec strengthenStmByForms :: "formula list \<Rightarrow> statement \<Rightarrow> statement" where
  "strengthenStmByForms [] S = S" |
  "strengthenStmByForms (g#gs) S = (strengthenStm g (strengthenStmByForms gs S))"

primrec strengthenR :: "formula list \<Rightarrow> formula list \<Rightarrow>rule \<Rightarrow> rule" where
  "strengthenR fs ss (guard g S) = 
    guard (strengthen fs g) (strengthenStmByForms ss S)"

primrec strengthenR1 :: "formula list \<Rightarrow> formula list \<Rightarrow>rule \<Rightarrow> rule" where
  "strengthenR1 fs ss (guard g S) = 
    guard (strengthen1 fs g) (strengthenStmByForms ss S)"

primrec strengthenR2 :: "formula list \<Rightarrow> formula list \<Rightarrow>rule \<Rightarrow> rule" where
  "strengthenR2 fs ss (guard g S) = 
    guard (strengthen2 fs g) (strengthenStmByForms ss S)"

primrec strengthenR2' :: "nat \<Rightarrow>paraFormula list  \<Rightarrow>formula list \<Rightarrow>rule \<Rightarrow> rule" where
  "strengthenR2' N pfs ss (guard g S) = 
    guard (andForm g (andList (map (\<lambda>pf. strengthen2' N pf g) pfs))) (strengthenStmByForms ss S)"

lemma strengthenByForm:
  "formEval f s \<longrightarrow> formEval g s \<longrightarrow> formEval (strengthenForm g f) s"
  by (induct_tac g, auto) 

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

lemma strengthenByForms1:
  "(\<forall>f. f \<in> set F \<longrightarrow> formEval f s) \<longrightarrow> formEval f s \<longrightarrow> formEval (strengthen1  F f) s"
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

lemma strengthenByForms1Inv:
  " formEval (strengthen1  F f) s \<longrightarrow>(\<forall>f. f \<in> set F \<longrightarrow> (formEval f s) \<and> formEval f s) "
  (is "?P F")
proof(induct_tac F)
  show "?P []"
    by auto
next
  fix a list
  assume b1:"?P list"
  show "?P (a#list)"
    by simp 
qed

lemma strengthenByForms2:
  "(\<forall>f. f \<in> set F \<longrightarrow> formEval f s) \<longrightarrow> formEval f s \<longrightarrow> formEval (strengthen2  F f) s"
  (is "?P F")
proof(induct_tac F)
  show "?P []"
    by auto
next
  fix a list
  assume b1:"?P list"
  show "?P (a#list)"
    using b1 strengthenByForm by  auto
qed

lemma strengthen1Implystrengthen2:
  assumes a1:"formEval (strengthen1  F f) s"
  shows "formEval (strengthen2  F f) s"
  using assms strengthenByForms2 by auto

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
  sorry
(*proof (induct_tac Stm)
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
qed*)

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
  assumes a1: "\<forall>r. r \<in> rs \<longrightarrow> (\<exists>Ls ss. set Ls \<subseteq> set S \<and>  set ss \<subseteq> set S \<and> strengthenR Ls ss r \<in> rs')"
    and a2: "\<forall>i s f. s \<in> reachableSetUpTo I rs' i \<longrightarrow> f \<in> set S \<longrightarrow> formEval f s" 
  shows "\<forall>s f. s \<in> reachableSetUpTo I rs i \<longrightarrow>
               f \<in> set S \<longrightarrow> (s \<in> reachableSetUpTo I rs' i \<and> formEval f s)" (is "?P i")
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
      have c2:" (\<exists> Ls ss. set Ls \<subseteq> set S\<and>  set ss \<subseteq> set S  \<and>  strengthenR Ls ss r \<in> rs') "
        using a1 c1 by auto 

      from c2 obtain Ls  ss where c2:"set Ls \<subseteq> set S \<and>  set ss \<subseteq> set S  \<and>  strengthenR Ls ss r \<in> rs'"
        by blast
      from b0 c1 c2 have c3:"\<forall>f. f \<in> set Ls \<longrightarrow> formEval f s0"
        by auto
      have c4:"formEval (strengthenFormByForms  Ls (pre r)) s0"
        using c1 c3 strengthenByForms by blast

      from b0 c1 c2 have c3:"\<forall>f. f \<in> set ss \<longrightarrow> formEval f s0"
        by auto
      have c5:"trans1 (strengthenStmByForms ss (act r)) s0 = trans1 (act r) s0"
        using c3 strengthTransSimEffect by blast
      have c6:"trans1  (act (strengthenR Ls ss r)) s0 = trans1 (act r) s0"
        by (metis act.simps c5 rule.exhaust strengthenR.simps)
      have c7:"s0 \<in> reachableSetUpTo I rs' n"
        using b0 b2 c1 by blast
      have c8:"formEval (pre (strengthenR Ls ss r)) s0"
        by (metis c1 c4 evalAnd pre.simps rule.exhaust strengthenR.simps strengthen_def) 
        
      have c8:"trans1  (act (strengthenR Ls ss r)) s0 \<in> reachableSetUpTo I rs' (Suc n)"
        using c2 c7 c8 by auto

      
      have "s \<in>reachableSetUpTo I rs' (Suc n) \<and> formEval f s"
        using a2 b2 c1 c6 c8 by presburger
    }
    ultimately show "s \<in>reachableSetUpTo I rs' (Suc n) \<and> formEval f s"
      by auto 
  qed
qed

lemma strengthenProtSimProt1:
  assumes a1:"\<forall>r. r \<in> rs \<longrightarrow>(\<exists> Ls ss. set Ls \<subseteq>  S \<and>  set ss \<subseteq>  S \<and> strengthenR1 Ls ss r \<in> rs')" and
  a2:"\<forall>i s f. s \<in>reachableSetUpTo I rs' i \<longrightarrow> f \<in> S \<longrightarrow>formEval f s" 
shows "\<forall>s. s \<in>reachableSetUpTo I rs i  \<longrightarrow>
   (s \<in>reachableSetUpTo I rs' i \<and>(\<forall>f. f \<in> S \<longrightarrow>formEval f s))" (is "?P i")
proof(induct_tac i)  
  show "?P 0"
    by (metis a2 reachableSet0)
next
  fix n
  assume b0:"?P n"
  show "?P (Suc n)"
  proof((rule allI)+,(rule impI)+)
    fix s f
    assume b1:"s \<in> reachableSetUpTo I rs (Suc n)" 
          
    have "s \<in> reachableSetUpTo I rs n |
        (\<exists>s0 r. r \<in>rs \<and>   s0 \<in>reachableSetUpTo I rs n\<and> formEval (pre r) s0 \<and> trans1 (act r) s0=s) "
      using b1 by auto
    moreover
    {assume b1:"s \<in> reachableSetUpTo I rs n "
      have " s \<in> reachableSetUpTo I rs' n \<and> (\<forall>f. f \<in> S \<longrightarrow> formEval f s)" (*"s \<in>reachableSetUpTo I rs' n \<and> formEval f s"*)
        using b0 b1  by blast
    }
    moreover
    {assume c1:"(\<exists>s0 r. r \<in>rs \<and>   s0 \<in>reachableSetUpTo I rs n\<and> 
      formEval (pre r) s0 \<and> trans1 (act r) s0=s) "
      from c1 obtain s0 r where c1:"r \<in>rs \<and>   s0 \<in>reachableSetUpTo I rs n\<and> 
      formEval (pre r) s0 \<and> trans1 (act r) s0=s"
        by blast
      have c2:" (\<exists> Ls ss. set Ls \<subseteq>  S\<and>  set ss \<subseteq>  S  \<and>  strengthenR1 Ls ss r \<in> rs') "
        using a1 c1 by auto 

      from c2 obtain Ls  ss where c2:"set Ls \<subseteq>  S \<and>  set ss \<subseteq>  S  \<and>  strengthenR1 Ls ss r \<in> rs'"
        by blast
      from b0 c1 c2 have c3:"\<forall>f. f \<in> set Ls \<longrightarrow> formEval f s0"
        by auto
      have c4:"formEval (strengthen1  Ls (pre r)) s0"
        by (simp add: c1 c3) 

      from b0 c1 c2 have c3:"\<forall>f. f \<in> set ss \<longrightarrow> formEval f s0"
        by auto
      have c5:"trans1 (strengthenStmByForms ss (act r)) s0 = trans1 (act r) s0"
        using c3 strengthTransSimEffect by blast
      have c6:"trans1  (act (strengthenR1 Ls ss r)) s0 = trans1 (act r) s0"
        by (metis act.simps c5 rule.exhaust strengthenR1.simps)
      have c7:"s0 \<in> reachableSetUpTo I rs' n"
        using b0  c1 by blast
      have c8:"formEval (pre (strengthenR1 Ls ss r)) s0"
        by (metis c1 c4 evalAnd pre.simps rule.exhaust strengthenR1.simps strengthen_def) 
        
      have c8:"trans1  (act (strengthenR1 Ls ss r)) s0 \<in> reachableSetUpTo I rs' (Suc n)"
        using c2 c7 c8 by auto

      
      have "s \<in>reachableSetUpTo I rs' (Suc n) \<and> (\<forall>f. f \<in> S \<longrightarrow> formEval f s)"
        using a2  c1 c6 c8 by presburger
    }
    ultimately show "s \<in>reachableSetUpTo I rs' (Suc n) \<and>(\<forall>f. f \<in> S \<longrightarrow> formEval f s)"
      by auto 
  qed
qed


lemma strengthenProtSimProt12:
  assumes a1:"\<forall>r1. r1 \<in> rs1 \<longrightarrow>(\<exists>r Ls ss. set Ls \<subseteq>  S \<and>   set ss \<subseteq>  S \<and> r1=strengthenR1 Ls ss r 
  \<and> strengthenR2 Ls ss r \<in> rs2 )" and
  a2:"\<forall>i s f. s \<in>reachableSetUpTo I rs2 i \<longrightarrow> f \<in> S \<longrightarrow>formEval f s" 
shows "\<forall>s . s \<in>reachableSetUpTo I rs1 i \<longrightarrow>
   (s \<in>reachableSetUpTo I rs2 i \<and>(\<forall>f. f \<in> S \<longrightarrow>formEval f s))" (is "?P i")
proof(induct_tac i)  
  show "?P 0"
    by (metis a2 reachableSet0)
next
  fix n
  assume b0:"?P n"
  show "?P (Suc n)"
  proof((rule allI)+,(rule impI)+)
    fix s f
    assume b1:"s \<in> reachableSetUpTo I rs1 (Suc n)"  
    have "s \<in> reachableSetUpTo I rs1 n |
        (\<exists>s0 r. r \<in>rs1 \<and>   s0 \<in>reachableSetUpTo I rs1 n\<and> formEval (pre r) s0 \<and> trans1 (act r) s0=s) "
      using b1 by auto
    moreover
    {assume b1:"s \<in> reachableSetUpTo I rs1 n "
      have "s \<in>reachableSetUpTo I rs2 n \<and>(\<forall>f. f \<in> S \<longrightarrow>formEval f s)"
        using b0 b1  by blast
    }
    moreover
    {assume c1:"(\<exists>s0 r. r \<in>rs1 \<and>   s0 \<in>reachableSetUpTo I rs1 n\<and> 
      formEval (pre r) s0 \<and> trans1 (act r) s0=s) "
      from c1 obtain s0 r1 where c1:"r1 \<in>rs1 \<and>   s0 \<in>reachableSetUpTo I rs1 n\<and> 
      formEval (pre r1) s0 \<and> trans1 (act r1) s0=s"
        by blast
      have c2:"\<exists>r Ls ss. set Ls \<subseteq>  S \<and>  set ss \<subseteq>  S \<and> r1=strengthenR1 Ls ss r 
  \<and> strengthenR2 Ls ss r \<in> rs2"
(*" (\<exists> Ls ss. set Ls \<subseteq> set S\<and>  set ss \<subseteq> set S  \<and>  strengthenR1 Ls ss r \<in> rs') "*)
        using a1 c1 by auto 

      from c2 obtain r Ls  ss where c2:"set Ls \<subseteq>  S \<and>  set ss \<subseteq>  S  \<and> r1=strengthenR1 Ls ss r 
  \<and> strengthenR2 Ls ss r \<in> rs2"
        by blast
      from b0 c1 c2 have c3:"\<forall>f. f \<in> set Ls \<longrightarrow> formEval f s0"
        by auto
      have c4:"formEval (strengthen2  Ls (pre r)) s0"
        by (metis c1 c2 pre.simps rule.exhaust strengthen1Implystrengthen2 strengthenR1.simps)
        

      from b0 c1 c2 have c3:"\<forall>f. f \<in> set ss \<longrightarrow> formEval f s0"
        by auto
      have c5:"trans1 (strengthenStmByForms ss (act r)) s0 = trans1 (act r) s0"
        using c3 strengthTransSimEffect by blast
      have c6:"trans1  (act (strengthenR1 Ls ss r)) s0 = trans1 (act r) s0"
        by (metis act.simps c5 rule.exhaust strengthenR1.simps)
      have c7:"s0 \<in> reachableSetUpTo I rs2 n"
        using b0  c1 by blast
      have c8:"formEval (pre (strengthenR2 Ls ss r)) s0"
        by (metis c4 pre.simps rule.exhaust strengthenR2.simps) 
        
      have c8:"trans1  (act (strengthenR2 Ls ss r)) s0 \<in> reachableSetUpTo I rs2 (Suc n)"
        using c2 c7 c8 by auto

      
      have "s \<in>reachableSetUpTo I rs2 (Suc n)\<and>(\<forall>f. f \<in> S \<longrightarrow>formEval f s)"
        by (metis a2 act.simps  c1 c2 c5 c6 c8 rule.exhaust strengthenR2.simps) 
    }
    ultimately show "s \<in>reachableSetUpTo I rs2 (Suc n) \<and>(\<forall>f. f \<in> S \<longrightarrow>formEval f s)"
      by auto 
  qed
qed 
(*
lemma strengthenProtSimProt12':
  assumes a1:"\<forall>r1. r1 \<in> rs1 \<longrightarrow>(\<exists>r Ls ss. set Ls \<subseteq>  S \<and>   set ss \<subseteq>  S \<and> r1=strengthenR1 Ls ss r 
  \<and> strengthenR2 Ls ss r \<in> rs2 )" 
shows "\<forall>s . s \<in>reachableSetUpTo I rs1 i \<longrightarrow>
   (s \<in>reachableSetUpTo I rs2 i)" (is "?P i")
proof(induct_tac i)  
  show "?P 0"
    by (metis  reachableSet0)
next
  fix n
  assume b0:"?P n"
  show "?P (Suc n)"
  proof((rule allI)+,(rule impI)+)
    fix s f
    assume b1:"s \<in> reachableSetUpTo I rs1 (Suc n)"  
    have "s \<in> reachableSetUpTo I rs1 n |
        (\<exists>s0 r. r \<in>rs1 \<and>   s0 \<in>reachableSetUpTo I rs1 n\<and> formEval (pre r) s0 \<and> trans1 (act r) s0=s) "
      using b1 by auto
    moreover
    {assume b1:"s \<in> reachableSetUpTo I rs1 n "
      have "s \<in>reachableSetUpTo I rs2 n"
        using b0 b1  by blast
    }
    moreover
    {assume c1:"(\<exists>s0 r. r \<in>rs1 \<and>   s0 \<in>reachableSetUpTo I rs1 n\<and> 
      formEval (pre r) s0 \<and> trans1 (act r) s0=s) "
      from c1 obtain s0 r1 where c1:"r1 \<in>rs1 \<and>   s0 \<in>reachableSetUpTo I rs1 n\<and> 
      formEval (pre r1) s0 \<and> trans1 (act r1) s0=s"
        by blast
      have c2:"\<exists>r Ls ss. set Ls \<subseteq>  S \<and>  set ss \<subseteq>  S \<and> r1=strengthenR1 Ls ss r 
  \<and> strengthenR2 Ls ss r \<in> rs2"
(*" (\<exists> Ls ss. set Ls \<subseteq> set S\<and>  set ss \<subseteq> set S  \<and>  strengthenR1 Ls ss r \<in> rs') "*)
        using a1 c1 by auto 

      from c2 obtain r Ls  ss where c2:"set Ls \<subseteq>  S \<and>  set ss \<subseteq>  S  \<and> r1=strengthenR1 Ls ss r 
  \<and> strengthenR2 Ls ss r \<in> rs2"
        by blast
      (*from b0 c1 c2 have c3:"\<forall>f. f \<in> set Ls \<longrightarrow> formEval f s0"
        by auto*)
      have c4:"formEval (strengthen2  Ls (pre r)) s0"
        by (metis c1 c2 pre.simps rule.exhaust strengthen1Implystrengthen2 strengthenR1.simps)
        

     (* from b0 c1 c2 have c3:"\<forall>f. f \<in> set ss \<longrightarrow> formEval f s0"
        by auto*)
      have c5:"trans1 (strengthenStmByForms ss (act r)) s0 = trans1 (act r) s0"
        using c3 strengthTransSimEffect by blast
      have c6:"trans1  (act (strengthenR1 Ls ss r)) s0 = trans1 (act r) s0"
        by (metis act.simps c5 rule.exhaust strengthenR1.simps)
      have c7:"s0 \<in> reachableSetUpTo I rs2 n"
        using b0  c1 by blast
      have c8:"formEval (pre (strengthenR2 Ls ss r)) s0"
        by (metis c4 pre.simps rule.exhaust strengthenR2.simps) 
        
      have c8:"trans1  (act (strengthenR2 Ls ss r)) s0 \<in> reachableSetUpTo I rs2 (Suc n)"
        using c2 c7 c8 by auto

      
      have "s \<in>reachableSetUpTo I rs2 (Suc n)\<and>(\<forall>f. f \<in> S \<longrightarrow>formEval f s)"
        by (metis a2 act.simps  c1 c2 c5 c6 c8 rule.exhaust strengthenR2.simps) 
    }
    ultimately show "s \<in>reachableSetUpTo I rs2 (Suc n) \<and>(\<forall>f. f \<in> S \<longrightarrow>formEval f s)"
      by auto 
  qed
qed 

*)

primrec absTransfVar :: "nat \<Rightarrow> varType \<Rightarrow> varType" where 
  "absTransfVar M (Ident n) = Ident n" |
  "absTransfVar M (Para n i) =
    (if i > M then dontCareVar else Para n i)" |
  "absTransfVar M dontCareVar = dontCareVar"

primrec absTransfExp :: "nat \<Rightarrow> expType \<Rightarrow> expType" and
  absTransfForm :: "nat \<Rightarrow> formula \<Rightarrow> formula" where
  "absTransfExp M (Const i) = Const (absTransfConst M i)" |

  "absTransfExp M (IVar v) =
    (if absTransfVar M v = dontCareVar then dontCareExp 
     else IVar (absTransfVar M v))" |

  "absTransfExp M (iteForm b e1 e2) = 
    (if absTransfForm M b \<noteq> dontCareForm \<and>
         absTransfExp M e1 \<noteq> dontCareExp \<and>
         absTransfExp M e2 \<noteq> dontCareExp  
     then iteForm (absTransfForm M b) (absTransfExp M e1) (absTransfExp M e2)
     else dontCareExp)" |

  "absTransfForm M (eqn e1 e2) =
    (if absTransfExp M e1 = dontCareExp | absTransfExp M e2 = dontCareExp
     then dontCareForm 
     else eqn (absTransfExp M e1) (absTransfExp M e2))" |

  "absTransfForm M (neg f) =
    (if absTransfForm M f = dontCareForm 
     then dontCareForm 
     else if absTransfForm M f = eqn (Const (index (Suc M))) (Const (index (Suc M))) then
       dontCareForm
     else neg (absTransfForm M f))" |

  "absTransfForm M (andForm f1 f2) =
    (if absTransfForm M f1 = dontCareForm then absTransfForm M f2
     else if absTransfForm M f2 = dontCareForm then absTransfForm M f1
     else andForm (absTransfForm M f1) (absTransfForm M f2))" |

  "absTransfForm M (orForm f1 f2) =
    (if absTransfForm M f1 = dontCareForm then dontCareForm
     else if absTransfForm M f2 = dontCareForm then dontCareForm
     else orForm (absTransfForm M f1) (absTransfForm M f2))" |

  "absTransfForm M (implyForm f1 f2) =
    (if absTransfForm M f1 = dontCareForm then dontCareForm
     else if absTransfForm M f2 = dontCareForm then dontCareForm
     else implyForm (absTransfForm M f1) (absTransfForm M f2))" |

  "absTransfForm M chaos = chaos" |

  "absTransfForm M dontCareForm = dontCareForm" |

  "absTransfExp M dontCareExp = dontCareExp" |

  "absTransfForm M (forallForm pf N) = forallForm (\<lambda>i. absTransfForm M (pf i)) M"

primrec absTransfStatement :: "nat \<Rightarrow> statement \<Rightarrow> statement" where
  "absTransfStatement M skip = skip"|
  "absTransfStatement M (assign as) = 
    (if absTransfVar M (fst as) = dontCareVar 
     then skip
     else assign (fst as, absTransfExp M (snd as)))" |
  "absTransfStatement M (parallel as S) =
    parallel (absTransfStatement M as) (absTransfStatement M S)" |
  "absTransfStatement M (forallStm PS N) =
    forallStm (\<lambda>i. absTransfStatement M (PS i)) M" 
 
(*"absTransfStatement M (forallStm PS N) =
   parallelList (map (\<lambda>i. absTransfStatement M (PS i)) (down N))"*)

definition topTransfForm::" formula \<Rightarrow>formula" where 
  "topTransfForm f \<equiv> if f = dontCareForm then chaos else f"

(*primrec topTransfExp::"  expType \<Rightarrow>expType"  and
topTransfForm::" formula \<Rightarrow>formula" where
"topTransfExp   (Const i) =Const (    i)" |

"topTransfExp  (IVar v) =
  (IVar v)" |

"topTransfExp  (iteForm b e1 e2) = 
    (if (b=dontCareForm \<or> e1=dontCareExp \<or> e2=dontCareExp) then dontCareExp
    else (iteForm (topTransfForm  b) (topTransfExp  e1) (topTransfExp  e2)))
   "|

"topTransfForm  (eqn e1 e2) =
   (eqn (topTransfExp  e1) (topTransfExp  e2))" |


"topTransfForm  (neg f) =
 
    (neg (topTransfForm  f))" |

"topTransfForm  (andForm f1 f2) =
   andForm (topTransfForm  f1) (topTransfForm  f2)" |

"topTransfForm  (orForm f1 f2) =
    orForm (topTransfForm  f1) (topTransfForm  f2)" |


"topTransfForm  (implyForm f1 f2) =
    implyForm (topTransfForm  f1) (topTransfForm  f2)" |

"topTransfForm  chaos= chaos" |

"topTransfForm  dontCareForm= chaos" |

"topTransfExp  dontCareExp= dontCareExp" |

"topTransfForm  (forallForm pf N) = (forallForm (\<lambda>i. topTransfForm ( pf i)) N)"
*)

primrec absTransfRule :: "nat \<Rightarrow> rule \<Rightarrow> rule" where
  "absTransfRule M (guard g a) =
    guard (topTransfForm (absTransfForm M g)) (absTransfStatement M a)"

definition indexedVar::"varType \<Rightarrow> bool" where [simp]:
  "indexedVar v \<equiv> \<forall>s. \<exists> n. s v = index n"


lemma agreeOnVars:
  shows "((\<forall>v. v \<in> (varOfExp e) \<longrightarrow>s1(v) = s2(v)) \<longrightarrow>(expEval e s1=expEval e s2))\<and>
((\<forall>v. v \<in> (varOfForm f) \<longrightarrow>s1(v) = s2(v))\<longrightarrow>  (formEval f s1 =formEval f s2))"
 (is "(( ?condOne e \<longrightarrow> ?LHS e =?RHS e )\<and> (?condOnf f \<longrightarrow> ?LHS1 f =?RHS1 f ))")
  sorry
(*proof(induct_tac e and f)
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
*)


definition skipRule :: rule where [simp]:
  "skipRule \<equiv>
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

primrec assumption :: "formula \<Rightarrow> formula" where
  "assumption (implyForm a b) = b"

primrec conclude :: "formula \<Rightarrow> formula" where
  "conclude (implyForm a b) = b" 


(*definition alphaEqExp  ::"expType \<Rightarrow> expType  \<Rightarrow>bool" where [simp]:
"alphaEqForm e1 e2  = ( (and2ListF f1) = (and2ListF f2))"*)

(*definition abs :: "varType set \<Rightarrow> varType set \<Rightarrow> nat \<Rightarrow> state \<Rightarrow> state" where [simp]:
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
*)



(*
lemma onMapSetDown:
  "set (map f (down N)) ={g. \<exists>j.  j\<le>N \<and> g= f j}" (is "?P N")
proof(induct_tac N,simp) 
  fix n
  assume a1:"?P n"
  show "?P (Suc n)"
    apply(cut_tac a1,auto)
  sorry*) 
lemma onMapStrenghthEnCat:
  "and2ListF (strengthen (x#xs) g) = 
  and2ListF (strengthenForm x g) \<union> (and2ListF (strengthen xs g))"
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
      show "and2ListF g \<union> (and2ListF (strengthenForm (f (Suc N)) g) \<union> and2ListF (strengthenFormByForms (map f (down N)) g)) = 
    and2ListF g \<union> {g'. \<exists>j\<le>Suc N. g' \<in> and2ListF (strengthenForm (f j) g)}"
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
  
proof(induct_tac x, auto simp del:taut_def)
  fix ant0 cons0 
  assume b1:" applySym2Form p (strengthenForm ant0 g) = 
  strengthenForm (applySym2Form p ant0) (applySym2Form p g)"
  and 
  b2:"applySym2Form p (strengthenForm cons0 g) =
   strengthenForm (applySym2Form p cons0) (applySym2Form p g)" and
  b3:"taut (implyForm g ant0)" and
  b4:"\<not> taut (implyForm (applySym2Form p g) (applySym2Form p ant0)) "
  have "taut (implyForm g ant0) | \<not> taut (implyForm g ant0)" 
    by blast
  let ?x="implyForm ant0 cons0"
  from b2 have b5:"taut (applySym2Form p (implyForm g ant0))"
       using assms b3 tautSYm by blast 
  with b4 have "False"
    by auto
  then show "applySym2Form p cons0 = chaos" by blast
next
  fix ant0 cons0 
  assume b1:" applySym2Form p (strengthenForm ant0 g) = 
  strengthenForm (applySym2Form p ant0) (applySym2Form p g)"
  and 
  b2:"applySym2Form p (strengthenForm cons0 g) =
   strengthenForm (applySym2Form p cons0) (applySym2Form p g)" and
  b3:"\<not>taut (implyForm g ant0)" and
  b4:" taut (implyForm (applySym2Form p g) (applySym2Form p ant0)) "
   
  let ?x="implyForm ant0 cons0"
from b2 have b5:"\<not>taut (applySym2Form p (implyForm g ant0))"
       using assms b3 tautSYm by blast 
  with b4 have "False"
    by auto
  then show " chaos = applySym2Form p cons0" by blast
   
qed

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



lemma onMapAndListF:
  "  and2ListF ( andList  (map f (down N)) ) =
    {g'. \<exists>j. j\<le>N   \<and> g' \<in> (and2ListF ( (f j) ))  }" (is "?P N")
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
    proof( simp  )  
      show "and2ListF (f (Suc N)) \<union> and2ListF (andList (map f (down N)))
   = {g'. \<exists>j\<le>Suc N. g' \<in> and2ListF (f j)} "
        (is "?LHS = ?RHS")
      proof
        show "?LHS \<subseteq> ?RHS"
        proof
          fix x
          assume c1:"x \<in> ?LHS "
          show "x \<in> ?RHS"
          proof -
            have c2:"x \<in> and2ListF (f (Suc N))  | x \<in>and2ListF (andList (map f (down N)))  "
              using c1 by blast
             
            moreover
            {assume d1:"x \<in>(and2ListF (f (Suc N)))"
              have "x \<in> ?RHS"
                using d1  by blast
            }
            moreover
            {assume d1:"x \<in>and2ListF (andList (map f (down N)))"
              have "x \<in> {g'. \<exists>j\<le>  N. g' \<in> and2ListF (f j)}"
                apply(cut_tac a1,simp)
                using a1 d1  by blast
              then    have "x \<in> ?RHS"
                using le_SucI by blast 
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
            have d1:"   x \<in> {g'. \<exists>j\<le>Suc N. g' \<in> and2ListF  (f j)}"
              using c1 by auto
             
            moreover
            {assume d1:"x \<in> {g'. \<exists>j\<le>Suc N. g' \<in> and2ListF (f j)} "
              have  "x \<in> {g'.  g' \<in>   ( and2ListF (f (Suc N)))} |
                 x \<in> {g'. \<exists>j\<le> N. g' \<in> and2ListF ( (f j) )}"
                using d1 le_Suc_eq by force 
              moreover
              {assume d1:"x \<in> {g'.  g' \<in>   ( and2ListF (f (Suc N)))} "
                have "x \<in> ?LHS"
                  using d1 by auto
              }
              moreover
              {assume d1:" x \<in> {g'. \<exists>j\<le> N. g' \<in> and2ListF ( (f j) )} "
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



lemma onMapAndListF2:
  "  and2ListF ( andList  LS ) =
    {g'. \<exists>l. l \<in>set LS  \<and> g' \<in> (and2ListF ( l ))  }" (is "?P LS")
proof(induct_tac LS,auto)qed
(*proof(induct_tac LS)
   show "?P []" 
    by simp
next
  fix l ls
  assume a1:"?P ls"
  show "?P (l#ls)"
  proof -
    (*have b1:"(map f (down (Suc N))) =map f ([Suc N]@(down N))"
      by simp *)
    show  "?P (l#ls)"
    proof( simp  )  
      show "and2ListF (f (Suc N)) \<union> and2ListF (andList (map f (down N)))
   = {g'. \<exists>j\<le>Suc N. g' \<in> and2ListF (f j)} "
        (is "?LHS = ?RHS")
      proof
        show "?LHS \<subseteq> ?RHS"
        proof
          fix x
          assume c1:"x \<in> ?LHS "
          show "x \<in> ?RHS"
          proof -
            have c2:"x \<in> and2ListF (f (Suc N))  | x \<in>and2ListF (andList (map f (down N)))  "
              using c1 by blast
             
            moreover
            {assume d1:"x \<in>(and2ListF (f (Suc N)))"
              have "x \<in> ?RHS"
                using d1  by blast
            }
            moreover
            {assume d1:"x \<in>and2ListF (andList (map f (down N)))"
              have "x \<in> {g'. \<exists>j\<le>  N. g' \<in> and2ListF (f j)}"
                apply(cut_tac a1,simp)
                using a1 d1  by blast
              then    have "x \<in> ?RHS"
                using le_SucI by blast 
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
            have d1:"   x \<in> {g'. \<exists>j\<le>Suc N. g' \<in> and2ListF  (f j)}"
              using c1 by auto
             
            moreover
            {assume d1:"x \<in> {g'. \<exists>j\<le>Suc N. g' \<in> and2ListF (f j)} "
              have  "x \<in> {g'.  g' \<in>   ( and2ListF (f (Suc N)))} |
                 x \<in> {g'. \<exists>j\<le> N. g' \<in> and2ListF ( (f j) )}"
                using d1 le_Suc_eq by force 
              moreover
              {assume d1:"x \<in> {g'.  g' \<in>   ( and2ListF (f (Suc N)))} "
                have "x \<in> ?LHS"
                  using d1 by auto
              }
              moreover
              {assume d1:" x \<in> {g'. \<exists>j\<le> N. g' \<in> and2ListF ( (f j) )} "
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
*)
lemma andListApplySym0:
 " applySym2Form p (andList (  (map (\<lambda>j.    (fg j )) (down N)))) =
  andList (map (\<lambda>j. (applySym2Form p (fg  j))) (down N))"  (is "?P N")
proof(induct_tac N)
  show "?P 0"
    by auto
next
  fix N
  assume b1:"?P N"
  show "?P (Suc N)"
    by (simp add: b1)
qed

lemma andListApplySym:
 " applySym2Form p (andList (  (map (\<lambda>j.    (fg i j)) (down N)))) =
  andList (map (\<lambda>j. (applySym2Form p (fg i j))) (down N))"  (is "?P N")
proof(induct_tac N)
  show "?P 0"
    by auto
next
  fix N
  assume b1:"?P N"
  show "?P (Suc N)"
    by (simp add: b1)
qed


lemma wellFormAndlistIsSym1:
  assumes a1:"\<forall>i . applySym2Form p (fg i ) = fg (p i) "  
  and   b1:" p permutes {i. i \<le> N} " 
shows " 
  (and2ListF  (andList (map (\<lambda>j.    (fg  j)) (down N)))) =
      and2ListF (applySym2Form p (andList (  (map (\<lambda>j.    (fg  j)) (down N)))))" 
(is " ?LHS0 N=?RHS0 N")
proof -
  
  have b3:"?LHS0 N= {g'. \<exists>j. j\<le>N   \<and> g' \<in> (and2ListF ( (fg   j) ))  }"
    using onMapAndListF by auto
  have b4:"applySym2Form p (andList (  (map (\<lambda>j.    (fg  j)) (down N)))) =  
   (andList (map (\<lambda>j. (applySym2Form p (fg  j))) (down N))) "
  proof(rule  andListApplySym )qed
  have b5:"?RHS0 N = {g'. \<exists>j. j\<le>N   \<and> g' \<in> (and2ListF (applySym2Form p (fg   (  j)) ))  }"
    using b4 onMapAndListF by auto
  have b6:"{g'. \<exists>j. j\<le>N   \<and> g' \<in> (and2ListF (applySym2Form p (fg   j) ))  }
   = {g'. \<exists>j. j\<le>N   \<and> g' \<in> (and2ListF (  (fg   ( p j)) ))  }"
    using a1 by auto
  have b7:"{g'. \<exists>j. j\<le>N   \<and> g' \<in> (and2ListF ( (fg   j) ))  }=
    {g'. \<exists>j. j\<le>N   \<and> g' \<in> (and2ListF (  (fg   ( p j)) ))  }"
  (is "?LHS =?RHS")
      
  proof
    show "?LHS \<subseteq> ?RHS"
    proof 
      fix x
      assume c1:"x \<in>?LHS"
      have c2:"\<exists>j\<le>N. x \<in> and2ListF (fg   j)"
        using c1 by blast
      then obtain j where c2:"j\<le>N \<and> x \<in> and2ListF (fg   j)" 
        by blast
      have c3:"\<exists> j'. j'\<le>N \<and>j=p j'"
        by (metis b1 c2 mem_Collect_eq permutes_def)
      then obtain j' where c3:"j' \<le>N \<and> j=p j'" by blast
      with c2 have c4:"j'\<le>N \<and> x \<in> and2ListF (fg   (p j'))"
        by blast
      then show  "x \<in> ?RHS"
        by blast
    qed
  next
    show "?RHS \<subseteq> ?LHS"
    proof 
      fix x
      assume c1:"x \<in>?RHS"
      have c2:"\<exists>j\<le>N. x \<in> and2ListF (fg   (p j))"
        using c1 by blast
      then obtain j where c2:"j\<le>N \<and> x \<in> and2ListF (fg   ( p j))" 
        by blast
      have c3:"\<exists> j'. j'\<le>N \<and>j'=p j"
        by (metis b1 c2 mem_Collect_eq permutes_def)
      then obtain j' where c3:"j' \<le>N \<and> j'=p j" by blast
      with c2 have c4:"j'\<le>N \<and> x \<in> and2ListF (fg   j')"
        by blast
      then show  "x \<in> ?LHS"
        by blast
    qed
  qed 
  show "and2ListF (andList (map (fg  ) (down N)))
   = and2ListF (applySym2Form p (andList (map (fg ) (down N))))"
    by (simp add: b3 b5 b6 b7)
    
 
qed

lemma wellFormAndlistIsSym1':
  assumes a1:"\<forall>i . applySym2Form p (fg i ) = fg (p i) "  
  and   b1:" p permutes {i. i \<le> N} " 
shows " 
  (and2ListF  (forallForm fg N)) =
      and2ListF (applySym2Form p (forallForm fg N))" 
(is " ?LHS0 N=?RHS0 N")
proof -
  have b3:"?LHS0 N= {g'. \<exists>j. j\<le>N   \<and> g' \<in> (and2ListF ( (fg   j) ))  }"
    by auto   
  (*have b4:"applySym2Form p (andList (  (map (\<lambda>j.    (fg  j)) (down N)))) =  
   (andList (map (\<lambda>j. (applySym2Form p (fg  j))) (down N))) "
  proof(rule  andListApplySym )qed*)
  have b5:"?RHS0 N = {g'. \<exists>j. j\<le>N   \<and> g' \<in> (and2ListF (applySym2Form p (fg   (  j)) ))  }"
      by auto
  have b6:"{g'. \<exists>j. j\<le>N   \<and> g' \<in> (and2ListF (applySym2Form p (fg   j) ))  }
   = {g'. \<exists>j. j\<le>N   \<and> g' \<in> (and2ListF (  (fg   ( p j)) ))  }"
    using a1 by auto
  have b7:"{g'. \<exists>j. j\<le>N   \<and> g' \<in> (and2ListF ( (fg   j) ))  }=
    {g'. \<exists>j. j\<le>N   \<and> g' \<in> (and2ListF (  (fg   ( p j)) ))  }"
  (is "?LHS =?RHS")
      
  proof
    show "?LHS \<subseteq> ?RHS"
    proof 
      fix x
      assume c1:"x \<in>?LHS"
      have c2:"\<exists>j\<le>N. x \<in> and2ListF (fg   j)"
        using c1 by blast
      then obtain j where c2:"j\<le>N \<and> x \<in> and2ListF (fg   j)" 
        by blast
      have c3:"\<exists> j'. j'\<le>N \<and>j=p j'"
        by (metis b1 c2 mem_Collect_eq permutes_def)
      then obtain j' where c3:"j' \<le>N \<and> j=p j'" by blast
      with c2 have c4:"j'\<le>N \<and> x \<in> and2ListF (fg   (p j'))"
        by blast
      then show  "x \<in> ?RHS"
        by blast
    qed
  next
    show "?RHS \<subseteq> ?LHS"
    proof 
      fix x
      assume c1:"x \<in>?RHS"
      have c2:"\<exists>j\<le>N. x \<in> and2ListF (fg   (p j))"
        using c1 by blast
      then obtain j where c2:"j\<le>N \<and> x \<in> and2ListF (fg   ( p j))" 
        by blast
      have c3:"\<exists> j'. j'\<le>N \<and>j'=p j"
        by (metis b1 c2 mem_Collect_eq permutes_def)
      then obtain j' where c3:"j' \<le>N \<and> j'=p j" by blast
      with c2 have c4:"j'\<le>N \<and> x \<in> and2ListF (fg   j')"
        by blast
      then show  "x \<in> ?LHS"
        by blast
    qed
  qed 
  show "and2ListF (forallForm fg N) = and2ListF (applySym2Form p (forallForm fg N))"
    by (simp add: b3 b5 b6 b7)
qed

lemma wellFormAndlistIsSym2:
  assumes a1:"\<forall>i j. applySym2Form p (fg i j) = fg (p i) (p j)"  
  and   b1:" p permutes {i. i \<le> N} " and b2:"i \<le> N"
shows " 
  (and2ListF  (andList (map (\<lambda>j.    (fg (p i) j)) (down N)))) =
      and2ListF (applySym2Form p (andList (  (map (\<lambda>j.    (fg i j)) (down N)))))" 
(is " ?LHS0 N=?RHS0 N")
proof -
  
  have b3:"?LHS0 N= {g'. \<exists>j. j\<le>N   \<and> g' \<in> (and2ListF ( (fg (p i) j) ))  }"
    using onMapAndListF by auto
  have b4:"applySym2Form p (andList (  (map (\<lambda>j.    (fg i j)) (down N)))) =  
   (andList (map (\<lambda>j. (applySym2Form p (fg i j))) (down N))) "
  proof(rule  andListApplySym )qed
  have b5:"?RHS0 N = {g'. \<exists>j. j\<le>N   \<and> g' \<in> (and2ListF (applySym2Form p (fg ( i) (  j)) ))  }"
    using b4 onMapAndListF by auto
  have b6:"{g'. \<exists>j. j\<le>N   \<and> g' \<in> (and2ListF (applySym2Form p (fg ( i) (  j)) ))  }
   = {g'. \<exists>j. j\<le>N   \<and> g' \<in> (and2ListF (  (fg (p i) ( p j)) ))  }"
    using a1 by auto
  have b7:"{g'. \<exists>j. j\<le>N   \<and> g' \<in> (and2ListF ( (fg (p i) j) ))  }=
    {g'. \<exists>j. j\<le>N   \<and> g' \<in> (and2ListF (  (fg (p i) ( p j)) ))  }"
  (is "?LHS =?RHS")
      
  proof
    show "?LHS \<subseteq> ?RHS"
    proof 
      fix x
      assume c1:"x \<in>?LHS"
      have c2:"\<exists>j\<le>N. x \<in> and2ListF (fg (p i) j)"
        using c1 by blast
      then obtain j where c2:"j\<le>N \<and> x \<in> and2ListF (fg (p i) j)" 
        by blast
      have c3:"\<exists> j'. j'\<le>N \<and>j=p j'"
        by (metis b1 c2 mem_Collect_eq permutes_def)
      then obtain j' where c3:"j' \<le>N \<and> j=p j'" by blast
      with c2 have c4:"j'\<le>N \<and> x \<in> and2ListF (fg (p i) (p j'))"
        by blast
      then show  "x \<in> ?RHS"
        by blast
    qed
  next
    show "?RHS \<subseteq> ?LHS"
    proof 
      fix x
      assume c1:"x \<in>?RHS"
      have c2:"\<exists>j\<le>N. x \<in> and2ListF (fg (p i) (p j))"
        using c1 by blast
      then obtain j where c2:"j\<le>N \<and> x \<in> and2ListF (fg (p i) ( p j))" 
        by blast
      have c3:"\<exists> j'. j'\<le>N \<and>j'=p j"
        by (metis b1 c2 mem_Collect_eq permutes_def)
      then obtain j' where c3:"j' \<le>N \<and> j'=p j" by blast
      with c2 have c4:"j'\<le>N \<and> x \<in> and2ListF (fg (p i) j')"
        by blast
      then show  "x \<in> ?LHS"
        by blast
    qed
  qed 
  show "and2ListF (andList (map (fg (p i)) (down N)))
   = and2ListF (applySym2Form p (andList (map (fg i) (down N))))"
    by (simp add: b3 b5 b6 b7)
qed

lemma and2ListAndCongruence:
  assumes a1:"and2ListF g1=and2ListF g2"
  shows "and2ListF (andForm f g1) =and2ListF (andForm f g2)"
  by (simp add: assms)
  
lemma and2ListForall:
  "(\<forall>f. f \<in>and2ListF g \<longrightarrow> formEval f s) = formEval g s"
  apply(induct_tac g,auto)
  apply blast
  by (meson rangeI) 

 
  
lemma and2ListFCong:
  shows a1:"and2ListF g1=and2ListF g2 \<longrightarrow> formEval  g1 s=formEval  g2 s"
  by (metis and2ListForall)
   
   


definition symProtRules' :: "nat \<Rightarrow> rule set \<Rightarrow> bool" where [simp]:
  "symProtRules' N rs = (\<forall>p r. p permutes {x.   x \<le> N} 
  \<and> r \<in> rs \<longrightarrow> (\<exists>r'. alphaEqRule r'( applySym2Rule p r) \<and> r' \<in> rs))"



primrec getValueType::"scalrValueType\<Rightarrow>string" where [simp]:
" getValueType (enum t v) =''enum''"|
" getValueType (index n) =''nat''"|
"  getValueType (boolV n) =''bool''"|
"  getValueType (dontCare) =''any''"


definition typeOf::"state \<Rightarrow>expType \<Rightarrow>string " where [simp]:
"typeOf s e =
   getValueType (expEval  e s)" 




definition isBoolVal::"state \<Rightarrow> expType \<Rightarrow> bool" where [simp]:
"isBoolVal s e\<equiv>typeOf s e =''bool'' "

definition isEnumVal::"state \<Rightarrow> expType \<Rightarrow> bool" where [simp]:
"isEnumVal s e\<equiv>typeOf s e =''enum'' "

definition isIndexVal::"state \<Rightarrow> expType \<Rightarrow> bool" where [simp]:
"isIndexVal s e\<equiv>typeOf s e =''nat'' "

definition isDontCareVal::"state \<Rightarrow> expType \<Rightarrow> bool" where [simp]:
"isDontCareVal s e\<equiv>typeOf s e =''any'' "

(*primrec isIndexVal::"state \<Rightarrow> expType \<Rightarrow> bool" where
"isIndexVal s (IVar v) = (if (\<exists> vn. s(v) =(index vn)) then True else False)" | 
"isIndexVal s (Const c) = (if (\<exists> vn. c =(index vn)) then True else False)" | 
"isIndexVal s (iteForm f e1 e2) = 
  ( (isIndexVal s e1) \<and> (isIndexVal s e2))"*)
lemma nonIndexEqn:
  assumes a:"isBoolVal s e1 \<or> isEnumVal s e1 "  and 
    b:"isBoolVal s e2 \<or> isEnumVal s e2"
  and a3:"(\<exists>v. e1=(IVar v)) | (\<exists>c. e1=(Const c))" and
  a4:"(\<exists>v. e2=(IVar v)) | (\<exists>c. e2=(Const c))"
shows "absTransfForm M ((eqn e1 e2))\<noteq>dontCareForm \<longrightarrow>formEval (neg(eqn e1 e2)) s \<longrightarrow>
  formEval (absTransfForm M (neg(eqn e1 e2))) (abs1 M s)" sorry
(*proof(rule impI)+
  assume a1:"absTransfForm M ((eqn e1 e2))\<noteq>dontCareForm" and
  a2:"formEval (neg(eqn e1 e2)) s"
  from a1 have b1:"absTransfExp M e1\<noteq>dontCareExp \<and> absTransfExp M e2\<noteq>dontCareExp "
    by auto
  have b2:"\<exists>i. isSimpExp i e1 \<and>absTransfExp M e1=e1"
  proof(cut_tac a3, erule disjE)
    assume  c1:"\<exists>v. e1 = IVar v "
    from c1 obtain v where c1:"e1 = IVar v" 
      by blast
    show "\<exists>i. isSimpExp i e1 \<and>absTransfExp M e1=e1"
    proof(case_tac "v")
      fix xn
      assume d1:"v=Ident xn"
      show "\<exists>i. isSimpExp i e1\<and>absTransfExp M e1=e1 "
      proof(rule_tac x="0" in exI,cut_tac c1 d1,auto)qed
    next
      fix n j
      assume d1:"v=Para n  j"
      show "\<exists>i. isSimpExp i e1\<and>absTransfExp M e1=e1 "
      proof(rule_tac x="j" in exI,cut_tac a1 c1 d1,auto)
      qed

    next
      assume d1:"v = dontCareVar"
      show "\<exists>i. isSimpExp i e1 \<and>absTransfExp M e1=e1"
      proof(cut_tac a1 b1 c1 d1,auto)qed
    qed
  next
    assume  c1:"\<exists>c. e1 = Const c "
    from c1 obtain c where c1:"e1 = Const c" 
      by blast
    show "\<exists>i. isSimpExp i e1 \<and>absTransfExp M e1=e1"
      by (metis a absTransfConst.simps(1) absTransfConst.simps(3) absTransfExp.simps(1) c1 expType.distinct(1) expType.distinct(7) expType.inject(2) isBoolVal.cases isEnumVal.cases isSimpExp.simps(2))

  qed

  have b3:"\<exists>i. isSimpExp i e2\<and>absTransfExp M e2=e2 "
  proof(cut_tac a4, erule disjE)
    assume  c1:"\<exists>v. e2= IVar v "
    from c1 obtain v where c1:"e2 = IVar v" 
      by blast
    show "\<exists>i. isSimpExp i e2 \<and>absTransfExp M e2=e2"
    proof(case_tac "v")
      fix xn
      assume d1:"v=Ident xn"
      show "\<exists>i. isSimpExp i e2 \<and>absTransfExp M e2=e2 "
      proof(rule_tac x="0" in exI,cut_tac c1 d1,auto)qed
    next
      fix n j
      assume d1:"v=Para n  j"
      show "\<exists>i. isSimpExp i e2 \<and>absTransfExp M e2=e2"
      proof(rule_tac x="j" in exI,cut_tac b1 c1 d1,auto)qed

    next
      assume d1:"v = dontCareVar"
      show "\<exists>i. isSimpExp i e2 \<and>absTransfExp M e2=e2"
      proof(cut_tac b1 c1 d1,auto)qed
    qed
  next
    assume  c1:"\<exists>c. e2 = Const c "
    from c1 obtain c where c1:"e2 = Const c" 
      by blast
    show "\<exists>i. isSimpExp i e2 \<and>absTransfExp M e2=e2"
      by (metis absTransfConst.simps(1) absTransfConst.simps(3) absTransfExp.simps(1) b c1 evalConst expType.distinct(1) expType.distinct(7) isBoolVal.simps isEnumVal.simps isSimpExp.simps(2))
   from b2 obtain i where b4:" isSimpExp i e1 \<and>absTransfExp M e1=e1"
    by blast

  from b3 obtain j where b5:" isSimpExp j e2 \<and>absTransfExp M e2=e2"
    using \<open>\<exists>i. isSimpExp i e2 \<and> absTransfExp M e2 = e2\<close> by blast
     

  have b6:" (absTransfForm M (neg(eqn e1 e2))) =neg (eqn e1 e2)"
    using a2 b4 b5 local.a1 by auto 

  have b7:"expEval e1 s= expEval (absTransfExp M e1) (abs1 M s)"
    
    using a a3 b2 apply auto
    apply (metis absTransfConst.simps(3) expType.distinct(1) expType.distinct(3) expType.inject(1) isBoolVal.simps)
    apply (metis absTransfConst.simps(3) expType.distinct(1) expType.distinct(3) expType.inject(1) isBoolVal.simps)
    apply (metis absTransfConst.simps(1) expType.distinct(1) expType.distinct(3) expType.inject(1) isEnumVal.simps)
    by (metis absTransfConst.simps(1) expType.distinct(1) expType.distinct(3) expType.inject(1) isEnumVal.simps)
     
     
  have b8:"expEval e2 s= expEval (absTransfExp M e2) (abs1 M s)"
    sorry
  show " formEval (absTransfForm M (neg (eqn e1 e2))) (abs1 M s)"
    using a2 b4 b5 b7 b8 by auto
qed
*)
(*lemma onWellAndList1:
  assumes a1:"s dontCareVar =dontCare" and "M \<le> N"
  shows "\<forall>f. (wellFormedAndList1  N f  \<longrightarrow>
  formEval  f s\<longrightarrow>((absTransfForm M f)\<noteq>dontCareForm \<and>formEval  (absTransfForm M f) (abs1 M s)))" 
    (is "\<forall>f. ?P f N")
  sorry*)
(*proof(induct_tac N)
  show "\<forall>f. ?P f 0"
  proof(rule allI,(rule impI)+)
    fix f
    assume b1:"wellFormedAndList1 0 f "  
    and b3:"formEval f s "
    show "absTransfForm M f \<noteq> dontCareForm \<and>formEval (absTransfForm M f) (abs1 M s)" 
    proof -
      have c1:" (\<exists> fg. f=fg 0 \<and>
              ( \<forall>i.  (isSimpFormula i (fg i))))" (is "\<exists> fg. ?P fg")
        by(cut_tac b1,auto)

      then obtain fg  where c1:"?P fg" 
        by blast
      have c2:"absTransfForm M (fg 0) \<noteq> dontCareForm" sorry
      show "absTransfForm M f \<noteq> dontCareForm \<and>
      formEval (absTransfForm M f) (abs1 M s)"
        using absExpForm  b3 c1 c2 local.a1 by blast 
    qed
  qed
next
  fix n
  assume b0:"\<forall>f. ?P f n"
  show "\<forall>f. ?P f (Suc n)"
  proof(rule allI,(rule impI)+)
    fix f
    assume b1:"wellFormedAndList1 (Suc n) f "  
    and b3:"formEval f s "
    show "absTransfForm M f \<noteq> dontCareForm \<and>
      formEval (absTransfForm M f) (abs1 M s)" 
    proof -
     have c1:" (\<exists> fg. f=andList (map (\<lambda>i. fg i) (down (Suc n))) \<and>
        ( \<forall>i.  (isSimpFormula i (fg i))))" (is "\<exists> fg. ?P fg")
       by(cut_tac b1,auto)
     then obtain fg where c1:"?P fg"
       by blast
     have c2:"f=andForm (fg (Suc n)) (andList (map (\<lambda>i. fg i) (down ( n))))"
       by (simp add: c1)
     have c3:"formEval  (fg (Suc n)) s \<and>
           formEval (andList (map (\<lambda>i. fg i) (down ( n)))) s"
       by(cut_tac c2 b3,auto)
     have c3a:"wellFormedAndList1  n (andList (map (\<lambda>i. fg i) (down ( n))))"
       using c1 wellFormedAndList1_def by blast
     have c3b:"absTransfForm M (andList (map (\<lambda>i. fg i) (down ( n)))) \<noteq> dontCareForm "  
       apply(cut_tac b0 c3 c3a,auto) done

     have c4:"absTransfForm M (fg (Suc n)) =dontCareForm \<or>
          absTransfForm M (fg (Suc n)) \<noteq>dontCareForm 
          " 
       by blast
    
     moreover
     {assume c4:"absTransfForm M (fg (Suc n)) =dontCareForm   "
       have c5:"absTransfForm M f=
        absTransfForm M (andList (map (\<lambda>i. fg i) (down ( n))))"
           by(cut_tac c2 c3 c4,auto)
       have "absTransfForm M f \<noteq> dontCareForm \<and>
      formEval (absTransfForm M f) (abs1 M s)"
         using b0 c3 c3a c5 by presburger 
     }
    moreover
     {assume c4:"absTransfForm M (fg (Suc n)) \<noteq>dontCareForm   "
       have c5:"absTransfForm M f=
        andForm (absTransfForm M (fg (Suc n)))
        (absTransfForm M (andList (map (\<lambda>i. fg i) (down ( n)))))"
         by (simp add: c2 c3b c4)
       have c6:"isSimpFormula (Suc n) (fg (Suc n))"
         using c1 by blast
          
       have c7:" formEval (absTransfForm M (fg (Suc n))) (abs1 M s)"
         apply(cut_tac c6 c4 c3,auto)
         using absExpForm local.a1 by blast

       have "absTransfForm M f \<noteq> dontCareForm \<and>
      formEval (absTransfForm M f) (abs1 M s)"
         using b0 c3 c3a c5 c7 evalAnd formula.distinct(21) by presburger 
     }
     ultimately show "absTransfForm M f \<noteq> dontCareForm \<and>
      formEval (absTransfForm M f) (abs1 M s)"
       by blast
   qed
 qed
qed*)
lemma andListAbstraction: 
 shows "formEval  (andList fs) s\<longrightarrow> (\<forall>f. f \<in> set fs \<longrightarrow>
  ((absTransfForm M f) =dontCareForm \<or> (formEval  (absTransfForm M f) (abs1 M s))))
  \<longrightarrow> ((absTransfForm M (andList fs)) =chaos\<or> 
  formEval  (absTransfForm M (andList fs)) (abs1 M s))" (is "?P fs")
proof(induct_tac fs)
  show "?P []"
    by auto
next
  fix fa fs
  assume b0:"?P fs"
  show "?P (fa#fs)" 
  proof(rule impI)+
    assume b1:" formEval (andList (fa # fs)) s " and
    b2:"\<forall>f. f \<in> set (fa # fs) \<longrightarrow>
        absTransfForm M f = dontCareForm \<or> formEval (absTransfForm M f) (abs1 M s)"  
    have b3:"formEval fa s \<and>formEval (andList (  fs)) s "
      using b1 by auto
    have b4:"\<forall>f. f \<in> set (  fs) \<longrightarrow>
        absTransfForm M f = dontCareForm \<or> formEval (absTransfForm M f) (abs1 M s)"  
      using b2 by auto
    have b5:"((absTransfForm M (andList fs)) =chaos\<or> 
    formEval  (absTransfForm M (andList fs)) (abs1 M s))" 
      using b0 b4 b3 by blast
    have b6:"absTransfForm M fa=dontCareForm \<or> formEval (absTransfForm M fa) (abs1 M s)"
      by (simp add: b2)
      
    show "(absTransfForm M (andList (fa#fs))) =chaos \<or>
    formEval  (absTransfForm M (andList (fa#fs))) (abs1 M s)"
      using b5 b6 by auto
  qed
qed

definition sameType :: "state \<Rightarrow> expType \<Rightarrow> expType \<Rightarrow> bool" where [simp]:
  "sameType s e1 e2 \<equiv> typeOf s e1 = typeOf s e2"

primrec isBoundExp::"state\<Rightarrow>nat \<Rightarrow> nat\<Rightarrow>expType\<Rightarrow>bool" and
isBoundFormula::"state\<Rightarrow>nat \<Rightarrow> nat\<Rightarrow>formula \<Rightarrow> bool" where
"isBoundExp s i M (IVar x) = ( (EX n. x=Ident n) |(EX n. x=Para n i))"|
"isBoundExp s i M (Const c) = True" |
"isBoundExp s i M ( dontCareExp) = False" |
"isBoundExp s i M (iteForm f e1 e2) = 
(( isBoundFormula s i M f) \<and> (isBoundExp s i M e1) \<and> (isBoundExp s i M e2)) " |
"isBoundFormula s i M (eqn e1 e2) = 
 ((isBoundExp s i M e1) \<and> (isBoundExp s i M e2) \<and>
  sameType s e1 e2 \<and> (isIndexVal s e1 \<longrightarrow>(the (scalar2Nat (expEval e1 s))\<le>M 
\<or> the (scalar2Nat (expEval e2 s))\<le>M))) " |
"isBoundFormula s i M (neg f) =  (isBoundFormula s i M f )"  |
"isBoundFormula s i M (andForm f1 f2) = 
  (( isBoundFormula s i M f1) \<and> ( isBoundFormula s i M f2))" |
"isBoundFormula s i M (orForm f1 f2) = 
   (( isBoundFormula s i M f1) \<and> ( isBoundFormula s i M f2)) " |
"isBoundFormula s i M (implyForm f1 f2) =  False " |
"isBoundFormula s i M (chaos) =  True " | 
"isBoundFormula s i M (dontCareForm) =  False " |
"isBoundFormula s i M (forallForm pf N) =  False "

lemma boolExpEvalAbs:"isBoolVal s e1 \<longrightarrow>
expEval e1 s=absTransfConst M (expEval e1 s)"
  apply(case_tac "(expEval e1 s)",auto) done
lemma enumExpEvalAbs:"isEnumVal s e1 \<longrightarrow>
expEval e1 s=absTransfConst M (expEval e1 s)"
  apply(case_tac "(expEval e1 s)",auto) done

lemma indexExpEvalAbsLe:"isIndexVal s e1 \<longrightarrow>
the (scalar2Nat (expEval e1 s))\<le>M \<longrightarrow>
expEval e1 s=absTransfConst M (expEval e1 s)"
  apply(case_tac "(expEval e1 s)",auto) done

lemma indexExpEvalAbsInv:"isIndexVal s e1 \<longrightarrow>
the (scalar2Nat (absTransfConst M (expEval e1 s)))\<le>M \<longrightarrow>
expEval e1 s=absTransfConst M (expEval e1 s)"
apply(case_tac "(expEval e1 s)",auto) done

lemma indexExpEvalAbsGe:"isIndexVal s e1 \<longrightarrow>
the (scalar2Nat ( (expEval e1 s)))>M \<longrightarrow>absTransfConst M (expEval e1 s)=index (M+1)"
  apply(case_tac "(expEval e1 s)",auto)  done

lemma dontCareExpEvalAbsGe:"isDontCareVal s e1 \<longrightarrow>absTransfConst M (expEval e1 s)=dontCare"
  apply(case_tac "(expEval e1 s)",auto) 
  done

lemma dontCareExpEvalAbs:"isDontCareVal s e \<longrightarrow> expEval (absTransfExp  M e) (abs1 M s)=dontCare"
  apply(induct_tac e,auto)
  sorry

primrec safeExp :: "state \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> expType \<Rightarrow> bool" and
  safeFormula :: "state \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> formula \<Rightarrow> bool" where
  "safeExp s i M (IVar x) = ( (EX n. x=Ident n) \<or>(EX n. x=Para n i))"|
  "safeExp s i M (Const c) = True" |
  "safeExp s i M dontCareExp = False" |
  "safeExp s i M (iteForm f e1 e2) =
    (safeFormula s i M f \<and> safeExp s i M e1 \<and> safeExp s i M e2)" |
  "safeFormula s i M (eqn e1 e2) =
    (safeExp s i M e1 \<and> safeExp s i M e2 \<and>
     sameType s e1 e2 \<and> (isIndexVal s e1 \<longrightarrow> (the (scalar2Nat (expEval e1 s)) \<le> M \<or>
                                              the (scalar2Nat (expEval e2 s)) \<le> M))) " |
  "safeFormula s i M (neg f) = safeFormula s i M f" |
  "safeFormula s i M (andForm f1 f2) = False" |
  "safeFormula s i M (orForm f1 f2) = (safeFormula s i M f1 \<and> safeFormula s i M f2) " |
  "safeFormula s i M (implyForm f1 f2) = False" |
  "safeFormula s i M chaos = True" | 
  "safeFormula s i M dontCareForm = False" |
  "safeFormula s i M (forallForm pf N) = False"

lemma absSafeExpFormGe:
   
  shows "(safeExp s i M e \<longrightarrow>i>M\<longrightarrow>(absTransfExp  M e=dontCareExp ) \<or>
  expEval (absTransfExp  M e) (abs1 M s)  =absTransfConst M (expEval e s)) \<and>
  (safeFormula s i M f \<longrightarrow>i>M\<longrightarrow>((absTransfForm  M f=dontCareForm ) \<or>
  (formEval f s =formEval (absTransfForm  M f) (abs1 M s) )))"
   (is "?Pe e s \<and>   ?Pf f s") 
proof(induct_tac e and f)
  fix x
  show "?Pe (IVar x) s"
  proof(case_tac "x")
    fix x1
    assume a1:"x=Ident x1"
    show "?Pe (IVar x) s"
      by auto
  next
  fix x21 x22
    assume a1:"x = Para x21 x22"
    show "?Pe (IVar x) s"
    proof(case_tac "x22 >M")
      assume b1:"x22>M "
      show "?Pe (IVar x) s"
        by(cut_tac  b1 a1,auto)
    next
      assume b1:"~x22>M "
      show "?Pe (IVar x) s"
        by (simp add: local.a1)
      
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
   (* using safeExp.simps(4) by blast*)
  
  proof(rule impI)+
    assume b1:"safeExp s i M (iteForm b e1 e2)" and b2:" M < i" 
    let ?Q="\<lambda>s e. absTransfExp M e = dontCareExp \<or>
    expEval (absTransfExp M e) (abs1 M s) =
     absTransfConst M (expEval e s)"
    let ?R="\<lambda>s f.(absTransfForm  M f=dontCareForm |
  formEval f s =formEval (absTransfForm  M f) (abs1 M s))"
    have b4:"safeFormula s i M b\<and> b\<noteq>dontCareForm"
      using b1 safeExp.simps(4) safeFormula.simps(7) by blast
    have b5:"safeExp s i M e1\<and> e1\<noteq>dontCareExp"
      using b1 safeExp.simps(3) safeExp.simps(4) by blast 
    have b6:"safeExp s i M e2\<and> e2\<noteq>dontCareExp"
      using b1 safeExp.simps(3) safeExp.simps(4) by blast 
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
    b0:"safeFormula s i M (eqn e1 e2) " 
  have b2:"safeExp s i M e1\<and> e1\<noteq>dontCareExp"
    using b0 safeExp.simps(3) safeFormula.simps(1) by blast
  have b3:"safeExp s i M e2\<and> e2\<noteq>dontCareExp"
    using b0 safeExp.simps(3) safeFormula.simps(1) by blast
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
          using b0 c2 safeFormula.simps(1) by blast
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
    formEval (eqn e1 e2) s = formEval (absTransfForm M (eqn e1 e2)) (abs1 M s)"
       by (smt absTransfConst.simps(1) absTransfConst.simps(3) absTransfForm.simps(1) b4 b5 c2 c3 calculation(4) dontCareExpEvalAbsGe evalEqn getValueType.simps(2) isDontCareVal_def isIndexVal_def scalrValueType.exhaust typeOf_def)
   }

   ultimately show c6:"absTransfForm M (eqn e1 e2) = dontCareForm \<or>
    formEval (eqn e1 e2) s = formEval (absTransfForm M (eqn e1 e2)) (abs1 M s)"
     by blast
    
  qed
  show "absTransfForm M (eqn e1 e2) = dontCareForm \<or>
    (formEval (eqn e1 e2) s = formEval (absTransfForm M (eqn e1 e2)) (abs1 M s))"
    using b6 by blast  
qed 
next
  fix f1 f2
  assume a1:"?Pf f1 s" and a2:"?Pf f2 s"
  show "?Pf (andForm f1 f2) s"
    using a2 local.a1 by auto
 (* proof(rule impI)+
    assume b1:"safeFormula s i M (andForm f1 f2)" and
    b2:"M<i"
    have b3:"safeFormula s i M   f1  "
      using b1 safeFormula.simps(3) by blast 
    have b4:"safeFormula s i M   f2  "
      using b1 safeFormula.simps(3) by blast   
    have b5:" absTransfForm M f1 = dontCareForm \<or> 
      formEval f1 s = formEval (absTransfForm M f1) (abs1 M s)"
      using b2 b3 local.a1 by blast
    have b6:" absTransfForm M f2 = dontCareForm \<or> 
      formEval f2 s = formEval (absTransfForm M f2) (abs1 M s)"
      using b2 b4 local.a2 by blast 
    show "absTransfForm M (andForm f1 f2) = dontCareForm \<or>
    formEval (andForm f1 f2) s = formEval (absTransfForm M (andForm f1 f2)) (abs1 M s)"
      apply(cut_tac b5 b6,auto)
  qed
*)
next 
  fix f
  assume a1:"?Pf f s" 
  
   show "?Pf (neg f) s"
     using local.a1 by auto
(*   proof(rule impI)+
     assume b1:"safeFormula s i M (neg f)" and b2:"i \<le>M"
     have b3:"safeFormula s i M f"
       using b1 safeFormula.simps(2) by blast
     let ?R="\<lambda>s f.(absTransfForm  M f\<noteq>dontCareForm \<and>
    absTransfForm M f \<noteq> eqn (Const (index (Suc M))) (Const (index (Suc M))) \<and>
      formEval f s \<longrightarrow>formEval (absTransfForm  M f) (abs1 M s))"  
     have b4:"?R s f"
       using b2 b3 safeFormula.simps(7) local.a1 by blast
     
      
     show "?R s (neg f)"
      by (cut_tac b3 b4,auto) 
      
  qed
*)
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
 

   
lemma absSafeExpFormLe:
  "(safeExp s i M e \<longrightarrow> i \<le> M \<longrightarrow>
    (absTransfExp M e \<noteq> dontCareExp \<and>
     expEval (absTransfExp M e) (abs1 M s) = absTransfConst M (expEval e s))) \<and>

   (safeFormula s i M f \<longrightarrow> i \<le> M \<longrightarrow>
    (absTransfForm M f \<noteq> dontCareForm \<and>
     absTransfForm M f \<noteq> eqn (Const (index (Suc M))) (Const (index (Suc M))) \<and>
     formEval f s = formEval (absTransfForm  M f) (abs1 M s)))"
   (is "?Pe e s \<and> ?Pf f s")  
proof (induct_tac e and f)
  fix x
  show "?Pe (IVar x) s"
  proof(case_tac "x")
    fix x1
    assume a1:"x=Ident x1"
    show "?Pe (IVar x) s"
      by auto
  next
  fix x21 x22
    assume a1:"x = Para x21 x22"
    show "?Pe (IVar x) s"
    proof(case_tac "x22 >M")
      assume b1:"x22>M "
      show "?Pe (IVar x) s"
        by(cut_tac  b1 a1,auto)
    next
      assume b1:"~x22>M "
      show "?Pe (IVar x) s"
        by (simp add: local.a1)
      
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
   (* using safeExp.simps(4) by blast*)
  
  proof(rule impI)+
    assume b1:"safeExp s i M (iteForm b e1 e2)" and b2:" i \<le> M" 
    let ?Q="\<lambda>s e.  (absTransfExp  M e)\<noteq>dontCareExp\<and>
    expEval (absTransfExp M e) (abs1 M s) =
     absTransfConst M (expEval e s)"
    let ?R="\<lambda>s f.( absTransfForm  M f\<noteq>dontCareForm \<and>
  formEval f s =formEval (absTransfForm  M f) (abs1 M s))"
    have b4:"safeFormula s i M b\<and> b\<noteq>dontCareForm"
      using b1 safeExp.simps(4) safeFormula.simps(7) by blast
    have b5:"safeExp s i M e1\<and> e1\<noteq>dontCareExp"
      using b1 safeExp.simps(3) safeExp.simps(4) by blast 
    have b6:"safeExp s i M e2\<and> e2\<noteq>dontCareExp"
      using b1 safeExp.simps(3) safeExp.simps(4) by blast 
    have b7:"?Q s e1"
      using b2 b5 local.a1 by blast
    have b8:"?Q s e2"
      using a2 b2 b6 by blast 
    have b9:"?R s b"
      using a3 b2 b4 by blast
    show "?Q s  (iteForm b e1 e2)"
      apply(cut_tac b7 b8 b9,auto)done
    
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
    b0:"safeFormula s i M (eqn e1 e2) " 
  have b2:"safeExp s i M e1\<and> e1\<noteq>dontCareExp"
    using b0 safeExp.simps(3) safeFormula.simps(1) by blast
  have b3:"safeExp s i M e2\<and> e2\<noteq>dontCareExp"
    using b0 safeExp.simps(3) safeFormula.simps(1) by blast
  let ?Q="\<lambda>s e. absTransfExp M e \<noteq> dontCareExp \<and>
    expEval (absTransfExp M e) (abs1 M s) =
     absTransfConst M (expEval e s)"
  have b4:"?Q s e1"
    using b1 b2 local.a1 by blast 
  have b5:"?Q s e2"
    using a2 b1 b3 by blast
  have b6:   "absTransfForm M (eqn e1 e2) \<noteq> dontCareForm \<and> 
    (absTransfForm  M (eqn e1 e2))\<noteq>eqn (Const (index (Suc M))) (Const (index (Suc M))) \<and>
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
  (absTransfForm  M (eqn e1 e2))\<noteq>eqn (Const (index (Suc M))) (Const (index (Suc M))) \<and>
    formEval (eqn e1 e2) s = formEval (absTransfForm M (eqn e1 e2)) (abs1 M s)"
          by (smt Suc_n_not_le_n absTransfForm.simps(1) b0 b4 b5 c4 c5 evalConst evalEqn formula.distinct(11) 
formula.inject(1) getValueType.simps(2) isIndexVal_def option.sel safeFormula.simps(1) scalar2Nat.simps(1) typeOf_def)
          
         
        
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
  (absTransfForm  M (eqn e1 e2))\<noteq>eqn (Const (index (Suc M))) (Const (index (Suc M))) \<and>
    formEval (eqn e1 e2) s = formEval (absTransfForm M (eqn e1 e2)) (abs1 M s)"
          by (smt Suc_n_not_le_n absTransfForm.simps(1) b0 b4 b5 c4 c5 evalConst evalEqn formula.distinct(11) formula.inject(1) getValueType.simps(2) isIndexVal_def option.sel safeFormula.simps(1) scalar2Nat.simps(1) typeOf_def)
          
         
      }  
      moreover
      {assume c2:"isIndexVal s e1"
        have c3:"isIndexVal s e2"
          using b0 c2 by auto
        have c4:"(the (scalar2Nat (expEval e1 s))\<le>M \<or> the (scalar2Nat (expEval e2 s))\<le>M)"
          using b0 c2 safeFormula.simps(1) by blast
        moreover
        {assume c4:"the (scalar2Nat (expEval e1 s))\<le>M "
        have c5:"absTransfConst M (expEval e1 s) = (expEval e1 s)  "
          using c2 c4 indexExpEvalAbsLe by auto 
        have c6:"absTransfForm M (eqn e1 e2) \<noteq> dontCareForm \<and>
  (absTransfForm  M (eqn e1 e2))\<noteq>eqn (Const (index (Suc M))) (Const (index (Suc M))) \<and>
    formEval (eqn e1 e2) s = formEval (absTransfForm M (eqn e1 e2)) (abs1 M s)"
          by (metis (mono_tags, lifting) Suc_n_not_le_n absTransfForm.simps(1) b4 b5 c3 c4 c5 evalConst evalEqn formula.simps(1) formula.simps(18) indexExpEvalAbsInv option.sel scalar2Nat.simps(1))
         
        (*  apply(cut_tac b0 c2,auto)
          using b4 b5 apply auto[1]
          using b4 b5 c5 indexExpEvalAbsInv apply fastforce
          using b4 b5 apply auto[1]
          using b4 b5 c5 indexExpEvalAbsLe by auto *)
      }  
      moreover
        {assume c4:"the (scalar2Nat (expEval e2 s))\<le>M "
        have c5:"absTransfConst M (expEval e2 s) = (expEval e2 s)  "
          using c3 c4 indexExpEvalAbsLe by auto  
        have "absTransfForm M (eqn e1 e2) \<noteq> dontCareForm \<and>
  (absTransfForm  M (eqn e1 e2))\<noteq>eqn (Const (index (Suc M))) (Const (index (Suc M))) \<and>
        formEval (eqn e1 e2) s = formEval (absTransfForm M (eqn e1 e2)) (abs1 M s)"
          by (metis (mono_tags, lifting) absTransfForm.simps(1) b4 b5 c2 c4 c5 calculation(2) evalEqn formula.distinct(11) formula.inject(1) indexExpEvalAbsInv) 
         
      }  
      ultimately  have "absTransfForm M (eqn e1 e2) \<noteq> dontCareForm \<and>
  (absTransfForm  M (eqn e1 e2))\<noteq>eqn (Const (index (Suc M))) (Const (index (Suc M))) \<and>
        formEval (eqn e1 e2) s = formEval (absTransfForm M (eqn e1 e2)) (abs1 M s)"
        by blast
    }
   moreover
   {assume c2:"isDontCareVal s e1"
     have c3:"isDontCareVal s e2"
       using b0 c2 by auto
     have c6:"absTransfForm M (eqn e1 e2) \<noteq> dontCareForm \<and>
  (absTransfForm  M (eqn e1 e2))\<noteq>eqn (Const (index (Suc M))) (Const (index (Suc M))) \<and>
  (absTransfForm  M (eqn e1 e2))\<noteq>eqn (Const (index (Suc M))) (Const (index (Suc M))) \<and>
        formEval (eqn e1 e2) s = formEval (absTransfForm M (eqn e1 e2)) (abs1 M s)"
     proof -
       have f1: "typeOf s e1 = typeOf s e2"
using b0 safeFormula.simps(1) sameType_def by blast
  have f2: "typeOf s e2 = ''any''"
    by (meson c3 isDontCareVal_def)
    have f3: "absTransfConst M (expEval e2 s) = dontCare"
by (meson c3 dontCareExpEvalAbsGe)
  have f4: "''nat'' \<noteq> ''any''"
    by force
  have f5: "\<forall>s. (\<exists>cs csa. s = enum cs csa) \<or> (\<exists>n. s = index n) \<or> (\<exists>b. s = boolV b) \<or> s = dontCare"
  by (metis (no_types) scalrValueType.exhaust)
  obtain bb :: "scalrValueType \<Rightarrow> bool" where
    f6: "\<forall>x0. (\<exists>v1. x0 = boolV v1) = (x0 = boolV (bb x0))"
    by moura
  obtain ccs :: "scalrValueType \<Rightarrow> char list" and ccsa :: "scalrValueType \<Rightarrow> char list" where
    "\<forall>x0. (\<exists>v1 v2. x0 = enum v1 v2) = (x0 = enum (ccs x0) (ccsa x0))"
    by moura
  then obtain nn :: "scalrValueType \<Rightarrow> nat" where
    f7: "\<forall>s. s = enum (ccs s) (ccsa s) \<or> s = index (nn s) \<or> s = boolV (bb s) \<or> s = dontCare"
    using f6 f5 by moura
  then have f8: "expEval e1 s \<noteq> dontCare \<longrightarrow> expEval e1 s = dontCare"
    using f4 f2 f1 by (metis (no_types) absTransfConst.simps(1) absTransfConst.simps(3) dontCareExpEvalAbsGe getValueType.simps(2) isDontCareVal_def typeOf_def)
  have "expEval e2 s = dontCare"
    using f7 f4 f3 f2 by (metis absTransfConst.simps(1) absTransfConst.simps(3) getValueType.simps(2) typeOf_def)
  then show ?thesis
    using f8 b4 b5 by force
qed
  (*     by (smt absTransfConst.simps(1) absTransfConst.simps(3) absTransfForm.simps(1) b4 b5 c2 c3 calculation(4) dontCareExpEvalAbsGe evalEqn formula.simps(18) getValueType.simps(2) isDontCareVal_def isIndexVal_def scalrValueType.exhaust typeOf_def)
   *)    }

   ultimately show c6:"absTransfForm M (eqn e1 e2) \<noteq> dontCareForm \<and>
  (absTransfForm  M (eqn e1 e2))\<noteq>eqn (Const (index (Suc M))) (Const (index (Suc M))) \<and>
        formEval (eqn e1 e2) s = formEval (absTransfForm M (eqn e1 e2)) (abs1 M s)"
     by blast
    
  qed
  show "absTransfForm M (eqn e1 e2) \<noteq> dontCareForm\<and>
  (absTransfForm  M (eqn e1 e2))\<noteq>eqn (Const (index (Suc M))) (Const (index (Suc M))) \<and>
        formEval (eqn e1 e2) s = formEval (absTransfForm M (eqn e1 e2)) (abs1 M s)"
    using b6 by blast  
qed 
next
  fix f1 f2
  assume a1:"?Pf f1 s" and a2:"?Pf f2 s"
  show "?Pf (andForm f1 f2) s"
    using a2 local.a1 by auto
  
next 
  fix f
  assume a1:"?Pf f s" 
  
  show "?Pf (neg f) s"
    by (simp add: local.a1)
 
    

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

lemma safeFormLe1:
assumes a1:"safeFormula s i M f" and a2:"i\<le> M" 
  shows "( (absTransfForm  M f)\<noteq>dontCareForm \<and>
  (absTransfForm  M f)\<noteq>eqn (Const (index (Suc M))) (Const (index (Suc M))) \<and>
  formEval f s =formEval (absTransfForm  M f) (abs1 M s))"
  using a2 absSafeExpFormLe local.a1 by blast
 
lemma absTopTransBoundForm:
  
  shows "(safeExp s i M e \<longrightarrow>(topTransfExp (absTransfExp  M e)=dontCareExp ) \<or>
  expEval (topTransfExp (absTransfExp  M e)) (abs1 M s)  =
  absTransfConst M (expEval e s)) \<and>
  (safeFormula s i M f \<longrightarrow>
  formEval f s \<longrightarrow>formEval (absTransfForm  M f) (abs1 M s) )"
   (is "?Pe e s \<and>   ?Pf f s") 
  sorry

primrec isBoundAssign :: "state \<Rightarrow> string \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> statement \<Rightarrow> bool" where  
  boundSkip: "isBoundAssign s a i M skip= False" |
  boundAssign: "isBoundAssign s a i M (assign as) =
    (fst as = Para a i \<and> safeExp s i M (snd as))" |
  boundParaLlel: "isBoundAssign s a i M (parallel as S) = False"|
  boundForallStm: "isBoundAssign s a i M (forallStm S n) = False"
 

primrec isGlobalExp::"expType\<Rightarrow>bool" where
  "isGlobalExp (IVar x) = (\<exists>n. x=Ident n)"|
  "isGlobalExp (Const c) = True" |
  "isGlobalExp dontCareExp = False" | 
  "isGlobalExp (iteForm f e1 e2) = False"

 

primrec globalAssignment::"statement \<Rightarrow>bool" where
  "globalAssignment skip = True" |
  "globalAssignment (assign as) = (\<exists>a. fst as = Ident a \<and> isGlobalExp (snd as))" |
  "globalAssignment (parallel as S) = False" |
  "globalAssignment (forallStm ps S) = False"

definition wellDefinedForStatement ::
  "state \<Rightarrow> string \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> statement) \<Rightarrow> statement list \<Rightarrow> bool" where [simp]:
  "wellDefinedForStatement s a N M f SL =
    (SL = map f (down N) \<and> (\<forall>i. isBoundAssign s a i M (f i)))"

definition local :: "(nat \<Rightarrow> formula) \<Rightarrow> nat \<Rightarrow> bool" where
  "local fg M \<equiv> \<forall>i. absTransfForm M (fg i) = dontCareForm"

inductive wellFormedGuard :: "state \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> formula \<Rightarrow> bool" where  
  wellNeg: "\<lbrakk>expEval e1 s = index M; expEval e2 s = index M\<rbrakk> \<Longrightarrow>
             wellFormedGuard s i M N (neg (eqn e1 e2)) "|
  wellBound: "safeFormula s i M g \<Longrightarrow> wellFormedGuard s i M N g" |
  wellForallForm1: "\<forall>i. safeFormula s i M (fg i) \<Longrightarrow> wellFormedGuard s i M N (forallForm fg N)" |
  wellForallForm2: "\<forall>i. safeFormula s i M (fg i) \<Longrightarrow> wellFormedGuard s i M N 
    (forallForm (\<lambda>j. implyForm (neg (eqn (Const (index i)) (Const (index j)))) (fg j)) N)" |
  wellAndForm: "\<lbrakk> wellFormedGuard s i M N g; wellFormedGuard s i M N h\<rbrakk> \<Longrightarrow>
                  wellFormedGuard s i M N (andForm g h)"



lemma wellFormGuardSatImplyItsAbsSat:
  assumes a1:"wellFormedGuard s i M N f" 
  shows "formEval  f s\<longrightarrow> M \<le>N \<longrightarrow>(absTransfForm M f)\<noteq>dontCareForm\<longrightarrow>
  formEval   (absTransfForm M f) (abs1 M s)" (is "?P1 f s") 
  using a1
proof induct
  fix e1 s M e2 i N  
  assume b1:"     expEval e1 s = index M " and b2:"expEval e2 s = index M"
  
  let ?f="neg (eqn e1 e2)"
  show "formEval (neg (eqn e1 e2)) s  \<longrightarrow>M \<le>N\<longrightarrow>
       absTransfForm M (neg (eqn e1 e2)) \<noteq> dontCareForm \<longrightarrow>
       formEval (absTransfForm M (neg (eqn e1 e2))) (abs1 M s)" (*"?P1 ?f s\<longrightarrow>?P2 s \<longrightarrow>?P3 ?f \<longrightarrow>?P4 ?f s"*)
    by (simp add: \<open>expEval e2 s = index M\<close> b1)
next
  fix s i M g N
  assume b1:"safeFormula s i M g" 
  let ?f="g"
  show " formEval g s \<longrightarrow>M \<le>N\<longrightarrow>absTransfForm M g \<noteq> dontCareForm \<longrightarrow>
  formEval (absTransfForm M g) (abs1 M s)"
    apply(case_tac "i\<le>M")
    using absSafeExpFormLe b1 apply blast
    using absSafeExpFormGe b1 not_le by blast 
    

    
next
  fix s M fg i N
  assume b1:"      \<forall>i. safeFormula s i M (fg i)"  
  show "formEval (forallForm fg N) s  \<longrightarrow>  M \<le>N\<longrightarrow>
  absTransfForm M (forallForm fg N) \<noteq> dontCareForm \<longrightarrow>
  formEval (absTransfForm M (forallForm fg N)) (abs1 M s)"
  
  proof(rule impI)+
    assume c1:"formEval (forallForm fg N) s " and c1':"M \<le>N"
    have c2:"(absTransfForm M (forallForm fg N)) = forallForm (\<lambda>i. absTransfForm M (fg i)) M"
      by auto
    have c3:"\<forall>i. i\<le>N \<longrightarrow> formEval ( fg i) s "
      by(cut_tac c1,auto)
     have c4:"\<forall>i. i\<le>M \<longrightarrow> formEval ( fg i) s "
      apply(cut_tac c1' c3,auto) done
     have c5:"\<forall>i. i\<le>M \<longrightarrow> formEval  (absTransfForm M (fg i)) (abs1 M s) "
       using b1 c4 safeFormLe1 by blast
     have c6:"formEval (forallForm (\<lambda>i. absTransfForm M (fg i)) M) (abs1 M s)"
       by (simp add: c5) 
     with c2 show "formEval (absTransfForm M (forallForm fg N)) (abs1 M s)"
       by auto
   qed
next
   fix s M fg i N
  assume b1:"      \<forall>i. safeFormula s i M (fg i)"  
  show " formEval (forallForm (\<lambda>j. implyForm (neg (eqn (Const (index i)) (Const (index j)))) (fg j)) N) s \<longrightarrow>
       M\<le>N \<longrightarrow>absTransfForm M
        (forallForm (\<lambda>j. implyForm (neg (eqn (Const (index i)) (Const (index j)))) (fg j)) N) \<noteq>
       dontCareForm \<longrightarrow>
       formEval
        (absTransfForm M
          (forallForm (\<lambda>j. implyForm (neg (eqn (Const (index i)) (Const (index j)))) (fg j)) N))
        (abs1 M s)"
    sorry
next
  fix s i M N g h
  assume b1:"wellFormedGuard s i M N g" and
  b3:"formEval g s \<longrightarrow>
       M \<le> N \<longrightarrow> absTransfForm M g \<noteq> dontCareForm \<longrightarrow> formEval (absTransfForm M g) (abs1 M s)" and  
  b4:"formEval h s \<longrightarrow>
       M \<le> N \<longrightarrow> absTransfForm M h \<noteq> dontCareForm \<longrightarrow> formEval (absTransfForm M h) (abs1 M s)" and
  b2:"wellFormedGuard s i M N h"
  show "formEval (andForm g h) s \<longrightarrow>
       M \<le> N \<longrightarrow>
       absTransfForm M (andForm g h) \<noteq> dontCareForm \<longrightarrow> 
      formEval (absTransfForm M (andForm g h)) (abs1 M s)"
  proof(rule impI)+
    assume c1:"formEval (andForm g h) s" and
    c2:"M \<le> N" and c3:"absTransfForm M (andForm g h) \<noteq> dontCareForm"

    show "formEval (absTransfForm M (andForm g h)) (abs1 M s)"
      using b3 b4 c1 c2 by auto
  qed
qed
  

lemma absGlobalStatement:
  shows "globalAssignment  S \<longrightarrow> 
  abs1 M (trans1 S s) = trans1 (absTransfStatement M S) (abs1 M s)" (is "?P S")
proof(induct_tac S,simp)
  fix as
  show "?P (assign as)"
  proof
    assume a1:"globalAssignment (assign as)"
    have a2:" (\<exists>a. (fst as) =Ident a \<and> isGlobalExp   (snd as)) "
      by(cut_tac a1,auto)
    then obtain a where a2:"( (fst as) =Ident a \<and> isGlobalExp   (snd as)) "
      by(cut_tac a1,auto)
    show "abs1 M (trans1 (assign as) s) = trans1 (absTransfStatement M (assign as)) (abs1 M s)"
    proof
      fix x
      show "abs1 M (trans1 (assign as) s) x =
         trans1 (absTransfStatement M (assign as)) (abs1 M s) x "
      proof(case_tac "(fst as \<noteq>x)")
        assume b1:"fst as \<noteq> x"
        show "abs1 M (trans1 (assign as) s) x =
         trans1 (absTransfStatement M (assign as)) (abs1 M s) x "
          by(cut_tac b1,auto)
      next
        assume b1:"\<not> fst as \<noteq> x"
        show "abs1 M (trans1 (assign as) s) x =
         trans1 (absTransfStatement M (assign as)) (abs1 M s) x "
        proof -
          have c1:"isGlobalExp (snd as)"
            by (simp add: a2)
            
          have c2:"abs1 M (trans1 (assign as) s) x= 
                  absTransfConst M (expEval  (snd as) s)"
            using a2 b1 by auto
           (* by (metis \<open>\<And>thesis. (\<And>a. fst as = Ident a \<and> isGlobalExp (snd as) \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> absExpForm absTransfExp.simps(2) absTransfVar.simps(1) assms b1 
evalVar expType.distinct(5) isSimpExp.simps(1) trans1.simps(2) varType.distinct(3))*)
          have c3:"trans1 (absTransfStatement M (assign as)) (abs1 M s) x =
               absTransfConst M (expEval  (snd as) s) " 
          proof(case_tac "snd as")
            fix x1
            assume d1:"snd as=IVar x1"
            show "trans1 (absTransfStatement M (assign as)) (abs1 M s) x =
               absTransfConst M (expEval  (snd as) s) "
              using a2 b1 d1 by auto
             (* by (metis a2 absExpForm absTransfExp.simps(2) absTransfStatement.simps(2)
               absTransfVar.simps(1) assms b1 d1 expType.simps(9) isGlobalExp.simps(1)
               isSimpExp.simps(1) prod.exhaust_sel trans1.simps(2) varType.simps(6)) 
              *)
          next  
            fix x2
            assume d1:"snd as=Const x2"
            show "trans1 (absTransfStatement M (assign as)) (abs1 M s) x =
               absTransfConst M (expEval  (snd as) s) "
              using a2 b1 d1 by force
          next
            fix f1 e1 e2
            assume d1:"snd as = iteForm f1 e1 e2"
            show "trans1 (absTransfStatement M (assign as)) (abs1 M s) x =
               absTransfConst M (expEval  (snd as) s)"
              by(cut_tac c1 d1,auto)

          next
            assume d1:"snd as =dontCareExp"
            show "trans1 (absTransfStatement M (assign as)) (abs1 M s) x =
               absTransfConst M (expEval  (snd as) s)"
              by(cut_tac c1 d1,auto)
        
          qed  
          show "abs1 M (trans1 (assign as) s) x = 
          trans1 (absTransfStatement M (assign as)) (abs1 M s) x "
            using c2 c3 by auto
          
      qed
    qed
  qed
qed 
next
  fix S0 S
  show "?P (parallel S0 S)"
    by auto
next
  fix x1 x2a
  show "globalAssignment (forallStm x1 x2a) \<longrightarrow>
       abs1 M (trans1 (forallStm x1 x2a) s) = trans1 (absTransfStatement M (forallStm x1 x2a)) (abs1 M s)"
    by simp
qed
   

lemma absBoundStatement: 
  shows "isBoundAssign s a i M S \<longrightarrow> 
  abs1 M (trans1 S s) = trans1 (absTransfStatement M S) (abs1 M s)" (is "?P S")
proof(induct_tac S,simp)
  fix as
  show "?P (assign as)"
  proof
    assume a1:"isBoundAssign s a i M (assign as)"
    have a2:" ( (fst as) =Para a i\<and> safeExp s i M  (snd as)) "
      apply(cut_tac a1,auto)
      done
    show "abs1 M (trans1 (assign as) s) = trans1 (absTransfStatement M (assign as)) (abs1 M s)"
    proof
      fix x
      show "abs1 M (trans1 (assign as) s) x =
         trans1 (absTransfStatement M (assign as)) (abs1 M s) x "
      proof(case_tac "(fst as \<noteq>x)")
        assume b1:"fst as \<noteq> x"
        show "abs1 M (trans1 (assign as) s) x =
         trans1 (absTransfStatement M (assign as)) (abs1 M s) x "
          by(cut_tac b1,auto)
      next
        assume b1:"\<not> fst as \<noteq> x"
        show "abs1 M (trans1 (assign as) s) x =
         trans1 (absTransfStatement M (assign as)) (abs1 M s) x "
        proof(case_tac "i> M")
           
          assume c1:"i>M"  
          have c2:"abs1 M (trans1 (assign as) s) x= dontCare"
            apply(cut_tac a2 b1 c1,auto) done
          have c3:"trans1 (absTransfStatement M (assign as)) (abs1 M s) x =
               dontCare "
            using a2 b1 c1 by auto 
           
          show "abs1 M (trans1 (assign as) s) x = 
          trans1 (absTransfStatement M (assign as)) (abs1 M s) x "
            using c2 c3 by auto
        next
          assume c1:"~i>M"
          show "abs1 M (trans1 (assign as) s) x = 
          trans1 (absTransfStatement M (assign as)) (abs1 M s) x "
            using c1 a2 apply auto
            by (simp add: absSafeExpFormLe) 
      qed
    qed
  qed
qed 
next
  fix S0 S
  show "?P (parallel S0 S)"
    by auto
next
  fix x1 x2a
  show "isBoundAssign s a i M  (forallStm x1 x2a) \<longrightarrow>
       abs1 M (trans1 (forallStm x1 x2a) s) = trans1 (absTransfStatement M (forallStm x1 x2a)) (abs1 M s)"
    by simp
qed


definition semanticStatementEq::"statement\<Rightarrow>statement \<Rightarrow>bool" where
"semanticStatementEq S1 S2 \<equiv>
  \<forall>s. trans1 S1 s =trans1 S2 s"

definition semanticFormEq::"formula \<Rightarrow> formula \<Rightarrow>bool" where
"semanticFormEq f1 f2 \<equiv>  \<forall>s. formEval f1 s =formEval f2 s"

definition semanticRuleEq::"rule \<Rightarrow>rule \<Rightarrow>bool" where
"semanticRuleEq r1 r2 \<equiv> 
 semanticFormEq (pre r1) (pre r2)\<and> semanticStatementEq (act r1) (act r2)"

lemma semanticStatementEqReflex:
  "semanticStatementEq S S"
  apply(induct_tac S,unfold  semanticStatementEq_def,auto)
  sorry
lemma semanticRuleEqReflex:"semanticRuleEq r r"
  sorry

definition semanticRuleSetEq::"rule set\<Rightarrow>rule set\<Rightarrow>bool" where
"semanticRuleSetEq R1 R2 \<equiv> 
 (\<forall>r1 \<in>R1. \<exists>r2\<in>R2. semanticRuleEq r1 r2) \<and> (\<forall>r2 \<in>R2. \<exists>r1\<in>R1. semanticRuleEq r1 r2) "

lemma forallSubst:
  assumes "\<forall>i.  (PS' i) = absTransfStatement M (PS i)" 
  shows "semanticStatementEq (forallStm PS' M) 
      (forallStm (\<lambda>i. absTransfStatement M (PS i)) M) "
proof(unfold semanticStatementEq_def,rule allI )
  fix s
  show "trans1 (forallStm PS' M) s = trans1 (forallStm (\<lambda>i. absTransfStatement M (PS i)) M) s"
    using assms by presburger
qed

lemma absTransfForallStmUnique:
  assumes a1:"mutualDiffDefinedStm (forallStm pS N) "  and 
  a2:"x \<in> varOfSent (pS i)" and a3:"i\<le>N "
shows "  (leastInd v N  ps)=Some(i)"
  sorry


lemma absTransfForallStmNone:
  assumes a1:"mutualDiffDefinedStm (forallStm pS N) "  and 
  a2:"\<forall>i. i\<le>N \<longrightarrow> x \<notin> varOfSent (pS i)" 
shows " (leastInd v N  ps)=None"
  sorry


lemma absTransfForallStmUnique1:
  assumes a1:"mutualDiffDefinedStm (forallStm pS N) "  and 
  a2:"x \<in> varOfSent (pS i)" and a3:"i\<le>N "
shows "trans1  (forallStm pS N) s  x= trans1 ( pS i) s x"
  sorry

lemma absTransfForallStmNone1:
  assumes a1:"mutualDiffDefinedStm (forallStm pS N) "  and 
  a2:"\<forall>i. i\<le>N \<longrightarrow>x \<notin> varOfSent (pS i)" 
shows "trans1  (forallStm pS N) s  x=  s x"
  sorry

lemma absForallStatement:
  assumes a1:"M\<le>N" and a2:"\<forall>i.  isBoundAssign s a i M (pS i)"
  shows "abs1 M (trans1 (forallStm pS N)  s) =
    (trans1 (absTransfStatement M (forallStm pS N)) ( abs1 M s))"
proof 
  fix x
  have b0:"mutualDiffDefinedStm (forallStm pS N) "
    sorry

   have b0':"mutualDiffDefinedStm (forallStm (\<lambda>i. absTransfStatement M (pS i)) N) "
    sorry
  have b1:"(\<exists>i. x=Para a i) | (\<forall>i. x\<noteq>Para a i)"
    by blast
  moreover
  {assume b1:"\<exists>i. x=Para a i"
    from b1 obtain i where b2:" x=Para a i"
      by blast
    have b3:"i\<le>M \<or>i>M"
      by arith
    moreover
    {assume b3:"i\<le>M"
      have b3':"isBoundAssign s a i M (pS i)"
        using a2 by blast
          
      have b4:"\<exists>e. pS i= (assign ((Para a i), e))"
        apply(cut_tac b3', case_tac "pS i",auto)done

      then obtain e where b4:"pS i= (assign ((Para a i), e))"
        by blast

      have b5:"x \<in> varOfSent (pS i)"
        by (simp add: b2 b4)
        
      have b6:"trans1  (forallStm pS N) s  x= trans1 ( pS i) s x"
        using absTransfForallStmUnique1 b0 b3 b5 local.a1 by auto 

       have b6:"abs1 M (trans1  (forallStm pS N) s)  x= abs1 M (trans1 ( pS i) s) x"
         using b6 by auto 

      have b7:"x\<in> varOfSent (  absTransfStatement M (pS i)  )"
        using b3 b4 b5 by auto

      have b8:"trans1  (forallStm (\<lambda>i. absTransfStatement M (pS i)) N) (abs1 M s)  x= 
        trans1 ( absTransfStatement M (pS i)) (abs1 M s) x"
        using absTransfForallStmUnique1 b0' b3 b7 le_less_trans local.a1 nat_less_le by blast

      
      have b9:"abs1 M (trans1 ( pS i) s) x=trans1 ( absTransfStatement M (pS i)) (abs1 M s) x"
        using absSafeExpFormLe b3 b3' b4 b7 by auto

      have b10:" abs1 M (trans1 (forallStm pS N) s) x = 
      trans1 (absTransfStatement M (forallStm pS N)) (abs1 M s) x"
proof -
  have f1: "M \<le> N"
    using less_or_eq_imp_le local.a1 by blast
  have f2: "x \<in> varOfSent (absTransfStatement M (pS i))"
    using b3 b4 b5 by force
  have "mutualDiffDefinedStm (forallStm (\<lambda>n. absTransfStatement M (pS n)) M)"
    using f1 b0' by force
  then show ?thesis
    using f2 absTransfForallStmUnique1 absTransfStatement.simps(4) b3 b6 b9 by presburger
qed
}
   moreover
   {assume b3:"i>M"

      have b3':"\<forall>i. isBoundAssign s a i M (pS i)"
        using a2 by blast
          
      have b4:"\<forall>i. \<exists>e. pS i= (assign ((Para a i), e))"
        apply(rule allI, cut_tac b3', drule_tac x="i" in spec, case_tac "pS i",auto)done

       

      have b5:" abs1 M (trans1 (forallStm pS N) s) x = dontCare"
        apply(cut_tac b2 b3,auto)done

      
      have b6:"(absTransfStatement M (forallStm pS N)) =
           (forallStm (\<lambda>n. absTransfStatement M (pS n)) M) "
        by auto

      have b7:"x\<notin> varOfSent (   (forallStm (\<lambda>n. absTransfStatement M (pS n)) M)  )"
        by (smt absTransfStatement.simps(2) absTransfVar.simps(2) b2 b3 b4 eqVarSent1 fst_conv le_less_trans less_not_refl3 singletonD varOfSent.simps(1) varType.simps(8))
        
      have b8:"trans1 ((forallStm (\<lambda>n. absTransfStatement M (pS n)) M)) (abs1 M s) x=(abs1 M s) x"
        by (smt absTransfStatement.simps(2) absTransfVar.simps(2) b2 b3 b4 fst_conv trans1.simps(1) trans1.simps(2) trans1.simps(4))

      have b9:"(abs1 M s) x =dontCare"
        by (simp add: b2 b3)
        
      have b10:"trans1 (absTransfStatement M (forallStm pS N)) (abs1 M s) x=dontCare"
        using b8 b9 by auto

      have b11:" abs1 M (trans1 (forallStm pS N) s) x = 
      trans1 (absTransfStatement M (forallStm pS N)) (abs1 M s) x"
        using b10 b5 by auto
    }
    ultimately have " abs1 M (trans1 (forallStm pS N) s) x = 
      trans1 (absTransfStatement M (forallStm pS N)) (abs1 M s) x"
      by blast
  }
  moreover
  {assume b3:"(\<forall>i. x\<noteq>Para a i)"
  have b3':"\<forall>i. isBoundAssign s a i M (pS i)"
        using a2 by blast
          
      have b4:"\<forall>i. \<exists>e. pS i= (assign ((Para a i), e))"
        apply(rule allI, cut_tac b3', drule_tac x="i" in spec, case_tac "pS i",auto)done

       
      have b4':"x \<notin> varOfSent (forallStm pS N)"
        apply(cut_tac b3 b4,auto)
        by (metis prod.sel(1) singletonD varOfSent.simps(1))
        
      have b5:" abs1 M (trans1 (forallStm pS N) s) x = abs1 M s x"
        by (metis (full_types) abs1_def absTransfForallStmNone1 b0 b4' eqVarSent1)

       
      
      have b6:"(absTransfStatement M (forallStm pS N)) =
           (forallStm (\<lambda>n. absTransfStatement M (pS n)) M) "
        by auto

      have b7:"x\<notin> varOfSent (   (forallStm (\<lambda>n. absTransfStatement M (pS n)) M)  )"
        by (smt absTransfStatement.simps(2) absTransfVar.simps(2) b4 b4' eqVarSent1 less_imp_le_nat local.a1 not_le order.trans prod.sel(1) varOfSent.simps(1) varType.simps(8))
          
      have b8:"trans1 ((forallStm (\<lambda>n. absTransfStatement M (pS n)) M)) (abs1 M s) x=(abs1 M s) x"
        by (smt absTransfStatement.simps(2) b4 b5 b6 calculation(2) fst_conv trans1.simps(1) trans1.simps(2) trans1.simps(4))
       
       

      have b11:" abs1 M (trans1 (forallStm pS N) s) x = 
      trans1 (absTransfStatement M (forallStm pS N)) (abs1 M s) x"
        using b8 b5 by auto      
    }
ultimately show " abs1 M (trans1 (forallStm pS N) s) x = 
      trans1 (absTransfStatement M (forallStm pS N)) (abs1 M s) x"
  by blast
qed


inductive wellFormedParallel :: "state \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> statement \<Rightarrow> bool" where
  wellGlobal: "globalAssignment S \<Longrightarrow> wellFormedParallel s i M N S" |
  wellForall: "\<forall>i. isBoundAssign s a i M (fs i) \<Longrightarrow> wellFormedParallel s i M N (forallStm fs N)" |
  wellAssign: "isBoundAssign s a i M S' \<Longrightarrow> wellFormedParallel s i M N S'" |
  wellParallel: "\<lbrakk>wellFormedParallel s i M N S1; wellFormedParallel s i M N S2;
                  varOfSent S1 \<inter> varOfSent S2 = {}\<rbrakk>\<Longrightarrow>
                  wellFormedParallel s i M N (parallel S1 S2)"

primrec boundIn :: "nat \<Rightarrow> statement \<Rightarrow> bool" where
  "boundIn M skip = True" |
  "boundIn M (assign as) = True" |
  "boundIn M (parallel as S) = (boundIn M as \<and> boundIn M S)" |
  "boundIn M (forallStm PS N) = (M \<le> N)" 

lemma varAbsKeep:
  shows "boundIn M S1\<longrightarrow>x\<notin>varOfSent S1 \<longrightarrow>x\<notin>varOfSent (absTransfStatement M S1)"
  apply (induct_tac S1,simp,simp,simp)
  sorry

lemma parallelAbs1:
  assumes a1:"(varOfSent S1) \<inter>  (varOfSent S2)={}" and
  a2:"x\<in>varOfSent S1" and a3:"boundIn M S1"
shows "trans1 (absTransfStatement M (parallel S1 S2)) s=
  trans1 (absTransfStatement M ( S1 )) s"
  sorry

lemma absWellParallelStatement:
  assumes  a2:" wellFormedParallel s i M N S  "
  shows "boundIn M S \<longrightarrow>M\<le>N \<longrightarrow>abs1 M (trans1 S  s) =
    (trans1 (absTransfStatement M S) ( abs1 M s))" (is "?P S")
  using a2
proof induct
  fix S s i M N
  assume b1:" globalAssignment S "
  show "boundIn M S \<longrightarrow>M\<le>N\<longrightarrow>abs1 M (trans1 S s) = trans1 (absTransfStatement M S) (abs1 M s)"
    by (simp add: absGlobalStatement b1)
next
  fix s a M fs i N
  assume b1:"     \<forall>i. isBoundAssign s a i M (fs i)"
  show "boundIn M (forallStm fs N) \<longrightarrow> M\<le>N\<longrightarrow>abs1 M (trans1 (forallStm fs N) s) = 
  trans1 (absTransfStatement M (forallStm fs N)) (abs1 M s)"
    using absForallStatement b1 by blast
next
  fix s a i M S' N
  assume b1:"     isBoundAssign s a i M S'" 
  show   "boundIn M S'\<longrightarrow>M\<le>N\<longrightarrow> abs1 M (trans1 S' s) = trans1 (absTransfStatement M S') (abs1 M s)"
    using absBoundStatement b1 by blast 
next
  fix s i M N S1 S2
  assume b1:"boundIn M S1 \<longrightarrow>M\<le>N \<longrightarrow> abs1 M (trans1 S1 s) = trans1 (absTransfStatement M S1) (abs1 M s)"
  and b2:" boundIn M S2 \<longrightarrow> M\<le>N \<longrightarrow> abs1 M (trans1 S2 s) = trans1 (absTransfStatement M S2) (abs1 M s)"
  and b3:" varOfSent S1 \<inter> varOfSent S2 = {}" and 
  b4:" wellFormedParallel s i M N S1" and
  b5:" wellFormedParallel s i M N S2"
  show "boundIn M (parallel S1 S2)\<longrightarrow>M\<le>N \<longrightarrow>
       abs1 M (trans1 (parallel S1 S2) s) = trans1 (absTransfStatement M (parallel S1 S2)) (abs1 M s)"
  proof(rule impI)+
    assume c1:"M\<le>N" and c0:"boundIn M (parallel S1 S2)"
    show "abs1 M (trans1 (parallel S1 S2) s) = trans1 (absTransfStatement M (parallel S1 S2)) (abs1 M s)"
    proof
      fix x
      show "abs1 M (trans1 (parallel S1 S2) s) x=
       trans1 (absTransfStatement M (parallel S1 S2)) (abs1 M s) x"
      proof - 
        have c2:"x \<in> varOfSent S1 | x \<notin> varOfSent S1"
          by blast
        moreover
        {assume c2:"x \<in> varOfSent S1"
          have c3:"(trans1 (parallel S1 S2) s) x=trans1 S1 s x"
            by (simp add: c2)
          have c4':"boundIn M S1"
            using boundIn.simps(3) c0 by blast 
          have c4:"abs1 M (trans1   S1   s) x =  
            trans1 (absTransfStatement M ( S1 )) (abs1 M s)  x"
            by (simp add: b1 c1 c4')
          have  c5:"trans1 (absTransfStatement M (parallel S1 S2)) s=
              trans1 (absTransfStatement M ( S1 )) s "
            using b3 c2 c4' parallelAbs1 by auto

          have c6:"abs1 M (trans1 (parallel S1 S2) s) x = abs1 M (trans1 S1 s) x"
            using c3 by auto
            
          have c7:"abs1 M (trans1 (parallel S1 S2) s) x = 
              trans1 (absTransfStatement M (parallel S1 S2)) (abs1 M s) x "
            using b3 c2 c4 c4' c6 parallelAbs1 by auto  
        }
         moreover
        {assume c2:"x \<notin>varOfSent S1"
          have c3:"(trans1 (parallel S1 S2) s) x=trans1 S2 s x"
            by (simp add: c2)
          have c6:"abs1 M (trans1 (parallel S1 S2) s) x = abs1 M (trans1 S2 s) x"
            using c3 by auto
          have c4':"boundIn M S2"
            using boundIn.simps(3) c0 by blast 
          have c4:"abs1 M (trans1   S2   s) x =  
            trans1 (absTransfStatement M ( S2 )) (abs1 M s)  x"
            by (simp add: b2 c1 c4')
          have c41:"boundIn M S1"
              using boundIn.simps(3) c0 by blast
          have c5':"x \<notin>varOfSent (absTransfStatement M S1)"
            by (simp add: c2 c41 varAbsKeep)
            
          have  c5:"trans1 (absTransfStatement M (parallel S1 S2)) s x=
              trans1 (absTransfStatement M ( S2 )) s x"
            apply(cut_tac c5',auto)done

           have c7:"abs1 M (trans1 (parallel S1 S2) s) x = 
              trans1 (absTransfStatement M (parallel S1 S2)) (abs1 M s) x "
             using c4 c5' c6 by auto
         }
         ultimately show "abs1 M (trans1 (parallel S1 S2) s) x = 
              trans1 (absTransfStatement M (parallel S1 S2)) (abs1 M s) x "
           by blast
       qed
     qed
   qed
 qed
            

lemma absRuleSim: 
  assumes a2: "wellFormedGuard s i M N (pre r)"
    and a3: "wellFormedParallel s i M N (act r)"
    and a4: "boundIn M (act r)"
    and a5: "M \<le> N"
  shows "trans_sim_on1 r (absTransfRule M r) M s"
proof(unfold trans_sim_on1_def,(rule impI)+,case_tac r,simp)
  fix g a
  assume b1:"r=guard g a" and b2:"formEval g s "
  have "absTransfForm M g=dontCareForm | absTransfForm M g\<noteq>dontCareForm"
    by auto
  moreover
  {assume b2:"absTransfForm M g=dontCareForm"
    have b3:"formEval (topTransfForm (absTransfForm M g)) (abs1 M s)"
      by (simp add: b2 topTransfForm_def)
  }   
  moreover
  {assume b21:"absTransfForm M g\<noteq>dontCareForm" 
    have b3:"formEval (topTransfForm (absTransfForm M g)) (abs1 M s)"
      
      using a2 a5 b1 b2 topTransfForm_def wellFormGuardSatImplyItsAbsSat by auto
  }   
  ultimately have b4:"formEval (topTransfForm (absTransfForm M g)) (abs1 M s)"
    by blast
  have b5:"wellFormedParallel s i M N a"
    by(cut_tac b1 a3, simp)
  have b6:" abs1 M (trans1 a s) = trans1 (absTransfStatement M a) (abs1 M s)"
    using a4 a5 absWellParallelStatement b1 b5 by auto
  show "formEval (topTransfForm (absTransfForm M g)) (abs1 M s) \<and>
       abs1 M (trans1 a s) = trans1 (absTransfStatement M a) (abs1 M s)"
    using b4 b6 by blast
qed
    
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

      have c9a:"trans1 (act r' ) (applySym2State p s0) = 
        trans1 (act (applySym2Rule p r)) (applySym2State p s0)"
        using c3 c7 c7a  sorry

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
    "\<forall>s . s \<in> reachableSetUpTo (andList fs) rs i \<longrightarrow> formEval (applySym2Form p f) s" (is "?P i")
proof ((rule allI)+,rule impI)
  fix s i
  assume b1:"s \<in> reachableSetUpTo (andList fs) rs i "
  show  "formEval (applySym2Form p f) s "
  proof -
    have c1:"s= applySym2State ( p) (applySym2State (inv p) s)"
      using a4 permutes_bij by fastforce

    have c2:"(inv p) permutes {x.   x \<le> N}"
      using a4 permutes_inv by auto
      
    have c3:"(applySym2State (inv p) s) \<in> reachableSetUpTo (andList fs) rs i"
      using a1 a2 b1 c2 reachSymLemma' by blast

    have c4:"formEval f (applySym2State (inv p) s)"
      using a3 c3 by blast
    show    "formEval (applySym2Form p f) s "
      by (metis a4 c1 c4 stFormSymCorrespondence)
  qed
qed


theorem symProtRulesUnion:
  assumes a1:"symProtRules' N A" and a2:"symProtRules' N B"
  shows "symProtRules' N (A \<union> B)"
  by (metis UnCI UnE a2 local.a1 symProtRules'_def)


end
