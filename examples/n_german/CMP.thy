theory CMP
  imports Main "HOL-Library.Permutations"
begin

subsection \<open>Datatypes for variables, values, expressions, and formulas\<close>

text \<open>
  Two kinds of variables are used in the protocols:
  1. simple identifiers to define global variables 
  2. array variables ---- arr[i]
\<close>
datatype varType =
  Ident string | Para string nat | dontCareVar

text \<open>
  Three kinds of values used in the protocols.
  1. enumerating values
  2. natural numbers 
  3. Boolean values
\<close>
datatype scalrValueType =
  enum string string | index nat | boolV bool | dontCare

text \<open>
  $Expressions$ and $formulas$ are defined mutually recursively.
  $Expressions$ can be simple or compound. 
  A simple expression is either a variable or a constant, 
  while a compound expression is constructed with the ite (if-then-else) form. 
  A $formula$ can be an atomic formula or a compound formula.
  An atomic formula can be a boolean variable or constant, 
  or in the equivalence forms. A $formula$ can also be constructed by 
  using the logic connectives, including negation, conjunction, 
  disjunction, implication.
\<close>
datatype expType =
  IVar varType |
  Const scalrValueType |
  iteForm formula expType expType |
  dontCareExp

and formula =
  eqn expType expType     (infixl "=\<^sub>f" 50) |
  andForm formula formula (infixr "\<and>\<^sub>f" 35) |
  neg formula             ("\<not>\<^sub>f _" [40] 40) |
  orForm formula formula  (infixr "\<or>\<^sub>f" 30) |
  implyForm formula formula  (infixr "\<longrightarrow>\<^sub>f" 25) |
  forallForm "nat \<Rightarrow> formula" nat (binder "\<forall>\<^sub>f" 10) |
  chaos |
  dontCareForm


subsection \<open>Datatypes for assignments, statements, and rules\<close>

text \<open>
  A statement is just a lists of assignments,
  but these assignments are executed in parallel, 
  \emph{not} in a sequential order
\<close>
type_synonym assignType = "varType \<times> expType"

datatype statement =
  skip |
  assign assignType |
  parallel statement statement |
  forallStm "nat \<Rightarrow> statement" nat


text \<open>
  A parameterized statement is just a function from a
  parameter to a statement.
\<close>
type_synonym paraStatement = "nat \<Rightarrow> statement"

text \<open>
  Similarly, a parameterized formula is a function from
  a parameter to a formula.
\<close>
type_synonym paraFormula = "nat \<Rightarrow> formula"


text \<open>
  With the formalizatiion of formula and statement,
  it is natural to define a rule.
\<close>
datatype rule = guard formula statement

fun pre :: "rule \<Rightarrow> formula" where
  "pre (guard f a) = f"

fun act :: "rule \<Rightarrow> statement" where
  "act (guard f a) = a"

text \<open>A parameterized rule is just from a natural number to a rule.\<close>
type_synonym paraRule = "nat \<Rightarrow> rule"


subsection \<open>Semantics of a protocol\<close>

text \<open>
  A state of a protocol is an instantaneous snapshot of its
  behaviour given by an assignment of values to variables of
  the protocol.
\<close>
type_synonym state = "varType \<Rightarrow> scalrValueType"

text \<open>
  The formal semantics of an expression and a formula is 
  formalized as follows:
\<close>
primrec expEval :: "expType \<Rightarrow> state \<Rightarrow> scalrValueType" and
        formEval :: "formula \<Rightarrow> state \<Rightarrow> bool" where
  evalVar:    "expEval (IVar ie) s = s ie" |
  evalConst:  "expEval (Const i) s = i" |
  evalITE:    "expEval (iteForm f e1 e2) s = (if formEval f s then expEval e1 s else expEval e2 s)" |
  evalDontCareExp: "expEval (dontCareExp) s = dontCare" |

  evalEqn:    "formEval (eqn e1 e2) s = (expEval e1 s = expEval e2 s)" |
  evalAnd:    "formEval (andForm f1 f2) s = (formEval f1 s \<and> formEval f2 s)" |
  evalNeg:    "formEval (neg f1) s = (\<not>formEval f1 s)" |
  evalOr:     "formEval (orForm f1 f2) s = (formEval f1 s \<or> formEval f2 s)" |
  evalImp:    "formEval (implyForm f1 f2) s = (formEval f1 s \<longrightarrow> formEval f2 s)" |
  evalForall: "formEval (forallForm ffun N) s = (\<forall>i\<le>N. formEval (ffun i) s)"|
  evalChaos:  "formEval chaos s = True" |
  evalDontCareForm: "formEval dontCareForm s = True"

primrec varOfSent :: "statement \<Rightarrow> varType set" where
  "varOfSent skip = {}" |
  "varOfSent (assign a) = {fst a}" |
  "varOfSent (parallel S1 S2) = varOfSent S1 \<union> varOfSent S2" |
  "varOfSent (forallStm ps N) = \<Union>{S. \<exists>i. i \<le> N \<and> S = varOfSent (ps i)}"

declare varOfSent.simps [simp del]

lemma varOfSentEq:
  "v \<in> varOfSent (forallStm ps N) \<longleftrightarrow> (\<exists>i. i \<le> N \<and> v \<in> varOfSent (ps i))"
  by (auto simp add: varOfSent.simps)

primrec mutualDiffDefinedStm :: "statement \<Rightarrow> bool" where
  "mutualDiffDefinedStm skip \<longleftrightarrow> True" |
  "mutualDiffDefinedStm (assign as) \<longleftrightarrow> True"|
  "mutualDiffDefinedStm (parallel P0 P1) \<longleftrightarrow> mutualDiffDefinedStm P0 \<and> mutualDiffDefinedStm P1 \<and>
    varOfSent P0 \<inter> varOfSent P1 = {}" |
  "mutualDiffDefinedStm (forallStm ps N) \<longleftrightarrow>
    (\<forall>i j. i\<le>N \<longrightarrow> j\<le>N \<longrightarrow> i\<noteq>j \<longrightarrow> varOfSent (ps i) \<inter> varOfSent (ps j) = {}) \<and>
    (\<forall>i. i\<le>N \<longrightarrow> mutualDiffDefinedStm (ps i))"

primrec leastInd :: "varType \<Rightarrow> nat \<Rightarrow> paraStatement \<Rightarrow> nat option" where
  "leastInd v 0 ps = (if v \<in> varOfSent (ps 0) then Some 0 else None)" |
  "leastInd v (Suc N) ps = (if v \<in> varOfSent (ps (Suc N)) then Some (Suc N) else leastInd v N ps)"

lemma leastIndNone:
  "leastInd v N ps = None \<longleftrightarrow> (\<forall>i\<le>N. v \<notin> varOfSent (ps i))"
  apply (induct N) apply auto
  by (metis le_Suc_eq)

lemma leastIndSome:
  "leastInd v N ps = Some i \<longleftrightarrow> i \<le> N \<and> v \<in> varOfSent (ps i) \<and> (\<forall>j\<le>N. j > i \<longrightarrow> v \<notin> varOfSent (ps j))"
proof (induct N)
  case 0
  then show ?case by auto
next
  case (Suc N)
  show ?case
    apply (rule iffI)
     apply (metis Suc.hyps leD le_Suc_eq leastInd.simps(2) option.inject)
    using Suc.hyps antisym_conv2 le_Suc_eq by auto
qed

primrec trans1 :: "statement \<Rightarrow> state \<Rightarrow> state" where
  "trans1 skip s v = s v" |
  "trans1 (assign as) s v = (if fst as = v then expEval (snd as) s else s v)" |
  "trans1 (parallel S1 S2) s v = (if v \<in> varOfSent S1 then trans1 S1 s v else trans1 S2 s v)"|
  "trans1 (forallStm ps N) s v = (case leastInd v N ps of None \<Rightarrow> s v
                                                        | Some i \<Rightarrow> trans1 (ps i) s v)"

subsection \<open>Permutations\<close>

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
  "applySym2Var f (Para nm i) = Para nm (f i)" |
  "applySym2Var f dontCareVar = dontCareVar"

lemma applySym2VarInv [simp]:
  assumes "bij p"
  shows "applySym2Var p (applySym2Var (inv p) v) = v"
proof (cases v)
  case (Ident nm)
  then show ?thesis
    using assms bij_is_surj surj_iff_all by fastforce
next
  case (Para nm i)
  then show ?thesis
    using assms bij_betw_inv_into_right by fastforce 
qed (auto)


primrec applySym2Exp :: "nat2nat \<Rightarrow> expType \<Rightarrow> expType"
  and
  applySym2Form :: "nat2nat \<Rightarrow> formula \<Rightarrow> formula" where

  "applySym2Exp f (IVar v) = IVar (applySym2Var f v)" |
  "applySym2Exp f (Const c) = Const (applySym2Const f c)" |
  "applySym2Exp f (iteForm f1 e1 e2) = iteForm (applySym2Form f f1) (applySym2Exp f e1) (applySym2Exp f e2)" |
  "applySym2Exp f dontCareExp = dontCareExp" | 
  "applySym2Form f (eqn l r) = eqn (applySym2Exp f l) (applySym2Exp f r)" |
  "applySym2Form f (andForm f1 f2) = andForm (applySym2Form f f1) (applySym2Form f f2)" |
  "applySym2Form f (neg f1) = neg (applySym2Form f f1)" |
  "applySym2Form f (orForm f1 f2) = orForm (applySym2Form f f1) (applySym2Form f f2)" |
  "applySym2Form f (implyForm f1 f2) = implyForm (applySym2Form f f1) (applySym2Form f f2)" |
  "applySym2Form f (forallForm fp N) = forallForm (\<lambda>i. applySym2Form f (fp i)) N" |
  "applySym2Form f dontCareForm = dontCareForm" | 
  "applySym2Form f chaos = chaos"

lemma applySym2ExpFormInv [simp]:
  assumes "bij p"
  shows "applySym2Exp p (applySym2Exp (inv p) e) = e \<and>
         applySym2Form p (applySym2Form (inv p) f) = f"
  apply (induction rule: expType_formula.induct)
  by (auto simp add: assms)


primrec applySym2Statement :: "nat2nat \<Rightarrow> statement \<Rightarrow> statement" where
  "applySym2Statement f skip = skip"
| "applySym2Statement f (assign as) = assign (applySym2Var f (fst as), applySym2Exp f (snd as))"
| "applySym2Statement f (parallel S1 S2) =
    parallel (applySym2Statement f S1) (applySym2Statement f S2)"
| "applySym2Statement f (forallStm ps N) = forallStm (\<lambda>i. applySym2Statement f (ps i)) N"

lemma applySym2statementInv[simp]:
  assumes "bij p"
  shows "applySym2Statement p (applySym2Statement (inv p) S) = S" (is "?P S")
  apply (induction S) by (auto simp add: assms)

primrec applySym2Rule :: "nat2nat \<Rightarrow> rule \<Rightarrow> rule" where
  "applySym2Rule p (guard g a) = guard (applySym2Form p g) (applySym2Statement p a)"

text \<open>Applying a permutation to a state\<close>
fun applySym2State :: "nat2nat \<Rightarrow> state \<Rightarrow> state" where
  "applySym2State p s (Ident sn) = applySym2Const p (s (Ident sn))" |
  "applySym2State p s (Para sn i) = applySym2Const p (s (Para sn ((inv p) i)))"|
  "applySym2State p s dontCareVar = applySym2Const p (s dontCareVar)"

lemma applySym2StateInv [simp]:
  assumes "bij p"
  shows "applySym2State p (applySym2State (inv p) s) v = s v"
proof (induction v)
  case (Ident nm)
  then show ?case by (auto simp add: assms)
next
  case (Para nm i)
  then show ?case
    by (simp add: assms bij_is_surj surj_imp_inj_inv)
next
  case dontCareVar
  then show ?case by (auto simp add: assms)
qed

lemma stFormSymCorrespondence:
  assumes "p permutes {x. x \<le> N}"
  shows "expEval (applySym2Exp p e) (applySym2State p s) = applySym2Const p (expEval e s) \<and>
         formEval (applySym2Form p f) (applySym2State p s) = formEval f s"
proof (induction rule: expType_formula.induct)
  case (IVar x)
  have "bij p"
    using assms by (simp add: permutes_bij)
  then show ?case
    apply (cases x)
    by (auto simp add: bijection.intro bijection.inv_left)
next
  case (eqn x1 x2)
  have "bij p"
    using assms by (simp add: permutes_bij)
  show ?case by (auto simp add: eqn \<open>bij p\<close>)
qed (auto)

lemma stFormSymCorrespondence1:
  assumes "p permutes {x. x \<le> N}"
  shows "expEval (applySym2Exp p e) (applySym2State p s) = applySym2Const p (expEval e s)"
        "formEval (applySym2Form p f) (applySym2State p s) = formEval f s"
  using stFormSymCorrespondence assms by auto

lemma stFormSymCorrespondence2:
  assumes "p permutes {x. x \<le> N}"
  shows "expEval e (applySym2State p s) = applySym2Const p (expEval (applySym2Exp (inv p) e) s)"
        "formEval f (applySym2State p s) = formEval (applySym2Form (inv p) f) s"
proof -
  have "bij p"
    using assms permutes_bij by auto
  show "expEval e (applySym2State p s) = applySym2Const p (expEval (applySym2Exp (inv p) e) s)"
    unfolding stFormSymCorrespondence1(1)[OF assms,symmetric]
    using \<open>bij p\<close> by auto
  show "formEval f (applySym2State p s) = formEval (applySym2Form (inv p) f) s"
    unfolding stFormSymCorrespondence1(2)[OF assms, of "applySym2Form (inv p) f", symmetric]
    using \<open>bij p\<close> by auto
qed

lemma stFormSymCorrespondence3:
  assumes "p permutes {x. x \<le> N}"
  shows "expEval e (applySym2State (inv p) s) = applySym2Const (inv p) (expEval (applySym2Exp p e) s)"
        "formEval f (applySym2State (inv p) s) = formEval (applySym2Form p f) s"
proof -
  have a: "(inv p) permutes {x. x \<le> N}"
    by (simp add: assms permutes_inv)
  have b: "bij p"
    using assms permutes_bij by auto
  then have c: "inv (inv p) = p"
    using inv_inv_eq by auto
  show "expEval e (applySym2State (inv p) s) = applySym2Const (inv p) (expEval (applySym2Exp p e) s)"
    using stFormSymCorrespondence2(1)[OF a] c by auto
  show "formEval f (applySym2State (inv p) s) = formEval (applySym2Form p f) s"
    using stFormSymCorrespondence2(2)[OF a] c by auto
qed

lemma varOfSentApplySym2Statement [simp]:
  "varOfSent (applySym2Statement p S) = (applySym2Var p) ` (varOfSent S)"
  apply (induction S) by (auto simp add: varOfSent.simps)

lemma applySym2VarEq:
  assumes "p permutes {x. x \<le> N}"
  shows
    "applySym2Var p v = Ident x \<Longrightarrow> v = Ident x"
    "applySym2Var p v = Para nm i \<Longrightarrow> v = Para nm (inv p i)"
    "applySym2Var p v = dontCareVar \<Longrightarrow> v = dontCareVar"
proof -
  have "bij p"
    using assms by (auto simp add: permutes_bij)
  show "applySym2Var p v = Para nm i \<Longrightarrow> v = Para nm (inv p i)"
    apply (cases v)
    by (auto simp add: \<open>bij p\<close> bij_inv_eq_iff)
qed (cases v, auto)+


lemma trans1Symmetric:
  assumes "p permutes {x. x \<le> N}"
  shows "applySym2State p (trans1 S s0) = trans1 (applySym2Statement p S) (applySym2State p s0)"
proof (induction S)
  case skip
  then show ?case by auto
next
  case (assign x)
  have "applySym2State p (trans1 (assign x) s0) v =
        trans1 (applySym2Statement p (assign x)) (applySym2State p s0) v" for v
  proof (cases v)
    case (Ident x1)
    show ?thesis
      by (simp add: Ident applySym2VarEq(1)[OF assms] stFormSymCorrespondence[OF assms])
  next
    case (Para x21 x22)
    have "bij p"
      using assms by (auto simp add: permutes_bij)
    have *: "p (inv p x22) = x22"
      by (meson \<open>bij p\<close> bij_inv_eq_iff)
    show ?thesis
      by (auto simp add: Para * applySym2VarEq(2)[OF assms] stFormSymCorrespondence[OF assms])
  next
    case dontCareVar
    show ?thesis
      by (simp add: dontCareVar applySym2VarEq(3)[OF assms] stFormSymCorrespondence[OF assms])
  qed
  then show ?case
    by (rule ext)
next
  case (parallel S1 S2)
  have "applySym2State p (trans1 (parallel S1 S2) s0) v =
        trans1 (applySym2Statement p (parallel S1 S2)) (applySym2State p s0) v" for v
  proof (cases v)
    case dontCareVar
    have 1: "dontCareVar \<in> applySym2Var p ` varOfSent S1 \<longleftrightarrow> dontCareVar \<in> varOfSent S1"
      apply (auto simp add: applySym2VarEq(1)[OF assms])
       apply (metis (full_types) applySym2Var.simps(1,2) varType.distinct(5) varType.exhaust)
      by force
    show ?thesis
      by (auto simp add: dontCareVar 1 parallel[symmetric])
  next    
    case (Ident x)
    have 1: "Ident x \<in> applySym2Var p ` varOfSent S1 \<longleftrightarrow> Ident x \<in> varOfSent S1"
      apply (auto simp add: applySym2VarEq(3)[OF assms])
       apply (metis (full_types) applySym2Var.simps varType.distinct(1) varType.exhaust)
      by force
    show ?thesis
      by (auto simp add: Ident 1 parallel[symmetric])
  next
    case (Para nm i)
    have "bij p"
      using assms by (auto simp add: permutes_bij)
    have *: "inv p (p x) = x" for x
      by (simp add: \<open>bij p\<close> bij_is_inj)
    have **: "p (inv p x) = x" for x
      by (meson \<open>bij p\<close> bij_inv_eq_iff)
    have 1: "Para nm i \<in> applySym2Var p ` varOfSent S1 \<longleftrightarrow> Para nm (inv p i) \<in> varOfSent S1"
      apply (auto simp add: applySym2VarEq(2)[OF assms])
      subgoal for x apply (cases x) by (auto simp add: *)
      by (metis "**" applySym2Var.simps(2) image_iff)
    show ?thesis
      by (auto simp add: Para 1 parallel[symmetric])
  qed
  then show ?case
    by (rule ext)
next
  case (forallStm ps N)
  have "applySym2State p (trans1 (forallStm ps N) s0) v =
        trans1 (applySym2Statement p (forallStm ps N)) (applySym2State p s0) v" for v
  proof (cases v)
    case (Ident x)
    have 1: "Ident x \<in> applySym2Var p ` varOfSent (ps i) \<longleftrightarrow> Ident x \<in> varOfSent (ps i)" for i
      apply (auto simp add: applySym2VarEq(3)[OF assms])
       apply (metis (full_types) applySym2Var.simps varType.distinct(1) varType.exhaust)
      by force
    have 2: "leastInd (Ident x) N ps = None \<longleftrightarrow> leastInd (Ident x) N (\<lambda>i. applySym2Statement p (ps i)) = None"
      by (simp add: leastIndNone 1)
    have 3: "leastInd (Ident x) N ps = Some i \<longleftrightarrow> leastInd (Ident x) N (\<lambda>i. applySym2Statement p (ps i)) = Some i" for i
      by (simp add: leastIndSome 1)
    show ?thesis
      apply (auto simp add: Ident)
      apply (cases "leastInd (Ident x) N ps")
      subgoal using 2 by auto
      subgoal for i using 3[of i]
        by (auto simp add: forallStm[symmetric])
      done
  next
    case (Para nm i)
    have "bij p"
      using assms by (auto simp add: permutes_bij)
    have *: "inv p (p x) = x" for x
      by (simp add: \<open>bij p\<close> bij_is_inj)
    have **: "p (inv p x) = x" for x
      by (meson \<open>bij p\<close> bij_inv_eq_iff)
    have 1: "Para nm i \<in> applySym2Var p ` varOfSent (ps i) \<longleftrightarrow> Para nm (inv p i) \<in> varOfSent (ps i)"
      apply (auto simp add: applySym2VarEq(2)[OF assms])
      subgoal for x apply (cases x) by (auto simp add: *)
      by (metis "**" applySym2Var.simps(2) image_iff)
    have 2: "leastInd (Para nm (inv p i)) N ps = None \<longleftrightarrow> leastInd (Para nm i) N (\<lambda>i. applySym2Statement p (ps i)) = None"
      apply (auto simp add: leastIndNone)
       apply (metis \<open>bij p\<close> applySym2Var.simps(2) applySym2VarInv bij_betw_inv_into inv_inv_eq)
      by (metis "**" applySym2Var.simps(2) image_iff)
    have 3: "leastInd (Para nm (inv p i)) N ps = Some j \<longleftrightarrow> leastInd (Para nm i) N (\<lambda>i. applySym2Statement p (ps i)) = Some j" for i j
      apply (auto simp add: leastIndSome)
         apply (metis "**" applySym2Var.simps(2) image_iff)
        apply (metis \<open>bij p\<close> applySym2Var.simps(2) applySym2VarInv bij_betw_inv_into inv_inv_eq)
       apply (metis \<open>bij p\<close> applySym2Var.simps(2) applySym2VarInv assms bij_betw_inv_into permutes_inv_inv)
      by (metis "**" applySym2Var.simps(2) image_iff)
    show ?thesis
    proof (cases "leastInd (Para nm (inv p i)) N ps")
      case None
      then show ?thesis
        using Para 2 by auto
    next
      case (Some j)
      then show ?thesis
        unfolding Para using 3[of i j]
        by (auto simp add: forallStm[symmetric])
    qed
  next
    case dontCareVar
    have 1: "dontCareVar \<in> applySym2Var p ` varOfSent (ps i) \<longleftrightarrow> dontCareVar \<in> varOfSent (ps i)" for i
      apply (auto simp add: applySym2VarEq(1)[OF assms])
       apply (metis (full_types) applySym2Var.simps(1,2) varType.distinct(5) varType.exhaust)
      by force
    have 2: "leastInd dontCareVar N ps = None \<longleftrightarrow> leastInd dontCareVar N (\<lambda>i. applySym2Statement p (ps i)) = None"
      by (simp add: leastIndNone 1)
    have 3: "leastInd dontCareVar N ps = Some i \<longleftrightarrow> leastInd dontCareVar N (\<lambda>i. applySym2Statement p (ps i)) = Some i" for i
      by (simp add: leastIndSome 1)
    show ?thesis
      apply (auto simp add: dontCareVar)
      apply (cases "leastInd dontCareVar N ps")
      subgoal using 2 by auto
      subgoal for i using 3[of i]
        by (auto simp add: forallStm[symmetric])
      done
  qed
  then show ?case
    by (rule ext)
qed


subsection \<open>Reachability\<close>

inductive reachableUpTo :: "formula set \<Rightarrow> rule set \<Rightarrow> nat \<Rightarrow> state \<Rightarrow> bool" where
  reachableSet0: "\<forall>f\<in>fs. formEval f s \<Longrightarrow> reachableUpTo fs rs 0 s"
| reachableSetNext: "reachableUpTo fs rs n s \<Longrightarrow> guard g a \<in> rs \<Longrightarrow> formEval g s \<Longrightarrow>
                     reachableUpTo fs rs (Suc n) (trans1 a s)"

inductive_cases reachableUpTo0: "reachableUpTo fs rs 0 s"
inductive_cases reachableUpToSuc: "reachableUpTo fs rs (Suc n) s"

text \<open>A set of rules is symmetric\<close>
definition symProtRules :: "nat \<Rightarrow> rule set \<Rightarrow> bool" where [simp]:
  "symProtRules N rs = (\<forall>p r. p permutes {x. x \<le> N} \<and> r \<in> rs \<longrightarrow> applySym2Rule p r \<in> rs)"

text \<open>A list of formulas is symmetric\<close>
definition symPredSet :: "nat \<Rightarrow> formula set \<Rightarrow> bool" where [simp]:
  "symPredSet N fs = (\<forall>p f. p permutes {x. x \<le> N} \<and> f \<in> fs \<longrightarrow> applySym2Form p f \<in> fs)"

lemma reachSymLemma:
  assumes "symPredSet N fs"
    and "symProtRules N rs"
    and "p permutes {x. x \<le> N}"
  shows "\<forall>s. reachableUpTo fs rs i s \<longrightarrow> reachableUpTo fs rs i (applySym2State p s)"
proof (induction i)
  case 0
  show ?case
    apply clarify subgoal for s
      apply (auto elim!: reachableUpTo0)
      apply (rule reachableUpTo.intros(1))
      apply (auto simp add: stFormSymCorrespondence2(2)[OF assms(3)])
      using assms(1,3) permutes_inv unfolding symPredSet_def by blast
    done
next
  case (Suc i)
  have 1: "guard g a \<in> rs \<Longrightarrow> guard (applySym2Form p g) (applySym2Statement p a) \<in> rs" for g a
    using assms(2,3) unfolding symProtRules_def by force
  show ?case
    apply clarify subgoal for s
      apply (auto elim!: reachableUpToSuc)
      subgoal for s0 g a
        unfolding trans1Symmetric[OF assms(3)]
        apply (rule reachableUpTo.intros(2))
        subgoal using Suc by auto
        using 1 apply auto
        using stFormSymCorrespondence1[OF assms(3)] by auto
      done
    done
qed

lemma SymLemma:
  assumes "symPredSet N fs"
    and "symProtRules N rs"
    and "\<forall>s i. reachableUpTo fs rs i s \<longrightarrow> formEval f s"
    and "p permutes {x. x \<le> N}"
    and "reachableUpTo fs rs i s"
  shows "formEval (applySym2Form p f) s"
proof -
  have "bij p"
    using assms(4) permutes_bij by blast
  have 0: "(inv p) permutes {x. x \<le> N}"
    using assms(4)
    by (simp add: permutes_inv)
  have 1: "reachableUpTo fs rs i (applySym2State (inv p) s)"
    using reachSymLemma[OF assms(1,2) 0] assms(5) by auto 
  have 2: "formEval (applySym2Form p f) (applySym2State p (applySym2State (inv p) s))"
    unfolding stFormSymCorrespondence1[OF assms(4)]
    using 1 assms(3) by auto
  then show ?thesis
    unfolding applySym2StateInv[OF \<open>bij p\<close>] by auto
qed


subsection \<open>Rule set parameterized by processes\<close>

text \<open>We consider a special form of rule set, where there is a set associated
to each process i\<close>
definition setOverDownN :: "nat \<Rightarrow> (nat \<Rightarrow> 'a set) \<Rightarrow> 'a set" where
  "setOverDownN N f = {r. \<exists>n\<le>N. r \<in> f n}"

definition setOverDownN2 :: "nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> 'a set) \<Rightarrow> 'a set"  where
  "setOverDownN2 N f = {r. \<exists>n1 n2. n1\<le>N \<and> n2\<le>N \<and> r \<in> f n1 n2}"

text \<open>There is a general theorem for showing symmetry\<close>
definition symParamRules :: "nat \<Rightarrow> (nat \<Rightarrow> rule set) \<Rightarrow> bool" where
  "symParamRules N f =
    (\<forall>p i. p permutes {x. x \<le> N} \<longrightarrow> i \<le> N \<longrightarrow> applySym2Rule p ` f i = f (p i))"

theorem symProtFromSymParam:
  assumes "symParamRules N f"
  shows "symProtRules N (setOverDownN N f)"
proof -
  have 1: "applySym2Rule p r \<in> f (p n)"
    if "p permutes {x. x \<le> N}" "n \<le> N" "r \<in> f n" for p r n
  proof -
    have "applySym2Rule p ` f n = f (p n)"
      using assms unfolding symParamRules_def
      using that(1,2) by auto
    then show ?thesis
      using that(3) by auto
  qed
  show ?thesis
    unfolding symProtRules_def setOverDownN_def
    apply auto
    subgoal for p r n
      apply (rule exI[where x="p n"])
      apply auto
      using permutes_in_image apply fastforce
      using assms unfolding symParamRules_def
      using 1 by auto
    done
qed

definition symParamRule2 :: "nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> rule) \<Rightarrow> bool" where
  "symParamRule2 N r =
    (\<forall>p i j. p permutes {x. x \<le> N} \<longrightarrow> i \<le> N \<longrightarrow> j \<le> N \<longrightarrow> applySym2Rule p (r i j) = r (p i) (p j))"

definition symParamRules2 :: "nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> rule set) \<Rightarrow> bool" where
  "symParamRules2 N rs =
    (\<forall>p i j. p permutes {x. x \<le> N} \<longrightarrow> i \<le> N \<longrightarrow> j \<le> N \<longrightarrow> applySym2Rule p ` (rs i j) = rs (p i) (p j))"

lemma symParamRules2Empty:
  "symParamRules2 N (\<lambda>i j. {})"
  unfolding symParamRules2_def by auto

lemma symParamRules2Insert:
  assumes "symParamRule2 N r"
    and "symParamRules2 N rs"
  shows "symParamRules2 N (\<lambda>i j. insert (r i j) (rs i j))"
  using assms unfolding symParamRule2_def symParamRules2_def by auto

theorem symProtFromSymParam2:
  assumes "symParamRules2 N f"
  shows "symProtRules N (setOverDownN2 N f)"
proof -
  have 1: "applySym2Rule p r \<in> f (p n) (p m)"
    if "p permutes {x. x \<le> N}" "n \<le> N" "m \<le> N"  "r \<in> f n m" for p r n m
  proof -
    have "applySym2Rule p ` (f n m)= f (p n) (p m)"
      using assms symParamRules2_def that(1) that(2) that(3) by blast
    then show ?thesis
      using that(4) by blast 
  qed
  show ?thesis
    unfolding symProtRules_def setOverDownN2_def
    apply auto
    subgoal for p r n m
      apply (rule exI[where x="p n"])
      apply (rule conjI)
      apply (metis mem_Collect_eq permutes_def)
      apply (rule exI[where x="p m"])
      apply auto
      using permutes_in_image apply fastforce
      using 1 by blast
    done
qed


subsection \<open>Formula set parameterized by two processes\<close>

text \<open>Likewise, we consider special cases of parameterized formulas.\<close>

definition equivForm :: "formula \<Rightarrow> formula \<Rightarrow> bool" where
  "equivForm f1 f2 = (\<forall>s. formEval f1 s = formEval f2 s)"

lemma equivFormRefl [simp]:
  "equivForm f f"
  unfolding equivForm_def by auto

lemma equivFormSym:
  "equivForm f1 f2 \<longleftrightarrow> equivForm f2 f1"
  unfolding equivForm_def by auto

lemma equivFormTrans:
  "equivForm f1 f2 \<Longrightarrow> equivForm f2 f3 \<Longrightarrow> equivForm f1 f3"
  unfolding equivForm_def by auto

definition symParamForm :: "nat \<Rightarrow> (nat \<Rightarrow> formula) \<Rightarrow> bool" where
  "symParamForm N f =
    (\<forall>p i. p permutes {x. x \<le> N} \<longrightarrow> i \<le> N \<longrightarrow> equivForm (applySym2Form p (f i)) (f (p i)))"

definition symParamForm2 :: "nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> formula) \<Rightarrow> bool" where
  "symParamForm2 N f =
    (\<forall>p i j. p permutes {x. x \<le> N} \<longrightarrow> i \<le> N \<longrightarrow> j \<le> N \<longrightarrow> equivForm (applySym2Form p (f i j)) (f (p i) (p j)))"

lemma symParamFormImply:
  assumes "symParamForm N f1"
    and "symParamForm N f2"
  shows "symParamForm N (\<lambda>i. implyForm (f1 i) (f2 i))"
  using assms equivForm_def unfolding symParamForm_def by auto

lemma symParamFormForall:
  assumes "symParamForm2 N f"
  shows "symParamForm N (\<lambda>i. forallForm (\<lambda>j. f i j) N)"
proof -
  have a: "formEval (f (p i) j) s"
    if "p permutes {x. x \<le> N}" "i \<le> N" "\<forall>k\<le>N. formEval (applySym2Form p (f i k)) s" "j \<le> N" for p i j s
  proof -
    have 1: "inv p j \<le> N"
      using that(1,4)
      by (metis (full_types) mem_Collect_eq permutes_def permutes_inverses(1))
    have 2: "formEval (applySym2Form p (f i (inv p j))) s"
      using that(3) 1 by auto
    have 3: "equivForm (applySym2Form p (f i (inv p j))) (f (p i) j)"
      using assms that unfolding symParamForm2_def
      using 1 permutes_inverses(1) by fastforce
    show ?thesis
      using 2 3 unfolding equivForm_def by auto
  qed
  have b: "formEval (applySym2Form p (f i j)) s"
    if "p permutes {x. x \<le> N}" "i \<le> N" "\<forall>k\<le>N. formEval (f (p i) k) s" "j \<le> N" for p i j s
  proof -
    have 1: "p j \<le> N"
      using bij_betwE permutes_imp_bij that(1) that(4) by fastforce
    have 2: "formEval (f (p i) (p j)) s"
      using that(3) 1 by auto
    have 3: "equivForm (applySym2Form p (f i j)) (f (p i) (p j))"
      using assms that unfolding symParamForm2_def by auto
    show ?thesis
      using 2 3 unfolding equivForm_def by auto
  qed
  show ?thesis
    unfolding symParamForm_def applySym2Form.simps equivForm_def
    using a b by auto
qed

(*
theorem symPredFromSymParam:
  assumes "symParamForm N f"
  shows "symPredSet N (setOverDownN N (\<lambda>i. {f i}))"
proof -
  have 1: "applySym2Form p r = f (p n)"
    if "p permutes {x. x \<le> N}" "n \<le> N" "r \<in> f n" for p r n
  proof -
    have "applySym2Form p ` f n = f (p n)"
      using assms unfolding symParamForm_def
      using that(1,2) by auto
    then show ?thesis
      using that(3) by auto
  qed
  show ?thesis
    unfolding symPredSet_def setOverDownN_def
    apply auto
    subgoal for p f n
      apply (rule exI[where x="p n"])
      apply auto
      using permutes_in_image apply fastforce
      using assms unfolding symPredSet_def
      using 1 by auto
    done
qed

theorem symPredFromSymParam2:
  assumes "symParamForm2 N f"
  shows "symPredSet N (setOverDownN2 N f)"
proof -
  have 1: "applySym2Form p r \<in> f (p n) (p m)"
    if "p permutes {x. x \<le> N}" "n \<le> N" "m \<le> N"  "r \<in> f n m" for p r n m
  proof -
    have "applySym2Form p ` (f n m) = f (p n) (p m)"
      using assms symParamForm2_def that(1) that(2) that(3) by blast
    then show ?thesis
      using that(4) by blast 
  qed
  show ?thesis
    unfolding symPredSet_def setOverDownN2_def
    apply auto
    subgoal for p f n m
      apply (rule exI[where x="p n"])
      apply (rule conjI)
      apply (metis mem_Collect_eq permutes_def)
      apply (rule exI[where x="p m"])
      apply auto
      using permutes_in_image apply fastforce
      using 1 by blast
    done
qed
*)

fun equivRule :: "rule \<Rightarrow> rule \<Rightarrow> bool" where
  "equivRule (guard g1 a1) (guard g2 a2) \<longleftrightarrow> equivForm g1 g2 \<and> a1 = a2"

lemma equivRuleRefl:
  "equivRule r r"
  apply (cases r) by auto

lemma equivRuleSym:
  "equivRule r1 r2 \<longleftrightarrow> equivRule r2 r1"
  apply (cases r1, cases r2) using equivFormSym by auto

lemma equivRuleTrans:
  "equivRule r1 r2 \<Longrightarrow> equivRule r2 r3 \<Longrightarrow> equivRule r1 r3"
  apply (cases r1, cases r2, cases r3) using equivFormTrans by auto

definition symParamRule :: "nat \<Rightarrow> (nat \<Rightarrow> rule) \<Rightarrow> bool" where
  "symParamRule N f =
    (\<forall>p i. p permutes {x. x \<le> N} \<longrightarrow> i \<le> N \<longrightarrow> equivRule (applySym2Rule p (f i)) (f (p i)))"

subsection \<open>Strengthening\<close>

text \<open>Strengthen a guard g by auxiliary invariant\<close>

fun strengthenForm :: "formula \<Rightarrow> formula \<Rightarrow> formula" where
  "strengthenForm invf g = andForm g invf"

fun strengthenRule :: "formula \<Rightarrow> rule \<Rightarrow> rule" where
  "strengthenRule invf (guard g a) = guard (strengthenForm invf g) a"

lemma symParamStrengthenRule:
  assumes "symParamRule N r"
    and "symParamForm N f"
  shows "symParamRule N (\<lambda>i. strengthenRule (f i) (r i))"
proof -
  have a: "equivForm (applySym2Form p (strengthenForm (f i) a1)) (strengthenForm (f (p i)) a2) \<and>
           applySym2Statement p g1 = g2"
    if "p permutes {x. x \<le> N}" "i \<le> N" "r i = guard a1 g1" "r (p i) = guard a2 g2" for p i a1 a2 g1 g2
  proof -
    have 1: "equivRule (applySym2Rule p (r i)) (r (p i))"
      using assms(1) unfolding symParamRule_def
      using that(1,2) by auto
    have 2: "equivForm (applySym2Form p a1) a2"
      using 1 unfolding that(3,4) by auto
    have 3: "equivForm (applySym2Form p (f i)) (f (p i))"
      using assms(2) unfolding symParamForm_def using that(1,2) by auto
    have 4: "equivForm (applySym2Form p (strengthenForm (f i) a1)) (strengthenForm (f (p i)) a2)"
      using 2 3 unfolding equivForm_def by auto
    have 5: "applySym2Statement p g1 = g2"
      using 1 unfolding that(3,4) by auto
    show ?thesis
      unfolding that(3,4) using 4 5 by auto
  qed
  show ?thesis
    unfolding symParamRule_def
    apply auto subgoal for p i
      apply (cases "r i") subgoal for a1 g1
        apply (cases "r (p i)") subgoal for a2 g2
          using a by auto
        done
      done
    done
qed


end