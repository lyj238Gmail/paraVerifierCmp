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
  forallFormExcl "nat \<Rightarrow> formula" nat nat |
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
  parallel statement statement (infixr "||" 35) |
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
datatype rule =
  guard formula statement (infix "\<triangleright>" 30)

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
  evalForall: "formEval (forallForm ffun N) s = (\<forall>i\<le>N. formEval (ffun i) s)" |
  evalForallExcl: "formEval (forallFormExcl ffun i N) s = (\<forall>j\<le>N. j \<noteq> i \<longrightarrow> formEval (ffun j) s)" |
  evalChaos:  "formEval chaos s = True" |
  evalDontCareForm: "formEval dontCareForm s = True"

primrec varOfSent :: "statement \<Rightarrow> varType set" where
  "varOfSent skip = {}" |
  "varOfSent (assign a) = {fst a}" |
  "varOfSent (parallel S1 S2) = varOfSent S1 \<union> varOfSent S2" |
  "varOfSent (forallStm ps N) = \<Union>{S. \<exists>i. i \<le> N \<and> S = varOfSent (ps i)}"

declare varOfSent.simps(4) [simp del]

lemma varOfSentEq:
  "v \<in> varOfSent (forallStm ps N) \<longleftrightarrow> (\<exists>i. i \<le> N \<and> v \<in> varOfSent (ps i))"
  by (auto simp add: varOfSent.simps(4))

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

definition mutualDiffVars :: "(nat \<Rightarrow> statement) \<Rightarrow> bool" where
  "mutualDiffVars ps \<longleftrightarrow> (\<forall>i j. i \<noteq> j \<longrightarrow> varOfSent (ps i) \<inter> varOfSent (ps j) = {})"

lemma trans1ForallAlt:
  assumes "mutualDiffVars ps"
  shows "trans1 (forallStm ps N) s v =
          (if v \<notin> varOfSent (forallStm ps N) then s v
           else trans1 (ps (THE i. v \<in> varOfSent (ps i))) s v)"
proof -
  have a: ?thesis if "v \<notin> varOfSent (forallStm ps N)"
  proof -
    have "leastInd v N ps = None"
      using leastIndNone that varOfSentEq by auto
    then show ?thesis
      using that by auto
  qed
  have b: ?thesis if assmb: "v \<in> varOfSent (forallStm ps N)"
  proof -
    obtain i where b1: "i \<le> N" "v \<in> varOfSent (ps i)"
      using assmb varOfSentEq by blast
    have b2: "leastInd v N ps = Some i"
      unfolding leastIndSome
      apply (auto simp add: b1)
      using assms b1 unfolding mutualDiffVars_def
      by (metis IntI empty_iff inf.strict_order_iff)
    have b3: "(THE i. v \<in> varOfSent (ps i)) = i"
      apply (rule the_equality) apply (rule b1(2))
      using assms b1(2) unfolding mutualDiffVars_def by auto
    show ?thesis
      using assmb b1 b2 b3 by auto
  qed
  show ?thesis
    using a b by auto 
qed

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

  "applySym2Exp p (IVar v) = IVar (applySym2Var p v)" |
  "applySym2Exp p (Const c) = Const (applySym2Const p c)" |
  "applySym2Exp p (iteForm f1 e1 e2) = iteForm (applySym2Form p f1) (applySym2Exp p e1) (applySym2Exp p e2)" |
  "applySym2Exp p dontCareExp = dontCareExp" | 
  "applySym2Form p (eqn l r) = eqn (applySym2Exp p l) (applySym2Exp p r)" |
  "applySym2Form p (andForm f1 f2) = andForm (applySym2Form p f1) (applySym2Form p f2)" |
  "applySym2Form p (neg f1) = neg (applySym2Form p f1)" |
  "applySym2Form p (orForm f1 f2) = orForm (applySym2Form p f1) (applySym2Form p f2)" |
  "applySym2Form p (implyForm f1 f2) = implyForm (applySym2Form p f1) (applySym2Form p f2)" |
  "applySym2Form p (forallForm fp N) = forallForm (\<lambda>i. applySym2Form p (fp i)) N" |
  "applySym2Form p (forallFormExcl fp i N) = forallFormExcl (\<lambda>j. applySym2Form p (fp j)) i N" |
  "applySym2Form p dontCareForm = dontCareForm" | 
  "applySym2Form p chaos = chaos"

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
  apply (induction S) by (auto simp add: varOfSent.simps(4))

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

lemma symParamFormAnd:
  assumes "symParamForm N f1"
    and "symParamForm N f2"
  shows "symParamForm N (\<lambda>i. andForm (f1 i) (f2 i))"
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

lemma symParamFormForallExcl:
  assumes "symParamForm2 N f"
  shows "symParamForm N (\<lambda>i. forallFormExcl (\<lambda>j. f i j) i N)"
proof -
  have a: "formEval (f (p i) j) s"
    if "p permutes {x. x \<le> N}" "i \<le> N" "\<forall>j\<le>N. j \<noteq> i \<longrightarrow> formEval (applySym2Form p (f i j)) s"
       "j \<le> N" "j \<noteq> p i" for p i s j
  proof -
    have 1: "inv p j \<le> N"
      using that(1,4)
      by (metis (full_types) mem_Collect_eq permutes_def permutes_inverses(1))
    have 2: "inv p j \<noteq> i"
    proof (rule ccontr)
      assume b: "\<not>inv p j \<noteq> i"
      have "inv p j = i" using b by auto
      then have "p (inv p j) = p i" by auto
      moreover have "p (inv p j) = j"
        apply (rule bijection.inv_right)
        using bijection.intro permutes_bij that(1) by auto
      ultimately show False
        using that(5) by auto
    qed
    have 3: "formEval (applySym2Form p (f i (inv p j))) s"
      using that(3) 1 2 by auto
    have 4: "equivForm (applySym2Form p (f i (inv p j))) (f (p i) (p (inv p j)))"
      using assms(1) unfolding symParamForm2_def using 1 that by auto
    have 5: "p (inv p j) = j"
      apply (rule bijection.inv_right)
      using bijection.intro permutes_bij that(1) by auto
    show ?thesis
      using 3 4 5 unfolding equivForm_def by auto
  qed
  have b: "formEval (applySym2Form p (f i j)) s"
    if "p permutes {x. x \<le> N}" "i \<le> N" "\<forall>j\<le>N. j \<noteq> p i \<longrightarrow> formEval (f (p i) j) s"
       "j \<le> N" "j \<noteq> i" for p i s j
  proof -
    have 1: "p j \<le> N"
      using that(1,4)
      by (metis (full_types) mem_Collect_eq permutes_def)
    have 2: "p j \<noteq> p i"
    proof (rule ccontr)
      assume b: "\<not>p j \<noteq> p i"
      have "p j = p i" using b by auto
      then have "inv p (p j) = inv p (p i)" by auto
      moreover have "inv p (p j) = j"
        apply (rule bijection.inv_left)
        using bijection.intro permutes_bij that(1) by auto
      moreover have "inv p (p i) = i"
        apply (rule bijection.inv_left)
        using bijection.intro permutes_bij that(1) by auto
      ultimately show False
        using that(5) by auto
    qed
    have 3: "formEval (f (p i) (p j)) s"
      using that(3) 1 2 by auto
    have 4: "equivForm (f (p i) (p j)) (applySym2Form p (f i j))"
      apply (subst equivFormSym)
      using assms(1) unfolding symParamForm2_def by (simp add: that)
    show ?thesis
      using 3 4 unfolding equivForm_def by auto
  qed
  show ?thesis
    unfolding symParamForm_def applySym2Form.simps equivForm_def
    using a b by auto
qed

subsection \<open>Equivalence of statements and rules\<close>

definition equivStatement :: "statement \<Rightarrow> statement \<Rightarrow> bool" where
  "equivStatement S1 S2 = (varOfSent S1 = varOfSent S2 \<and> (\<forall>s. trans1 S1 s = trans1 S2 s))"

lemma equivStatementRefl [intro]:
  "equivStatement S S"
  unfolding equivStatement_def by auto

lemma equivStatementSym:
  "equivStatement S1 S2 \<Longrightarrow> equivStatement S2 S1"
  unfolding equivStatement_def by auto

lemma equivStatementTrans:
  "equivStatement S1 S2 \<Longrightarrow> equivStatement S2 S3 \<Longrightarrow> equivStatement S1 S3"
  unfolding equivStatement_def by auto

lemma equivStatementSkipLeft:
  "equivStatement (skip || S) S"
  unfolding equivStatement_def by auto

lemma unaffectedVars:
  "x \<notin> varOfSent S \<Longrightarrow> s x = trans1 S s x"
  apply (induction S) apply (auto simp add: varOfSentEq)
  subgoal for ps N
    apply (cases "leastInd x N ps")
    by (auto simp add: leastIndSome)
  done

lemma equivStatementSkipRight:
  "equivStatement (S || skip) S"
  unfolding equivStatement_def
  apply auto subgoal for s
    apply (rule ext) using unaffectedVars by auto
  done

lemma equivStatementParallel:
  "equivStatement S1 S1' \<Longrightarrow> equivStatement S2 S2' \<Longrightarrow> equivStatement (S1 || S2) (S1' || S2')"
  by (auto simp add: equivStatement_def)

lemma equivStatementForall:
  assumes "\<forall>i. i \<le> N \<longrightarrow> equivStatement (f i) (g i)"
  shows "equivStatement (forallStm f N) (forallStm g N)"
proof -
  have a: "leastInd v N f = None \<longleftrightarrow> leastInd v N g = None" for v
    unfolding leastIndNone
    using assms unfolding equivStatement_def by auto
  have b: "leastInd v N f = Some i \<longleftrightarrow> leastInd v N g = Some i" for v i
    unfolding leastIndSome
    using assms unfolding equivStatement_def by auto
  have c: "(case leastInd v N f of None \<Rightarrow> s v | Some i \<Rightarrow> trans1 (f i) s v) =
           (case leastInd v N g of None \<Rightarrow> s v | Some i \<Rightarrow> trans1 (g i) s v)" for s v
  proof (cases "leastInd v N f")
    case None
    have "leastInd v N g = None"
      using None a by auto
    then show ?thesis
      using assms unfolding equivStatement_def None by auto
  next
    case (Some i)
    have "leastInd v N g = Some i"
      using Some b by auto
    then show ?thesis
      using assms unfolding equivStatement_def Some apply auto
      by (simp add: leastIndSome)
  qed
  have "trans1 (forallStm f N) s v = trans1 (forallStm g N) s v" for v s
    using a c by auto
  then show ?thesis
    apply (auto simp add: equivStatement_def varOfSentEq)
    using assms equivStatement_def by auto
qed

lemma equivStatementPermute:
  assumes "p permutes {x. x \<le> N}"
    and "mutualDiffVars ps"
  shows "equivStatement (forallStm ps N) (forallStm (\<lambda>i. ps (p i)) N)"
proof -
  have a: "bij p"
    using assms(1) permutes_bij by auto
  have b: "\<exists>j\<le>N. x \<in> varOfSent (ps (p j))" if "i \<le> N" "x \<in> varOfSent (ps i)" for x i
  proof -
    have 1: "inv p i \<le> N"
      using that(1) assms(1)
      by (metis (full_types) mem_Collect_eq permutes_def permutes_inverses(1))
    have 2: "p (inv p i) = i"
      by (rule permutes_inverses[OF assms(1)])
    show ?thesis
      apply (rule exI[where x="inv p i"])
      using 1 2 that(2) by auto
  qed
  have c: "\<exists>i\<le>N. x \<in> varOfSent (ps i)" if "i \<le> N" "x \<in> varOfSent (ps (p i))" for x i
  proof -
    have 1: "p i \<le> N"
      by (metis (full_types) assms(1) mem_Collect_eq permutes_def that(1))
    show ?thesis
      apply (rule exI[where x="p i"])
      using 1 that(2) by auto
  qed
  have bc: "varOfSent (forallStm (\<lambda>i. ps (p i)) N) = varOfSent (forallStm ps N)"
    using b c by (auto simp add: varOfSentEq)
  have d: "trans1 (forallStm ps N) s v = trans1 (forallStm (\<lambda>i. ps (p i)) N) s v" for s v
  proof -
    have d1: "mutualDiffVars (\<lambda>i. ps (p i))"
      using assms(2) unfolding mutualDiffVars_def
      using assms(1) by (metis permutes_def)
    have d2: "trans1 (ps (THE i. v \<in> varOfSent (ps i))) s v = trans1 (ps (p (THE i. v \<in> varOfSent (ps (p i))))) s v"
      if assmd2: "v \<in> varOfSent (forallStm ps N)"
    proof -
      obtain i where d21: "i \<le> N" "v \<in> varOfSent (ps i)"
        using assmd2 varOfSentEq by blast
      have d22: "(THE i. v \<in> varOfSent (ps i)) = i"
        apply (rule the_equality) apply (rule d21(2))
        using assms(2) unfolding mutualDiffVars_def using d21(2) by blast
      have d23: "p (inv p i) = i"
        apply (rule permutes_inverses(1))
        using assms(1) by auto
      have d24: "v \<in> varOfSent (ps (p (inv p i)))"
        using d23 d21(2) by auto
      have d25: "(THE i. v \<in> varOfSent (ps (p i))) = inv p i"
        apply (rule the_equality)
         apply (auto simp add: d23 d21(2))
        using d1[unfolded mutualDiffVars_def] d24 by auto
      show ?thesis
        unfolding d22 d25 d23 by auto
    qed
    show ?thesis
      unfolding trans1ForallAlt[OF assms(2)] trans1ForallAlt[OF d1] bc
      using d2 by auto
  qed
  show ?thesis
    unfolding equivStatement_def apply (auto simp add: varOfSentEq)
    using b c d by auto
qed

definition symParamStatement :: "nat \<Rightarrow> (nat \<Rightarrow> statement) \<Rightarrow> bool" where
  "symParamStatement N ps =
    (\<forall>p i. p permutes {x. x \<le> N} \<longrightarrow> i \<le> N \<longrightarrow> equivStatement (applySym2Statement p (ps i)) (ps (p i)))"

lemma symParamStatementParallel:
  assumes "symParamStatement N a1"
    and "symParamStatement N a2"
  shows "symParamStatement N (\<lambda>i. parallel (a1 i) (a2 i))"
  using assms unfolding symParamStatement_def equivStatement_def by auto

definition symParamStatement2 :: "nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> statement) \<Rightarrow> bool" where
  "symParamStatement2 N ps =
    (\<forall>p i j. p permutes {x. x \<le> N} \<longrightarrow> i \<le> N \<longrightarrow> j \<le> N \<longrightarrow>
             equivStatement (applySym2Statement p (ps i j)) (ps (p i) (p j)))"

lemma symParamStatementForall:
  assumes "symParamStatement2 N ps"
    and "\<And>i. mutualDiffVars (ps i)"
  shows "symParamStatement N (\<lambda>i. forallStm (\<lambda>j. ps i j) N)"
proof -
  have a: "equivStatement (forallStm (\<lambda>j. applySym2Statement p (ps i j)) N)
                          (forallStm (\<lambda>j. ps (p i) (p j)) N)"
    if "p permutes {x. x \<le> N}" "i \<le> N" for p i
    apply (rule equivStatementForall)
    using assms unfolding symParamStatement2_def by (simp add: that)
  have b: "equivStatement (forallStm (\<lambda>j. ps (p i) (p j)) N)
                          (forallStm (\<lambda>j. ps (p i) j) N)"
    if "p permutes {x. x \<le> N}" "i \<le> N" for p i
    apply (rule equivStatementSym)
    apply (rule equivStatementPermute)
    using that assms(2) by auto
  show ?thesis
    unfolding symParamStatement_def applySym2Statement.simps
    using a b equivStatementTrans by blast
qed

fun equivRule :: "rule \<Rightarrow> rule \<Rightarrow> bool" where
  "equivRule (guard g1 a1) (guard g2 a2) \<longleftrightarrow> equivForm g1 g2 \<and> equivStatement a1 a2"

lemma equivRuleRefl:
  "equivRule r r"
  apply (cases r) by auto

lemma equivRuleSym:
  "equivRule r1 r2 \<longleftrightarrow> equivRule r2 r1"
  apply (cases r1, cases r2) using equivFormSym equivStatementSym by auto

lemma equivRuleTrans:
  "equivRule r1 r2 \<Longrightarrow> equivRule r2 r3 \<Longrightarrow> equivRule r1 r3"
  apply (cases r1, cases r2, cases r3)
  using equivFormTrans equivStatementTrans by auto

definition symParamRule :: "nat \<Rightarrow> (nat \<Rightarrow> rule) \<Rightarrow> bool" where
  "symParamRule N r =
    (\<forall>p i. p permutes {x. x \<le> N} \<longrightarrow> i \<le> N \<longrightarrow> equivRule (applySym2Rule p (r i)) (r (p i)))"

lemma symParamRuleI:
  "symParamForm N f \<Longrightarrow> symParamStatement N ps \<Longrightarrow> symParamRule N (\<lambda>i. guard (f i) (ps i))"
  unfolding symParamRule_def symParamForm_def symParamStatement_def by auto

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
           equivStatement (applySym2Statement p g1) g2"
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
    have 5: "equivStatement (applySym2Statement p g1) g2"
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

subsection \<open>More refined strengthening\<close>

fun removeImplies :: "formula \<Rightarrow> formula \<Rightarrow> formula" where
  "removeImplies (implyForm f1 f2) g = (if equivForm f1 g then f2 else implyForm f1 f2)"
| "removeImplies invf g = invf"

fun strengthenForm2 :: "formula \<Rightarrow> formula \<Rightarrow> formula" where
  "strengthenForm2 invf g = andForm g (removeImplies invf g)"

fun strengthenRule2 :: "formula \<Rightarrow> rule \<Rightarrow> rule" where
  "strengthenRule2 invf (guard g a) = guard (strengthenForm2 invf g) a"


text \<open>Equivalence between strengthenRule and strengthenRule2\<close>

lemma removeImpliesEquiv [simp]:
  "formEval g s \<Longrightarrow> formEval (removeImplies invf g) s  \<longleftrightarrow> formEval invf s"
  apply (cases invf) by (auto simp add: equivForm_def)

lemma strengthenForm2Equiv:
  "equivForm (strengthenForm2 invf g) (strengthenForm invf g)"
  using removeImpliesEquiv by (auto simp add: equivForm_def)

lemma strengthenRule2Equiv:
  "equivRule (strengthenRule2 invf r) (strengthenRule invf r)"
  apply (cases r) using strengthenForm2Equiv by auto

lemma equivApply2SymForm:
  assumes "p permutes {x. x \<le> N}"
    and "equivForm f1 f2"
  shows "equivForm (applySym2Form p f1) (applySym2Form p f2)"
proof -
  have "formEval (applySym2Form p f1) s \<longleftrightarrow> formEval (applySym2Form p f2) s" for s
    unfolding stFormSymCorrespondence3(2)[OF assms(1), symmetric]
    using assms(2) unfolding equivForm_def by auto
  then show ?thesis
    unfolding equivForm_def by auto
qed

lemma equivApply2SymStatement:
  assumes "p permutes {x. x \<le> N}"
    and "equivStatement a1 a2"
  shows "equivStatement (applySym2Statement p a1) (applySym2Statement p a2)"
proof -
  have a: "bij p"
    using assms by (simp add: permutes_bij)
  have b: "varOfSent (applySym2Statement p a1) = varOfSent (applySym2Statement p a2)"
    using assms(2) equivStatement_def by auto
  have c: "trans1 (applySym2Statement p a1) s = trans1 (applySym2Statement p a2) s" for s
  proof -
    have "trans1 (applySym2Statement p a) (applySym2State p (applySym2State (inv p) s)) =
          applySym2State p (trans1 a (applySym2State (inv p) s))" for a
      using trans1Symmetric[OF assms(1)] by auto
    moreover have "applySym2State p (applySym2State (inv p) s) = s"
      using \<open>bij p\<close> by auto
    moreover have "trans1 a1 (applySym2State (inv p) s) = trans1 a2 (applySym2State (inv p) s)"
      using assms(2) unfolding equivStatement_def by auto
    ultimately show ?thesis
      by auto
  qed
  show ?thesis
    unfolding equivStatement_def using b c by auto
qed

lemma equivApply2SymRule:
  assumes "p permutes {x. x \<le> N}"
    and "equivRule r1 r2"
  shows "equivRule (applySym2Rule p r1) (applySym2Rule p r2)"
proof -
  show ?thesis
    apply (cases r1) subgoal for g1 a1
      apply (cases r2) subgoal for g2 a2
        using assms equivApply2SymForm equivApply2SymStatement by auto
      done
    done
qed

lemma symParamStrengthenRule2:
  assumes "symParamRule N r"
    and "symParamForm N f"
  shows "symParamRule N (\<lambda>i. strengthenRule2 (f i) (r i))"
proof -
  have a: "symParamRule N (\<lambda>i. strengthenRule (f i) (r i))"
    using symParamStrengthenRule[OF assms] by auto
  have b: "equivRule (applySym2Rule p (strengthenRule2 (f i) (r i))) (strengthenRule2 (f (p i)) (r (p i)))"
    if "p permutes {x. x \<le> N}" "i \<le> N" for p i 
  proof -
    have 1: "equivRule (applySym2Rule p (strengthenRule2 (f i) (r i))) (applySym2Rule p (strengthenRule (f i) (r i)))"
      apply (rule equivApply2SymRule[OF that(1)])
      using strengthenRule2Equiv by auto
    have 2: "equivRule (applySym2Rule p (strengthenRule (f i) (r i))) (strengthenRule (f (p i)) (r (p i)))"
      using a that unfolding symParamRule_def by auto
    have 3: "equivRule (strengthenRule (f (p i)) (r (p i))) (strengthenRule2 (f (p i)) (r (p i)))"
      apply (subst equivRuleSym)
      using strengthenRule2Equiv by auto
    show ?thesis
      using 1 2 3 equivRuleTrans by blast
  qed
  show ?thesis
    unfolding symParamRule_def using b by auto
qed


subsection \<open>Assume-guarantee property of strengthening\<close>

text \<open>This corresponds to Lemma 1 in the Handbook of Model Checking
  Inv - the set of possible strengthening
  rs  - set of rules before strengthening
  rs' - set of rules after strengthening
  f   - invariant to be checked
\<close>
lemma strengthenProtSim:
  assumes "\<And>r. r \<in> rs \<Longrightarrow> r \<in> rs' \<or> (\<exists>inv\<in>Inv. strengthenRule inv r \<in> rs')"
    and "\<And>i. \<forall>s. reachableUpTo I rs i s \<longrightarrow> formEval f s \<Longrightarrow>
             \<forall>s. \<forall>inv\<in>Inv. reachableUpTo I rs i s \<longrightarrow> formEval inv s"
    and "\<And>i. \<forall>s. reachableUpTo I rs' i s \<longrightarrow> formEval f s"
  shows "\<forall>s. reachableUpTo I rs i s \<longrightarrow> reachableUpTo I rs' i s \<and> formEval f s"
proof (induction i)
  case 0
  have a: "reachableUpTo I rs 0 s \<longleftrightarrow> reachableUpTo I rs' 0 s" for s
    by (meson reachableSet0 reachableUpTo0)
  have b: "\<forall>s. reachableUpTo I rs' 0 s \<longrightarrow> formEval f s"
    using assms(3) by auto
  show ?case apply auto
     apply (meson reachableSet0 reachableUpTo0)
    using a b by auto
next
  case (Suc i)
  have 1: "reachableUpTo I rs' (Suc i) s" if a: "reachableUpTo I rs (Suc i) s" for s
  proof -
    obtain s' g a where b: "s = trans1 a s'" "reachableUpTo I rs i s'" "(g \<triangleright> a) \<in> rs" "formEval g s'"
      using reachableUpToSuc[OF a] by metis
    have c: "reachableUpTo I rs' i s'"
      using b(2) Suc by auto
    have d: "\<forall>s. reachableUpTo I rs i s \<longrightarrow> formEval f s"
      using Suc by auto
    have e: "\<forall>inv\<in>Inv. formEval inv s'"
      using assms(2)[OF d] b(2) by auto
    have f: "(g \<triangleright> a) \<in> rs' \<or> (\<exists>inv\<in>Inv. strengthenRule inv (g \<triangleright> a) \<in> rs')"
      using assms(1) b(3) by blast
    have g: ?thesis if g1: "(g \<triangleright> a) \<in> rs'"
      unfolding b(1)
      by (rule reachableSetNext[OF c g1 b(4)])
    have h: ?thesis if h1: "\<exists>inv\<in>Inv. strengthenRule inv (g \<triangleright> a) \<in> rs'"
    proof -
      obtain inv where h2: "inv \<in> Inv" "strengthenRule inv (g \<triangleright> a) \<in> rs'"
        using h1 by auto
      have h3: "(g \<and>\<^sub>f inv \<triangleright> a) \<in> rs'"
        using h2(2) by auto
      show ?thesis
        unfolding b(1)
        apply (rule reachableSetNext[OF c h3])
        using b(4) e h2 by auto
    qed
    show ?thesis
      using f g h by auto
  qed
  show ?case
    using 1 assms(3) by auto
qed


subsection \<open>Abstraction\<close>

text \<open>Abstraction of constant:
  Index greater than M is abstracted to M + 1, others are unchanged.
\<close>
primrec absTransfConst :: "nat \<Rightarrow> scalrValueType \<Rightarrow> scalrValueType" where [simp]:
  "absTransfConst M (enum t n) = enum t n"
| "absTransfConst M (index n) = (if n > M then index (M+1) else index n)"
| "absTransfConst M (boolV b) = boolV b"
| "absTransfConst M dontCare = dontCare"

text \<open>Abstraction of state\<close>
fun abs1 :: "nat \<Rightarrow> state \<Rightarrow> state" where
  "abs1 M s (Para nm i) = (if i > M then dontCare else absTransfConst M (s (Para nm i)))"
| "abs1 M s (Ident v) = absTransfConst M (s (Ident v))"
| "abs1 M s dontCareVar = dontCare"

text \<open>Abstraction of variables\<close>
primrec absTransfVar :: "nat \<Rightarrow> varType \<Rightarrow> varType" where 
  "absTransfVar M (Ident n) = Ident n" |
  "absTransfVar M (Para n i) =
    (if i > M then dontCareVar else Para n i)" |
  "absTransfVar M dontCareVar = dontCareVar"

lemma abs1Eq:
  "abs1 M s v = (if absTransfVar M v = dontCareVar then dontCare else absTransfConst M (s v))"
  apply (cases v) by auto

primrec boundVar :: "nat \<Rightarrow> expType \<Rightarrow> bool" where
  "boundVar i (Const n) = False"
| "boundVar i (IVar v) =
    (case v of (Ident n) \<Rightarrow> True | (Para n j) \<Rightarrow> i = j | dontCareVar \<Rightarrow> False)"
| "boundVar i (iteForm b e1 e2) = False"
| "boundVar i dontCareExp = False"

primrec boundExp :: "nat \<Rightarrow> expType \<Rightarrow> bool" and
        boundForm :: "nat \<Rightarrow> formula \<Rightarrow> bool" where
  "boundExp i (Const x) =
    (case x of (enum nm i) \<Rightarrow> True | boolV b \<Rightarrow> True | _ \<Rightarrow> False)"
| "boundExp i (IVar v) = False"
| "boundExp i (iteForm b e1 e2) = False"
| "boundExp i dontCareExp = False"

| "boundForm i (eqn e1 e2) = (boundVar i e1 \<and> boundExp i e2)"
| "boundForm i (neg f) = boundForm i f"
| "boundForm i (andForm f1 f2) = (boundForm i f1 \<and> boundForm i f2)"
| "boundForm i (orForm f1 f2) = (boundForm i f1 \<and> boundForm i f2)"
| "boundForm i (implyForm f1 f2) = (boundForm i f1 \<and> boundForm i f2)"
| "boundForm i chaos = True"
| "boundForm i dontCareForm = True"
| "boundForm i (forallForm pf N) = False"
| "boundForm i (forallFormExcl pf j N) = False"

lemma absUnchanged:
  assumes "case v of Ident n \<Rightarrow> True | Para n i \<Rightarrow> i \<le> M | dontCareVar \<Rightarrow> False"
    and "case s v of index i \<Rightarrow> False | dontCare \<Rightarrow> False | _ \<Rightarrow> True"
  shows "abs1 M s v = s v"
  apply (cases v) using assms by (cases "s v", auto)+

lemma absUnchanged2:
  assumes "case v of Ident n \<Rightarrow> True | Para n i \<Rightarrow> i \<le> M | dontCareVar \<Rightarrow> False"
    and "case abs1 M s v of index i \<Rightarrow> False | dontCare \<Rightarrow> False | _ \<Rightarrow> True"
  shows "abs1 M s v = s v"
  apply (cases v) using assms by (cases "s v", auto)+

lemma boundEval:
  assumes "i \<le> M"
  shows "(boundExp i e \<longrightarrow> expEval e s = expEval e (abs1 M s)) \<and>
         (boundForm i f \<longrightarrow> (formEval f s \<longleftrightarrow> formEval f (abs1 M s)))"
proof (induction rule: expType_formula.induct)
  case (eqn e1 e2)
  show ?case
    apply (cases e1)
       apply auto subgoal for v
      apply (cases e2)
         apply auto apply (cases v) using absUnchanged assms apply auto
       apply (metis abs1.simps(2) varType.simps(9))
      by (metis abs1.simps(1) leD varType.simps(10))
    subgoal for v
      apply (cases e2)
         apply auto apply (cases v) using absUnchanged2 assms apply auto
      apply (metis abs1.simps(2) varType.simps(9))
      by (metis abs1.simps(1) leD varType.simps(10))
    done
qed (auto)

primrec safeExp :: "nat \<Rightarrow> expType \<Rightarrow> bool" and
        safeForm :: "nat \<Rightarrow> formula \<Rightarrow> bool" where
  "safeExp M (Const x) =
    (case x of (enum nm i) \<Rightarrow> True | boolV b \<Rightarrow> True | _ \<Rightarrow> False)"
| "safeExp M (IVar v) = False"
| "safeExp M (iteForm b e1 e2) = False"
| "safeExp M dontCareExp = False"

| "safeForm M (eqn e1 e2) = (\<exists>i\<le>M. boundVar i e1 \<and> safeExp i e2)"
| "safeForm M (neg f) = safeForm M f"
| "safeForm M (andForm f1 f2) = (safeForm M f1 \<and> safeForm M f2)"
| "safeForm M (orForm f1 f2) = (safeForm M f1 \<and> safeForm M f2)"
| "safeForm M (implyForm f1 f2) = (safeForm M f1 \<and> safeForm M f2)"
| "safeForm M chaos = True"
| "safeForm M dontCareForm = True"
| "safeForm M (forallForm pf N) = False"
| "safeForm M (forallFormExcl pf j N) = False"

lemma safeEval:
  "(safeExp M e \<longrightarrow> expEval e s = expEval e (abs1 M s)) \<and>
   (safeForm M f \<longrightarrow> (formEval f s \<longleftrightarrow> formEval f (abs1 M s)))"
proof (induction rule: expType_formula.induct)
  case (IVar x)
  then show ?case by auto
next
  case (Const x)
  then show ?case by auto
next
  case (iteForm x1 x2 x3)
  then show ?case by auto
next
  case dontCareExp
  then show ?case by auto
next
  case (eqn e1 e2)
  show ?case
    apply (cases e1)
       apply auto subgoal for v i
      apply (cases e2)
         apply auto apply (cases v) using absUnchanged apply auto
       apply (metis abs1.simps(2) varType.simps(9))
      by (metis abs1.simps(1) leD varType.simps(10))
    subgoal for v
      apply (cases e2)
         apply auto apply (cases v) using absUnchanged2 apply auto
      apply (metis abs1.simps(2) varType.simps(9))
      by (metis abs1.simps(1) leD varType.simps(10))
    done
next
  case (andForm x1 x2)
  then show ?case by auto
next
  case (neg x)
  then show ?case by auto
next
  case (orForm x1 x2)
  then show ?case by auto
next
  case (implyForm x1 x2)
  then show ?case by auto
next
  case (forallForm x1 x2)
  then show ?case by auto
next
  case (forallFormExcl x1 x2 x3)
  then show ?case by auto
next
  case chaos
  then show ?case by auto
next
  case dontCareForm
  then show ?case by auto
qed


text \<open>Abstraction of expressions and formulas\<close>
primrec absTransfExp :: "nat \<Rightarrow> expType \<Rightarrow> expType" and
  absTransfForm :: "nat \<Rightarrow> formula \<Rightarrow> formula" where
  "absTransfExp M (Const i) = Const (absTransfConst M i)" |

  "absTransfExp M (IVar v) =
    (if absTransfVar M v = dontCareVar then dontCareExp
     else IVar (absTransfVar M v))" |

  "absTransfExp M (iteForm b e1 e2) = dontCareExp" |

  "absTransfExp M dontCareExp = dontCareExp" |

  "absTransfForm M (eqn e1 e2) =
    (if absTransfExp M e1 = dontCareExp \<or> absTransfExp M e2 = dontCareExp
     then dontCareForm 
     else eqn (absTransfExp M e1) (absTransfExp M e2))" |

  "absTransfForm M (neg f) =
    (if safeForm M f then neg f else dontCareForm)" |

  "absTransfForm M (andForm f1 f2) =
    (if absTransfForm M f1 = dontCareForm then absTransfForm M f2
     else if absTransfForm M f2 = dontCareForm then absTransfForm M f1
     else andForm (absTransfForm M f1) (absTransfForm M f2))" |

  "absTransfForm M (orForm f1 f2) =
    (if absTransfForm M f1 = dontCareForm then dontCareForm
     else if absTransfForm M f2 = dontCareForm then dontCareForm
     else orForm (absTransfForm M f1) (absTransfForm M f2))" |

  "absTransfForm M (implyForm f1 f2) = dontCareForm" |

  "absTransfForm M chaos = chaos" |

  "absTransfForm M dontCareForm = dontCareForm" |

  "absTransfForm M (forallForm pf N) =
    (if M \<le> N \<and> (\<forall>j. boundForm j (pf j)) then forallForm pf M else dontCareForm)" |

  "absTransfForm M (forallFormExcl pf i N) =
    (if i > M \<and> M \<le> N \<and> (\<forall>j. boundForm j (pf j)) then forallForm pf M else dontCareForm)"

lemma absTransfConstEnum [simp]:
  "absTransfConst M v = enum nm i \<longleftrightarrow> v = enum nm i"
  apply (cases v) by auto

lemma absTransfConstBoolV [simp]:
  "absTransfConst M v = boolV b \<longleftrightarrow> v = boolV b"
  apply (cases v) by auto

lemma absBoundVar:
  assumes "i \<le> M"
    and "boundVar i e"
  shows "absTransfExp M e = e"
proof (cases e)
  case (IVar v)
  have "absTransfVar M v = v"
    apply (cases v)
      apply auto using assms(2) unfolding IVar
    using assms by auto
  then show ?thesis
    using IVar apply auto
    using assms unfolding IVar by auto
next
  case (Const x2)
  then show ?thesis
    using assms by auto
next
  case (iteForm x31 x32 x33)
  then show ?thesis
    using assms by auto
next
  case dontCareExp
  then show ?thesis by auto
qed

lemma absTransfFormSim:
  "(absTransfExp M e \<noteq> dontCareExp \<longrightarrow>
    expEval (absTransfExp M e) (abs1 M s) = absTransfConst M (expEval e s)) \<and>
   (absTransfForm M f \<noteq> dontCareForm \<longrightarrow>
    formEval f s \<longrightarrow> formEval (absTransfForm M f) (abs1 M s))"
proof (induction rule: expType_formula.induct[where expType=e and formula=f])
  case (IVar v)
  show ?case
    apply (cases v) by auto
next
  case (Const x)
  then show ?case by auto
next
  case (iteForm b e1 e2)
  then show ?case by auto
next
  case dontCareExp
  then show ?case by auto
next
  case (eqn e1 e2)
  have "formEval (e1 =\<^sub>f e2) s \<longrightarrow> formEval (absTransfForm M (e1 =\<^sub>f e2)) (abs1 M s)"
    if "absTransfForm M (e1 =\<^sub>f e2) \<noteq> dontCareForm"
  proof -
    have 1: "absTransfExp M e1 \<noteq> dontCareExp" "absTransfExp M e2 \<noteq> dontCareExp"
      using that by auto
    have 2: "absTransfForm M (e1 =\<^sub>f e2) = eqn (absTransfExp M e1) (absTransfExp M e2)"
      using 1 by auto
    have 3: "expEval (absTransfExp M e1) (abs1 M s) = absTransfConst M (expEval e1 s)"
            "expEval (absTransfExp M e2) (abs1 M s) = absTransfConst M (expEval e2 s)"
      using eqn 2 by auto
    show ?thesis
      unfolding 2 3 formEval.simps by auto
  qed
  then show ?case by auto
next
  case (andForm f1 f2)
  then show ?case by auto
next
  case (neg f)
  show ?case
    apply auto
    using safeEval by blast
next
  case (orForm f1 f2)
  then show ?case by auto
next
  case (implyForm x1 x2)
  then show ?case by auto
next
  case (forallForm pf N)
  show ?case 
    apply auto
    by (meson boundEval order.trans)
next
  case (forallFormExcl pf i N)
  show ?case
    apply auto
    by (metis boundEval dual_order.trans leD)
next
  case chaos
  then show ?case by auto
next
  case dontCareForm
  then show ?case by auto
qed

lemma absTransfFormSim1:
  "absTransfExp M e \<noteq> dontCareExp \<Longrightarrow> expEval (absTransfExp M e) (abs1 M s) = absTransfConst M (expEval e s)"
  "absTransfForm M f \<noteq> dontCareForm \<Longrightarrow> formEval f s \<Longrightarrow> formEval (absTransfForm M f) (abs1 M s)"
  using absTransfFormSim by auto

subsection \<open>Wellformedness\<close>

text \<open>The statement only assigns to index i\<close>
fun boundAssign :: "nat \<Rightarrow> statement \<Rightarrow> bool" where
  "boundAssign i skip = True"
| "boundAssign i (assign (v, e)) = (\<exists>nm. v = Para nm i \<and> boundVar i e)"
| "boundAssign i (S1 || S2) = (boundAssign i S1 \<and> boundAssign i S2)"
| "boundAssign i (forallStm ps N) = False"

text \<open>The statement is well-formed, with all forallStm over n.\<close>
primrec wellFormedStatement :: "nat \<Rightarrow> statement \<Rightarrow> bool" where
  "wellFormedStatement n skip = True"
| "wellFormedStatement n (assign x) = (\<forall>M. absTransfVar M (fst x) \<noteq> dontCareVar \<longrightarrow> absTransfExp M (snd x) \<noteq> dontCareExp)"
| "wellFormedStatement n (parallel S1 S2) = (wellFormedStatement n S1 \<and> wellFormedStatement n S2)"
| "wellFormedStatement n (forallStm ps N) = (n = N \<and> (\<forall>i. boundAssign i (ps i) \<and> wellFormedStatement n (ps i)))"

lemma varOfSentBoundAssign:
  "boundAssign i S \<Longrightarrow> v \<in> varOfSent S \<Longrightarrow> (\<exists>nm. v = Para nm i)"
proof (induction S)
  case (assign x)
  then show ?case apply (cases x) by auto
qed (auto)

lemma varOfSentBoundAssignValid:
  "boundAssign i S \<Longrightarrow> v \<in> varOfSent S \<Longrightarrow> i \<le> M \<Longrightarrow> absTransfVar M v \<noteq> dontCareVar"
  using varOfSentBoundAssign by fastforce

subsection \<open>Abstraction of statement\<close>

primrec absTransfStatement :: "nat \<Rightarrow> statement \<Rightarrow> statement" where
  "absTransfStatement M skip = skip" |
  "absTransfStatement M (assign as) = 
    (if absTransfVar M (fst as) = dontCareVar 
     then skip
     else assign (fst as, absTransfExp M (snd as)))" |
  "absTransfStatement M (parallel S1 S2) =
    parallel (absTransfStatement M S1) (absTransfStatement M S2)" |
  "absTransfStatement M (forallStm PS N) =
    forallStm (\<lambda>i. absTransfStatement M (PS i)) M"

lemma equivStatementBoundAssign:
  assumes "i \<le> M"
  shows "boundAssign i S \<Longrightarrow> equivStatement (absTransfStatement M S) S"
proof (induction S)
  case skip
  then show ?case by auto
next
  case (assign x)
  show ?case
  proof (cases x)
    case (Pair v e)
    obtain nm where v: "v = Para nm i" "boundVar i e"
      using assign unfolding Pair by auto
    have valid_e: "absTransfExp M e = e"
      using v(2) absBoundVar assms by auto
    have "absTransfStatement M (assign (Para nm i, e)) = assign (Para nm i, e)"
      using valid_e assms by auto
    then show ?thesis
      unfolding Pair v by auto
  qed
next
  case (parallel S1 S2)
  then show ?case
    by (auto simp add: equivStatement_def)
next
  case (forallStm x1 x2a)
  then show ?case by auto
qed

lemma equivStatementForallAbs:
  assumes "\<And>i. boundAssign i (ps i)"
  shows "equivStatement
    (forallStm (\<lambda>i. absTransfStatement M (ps i)) M)
    (forallStm ps M)"
proof -
  have a: "equivStatement (absTransfStatement M (ps i)) (ps i)" if "i \<le> M" for i
    using equivStatementBoundAssign that assms by auto
  have b: "varOfSent (forallStm (\<lambda>i. absTransfStatement M (ps i)) M) = varOfSent (forallStm ps M)"
    apply (auto simp add: varOfSentEq)
    using a unfolding equivStatement_def by auto
  have c: "leastInd v M (\<lambda>i. absTransfStatement M (ps i)) = None \<longleftrightarrow> leastInd v M ps = None" for v
    unfolding leastIndNone using a equivStatement_def by auto
  have d: "leastInd v M (\<lambda>j. absTransfStatement M (ps j)) = Some i \<longleftrightarrow> leastInd v M ps = Some i" for v i
    unfolding leastIndSome using a equivStatement_def by auto
  have e: "trans1 (forallStm (\<lambda>i. absTransfStatement M (ps i)) M) s v = trans1 (forallStm ps M) s v" for s v
    using c[of v] d[of v] apply auto
    by (metis a equivStatement_def leastIndSome)
  show ?thesis
    unfolding equivStatement_def using b e by auto
qed

lemma varOfSentAbs:
  assumes "M \<le> n"
  shows "wellFormedStatement n S \<Longrightarrow>
         v \<in> varOfSent (absTransfStatement M S) \<longleftrightarrow> v \<in> varOfSent S \<and> absTransfVar M v \<noteq> dontCareVar"
proof (induction S)
  case skip
  then show ?case by auto
next
  case (assign x)
  then show ?case by auto
next
  case (parallel S1 S2)
  then show ?case by auto
next
  case (forallStm ps N)
  have a: "boundAssign i (ps i)" for i
    using forallStm(2) by auto
  have b: "Para nm j \<in> varOfSent (ps i) \<longrightarrow> j = i" for nm i j
    using varOfSentBoundAssign[OF a] by auto
  have c: "\<exists>j\<le>N. v \<in> varOfSent (ps j)" "absTransfVar M v \<noteq> dontCareVar"
    if "i \<le> M" "v \<in> varOfSent (absTransfStatement M (ps i))" for i
  proof -
    have c1: "wellFormedStatement n (ps i)" "n = N"
      using forallStm(2) by auto
    have c2: "v \<in> varOfSent (absTransfStatement M (ps i)) = (v \<in> varOfSent (ps i) \<and> absTransfVar M v \<noteq> dontCareVar)"
      apply (rule forallStm(1))
      using c1 by auto
    have c3: "v \<in> varOfSent (ps i)" "absTransfVar M v \<noteq> dontCareVar"
      using c2 that(2) by auto
    show "\<exists>j\<le>N. v \<in> varOfSent (ps j)"
      apply (rule exI[where x=i])
      using assms c1(2) c3(1) le_trans that(1) by blast
    show "absTransfVar M v \<noteq> dontCareVar"
      using c3 by auto
  qed
  have d: "\<exists>j\<le>M. v \<in> varOfSent (absTransfStatement M (ps j))"
    if assmd: "absTransfVar M v \<noteq> dontCareVar" "i \<le> N" "v \<in> varOfSent (ps i)" for i
  proof -
    obtain nm where d1: "v = Para nm i"
      using assmd(3) a[of i] varOfSentBoundAssign by blast
    have d2: "i \<le> M"
      using d1 assmd(1) nat_neq_iff by fastforce
    have d3: "wellFormedStatement n (ps i)" "n = N"
      using forallStm(2) by auto
    have d4: "absTransfVar M v \<noteq> dontCareVar"
      using d1 d2 by auto
    have d5: "v \<in> varOfSent (absTransfStatement M (ps i)) = (v \<in> varOfSent (ps i) \<and> absTransfVar M v \<noteq> dontCareVar)"
      apply (rule forallStm(1))
      using d3 by auto
    show ?thesis
      apply (rule exI[where x=i])
      unfolding d5 by (auto simp add: d2 d4 assmd(3))
  qed
  show ?case
    by (auto simp add: varOfSentEq c d)
qed


lemma absStatement:
  assumes "M \<le> n"
  shows "wellFormedStatement n S \<Longrightarrow>
         abs1 M (trans1 S s) = trans1 (absTransfStatement M S) (abs1 M s)"
proof (induction S)
  case skip
  then show ?case by auto
next
  case (assign x)
  have a: "abs1 M (\<lambda>a. if v = a then expEval e s else s a) w = abs1 M s w"
    if "absTransfVar M v = dontCareVar" "x = (v, e)" for v e w
  proof -
    have "v = dontCareVar \<or> (\<exists>n i. i > M \<and> v = Para n i)"
      using that apply (cases v) apply auto
      by (meson varType.distinct(5))
    then show ?thesis
      apply (cases w) by auto
  qed
  have b: "abs1 M (\<lambda>a. if v = a then expEval e s else s a) w =
           (if v = w then expEval (absTransfExp M e) (abs1 M s) else abs1 M s w)"
    if "absTransfVar M v \<noteq> dontCareVar" "x = (v, e)" for v e w
  proof -
    have valid_e: "absTransfExp M e \<noteq> dontCareExp"
      using assign that by auto
    have "(\<exists>n. v = Ident n) \<or> (\<exists>n i. i \<le> M \<and> v = Para n i)"
      using that apply (cases v) apply auto
      by (meson leI)
    then show ?thesis
      apply (cases w) apply auto
      using valid_e absTransfFormSim1(1) by auto
  qed
  show ?case
    apply (cases x)
    subgoal for v e apply auto
      using a apply auto[1]
      using b apply auto[1]
      done
    done
next
  case (parallel S1 S2)
  have a: "wellFormedStatement n S1" "wellFormedStatement n S2"
    using parallel(3) by auto
  have b: "v \<in> varOfSent (absTransfStatement M S1) \<longleftrightarrow> v \<in> varOfSent S1 \<and> absTransfVar M v \<noteq> dontCareVar" for v
    using varOfSentAbs[OF assms a(1)] by auto
  have c: "abs1 M (\<lambda>a. if a \<in> varOfSent S1 then trans1 S1 s a else trans1 S2 s a) w =
           (if w \<in> varOfSent (absTransfStatement M S1) then
              abs1 M (trans1 S1 s) w
            else
              abs1 M (trans1 S2 s) w)" for w
    unfolding abs1Eq b by auto
  show ?case
    using parallel c by auto 
next
  case (forallStm ps N)
  have a: "n = N"
    using forallStm(2) by auto
  have b: "boundAssign i (ps i)" "wellFormedStatement n (ps i)" for i
    using forallStm(2) by auto
  have c: "v \<in> varOfSent (absTransfStatement M (ps i)) \<longleftrightarrow> v \<in> varOfSent (ps i) \<and> absTransfVar M v \<noteq> dontCareVar" for v i
    by (rule varOfSentAbs[OF assms b(2)])
  have d: "abs1 M (trans1 (ps i) s) = trans1 (absTransfStatement M (ps i)) (abs1 M s)" for i
    using forallStm(1)[OF _ b(2)] by auto
  have e: "leastInd v M (\<lambda>i. absTransfStatement M (ps i)) = None \<longleftrightarrow>
           leastInd v N ps = None \<or> absTransfVar M v = dontCareVar" for v
    unfolding leastIndNone c apply auto
     apply (metis absTransfVar.simps(2) b(1) not_le_imp_less varOfSentBoundAssign)
    using a assms by auto
  have f: "leastInd v M (\<lambda>j. absTransfStatement M (ps j)) = Some i \<longleftrightarrow>
           leastInd v N ps = Some i \<and> absTransfVar M v \<noteq> dontCareVar" for v i
    unfolding leastIndSome c apply auto
    using a assms dual_order.trans apply blast
      apply (metis b(1) varOfSentBoundAssign varType.inject(2))
    using b(1) not_le_imp_less varOfSentBoundAssign apply fastforce
    using a assms order_trans by blast
  have g: "abs1 M (\<lambda>a. case leastInd a N ps of None \<Rightarrow> s a | Some i \<Rightarrow> trans1 (ps i) s a) w =
            (case leastInd w M (\<lambda>i. absTransfStatement M (ps i)) of
               None \<Rightarrow> abs1 M s w
             | Some i \<Rightarrow> abs1 M (trans1 (ps i) s) w)" for w
    unfolding abs1Eq using e f
    by (smt option.case_eq_if option.collapse)
  show ?case
    apply auto unfolding d[symmetric] using g by auto
qed

subsection \<open>Simplified abstraction for statement\<close>

primrec absTransfStatement2 :: "nat \<Rightarrow> statement \<Rightarrow> statement" where
  "absTransfStatement2 M skip = skip" |
  "absTransfStatement2 M (assign as) = 
    (if absTransfVar M (fst as) = dontCareVar 
     then skip
     else assign (fst as, absTransfExp M (snd as)))" |
  "absTransfStatement2 M (parallel S1 S2) =
    (if absTransfStatement2 M S1 = skip then absTransfStatement2 M S2
     else if absTransfStatement2 M S2 = skip then absTransfStatement2 M S1
     else parallel (absTransfStatement2 M S1) (absTransfStatement2 M S2))" |
  "absTransfStatement2 M (forallStm PS N) =
    forallStm PS M"

lemma absStatementEq:
  assumes "M \<le> N"
  shows "wellFormedStatement N S \<Longrightarrow>
         equivStatement (absTransfStatement M S) (absTransfStatement2 M S)"
proof (induction S)
  case skip
  then show ?case by auto
next
  case (assign x)
  then show ?case by auto
next
  case (parallel S1 S2)
  have a: "equivStatement (absTransfStatement M S1) (absTransfStatement2 M S1)"
    using parallel by auto
  have b: "equivStatement (absTransfStatement M S2) (absTransfStatement2 M S2)"
    using parallel by auto
  have c: "equivStatement
            (absTransfStatement M S1 || absTransfStatement M S2)
            (absTransfStatement2 M S1 || absTransfStatement2 M S2)"
    using a b by (auto intro: equivStatementParallel)
  show ?case
    apply (cases "absTransfStatement2 M S1 = skip")
    subgoal
      apply auto apply (rule equivStatementTrans[OF c])
      using b equivStatementSkipLeft equivStatementTrans by auto
    apply (cases "absTransfStatement2 M S2 = skip")
    subgoal
      apply auto apply (rule equivStatementTrans[OF c])
      by (metis equivStatementSkipRight)
    using c by auto
next
  case (forallStm ps N')
  show ?case
    apply auto
    apply (rule equivStatementForallAbs)
    using forallStm(2) by auto
qed

lemma absStatement2:
  assumes "M \<le> N"
  shows "wellFormedStatement N S \<Longrightarrow>
         abs1 M (trans1 S s) = trans1 (absTransfStatement2 M S) (abs1 M s)"
  using absStatement absStatementEq assms equivStatement_def by auto


subsection \<open>Abstraction of rules, simulation relation\<close>

fun topTransfForm :: "formula \<Rightarrow> formula" where
  "topTransfForm f = (if f = dontCareForm then chaos else f)"

fun wellFormedRule :: "nat \<Rightarrow> rule \<Rightarrow> bool" where
  "wellFormedRule M (guard g a) = wellFormedStatement M a"

fun absTransfRule :: "nat \<Rightarrow> rule \<Rightarrow> rule" where
  "absTransfRule M (guard g a) =
     guard (topTransfForm (absTransfForm M g)) (absTransfStatement2 M a)"

definition transSimRule :: "rule \<Rightarrow> rule \<Rightarrow> nat \<Rightarrow> bool" where
  "transSimRule r1 r2 M =
    (\<forall>s. formEval (pre r1) s \<longrightarrow> formEval (pre r2) (abs1 M s) \<and>
         abs1 M (trans1 (act r1) s) = trans1 (act r2) (abs1 M s))"

lemma absRuleSim:
  assumes "M \<le> N"
    and "wellFormedRule N r"
  shows "transSimRule r (absTransfRule M r) M"
  unfolding transSimRule_def
  apply auto
  subgoal for s
    apply (cases r)
    using absTransfFormSim1(2) by auto
  subgoal for s
    apply (cases r)
    apply auto apply (rule absStatement2[OF assms(1)])
    using assms(2) by auto
  done

definition transSimRules :: "rule set \<Rightarrow> rule set \<Rightarrow> nat \<Rightarrow> bool" where
  "transSimRules rs1 rs2 M = (\<forall>r\<in>rs1. \<exists>r'\<in>rs2. transSimRule r r' M)"

lemma transSimRulesUnion:
  "transSimRules rs1 rs2 M \<Longrightarrow> transSimRules rs3 rs4 M \<Longrightarrow> transSimRules (rs1 \<union> rs3) (rs2 \<union> rs4) M"
  unfolding transSimRules_def by auto

lemma transSimRulesAbs:
  assumes "M \<le> N"
    and "\<And>i. wellFormedRule N (rf i)"
  shows "transSimRules (rf ` {0..N}) ((\<lambda>i. absTransfRule M (rf i)) ` {0..N}) M"
  unfolding transSimRules_def using absRuleSim assms by blast


text \<open>f2 simulates f1 on the abstract state\<close>
definition predSim :: "formula \<Rightarrow> formula \<Rightarrow> nat \<Rightarrow> bool" where
  "predSim f1 f2 M = (\<forall>s. formEval f1 s \<longrightarrow> formEval f2 (abs1 M s))"

definition predSimSet :: "formula set \<Rightarrow> formula set \<Rightarrow> nat \<Rightarrow> bool" where
  "predSimSet fs1 fs2 M = (\<forall>f2\<in>fs2. \<exists>f1\<in>fs1. predSim f1 f2 M)"

lemma transSimRulesReachable:
  assumes "predSimSet fs1 fs2 M"
    and "transSimRules rs1 rs2 M"
  shows "reachableUpTo fs1 rs1 i s \<Longrightarrow> reachableUpTo fs2 rs2 i (abs1 M s)"
proof (induction i arbitrary: s)
  case 0
  have a: "formEval f1 s" if "f1 \<in> fs1" for f1
    using reachableUpTo0[OF 0] that by auto
  have b: "formEval f2 (abs1 M s)" if assmb: "f2 \<in> fs2" for f2
  proof -
    obtain f1 where b1: "f1 \<in> fs1" "predSim f1 f2 M"
      using assms(1) unfolding predSimSet_def using assmb by auto
    then show ?thesis
      unfolding predSim_def using a(1) by auto
  qed
  show ?case 
    apply (rule reachableSet0)
    using b by auto
next
  case (Suc i)
  obtain s' g a where a: "s = trans1 a s'" "reachableUpTo fs1 rs1 i s'" "(g \<triangleright> a) \<in> rs1" "formEval g s'"
    using reachableUpToSuc[OF Suc(2)] by metis
  obtain r2 where b: "r2 \<in> rs2" "transSimRule (g \<triangleright> a) r2 M"
    using assms(2) a(3) unfolding transSimRules_def by auto
  have c: "formEval (pre r2) (abs1 M s')"
    using b(2) a(4) unfolding transSimRule_def by auto
  have d: "abs1 M (trans1 a s') = trans1 (act r2) (abs1 M s')"
    using b(2) a(4) unfolding transSimRule_def by auto
  have e: "reachableUpTo fs2 rs2 i (abs1 M s')"
    by (rule Suc(1)[OF a(2)])
  show ?case
    unfolding a(1) d
    apply (rule reachableSetNext[OF e _ c])
    using b(1) apply (cases r2) by auto
qed

end
