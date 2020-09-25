(*  Title:     paraTheory.thy
    Author:    Yongjian Li, State Key Laboratory of Computer Science, Institute of Software,
Chinese Academy of Sciences
    Copyright   2016  State Key Laboratory of Computer Science, Institute of Software,
Chinese Academy of Sciences

A mechanical theory for verification of parameterized protocols like cache coherence protocols
*)

theory paraTheory imports Main 
begin

section{*Datatypes to define variables, values, expressions, and formulas*}



datatype varType=Ident  string | Para varType  nat |Field  varType   string 
text{*
Three kinds of variables used in the protocols. 
1. simple identifiers to define global variables 
2. array variables ----arr[i]
3. record variables -----rcd.f*}


datatype scalrValueType=enum string string |index nat | boolV bool
text{*
Three kinds of values used in the protocols.
1. enumerating values
2. natural numbers 
3. Boolean values*}


datatype expType= IVar varType   |  
         Const scalrValueType |
         iteForm formula  expType  expType 

and  formula = eqn expType expType|
               andForm  formula formula |
               neg formula|
               orForm formula formula | 
               implyForm formula formula |
               chaos 

text{*
$Experssions$ and $formulas$ are defined mutually recursively.
 $Experssions$ can be simple or compound. 
A simple expression is either a variable or a constant, 
while a compound expression is constructed with the ite(if-then-else) form. 
A $formula$ can be an atomic formula or a compound formula.
An atomic formula can be a boolean variable or constant, 
or in the equivalence forms. A $formula$ can also be constructed by 
using the logic connectives, including negation, conjunction, 
disjunction, implication.
*}
              
section{*Datatypes to define assignments, statements, rules*}

type_synonym assignType=  "varType \<times>   expType"

datatype statement=  skip| assign assignType          |
                  parallel assignType  statement
text{*A statement is is just a lists of assignments, 
but these assignments are extecuted in parallel, 
\emph{not} in a sequential order*}

type_synonym paraStatement= "nat \<Rightarrow> statement"
text{*A parameterized statement is just a function from a 
parameter to a statement. *}



primrec cat::"statement \<Rightarrow> statement \<Rightarrow>statement" where
cat1:"cat (assign a) S=parallel a S" |
cat2:"cat (parallel a S1) S=parallel a (cat S1 S)"|
cat3:"cat skip S= S"
text{*For conveniece, we also define the concatation of statements.*}

primrec  parallelList::"statement list \<Rightarrow> statement" where
"parallelList [] = skip"|
"parallelList (S1#SL) = cat S1 (parallelList (SL))" 

fun  forallSent::"nat list\<Rightarrow>paraStatement \<Rightarrow> statement"  where
oneSent: "forallSent ([i])  paraS = paraS i"|
moreSent:" forallSent  (i#xs ) paraS=cat (paraS i) (forallSent (xs) paraS)  " 
 



type_synonym paraFormula="nat \<Rightarrow> formula"
text{*Similarly, a parameterized formula is a function from 
a parameter to a formula. We also define  the $\mathsf{forall}$ 
and $mathsf{exists}$ formulas$.*}

fun forallForm::"nat list \<Rightarrow>paraFormula \<Rightarrow> formula" where
oneAllForm: "forallForm [i] forms = forms i"|
moreAllForm: "forallForm (i#j#xs)  forms = andForm (forms i) (forallForm (j#xs)  forms)"


fun existsForm::"nat list \<Rightarrow>paraFormula \<Rightarrow> formula" where
oneExForm: " existsForm [i] forms = forms i"|
moreExForm: " existsForm (i#j#xs)  forms = orForm (forms i) (forallForm (j#xs)  forms)"




datatype rule =  guard formula  statement
text{*With the formalizatiion of formula and statement, 
it is natural to define a rule. A guard and
 statement of a rule are also defined for convenience. *}


primrec pre::"rule \<Rightarrow> formula" where
"pre (guard f a)=f"

primrec act::"rule \<Rightarrow>statement" where
"act  (guard f a)=a"



type_synonym paraRule=" nat \<Rightarrow> rule"
text{*A parameterized rule is just from a natural number to a rule.*}



section{*semantics of a protocol*}


type_synonym state= "varType \<Rightarrow> scalrValueType "
text{*A  state of a protocol  is an instantaneous snapshot of its 
 behaviour given by an assignment of  values to variables of
the circuit. Therefore, we define:*}

text{*The formal semantics of an expression and a formula is 
formalized as follows:*}
primrec expEval :: "expType \<Rightarrow> state \<Rightarrow> scalrValueType" and 
 formEval :: "formula \<Rightarrow> state \<Rightarrow>bool"  where
 
evalVar:"expEval  (IVar ie) s =  ( s ie)" |
"expEval  (Const i) s =  i"  |
"expEval  (iteForm f e1 e2) s= 
   ( if (formEval f s) then     (expEval e1 s)
   else (expEval e2 s))"  |

evalEqn: "formEval (eqn e1 e2) s= ((expEval e1 s) = (expEval e2 s))" |
evalAnd: "formEval ( andForm f1 f2) s=( (formEval f1 s) \<and> (formEval f2 s))"|
evalNeg: "formEval (neg f1 ) s= ( \<not>(formEval f1 s))"|
evalOr: "formEval (orForm f1 f2) s=( (formEval f1 s) \<or>  (formEval f2 s))"|
evalImp:"formEval (implyForm f1 f2) s= ( (formEval f1 s) \<longrightarrow>  (formEval f2 s))" |
"formEval chaos s=True"


text{*A state transition from a state to another state, which is caused by 
an execution of a statement, is  defined as follows:*}

primrec statement2Assigns::"statement \<Rightarrow> assignType list" where
"statement2Assigns (assign asgn)=[asgn]" |
"statement2Assigns (parallel a S)=a#statement2Assigns S"|
"statement2Assigns (skip)=[]" 

definition wellformedAssgnList::"assignType list => bool" where
" wellformedAssgnList asgns\<equiv>distinct (map fst asgns)"
text{* Condition wellformedAssgnList guranttees that asgns assign different 
variables to values*}

primrec transAux:: "assignType list \<Rightarrow> state \<Rightarrow>state " where
"transAux [] s= s " |
"transAux (pair#asgns) s=( transAux asgns s) ((fst pair):= expEval  (snd pair) s) "

definition trans:: "statement \<Rightarrow> state \<Rightarrow>state " where [simp]:
"trans S s \<equiv> transAux (statement2Assigns S) s"

text{*Here we must point out the fact that the assignments in a 
parallel assignment is executed in parallel, and the statement can be 
transformed into a wellformedAssgnList, 
therefore we always assign an evaluation of an expression in 
the state $s$ to the corresponding variable.*}



text{*The reachable sate set of a protocol, 
which is describled by a set of initiate formulas and a set of rules,
 can be formalized inductively as follows:*}


inductive_set reachableSet::" formula set\<Rightarrow> rule set \<Rightarrow>state set" 
  for  inis::"formula set"  and rules::"rule set"   where

initState:  "\<lbrakk>formEval  ini s; ini \<in>  inis\<rbrakk>  \<Longrightarrow>(  s \<in>  ( reachableSet inis rules))" |

oneStep:    " \<lbrakk>s \<in>  reachableSet inis rules ;
               r \<in>   rules ;formEval (pre r ) s \<rbrakk> \<Longrightarrow>  trans  (act r ) s  \<in>  reachableSet inis rules"

text{*The rule $\mathsf{initState}$ says that a state $s$ is 
in $\mathsf{reachableSet}~inis~ rules$ if
 there exists a formula $ini$ that is true in state $s$.
 Next rule $\mathsf{oneStep}$ says that 
$$\mathsf{ trans}~  ($\mathsf{act}~ r )~ s $ is also in
 $\mathsf{reachableSet}~inis~ rules$ if $s$ already is in 
 $\mathsf{reachableSet}~inis~ rules$ and $r \<in> rules$.*}


section{*substitions and  preconditions *}

primrec valOf::"assignType list \<Rightarrow> varType =>expType"  where
"valOf [] v=IVar v" |
"valOf (x#xs) v= (if ((fst x) =v) then (snd x) else valOf xs v)"
text{*Let $asgn\!=\![(v_1,e_1),\ldots,(v_n,e_n)]$ be an assignment,
 valOf asgn $x_i$ is the expression $e_i$ assigned to $v_i$*}

lemma lemmaOnValOf:
  shows "expEval (valOf (statement2Assigns S) v) s = transAux ( statement2Assigns S) s v" 
  (is "?LHS1 S =?RHS1 S")
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

text{*This lemma says that the value of (statement2Assigns S) assigned to variable v, which is evaluated 
at the state s, is the same as that of v at the result  state  after execution of S from state s*}

primrec substExp :: "expType\<Rightarrow> assignType list \<Rightarrow>expType"  and 
substForm ::"formula \<Rightarrow> assignType list \<Rightarrow> formula" where

substExpVar: "substExp  (IVar v') asgns=   (valOf  asgns v')  "| 

substExpConst: "substExp  (Const i)  asgns= Const i" |

substExpite: "substExp  (iteForm f e1 e2)  asgns= 
  (iteForm (substForm f asgns) (substExp e1  asgns) (substExp e2  asgns))"| 
"substForm (eqn l r)  asgns=
  (eqn (substExp l  asgns) (substExp r  asgns))"  |
"substForm ( andForm f1 f2)  asgns = 
  (andForm (substForm f1  asgns)  (substForm f2  asgns))"|
"substForm (neg f1 )   asgns=
   (neg ( substForm f1  asgns ))"|
"substForm (orForm f1 f2)   asgns=
   ( orForm (substForm f1  asgns )  (substForm f2  asgns))"|
"substForm (implyForm f1 f2)   asgns= 
  (implyForm (substForm f1 asgns)  (substForm f2  asgns))" |
"substForm  chaos   asgns=chaos"

text{*$\mathsf{substExp}~asgn~e$ ($\mathsf{substForm}~asgn~f$)
 denotes the expression $e$ (formula $f$) in which the occurrence of variable
  $x_i$ is replaced by $e_i$.*}

definition  substExpByStatement ::"expType \<Rightarrow>statement \<Rightarrow>expType"   where [simp]:
"substExpByStatement e S\<equiv>substExp e (statement2Assigns S)" 

definition substFormByStatement ::"formula \<Rightarrow>statement \<Rightarrow>formula"   where [simp]:
"substFormByStatement f S\<equiv>substForm f (statement2Assigns S)" 
text{*A statement $S$ can be transformed into an assignment to some variables
 $x_i$,  which is formalized by $\mathsf{statement2Assigns}~ S$.  
we use substExpByStatement e S and  substFormByStatement f S to denote the 
formula transformed from $f$  by substituting each $x_i$ with $e_i$. 
Furthermore, substFormByStatement f S  can be regarded as the weakest 
precondition of formula $f$ w.r.t. statement $S$. As Hoare logics specifies, *}


lemma  preCondOnExp:
  
  shows "(expEval (substExpByStatement e S) s =expEval e (trans S s)) \<and>
         (formEval (substFormByStatement f S) s = formEval f (trans S s))"           
    (is "((  ?LHS e S=?RHS e S)\<and> ( ?LHS1 f S=?RHS1 f S))")
proof(induct_tac e and f)
      fix v
      let ?e="(IVar v)"
      show  "?LHS ?e S=?RHS ?e S"
      by (simp add: lemmaOnValOf)
      
next 
  fix n
  let ?e="(Const n)"
      show  "?LHS ?e S=?RHS ?e S"
      apply( simp)
      done
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
qed


section{*causal relations and consistency lemma*}
text{*A novel feature of our work lies in that three kinds of causal
relations are exploited, which are essentially special cases of the
general induction rule.  Consider a rule $r$, a formula $f$, and a formula set $fs$, three
 kinds of causal relations are defined as follows:*}

definition invHoldForRule1::" state \<Rightarrow> formula \<Rightarrow> rule \<Rightarrow> bool" where [simp]:
"invHoldForRule1 s f  r \<equiv>  
(formEval (pre r) s \<longrightarrow>  formEval  (substFormByStatement f  (act r)) s )"
text{* $\mathsf{invHoldRule}_1(s,f, r)$ means that after rule $r$ is executed, $f$ becomes true immediately;*}

 definition invHoldForRule2::" state \<Rightarrow> formula \<Rightarrow> rule \<Rightarrow> bool" where [simp]:
"invHoldForRule2 s f  r \<equiv>  
(formEval  (substFormByStatement f  (act r)) s  =  formEval f s)"
text{*$\mathsf{invHoldRule}_2(s,f, r)$ states that $\mathsf{preCond}(S,f)$ is equivalent to $f$, 
which intuitively means that none of state variables in $f$ is changed, and the execution of 
statement $S$ does not affect the evaluation of $f$;*}

definition  invHoldForRule3::"state \<Rightarrow> formula \<Rightarrow> rule \<Rightarrow>formula set\<Rightarrow> bool"  where [simp]:
"invHoldForRule3 s f r fs  \<equiv>  
(let pref=substFormByStatement f (act r) in
(\<exists>f'. f' \<in> fs \<and>  (formEval   (andForm (pre r)  f') s\<longrightarrow> formEval  pref s)))"  
text{*$\mathsf{invHoldRule}_3(s,f, r,fs)$ states that there exists another invariant $f' \in fs$ such that
  the conjunction of the guard of $r$ and $f'$ implies the precondition  $\mathsf{preCond}(S,f)$.*}

abbreviation invHoldForRule::"state \<Rightarrow>formula \<Rightarrow> rule \<Rightarrow> (formula set) \<Rightarrow> bool" where
  "invHoldForRule s inv0 r invs \<equiv>
    invHoldForRule1 s inv0 r \<or>  invHoldForRule2 s inv0 r \<or>   invHoldForRule3 s inv0 r invs "

text{*The relation $\mathsf{invHoldRule}(s, f,r,fs)$ defines a causality relation
between $f$, $r$, and $fs$, which guarantees that if each formula in $fs$ holds
before the execution of rule $r$, then $f$ holds after the execution of rule $r$.
We can also view $\mathsf{invHoldRule}(s, f, r, fs)$ as a
special kind of inductive tactics, which can be applied to prove
each formula in $fs$ holds at each inductive protocol rule cases. 
Note that the three kinds of inductive tactics can be done by a theorem prover, 
which is the cornerstone of our work.

With the $\mathsf{invHoldRule}$ relation, we define a consistency relation 
$\mathsf{consistent}( invs,inis, rs)$ between a protocol $(inis,rs)$ and a
 set of invariants $invs=\{inv_1,\ldots, inv_n\}$. *}


definition consistent::"formula set \<Rightarrow> formula set \<Rightarrow> rule set \<Rightarrow>bool"  where
"consistent invs inis rs \<equiv>
(\<forall>inv ini s. (inv \<in> invs \<longrightarrow> ini\<in> inis\<longrightarrow> formEval ini s \<longrightarrow> formEval inv s)) \<and>
 (\<forall> inv r s.  (inv \<in>invs  \<longrightarrow> r \<in> rs \<longrightarrow> invHoldForRule s inv r invs  ))"   

text{*For any invariant $inv \in invs$, $inv$ holds at a reachable state $s$  of a protocol $P=(ini,rs)$
  if the consistency relation
$\mathsf{consistent}( invs, inis, rs)$ holds. 
The following lemma formalizes the essence of the aforementioned causal relation, 
and is called consistency lemma.*}

lemma consistentLemma:
  assumes a1:"consistent invs inis rs" and a2:"s \<in> reachableSet inis rs" 
  shows "\<forall> inv. inv \<in> invs \<longrightarrow>formEval inv s"  (is "?P s")
  using a2
  proof induct
    case (initState ini s)
    show "?P s"
      apply(cut_tac a1, unfold consistent_def)
      by (metis (lifting) initState(1) initState(2))
  next
    case (oneStep s r)
    show "?P  (trans (act r) s)"    
    proof (rule allI, rule impI)
      fix inv
      assume b1:"inv \<in> invs"
      have b2:" invHoldForRule3 s inv r  invs \<or> invHoldForRule2 s inv r   \<or> invHoldForRule1 s inv r  "
        apply(cut_tac a1, unfold consistent_def)
        by (metis b1 oneStep(3))
        
     moreover
      { assume c1:"invHoldForRule3 s inv r invs"
        
        let ?pref="substFormByStatement inv (act r)"
          have b3:"  ( (\<forall> f'.  f' \<in>  invs\<longrightarrow>formEval f'  s) \<longrightarrow>formEval (pre r)  s\<longrightarrow> formEval  ?pref s)  "  (is " ?P fs ")
           apply (cut_tac c1, unfold invHoldForRule3_def,auto)
          done

        then have b3':"?P fs  "
          by blast

        have b4:" (\<forall> f'.  f' \<in>  invs\<longrightarrow>formEval f'  s)"
          apply(cut_tac b3' )
          by (metis (no_types) oneStep(2))

        have b5:"formEval (pre r) s"
          by (metis (lifting) oneStep(4))

        have b6:"formEval ?pref s"
         by(cut_tac b4 b5 b3', auto)

        have "formEval inv (trans (act r) s)"
           apply(cut_tac b6,metis preCondOnExp)
            done
      }
     
     moreover
      {assume b1':"invHoldForRule2 s inv r "
        have b2:"formEval inv s"
        by (metis b1 oneStep.hyps(2))
        
        let ?pref="substFormByStatement inv (act r)"
        have b3:" (  formEval  ?pref s  =  formEval inv s)"
        by(cut_tac b1',unfold  invHoldForRule2_def,simp)
        
        with b2 have b4:"formEval ?pref s"
          by auto
          
        have "formEval inv (trans (act r) s)"
        by (cut_tac b4,  metis preCondOnExp)
         
      }
      moreover
      {assume b1':"invHoldForRule1 s inv r "
         
         have b5:"formEval (pre r) s"
          by (metis (lifting) oneStep(4))
        
         have "formEval inv (trans (act r) s)"
           apply(subgoal_tac "formEval (substFormByStatement inv (act r)) s")
           apply (metis preCondOnExp)
           apply(cut_tac b1' b5)
           by(unfold invHoldForRule1_def,auto)
       
       }
       ultimately show "formEval inv (trans (act r) s)"
         by blast
     qed
 qed  


section{*miscellaneous definitions and lemmas*}

text{*Variables of a variable, an expression, a formula, and a statement is defined by
varsOfVar, varOfExp, varOfForm and varOfSent respectively*}

definition varsOfVar::" varType \<Rightarrow> varType set"  where  [simp]:
" varsOfVar x  = set [x]" 

primrec varOfExp::"expType \<Rightarrow> varType set"  and
  varOfForm::"formula \<Rightarrow> varType set"  where 

"varOfExp  (IVar v) =   varsOfVar v" |
"varOfExp   (Const j) =  set []" |

"varOfExp   (iteForm f e1 e2) = ((varOfForm f) \<union>  (varOfExp   e1 )  \<union>   (varOfExp  e2))" |

"varOfForm   (eqn e1 e2) =  ( (varOfExp   e1 )  \<union>  (varOfExp  e2))" |
"varOfForm   ( andForm f1 f2) =  (  (varOfForm  f1 )   \<union> (varOfForm  f2 ))"|
"varOfForm   (neg f1 ) = (  (varOfForm   f1 ))"|
"varOfForm   (orForm f1 f2) =(  (varOfForm   f1 )   \<union>   (varOfForm  f2 ))"|
"varOfForm   (implyForm f1 f2) = (  (varOfForm  f1 )  \<union>  (varOfForm f2 ))"|
"varOfForm   (chaos) ={}"

primrec  varOfSent::"statement \<Rightarrow> varType set" where
" varOfSent  (assign a)=( varsOfVar  (fst a)) "|
" varOfSent  skip={} "|
" varOfSent  ( parallel a sent2)= (( varsOfVar  (fst a)) \<union>  (varOfSent  sent2))"

primrec varOfFormList::"formula list \<Rightarrow> varType set" where
"varOfFormList [] = {}" |
"varOfFormList (f#fs) =(varOfForm  f) \<union> (varOfFormList fs)"

lemma varsOfSent1:
  " (varOfSent S) = set (map fst (statement2Assigns S))"
  proof(induct_tac S,auto) qed 

primrec down ::"nat \<Rightarrow>nat list" where
"down 0=[0]" |
"down (Suc n)=Suc n #(down n)"

lemma simpDown:"down 5=[5,4,3,2,1,0]"
 by (simp add: eval_nat_numeral(2) eval_nat_numeral(3))

lemma downNIsNotEmpty:
  "\<exists> j xs. down N= j#xs" (is "?P N")
  proof(induct_tac N,auto)qed   




 
 

text{*definitions and lemmas on forallForm formula constructor*}  

lemma forall1:
  shows "\<forall> i. i \<le> N \<longrightarrow>formEval (forallForm (down N) pf ) s\<longrightarrow>formEval (pf i) s" (is "?P N")  
proof(induct_tac N)
    show "?P  0"
      by simp
  next
    fix N
    assume b1:"?P N"
    show "?P  (Suc N)"
      proof(case_tac "N =0")
        assume c1:"N=0"
        show "?P  (Suc N)"
        proof(cut_tac c1, auto,case_tac "i=0", auto,case_tac "i=1",auto)qed
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
  shows "(\<forall> i. i \<le> N \<longrightarrow>formEval (pf i) s) \<longrightarrow> formEval (forallForm (down N) pf ) s" (is "?P N")  
proof(induct_tac N)
    show "?P  0"
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
        by (metis down.simps(2) downNIsNotEmpty evalAnd paraTheory.moreAllForm)
    qed   
  qed     

lemma forall2:
   "(\<forall> i. i \<le> N \<longrightarrow>formEval (pf i) s) \<Longrightarrow> formEval (forallForm (down N) pf ) s"
  by (simp add: forall2Aux)  
        

lemma forallLemma [simp,intro]:
  assumes a1:"i \<le> N" and a2:"formEval (forallForm (down N) pf ) s"
  shows "formEval (pf i) s"
  using a1 a2 forall1 less_imp_le by blast

lemma forallLemma1:
  assumes a1:"i \<le> N" and a2:"formEval (forallForm (down N) pf ) s"
  and a3:"formEval (pf i) s  \<longrightarrow> A"
  shows "A"
  using a1 a2 a3 by blast

lemma forallMono[intro,simp]:
  assumes a1:"formEval (forallForm (down N) f) s" and a2:"N' < N"
  shows "formEval (forallForm (down N') f) s"
proof(rule forall2)
  show "(\<forall> i. i \<le> N' \<longrightarrow>formEval (f i) s)"
    by (meson Suc_leI a1 a2 forall1 le_SucI le_trans) 
qed  

subsection{*lemmas on varsOf*}  

lemma varsOnCat[simp]:
  shows "varOfSent (cat S1 S2)=(varOfSent S1 ) \<union> (varOfSent S2 )"
  apply(induct_tac S1)
    apply simp
   apply simp
  apply simp
  done

lemma   forallVars:
  assumes a1:"\<forall> i.( varOfSent (paraForm i))\<inter> varSet ={}"
   shows  "(varOfSent (forallSent (down N) paraForm))\<inter> varSet ={}"
  proof(induct_tac N)
    show " varOfSent (forallSent (down 0) paraForm) \<inter> varSet = {}"
      apply(cut_tac a1,force) 
      done
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

lemma   forallVars1[simp,intro!]:
  assumes a1:"\<forall>i. v \<notin>( varOfSent (paraForm i))"
   shows  "v \<notin>(varOfSent (forallSent (down N) paraForm))" (is "?P N")
  proof(induct_tac N)
    show "?P 0"
      apply(cut_tac a1,force) 
      done
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
  "i \<le>N \<longrightarrow>v \<in> varOfSent (paraForm i) \<longrightarrow> v \<in> varOfSent (forallSent (down N) paraForm)" ( is "?P N")
proof(induct_tac N)
  show "?P 0"
   by auto
   next
    fix N
   assume a1:"?P N" 
   show "?P (Suc N)"
   proof(rule impI)+
    
    assume b0:"i \<le> Suc N" and b1:"  v \<in> varOfSent (paraForm i)"  
    have b2:"  varOfSent  (forallSent (down (Suc N)) paraForm) = varOfSent (paraForm (Suc N)) \<union>   varOfSent (forallSent (down N) paraForm)"
     by (metis down.simps(2) downNIsNotEmpty paraTheory.moreSent varsOnCat) 
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
"v \<notin> set (map fst   (statement2Assigns S)) \<Longrightarrow>
 v \<in>set( map fst (statement2Assigns  (cat S S'))) = (v \<in> set (map fst   (statement2Assigns S'))) "
by (metis Un_iff varsOfSent1 varsOnCat)



lemma ForallSentForm [simp]:
  shows a1:" (statement2Assigns (forallSent (down N)  (\<lambda>i. assign (Para n i, e' i))))=map (\<lambda>i. (Para n i, e' i)) (down N)" (is "?P N")
proof(induct_tac N)
  show "?P 0"
    apply simp
    done
next
  fix N
  assume b1:"?P N"
  show "?P (Suc N )"
  proof(cut_tac b1, simp)
    have b2:"\<exists> j xs. down N= j#xs"
      by (metis downNIsNotEmpty) 
  then obtain j xs where b2:"down N=j#xs" by blast
    show"  statement2Assigns (forallSent (Suc N # down N) (\<lambda>i. assign (Para n i, e' i))) = 
           (Para n (Suc N), e' (Suc N)) # map (\<lambda>i. (Para n i, e' i)) (down N)"
      apply(cut_tac b1 b2,simp)
      done
  qed
qed

subsection{*more lemmas on valOf operator*}

text{*more lemmas on valOf operator*}

lemma valOfLemma[simp]: "i \<le> N \<longrightarrow> (valOf (map (\<lambda>i. (Para v i, e i)) (down N)) (Para v i))=e i"
  apply(induct_tac N)
  apply simp
  apply auto
done   

lemma valOfLemma2Aux[simp]: "(var' \<notin> set (map fst xs)) \<longrightarrow> (valOf xs (var'))=IVar var'"
  apply(induct_tac xs)
  apply simp
  apply auto
done  

lemma valOfLemma2[simp,intro]: "(var' \<notin> set (map fst xs)) \<Longrightarrow> (valOf xs (var'))=IVar var'"
by (metis (lifting) valOfLemma2Aux)
  
lemma valOfLemma3 [simp]:"(\<forall> i.  var' \<noteq> Para v i) \<Longrightarrow>  (valOf (map (\<lambda>i. (Para v i, e i)) (down N)) var')=IVar var'"
apply(rule valOfLemma2)
apply(induction N)
by auto

lemma valOfLemma4Aux :"v \<notin> set (map fst   (statement2Assigns S)) \<longrightarrow>( valOf (statement2Assigns  (cat S S')) v) =    ( valOf (statement2Assigns S')) v"
    proof(induct_tac S,auto)qed
    
    

lemma valOfLemma4 [simp,intro]:"v \<notin> set (map fst   (statement2Assigns S)) \<Longrightarrow>( valOf (statement2Assigns  (cat S S')) v) =    ( valOf (statement2Assigns S')) v"
by (metis valOfLemma4Aux)

lemma valOfLemma5Aux :"( valOf (statement2Assigns   S ) v=IVar v) \<and>  
  ( valOf (statement2Assigns S') v=IVar v)\<longrightarrow>( valOf (statement2Assigns  (cat S S')) v=IVar v) "
    proof(induct_tac S,auto)qed
    
lemma valOfLemma5 [simp,intro]:"( valOf (statement2Assigns   S ) v=IVar v) \<and>  
  ( valOf (statement2Assigns S') v=IVar v)  \<Longrightarrow> ( valOf (statement2Assigns  (cat S S')) v=IVar v) "
  by(metis  valOfLemma5Aux)
  
lemma valOfLemma6Aux :"( valOf (statement2Assigns   S ) v=IVar v) \<and>   
  ( valOf (statement2Assigns S') v=IVar v)\<longrightarrow>( valOf (statement2Assigns  (cat S S')) v=IVar v) "
    proof(induct_tac S,auto)qed


lemma valOfLemma7Aux:"v \<notin> varOfSent S \<longrightarrow>( valOf (statement2Assigns  (cat S S')) v) =    ( valOf (statement2Assigns S')) v"
proof(induct_tac S,auto)qed

lemma valOfLemma7 [simp,intro]:"v \<notin> varOfSent S \<Longrightarrow>( valOf (statement2Assigns  (cat S S')) v) =    ( valOf (statement2Assigns S')) v"
by(metis valOfLemma7Aux)

lemma valOfLemma8Aux:"v \<in> varOfSent S \<longrightarrow>( valOf (statement2Assigns  (cat S S')) v) =    ( valOf (statement2Assigns S)) v"
proof(induct_tac S,auto)qed

lemma valOfLemma8A[simp,intro]:"v \<in> varOfSent S \<Longrightarrow>( valOf (statement2Assigns  (cat S S')) v) =    ( valOf (statement2Assigns S)) v"
by(metis valOfLemma8Aux)    


lemma noEffectValOfStatementAux[intro]:
  shows "( v \<notin>  (varOfSent S) )\<longrightarrow> valOf (statement2Assigns  S)  v=IVar v" (is "?P N") 
 proof(induct_tac S,auto)qed
 
  lemma noEffectValOfStatement[simp,intro]:
  assumes "( v \<notin>  (varOfSent S)) "
  shows   "valOf (statement2Assigns  S)  v=IVar v" (is "?P N")
by (metis assms valOfLemma2Aux varsOfSent1) 
 
 lemma noEffectValOfForallStatementAux[intro]:
  shows "( \<forall>i. (v\<notin>  (varOfSent (ps i)) ))\<longrightarrow> valOf (statement2Assigns  (forallSent (down N) ps)) v=IVar v" (is "?P N")
  proof(induct_tac N)
    show "?P 0"
      apply simp
      done
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

lemma valOfLemma9[intro,simp]:
  shows " valOf (statement2Assigns ( cat St skip))  v= valOf (statement2Assigns St)  v" (is "?P St") 
proof(induct_tac St,auto)qed

text{*definitions and lemmas on  andList formula constructor*}   


primrec andList::"formula list \<Rightarrow> formula" where
"andList [] = chaos" |
"andList (frm#frms) = andForm frm (andList frms)" 
   
lemma andListFormAux1:
 
  shows "set fs \<subseteq>  fs' \<longrightarrow>( \<forall> inv. inv \<in> fs' \<longrightarrow>formEval inv s)\<longrightarrow> formEval (andList fs) s"
  proof(induct_tac fs,auto)qed
  
lemma andListForm1[simp,intro]:
 
  "\<lbrakk>set fs \<subseteq>  invs ; ( \<forall> inv. inv \<in>invs \<longrightarrow>formEval inv s)\<rbrakk>\<Longrightarrow> formEval (andList fs) s"
 by(metis  andListFormAux1)  




lemma andList2Aux:
   shows "formEval (neg frm) s \<longrightarrow> frm \<in>set frms \<longrightarrow> formEval (neg (andList frms)) s"
   proof(induct_tac frms,auto) qed
   
lemma andList2:
   shows "formEval (neg frm) s \<Longrightarrow> frm \<in>set frms \<Longrightarrow> formEval (neg (andList frms)) s"
   by (metis andList2Aux)
   
lemma andList1Aux:
   shows "formEval ( (andList frms)) s  \<longrightarrow> frm \<in>set frms \<longrightarrow> formEval ( frm) s "
   proof(induct_tac frms,auto)qed
   
lemma andList1:
   shows "formEval ( (andList frms)) s  \<Longrightarrow>  frm \<in>set frms \<Longrightarrow> formEval ( frm) s " 
    by (metis andList1Aux)
lemma resAux1:
  assumes   b:"formEval frm s" and c:"formEval (neg (andList (frm#frms))) s"
  shows"formEval (neg (andList frms)) s"
  apply(cut_tac b c)
  apply auto
  done

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


text{*If $asgns$ does not assign any variable in $E$ to any value, then evaluation of $E$ at the state $s$ is the same as that of $E$ 
at the state $transAux~ asgns~ s$ *}
lemma noEffectOnExpAux: 
  shows "(\<forall> s. (varOfExp E) \<inter>  set (map fst asgns) ={} \<longrightarrow>
  expEval E  s  =  expEval E (transAux asgns s))  \<and>
  (\<forall>   s. (varOfForm f) \<inter>  set (map fst asgns) ={} \<longrightarrow>
  formEval f s  =  formEval f (transAux asgns s))"
  (is "(\<forall>  s. ?P asgns s E) \<and>( \<forall>  s. ?Q asgns s f)")
proof(induct_tac E and f)

  fix varType
  let ?E="IVar varType"
  show "(\<forall>  s. ?P asgns s ?E)" (is "\<forall>s. ?R s asgns")
  proof(rule allI)
  fix s
  show "?R s asgns"
  proof( induct_tac asgns)
    show "?R s []" by simp
    next  
    fix a asgns  
    assume  a1:"?R s asgns"
    show "?R s (a#asgns)"    
    proof 

    assume c1:" varOfExp (?E) \<inter> set (map fst (a # asgns)) = {}"

      have d1:"\<exists> v val0. a=(v,val0)"
            by auto 
    then obtain var val0 where d2:"a=(var,val0)"
            by blast
     
     have f1:"expEval ?E s = expEval ?E (transAux ( asgns) s)"
          apply(cut_tac a1  c1 )
          apply auto
          done
      have f2:" expEval ?E (transAux (a # asgns) s)= expEval ?E (transAux ( asgns) s)"
          apply(cut_tac a1 c1,simp)
          apply( auto)
         done
      show " expEval ?E s = expEval ?E (transAux (a # asgns) s)"
         apply(cut_tac f1 f2, simp)
         done
     qed
   qed
  qed
next
  fix n
  
  let ?E="Const n"
  show "(\<forall>  s. ?P asgns s ?E)" (is "\<forall>s. ?R s asgns")  
  by auto
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
   apply auto
   done
   qed  
next
  fix e1 e2
  let ?f="eqn e1 e2" 
  assume a1:"(\<forall>  s. ?P asgns s e1)" and a2:"(\<forall>  s. ?P asgns s e2)"
  
  show "(\<forall>  s. ?Q asgns s ?f)" (is "\<forall>s. ?R s asgns")  
  proof(rule allI,rule impI,cut_tac a1 a2,auto) 
  qed
next
  fix f1 f2
  let ?f="andForm f1 f2"
  assume a1:"( \<forall>  s. ?Q asgns s f1)" and  a2:"( \<forall>  s. ?Q asgns s f2)"
  show "( \<forall>  s. ?Q asgns s ?f)"
  
  proof(rule allI,rule impI,cut_tac a1 a2,auto) 
  qed
next
  fix f1 
  let ?f="neg f1 "
  assume a1:"( \<forall>  s. ?Q asgns s f1)"
  show "( \<forall>  s. ?Q asgns s ?f)"
  
  proof(rule allI,rule impI,cut_tac a1 ,auto) 
  qed
next
  fix f1 f2
  let ?f="orForm f1 f2"
  assume a1:"( \<forall>  s. ?Q asgns s f1)" and  a2:"( \<forall>  s. ?Q asgns s f2)"
  show "( \<forall>  s. ?Q asgns s ?f)"
  
  proof(rule allI,rule impI,cut_tac a1 a2,auto) qed
next
fix f1 f2
  let ?f="implyForm f1 f2"
  assume a1:"( \<forall>  s. ?Q asgns s f1)" and  a2:"( \<forall>  s. ?Q asgns s f2)"
  show "( \<forall>  s. ?Q asgns s ?f)"
  
  proof(rule allI,rule impI,cut_tac a1 a2,auto) qed
next
  show "( \<forall>  s. ?Q asgns s chaos)"
  by auto
qed
 

lemma noEffect: 
shows "(\<forall>   s. (varOfExp E) \<inter>  (varOfSent S) ={} \<longrightarrow> expEval E s  =  expEval E (trans S s)) \<and> 
(\<forall>s. varOfForm f \<inter>  (varOfSent S) ={}\<longrightarrow>
         formEval f s = formEval f (trans S s))"
apply(cut_tac  f="f" and E="E" and asgns="  ((statement2Assigns S))" in noEffectOnExpAux) 
apply(unfold trans_def)
apply(cut_tac S="S" in varsOfSent1)
apply metis
done

lemma noEffectOnExp: 
  assumes a1:"(varOfExp E) \<inter>  (varOfSent S) ={} "
    shows " expEval E s  =  expEval E (trans S s)"
by (metis assms noEffect) 


lemma noEffectOnFormula: 
  assumes a1:"(varOfForm f) \<inter>  (varOfSent S) ={} "
    shows " formEval f s  =  formEval f (trans S s)"
by (metis assms noEffect) 


   
text{*if varianles occurring in an expression e (or a formula f) is disjoint with that in a statement S, then 
substExpByStatement e S (or substFormByStatement f S)
is the same as e(or f)*} 
  
lemma noEffectSubstAux:
  
  shows " (  (varOfExp e \<inter>  (varOfSent S) ={}) \<longrightarrow>(substExpByStatement e S)  =e) \<and>
           (  (varOfForm f \<inter>  (varOfSent S) ={} )\<longrightarrow> (substFormByStatement f S)  =  f )"
           
    (is "(( ?condOne e S\<longrightarrow> ?LHS e S=?RHS e S)\<and> (?condOnf f S\<longrightarrow> ?LHS1 f S=?RHS1 f S))")
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
        
        apply(unfold  substExpByStatement_def trans_def,auto)
        done
    next
       fix prod S
       let ?S="parallel prod S"
       assume b1:"?condOne ?e S \<longrightarrow>?LHS ?e S=?RHS ?e S"
       
       show "?condOne ?e ?S \<longrightarrow> ?LHS ?e ?S=?RHS ?e ?S"
       
       proof(unfold  substExpByStatement_def trans_def,
       case_tac "fst prod =v",force)
       assume d1:"fst prod \<noteq> v "
       show "varOfExp (IVar v) \<inter> varOfSent (parallel prod S) = {} \<longrightarrow> (substExp (IVar v) (statement2Assigns (parallel prod S))) =
               (IVar v)"
       proof(cut_tac d1,simp) qed
      
      qed 
    qed 
next 
  fix n
  let ?e="(Const n)"
      show  "?condOne ?e S \<longrightarrow>?LHS ?e S=?RHS ?e S"
      apply( simp)
      done
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
qed

lemma noEffectSubstExp [intro!]:
  
  shows " (  (varOfExp e \<inter>  (varOfSent S) ={}) \<Longrightarrow>(substExpByStatement e S)  =e) "
by (metis noEffectSubstAux)
  
lemma noEffectSubstForm [intro!]:
  
  shows " 
             (varOfForm f \<inter>  (varOfSent S) ={}) \<Longrightarrow> (substFormByStatement f S)  =  f "
 by (metis noEffectSubstAux) 
 
 
lemma  noEffectOnRule[simp,intro]:
  assumes a1:"  (varOfForm f \<inter>  (varOfSent (act r)) ={})"
  shows " invHoldForRule s f r R "  (is "?P1 s \<or> ?P2 s \<or> ?P3 s")
proof -
  have "?P2 s"
  using assms noEffectSubstForm by auto
  then show "?P1 s \<or> ?P2 s \<or> ?P3 s"
  by auto
qed 
  
lemma noEffectValOfForallStatement[simp,intro]:
  shows "( \<forall>i. (v \<notin>  (varOfSent (ps i))) ) \<Longrightarrow>  valOf (statement2Assigns  (forallSent (down N) ps)) v=IVar v" 
  by(metis noEffectValOfForallStatementAux)
  
 lemma noEffectValOfForallStatement1[simp,intro]:
  shows "( \<forall>i. (v \<notin>  (varOfSent (ps i))) ) \<Longrightarrow>  expEval ( valOf (statement2Assigns  (forallSent (down N) ps)) v) s=s  v"
by auto

section{*on CMP theoretical foundation*}

primrec isGlobal :: "varType \<Rightarrow> bool" where
"isGlobal (Ident v) = True "|
"isGlobal (Para n i) = False"|
"isGlobal (Field  n n') = isGlobal n "

definition
  state_sim_on ::"state\<Rightarrow>state\<Rightarrow>nat set\<Rightarrow>varType set \<Rightarrow>varType set \<Rightarrow> nat\<Rightarrow>bool" where
  " state_sim_on s s' indice globalVars indVars other==
  (\<forall>n i.  i\<in> indice\<longrightarrow>( s (Para n i) =s'(Para n i))) \<and> 
  (\<forall>v. v \<in>globalVars \<longrightarrow> isGlobal v \<longrightarrow> ( s v =s' v)) \<and>
  (\<forall>v. v \<in>  indVars  \<longrightarrow> (\<exists>j. s v=index j \<and> j \<in> indice) \<longrightarrow> (s v =s' v )) \<and> 
  (\<forall>v. v \<in>  indVars  \<longrightarrow> (\<exists>j. s v=index j \<and> j \<notin> indice)\<longrightarrow> (s' v =index other ))"

definition 
  pred_sim_on :: "formula\<Rightarrow>formula\<Rightarrow>nat set\<Rightarrow>varType set \<Rightarrow>varType set \<Rightarrow> nat\<Rightarrow>bool" where
  "pred_sim_on f1 f2 indice globalVars indVars other \<equiv>
  \<forall> s. formEval f1 s \<longrightarrow> (\<exists>s'. formEval f2 s' \<and>  state_sim_on s s' indice globalVars indVars other)"

definition
  trans_sim_on :: "rule \<Rightarrow> rule \<Rightarrow>nat set\<Rightarrow>varType set \<Rightarrow>varType set \<Rightarrow> nat\<Rightarrow>bool" where
"trans_sim_on r1 r2 indice globalVars indVars other \<equiv>
  \<forall>s1 s1'. ((formEval (pre r1) s1 \<and> s1'=trans (act r1) s1) \<longrightarrow>
           (\<exists>s2 s2'. (state_sim_on s1 s2 indice globalVars indVars other \<and>
             state_sim_on s1 s2 indice globalVars indVars other \<and>
            (formEval (pre r2) s2 \<and> s2'=trans (act r2) s2))))"  
definition
  prot_sim_on ::"formula set \<Rightarrow> formula set \<Rightarrow> rule set \<Rightarrow> rule set \<Rightarrow> nat set\<Rightarrow>varType set \<Rightarrow>varType set \<Rightarrow> nat\<Rightarrow>bool" where 
"prot_sim_on I I' rs rs' indice globalVars indVars other \<equiv>
  (\<forall>f. f \<in> I \<longrightarrow> (\<exists>f'. f' \<in> I' \<and> pred_sim_on f f' indice globalVars indVars other)) \<and>
  (\<forall>r. r \<in> rs\<longrightarrow>(\<exists> r'. r' \<in> rs' \<and> trans_sim_on r r' indice globalVars indVars other))"

 definition
  state_sim_on' ::"state\<Rightarrow>state\<Rightarrow>formula set\<Rightarrow>bool" where [simp]:
  " state_sim_on' s s' F ==
  (\<forall>f v. f \<in>F \<longrightarrow>v \<in> varOfForm f \<longrightarrow> (s v) = (s' v) ) "

  definition
  state_sim_on1 ::"state\<Rightarrow>state\<Rightarrow>formula set\<Rightarrow>bool" where [simp]:
  " state_sim_on1 s s' F ==(\<forall>f v. f \<in>F \<longrightarrow> v \<in>varOfForm f\<longrightarrow>s(v) = s'(v))" 
 (* (\<forall>f. f \<in>F \<longrightarrow> (formEval f s = formEval f s')) "*)

definition
  state_sim_on2 ::"state\<Rightarrow>state\<Rightarrow>varType  set\<Rightarrow>bool" where [simp]:
  " state_sim_on2 s s' V ==(\<forall> v.  v \<in>V\<longrightarrow>s(v) = s'(v))" 


primrec scalar2Nat ::"scalrValueType \<Rightarrow>nat"  where
"scalar2Nat (index n) = n"

definition
  state_sim_on3 ::"state\<Rightarrow>state\<Rightarrow>varType  set\<Rightarrow>varType  set\<Rightarrow>nat=>bool" where [simp]:
  " state_sim_on3 s s' V V' N ==(\<forall> v.  v \<in>V\<longrightarrow>s(v) = s'(v))\<and>(\<forall> v.  v \<in>V'\<longrightarrow>scalar2Nat(s(v))\<le>N \<longrightarrow>s(v) = s'(v))" 

definition                                                           
  pred_sim_on1 :: "formula\<Rightarrow>formula\<Rightarrow>formula set\<Rightarrow>state\<Rightarrow>bool" where [simp]:
  "pred_sim_on1 f1 f2 F s\<equiv>
   formEval f1 s \<longrightarrow> (\<exists>s'. formEval f2 s' \<and>  state_sim_on1 s s' F)"
                                                                       
definition 
  pred_sim_on2 :: "formula\<Rightarrow>formula\<Rightarrow>varType set\<Rightarrow>state\<Rightarrow>bool" where [simp]:
  "pred_sim_on2 f1 f2 V s\<equiv>
   formEval f1 s \<longrightarrow> (\<exists>s'. formEval f2 s' \<and>  state_sim_on2 s s' V)"

definition 
  pred_sim_on3 :: "formula\<Rightarrow>formula\<Rightarrow>varType set \<Rightarrow>varType set \<Rightarrow> nat\<Rightarrow>state\<Rightarrow>bool" where [simp]:
  "pred_sim_on3 f1 f2 V V' N  s\<equiv>
   formEval f1 s \<longrightarrow> (\<exists>s'. formEval f2 s' \<and>  state_sim_on3 s s' V V' N )"

definition
  trans_sim_on1 :: "rule \<Rightarrow> rule \<Rightarrow>formula set\<Rightarrow>state\<Rightarrow>bool" where [simp]:
"trans_sim_on1 r1 r2 F s1 \<equiv>
  \<forall> s2. ((formEval (pre r1) s1 ) \<and>(\<forall>f. f\<in>F \<longrightarrow> formEval f s1)\<longrightarrow>state_sim_on1 s1 s2 F \<longrightarrow>
           ((state_sim_on1 (trans (act r1) s1) (trans (act r2) s2) F \<and> (formEval (pre r2) s2 ))
           \<or> state_sim_on1 (trans (act r1) s1) s2 F))" 

definition
  trans_sim_on2 :: "rule \<Rightarrow> rule \<Rightarrow>varType set\<Rightarrow>formula set => state\<Rightarrow>bool" where [simp]:
"trans_sim_on2 r1 r2 V F s1 \<equiv>
  \<forall> s2. ((formEval (pre r1) s1 ) \<and>(\<forall>f. f\<in>F \<longrightarrow> formEval f s1)\<longrightarrow>state_sim_on2 s1 s2 V \<longrightarrow>
           ((state_sim_on2 (trans (act r1) s1) (trans (act r2) s2) V \<and> (formEval (pre r2) s2 ))
           \<or> state_sim_on2 (trans (act r1) s1) s2 V))" 

definition
  trans_sim_on3 :: "rule \<Rightarrow> rule \<Rightarrow>varType set\<Rightarrow>varType set\<Rightarrow> nat => state\<Rightarrow>bool" where [simp]:
"trans_sim_on3 r1 r2 V V' N  s1 \<equiv>
  \<forall> s2. ((formEval (pre r1) s1 ) \<longrightarrow>state_sim_on3 s1 s2 V V' N\<longrightarrow>
           ((state_sim_on3 (trans (act r1) s1) (trans (act r2) s2) V V' N\<and> (formEval (pre r2) s2 ))
           \<or> state_sim_on3 (trans (act r1) s1) s2 V V' N))" 

definition
  prot_sim_on1 ::"formula set \<Rightarrow> formula set \<Rightarrow> rule set \<Rightarrow> rule set \<Rightarrow> formula set\<Rightarrow>state\<Rightarrow>bool" where [simp]:
"prot_sim_on1 I I' rs rs' F s\<equiv>
  (\<forall>f. f \<in> I \<longrightarrow> (\<exists>f'. f' \<in> I' \<and> pred_sim_on1 f f' F s)) \<and>
  (\<forall>r. r \<in> rs\<longrightarrow>(\<exists> r'. r' \<in> rs' \<and> trans_sim_on1 r r' F s))"



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
qed

lemma stSim: 
  assumes  a1:"state_sim_on1 s1 s2 F"
  shows " (\<forall>f. f \<in>F \<longrightarrow> (formEval f s1 = formEval f s2)) "
proof(rule allI, rule impI)
  fix f
  assume b1:"f \<in> F"
  show " (formEval f s1 = formEval f s2)"
    using agreeOnVars assms b1 by auto
qed  

lemma stSim2: 
  assumes  a1:"state_sim_on2 s1 s2 V"
  shows " (\<forall>f. (varOfForm f) \<subseteq> V \<longrightarrow> (formEval f s1 = formEval f s2)) "
proof(rule allI, rule impI)
  fix f
  assume b1:"(varOfForm f) \<subseteq> V"
  show " (formEval f s1 = formEval f s2)"
    by (metis agreeOnVars assms b1 set_mp state_sim_on2_def)
qed  

lemma stSim3: 
  assumes  a1:"state_sim_on3 s1 s2 V V' F" and a2:"\<forall> v. v \<in>V' \<longrightarrow> s(v) \<le> N"
  shows " (\<forall>f. (varOfForm f) \<subseteq> V \<longrightarrow> (formEval f s1 = formEval f s2)) "
proof(rule allI, rule impI)
  fix f
  assume b1:"(varOfForm f) \<subseteq> V"
  show " (formEval f s1 = formEval f s2)"
    by (metis agreeOnVars assms b1 set_mp state_sim_on3_def)
qed  
  
lemma sim:
  
  assumes  a1:"\<forall>s. s \<in>reachableSet I rs \<longrightarrow> (\<forall> f. f \<in>F \<longrightarrow> formEval f s )\<longrightarrow>prot_sim_on1 I I' rs rs' F s"
    and a2:"\<forall>s f. s \<in>reachableSet I' rs' \<longrightarrow>f \<in>F \<longrightarrow> formEval f s  " 
  and a4:"s \<in>reachableSet I rs " and a5:"\<forall> s f.  f \<in>I \<longrightarrow> formEval f s \<longrightarrow> (\<forall>f'. f' \<in>F \<longrightarrow> formEval  f' s)   "
  and a6:"\<forall> s f.  f \<in>I' \<longrightarrow> formEval f s \<longrightarrow> (\<forall>f'. f' \<in>F \<longrightarrow> formEval  f' s)   "
shows "((\<exists>s'. s' \<in>reachableSet I' rs' \<and> state_sim_on1 s s' F  )\<and> (\<forall> f. f \<in>F \<longrightarrow> formEval f s ))" (is "?con1 s \<and> ?con2 s")
  using a4
proof induct
  fix ini s
  assume b1:"formEval ini s" and b2:"ini \<in>I"
  show "?con1 s \<and> ?con2 s"
  proof(rule conjI)
    
    have c0:"s \<in> reachableSet I rs"
      using b1 b2 reachableSet.initState by auto
    have c1:" (\<forall>f. f \<in> I \<longrightarrow> (\<exists>f'. f' \<in> I' \<and> pred_sim_on1 f f' F s))"
      by (meson a5 b1 b2 c0 local.a1 prot_sim_on1_def)
      have c2:"\<exists>f'. f' \<in> I' \<and> pred_sim_on1 ini f' F s"  (is "\<exists>f'. ?P f'")
        by(cut_tac c1 b2  ,auto)
    then obtain ini' where c3:"?P ini'" by blast
    then have "\<exists>s'. formEval ini' s' \<and> state_sim_on1 s s' F"  (is "\<exists>s'. ?P s'")
        by(cut_tac b1 c3 a5 a6, auto)
    then obtain s' where c4:"?P s'" by blast
    show "?con1 s"
    proof(rule_tac x="s'" in exI,rule conjI)
      show "s' \<in>reachableSet I' rs'"
      proof(rule_tac ?ini="ini'" in initState)
        show "formEval ini' s'" by(cut_tac c4,simp)
        next
          show "ini' \<in> I'" by(cut_tac c3,simp)
      qed
    next
     show "state_sim_on1 s s' F" by(cut_tac c4,auto)
   qed
   next show "?con2 s"
      by(cut_tac a5 b2 b1,auto)
  qed
next
  fix s r
  let ?s'="trans (act r) s"
  assume b1:"?con1 s \<and> ?con2 s" and b2:"s \<in> reachableSet I rs" 
  and b3:"r \<in> rs"  and b4:"formEval (pre r)  s"  
  show "?con1 ?s' \<and> ?con2 ?s'"
  proof -
    have c1:" (\<exists> r'. r' \<in> rs' \<and> trans_sim_on1 r r' F s)" (is "EX r'. ?P r'")
      using b1 b2 b3 local.a1 prot_sim_on1_def by blast 
    then obtain r' where c2:"?P r'"  by blast

    have c3:"(\<exists>s2 . (s2 \<in> reachableSet I' rs' \<and> state_sim_on1 s s2 F  ))" (is "EX s2. ?P s2")
      apply(cut_tac b1 c2 b4, auto ) done
    then obtain s2 where c3:"?P s2"  by blast

    
    have c4:"
            ( state_sim_on1 (trans (act r) s) (trans (act r') s2) F \<and>
            (formEval (pre r') s2 )) | state_sim_on1 (trans (act r) s) s2  F" (is " ?P s2")
      apply(cut_tac  b1 b4  c3 c2 , auto)  done
    moreover
    {assume c5:"( state_sim_on1 (trans (act r) s) (trans (act r') s2) F \<and>
            (formEval (pre r') s2 ))"
      have c6: "?con1 ?s'"
      proof(rule_tac x="trans (act r') s2" in exI,rule conjI)
        show " trans (act r') s2\<in>reachableSet I' rs'"
        proof(rule_tac ?s="s2" in oneStep)
          show "s2\<in>reachableSet I' rs'" apply(cut_tac b1 c3,simp) done
        next
          show "r' \<in> rs'" by(cut_tac c2,simp)
        next
          show "(formEval (pre r') s2 )" by(cut_tac c5,auto)
        qed
      next
        show "state_sim_on1 (trans (act r) s) (trans (act r') s2) F"
          by(cut_tac c5, auto)
      qed
      then obtain s' where  c7: "s' \<in>reachableSet I' rs' \<and> state_sim_on1 ?s' s' F " by blast
      
     have c8:"?con2 ?s'"
     proof(rule allI,rule impI)
      fix f
      assume d1:"f \<in> F"
      have c9:"formEval f s'" by(cut_tac a2 c7 d1,auto)
      show "formEval f ?s'"
        using c7 c9 d1 stSim by blast
    qed
    have "?con1 ?s' \<and> ?con2 ?s'" by(cut_tac c6 c8, auto)
    }
    moreover
    {assume c5:"state_sim_on1 (trans (act r) s) s2  F"
      have c6:"?con1 ?s'"
      proof(rule_tac x=" s2" in exI,rule conjI)
        show " s2\<in>reachableSet I' rs'"
          by (simp add: c3) 
        next
          show "state_sim_on1 (trans (act r) s)  s2 F" by(cut_tac c5,auto)
        qed
      
      
    
      have c8:"?con2 ?s'"
      proof(rule allI,rule impI)
        fix f
        assume d1:"f \<in> F"
        have c9:"formEval f s2" by(cut_tac a2 c3 d1,auto)
        show "formEval f ?s'"
          using c5 c9 d1 stSim by blast 
      qed
      have "?con1 ?s' \<and> ?con2 ?s'" by(cut_tac c6 c8, auto)  
    }
    ultimately show c6:"?con1 ?s'\<and> ?con2 ?s'" by blast

   
  qed
qed

(*lemma ruleSim:
  assumes a1:"\<forall>s1 s2 f. (\<forall> f. f \<in>F \<longrightarrow> formEval f s1 ) \<longrightarrow> 
    state_sim_on1 s1 s2 F\<longrightarrow> formEval  (pre r1)  s1 \<longrightarrow> formEval (pre r2) s2" and
    a2:"\<forall>s1 s2  f.(f \<in>F \<longrightarrow>(\<forall> f. f \<in>F \<longrightarrow> formEval f s1 )\<longrightarrow>
    state_sim_on1 s1 s2 F\<longrightarrow>
   ((formEval  (substFormByStatement f (act r1)) s1) = (formEval (substFormByStatement f (act r2))) s2))"
  shows "trans_sim_on1 r1 r2 F"
proof(unfold trans_sim_on1_def,(rule allI)+,(rule impI)+)
  fix s1 s2
  assume b1:"formEval (pre r1) s1 \<and>(\<forall> f. f \<in>F \<longrightarrow> formEval f s1 ) "  and b2:"state_sim_on1 s1 s2 F" 
  show "((state_sim_on1 (trans (act r1) s1) (trans (act r2) s2) F \<and> (formEval (pre r2) s2 ))
           \<or> state_sim_on1 (trans (act r1) s1) s2 F)"
  proof(rule disjI1,rule conjI)
    show "state_sim_on1 (trans (act r1) s1) (trans (act r2) s2) F"
    proof(unfold state_sim_on1_def,rule allI,rule impI)
      fix f
      assume c1:"f \<in>F"
      have c2:"formEval  (substFormByStatement f (act r1)) s1 = formEval f (trans (act r1) s1)"
        using preCondOnExp by auto
      have c3:"formEval  (substFormByStatement f (act r2)) s2 = formEval f (trans (act r2) s2)"
        using preCondOnExp by auto  
      
      have c6:"formEval  (substFormByStatement f (act r1)) s1 = (formEval (substFormByStatement f (act r2))) s2"
        apply(cut_tac  a2 b1 b2 c1,simp) done
      show  "formEval f (trans (act r1) s1) =formEval f  (trans (act r2) s2)"
        using c2 c3 c6 by blast
    qed
    show "formEval (pre r2) s2"
      using b1 b2 local.a1 by blast
  qed
qed  *)

(*lemma ruleSimCond:
  assumes a1:"\<forall>s. (\<forall> f. f \<in>F \<longrightarrow> formEval f s ) \<longrightarrow> formEval (pre r1) s \<longrightarrow>formEval (pre r2) s" and
  a2:" \<forall>s f. f \<in>F \<longrightarrow> ((formEval  (substFormByStatement f (act r1)) s) = (formEval (substFormByStatement f (act r2))) s)"
shows "trans_sim_on1 r1 r2 F"
proof(unfold trans_sim_on1_def,(rule allI)+,(rule impI)+)
  fix s1 s2
  assume b1:"formEval (pre r1) s1 \<and> (\<forall> f. f \<in>F \<longrightarrow> formEval f s1 )" and b2:"state_sim_on1 s1 s2 F"
  show "((state_sim_on1 (trans (act r1) s1) (trans (act r2) s2) F \<and> (formEval (pre r2) s2 ))
           \<or> state_sim_on1 (trans (act r1) s1) s2 F)"
  proof(rule disjI1,rule conjI)
    show "state_sim_on1 (trans (act r1) s1) (trans (act r2) s2) F"
    proof(unfold state_sim_on1_def,rule allI,rule impI)
      fix f
      assume c1:"f \<in>F"
      have c2:"formEval  (substFormByStatement f (act r1)) s1 = formEval f (trans (act r1) s1)"
        using preCondOnExp by auto
     have c3:"formEval  (substFormByStatement f (act r2)) s2 = formEval f (trans (act r2) s2)"
       using preCondOnExp by auto  
     have c4:"formEval  (substFormByStatement f (act r2)) s1=formEval  (substFormByStatement f (act r2)) s2 " sorry
     have c5:"formEval  (substFormByStatement f (act r1)) s1=formEval  (substFormByStatement f (act r2)) s1" 
       by(cut_tac b1 c1 a2,auto)
     show  "formEval f (trans (act r1) s1) =formEval f  (trans (act r2) s2)"
       using a2 c1 c2 c3 c4 by blast 
   qed
 next
   have "formEval (pre r2) s1"
     by (simp add: b1 local.a1)
   then    show "formEval (pre r2) s2" 
    
  qed*)
thm  agreeOnVars
lemma agreeOnVarsOfExp: assumes a:"\<forall> v.   v \<in> varOfExp e \<longrightarrow> s1(v) = s2 v" 
  shows "expEval e s1 = expEval e s2"
  by (simp add: agreeOnVars assms) 

lemma setOfList: "  varOfFormList flist={v. \<exists>f. f \<in> set flist \<and> v \<in> varOfForm f} "
proof(induct_tac flist,auto) qed
  
lemma ruleSimCond:
  assumes  a1:" formEval (pre r1) s \<longrightarrow>formEval (pre r2) s" and 
  a3:"\<forall>v. v\<in>varOfForm (pre r2) \<longrightarrow>v \<in> (varOfFormList F ) "  and  
  a4:" (\<forall>  v. v \<in>varOfFormList F \<longrightarrow>   formEval (pre r1) s \<longrightarrow> expEval (substExpByStatement (IVar v)  (act r2)) s = expEval (substExpByStatement (IVar v)  (act r1)) s)" and
  a5:"\<forall> v va. v \<in> varOfFormList F \<longrightarrow>va\<in>varOfExp ( substExpByStatement (IVar v)  (act r2))\<longrightarrow> va \<in> (varOfFormList F )"   
shows "trans_sim_on1 r1 r2 (set F) s"
proof(unfold trans_sim_on1_def,(rule allI)+,(rule impI)+)
  fix  s2
  assume b1:"formEval (pre r1) s \<and> (\<forall> f. f \<in>(set F) \<longrightarrow> formEval f s )" and b2:"state_sim_on1 s s2 (set F)"
  show "((state_sim_on1 (trans (act r1) s) (trans (act r2) s2) (set F) \<and> (formEval (pre r2) s2 ))
           \<or> state_sim_on1 (trans (act r1) s) s2 (set F))"
   proof(rule disjI1,rule conjI)
    show "state_sim_on1 (trans (act r1) s) (trans (act r2) s2) (set F)"
    proof(unfold state_sim_on1_def,(rule allI)+,(rule impI)+)
      fix f v
      assume c1:"f \<in>set F"  and c2:"v \<in>varOfForm f"
      have c20:"expEval  (substExpByStatement (IVar v) (act r1)) s = expEval (IVar v) (trans (act r1) s)" 
        using preCondOnExp by blast
     have c3:"expEval  (substExpByStatement (IVar v) (act r1)) s2 = expEval (IVar v) (trans (act r1) s2)"
       using preCondOnExp by blast

     have c30:"v \<in> varOfFormList F "
       using c1 c2 setOfList by auto 

     have c4:"\<forall>va. va \<in> varOfExp (substExpByStatement  (IVar v)  (act r2)) \<longrightarrow> s(va) = s2 va"
       by (smt a5 b2 c1 c2 c30 mem_Collect_eq setOfList state_sim_on1_def)
       (*using a5 b2 c1 c2 state_sim_on1_def by blast*)
 
     have c5:"expEval (substExpByStatement (IVar v)  (act r2)) s = expEval (substExpByStatement (IVar v)  (act r2)) s2"
       using agreeOnVars c4 by blast 

     from c1 c2 have c6:" v \<in> varOfFormList F"
       using setOfList by auto

     show " trans (act r1) s v =   trans (act r2) s2 v"
       using a4 b1 c6 c5 lemmaOnValOf by auto
   qed
 next
   have "formEval (pre r2) s"
     by (simp add: b1 local.a1)
   have c4:"\<forall>va. va \<in> varOfForm  (pre r2)\<longrightarrow> s(va) = s2 va"
   proof(rule allI,rule impI)
     fix va
     assume c1:"va \<in> varOfForm  (pre r2)"
     from a3 have c2:"va \<in> (varOfFormList F )" using c1 by blast
      have c3:" (\<exists>f. f \<in>set F \<and>va \<in> varOfForm f)"
        using c2 setOfList by auto 
      show  "s(va) = s2 va"
        using b2 c3 by auto
    qed
      show "formEval (pre r2) s2"
     using \<open>formEval (pre r2) s\<close> agreeOnVars c4 by blast 
    
 qed
qed

(*lemma ruleSimCond:
  assumes a1:" (\<forall> f. f \<in>set F \<longrightarrow> formEval f s ) \<longrightarrow> formEval (pre r1) s \<longrightarrow>formEval (pre r2) s" and
  (*a2:" \<forall>s f. f \<in>F \<longrightarrow> ((formEval  (substFormByStatement f (act r1)) s) = (formEval (substFormByStatement f (act r2))) s)" and*)
  a3:"\<forall>v. v\<in>varOfForm (pre r2) \<longrightarrow>v \<in> (varOfFormList F ) " (*(\<exists>f. f \<in>F \<and>v \<in> varOfForm f)*)and  
  a4:"(\<forall> f. f \<in>set F \<longrightarrow> formEval f s )\<longrightarrow>
  (\<forall>f  v. f\<in> set F \<longrightarrow>  v \<in> varOfForm f \<longrightarrow>   formEval (pre r1) s \<longrightarrow> expEval (substExpByStatement (IVar v)  (act r2)) s = expEval (substExpByStatement (IVar v)  (act r1)) s)" and
  a5:"\<forall>f v va. v \<in> varOfForm f \<longrightarrow> f \<in> set F \<longrightarrow>va\<in>varOfExp ( substExpByStatement (IVar v)  (act r2))\<longrightarrow> va \<in> (varOfFormList F )"  (*(\<exists>f. f \<in>F \<and>v \<in> varOfForm f)*)
shows "trans_sim_on1 r1 r2 (set F) s"
proof(unfold trans_sim_on1_def,(rule allI)+,(rule impI)+)
  fix  s2
  assume b1:"formEval (pre r1) s \<and> (\<forall> f. f \<in>(set F) \<longrightarrow> formEval f s )" and b2:"state_sim_on1 s s2 (set F)"
  show "((state_sim_on1 (trans (act r1) s) (trans (act r2) s2) (set F) \<and> (formEval (pre r2) s2 ))
           \<or> state_sim_on1 (trans (act r1) s) s2 (set F))"
   proof(rule disjI1,rule conjI)
    show "state_sim_on1 (trans (act r1) s) (trans (act r2) s2) (set F)"
    proof(unfold state_sim_on1_def,(rule allI)+,(rule impI)+)
      fix f v
      assume c1:"f \<in>set F"  and c2:"v \<in>varOfForm f"
      have c20:"expEval  (substExpByStatement (IVar v) (act r1)) s = expEval (IVar v) (trans (act r1) s)" 
        using preCondOnExp by blast
     have c3:"expEval  (substExpByStatement (IVar v) (act r1)) s2 = expEval (IVar v) (trans (act r1) s2)"
       using preCondOnExp by blast

     have c4:"\<forall>va. va \<in> varOfExp (substExpByStatement  (IVar v)  (act r2)) \<longrightarrow> s(va) = s2 va"
       by (smt a5 b2 c1 c2 mem_Collect_eq setOfList state_sim_on1_def)
       (*using a5 b2 c1 c2 state_sim_on1_def by blast*)
 
     have c5:"expEval (substExpByStatement (IVar v)  (act r2)) s = expEval (substExpByStatement (IVar v)  (act r2)) s2"
       using agreeOnVars c4 by blast 
     show " trans (act r1) s v =   trans (act r2) s2 v"
       using a4 b1 c1 c2 c5 lemmaOnValOf by auto
   qed
 next
   have "formEval (pre r2) s"
     by (simp add: b1 local.a1)
   have c4:"\<forall>va. va \<in> varOfForm  (pre r2)\<longrightarrow> s(va) = s2 va"
   proof(rule allI,rule impI)
     fix va
     assume c1:"va \<in> varOfForm  (pre r2)"
     from a3 have c2:"va \<in> (varOfFormList F )" using c1 by blast
      have c3:" (\<exists>f. f \<in>set F \<and>va \<in> varOfForm f)"
        using c2 setOfList by auto 
      show  "s(va) = s2 va"
        using b2 c3 by auto
    qed
      show "formEval (pre r2) s2"
     using \<open>formEval (pre r2) s\<close> agreeOnVars c4 by blast 
    
 qed
qed*)

lemma noSubVar: 
  shows      "(\<not>(\<exists>a. a \<in> set (statement2Assigns S) \<and> (fst a) =v )) \<longrightarrow>(substExpByStatement (IVar v)   S) =   (IVar v)"
proof(induct_tac S,auto)qed

lemma ruleSimId: 
  assumes  a3:"\<forall>v. v\<in>varOfForm (pre r) \<longrightarrow>v \<in> (varOfFormList F )" and  (* (\<exists>f. f \<in>F \<and>v \<in> varOfForm f)**)
  (*a5:"\<forall>f v va. v \<in> varOfForm f \<longrightarrow> f \<in>F \<longrightarrow>va\<in>varOfExp ( substExpByStatement (IVar v)  (act r))\<longrightarrow> (\<exists>f. f \<in> F \<and> va \<in> varOfForm f)" *)
  a5:"\<forall>v a. a \<in> set (statement2Assigns (act r)) \<longrightarrow> v\<in>varOfExp ( substExpByStatement (IVar (fst a))  (act r))\<longrightarrow> v \<in> (varOfFormList F )"
shows
"trans_sim_on1 r r (set F ) s" 
proof(unfold trans_sim_on1_def,(rule allI)+,(rule impI)+ ) 
  fix s1 s2
  assume b1:"formEval (pre r) s1 \<and> (\<forall> f. f \<in> (set F )\<longrightarrow> formEval f s1 )" and b2:"state_sim_on1 s1 s2 (set F )"
  show "((state_sim_on1 (trans (act r) s1) (trans (act r) s2) (set F ) \<and> (formEval (pre r) s2 ))
           \<or> state_sim_on1 (trans (act r) s1) s2 (set F ))"
  proof(rule disjI1,rule conjI)
    show "state_sim_on1 (trans (act r) s1) (trans (act r) s2) (set F )"
    proof(unfold state_sim_on1_def,(rule allI)+,(rule impI)+)
      fix f v
      assume c1:"f \<in>(set F )"  and c2:"v \<in>varOfForm f"
      have c20:"expEval  (substExpByStatement (IVar v) (act r)) s1 = expEval (IVar v) (trans (act r) s1)" 
        using preCondOnExp by blast
     have c3:"expEval  (substExpByStatement (IVar v) (act r)) s2 = expEval (IVar v) (trans (act r) s2)"
       using preCondOnExp by blast

     have c4:"\<forall>v a. a \<in> set (statement2Assigns (act r)) \<longrightarrow> v\<in>varOfExp ( substExpByStatement (IVar (fst a))  (act r)) \<longrightarrow> s1(v) = s2 v"
       using a5 b2 setOfList by auto 
 
     have c5:"expEval (substExpByStatement (IVar v)  (act r)) s1 = expEval (substExpByStatement (IVar v)  (act r)) s2"
     proof(case_tac "\<exists>a. a \<in> set (statement2Assigns (act r)) \<and> (fst a) =v")
       assume d1:"\<exists>a. a \<in> set (statement2Assigns (act r)) \<and> (fst a) =v"
       from d1 obtain as where d2:"as \<in> set (statement2Assigns (act r)) \<and> (fst as) =v" by blast
         have d3:"\<forall>v.  v\<in>varOfExp ( substExpByStatement (IVar (fst as))  (act r)) \<longrightarrow> s1(v) = s2 v"
           using c4 d2 by blast
         then show "expEval (substExpByStatement (IVar v)  (act r)) s1 = expEval (substExpByStatement (IVar v)  (act r)) s2"
           using agreeOnVarsOfExp d2 by blast
       next
         assume d1:"\<not>(\<exists>a. a \<in> set (statement2Assigns (act r)) \<and> (fst a) =v )"
         have d10:"(substExpByStatement (IVar v)  (act r)) =   (IVar v)"
           using d1 noSubVar by auto  
         then show "expEval (substExpByStatement (IVar v)  (act r)) s1 = expEval (substExpByStatement (IVar v)  (act r)) s2"
           using b2 c1 c2 by auto
     qed     
     show " trans (act r) s1 v =   trans (act r) s2 v"
       using  c1 c2 c5 lemmaOnValOf by auto
   qed
 next
   have "formEval (pre r) s1"
     by (simp add: b1 )
  have c4:"\<forall>va. va \<in> varOfForm  (pre r)\<longrightarrow> s1(va) = s2 va"
    using a3 b2 setOfList by auto 
   show "formEval (pre r) s2"
     using \<open>formEval (pre r) s1\<close> agreeOnVars c4 by blast 
    
 qed
qed
(*
lemma ruleSimId3: 
  assumes   a3:" formEval (pre r) s \<longrightarrow>formEval (pre r') s" and   
  a5:"\<forall>v a. a \<in> set (statement2Assigns (act r)) \<longrightarrow>fst a \<in> V \<longrightarrow>  a \<in> set (statement2Assigns (act r'))" and
  a6:"\<forall>f v . v \<in> varOfForm f \<longrightarrow> f \<in>F\<longrightarrow>(v \<in> V | (v \<in>V' \<and> scalr2Nat (s(v)) \<le> N))"
shows
"trans_sim_on3 r r' V V' N F s" 
proof(unfold trans_sim_on3_def,(rule allI)+,(rule impI)+ ) 
  fix  s2
  assume b1:"formEval (pre r) s \<and> (\<forall> f. f \<in> ( F )\<longrightarrow> formEval f s )" and b2:"state_sim_on3 s s2 V V' N "
  show "((state_sim_on3 (trans (act r) s) (trans (act r') s2) V V' N \<and> (formEval (pre r') s2 ))
           \<or> state_sim_on3 (trans (act r) s) s2 V V' N )"
  proof(rule disjI1,rule conjI)
    show "state_sim_on3 (trans (act r) s) (trans (act r') s2) V V' N"
    proof(unfold state_sim_on3_def,rule conjI)         
      show " \<forall>v. v \<in> V \<longrightarrow> paraTheory.trans (act r) s v = paraTheory.trans (act r') s2 v"
      proof((rule allI)+,(rule impI)+)
        fix  v
        assume c1:"v\<in>V"
        have c20:"expEval  (substExpByStatement (IVar v) (act r)) s = expEval (IVar v) (trans (act r') s)" 
          using a5 preCondOnExp by blast
     have c3:"expEval  (substExpByStatement (IVar v) (act r)) s2 = expEval (IVar v) (trans (act r) s2)"
       using preCondOnExp by blast

     have c4:"\<forall>v a. a \<in> set (statement2Assigns (act r)) \<longrightarrow> v\<in>varOfExp ( substExpByStatement (IVar (fst a))  (act r)) \<longrightarrow> s(v) = s2 v"
       using a5 b2 setOfList by auto 
 
     have c5:"expEval (substExpByStatement (IVar v)  (act r)) s = expEval (substExpByStatement (IVar v)  (act r)) s2"
     proof(case_tac "\<exists>a. a \<in> set (statement2Assigns (act r)) \<and> (fst a) =v")
       assume d1:"\<exists>a. a \<in> set (statement2Assigns (act r)) \<and> (fst a) =v"
       from d1 obtain as where d2:"as \<in> set (statement2Assigns (act r)) \<and> (fst as) =v" by blast
         have d3:"\<forall>v.  v\<in>varOfExp ( substExpByStatement (IVar (fst as))  (act r)) \<longrightarrow> s(v) = s2 v"
           using c4 d2 by blast
         then show "expEval (substExpByStatement (IVar v)  (act r)) s = expEval (substExpByStatement (IVar v)  (act r)) s2"
           using agreeOnVarsOfExp d2 by blast
       next
         assume d1:"\<not>(\<exists>a. a \<in> set (statement2Assigns (act r)) \<and> (fst a) =v )"
         have d10:"(substExpByStatement (IVar v)  (act r)) =   (IVar v)"
           using d1 noSubVar by auto  
         then show "expEval (substExpByStatement (IVar v)  (act r)) s = expEval (substExpByStatement (IVar v)  (act r)) s2"
           using b2 c1 by auto
     qed     
     show " trans (act r) s v =   trans (act r) s2 v"
       by (metis c5 evalVar preCondOnExp)
   qed
*)
lemma ruleSimId2: 
  assumes   a3:"\<forall>v. v\<in>varOfForm (pre r) \<longrightarrow>v \<in> V" and  (* (\<exists>f. f \<in>F \<and>v \<in> varOfForm f)**)
  (*a5:"\<forall>f v va. v \<in> varOfForm f \<longrightarrow> f \<in>F \<longrightarrow>va\<in>varOfExp ( substExpByStatement (IVar v)  (act r))\<longrightarrow> (\<exists>f. f \<in> F \<and> va \<in> varOfForm f)" *)
  a5:"\<forall>v a. a \<in> set (statement2Assigns (act r)) \<longrightarrow> v\<in>varOfExp ( substExpByStatement (IVar (fst a))  (act r))\<longrightarrow> v \<in>V"
shows
"trans_sim_on2 r r V F s" 
proof(unfold trans_sim_on2_def,(rule allI)+,(rule impI)+ ) 
  fix  s2
  assume b1:"formEval (pre r) s \<and> (\<forall> f. f \<in> ( F )\<longrightarrow> formEval f s )" and b2:"state_sim_on2 s s2 V"
  show "((state_sim_on2 (trans (act r) s) (trans (act r) s2) V \<and> (formEval (pre r) s2 ))
           \<or> state_sim_on2 (trans (act r) s) s2 V)"
  proof(rule disjI1,rule conjI)
    show "state_sim_on2 (trans (act r) s) (trans (act r) s2) V"
    proof(unfold state_sim_on2_def,(rule allI)+,(rule impI)+)
      fix  v
      assume c1:"v\<in>V" 
      have c20:"expEval  (substExpByStatement (IVar v) (act r)) s = expEval (IVar v) (trans (act r) s)" 
        using preCondOnExp by blast
     have c3:"expEval  (substExpByStatement (IVar v) (act r)) s2 = expEval (IVar v) (trans (act r) s2)"
       using preCondOnExp by blast

     have c4:"\<forall>v a. a \<in> set (statement2Assigns (act r)) \<longrightarrow> v\<in>varOfExp ( substExpByStatement (IVar (fst a))  (act r)) \<longrightarrow> s(v) = s2 v"
       using a5 b2 setOfList by auto 
 
     have c5:"expEval (substExpByStatement (IVar v)  (act r)) s = expEval (substExpByStatement (IVar v)  (act r)) s2"
     proof(case_tac "\<exists>a. a \<in> set (statement2Assigns (act r)) \<and> (fst a) =v")
       assume d1:"\<exists>a. a \<in> set (statement2Assigns (act r)) \<and> (fst a) =v"
       from d1 obtain as where d2:"as \<in> set (statement2Assigns (act r)) \<and> (fst as) =v" by blast
         have d3:"\<forall>v.  v\<in>varOfExp ( substExpByStatement (IVar (fst as))  (act r)) \<longrightarrow> s(v) = s2 v"
           using c4 d2 by blast
         then show "expEval (substExpByStatement (IVar v)  (act r)) s = expEval (substExpByStatement (IVar v)  (act r)) s2"
           using agreeOnVarsOfExp d2 by blast
       next
         assume d1:"\<not>(\<exists>a. a \<in> set (statement2Assigns (act r)) \<and> (fst a) =v )"
         have d10:"(substExpByStatement (IVar v)  (act r)) =   (IVar v)"
           using d1 noSubVar by auto  
         then show "expEval (substExpByStatement (IVar v)  (act r)) s = expEval (substExpByStatement (IVar v)  (act r)) s2"
           using b2 c1 by auto
     qed     
     show " trans (act r) s v =   trans (act r) s2 v"
       by (metis c5 evalVar preCondOnExp)
   qed
 next
   have "formEval (pre r) s"
     by (simp add: b1 )
  have c4:"\<forall>va. va \<in> varOfForm  (pre r)\<longrightarrow> s(va) = s2 va"
    using a3 b2 setOfList by auto 
   show "formEval (pre r) s2"
     using \<open>formEval (pre r) s\<close> agreeOnVars c4 by blast
    
 qed
qed


lemma ruleSimCond2:
  assumes 

    a1:" formEval (pre r1) s \<longrightarrow>formEval (pre r2) s" and

   a3:"\<forall>v. v\<in>varOfForm (pre r2) \<longrightarrow>v \<in> V"  and 

  a4:" (\<forall>  v. v \<in>  varOfSent (act r2) \<longrightarrow>  v \<in> V \<longrightarrow> formEval (pre r1) s \<longrightarrow> 
    expEval (substExpByStatement (IVar v)  (act r2)) s = expEval (substExpByStatement (IVar v)  (act r1)) s)" and

   a41:" \<forall>  v. v \<in>  varOfSent (act r1) \<longrightarrow>  v \<in> V\<longrightarrow> v \<in>  varOfSent (act r2)" and

  a5:"\<forall> v va. v \<in> varOfSent (act r2) \<longrightarrow>va\<in>varOfExp ( substExpByStatement (IVar v)  (act r2))\<longrightarrow> va \<in> V " 

shows "trans_sim_on2 r1 r2 V (set F) s"
proof(unfold trans_sim_on2_def,(rule allI)+,(rule impI)+)
  fix  s2
  assume b1:"formEval (pre r1) s \<and> (\<forall> f. f \<in>(set F) \<longrightarrow> formEval f s )" and b2:"state_sim_on2 s s2 V"
  show "((state_sim_on2 (trans (act r1) s) (trans (act r2) s2) V \<and> (formEval (pre r2) s2 ))
           \<or> state_sim_on2 (trans (act r1) s) s2 V)"
   proof(rule disjI1,rule conjI)
    show "state_sim_on2 (trans (act r1) s) (trans (act r2) s2) V"
    proof(unfold state_sim_on2_def,(rule allI)+,(rule impI)+)
      fix  v
      assume  c2:"v \<in>V"
      have c20:"expEval  (substExpByStatement (IVar v) (act r1)) s = expEval (IVar v) (trans (act r1) s)" 
        using preCondOnExp by blast
     have c3:"expEval  (substExpByStatement (IVar v) (act r1)) s2 = expEval (IVar v) (trans (act r1) s2)"
       using preCondOnExp by blast

     (*have c30:"v \<in> varOfFormList F "
       using  c2 setOfList by auto *)
     have c31:"v \<in>  varOfSent (act r1) |v \<in>  varOfSent (act r2) | (v \<notin>  varOfSent (act r2) \<and>v \<notin>  varOfSent (act r2) )" by blast
     moreover{
       assume d1:"v \<in>  varOfSent (act r2)"
       have c4:"\<forall>va. va \<in> varOfExp (substExpByStatement  (IVar v)  (act r2)) \<longrightarrow> s(va) = s2 va"
         using a5 b2 d1 state_sim_on2_def by blast 
       (*using a5 b2 c1 c2 state_sim_on1_def by blast*)
 
      have c5:"expEval (substExpByStatement (IVar v)  (act r2)) s = expEval (substExpByStatement (IVar v)  (act r2)) s2"
        using agreeOnVars c4 by blast 

       
      have " trans (act r1) s v =   trans (act r2) s2 v"
        using a4 b1 c2 c5 d1 lemmaOnValOf by auto
   }
    moreover{
      assume d1:"v \<in>  varOfSent (act r1)"
      have d2:"v \<in>  varOfSent (act r2) "
        by (simp add: a41 c2 d1) 
       have c4:"\<forall>va. va \<in> varOfExp (substExpByStatement  (IVar v)  (act r2)) \<longrightarrow> s(va) = s2 va"
         using a5 b2 d2 state_sim_on2_def by blast
 
      have c5:"expEval (substExpByStatement (IVar v)  (act r2)) s = expEval (substExpByStatement (IVar v)  (act r2)) s2"
        using agreeOnVars c4 by blast 

      
      have " trans (act r1) s v =   trans (act r2) s2 v"
        using calculation(2) d2 by auto 
       }
     moreover{
       assume d1:"v \<notin> varOfSent (act r1) \<and> v \<notin>  varOfSent (act r2)"
       have d2:"trans (act r2) s2 v= s2 v"
         by (metis d1 evalVar lemmaOnValOf noEffectValOfStatementAux paraTheory.trans_def)

       have d3:"trans (act r1) s v= s v"
         by (metis d1 evalVar lemmaOnValOf noEffectValOfStatementAux paraTheory.trans_def)
         
      have " trans (act r1) s v =   trans (act r2) s2 v"
        using b2 c2 d2 d3 by auto
       } 
       ultimately show " trans (act r1) s v =   trans (act r2) s2 v"
         by satx
   qed
 next
   have "formEval (pre r2) s"
     by (simp add: b1 local.a1)
   have c4:"\<forall>va. va \<in> varOfForm  (pre r2)\<longrightarrow> s(va) = s2 va"
   proof(rule allI,rule impI)
     fix va
     assume c1:"va \<in> varOfForm  (pre r2)"
     from a3 have c2:"va \<in> V" using c1 by blast
      show  "s(va) = s2 va"
        using b2 c2 state_sim_on2_def by blast
    qed
      show "formEval (pre r2) s2"
     using \<open>formEval (pre r2) s\<close> agreeOnVars c4 by blast 
    
 qed
qed

lemma ruleSimCond20:
  assumes 

    a1:" formEval (pre r1) s \<longrightarrow>formEval (pre r2) s" and

   a3:"\<forall>v. v\<in>varOfForm (pre r2) \<longrightarrow>v \<in> V"  and 

  a4:" (\<forall>  v. v \<in>  varOfSent (act r2) \<longrightarrow>  v \<in> V \<longrightarrow> formEval (pre r1) s \<longrightarrow> 
    expEval (substExpByStatement (IVar v)  (act r2)) s = expEval (substExpByStatement (IVar v)  (act r1)) s)" and

   a41:" \<forall>  v. v \<in>  varOfSent (act r1) \<longrightarrow>  v \<in> V\<longrightarrow> v \<in>  varOfSent (act r2)" and

  a5:"\<forall> v va. v \<in> varOfSent (act r2) \<longrightarrow>va\<in>varOfExp ( substExpByStatement (IVar v)  (act r2))\<longrightarrow> va \<in> V " 

shows "trans_sim_on2 r1 r2 V (set F) s"
proof(unfold trans_sim_on2_def,(rule allI)+,(rule impI)+)
  fix  s2
  assume b1:"formEval (pre r1) s \<and> (\<forall> f. f \<in>(set F) \<longrightarrow> formEval f s )" and b2:"state_sim_on2 s s2 V"
  show "((state_sim_on2 (trans (act r1) s) (trans (act r2) s2) V \<and> (formEval (pre r2) s2 ))
           \<or> state_sim_on2 (trans (act r1) s) s2 V)"
   proof(rule disjI1,rule conjI)
    show "state_sim_on2 (trans (act r1) s) (trans (act r2) s2) V"
    proof(unfold state_sim_on2_def,(rule allI)+,(rule impI)+)
      fix  v
      assume  c2:"v \<in>V"
      have c20:"expEval  (substExpByStatement (IVar v) (act r1)) s = expEval (IVar v) (trans (act r1) s)" 
        using preCondOnExp by blast
     have c3:"expEval  (substExpByStatement (IVar v) (act r1)) s2 = expEval (IVar v) (trans (act r1) s2)"
       using preCondOnExp by blast

     (*have c30:"v \<in> varOfFormList F "
       using  c2 setOfList by auto *)
     have c31:"v \<in>  varOfSent (act r1) |v \<in>  varOfSent (act r2) | (v \<notin>  varOfSent (act r2) \<and>v \<notin>  varOfSent (act r2) )" by blast
     moreover{
       assume d1:"v \<in>  varOfSent (act r2)"
       have c4:"\<forall>va. va \<in> varOfExp (substExpByStatement  (IVar v)  (act r2)) \<longrightarrow> s(va) = s2 va"
         using a5 b2 d1 state_sim_on2_def by blast 
       (*using a5 b2 c1 c2 state_sim_on1_def by blast*)
 
      have c5:"expEval (substExpByStatement (IVar v)  (act r2)) s = expEval (substExpByStatement (IVar v)  (act r2)) s2"
        using agreeOnVars c4 by blast 

       
      have " trans (act r1) s v =   trans (act r2) s2 v"
        using a4 b1 c2 c5 d1 lemmaOnValOf by auto
   }
    moreover{
      assume d1:"v \<in>  varOfSent (act r1)"
      have d2:"v \<in>  varOfSent (act r2) "
        by (simp add: a41 c2 d1) 
       have c4:"\<forall>va. va \<in> varOfExp (substExpByStatement  (IVar v)  (act r2)) \<longrightarrow> s(va) = s2 va"
         using a5 b2 d2 state_sim_on2_def by blast
 
      have c5:"expEval (substExpByStatement (IVar v)  (act r2)) s = expEval (substExpByStatement (IVar v)  (act r2)) s2"
        using agreeOnVars c4 by blast 

      
      have " trans (act r1) s v =   trans (act r2) s2 v"
        using calculation(2) d2 by auto 
       }
     moreover{
       assume d1:"v \<notin> varOfSent (act r1) \<and> v \<notin>  varOfSent (act r2)"
       have d2:"trans (act r2) s2 v= s2 v"
         by (metis d1 evalVar lemmaOnValOf noEffectValOfStatementAux paraTheory.trans_def)

       have d3:"trans (act r1) s v= s v"
         by (metis d1 evalVar lemmaOnValOf noEffectValOfStatementAux paraTheory.trans_def)
         
      have " trans (act r1) s v =   trans (act r2) s2 v"
        using b2 c2 d2 d3 by auto
       } 
       ultimately show " trans (act r1) s v =   trans (act r2) s2 v"
         by satx
   qed
 next
   have "formEval (pre r2) s"
     by (simp add: b1 local.a1)
   have c4:"\<forall>va. va \<in> varOfForm  (pre r2)\<longrightarrow> s(va) = s2 va"
   proof(rule allI,rule impI)
     fix va
     assume c1:"va \<in> varOfForm  (pre r2)"
     from a3 have c2:"va \<in> V" using c1 by blast
      show  "s(va) = s2 va"
        using b2 c2 state_sim_on2_def by blast
    qed
      show "formEval (pre r2) s2"
     using \<open>formEval (pre r2) s\<close> agreeOnVars c4 by blast 
    
 qed
qed



lemma ruleSimCond3:
  assumes  a1:" formEval (pre r1) s \<longrightarrow>formEval (pre r2) s" and 

  a3:"\<forall>v. v\<in>varOfForm (pre r2) \<longrightarrow>  formEval (pre r1) s\<longrightarrow>(v \<in>V \<or> (v \<in> V' \<and> ((scalar2Nat (s(v)) )\<le> N)))"  and 

  a4:" (\<forall>  v. v \<in>  varOfSent (act r2) \<longrightarrow>  formEval (pre r1) s \<longrightarrow> 
    expEval (substExpByStatement (IVar v)  (act r2)) s = expEval (substExpByStatement (IVar v)  (act r1)) s)" and

  a41:" \<forall>  v. v \<in>  varOfSent (act r1)  \<longrightarrow> v \<in>V \<longrightarrow>v \<in>  varOfSent (act r2)" and  

  a42:" \<forall>  v. v \<in>  varOfSent (act r1) \<longrightarrow>v \<in>V'\<longrightarrow>  formEval (pre r1) s \<longrightarrow> 
    scalar2Nat ( expEval  ( substExpByStatement (IVar v)  (act r1)) s) \<le> N\<longrightarrow>
    v \<in>  varOfSent (act r2)" and

  a5:"\<forall> v va. v \<in> varOfSent (act r2) \<longrightarrow>va\<in>varOfExp ( substExpByStatement (IVar v)  (act r2))\<longrightarrow> 
      (va \<in> V | va \<in> V' \<and> scalar2Nat (s(va)) \<le> N)" 
 
shows "trans_sim_on3 r1 r2 V V' N  s"  
proof(unfold trans_sim_on3_def,(rule allI)+,(rule impI)+)
  fix  s2
  assume b1:"formEval (pre r1) s " and b2:" state_sim_on3 s s2 V V' N"
  show "((state_sim_on3 (trans (act r1) s) (trans (act r2) s2) V V' N \<and> (formEval (pre r2) s2 ))
           \<or> state_sim_on3 (trans (act r1) s) s2 V V' N)"
   proof(rule disjI1,rule conjI)
    show "state_sim_on3 (trans (act  r1) s) (trans (act r2) s2) V V' N "
    proof(unfold state_sim_on3_def,rule conjI)
      show " \<forall>v. v \<in> V \<longrightarrow> paraTheory.trans (act r1) s v = paraTheory.trans (act r2) s2 v"
      proof((rule allI)+,(rule impI)+)
        fix  v
        assume c1:"v \<in> V"  
        have c20:"expEval  (substExpByStatement (IVar v) (act r1)) s = expEval (IVar v) (trans (act r1) s)" 
          using preCondOnExp by blast
        have c3:"expEval  (substExpByStatement (IVar v) (act r1)) s2 = expEval (IVar v) (trans (act r1) s2)"
          using preCondOnExp by blast

    (* have c30:"v \<in> varOfFormList F "
       using c1 c2 setOfList by auto *)
     have c31:"v \<in>  varOfSent (act r1) |v \<in>  varOfSent (act r2) | (v \<notin>  varOfSent (act r2) \<and>v \<notin>  varOfSent (act r2) )" by blast
     moreover{
       assume d1:"v \<in>  varOfSent (act r2)"
       from b1 b2 d1  c1 a5 have c4:"\<forall>va. va \<in> varOfExp (substExpByStatement  (IVar v)  (act r2)) \<longrightarrow> s(va) = s2 va"
         by auto
 
      have c5:"expEval (substExpByStatement (IVar v)  (act r2)) s = expEval (substExpByStatement (IVar v)  (act r2)) s2"
        using agreeOnVars c4 by blast 

      
      have " trans (act r1) s v =   trans (act r2) s2 v"
        using a4 b1 c5 d1 lemmaOnValOf by auto
   }
    moreover{
      assume d1:"v \<in>  varOfSent (act r1)"
      have d2:"v \<in>  varOfSent (act r2) "
        using a41 c1 d1 by auto
      from b1 c1 a5 have c4:"\<forall>va. va \<in> varOfExp (substExpByStatement  (IVar v)  (act r2)) \<longrightarrow> s(va) = s2 va"
         using b2 d2 state_sim_on3_def by blast 
 
      have c5:"expEval (substExpByStatement (IVar v)  (act r2)) s = expEval (substExpByStatement (IVar v)  (act r2)) s2"
        using agreeOnVars c4 by blast 

      
      have " trans (act r1) s v =   trans (act r2) s2 v"
        using a4 b1 c5 d2 lemmaOnValOf by auto
       }
     moreover{
       assume d1:"v \<notin> varOfSent (act r1) \<and> v \<notin>  varOfSent (act r2)"
       have d2:"trans (act r2) s2 v= s2 v"
         by (metis d1 evalVar lemmaOnValOf noEffectValOfStatementAux paraTheory.trans_def)

       have d3:"trans (act r1) s v= s v"
         by (metis d1 evalVar lemmaOnValOf noEffectValOfStatementAux paraTheory.trans_def)
         
      have " trans (act r1) s v =   trans (act r2) s2 v"
        using b2 c1 d2 d3 by auto 
       } 
       ultimately show " trans (act r1) s v =   trans (act r2) s2 v"
         by satx
   qed
 next
   show " \<forall>v. v \<in> V' \<longrightarrow> scalar2Nat (paraTheory.trans (act r1) s v) \<le> N \<longrightarrow> paraTheory.trans (act r1) s v = paraTheory.trans (act r2) s2 v"
   proof((rule allI)+,(rule impI)+)
        fix  v
        assume c1:"v \<in> V'"  and c2:"scalar2Nat (paraTheory.trans (act r1) s v) \<le> N"
        have c20:"expEval  (substExpByStatement (IVar v) (act r1)) s = expEval (IVar v) (trans (act r1) s)" 
          using preCondOnExp by blast
        have c3:"expEval  (substExpByStatement (IVar v) (act r1)) s2 = expEval (IVar v) (trans (act r1) s2)"
          using preCondOnExp by blast

    (* have c30:"v \<in> varOfFormList F "
       using c1 c2 setOfList by auto *)
     have c31:"v \<in>  varOfSent (act r1) |v \<in>  varOfSent (act r2) | (v \<notin>  varOfSent (act r2) \<and>v \<notin>  varOfSent (act r2) )" by blast
     moreover{
       assume d1:"v \<in>  varOfSent (act r2)"
       from b1 c1 a5 have c4:"\<forall>va. va \<in> varOfExp (substExpByStatement  (IVar v)  (act r2)) \<longrightarrow> s(va) = s2 va"
         using b2 d1 state_sim_on3_def by blast 
 
      have c5:"expEval (substExpByStatement (IVar v)  (act r2)) s = expEval (substExpByStatement (IVar v)  (act r2)) s2"
        using agreeOnVars c4 by blast 

      
      have " trans (act r1) s v =   trans (act r2) s2 v"
        using a4 b1 c5 d1 lemmaOnValOf by auto
   }
    moreover{
      assume d1:"v \<in>  varOfSent (act r1)"
      have d2:"trans (act r1) s v = expEval  (substExpByStatement (IVar v) (act r1)) s"
        using c20 by auto 
      have d3:" scalar2Nat ( expEval  ( substExpByStatement (IVar v)  (act r1)) s) \<le> N"
        using c2 d2 by auto 
        
      have d2:"v \<in>  varOfSent (act r2) "
        using a42 b1 c1 d1 d3 by blast 
      from b1 c1 a5 have c4:"\<forall>va. va \<in> varOfExp (substExpByStatement  (IVar v)  (act r2)) \<longrightarrow> s(va) = s2 va"
         using b2 d2 state_sim_on3_def by blast 
 
      have c5:"expEval (substExpByStatement (IVar v)  (act r2)) s = expEval (substExpByStatement (IVar v)  (act r2)) s2"
        using agreeOnVars c4 by blast 

      
      have " trans (act r1) s v =   trans (act r2) s2 v"
        using a4 b1 c5 d2 lemmaOnValOf by auto
       }
     moreover{
       assume d1:"v \<notin> varOfSent (act r1) \<and> v \<notin>  varOfSent (act r2)"
       have d2:"trans (act r2) s2 v= s2 v"
         by (metis d1 evalVar lemmaOnValOf noEffectValOfStatementAux paraTheory.trans_def)

       have d3:"trans (act r1) s v= s v"
         by (metis d1 evalVar lemmaOnValOf noEffectValOfStatementAux paraTheory.trans_def)
         
      have " trans (act r1) s v =   trans (act r2) s2 v"
        using b2 c1 c2 d2 d3 by auto
       } 
       ultimately show " trans (act r1) s v =   trans (act r2) s2 v"
         by satx
     qed
   qed
   next
   have "formEval (pre r2) s"
     by (simp add: b1 local.a1) thm agreeOnVars
   have c4:"\<forall>va. va \<in>varOfForm  (pre r2)\<longrightarrow> s(va) = s2 va"
   proof(rule allI,rule impI)
     fix va
     assume c1:"va \<in> varOfForm  (pre r2)"
     from a3 b1 have c2:"va \<in> V | (va \<in> V'  \<and> ((scalar2Nat (s(va)) )\<le> N)) " 
        using c1 by blast 
      show  "s(va) = s2 va"
        using b2 c2  by auto
    qed
      show "formEval (pre r2) s2"
     using \<open>formEval (pre r2) s\<close> agreeOnVars c4 by blast 
    
 qed
qed


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
(*lemma onF[simp,intro]: 
  " varOfFormList invariantsAbs = 
  { (Field (Para (Ident ''n'') 0) ''data''),varType.Field (Para (Ident ''n'') 0) ''st'' , varType.Field (Para (Ident ''n'') 1) ''st'',
   (Ident ''x''),(Ident ''memDATA''),(Ident ''auxDATA'')  }"    
{v. \<exists>f. f \<in> invariantsAbs \<and> v \<in> varOfForm f})
  by auto*)
      
(*lemma example1:
  show " (\<exists>f. f \<in> F \<and> va \<in> varOfForm f)
    proof(rule allI, rule impI)
       fix va
       assume d1:"va \<in> varOfExp (substExpByStatement  (IVar v)  (act r2))"
       show  "(\<exists>f. f \<in> F \<and> va \<in> varOfForm f)"
         apply(cut_tac d1 a5 c1 c2 ,drule_tac x="f" in spec,drule_tac x="v" in spec,drule_tac x="va" in spec)
         apply simp


have c4:"formEval  (substFormByStatement f (act r1)) s1 = (formEval (substFormByStatement f (act r2))) s1"
        apply(cut_tac  a2, drule_tac x="s1" in spec, drule_tac x="f" in spec,simp,cut_tac b1 c1,simp) done
      have c5:"(\<forall> f. f \<in>F \<longrightarrow> formEval f s2 )" 
        apply(cut_tac b1 b2,auto) done
*)
end
