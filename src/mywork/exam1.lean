/- 
   *******************************
   PART 1 of 2: AXIOMS [50 points]
   *******************************
Esha Khator (kaq8eg)
-/
/-
Explain the inference (introduction and
elimination) rules of predicate logic as
directed below. To give you guidance on
how to answer these questions we include
answers for some questions.
-/


-- -------------------------------------

/- #1: → implies [5 points]

INTRODUCTION

Explain the introduction rule for →. 

[We give you the answer here.]

In English: Given propositions, P and Q, 
a derivation (computation) a proof of Q 
from any proof of P, is a proof of P → Q.

In constructive logic, a derivation is a
given as a function definition. A proof
of P → Q literally is a function, that,
when given any proof of P as an argument
returns a proof of Q. If you define such
a function, you have proved P → Q.

ELIMINATION

Complete the definition of the elimination
rule for →.

(P Q : Prop) (p2q : P → Q) (p : P)
---------------------------------- elim
      ((p → q) p : Q)
applying a proof of P implies Q to a proof of p 
to get q in return
-/

-- Give a formal proof of the following
example : ∀ (P Q : Prop) (p2q : P → Q) (p : P), Q :=
begin
  assume P Q,
  assume piq,
  apply piq,
end

-- Extra credit [2 points]. Who invented this principle?
-- demorgan


-- -------------------------------------


/- #2: true [5 points]

INTRODUCTION

Give the introduction rule for true using
inference rule notation.

[Here's our answer.]

---------- intro
(pf: true)

Give a brief English language explanation of
the introduction rule for true.

-- There's only one proof of true which is 
  true.intro and therefore is always true

ELIMINATION

Give an English language description of the
eliimination rule for true.

[Our answer]

A proof of true carries no information so
there's no use for an elimination rule.
-/

-- Give a formal proof of the following:

example : true := true.intro


-- -------------------------------------

/- #3: ∧ - and [10 points]

INTRODUCTION

Using inference rule notation, give the 
introduction rule for ∧.

[Our answer]

(P Q : Prop) (p : P) (q : Q)
---------------------------- intro
        (pq : P ∧ Q)

Given an English language description of
this inference rule. What does it really
say, in plain simple English. 

-- Given a proof that p is true and given 
  a proof that q is true, we can conclude
  p and q is true

ELIMINATION

Given the elimination rules for ∧ in both
inference rule and English language forms.

(P Q : Prop) (p q : P ∧ Q)
---------------------------- .left
        (p : P) 
Given that p and q is true, we can derive that
p must be true by the left elimination rule of ∧ 

  (P Q : Prop) (p q : P ∧ Q)
---------------------------- .right
          (q : Q)
Given that p and q is true, we can derive that
q must be true by the right elimination rule of ∧ 

-/

/-
Formally state and prove the theorem that, 
for any propositions P and Q,  Q ∧ P → P. 
-/

example : ∀(P Q : Prop), Q ∧ P → P := 
begin 
  assume P Q,
  assume qandp,
  apply and.elim_right qandp,
end 



-- -------------------------------------

/- #4: ∀ - for all [10 points]

INTRODUCTION

Explain in English the introduction rule for ∀. If 
T is any type (such as nat) and Q is any proposition 
(often in the form of a predicate on values of the
given type), how do you prove ∀ (t : T), Q? What is
the introduction rule for ∀?

-- Assume we are given any arbituary object t of type T
  and if the propisition Q works for that object t, it 
  will work for all objects of the same type

ELIMINATION

Here's an inference rule representation of the elim
rule for ∀. First, complete the inference rule by
filling in the bottom half, then Explain in English
what it says.

(T : Type) (Q : Prop), (pf : ∀ (t : T), Q) (t : T)
-------------------------------------------------- elim
                (Q t : Q T)

-- Apply ∀ (t : T), Q to an arbituary value of T such as t
  and then show since t has Q, and proove that all objects
  of type T has the property Q

Given a proof, (pf : ∀ (t : T), Q), and a value, (t : T),
briefly explain in English how you *use* pf to derive a
proof of Q.

-- apply pf to t to create a proof of Q t
-/

/-
Consider the following assumptions, and then in the
context of these assumptions, given answers to the
challenge problems.
-/

axioms
  (Person : Type)
  (KnowsLogic BetterComputerScientist : Person → Prop)
  (LogicMakesYouBetterAtCS: 
    ∀ (p : Person), KnowsLogic p → BetterComputerScientist p)
     
  -- formalizee the following assumptions here
  -- (1) Lynn is a person
  -- (2) Lynn knows logic
  -- add answer here
  (lynn : Person)
  -- add answer here 
  (lynnKnowsLogic : KnowsLogic lynn)

/-
Now, formally state and prove the proposition that
Lynn is a better computer scientist
-/
example : ∀ (p : Person), KnowsLogic p → BetterComputerScientist p := 
begin 
  assume lynn,
  assume lynnKnowsLogic,
  apply LogicMakesYouBetterAtCS lynn,
  exact lynnKnowsLogic,
end



-- -------------------------------------

/- #5: ¬ - not [10 points] 

The ¬ connective in Lean is short for *not*. Give
the short formal definition of ¬ in Lean. Note that
surround the place where you give your answer with
a namespace. This is just to avoid conflicting with
Lean's definition of not.
-/
 
namespace hidden
def not (P : Prop) := P → false -- fill in the placeholder
end hidden

/-
Explain precisely in English the "proof strategy"
of "proof by negation." Explain how one uses this
strategy to prove a proposition, ¬P. 
-/

-- Proof by negation is trying to proove ¬P so you assume P then show false

/-
Explain precisely in English the "proof strategy"
of "proof by contradiction." Explain how one uses
this strategy to prove a proposition, P (notice 
the lack of a ¬ in front of the P). 

Fill in the blanks the following partial answer:

To prove P, assume ¬P and show that it leads to a contradiction.
From this derivation you can conclude P → false → false.
Then you apply the rule of negation P is true
to that result to arrive a a proof of P. We have
seen that the inference rule you apply in the 
last step is not constructively valid but that it
is uninformatively valid, and that accepting the axiom
of the excluded middle suffices to establish negation
elimination (better called double negative elimination)
as a theorem.
-/



-- -------------------------------------

/- 
#6: ↔ - if and only if, equivalent to [10 points]
-/

/-
ELIMINATION 

As with ∧, ↔ has two elimination rules. You can 
see their statements here.
-/
#check @iff.elim_left
#check @iff.elim_right

/-
Formally state and prove the theorem that 
biimplication, ↔, is *commutative*. Note: 
put parentheses around each ↔ proposition,
as → has higher precedence than ↔. Recall
that iff has both elim_left and elim_right
rules, just like ∧.
-/

example : ∀ (P Q : Prop), (P ↔ Q) ↔ (Q ↔ P) := 
begin
  assume P Q,
  apply iff.intro _ _,
  --forward
    assume piffq,
    apply iff.intro _ _,
      assume q,
      apply iff.elim_right piffq,
      exact q,
      apply iff.elim_left piffq,
  --backwards
    assume qiffp,
    apply iff.intro _ _,
      assume p,
      apply iff.elim_right qiffp,
      exact p,
      apply iff.elim_left qiffp,
end


/- 
   ************************************************
   PART 2 of 3: PROPOSITIONS AND PROOFS [50 points]
   ************************************************
-/

/- #7 [20 points]

First, give a fluent English rendition of
the following proposition. Note that the
identifier we use, elantp, is short for
"everyone likes a nice, talented person."
Then give a formal proof. Hint: try the
"intros" tactic by itself where you'd
previously have used assume followed by
a list of identifiers. Think about what
each expression means. 
-/


def ELJL : Prop := 
  ∀ (Person : Type) 
    (Nice : Person → Prop)
    (Talented : Person → Prop)
    (Likes : Person → Person → Prop)
    (elantp : ∀ (p : Person), 
      Nice p → Talented p → 
      ∀ (q : Person), Likes q p)
    (JohnLennon : Person)
    (JLNT : Nice JohnLennon ∧ Talented JohnLennon),
    (∀ (p : Person), Likes p JohnLennon) 
    
/-  
  Person is a type. A person can be nice, can be talented.
  A person can like another person.
  Every person p who is nice and is talented is liked by a person q.
-/
example : ELJL :=
begin
  assume person nice talented likes elantp,
  assume john,
  assume natjohn,
  have nicejohn := and.elim_left natjohn,
  have taljohn := and.elim_right natjohn,
  assume q,
  have x :=  elantp john,
  apply x nicejohn taljohn,

end
/-
assume p,
  assume nice,
  assume talented,
  assume like,
  assume elantp,
  assume JohnLennon,
  apply elantp JohnLennon,-/

/- #8 [10 points]

If every car is either heavy or light, and red or 
blue, and we want a prove by cases that every car 
is rad, then: 

-- how many cases will need to be considered? 4
-- list the cases (informaly)
    -- answer here
     - the car is heavy and red
     - the car is light and red
     - the car is heavy and blue
     - the car is light and blue

-/

/-
  *********
  RELATIONS
  *********
-/


/- #9 [20 points]
Equality can be understood as a binary relation
on objects of a given type. There is a binary 
equality relation on natural numbers, rational 
numbers, on strings, on Booleans, and so forth.

We also saw that from the two axioms (inference
rules) for equality, we could prove that it is
not only reflexive, but also both symmetric and
transitive.

Complete the following definitions to express
the propositions that equality is respectively
symmetric and transitive. (Don't worry about
proving these propositions. We just want you
to write them formally, to show that you what
the terms means.)
-/

def eq_is_symmetric : Prop :=
  ∀ (T : Type) (x y : T), (x = y → y = x)

def eq_is_transitive : Prop :=
  ∀ (T : Type) (x y z : T), (x = y → y = z → x = z)


/-
  ************
  EXTRA CREDIT
  ************
-/

/- 
EXTRA CREDIT: State and prove the proposition
that (double) negation elimination is equivalent
to excluded middle. You get 1 point for writing
the correct proposition, 2 points for proving it
in one direction and five points for proving it
both directions. 
-/

#check classical.em
def negelim_equiv_exmid : Prop := 
  ∀ (P : Prop), (¬¬P ↔ (P ∨ ¬P))
example :  negelim_equiv_exmid :=
begin 
  assume P,
  apply iff.intro _ _,
  --forwards
  assume nnp,
  apply or.intro_left,
  have pornp := classical.em P,
  cases pornp,
  exact pornp,
  contradiction,
  --backwards
  assume pornp,
  assume np,
  have pornp := classical.em P,
  cases pornp,
  contradiction,

  
end


/- 
EXTRA CREDIT: Formally express and prove the
proposition that if there is someone everyone
loves, and loves is a symmetric relation, then 
thre is someone who loves everyone. [5 points]
-/

axiom Loves : Person → Person → Prop

example : ( ∀ (q : Person), ∃ (p: Person), Loves q p) →
 ( ∀ (q : Person), ∃ (p: Person), Loves p q) :=
begin 
  assume elp,
  assume q,
  apply exists.intro q,
  have x :=  (elp q),
  apply x q,
end
