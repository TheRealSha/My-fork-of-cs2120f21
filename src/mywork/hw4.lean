/-
esha khator (kaq8eg)
alexander davis (wfy8cn)
-/
-- 1
example : 0 ≠ 1 :=
begin
  -- ¬ (0 = 1)
  -- (0 = 1) → false
  assume h,
  cases h, --trivial,
end


-- 2
example : 0 ≠ 0 → 2 = 3 :=
begin
  assume h,
  have zeqz := eq.refl 0,
  have f : false := h zeqz,
  exact false.elim (f),
end

-- 3
example : ∀ (P : Prop), P → ¬¬P :=
begin
  assume P,
  assume (p : P),
  -- ¬¬P
  -- ¬P → false
  -- (P → false) → false
  assume h,
  have f := h p,
  exact f,
end 

-- We might need classical (vs constructive) reasoning 
#check classical.em
open classical
#check em

/-
axiom em : ∀ (p : Prop), p ∨ ¬p

This is the famous and historically controversial
"law" (now axiom) of the excluded middle. It's is
a key to proving many intuitive theorems in logic
and mathematics. But it also leads to giving up on
having evidence *why* something is either true or
not true, in that you no longer need a proof of 
either P or of ¬P to have a proof of P ∨ ¬P.
-/

-- 4
theorem neg_elim : ∀ (P : Prop), ¬¬P → P :=
begin
  assume P,
  assume h,
  have pornp := classical.em P,
  cases pornp with p pn,
  assumption,
  contradiction,
end
-- proof by negation: trying to proove not p 
  -- assume p then show false
-- proof by contradiction: trying to prove p
  -- show p is false

-- 5
theorem demorgan_1 : ∀ (P Q : Prop), ¬ (P ∧ Q) ↔ ¬ P ∨ ¬ Q :=
begin
  assume P Q,
  apply iff.intro,  --split,
  --forwards
  assume notpandq,
  have pornp := classical.em P,
  cases pornp,
    --case: P is true
    apply or.intro_right (¬P) _,
    assume q,
    have pandq := and.intro pornp q,
    exact notpandq pandq,
    -- case: P implies false
    apply or.intro_left (¬Q) pornp,
  --backwards
  assume notporq,
  cases notporq,
    -- cases: ¬P is true
    assume pandq2,
    have p := and.elim_left pandq2,
    apply notporq p, --contradiction
    -- case: ¬Q is true
    assume pandq3,
    have q := and.elim_right pandq3,
    apply notporq q,
end

/- admit, a command to put a knife to 
lean's neck and force it to accept it -/

-- 6
theorem demorgan_2 : ∀ (P Q : Prop), ¬ (P ∨ Q) → ¬P ∧ ¬Q :=
begin
  assume P Q,
  assume notporq,
  apply and.intro _ _,
  --build the parts for and.intro
  assume p,
  have porq := or.intro_left Q p,
  contradiction,
  assume q, 
  have porq := or.intro_right P q,
  contradiction,
end


-- 7
theorem disappearing_opposite : 
  ∀ (P Q : Prop), P ∨ ¬P ∧ Q ↔ P ∨ Q := 
begin
  assume P Q,
  apply iff.intro,
  --forwards
  assume pornotpandq,
  cases pornotpandq,
    --case: P is true
  apply or.intro_left Q pornotpandq,
    --case: ¬P or Q is true
  have q := and.elim_right pornotpandq,
  apply or.intro_right P q,
  --backwards
  assume porq,
  cases porq,
    -- case: P is true
    apply or.intro_left (¬P ∧ Q) porq,
    -- case Q is true
    have pornotp := classical.em P,
    cases pornotp,
      -- case P is true
      apply or.intro_left (¬P ∧ Q) pornotp,
      -- case ¬P is true
      apply or.intro_right P _,
      apply and.intro pornotp porq,
end


-- 8
theorem distrib_and_or : 
  ∀ (P Q R: Prop), (P ∨ Q) ∧ (P ∨ R) ↔
                    P ∨ (Q ∧ R) :=
begin
  assume P Q R,
  apply iff.intro _ _,
  --forward
   assume porqandporr,
   have porq := and.elim_left porqandporr,
   have porr := and.elim_right porqandporr,
   cases porq,
    -- case P is true
    apply or.intro_left (Q ∧ R) porq,
    -- case Q is true
    cases porr,
      -- case: P is true
      apply or.intro_left (Q ∧ R) porr,
      -- case R is true
      apply or.intro_right P _,
      apply and.intro porq porr,
  -- backward
  assume porqandr,
  apply and.intro _ _,
  cases porqandr,
    -- case: P is true
    apply or.intro_left Q porqandr,
    -- case: Q ∧ R is true
    have q := and.elim_left porqandr,
    apply or.intro_right P q,
  cases porqandr,
    -- case: P is true
    apply or.intro_left R porqandr,
    -- case Q ∧ R is true
    have r := and.elim_right porqandr,
    apply or.intro_right P r,
end

-- remember or is right associative
-- you need this to know what the lefts and rights are
-- 9
theorem distrib_and_or_foil : 
  ∀ (P Q R S : Prop),
  (P ∨ Q) ∧ (R ∨ S) ↔
  (P ∧ R) ∨ (P ∧ S) ∨ (Q ∧ R) ∨ (Q ∧ S) :=
begin
  assume P Q R S,
  apply iff.intro,
  --forwards
  assume porqandrors,
  have porq := and.elim_left porqandrors,
  have rors := and.elim_right porqandrors,
  cases porq,
    cases rors,
    -- case: P is true and R is true
    apply or.intro_left _ _,
    apply and.intro porq rors,
    -- case: P is true and S is true
    apply or.intro_right _ _,
    apply or.intro_left _ _,
    apply and.intro porq rors,
    cases rors,
    -- case: Q is true and R is true
    apply or.intro_right _ _,
    apply or.intro_right _ _,
    apply or.intro_left _ _,
    apply and.intro porq rors,
    -- case: Q is true and S is true
    apply or.intro_right _ _,
    apply or.intro_right _ _,
    apply or.intro_right _ _,
    apply and.intro porq rors,
  -- backwards
  assume foil,
  cases foil,
  apply and.intro _ _,
  apply or.intro_left Q (and.elim_left foil),
  apply or.intro_left S (and.elim_right foil),
  cases foil,
  apply and.intro _ _,
  apply or.intro_left Q (and.elim_left foil),
  apply or.intro_right R (and.elim_right foil),
  cases foil,
  apply and.intro _ _,
  apply or.intro_right P (and.elim_left foil),
  apply or.intro_left S (and.elim_right foil),
  apply and.intro _ _,
  apply or.intro_right P (and.elim_left foil),
  apply or.intro_right R (and.elim_right foil),
end


/- 10
Formally state and prove the proposition that
not every natural number is equal to zero.
-/
lemma not_all_nats_are_zero : ¬(∀ (n : ℕ), n = 0) :=
begin
  assume pred,
  have aaagh := pred 1,
  cases aaagh,
end 

-- 11. equivalence of P→Q and (¬P∨Q)
example : ∀ (P Q : Prop), (P → Q) ↔ (¬P ∨ Q) :=
begin
  assume P Q,
  apply iff.intro,
  -- forward
  assume quokka,
  have porp := classical.em P,
  cases porp,
    --case: P is true
    apply or.intro_right (¬P) _,
    apply quokka porp,
    --case: ¬P is true
    apply or.intro_left Q porp,
  --backward
  assume porqupine,
  assume puffin,
  cases porqupine,
  contradiction,
  exact porqupine,
end

-- 12
example : ∀ (P Q : Prop), (P → Q) → (¬ Q → ¬ P) :=
begin
  assume P Q,
  assume pimpq,
  assume notq,
  assume p,
  have q := pimpq p,
  contradiction,
end

-- 13
example : ∀ (P Q : Prop), ( ¬P → ¬Q) → (Q → P) :=
begin
  assume P Q,
  assume notpimpnotq,
  assume q,
  have porp := classical.em P,
  cases porp,
    --case P is true
    exact porp,
    --case ¬P is true
    have p := notpimpnotq porp,
    contradiction,
end

