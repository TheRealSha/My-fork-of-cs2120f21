/-
esha khator (kaq8eg)
alexander davis (wfy8cn)
-/

/-
Prove the following simple logical conjectures.
Give a formal and an English proof of each one.
Your English language proofs should be complete
in the sense that they identify all the axioms
and/or theorems that you use.
-/ 

example : true := true.intro

example : false := _    
-- trick question? why? there is not any proof of false

example : ∀ (P : Prop), P ∨ P ↔ P := 
begin
  assume P,
  apply iff.intro _ _,
  --forward
  assume porp,
  apply or.elim porp,
    --left disjunct is true
    assume p1,
    exact p1,
    --right disjunct is true
    assume p2,
    exact p2,
  --backwards
  assume p3,
  exact or.intro_left P p3,
end

example : ∀ (P : Prop), P ∧ P ↔ P := 
begin
  assume P,
  apply iff.intro _ _,
  --forward
  assume pandp,
  apply and.elim_left pandp, 
  --backwards
  assume p,
  apply and.intro p p, 
end

example : ∀ (P Q : Prop), P ∨ Q ↔ Q ∨ P := 
begin
  assume P Q,
  apply iff.intro _ _,
  --forward
  assume porq,
  apply or.elim porq,
  --left disjunct is true
    assume p1,
    apply or.intro_right Q p1,
  --right disjunct is true
    assume q1,
    apply or.intro_left P q1,
  --backwards
  assume qorp,
  apply or.elim qorp,
   --left disjunct is true
    assume q2,
    apply or.intro_right P q2,
  --right disjunct is true
    assume p2,
    apply or.intro_left Q p2,
end

example : ∀ (P Q : Prop), P ∧ Q ↔ Q ∧ P := 
begin
  assume P Q,
  apply iff.intro _ _,
  --forward
  assume pandq,
  apply and.intro _ _,
  apply and.elim_right pandq,
  apply and.elim_left pandq,
  --backwards
  assume qandp,
  apply and.intro _ _,
  apply and.elim_right qandp,
  apply and.elim_left qandp,

end

example : ∀ (P Q R : Prop), P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := 
begin
  assume P Q R,
  apply iff.intro _ _,
  --forward
  assume pandqorr,
  have p := and.elim_left pandqorr,
  have qorr := and.elim_right pandqorr,
  cases qorr,
    --case: q is true
    apply or.intro_left _ _,
    apply and.intro p qorr,
    --case: r is true
    apply or.intro_right _ _,
    apply and.intro p qorr,
  --backward
  assume pandqorpandr,
  apply and.intro _ _,
  cases pandqorpandr,
   --case P and Q is true
   have p2 : P := and.elim_left pandqorpandr,
   exact p2,
    --case P and R is true
   have p3 : P := and.elim_left pandqorpandr,
   exact p3,
  cases pandqorpandr,
   --case P and Q is true
   have q2 : Q := and.elim_right pandqorpandr,
   apply or.intro_left R q2,
    --case P and R is true
   have r2 : R := and.elim_right pandqorpandr,
   apply or.intro_right Q r2,
end

example : ∀ (P Q R : Prop), P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) := 
begin
  assume P Q R,
  apply iff.intro _ _,
  --forward
  assume porqandr,
  apply and.intro _ _,
  cases porqandr,
    --cases P is true
    apply or.intro_left Q porqandr,
    --cases Q and R is true
    apply or.intro_right P (and.elim_left porqandr),
  cases porqandr,
    --cases P is true
    apply or.intro_left R porqandr,
    --cases Q and R is true
    apply or.intro_right P (and.elim_right porqandr),
  --backwards
  assume porqandporr,
  have porq := and.elim_left porqandporr,
  have porr := and.elim_right porqandporr,
  cases porq,
    --case: P is true
    apply or.intro_left (Q ∧ R) porq,
    --case: Q is true
    cases porr,
      --case: P is true
      apply or.intro_left (Q ∧ R) porr,
      --case R is true
      apply or.intro_right P (and.intro porq porr),
end

example : ∀ (P Q : Prop), P ∧ (P ∨ Q) ↔ P := 
begin
  assume P Q,
  apply iff.intro _ _,
  --forward
  assume pandporq,
  apply and.elim_left pandporq,
  --backward
  assume p5,
  apply and.intro p5,
  apply or.intro_left Q p5,
end

example : ∀ (P Q : Prop), P ∨ (P ∧ Q) ↔ P := 
begin
  assume P Q,
  apply iff.intro _ _,
  --forwards
  assume porpandq,
  cases porpandq,
    --case: P is true
    exact porpandq,
    --case: P and Q is true
    apply and.elim_left porpandq,
  --backwards
  assume p6,
  apply or.intro_left (P ∧ Q) p6,
end

example : ∀ (P : Prop), P ∨ true ↔ true := 
begin
  assume P,
  apply iff.intro _ _,
  --forwards
  assume portrue,
  exact true.intro,
  --backwards
  assume t,
  apply or.intro_right P t,
end

example : ∀ (P : Prop), P ∨ false ↔ P := 
begin
  assume P,
  apply iff.intro _ _,
  --forwards
  assume porfalse,
  cases porfalse,
    --case P is true
    exact porfalse,
    --case false is true 
    cases porfalse,
  --backwards
  assume p8,
  apply or.intro_left false p8,
end

example : ∀ (P : Prop), P ∧ true ↔ P := 
begin
  assume P,
  apply iff.intro _ _,
  --forwards
  assume pandtrue,
  apply and.elim_left pandtrue,
  --backwards
  assume p7,
  apply and.intro p7 true.intro,
end

example : ∀ (P : Prop), P ∧ false ↔ false := 
begin
  assume P,
  apply iff.intro _ _,
  --forwards
  assume pandfalse,
  apply and.elim_right pandfalse,
  --backwards
  assume f,
  cases f,
  --theres no proof of false, stuck
end


