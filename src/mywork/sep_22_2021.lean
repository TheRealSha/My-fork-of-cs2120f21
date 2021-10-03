/-
SOME THEOREMS INVOLVING FALSE AND NEGATION
-/

theorem no_contradiction : ∀ (P : Prop), ¬(P ∧ ¬P) :=
begin 
  assume P,
  assume pandnotp,
  apply and.elim_right pandnotp,
  apply and.elim_left pandnotp,
end

theorem no_contradiction2 : ∀ (P : Prop), ¬(P ∧ ¬P) :=
begin 
  assume P,
  assume pandnotp,
  have p := pandnotp.left, --like and.elim_left
  have np := pandnotp.right,
  have f := np p, --*
  exact f,
end

/-
LAW OF THE EXCLUDED MIDDLE
-/
axiom excluded_middle : ∀ (P : Prop), (P ∨ ¬P)
begin 
  ∀∀∀∀∀∀∀∀∀∀∀∀∀∀∀∀∀∀∀∀∀∀∀∀∀∀∀∀∀∀∀∀∀∀∀∀
  --stuck
end

--contd sep 24
--!!!!!!!!!!!!!!!!!!!!

--1
example : 0 ≠ 1 :=
begin 
  -- ¬(0 = 1) 
  --- (0 = 1) → 1
  assume zeroequalsone,
  cases zeroequalsone,
end

--2
example : 0 ≠ 0 → 2 = 3 :=
begin 
  assume kitty,
  exact false.elim (kitty (eq.refl 0)),
end

--3
example : ∀ (P : Prop), P → ¬¬P :=
begin 
  assume P, 
  assume (p : P),
  -- ¬¬P
  -- ¬P → false
  -- (P → false) → false
  assume notp,
  apply notp p,
end 

--4
theorem neg_elim : ∀ (P : Prop), ¬¬P → P :=
begin 
  assume P,
  assume notnotp,
  -- negation elimination : 
  have pornotp := classical.em P,
  cases pornotp,
  --case: P is true
  --exact P,
  assumption,
  contradiction,
end