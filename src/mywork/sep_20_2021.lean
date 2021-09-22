/-
if ¬P is true then there can be no proof of P

if P implies false: if P is true then there is a proof 
of false, but there are no proofs of false, so P has 
no proofs
-/

--does false imply false
example : false → false :=
begin
  assume f,
  exact f,
end

--does false imply true
example : false → true :=
begin
  assume f,
  exact true.intro,
end

--does true imply true
example : true → true :=
begin
  assume t,
  exact true.intro,
end

--does true imply false
example : true → false :=
begin
  assume t,
  --SIKE youre stuck
end

/-
***********
We define ¬P to be the proposition P → false
Same proof strategy for these two
***********
-/

#check not

--examples
/-
you cant prove false but you can prove ¬ false
-/

example : ¬ (0 = 1) :=
begin 
  assume h,
  cases h,
end

--case analysis
example : ∀ (P Q R : Prop), P ∨ Q → R :=
begin
  assume P Q R,
  assume pq,
  case pq,  --or elimination
            --stuck here, ofc
end

example : false → false :=
begin
  assume f,
  cases f,
end

example : false → false :=
begin
  assume f,
  exact false.elim f,
end

theorem false_elim (P : Prop) (f : false) : P :=
begin 
  exact false.elim f,
  --or we can do cases f,
end