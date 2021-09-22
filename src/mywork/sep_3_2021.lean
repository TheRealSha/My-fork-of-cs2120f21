/-
Theorem: Equality is symmetric
-/
theorem eq_symm : 
 ∀ (T : Type) (x y : T), x = y → y = x:=
 begin
   assume (T : Type),
   assume (x y : T),
   assume (e : x = y),
   rw e, 
 end
 /-
 Theorem: Equality is symmetric. 
 In other words  ∀ (T : Type) (x y : T), x = y → y = x:=

 Proof: What we really need to show is that
 First we will assume that T is any type and we have 
 objects x and y of this type What remains to be shown 
 is that x = y → y = x. To prove this, we'll assume the 
 premise, that x = y, and in this context we to prove 
 y = x. But by the axiom of substitutability of equals, 
 and using the fact x = y, we can rewrite x in the goal 
 as y, yielding y = y as our new proof goal. But this is 
 true by the axiom of reflexivity of equality. QED.
 -/

 /-
Theorem: Equality is transitive
-/
theorem eq_trans : 
 ∀ (T : Type) (x y z : T), x = y → y = z → x = z :=
 begin
   assume T,
   assume x y z,
   assume e1,
   assume e2,
   rw e1,
   exact e2,
 end