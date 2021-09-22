namespace implies
axioms ( P Q : Prop)

--define this identifier and bound tp P implies Q
def  if_P_is_true_then_so_is_Q : Prop := P → Q

axiom p : P
--assume P is true
--assume we have a proof of P (p)

axiom pq : P → Q
--assume that we have a proof, pq, of P → Q

--intro rule for implies: assume premise, show conclusion
--elim rule for implies: just apply it bro

#check pq
#check p
#check(pq p) --reduces to Q

/-
Suppose P and Q are propisitons and you 
know that P → Q and that P are both true.
Show that Q is true

Proof: Apply the truth of P → Q to the
truth of P to derive the truth of Q

Proof: By the elimination rul for → with
pq applied to p. 

Proof: By "modus ponens". QED
-/
end implies

/-
FOR ALL
-/
namespace all

axioms
  (T : Type )
  (P : T → Prop)
  (t : T)
  (a : ∀ (x : T), P x )

--Does t have property P? yah
example : P t := a t
#check a t

end all


/- 
AND and →
-/

axioms (P Q : Prop)

/-
Want a proof of P ∧ Q.
-/