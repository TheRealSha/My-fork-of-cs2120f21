axioms 
 (Person : Type)
 (Likes : Person → Person → Prop)

 example :
 ¬ (∀ p : Person, Likes p p) ↔
 ∃ p : Person, ¬Likes p p :=
 begin 
   split,
   -- forwards
    assume h,
    have f := classical.em (∃ (p : Person), ¬Likes p p),
    cases f,
      --case: there IS someone who dislikes themself
      exact f, --asumption
      --case there IS NOT someone who dislikes themself
      --propose new fact, proof to be constructed
      have contra : ∀ (p : Person), Likes p p :=_,
      --prove current goal using proposed fact
      contradiction,
      --supposition
      assume p,
      have g := classical.em (Likes p p),
      cases g,
      assumption,
      have a : ∃ (p : Person), ¬Likes p p := exists.intro p g,
      contradiction,
    --backwards
    admit,
 end