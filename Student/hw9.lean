example (A B : Prop) : ¬(A ∧ B) → ¬A ∨ ¬B :=
λ nab =>
  let proof_of_aornota := or.elim (em A)
    (λ pa : A, false.elim (nab (and.intro pa (classical.by_contradiction (λ na, paornota (or.inl na)))))
    (λ na : ¬A, or.inl na)
  let proof_of_bornotb := or.elim (em B)
    (λ pb : B, false.elim (nab (and.intro (classical.by_contradiction (λ nb, pbornotb (or.inr nb)))) pb))
    (λ nb : ¬B, or.inr nb)
  or.swap (proof_of_aornota) (proof_of_bornotb)
