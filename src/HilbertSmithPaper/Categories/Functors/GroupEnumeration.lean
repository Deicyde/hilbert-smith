import Mathlib

/-!
# The group enumeration

For a finite group `G` the bijection `ε_G : G → {0..|G|-1}` is `Fintype.equivFin G`, fixed once,
and the *group enumeration* is `e^G_n : G × Fin n ≃ Fin (|G| n)`, `e(g, k) = ε_G(g) n + k`
(`HSP.groupEnum`).
-/

namespace HSP

/-- **The group enumeration** `e^G_n : G × Fin n ≃ Fin (|G| n)`, `e(g, k) = ε_G(g) n + k` with
`ε_G = Fintype.equivFin G`. -/
noncomputable def groupEnum (G : Type*) [Fintype G] (n : ℕ) :
    G × Fin n ≃ Fin (Fintype.card G * n) :=
  ((Fintype.equivFin G).prodCongr (Equiv.refl _)).trans finProdFinEquiv

end HSP
