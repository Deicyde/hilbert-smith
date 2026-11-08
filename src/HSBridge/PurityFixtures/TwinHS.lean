import HSFormal.Statement

/-!
# A fixture for the route-separation audit: a theorem stated twice, here through HS_proof

This module and `HSBridge.PurityFixtures.TwinClean` both declare `HSBridge.PurityFixtures.twin`,
with the same statement; both import HS_proof and neither belongs to it, so the two copies are of
the same kind and the audit does not call their provenance ambiguous. This copy's proof mentions
HS_proof's `HSFormal.PadicExclusion`; the other's does not. `HSBridge.PurityTest` imports this
module first, so the kernel keeps the other copy, and checks that the audit walks both.
-/

namespace HSBridge.PurityFixtures

/-- `n + 0 = n`, proved through a conjunction that mentions HS_proof's `HSFormal.PadicExclusion`. -/
theorem twin (n : ℕ) : n + 0 = n :=
  (⟨Nat.add_zero n, rfl⟩ : n + 0 = n ∧ HSFormal.PadicExclusion = HSFormal.PadicExclusion).1

end HSBridge.PurityFixtures
