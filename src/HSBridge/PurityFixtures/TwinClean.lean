import HSFormal.Statement

/-!
# A fixture for the route-separation audit: a theorem stated twice, here without HS_proof

The second copy of `HSBridge.PurityFixtures.twin` (see `HSBridge.PurityFixtures.TwinHS`). This
module imports HS_proof, but this copy's proof uses nothing from it. Loaded last, it is the copy
the kernel keeps.
-/

namespace HSBridge.PurityFixtures

/-- `n + 0 = n`, proved without HS_proof. -/
theorem twin (n : ℕ) : n + 0 = n :=
  Nat.add_zero n

end HSBridge.PurityFixtures
