import HSFormal.Statement

/-!
# A fixture for the route-separation audit: a clean declaration in a module that imports HS_proof

The audit enters every constant of a module that imports HS_proof. `HSBridge.PurityTest` checks
that it then judges the constant by what it actually uses: the theorem below uses nothing from
HS_proof, although its module imports `HSFormal.Statement`.
-/

namespace HSBridge.PurityFixtures

/-- A theorem that uses no constant of HS_proof, in a module that imports HS_proof. -/
theorem two_mul_eq_add (n : ℕ) : 2 * n = n + n :=
  Nat.two_mul n

end HSBridge.PurityFixtures
