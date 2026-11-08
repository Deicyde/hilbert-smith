import HSBridge.Purity
import FCSolution
import FCChallenge

/-!
# A fixture for the route-separation audit: the FC pair in the other order

`HSBridge.PurityTest` imports HS_proof's `FCChallenge` before `FCSolution`. This module imports
them the other way round. Lean's index of declaring modules then names `FCSolution`, the kernel
holds `FCChallenge`'s `sorry` body, and `#print axioms` reads the axioms recorded for
`FCSolution`'s copy, which are clean. Both modules belong to HS_proof's package, so the audit
reports the constant as HS_proof in this order too. (The two `declaration uses 'sorry'` warnings
that Lake prints when it builds `FCChallenge` come from HS_proof's own file.)
-/

/--
error: route audit: 'Hilbert5.hilbert_smith_padic_formulation.variants.second_countable' depends
  on HS_proof; entry points:
  Hilbert5.hilbert_smith_padic_formulation.variants.second_countable
-/
#guard_msgs (whitespace := lax) in
#assert_route_pure Hilbert5.hilbert_smith_padic_formulation.variants.second_countable
