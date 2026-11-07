import HilbertSmith.Statements
import HSGeneral.Interior
import HSGeneral.Padic
import HSGeneral.FormalConjectures
import HSGeneral.Group

/-!
# HS_proof's theorems without second countability

HS_proof (adbrw/HS_proof, library `HSFormal`) proves p-adic exclusion and the Hilbert–Smith
conjecture for second-countable manifolds and groups. This library removes those assumptions:

* p-adic exclusion without second countability, for manifolds in every universe, with and without
  boundary, and Formal Conjectures' `Hilbert5.hilbert_smith_padic_formulation`;
* the Hilbert–Smith theorem without countability for groups and manifolds in `Type` only, with and
  without boundary. Formal Conjectures' `Hilbert5.hilbert_smith_conjecture` (any universe,
  real-analytic conclusion) is not proved here.

The code imports `HSFormal` and calls its declarations; it copies none of HS_proof's proofs or
text. Each file lists the `HSFormal` declarations it uses.
-/
