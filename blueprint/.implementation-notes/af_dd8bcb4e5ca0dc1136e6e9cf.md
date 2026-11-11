Planned declaration: `HSP.signatureTail_eventually_dvd`. The conclusion is stated as `∀ᶠ i in atTop, (p:ℤ) ∣ σ i` for any representative `σ`. Use `IsPGroup.iff_orderOf`, `Subgroup.zpowers` and `Polynomial.eval_one_cyclotomic_prime_pow`. HS paper lines 367-380.

c2 fix: tau_P, tau_V are the new def signatures/point-functors/tail-permutation-functor (C_p acting through chi_i, not G_i/ker chi_i). `Φ ∘ (τ ⊗ -) = τ_V ∘ Φ` should be a `Functor.ext` with `rfl` on objects, provided permutation-tensor uses the same enumeration term as categories' tensor-permutation. Step 1 transports nilpotence from L(A_X) to L(A_G(X)) by `ιOfLE` both ways (an isomorphism of categories) and ultimate equivalence-invariance. Rests on the open Lemma U.


f-algebra pass (g-sweep 2): the $G_i$ are `Group`s written multiplicatively (no commutativity); step 5 is `g_i ≠ 1`. Step 1 uses `HSP.supportWholeIso` (categories/supports/support-whole.md) instead of the inline inclusion argument.
