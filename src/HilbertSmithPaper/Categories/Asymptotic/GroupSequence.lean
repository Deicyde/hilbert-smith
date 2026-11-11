import Mathlib

/-!
# Group sequence

A group sequence `𝐆 = (G_i, χ_i)_{i ∈ ℕ}` is a sequence of finite groups `G_i` with homomorphisms
`χ_i : G_i → C_p`, where `C_p = ZMod p` is written additively (interface sheet).

Encoding choices.
* The groups are written additively: `G : ℕ → Type` with `[∀ i, AddGroup (G i)]`. Every concrete
  group sequence of the paper is abelian (the standing data's `ℤ/p^{a_i}`, the geometric sequence
  `ℤ/p^{max(i,1)}`, the trivial sequence), and the corner chapter writes `G_i` additively, but the
  categories chapter never uses commutativity, so `AddGroup` (not `AddCommGroup`) keeps the
  article's "finite groups" without narrowing it.
* Finiteness is `[∀ i, Fintype (G i)]` (sums over `G_i` and the bases `G_i × {1..n}` of the
  asymptotic categories need it); equality is decidable, `[∀ i, DecidableEq (G i)]`, so that
  matrices indexed by these bases have identity matrices.
* `χ i : G i →+ ZMod p`.
* A `C_p`-space `X` (an `AddAction (ZMod p) X`) is a `G_i`-space through `χ_i`:
  `GroupSeq.addAction` is `g +ᵥ x = χ_i(g) +ᵥ x`. It is a definition, not an instance, to avoid
  diamonds when `G_i` is itself `ZMod p`.
* The trivial sequence `𝟏` is `GroupSeq.trivial p`, with every `G_i` the one-point group.
-/

namespace HSP

/-- A *group sequence* `𝐆 = (G_i, χ_i)_{i ∈ ℕ}`: finite groups `G_i` (written additively) with
homomorphisms `χ_i : G_i → C_p = ZMod p`. -/
structure GroupSeq (p : ℕ) where
  /-- The group `G_i` at level `i`. -/
  G : ℕ → Type
  /-- Each `G_i` is a group (written additively). -/
  [addGroup : ∀ i, AddGroup (G i)]
  /-- Each `G_i` is finite. -/
  [fintype : ∀ i, Fintype (G i)]
  /-- Equality in each `G_i` is decidable. -/
  [decEq : ∀ i, DecidableEq (G i)]
  /-- The homomorphism `χ_i : G_i → C_p`. -/
  χ : ∀ i, G i →+ ZMod p

attribute [instance] GroupSeq.addGroup GroupSeq.fintype GroupSeq.decEq

namespace GroupSeq

variable {p : ℕ}

/-- A `C_p`-space is regarded as a `G_i`-space through `χ_i`: `g +ᵥ x = χ_i(g) +ᵥ x`. -/
abbrev addAction (G : GroupSeq p) (i : ℕ) (X : Type*) [AddAction (ZMod p) X] :
    AddAction (G.G i) X :=
  AddAction.compHom X (G.χ i)

/-- The *trivial group sequence* `𝟏`: every `G_i` is the trivial group. -/
def trivial (p : ℕ) : GroupSeq p where
  G _ := Unit
  χ _ := 0

end GroupSeq

end HSP
