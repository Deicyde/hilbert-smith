import HilbertSmithPaper.Categories.Asymptotic.Restriction.RestrictionSubBasis

/-!
# Coordinate inclusion of a restriction

The coordinate inclusion `M_P → M` of a restriction: at level `i` the matrix `inclMat e` of the
enumeration `e` of the indices with `P`. Its nonzero entries join equal labels, so its propagation
is `0`.
-/

open CategoryTheory CategoryTheory.Limits Filter Topology

namespace HSP

variable {p : ℕ} {G : GroupSeq p} {X : Type*} [MetricSpace X] [AddAction (ZMod p) X]

namespace AsymPre

/-- A matrix all of whose nonzero entries join equal labels has propagation `0`. -/
private theorem prop_eq_zero_of' {B B' : Type*} [Fintype B] [Fintype B'] (l : B → X)
    (l' : B' → X) (u : Matrix B' B ℚ) (h : ∀ b' b, u b' b ≠ 0 → l' b' = l b) :
    prop l l' u = 0 :=
  le_antisymm (Finset.sup_le fun q hq => by
    rw [h q.1 q.2 (Finset.mem_filter.1 hq).2, nndist_self]) zero_le

private theorem inclMat_mem' {H : Type} [AddGroup H] [DecidableEq H] {m m' : ℕ}
    (e : Fin m → Fin m') : FreeCat.inclMat (G := H) e ∈ FreeCat.equivariant H m' m := by
  intro g h h' k' k
  simp [FreeCat.inclMat]

private theorem inclMat_ne_zero' {H : Type} [DecidableEq H] {m m' : ℕ} {e : Fin m → Fin m'}
    {a : H × Fin m'} {b : H × Fin m} (h : FreeCat.inclMat e a b ≠ 0) : a = (b.1, e b.2) := by
  by_contra h'
  exact h (by simp [FreeCat.inclMat, h'])

variable (M : AsymPre G X) (P : ∀ i, Fin (M.n i) → Prop)

/-- The coordinate inclusion `M_P → M` (propagation `0`). -/
noncomputable def restrictInc : M.restrict P ⟶ M :=
  homMk (fun i => (FreeCat.ofMat (FreeCat.inclMat (M.restrictEmb P i))
      (inclMat_mem' _) : (M.restrict P).free i ⟶ M.free i)) (by
    refine (tendsto_congr fun i => ?_).2 tendsto_const_nhds
    refine prop_eq_zero_of' _ _ _ fun a b h => ?_
    rw [inclMat_ne_zero' h]
    rfl)

private theorem mat_restrictInc (i : ℕ) :
    FreeCat.mat (coord (M.restrictInc P) i) = FreeCat.inclMat (M.restrictEmb P i) := rfl

end AsymPre

end HSP
