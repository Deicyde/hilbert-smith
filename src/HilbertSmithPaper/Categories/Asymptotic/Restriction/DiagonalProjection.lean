import HilbertSmithPaper.Categories.Asymptotic.AsymptoticCategory

/-!
# Diagonal coordinate projection

For a decidable predicate `P i k` on the indices of `M`, `M.trunc P : M → M` is the diagonal
coordinate projection onto the indices with `P`: at level `i` the diagonal matrix with entry `1`
at `(g, k)` if `P i k` and `0` otherwise. It is equivariant with propagation `0`.
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

private theorem diag_mem {H : Type} [AddGroup H] [DecidableEq H] {m : ℕ} (d : Fin m → ℚ) :
    Matrix.diagonal (fun b : H × Fin m => d b.2) ∈ FreeCat.equivariant H m m := by
  intro g h h' k' k
  simp only [Matrix.diagonal_apply, Prod.mk.injEq, add_right_inj]

variable (M : AsymPre G X) (P : ∀ i, Fin (M.n i) → Prop)

/-- The diagonal coordinate projection of `M` onto the indices `k` with `P i k`. -/
noncomputable def trunc [∀ i, DecidablePred (P i)] : M ⟶ M :=
  homMk (fun i => (FreeCat.ofMat
      (Matrix.diagonal fun b : G.G i × Fin (M.n i) => if P i b.2 then 1 else 0)
      (by exact diag_mem (H := G.G i) fun k => if P i k then 1 else 0) :
      M.free i ⟶ M.free i)) (by
    refine (tendsto_congr fun i => ?_).2 tendsto_const_nhds
    refine prop_eq_zero_of' _ _ _ fun a b h => ?_
    by_contra h'
    exact h (Matrix.diagonal_apply_ne _ fun e => h' (by rw [e])))

theorem mat_trunc [∀ i, DecidablePred (P i)] (i : ℕ) :
    FreeCat.mat (coord (M.trunc P) i) = Matrix.diagonal fun b => if P i b.2 then 1 else 0 := rfl

end AsymPre

end HSP
