import Mathlib
import HilbertSmithPaper.Categories.Asymptotic.AsymptoticCategory

/-!
# Concatenation

The concatenation of `⟨M⟩` and `⟨N⟩` is the sequence `(n_i + m_i, x_i ⧺ y_i)` (`Fin.append`), with
the coordinate inclusions and projections of `Free(ℚ[G_i])` at each level; their entries join equal
labels, so they have propagation `0`. They form a binary bicone `HSP.AsymCat.binaryBicone`; its
defining equations are `HSP.AsymCat.binaryBicone_pt`, `_fst`, `_snd`, `_inl` and `_inr`.
-/

open CategoryTheory CategoryTheory.Limits Filter Topology
open scoped NNReal

namespace HSP

variable {p : ℕ}

namespace AsymPre

variable {G : GroupSeq p} {X : Type*} [MetricSpace X] [AddAction (ZMod p) X]

/-- A matrix all of whose nonzero entries join equal labels has propagation `0`. -/
private theorem prop_eq_zero_of {B B' : Type*} [Fintype B] [Fintype B'] (l : B → X)
    (l' : B' → X) (u : Matrix B' B ℚ) (h : ∀ b' b, u b' b ≠ 0 → l' b' = l b) :
    prop l l' u = 0 :=
  le_antisymm (Finset.sup_le fun q hq => by
    rw [h q.1 q.2 (Finset.mem_filter.1 hq).2, nndist_self]) zero_le

/-- The concatenation `(n_i + m_i, x_i ⧺ y_i)`. -/
private def sum (M N : AsymPre G X) : AsymPre G X where
  n i := M.n i + N.n i
  x i := Fin.append (M.x i) (N.x i)

omit [MetricSpace X] in
private theorem label_sum_castAdd (M N : AsymPre G X) (i : ℕ) (g : G.G i) (k : Fin (M.n i)) :
    (M.sum N).label i (g, Fin.castAdd (N.n i) k) = M.label i (g, k) := by
  simp [label, sum]

omit [MetricSpace X] in
private theorem label_sum_natAdd (M N : AsymPre G X) (i : ℕ) (g : G.G i) (k : Fin (N.n i)) :
    (M.sum N).label i (g, Fin.natAdd (M.n i) k) = N.label i (g, k) := by
  simp [label, sum]

private theorem inclMat_ne_zero {H : Type} [DecidableEq H] {m m' : ℕ} {e : Fin m → Fin m'}
    {a : H × Fin m'} {b : H × Fin m} (h : FreeCat.inclMat e a b ≠ 0) : a = (b.1, e b.2) := by
  by_contra h'
  exact h (by simp [FreeCat.inclMat, h'])

/-- The coordinate inclusion `M → M ⊕ N`. -/
private def inl (M N : AsymPre G X) : M ⟶ M.sum N :=
  homMk (fun i => (FreeCat.binaryBicone (M.free i) (N.free i)).inl) (by
    refine (tendsto_congr fun i => ?_).2 tendsto_const_nhds
    refine prop_eq_zero_of _ _ _ fun a b h => ?_
    have h' : FreeCat.inclMat (G := G.G i) (Fin.castAdd (N.n i)) a b ≠ 0 := h
    rw [inclMat_ne_zero h']
    exact label_sum_castAdd M N i b.1 b.2)

/-- The coordinate inclusion `N → M ⊕ N`. -/
private def inr (M N : AsymPre G X) : N ⟶ M.sum N :=
  homMk (fun i => (FreeCat.binaryBicone (M.free i) (N.free i)).inr) (by
    refine (tendsto_congr fun i => ?_).2 tendsto_const_nhds
    refine prop_eq_zero_of _ _ _ fun a b h => ?_
    have h' : FreeCat.inclMat (G := G.G i) (Fin.natAdd (M.n i)) a b ≠ 0 := h
    rw [inclMat_ne_zero h']
    exact label_sum_natAdd M N i b.1 b.2)

/-- The coordinate projection `M ⊕ N → M`. -/
private def fst (M N : AsymPre G X) : M.sum N ⟶ M :=
  homMk (fun i => (FreeCat.binaryBicone (M.free i) (N.free i)).fst) (by
    refine (tendsto_congr fun i => ?_).2 tendsto_const_nhds
    refine prop_eq_zero_of _ _ _ fun b a h => ?_
    have h' : FreeCat.inclMat (G := G.G i) (Fin.castAdd (N.n i)) a b ≠ 0 := h
    rw [inclMat_ne_zero h']
    exact (label_sum_castAdd M N i b.1 b.2).symm)

/-- The coordinate projection `M ⊕ N → N`. -/
private def snd (M N : AsymPre G X) : M.sum N ⟶ N :=
  homMk (fun i => (FreeCat.binaryBicone (M.free i) (N.free i)).snd) (by
    refine (tendsto_congr fun i => ?_).2 tendsto_const_nhds
    refine prop_eq_zero_of _ _ _ fun b a h => ?_
    have h' : FreeCat.inclMat (G := G.G i) (Fin.natAdd (M.n i)) a b ≠ 0 := h
    rw [inclMat_ne_zero h']
    exact (label_sum_natAdd M N i b.1 b.2).symm)

private theorem inl_fst (M N : AsymPre G X) : inl M N ≫ fst M N = 𝟙 M :=
  hom_ext fun i => (FreeCat.binaryBicone (M.free i) (N.free i)).inl_fst
private theorem inl_snd (M N : AsymPre G X) : inl M N ≫ snd M N = 0 :=
  hom_ext fun i => (FreeCat.binaryBicone (M.free i) (N.free i)).inl_snd
private theorem inr_fst (M N : AsymPre G X) : inr M N ≫ fst M N = 0 :=
  hom_ext fun i => (FreeCat.binaryBicone (M.free i) (N.free i)).inr_fst
private theorem inr_snd (M N : AsymPre G X) : inr M N ≫ snd M N = 𝟙 N :=
  hom_ext fun i => (FreeCat.binaryBicone (M.free i) (N.free i)).inr_snd
end AsymPre

namespace AsymCat

variable {G : GroupSeq p} {X : Type*} [MetricSpace X] [AddAction (ZMod p) X]

/-- **The concatenation** of `⟨M⟩` and `⟨N⟩`, with the coordinate inclusions and projections. -/
def binaryBicone (P Q : AsymCat G X) : BinaryBicone P Q where
  pt := ⟨P.as.sum Q.as⟩
  fst := mkHom (AsymPre.fst P.as Q.as)
  snd := mkHom (AsymPre.snd P.as Q.as)
  inl := mkHom (AsymPre.inl P.as Q.as)
  inr := mkHom (AsymPre.inr P.as Q.as)
  inl_fst := by rw [← Functor.map_comp, AsymPre.inl_fst, CategoryTheory.Functor.map_id]; rfl
  inl_snd := by rw [← Functor.map_comp, AsymPre.inl_snd, CategoryTheory.Functor.map_zero]
  inr_fst := by rw [← Functor.map_comp, AsymPre.inr_fst, CategoryTheory.Functor.map_zero]
  inr_snd := by rw [← Functor.map_comp, AsymPre.inr_snd, CategoryTheory.Functor.map_id]; rfl

@[simp] theorem binaryBicone_pt (P Q : AsymCat G X) :
    (binaryBicone P Q).pt =
      ⟨⟨fun i => P.as.n i + Q.as.n i, fun i => Fin.append (P.as.x i) (Q.as.x i)⟩⟩ :=
  rfl

/-- The defining equation of the first projection: its matrices are the coordinate projections. -/
theorem binaryBicone_fst (P Q : AsymCat G X) :
    ∃ u, (binaryBicone P Q).fst = mkHom u ∧
      ∀ i, AsymPre.coord u i = (FreeCat.binaryBicone (P.as.free i) (Q.as.free i)).fst :=
  ⟨_, rfl, fun _ => rfl⟩

/-- The defining equation of the second projection. -/
theorem binaryBicone_snd (P Q : AsymCat G X) :
    ∃ u, (binaryBicone P Q).snd = mkHom u ∧
      ∀ i, AsymPre.coord u i = (FreeCat.binaryBicone (P.as.free i) (Q.as.free i)).snd :=
  ⟨_, rfl, fun _ => rfl⟩

/-- The defining equation of the first inclusion. -/
theorem binaryBicone_inl (P Q : AsymCat G X) :
    ∃ u, (binaryBicone P Q).inl = mkHom u ∧
      ∀ i, AsymPre.coord u i = (FreeCat.binaryBicone (P.as.free i) (Q.as.free i)).inl :=
  ⟨_, rfl, fun _ => rfl⟩

/-- The defining equation of the second inclusion. -/
theorem binaryBicone_inr (P Q : AsymCat G X) :
    ∃ u, (binaryBicone P Q).inr = mkHom u ∧
      ∀ i, AsymPre.coord u i = (FreeCat.binaryBicone (P.as.free i) (Q.as.free i)).inr :=
  ⟨_, rfl, fun _ => rfl⟩

end AsymCat

end HSP
