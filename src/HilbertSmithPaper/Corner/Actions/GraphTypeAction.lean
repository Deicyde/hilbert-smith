import Mathlib
import HilbertSmithPaper.Corner.StandingData
import HilbertSmithPaper.Corner.RoundSphere
import HilbertSmithPaper.Corner.Exterior
import HilbertSmithPaper.Corner.Actions.GraphType
import HilbertSmithPaper.Corner.Actions.ExteriorWitness
import HilbertSmithPaper.Categories.Supports.ExteriorQuotient
import HilbertSmithPaper.LTheory.Base.Pairs.SymmetricPoincareComplex
import HilbertSmithPaper.LTheory.Base.Complexes.DualComplex

/-!
# Graph-type homotopy action

Take the standing data, `X = T × S^n` and `Z = T × Z₀`. Let `(C, φ)` be a strict `N`-dimensional
symmetric Poincaré complex in `ℬ_{𝟏,Z}(T × S^n)` (`N = n + 4`), with fixed representative
matrices `d_i` and `φ_i` on its based modules. A *graph-type homotopy action* of `𝐆` on `(C, φ)` is
a null sequence `(δ_i)` and, for every `i` and `g, h ∈ G_i`, matrices `A_g` (degree `0`,
`A_0 = 1`), `B_{g,h}` (degree `+1`) and `V_g : C^{N-*} → C` (degree `+1`) of graph types
`χ_i(g)`, `χ_i(g+h)`, `χ_i(g)` with bound `δ_i`, such that `dA_g - A_g d`,
`A_g A_h - A_{g+h} - dB_{g,h} - B_{g,h} d` and `A_g φ - φ A_{-g}^* - dV_g - V_g d` are exterior
witnesses of types `χ_i(g)`, `χ_i(g+h)`, `χ_i(g)` with bound `δ_i`.

## Encoding

* `ℬ_{𝟏,Z}(T × S^n)` is `HSP.Ext (GroupSeq.trivial S.p) (S.T × RoundSphere S.n) Z` with
  `Z = (Set.univ : Set S.T) ×ˢ exterior S.n S.R`; its objects are those of `𝒜_𝟏(T × S^n)`, so the
  chain objects are based modules with identity idempotents. The based module of `C_r` at level
  `i` has basis `𝟏_i × Fin n_i` (`𝟏_i` the one-point group) with the labels `label i` of the
  underlying object `(C.C.X r).as.as`.
* The representatives are parameters: `d a b` is a morphism of `𝒜_𝟏` whose class is `C.d a b`
  (`d` is indexed by source and target, so that every composite below is well typed), and `φ x`
  one whose class is `φ x` (the dual of an object of `ℬ_{𝟏,Z}` is the same object, so `φ x` is a
  morphism `C_s → C_r` of `𝒜_𝟏`); their level-`i` matrices are `FreeCat.mat (AsymPre.coord _ i)`.
* `A i g r : C_r → C_r`, `B i g h r : C_r → C_{r+1}` and `V i g r : (C^{N-*})_r = C_{N-r}^* → C_{r+1}`
  are matrices on the level-`i` bases. The dual of a matrix is its transpose, and the differential
  of `C^{N-*}` from degree `r+1` to `r` is `(-1)^{r+1} d^*`. The three relations are stated on
  `C_{r+1}` (respectively `(C^{N-*})_{r+1}`) for every `r ∈ ℤ`, which covers every degree.
* `G_i = ZMod (p^{a_i})` is written additively, and `χ_i(g)` is `S.groupSeq.χ i g`. The single
  sequence `δ` comes before the matrices, so one bound serves every `g, h`.
-/

open CategoryTheory Filter Topology

namespace HSP.Corner

/-- A *graph-type homotopy action* of `𝐆` on a strict `N`-dimensional symmetric Poincaré complex
`(C, φ)` in `ℬ_{𝟏,Z}(T × S^n)`, with fixed representatives `d` of its differentials and `φ` of
its structure: a null sequence `δ` and matrices `A_g` (`A_0 = 1`), `B_{g,h}`, `V_g` of graph types
`χ_i(g)`, `χ_i(g+h)`, `χ_i(g)` with bound `δ_i`, such that `dA_g - A_g d`,
`A_g A_h - A_{g+h} - dB_{g,h} - B_{g,h} d` and `A_g φ - φ A_{-g}^* - dV_g - V_g d` are exterior
witnesses of types `χ_i(g)`, `χ_i(g+h)`, `χ_i(g)` with bound `δ_i`. -/
structure GraphAction (S : StandingData)
    (C : SymPoincare (Ext (GroupSeq.trivial S.p) (S.T × RoundSphere S.n)
      ((Set.univ : Set S.T) ×ˢ exterior S.n S.R)) (S.N : ℤ))
    (d : ∀ a b : ℤ, (C.C.X a).as.as ⟶ (C.C.X b).as.as)
    (hd : ∀ a b, (FiltQuot.functor _).map (AsymCat.mkHom (d a b)) = C.C.d a b)
    (φ : ∀ x : {x : ℤ × ℤ // x.1 + x.2 = (S.N : ℤ)},
      (C.C.X x.1.2).as.as ⟶ (C.C.X x.1.1).as.as)
    (hφ : ∀ x, (FiltQuot.functor _).map (AsymCat.mkHom (φ x)) = C.φ x) where
  /-- The bound sequence `δ_i`. -/
  δ : ℕ → ℝ
  /-- `δ_i → 0`. -/
  tendsto_δ : Tendsto δ atTop (𝓝 0)
  /-- `A_g : C_r → C_r` at level `i`. -/
  A : ∀ (i : ℕ), S.groupSeq.G i → ∀ r : ℤ,
    Matrix ((GroupSeq.trivial S.p).G i × Fin ((C.C.X r).as.as.free i).n)
      ((GroupSeq.trivial S.p).G i × Fin ((C.C.X r).as.as.free i).n) ℚ
  /-- `B_{g,h} : C_r → C_{r+1}` at level `i`. -/
  B : ∀ (i : ℕ), S.groupSeq.G i → S.groupSeq.G i → ∀ r : ℤ,
    Matrix ((GroupSeq.trivial S.p).G i × Fin ((C.C.X (r + 1)).as.as.free i).n)
      ((GroupSeq.trivial S.p).G i × Fin ((C.C.X r).as.as.free i).n) ℚ
  /-- `V_g : (C^{N-*})_r = C_{N-r}^* → C_{r+1}` at level `i`. -/
  V : ∀ (i : ℕ), S.groupSeq.G i → ∀ r : ℤ,
    Matrix ((GroupSeq.trivial S.p).G i × Fin ((C.C.X (r + 1)).as.as.free i).n)
      ((GroupSeq.trivial S.p).G i × Fin ((C.C.X ((S.N : ℤ) - r)).as.as.free i).n) ℚ
  /-- `A_0 = 1`. -/
  A_zero : ∀ i r, A i 0 r = 1
  /-- `A_g` has graph type `χ_i(g)`. -/
  A_graph : ∀ i g r, IsGraphType ((C.C.X r).as.as.label i) ((C.C.X r).as.as.label i)
    (S.groupSeq.χ i g) (δ i) (A i g r)
  /-- `B_{g,h}` has graph type `χ_i(g+h)`. -/
  B_graph : ∀ i g h r, IsGraphType ((C.C.X r).as.as.label i) ((C.C.X (r + 1)).as.as.label i)
    (S.groupSeq.χ i (g + h)) (δ i) (B i g h r)
  /-- `V_g` has graph type `χ_i(g)`. -/
  V_graph : ∀ i g r, IsGraphType ((C.C.X ((S.N : ℤ) - r)).as.as.label i)
    ((C.C.X (r + 1)).as.as.label i) (S.groupSeq.χ i g) (δ i) (V i g r)
  /-- `dA_g - A_g d` (on `C_{r+1}`) is an exterior witness of type `χ_i(g)`. -/
  chain_witness : ∀ i g r, IsExteriorWitness ((Set.univ : Set S.T) ×ˢ exterior S.n S.R)
    ((C.C.X (r + 1)).as.as.label i) ((C.C.X r).as.as.label i) (S.groupSeq.χ i g) (δ i)
    (FreeCat.mat (AsymPre.coord (d (r + 1) r) i) * A i g (r + 1) -
      A i g r * FreeCat.mat (AsymPre.coord (d (r + 1) r) i))
  /-- `A_g A_h - A_{g+h} - dB_{g,h} - B_{g,h} d` (on `C_{r+1}`) is an exterior witness of type
  `χ_i(g+h)`. -/
  mul_witness : ∀ i g h r, IsExteriorWitness ((Set.univ : Set S.T) ×ˢ exterior S.n S.R)
    ((C.C.X (r + 1)).as.as.label i) ((C.C.X (r + 1)).as.as.label i) (S.groupSeq.χ i (g + h))
    (δ i)
    (A i g (r + 1) * A i h (r + 1) - A i (g + h) (r + 1) -
      FreeCat.mat (AsymPre.coord (d (r + 1 + 1) (r + 1)) i) * B i g h (r + 1) -
      B i g h r * FreeCat.mat (AsymPre.coord (d (r + 1) r) i))
  /-- `A_g φ - φ A_{-g}^* - dV_g - V_g d` (on `(C^{N-*})_{r+1}`) is an exterior witness of type
  `χ_i(g)`. -/
  dual_witness : ∀ i g r, IsExteriorWitness ((Set.univ : Set S.T) ×ˢ exterior S.n S.R)
    ((C.C.X ((S.N : ℤ) - (r + 1))).as.as.label i) ((C.C.X (r + 1)).as.as.label i)
    (S.groupSeq.χ i g) (δ i)
    (A i g (r + 1) * FreeCat.mat (AsymPre.coord (φ ⟨(r + 1, (S.N : ℤ) - (r + 1)), by ring⟩) i) -
      FreeCat.mat (AsymPre.coord (φ ⟨(r + 1, (S.N : ℤ) - (r + 1)), by ring⟩) i) *
        (A i (-g) ((S.N : ℤ) - (r + 1))).transpose -
      FreeCat.mat (AsymPre.coord (d (r + 1 + 1) (r + 1)) i) * V i g (r + 1) -
      V i g r * (((r + 1).negOnePow : ℤ) •
        (FreeCat.mat (AsymPre.coord (d ((S.N : ℤ) - r) ((S.N : ℤ) - (r + 1))) i)).transpose))

end HSP.Corner

/-! ### Non-vacuity witness (private)

The toy standing data of the graph-type article (`T = ZMod 2` with the discrete metric and the
translation action, `G_i = ℤ/2^{max(i,1)}`), the zero complex on the empty object, the zero
representatives, `A_g = 1` and `B = V = 0`. -/

section Witness
open HSP HSP.Corner CategoryTheory CategoryTheory.Limits

/-- Toy control space: `ZMod 2` with the discrete metric. -/
private def Tw : Type := ZMod 2

private instance : DecidableEq Tw := inferInstanceAs (DecidableEq (ZMod 2))
private instance : Fintype Tw := inferInstanceAs (Fintype (ZMod 2))
private instance : AddAction (ZMod 2) Tw := inferInstanceAs (AddAction (ZMod 2) (ZMod 2))

private instance : MetricSpace Tw where
  dist x y := if x = y then 0 else 1
  dist_self x := by simp
  dist_comm x y := by by_cases h : x = y <;> simp [h, eq_comm]
  dist_triangle x y z := by
    by_cases h1 : x = y <;> by_cases h2 : y = z <;> by_cases h3 : x = z <;> simp_all
  eq_of_dist_eq_zero {x y} h := by by_contra h'; simp [h'] at h

private instance : IsIsometricVAdd (ZMod 2) Tw :=
  ⟨fun c => Isometry.of_dist_eq fun x y => by
    show (if c + (show ZMod 2 from x) = c + (show ZMod 2 from y) then (0:ℝ) else 1) = if (show ZMod 2 from x) = (show ZMod 2 from y) then 0 else 1
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd (add_left_cancel h1) h2
    · exact absurd (by rw [h2]) h1
    · rfl⟩

private def standingWitness : StandingData where
  p := 2
  hp := ⟨Nat.prime_two⟩
  a i := max i 1
  one_le_a i := le_max_right _ _
  χ i := (ZMod.castHom (dvd_pow_self 2 (by omega : max i 1 ≠ 0)) (ZMod 2)).toAddMonoidHom
  χ_surjective i := ZMod.ringHom_surjective _
  T := Tw
  nonempty := ⟨(0 : ZMod 2)⟩
  free c t h := by
    have h' : c + (show ZMod 2 from t) = 0 + (show ZMod 2 from t) := by rw [zero_add]; exact h
    exact add_right_cancel h'
  n := 1
  one_le_n := le_rfl
  R := 2
  s := 1
  R_pos := by norm_num
  s_pos := by norm_num
  s_lt := by norm_num


private abbrev Bw : Type _ := Ext (GroupSeq.trivial standingWitness.p)
  (standingWitness.T × RoundSphere standingWitness.n)
  ((Set.univ : Set standingWitness.T) ×ˢ exterior standingWitness.n standingWitness.R)

/-- The empty object of `ℬ_{𝟏,Z}`. -/
private def Ow : Bw := ⟨⟨AsymPre.zero⟩⟩

private theorem isZero_Ow : IsZero Ow :=
  (FiltQuot.functor _).map_isZero AsymCat.isZero_zero

/-- The zero complex on the empty object. -/
private noncomputable def zeroCxW : ChainComplex Bw ℤ where
  X _ := Ow
  d _ _ := 0

/-- The zero complex with the zero structure, as a strict `N`-dimensional symmetric Poincaré
complex. -/
private noncomputable def zeroPoincareW : SymPoincare Bw (standingWitness.N : ℤ) where
  C := zeroCxW
  φ := 0
  bounded _ _ := isZero_Ow
  cycle := map_zero _
  symmetric := map_zero _
  poincare := by
    refine ⟨HomotopyEquiv.ofIso (HomologicalComplex.Hom.isoOfComponents
      (fun _ => IsZero.iso isZero_Ow isZero_Ow) (fun _ _ _ => IsZero.eq_of_src isZero_Ow _ _)), ?_⟩
    ext r
    exact IsZero.eq_of_src isZero_Ow _ _

private theorem graphActionWitness :
    Nonempty (GraphAction standingWitness zeroPoincareW (fun _ _ => 0)
      (fun _ _ => by simp only [AsymCat.mkHom, Functor.map_zero]; rfl) (fun _ => 0)
      (fun _ => by simp only [AsymCat.mkHom, Functor.map_zero]; rfl)) :=
  ⟨{ δ := fun _ => 0
     tendsto_δ := tendsto_const_nhds
     A := fun _ _ _ => 1
     B := fun _ _ _ _ => 0
     V := fun _ _ _ => 0
     A_zero := fun _ _ => rfl
     A_graph := fun _ _ _ b' _ _ => b'.2.elim0
     B_graph := fun _ _ _ _ b' _ _ => b'.2.elim0
     V_graph := fun _ _ _ b' _ _ => b'.2.elim0
     chain_witness := fun _ _ _ => ⟨0, Fin.elim0, 0, 0, Matrix.ext fun b' _ => b'.2.elim0,
       fun w => w.elim0, fun b' _ _ => b'.elim0, fun b' _ _ => b'.2.elim0⟩
     mul_witness := fun _ _ _ _ => ⟨0, Fin.elim0, 0, 0, Matrix.ext fun b' _ => b'.2.elim0,
       fun w => w.elim0, fun b' _ _ => b'.elim0, fun b' _ _ => b'.2.elim0⟩
     dual_witness := fun _ _ _ => ⟨0, Fin.elim0, 0, 0, Matrix.ext fun b' _ => b'.2.elim0,
       fun w => w.elim0, fun b' _ _ => b'.elim0, fun b' _ _ => b'.2.elim0⟩ }⟩

end Witness
