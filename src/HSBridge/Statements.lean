import HilbertSmith.Inputs
import HilbertSmith.Statements
import HSFormal.MontgomeryPrime
import HSFormal.Newman.Newman
import HSFormal.Statement
import HSFormal.Universe
import HSFormal.Inputs.GY.NSSIsLie
import HSFormal.Inputs.Lemma7

/-!
# The compared statements are HS_proof's statements

This file checks, by `Iff.rfl`, that the statements of `HilbertSmith.Statements` (written from
OpenAI's preprint, Mathlib only) are HS_proof's statements, and discharges the published input
`HilbertSmith.NewmanInput` of OpenAI's route from HS_proof's proof of Newman's theorem.

* `HSBridge.statements_agree`: `HilbertSmith.Statements.PadicExclusion` in `Type` is
  `HSFormal.PadicExclusion`; `HSBridge.statements_agree_univ` is the same in every universe,
  against `HSFormal.Universe.PadicExclusionIn`.
* `HSBridge.hilbertSmith_statements_agree` and `HSBridge.hilbertSmith_statements_agree_univ`: the
  same for the Hilbert–Smith conjecture; `HSBridge.isLieGroup_iff` for the Lie conclusion.
* `HSBridge.hilbertSmith_of_padicExclusion`: p-adic exclusion implies the Hilbert–Smith
  conjecture, by HS_proof's form of the classical reduction that OpenAI cites for Theorem 1.1.
* `HSBridge.newmanInput`: `HilbertSmith.NewmanInput`, from `HSFormal.Newman.newmanPrimeOrder`
  through `HSFormal.newman_rigidity'`.
-/

open Set Topology

namespace HSBridge

universe u v

/-! ### Statement identity -/

/-- The Lie-group conclusion of both routes is the same predicate. -/
theorem isLieGroup_iff (G : Type) [Group G] [TopologicalSpace G] :
    HilbertSmith.Statements.IsLieGroup G ↔ HSFormal.IsLieGroup G :=
  Iff.rfl

/-- **The p-adic statements agree**: OpenAI's Theorem 1.2, as stated in
`HilbertSmith.Statements.PadicExclusion` for manifolds in `Type`, is HS_proof's
`HSFormal.PadicExclusion`, by definition. -/
theorem statements_agree :
    HilbertSmith.Statements.PadicExclusion.{0} ↔ HSFormal.PadicExclusion :=
  Iff.rfl

/-- `HilbertSmith.Statements.PadicExclusion` in universe `u` is HS_proof's universe-polymorphic
`HSFormal.Universe.PadicExclusionIn`, by definition. -/
theorem statements_agree_univ :
    HilbertSmith.Statements.PadicExclusion.{u} ↔ HSFormal.Universe.PadicExclusionIn.{u} :=
  Iff.rfl

/-- **The Hilbert–Smith statements agree**: OpenAI's Theorem 1.1, as stated in
`HilbertSmith.Statements.HilbertSmith` for manifolds and groups in `Type`, is HS_proof's
`HSFormal.HilbertSmith`, by definition. -/
theorem hilbertSmith_statements_agree :
    HilbertSmith.Statements.HilbertSmith.{0, 0} ↔ HSFormal.HilbertSmith :=
  Iff.rfl

/-- `HilbertSmith.Statements.HilbertSmith` in universes `u, v` is HS_proof's
`HSFormal.Universe.HilbertSmithIn`, by definition. -/
theorem hilbertSmith_statements_agree_univ :
    HilbertSmith.Statements.HilbertSmith.{u, v} ↔ HSFormal.Universe.HilbertSmithIn.{u, v} :=
  Iff.rfl

/-! ### The classical reduction -/

/-- **The classical Hilbert–Smith reduction**: p-adic exclusion implies the Hilbert–Smith
conjecture, for manifolds and groups in `Type`. OpenAI's proof of Theorem 1.1 (`cor:lie`) cites
this reduction ([Pardon 2013, Introduction, p. 1]) and applies Theorem 1.2 to an embedded copy of
`ℤ_[p]`. Here it is HS_proof's `HSFormal.hilbertSmith_of_padicExclusion'`, with its three
published inputs discharged by HS_proof's proofs: Gleason–Yamabe (`HSFormal.GY.nssIsLie`),
[Tao 2011, Lemma 7] (`HSFormal.Lemma7.compactTorsionFreeContainsPadic`) and Newman's theorem
(`HSFormal.Newman.newmanPrimeOrder`). -/
theorem hilbertSmith_of_padicExclusion (h : HilbertSmith.Statements.PadicExclusion.{0}) :
    HilbertSmith.Statements.HilbertSmith.{0, 0} :=
  HSFormal.hilbertSmith_of_padicExclusion' HSFormal.GY.nssIsLie
    HSFormal.Lemma7.compactTorsionFreeContainsPadic HSFormal.Newman.newmanPrimeOrder h

/-! ### Newman's theorem -/

/-- A homeomorphism of a manifold that is the identity on a neighbourhood of every point of the
closure of the interior of its fixed set, as Newman's theorem gives, through a chart. This is the
closedness step of `HSBridge.newmanInput`: for a point `y` of the closure, an `f`-invariant
connected open neighbourhood of `y` inside one chart is carried by the chart into `ℝⁿ`, where
`HSFormal.newman_rigidity'` applies. -/
theorem mem_interior_fixed_of_mem_closure {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (f : M ≃ₜ M) (m : ℕ)
    (hper : ∀ x, f^[m + 1] x = x) {y : M}
    (hy : y ∈ closure (interior {x | f x = x})) : y ∈ interior {x | f x = x} := by
  have : LocallyConnectedSpace M :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin n)) M
  set S : Set M := interior {x | f x = x}
  have hfy : f y = y :=
    closure_minimal interior_subset (isClosed_eq f.continuous continuous_id) hy
  set e := chartAt (EuclideanSpace ℝ (Fin n)) y
  -- `W`: the points whose first `m + 1` iterates lie in the chart; open, `f`-invariant, `∋ y`.
  set W : Set M := ⋂ i ∈ Finset.range (m + 1), f^[i] ⁻¹' e.source
  have hWo : IsOpen W :=
    isOpen_biInter_finset fun i _ => e.open_source.preimage (f.continuous.iterate i)
  have hyW : y ∈ W := by
    simp only [W, mem_iInter, mem_preimage, Function.iterate_fixed hfy]
    exact fun _ _ => mem_chart_source _ y
  have hWe : W ⊆ e.source := fun x hx => by
    simpa using mem_iInter₂.1 hx 0 (Finset.mem_range.2 m.succ_pos)
  have hfW : MapsTo f W W := by
    intro x hx
    simp only [W, mem_iInter, mem_preimage, Finset.mem_range] at hx ⊢
    intro i hi
    rw [← Function.iterate_succ_apply]
    rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.succ_lt_succ hi) with h | h
    · exact hx _ h
    · rw [h, hper]; exact hx 0 m.succ_pos
  -- `D`: the component of `y` in `W`; open, connected and `f`-invariant.
  set D := connectedComponentIn W y
  have hDo : IsOpen D := hWo.connectedComponentIn
  have hDc : IsConnected D := isConnected_connectedComponentIn_iff.2 hyW
  have hyD : y ∈ D := mem_connectedComponentIn hyW
  have hDe : D ⊆ e.source := (connectedComponentIn_subset _ _).trans hWe
  have hfD : MapsTo f D D := by
    intro x hx
    have h := (hDc.isPreconnected.image f f.continuous.continuousOn).subset_connectedComponentIn
      (x := y) ⟨y, hyD, hfy⟩
      ((image_mono (connectedComponentIn_subset W y)).trans (mapsTo_iff_image_subset.1 hfW))
    exact h (mem_image_of_mem f hx)
  -- Transport to the open subset `e '' D` of `ℝⁿ`, conjugating `f` by the chart.
  set h : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) := e ∘ f ∘ e.symm
  have hh : ∀ x ∈ D, h (e x) = e (f x) := fun x hx => by
    simp only [h, Function.comp_apply, e.left_inv (hDe hx)]
  have hhit : ∀ j, ∀ x ∈ D, h^[j] (e x) = e (f^[j] x) := by
    intro j
    induction j with
    | zero => intro x _; rfl
    | succ j ih =>
      intro x hx
      rw [Function.iterate_succ_apply', ih x hx, hh _ (hfD.iterate j hx),
        Function.iterate_succ_apply']
  have hsymm : MapsTo e.symm (e '' D) D := by
    rintro _ ⟨x, hx, rfl⟩; rwa [e.left_inv (hDe hx)]
  obtain ⟨z, hzD, hzS⟩ := mem_closure_iff.1 hy D hDo hyD
  have key := HSFormal.newman_rigidity' HSFormal.Newman.newmanPrimeOrder (n := n)
    (M := EuclideanSpace ℝ (Fin n)) (D := e '' D) (U := e '' (D ∩ S)) (h := h) (m := m)
    (e.isOpen_image_of_subset_source hDo hDe) (hDc.image e (e.continuousOn.mono hDe))
    (e.isOpen_image_of_subset_source (hDo.inter isOpen_interior) (inter_subset_left.trans hDe))
    ⟨e z, mem_image_of_mem e ⟨hzD, hzS⟩, mem_image_of_mem e hzD⟩
    (by rintro _ ⟨x, hx, rfl⟩; rw [hh x hx]; exact mem_image_of_mem e (hfD hx))
    (e.continuousOn.comp (f.continuous.comp_continuousOn
      (e.continuousOn_symm.mono (e.mapsTo.mono_left hDe).image_subset))
      fun _ hx => hDe (hfD (hsymm hx)))
    (by rintro _ ⟨x, hx, rfl⟩; rw [hhit _ x hx, hper])
    (by rintro _ ⟨⟨x, ⟨hxD, hxS⟩, rfl⟩, -⟩; rw [hh x hxD, interior_subset hxS])
  refine interior_maximal (fun x hx => ?_) hDo hyD
  have := key (e x) (mem_image_of_mem e hx)
  rw [hh x hx] at this
  exact e.injOn (hDe (hfD hx)) (hDe hx) this

/-- **Newman's theorem in OpenAI's form** (`HilbertSmith.NewmanInput`, used in the proof of
OpenAI's Proposition 5.1), from HS_proof's proof of Newman's theorem for prime order,
`HSFormal.Newman.newmanPrimeOrder`. The interior of the fixed set is nonempty and open, and it is
closed by `HSBridge.mem_interior_fixed_of_mem_closure`; so it is everything. -/
theorem newmanInput : HilbertSmith.NewmanInput.{u} := by
  intro n M _ _ _ _ f k hk hper U hU hUne hfix
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, (Nat.succ_pred_eq_of_pos hk).symm⟩
  have hS : IsClopen (interior {x | f x = x}) :=
    ⟨isClosed_of_closure_subset fun y hy => mem_interior_fixed_of_mem_closure (n := n) f m hper hy,
      isOpen_interior⟩
  have hSne : (interior {x | f x = x}).Nonempty := hUne.mono (interior_maximal hfix hU)
  intro x
  have hx : x ∈ interior {x | f x = x} := hS.eq_univ hSne ▸ mem_univ x
  exact interior_subset (s := {x | f x = x}) hx

end HSBridge
