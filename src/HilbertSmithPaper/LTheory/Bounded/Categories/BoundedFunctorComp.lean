import HilbertSmithPaper.LTheory.Bounded.Categories.BoundedFunctorIter
import HilbertSmithPaper.LTheory.Base.Categories.DualityFunctors.CompositeDualityFunctor

/-!
# Bounded extension is functorial

Let `(F, ξ) : A → A'` and `(G, ζ) : A' → A''` be duality functors and `j ≥ 0`. Then
`C_{ℤ^j}(id_A) = id_{C_{ℤ^j}(A)}` and `C_{ℤ^j}((G, ζ) ∘ (F, ξ)) = C_{ℤ^j}(G, ζ) ∘ C_{ℤ^j}(F, ξ)`
as duality functors, duality data included.

For `j = 1` both sides agree on objects and morphisms entry by entry, and the duality data are the
same diagonal matrices: the identity diagonal, and `(ζ_{F M_n} G(ξ_{M_n}))_n`. The general case
follows by induction on `j`, since `C_{ℤ^{j+1}} = C_ℤ C_{ℤ^j}`.
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace HSP

open DualCat

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace Bounded

variable {A : Type u₁} [Category.{v₁} A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
  [DualCat A]
  {A' : Type u₂} [Category.{v₂} A'] [Preadditive A'] [Linear ℚ A'] [HasFiniteBiproducts A']
  [DualCat A']
  {A'' : Type u₃} [Category.{v₃} A''] [Preadditive A''] [Linear ℚ A''] [HasFiniteBiproducts A'']
  [DualCat A'']

/-- Duality functors with the same underlying functor and the same duality isomorphisms are
equal. -/
private lemma dualFunctor_ext {F G : DualFunctor A A'} (h : F.toFunctor = G.toFunctor)
    (hξ : ∀ M, HEq (F.ξ M) (G.ξ M)) : F = G := by
  cases F
  cases G
  cases h
  congr
  funext M
  exact eq_of_heq (hξ M)

omit [HasFiniteBiproducts A] [DualCat A] [HasFiniteBiproducts A'] [DualCat A'] in
/-- `C_ℤ G` of a diagonal matrix is the diagonal matrix of the images. -/
private lemma mapFunctor_diag (G : A ⥤ A') [G.Additive] {M N : Bounded A}
    (d : ∀ n, M.X n ⟶ N.X n) :
    (mapFunctor G).map (diag d) = diag (M := (mapFunctor G).obj M) (N := (mapFunctor G).obj N)
      fun n => G.map (d n) :=
  hom_ext fun a b => by
    show G.map (diagF d a b) =
      diagF (M := (mapFunctor G).obj M) (N := (mapFunctor G).obj N) (fun n => G.map (d n)) a b
    by_cases h : a = b
    · subst h
      erw [diagF_self, diagF_self]
    · erw [diagF_ne _ h, diagF_ne _ h, G.map_zero]
      rfl

/-- `C_ℤ(id_A) = id_{C_ℤ(A)}`. -/
private lemma map_id : map (DualFunctor.id A) = DualFunctor.id (Bounded A) :=
  dualFunctor_ext rfl fun M => heq_of_eq (Iso.ext (by
    exact (id_eq_diag (dual M)).symm))

/-- `C_ℤ(G ∘ F) = C_ℤ G ∘ C_ℤ F`. -/
private lemma map_comp (F : DualFunctor A A') (G : DualFunctor A' A'') :
    map (F.comp G) = (map F).comp (map G) :=
  dualFunctor_ext rfl fun M => heq_of_eq (Iso.ext (by
    change diag (M := ⟨fun n => G.toFunctor.obj (F.toFunctor.obj (dual (M.X n)))⟩)
        (N := ⟨fun n => dual (G.toFunctor.obj (F.toFunctor.obj (M.X n)))⟩)
        (fun n => G.toFunctor.map (F.ξ (M.X n)).hom ≫ (G.ξ (F.toFunctor.obj (M.X n))).hom) =
      (mapFunctor G.toFunctor).map (diag (M := ⟨fun n => F.toFunctor.obj (dual (M.X n))⟩)
          (N := ⟨fun n => dual (F.toFunctor.obj (M.X n))⟩) fun n => (F.ξ (M.X n)).hom) ≫
        diag (M := ⟨fun n => G.toFunctor.obj (dual (F.toFunctor.obj (M.X n)))⟩)
          (N := ⟨fun n => dual (G.toFunctor.obj (F.toFunctor.obj (M.X n)))⟩)
          fun n => (G.ξ (F.toFunctor.obj (M.X n))).hom
    erw [mapFunctor_diag, diag_comp_diag]
    rfl))

private lemma mapIter_id : ∀ j : ℕ, mapIter (DualFunctor.id A) j = DualFunctor.id _
  | 0 => rfl
  | j + 1 => by
    change map (mapIter (DualFunctor.id A) j) = _
    rw [mapIter_id j]
    exact map_id

private lemma mapIter_comp (F : DualFunctor A A') (G : DualFunctor A' A'') :
    ∀ j : ℕ, mapIter (F.comp G) j = (mapIter F j).comp (mapIter G j)
  | 0 => rfl
  | j + 1 => by
    change map (mapIter (F.comp G) j) = (map (mapIter F j)).comp (map (mapIter G j))
    rw [mapIter_comp F G j]
    exact map_comp _ _

/-- **Bounded extension is functorial.** `C_{ℤ^j}(id_A) = id` and
`C_{ℤ^j}(G ∘ F) = C_{ℤ^j} G ∘ C_{ℤ^j} F` as duality functors. -/
theorem mapIter_id_comp (F : DualFunctor A A') (G : DualFunctor A' A'') (j : ℕ) :
    mapIter (DualFunctor.id A) j = DualFunctor.id _ ∧
      mapIter (F.comp G) j = (mapIter F j).comp (mapIter G j) :=
  ⟨mapIter_id j, mapIter_comp F G j⟩

end Bounded

end HSP

end
