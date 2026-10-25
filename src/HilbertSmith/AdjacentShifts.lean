import Mathlib

namespace HilbertSmith

open CategoryTheory CategoryTheory.Limits ZeroObject CategoryTheory.Pretriangulated

universe u v

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasShift C ℤ]
  [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- A full replete triangulated subcategory of a pretriangulated category,
given by a predicate on objects. Fullness is automatic; the fields record
repleteness (closure under isomorphism), stability under shift and cones,
and density (every object is a summand of a member). -/
structure TriangulatedSubcategory (C : Type u) [Category.{v} C] [Preadditive C]
    [HasShift C ℤ] [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] where
  /-- The membership predicate. -/
  P : C → Prop
  /-- Closure under isomorphism. -/
  replete : ∀ {X Y : C}, P X → (X ≅ Y) → P Y
  /-- Stability under shift. -/
  shift_mem : ∀ (X : C) (n : ℤ), P X → P (X⟦n⟧)
  /-- Stability under cones: the cone of a map between members is a member. -/
  cone_mem : ∀ {X Y : C}, P X → P Y → ∀ (f : X ⟶ Y) (Z : C) (g : Y ⟶ Z)
    (h : Z ⟶ X⟦(1 : ℤ)⟧), Triangle.mk f g h ∈ distTriang C → P Z
  /-- Density: every object is a summand of a member. -/
  dense : ∀ Y : C, ∃ X, P X ∧ ∃ Z, Nonempty (X ≅ Y ⊞ Z)

omit [Preadditive C] [HasShift C ℤ] [HasZeroObject C]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] in
/-- If both composites are isomorphisms, the first map is an isomorphism. -/
lemma isIso_of_isIso_comp_both {X Y : C} (a : X ⟶ Y) (b : Y ⟶ X)
    (h₁ : IsIso (a ≫ b)) (h₂ : IsIso (b ≫ a)) : IsIso a := by
  obtain ⟨u, hu₁, -⟩ := h₁.out
  obtain ⟨v, -, hv₂⟩ := h₂.out
  have har : a ≫ (b ≫ u) = 𝟙 X := by
    rw [← Category.assoc]
    exact hu₁
  have hla : (v ≫ b) ≫ a = 𝟙 Y := by
    rw [Category.assoc]
    exact hv₂
  refine ⟨b ≫ u, har, ?_⟩
  calc (b ≫ u) ≫ a = ((v ≫ b) ≫ a) ≫ ((b ≫ u) ≫ a) := by
          rw [hla, Category.id_comp]
    _ = (v ≫ b) ≫ (a ≫ (b ≫ u)) ≫ a := by
          simp only [Category.assoc]
    _ = 𝟙 Y := by
          rw [har, Category.id_comp]
          exact hla

/-- In a dense subcategory, `Y ⊞ Y⟦1⟧` is always a member: it is the cone
of `0 ⊞⊞ 𝟙` on a dense cover, identified via the split-triangle identity. -/
theorem TriangulatedSubcategory.mem_add_shift_one (S : TriangulatedSubcategory C)
    (Y : C) : S.P (Y ⊞ Y⟦(1 : ℤ)⟧) := by
  obtain ⟨c, hc, Z, ⟨e⟩⟩ := S.dense Y
  have hYZ : S.P (Y ⊞ Z) := S.replete hc e
  -- The triangle on `0 : Y → Y`; its rotation splits.
  obtain ⟨C₀, g₀, h₀, hT₀⟩ :=
    Pretriangulated.distinguished_cocone_triangle (0 : Y ⟶ Y)
  have hT₀r := rot_of_distTriang _ hT₀
  have hmor : (Triangle.mk (0 : Y ⟶ Y) g₀ h₀).rotate.mor₃ = 0 := by
    show -(0 : Y ⟶ Y)⟦(1 : ℤ)⟧' = 0
    simp
  obtain ⟨e₀, -, -⟩ := exists_iso_binaryBiproduct_of_distTriang _ hT₀r hmor
  have e₀' : C₀ ≅ Y ⊞ Y⟦(1 : ℤ)⟧ := e₀
  -- The triangle on `0 ⊞⊞ 𝟙`, whose cone lies in the subcategory.
  obtain ⟨W, g, h, hT⟩ := Pretriangulated.distinguished_cocone_triangle
    (biprod.map (0 : Y ⟶ Y) (𝟙 Z))
  have hW : S.P W := S.cone_mem hYZ hYZ _ W g h hT
  -- The contractible triangle on `𝟙 Z`.
  have hT₁ : Triangle.mk (𝟙 Z) (0 : Z ⟶ 0) (0 : (0 : C) ⟶ Z⟦(1 : ℤ)⟧) ∈
      distTriang C := by
    rw [Triangle.distinguished_iff_of_isZero₃ _ (isZero_zero C)]
    show IsIso (𝟙 Z)
    exact ⟨𝟙 _, Category.id_comp _, Category.id_comp _⟩
  -- Commutativity for the four comparison maps.
  have hcommφ : (0 : Y ⟶ Y) ≫ (biprod.inl : Y ⟶ Y ⊞ Z) =
      (biprod.inl : Y ⟶ Y ⊞ Z) ≫ biprod.map (0 : Y ⟶ Y) (𝟙 Z) := by simp
  have hcommψ : biprod.map (0 : Y ⟶ Y) (𝟙 Z) ≫ (biprod.fst : Y ⊞ Z ⟶ Y) =
      (biprod.fst : Y ⊞ Z ⟶ Y) ≫ (0 : Y ⟶ Y) := by simp
  have hcommχ : biprod.map (0 : Y ⟶ Y) (𝟙 Z) ≫ (biprod.snd : Y ⊞ Z ⟶ Z) =
      (biprod.snd : Y ⊞ Z ⟶ Z) ≫ 𝟙 Z := by simp
  have hcommθ : (𝟙 Z) ≫ (biprod.inr : Z ⟶ Y ⊞ Z) =
      (biprod.inr : Z ⟶ Y ⊞ Z) ≫ biprod.map (0 : Y ⟶ Y) (𝟙 Z) := by simp
  obtain ⟨φ₃, hφ₂', hφ₃'⟩ :=
    Pretriangulated.complete_distinguished_triangle_morphism
      _ _ hT₀ hT (biprod.inl : Y ⟶ Y ⊞ Z) (biprod.inl : Y ⟶ Y ⊞ Z) hcommφ
  obtain ⟨ψ₃, hψ₂', hψ₃'⟩ :=
    Pretriangulated.complete_distinguished_triangle_morphism
      _ _ hT hT₀ (biprod.fst : Y ⊞ Z ⟶ Y) (biprod.fst : Y ⊞ Z ⟶ Y) hcommψ
  obtain ⟨χ₃, hχ₂', hχ₃'⟩ :=
    Pretriangulated.complete_distinguished_triangle_morphism
      _ _ hT hT₁ (biprod.snd : Y ⊞ Z ⟶ Z) (biprod.snd : Y ⊞ Z ⟶ Z) hcommχ
  obtain ⟨θ₃, hθ₂', hθ₃'⟩ :=
    Pretriangulated.complete_distinguished_triangle_morphism
      _ _ hT₁ hT (biprod.inr : Z ⟶ Y ⊞ Z) (biprod.inr : Z ⟶ Y ⊞ Z) hcommθ
  have hφ₂ : g₀ ≫ φ₃ = (biprod.inl : Y ⟶ Y ⊞ Z) ≫ g := hφ₂'
  have hφ₃ : h₀ ≫ (biprod.inl : Y ⟶ Y ⊞ Z)⟦(1 : ℤ)⟧' = φ₃ ≫ h := hφ₃'
  have hψ₂ : g ≫ ψ₃ = (biprod.fst : Y ⊞ Z ⟶ Y) ≫ g₀ := hψ₂'
  have hψ₃ : h ≫ (biprod.fst : Y ⊞ Z ⟶ Y)⟦(1 : ℤ)⟧' = ψ₃ ≫ h₀ := hψ₃'
  have hχ₂ : g ≫ χ₃ = (biprod.snd : Y ⊞ Z ⟶ Z) ≫ (0 : Z ⟶ 0) := hχ₂'
  have hχ₃ : h ≫ (biprod.snd : Y ⊞ Z ⟶ Z)⟦(1 : ℤ)⟧' =
      χ₃ ≫ (0 : (0 : C) ⟶ Z⟦(1 : ℤ)⟧) := hχ₃'
  have hθ₂ : (0 : Z ⟶ 0) ≫ θ₃ = (biprod.inr : Z ⟶ Y ⊞ Z) ≫ g := hθ₂'
  have hθ₃ : (0 : (0 : C) ⟶ Z⟦(1 : ℤ)⟧) ≫
      (biprod.inr : Z ⟶ Y ⊞ Z)⟦(1 : ℤ)⟧' = θ₃ ≫ h := hθ₃'
  -- The `y`-summand retract: `φ₃ ≫ ψ₃` is an isomorphism by the five lemma.
  have he₀comm₁ : (0 : Y ⟶ Y) ≫ ((biprod.inl : Y ⟶ Y ⊞ Z) ≫
      (biprod.fst : Y ⊞ Z ⟶ Y)) = ((biprod.inl : Y ⟶ Y ⊞ Z) ≫
      (biprod.fst : Y ⊞ Z ⟶ Y)) ≫ (0 : Y ⟶ Y) := by simp
  have he₀comm₂ : g₀ ≫ (φ₃ ≫ ψ₃) = ((biprod.inl : Y ⟶ Y ⊞ Z) ≫
      (biprod.fst : Y ⊞ Z ⟶ Y)) ≫ g₀ := by
    rw [← Category.assoc, hφ₂, Category.assoc, hψ₂, ← Category.assoc]
  have he₀comm₃ : h₀ ≫ (((biprod.inl : Y ⟶ Y ⊞ Z) ≫
      (biprod.fst : Y ⊞ Z ⟶ Y)))⟦(1 : ℤ)⟧' = (φ₃ ≫ ψ₃) ≫ h₀ := by
    rw [Functor.map_comp, ← Category.assoc, hφ₃, Category.assoc, hψ₃,
      ← Category.assoc]
  have he₀₁ : IsIso ((biprod.inl : Y ⟶ Y ⊞ Z) ≫
      (biprod.fst : Y ⊞ Z ⟶ Y)) := by
    rw [biprod.inl_fst]
    exact ⟨𝟙 _, Category.id_comp _, Category.id_comp _⟩
  let e₀mor : Triangle.mk (0 : Y ⟶ Y) g₀ h₀ ⟶ Triangle.mk (0 : Y ⟶ Y) g₀ h₀ :=
    { hom₁ := (biprod.inl : Y ⟶ Y ⊞ Z) ≫ (biprod.fst : Y ⊞ Z ⟶ Y)
      hom₂ := (biprod.inl : Y ⟶ Y ⊞ Z) ≫ (biprod.fst : Y ⊞ Z ⟶ Y)
      hom₃ := φ₃ ≫ ψ₃
      comm₁ := he₀comm₁
      comm₂ := he₀comm₂
      comm₃ := he₀comm₃ }
  have hφψ : IsIso (φ₃ ≫ ψ₃) := isIso₃_of_isIso₁₂ e₀mor hT₀ hT₀ he₀₁ he₀₁
  -- The total endomorphism has identity components, so its third
  -- component is an isomorphism by the five lemma.
  have htot : ((biprod.fst : Y ⊞ Z ⟶ Y) ≫ (biprod.inl : Y ⟶ Y ⊞ Z)) +
      ((biprod.snd : Y ⊞ Z ⟶ Z) ≫ (biprod.inr : Z ⟶ Y ⊞ Z)) = 𝟙 (Y ⊞ Z) := by
    apply biprod.hom_ext'
    · simp
    · simp
  have hp1 : g ≫ (ψ₃ ≫ φ₃) = ((biprod.fst : Y ⊞ Z ⟶ Y) ≫
      (biprod.inl : Y ⟶ Y ⊞ Z)) ≫ g := by
    rw [← Category.assoc, hψ₂, Category.assoc, hφ₂, ← Category.assoc]
  have hp2 : g ≫ (χ₃ ≫ θ₃) = ((biprod.snd : Y ⊞ Z ⟶ Z) ≫
      (biprod.inr : Z ⟶ Y ⊞ Z)) ≫ g := by
    rw [← Category.assoc, hχ₂, Category.assoc, hθ₂, ← Category.assoc]
  have hq1 : (ψ₃ ≫ φ₃) ≫ h = h ≫ (((biprod.fst : Y ⊞ Z ⟶ Y) ≫
      (biprod.inl : Y ⟶ Y ⊞ Z)))⟦(1 : ℤ)⟧' := by
    rw [Category.assoc, ← hφ₃, ← Category.assoc, ← hψ₃, Category.assoc,
      ← Functor.map_comp]
  have hq2 : (χ₃ ≫ θ₃) ≫ h = h ≫ (((biprod.snd : Y ⊞ Z ⟶ Z) ≫
      (biprod.inr : Z ⟶ Y ⊞ Z)))⟦(1 : ℤ)⟧' := by
    rw [Category.assoc, ← hθ₃, ← Category.assoc, ← hχ₃, Category.assoc,
      ← Functor.map_comp]
  have he₁comm₁ : biprod.map (0 : Y ⟶ Y) (𝟙 Z) ≫ 𝟙 (Y ⊞ Z) =
      𝟙 (Y ⊞ Z) ≫ biprod.map (0 : Y ⟶ Y) (𝟙 Z) := by simp
  have he₁comm₂ : g ≫ ((ψ₃ ≫ φ₃) + (χ₃ ≫ θ₃)) = 𝟙 (Y ⊞ Z) ≫ g := by
    rw [Preadditive.comp_add, hp1, hp2, ← Preadditive.add_comp, htot]
  have he₁comm₃ : h ≫ (𝟙 (Y ⊞ Z))⟦(1 : ℤ)⟧' =
      ((ψ₃ ≫ φ₃) + (χ₃ ≫ θ₃)) ≫ h := by
    rw [Preadditive.add_comp, hq1, hq2, ← Preadditive.comp_add,
      ← Functor.map_add, htot]
  have he₁₁ : IsIso (𝟙 (Y ⊞ Z)) := ⟨𝟙 _, Category.id_comp _, Category.id_comp _⟩
  let e₁mor : Triangle.mk (biprod.map (0 : Y ⟶ Y) (𝟙 Z)) g h ⟶
    Triangle.mk (biprod.map (0 : Y ⟶ Y) (𝟙 Z)) g h :=
    { hom₁ := 𝟙 (Y ⊞ Z)
      hom₂ := 𝟙 (Y ⊞ Z)
      hom₃ := (ψ₃ ≫ φ₃) + (χ₃ ≫ θ₃)
      comm₁ := he₁comm₁
      comm₂ := he₁comm₂
      comm₃ := he₁comm₃ }
  have hsum : IsIso ((ψ₃ ≫ φ₃) + (χ₃ ≫ θ₃)) :=
    isIso₃_of_isIso₁₂ e₁mor hT hT he₁₁ he₁₁
  -- The `z`-summand contribution factors through zero, so `ψ₃ ≫ φ₃`
  -- is itself an isomorphism.
  have hχ0 : χ₃ = 0 := (isZero_zero C).eq_of_tgt _ _
  have hψφ : IsIso (ψ₃ ≫ φ₃) := by
    have h := hsum
    rw [hχ0, zero_comp, add_zero] at h
    exact h
  have hφ : IsIso φ₃ := isIso_of_isIso_comp_both φ₃ ψ₃ hφψ hψφ
  obtain ⟨inv, h1, h2⟩ := hφ.out
  exact S.replete hW ((Iso.mk φ₃ inv h1 h2).symm.trans e₀')

/-- In a dense subcategory, `Y ⊞ Y⟦-1⟧` is always a member: apply the
positive case at `Y⟦-1⟧` and cancel the shifts. -/
theorem TriangulatedSubcategory.mem_add_shift_neg_one
    (S : TriangulatedSubcategory C) (Y : C) : S.P (Y ⊞ Y⟦(-1 : ℤ)⟧) := by
  have h := S.mem_add_shift_one (Y⟦(-1 : ℤ)⟧)
  have hshift : Y⟦(-1 : ℤ)⟧⟦(1 : ℤ)⟧ ≅ Y := shiftNegShift Y 1
  refine S.replete h ⟨biprod.desc (biprod.inr : Y⟦(-1 : ℤ)⟧ ⟶ Y ⊞ Y⟦(-1 : ℤ)⟧)
    (hshift.hom ≫ (biprod.inl : Y ⟶ Y ⊞ Y⟦(-1 : ℤ)⟧)),
    biprod.desc (hshift.inv ≫ (biprod.inr : Y⟦(-1 : ℤ)⟧⟦(1 : ℤ)⟧ ⟶
      Y⟦(-1 : ℤ)⟧ ⊞ Y⟦(-1 : ℤ)⟧⟦(1 : ℤ)⟧))
    (biprod.inl : Y⟦(-1 : ℤ)⟧ ⟶ Y⟦(-1 : ℤ)⟧ ⊞ Y⟦(-1 : ℤ)⟧⟦(1 : ℤ)⟧), ?_, ?_⟩
  · apply biprod.hom_ext'
    · rw [← Category.assoc, biprod.inl_desc, biprod.inr_desc, Category.comp_id]
    · rw [← Category.assoc, biprod.inr_desc, Category.assoc, biprod.inl_desc,
        ← Category.assoc, Iso.hom_inv_id, Category.id_comp, Category.comp_id]
  · apply biprod.hom_ext'
    · rw [← Category.assoc, biprod.inl_desc, Category.assoc, biprod.inr_desc,
        ← Category.assoc, Iso.inv_hom_id, Category.id_comp, Category.comp_id]
    · rw [← Category.assoc, biprod.inr_desc, biprod.inl_desc, Category.comp_id]

end HilbertSmith
