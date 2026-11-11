import HilbertSmithPaper.LTheory.Base.Complexes.StructurePush

/-!
# Pushforward preserves composition

`(g ≫ h)_% = g_% ≫ h_%`: componentwise `(h g)_q^* f (h g)_p = h_q^* (g_q^* f g_p) h_p`.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

open DualCat

universe v u

variable {B : Type u} [Category.{v} B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]
  [DualCat B]

namespace StructureCx

/-- **Pushforward preserves composition.** `(g ≫ h)_% = g_% ≫ h_%`. -/
lemma push_comp {C D E : ChainComplex B ℤ} (g : C ⟶ D) (h : D ⟶ E) :
    push (g ≫ h) = push g ≫ push h := by
  ext n f ⟨⟨p, q⟩, hpq⟩
  change dualHom ((g ≫ h).f q) ≫ f ⟨(p, q), hpq⟩ ≫ (g ≫ h).f p =
    dualHom (h.f q) ≫ (dualHom (g.f q) ≫ f ⟨(p, q), hpq⟩ ≫ g.f p) ≫ h.f p
  simp

end StructureCx

end HSP
