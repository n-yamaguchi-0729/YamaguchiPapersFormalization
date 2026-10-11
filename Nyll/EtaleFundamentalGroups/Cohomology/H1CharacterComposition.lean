/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Cohomology.H1Character
import Nyll.EtaleFundamentalGroups.GeometricFiber.FundamentalGroupComposition

/-!
# H¹ characters and successive geometric fundamental-group maps

The actual comparison character removes the choice of pullback comparison.
The proof uses the existing geometric base-point naturality.
-/

noncomputable section

open CategoryTheory CategoryTheory.PreGaloisCategory AlgebraicGeometry

namespace EtaleFundamentalGroups.Cohomology

/-- Evaluation of a genuine H¹ class agrees for successive scheme maps and
their composite, including the canonical fibre-comparison isomorphisms. -/
theorem h1Character_fundamentalGroupHom_comp
    {X Y Z : Scheme} [ConnectedSpace Z]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    {Ω : Type} [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (.of Ω) ⟶ X) (A : AddCommGrpCat.{0}) [Finite A]
    (a : Sheaf.H.{0} ((constantSheaf Z.smallEtaleTopology AddCommGrpCat.{0}).obj A) 1)
    (σ : Aut (FiniteEtale.fiber ξ)) :
    let : TopologicalSpace (Multiplicative A) := ⊥
    h1Character A ((ξ ≫ f) ≫ g) a
        (FiniteEtale.fundamentalGroupHom g (ξ ≫ f)
          (FiniteEtale.fundamentalGroupHom f ξ σ)) =
      h1Character A (ξ ≫ f ≫ g) a
        (FiniteEtale.fundamentalGroupHom (f ≫ g) ξ σ) := by
  intro htop
  let t₁ := FiniteEtale.pullbackFiberIso (f ≫ g) ξ
  let t₂ := FiniteEtale.pullbackCompositeFiberIso f g ξ
  let t := t₁.symm ≪≫ t₂
  have ht : t₁ ≪≫ t = t₂ := by
    change t₁ ≪≫ (t₁.symm ≪≫ t₂) = t₂
    rw [← Iso.trans_assoc, Iso.self_symm_id, Iso.refl_trans]
  have hmap : t.conjAut (FiniteEtale.fundamentalGroupHom (f ≫ g) ξ σ) =
      autHomOfCompIso (FiniteEtale.pullback (f ≫ g)) t₂ σ := by
    let v := (((Functor.whiskeringLeft _ _ FintypeCat).obj
      (FiniteEtale.pullback (f ≫ g))).mapAut (FiniteEtale.fiber ξ) σ)
    change t.conjAut (t₁.conjAut v) = t₂.conjAut v
    exact (t₁.trans_conjAut t v).symm.trans
      (congrArg (fun e => e.conjAut v) ht)
  have h := congrArg
    (fun χ : Aut (FiniteEtale.fiber (ξ ≫ f ≫ g)) →ₜ* Multiplicative A =>
      χ (FiniteEtale.fundamentalGroupHom (f ≫ g) ξ σ))
    (h1Character_basePoint A (ξ ≫ f ≫ g) ((ξ ≫ f) ≫ g) t a)
  change h1Character A ((ξ ≫ f) ≫ g) a
      (t.conjAut (FiniteEtale.fundamentalGroupHom (f ≫ g) ξ σ)) = _ at h
  rw [hmap] at h
  rw [FiniteEtale.fundamentalGroupHom_comp_eq_autHomOfCompIso]
  exact h

end EtaleFundamentalGroups.Cohomology
