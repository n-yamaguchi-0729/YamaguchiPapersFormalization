/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.SchemeNormalizationFunctionField
import Nyll.EtaleFundamentalGroups.Inertia.FiniteEtaleFunctionFieldAction
import Mathlib.Algebra.Algebra.Tower

/-!
# The canonical Galois action on actual normalization points

For an affine connected finite etale cover, the algebra on its function
field constructed from its structure morphism factors through the canonical
function-field embedding of the cover. Consequently the normalization-point
action is the restriction of the canonical function-field Galois action.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.PreGaloisCategory

namespace EtaleFundamentalGroups.Inertia

universe u

variable (R : Type u) [CommRing R]
variable {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X]

omit [IsLocallyNoetherian X] in
/-- The algebra obtained from the actual composite structure morphism factors
through the canonical function-field map of the finite etale cover. -/
theorem finiteEtaleMorphism_functionField_isScalarTower
    (g : X ⟶ Spec (.of R)) (Y : FiniteEtale X) [IsConnected Y] :
    let : IsIntegral Y.left := isIntegral_left_of_isConnected_finiteEtale Y
    let : Algebra X.functionField Y.left.functionField := finiteEtaleFunctionFieldAlgebra Y
    let : Algebra R X.functionField := affineMorphismFunctionFieldAlgebra R g
    let : Algebra R Y.left.functionField :=
      affineMorphismFunctionFieldAlgebra R ((show Y.left ⟶ X from Y.hom) ≫ g)
    IsScalarTower R X.functionField Y.left.functionField := by
  intro hIntegral hKL hRK hRL
  have : Nonempty (⊤ : X.Opens) :=
    ⟨⟨Classical.choice (inferInstance : Nonempty X), trivial⟩⟩
  have : Nonempty (⊤ : Y.left.Opens) :=
    ⟨⟨Classical.choice (inferInstance : Nonempty Y.left), trivial⟩⟩
  apply IsScalarTower.of_algebraMap_eq
  intro r
  change Y.left.germToFunctionField ⊤
      (((show Y.left ⟶ X from Y.hom) ≫ g).appTop ((Scheme.ΓSpecIso (.of R)).inv r)) =
    (show Y.left ⟶ X from Y.hom).functionFieldMap (finiteEtale_hom_denseRange_of_isConnected Y)
      (X.germToFunctionField ⊤ (g.appTop ((Scheme.ΓSpecIso (.of R)).inv r)))
  rw [Scheme.Hom.comp_appTop]
  exact (DFunLike.congr_fun
    ((show Y.left ⟶ X from Y.hom).functionFieldMap_comp_germToFunctionField_top
    (finiteEtale_hom_denseRange_of_isConnected Y))
      (g.appTop ((Scheme.ΓSpecIso (.of R)).inv r))).symm

variable [IsAffine X]

/-- The actual normalization's field automorphism equals the canonical deck
function-field automorphism, restricted to the original affine base. -/
theorem finiteEtaleMorphismFunctionFieldAlgEquiv_eq
    (g : X ⟶ Spec (.of R)) (Y : FiniteEtale X) [IsConnected Y] (sigma : Aut Y) :
    let : IsIntegral Y.left := isIntegral_left_of_isConnected_finiteEtale Y
    let : IsAffine Y.left := isAffine_of_isAffineHom (show Y.left ⟶ X from Y.hom)
    let : Algebra X.functionField Y.left.functionField := finiteEtaleFunctionFieldAlgebra Y
    let : Algebra R X.functionField := affineMorphismFunctionFieldAlgebra R g
    let : Algebra R Y.left.functionField :=
      affineMorphismFunctionFieldAlgebra R ((show Y.left ⟶ X from Y.hom) ≫ g)
    let : IsScalarTower R X.functionField Y.left.functionField :=
      finiteEtaleMorphism_functionField_isScalarTower R g Y
    affineMorphismFunctionFieldAlgEquiv R ((show Y.left ⟶ X from Y.hom) ≫ g)
        (show Y.left ≅ Y.left from (FiniteEtale.forget X ⋙ Over.forget X).mapIso sigma)
        (by
          change sigma.hom.left ≫ ((show Y.left ⟶ X from Y.hom) ≫ g) = _
          have hw : sigma.hom.left ≫ (show Y.left ⟶ X from Y.hom) =
              (show Y.left ⟶ X from Y.hom) := sigma.hom.w
          rw [← Category.assoc, hw]) =
      (finiteEtaleAutFunctionFieldAlgEquiv Y sigma).restrictScalars R := by
  intro hIntegral hAffine hKL hRK hRL hTower
  have h := (affineMorphismFunctionFieldAlgEquiv_eq_functionFieldMap R
    ((show Y.left ⟶ X from Y.hom) ≫ g)
    (show Y.left ≅ Y.left from (FiniteEtale.forget X ⋙ Over.forget X).mapIso sigma)
    (by
          change sigma.hom.left ≫ ((show Y.left ⟶ X from Y.hom) ≫ g) = _
          have hw : sigma.hom.left ≫ (show Y.left ⟶ X from Y.hom) =
              (show Y.left ⟶ X from Y.hom) := sigma.hom.w
          rw [← Category.assoc, hw])).trans
      (finiteEtaleAutFunctionFieldAlgEquiv_eq_functionFieldMap Y sigma).symm
  apply AlgEquiv.ext
  intro x
  exact RingHom.congr_fun h x

/-- Every geometric normalization point supplies an actual integral-closure
prime whose inertia condition is exactly the cover's geometric fixed condition.
The action here is the literal restriction of the canonical field action. -/
theorem exists_finiteEtaleMorphism_point_inertia_iff
    (g : X ⟶ Spec (.of R)) [QuasiCompact g] [QuasiSeparated g]
    (Y : FiniteEtale X) [IsConnected Y]
    {Ω : Type u} [Field Ω]
    (z : Spec (.of Ω) ⟶ ((show Y.left ⟶ X from Y.hom) ≫ g).normalization) :
    let : IsIntegral Y.left := isIntegral_left_of_isConnected_finiteEtale Y
    let : IsAffine Y.left := isAffine_of_isAffineHom (show Y.left ⟶ X from Y.hom)
    let : IsNormalIntegral Y.left := isNormalIntegral_left_of_isConnected_finiteEtale Y
    let : Algebra X.functionField Y.left.functionField := finiteEtaleFunctionFieldAlgebra Y
    let : Algebra R X.functionField := affineMorphismFunctionFieldAlgebra R g
    let : Algebra R Y.left.functionField :=
      affineMorphismFunctionFieldAlgebra R ((show Y.left ⟶ X from Y.hom) ≫ g)
    let : IsScalarTower R X.functionField Y.left.functionField :=
      finiteEtaleMorphism_functionField_isScalarTower R g Y
    let : MulSemiringAction Gal(Y.left.functionField/X.functionField)
        (integralClosure R Y.left.functionField) :=
      MulSemiringAction.compHom (integralClosure R Y.left.functionField)
        ((integralClosureAutHom R Y.left.functionField).comp (AlgEquiv.restrictScalarsHom R))
    ∃ φ : integralClosure R Y.left.functionField →+* Ω,
      Spec.map (CommRingCat.ofHom φ) =
          z ≫ (affineMorphismFunctionFieldNormalizationIso R
            ((show Y.left ⟶ X from Y.hom) ≫ g)).hom ∧
        ∀ sigma : Aut Y,
          finiteEtaleAutFunctionFieldAlgEquiv Y sigma ∈
              (RingHom.ker φ).inertia Gal(Y.left.functionField/X.functionField) ↔
            z ≫ normalizationEndomorphism ((show Y.left ⟶ X from Y.hom) ≫ g) sigma.hom.left
              (by
                have hw : sigma.hom.left ≫ (show Y.left ⟶ X from Y.hom) =
                    (show Y.left ⟶ X from Y.hom) := sigma.hom.w
                rw [← Category.assoc, hw]) = z := by
  intro hIntegral hAffine hNormal hKL hRK hRL hTower hAction
  obtain ⟨φ, hφ, hfix⟩ :=
    exists_affineMorphismFunctionField_point_inertia_iff R ((show Y.left ⟶ X from Y.hom) ≫ g) z
  refine ⟨φ, hφ, ?_⟩
  intro sigma
  let e : Y.left ≅ Y.left := (FiniteEtale.forget X ⋙ Over.forget X).mapIso sigma
  have he : e.hom ≫ ((show Y.left ⟶ X from Y.hom) ≫ g) = (show Y.left ⟶ X from Y.hom) ≫ g := by
    change sigma.hom.left ≫ ((show Y.left ⟶ X from Y.hom) ≫ g) = _
    have hw : sigma.hom.left ≫ (show Y.left ⟶ X from Y.hom) =
        (show Y.left ⟶ X from Y.hom) := sigma.hom.w
    rw [← Category.assoc, hw]
  have h := hfix e he
  rw [finiteEtaleMorphismFunctionFieldAlgEquiv_eq R g Y sigma] at h
  exact h

end EtaleFundamentalGroups.Inertia
