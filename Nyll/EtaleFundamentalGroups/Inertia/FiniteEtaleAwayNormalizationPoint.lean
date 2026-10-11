/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.FiniteEtaleAwayNormalizationAction
import Mathlib.RingTheory.Ideal.Defs
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# Actual normalization points with the canonical away-cover scalars

The coefficient algebras are compared before extracting a prime from the
normalization point. The resulting prime and Galois action therefore use
exactly the coefficient structures of the normal-crossings ramification
theorems. The point's map to the affine base is retained as an equality of
scheme morphisms.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.PreGaloisCategory

namespace EtaleFundamentalGroups.Inertia

universe u

/-- The kernel prime extracted from an affine geometric point lies over the
actual underlying prime of its displayed map to the base. -/
theorem ker_liesOver_of_specMap_comp
    {R B Ω : Type u} [CommRing R] [CommRing B] [Field Ω] [Algebra R B]
    (φ : B →+* Ω) (y : Spec (.of Ω) ⟶ Spec (.of R))
    (hy : Spec.map (CommRingCat.ofHom φ) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R B)) = y) :
    (RingHom.ker φ).LiesOver (y (IsLocalRing.closedPoint Ω)).asIdeal := by
  constructor
  rw [← hy]
  change Ideal.comap (algebraMap R B)
    (Ideal.comap φ (IsLocalRing.maximalIdeal Ω)) =
      Ideal.comap (algebraMap R B) (RingHom.ker φ)
  rw [IsLocalRing.maximalIdeal_eq_bot]
  rfl

private theorem exists_awayPoint_of_algebraEq
    (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [IsNoetherianRing R] (f : R) (hf : f ≠ 0)
    (Y : FiniteEtale (Spec (.of (Localization.Away f)))) [IsConnected Y]
    {Ω : Type u} [Field Ω]
    (z : Spec (.of Ω) ⟶
      ((show Y.left ⟶ Spec (.of (Localization.Away f)) from Y.hom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f)))).normalization) :
    let S := Localization.Away f
    let : IsDomain S := IsLocalization.Away.isDomain S hf
    let : IsIntegrallyClosed S := isIntegrallyClosed_of_isLocalization S
      (Submonoid.powers f)
      (Submonoid.powers_le.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr hf))
    let : IsIntegral Y.left := isIntegral_left_of_isConnected_finiteEtale Y
    let : Algebra (Spec (.of S)).functionField Y.left.functionField :=
      finiteEtaleFunctionFieldAlgebra Y
    ∀ (a : Algebra R (Spec (.of S)).functionField) (b : Algebra R Y.left.functionField)
      (ha : a = affineMorphismFunctionFieldAlgebra R
        (Spec.map (CommRingCat.ofHom (algebraMap R S))))
      (hb : b = affineMorphismFunctionFieldAlgebra R
        ((show Y.left ⟶ Spec (.of S) from Y.hom) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R S)))),
    let : Algebra R (Spec (.of S)).functionField := a
    let : Algebra R Y.left.functionField := b
    let : IsScalarTower R (Spec (.of S)).functionField Y.left.functionField := by
      cases ha
      cases hb
      exact finiteEtaleMorphism_functionField_isScalarTower R
        (Spec.map (CommRingCat.ofHom (algebraMap R S))) Y
    ∃ φ : integralClosure R Y.left.functionField →+* Ω,
      Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom
          (algebraMap R (integralClosure R Y.left.functionField))) =
        z ≫ ((show Y.left ⟶ Spec (.of S) from Y.hom) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R S))).fromNormalization ∧
      ∀ σ : Aut Y,
        finiteEtaleAutFunctionFieldAlgEquiv Y σ ∈
          (RingHom.ker φ).inertia Gal(Y.left.functionField/(Spec (.of S)).functionField) ↔
        z ≫ normalizationEndomorphism
          ((show Y.left ⟶ Spec (.of S) from Y.hom) ≫
            Spec.map (CommRingCat.ofHom (algebraMap R S))) σ.hom.left
          (by
            rw [← Category.assoc]
            exact congrArg
              (fun k => k ≫ Spec.map (CommRingCat.ofHom (algebraMap R S))) σ.hom.w) = z := by
  intro S hDomain hNormal hIntegral hKL a b ha hb
  subst a
  subst b
  intro hRK hRL hTower
  have : IsNormalIntegral Y.left := isNormalIntegral_left_of_isConnected_finiteEtale Y
  let g : Spec (.of S) ⟶ Spec (.of R) :=
    Spec.map (CommRingCat.ofHom (algebraMap R S))
  obtain ⟨φ, hφ, hfix⟩ := exists_finiteEtaleMorphism_point_inertia_iff R g Y z
  refine ⟨φ, ?_, ?_⟩
  · exact (congrArg (fun k => k ≫ Spec.map (CommRingCat.ofHom
        (algebraMap R (integralClosure R Y.left.functionField)))) hφ).trans
      ((Category.assoc z _ _).trans
        (congrArg (fun k => z ≫ k)
          (affineMorphismFunctionFieldNormalizationIso_hom_base R
            ((show Y.left ⟶ Spec (.of S) from Y.hom) ≫ g))))
  · intro σ
    have hsmul (b : integralClosure R Y.left.functionField) :
        (finiteEtaleAutFunctionFieldAlgEquiv Y σ) • b =
        ((integralClosureAutHom R Y.left.functionField).comp
          (AlgEquiv.restrictScalarsHom R)) (finiteEtaleAutFunctionFieldAlgEquiv Y σ) b := by
      apply Subtype.ext
      exact integralClosure.coe_smul _ _
    have hmem :
        finiteEtaleAutFunctionFieldAlgEquiv Y σ ∈
          (RingHom.ker φ).inertia Gal(Y.left.functionField/(Spec (.of S)).functionField) ↔
        (let : MulSemiringAction Gal(Y.left.functionField/(Spec (.of S)).functionField)
            (integralClosure R Y.left.functionField) :=
          MulSemiringAction.compHom (integralClosure R Y.left.functionField)
            ((integralClosureAutHom R Y.left.functionField).comp (AlgEquiv.restrictScalarsHom R))
         finiteEtaleAutFunctionFieldAlgEquiv Y σ ∈
          (RingHom.ker φ).inertia Gal(Y.left.functionField/(Spec (.of S)).functionField)) := by
      constructor
      · intro hσ
        apply Ideal.mem_inertia.mpr
        intro b
        exact (hsmul b ▸ Ideal.mem_inertia.mp hσ b)
      · intro hσ
        apply Ideal.mem_inertia.mpr
        intro b
        exact ((hsmul b).symm ▸ Ideal.mem_inertia.mp hσ b)
    exact hmem.trans (hfix σ)

/-- An actual point above a finite-etale away cover yields its integral-closure
prime and precisely the canonical function-field inertia condition. -/
theorem exists_finiteEtaleAway_normalizationPoint_inertia_iff
    (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [IsNoetherianRing R] (f : R) (hf : f ≠ 0)
    (Y : FiniteEtale (Spec (.of (Localization.Away f)))) [IsConnected Y]
    {Ω : Type u} [Field Ω]
    (z : Spec (.of Ω) ⟶
      ((show Y.left ⟶ Spec (.of (Localization.Away f)) from Y.hom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f)))).normalization) :
    let S := Localization.Away f
    let : IsDomain S := IsLocalization.Away.isDomain S hf
    let : IsIntegrallyClosed S := isIntegrallyClosed_of_isLocalization S
      (Submonoid.powers f)
      (Submonoid.powers_le.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr hf))
    let : IsIntegral Y.left := isIntegral_left_of_isConnected_finiteEtale Y
    let : Algebra (Spec (.of S)).functionField Y.left.functionField :=
      finiteEtaleFunctionFieldAlgebra Y
    let : Algebra R (Spec (.of S)).functionField :=
      localizationAwaySpecFunctionFieldAlgebra f hf
    let : Algebra R Y.left.functionField := finiteEtaleAwayFunctionFieldAlgebra f hf Y
    let : IsScalarTower R (Spec (.of S)).functionField Y.left.functionField :=
      finiteEtaleAway_functionField_isScalarTower f hf Y
    ∃ φ : integralClosure R Y.left.functionField →+* Ω,
      Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom
          (algebraMap R (integralClosure R Y.left.functionField))) =
        z ≫ ((show Y.left ⟶ Spec (.of S) from Y.hom) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R S))).fromNormalization ∧
      ∀ σ : Aut Y,
        finiteEtaleAutFunctionFieldAlgEquiv Y σ ∈
          (RingHom.ker φ).inertia Gal(Y.left.functionField/(Spec (.of S)).functionField) ↔
        z ≫ normalizationEndomorphism
          ((show Y.left ⟶ Spec (.of S) from Y.hom) ≫
            Spec.map (CommRingCat.ofHom (algebraMap R S))) σ.hom.left
          (by
            rw [← Category.assoc]
            exact congrArg
              (fun k => k ≫ Spec.map (CommRingCat.ofHom (algebraMap R S))) σ.hom.w) = z := by
  intro S hDomain hNormal hIntegral hKL hRK hRL hTower
  exact exists_awayPoint_of_algebraEq R f hf Y z hRK hRL
    (affineMorphismFunctionFieldAlgebra_specMap R S (algebraMap R S)).symm
    (finiteEtaleAwayFunctionFieldAlgebra_eq_affineMorphism f hf Y)

end EtaleFundamentalGroups.Inertia
