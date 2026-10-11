/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.FiniteEtaleNormalizationAction

/-!
# Geometric normalization points and the intrinsic integral-closure action

The coordinate homomorphism of a normalization point retains its actual map
to the base. Its kernel inertia, with the intrinsic Galois action on the
integral closure, is exactly the geometric fixed-point condition.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.PreGaloisCategory

namespace EtaleFundamentalGroups.Inertia

universe u

/-- Extract the actual integral-closure prime and its inertia from a geometric
normalization point, using the algebras supplied by the displayed morphism. -/
theorem exists_finiteEtaleMorphism_normalizationPoint_inertia_iff
    (R : Type u) [CommRing R]
    {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X]
    [IsAffine X]
    (g : X ⟶ Spec (.of R)) [QuasiCompact g] [QuasiSeparated g]
    (Y : FiniteEtale X) [IsConnected Y]
    {Ω : Type u} [Field Ω]
    (z : Spec (.of Ω) ⟶ ((show Y.left ⟶ X from Y.hom) ≫ g).normalization) :
    let : IsIntegral Y.left := isIntegral_left_of_isConnected_finiteEtale Y
    let : Algebra X.functionField Y.left.functionField := finiteEtaleFunctionFieldAlgebra Y
    let : Algebra R X.functionField := affineMorphismFunctionFieldAlgebra R g
    let : Algebra R Y.left.functionField :=
      affineMorphismFunctionFieldAlgebra R ((show Y.left ⟶ X from Y.hom) ≫ g)
    let : IsScalarTower R X.functionField Y.left.functionField :=
      finiteEtaleMorphism_functionField_isScalarTower R g Y
    ∃ φ : integralClosure R Y.left.functionField →+* Ω,
      Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom
          (algebraMap R (integralClosure R Y.left.functionField))) =
        z ≫ ((show Y.left ⟶ X from Y.hom) ≫ g).fromNormalization ∧
      ∀ σ : Aut Y,
        finiteEtaleAutFunctionFieldAlgEquiv Y σ ∈
          (RingHom.ker φ).inertia Gal(Y.left.functionField/X.functionField) ↔
        z ≫ normalizationEndomorphism ((show Y.left ⟶ X from Y.hom) ≫ g) σ.hom.left
          (by
            rw [← Category.assoc]
            exact congrArg (fun k => k ≫ g) σ.hom.w) = z := by
  intro hIntegral hKL hRK hRL hTower
  have : IsAffine Y.left := isAffine_of_isAffineHom (show Y.left ⟶ X from Y.hom)
  have : IsNormalIntegral Y.left := isNormalIntegral_left_of_isConnected_finiteEtale Y
  obtain ⟨φ, hφ, hfix⟩ := exists_finiteEtaleMorphism_point_inertia_iff R g Y z
  refine ⟨φ, ?_, ?_⟩
  · exact (congrArg (fun k => k ≫ Spec.map (CommRingCat.ofHom
        (algebraMap R (integralClosure R Y.left.functionField)))) hφ).trans
      ((Category.assoc z _ _).trans
        (congrArg (fun k => z ≫ k)
          (affineMorphismFunctionFieldNormalizationIso_hom_base R
            ((show Y.left ⟶ X from Y.hom) ≫ g))))
  · intro σ
    have hsmul (b : integralClosure R Y.left.functionField) :
        (finiteEtaleAutFunctionFieldAlgEquiv Y σ) • b =
        ((integralClosureAutHom R Y.left.functionField).comp
          (AlgEquiv.restrictScalarsHom R)) (finiteEtaleAutFunctionFieldAlgEquiv Y σ) b := by
      apply Subtype.ext
      exact integralClosure.coe_smul _ _
    have hmem :
        finiteEtaleAutFunctionFieldAlgEquiv Y σ ∈
          (RingHom.ker φ).inertia Gal(Y.left.functionField/X.functionField) ↔
        (let : MulSemiringAction Gal(Y.left.functionField/X.functionField)
            (integralClosure R Y.left.functionField) :=
          MulSemiringAction.compHom (integralClosure R Y.left.functionField)
            ((integralClosureAutHom R Y.left.functionField).comp (AlgEquiv.restrictScalarsHom R))
         finiteEtaleAutFunctionFieldAlgEquiv Y σ ∈
          (RingHom.ker φ).inertia Gal(Y.left.functionField/X.functionField)) := by
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

end EtaleFundamentalGroups.Inertia
