/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.DivisorialQuotientFundamentalGroup
import EtaleFundamentalGroups.Inertia.Normalization.Localization
import EtaleFundamentalGroups.GaloisCovers.FunctionFieldAutomorphisms
import EtaleFundamentalGroups.Kummer.Normalization.FiniteEtaleGaloisCoverNormalizationAction
import Mathlib.RingTheory.Ideal.Pointwise

/-!
# Categorical finite images of divisorial inertia sources

The canonical fundamental-group quotient of the inertia fixed field is
transported from the function-field Galois group to the automorphism group of
an actual finite-etale Galois cover.  Its range is the categorical
normalization-prime inertia subgroup.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.FiniteEtale
open CategoryTheory.PreGaloisCategory

namespace EtaleFundamentalGroups.Inertia

universe u uA

/-- Transport the range before specializing the actions to a normalization. -/
private theorem range_inertia_transport
    {G H S B : Type*} [Group G] [Group H] [Group S] [Ring B]
    [MulSemiringAction G B] [MulSemiringAction H B]
    (Q : Ideal B) (e : G ≃* H)
    (he : ∀ (g : G) (b : B), e g • b = g • b)
    (f : S →* H) (hf : f.range = Q.toAddSubgroup.inertia H) :
    (e.symm.toMonoidHom.comp f).range = Q.toAddSubgroup.inertia G := by
  ext g
  constructor
  · rintro ⟨s, hs⟩
    change e.symm (f s) = g at hs
    have hm : f s ∈ Q.toAddSubgroup.inertia H := hf ▸ ⟨s, rfl⟩
    have heq : f s = e g := e.symm_apply_eq.mp hs
    change ∀ b : B, g • b - b ∈ Q
    intro b
    rw [← he, ← heq]
    exact hm b
  · intro hg
    have hm : e g ∈ Q.toAddSubgroup.inertia H := by
      change ∀ b : B, e g • b - b ∈ Q
      intro b
      rw [he]
      exact hg b
    rw [← hf] at hm
    obtain ⟨s, hs⟩ := hm
    refine ⟨s, ?_⟩
    change e.symm (f s) = g
    rw [hs, e.symm_apply_apply]

/-- Compare the two normalization actions while the fields are abstract. -/
private theorem normalization_inertia_actions_eq
    (A K L : Type*) [CommRing A] [IsDomain A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsIntegrallyClosed A] [FiniteDimensional K L]
    (Q : Ideal (integralClosure A L)) :
    let B := integralClosure A L
    letI : IsFractionRing B L :=
      IsIntegralClosure.isFractionRing_of_finite_extension A K L B
    Q.toAddSubgroup.inertia Gal(L/K) =
      (letI : MulSemiringAction Gal(L/K) B := IsIntegralClosure.MulSemiringAction A K L B
       Q.toAddSubgroup.inertia Gal(L/K)) := by
  let B := integralClosure A L
  let : IsFractionRing B L :=
    IsIntegralClosure.isFractionRing_of_finite_extension A K L B
  let genericAction : MulSemiringAction Gal(L/K) B := inferInstance
  let integralClosureAction : MulSemiringAction Gal(L/K) B :=
    IsIntegralClosure.MulSemiringAction A K L B
  have hsmul : ∀ (sigma : Gal(L/K)) (b : B),
      (letI := genericAction; sigma • b) =
        (letI := integralClosureAction; sigma • b) := by
    intro sigma b
    apply Subtype.ext
    calc
      ((letI := genericAction; (sigma • b : B)) : L) = sigma • (b : L) :=
        integralClosure.coe_smul sigma b
      _ = sigma (b : L) := AlgEquiv.smul_def _ _
      _ = ((letI := integralClosureAction; (sigma • b : B)) : L) := by
        let : MulSemiringAction Gal(L/K) B := integralClosureAction
        exact (algebraMap_galRestrict_apply A sigma b).symm
  ext sigma
  change (∀ b : B, (letI := genericAction; sigma • b) - b ∈ Q) ↔
    (∀ b : B, (letI := integralClosureAction; sigma • b) - b ∈ Q)
  constructor
  · intro hsigma b
    rw [← hsmul sigma b]
    exact hsigma b
  · intro hsigma b
    rw [hsmul sigma b]
    exact hsigma b

/-- The canonical inertia-fixed-field fundamental-group quotient, with target
transported to the automorphism group of a finite-etale Galois cover. -/
noncomputable def finiteEtaleGaloisCoverIdealInertiaFieldQuotientHom
    {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
    [IsLocallyNoetherian X]
    (Y : FiniteEtale X) (hY : IsGalois Y) :
    letI : IsGalois Y := hY
    letI : IsIntegral Y.left :=
      isIntegral_left_of_isConnected_finiteEtale Y
    let K := X.functionField
    let L := Y.left.functionField
    letI : Algebra K L := finiteEtaleFunctionFieldAlgebra Y
    ∀ (A : Type uA) [CommRing A] [IsDomain A]
      [Algebra A K] [IsFractionRing A K]
      [Algebra A L] [IsScalarTower A K L]
      [IsIntegrallyClosed A]
      (P : Ideal A) [P.IsPrime]
      (Q : Ideal (integralClosure A L)) [Q.IsPrime] [Q.LiesOver P],
      letI : FiniteDimensional K L :=
        finiteDimensional_functionField_of_finiteEtale_isConnected Y
      letI : _root_.IsGalois K L :=
        isGalois_functionField_of_isGalois_finiteEtale Y hY
      let B := integralClosure A L
      letI : IsFractionRing B L :=
        IsIntegralClosure.isFractionRing_of_finite_extension A K L B
      letI : MulSemiringAction Gal(L/K) B :=
        IsIntegralClosure.MulSemiringAction A K L B
      letI : MulSemiringAction (Aut Y)ᵐᵒᵖ B :=
        EtaleFundamentalGroups.Kummer.finiteEtaleGaloisCoverNormalizationAction
          Y hY A B
      let F := localizedNormalizationInertiaField
        (K := K) (L := L) P Q
      let Omega := SeparableClosure L
      letI : Algebra F Omega :=
        ((algebraMap L Omega).comp (algebraMap F L)).toAlgebra
      Aut (fib F Omega) →* (Aut Y)ᵐᵒᵖ := by
  letI : IsGalois Y := hY
  letI : IsIntegral Y.left :=
    isIntegral_left_of_isConnected_finiteEtale Y
  let K := X.functionField
  let L := Y.left.functionField
  letI : Algebra K L := finiteEtaleFunctionFieldAlgebra Y
  dsimp only
  intro A instCommRing instDomain instAK instFracAK instAL instTower instNormal P
    instPprime Q instQprime instQover
  letI : FiniteDimensional K L :=
    finiteDimensional_functionField_of_finiteEtale_isConnected Y
  letI : _root_.IsGalois K L :=
    isGalois_functionField_of_isGalois_finiteEtale Y hY
  exact (finiteEtaleAutOpFunctionFieldMulEquiv Y hY).symm.toMonoidHom.comp
    (localizedNormalizationInertiaFieldFundamentalGroupHom (K := K) (L := L) P Q)

/-- The canonical inertia-fixed-field source maps onto exactly the
categorical ideal-inertia subgroup of the cover automorphism group. -/
theorem finiteEtaleGaloisCoverIdealInertiaFieldQuotientHom_range
    {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
    [IsLocallyNoetherian X]
    (Y : FiniteEtale X) (hY : IsGalois Y) :
    letI : IsGalois Y := hY
    letI : IsIntegral Y.left :=
      isIntegral_left_of_isConnected_finiteEtale Y
    let K := X.functionField
    let L := Y.left.functionField
    letI : Algebra K L := finiteEtaleFunctionFieldAlgebra Y
    ∀ (A : Type uA) [CommRing A] [IsDomain A]
      [Algebra A K] [IsFractionRing A K]
      [Algebra A L] [IsScalarTower A K L]
      [IsIntegrallyClosed A]
      (P : Ideal A) [P.IsPrime]
      (Q : Ideal (integralClosure A L)) [Q.IsPrime] [Q.LiesOver P],
      letI : FiniteDimensional K L :=
        finiteDimensional_functionField_of_finiteEtale_isConnected Y
      letI : _root_.IsGalois K L :=
        isGalois_functionField_of_isGalois_finiteEtale Y hY
      let B := integralClosure A L
      letI : IsFractionRing B L :=
        IsIntegralClosure.isFractionRing_of_finite_extension A K L B
      letI : MulSemiringAction Gal(L/K) B :=
        IsIntegralClosure.MulSemiringAction A K L B
      letI : MulSemiringAction (Aut Y)ᵐᵒᵖ B :=
        EtaleFundamentalGroups.Kummer.finiteEtaleGaloisCoverNormalizationAction
          Y hY A B
      (finiteEtaleGaloisCoverIdealInertiaFieldQuotientHom Y hY A P Q).range =
        Q.toAddSubgroup.inertia (Aut Y)ᵐᵒᵖ := by
  let : IsGalois Y := hY
  let : IsIntegral Y.left :=
    isIntegral_left_of_isConnected_finiteEtale Y
  let K := X.functionField
  let L := Y.left.functionField
  let : Algebra K L := finiteEtaleFunctionFieldAlgebra Y
  dsimp only
  intro A instCommRing instDomain instAK instFracAK instAL instTower instNormal P
    instPprime Q instQprime instQover
  let : FiniteDimensional K L :=
    finiteDimensional_functionField_of_finiteEtale_isConnected Y
  let : _root_.IsGalois K L :=
    isGalois_functionField_of_isGalois_finiteEtale Y hY
  let B := integralClosure A L
  let : IsFractionRing B L :=
    IsIntegralClosure.isFractionRing_of_finite_extension A K L B
  let genericAction : MulSemiringAction Gal(L/K) B := inferInstance
  let integralClosureAction : MulSemiringAction Gal(L/K) B :=
    IsIntegralClosure.MulSemiringAction A K L B
  let : MulSemiringAction Gal(L/K) B := integralClosureAction
  let : MulSemiringAction (Aut Y)ᵐᵒᵖ B :=
    EtaleFundamentalGroups.Kummer.finiteEtaleGaloisCoverNormalizationAction
      Y hY A B
  let F := localizedNormalizationInertiaField (K := K) (L := L) P Q
  let Omega := SeparableClosure L
  let : Algebra F Omega :=
    ((algebraMap L Omega).comp (algebraMap F L)).toAlgebra
  let sourceHom := localizedNormalizationInertiaFieldFundamentalGroupHom
    (K := K) (L := L) P Q
  let Hgal :=
    (letI := integralClosureAction
     Q.toAddSubgroup.inertia Gal(L/K))
  have haction :
      (letI := genericAction; Q.toAddSubgroup.inertia Gal(L/K)) = Hgal :=
    normalization_inertia_actions_eq A K L Q
  have hsourceRange : sourceHom.range = Hgal := by
    calc
      sourceHom.range =
          localizedNormalizationInertia (K := K) (L := L) P Q :=
        localizedNormalizationInertiaFieldFundamentalGroupHom_range
          (K := K) (L := L) P Q
      _ = Hgal :=
        (normalizationInertia_eq_localizedNormalizationInertia
          (K := K) (L := L) P Q).symm.trans haction
  change ((finiteEtaleAutOpFunctionFieldMulEquiv Y hY).symm.toMonoidHom.comp sourceHom).range = _
  exact range_inertia_transport Q (finiteEtaleAutOpFunctionFieldMulEquiv Y hY)
    (EtaleFundamentalGroups.Kummer.finiteEtaleGaloisCoverNormalizationAction_smul Y hY A B)
    sourceHom hsourceRange

end EtaleFundamentalGroups.Inertia

end
