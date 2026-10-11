/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Kummer.NormalCrossings.BoundaryHeightOneNormalizationEtale
import EtaleFundamentalGroups.Normalization.Localization.IntegralClosure.PrimeAtPrimeEquiv

/-!
# Prime-local form of height-one boundary normalization etaleness

The normal-crossings calculation gives etaleness after first localizing the
base stalk and then taking its normalization.  The affine normalization
criterion instead asks for formal etaleness of the literal local-ring map at
a prime of the original normalization.  The canonical normalization and
prime-localization equivalences identify these two maps.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace EtaleFundamentalGroups

universe uA uK uL

variable {A : Type uA} {K : Type uK} {L : Type uL}
variable [CommRing A] [IsDomain A]
variable [Field K] [Field L]
variable [Algebra A K] [IsFractionRing A K]
variable [Algebra K L] [Algebra A L] [IsScalarTower A K L]

omit [IsDomain A] in
/-- Etaleness of the normalization after localizing the base at the
contraction of `Q` gives formal etaleness of the literal prime-local map of
the original normalization at `Q`. -/
theorem
    integralClosure_primeLocalization_formallyEtale_of_local_integralClosure_etale
    (Q : Ideal (integralClosure A L)) [Q.IsPrime]
    (hlocal :
      let P := Q.under A
      let : Algebra (Localization.AtPrime P) L :=
        localizationAtPrimeToExtensionAlgebra (K := K) (L := L) P
      Algebra.Etale (Localization.AtPrime P)
        (integralClosure (Localization.AtPrime P) L)) :
    let P := Q.under A
    let : P.IsPrime := inferInstance
    let : Q.LiesOver P := inferInstance
    let : Algebra (Localization.AtPrime P) L :=
      localizationAtPrimeToExtensionAlgebra (K := K) (L := L) P
    let : IsScalarTower A (Localization.AtPrime P) L :=
      localizationAtPrimeToExtension_isScalarTower
      (K := K) (L := L) P
    let : Algebra (Localization.AtPrime P) (Localization.AtPrime Q) :=
      Localization.AtPrime.algebraOfLiesOver P Q
    let C := integralClosure A L
    let phi : A →+* C := algebraMap A C
    (Localization.localRingHom P Q phi rfl).FormallyEtale := by
  intro P primeP overQ algebraVL towerAVL algebraVQ C phi
  let V := Localization.AtPrime P
  let Cp := integralClosure V L
  let : Algebra C Cp := integralClosureLocalizationAlgebra (L := L) P
  let q := localizedNormalizationPrime (K := K) (L := L) P Q
  let : q.IsMaximal :=
    localizedNormalizationPrime_isMaximal (K := K) (L := L) P Q
  let : Algebra.Etale V Cp := hlocal
  let : Algebra.FormallyEtale Cp (Localization.AtPrime q) :=
    Algebra.FormallyEtale.of_isLocalization q.primeCompl
  let : Algebra.FormallyEtale V (Localization.AtPrime q) :=
    Algebra.FormallyEtale.comp V Cp (Localization.AtPrime q)
  let e : Localization.AtPrime Q ≃ₐ[V] Localization.AtPrime q :=
    integralClosurePrimeLocalizationAlgEquiv (K := K) (L := L) P Q
  let : Algebra.FormallyEtale V (Localization.AtPrime Q) :=
    Algebra.FormallyEtale.of_equiv
      (R := V) (A := Localization.AtPrime q)
      (B := Localization.AtPrime Q) e.symm
  change Algebra.FormallyEtale V (Localization.AtPrime Q)
  exact inferInstance

end EtaleFundamentalGroups

namespace AlgebraicGeometry.Scheme.EffectiveCartierDivisor

open CategoryTheory.PreGaloisCategory EtaleFundamentalGroups

universe u

variable {X : Scheme.{u}}

/-- The height-one normal-crossings calculation, in the literal
prime-local form used by affine normalization charts. -/
theorem
    HasSurjectiveComponentsOverIntegers.heightOneBoundaryNormalizationPrime_formallyEtale
    [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X]
    (D : EffectiveCartierDivisor X)
    (hSurjective : D.HasSurjectiveComponentsOverIntegers)
    (hNC : D.IsNormalCrossings)
    [Nonempty D.1.supportComplement]
    (W : FiniteEtale D.1.supportComplement) (hW : IsGalois W)
    (z : D.1.subscheme) :
    let : IsIntegral D.1.supportComplement :=
      isIntegral_of_isOpenImmersion D.1.supportComplement.ι
    let : IsIntegral W.left :=
      EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale W
    let K := (D.1.supportComplement : Scheme).functionField
    let L := W.left.functionField
    let : Algebra K L :=
      EtaleFundamentalGroups.finiteEtaleFunctionFieldAlgebra W
    let : FiniteDimensional K L :=
      EtaleFundamentalGroups.finiteDimensional_functionField_of_finiteEtale_isConnected W
    let : _root_.IsGalois K L :=
      EtaleFundamentalGroups.isGalois_functionField_of_isGalois_finiteEtale W hW
    let x := D.1.subschemeι z
    let Ax := X.presheaf.stalk x
    let : Algebra Ax K := D.1.supportComplementFunctionFieldAlgebra x
    let : IsFractionRing Ax K :=
      D.1.supportComplementFunctionField_isFractionRing x
    let : Algebra Ax L :=
      ((algebraMap K L).comp (algebraMap Ax K)).toAlgebra
    let : IsScalarTower Ax K L := IsScalarTower.of_algebraMap_eq' rfl
    let C := integralClosure Ax L
    ∀ (Q : Ideal C), [Q.IsPrime] →
      (Q.under Ax).height = 1 →
      D.1.stalkIdeal x ≤ Q.under Ax →
      let P := Q.under Ax
      let : P.IsPrime := inferInstance
      let : Q.LiesOver P := inferInstance
      let : Algebra (Localization.AtPrime P) L :=
        EtaleFundamentalGroups.localizationAtPrimeToExtensionAlgebra
        (K := K) (L := L) P
      let : IsScalarTower Ax (Localization.AtPrime P) L :=
        EtaleFundamentalGroups.localizationAtPrimeToExtension_isScalarTower
        (K := K) (L := L) P
      let : Algebra (Localization.AtPrime P) (Localization.AtPrime Q) :=
        Localization.AtPrime.algebraOfLiesOver P Q
      let phi : Ax →+* C := algebraMap Ax C
      (Localization.localRingHom P Q phi rfl).FormallyEtale := by
  intro integralU integralW K L algebraKL finiteKL galoisKL x Ax
    algebraAxK fractionAxK algebraAxL towerAxKL C Q primeQ hheight hboundary
  let q : Spec Ax := ⟨Q.under Ax, inferInstance⟩
  apply
    integralClosure_primeLocalization_formallyEtale_of_local_integralClosure_etale
      (K := K) (L := L) Q
  exact
    hSurjective.heightOneBoundaryIntegralClosure_etale_of_stalkIdeal_le
      D hNC W hW z q hheight hboundary

end AlgebraicGeometry.Scheme.EffectiveCartierDivisor

end
