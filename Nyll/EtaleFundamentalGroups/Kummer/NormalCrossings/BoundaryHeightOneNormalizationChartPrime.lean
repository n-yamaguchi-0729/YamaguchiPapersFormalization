/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Kummer.NormalCrossings.BoundaryHeightOneNormalizationPrimeLocalization
import Nyll.EtaleFundamentalGroups.Normalization.IntegralClosure.BaseRingEquiv
import Nyll.EtaleFundamentalGroups.Normalization.IntegralClosure.IntegralBase.PrimeLocalizationEquiv
import Nyll.EtaleFundamentalGroups.Purity.ConnectedCoverGenericNormalizationFinite
import Nyll.EtaleFundamentalGroups.Purity.PuncturedSpectrumConnectedRestriction

/-!
# Height-one primes on affine charts of a boundary normalization

This file carries a height-one prime on an affine integral-closure chart of
the generic-extension normalization to the corresponding prime over the
ambient boundary stalk.  The literal local-ring map on the original chart is
retained in the conclusion.
-/

noncomputable section

open CategoryTheory TopologicalSpace
open CategoryTheory.PreGaloisCategory
open AlgebraicGeometry.FiniteEtale
open EtaleFundamentalGroups

namespace AlgebraicGeometry.Scheme.EffectiveCartierDivisor

universe u

variable {X : Scheme.{u}}

/-- A height-one prime of an affine chart of the generic-extension
normalization which lies over the boundary has a formally etale literal
prime-local map. -/
theorem
    HasSurjectiveComponentsOverIntegers.heightOneBoundaryGenericExtensionChartPrime_formallyEtale
    [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X]
    (D : EffectiveCartierDivisor X)
    (hSurjective : D.HasSurjectiveComponentsOverIntegers)
    (hNC : D.IsNormalCrossings)
    [Nonempty D.1.supportComplement]
    (W : FiniteEtale D.1.supportComplement) (hW : IsGalois W) :
    let : IsIntegral D.1.supportComplement :=
      isIntegral_of_isOpenImmersion D.1.supportComplement.ι
    let : IsNormalIntegral D.1.supportComplement :=
      IsNormalIntegral.of_isOpenImmersion D.1.supportComplement.ι
    let : IsLocallyNoetherian D.1.supportComplement :=
      isLocallyNoetherian_of_isOpenImmersion D.1.supportComplement.ι
    let : IsIntegral W.left :=
      EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale W
    let K := (D.1.supportComplement : Scheme).functionField
    let L := W.left.functionField
    let : Algebra K L :=
      EtaleFundamentalGroups.finiteEtaleFunctionFieldAlgebra W
    let e : X.functionField ≃+* K :=
      D.1.supportComplement.ι.functionFieldRingEquivOfIsOpenImmersion
    let : Algebra X.functionField L :=
      ((algebraMap K L).comp e.toRingHom).toAlgebra
    let f := X.genericExtensionMorphism L
    ∀ (V : X.Opens) (hV : IsAffineOpen V)
      (Q : PrimeSpectrum
        (letI := (f.app V).hom.toAlgebra
         integralClosure Γ(X, V) Γ(Spec (.of L), f ⁻¹ᵁ V))),
      f.fromNormalization
          (f.normalizationOpenCover.f ⟨V, hV⟩ Q) ∉ D.1.supportComplement →
      let : Algebra Γ(X, V) Γ(Spec (.of L), f ⁻¹ᵁ V) :=
        (f.app V).hom.toAlgebra
      let C := integralClosure Γ(X, V) Γ(Spec (.of L), f ⁻¹ᵁ V)
      let phi : Γ(X, V) →+* C := algebraMap Γ(X, V) C
      (Q.comap phi).asIdeal.height = 1 →
      (Localization.localRingHom
        (Q.comap phi).asIdeal Q.asIdeal phi rfl).FormallyEtale := by
  intro hUIntegral hUNormal hUNoetherian hWIntegral K L hKL e hXL f V hV Q hboundary
  let A := Γ(X, V)
  let S := Γ(Spec (.of L), f ⁻¹ᵁ V)
  intro algebraAS C phi hheight
  let P : Ideal A := Q.asIdeal.under A
  let : P.IsPrime := inferInstance
  change P.height = 1 at hheight
  let pSpec : Spec (.of A) := ⟨P, inferInstance⟩
  let x : X := hV.fromSpec pSpec
  have hxV : x ∈ V := by
    change (hV.isoSpec.inv pSpec).1 ∈ V
    exact (hV.isoSpec.inv pSpec).2
  have hpoint :
      f.fromNormalization
          (f.normalizationOpenCover.f ⟨V, hV⟩ Q) = x := by
    change (f.normalizationOpenCover.f ⟨V, hV⟩ ≫
      f.fromNormalization) Q = hV.fromSpec pSpec
    exact congrArg (fun k : Spec (.of C) ⟶ X ↦ k Q)
      (f.ι_fromNormalization ⟨V, hV⟩)
  have hxBoundary : x ∈ D.1.support := by
    have hxOutside : x ∉ D.1.supportComplement := by
      rwa [hpoint] at hboundary
    by_contra hx
    exact hxOutside ((D.1.mem_supportComplement x).2 hx)
  have hxRange : x ∈ Set.range D.1.subschemeι := by
    rw [D.1.range_subschemeι]
    exact hxBoundary
  obtain ⟨z, hz⟩ := hxRange
  have hstalkBoundary :
      D.1.stalkIdeal x ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
    have hclosed :
        X.fromSpecStalk x
            (IsLocalRing.closedPoint (X.presheaf.stalk x)) ∈ D.1.support := by
      rw [X.fromSpecStalk_closedPoint]
      exact hxBoundary
    have hle :=
      (D.1.mem_support_fromSpecStalk_iff_stalkIdeal_le x
        (IsLocalRing.closedPoint (X.presheaf.stalk x))).mp hclosed
    change D.1.stalkIdeal x ≤
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) at hle
    exact hle
  let : Nonempty V := ⟨⟨x, hxV⟩⟩
  let : IsFractionRing A X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X V hV
  let : Algebra A K :=
    (e.toRingHom.comp (algebraMap A X.functionField)).toAlgebra
  let eK : X.functionField ≃ₐ[A] K :=
    AlgEquiv.ofRingEquiv (f := e) fun _ ↦ rfl
  let : IsFractionRing A K := IsFractionRing.of_algEquiv eK
  let : Algebra A L := X.affineExtensionAlgebra V L
  let : IsScalarTower A K L := by
    apply IsScalarTower.of_algebraMap_eq
    intro a
    change algebraMap X.functionField L (X.germToFunctionField V a) =
      algebraMap K L (e (X.germToFunctionField V a))
    rfl
  let eS : S ≃ₐ[A] L := X.genericExtensionSectionsAlgEquiv L V
  let eC : C ≃ₐ[A] integralClosure A L := eS.mapIntegralClosure
  let QL : Ideal (integralClosure A L) := Q.asIdeal.map eC.toRingEquiv
  let : QL.IsPrime := inferInstance
  let : Q.asIdeal.LiesOver P := inferInstance
  let : QL.LiesOver P := by
    refine ⟨(Q.asIdeal.over_def P).trans ?_⟩
    ext a
    change algebraMap A C a ∈ Q.asIdeal ↔
      algebraMap A (integralClosure A L) a ∈ QL
    rw [← eC.commutes a]
    exact Ideal.apply_mem_of_equiv_iff.symm
  let AP := Localization.AtPrime P
  let : Algebra AP L :=
    localizationAtPrimeToExtensionAlgebra (K := K) (L := L) P
  let : IsScalarTower A AP L :=
    localizationAtPrimeToExtension_isScalarTower (K := K) (L := L) P
  let q0 := localizedNormalizationPrime (K := K) (L := L) P QL
  let : q0.IsMaximal :=
    localizedNormalizationPrime_isMaximal (K := K) (L := L) P QL
  let : q0.LiesOver (IsLocalRing.maximalIdeal AP) :=
    localizedNormalizationPrime_liesOver (K := K) (L := L) P QL
  have hEtaleAP : Algebra.FormallyEtale AP (Localization.AtPrime q0) := by
    let Ax := X.presheaf.stalk x
    let : Algebra A Ax :=
      TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxV⟩
    let : IsLocalization.AtPrime Ax P := hV.isLocalization_stalk' pSpec hxV
    let eBase : AP ≃ₐ[A] Ax :=
      IsLocalization.algEquiv P.primeCompl AP Ax
    let : Algebra Ax K := D.1.supportComplementFunctionFieldAlgebra x
    let : IsFractionRing Ax K :=
      D.1.supportComplementFunctionField_isFractionRing x
    let : IsScalarTower A Ax K := by
      apply IsScalarTower.of_algebraMap_eq
      intro a
      change e (X.germToFunctionField V a) =
        e (algebraMap Ax X.functionField
          (X.presheaf.germ V x hxV a))
      rw [X.algebraMap_germ_eq_germToFunctionField hxV a]
    let : Algebra Ax L :=
      ((algebraMap K L).comp (algebraMap Ax K)).toAlgebra
    let : IsScalarTower Ax K L := IsScalarTower.of_algebraMap_eq' rfl
    let : IsScalarTower A Ax L := by
      apply IsScalarTower.of_algebraMap_eq
      intro a
      change algebraMap K L (algebraMap A K a) =
        algebraMap K L (algebraMap Ax K (algebraMap A Ax a))
      rw [IsScalarTower.algebraMap_apply A Ax K]
    have hBaseL :
        (algebraMap Ax L).comp eBase.toRingHom = algebraMap AP L := by
      apply IsLocalization.ringHom_ext P.primeCompl
      ext a
      simp only [RingHom.comp_apply]
      change algebraMap Ax L (eBase (algebraMap A AP a)) =
        algebraMap AP L (algebraMap A AP a)
      calc
        algebraMap Ax L (eBase (algebraMap A AP a)) =
            algebraMap Ax L (algebraMap A Ax a) := by
          rw [eBase.commutes a]
        _ = algebraMap A L a :=
          (IsScalarTower.algebraMap_apply A Ax L a).symm
        _ = algebraMap AP L (algebraMap A AP a) :=
          IsScalarTower.algebraMap_apply A AP L a
    let : Algebra AP Ax := eBase.toRingHom.toAlgebra
    let : Algebra AP (integralClosure Ax L) :=
      integralClosureBaseRingAlgebra eBase.toRingEquiv
    let eTarget : integralClosure AP L ≃ₐ[AP] integralClosure Ax L :=
      integralClosureBaseRingAlgEquiv eBase.toRingEquiv hBaseL
    let qx : Ideal (integralClosure Ax L) := q0.map eTarget.toRingEquiv
    let : qx.IsPrime := inferInstance
    let : qx.IsMaximal := inferInstance
    have hqxUnderMaximal : qx.under Ax = IsLocalRing.maximalIdeal Ax := by
      have hmax : (qx.under Ax).IsMaximal :=
        Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap Ax _)
          (fun x ↦ Algebra.IsIntegral.isIntegral x) qx
      exact IsLocalRing.eq_maximalIdeal hmax
    have hqxHeight : (qx.under Ax).height = 1 := by
      rw [hqxUnderMaximal]
      apply WithBot.coe_eq_coe.mp
      calc
        (((IsLocalRing.maximalIdeal Ax).height : ℕ∞) : WithBot ℕ∞) =
            ringKrullDim Ax := IsLocalRing.maximalIdeal_height_eq_ringKrullDim
        _ = ((P.height : ℕ∞) : WithBot ℕ∞) :=
          IsLocalization.AtPrime.ringKrullDim_eq_height P Ax
        _ = (((1 : ℕ∞)) : WithBot ℕ∞) := by rw [hheight]
    have hqxBoundary : D.1.stalkIdeal x ≤ qx.under Ax := by
      rw [hqxUnderMaximal]
      exact hstalkBoundary
    have hStalk :
        let phiX : Ax →+* integralClosure Ax L :=
          algebraMap Ax (integralClosure Ax L)
        (Localization.localRingHom
          (qx.under Ax) qx phiX rfl).FormallyEtale := by
      have hlocal := hSurjective.heightOneBoundaryNormalizationPrime_formallyEtale
        D hNC W hW z
      rw [hz] at hlocal
      exact hlocal qx hqxHeight hqxBoundary
    let : IsScalarTower AP Ax (integralClosure Ax L) :=
      IsScalarTower.of_algebraMap_eq' rfl
    let eTargetLocal : Localization.AtPrime q0 ≃ₐ[AP]
        Localization.AtPrime qx :=
      localizationAtMappedPrimeAlgEquiv eTarget q0
    have hStalkAlg : Algebra.FormallyEtale Ax (Localization.AtPrime qx) := by
      let px := qx.under Ax
      let : Algebra (Localization.AtPrime px) (Localization.AtPrime qx) :=
        Localization.AtPrime.algebraOfLiesOver px qx
      let : Algebra.FormallyEtale (Localization.AtPrime px) (Localization.AtPrime qx) :=
        hStalk
      let : Algebra.FormallyEtale Ax (Localization.AtPrime px) :=
        Algebra.FormallyEtale.of_isLocalization px.primeCompl
      exact Algebra.FormallyEtale.comp Ax (Localization.AtPrime px) (Localization.AtPrime qx)
    let eBaseAlg : AP ≃ₐ[AP] Ax :=
      AlgEquiv.ofRingEquiv (f := eBase.toRingEquiv) fun _ ↦ rfl
    let : Algebra.FormallyEtale AP Ax :=
      Algebra.FormallyEtale.of_equiv eBaseAlg
    let : Algebra.FormallyEtale AP (Localization.AtPrime qx) :=
      Algebra.FormallyEtale.comp AP Ax (Localization.AtPrime qx)
    exact Algebra.FormallyEtale.of_equiv eTargetLocal.symm
  let : Algebra.FormallyEtale AP (Localization.AtPrime q0) := hEtaleAP
  let : Algebra AP (Localization.AtPrime Q.asIdeal) :=
    Localization.AtPrime.algebraOfLiesOver P Q.asIdeal
  let : Algebra AP (Localization.AtPrime QL) :=
    Localization.AtPrime.algebraOfLiesOver P QL
  let eChartLocal : Localization.AtPrime Q.asIdeal ≃ₐ[AP]
      Localization.AtPrime QL :=
    localizationAtMappedPrimeAlgEquiv_overAtPrime eC P Q.asIdeal
  let ePrimeLocal : Localization.AtPrime QL ≃ₐ[AP]
      Localization.AtPrime q0 :=
    integralClosurePrimeLocalizationAlgEquiv (K := K) (L := L) P QL
  let : Algebra.FormallyEtale AP (Localization.AtPrime QL) :=
    Algebra.FormallyEtale.of_equiv (R := AP)
      (A := Localization.AtPrime q0) (B := Localization.AtPrime QL) ePrimeLocal.symm
  let : Algebra.FormallyEtale AP (Localization.AtPrime Q.asIdeal) :=
    Algebra.FormallyEtale.of_equiv (R := AP)
      (A := Localization.AtPrime QL) (B := Localization.AtPrime Q.asIdeal) eChartLocal.symm
  change Algebra.FormallyEtale AP (Localization.AtPrime Q.asIdeal)
  exact inferInstance

namespace HasSurjectiveComponentsOverIntegers

/-- Canonical-cover form of
`heightOneBoundaryGenericExtensionChartPrime_formallyEtale`.  The public
source equality for the connected-cover generic composite transports the
whole dependent affine chart, including its normalization prime. -/
theorem
    heightOneBoundaryConnectedCoverNormalizationChartPrime_formallyEtale
    [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X]
    (D : EffectiveCartierDivisor X)
    (hSurjective : D.HasSurjectiveComponentsOverIntegers)
    (hNC : D.IsNormalCrossings)
    [Nonempty D.1.supportComplement]
    (W : FiniteEtale D.1.supportComplement) (hW : IsGalois W) :
    let : IsIntegral D.1.supportComplement :=
      isIntegral_of_isOpenImmersion D.1.supportComplement.ι
    let : IsNormalIntegral D.1.supportComplement :=
      IsNormalIntegral.of_isOpenImmersion D.1.supportComplement.ι
    let : IsLocallyNoetherian D.1.supportComplement :=
      isLocallyNoetherian_of_isOpenImmersion D.1.supportComplement.ι
    let : IsIntegral W.left :=
      EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale W
    let g := connectedCoverGenericComposite W ≫ D.1.supportComplement.ι
    ∀ (V : X.Opens) (hV : IsAffineOpen V)
      (Q : PrimeSpectrum
        (letI := (g.app V).hom.toAlgebra
         integralClosure Γ(X, V) Γ(Spec (.of W.left.functionField), g ⁻¹ᵁ V))),
      g.fromNormalization
          (g.normalizationOpenCover.f ⟨V, hV⟩ Q) ∉ D.1.supportComplement →
      let : Algebra Γ(X, V) Γ(Spec (.of W.left.functionField), g ⁻¹ᵁ V) :=
        (g.app V).hom.toAlgebra
      let C := integralClosure Γ(X, V)
        Γ(Spec (.of W.left.functionField), g ⁻¹ᵁ V)
      let phi : Γ(X, V) →+* C := algebraMap Γ(X, V) C
      (Q.comap phi).asIdeal.height = 1 →
      (Localization.localRingHom
        (Q.comap phi).asIdeal Q.asIdeal phi rfl).FormallyEtale := by
  intro hUIntegral hUNormal hUNoetherian hWIntegral g
  let K := (D.1.supportComplement : Scheme).functionField
  let L := W.left.functionField
  let : Algebra K L :=
    EtaleFundamentalGroups.finiteEtaleFunctionFieldAlgebra W
  let e : X.functionField ≃+* K :=
    D.1.supportComplement.ι.functionFieldRingEquivOfIsOpenImmersion
  let : Algebra X.functionField L :=
    ((algebraMap K L).comp e.toRingHom).toAlgebra
  have hsource :
      X.genericExtensionMorphism L =
        connectedCoverGenericComposite W ≫ D.1.supportComplement.ι :=
    genericExtensionMorphism_eq_connectedCoverGenericComposite_comp
        D.1.supportComplement.ι W
  let chartProperty (g : Spec (.of L) ⟶ X) : Prop :=
    ∀ [QuasiCompact g] [QuasiSeparated g]
      (V : X.Opens) (hV : IsAffineOpen V)
      (Q : PrimeSpectrum
        (letI := (g.app V).hom.toAlgebra
         integralClosure Γ(X, V) Γ(Spec (.of L), g ⁻¹ᵁ V))),
      g.fromNormalization
          (g.normalizationOpenCover.f ⟨V, hV⟩ Q) ∉ D.1.supportComplement →
      let : Algebra Γ(X, V) Γ(Spec (.of L), g ⁻¹ᵁ V) :=
        (g.app V).hom.toAlgebra
      let C := integralClosure Γ(X, V) Γ(Spec (.of L), g ⁻¹ᵁ V)
      let phi : Γ(X, V) →+* C := algebraMap Γ(X, V) C
      (Q.comap phi).asIdeal.height = 1 →
      (Localization.localRingHom
        (Q.comap phi).asIdeal Q.asIdeal phi rfl).FormallyEtale
  have hgeneric : chartProperty (X.genericExtensionMorphism L) := by
    intro _ _
    exact hSurjective.heightOneBoundaryGenericExtensionChartPrime_formallyEtale D hNC W hW
  have hconnected : chartProperty
      (connectedCoverGenericComposite W ≫ D.1.supportComplement.ι) := by
    rw [← hsource]
    exact hgeneric
  exact hconnected

end HasSurjectiveComponentsOverIntegers

end AlgebraicGeometry.Scheme.EffectiveCartierDivisor

end
