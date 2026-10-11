/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Normalization.Localization.IntegralClosure.IsoOver
import Nyll.EtaleFundamentalGroups.Purity.FiniteEtaleFromBoundaryStalks
import Nyll.EtaleFundamentalGroups.Purity.PuncturedSpectrumBoundaryNormalizationExtension
import Nyll.EtaleFundamentalGroups.Purity.PuncturedSpectrumConnectedNormalizationFiberComparison

/-!
# Boundary stalks of the connected punctured normalization

The canonical global relative normalization attached to a connected cover of
a punctured local spectrum is already identified with the spectrum of the
literal integral closure.  Here that global comparison is refined at a point:
the actual normalization stalk map is the canonical prime-local map obtained
after localizing the base and normalizing there.
-/

noncomputable section

open CategoryTheory IsLocalRing
open CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.FiniteEtale

universe u

variable (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [IsLocalRing R] [IsNoetherianRing R]

/-- At the point of the global relative normalization corresponding to a
prime `Q` of the literal integral closure, the actual normalization stalk map
is the canonical local map at the transported prime after base localization.
-/
noncomputable def
    connectedPuncturedCoverGenericNormalizationBoundaryStalkArrowIso
    (hpos : (1 : WithBot ℕ∞) ≤ ringKrullDim R)
    (W : FiniteEtale (Scheme.puncturedSpectrum R)) [IsConnected W] :
    let U := Scheme.puncturedSpectrum R
    let j : U ⟶ Spec (.of R) := Scheme.puncturedSpectrumInclusion R
    letI : Nonempty U :=
      Scheme.puncturedSpectrum_nonempty_of_one_le_ringKrullDim R hpos
    letI : IsOpenImmersion j := by
      dsimp only [j, Scheme.puncturedSpectrumInclusion]
      infer_instance
    letI : IsIntegral U := isIntegral_of_isOpenImmersion j
    letI : Algebra R U.functionField :=
      puncturedSpectrumFunctionFieldAlgebraOfPositiveDimension R hpos
    letI : IsFractionRing R U.functionField :=
      puncturedSpectrumFunctionField_isFractionRing_of_positiveDimension R hpos
    letI : IsIntegral W.left :=
      EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale W
    letI : Algebra U.functionField W.left.functionField :=
      EtaleFundamentalGroups.finiteEtaleFunctionFieldAlgebra W
    letI : Algebra R W.left.functionField :=
      ((algebraMap U.functionField W.left.functionField).comp
        (algebraMap R U.functionField)).toAlgebra
    letI : IsScalarTower R U.functionField W.left.functionField :=
      IsScalarTower.of_algebraMap_eq' rfl
    let C := integralClosure R W.left.functionField
    let g : Spec (.of W.left.functionField) ⟶ Spec (.of R) :=
      connectedCoverGenericComposite W ≫ j
    let z := g.fromNormalization
    let e : g.normalization ≅ Spec (.of C) :=
      connectedPuncturedCoverGenericNormalizationIsoSpecIntegralClosure
        R hpos W
    ∀ (Q : Ideal C), [Q.IsPrime] →
    let P := Q.under R
    letI : P.IsPrime := inferInstance
    letI : Q.LiesOver P := inferInstance
    letI := EtaleFundamentalGroups.localizationAtPrimeToExtensionAlgebra
      (K := U.functionField) (L := W.left.functionField) P
    letI := EtaleFundamentalGroups.localizationAtPrimeToExtension_isScalarTower
      (K := U.functionField) (L := W.left.functionField) P
    letI : Algebra (Localization.AtPrime P) (Localization.AtPrime Q) :=
      Localization.AtPrime.algebraOfLiesOver P Q
    let q := EtaleFundamentalGroups.localizedNormalizationPrime
      (K := U.functionField) (L := W.left.functionField) P Q
    letI : q.IsMaximal :=
      EtaleFundamentalGroups.localizedNormalizationPrime_isMaximal
        (K := U.functionField) (L := W.left.functionField) P Q
    Arrow.mk
        (z.stalkMap
          (e.inv (⟨Q, inferInstance⟩ : PrimeSpectrum C))) ≅
      Arrow.mk (CommRingCat.ofHom
        (R := Localization.AtPrime P) (S := Localization.AtPrime q)
        (algebraMap (Localization.AtPrime P) (Localization.AtPrime q))) := by
  dsimp only
  let U := Scheme.puncturedSpectrum R
  let j : U ⟶ Spec (.of R) := Scheme.puncturedSpectrumInclusion R
  letI : Nonempty U :=
    Scheme.puncturedSpectrum_nonempty_of_one_le_ringKrullDim R hpos
  letI : IsOpenImmersion j := by
    dsimp only [j, Scheme.puncturedSpectrumInclusion]
    infer_instance
  letI : IsIntegral U := isIntegral_of_isOpenImmersion j
  letI : Algebra R U.functionField :=
    puncturedSpectrumFunctionFieldAlgebraOfPositiveDimension R hpos
  letI : IsFractionRing R U.functionField :=
    puncturedSpectrumFunctionField_isFractionRing_of_positiveDimension R hpos
  letI : IsIntegral W.left :=
    EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale W
  letI : Algebra U.functionField W.left.functionField :=
    EtaleFundamentalGroups.finiteEtaleFunctionFieldAlgebra W
  letI : Algebra R W.left.functionField :=
    ((algebraMap U.functionField W.left.functionField).comp
      (algebraMap R U.functionField)).toAlgebra
  letI : IsScalarTower R U.functionField W.left.functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  let C := integralClosure R W.left.functionField
  let g : Spec (.of W.left.functionField) ⟶ Spec (.of R) :=
    connectedCoverGenericComposite W ≫ j
  let z := g.fromNormalization
  let e : g.normalization ≅ Spec (.of C) :=
    connectedPuncturedCoverGenericNormalizationIsoSpecIntegralClosure
      R hpos W
  intro Q _
  exact EtaleFundamentalGroups.integralClosureStalkArrowIsoOfIsoOver
    (K := U.functionField) (L := W.left.functionField) z e
    (connectedPuncturedCoverGenericNormalizationIsoSpecIntegralClosure_hom_fromSpec
      R hpos W) Q

/-- Formal etaleness of the canonical prime-local map transports back to the
actual stalk map of the global relative normalization. -/
theorem
    connectedPuncturedCoverGenericNormalizationBoundaryStalk_formallyEtale
    (hpos : (1 : WithBot ℕ∞) ≤ ringKrullDim R)
    (W : FiniteEtale (Scheme.puncturedSpectrum R)) [IsConnected W] :
    let U := Scheme.puncturedSpectrum R
    let j : U ⟶ Spec (.of R) := Scheme.puncturedSpectrumInclusion R
    letI : Nonempty U :=
      Scheme.puncturedSpectrum_nonempty_of_one_le_ringKrullDim R hpos
    letI : IsOpenImmersion j := by
      dsimp only [j, Scheme.puncturedSpectrumInclusion]
      infer_instance
    letI : IsIntegral U := isIntegral_of_isOpenImmersion j
    letI : Algebra R U.functionField :=
      puncturedSpectrumFunctionFieldAlgebraOfPositiveDimension R hpos
    letI : IsFractionRing R U.functionField :=
      puncturedSpectrumFunctionField_isFractionRing_of_positiveDimension R hpos
    letI : IsIntegral W.left :=
      EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale W
    letI : Algebra U.functionField W.left.functionField :=
      EtaleFundamentalGroups.finiteEtaleFunctionFieldAlgebra W
    letI : Algebra R W.left.functionField :=
      ((algebraMap U.functionField W.left.functionField).comp
        (algebraMap R U.functionField)).toAlgebra
    letI : IsScalarTower R U.functionField W.left.functionField :=
      IsScalarTower.of_algebraMap_eq' rfl
    let C := integralClosure R W.left.functionField
    let g : Spec (.of W.left.functionField) ⟶ Spec (.of R) :=
      connectedCoverGenericComposite W ≫ j
    let z := g.fromNormalization
    let e : g.normalization ≅ Spec (.of C) :=
      connectedPuncturedCoverGenericNormalizationIsoSpecIntegralClosure
        R hpos W
    ∀ (Q : Ideal C), [Q.IsPrime] →
    let P := Q.under R
    letI : P.IsPrime := inferInstance
    letI : Q.LiesOver P := inferInstance
    letI := EtaleFundamentalGroups.localizationAtPrimeToExtensionAlgebra
      (K := U.functionField) (L := W.left.functionField) P
    letI := EtaleFundamentalGroups.localizationAtPrimeToExtension_isScalarTower
      (K := U.functionField) (L := W.left.functionField) P
    letI : Algebra (Localization.AtPrime P) (Localization.AtPrime Q) :=
      Localization.AtPrime.algebraOfLiesOver P Q
    let q := EtaleFundamentalGroups.localizedNormalizationPrime
      (K := U.functionField) (L := W.left.functionField) P Q
    letI : q.IsMaximal :=
      EtaleFundamentalGroups.localizedNormalizationPrime_isMaximal
        (K := U.functionField) (L := W.left.functionField) P Q
    (algebraMap (Localization.AtPrime P)
      (Localization.AtPrime q)).FormallyEtale →
      (z.stalkMap
        (e.inv (⟨Q, inferInstance⟩ : PrimeSpectrum C))).hom.FormallyEtale := by
  dsimp only
  let U := Scheme.puncturedSpectrum R
  let j : U ⟶ Spec (.of R) := Scheme.puncturedSpectrumInclusion R
  let : Nonempty U :=
    Scheme.puncturedSpectrum_nonempty_of_one_le_ringKrullDim R hpos
  let : IsOpenImmersion j := by
    dsimp only [j, Scheme.puncturedSpectrumInclusion]
    infer_instance
  let : IsIntegral U := isIntegral_of_isOpenImmersion j
  let : Algebra R U.functionField :=
    puncturedSpectrumFunctionFieldAlgebraOfPositiveDimension R hpos
  let : IsFractionRing R U.functionField :=
    puncturedSpectrumFunctionField_isFractionRing_of_positiveDimension R hpos
  let : IsIntegral W.left :=
    EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale W
  let : Algebra U.functionField W.left.functionField :=
    EtaleFundamentalGroups.finiteEtaleFunctionFieldAlgebra W
  let : Algebra R W.left.functionField :=
    ((algebraMap U.functionField W.left.functionField).comp
      (algebraMap R U.functionField)).toAlgebra
  let : IsScalarTower R U.functionField W.left.functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  intro Q _ hlocal
  exact
    (EtaleFundamentalGroups.RingHom.FormallyEtale.respectsIso.arrow_mk_iso_iff
      (connectedPuncturedCoverGenericNormalizationBoundaryStalkArrowIso
        R hpos W Q)).mpr hlocal

/-- If the canonical prime-local maps are formally etale at every prime over
the closed point, then the actual global normalization stalk maps are
formally etale at every point over the puncture's complement.  This is the
literal boundary input required by the global finite-etale criterion. -/
theorem
    connectedPuncturedCoverGenericNormalization_boundaryStalkMap_formallyEtale_of_primeLocalizations
    (hpos : (1 : WithBot ℕ∞) ≤ ringKrullDim R)
    (W : FiniteEtale (Scheme.puncturedSpectrum R)) [IsConnected W]
    (hlocal :
      let U := Scheme.puncturedSpectrum R
      let j : U ⟶ Spec (.of R) := Scheme.puncturedSpectrumInclusion R
      letI : Nonempty U :=
        Scheme.puncturedSpectrum_nonempty_of_one_le_ringKrullDim R hpos
      letI : IsOpenImmersion j := by
        dsimp only [j, Scheme.puncturedSpectrumInclusion]
        infer_instance
      letI : IsIntegral U := isIntegral_of_isOpenImmersion j
      letI : Algebra R U.functionField :=
        puncturedSpectrumFunctionFieldAlgebraOfPositiveDimension R hpos
      letI : IsFractionRing R U.functionField :=
        puncturedSpectrumFunctionField_isFractionRing_of_positiveDimension R hpos
      letI : IsIntegral W.left :=
        EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale W
      letI : Algebra U.functionField W.left.functionField :=
        EtaleFundamentalGroups.finiteEtaleFunctionFieldAlgebra W
      letI : Algebra R W.left.functionField :=
        ((algebraMap U.functionField W.left.functionField).comp
          (algebraMap R U.functionField)).toAlgebra
      letI : IsScalarTower R U.functionField W.left.functionField :=
        IsScalarTower.of_algebraMap_eq' rfl
      let C := integralClosure R W.left.functionField
      ∀ (Q : Ideal C), [Q.IsPrime] →
        Q.under R = maximalIdeal R →
        let P := Q.under R
        letI : P.IsPrime := inferInstance
        letI : Q.LiesOver P := inferInstance
        letI := EtaleFundamentalGroups.localizationAtPrimeToExtensionAlgebra
          (K := U.functionField) (L := W.left.functionField) P
        letI := EtaleFundamentalGroups.localizationAtPrimeToExtension_isScalarTower
          (K := U.functionField) (L := W.left.functionField) P
        letI : Algebra (Localization.AtPrime P) (Localization.AtPrime Q) :=
          Localization.AtPrime.algebraOfLiesOver P Q
        let q := EtaleFundamentalGroups.localizedNormalizationPrime
          (K := U.functionField) (L := W.left.functionField) P Q
        letI : q.IsMaximal :=
          EtaleFundamentalGroups.localizedNormalizationPrime_isMaximal
            (K := U.functionField) (L := W.left.functionField) P Q
        (algebraMap (Localization.AtPrime P)
          (Localization.AtPrime q)).FormallyEtale) :
    let U := Scheme.puncturedSpectrum R
    let j : U ⟶ Spec (.of R) := Scheme.puncturedSpectrumInclusion R
    letI : Nonempty U :=
      Scheme.puncturedSpectrum_nonempty_of_one_le_ringKrullDim R hpos
    letI : IsOpenImmersion j := by
      dsimp only [j, Scheme.puncturedSpectrumInclusion]
      infer_instance
    letI : IsIntegral U := isIntegral_of_isOpenImmersion j
    letI : Algebra R U.functionField :=
      puncturedSpectrumFunctionFieldAlgebraOfPositiveDimension R hpos
    letI : IsFractionRing R U.functionField :=
      puncturedSpectrumFunctionField_isFractionRing_of_positiveDimension R hpos
    letI : IsIntegral W.left :=
      EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale W
    letI : Algebra U.functionField W.left.functionField :=
      EtaleFundamentalGroups.finiteEtaleFunctionFieldAlgebra W
    letI : Algebra R W.left.functionField :=
      ((algebraMap U.functionField W.left.functionField).comp
        (algebraMap R U.functionField)).toAlgebra
    letI : IsScalarTower R U.functionField W.left.functionField :=
      IsScalarTower.of_algebraMap_eq' rfl
    let z := (connectedCoverGenericComposite W ≫ j).fromNormalization
    ∀ y : (connectedCoverGenericComposite W ≫ j).normalization,
      z y ∉ Scheme.puncturedSpectrumOpen R →
        (z.stalkMap y).hom.FormallyEtale := by
  dsimp only
  let U := Scheme.puncturedSpectrum R
  let j : U ⟶ Spec (.of R) := Scheme.puncturedSpectrumInclusion R
  let : Nonempty U :=
    Scheme.puncturedSpectrum_nonempty_of_one_le_ringKrullDim R hpos
  let : IsOpenImmersion j := by
    dsimp only [j, Scheme.puncturedSpectrumInclusion]
    infer_instance
  let : IsIntegral U := isIntegral_of_isOpenImmersion j
  let : Algebra R U.functionField :=
    puncturedSpectrumFunctionFieldAlgebraOfPositiveDimension R hpos
  let : IsFractionRing R U.functionField :=
    puncturedSpectrumFunctionField_isFractionRing_of_positiveDimension R hpos
  let : IsIntegral W.left :=
    EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale W
  let : Algebra U.functionField W.left.functionField :=
    EtaleFundamentalGroups.finiteEtaleFunctionFieldAlgebra W
  let : Algebra R W.left.functionField :=
    ((algebraMap U.functionField W.left.functionField).comp
      (algebraMap R U.functionField)).toAlgebra
  let : IsScalarTower R U.functionField W.left.functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  let C := integralClosure R W.left.functionField
  let g : Spec (.of W.left.functionField) ⟶ Spec (.of R) :=
    connectedCoverGenericComposite W ≫ j
  let z := g.fromNormalization
  let e : g.normalization ≅ Spec (.of C) :=
    connectedPuncturedCoverGenericNormalizationIsoSpecIntegralClosure
      R hpos W
  intro y hy
  let p : PrimeSpectrum C := e.hom y
  let Q : Ideal C := p.asIdeal
  let : Q.IsPrime := p.isPrime
  have hzclosed : z y = closedPoint R := by
    by_contra hne
    exact hy ((Scheme.mem_puncturedSpectrumOpen_iff R (z y)).2 hne)
  have hzSpec :
      Spec.map (CommRingCat.ofHom (algebraMap R C)) p = z y := by
    change (Spec.map (CommRingCat.ofHom (algebraMap R C))) (e.hom y) = z y
    rw [← Scheme.Hom.comp_apply,
      connectedPuncturedCoverGenericNormalizationIsoSpecIntegralClosure_hom_fromSpec
        R hpos W]
  have hQmax : Q.under R = maximalIdeal R := by
    have hpclosed :
        Spec.map (CommRingCat.ofHom (algebraMap R C)) p =
          closedPoint R := hzSpec.trans hzclosed
    have hideal := PrimeSpectrum.ext_iff.mp hpclosed
    change Ideal.comap (algebraMap R C) p.asIdeal = maximalIdeal R at hideal
    simpa only [Q, Ideal.under_def] using hideal
  have hstalk :
      (z.stalkMap
        (e.inv (p : PrimeSpectrum C))).hom.FormallyEtale :=
    connectedPuncturedCoverGenericNormalizationBoundaryStalk_formallyEtale
      R hpos W Q (hlocal Q hQmax)
  have hePoint : e.inv p = y := by
    exact congr(($(e.hom_inv_id).base y))
  exact
    (EtaleFundamentalGroups.RingHom.FormallyEtale.respectsIso.arrow_mk_iso_iff
      (z.arrowStalkMapIsoOfEq hePoint)).mp hstalk

/-- Prime-local formal etaleness over the closed point makes the canonical
global relative normalization finite etale.  This closes the path from the
literal local integral-closure calculation to the global normalization used
to extend the connected punctured cover. -/
theorem
    connectedPuncturedCoverGenericNormalization_isFiniteEtale_of_primeLocalizations
    (hpos : (1 : WithBot ℕ∞) ≤ ringKrullDim R)
    (W : FiniteEtale (Scheme.puncturedSpectrum R)) [IsConnected W]
    (hlocal :
      let U := Scheme.puncturedSpectrum R
      let j : U ⟶ Spec (.of R) := Scheme.puncturedSpectrumInclusion R
      letI : Nonempty U :=
        Scheme.puncturedSpectrum_nonempty_of_one_le_ringKrullDim R hpos
      letI : IsOpenImmersion j := by
        dsimp only [j, Scheme.puncturedSpectrumInclusion]
        infer_instance
      letI : IsIntegral U := isIntegral_of_isOpenImmersion j
      letI : Algebra R U.functionField :=
        puncturedSpectrumFunctionFieldAlgebraOfPositiveDimension R hpos
      letI : IsFractionRing R U.functionField :=
        puncturedSpectrumFunctionField_isFractionRing_of_positiveDimension R hpos
      letI : IsIntegral W.left :=
        EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale W
      letI : Algebra U.functionField W.left.functionField :=
        EtaleFundamentalGroups.finiteEtaleFunctionFieldAlgebra W
      letI : Algebra R W.left.functionField :=
        ((algebraMap U.functionField W.left.functionField).comp
          (algebraMap R U.functionField)).toAlgebra
      letI : IsScalarTower R U.functionField W.left.functionField :=
        IsScalarTower.of_algebraMap_eq' rfl
      let C := integralClosure R W.left.functionField
      ∀ (Q : Ideal C), [Q.IsPrime] →
        Q.under R = maximalIdeal R →
        let P := Q.under R
        letI : P.IsPrime := inferInstance
        letI : Q.LiesOver P := inferInstance
        letI := EtaleFundamentalGroups.localizationAtPrimeToExtensionAlgebra
          (K := U.functionField) (L := W.left.functionField) P
        letI := EtaleFundamentalGroups.localizationAtPrimeToExtension_isScalarTower
          (K := U.functionField) (L := W.left.functionField) P
        letI : Algebra (Localization.AtPrime P) (Localization.AtPrime Q) :=
          Localization.AtPrime.algebraOfLiesOver P Q
        let q := EtaleFundamentalGroups.localizedNormalizationPrime
          (K := U.functionField) (L := W.left.functionField) P Q
        letI : q.IsMaximal :=
          EtaleFundamentalGroups.localizedNormalizationPrime_isMaximal
            (K := U.functionField) (L := W.left.functionField) P Q
        (algebraMap (Localization.AtPrime P)
          (Localization.AtPrime q)).FormallyEtale) :
    let U := Scheme.puncturedSpectrum R
    let j : U ⟶ Spec (.of R) := Scheme.puncturedSpectrumInclusion R
    letI : Nonempty U :=
      Scheme.puncturedSpectrum_nonempty_of_one_le_ringKrullDim R hpos
    letI : IsOpenImmersion j := by
      dsimp only [j, Scheme.puncturedSpectrumInclusion]
      infer_instance
    letI : IsIntegral U := isIntegral_of_isOpenImmersion j
    letI : Algebra R U.functionField :=
      puncturedSpectrumFunctionFieldAlgebraOfPositiveDimension R hpos
    letI : IsFractionRing R U.functionField :=
      puncturedSpectrumFunctionField_isFractionRing_of_positiveDimension R hpos
    letI : IsIntegral W.left :=
      EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale W
    letI : Algebra U.functionField W.left.functionField :=
      EtaleFundamentalGroups.finiteEtaleFunctionFieldAlgebra W
    letI : Algebra R W.left.functionField :=
      ((algebraMap U.functionField W.left.functionField).comp
        (algebraMap R U.functionField)).toAlgebra
    letI : IsScalarTower R U.functionField W.left.functionField :=
      IsScalarTower.of_algebraMap_eq' rfl
    IsFiniteEtale
      (connectedCoverGenericComposite W ≫ j).fromNormalization := by
  dsimp only
  let U := Scheme.puncturedSpectrum R
  let j : U ⟶ Spec (.of R) := Scheme.puncturedSpectrumInclusion R
  let : Nonempty U :=
    Scheme.puncturedSpectrum_nonempty_of_one_le_ringKrullDim R hpos
  let : IsOpenImmersion j := by
    dsimp only [j, Scheme.puncturedSpectrumInclusion]
    infer_instance
  let : IsIntegral U := isIntegral_of_isOpenImmersion j
  let : Algebra R U.functionField :=
    puncturedSpectrumFunctionFieldAlgebraOfPositiveDimension R hpos
  let : IsFractionRing R U.functionField :=
    puncturedSpectrumFunctionField_isFractionRing_of_positiveDimension R hpos
  let : IsIntegral W.left :=
    EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale W
  let : Algebra U.functionField W.left.functionField :=
    EtaleFundamentalGroups.finiteEtaleFunctionFieldAlgebra W
  let : Algebra R W.left.functionField :=
    ((algebraMap U.functionField W.left.functionField).comp
      (algebraMap R U.functionField)).toAlgebra
  let : IsScalarTower R U.functionField W.left.functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  exact
    connectedPuncturedCoverGenericNormalization_isFiniteEtale_of_boundary_stalkMap_formallyEtale
      R hpos W
      (
connectedPuncturedCoverGenericNormalization_boundaryStalkMap_formallyEtale_of_primeLocalizations
        R hpos W hlocal)

end AlgebraicGeometry.FiniteEtale

end
