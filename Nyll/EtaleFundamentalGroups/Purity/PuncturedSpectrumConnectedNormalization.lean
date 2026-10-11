/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.StalkFunctionFieldNormalization
import Nyll.EtaleFundamentalGroups.Purity.PuncturedSpectrumNormalizationFinite
import Nyll.EtaleFundamentalGroups.Purity.SpecialLocal.DimensionTwo.IntegralClosure.Local
import Nyll.EtaleFundamentalGroups.LocalGeometry.RegularLocal.DimensionTwoIntegrallyClosed

/-!
# Connected normalizations across a punctured spectrum

This file isolates the connected part of the normalization construction for
a finite-etale cover of a punctured two-dimensional regular local spectrum.
The cover supplies a finite separable function-field extension, and its
stalks supply the codimension-one etaleness input for local purity.
-/

noncomputable section

open CategoryTheory Limits TopologicalSpace
open CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.FiniteEtale

universe u

variable (R : Type u) [CommRing R] [IsDomain R] [IsRegularLocalRing R]

private theorem puncturedSpectrum_nonempty
    (hdim : ringKrullDim R = ((2 : ℕ∞) : WithBot ℕ∞)) :
    Nonempty (Scheme.puncturedSpectrum R) := by
  apply Scheme.puncturedSpectrum_nonempty_of_one_le_ringKrullDim R
  rw [hdim]
  norm_num

private noncomputable def puncturedSpectrumFunctionFieldRingEquiv
    (hdim : ringKrullDim R = ((2 : ℕ∞) : WithBot ℕ∞)) :
  let X := Spec (.of R)
  let U := Scheme.puncturedSpectrum R
  let j : U ⟶ X := Scheme.puncturedSpectrumInclusion R
  letI : Nonempty U := puncturedSpectrum_nonempty R hdim
  letI : IsIntegral X := inferInstance
  letI : IsOpenImmersion j := by
    dsimp only [j, Scheme.puncturedSpectrumInclusion]
    infer_instance
  letI : IsIntegral U := isIntegral_of_isOpenImmersion j
  X.functionField ≃+* U.functionField := by
    dsimp only
    let X := Spec (.of R)
    let U := Scheme.puncturedSpectrum R
    let j : U ⟶ X := Scheme.puncturedSpectrumInclusion R
    letI : Nonempty U := puncturedSpectrum_nonempty R hdim
    letI : IsIntegral X := inferInstance
    letI : IsOpenImmersion j := by
      dsimp only [j, Scheme.puncturedSpectrumInclusion]
      infer_instance
    letI : IsIntegral U := isIntegral_of_isOpenImmersion j
    change X.functionField ≃+* U.functionField
    let h : j (genericPoint U) = genericPoint X :=
      genericPoint_eq_of_isOpenImmersion j
    let e : X.functionField ≅ U.functionField :=
      X.presheaf.stalkCongr (.of_eq h.symm) ≪≫
        asIso (j.stalkMap (genericPoint U))
    exact e.commRingCatIsoToRingEquiv

/-- The fraction-field structure on the function field of the punctured
spectrum induced from the full local spectrum. -/
@[reducible] noncomputable def puncturedSpectrumFunctionFieldAlgebra
    (hdim : ringKrullDim R = ((2 : ℕ∞) : WithBot ℕ∞)) :
    let U := Scheme.puncturedSpectrum R
    letI : Nonempty U := puncturedSpectrum_nonempty R hdim
    letI : IsOpenImmersion (Scheme.puncturedSpectrumInclusion R) := by
      dsimp only [Scheme.puncturedSpectrumInclusion]
      infer_instance
    letI : IsIntegral U := by
      apply isIntegral_of_isOpenImmersion (Scheme.puncturedSpectrumInclusion R)
    letI : Algebra R (Spec (.of R)).functionField :=
      AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (.of R)
    Algebra R U.functionField :=
  by
    dsimp only
    let X := Spec (.of R)
    let U := Scheme.puncturedSpectrum R
    letI : Nonempty U := puncturedSpectrum_nonempty R hdim
    letI : IsOpenImmersion (Scheme.puncturedSpectrumInclusion R) := by
      dsimp only [Scheme.puncturedSpectrumInclusion]
      infer_instance
    letI : IsIntegral U :=
      isIntegral_of_isOpenImmersion (Scheme.puncturedSpectrumInclusion R)
    letI : Algebra R X.functionField :=
      AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (.of R)
    exact ((puncturedSpectrumFunctionFieldRingEquiv R hdim).toRingHom.comp
      (algebraMap R X.functionField)).toAlgebra

private noncomputable def puncturedSpectrumFunctionFieldAlgEquiv
    (hdim : ringKrullDim R = ((2 : ℕ∞) : WithBot ℕ∞)) :
    let U := Scheme.puncturedSpectrum R
    letI : Nonempty U := puncturedSpectrum_nonempty R hdim
    letI : IsOpenImmersion (Scheme.puncturedSpectrumInclusion R) := by
      dsimp only [Scheme.puncturedSpectrumInclusion]
      infer_instance
    letI : IsIntegral U := by
      apply isIntegral_of_isOpenImmersion (Scheme.puncturedSpectrumInclusion R)
    letI : Algebra R (Spec (.of R)).functionField :=
      AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (.of R)
    letI := puncturedSpectrumFunctionFieldAlgebra R hdim
    (Spec (.of R)).functionField ≃ₐ[R]
      U.functionField :=
  by
    dsimp only
    let X := Spec (.of R)
    let U := Scheme.puncturedSpectrum R
    letI : Nonempty U := puncturedSpectrum_nonempty R hdim
    letI : IsOpenImmersion (Scheme.puncturedSpectrumInclusion R) := by
      dsimp only [Scheme.puncturedSpectrumInclusion]
      infer_instance
    letI : IsIntegral U :=
      isIntegral_of_isOpenImmersion (Scheme.puncturedSpectrumInclusion R)
    letI : Algebra R X.functionField :=
      AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (.of R)
    letI : Algebra R U.functionField :=
      puncturedSpectrumFunctionFieldAlgebra R hdim
    exact
      { puncturedSpectrumFunctionFieldRingEquiv R hdim with
        commutes' := fun _ ↦ rfl }

theorem puncturedSpectrumFunctionField_isFractionRing
    (hdim : ringKrullDim R = ((2 : ℕ∞) : WithBot ℕ∞)) :
    let U := Scheme.puncturedSpectrum R
    letI : Nonempty U := puncturedSpectrum_nonempty R hdim
    letI : IsOpenImmersion (Scheme.puncturedSpectrumInclusion R) := by
      dsimp only [Scheme.puncturedSpectrumInclusion]
      infer_instance
    letI : IsIntegral U := by
      apply isIntegral_of_isOpenImmersion (Scheme.puncturedSpectrumInclusion R)
    letI : Algebra R (Spec (.of R)).functionField :=
      AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (.of R)
    letI := puncturedSpectrumFunctionFieldAlgebra R hdim
    IsFractionRing R U.functionField := by
  let U := Scheme.puncturedSpectrum R
  let : Nonempty U := puncturedSpectrum_nonempty R hdim
  let : IsOpenImmersion (Scheme.puncturedSpectrumInclusion R) := by
    dsimp only [Scheme.puncturedSpectrumInclusion]
    infer_instance
  let : IsIntegral U := by
    apply isIntegral_of_isOpenImmersion (Scheme.puncturedSpectrumInclusion R)
  let : Algebra R (Spec (.of R)).functionField :=
    AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (.of R)
  let := puncturedSpectrumFunctionFieldAlgebra R hdim
  let : IsFractionRing R (Spec (.of R)).functionField :=
    AlgebraicGeometry.functionField_isFractionRing_of_affine (.of R)
  exact IsFractionRing.of_algEquiv
    (puncturedSpectrumFunctionFieldAlgEquiv R hdim)

/-- At a height-one prime of the local base, the normalization in the
function field of a connected punctured cover is etale. -/
theorem connectedPuncturedCover_localIntegralClosure_etale
    (hdim : ringKrullDim R = ((2 : ℕ∞) : WithBot ℕ∞))
    (W : FiniteEtale (Scheme.puncturedSpectrum R)) [IsConnected W]
    (q : Ideal R) [q.IsPrime] (hq : q.height = 1) :
    let U := Scheme.puncturedSpectrum R
    letI : IsIntegrallyClosed R :=
      (open _root_.EtaleFundamentalGroups.SpecialLocalPurity in
        isIntegrallyClosed_of_isRegularLocalRing_dimension_two hdim)
    letI : Nonempty U := puncturedSpectrum_nonempty R hdim
    letI : IsOpenImmersion (Scheme.puncturedSpectrumInclusion R) := by
      dsimp only [Scheme.puncturedSpectrumInclusion]
      infer_instance
    letI : IsIntegral U :=
      isIntegral_of_isOpenImmersion (Scheme.puncturedSpectrumInclusion R)
    letI : IsNormalIntegral U := inferInstance
    letI : IsLocallyNoetherian U := inferInstance
    letI : Algebra R U.functionField :=
      puncturedSpectrumFunctionFieldAlgebra R hdim
    letI : IsFractionRing R U.functionField :=
      puncturedSpectrumFunctionField_isFractionRing R hdim
    letI : IsIntegral W.left :=
      EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale W
    letI : Algebra U.functionField W.left.functionField :=
      EtaleFundamentalGroups.finiteEtaleFunctionFieldAlgebra W
    letI : Algebra R W.left.functionField :=
      ((algebraMap U.functionField W.left.functionField).comp
        (algebraMap R U.functionField)).toAlgebra
    letI : IsScalarTower R U.functionField W.left.functionField :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI : FiniteDimensional U.functionField W.left.functionField :=
      EtaleFundamentalGroups.finiteDimensional_functionField_of_finiteEtale_isConnected W
    letI : Algebra.IsSeparable U.functionField W.left.functionField :=
      EtaleFundamentalGroups.isSeparable_functionField_of_finiteEtale_isConnected W
    letI := EtaleFundamentalGroups.localizationAtPrimeToExtensionAlgebra
      (K := U.functionField)
      (L := W.left.functionField) q
    Algebra.Etale (Localization.AtPrime q)
      (integralClosure (Localization.AtPrime q) W.left.functionField) := by
  dsimp only
  let U := Scheme.puncturedSpectrum R
  let : IsIntegrallyClosed R :=
    EtaleFundamentalGroups.SpecialLocalPurity.isIntegrallyClosed_of_isRegularLocalRing_dimension_two
      hdim
  let : Nonempty U := puncturedSpectrum_nonempty R hdim
  let : IsOpenImmersion (Scheme.puncturedSpectrumInclusion R) := by
    dsimp only [Scheme.puncturedSpectrumInclusion]
    infer_instance
  let : IsIntegral U :=
    isIntegral_of_isOpenImmersion (Scheme.puncturedSpectrumInclusion R)
  let : IsNormalIntegral U := inferInstance
  let : IsLocallyNoetherian U := inferInstance
  let X := Spec (.of R)
  let : Algebra R X.functionField :=
    AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (.of R)
  let K : Type u := U.functionField
  let : Algebra R K := puncturedSpectrumFunctionFieldAlgebra R hdim
  let : IsFractionRing R K :=
    puncturedSpectrumFunctionField_isFractionRing R hdim
  let : IsIntegral W.left :=
    EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale W
  let L : Type u := W.left.functionField
  let : Algebra K L :=
    EtaleFundamentalGroups.finiteEtaleFunctionFieldAlgebra W
  let : Algebra R L :=
    ((algebraMap K L).comp (algebraMap R K)).toAlgebra
  let : IsScalarTower R K L := IsScalarTower.of_algebraMap_eq' rfl
  let : FiniteDimensional K L :=
    EtaleFundamentalGroups.finiteDimensional_functionField_of_finiteEtale_isConnected W
  let : Algebra.IsSeparable K L :=
    EtaleFundamentalGroups.isSeparable_functionField_of_finiteEtale_isConnected W
  let : Algebra (Localization.AtPrime q) L :=
    EtaleFundamentalGroups.localizationAtPrimeToExtensionAlgebra
      (K := K) (L := L) q
  let : IsScalarTower R (Localization.AtPrime q) L :=
    EtaleFundamentalGroups.localizationAtPrimeToExtension_isScalarTower
      (K := K) (L := L) q
  have hmax : (IsLocalRing.maximalIdeal R).height = (2 : ℕ∞) := by
    have hcast :
        (((IsLocalRing.maximalIdeal R).height : ℕ∞) : WithBot ℕ∞) =
          ((2 : ℕ∞) : WithBot ℕ∞) := by
      rw [IsLocalRing.maximalIdeal_height_eq_ringKrullDim, hdim]
    exact WithBot.coe_eq_coe.mp hcast
  have hqmax : q ≠ IsLocalRing.maximalIdeal R := by
    intro h
    subst q
    rw [hmax] at hq
    norm_num at hq
  let p : PrimeSpectrum R := ⟨q, inferInstance⟩
  have hp : p ≠ IsLocalRing.closedPoint (CommRingCat.of R) := by
    intro h
    apply hqmax
    exact congrArg PrimeSpectrum.asIdeal h
  let x : U :=
    ⟨p, (Scheme.mem_puncturedSpectrumOpen_iff R p).2 hp⟩
  let stalkAlg : Algebra (U.presheaf.stalk x) L :=
    U.stalkExtensionAlgebra x L
  let : Algebra (U.presheaf.stalk x) L := stalkAlg
  have hstalk : Algebra.Etale (U.presheaf.stalk x)
      (integralClosure (U.presheaf.stalk x) L) :=
    EtaleFundamentalGroups.integralClosure_functionField_etale_on_stalk_of_finiteEtale_isConnected
      W x
  let eCat : U.presheaf.stalk x ≅
      CommRingCat.of (Localization.AtPrime q) :=
    (Scheme.puncturedSpectrumOpen R).stalkIso x ≪≫
      Spec.stalkIso (.of R) p
  let e : Localization.AtPrime q ≃+* U.presheaf.stalk x :=
    eCat.symm.commRingCatIsoToRingEquiv
  have he : (algebraMap (U.presheaf.stalk x) L).comp e.toRingHom =
      algebraMap (Localization.AtPrime q) L := by
    apply IsLocalization.ringHom_ext q.primeCompl
    ext r
    simp only [RingHom.comp_apply]
    rw [← IsScalarTower.algebraMap_apply R (Localization.AtPrime q) L r]
    change algebraMap K L
        (algebraMap (U.presheaf.stalk x) K
          (e (algebraMap R (Localization.AtPrime q) r))) =
      algebraMap K L (algebraMap R K r)
    congr 1
    change algebraMap (U.presheaf.stalk x) K
        (((Scheme.puncturedSpectrumOpen R).stalkIso x).inv
          ((Spec.stalkIso (.of R) p).inv
            (algebraMap R (Localization.AtPrime q) r))) =
      algebraMap R K r
    rw [Scheme.Opens.stalkIso_inv]
    let j : U ⟶ Spec (.of R) := Scheme.puncturedSpectrumInclusion R
    let hg := (genericPoint_spec U).specializes (show x ∈ Set.univ by trivial)
    change U.presheaf.stalkSpecializes hg
        (j.stalkMap x
          ((Spec.stalkIso (.of R) p).inv
            (algebraMap R (Localization.AtPrime q) r))) =
      (puncturedSpectrumFunctionFieldRingEquiv R hdim)
        (algebraMap R (Spec (.of R)).functionField r)
    refine (j.stalkSpecializes_stalkMap_apply
      (genericPoint U) x hg
      ((Spec.stalkIso (.of R) p).inv
        (algebraMap R (Localization.AtPrime q) r))).symm.trans ?_
    have hspec :
        (Spec.stalkIso (.of R) p).inv
            (algebraMap R (Localization.AtPrime q) r) =
          (Spec (.of R)).presheaf.germ ⊤ p trivial
            ((Scheme.ΓSpecIso (.of R)).inv r) := by
      have h := congrArg
        (fun f : CommRingCat.of R ⟶
            (Spec (.of R)).presheaf.stalk p ↦ f r)
        (Spec.algebraMap_stalkIso_inv (R := CommRingCat.of R) p)
      simpa [ConcreteCategory.comp_apply] using h
    rw [hspec]
    change j.stalkMap (genericPoint U)
        ((Spec (.of R)).presheaf.stalkSpecializes
          (j.base.hom.map_specializes hg)
          ((Spec (.of R)).presheaf.germ ⊤ (j x) trivial
            ((Scheme.ΓSpecIso (.of R)).inv r))) =
      (puncturedSpectrumFunctionFieldRingEquiv R hdim)
        (algebraMap R (Spec (.of R)).functionField r)
    have hgerm := DFunLike.congr_fun
      (CommRingCat.hom_ext_iff.mp
        ((Spec (.of R)).presheaf.germ_stalkSpecializes
          (show j x ∈ (⊤ : (Spec (.of R)).Opens) by trivial)
          (j.base.hom.map_specializes hg)))
      ((Scheme.ΓSpecIso (.of R)).inv r)
    have hgerm' :
        (Spec (.of R)).presheaf.stalkSpecializes
            (j.base.hom.map_specializes hg)
            ((Spec (.of R)).presheaf.germ ⊤ (j x) trivial
              ((Scheme.ΓSpecIso (.of R)).inv r)) =
          (Spec (.of R)).presheaf.germ ⊤ (j (genericPoint U)) trivial
            ((Scheme.ΓSpecIso (.of R)).inv r) := by
      change (CommRingCat.Hom.hom
          ((Spec (.of R)).presheaf.germ ⊤ (j x) trivial ≫
            (Spec (.of R)).presheaf.stalkSpecializes
              (j.base.hom.map_specializes hg)))
          ((Scheme.ΓSpecIso (.of R)).inv r) = _
      exact hgerm
    rw [hgerm']
    let : Nonempty (⊤ : (Spec (.of R)).Opens) :=
      ⟨⟨genericPoint (Spec (.of R)), trivial⟩⟩
    let hgen : j (genericPoint U) = genericPoint (Spec (.of R)) :=
      genericPoint_eq_of_isOpenImmersion j
    change j.stalkMap (genericPoint U)
        ((Spec (.of R)).presheaf.germ ⊤ (j (genericPoint U)) trivial
          ((Scheme.ΓSpecIso (.of R)).inv r)) =
      (puncturedSpectrumFunctionFieldRingEquiv R hdim)
        ((Spec (.of R)).germToFunctionField ⊤
          ((Scheme.ΓSpecIso (.of R)).inv r))
    change j.stalkMap (genericPoint U)
        ((Spec (.of R)).presheaf.germ ⊤ (j (genericPoint U)) trivial
          ((Scheme.ΓSpecIso (.of R)).inv r)) =
      j.stalkMap (genericPoint U)
        ((Spec (.of R)).presheaf.stalkSpecializes
          (Inseparable.of_eq hgen.symm).ge
          ((Spec (.of R)).presheaf.germ ⊤
            (genericPoint (Spec (.of R))) trivial
            ((Scheme.ΓSpecIso (.of R)).inv r)))
    congr 1
    have hgeneric := DFunLike.congr_fun
      (CommRingCat.hom_ext_iff.mp
        ((Spec (.of R)).presheaf.germ_stalkSpecializes
          (show genericPoint (Spec (.of R)) ∈
            (⊤ : (Spec (.of R)).Opens) by trivial)
          (Inseparable.of_eq hgen.symm).ge))
      ((Scheme.ΓSpecIso (.of R)).inv r)
    symm
    change (CommRingCat.Hom.hom
        ((Spec (.of R)).presheaf.germ ⊤
            (genericPoint (Spec (.of R))) trivial ≫
          (Spec (.of R)).presheaf.stalkSpecializes
            (Inseparable.of_eq hgen.symm).ge))
        ((Scheme.ΓSpecIso (.of R)).inv r) = _
    exact hgeneric
  exact EtaleFundamentalGroups.integralClosure_etale_of_baseRingEquiv
    e he hstalk

/-- The integral closure of a two-dimensional regular local domain in the
function field of a connected finite-etale cover of its punctured spectrum
is etale over the local domain. -/
theorem connectedPuncturedCover_integralClosure_etale
    (hdim : ringKrullDim R = ((2 : ℕ∞) : WithBot ℕ∞))
    (W : FiniteEtale (Scheme.puncturedSpectrum R)) [IsConnected W] :
    let U := Scheme.puncturedSpectrum R
    letI : IsIntegrallyClosed R :=
      (open _root_.EtaleFundamentalGroups.SpecialLocalPurity in
        isIntegrallyClosed_of_isRegularLocalRing_dimension_two hdim)
    letI : Nonempty U := puncturedSpectrum_nonempty R hdim
    letI : IsOpenImmersion (Scheme.puncturedSpectrumInclusion R) := by
      dsimp only [Scheme.puncturedSpectrumInclusion]
      infer_instance
    letI : IsIntegral U :=
      isIntegral_of_isOpenImmersion (Scheme.puncturedSpectrumInclusion R)
    letI : IsNormalIntegral U := inferInstance
    letI : IsLocallyNoetherian U := inferInstance
    letI : Algebra R U.functionField :=
      puncturedSpectrumFunctionFieldAlgebra R hdim
    letI : IsFractionRing R U.functionField :=
      puncturedSpectrumFunctionField_isFractionRing R hdim
    letI : IsIntegral W.left :=
      EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale W
    letI : Algebra U.functionField W.left.functionField :=
      EtaleFundamentalGroups.finiteEtaleFunctionFieldAlgebra W
    letI : Algebra R W.left.functionField :=
      ((algebraMap U.functionField W.left.functionField).comp
        (algebraMap R U.functionField)).toAlgebra
    letI : IsScalarTower R U.functionField W.left.functionField :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI : FiniteDimensional U.functionField W.left.functionField :=
      EtaleFundamentalGroups.finiteDimensional_functionField_of_finiteEtale_isConnected W
    letI : Algebra.IsSeparable U.functionField W.left.functionField :=
      EtaleFundamentalGroups.isSeparable_functionField_of_finiteEtale_isConnected W
    Algebra.Etale R (integralClosure R W.left.functionField) := by
  dsimp only
  let U := Scheme.puncturedSpectrum R
  let : IsIntegrallyClosed R :=
    EtaleFundamentalGroups.SpecialLocalPurity.isIntegrallyClosed_of_isRegularLocalRing_dimension_two
      hdim
  let : Nonempty U := puncturedSpectrum_nonempty R hdim
  let : IsOpenImmersion (Scheme.puncturedSpectrumInclusion R) := by
    dsimp only [Scheme.puncturedSpectrumInclusion]
    infer_instance
  let : IsIntegral U :=
    isIntegral_of_isOpenImmersion (Scheme.puncturedSpectrumInclusion R)
  let : IsNormalIntegral U := inferInstance
  let : IsLocallyNoetherian U := inferInstance
  let K : Type u := U.functionField
  let : Algebra R K := puncturedSpectrumFunctionFieldAlgebra R hdim
  let : IsFractionRing R K :=
    puncturedSpectrumFunctionField_isFractionRing R hdim
  let : IsIntegral W.left :=
    EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale W
  let L : Type u := W.left.functionField
  let : Algebra K L :=
    EtaleFundamentalGroups.finiteEtaleFunctionFieldAlgebra W
  let : Algebra R L :=
    ((algebraMap K L).comp (algebraMap R K)).toAlgebra
  let : IsScalarTower R K L := IsScalarTower.of_algebraMap_eq' rfl
  let : FiniteDimensional K L :=
    EtaleFundamentalGroups.finiteDimensional_functionField_of_finiteEtale_isConnected W
  let : Algebra.IsSeparable K L :=
    EtaleFundamentalGroups.isSeparable_functionField_of_finiteEtale_isConnected W
  apply
    (open _root_.EtaleFundamentalGroups.SpecialLocalPurity in
      integralClosure_etale_of_isRegularLocalRing_dimension_two (K := K) hdim)
  intro q _ hq
  exact
    EtaleFundamentalGroups.localization_integralClosure_etale_of_local_integralClosure_etale
      (K := K) (L := L) q
      (connectedPuncturedCover_localIntegralClosure_etale R hdim W q hq)

/-- The function-field normalization attached to a connected finite-etale
cover of a punctured two-dimensional regular local spectrum, packaged as an
actual finite-etale cover of the full spectrum. -/
noncomputable def connectedPuncturedCoverIntegralClosureExtension
    (hdim : ringKrullDim R = ((2 : ℕ∞) : WithBot ℕ∞))
    (W : FiniteEtale (Scheme.puncturedSpectrum R)) [IsConnected W] :
    FiniteEtale (Spec (.of R)) := by
  let U := Scheme.puncturedSpectrum R
  letI : IsIntegrallyClosed R :=
    EtaleFundamentalGroups.SpecialLocalPurity.isIntegrallyClosed_of_isRegularLocalRing_dimension_two
      hdim
  letI : Nonempty U := puncturedSpectrum_nonempty R hdim
  letI : IsOpenImmersion (Scheme.puncturedSpectrumInclusion R) := by
    dsimp only [Scheme.puncturedSpectrumInclusion]
    infer_instance
  letI : IsIntegral U :=
    isIntegral_of_isOpenImmersion (Scheme.puncturedSpectrumInclusion R)
  letI : IsNormalIntegral U := inferInstance
  letI : IsLocallyNoetherian U := inferInstance
  let K : Type u := U.functionField
  letI : Algebra R K := puncturedSpectrumFunctionFieldAlgebra R hdim
  letI : IsFractionRing R K :=
    puncturedSpectrumFunctionField_isFractionRing R hdim
  letI : IsIntegral W.left :=
    EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale W
  let L : Type u := W.left.functionField
  letI : Algebra K L :=
    EtaleFundamentalGroups.finiteEtaleFunctionFieldAlgebra W
  letI : Algebra R L :=
    ((algebraMap K L).comp (algebraMap R K)).toAlgebra
  letI : IsScalarTower R K L := IsScalarTower.of_algebraMap_eq' rfl
  letI : FiniteDimensional K L :=
    EtaleFundamentalGroups.finiteDimensional_functionField_of_finiteEtale_isConnected W
  letI : Algebra.IsSeparable K L :=
    EtaleFundamentalGroups.isSeparable_functionField_of_finiteEtale_isConnected W
  let C := integralClosure R L
  have hEtale : Algebra.Etale R C :=
    connectedPuncturedCover_integralClosure_etale R hdim W
  letI : Algebra.Etale R C := hEtale
  letI : Module.Finite R C :=
    IsIntegralClosure.finite R K L C
  let f : Spec (.of C) ⟶ Spec (.of R) :=
    Spec.map (CommRingCat.ofHom (algebraMap R C))
  have hf : IsFiniteEtale f := by
    dsimp only [f]
    rw [IsFiniteEtale.SpecMap_iff]
    change (algebraMap R C).FiniteEtale
    rw [RingHom.finiteEtale_algebraMap_iff,
      Algebra.finiteEtale_iff]
    exact ⟨inferInstance, inferInstance⟩
  exact @FiniteEtale.mk (Spec (.of R)) _ f hf

end AlgebraicGeometry.FiniteEtale
