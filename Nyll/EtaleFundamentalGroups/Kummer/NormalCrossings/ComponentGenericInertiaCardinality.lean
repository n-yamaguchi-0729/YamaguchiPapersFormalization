/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Ramification.BaseChange.Equiv
import Nyll.EtaleFundamentalGroups.Kummer.NormalCrossings.SurjectiveComponentInertiaCoprimality
import Nyll.EtaleFundamentalGroups.Inertia.Localized.NormalCardinality
import Nyll.EtaleFundamentalGroups.Normalization.Branch.GaloisRamification.AtLargerPrime
import Nyll.EtaleFundamentalGroups.Normalization.IntegralClosure.BaseRingEquiv
import Mathlib.RingTheory.Spectrum.Prime.Defs

/-!
# Inertia cardinality at a fixed boundary component

The branch prime attached to a component at any of its specializations has
the component generic stalk as its prime localization.  This identifies the
ramification index seen in every specialized stalk with one fixed index at
the component generic point.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme

universe u

/-- The canonical identification of a generization stalk with the
corresponding prime localization. -/
noncomputable def stalkSpecializationEquivLocalization
    {X : Scheme.{u}} {x y : X} (hxy : x ⤳ y) :
    let : (specializationPrime hxy).asIdeal.IsPrime := (specializationPrime hxy).isPrime
    X.presheaf.stalk x ≃+*
      Localization.AtPrime (specializationPrime hxy).asIdeal := by
  intro hPPrime
  let hpoint : X.fromSpecStalk y (specializationPrime hxy) = x :=
    X.fromSpecStalk_specializationPrime hxy
  exact
    (X.presheaf.stalkCongr (.of_eq hpoint)).symm.commRingCatIsoToRingEquiv |>.trans
      (X.stalkFromSpecStalkEquivLocalization y (specializationPrime hxy))

/-- The canonical identification of a generization stalk with the
corresponding prime localization extends the generization map. -/
theorem stalkSpecializationEquivLocalization_comp_stalkSpecializes
    {X : Scheme.{u}} {x y : X} (hxy : x ⤳ y) :
    let : (specializationPrime hxy).asIdeal.IsPrime := (specializationPrime hxy).isPrime
    (stalkSpecializationEquivLocalization hxy).toRingHom.comp
        (X.presheaf.stalkSpecializes hxy).hom =
      algebraMap (X.presheaf.stalk y)
        (Localization.AtPrime (specializationPrime hxy).asIdeal) := by
  intro hPPrime
  apply RingHom.ext
  intro a
  simp only [stalkSpecializationEquivLocalization, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_ringHom_trans, Iso.commRingCatIsoToRingEquiv_toRingHom,
    Iso.symm_hom, TopCat.Presheaf.stalkCongr_inv, RingHom.coe_comp,
    RingHom.coe_coe, Function.comp_apply]
  set p : PrimeSpectrum (X.presheaf.stalk y) := specializationPrime hxy
  have hpoint : X.fromSpecStalk y p = x :=
    X.fromSpecStalk_specializationPrime hxy
  obtain ⟨U, hyU, s, hs⟩ := X.presheaf.exists_germ_eq a
  rw [← hs]
  have hxU : x ∈ U := hxy.mem_open U.2 hyU
  simp only [TopCat.Presheaf.germ_stalkSpecializes_apply]
  have hfromU : X.fromSpecStalk y p ∈ U := by
    rw [hpoint]
    exact hxU
  have htransport :
      (X.presheaf.stalkSpecializes
        (Inseparable.of_eq hpoint).le).hom
          (X.presheaf.germ U x hxU s) =
        X.presheaf.germ U
          (X.fromSpecStalk y p) hfromU s :=
    ConcreteCategory.congr_hom
      (X.presheaf.germ_stalkSpecializes hxU
        (Inseparable.of_eq hpoint).le) s
  rw [htransport]
  dsimp only [Scheme.stalkFromSpecStalkEquivLocalization]
  change
    (Spec.stalkIso (X.presheaf.stalk y) p).hom
        ((X.fromSpecStalk y).stalkMap p
          (X.presheaf.germ U
            (X.fromSpecStalk y p) hfromU s)) =
      algebraMap (X.presheaf.stalk y)
        (Localization.AtPrime p.asIdeal)
          (X.presheaf.germ U y hyU s)
  rw [Scheme.Hom.germ_stalkMap_apply]
  change
    ((X.fromSpecStalk y).app U ≫
      (Spec (X.presheaf.stalk y)).presheaf.germ
        (X.fromSpecStalk y ⁻¹ᵁ U) p hfromU ≫
      (Spec.stalkIso (X.presheaf.stalk y) p).hom) s = _
  have hres := (Spec (X.presheaf.stalk y)).presheaf.germ_res
    (homOfLE (show X.fromSpecStalk y ⁻¹ᵁ U ≤ ⊤ from le_top))
    (show Spec (X.presheaf.stalk y) from p) hfromU
  have hinner :
      (Spec (X.presheaf.stalk y)).presheaf.map (homOfLE le_top).op ≫
        ((Spec (X.presheaf.stalk y)).presheaf.germ
          (X.fromSpecStalk y ⁻¹ᵁ U) p hfromU ≫
          (Spec.stalkIso (X.presheaf.stalk y) p).hom) =
      (ΓSpecIso (X.presheaf.stalk y)).hom ≫
        CommRingCat.ofHom (algebraMap (X.presheaf.stalk y)
          (Localization.AtPrime p.asIdeal)) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ (Spec.stalkIso (X.presheaf.stalk y) p).hom) hres).trans
        (Spec.germ_stalkMapIso_hom (R := X.presheaf.stalk y) p))
  have hwhole :
      (X.fromSpecStalk y).app U ≫
        ((Spec (X.presheaf.stalk y)).presheaf.germ
          (X.fromSpecStalk y ⁻¹ᵁ U) p hfromU ≫
          (Spec.stalkIso (X.presheaf.stalk y) p).hom) =
      X.presheaf.germ U y hyU ≫ CommRingCat.ofHom
        (algebraMap (X.presheaf.stalk y) (Localization.AtPrime p.asIdeal)) := by
    rw [Scheme.fromSpecStalk_app hyU]
    simp only [Category.assoc]
    exact (congrArg (fun f => X.presheaf.germ U y hyU ≫
      (ΓSpecIso (X.presheaf.stalk y)).inv ≫ f) hinner).trans
        (congrArg (fun f => X.presheaf.germ U y hyU ≫ f)
          ((ΓSpecIso (X.presheaf.stalk y)).inv_hom_id_assoc
            (CommRingCat.ofHom (algebraMap (X.presheaf.stalk y)
              (Localization.AtPrime p.asIdeal)))))
  exact ConcreteCategory.congr_hom hwhole s

/-- A generization map of scheme stalks is the localization at the prime
represented by that generization. -/
theorem stalkSpecializes_isLocalization
    {X : Scheme.{u}} {x y : X} (hxy : x ⤳ y) :
    let : (specializationPrime hxy).asIdeal.IsPrime := (specializationPrime hxy).isPrime
    letI : Algebra (X.presheaf.stalk y) (X.presheaf.stalk x) :=
      (X.presheaf.stalkSpecializes hxy).hom.toAlgebra
    IsLocalization (specializationPrime hxy).asIdeal.primeCompl
      (X.presheaf.stalk x) := by
  intro hPPrime
  let : Algebra (X.presheaf.stalk y) (X.presheaf.stalk x) :=
    (X.presheaf.stalkSpecializes hxy).hom.toAlgebra
  let e := stalkSpecializationEquivLocalization hxy
  let eAlg : X.presheaf.stalk x ≃ₐ[X.presheaf.stalk y]
      Localization.AtPrime (specializationPrime hxy).asIdeal :=
    AlgEquiv.ofRingEquiv (f := e) fun r ↦ by
      exact DFunLike.congr_fun
        (stalkSpecializationEquivLocalization_comp_stalkSpecializes hxy) r
  exact IsLocalization.isLocalization_of_algEquiv
    (specializationPrime hxy).asIdeal.primeCompl eAlg.symm

/-- The maps from specialized and generization stalks to the function field
of an integral scheme commute with the generization map. -/
theorem stalkFunctionFieldAlgebra_comp_stalkSpecializes
    {X : Scheme.{u}} [IsIntegral X] {x y : X} (hxy : x ⤳ y) :
    (algebraMap (X.presheaf.stalk x) X.functionField).comp
        (X.presheaf.stalkSpecializes hxy).hom =
      algebraMap (X.presheaf.stalk y) X.functionField := by
  change
    (X.presheaf.stalkSpecializes (genericPoint_specializes x)).hom.comp
        (X.presheaf.stalkSpecializes hxy).hom =
      (X.presheaf.stalkSpecializes (genericPoint_specializes y)).hom
  rw [← CommRingCat.hom_comp]
  exact congrArg CommRingCat.Hom.hom
    (TopCat.Presheaf.stalkSpecializes_comp X.presheaf
      (genericPoint_specializes x) hxy)

/-- The maps from specialized and generization stalks to the function field
of an ideal-sheaf complement commute with the generization map. -/
theorem IdealSheafData.supportComplementFunctionFieldAlgebra_comp_stalkSpecializes
    {X : Scheme.{u}} [IsIntegral X] (I : X.IdealSheafData)
    [Nonempty I.supportComplement] {x y : X} (hxy : x ⤳ y) :
    letI : Algebra (X.presheaf.stalk x)
        (I.supportComplement : Scheme).functionField :=
      I.supportComplementFunctionFieldAlgebra x
    letI : Algebra (X.presheaf.stalk y)
        (I.supportComplement : Scheme).functionField :=
      I.supportComplementFunctionFieldAlgebra y
    (algebraMap (X.presheaf.stalk x)
        (I.supportComplement : Scheme).functionField).comp
          (X.presheaf.stalkSpecializes hxy).hom =
      algebraMap (X.presheaf.stalk y)
        (I.supportComplement : Scheme).functionField := by
  let : Algebra (X.presheaf.stalk x)
      (I.supportComplement : Scheme).functionField :=
    I.supportComplementFunctionFieldAlgebra x
  let : Algebra (X.presheaf.stalk y)
      (I.supportComplement : Scheme).functionField :=
    I.supportComplementFunctionFieldAlgebra y
  change
    (I.supportComplement.ι.functionFieldRingEquivOfIsOpenImmersion.toRingHom.comp
      (algebraMap (X.presheaf.stalk x) X.functionField)).comp
        (X.presheaf.stalkSpecializes hxy).hom =
      I.supportComplement.ι.functionFieldRingEquivOfIsOpenImmersion.toRingHom.comp
        (algebraMap (X.presheaf.stalk y) X.functionField)
  rw [RingHom.comp_assoc,
    stalkFunctionFieldAlgebra_comp_stalkSpecializes hxy]

/-- Under the canonical prime-localization model, the map from a component
generic stalk to the complement function field is unchanged. -/
theorem IdealSheafData.supportComplementFunctionFieldAlgebra_comp_stalkSpecializationEquiv
    {X : Scheme.{u}} [IsIntegral X] (I : X.IdealSheafData)
    [Nonempty I.supportComplement] {x y : X} (hxy : x ⤳ y) :
    let K := (I.supportComplement : Scheme).functionField
    let p := specializationPrime hxy
    let : p.asIdeal.IsPrime := p.isPrime
    letI : Algebra (X.presheaf.stalk y) K :=
      I.supportComplementFunctionFieldAlgebra y
    letI : Algebra (X.presheaf.stalk x) K :=
      I.supportComplementFunctionFieldAlgebra x
    letI : IsFractionRing (X.presheaf.stalk y) K :=
      I.supportComplementFunctionField_isFractionRing y
    letI : Algebra (Localization.AtPrime p.asIdeal) K :=
      EtaleFundamentalGroups.localizationAtPrimeToFractionFieldAlgebra
        (K := K) p.asIdeal
    (algebraMap (Localization.AtPrime p.asIdeal) K).comp
        (stalkSpecializationEquivLocalization hxy).toRingHom =
      algebraMap (X.presheaf.stalk x) K := by
  intro K p hPPrime
  let Ay := X.presheaf.stalk y
  let Ax := X.presheaf.stalk x
  let V := Localization.AtPrime p.asIdeal
  let : Algebra Ay K := I.supportComplementFunctionFieldAlgebra y
  let : Algebra Ax K := I.supportComplementFunctionFieldAlgebra x
  let : IsFractionRing Ay K :=
    I.supportComplementFunctionField_isFractionRing y
  let : Algebra Ay Ax :=
    (X.presheaf.stalkSpecializes hxy).hom.toAlgebra
  let : IsLocalization p.asIdeal.primeCompl Ax :=
    stalkSpecializes_isLocalization hxy
  let : Algebra V K :=
    EtaleFundamentalGroups.localizationAtPrimeToFractionFieldAlgebra
      (K := K) p.asIdeal
  let : IsScalarTower Ay V K :=
    EtaleFundamentalGroups.localizationAtPrimeToFractionField_isScalarTower
      (K := K) p.asIdeal
  apply IsLocalization.ringHom_ext p.asIdeal.primeCompl
  ext r
  simp only [RingHom.comp_apply]
  calc
    algebraMap V K (stalkSpecializationEquivLocalization hxy
        (algebraMap Ay Ax r)) =
        algebraMap V K (algebraMap Ay V r) := by
      rw [show algebraMap Ay Ax r =
          X.presheaf.stalkSpecializes hxy r by rfl]
      exact congrArg (algebraMap V K)
        (DFunLike.congr_fun
          (stalkSpecializationEquivLocalization_comp_stalkSpecializes hxy) r)
    _ = algebraMap Ay K r :=
      (IsScalarTower.algebraMap_apply Ay V K r).symm
    _ = algebraMap Ax K (algebraMap Ay Ax r) := by
      rw [show algebraMap Ay Ax r =
          X.presheaf.stalkSpecializes hxy r by rfl]
      exact (congrArg (fun f : Ay →+* K ↦ f r)
        (I.supportComplementFunctionFieldAlgebra_comp_stalkSpecializes
          hxy)).symm

/-- A normalization prime over the closed point of the fixed component
generic stalk.  This is selected once, independently of any later
specialization of the component. -/
noncomputable def IdealSheafData.componentGenericNormalizationPrimeOver
    {X : Scheme.{u}} [IsIntegral X] (I : X.IdealSheafData)
    [Nonempty I.supportComplement]
    (Z : Set I.subscheme) (hZ : Z ∈ irreducibleComponents I.subscheme)
    {L : Type u} [Field L]
    [Algebra (I.supportComplement : Scheme).functionField L] :
    let K := (I.supportComplement : Scheme).functionField
    let eta := I.componentGenericPoint Z hZ
    let A := X.presheaf.stalk eta
    letI : Algebra A K := I.supportComplementFunctionFieldAlgebra eta
    letI : IsFractionRing A K :=
      I.supportComplementFunctionField_isFractionRing eta
    letI : Algebra A L :=
      ((algebraMap K L).comp (algebraMap A K)).toAlgebra
    letI : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq' rfl
    let B := integralClosure A L
    (IsLocalRing.maximalIdeal A).primesOver B := by
  dsimp only
  let K := (I.supportComplement : Scheme).functionField
  let eta := I.componentGenericPoint Z hZ
  let A := X.presheaf.stalk eta
  letI : Algebra A K := I.supportComplementFunctionFieldAlgebra eta
  letI : IsFractionRing A K :=
    I.supportComplementFunctionField_isFractionRing eta
  letI : Algebra A L :=
    ((algebraMap K L).comp (algebraMap A K)).toAlgebra
  letI : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq' rfl
  let B := integralClosure A L
  letI : FaithfulSMul A B :=
    (faithfulSMul_iff_algebraMap_injective A B).mpr (by
      intro a b hab
      apply IsFractionRing.injective A K
      apply (algebraMap K L).injective
      have habL := congrArg (fun c : B ↦ (c : L)) hab
      change algebraMap A L a = algebraMap A L b at habL
      simpa only [IsScalarTower.algebraMap_apply A K L] using habL)
  exact Classical.choice (inferInstance :
    Nonempty ((IsLocalRing.maximalIdeal A).primesOver B))

/-- The underlying fixed normalization prime at the component generic
point. -/
noncomputable def IdealSheafData.componentGenericNormalizationPrime
    {X : Scheme.{u}} [IsIntegral X] (I : X.IdealSheafData)
    [Nonempty I.supportComplement]
    (Z : Set I.subscheme) (hZ : Z ∈ irreducibleComponents I.subscheme)
    {L : Type u} [Field L]
    [Algebra (I.supportComplement : Scheme).functionField L] :
    let K := (I.supportComplement : Scheme).functionField
    let eta := I.componentGenericPoint Z hZ
    let A := X.presheaf.stalk eta
    letI : Algebra A K := I.supportComplementFunctionFieldAlgebra eta
    letI : IsFractionRing A K :=
      I.supportComplementFunctionField_isFractionRing eta
    letI : Algebra A L :=
      ((algebraMap K L).comp (algebraMap A K)).toAlgebra
    letI : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq' rfl
    Ideal (integralClosure A L) := by
  dsimp only
  exact (I.componentGenericNormalizationPrimeOver Z hZ (L := L)).1

instance IdealSheafData.componentGenericNormalizationPrime_isPrime
    {X : Scheme.{u}} [IsIntegral X] (I : X.IdealSheafData)
    [Nonempty I.supportComplement]
    (Z : Set I.subscheme) (hZ : Z ∈ irreducibleComponents I.subscheme)
    {L : Type u} [Field L]
    [Algebra (I.supportComplement : Scheme).functionField L] :
    let K := (I.supportComplement : Scheme).functionField
    let eta := I.componentGenericPoint Z hZ
    let A := X.presheaf.stalk eta
    letI : Algebra A K := I.supportComplementFunctionFieldAlgebra eta
    letI : IsFractionRing A K :=
      I.supportComplementFunctionField_isFractionRing eta
    letI : Algebra A L :=
      ((algebraMap K L).comp (algebraMap A K)).toAlgebra
    letI : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq' rfl
    (I.componentGenericNormalizationPrime Z hZ (L := L)).IsPrime := by
  dsimp only
  exact (I.componentGenericNormalizationPrimeOver Z hZ (L := L)).2.1

instance IdealSheafData.componentGenericNormalizationPrime_liesOver
    {X : Scheme.{u}} [IsIntegral X] (I : X.IdealSheafData)
    [Nonempty I.supportComplement]
    (Z : Set I.subscheme) (hZ : Z ∈ irreducibleComponents I.subscheme)
    {L : Type u} [Field L]
    [Algebra (I.supportComplement : Scheme).functionField L] :
    let K := (I.supportComplement : Scheme).functionField
    let eta := I.componentGenericPoint Z hZ
    let A := X.presheaf.stalk eta
    letI : Algebra A K := I.supportComplementFunctionFieldAlgebra eta
    letI : IsFractionRing A K :=
      I.supportComplementFunctionField_isFractionRing eta
    letI : Algebra A L :=
      ((algebraMap K L).comp (algebraMap A K)).toAlgebra
    letI : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq' rfl
    (I.componentGenericNormalizationPrime Z hZ (L := L)).LiesOver
      (IsLocalRing.maximalIdeal A) := by
  dsimp only
  exact (I.componentGenericNormalizationPrimeOver Z hZ (L := L)).2.2

/-- The fixed ramification index attached to a boundary component and a
function-field extension. -/
noncomputable def IdealSheafData.componentGenericNormalizationRamificationIndex
    {X : Scheme.{u}} [IsIntegral X] (I : X.IdealSheafData)
    [Nonempty I.supportComplement]
    (Z : Set I.subscheme) (hZ : Z ∈ irreducibleComponents I.subscheme)
    {L : Type u} [Field L]
    [Algebra (I.supportComplement : Scheme).functionField L] : ℕ := by
  let K := (I.supportComplement : Scheme).functionField
  let eta := I.componentGenericPoint Z hZ
  let A := X.presheaf.stalk eta
  letI : Algebra A K := I.supportComplementFunctionFieldAlgebra eta
  letI : IsFractionRing A K :=
    I.supportComplementFunctionField_isFractionRing eta
  letI : Algebra A L :=
    ((algebraMap K L).comp (algebraMap A K)).toAlgebra
  letI : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq' rfl
  exact (I.componentGenericNormalizationPrime Z hZ (L := L)).ramificationIdx A

end AlgebraicGeometry.Scheme

namespace EtaleFundamentalGroups

universe uR uS uT uU

/-- Compatible equivalences carry the contraction of a target ideal to the
corresponding base ideal. -/
theorem Ideal.under_map_eq_map_under_of_compatible_ringEquiv
    {R : Type uR} {S : Type uS} {T : Type uT} {U : Type uU}
    [CommRing R] [CommRing S] [CommRing T] [CommRing U]
    [Algebra R T] [Algebra S U]
    (eBase : R ≃+* S) (eTarget : T ≃+* U)
    (hcompat : eTarget.toRingHom.comp (algebraMap R T) =
      (algebraMap S U).comp eBase.toRingHom)
    (q : Ideal T) :
    (q.map eTarget.toRingHom).under S =
      (q.under R).map eBase.toRingHom := by
  ext s
  obtain ⟨r, rfl⟩ := eBase.surjective s
  change algebraMap S U (eBase r) ∈ q.map eTarget.toRingHom ↔
    eBase r ∈ (q.under R).map eBase.toRingHom
  have hr := DFunLike.congr_fun hcompat r
  change eTarget (algebraMap R T r) = algebraMap S U (eBase r) at hr
  rw [← hr]
  constructor
  · intro h
    have hrq : algebraMap R T r ∈ q :=
      (Ideal.apply_mem_of_equiv_iff
        (I := q) (f := eTarget) (x := algebraMap R T r)).mp h
    exact (Ideal.apply_mem_of_equiv_iff
      (I := q.under R) (f := eBase) (x := r)).mpr hrq
  · intro h
    have hrq : algebraMap R T r ∈ q :=
      (Ideal.apply_mem_of_equiv_iff
        (I := q.under R) (f := eBase) (x := r)).mp h
    exact (Ideal.apply_mem_of_equiv_iff
      (I := q) (f := eTarget) (x := algebraMap R T r)).mpr hrq

end EtaleFundamentalGroups

namespace AlgebraicGeometry.Scheme.IdealSheafData

open EtaleFundamentalGroups

universe u

variable {X : Scheme.{u}}

/-- A normalization prime above the branch of a fixed component in any
specialized stalk has the fixed component-generic ramification index. -/
theorem normalizationPrime_ramificationIdx_eq_componentGeneric
    [IsIntegral X] [IsNormalIntegral X]
    (I : X.IdealSheafData) [Nonempty I.supportComplement]
    (Z : Set I.subscheme) (hZ : Z ∈ irreducibleComponents I.subscheme)
    {L : Type u} [Field L]
    [Algebra (I.supportComplement : Scheme).functionField L]
    [FiniteDimensional (I.supportComplement : Scheme).functionField L]
    [_root_.IsGalois (I.supportComplement : Scheme).functionField L]
    (z : I.subscheme) (hz : z ∈ Z) :
    let K := (I.supportComplement : Scheme).functionField
    let eta := I.componentGenericPoint Z hZ
    let x := I.subschemeι z
    let p := (I.componentBranchPrimeAt Z hZ z hz).asIdeal
    let Aeta := X.presheaf.stalk eta
    let Ax := X.presheaf.stalk x
    letI : Algebra Aeta K := I.supportComplementFunctionFieldAlgebra eta
    letI : IsFractionRing Aeta K :=
      I.supportComplementFunctionField_isFractionRing eta
    letI : Algebra Ax K := I.supportComplementFunctionFieldAlgebra x
    letI : IsFractionRing Ax K :=
      I.supportComplementFunctionField_isFractionRing x
    letI : Algebra Aeta L :=
      ((algebraMap K L).comp (algebraMap Aeta K)).toAlgebra
    letI : IsScalarTower Aeta K L := IsScalarTower.of_algebraMap_eq' rfl
    letI : Algebra Ax L :=
      ((algebraMap K L).comp (algebraMap Ax K)).toAlgebra
    letI : IsScalarTower Ax K L := IsScalarTower.of_algebraMap_eq' rfl
    let Bx := integralClosure Ax L
    ∀ (q : Ideal Bx), q.IsPrime → q.LiesOver p →
      q.ramificationIdx Ax =
        I.componentGenericNormalizationRamificationIndex Z hZ (L := L) := by
  dsimp only
  let K := (I.supportComplement : Scheme).functionField
  let eta := I.componentGenericPoint Z hZ
  let x := I.subschemeι z
  let hxy := I.componentGenericPoint_specializes_subschemeι Z hZ z hz
  let pSpec := specializationPrime hxy
  let p := pSpec.asIdeal
  let : p.IsPrime := pSpec.isPrime
  let Aeta := X.presheaf.stalk eta
  let Ax := X.presheaf.stalk x
  let V := Localization.AtPrime p
  let : Algebra Aeta K := I.supportComplementFunctionFieldAlgebra eta
  let : IsFractionRing Aeta K :=
    I.supportComplementFunctionField_isFractionRing eta
  let : Algebra Ax K := I.supportComplementFunctionFieldAlgebra x
  let : IsFractionRing Ax K :=
    I.supportComplementFunctionField_isFractionRing x
  let : IsIntegrallyClosed Ax :=
    IsNormalIntegral.stalk_isIntegrallyClosed x
  let : Algebra Aeta L :=
    ((algebraMap K L).comp (algebraMap Aeta K)).toAlgebra
  let : IsScalarTower Aeta K L := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra Ax L :=
    ((algebraMap K L).comp (algebraMap Ax K)).toAlgebra
  let : IsScalarTower Ax K L := IsScalarTower.of_algebraMap_eq' rfl
  let Beta := integralClosure Aeta L
  let Bx := integralClosure Ax L
  intro q hqPrime hqOver
  let : q.IsPrime := hqPrime
  let : q.LiesOver p := by
    simpa only [p, pSpec, hxy, IdealSheafData.componentBranchPrimeAt] using hqOver
  let : Algebra V K :=
    localizationAtPrimeToFractionFieldAlgebra (K := K) p
  let : IsScalarTower Ax V K :=
    localizationAtPrimeToFractionField_isScalarTower (K := K) p
  let : IsFractionRing V K :=
    localizationAtPrimeToFractionField_isFractionRing (K := K) p
  let : IsIntegrallyClosed V :=
    isIntegrallyClosed_of_isLocalization V p.primeCompl
      p.primeCompl_le_nonZeroDivisors
  let : Algebra V L :=
    localizationAtPrimeToExtensionAlgebra (K := K) (L := L) p
  let : IsScalarTower V K L :=
    localizationAtPrimeToFractionFieldToExtension_isScalarTower
      (K := K) (L := L) p
  let : IsScalarTower Ax V L :=
    localizationAtPrimeToExtension_isScalarTower (K := K) (L := L) p
  let Bv := integralClosure V L
  let qv := localizedNormalizationPrime (K := K) (L := L) p q
  let : qv.IsPrime := by
    apply localizedNormalizationPrime_isPrime_of_under_le
    rw [← q.over_def p]
  let : qv.LiesOver (IsLocalRing.maximalIdeal V) :=
    localizedNormalizationPrime_liesOver (K := K) (L := L) p q
  let eBase : Aeta ≃+* V :=
    stalkSpecializationEquivLocalization hxy
  have hBaseK :
      (algebraMap V K).comp eBase.toRingHom = algebraMap Aeta K := by
    simpa only [pSpec, p, Aeta, V, eta] using
      I.supportComplementFunctionFieldAlgebra_comp_stalkSpecializationEquiv
        hxy
  have hBaseL :
      (algebraMap V L).comp eBase.toRingHom = algebraMap Aeta L := by
    apply RingHom.ext
    intro a
    change algebraMap K L (algebraMap V K (eBase a)) =
      algebraMap K L (algebraMap Aeta K a)
    exact congrArg (algebraMap K L) (DFunLike.congr_fun hBaseK a)
  let : Algebra Aeta Bv := integralClosureBaseRingAlgebra eBase
  let eTargetAlg : Beta ≃ₐ[Aeta] Bv :=
    integralClosureBaseRingAlgEquiv eBase hBaseL
  let eTarget : Beta ≃+* Bv := eTargetAlg.toRingEquiv
  have hTarget :
      eTarget.toRingHom.comp (algebraMap Aeta Beta) =
        (algebraMap V Bv).comp eBase.toRingHom := by
    apply RingHom.ext
    intro a
    change eTargetAlg (algebraMap Aeta Beta a) =
      algebraMap V Bv (eBase a)
    exact eTargetAlg.commutes a
  let Qeta : Ideal Beta :=
    I.componentGenericNormalizationPrime Z hZ (L := L)
  let Qv : Ideal Bv := Qeta.map eTarget.toRingHom
  let : Qeta.IsPrime :=
    I.componentGenericNormalizationPrime_isPrime Z hZ (L := L)
  let : Qeta.LiesOver (IsLocalRing.maximalIdeal Aeta) :=
    I.componentGenericNormalizationPrime_liesOver Z hZ (L := L)
  let : Qv.IsPrime := by
    dsimp only [Qv]
    change (Qeta.map eTarget).IsPrime
    infer_instance
  have hQvUnder : Qv.under V = IsLocalRing.maximalIdeal V := by
    calc
      Qv.under V = (Qeta.under Aeta).map eBase.toRingHom :=
        Ideal.under_map_eq_map_under_of_compatible_ringEquiv
          eBase eTarget hTarget Qeta
      _ = (IsLocalRing.maximalIdeal Aeta).map eBase.toRingHom := by
        rw [← Qeta.over_def (IsLocalRing.maximalIdeal Aeta)]
      _ = IsLocalRing.maximalIdeal V :=
        IsLocalRing.map_ringEquiv_maximalIdeal eBase
  let : Qv.LiesOver (IsLocalRing.maximalIdeal V) := ⟨hQvUnder.symm⟩
  let : IsFractionRing Bv L :=
    IsIntegralClosure.isFractionRing_of_finite_extension V K L Bv
  let : MulSemiringAction Gal(L/K) Bv :=
    IsIntegralClosure.MulSemiringAction V K L Bv
  let : IsGaloisGroup Gal(L/K) V Bv :=
    IsGaloisGroup.of_isFractionRing Gal(L/K) V Bv K L
  calc
    q.ramificationIdx Ax = qv.ramificationIdx V :=
      (localizedNormalizationPrime_ramificationIdx
        (K := K) (L := L) p q).symm
    _ = Qv.ramificationIdx V :=
      Ideal.ramificationIdx_eq_of_isGaloisGroup
        (IsLocalRing.maximalIdeal V) qv Qv Gal(L/K)
    _ = Qeta.ramificationIdx Aeta :=
      ramificationIdx_map_eq_of_compatible_ringEquiv
        eBase eTarget hTarget Qeta
    _ = I.componentGenericNormalizationRamificationIndex
        Z hZ (L := L) := rfl

/-- At a characteristic-zero component branch, the inertia cardinality in a
specialized stalk is the fixed component-generic ramification index. -/
theorem normalizationInertia_card_eq_componentGenericRamificationIndex
    [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (hEffective : I.IsEffectiveCartier)
    [Nonempty I.supportComplement]
    (Z : Set I.subscheme) (hZ : Z ∈ irreducibleComponents I.subscheme)
    {L : Type u} [Field L]
    [Algebra (I.supportComplement : Scheme).functionField L]
    [FiniteDimensional (I.supportComplement : Scheme).functionField L]
    [_root_.IsGalois (I.supportComplement : Scheme).functionField L]
    (z : I.subscheme) (hz : z ∈ Z)
    (hCharZero : I.HasCharacteristicZeroBranchesAt (I.subschemeι z)) :
    let K := (I.supportComplement : Scheme).functionField
    let x := I.subschemeι z
    let p := (I.componentBranchPrimeAt Z hZ z hz).asIdeal
    let Ax := X.presheaf.stalk x
    letI : Algebra Ax K := I.supportComplementFunctionFieldAlgebra x
    letI : IsFractionRing Ax K :=
      I.supportComplementFunctionField_isFractionRing x
    letI : Algebra Ax L :=
      ((algebraMap K L).comp (algebraMap Ax K)).toAlgebra
    letI : IsScalarTower Ax K L := IsScalarTower.of_algebraMap_eq' rfl
    let Bx := integralClosure Ax L
    ∀ (q : Ideal Bx), q.IsPrime → q.LiesOver p →
      Nat.card (q.toAddSubgroup.inertia Gal(L/K)) =
        I.componentGenericNormalizationRamificationIndex Z hZ (L := L) := by
  dsimp only
  let K := (I.supportComplement : Scheme).functionField
  let x := I.subschemeι z
  let pSpec := I.componentBranchPrimeAt Z hZ z hz
  let p := pSpec.asIdeal
  let Ax := X.presheaf.stalk x
  let : Algebra Ax K := I.supportComplementFunctionFieldAlgebra x
  let : IsFractionRing Ax K :=
    I.supportComplementFunctionField_isFractionRing x
  let : Algebra Ax L :=
    ((algebraMap K L).comp (algebraMap Ax K)).toAlgebra
  let : IsScalarTower Ax K L := IsScalarTower.of_algebraMap_eq' rfl
  let Bx := integralClosure Ax L
  let : IsIntegrallyClosed Ax :=
    IsNormalIntegral.stalk_isIntegrallyClosed x
  let : p.IsPrime := pSpec.2
  have hpHeight : p.height = 1 :=
    hEffective.componentBranchPrimeAt_height_eq_one Z hZ z hz
  let : CharZero (Ax ⧸ p) :=
    hCharZero p inferInstance hpHeight
      (I.stalkIdeal_le_componentBranchPrimeAt Z hZ z hz)
  intro q hqPrime hqOver
  let : q.IsPrime := hqPrime
  let : q.LiesOver p := hqOver
  calc
    Nat.card (q.toAddSubgroup.inertia Gal(L/K)) =
        q.ramificationIdx Ax :=
      normalizationInertia_card_eq_ramificationIdx_of_normal_noetherian
        (K := K) (L := L) p hpHeight q
    _ = I.componentGenericNormalizationRamificationIndex
        Z hZ (L := L) :=
      I.normalizationPrime_ramificationIdx_eq_componentGeneric
        Z hZ z hz q hqPrime hqOver

/-- Equality-transport form of
`normalizationInertia_card_eq_componentGenericRamificationIndex`, matching
the ambient stalk returned by an etale chart whose image point is identified
with the prescribed component specialization. -/
theorem normalizationInertia_card_eq_componentGenericRamificationIndex_of_eq
    [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (hEffective : I.IsEffectiveCartier)
    [Nonempty I.supportComplement]
    (Z : Set I.subscheme) (hZ : Z ∈ irreducibleComponents I.subscheme)
    {L : Type u} [Field L]
    [Algebra (I.supportComplement : Scheme).functionField L]
    [FiniteDimensional (I.supportComplement : Scheme).functionField L]
    [_root_.IsGalois (I.supportComplement : Scheme).functionField L]
    (z : I.subscheme) (hz : z ∈ Z)
    (hCharZero : I.HasCharacteristicZeroBranchesAt (I.subschemeι z))
    (y : X) (hy : y = I.subschemeι z) :
    let K := (I.supportComplement : Scheme).functionField
    let p0 := (I.componentBranchPrimeAt Z hZ z hz).asIdeal
    let py : Ideal (X.presheaf.stalk y) := hy.symm ▸ p0
    let Ay := X.presheaf.stalk y
    letI : Algebra Ay K := I.supportComplementFunctionFieldAlgebra y
    letI : IsFractionRing Ay K :=
      I.supportComplementFunctionField_isFractionRing y
    letI : Algebra Ay L :=
      ((algebraMap K L).comp (algebraMap Ay K)).toAlgebra
    letI : IsScalarTower Ay K L := IsScalarTower.of_algebraMap_eq' rfl
    let By := integralClosure Ay L
    ∀ (q : Ideal By), q.IsPrime → q.LiesOver py →
      Nat.card (q.toAddSubgroup.inertia Gal(L/K)) =
        I.componentGenericNormalizationRamificationIndex Z hZ (L := L) := by
  subst y
  simpa using
    I.normalizationInertia_card_eq_componentGenericRamificationIndex
      hEffective Z hZ z hz hCharZero (L := L)

end AlgebraicGeometry.Scheme.IdealSheafData

namespace AlgebraicGeometry.Scheme.EffectiveCartierDivisor

open CategoryTheory.PreGaloisCategory EtaleFundamentalGroups

universe u

variable {X : Scheme.{u}}

local instance : IsDomain (ULift.{u} ℤ) :=
  (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).toMulEquiv.isDomain ℤ

namespace HasSurjectiveComponentsOverIntegers

/-- For a fixed component and a fixed connected Galois cover, its one
component-generic ramification index is prime to every rational prime.  The
specialized normalization prime used for each rational prime may vary, but
the integer on the left does not. -/
theorem forall_prime_componentGenericNormalizationRamificationIndex_coprime
    [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X]
    (D : EffectiveCartierDivisor X)
    (hSurjective : D.HasSurjectiveComponentsOverIntegers)
    (hNC : D.IsNormalCrossings)
    (Z : Set D.1.subscheme)
    (hZ : Z ∈ irreducibleComponents D.1.subscheme)
    [Nonempty D.1.supportComplement]
    (W : FiniteEtale D.1.supportComplement) (hW : IsGalois W) :
    letI : IsIntegral D.1.supportComplement :=
      isIntegral_of_isOpenImmersion D.1.supportComplement.ι
    letI : IsIntegral W.left :=
      EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale W
    let K := (D.1.supportComplement : Scheme).functionField
    let L := W.left.functionField
    letI : Algebra K L :=
      EtaleFundamentalGroups.finiteEtaleFunctionFieldAlgebra W
    letI : FiniteDimensional K L :=
      EtaleFundamentalGroups.finiteDimensional_functionField_of_finiteEtale_isConnected W
    letI : _root_.IsGalois K L :=
      EtaleFundamentalGroups.isGalois_functionField_of_isGalois_finiteEtale W hW
    ∀ p : ℕ, p.Prime →
      Nat.Coprime
        (D.1.componentGenericNormalizationRamificationIndex Z hZ (L := L)) p := by
  dsimp only
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
  intro p hp
  obtain ⟨z, hz, hchar, hsource⟩ :=
    hSurjective.forall_prime_exists_componentNormalizationInertia_coprime
      D hNC Z hZ W hW p hp
  let : CharP (X.residueField (D.1.subschemeι z)) p :=
    ringChar.of_eq hchar
  dsimp only at hsource
  obtain ⟨U, f, u, hfu, hf, q, hqPrime, hqOver, hcoprime⟩ := hsource
  let Base := Spec (CommRingCat.of (ULift.{u} ℤ))
  let e : Base.residueField (genericPoint Base) ≃+* ℚ :=
    specULiftZGenericResidueFieldEquivQ
  let : CharZero (Base.residueField (genericPoint Base)) :=
    e.toRingHom.charZero
  have hHorizontal :
      D.IsHorizontalOver (specULiftZIsTerminal.from X) :=
    hSurjective.isHorizontalOverIntegers
  have hCharZero :
      D.1.HasCharacteristicZeroBranchesAt (D.1.subschemeι z) :=
    hHorizontal.hasCharacteristicZeroBranchesAt
      D (specULiftZIsTerminal.from X) (D.1.subschemeι z)
  have hcard :=
    D.1.normalizationInertia_card_eq_componentGenericRamificationIndex_of_eq
      D.2 Z hZ z hz hCharZero (f u) hfu q hqPrime hqOver
  rw [hcard] at hcoprime
  exact hcoprime

end HasSurjectiveComponentsOverIntegers

/-- The fixed component-generic ramification index is one.  Indeed, the
same natural number is prime to every rational prime by specializing the
component in every positive residue characteristic. -/
theorem HasSurjectiveComponentsOverIntegers.componentGenericNormalizationRamificationIndex_eq_one
    [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X]
    (D : EffectiveCartierDivisor X)
    (hSurjective : D.HasSurjectiveComponentsOverIntegers)
    (hNC : D.IsNormalCrossings)
    (Z : Set D.1.subscheme)
    (hZ : Z ∈ irreducibleComponents D.1.subscheme)
    [Nonempty D.1.supportComplement]
    (W : FiniteEtale D.1.supportComplement) (hW : IsGalois W) :
    letI : IsIntegral D.1.supportComplement :=
      isIntegral_of_isOpenImmersion D.1.supportComplement.ι
    letI : IsIntegral W.left :=
      EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale W
    let K := (D.1.supportComplement : Scheme).functionField
    let L := W.left.functionField
    letI : Algebra K L :=
      EtaleFundamentalGroups.finiteEtaleFunctionFieldAlgebra W
    letI : FiniteDimensional K L :=
      EtaleFundamentalGroups.finiteDimensional_functionField_of_finiteEtale_isConnected W
    letI : _root_.IsGalois K L :=
      EtaleFundamentalGroups.isGalois_functionField_of_isGalois_finiteEtale W hW
    D.1.componentGenericNormalizationRamificationIndex Z hZ (L := L) = 1 := by
  dsimp only
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
  apply Nat.eq_one_iff_not_exists_prime_dvd.mpr
  intro p hp hpdvd
  have hcoprime :=
    hSurjective.forall_prime_componentGenericNormalizationRamificationIndex_coprime
      D hNC Z hZ W hW p hp
  exact (hp.coprime_iff_not_dvd.mp hcoprime.symm) hpdvd

/-- The inertia group at the fixed component-generic normalization prime has
cardinality equal to the fixed component ramification index. -/
theorem IsHorizontalOver.componentGenericNormalizationInertia_card_eq_ramificationIndex
    {S : Scheme.{u}}
    [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X]
    [IsIntegral S]
    (D : EffectiveCartierDivisor X) (structural : X ⟶ S)
    (hHorizontal : D.IsHorizontalOver structural)
    [CharZero (S.residueField (genericPoint S))]
    (Z : Set D.1.subscheme)
    (hZ : Z ∈ irreducibleComponents D.1.subscheme)
    [Nonempty D.1.supportComplement]
    {L : Type u} [Field L]
    [Algebra (D.1.supportComplement : Scheme).functionField L]
    [FiniteDimensional (D.1.supportComplement : Scheme).functionField L]
    [_root_.IsGalois (D.1.supportComplement : Scheme).functionField L] :
    let K := (D.1.supportComplement : Scheme).functionField
    let eta := D.1.componentGenericPoint Z hZ
    let Aeta := X.presheaf.stalk eta
    letI : Algebra Aeta K :=
      D.1.supportComplementFunctionFieldAlgebra eta
    letI : IsFractionRing Aeta K :=
      D.1.supportComplementFunctionField_isFractionRing eta
    letI : Algebra Aeta L :=
      ((algebraMap K L).comp (algebraMap Aeta K)).toAlgebra
    letI : IsScalarTower Aeta K L := IsScalarTower.of_algebraMap_eq' rfl
    let Beta := integralClosure Aeta L
    let Qeta : Ideal Beta :=
      D.1.componentGenericNormalizationPrime Z hZ (L := L)
    Nat.card (Qeta.toAddSubgroup.inertia Gal(L/K)) =
      D.1.componentGenericNormalizationRamificationIndex Z hZ (L := L) := by
  dsimp only
  let K := (D.1.supportComplement : Scheme).functionField
  let eta := D.1.componentGenericPoint Z hZ
  let Aeta := X.presheaf.stalk eta
  let : Algebra Aeta K :=
    D.1.supportComplementFunctionFieldAlgebra eta
  let : IsFractionRing Aeta K :=
    D.1.supportComplementFunctionField_isFractionRing eta
  let : Algebra Aeta L :=
    ((algebraMap K L).comp (algebraMap Aeta K)).toAlgebra
  let : IsScalarTower Aeta K L := IsScalarTower.of_algebraMap_eq' rfl
  let Beta := integralClosure Aeta L
  let Qeta : Ideal Beta :=
    D.1.componentGenericNormalizationPrime Z hZ (L := L)
  let P : Ideal Aeta := IsLocalRing.maximalIdeal Aeta
  let : IsIntegrallyClosed Aeta :=
    IsNormalIntegral.stalk_isIntegrallyClosed eta
  let : P.IsPrime := (IsLocalRing.maximalIdeal.isMaximal Aeta).isPrime
  have hPheight : P.height = 1 := by
    apply WithBot.coe_eq_coe.mp
    calc
      ((P.height : ℕ∞) : WithBot ℕ∞) = ringKrullDim Aeta :=
        IsLocalRing.maximalIdeal_height_eq_ringKrullDim
      _ = ((Order.coheight eta : ℕ∞) : WithBot ℕ∞) :=
        ringKrullDim_stalk_eq_coheight eta
      _ = (((1 : ℕ∞)) : WithBot ℕ∞) := by
        rw [D.2.coheight_componentGenericPoint_eq_one Z hZ]
  have hetaSupport : eta ∈ D.1.support :=
    D.1.componentGenericPoint_mem_support Z hZ
  have hIP : D.1.stalkIdeal eta ≤ P := by
    have hclosed :
        X.fromSpecStalk eta (IsLocalRing.closedPoint Aeta) ∈ D.1.support := by
      rw [fromSpecStalk_closedPoint]
      exact hetaSupport
    have hle :=
      (D.1.mem_support_fromSpecStalk_iff_stalkIdeal_le eta
        (IsLocalRing.closedPoint Aeta)).mp hclosed
    change D.1.stalkIdeal eta ≤ IsLocalRing.maximalIdeal Aeta at hle
    exact hle
  have hCharBranches : D.1.HasCharacteristicZeroBranchesAt eta :=
    hHorizontal.hasCharacteristicZeroBranchesAt D structural eta
  let : CharZero (Aeta ⧸ P) :=
    hCharBranches P inferInstance hPheight hIP
  let : Qeta.IsPrime :=
    D.1.componentGenericNormalizationPrime_isPrime Z hZ (L := L)
  let : Qeta.LiesOver P :=
    D.1.componentGenericNormalizationPrime_liesOver Z hZ (L := L)
  calc
    Nat.card (Qeta.toAddSubgroup.inertia Gal(L/K)) =
        Qeta.ramificationIdx Aeta :=
      normalizationInertia_card_eq_ramificationIdx_of_normal_noetherian
        (K := K) (L := L) P hPheight Qeta
    _ = D.1.componentGenericNormalizationRamificationIndex
        Z hZ (L := L) := rfl

namespace HasSurjectiveComponentsOverIntegers

/-- The cardinality of one fixed divisorial inertia group is prime to every
rational prime.  Both the normalization prime and the inertia group are now
independent of the residue characteristic used in the local argument. -/
theorem forall_prime_componentGenericNormalizationInertia_card_coprime
    [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X]
    (D : EffectiveCartierDivisor X)
    (hSurjective : D.HasSurjectiveComponentsOverIntegers)
    (hNC : D.IsNormalCrossings)
    (Z : Set D.1.subscheme)
    (hZ : Z ∈ irreducibleComponents D.1.subscheme)
    [Nonempty D.1.supportComplement]
    (W : FiniteEtale D.1.supportComplement) (hW : IsGalois W) :
    letI : IsIntegral D.1.supportComplement :=
      isIntegral_of_isOpenImmersion D.1.supportComplement.ι
    letI : IsIntegral W.left :=
      EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale W
    let K := (D.1.supportComplement : Scheme).functionField
    let L := W.left.functionField
    letI : Algebra K L :=
      EtaleFundamentalGroups.finiteEtaleFunctionFieldAlgebra W
    letI : FiniteDimensional K L :=
      EtaleFundamentalGroups.finiteDimensional_functionField_of_finiteEtale_isConnected W
    letI : _root_.IsGalois K L :=
      EtaleFundamentalGroups.isGalois_functionField_of_isGalois_finiteEtale W hW
    let eta := D.1.componentGenericPoint Z hZ
    let Aeta := X.presheaf.stalk eta
    letI : Algebra Aeta K :=
      D.1.supportComplementFunctionFieldAlgebra eta
    letI : IsFractionRing Aeta K :=
      D.1.supportComplementFunctionField_isFractionRing eta
    letI : Algebra Aeta L :=
      ((algebraMap K L).comp (algebraMap Aeta K)).toAlgebra
    letI : IsScalarTower Aeta K L := IsScalarTower.of_algebraMap_eq' rfl
    let Beta := integralClosure Aeta L
    let Qeta : Ideal Beta :=
      D.1.componentGenericNormalizationPrime Z hZ (L := L)
    ∀ p : ℕ, p.Prime →
      Nat.Coprime (Nat.card (Qeta.toAddSubgroup.inertia Gal(L/K))) p := by
  dsimp only
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
  let eta := D.1.componentGenericPoint Z hZ
  let Aeta := X.presheaf.stalk eta
  let : Algebra Aeta K :=
    D.1.supportComplementFunctionFieldAlgebra eta
  let : IsFractionRing Aeta K :=
    D.1.supportComplementFunctionField_isFractionRing eta
  let : Algebra Aeta L :=
    ((algebraMap K L).comp (algebraMap Aeta K)).toAlgebra
  let : IsScalarTower Aeta K L := IsScalarTower.of_algebraMap_eq' rfl
  let Beta := integralClosure Aeta L
  let Qeta : Ideal Beta :=
    D.1.componentGenericNormalizationPrime Z hZ (L := L)
  let Base := Spec (CommRingCat.of (ULift.{u} ℤ))
  let e : Base.residueField (genericPoint Base) ≃+* ℚ :=
    specULiftZGenericResidueFieldEquivQ
  let : CharZero (Base.residueField (genericPoint Base)) :=
    e.toRingHom.charZero
  have hHorizontal :
      D.IsHorizontalOver (specULiftZIsTerminal.from X) :=
    hSurjective.isHorizontalOverIntegers
  have hcard : Nat.card (Qeta.toAddSubgroup.inertia Gal(L/K)) =
      D.1.componentGenericNormalizationRamificationIndex Z hZ (L := L) :=
    hHorizontal.componentGenericNormalizationInertia_card_eq_ramificationIndex
      D (specULiftZIsTerminal.from X) Z hZ (L := L)
  intro p hp
  rw [hcard]
  exact
    hSurjective.forall_prime_componentGenericNormalizationRamificationIndex_coprime
      D hNC Z hZ W hW p hp

end HasSurjectiveComponentsOverIntegers

/-- Every normalization ideal inertia group above a specialization of the
fixed boundary component is trivial.  Its cardinality is the fixed
component-generic ramification index, which is one by the all-prime
specialization argument. -/
theorem HasSurjectiveComponentsOverIntegers.componentNormalizationInertia_eq_bot
    [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X]
    (D : EffectiveCartierDivisor X)
    (hSurjective : D.HasSurjectiveComponentsOverIntegers)
    (hNC : D.IsNormalCrossings)
    (Z : Set D.1.subscheme)
    (hZ : Z ∈ irreducibleComponents D.1.subscheme)
    [Nonempty D.1.supportComplement]
    (W : FiniteEtale D.1.supportComplement) (hW : IsGalois W)
    (z : D.1.subscheme) (hz : z ∈ Z) :
    letI : IsIntegral D.1.supportComplement :=
      isIntegral_of_isOpenImmersion D.1.supportComplement.ι
    letI : IsIntegral W.left :=
      EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale W
    let K := (D.1.supportComplement : Scheme).functionField
    let L := W.left.functionField
    letI : Algebra K L :=
      EtaleFundamentalGroups.finiteEtaleFunctionFieldAlgebra W
    letI : FiniteDimensional K L :=
      EtaleFundamentalGroups.finiteDimensional_functionField_of_finiteEtale_isConnected W
    letI : _root_.IsGalois K L :=
      EtaleFundamentalGroups.isGalois_functionField_of_isGalois_finiteEtale W hW
    let x := D.1.subschemeι z
    let p := (D.1.componentBranchPrimeAt Z hZ z hz).asIdeal
    let Ax := X.presheaf.stalk x
    letI : Algebra Ax K := D.1.supportComplementFunctionFieldAlgebra x
    letI : IsFractionRing Ax K :=
      D.1.supportComplementFunctionField_isFractionRing x
    letI : Algebra Ax L :=
      ((algebraMap K L).comp (algebraMap Ax K)).toAlgebra
    letI : IsScalarTower Ax K L := IsScalarTower.of_algebraMap_eq' rfl
    let Bx := integralClosure Ax L
    ∀ (q : Ideal Bx), q.IsPrime → q.LiesOver p →
      q.toAddSubgroup.inertia Gal(L/K) = ⊥ := by
  dsimp only
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
  let p := (D.1.componentBranchPrimeAt Z hZ z hz).asIdeal
  let Ax := X.presheaf.stalk x
  let : Algebra Ax K := D.1.supportComplementFunctionFieldAlgebra x
  let : IsFractionRing Ax K :=
    D.1.supportComplementFunctionField_isFractionRing x
  let : Algebra Ax L :=
    ((algebraMap K L).comp (algebraMap Ax K)).toAlgebra
  let : IsScalarTower Ax K L := IsScalarTower.of_algebraMap_eq' rfl
  let Bx := integralClosure Ax L
  let Base := Spec (CommRingCat.of (ULift.{u} ℤ))
  let e : Base.residueField (genericPoint Base) ≃+* ℚ :=
    specULiftZGenericResidueFieldEquivQ
  let : CharZero (Base.residueField (genericPoint Base)) :=
    e.toRingHom.charZero
  have hHorizontal :
      D.IsHorizontalOver (specULiftZIsTerminal.from X) :=
    hSurjective.isHorizontalOverIntegers
  have hCharZero : D.1.HasCharacteristicZeroBranchesAt x :=
    hHorizontal.hasCharacteristicZeroBranchesAt
      D (specULiftZIsTerminal.from X) x
  intro q hqPrime hqOver
  let : q.IsPrime := hqPrime
  let : q.LiesOver p := hqOver
  let : Finite Gal(L/K) :=
    IsGaloisGroup.finite Gal(L/K) K L
  let : Finite (q.toAddSubgroup.inertia Gal(L/K)) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  apply (Subgroup.eq_bot_iff_card (q.toAddSubgroup.inertia Gal(L/K))).2
  calc
    Nat.card (q.toAddSubgroup.inertia Gal(L/K)) =
        D.1.componentGenericNormalizationRamificationIndex
          Z hZ (L := L) :=
      D.1.normalizationInertia_card_eq_componentGenericRamificationIndex
        D.2 Z hZ z hz hCharZero q hqPrime hqOver
    _ = 1 :=
      hSurjective.componentGenericNormalizationRamificationIndex_eq_one
        D hNC Z hZ W hW

end AlgebraicGeometry.Scheme.EffectiveCartierDivisor

end
