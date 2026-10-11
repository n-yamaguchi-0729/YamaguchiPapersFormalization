/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.StrictHenselian.NormalizationSpecializationFiber
import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkResidueClosure
import Nyll.EtaleFundamentalGroups.GeometricFiber.HenselianResidueFundamentalGroup
import Nyll.EtaleFundamentalGroups.GeometricFiber.ExtendedFiberGaloisAction
import Nyll.EtaleFundamentalGroups.GeometricFiber.HenselianSpecializationConjugacy

/-!
# The original ordinary-henselization fundamental group and strict residue

The canonical generic-to-residue specialization and the henselian closed-point
comparison identify the actual ordinary-henselization fundamental group with
the automorphisms of the actual strict-stalk residue over the original residue
field. The original normalization residue field is only a separably closed
overfield; it is not required to be separable over the base residue field.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale

namespace EtaleFundamentalGroups.StrictHenselian

universe u v

variable (A : Type u) (K : Type v) (L : Type u)
  [CommRing A] [IsDomain A] [IsLocalRing A] [Field K] [Field L]
  [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [IsGalois K L] [IsSepClosed L]
  (Q : Ideal (integralClosure A L)) [Q.IsPrime]
  (hQ : Q.under A = IsLocalRing.maximalIdeal A)

/-- The actual ordinary residue point equals the original closed point through κ(A). -/
theorem normalizationOrdinaryResiduePoint_eq :
    let : IsLocalHom (integralClosurePrimeBaseMap A L Q) :=
      integralClosurePrimeBaseMap_isLocalHom A L Q hQ
    let : Algebra (IsLocalRing.ResidueField A)
        (IsLocalRing.ResidueField (Localization.AtPrime Q)) :=
      (IsLocalRing.ResidueField.map (integralClosurePrimeBaseMap A L Q)).toAlgebra
    let : Algebra (ordinaryHenselization A) (Localization.AtPrime Q) :=
      (ordinaryHenselizationToNormalizationPrime A K L Q hQ).toAlgebra
    ξ (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField (Localization.AtPrime Q)) ≫
        henselianClosedPoint (ordinaryHenselization A) (IsLocalRing.ResidueField A)
          (ordinaryHenselizationResidueEquiv A) =
      Spec.algebraMap (ordinaryHenselization A)
        (IsLocalRing.ResidueField (Localization.AtPrime Q)) := by
  intro actualLocal actualResidueAlgebra actualLocalAlgebra
  let H := ordinaryHenselization A
  let R := Localization.AtPrime Q
  let k := IsLocalRing.ResidueField A
  let Ω := IsLocalRing.ResidueField R
  let f : A →+* R := integralClosurePrimeBaseMap A L Q
  let g : H →+* R := ordinaryHenselizationToNormalizationPrime A K L Q hQ
  let β : k →+* Ω := IsLocalRing.ResidueField.map f
  let e : IsLocalRing.ResidueField H ≃+* k := ordinaryHenselizationResidueEquiv A
  have : HenselianLocalRing R := (integralClosure_localizationAtPrime_strictHenselian A K L Q).1
  have : Algebra.IsAlgebraic A L :=
    (IsFractionRing.comap_isAlgebraic_iff (A := A) (K := K) (C := L)).mpr inferInstance
  have : FaithfulSMul A L :=
    (Module.isTorsionFree_iff_faithfulSMul (R := A) (A := L)).mp
      (Module.IsTorsionFree.trans_faithfulSMul A K L)
  have : IsLocalHom g := ordinaryHenselizationLift_isLocalHom f
  let ε : H →+* k := (geometricStalkEvaluation
    (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)))).hom
  have : IsLocalHom ε := geometricStalkEvaluation_isLocalHom
    (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)))
  have hε : e.toRingHom.comp (IsLocalRing.residue H) = ε :=
    IsLocalRing.ResidueField.lift_comp_residue ε
  have hres : (IsLocalRing.residue R).comp g = β.comp ε :=
    ordinaryHenselization_localMap_residue f g
      (ordinaryHenselizationToNormalizationPrime_comp_map A K L Q hQ)
  have hscalar : algebraMap H Ω = β.comp (e.toRingHom.comp (IsLocalRing.residue H)) := by
    calc
      algebraMap H Ω = (IsLocalRing.residue R).comp g := by
        apply RingHom.ext
        intro a
        exact (IsScalarTower.algebraMap_apply H R Ω a).trans
          (RingHom.congr_fun (IsLocalRing.ResidueField.algebraMap_eq (R := R)) (g a))
      _ = β.comp ε := hres
      _ = β.comp (e.toRingHom.comp (IsLocalRing.residue H)) :=
        congrArg (fun z : H →+* k => β.comp z) hε.symm
  change Spec.map (CommRingCat.ofHom β) ≫
    (Spec.map (CommRingCat.ofHom e.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue H))) =
    Spec.map (CommRingCat.ofHom (algebraMap H Ω))
  calc
    _ = Spec.map (CommRingCat.ofHom
        (β.comp (e.toRingHom.comp (IsLocalRing.residue H)))) :=
      (congrArg (fun t : Spec (.of k) ⟶ Spec (.of H) =>
        Spec.map (CommRingCat.ofHom β) ≫ t)
          (Spec.map_comp (CommRingCat.ofHom (IsLocalRing.residue H))
            (CommRingCat.ofHom e.toRingHom)).symm).trans
        (Spec.map_comp
          (CommRingCat.ofHom (e.toRingHom.comp (IsLocalRing.residue H)))
          (CommRingCat.ofHom β)).symm
    _ = _ := congrArg (fun r : H →+* Ω => Spec.map (CommRingCat.ofHom r)) hscalar.symm

/-- The actual strict residue Galois group at the actual closed ordinary point. -/
def normalizationClosedResidueGaloisEquiv :
    let : HenselianLocalRing (Localization.AtPrime Q) :=
      (integralClosure_localizationAtPrime_strictHenselian A K L Q).1
    let : IsSepClosed (IsLocalRing.ResidueField (Localization.AtPrime Q)) :=
      (integralClosure_localizationAtPrime_strictHenselian A K L Q).2
    let : IsLocalHom (integralClosurePrimeBaseMap A L Q) :=
      integralClosurePrimeBaseMap_isLocalHom A L Q hQ
    let φ := (IsLocalRing.residue (Localization.AtPrime Q)).comp
      (integralClosurePrimeBaseMap A L Q)
    let : Algebra A (geometricStalk (Spec.map (CommRingCat.ofHom φ))) :=
      (geometricStalkStructureMap φ).toAlgebra
    let : IsLocalHom (algebraMap A (geometricStalk (Spec.map (CommRingCat.ofHom φ)))) := by
      change IsLocalHom (geometricStalkStructureMap φ)
      exact geometricStalkStructureMap_isLocalHom φ
    let : Algebra (ordinaryHenselization A) (Localization.AtPrime Q) :=
      (ordinaryHenselizationToNormalizationPrime A K L Q hQ).toAlgebra
    Gal(IsLocalRing.ResidueField (geometricStalk (Spec.map (CommRingCat.ofHom φ)))/
        IsLocalRing.ResidueField A) ≃ₜ*
      π₁ᵉᵗ(Spec.algebraMap (ordinaryHenselization A)
        (IsLocalRing.ResidueField (Localization.AtPrime Q))) := by
  intro actualHenselian actualSepClosed actualLocal φ actualStructureAlgebra actualStructureLocal
    actualLocalAlgebra
  let H := ordinaryHenselization A
  let k := IsLocalRing.ResidueField A
  let Ω := IsLocalRing.ResidueField (Localization.AtPrime Q)
  let C := IsLocalRing.ResidueField (geometricStalk (Spec.map (CommRingCat.ofHom φ)))
  let : Algebra k Ω := (IsLocalRing.ResidueField.map (integralClosurePrimeBaseMap A L Q)).toAlgebra
  let j : C →ₐ[k] Ω := geometricStalkResidueAlgHom A Ω
  let : Algebra C Ω := j.toRingHom.toAlgebra
  have : IsScalarTower k C Ω := IsScalarTower.of_algebraMap_eq' j.comp_algebraMap.symm
  have : IsSepClosed C := geometricStalk_residueField_isSepClosed _
  have : IsSepClosure k C := ⟨inferInstance, geometricStalk_residue_isSeparable A Ω φ⟩
  let e := ordinaryHenselizationResidueEquiv A
  let t := eqToIso (congrArg fiber (normalizationOrdinaryResiduePoint_eq A K L Q hQ))
  exact (henselianResidueGaloisEquivFundamentalGroup H k e C Ω).trans
    (CategoryTheory.PreGaloisCategory.continuousConjAut t)

/-- The actual ordinary generic fundamental group is the Galois group of the
actual strict-stalk residue, using the canonical specialization path. -/
def normalizationOrdinaryResidueFundamentalGroupEquiv :
    let : HenselianLocalRing (Localization.AtPrime Q) :=
      (integralClosure_localizationAtPrime_strictHenselian A K L Q).1
    let : IsSepClosed (IsLocalRing.ResidueField (Localization.AtPrime Q)) :=
      (integralClosure_localizationAtPrime_strictHenselian A K L Q).2
    let : IsLocalHom (integralClosurePrimeBaseMap A L Q) :=
      integralClosurePrimeBaseMap_isLocalHom A L Q hQ
    let φ := (IsLocalRing.residue (Localization.AtPrime Q)).comp
      (integralClosurePrimeBaseMap A L Q)
    let : Algebra A (geometricStalk (Spec.map (CommRingCat.ofHom φ))) :=
      (geometricStalkStructureMap φ).toAlgebra
    let : IsLocalHom (algebraMap A (geometricStalk (Spec.map (CommRingCat.ofHom φ)))) := by
      change IsLocalHom (geometricStalkStructureMap φ)
      exact geometricStalkStructureMap_isLocalHom φ
    let : Algebra (ordinaryHenselization A) (Localization.AtPrime Q) :=
      (ordinaryHenselizationToNormalizationPrime A K L Q hQ).toAlgebra
    let : Algebra (ordinaryHenselization A) L :=
      (ordinaryHenselizationToNormalizationField A K L Q hQ).toAlgebra
    π₁ᵉᵗ(Spec.algebraMap (ordinaryHenselization A) L) ≃ₜ*
      Gal(IsLocalRing.ResidueField (geometricStalk (Spec.map (CommRingCat.ofHom φ)))/
        IsLocalRing.ResidueField A) := by
  intro actualHenselian actualSepClosed actualLocal φ actualStructureAlgebra actualStructureLocal
    actualLocalAlgebra actualAmbientAlgebra
  let specialization : π₁ᵉᵗ(Spec.algebraMap (ordinaryHenselization A) L) ≃ₜ*
      π₁ᵉᵗ(Spec.algebraMap (ordinaryHenselization A)
        (IsLocalRing.ResidueField (Localization.AtPrime Q))) :=
    normalizationSpecializationFundamentalGroupEquiv A K L Q hQ
  let closedResidue :
      Gal(IsLocalRing.ResidueField (geometricStalk (Spec.map (CommRingCat.ofHom φ)))/
        IsLocalRing.ResidueField A) ≃ₜ*
      π₁ᵉᵗ(Spec.algebraMap (ordinaryHenselization A)
        (IsLocalRing.ResidueField (Localization.AtPrime Q))) :=
    normalizationClosedResidueGaloisEquiv A K L Q hQ
  exact specialization.trans closedResidue.symm

/-- Retain the actual closed-point comparison as an equality of automorphisms,
before evaluating it on a component of the concrete fiber functor. -/
theorem normalizationClosedResidueGaloisEquiv_apply :
    let : HenselianLocalRing (Localization.AtPrime Q) :=
      (integralClosure_localizationAtPrime_strictHenselian A K L Q).1
    let : IsSepClosed (IsLocalRing.ResidueField (Localization.AtPrime Q)) :=
      (integralClosure_localizationAtPrime_strictHenselian A K L Q).2
    let : IsLocalHom (integralClosurePrimeBaseMap A L Q) :=
      integralClosurePrimeBaseMap_isLocalHom A L Q hQ
    let φ := (IsLocalRing.residue (Localization.AtPrime Q)).comp
      (integralClosurePrimeBaseMap A L Q)
    let : Algebra A (geometricStalk (Spec.map (CommRingCat.ofHom φ))) :=
      (geometricStalkStructureMap φ).toAlgebra
    let : IsLocalHom (algebraMap A (geometricStalk (Spec.map (CommRingCat.ofHom φ)))) := by
      change IsLocalHom (geometricStalkStructureMap φ)
      exact geometricStalkStructureMap_isLocalHom φ
    let : Algebra (ordinaryHenselization A) (Localization.AtPrime Q) :=
      (ordinaryHenselizationToNormalizationPrime A K L Q hQ).toAlgebra
    let H := ordinaryHenselization A
    let k := IsLocalRing.ResidueField A
    let Ω := IsLocalRing.ResidueField (Localization.AtPrime Q)
    let C := IsLocalRing.ResidueField (geometricStalk (Spec.map (CommRingCat.ofHom φ)))
    let : Algebra k Ω :=
      (IsLocalRing.ResidueField.map (integralClosurePrimeBaseMap A L Q)).toAlgebra
    let j : C →ₐ[k] Ω := geometricStalkResidueAlgHom A Ω
    let : Algebra C Ω := j.toRingHom.toAlgebra
    let : IsScalarTower k C Ω := IsScalarTower.of_algebraMap_eq' j.comp_algebraMap.symm
    let : IsSepClosed C := geometricStalk_residueField_isSepClosed _
    let : IsSepClosure k C := ⟨inferInstance, geometricStalk_residue_isSeparable A Ω φ⟩
    let e := ordinaryHenselizationResidueEquiv A
    ∀ σ : Gal(C/k), normalizationClosedResidueGaloisEquiv A K L Q hQ σ =
      CategoryTheory.PreGaloisCategory.continuousConjAut
        (eqToIso (congrArg fiber (normalizationOrdinaryResiduePoint_eq A K L Q hQ)))
        (henselianResidueGaloisEquivFundamentalGroup H k e C Ω σ) := by
  intro actualHenselian actualSepClosed actualLocal φ actualStructureAlgebra actualStructureLocal
    actualLocalAlgebra H k Ω C actualResidueAlgebra j actualEmbeddingAlgebra actualTower
    actualStrictSepClosed actualSepClosure e σ
  rfl

/-- The closed-point comparison has the literal compatible residue-field action. -/
theorem normalizationClosedResidueGaloisEquiv_point :
    let : HenselianLocalRing (Localization.AtPrime Q) :=
      (integralClosure_localizationAtPrime_strictHenselian A K L Q).1
    let : IsSepClosed (IsLocalRing.ResidueField (Localization.AtPrime Q)) :=
      (integralClosure_localizationAtPrime_strictHenselian A K L Q).2
    let : IsLocalHom (integralClosurePrimeBaseMap A L Q) :=
      integralClosurePrimeBaseMap_isLocalHom A L Q hQ
    let φ := (IsLocalRing.residue (Localization.AtPrime Q)).comp
      (integralClosurePrimeBaseMap A L Q)
    let : Algebra A (geometricStalk (Spec.map (CommRingCat.ofHom φ))) :=
      (geometricStalkStructureMap φ).toAlgebra
    let : IsLocalHom (algebraMap A (geometricStalk (Spec.map (CommRingCat.ofHom φ)))) := by
      change IsLocalHom (geometricStalkStructureMap φ)
      exact geometricStalkStructureMap_isLocalHom φ
    let : Algebra (ordinaryHenselization A) (Localization.AtPrime Q) :=
      (ordinaryHenselizationToNormalizationPrime A K L Q hQ).toAlgebra
    ∀ (σ : Gal(IsLocalRing.ResidueField (geometricStalk (Spec.map (CommRingCat.ofHom φ)))/
        IsLocalRing.ResidueField A))
      (ρ : IsLocalRing.ResidueField (Localization.AtPrime Q) →+*
        IsLocalRing.ResidueField (Localization.AtPrime Q)),
      (∀ z, ρ (geometricStalkResidueEmbedding (Spec.map (CommRingCat.ofHom φ)) z) =
        geometricStalkResidueEmbedding (Spec.map (CommRingCat.ofHom φ)) (σ z)) →
      ∀ (X : FiniteEtale (Spec (ordinaryHenselization A)))
        (x : (fiber (Spec.algebraMap (ordinaryHenselization A)
          (IsLocalRing.ResidueField (Localization.AtPrime Q)))).obj X),
        (fiberObjEquivHom (Spec.algebraMap (ordinaryHenselization A)
          (IsLocalRing.ResidueField (Localization.AtPrime Q))) X
            ((normalizationClosedResidueGaloisEquiv A K L Q hQ σ).hom.app X x)).left =
          Spec.map (CommRingCat.ofHom ρ) ≫
            (fiberObjEquivHom (Spec.algebraMap (ordinaryHenselization A)
              (IsLocalRing.ResidueField (Localization.AtPrime Q))) X x).left := by
  intro actualHenselian actualSepClosed actualLocal φ actualStructureAlgebra actualStructureLocal
    actualLocalAlgebra σ ρ hρ X x
  let H := ordinaryHenselization A
  let k := IsLocalRing.ResidueField A
  let Ω := IsLocalRing.ResidueField (Localization.AtPrime Q)
  let C := IsLocalRing.ResidueField (geometricStalk (Spec.map (CommRingCat.ofHom φ)))
  let : Algebra k Ω := (IsLocalRing.ResidueField.map (integralClosurePrimeBaseMap A L Q)).toAlgebra
  let j : C →ₐ[k] Ω := geometricStalkResidueAlgHom A Ω
  let : Algebra C Ω := j.toRingHom.toAlgebra
  have : IsScalarTower k C Ω := IsScalarTower.of_algebraMap_eq' j.comp_algebraMap.symm
  have : IsSepClosed C := geometricStalk_residueField_isSepClosed _
  have : IsSepClosure k C := ⟨inferInstance, geometricStalk_residue_isSeparable A Ω φ⟩
  let e := ordinaryHenselizationResidueEquiv A
  have hcoeff : ρ.comp (algebraMap C Ω) = (algebraMap C Ω).comp σ.toRingHom :=
    RingHom.ext hρ
  have hvalue := normalizationClosedResidueGaloisEquiv_apply A K L Q hQ σ
  exact (congrArg (fun a : π₁ᵉᵗ(Spec.algebraMap H Ω) =>
    (fiberObjEquivHom (Spec.algebraMap H Ω) X (a.hom.app X x)).left) hvalue).trans
      (point_action_of_eqToIso (normalizationOrdinaryResiduePoint_eq A K L Q hQ)
        (henselianResidueGaloisEquivFundamentalGroup H k e C Ω σ) ρ
        (henselianResidueGaloisEquivFundamentalGroup_point H k e C Ω σ ρ hcoeff) X x)

end EtaleFundamentalGroups.StrictHenselian
