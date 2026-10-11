/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.InvariantPrimeLocalizationMap
import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkHenselianMap
import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkStructure
import Nyll.EtaleFundamentalGroups.StrictHenselian.NormalizationPrimeEmbedding
import Nyll.EtaleFundamentalGroups.StrictHenselian.NormalizationPrimeField
import Nyll.EtaleFundamentalGroups.StrictHenselian.NormalizationPrimeStalkFraction
import Nyll.EtaleFundamentalGroups.StrictHenselian.NormalizationPrimeStalkInertiaRange
import Nyll.SchemeTheory.RingTheory.Localization.SubalgebraPrime
import Nyll.SchemeTheory.RingTheory.Ramification.InertiaFixedIntegralMultiple
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.Localization.FractionRing

/-!
# The actual geometric-stalk fraction image is the inertia-fixed field

The original fixed-field numerator theorem makes an inertia-fixed field
element integral after multiplication by a nonzero base coefficient. The
actual invariant-localization range theorem supplies a stalk preimage of
that numerator. The original coefficient is still nonzero in the ambient
field, so division in the actual stalk fraction ring gives the required
preimage. The reverse implication is the existing forward inertia theorem.
-/

noncomputable section

open AlgebraicGeometry

namespace EtaleFundamentalGroups.StrictHenselian

open EtaleFundamentalGroups.Inertia SchemeTheory

universe u v

attribute [local instance] normalizationInertiaImageAction normalizationInertiaCoefficientCommClass

/-- The image of the actual geometric-stalk fraction field in the original
ambient separably closed Galois field is exactly the elements fixed by the
original normalization inertia. A nonzero base coefficient is inverted only
in the fraction ring; it is not required to avoid the normalization prime. -/
theorem geometricStalkFractionToNormalizationField_mem_range_iff
    (A : Type u) (K : Type v) (L : Type u)
    [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsLocalRing A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L] [IsSepClosed L]
    (Q : Ideal (integralClosure A L)) [Q.IsMaximal] (x : L) :
    let : Algebra.IsAlgebraic A L :=
      (IsFractionRing.comap_isAlgebraic_iff (A := A) (K := K) (C := L)).mpr inferInstance
    let : FaithfulSMul A L :=
      (Module.isTorsionFree_iff_faithfulSMul (R := A) (A := L)).mp
        (Module.IsTorsionFree.trans_faithfulSMul A K L)
    let : HenselianLocalRing (Localization.AtPrime Q) :=
      (integralClosure_primeLocalization_strictHenselian_of_algebraic A L Q).1
    let : IsSepClosed (IsLocalRing.ResidueField (Localization.AtPrime Q)) :=
      (integralClosure_primeLocalization_strictHenselian_of_algebraic A L Q).2
    x ∈ (geometricStalkFractionToNormalizationField A L Q).range ↔
      ∀ σ ∈ Q.inertia Gal(L/K), σ x = x := by
  intro actualAlgebraic actualFaithful actualHenselian actualSepClosed
  constructor
  · rintro ⟨y, rfl⟩ σ hσ
    exact RingHom.congr_fun
      (geometricStalkFractionToNormalizationField_comp_inertia A K L Q σ hσ) y
  · intro hx
    obtain ⟨a, ha, b, hb, hbfixed⟩ :=
      integralClosure_exists_inertia_fixed_integral_multiple A K L Q x hx
    let C := integralClosure A L
    let I := normalizationInertiaFixedSubalgebra A K L Q
    let bI : I := ⟨b, fun σ => hbfixed σ.val σ.property⟩
    let U : CommAlgCat.{u} A := inertiaInvariantPrimeLocalizationAlgebra A K L Q
    let z : U := (primeLocalizationComapCoefficientMap I.val.toRingHom Q).toFun bI
    obtain ⟨s, hs⟩ :=
      inertiaInvariantPrimeLocalization_exists_geometricStalk_preimage A K L Q z
    let S := geometricStalk (Spec.map (CommRingCat.ofHom
      ((IsLocalRing.residue (Localization.AtPrime Q)).comp
        (integralClosurePrimeBaseMap A L Q))))
    have : IsDomain S :=
      (geometricStalkToIntegralClosurePrime_injective A L Q
        (integralClosure_maximalPrime_under A L Q)).isDomain
          (geometricStalkToHenselian (integralClosurePrimeBaseMap A L Q))
    let f : FractionRing S →+* L := geometricStalkFractionToNormalizationField A L Q
    have hcomp := geometricStalkFractionToNormalizationField_comp_stalk A K L Q
    have hnormal : inertiaInvariantPrimeLocalizationMap A K L Q z =
        algebraMap C (Localization.AtPrime Q) b :=
      RingHom.congr_fun (primeLocalizationComapMap_comp_coefficient I.val.toRingHom Q) bI
    have hnum : f (algebraMap S (FractionRing S) s) = b.val :=
      (RingHom.congr_fun hcomp s).trans
        ((congrArg (integralClosurePrimeToAmbientField A K L Q)
          (hs.trans hnormal)).trans
            (RingHom.congr_fun
              (integralClosurePrimeToAmbientField_comp_coefficient A K L Q) b))
    let t : S := geometricStalkStructureMap
      ((IsLocalRing.residue (Localization.AtPrime Q)).comp
        (integralClosurePrimeBaseMap A L Q)) a
    have hden : f (algebraMap S (FractionRing S) t) = algebraMap A L a :=
      (RingHom.congr_fun hcomp t).trans
        ((congrArg (integralClosurePrimeToAmbientField A K L Q)
          (RingHom.congr_fun
            (geometricStalkToHenselian_comp_structure (integralClosurePrimeBaseMap A L Q)) a)).trans
              (RingHom.congr_fun
                (integralClosurePrimeToAmbientField_comp_baseMap A K L Q) a))
    have hane : algebraMap A L a ≠ 0 := by
      intro h
      exact ha ((FaithfulSMul.algebraMap_injective A L)
        (h.trans (map_zero (algebraMap A L)).symm))
    refine ⟨algebraMap S (FractionRing S) s / algebraMap S (FractionRing S) t, ?_⟩
    change f (algebraMap S (FractionRing S) s / algebraMap S (FractionRing S) t) = x
    rw [map_div₀, hnum, hden]
    apply (div_eq_iff hane).mpr
    exact hb.trans ((Algebra.smul_def a x).trans (mul_comm (algebraMap A L a) x))

/-- The literal embedded fraction field of the geometric stalk is the
original inertia-fixed intermediate field, stated as equality of their
subrings in the same ambient field. -/
theorem geometricStalkFractionToNormalizationField_range_eq_fixedField
    (A : Type u) (K : Type v) (L : Type u)
    [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsLocalRing A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L] [IsSepClosed L]
    (Q : Ideal (integralClosure A L)) [Q.IsMaximal] :
    let : Algebra.IsAlgebraic A L :=
      (IsFractionRing.comap_isAlgebraic_iff (A := A) (K := K) (C := L)).mpr inferInstance
    let : FaithfulSMul A L :=
      (Module.isTorsionFree_iff_faithfulSMul (R := A) (A := L)).mp
        (Module.IsTorsionFree.trans_faithfulSMul A K L)
    let : HenselianLocalRing (Localization.AtPrime Q) :=
      (integralClosure_primeLocalization_strictHenselian_of_algebraic A L Q).1
    let : IsSepClosed (IsLocalRing.ResidueField (Localization.AtPrime Q)) :=
      (integralClosure_primeLocalization_strictHenselian_of_algebraic A L Q).2
    (geometricStalkFractionToNormalizationField A L Q).range =
      (IntermediateField.fixedField (Q.inertia Gal(L/K))).toSubalgebra.toSubring := by
  intro actualAlgebraic actualFaithful actualHenselian actualSepClosed
  apply Subring.ext
  intro x
  exact (geometricStalkFractionToNormalizationField_mem_range_iff A K L Q x).trans
    (IntermediateField.mem_fixedField_iff (Q.inertia Gal(L/K)) x).symm

end EtaleFundamentalGroups.StrictHenselian
