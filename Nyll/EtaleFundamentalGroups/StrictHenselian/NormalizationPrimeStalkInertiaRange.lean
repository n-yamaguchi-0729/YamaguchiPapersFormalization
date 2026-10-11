/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.FiniteLevelEtaleColimit
import Nyll.EtaleFundamentalGroups.Inertia.FiniteLevelEtaleDiagram
import Nyll.EtaleFundamentalGroups.Inertia.FiniteLevelEtaleNeighborhoods
import Nyll.EtaleFundamentalGroups.Inertia.InvariantPrimeLocalizationMap
import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkHenselianEtaleRange
import Nyll.EtaleFundamentalGroups.StrictHenselian.NormalizationPrime
import Nyll.EtaleFundamentalGroups.StrictHenselian.NormalizationPrimeEmbedding
import Nyll.SchemeTheory.RingTheory.Ramification.FiniteLevelInertiaLocalization
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-!
# The inertia-invariant localization lies in the actual stalk-map range

The existing genuine etale colimit provides a finite principal etale
representative of an element of the inertia-invariant localization. Its
actual map into the normalization prime localization has the original base
square, so the proved geometric-stalk etale factorization supplies a
preimage. This concerns the invariant-localization image only.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace EtaleFundamentalGroups.StrictHenselian

open EtaleFundamentalGroups.Inertia

universe u v

attribute [local instance] normalizationInertiaImageAction normalizationInertiaImageTower
  normalizationInertiaCoefficientCommClass inertiaInvariantPrime_isPrime
  finiteLevelInertiaPrime_isPrime

/-- Every element of the original inertia-invariant prime localization has
an actual preimage under the geometric-stalk map to the normalization prime
localization. The strict target and its separably closed residue field are
supplied by the original separably closed ambient field. -/
theorem inertiaInvariantPrimeLocalization_exists_geometricStalk_preimage
    (A : Type u) (K : Type v) (L : Type u)
    [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsGalois K L] [IsSepClosed L]
    (Q : Ideal (integralClosure A L)) [Q.IsPrime]
    (z : inertiaInvariantPrimeLocalizationAlgebra A K L Q) :
    let : HenselianLocalRing (Localization.AtPrime Q) :=
      (integralClosure_localizationAtPrime_strictHenselian A K L Q).1
    let : IsSepClosed (IsLocalRing.ResidueField (Localization.AtPrime Q)) :=
      (integralClosure_localizationAtPrime_strictHenselian A K L Q).2
    ∃ a : geometricStalk (Spec.map (CommRingCat.ofHom
        ((IsLocalRing.residue (Localization.AtPrime Q)).comp
          (integralClosurePrimeBaseMap A L Q)))),
      geometricStalkToHenselian (integralClosurePrimeBaseMap A L Q) a =
        inertiaInvariantPrimeLocalizationMap A K L Q z := by
  intro actualHenselian actualSepClosed
  obtain ⟨X, x, hx⟩ := Concrete.isColimit_exists_rep
    (finiteLevelEtaleDiagram A K L Q ⋙ forget₂ (CommAlgCat.{u} A) (AlgCat.{u} A))
    (finiteLevelEtaleCoconeIsColimit A K L Q) z
  let B : CommAlgCat.{u} A := (finiteLevelEtaleDiagram A K L Q).obj X
  let U : CommAlgCat.{u} A := inertiaInvariantPrimeLocalizationAlgebra A K L Q
  let j : B →ₐ[A] U := finiteLevelEtaleNeighborhoodInclusion A K L Q X
  have hjx : j x = z := hx
  have : Algebra.Etale A B := X.etale
  let g : B →+* Localization.AtPrime Q :=
    (inertiaInvariantPrimeLocalizationMap A K L Q).comp j.toRingHom
  have hupper : (inertiaInvariantPrimeLocalizationMap A K L Q).comp
      (algebraMap A U) = integralClosurePrimeBaseMap A L Q :=
    (congrArg
      (fun c : A →+* U => (inertiaInvariantPrimeLocalizationMap A K L Q).comp c)
      (inertiaInvariantPrimeLocalizationBaseMap_eq_algebraMap A K L Q)).symm.trans
        (inertiaInvariantPrimeLocalizationMap_comp_base A K L Q)
  have hbase : g.comp (algebraMap A B) = integralClosurePrimeBaseMap A L Q :=
    (RingHom.comp_assoc (algebraMap A B) j.toRingHom
      (inertiaInvariantPrimeLocalizationMap A K L Q)).trans
        ((congrArg
          (fun c : A →+* U => (inertiaInvariantPrimeLocalizationMap A K L Q).comp c)
          j.comp_algebraMap).trans hupper)
  obtain ⟨a, ha⟩ := geometricStalkToHenselian_exists_preimage_of_etale
    (integralClosurePrimeBaseMap A L Q) g hbase x
  exact ⟨a, ha.trans (congrArg (inertiaInvariantPrimeLocalizationMap A K L Q) hjx)⟩

end EtaleFundamentalGroups.StrictHenselian
