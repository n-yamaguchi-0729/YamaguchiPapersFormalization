/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.LocalGeometry.HeightOne.CartierComponentStalkDVR
import SchemeTheory.Divisors.LocalComplement
import Mathlib.AlgebraicGeometry.OpenImmersion

/-!
# The local fraction field as a point of the Cartier complement

At a point whose stalk is a domain, a local Cartier equation remains a
nonzero element in the fraction field. Consequently the canonical map from
the spectrum of that field to the ambient scheme factors through the
complement of the Cartier support. The factorization is constructed with the
open immersion's universal property and its composite is proved to be the
canonical fraction-field-to-stalk morphism.

At the generic point of a boundary component, the required domain instance
is supplied by `isDomain_stalk_componentGenericPoint`, proved from the
paper's regularity-along-the-boundary assumption. This map allows actual
finite etale covers of the complement to be pulled back to the local
fraction field; it is not additional comparison data.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry.Scheme.IdealSheafData

universe u

variable {X : Scheme.{u}} {I : X.IdealSheafData}

/-- The local fraction-field point misses every effective Cartier support. -/
theorem IsEffectiveCartier.fractionStalkPoint_mem_supportComplement
    (hI : I.IsEffectiveCartier) (x : X) [IsDomain (X.presheaf.stalk x)]
    (y : Spec (.of (FractionRing (X.presheaf.stalk x)))) :
    (Spec.map (CommRingCat.ofHom
        (algebraMap (X.presheaf.stalk x)
          (FractionRing (X.presheaf.stalk x)))) ≫ X.fromSpecStalk x) y ∈
      I.supportComplement := by
  change X.fromSpecStalk x
    (Spec.map (CommRingCat.ofHom
      (algebraMap (X.presheaf.stalk x)
        (FractionRing (X.presheaf.stalk x)))) y) ∉ I.support
  rw [I.mem_support_fromSpecStalk_iff_stalkIdeal_le]
  have hprime :
      (Spec.map (CommRingCat.ofHom
        (algebraMap (X.presheaf.stalk x)
          (FractionRing (X.presheaf.stalk x)))) y).asIdeal = ⊥ := by
    have hy : y = (⊥ : PrimeSpectrum (FractionRing (X.presheaf.stalk x))) :=
      Subsingleton.elim _ _
    rw [hy]
    change RingHom.ker
      (algebraMap (X.presheaf.stalk x)
        (FractionRing (X.presheaf.stalk x))) = ⊥
    exact (RingHom.injective_iff_ker_eq_bot
      (algebraMap (X.presheaf.stalk x)
        (FractionRing (X.presheaf.stalk x)))).mp
      (IsFractionRing.injective (X.presheaf.stalk x)
        (FractionRing (X.presheaf.stalk x)))
  rw [hprime]
  intro hle
  obtain ⟨a, ha, hgen⟩ := hI.exists_regular_stalkIdeal_generator x
  have haI : a ∈ I.stalkIdeal x := by
    rw [hgen]
    exact Ideal.mem_span_singleton_self a
  exact ha.ne_zero (Ideal.mem_bot.mp (hle haI))

/-- The canonical local fraction-field map, factored through the actual
open complement of an effective Cartier divisor. -/
def IsEffectiveCartier.fractionStalkToSupportComplement
    (hI : I.IsEffectiveCartier) (x : X) [IsDomain (X.presheaf.stalk x)] :
    Spec (.of (FractionRing (X.presheaf.stalk x))) ⟶ I.supportComplement :=
  IsOpenImmersion.lift I.supportComplement.ι
    (Spec.map (CommRingCat.ofHom
      (algebraMap (X.presheaf.stalk x)
        (FractionRing (X.presheaf.stalk x)))) ≫ X.fromSpecStalk x)
    (by
      rintro _ ⟨y, rfl⟩
      exact ⟨⟨_, hI.fractionStalkPoint_mem_supportComplement x y⟩, rfl⟩)

/-- The constructed local map lies over the canonical map to `X`. -/
@[reassoc]
theorem IsEffectiveCartier.fractionStalkToSupportComplement_comp_ι
    (hI : I.IsEffectiveCartier) (x : X) [IsDomain (X.presheaf.stalk x)] :
    hI.fractionStalkToSupportComplement x ≫ I.supportComplement.ι =
      Spec.map (CommRingCat.ofHom
        (algebraMap (X.presheaf.stalk x)
          (FractionRing (X.presheaf.stalk x)))) ≫ X.fromSpecStalk x :=
  IsOpenImmersion.lift_fac _ _ _

end AlgebraicGeometry.Scheme.IdealSheafData
