/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.CartierLocalFractionField
import Nyll.SchemeTheory.RingTheory.FieldExtensions.DVRFractionFieldAway
import Nyll.SchemeTheory.Divisors.RegularCartier

/-!
# The actual fraction-stalk pullback of a Cartier complement

At a divisor point with discrete valuation stalk, the inverse image of the
complement is the spectrum of the actual fraction field. The horizontal map
is the previously constructed canonical factorization through the complement.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.IdealSheafData

universe u

/-- At a discrete valuation stalk on an effective Cartier divisor, the
canonical fraction-field diagram is the pullback of the actual complement. -/
theorem IsEffectiveCartier.isPullback_fractionStalkToSupportComplement
    {X : Scheme.{u}} {I : X.IdealSheafData}
    (hI : I.IsEffectiveCartier) (x : X) (hx : x ∈ I.support)
    [IsDomain (X.presheaf.stalk x)] [IsDiscreteValuationRing (X.presheaf.stalk x)] :
    IsPullback (hI.fractionStalkToSupportComplement x)
      (Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x)
        (FractionRing (X.presheaf.stalk x)))))
      I.supportComplement.ι (X.fromSpecStalk x) := by
  obtain ⟨a, ha, hgen⟩ := hI.exists_regular_stalkIdeal_generator x
  have hideal : I.stalkIdeal x ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
    apply (I.mem_support_fromSpecStalk_iff_stalkIdeal_le x
      (IsLocalRing.closedPoint (X.presheaf.stalk x))).mp
    rw [Scheme.fromSpecStalk_closedPoint]
    exact hx
  have hanu : ¬ IsUnit a := hideal (by
    rw [hgen]
    exact Ideal.mem_span_singleton_self a)
  let : IsLocalization.Away a (FractionRing (X.presheaf.stalk x)) :=
    SchemeTheory.isLocalizationAway_fractionField_of_isDiscreteValuationRing
      (X.presheaf.stalk x) (FractionRing (X.presheaf.stalk x)) a ha.ne_zero hanu
  let : IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x)
        (FractionRing (X.presheaf.stalk x))))) :=
    IsOpenImmersion.of_isLocalization a
  apply IsOpenImmersion.isPullback
  · exact (hI.fractionStalkToSupportComplement_comp_ι x).symm
  · rw [Scheme.Opens.opensRange_ι, I.fromSpecStalk_preimage_supportComplement,
      hgen, PrimeSpectrum.idealComplement_span_singleton]
    apply TopologicalSpace.Opens.ext
    exact (PrimeSpectrum.localization_away_comap_range
      (FractionRing (X.presheaf.stalk x)) a).symm

end AlgebraicGeometry.Scheme.IdealSheafData
