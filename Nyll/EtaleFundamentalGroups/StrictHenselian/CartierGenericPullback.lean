/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.StrictHenselian.CartierGenericPoint
import Nyll.SchemeTheory.RingTheory.DVRFractionFieldAway
import Nyll.SchemeTheory.Divisors.RegularCartier

/-!
# The Cartier complement over the actual strict henselization

At a boundary point with discrete valuation stalk, the inverse image of the
Cartier complement in the actual geometric etale stalk is its generic point.
The pullback uses the previously constructed generic morphism and the actual
structure map; no comparison morphism is supplied as extra data.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace EtaleFundamentalGroups.StrictHenselian

universe u

/-- The strict-Henselian generic morphism is the actual base change of the
Cartier complement along the geometric-stalk structure morphism. -/
theorem isPullback_geometricStalkFractionFieldToComplement
    {X : Scheme.{u}} (D : X.EffectiveCartierDivisor) (x : X)
    (hx : x ∈ D.1.support)
    [IsDomain (X.presheaf.stalk x)] [IsDiscreteValuationRing (X.presheaf.stalk x)]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (φ : X.presheaf.stalk x →+* Ω) [IsLocalHom φ] :
    let S := geometricStalk (Spec.map (CommRingCat.ofHom φ))
    IsPullback (geometricStalkFractionFieldToComplement D x φ)
      (Spec.map (CommRingCat.ofHom (algebraMap S (FractionRing S))))
      D.1.supportComplement.ι
      (Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ)) ≫
        X.fromSpecStalk x) := by
  intro S
  let ρ : X.presheaf.stalk x →+* S := geometricStalkStructureMap φ
  obtain ⟨a, ha, hgen⟩ := D.2.exists_regular_stalkIdeal_generator x
  have hideal : D.1.stalkIdeal x ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
    apply (D.1.mem_support_fromSpecStalk_iff_stalkIdeal_le x
      (IsLocalRing.closedPoint (X.presheaf.stalk x))).mp
    rw [Scheme.fromSpecStalk_closedPoint]
    exact hx
  have hanu : ¬ IsUnit a := hideal (by
    rw [hgen]
    exact Ideal.mem_span_singleton_self a)
  have hρa0 : ρ a ≠ 0 := by
    intro hzero
    exact ha.ne_zero ((geometricStalkStructureMap_injective φ)
      (hzero.trans (map_zero ρ).symm))
  have hρanu : ¬ IsUnit (ρ a) := fun h => hanu (isUnit_of_map_unit ρ a h)
  let : IsLocalization.Away (ρ a) (FractionRing S) :=
    SchemeTheory.isLocalizationAway_fractionField_of_isDiscreteValuationRing
      S (FractionRing S) (ρ a) hρa0 hρanu
  let : IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (algebraMap S (FractionRing S)))) :=
    IsOpenImmersion.of_isLocalization (ρ a)
  apply IsOpenImmersion.isPullback
  · symm
    have hcomp := Spec.map_comp (CommRingCat.ofHom ρ)
      (CommRingCat.ofHom (algebraMap S (FractionRing S)))
    exact (geometricStalkFractionFieldToComplement_comp_ι D x φ).trans
      ((congrArg (fun k : Spec (.of (FractionRing S)) ⟶ Spec (X.presheaf.stalk x) =>
        k ≫ X.fromSpecStalk x) hcomp).trans (Category.assoc _ _ _))
  · rw [Scheme.Opens.opensRange_ι, Scheme.Hom.comp_preimage,
      D.1.fromSpecStalk_preimage_supportComplement, hgen,
      PrimeSpectrum.idealComplement_span_singleton]
    change PrimeSpectrum.basicOpen (ρ a) = _
    apply TopologicalSpace.Opens.ext
    exact (PrimeSpectrum.localization_away_comap_range (FractionRing S) (ρ a)).symm

end EtaleFundamentalGroups.StrictHenselian
