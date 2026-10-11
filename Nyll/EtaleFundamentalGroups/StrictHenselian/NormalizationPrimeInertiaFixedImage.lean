/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.StrictHenselian.NormalizationPrime
import Nyll.EtaleFundamentalGroups.StrictHenselian.NormalizationPrimeEmbedding
import Nyll.EtaleFundamentalGroups.StrictHenselian.NormalizationPrimeInertia
import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkHenselianMap
import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkHenselianRigidity
import Nyll.SchemeTheory.RingTheory.Ramification.FiniteLevelInertiaImage
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.RingTheory.Henselian

/-!
# Original normalization inertia fixes the actual stalk image

The target is the literal prime localization of the original integral
closure. Its strict Henselian properties have already been constructed.
The original inertia element supplies an actual native local automorphism
with the proved base and residue squares, so the existing stalk rigidity
theorem fixes the constructed map. No fixed-image or comparison premise is
introduced; the reverse image and ambient fraction-field identifications
remain separate.
-/

noncomputable section

namespace EtaleFundamentalGroups.StrictHenselian

open EtaleFundamentalGroups.Inertia

universe u v

attribute [local instance] normalizationInertiaImageAction

/-- Every original normalization inertia element fixes the actual
geometric-stalk map into the literal prime localization. -/
theorem normalizationPrimeInertia_comp_geometricStalkMap
    (A : Type u) (K : Type v) (L : Type u)
    [CommRing A] [IsDomain A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsGalois K L] [IsSepClosed L]
    (Q : Ideal (integralClosure A L)) [Q.IsPrime]
    (σ : Gal(L/K)) (hσ : σ ∈ Q.inertia Gal(L/K)) :
    let : HenselianLocalRing (Localization.AtPrime Q) :=
      (integralClosure_localizationAtPrime_strictHenselian A K L Q).1
    let : IsSepClosed (IsLocalRing.ResidueField (Localization.AtPrime Q)) :=
      (integralClosure_localizationAtPrime_strictHenselian A K L Q).2
    (normalizationPrimeInertiaRingEquiv A K L Q σ hσ).toRingHom.comp
        (geometricStalkToHenselian (integralClosurePrimeBaseMap A L Q)) =
      geometricStalkToHenselian (integralClosurePrimeBaseMap A L Q) := by
  intro actualHenselian actualSepClosed
  exact geometricStalkToHenselian_comp_endomorphism (integralClosurePrimeBaseMap A L Q)
    (normalizationPrimeInertiaRingEquiv A K L Q σ hσ).toRingHom
    (normalizationPrimeInertiaRingEquiv_comp_baseMap A K L Q σ hσ)
    (normalizationPrimeInertiaRingEquiv_comp_residue A K L Q σ hσ)

end EtaleFundamentalGroups.StrictHenselian
