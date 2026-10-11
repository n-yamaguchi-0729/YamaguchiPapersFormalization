/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.StrictHenselian.NormalizationPrimeOrdinaryDecomposition
import EtaleFundamentalGroups.StrictHenselian.NormalizationPrimeOrdinaryFieldTower
import Mathlib.Algebra.Group.Subgroup.Map

/-!
# Actual ordinary-generic Galois restriction has image original decomposition

The actual original-field map and ordinary fraction embedding form the proved
scalar tower. Restricting scalars along this tower has image exactly the
original stabilizer of the normalization prime, by the proved fixing criterion
for that same ordinary fraction embedding.
-/

noncomputable section

namespace EtaleFundamentalGroups.StrictHenselian

open EtaleFundamentalGroups.Inertia
open scoped Pointwise

universe u v

attribute [local instance] normalizationInertiaImageAction

/-- The relative Galois group of the fraction field of the actual ordinary
henselization maps onto the original decomposition subgroup by literal
restriction of ambient automorphisms. -/
theorem ordinaryHenselizationAbsoluteGalois_restriction_range
    (A : Type u) (K : Type v) (L : Type u)
    [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsLocalRing A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L] [IsSepClosed L]
    (Q : Ideal (integralClosure A L)) [Q.IsPrime]
    (hQ : Q.under A = IsLocalRing.maximalIdeal A) :
    let : IsDomain (ordinaryHenselization A) :=
      geometricStalk_isDomain_of_normal (IsLocalRing.residue A)
    let : Algebra K (FractionRing (ordinaryHenselization A)) :=
      (ordinaryHenselizationFractionBaseMap A K).toAlgebra
    let : Algebra (FractionRing (ordinaryHenselization A)) L :=
      (ordinaryHenselizationFractionToNormalizationField A K L Q hQ).toAlgebra
    let : IsScalarTower K (FractionRing (ordinaryHenselization A)) L :=
      ordinaryHenselizationFractionField_isScalarTower A K L Q hQ
    (AlgEquiv.restrictScalarsHom K :
      Gal(L/FractionRing (ordinaryHenselization A)) →* Gal(L/K)).range =
        MulAction.stabilizer Gal(L/K) Q := by
  intro actualDomain actualBaseAlgebra actualAmbientAlgebra actualTower
  apply Subgroup.ext
  intro σ
  constructor
  · rintro ⟨τ, rfl⟩
    apply (ordinaryHenselizationFractionToNormalizationField_comp_eq_self_iff A K L Q hQ
      (AlgEquiv.restrictScalarsHom K τ)).mp
    apply RingHom.ext
    intro y
    exact τ.commutes y
  · intro hσ
    have hfixed :=
      (ordinaryHenselizationFractionToNormalizationField_comp_eq_self_iff A K L Q hQ σ).mpr hσ
    let τ : Gal(L/FractionRing (ordinaryHenselization A)) :=
      { σ.toRingEquiv with commutes' := fun y => RingHom.congr_fun hfixed y }
    refine ⟨τ, ?_⟩
    apply AlgEquiv.ext
    intro y
    rfl

end EtaleFundamentalGroups.StrictHenselian
