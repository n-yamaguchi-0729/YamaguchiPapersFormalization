/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.StrictHenselian.NormalizationFiberDegreeCriterion
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.Localization.FractionRing

/-!
# The closed-fiber criterion with the original fraction field

Transport only the scalar action along the canonical fraction-field
isomorphism. The ambient algebra and its integral closure remain unchanged,
and the native dimension comparison preserves the original generic degree.
-/

noncomputable section

namespace EtaleFundamentalGroups

open scoped TensorProduct

universe u

/-- The normalization closed-fiber criterion for an arbitrary chosen
fraction field, preserving the original algebra and its field degree. -/
theorem integralClosure_etale_of_local_fiber_degree
    {R Ω : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsLocalRing R]
    [Field Ω] [IsSepClosed Ω] (φ : R →+* Ω) [IsLocalHom φ]
    (K L : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    [CommRing L] [Algebra R L] [Algebra K L] [IsScalarTower R K L]
    [Module.Finite K L]
    [Algebra.Etale (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField R ⊗[R] integralClosure R L)]
    (hdegree : Module.finrank K L ≤ Module.finrank (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField R ⊗[R] integralClosure R L)) :
    Algebra.Etale R (integralClosure R L) := by
  let Q := FractionRing R
  let e : Q ≃ₐ[R] K := IsLocalization.algEquiv (nonZeroDivisors R) Q K
  let : Algebra Q K := e.toRingHom.toAlgebra
  let : Algebra Q L := ((algebraMap K L).comp e.toRingHom).toAlgebra
  have : IsScalarTower Q K L := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower R Q L := IsScalarTower.of_algebraMap_eq <| by
    intro r
    change algebraMap R L r = algebraMap K L (e (algebraMap R Q r))
    rw [e.commutes, ← IsScalarTower.algebraMap_apply R K L]
  have : Module.Finite Q K :=
    Module.Finite.of_surjective (Algebra.linearMap Q K) e.surjective
  have : Module.Finite Q L := Module.Finite.trans K L
  have hdimension : Module.finrank Q L = Module.finrank K L :=
    Algebra.finrank_eq_of_equiv_equiv e.toRingEquiv (RingEquiv.refl L) rfl
  apply StrictHenselian.integralClosure_etale_of_normal_local_fiber_degree φ L
  exact hdimension.trans_le hdegree

end EtaleFundamentalGroups
