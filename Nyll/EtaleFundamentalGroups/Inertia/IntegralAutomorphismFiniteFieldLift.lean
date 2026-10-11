/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Finite fraction-field lifts of integral automorphisms

Extends an intrinsic finite-normalization automorphism to a finite extension of fraction fields
with the corresponding coefficient square.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open scoped nonZeroDivisors

universe u v

/-- An intrinsic automorphism of the finite normalization extends to an
actual finite extension of fraction fields. Only the constructed fields,
scalar maps, finiteness, automorphism and coefficient square are returned. -/
theorem integralAutomorphism_exists_finite_field_lift
    (A : Type u) (B : Type v)
    [CommRing A] [IsDomain A] [CommRing B] [IsDedekindDomain B]
    [Algebra A B] [Module.Finite A B] [Module.IsTorsionFree A B]
    (σ : B ≃ₐ[A] B) :
    ∃ (K : Type u) (L : Type v) (kField : Field K) (lField : Field L),
      let : Field K := kField
      let : Field L := lField
      ∃ (bL : Algebra B L),
        let : Algebra B L := bL
        ∃ (kL : Algebra K L),
          let : Algebra K L := kL
          IsFractionRing B L ∧ FiniteDimensional K L ∧
            ∃ ρ : L ≃ₐ[K] L,
              ρ.toRingHom.comp (algebraMap B L) =
                (algebraMap B L).comp σ.toRingHom := by
  let L := FractionRing B
  let ρRing : L ≃+* L := IsFractionRing.ringEquivOfRingEquiv σ.toRingEquiv
  have hcoeff : ρRing.toRingHom.comp (algebraMap B L) =
      (algebraMap B L).comp σ.toRingHom := by
    apply RingHom.ext
    intro b
    exact IsFractionRing.ringEquivOfRingEquiv_algebraMap σ.toRingEquiv b
  let K := FractionRing A
  let akl : Algebra K L := FractionRing.liftAlgebra A L
  have atower : IsScalarTower A K L := FractionRing.isScalarTower_liftAlgebra A L
  have ic : IsIntegralClosure B A L := IsIntegralClosure.of_isIntegrallyClosed _ _ _
  have alg : Algebra.IsAlgebraic K L := isAlgebraic_of_isFractionRing A B K L
  have loc : IsLocalization (Algebra.algebraMapSubmonoid B A⁰) L :=
    IsIntegralClosure.isLocalization A K L B
  have fd : FiniteDimensional K L := .of_isLocalization A B A⁰
  let ρ : L ≃ₐ[K] L := IsFractionRing.fieldEquivOfAlgEquiv K L L σ
  change ρ.toRingHom.comp (algebraMap B L) =
    (algebraMap B L).comp σ.toRingHom at hcoeff
  exact ⟨K, L, inferInstance, inferInstance, inferInstance, akl,
    inferInstance, fd, ρ, hcoeff⟩

end EtaleFundamentalGroups.Inertia
