/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SchemeTheory.RingTheory.Ramification.FiniteLevelInertiaImage
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# Finite Galois quotients killing every original normalization inertia

The original inertia image theorem and lying over show that a finite Galois
restriction kills all inertia in an arbitrary Galois normalization exactly
when every inertia group in the finite normalization is trivial. Neither
normalization is assumed module finite over the base.
-/

namespace EtaleFundamentalGroups.Inertia

universe u v w

private theorem exists_prime_comap_mapIntegralClosure
    {A : Type u} {R : Type v} {S : Type w}
    [CommRing A] [CommRing R] [CommRing S] [IsDomain S]
    [Algebra A R] [Algebra A S]
    (f : R →ₐ[A] S) (hf : Function.Injective f)
    (q : Ideal (integralClosure A R)) [q.IsPrime] :
    ∃ Q : Ideal (integralClosure A S), Q.IsPrime ∧
      Q.comap f.mapIntegralClosure = q := by
  let : Algebra (integralClosure A R) (integralClosure A S) :=
    f.mapIntegralClosure.toRingHom.toAlgebra
  have : IsScalarTower A (integralClosure A R) (integralClosure A S) :=
    IsScalarTower.of_algebraMap_eq' f.mapIntegralClosure.comp_algebraMap.symm
  have : Algebra.IsIntegral (integralClosure A R) (integralClosure A S) :=
    ⟨fun b => (Algebra.IsIntegral.isIntegral (R := A) b).tower_top⟩
  have hinj : Function.Injective
      (algebraMap (integralClosure A R) (integralClosure A S)) := by
    intro b c h
    apply Subtype.ext
    exact hf (congrArg Subtype.val h)
  have hker : RingHom.ker
      (algebraMap (integralClosure A R) (integralClosure A S)) ≤ q := by
    rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]
    exact bot_le
  exact Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain q hker

attribute [local instance] normalizationInertiaImageAction

variable (A : Type u) (K : Type v) (L : Type w)
  [CommRing A] [Field K] [Field L]
  [Algebra A K] [IsFractionRing A K]
  [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]

/-- All original inertia in the possibly infinite normalization fixes a
finite Galois subfield exactly when every original inertia in that finite
normalization is trivial. Every finite prime is reached by lying over. -/
theorem all_normalization_inertia_le_fixingSubgroup_iff
    (E : FiniteGaloisIntermediateField K L) :
    (∀ (Q : Ideal (integralClosure A L)) [Q.IsPrime],
      Q.inertia Gal(L/K) ≤ E.toIntermediateField.fixingSubgroup) ↔
    ∀ (q : Ideal (integralClosure A E)) [q.IsPrime], q.inertia Gal(E/K) = ⊥ := by
  have : IsScalarTower A E L :=
    Subalgebra.isScalarTower_mid (S := E.toIntermediateField.toSubalgebra)
      (α := A) (β := L)
  constructor
  · intro h q hq
    obtain ⟨Q, hQ, hQq⟩ := exists_prime_comap_mapIntegralClosure
      (IsScalarTower.toAlgHom A E L) (algebraMap E L).injective q
    have : Q.IsPrime := hQ
    rw [← hQq,
      ← integralClosure_inertia_map_eq_finiteGalois_contraction A K L E Q]
    apply (Subgroup.map_eq_bot_iff (Q.inertia Gal(L/K))).mpr
    rw [IntermediateField.restrictNormalHom_ker E.toIntermediateField]
    exact h Q
  · intro h Q hQ
    have : (Q.comap (IsScalarTower.toAlgHom A E L).mapIntegralClosure).IsPrime :=
      Ideal.IsPrime.comap (IsScalarTower.toAlgHom A E L).mapIntegralClosure
    rw [← IntermediateField.restrictNormalHom_ker E.toIntermediateField,
      ← Subgroup.map_eq_bot_iff,
      integralClosure_inertia_map_eq_finiteGalois_contraction A K L E Q]
    exact h (Q.comap (IsScalarTower.toAlgHom A E L).mapIntegralClosure)

end EtaleFundamentalGroups.Inertia
