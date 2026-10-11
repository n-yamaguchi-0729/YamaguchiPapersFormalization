/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.DivisorialQuotientFieldSource

/-!
# Absolute normalization-prime inertia

Fixing a prime in the normalization inside one separable closure gives a
single absolute inertia subgroup.  Its restriction to every finite normal
subextension lies in the inertia subgroup of the contracted prime.  This is
the field-theoretic model of divisorial inertia and does not require a
separate strict-henselization construction.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

universe uA u

variable {A : Type uA} {K L Omega : Type u}
variable [CommRing A]
variable [Field K] [Field L] [Field Omega]
variable [Algebra A K] [IsFractionRing A K]
variable [Algebra K L] [Algebra A L] [IsScalarTower A K L]
variable [FiniteDimensional K L] [_root_.IsGalois K L]
variable [Algebra K Omega] [Algebra A Omega] [IsScalarTower A K Omega]
variable [Algebra L Omega] [IsScalarTower K L Omega]
variable [IsScalarTower A L Omega]
variable [Algebra.IsAlgebraic K Omega]

local notation "B" => integralClosure A L
local notation "C" => integralClosure A Omega

/-- The map between normalizations induced by a chosen embedding of a finite
normal extension into the fixed separable closure. -/
noncomputable def finiteNormalizationToAbsoluteNormalization : B →ₐ[A] C :=
  (IsScalarTower.toAlgHom A L Omega).mapIntegralClosure

/-- Contraction of an absolute normalization prime to a finite normal
subextension. -/
noncomputable def absoluteNormalizationPrimeContraction
    (Q : Ideal C) : Ideal B :=
  Q.comap (finiteNormalizationToAbsoluteNormalization
    (A := A) (L := L) (Omega := Omega))

instance absoluteNormalizationPrimeContraction_isPrime
    (Q : Ideal C) [Q.IsPrime] :
    (absoluteNormalizationPrimeContraction
      (A := A) (L := L) (Omega := Omega) Q).IsPrime := by
  change (Q.comap (finiteNormalizationToAbsoluteNormalization
    (A := A) (L := L) (Omega := Omega))).IsPrime
  exact Ideal.IsPrime.comap
    (finiteNormalizationToAbsoluteNormalization
      (A := A) (L := L) (Omega := Omega))

instance absoluteNormalizationPrimeContraction_liesOver
    (P : Ideal A) (Q : Ideal C) [Q.LiesOver P] :
    (absoluteNormalizationPrimeContraction
      (A := A) (L := L) (Omega := Omega) Q).LiesOver P := by
  change (Q.comap (finiteNormalizationToAbsoluteNormalization
    (A := A) (L := L) (Omega := Omega))).LiesOver P
  exact Ideal.comap_liesOver Q P
    (finiteNormalizationToAbsoluteNormalization
      (A := A) (L := L) (Omega := Omega))

local instance finiteNormalization_galoisAction :
    MulSemiringAction Gal(L/K) B :=
  IsIntegralClosure.MulSemiringAction A K L B

local instance absoluteNormalization_galoisAction :
    MulSemiringAction Gal(Omega/K) C :=
  IsIntegralClosure.MulSemiringAction A K Omega C

omit [FiniteDimensional K L] in
/-- Absolute inertia restricts into inertia at the contracted prime in every
finite normal subextension. -/
theorem absoluteNormalizationPrime_inertia_map_le_contraction
    (Q : Ideal C) [Q.IsPrime] :
    Subgroup.map
        (AlgEquiv.restrictNormalHom (F := K) (K₁ := Omega) L)
        (Q.toAddSubgroup.inertia Gal(Omega/K)) ≤
      (absoluteNormalizationPrimeContraction
        (A := A) (L := L) (Omega := Omega) Q).toAddSubgroup.inertia
          Gal(L/K) := by
  rintro tau ⟨sigma, hsigma, rfl⟩
  intro x
  change
    (finiteNormalizationToAbsoluteNormalization
      (A := A) (L := L) (Omega := Omega))
        ((AlgEquiv.restrictNormalHom (F := K) (K₁ := Omega) L sigma) • x - x) ∈ Q
  have h := hsigma
    ((finiteNormalizationToAbsoluteNormalization
      (A := A) (L := L) (Omega := Omega)) x)
  have haction :
      (finiteNormalizationToAbsoluteNormalization
        (A := A) (L := L) (Omega := Omega))
          ((AlgEquiv.restrictNormalHom (F := K) (K₁ := Omega) L sigma) • x) =
        sigma •
          (finiteNormalizationToAbsoluteNormalization
            (A := A) (L := L) (Omega := Omega)) x := by
    apply Subtype.ext
    change
      algebraMap L Omega
          (algebraMap B L
            (galRestrict A K L B
              (AlgEquiv.restrictNormalHom (F := K) (K₁ := Omega) L sigma) x)) =
        algebraMap C Omega
          (galRestrict A K Omega C sigma
            ((finiteNormalizationToAbsoluteNormalization
              (A := A) (L := L) (Omega := Omega)) x))
    rw [algebraMap_galRestrict_apply A, algebraMap_galRestrict_apply A]
    exact
      (AlgEquiv.restrictNormal_commutes sigma L
        (algebraMap B L x)).trans (by rfl)
  rw [map_sub, haction]
  exact h

end EtaleFundamentalGroups.Inertia

end
