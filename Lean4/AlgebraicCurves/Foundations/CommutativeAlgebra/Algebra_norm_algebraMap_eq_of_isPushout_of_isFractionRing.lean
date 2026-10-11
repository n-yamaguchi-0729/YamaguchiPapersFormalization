/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Algebra_norm_algebraMap_eq_of_isPushout_of_isFractionRing.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.TensorProduct.Finite
import AlgebraicCurves.Foundations.Algebra.Algebra_norm_one_tmul_eq_algebraMap_norm

/-!
# Algebra norm algebra Map eq of is Pushout of is Fraction Ring
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs.AlgebraNormAlgebraMapIsPushoutIs

universe u

open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace Algebra

export _root_.Algebra (IsPushout algebraMap norm_eq_of_algEquiv norm algebraMapSubmonoid
  IsPushout.equiv IsPushout.symm IsIntegral.of_finite IsAlgebraic.isAlgebraic
  IsIntegral.isAlgebraic IsPushout.comp_iff IsPushout.equiv_tmul TensorProduct.rightAlgebra
  norm_one_tmul_eq_algebraMap_norm)

namespace NormBaseChange

open _root_.Algebra


theorem isLocalization_of_finite (A B L : Type*) [CommRing A] [IsDomain A] [CommRing B] [IsDomain
  B] [Algebra A B]
    [Module.Finite A B] [Field L] [Algebra B L] [IsFractionRing B L] (h : Function.Injective
      (algebraMap A B)) :
    IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) L := by
  have : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite _ _
  have : Algebra.IsAlgebraic A B := Algebra.IsIntegral.isAlgebraic
  refine (IsLocalization.iff_of_le_of_exists_dvd (Algebra.algebraMapSubmonoid B (nonZeroDivisors A))
    (nonZeroDivisors B) ?_ ?_).mpr inferInstance
  · rintro _ ⟨r, hr, rfl⟩
    apply mem_nonZeroDivisors_of_ne_zero
    rw [map_ne_zero_iff _ h]
    exact nonZeroDivisors.ne_zero hr
  · intro n hn
    obtain ⟨r, hr, hdvd⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := A) n).exists_nonzero_dvd hn
    exact ⟨algebraMap _ _ r, ⟨r, mem_nonZeroDivisors_of_ne_zero hr, rfl⟩, hdvd⟩

theorem isPushout_of_finite (A B K L : Type*) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
  [Algebra A B]
    [Module.Finite A B] [Field K] [Algebra A K] [IsFractionRing A K] [Field L] [Algebra B L]
      [IsFractionRing B L]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L] (h :
      Function.Injective (algebraMap A B)) :
    Algebra.IsPushout A K B L :=
  ⟨(isLocalizedModule_iff_isBaseChange (nonZeroDivisors A) K _).mp
    (isLocalizedModule_iff_isLocalization.mpr (isLocalization_of_finite A B L h))⟩

end Algebra.NormBaseChange

open Algebra.NormBaseChange in
theorem _root_.Algebra.norm_algebraMap_eq_of_isPushout_of_isFractionRing
    {A B A' B' : Type u} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [IsDomain A] [IsDomain B] [IsDomain A'] [IsDomain B']
    [Algebra A B] [Algebra A A'] [Algebra B B'] [Algebra A' B'] [Algebra A B']
    [IsScalarTower A B B'] [IsScalarTower A A' B'] [Algebra.IsPushout A B A' B']
    [Module.Finite A B] (hAB : Function.Injective (algebraMap A B)) (hA'B' : Function.Injective
      (algebraMap A' B'))
    (K L K' L' : Type u) [Field K] [Field L] [Field K'] [Field L']
    [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsFractionRing B L]
    [Algebra A' K'] [IsFractionRing A' K'] [Algebra B' L'] [IsFractionRing B' L']
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L]
    [Algebra K' L'] [Algebra A' L'] [IsScalarTower A' K' L'] [IsScalarTower A' B' L']
    (φ : K →+* K') (hφ : φ.comp (algebraMap A K) = (algebraMap A' K').comp (algebraMap A A'))
    (b : B) :
    φ (Algebra.norm K (algebraMap B L b)) = Algebra.norm K' (algebraMap B' L' (algebraMap B B' b))
      := by
  classical
  let algKK' : Algebra K K' := φ.toAlgebra
  let algAK' : Algebra A K' := ((algebraMap A' K').comp (algebraMap A A')).toAlgebra
  have : IsScalarTower A A' K' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower A K K' := IsScalarTower.of_algebraMap_eq fun a => (RingHom.congr_fun hφ
    a).symm
  let algBL' : Algebra B L' := ((algebraMap B' L').comp (algebraMap B B')).toAlgebra
  have : IsScalarTower B B' L' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let algAL' : Algebra A L' := ((algebraMap A' L').comp (algebraMap A A')).toAlgebra
  have : IsScalarTower A A' L' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower A K' L' := IsScalarTower.of_algebraMap_eq fun a => by
    change algebraMap A' L' (algebraMap A A' a) = algebraMap K' L' (algebraMap A' K' (algebraMap A
      A' a))
    rw [IsScalarTower.algebraMap_apply A' K' L']
  have : IsScalarTower A B L' := IsScalarTower.of_algebraMap_eq fun a => by
    change algebraMap A' L' (algebraMap A A' a) = algebraMap B' L' (algebraMap B B' (algebraMap A
      B a))
    rw [IsScalarTower.algebraMap_apply A' B' L', ← IsScalarTower.algebraMap_apply A A' B',
      IsScalarTower.algebraMap_apply A B B']
  have : IsScalarTower A B' L' := IsScalarTower.of_algebraMap_eq fun a => by
    change algebraMap A' L' (algebraMap A A' a) = algebraMap B' L' (algebraMap A B' a)
    rw [IsScalarTower.algebraMap_apply A' B' L', ← IsScalarTower.algebraMap_apply A A' B']
  let algBT : Algebra B (K' ⊗[K] L) := ((algebraMap L (K' ⊗[K] L)).comp (algebraMap B L)).toAlgebra
  have : IsScalarTower B L (K' ⊗[K] L) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hAKT : ∀ a : A, algebraMap A (K' ⊗[K] L) a = algebraMap K (K' ⊗[K] L) (algebraMap A K a) :=
    fun a => by
    rw [IsScalarTower.algebraMap_apply A K' (K' ⊗[K] L), IsScalarTower.algebraMap_apply A K K',
      ← IsScalarTower.algebraMap_apply K K' (K' ⊗[K] L)]
  have : IsScalarTower A K (K' ⊗[K] L) := IsScalarTower.of_algebraMap_eq hAKT
  have : IsScalarTower A B (K' ⊗[K] L) := IsScalarTower.of_algebraMap_eq fun a => by
    rw [hAKT, IsScalarTower.algebraMap_apply B L (K' ⊗[K] L), ← IsScalarTower.algebraMap_apply A B
      L,
      IsScalarTower.algebraMap_apply A K L, ← IsScalarTower.algebraMap_apply K L (K' ⊗[K] L)]
  have : IsScalarTower A L (K' ⊗[K] L) := IsScalarTower.of_algebraMap_eq fun a => by
    rw [hAKT, IsScalarTower.algebraMap_apply A K L, ← IsScalarTower.algebraMap_apply K L (K' ⊗[K]
      L)]
  have : Algebra.IsPushout A A' B B' := Algebra.IsPushout.symm inferInstance
  have : Module.Finite A' B' :=
    Module.Finite.equiv (R := A') (Algebra.IsPushout.equiv A A' B B').toLinearEquiv
  have P1 : Algebra.IsPushout A K B L := isPushout_of_finite A B K L hAB
  have P2 : Algebra.IsPushout A' K' B' L' := isPushout_of_finite A' B' K' L' hA'B'
  have : IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) L :=
    isLocalization_of_finite A B L hAB
  have : Module.Finite K L := Module.Finite.of_isLocalization A B (nonZeroDivisors A)
  have : Module.Free K L := Module.Free.of_divisionRing K L
  have big1 : Algebra.IsPushout A K' B L' := (Algebra.IsPushout.comp_iff A A' B B').mpr P2
  have := P1
  have big2 : Algebra.IsPushout A K' B (K' ⊗[K] L) := (Algebra.IsPushout.comp_iff A K B L).mpr
    inferInstance
  let e₁ : TensorProduct A K' B ≃ₐ[K'] L' := @Algebra.IsPushout.equiv A K' _ _ _ B L' _ _ _ _ _ _
    _ _ big1
  let e₂ : TensorProduct A K' B ≃ₐ[K'] (K' ⊗[K] L) := @Algebra.IsPushout.equiv A K' _ _ _ B (K'
    ⊗[K] L) _ _ _ _ _ _ _ _ big2
  have h1 : e₁ ((1 : K') ⊗ₜ[A] b) = algebraMap B' L' (algebraMap B B' b) := by
    change Algebra.IsPushout.equiv A K' B L' ((1 : K') ⊗ₜ[A] b) = _
    rw [Algebra.IsPushout.equiv_tmul, map_one, one_mul]; rfl
  have h2 : e₂ ((1 : K') ⊗ₜ[A] b) = (1 : K') ⊗ₜ[K] algebraMap B L b := by
    change Algebra.IsPushout.equiv A K' B (K' ⊗[K] L) ((1 : K') ⊗ₜ[A] b) = _
    rw [Algebra.IsPushout.equiv_tmul, map_one, one_mul]; rfl
  calc φ (Algebra.norm K (algebraMap B L b))
      = algebraMap K K' (Algebra.norm K (algebraMap B L b)) := rfl
    _ = Algebra.norm K' ((1 : K') ⊗ₜ[K] algebraMap B L b) :=
      (Algebra.norm_one_tmul_eq_algebraMap_norm K' _).symm
    _ = Algebra.norm K' ((e₂.symm.trans e₁) ((1 : K') ⊗ₜ[K] algebraMap B L b)) :=
      (Algebra.norm_eq_of_algEquiv _ _).symm
    _ = Algebra.norm K' (algebraMap B' L' (algebraMap B B' b)) := by
        congr 1
        change e₁ (e₂.symm ((1 : K') ⊗ₜ[K] algebraMap B L b)) = _
        rw [← h2, AlgEquiv.symm_apply_apply, h1]
end AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs.AlgebraNormAlgebraMapIsPushoutIs
end ProofImplementation
