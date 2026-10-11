/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SchemeTheory.Normalization.GenericFiber.SmoothIntegralClosure
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Topology.Connected.Clopen

/-!
# Connected generic fibres of smooth algebras over normal domains

For a smooth algebra over a normal domain, every idempotent in the generic
fibre is the image of a unique idempotent of the original algebra. Indeed,
idempotents are integral and smooth base change commutes with integral closure.
Flatness makes the map to the generic fibre injective.

Consequently, a connected affine smooth scheme has connected generic fibre.
This applies to a connected finite-etale cover of an affine smooth arithmetic
scheme, since its composite structure morphism is smooth. The result concerns
the ordinary generic fibre; geometric connectedness requires the additional
arithmetic argument about the field of constants.
-/

noncomputable section

namespace EtaleFundamentalGroups

open scoped TensorProduct
open Polynomial

universe uR uS uK

variable {R : Type uR} {S : Type uS} {K : Type uK}
variable [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
variable [CommRing S] [Algebra R S] [Algebra.Smooth R S]
variable [Field K] [Algebra R K] [IsFractionRing R K]

/-- Every idempotent of the generic fibre of a smooth algebra over a normal
domain descends uniquely to an idempotent of the original algebra. -/
theorem existsUnique_isIdempotentElem_genericFiber_of_smooth
    (e : S ⊗[R] K) (he : IsIdempotentElem e) :
    ∃! s : S, IsIdempotentElem s ∧
      (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] K) s = e := by
  have heIntegral : IsIntegral S e := by
    refine ⟨X * (X - C 1), monic_X.mul (monic_X_sub_C 1), ?_⟩
    change aeval e (X * (X - C 1)) = 0
    rw [map_mul, aeval_X, map_sub, aeval_X, aeval_C, map_one]
    rw [mul_sub, mul_one, he.eq, sub_self]
  obtain ⟨s, hs⟩ :=
    exists_eq_includeLeft_of_isIntegral_genericFiber_of_smooth e heIntegral
  have hinjective : Function.Injective
      (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] K) :=
    Algebra.TensorProduct.includeLeft_injective
      (FaithfulSMul.algebraMap_injective R K)
  refine ⟨s, ⟨?_, hs⟩, ?_⟩
  · apply hinjective
    simpa only [map_mul, hs] using he.eq
  · intro t ht
    exact hinjective (ht.2.trans hs.symm)

/-- A connected smooth affine scheme over a normal domain has connected
ordinary generic fibre. No properness or finiteness as a module is required. -/
theorem connectedSpace_primeSpectrum_genericFiber_of_smooth
    [ConnectedSpace (PrimeSpectrum S)] :
    ConnectedSpace (PrimeSpectrum (S ⊗[R] K)) := by
  have hinjective : Function.Injective
      (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] K) :=
    Algebra.TensorProduct.includeLeft_injective
      (FaithfulSMul.algebraMap_injective R K)
  let : Nontrivial S :=
    PrimeSpectrum.nonempty_iff_nontrivial.mp inferInstance
  let : Nontrivial (S ⊗[R] K) := Function.Injective.nontrivial hinjective
  apply connectedSpace_iff_clopen.mpr
  refine ⟨inferInstance, ?_⟩
  intro V hV
  obtain ⟨e, he, rfl⟩ := PrimeSpectrum.isClopen_iff.mp hV
  obtain ⟨s, ⟨hs, hse⟩, _⟩ :=
    existsUnique_isIdempotentElem_genericFiber_of_smooth e he
  have hsClopen : IsClopen
      (PrimeSpectrum.basicOpen s : Set (PrimeSpectrum S)) :=
    PrimeSpectrum.isClopen_iff.mpr ⟨s, hs, rfl⟩
  rcases isClopen_iff.mp hsClopen with hsEmpty | hsUniv
  · have hsZero : s = 0 := by
      apply PrimeSpectrum.basicOpen_injOn_isIdempotentElem hs
        (show IsIdempotentElem (0 : S) from zero_mul 0)
      apply SetLike.ext'
      simpa only [PrimeSpectrum.basicOpen_zero,
        TopologicalSpace.Opens.coe_bot] using hsEmpty
    have heZero : e = 0 := by
      rw [hsZero, map_zero] at hse
      exact hse.symm
    left
    rw [heZero, PrimeSpectrum.basicOpen_zero, TopologicalSpace.Opens.coe_bot]
  · have hsOne : s = 1 := by
      apply PrimeSpectrum.basicOpen_injOn_isIdempotentElem hs
        (show IsIdempotentElem (1 : S) from one_mul 1)
      apply SetLike.ext'
      simpa only [PrimeSpectrum.basicOpen_one,
        TopologicalSpace.Opens.coe_top] using hsUniv
    have heOne : e = 1 := by
      rw [hsOne, map_one] at hse
      exact hse.symm
    right
    rw [heOne, PrimeSpectrum.basicOpen_one, TopologicalSpace.Opens.coe_top]

end EtaleFundamentalGroups
