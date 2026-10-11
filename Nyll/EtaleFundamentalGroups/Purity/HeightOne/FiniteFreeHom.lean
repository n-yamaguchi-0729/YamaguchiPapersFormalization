/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.LinearAlgebra.Matrix.ToLin
import Nyll.EtaleFundamentalGroups.Purity.HeightOne.UFDIntersection
import Mathlib.Data.Fintype.EquivFin

/-!
# Descent of finite-free morphisms from height-one localizations

Over a unique factorization domain, a matrix over the fraction field whose
entries belong to every prime-element localization has a unique matrix over
the original ring.  Via the standard bases, this gives existence and
uniqueness of a descended morphism between finite free modules.

This is a coordinate codimension-one full-faithfulness input.  It does not
assert extension of finite étale covers across a punctured spectrum.
-/

noncomputable section

namespace EtaleFundamentalGroups

open nonZeroDivisors

universe u v

/-- A finite matrix over the fraction field descends uniquely when every
entry belongs to each prime-element localization. -/
theorem existsUnique_matrix_over_base_of_mem_localization_primeElement
    {A : Type u} {K : Type v}
    [CommRing A] [IsDomain A] [UniqueFactorizationMonoid A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    {m n : Type*} (M : Matrix m n K)
    (hM : ∀ i j (p : A) (hp : Prime p),
      letI : (Ideal.span {p}).IsPrime :=
        Ideal.isPrime_span_singleton_of_prime hp
      M i j ∈ Localization.subalgebra.ofField K
        (Ideal.span {p}).primeCompl
        (Ideal.primeCompl_le_nonZeroDivisors (Ideal.span {p}))) :
    ∃! M₀ : Matrix m n A,
      ∀ i j, algebraMap A K (M₀ i j) = M i j := by
  classical
  have hentry (i : m) (j : n) : M i j ∈ (⊥ : Subalgebra A K) :=
    mem_bot_of_mem_localization_primeElement (M i j) (hM i j)
  let M₀ : Matrix m n A := fun i j ↦
    Classical.choose (Algebra.mem_bot.mp (hentry i j))
  have hM₀ (i : m) (j : n) : algebraMap A K (M₀ i j) = M i j :=
    Classical.choose_spec (Algebra.mem_bot.mp (hentry i j))
  refine ⟨M₀, hM₀, ?_⟩
  intro N hN
  ext i j
  exact IsFractionRing.injective A K <| (hN i j).trans (hM₀ i j).symm

/-- A linear map between finite coordinate modules over the fraction field
descends uniquely when every entry of its standard matrix belongs to each
prime-element localization. -/
theorem existsUnique_linearMap_pi_over_base_of_mem_localization_primeElement
    {A : Type u} {K : Type v}
    [CommRing A] [IsDomain A] [UniqueFactorizationMonoid A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    {m n : Type*} [Finite m] [Fintype n] [DecidableEq n]
    (f : (n → K) →ₗ[K] (m → K))
    (hf : ∀ i j (p : A) (hp : Prime p),
      letI : (Ideal.span {p}).IsPrime :=
        Ideal.isPrime_span_singleton_of_prime hp
      LinearMap.toMatrix' f i j ∈ Localization.subalgebra.ofField K
        (Ideal.span {p}).primeCompl
        (Ideal.primeCompl_le_nonZeroDivisors (Ideal.span {p}))) :
    ∃! g : (n → A) →ₗ[A] (m → A),
      ∀ i j,
        algebraMap A K (LinearMap.toMatrix' g i j) =
          LinearMap.toMatrix' f i j := by
  let := Fintype.ofFinite m
  obtain ⟨M, hM, hM_unique⟩ :=
    existsUnique_matrix_over_base_of_mem_localization_primeElement
      (LinearMap.toMatrix' f) hf
  let g : (n → A) →ₗ[A] (m → A) := Matrix.toLin' M
  refine ⟨g, ?_, ?_⟩
  · simpa only [g, LinearMap.toMatrix'_toLin'] using hM
  · intro g' hg'
    apply LinearMap.toMatrix'.injective
    rw [show LinearMap.toMatrix' g = M by
      exact LinearMap.toMatrix'_toLin' M]
    exact hM_unique (LinearMap.toMatrix' g') hg'

end EtaleFundamentalGroups

end
