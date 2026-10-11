/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Algebra_exists_finitePresentation_tensorProduct_algEquiv_of_isDirectLimit.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.Extension.Presentation.Core
import Mathlib.Data.Finset.Order
import Nyll.AlgebraicCurves.Foundations.Algebra.Mathlib_Algebra_IsDirectLimit

/-!
# Algebra exists finite Presentation tensor Product alg Equiv of is Direct Limit
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.Algebra.Proofs
namespace Algebra_exists_finitePresentation_tensorProduct_algEquiv_of_isDirectLimit

open scoped TensorProduct

universe u v w w'

namespace AlgSpreadDirected

theorem range_mono {ι : Type u} [Preorder ι]
    {G : ι → Type v} [∀ i, CommRing (G i)] (f : ∀ i j : ι, i ≤ j → G i →+* G j)
    [DirectedSystem G fun i j h => ⇑(f i j h)]
    {R : Type w} [CommRing R] [∀ i, Algebra (G i) R]
    (hR : IsDirectLimit (fun i j h => ⇑(f i j h)) fun i => ⇑(algebraMap (G i) R))
    {i j : ι} (hij : i ≤ j) :
    Set.range (algebraMap (G i) R) ⊆ Set.range (algebraMap (G j) R) := by
  rintro _ ⟨x, rfl⟩
  exact ⟨f i j hij x, hR.compatibility i j hij x⟩

theorem exists_subset_range_of_finite {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    {G : ι → Type v} [∀ i, CommRing (G i)] (f : ∀ i j : ι, i ≤ j → G i →+* G j)
    [DirectedSystem G fun i j h => ⇑(f i j h)]
    {R : Type w} [CommRing R] [∀ i, Algebra (G i) R]
    (hR : IsDirectLimit (fun i j h => ⇑(f i j h)) fun i => ⇑(algebraMap (G i) R))
    {s : Set R} (hs : s.Finite) :
    ∃ i : ι, s ⊆ Set.range (algebraMap (G i) R) := by
  classical
  let idx : R → ι := fun r => (hR.surj r).choose
  have hidx : ∀ r : R, r ∈ Set.range (algebraMap (G (idx r)) R) := fun r =>
    let ⟨x, hx⟩ := (hR.surj r).choose_spec
    ⟨x, hx⟩
  obtain ⟨M, hM⟩ := Finset.exists_le (hs.toFinset.image idx)
  refine ⟨M, fun r hr => ?_⟩
  have hle : idx r ≤ M := hM _ (Finset.mem_image_of_mem idx (hs.mem_toFinset.mpr hr))
  exact range_mono f hR hle (hidx r)

end AlgSpreadDirected

open AlgSpreadDirected in
theorem _root_.Algebra.exists_finitePresentation_tensorProduct_algEquiv_of_isDirectLimit
    {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    (G : ι → Type v) [∀ i, CommRing (G i)] (f : ∀ i j : ι, i ≤ j → G i →+* G j)
    [DirectedSystem G fun i j h => ⇑(f i j h)]
    (R : Type w) [CommRing R] [∀ i, Algebra (G i) R]
    (hR : IsDirectLimit (fun i j h => ⇑(f i j h)) fun i => ⇑(algebraMap (G i) R))
    (A : Type w') [CommRing A] [Algebra R A] [Algebra.FinitePresentation R A] :
    ∃ (i : ι) (A₀ : Type v) (_ : CommRing A₀) (_ : Algebra (G i) A₀)
      (_ : Algebra.FinitePresentation (G i) A₀), Nonempty ((R ⊗[G i] A₀) ≃ₐ[R] A) := by
  classical
  let P := Algebra.Presentation.ofFinitePresentation R A
  obtain ⟨i, hi⟩ := exists_subset_range_of_finite f hR (s := P.coeffs)
    Algebra.Presentation.finite_coeffs
  let : Algebra (G i) A := ((algebraMap R A).comp (algebraMap (G i) R)).toAlgebra
  have : IsScalarTower (G i) R A := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : P.HasCoeffs (G i) := ⟨hi⟩
  exact ⟨i, P.ModelOfHasCoeffs (G i), inferInstance, inferInstance, inferInstance,
    ⟨P.tensorModelOfHasCoeffsEquiv (G i)⟩⟩
end Algebra_exists_finitePresentation_tensorProduct_algEquiv_of_isDirectLimit
end AlgebraicCurves.Foundations.Algebra.Proofs
end ProofImplementation
