/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Algebra_FormallySmooth_of_maximalIdeal_eq_span_of_perfectField.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.FieldTheory.SeparablyGenerated
import Nyll.AlgebraicCurves.Foundations.CommutativeAlgebra.Algebra_FormallySmooth_of_maximalIdeal_eq_span_of_isSeparable_residueField

/-!
# Algebra Formally Smooth of maximal Ideal eq span of perfect Field
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
namespace Algebra_FormallySmooth_of_maximalIdeal_eq_span_of_perfectField

universe u v

open IsLocalRing

theorem _root_.Algebra.FormallySmooth.of_maximalIdeal_eq_span_of_perfectField
    (K : Type u) [Field K] [PerfectField K] (𝒪 : Type v) [CommRing 𝒪] [IsLocalRing 𝒪] [IsDomain 𝒪]
      [IsNoetherianRing 𝒪]
    [Algebra K 𝒪] [Algebra.EssFiniteType K 𝒪]
    (u : 𝒪) (hu0 : u ≠ 0) (hu : maximalIdeal 𝒪 = Ideal.span {u}) :
    Algebra.FormallySmooth K 𝒪 := by
  classical
  let _ : Algebra.EssFiniteType K (ResidueField 𝒪) :=
    Algebra.EssFiniteType.comp K 𝒪 (ResidueField 𝒪)
  obtain ⟨s, hs, hsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField K
    (ResidueField 𝒪)
  have hinj : Function.Injective (MvPolynomial.aeval (R := K) ((↑) : s → ResidueField 𝒪)) :=
    algebraicIndependent_iff_injective_aeval.1 hs.1
  choose t ht using fun x : s => IsLocalRing.residue_surjective (R := 𝒪) (x : ResidueField 𝒪)
  let P := MvPolynomial s K
  let φ : P →ₐ[K] 𝒪 := MvPolynomial.aeval t
  have hφres : ∀ f : P, IsLocalRing.residue 𝒪 (φ f) = MvPolynomial.aeval ((↑) : s → ResidueField 𝒪)
    f := by
    intro f
    have hcomp : ((IsScalarTower.toAlgHom K 𝒪 (ResidueField 𝒪)).comp φ) =
        MvPolynomial.aeval ((↑) : s → ResidueField 𝒪) := by
      refine MvPolynomial.algHom_ext fun i => ?_
      simp [φ, ht i]
    exact congrArg (fun g : P →ₐ[K] ResidueField 𝒪 => g f) hcomp
  have hunit : ∀ f : P, f ≠ 0 → IsUnit (φ f) := by
    intro f hf
    by_contra h
    have hmem : φ f ∈ maximalIdeal 𝒪 := h
    have h0 : IsLocalRing.residue 𝒪 (φ f) = 0 := (IsLocalRing.residue_eq_zero_iff _).mpr hmem
    rw [hφres] at h0
    exact hf (hinj (by rw [h0, map_zero]))
  let K₀ := FractionRing P
  let ψ : K₀ →ₐ[K] 𝒪 := IsLocalization.liftAlgHom (M := nonZeroDivisors P) (f := φ)
    (fun y => hunit y.1 (nonZeroDivisors.ne_zero y.2))
  let _ : Algebra K₀ 𝒪 := ψ.toRingHom.toAlgebra
  have hψ : ∀ z : K₀, algebraMap K₀ 𝒪 z = ψ z := fun _ => rfl
  let _ : IsScalarTower K K₀ 𝒪 := IsScalarTower.of_algebraMap_eq fun x => by
    rw [hψ, ψ.commutes]
  let _ : Algebra P 𝒪 := φ.toRingHom.toAlgebra
  have hφ : ∀ f : P, algebraMap P 𝒪 f = φ f := fun _ => rfl
  let _ : IsScalarTower P K₀ 𝒪 := IsScalarTower.of_algebraMap_eq fun f => by
    rw [hψ, hφ]
    change φ f = IsLocalization.lift (M := nonZeroDivisors P) _ (algebraMap P K₀ f)
    rw [IsLocalization.lift_eq]
    rfl
  let _ : Algebra.FormallySmooth P K₀ := Algebra.FormallySmooth.of_isLocalization (Rₘ := K₀)
    (nonZeroDivisors P)
  let _ : Algebra.FormallySmooth K K₀ := Algebra.FormallySmooth.comp K P K₀
  let _ : Algebra.EssFiniteType K₀ 𝒪 := Algebra.EssFiniteType.of_comp K K₀ 𝒪
  let F : IntermediateField K (ResidueField 𝒪) := IntermediateField.adjoin K (Set.range ((↑) : s →
    ResidueField 𝒪))
  let e : K₀ ≃ₐ[K] F := hs.1.aevalEquivField
  have hrange : (Set.range ((↑) : s → ResidueField 𝒪)) = (s : Set (ResidueField 𝒪)) := by
    ext x; simp
  let _ : Algebra.IsSeparable F (ResidueField 𝒪) := by
    have : F = IntermediateField.adjoin K (s : Set (ResidueField 𝒪)) := by rw [← hrange]
    rw [this]; exact hsep
  have hcompat : (algebraMap K₀ (ResidueField 𝒪)).comp (e.symm.toRingEquiv : F →+* K₀) =
      (RingEquiv.refl (ResidueField 𝒪) : ResidueField 𝒪 →+* ResidueField 𝒪).comp (algebraMap F
        (ResidueField 𝒪)) := by
    have key : (algebraMap K₀ (ResidueField 𝒪)) = (algebraMap F (ResidueField 𝒪)).comp
      (e.toRingEquiv : K₀ →+* F) := by
      refine IsLocalization.ringHom_ext (nonZeroDivisors P) ?_
      ext f
      · simp only [RingHom.coe_comp, Function.comp_apply]
        rw [IsScalarTower.algebraMap_apply K₀ 𝒪 (ResidueField 𝒪), ← IsScalarTower.algebraMap_apply
          P K₀ 𝒪]
        change IsLocalRing.residue 𝒪 (φ (MvPolynomial.C f)) = _
        rw [hφres]
        change MvPolynomial.aeval _ (MvPolynomial.C f) =
          ((e (algebraMap P K₀ (MvPolynomial.C f)) : F) : ResidueField 𝒪)
        rw [AlgebraicIndependent.aevalEquivField_algebraMap_apply_coe]
      · simp only [RingHom.coe_comp, Function.comp_apply]
        rw [IsScalarTower.algebraMap_apply K₀ 𝒪 (ResidueField 𝒪), ← IsScalarTower.algebraMap_apply
          P K₀ 𝒪]
        change IsLocalRing.residue 𝒪 (φ (MvPolynomial.X _)) = _
        rw [hφres]
        change MvPolynomial.aeval _ (MvPolynomial.X _) =
          ((e (algebraMap P K₀ (MvPolynomial.X _)) : F) : ResidueField 𝒪)
        rw [AlgebraicIndependent.aevalEquivField_algebraMap_apply_coe]
    rw [key]
    ext x
    simp
  let _ : Algebra.IsSeparable K₀ (ResidueField 𝒪) :=
    Algebra.IsSeparable.of_equiv_equiv (e.symm.toRingEquiv : F ≃+* K₀) (RingEquiv.refl
      (ResidueField 𝒪)) hcompat
  let _ : Algebra.IsAlgebraic K₀ (ResidueField 𝒪) := Algebra.IsSeparable.isAlgebraic _ _
  let _ := Algebra.FormallySmooth.of_maximalIdeal_eq_span_of_isSeparable_residueField K₀ 𝒪 u hu0 hu
  exact Algebra.FormallySmooth.comp K K₀ 𝒪
end Algebra_FormallySmooth_of_maximalIdeal_eq_span_of_perfectField
end AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
end ProofImplementation
