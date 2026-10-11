/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_serrePairing_pullbackAlong_eq_serrePairing_traceAlong.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Divisors.ClassGroup
import AlgebraicCurves.Cohomology.Adelic.Repartitions
import AlgebraicCurves.Cohomology.Adelic.Index
import AlgebraicCurves.FunctionFields.CurveOver
import AlgebraicCurves.Differentials.Order
import AlgebraicCurves.Divisors.Canonical
import AlgebraicCurves.Differentials.Residues.Basic
import AlgebraicCurves.Differentials.Kaehler.Weil
import AlgebraicCurves.Differentials.Regular
import AlgebraicCurves.Cohomology.Cech.DivisorSections
import AlgebraicCurves.Cohomology.SerrePairing
import AlgebraicCurves.Divisors.Correspondences
import AlgebraicCurves.Differentials.Maps
import AlgebraicCurves.Cohomology.Cech.Maps
import AlgebraicCurves.Differentials.Residues.FibreIdentity

/-!
# Serre Pairing pullback Along eq serre Pairing trace Along
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Proofs.SerrePairingPullbackAlongSerre

open KaehlerDifferential

namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

theorem finsum_eq_finsum_sum_fiberAlong [HasPrincipalDivisors K F'] (φ : F →ₐ[K] F')
    (hφ : φ.toRingHom.IsIntegral) {M : Type*} [AddCommMonoid M] (g : Place K F' → M)
    (hg : (Function.support g).Finite) :
    ∑ᶠ w, g w = ∑ᶠ v, ∑ w ∈ Place.fiberAlong φ hφ v, g w := by
  classical
  set T := hg.toFinset with hTdef
  have hT : ∀ w, g w ≠ 0 → w ∈ T := fun w hw => hg.mem_toFinset.mpr hw
  have hsub : Function.support g ⊆ (T : Set (Place K F')) := fun w hw => by
    rw [Finset.mem_coe]
    exact hT w hw
  rw [finsum_eq_sum_of_support_subset g hsub]
  have hsupp : (Function.support fun v => ∑ w ∈ Place.fiberAlong φ hφ v, g w)
      ⊆ ((T.image (Place.restrictAlong φ hφ) : Finset (Place K F)) : Set (Place K F)) := by
    intro v hv
    rw [Function.mem_support] at hv
    obtain ⟨w, hw, hgw⟩ := Finset.exists_ne_zero_of_sum_ne_zero hv
    rw [Finset.coe_image]
    exact ⟨w, by rw [Finset.mem_coe]; exact hT w hgw, Place.mem_fiberAlong.mp hw⟩
  rw [finsum_eq_sum_of_support_subset _ hsupp,
    ← Finset.sum_fiberwise_of_maps_to (s := T) (t := T.image (Place.restrictAlong φ hφ))
      (g := Place.restrictAlong φ hφ) (fun w hw => Finset.mem_image_of_mem _ hw) g]
  refine Finset.sum_congr rfl fun v _ => ?_
  apply Finset.sum_subset
  · intro w hw
    rw [Finset.mem_filter] at hw
    exact Place.mem_fiberAlong.mpr hw.2
  · intro w hwfib hwT
    by_contra hgw
    exact hwT (Finset.mem_filter.mpr ⟨hT w hgw, Place.mem_fiberAlong.mp hwfib⟩)

section Adjunction

variable [HasCanonicalLocalResidueKStar K F] [HasCanonicalLocalResidueKStar K F']
  [∀ v : Place K F, v.DCoordGenerates] [∀ w : Place K F', w.DCoordGenerates]
  [Nontrivial Ω[F⁄K]] [Nontrivial Ω[F'⁄K]]
  [HasCanonicalDivisor (K := K) (F := F)] [HasCanonicalDivisor (K := K) (F := F')]
  [HasPrincipalDivisors K F] [HasPrincipalDivisors K F']

open Classical in
theorem support_ite_kaehlerResidueTerm_finite (S : Set (Place K F')) (η : Ω[F'⁄K]) (f' : F') :
    (Function.support fun w => if w ∈ S then (0 : K) else kaehlerResidueTerm η (diagonalHom K F'
      f') w).Finite := by
  have hfin : (Function.support (kaehlerResidueTerm η (diagonalHom K F' f'))).Finite := by
    rcases eq_or_ne η 0 with rfl | hη
    · exact Set.Finite.subset Set.finite_empty fun w hw => hw (kaehlerResidueTerm_zero_left _ w)
    · exact kaehlerResidueTerm_support_finite_of_adeleSpace hη (diagonal_mem_adeleSpace f')
  refine hfin.subset fun w hw => ?_
  rw [Function.mem_support] at hw ⊢
  intro h
  apply hw
  rw [h, ite_self]

theorem serrePairing_pullbackAlong_eq_serrePairing_traceAlong'
    (hRT : ResidueTheorem K F) (hRT' : ResidueTheorem K F')
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (htr : TraceIntegralAlong φ hφ)
    (hfib : FibreResidueIdentityAlong φ hφ)
    {S₀ S₁ : Set (Place K F)} (hcover : S₀ ∪ S₁ = Set.univ)
    (ω : ↥(regularDifferentials K F))
    (hω' : Differential.pullbackAlong φ (ω : Ω[F⁄K]) ∈ regularDifferentials K F')
    (x' : cechH1 ((Place.restrictAlong φ hφ) ⁻¹' S₀) ((Place.restrictAlong φ hφ) ⁻¹' S₁) (0 :
      Divisor K F')) :
    serrePairing hRT' (preimage_restrictAlong_union_eq_univ φ hφ hcover)
        ⟨Differential.pullbackAlong φ (ω : Ω[F⁄K]), hω'⟩ x'
      = serrePairing hRT hcover ω (cechH1.traceAlong φ hφ htr S₀ S₁ x') := by
  classical
  obtain ⟨f', rfl⟩ := Submodule.Quotient.mk_surjective _ x'
  rw [cechH1.traceAlong_mk, serrePairing_apply_mk_eq_finsum_ite,
    serrePairing_apply_mk_eq_finsum_ite,
    lSpaceOnZero.coe_traceAlong_apply]
  rw [finsum_eq_finsum_sum_fiberAlong φ hφ _ (support_ite_kaehlerResidueTerm_finite _ _ _)]
  refine finsum_congr fun v => ?_
  by_cases hv : v ∈ S₀
  · rw [ite_eq_left hv]
    refine Finset.sum_eq_zero fun w hw => ?_
    rw [ite_eq_left]
    rw [Set.mem_preimage, Place.mem_fiberAlong.mp hw]
    exact hv
  · rw [ite_eq_right hv, ← hfib v (ω : Ω[F⁄K]) (f' : F')]
    refine Finset.sum_congr rfl fun w hw => ?_
    rw [ite_eq_right]
    rw [Set.mem_preimage, Place.mem_fiberAlong.mp hw]
    exact hv

end Adjunction

end AlgebraicCurve

open _root_.AlgebraicCurve
  _root_.AlgebraicCurves.Cohomology.Proofs.SerrePairingPullbackAlongSerre.AlgebraicCurve in
theorem _root_.AlgebraicCurve.serrePairing_pullbackAlong_eq_serrePairing_traceAlong
    {K : Type*} {F : Type*} {F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [HasCanonicalLocalResidueKStar K F] [HasCanonicalLocalResidueKStar K F']
    [∀ v : Place K F, v.DCoordGenerates] [∀ w : Place K F', w.DCoordGenerates]
    [Nontrivial Ω[F⁄K]] [Nontrivial Ω[F'⁄K]]
    [HasCanonicalDivisor (K := K) (F := F)] [HasCanonicalDivisor (K := K) (F := F')]
    [HasPrincipalDivisors K F] [HasPrincipalDivisors K F']
    (hRT : ResidueTheorem K F) (hRT' : ResidueTheorem K F')
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (htr : TraceIntegralAlong φ hφ)
    (hfib : FibreResidueIdentityAlong φ hφ)
    {S₀ S₁ : Set (Place K F)} (hcover : S₀ ∪ S₁ = Set.univ)
    (ω : ↥(regularDifferentials K F))
    (hω' : Differential.pullbackAlong φ (ω : Ω[F⁄K]) ∈ regularDifferentials K F')
    (x' : cechH1 ((Place.restrictAlong φ hφ) ⁻¹' S₀) ((Place.restrictAlong φ hφ) ⁻¹' S₁) (0 :
      Divisor K F')) :
    serrePairing hRT' (preimage_restrictAlong_union_eq_univ φ hφ hcover)
        ⟨Differential.pullbackAlong φ (ω : Ω[F⁄K]), hω'⟩ x'
      = serrePairing hRT hcover ω (cechH1.traceAlong φ hφ htr S₀ S₁ x') :=
  serrePairing_pullbackAlong_eq_serrePairing_traceAlong' hRT hRT' φ hφ htr hfib hcover ω hω' x'
end AlgebraicCurves.Cohomology.Proofs.SerrePairingPullbackAlongSerre
end ProofImplementation
