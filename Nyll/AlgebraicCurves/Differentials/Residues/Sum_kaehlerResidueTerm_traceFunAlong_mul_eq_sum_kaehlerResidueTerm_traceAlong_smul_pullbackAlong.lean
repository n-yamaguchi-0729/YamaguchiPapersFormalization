/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_sum_kaehlerResidueTerm_traceFunAlong_mul_eq_sum_kaehlerResidueTerm_traceAlong_smul_pullbackAlong.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.Correspondences
import Nyll.AlgebraicCurves.Differentials.Residues.Basic
import Nyll.AlgebraicCurves.Differentials.Maps
import Nyll.AlgebraicCurves.Cohomology.Cech.Maps
import Nyll.AlgebraicCurves.Differentials.Residues.FibreIdentity

/-!
# Sum kaehler Residue Term trace Fun Along mul eq sum kaehler Residue Term trace Along smul
pullback Along
-/

section ProofImplementation

namespace AlgebraicCurves.Differentials.Residues.Proofs.ResidueTraceProjection

open _root_.KaehlerDifferential
open _root_.AlgebraicCurve

namespace AlgebraicCurve
open _root_.AlgebraicCurve
namespace Theta3Sol
open _root_.AlgebraicCurve

open _root_.KaehlerDifferential
open _root_.AlgebraicCurve

variable {K F R : Type*} [Field K] [Field F] [Field R] [Algebra K F] [Algebra K R]
  [HasPrincipalDivisors K R]

theorem pairwiseDisjoint_fiberAlong (φ : F →ₐ[K] R) (hφ : φ.toRingHom.IsIntegral) (S : Finset
  (Place K F)) :
    (S : Set (Place K F)).PairwiseDisjoint (Place.fiberAlong φ hφ) := by
  intro x _ x' _ hne
  refine Finset.disjoint_left.mpr fun w hw hw' => hne ?_
  rw [Place.mem_fiberAlong] at hw hw'
  exact hw.symm.trans hw'

theorem mem_biUnion_fiberAlong [DecidableEq (Place K R)] (φ : F →ₐ[K] R) (hφ :
  φ.toRingHom.IsIntegral) (S : Finset (Place K F)) (w : Place K R) :
    w ∈ S.biUnion (Place.fiberAlong φ hφ) ↔ Place.restrictAlong φ hφ w ∈ S := by
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨x, hx, hw⟩
    rw [Place.mem_fiberAlong] at hw
    rwa [hw]
  · intro h
    exact ⟨_, h, Place.mem_fiberAlong.mpr rfl⟩

end AlgebraicCurve.Theta3Sol

open KaehlerDifferential _root_.AlgebraicCurve
  _root_.AlgebraicCurves.Differentials.Residues.Proofs.ResidueTraceProjection.AlgebraicCurve
end AlgebraicCurves.Differentials.Residues.Proofs.ResidueTraceProjection

namespace AlgebraicCurve

open _root_.AlgebraicCurves.Differentials.Residues.Proofs.ResidueTraceProjection
open _root_.KaehlerDifferential
open _root_.AlgebraicCurve
  AlgebraicCurve.Theta3Sol in
theorem
 sum_kaehlerResidueTerm_traceFunAlong_mul_eq_sum_kaehlerResidueTerm_traceAlong_smul_pullbackAlong
    {K F R : Type*} [Field K] [Field F] [Field R] [Algebra K F] [Algebra K R]
    [HasPrincipalDivisors K R] [HasCanonicalLocalResidueKStar K F] [HasCanonicalLocalResidueKStar K
      R]
    [∀ v : Place K F, v.DCoordGenerates] [∀ w : Place K R, w.DCoordGenerates] [Nontrivial Ω[F⁄K]]
      [Nontrivial Ω[R⁄K]]
    (α β : F →ₐ[K] R) (hα : α.toRingHom.IsIntegral) (hβ : β.toRingHom.IsIntegral)
    (hFα : FibreResidueIdentityAlong α hα) (hFβ : FibreResidueIdentityAlong β hβ) (hsep :
      SeparableAlong K β)
    (hΩ : ∀ η : Ω[R⁄K], ∃ (ω₁ : Ω[F⁄K]) (c : R), η = c • Differential.pullbackAlong β ω₁)
    (S : Finset (Place K F))
    (hS : ∀ w : Place K R, Place.restrictAlong α hα w ∈ S ↔ Place.restrictAlong β hβ w ∈ S)
    (g : F) (u : R) (ω : Ω[F⁄K]) :
    ∑ x ∈ S, kaehlerResidueTerm ω (diagonalHom K F (traceFunAlong α (β g * u))) x
      = ∑ z ∈ S, kaehlerResidueTerm (Differential.traceAlong β (u • Differential.pullbackAlong α
        ω)) (diagonalHom K F g) z := by
  classical
  have step1 : ∀ x ∈ S, kaehlerResidueTerm ω (diagonalHom K F (traceFunAlong α (β g * u))) x
      = ∑ w ∈ Place.fiberAlong α hα x, kaehlerResidueTerm (Differential.pullbackAlong α ω)
        (diagonalHom K R (β g * u)) w :=
    fun x _ => (hFα x ω (β g * u)).symm
  rw [Finset.sum_congr rfl step1, ← Finset.sum_biUnion (pairwiseDisjoint_fiberAlong α hα S)]
  have hunion : S.biUnion (Place.fiberAlong α hα) = S.biUnion (Place.fiberAlong β hβ) := by
    ext w
    rw [mem_biUnion_fiberAlong (K := K) α hα S w, mem_biUnion_fiberAlong (K := K) β hβ S w, hS]
  rw [hunion, Finset.sum_biUnion (pairwiseDisjoint_fiberAlong β hβ S)]
  refine Finset.sum_congr rfl fun z _ => ?_
  obtain ⟨ω₁, c, hc⟩ := hΩ (u • Differential.pullbackAlong α ω)
  have hterm : ∀ w : Place K R, kaehlerResidueTerm (Differential.pullbackAlong α ω) (diagonalHom K
    R (β g * u)) w
      = kaehlerResidueTerm (Differential.pullbackAlong β ω₁) (diagonalHom K R (β g * c)) w := by
    intro w
    unfold kaehlerResidueTerm
    have key : u * w.differentialCoeff (Differential.pullbackAlong α ω) = c * w.differentialCoeff
      (Differential.pullbackAlong β ω₁) := by
      rw [← w.differentialCoeff_smul, ← w.differentialCoeff_smul, hc]
    rw [diagonalHom_apply, diagonalHom_apply, mul_assoc, key, ← mul_assoc]
  rw [Finset.sum_congr rfl fun w _ => hterm w, hFβ z ω₁ (β g * c)]
  have htr : traceFunAlong β (β g * c) = g * traceFunAlong β c := by
    let := algebraAlong β
    rw [traceFunAlong_apply, traceFunAlong_apply]
    change Algebra.trace F R (algebraMap F R g * c) = g * Algebra.trace F R c
    rw [← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]
  have hTr : Differential.traceAlong β (u • Differential.pullbackAlong α ω) = traceFunAlong β c •
    ω₁ := by
    rw [hc, Differential.traceAlong_smul_pullbackAlong β hsep c ω₁, traceFunAlong_apply]
  unfold kaehlerResidueTerm
  rw [diagonalHom_apply, diagonalHom_apply, htr, hTr, z.differentialCoeff_smul, mul_assoc]

end AlgebraicCurve
end ProofImplementation
