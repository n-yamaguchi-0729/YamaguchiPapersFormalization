/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_ProjSpaceCech_GradedModule_subsingleton_cohomology_shift_of_isFG.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.SchemeTheory.Cohomology.Cech.ProjSpaceCechTwist
import Nyll.SchemeTheory.Cohomology.Cech.ProjSpaceCechGradedModule
import Nyll.AlgebraicCurves.Cohomology.Cech.ProjSpaceCech_Twist_subsingleton_cohomology_of_neg_le
import Nyll.AlgebraicCurves.Cohomology.Cech.ProjSpaceCech_GradedModule_HMap_bijective_of_cochainMap_bijective
import Nyll.SchemeTheory.Cohomology.Cech.ProjSpaceCech_GradedModule_nonempty_HEquiv_FD
import Nyll.SchemeTheory.Cohomology.Cech.ProjSpaceCech_GradedModule_nonempty_HEquiv_pi
import Nyll.AlgebraicCurves.Cohomology.Cech.ProjSpaceCech_GradedModule_Presentation_subsingleton_H_of_ses
import Nyll.SchemeTheory.Cohomology.Cech.ProjSpaceCech_GradedModule_Presentation_ker_isFG

/-!
# Proj Space Cech Graded Module subsingleton cohomology shift of is FG
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Cech.Proofs
namespace ProjSpaceCech_GradedModule_subsingleton_cohomology_shift_of_isFG

universe u

noncomputable section

open Finset Function MvPolynomial

namespace ProjSpaceCech
open _root_.ProjSpaceCech
open _root_.ProjSpaceCech

section SerreVanishing

variable {R : Type u} [CommRing R] {n : ℕ}

namespace GradedModule
open _root_.ProjSpaceCech.GradedModule
end GradedModule
open scoped _root_.ProjSpaceCech.GradedModule in
theorem GradedModule.subsingleton_H_pi_FD {ι : Type} [Fintype ι] (e : ι → ℤ) {i : ℕ} (hi : 1 ≤ i)
    (he : ∀ k, -(n : ℤ) ≤ e k) :
    Subsingleton (GradedModule.H (GradedModule.pi (fun k => GradedModule.FD R n (e k))) i) := by
  obtain ⟨epi⟩ := GradedModule.nonempty_HEquiv_pi (fun k => GradedModule.FD R n (e k)) i
  have : ∀ k, Subsingleton (GradedModule.H (GradedModule.FD R n (e k)) i) := fun k => by
    obtain ⟨eFD⟩ := GradedModule.nonempty_HEquiv_FD R n (e k) i
    have := Twist.subsingleton_cohomology_of_neg_le R n (he k) hi
    exact eFD.symm.toEquiv.subsingleton
  exact epi.toEquiv.subsingleton

variable {M : GradedModule R n}

namespace GradedModule
open _root_.ProjSpaceCech.GradedModule
namespace Presentation
open _root_.ProjSpaceCech.GradedModule.Presentation
end GradedModule.Presentation
namespace GradedModule.Presentation
open scoped _root_.ProjSpaceCech.GradedModule _root_.ProjSpaceCech.GradedModule.Presentation in
private def _root_.ProjSpaceCech.GradedModule.Presentation.shiftP (σ : GradedModule.Presentation M)
  (d : ℤ) :
    GradedModule.Presentation (GradedModule.shift M d) where
  J := σ.J
  d₀ := fun k => σ.d₀ k + d
  hom :=
    { toLinearMap := σ.hom.toLinearMap
      mem_grade := fun c m hm => by
        change σ.hom.toLinearMap m ∈ M.grade (c + d)
        refine σ.hom.mem_grade (c + d) m ?_
        intro k hk
        have h := hm k hk
        change m k ∈ GradedModule.freeGrade R n (c + (σ.d₀ k + d)) at h
        change m k ∈ GradedModule.freeGrade R n (c + d + σ.d₀ k)
        rwa [show c + d + σ.d₀ k = c + (σ.d₀ k + d) by ring]
      xMul_comm := fun j => LinearMap.ext fun m => LinearMap.congr_fun (σ.hom.xMul_comm j) m }
  surj := fun c m hm => by
    obtain ⟨m', hm', h⟩ := σ.surj (c + d) m hm
    refine ⟨m', fun k hk => ?_, h⟩
    have h' := hm' k hk
    change m' k ∈ GradedModule.freeGrade R n (c + d + σ.d₀ k) at h'
    change m' k ∈ GradedModule.freeGrade R n (c + (σ.d₀ k + d))
    rwa [show c + (σ.d₀ k + d) = c + d + σ.d₀ k by ring]

end GradedModule.Presentation
open _root_.ProjSpaceCech
namespace GradedModule.Presentation
open scoped _root_.ProjSpaceCech.GradedModule _root_.ProjSpaceCech.GradedModule.Presentation in
private def _root_.ProjSpaceCech.GradedModule.Presentation.kerToShift (σ :
  GradedModule.Presentation M) (d : ℤ) :
    GradedModule.Hom (GradedModule.Presentation.ker (σ.shiftP d)) (GradedModule.shift σ.ker d) where
  toLinearMap := LinearMap.id
  mem_grade := fun c m hm => by
    refine ⟨fun k hk => ?_, hm.2⟩
    have h := hm.1 k hk
    change m k ∈ GradedModule.freeGrade R n (c + (σ.d₀ k + d)) at h
    change m k ∈ GradedModule.freeGrade R n (c + d + σ.d₀ k)
    rwa [show c + d + σ.d₀ k = c + (σ.d₀ k + d) by ring]
  xMul_comm := fun _ => rfl

end GradedModule.Presentation
open _root_.ProjSpaceCech
namespace GradedModule.Presentation
open scoped _root_.ProjSpaceCech.GradedModule _root_.ProjSpaceCech.GradedModule.Presentation in
private def _root_.ProjSpaceCech.GradedModule.Presentation.shiftToKer (σ :
  GradedModule.Presentation M) (d : ℤ) :
    GradedModule.Hom (GradedModule.shift σ.ker d) (GradedModule.Presentation.ker (σ.shiftP d)) where
  toLinearMap := LinearMap.id
  mem_grade := fun c m hm => by
    refine ⟨fun k hk => ?_, hm.2⟩
    have h := hm.1 k hk
    change m k ∈ GradedModule.freeGrade R n (c + d + σ.d₀ k) at h
    change m k ∈ GradedModule.freeGrade R n (c + (σ.d₀ k + d))
    rwa [show c + (σ.d₀ k + d) = c + d + σ.d₀ k by ring]
  xMul_comm := fun _ => rfl

end GradedModule.Presentation
open _root_.ProjSpaceCech
open scoped _root_.ProjSpaceCech.GradedModule _root_.ProjSpaceCech.GradedModule.Presentation in
theorem GradedModule.Presentation.secMap_shiftToKer_kerToShift (σ : GradedModule.Presentation M) (d
  : ℤ)
    (I : Finset (Fin (n + 1))) (q : GradedModule.sec (GradedModule.Presentation.ker (σ.shiftP d))
      I) :
    GradedModule.Hom.secMap (σ.shiftToKer d) I (GradedModule.Hom.secMap (σ.kerToShift d) I q) = q
      := by
  obtain ⟨x⟩ := q; rfl

open scoped _root_.ProjSpaceCech.GradedModule _root_.ProjSpaceCech.GradedModule.Presentation in
theorem GradedModule.Presentation.secMap_kerToShift_shiftToKer (σ : GradedModule.Presentation M) (d
  : ℤ)
    (I : Finset (Fin (n + 1))) (q : GradedModule.sec (GradedModule.shift σ.ker d) I) :
    GradedModule.Hom.secMap (σ.kerToShift d) I (GradedModule.Hom.secMap (σ.shiftToKer d) I q) = q
      := by
  obtain ⟨x⟩ := q; rfl

open scoped _root_.ProjSpaceCech.GradedModule _root_.ProjSpaceCech.GradedModule.Presentation in
theorem GradedModule.Presentation.cochainMap_kerToShift_bijective (σ : GradedModule.Presentation M)
  (d : ℤ)
    (i : ℕ) : Function.Bijective (GradedModule.Hom.cochainMap (σ.kerToShift d) i) := by
  refine Function.bijective_iff_has_inverse.mpr ⟨GradedModule.Hom.cochainMap (σ.shiftToKer d) i,
    ?_, ?_⟩
  · intro f; funext s
    exact GradedModule.Presentation.secMap_shiftToKer_kerToShift σ d _ (f s)
  · intro f; funext s
    exact GradedModule.Presentation.secMap_kerToShift_shiftToKer σ d _ (f s)

open scoped _root_.ProjSpaceCech.GradedModule in
theorem GradedModule.subsingleton_cohomology_shift_of_isFG' [IsNoetherianRing R]
    (M : GradedModule R n) (hM : GradedModule.IsFG M) :
    ∃ d₀ : ℤ, ∀ d, d₀ ≤ d → ∀ i, 1 ≤ i →
      Subsingleton (GradedModule.H (GradedModule.shift M d) i) := by
  classical
  have main : ∀ i, 1 ≤ i → ∀ (M' : GradedModule R n), GradedModule.IsFG M' →
      ∃ d₀ : ℤ, ∀ d, d₀ ≤ d → Subsingleton (GradedModule.H (GradedModule.shift M' d) i) := by
    intro i
    induction i using Nat.strong_decreasing_induction with
    | base =>
      refine ⟨n, fun m hm _ M' _ => ⟨0, fun d _ => ?_⟩⟩
      exact GradedModule.subsingleton_cohomology_of_lt (GradedModule.shift M' d) hm
    | step i IH =>
      intro hi M' hM'
      obtain ⟨σ⟩ := hM'
      obtain ⟨dK, hdK⟩ := IH (i + 1) (Nat.lt_succ_self i) (by omega) σ.ker
        (GradedModule.Presentation.ker_isFG σ)
      refine ⟨max (-(n : ℤ) + ∑ k, |σ.d₀ k|) dK, fun d hd => ?_⟩
      have hdF : ∀ k, -(n : ℤ) ≤ σ.d₀ k + d := fun k => by
        have h1 : |σ.d₀ k| ≤ ∑ j, |σ.d₀ j| :=
          Finset.single_le_sum (f := fun j => |σ.d₀ j|) (fun j _ => abs_nonneg _) (Finset.mem_univ
            k)
        have h2 : -σ.d₀ k ≤ |σ.d₀ k| := neg_le_abs _
        have h3 := le_of_max_le_left hd
        linarith
      have hF : Subsingleton (GradedModule.H (GradedModule.Presentation.F (σ.shiftP d)) i) :=
        GradedModule.subsingleton_H_pi_FD (fun k => σ.d₀ k + d) hi hdF
      have hK : Subsingleton
          (GradedModule.H (GradedModule.Presentation.ker (σ.shiftP d)) (i + 1)) := by
        have := hdK d (le_of_max_le_right hd)
        exact (GradedModule.HMap_bijective_of_cochainMap_bijective (σ.kerToShift d)
          (GradedModule.Presentation.cochainMap_kerToShift_bijective σ d) (i + 1)).1.subsingleton
      exact GradedModule.Presentation.subsingleton_H_of_ses (σ.shiftP d) i hF hK
  have hall : ∀ i, ∃ d₀ : ℤ, ∀ d, d₀ ≤ d → 1 ≤ i →
      Subsingleton (GradedModule.H (GradedModule.shift M d) i) := by
    intro i
    by_cases hi : 1 ≤ i
    · obtain ⟨d₀, h⟩ := main i hi M hM
      exact ⟨d₀, fun d hd _ => h d hd⟩
    · exact ⟨0, fun d _ h => absurd h hi⟩
  choose f hf using hall
  refine ⟨∑ i ∈ Finset.range (n + 1), |f i|, fun d hd i hi => ?_⟩
  by_cases hin : n < i
  · exact GradedModule.subsingleton_cohomology_of_lt (GradedModule.shift M d) hin
  · refine hf i d ?_ hi
    have h1 : |f i| ≤ ∑ j ∈ Finset.range (n + 1), |f j| :=
      Finset.single_le_sum (f := fun j => |f j|) (fun j _ => abs_nonneg _)
        (Finset.mem_range.mpr (by omega))
    have h2 : f i ≤ |f i| := le_abs_self _
    linarith

end SerreVanishing

end ProjSpaceCech

theorem _root_.ProjSpaceCech.GradedModule.subsingleton_cohomology_shift_of_isFG {R : Type u}
  [CommRing R] [IsNoetherianRing R] {n : ℕ}
    (M : ProjSpaceCech.GradedModule R n) (hM : ProjSpaceCech.GradedModule.IsFG M) :
    ∃ d₀ : ℤ, ∀ d, d₀ ≤ d → ∀ i, 1 ≤ i → Subsingleton (ProjSpaceCech.GradedModule.H
      (ProjSpaceCech.GradedModule.shift M d) i) :=
  ProjSpaceCech.GradedModule.subsingleton_cohomology_shift_of_isFG' M hM

end
end ProjSpaceCech_GradedModule_subsingleton_cohomology_shift_of_isFG
end AlgebraicCurves.Cohomology.Cech.Proofs
end ProofImplementation
