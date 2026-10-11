/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Cohomology.Cech.TwoChartCech
import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.Finiteness.Basic

/-!
# Kernel base change for a map with projective cokernel

Splitting the cokernel makes the image a projective direct summand.
Splitting the surjection onto this image makes the kernel a finite
projective direct summand and proves its canonical arbitrary base change.
-/

noncomputable section

open scoped TensorProduct

namespace TwoChartCech

universe u

private theorem exists_subtype_retraction_of_projective_quotient
    {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    (K : Submodule R M) [Module.Projective R (M ⧸ K)] :
    ∃ r : M →ₗ[R] K, r ∘ₗ K.subtype = LinearMap.id := by
  obtain ⟨s, hs⟩ := K.mkQ.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr K.mkQ_surjective)
  have hsApply (x : M ⧸ K) : K.mkQ (s x) = x := LinearMap.congr_fun hs x
  have hmem (x : M) : x - s (K.mkQ x) ∈ K := by
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply,
      map_sub, hsApply, sub_self]
  let r : M →ₗ[R] K := (LinearMap.id - s ∘ₗ K.mkQ).codRestrict K hmem
  refine ⟨r, LinearMap.ext fun x => Subtype.ext ?_⟩
  change x.1 - s (K.mkQ x.1) = x.1
  have hx0 : K.mkQ x.1 = 0 := (Submodule.Quotient.mk_eq_zero K).mpr x.2
  rw [hx0, map_zero, sub_zero]

/-- Projectivity of the actual cokernel supplies finite projectivity of
the kernel and bijectivity of its canonical base-change map over every algebra. -/
theorem finite_projective_ker_and_bijective_baseChange_of_projective_coker
    {R M N : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
    [AddCommGroup N] [Module R N] [Module.Projective R N]
    (d : M →ₗ[R] N) [Module.Projective R (N ⧸ LinearMap.range d)] :
    Module.Finite R (LinearMap.ker d) ∧ Module.Projective R (LinearMap.ker d) ∧
      ∀ (A : Type u) [CommRing A] [Algebra R A],
        Function.Bijective (kerBaseChangeHom d A) := by
  let I : Submodule R N := LinearMap.range d
  let K : Submodule R M := LinearMap.ker d
  obtain ⟨rI, hrI⟩ := exists_subtype_retraction_of_projective_quotient I
  have hProjectiveI : Module.Projective R I := Module.Projective.of_split I.subtype rI hrI
  obtain ⟨s, hs⟩ := d.rangeRestrict.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr d.surjective_rangeRestrict)
  have hsApply (x : I) : d (s x) = x.1 :=
    congrArg Subtype.val (LinearMap.congr_fun hs x)
  have hmem (x : M) : x - s (d.rangeRestrict x) ∈ K := by
    change d (x - s (d.rangeRestrict x)) = 0
    rw [map_sub, hsApply]
    exact sub_self (d x)
  let rK : M →ₗ[R] K :=
    (LinearMap.id - s ∘ₗ d.rangeRestrict).codRestrict K hmem
  have hrK : rK ∘ₗ K.subtype = LinearMap.id := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change x.1 - s (d.rangeRestrict x.1) = x.1
    have hx : d.rangeRestrict x.1 = 0 := Subtype.ext x.2
    rw [hx, map_zero, sub_zero]
  have hFiniteK : Module.Finite R K :=
    Module.Finite.of_surjective rK (fun x => ⟨x.1, LinearMap.congr_fun hrK x⟩)
  have hProjectiveK : Module.Projective R K := Module.Projective.of_split K.subtype rK hrK
  have hImage : I.subtype ∘ₗ d.rangeRestrict = d := LinearMap.ext fun _ => rfl
  have hKernel : K.subtype ∘ₗ rK = LinearMap.id - s ∘ₗ d.rangeRestrict :=
    LinearMap.ext fun _ => rfl
  refine ⟨hFiniteK, hProjectiveK, fun A _ _ => ?_⟩
  have hLeftI : Function.LeftInverse (rI.baseChange A) (I.subtype.baseChange A) := by
    intro x
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hrI,
      LinearMap.baseChange_id, LinearMap.id_apply]
  have hLeftK : Function.LeftInverse (rK.baseChange A) (K.subtype.baseChange A) := by
    intro x
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hrK,
      LinearMap.baseChange_id, LinearMap.id_apply]
  constructor
  · intro x y hxy
    exact hLeftK.injective (congrArg Subtype.val hxy)
  · intro z
    have hz : (d.rangeRestrict.baseChange A) z.1 = 0 := by
      apply hLeftI.injective
      rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hImage, map_zero]
      exact z.2
    refine ⟨rK.baseChange A z.1, Subtype.ext ?_⟩
    change (K.subtype.baseChange A) (rK.baseChange A z.1) = z.1
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hKernel,
      LinearMap.baseChange_sub, LinearMap.baseChange_id, LinearMap.baseChange_comp,
      LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, hz, map_zero, sub_zero]

end TwoChartCech
