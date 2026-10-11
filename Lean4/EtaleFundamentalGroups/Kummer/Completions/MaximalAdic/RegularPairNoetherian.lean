/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.RingTheory.PowerSeries.Evaluation
import Mathlib.RingTheory.PowerSeries.Ideal
import EtaleFundamentalGroups.Kummer.Completions.RegularPair.ParameterQuotient

/-!
# Noetherianity of the maximal-adic completion of a regular pair

Mathlib constructs the maximal-adic completion of a Noetherian local ring as
a complete local ring, but does not currently provide its Noetherian-ring
instance.  For the two-parameter situation used by one-point inertia, there
is a concrete source for that missing finiteness.

If `x, y` is a regular system generating the closed point of `B`, evaluate
the two variables of the iterated power-series ring `B⟦X⟧⟦X⟧` at the images
of `x` and `y` in `B̂`.  The source is Noetherian by the univariate
power-series Hilbert basis theorem.  Surjectivity is proved one variable at
a time.  Modulo `y`, the completed quotient is a DVR, so the inner evaluation
is separated; modulo its remaining uniformizer the map is the usual residue
map of the completion.  Adic completeness then lifts residue-level
surjectivity first across `x` and then across `y`.

This supplies an actual Noetherian source and does not add Noetherianity of
the completion as a hypothesis.
-/

noncomputable section

open IsLocalRing
open RingTheory.Sequence
open scoped PowerSeries.WithPiTopology

namespace EtaleFundamentalGroups.Kummer

universe u

/-- Hausdorffness for a larger ideal implies Hausdorffness for a smaller
ideal.  This elementary direction does not require a Noetherian ring. -/
theorem IsHausdorff.of_le_ideal
    {R : Type u} [CommRing R] {I J : Ideal R}
    [IsHausdorff J R] (hIJ : I ≤ J) : IsHausdorff I R := by
  refine ⟨fun z hz ↦ IsHausdorff.haus (I := J) inferInstance z fun n ↦ ?_⟩
  exact SModEq.mono
    (Submodule.smul_mono
      (pow_le_pow_left' hIJ n) (le_refl (⊤ : Submodule R R)))
    (hz n)

/-- Evaluation of two successive formal variables at a regular pair in the
maximal-adic completion is surjective. -/
theorem iteratedPowerSeries_surjective_maximalAdicCompletion_of_regularPair
    {B : Type u} [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    {x y : B}
    (hreg : IsRegular B [x, y])
    (hgen : Ideal.ofList [x, y] = maximalIdeal B) :
    ∃ f : PowerSeries (PowerSeries B) →+*
        AdicCompletion (maximalIdeal B) B,
      Function.Surjective f := by
  classical
  let Bhat := AdicCompletion (maximalIdeal B) B
  let xhat : Bhat := algebraMap B Bhat x
  let yhat : Bhat := algebraMap B Bhat y
  have hgeometry := maximalAdicCompletion_regularPair_geometry hreg hgen
  let : IsDomain Bhat := hgeometry.1
  have hxMem : x ∈ maximalIdeal B := by
    rw [← hgen]
    exact Ideal.subset_span (by simp)
  have hyMem : y ∈ maximalIdeal B := by
    rw [← hgen]
    exact Ideal.subset_span (by simp)
  have hxhatMem : xhat ∈ maximalIdeal Bhat := by
    rw [AdicCompletion.maximalIdeal_eq_map]
    exact Ideal.mem_map_of_mem (algebraMap B Bhat) hxMem
  have hyhatMem : yhat ∈ maximalIdeal Bhat := by
    rw [AdicCompletion.maximalIdeal_eq_map]
    exact Ideal.mem_map_of_mem (algebraMap B Bhat) hyMem
  let : WithIdeal B := ⟨⊥⟩
  let : WithIdeal Bhat := ⟨maximalIdeal Bhat⟩
  have hCompleteHat :
      IsAdicComplete (maximalIdeal Bhat) Bhat := inferInstance
  have hAdicHat : IsAdic (maximalIdeal Bhat) := rfl
  let : CompleteSpace Bhat :=
    (hAdicHat.isAdicComplete_iff.mp hCompleteHat).1
  let : T2Space Bhat :=
    (hAdicHat.isAdicComplete_iff.mp hCompleteHat).2
  let coeffMap : B →+* Bhat := algebraMap B Bhat
  have hcoeffMap :
      Ideal.map coeffMap (⊥ : Ideal B) ≤ maximalIdeal Bhat := by
    rw [Ideal.map_bot]
    exact bot_le
  have hcontinuousAlgebraMap :
      Continuous coeffMap :=
    (WithIdeal.uniformContinuous_of_map_le
      (f := coeffMap) hcoeffMap).continuous
  have hxEval : PowerSeries.HasEval xhat :=
    WithIdeal.isTopologicallyNilpotent_of_mem hxhatMem
  have hyEval : PowerSeries.HasEval yhat :=
    WithIdeal.isTopologicallyNilpotent_of_mem hyhatMem
  let fInner : PowerSeries B →+* Bhat :=
    PowerSeries.eval₂Hom hcontinuousAlgebraMap hxEval
  have hfInnerC (b : B) : fInner (PowerSeries.C b) = algebraMap B Bhat b := by
    simpa only [fInner, coeffMap, PowerSeries.coe_eval₂Hom] using
      PowerSeries.eval₂_C (R := B) (S := Bhat)
        (φ := coeffMap) (a := xhat) b
  have hfInnerX : fInner PowerSeries.X = xhat := by
    simpa only [fInner, PowerSeries.coe_eval₂Hom] using
      PowerSeries.eval₂_X (R := B) (S := Bhat)
        (φ := coeffMap) (a := xhat)
  have hfInnerContinuous : Continuous fInner := by
    simpa only [fInner, PowerSeries.coe_eval₂Hom] using
      PowerSeries.continuous_eval₂ hcontinuousAlgebraMap hxEval
  let f : PowerSeries (PowerSeries B) →+* Bhat :=
    PowerSeries.eval₂Hom hfInnerContinuous hyEval
  have hfC (a : PowerSeries B) : f (PowerSeries.C a) = fInner a := by
    simpa only [f, PowerSeries.coe_eval₂Hom] using
      PowerSeries.eval₂_C (R := PowerSeries B) (S := Bhat)
        (φ := fInner) (a := yhat) a
  have hfX : f PowerSeries.X = yhat := by
    simpa only [f, PowerSeries.coe_eval₂Hom] using
      PowerSeries.eval₂_X (R := PowerSeries B) (S := Bhat)
        (φ := fInner) (a := yhat)
  let IInner : Ideal (PowerSeries B) := Ideal.span {PowerSeries.X}
  let IOuter : Ideal (PowerSeries (PowerSeries B)) :=
    Ideal.span {PowerSeries.X}
  let Iy : Ideal Bhat := Ideal.span {yhat}
  let Q := Bhat ⧸ Iy
  let qy : Bhat →+* Q := Ideal.Quotient.mk Iy
  let fInnerQ : PowerSeries B →+* Q := qy.comp fInner
  let : IsDomain Q :=
    completedRegularPair_secondParameterQuotient_isDomain hreg hgen
  let : IsDiscreteValuationRing Q := by
    exact completedRegularPair_secondParameterQuotient_isDVR hreg hgen
  have hmapInner :
      IInner.map fInnerQ = Ideal.span {qy xhat} := by
    change (Ideal.span {PowerSeries.X}).map fInnerQ =
      Ideal.span {qy xhat}
    rw [Ideal.map_span, Set.image_singleton]
    have hx : fInnerQ PowerSeries.X = qy xhat := by
      change qy (fInner PowerSeries.X) = qy xhat
      rw [hfInnerX]
    rw [hx]
  have hmapOuter : IOuter.map f = Iy := by
    change (Ideal.span {PowerSeries.X}).map f = Ideal.span {yhat}
    rw [Ideal.map_span, Set.image_singleton, hfX]
  have hmaxQ : maximalIdeal Q = Ideal.span {qy xhat} := by
    exact completedRegularPair_secondParameterQuotient_maximalIdeal_eq
      hreg hgen
  have hmapInnerMax : IInner.map fInnerQ = maximalIdeal Q :=
    hmapInner.trans hmaxQ.symm
  have hresidueSurj : Function.Surjective
      ((Ideal.Quotient.mk (IInner.map fInnerQ)).comp fInnerQ) := by
    rw [hmapInnerMax]
    have hsource : Function.Surjective
        ((Ideal.Quotient.mk (maximalIdeal Q)).comp
          (qy.comp (algebraMap B Bhat))) :=
      completedRegularPair_secondParameterQuotient_residue_surjective
        hreg hgen
    intro z
    rcases hsource z with ⟨b, hb⟩
    refine ⟨PowerSeries.C b, ?_⟩
    simpa only [RingHom.comp_apply, fInnerQ, hfInnerC] using hb
  let : IsHausdorff (IInner.map fInnerQ) Q := by
    rw [hmapInnerMax]
    infer_instance
  have hInnerSurj : Function.Surjective fInnerQ :=
    surjective_of_mk_map_comp_surjective fInnerQ hresidueSurj
  have hOuterResidueSurj : Function.Surjective
      ((Ideal.Quotient.mk (IOuter.map f)).comp f) := by
    intro z
    rcases Ideal.Quotient.mk_surjective z with ⟨bhat, rfl⟩
    rcases hInnerSurj (qy bhat) with ⟨a, ha⟩
    refine ⟨PowerSeries.C a, ?_⟩
    rw [RingHom.comp_apply, hfC]
    rw [hmapOuter]
    change qy (fInner a) = qy bhat
    change qy (fInner a) = qy bhat at ha
    exact ha
  have hIyLe : Iy ≤ maximalIdeal Bhat := by
    change Ideal.span {yhat} ≤ maximalIdeal Bhat
    exact Ideal.span_le.2 (Set.singleton_subset_iff.2 hyhatMem)
  let : IsHausdorff (IOuter.map f) Bhat := by
    rw [hmapOuter]
    exact IsHausdorff.of_le_ideal hIyLe
  have hfSurj : Function.Surjective f :=
    surjective_of_mk_map_comp_surjective f hOuterResidueSurj
  exact ⟨f, hfSurj⟩

/-- The maximal-adic completion of a Noetherian local ring equipped with a
two-element regular system of parameters is Noetherian. -/
theorem maximalAdicCompletion_isNoetherianRing_of_regularPair
    {B : Type u} [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    {x y : B}
    (hreg : IsRegular B [x, y])
    (hgen : Ideal.ofList [x, y] = maximalIdeal B) :
    IsNoetherianRing (AdicCompletion (maximalIdeal B) B) := by
  rcases iteratedPowerSeries_surjective_maximalAdicCompletion_of_regularPair
      hreg hgen with ⟨f, hf⟩
  exact isNoetherianRing_of_surjective
    (PowerSeries (PowerSeries B))
    (AdicCompletion (maximalIdeal B) B) f hf

end EtaleFundamentalGroups.Kummer

end
