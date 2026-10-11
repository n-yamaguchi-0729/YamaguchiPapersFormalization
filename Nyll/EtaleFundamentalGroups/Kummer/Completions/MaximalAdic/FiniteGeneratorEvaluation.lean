/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.RingTheory.MvPowerSeries.Evaluation

/-!
# Finite-generator presentations of maximal-adic completions

If a finite family generates the maximal ideal of a Noetherian local ring,
evaluation of multivariate formal power series at the images of that family
surjects onto the maximal-adic completion.  This works for an arbitrary
finite number of generators and does not use regularity.

The remaining step from this presentation to Noetherianity is precisely the
multivariate formal-power-series Hilbert basis theorem for a finite variable
type.  Mathlib currently supplies that theorem only for the univariate
`PowerSeries` specialization.
-/

noncomputable section

open IsLocalRing
open scoped MvPowerSeries.WithPiTopology

namespace EtaleFundamentalGroups.Kummer

universe u v

/-- Evaluation at any finite generating family of the closed point is a
surjection from the corresponding multivariate power-series ring onto the
maximal-adic completion. -/
theorem mvPowerSeries_surjective_maximalAdicCompletion_of_generators
    {B : Type u} [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    {ι : Type v} [Finite ι]
    (t : ι → B)
    (hgen : Ideal.span (Set.range t) = maximalIdeal B) :
    ∃ f : MvPowerSeries ι B →+*
        AdicCompletion (maximalIdeal B) B,
      Function.Surjective f := by
  classical
  let Bhat := AdicCompletion (maximalIdeal B) B
  let that : ι → Bhat := fun i ↦ algebraMap B Bhat (t i)
  have htMem (i : ι) : t i ∈ maximalIdeal B := by
    rw [← hgen]
    exact Ideal.subset_span (Set.mem_range_self i)
  have hthatMem (i : ι) : that i ∈ maximalIdeal Bhat := by
    rw [AdicCompletion.maximalIdeal_eq_map]
    exact Ideal.mem_map_of_mem (algebraMap B Bhat) (htMem i)
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
  have hcontinuousAlgebraMap : Continuous coeffMap :=
    (WithIdeal.uniformContinuous_of_map_le
      (f := coeffMap) hcoeffMap).continuous
  have hEval : MvPowerSeries.HasEval that :=
    { hpow := fun i ↦
        WithIdeal.isTopologicallyNilpotent_of_mem (hthatMem i)
      tendsto_zero := by
        rw [Filter.cofinite_eq_bot]
        exact Filter.tendsto_bot }
  let f : MvPowerSeries ι B →+* Bhat :=
    MvPowerSeries.eval₂Hom hcontinuousAlgebraMap hEval
  have hfC (b : B) :
      f (MvPowerSeries.C b) = algebraMap B Bhat b := by
    simpa only [f, coeffMap, MvPowerSeries.coe_eval₂Hom] using
      MvPowerSeries.eval₂_C (φ := coeffMap) (a := that) b
  have hfX (i : ι) : f (MvPowerSeries.X i) = that i := by
    simpa only [f, MvPowerSeries.coe_eval₂Hom] using
      MvPowerSeries.eval₂_X (φ := coeffMap) (a := that) i
  let Ivars : Ideal (MvPowerSeries ι B) :=
    Ideal.span (Set.range MvPowerSeries.X)
  have hmap : Ivars.map f = maximalIdeal Bhat := by
    calc
      Ivars.map f = Ideal.span (f '' Set.range MvPowerSeries.X) := by
        change (Ideal.span (Set.range MvPowerSeries.X)).map f = _
        rw [Ideal.map_span]
      _ = Ideal.span (Set.range that) := by
        congr 1
        ext z
        simp only [Set.mem_image, Set.mem_range]
        constructor
        · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
          exact ⟨i, (hfX i).symm⟩
        · rintro ⟨i, rfl⟩
          exact ⟨MvPowerSeries.X i, ⟨i, rfl⟩, hfX i⟩
      _ = (Ideal.span (Set.range t)).map (algebraMap B Bhat) := by
        rw [Ideal.map_span]
        congr 1
        ext z
        simp only [Set.mem_image, Set.mem_range, that]
        constructor
        · rintro ⟨i, rfl⟩
          exact ⟨t i, ⟨i, rfl⟩, rfl⟩
        · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
          exact ⟨i, rfl⟩
      _ = (maximalIdeal B).map (algebraMap B Bhat) := by rw [hgen]
      _ = maximalIdeal Bhat := AdicCompletion.maximalIdeal_eq_map.symm
  have hbaseResidue : Function.Surjective
      ((Ideal.Quotient.mk (maximalIdeal Bhat)).comp
        (algebraMap B Bhat)) := by
    have hresidue : Function.Surjective
        (IsLocalRing.ResidueField.map (algebraMap B Bhat)) :=
      (AdicCompletion.residueField_map_bijective B).2
    intro z
    obtain ⟨w, hw⟩ := hresidue z
    obtain ⟨b, hb⟩ := IsLocalRing.residue_surjective w
    refine ⟨b, ?_⟩
    change IsLocalRing.residue Bhat (algebraMap B Bhat b) = z
    rw [← IsLocalRing.ResidueField.map_residue, hb]
    exact hw
  have hresidueSurj : Function.Surjective
      ((Ideal.Quotient.mk (Ivars.map f)).comp f) := by
    rw [hmap]
    intro z
    obtain ⟨b, hb⟩ := hbaseResidue z
    refine ⟨MvPowerSeries.C b, ?_⟩
    simpa only [RingHom.comp_apply, hfC] using hb
  let : IsHausdorff (Ivars.map f) Bhat := by
    rw [hmap]
    infer_instance
  have hfSurj : Function.Surjective f :=
    surjective_of_mk_map_comp_surjective f hresidueSurj
  exact ⟨f, hfSurj⟩

/-- Fin-indexed form of the finite-generator presentation. -/
theorem mvPowerSeries_fin_surjective_maximalAdicCompletion_of_generators
    {B : Type u} [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    (n : ℕ) (t : Fin n → B)
    (hgen : Ideal.span (Set.range t) = maximalIdeal B) :
    ∃ f : MvPowerSeries (Fin n) B →+*
        AdicCompletion (maximalIdeal B) B,
      Function.Surjective f :=
  mvPowerSeries_surjective_maximalAdicCompletion_of_generators t hgen

end EtaleFundamentalGroups.Kummer

end
