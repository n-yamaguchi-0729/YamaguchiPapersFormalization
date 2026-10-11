/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_finiteDimensional_adjoin_of_transcendental.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Finite Dimensional adjoin of transcendental
-/

section ProofImplementation

namespace AlgebraicCurves.FunctionFields.Proofs.FiniteDimensional_adjoin_of_transcendental

open Set Cardinal

namespace AlgebraicCurve
namespace FF2KE3

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem isAlgebraic_adjoin_of_transcendental' (x : F)
    [halg : Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F]
    {t : F} (ht : Transcendental K t) :
    Algebra.IsAlgebraic (IntermediateField.adjoin K ({t} : Set F)) F := by
  have hx : Transcendental K x := by
    intro hxalg
    have : Algebra.IsAlgebraic K (IntermediateField.adjoin K ({x} : Set F)) :=
      IntermediateField.isAlgebraic_adjoin_simple hxalg.isIntegral
    have : Algebra.IsAlgebraic K F :=
      Algebra.IsAlgebraic.trans K (IntermediateField.adjoin K ({x} : Set F)) F
    exact ht (Algebra.IsAlgebraic.isAlgebraic t)
  have hbx : IsTranscendenceBasis K ![x] := by
    rw [isTranscendenceBasis_iff_algebraicIndependent_isAlgebraic]
    refine ⟨algebraicIndependent_iff_transcendental.mpr hx, ?_⟩
    have : Set.range ![x] = {x} := by simp
    rw [this]
    exact (IntermediateField.isAlgebraic_adjoin_iff_top (F := K) (s := ({x} : Set F))).mp halg
  have hind : AlgebraicIndepOn K id ({t} : Set F) := by
    rw [AlgebraicIndepOn, algebraicIndependent_unique_type_iff]
    simpa using ht
  obtain ⟨S, htS, hS⟩ := exists_isTranscendenceBasis_superset hind
  have hcard := hS.lift_cardinalMk_eq hbx
  simp only [Cardinal.mk_fin, Nat.cast_one, Cardinal.lift_one, Cardinal.lift_eq_one] at hcard
  have hS_eq : S = {t} :=
    (Cardinal.mk_le_one_iff_set_subsingleton.mp hcard.le).eq_singleton_of_mem (htS rfl)
  subst hS_eq
  have h := hS.isAlgebraic_field
  rwa [Subtype.range_coe] at h

theorem finiteDimensional_adjoin_of_transcendental' (x : F)
    [hfin : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    {t : F} (ht : Transcendental K t) :
    FiniteDimensional (IntermediateField.adjoin K ({t} : Set F)) F := by
  have halg : Algebra.IsAlgebraic (IntermediateField.adjoin K ({t} : Set F)) F :=
    isAlgebraic_adjoin_of_transcendental' x ht
  set E := IntermediateField.adjoin K ({t} : Set F)
  set Kx := IntermediateField.adjoin K ({x} : Set F)
  let b := Module.finBasis Kx F
  let S : Set F := insert x (Set.range b)
  have : Finite S := Set.Finite.insert x (Set.finite_range b) |>.to_subtype
  have hM : FiniteDimensional E (IntermediateField.adjoin E S) :=
    IntermediateField.finiteDimensional_adjoin fun y _ => (halg.isAlgebraic y).isIntegral
  have htop : IntermediateField.adjoin E S = ⊤ := by
    rw [eq_top_iff]
    intro y _
    have hKx : ∀ c : Kx, (c : F) ∈ IntermediateField.adjoin E S := by
      intro c
      have hle : Kx ≤ (IntermediateField.adjoin E S).restrictScalars K := by
        rw [IntermediateField.adjoin_le_iff]
        intro z hz
        rw [Set.mem_singleton_iff] at hz
        subst hz
        exact IntermediateField.subset_adjoin E S (Set.mem_insert _ _)
      exact hle c.2
    rw [← b.sum_repr y]
    refine Subfield.sum_mem _ fun i _ => ?_
    rw [IntermediateField.smul_def]
    exact mul_mem (hKx _) (IntermediateField.subset_adjoin E S (Set.mem_insert_of_mem _ ⟨i, rfl⟩))
  rw [htop] at hM
  exact (IntermediateField.topEquiv (F := E) (E := F)).toLinearEquiv.finiteDimensional

end AlgebraicCurve.FF2KE3

theorem _root_.AlgebraicCurve.finiteDimensional_adjoin_of_transcendental {K F : Type*} [Field K]
  [Field F] [Algebra K F] (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] {t : F} (ht : Transcendental
      K t) :
    FiniteDimensional (IntermediateField.adjoin K ({t} : Set F)) F :=
  AlgebraicCurve.FF2KE3.finiteDimensional_adjoin_of_transcendental' x ht
end AlgebraicCurves.FunctionFields.Proofs.FiniteDimensional_adjoin_of_transcendental
end ProofImplementation
