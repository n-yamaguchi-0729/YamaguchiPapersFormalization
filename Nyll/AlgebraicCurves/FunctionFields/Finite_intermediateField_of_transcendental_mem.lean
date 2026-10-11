/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_finite_intermediateField_of_transcendental_mem.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

/-!
# Finite intermediate Field of transcendental mem
-/

section ProofImplementation

namespace AlgebraicCurves.FunctionFields.Proofs.Finite_intermediateField_of_transcendental_mem

namespace S2Finite

open IntermediateField

variable {K F : Type} [Field K] [Field F] [Algebra K F]

theorem finiteDimensional_adjoin_of_transcendental {x₀ : F} (hx₀ : Transcendental K x₀)
    (hfd : FiniteDimensional K⟮x₀⟯ F) {t : F} (ht : Transcendental K t) : FiniteDimensional K⟮t⟯ F
      := by
  have halg₀ : Algebra.IsAlgebraic (Algebra.adjoin K (Set.range fun _ : Fin 1 => x₀)) F := by
    have : Algebra.IsAlgebraic K⟮x₀⟯ F := Algebra.IsAlgebraic.of_finite _ _
    rw [Set.range_const]
    exact IntermediateField.isAlgebraic_adjoin_iff_top.mp this
  have hb₀ : IsTranscendenceBasis K (fun _ : Fin 1 => x₀) :=
    isTranscendenceBasis_iff_algebraicIndependent_isAlgebraic.mpr
      ⟨(algebraicIndependent_singleton_iff (0 : Fin 1)).mpr hx₀, halg₀⟩
  have htr : Algebra.trdeg K F = Cardinal.mk (Fin 1) := hb₀.cardinalMk_eq_trdeg.symm
  have hbt : IsTranscendenceBasis K (fun _ : Fin 1 => t) :=
    AlgebraicIndependent.isTranscendenceBasis_of_trdeg_le_of_finite
      ((algebraicIndependent_singleton_iff (0 : Fin 1)).mpr ht) htr.le
  have halg : Algebra.IsAlgebraic K⟮t⟯ F := by
    have h := hbt.isAlgebraic_field
    rwa [Set.range_const] at h
  set L := K⟮t⟯
  have hint : IsIntegral L x₀ := (halg.isAlgebraic x₀).isIntegral
  set N : IntermediateField L F := L⟮x₀⟯
  have : FiniteDimensional L N := IntermediateField.adjoin.finiteDimensional hint
  have hmem : ∀ s : K⟮x₀⟯, (s : F) ∈ N := by
    intro s
    have hle : K⟮x₀⟯ ≤ N.restrictScalars K :=
      IntermediateField.adjoin_simple_le_iff.mpr (IntermediateField.mem_adjoin_simple_self L x₀)
    exact hle s.2
  let : Algebra K⟮x₀⟯ N := RingHom.toAlgebra
    { toFun := fun s => ⟨(s : F), hmem s⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have : IsScalarTower K⟮x₀⟯ N F := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Module.Finite N F := Module.Finite.of_restrictScalars_finite K⟮x₀⟯ N F
  exact Module.Finite.trans N F

end S2Finite

open IntermediateField in
theorem _root_.AlgebraicCurve.finite_intermediateField_of_transcendental_mem
    (K L : Type) [Field K] [Field L] [Algebra K L]
    (E : IntermediateField K L) (t : L) (htE : t ∈ E) (ht : Transcendental K t)
    (hfg : ∃ x : L, Transcendental K x ∧ FiniteDimensional ↥(IntermediateField.adjoin K ({x} : Set
      L)) L) :
    Module.Finite ↥E L := by
  obtain ⟨x, hx, hfd⟩ := hfg
  have hfin : FiniteDimensional K⟮t⟯ L := S2Finite.finiteDimensional_adjoin_of_transcendental hx
    hfd ht
  have hle : K⟮t⟯ ≤ E := IntermediateField.adjoin_simple_le_iff.mpr htE
  let : Algebra K⟮t⟯ E := (IntermediateField.inclusion hle).toAlgebra
  have : IsScalarTower K⟮t⟯ E L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact Module.Finite.of_restrictScalars_finite K⟮t⟯ E L
end AlgebraicCurves.FunctionFields.Proofs.Finite_intermediateField_of_transcendental_mem
end ProofImplementation
