/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


import Nyll.AlgebraicCurves.Valuations.FinitelyGeneratedValuationDetection
import Nyll.GaloisCohomology.FieldTheory.FinitelyGeneratedPositiveChar
import Nyll.GaloisCohomology.FieldTheory.ScalarRatioRigidity
import Nyll.ValuedFieldTheory.Valuation.FiniteOrderAutomorphism

/-!
# Discrete valuations moved by finite-order automorphisms

A nontrivial finite-order automorphism of an infinite finitely generated
field of positive characteristic moves a discrete valuation class.
-/

namespace FieldTheory
open ValuationTheory.DiscreteValuationField
universe u

/-- A nontrivial finite-order automorphism of an infinite finitely generated
field of positive characteristic moves some discrete valuation class. -/
theorem exists_moved_DVF_of_fg_posChar
    (K : Type u) [Field K] [Infinite K] (hfg : Field.FG K)
    (hchar : ringChar K ≠ 0) (τ : K ≃+* K) (hne : τ ≠ 1)
    (n : ℕ) (hn : 0 < n) (hpow : τ ^ n = 1) :
    ∃ D : DVF.{u,0} K, ¬ D.valuation.IsEquiv (D.valuation.comap τ.toRingHom) := by
  classical
  by_contra hno
  have hstable (D : DVF.{u,0} K) :
      D.valuation.IsEquiv (D.valuation.comap τ.toRingHom) :=
    not_not.mp (fun h => hno ⟨D, h⟩)
  let C : Subfield K := (algebraicClosure (⊥ : Subfield K) K).toSubfield
  have : Finite C := finite_constants_of_fg_posChar K hfg hchar
  have hC : C ≠ ⊤ := by
    intro heq
    have : Finite K := Finite.of_surjective C.subtype (by
      intro x
      exact ⟨⟨x, heq ▸ Subfield.mem_top x⟩, rfl⟩)
    exact not_finite K
  have hratio (x : K) (hx : x ≠ 0) : τ x / x ∈ C := by
    by_contra hc
    obtain ⟨D, hD⟩ := exists_DVF_detect_nonconstant K hfg (τ x / x) hc
    apply hD
    rw [map_div₀, Valuation.map_apply_eq_of_isEquiv_comap_of_pow_eq_one
      D.valuation τ (hstable D) n hn hpow]
    exact div_self ((map_ne_zero D.valuation).mpr hx)
  have heq := ringHom_eq_id_of_div_mem_subfield C hC τ.toRingHom hratio
  apply hne
  apply RingEquiv.ext
  intro x
  exact DFunLike.congr_fun heq x
end FieldTheory
