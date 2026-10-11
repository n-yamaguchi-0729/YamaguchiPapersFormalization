/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Algebra_FormallyEtale_of_formallySmooth_of_bijective_mapBaseChange.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Kaehler.JacobiZariski

/-!
# Algebra Formally Etale of formally Smooth of bijective map Base Change
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.Algebra.Proofs
namespace Algebra_FormallyEtale_of_formallySmooth_of_bijective_mapBaseChange

open _root_.KaehlerDifferential
open _root_.Algebra
open _root_.TensorProduct
open _root_.Algebra.TensorProduct

universe u

namespace R1NeronObjE1

section algebra

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

theorem subsingleton_kaehler_of_surjective
    (h : Function.Surjective (KaehlerDifferential.mapBaseChange R S T)) :
    Subsingleton Ω[T⁄S] := by
  have hex := KaehlerDifferential.exact_mapBaseChange_map R S T
  have hsurj := KaehlerDifferential.map_surjective R S T
  refine ⟨fun a b => ?_⟩
  obtain ⟨a', rfl⟩ := hsurj a
  obtain ⟨b', rfl⟩ := hsurj b
  have ha : KaehlerDifferential.map R S T T a' = 0 := by
    obtain ⟨x, rfl⟩ := h a'
    exact hex.apply_apply_eq_zero x
  have hb : KaehlerDifferential.map R S T T b' = 0 := by
    obtain ⟨x, rfl⟩ := h b'
    exact hex.apply_apply_eq_zero x
  rw [ha, hb]

theorem formallyEtale_of_formallySmooth_of_bijective [Algebra.FormallySmooth R T]
    (h : Function.Bijective (KaehlerDifferential.mapBaseChange R S T)) :
    Algebra.FormallyEtale S T := by
  have hΩ : Subsingleton Ω[T⁄S] := subsingleton_kaehler_of_surjective h.2
  have : Algebra.FormallyUnramified S T := ⟨hΩ⟩
  have hδ : ∀ x, Algebra.H1Cotangent.δ R S T x = 0 := by
    intro x
    have hex := Algebra.H1Cotangent.exact_δ_mapBaseChange R S T
    have hmem : Algebra.H1Cotangent.δ R S T x ∈
        LinearMap.ker (KaehlerDifferential.mapBaseChange R S T) := by
      rw [LinearMap.mem_ker]
      exact hex.apply_apply_eq_zero x
    rwa [LinearMap.ker_eq_bot.mpr h.1, Submodule.mem_bot] at hmem
  have hH1 : Subsingleton (Algebra.H1Cotangent S T) := by
    refine ⟨fun a b => ?_⟩
    have hex := Algebra.H1Cotangent.exact_map_δ R S T
    have ha : a ∈ Set.range (Algebra.H1Cotangent.map R S T T) := (hex a).mp (hδ a)
    have hb : b ∈ Set.range (Algebra.H1Cotangent.map R S T T) := (hex b).mp (hδ b)
    obtain ⟨a', rfl⟩ := ha
    obtain ⟨b', rfl⟩ := hb
    rw [Subsingleton.elim a' b']
  have : Module.Projective T Ω[T⁄S] := Module.Projective.of_free
  have : Algebra.FormallySmooth S T := ⟨inferInstance, hH1⟩
  exact Algebra.FormallyEtale.of_formallyUnramified_and_formallySmooth

end algebra

end R1NeronObjE1

theorem _root_.Algebra.FormallyEtale.of_formallySmooth_of_bijective_mapBaseChange
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Algebra.FormallySmooth R T]
    (h : Function.Bijective (KaehlerDifferential.mapBaseChange R S T)) :
    Algebra.FormallyEtale S T :=
  R1NeronObjE1.formallyEtale_of_formallySmooth_of_bijective (R := R) h
end Algebra_FormallyEtale_of_formallySmooth_of_bijective_mapBaseChange
end AlgebraicCurves.Foundations.Algebra.Proofs
end ProofImplementation
