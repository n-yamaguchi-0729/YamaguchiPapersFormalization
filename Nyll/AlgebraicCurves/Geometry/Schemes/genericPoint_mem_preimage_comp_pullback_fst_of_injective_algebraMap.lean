/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_genericPoint_mem_preimage_comp_pullback_fst_of_injective_algebraMap.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.Topology.Sober
import Mathlib.RingTheory.Ideal.Prime
import Mathlib.RingTheory.Ideal.Maps

/-!
# generic Point mem preimage comp pullback fst of injective algebra Map
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace genericPoint_mem_preimage_comp_pullback_fst_of_injective_algebraMap

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem _root_.AlgebraicGeometry.genericPoint_mem_preimage_comp_pullback_fst_of_injective_algebraMap
    {R : Type u} [CommRing R] {K : Type u} [Field K] [Algebra R K]
    (hinj : Function.Injective (algebraMap R K))
    {X : Scheme.{u}} (c : X ⟶ Spec (.of R)) [IsIntegral X]
    {Y : Scheme.{u}} [IsIntegral Y]
    (e₀ : Y ⟶ pullback c (Spec.map (CommRingCat.ofHom (algebraMap R K)))) [IsIso e₀]
    (U : X.Opens) (hU : (U : Set X).Nonempty) :
    genericPoint Y ∈ (e₀ ≫ pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ⁻¹ᵁ U :=
      by
  let ι : Spec (.of K) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom (algebraMap R K))
  let g : Y ⟶ X := e₀ ≫ pullback.fst c ι
  change genericPoint Y ∈ g ⁻¹ᵁ U
  have hηU : genericPoint X ∈ (U : Set X) :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).2 (by simpa using hU)
  let z₀ : ↥(pullback c ι) := e₀ (genericPoint Y)
  have hz : ∀ z : ↥(pullback c ι), c (pullback.fst c ι z) = ι (pullback.snd c ι z) := fun z => by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
  have hbot : ∀ w : ↥(Spec (.of K)), (show PrimeSpectrum R from ι w).asIdeal = ⊥ := fun w => by
    let p : PrimeSpectrum K := w
    have hw : p.asIdeal = ⊥ := Ideal.eq_bot_of_prime _
    exact (PrimeSpectrum.comap_asIdeal (algebraMap R K) p).trans
      ((congrArg (Ideal.comap (algebraMap R K)) hw).trans
        (Ideal.comap_bot_of_injective (algebraMap R K) hinj))
  have hle : (show PrimeSpectrum R from c (genericPoint X)).asIdeal ≤ ⊥ := by
    rw [← hbot (pullback.snd c ι z₀), PrimeSpectrum.asIdeal_le_asIdeal,
      PrimeSpectrum.le_iff_specializes]
    change c (genericPoint X) ⤳ ι (pullback.snd c ι z₀)
    rw [← hz z₀]
    exact (genericPoint_specializes (pullback.fst c ι z₀)).map c.continuous
  have hcη : c (genericPoint X) = ι (pullback.snd c ι z₀) :=
    PrimeSpectrum.ext ((le_bot_iff.1 hle).trans (hbot _).symm)
  have hrange : genericPoint X ∈ Set.range (pullback.fst c ι) := by
    rw [Scheme.Pullback.range_fst]
    exact ⟨pullback.snd c ι z₀, hcη.symm⟩
  obtain ⟨z, hz'⟩ := hrange
  have hgy : g (inv e₀ z) = genericPoint X := by
    change (inv e₀ ≫ e₀ ≫ pullback.fst c ι) z = genericPoint X
    rw [IsIso.inv_hom_id_assoc]
    exact hz'
  have hsp : g (genericPoint Y) ⤳ genericPoint X := hgy ▸ (genericPoint_specializes (inv e₀ z)).map
    g.continuous
  exact hsp.mem_open U.isOpen hηU
end genericPoint_mem_preimage_comp_pullback_fst_of_injective_algebraMap
end AlgebraicCurves.Geometry.Schemes.Proofs
end ProofImplementation
