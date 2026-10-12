/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_ker_and_pullbackAlong_eq_and_saturated_of_isDiscreteValuationRing.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_comap_ker_subschemeIota_comp_mapOnProdOver_eq_and_saturated_of_isDiscreteValuationRing
import Nyll.AlgebraicCurves.Geometry.Sheaves.IdealSheafData_flat_subschemeInclusion_comp_of_forall_mul_mem_of_isDiscreteValuationRing
import Nyll.JacobianVarieties.Picard.RelEffCartierDiv_exists_I_eq_of_flat_of_comap_mapOnProdOver_eq_of_isDiscreteValuationRing
import Mathlib.Util.WithWeakNamespace

/-!
# The saturated closure of an effective divisor over a discrete valuation ring
-/


section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.SaturatedCartierDVR

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

open _root_.AlgebraicGeometry.Scheme.IdealSheafData in
open _root_.AlgebraicGeometry.IdealSheafData in
with_weak_namespace _root_.AlgebraicGeometry.RelEffCartierDiv
theorem exists_I_eq_ker_and_pullbackAlong_eq_and_saturated_of_isDiscreteValuationRing
    {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} [IsProper f]
    {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (g : Spec (CommRingCat.of O) ⟶ S)
    (T' : Type u) [Field T'] [Algebra O T'] [IsFractionRing O T']
    {gT : Spec (CommRingCat.of T') ⟶ S}
    (hψ : Spec.map (CommRingCat.ofHom (algebraMap O T')) ≫ g = gT)
    {r : ℕ} (E : RelEffCartierDiv f r gT) :
    ∃ Ebar : RelEffCartierDiv f r g,
      Ebar.I = (E.I.subschemeι ≫
        mapOnProdOver f (Spec.map (CommRingCat.ofHom (algebraMap O T'))) hψ).ker ∧
      Ebar.pullbackAlong (Spec.map (CommRingCat.ofHom (algebraMap O T'))) hψ = E ∧
      ∀ (ϖ : O), Irreducible ϖ → ∀ (U : (pullback f g).affineOpens) (s : Γ(pullback f g, U)),
        (pullback f g).presheaf.map (homOfLE (le_top : (U : (pullback f g).Opens) ≤ ⊤)).op
            ((pullback.snd f g).appTop ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ϖ)) * s ∈
          Ebar.I.ideal U →
          s ∈ Ebar.I.ideal U := by
  obtain ⟨hJE, hsat⟩ :=
    comap_ker_subschemeIota_comp_mapOnProdOver_eq_and_saturated_of_isDiscreteValuationRing
      g T' hψ E.I
  have := flat_subschemeInclusion_comp_of_forall_mul_mem_of_isDiscreteValuationRing
    (pullback.snd f g) _ hsat
  obtain ⟨Ebar, hI, hpb⟩ :=
    exists_I_eq_of_flat_of_comap_mapOnProdOver_eq_of_isDiscreteValuationRing g T' hψ E _ hJE
  refine ⟨Ebar, hI, hpb, ?_⟩
  intro ϖ hϖ U s hs
  rw [hI] at hs ⊢
  exact hsat ϖ hϖ U s hs
end JacobianVarieties.Picard.Proofs.SaturatedCartierDVR
end ProofImplementation
