/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_of_flat_of_comap_mapOnProdOver_eq_of_isDiscreteValuationRing.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Topology.LocallyConstant.Basic
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv
import Nyll.AlgebraicCurves.Geometry.Schemes.LocallyQuasiFinite_of_flat_of_locallyQuasiFinite_genericFiber
import Mathlib.Util.WithWeakNamespace

/-!
# Extending a relative effective divisor over a discrete valuation ring
-/


section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.ExtendCartierDVR

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

with_weak_namespace _root_.AlgebraicGeometry.RelEffCartierDiv
theorem exists_I_eq_of_flat_of_comap_mapOnProdOver_eq_of_isDiscreteValuationRing
    {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} [IsProper f]
    {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (g : Spec (CommRingCat.of O) ⟶ S)
    (T' : Type u) [Field T'] [Algebra O T'] [IsFractionRing O T']
    {gT : Spec (CommRingCat.of T') ⟶ S}
    (hψ : Spec.map (CommRingCat.ofHom (algebraMap O T')) ≫ g = gT)
    {r : ℕ} (E : RelEffCartierDiv f r gT)
    (J : (pullback f g).IdealSheafData) [Flat (J.subschemeι ≫ pullback.snd f g)]
    (hJ : J.comap (mapOnProdOver f (Spec.map (CommRingCat.ofHom (algebraMap O T'))) hψ) = E.I) :
    ∃ Ebar : RelEffCartierDiv f r g, Ebar.I = J ∧
      Ebar.pullbackAlong (Spec.map (CommRingCat.ofHom (algebraMap O T'))) hψ = E := by
  obtain ⟨I, hfinE, hflatE, hlfpE, hrkE⟩ := E
  dsimp only at hJ
  subst hJ
  set ψ : Spec (CommRingCat.of T') ⟶ Spec (CommRingCat.of O) :=
    Spec.map (CommRingCat.ofHom (algebraMap O T')) with hψdef
  set h := J.subschemeι ≫ pullback.snd f g with hh
  have : IsNoetherianRing O := inferInstance
  have : IsProper h := inferInstance
  have : LocallyOfFiniteType h := inferInstance
  have : LocallyOfFinitePresentation h := inferInstance
  have sq := isPullback_comap_snd_over (f := f) J ψ hψ
  have := hfinE
  have := hflatE
  have : LocallyQuasiFinite (pullback.snd h ψ) := by
    rw [← sq.isoPullback_inv_snd]
    infer_instance
  have : LocallyQuasiFinite h :=
    AlgebraicGeometry.LocallyQuasiFinite.of_flat_of_locallyQuasiFinite_genericFiber
      (R := O) (K := T') h
  have : IsFinite h := IsFinite.of_isProper_of_locallyQuasiFinite h
  have hrank : ∀ t : Spec (CommRingCat.of O), h.finrank t = r := by
    have hlc : IsLocallyConstant h.finrank := h.isLocallyConstant_finrank
    have : PreconnectedSpace (Spec (CommRingCat.of O)) :=
      inferInstanceAs (PreconnectedSpace (PrimeSpectrum O))
    have hη : ∀ s : Spec (CommRingCat.of T'), h.finrank (ψ s) = r := by
      intro s
      rw [← Scheme.Hom.finrank_of_isPullback _ _ _ _ sq s]
      exact hrkE s
    obtain ⟨s⟩ : Nonempty (Spec (CommRingCat.of T')) := inferInstance
    intro t
    rw [hlc.apply_eq_of_preconnectedSpace t (ψ s)]
    exact hη s
  refine ⟨⟨J, ‹IsFinite h›, ‹Flat h›, ‹LocallyOfFinitePresentation h›, hrank⟩, rfl, ?_⟩
  exact RelEffCartierDiv.ext rfl
end JacobianVarieties.Picard.Proofs.ExtendCartierDVR
end ProofImplementation
