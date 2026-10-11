/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_of_isProper_of_support_finite.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import AlgebraicCurves.RelativeDivisors.RelEffCartierDiv

/-!
# Rel Eff Cartier Div exists I eq of is Proper of support finite
-/

section ProofImplementation

namespace AlgebraicCurves.RelativeDivisors.Proofs
namespace RelEffCartierDiv_exists_I_eq_of_isProper_of_support_finite

universe u


open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.TopologicalSpace


theorem _root_.AlgebraicGeometry.RelEffCartierDiv.exists_I_eq_of_isProper_of_support_finite
    {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} [IsProper f]
    {k : Type u} [Field k] (x : Spec (CommRingCat.of k) ⟶ S)
    (I : (pullback f x).IdealSheafData) (hfin : (I.support : Set ↥(pullback f x)).Finite) :
    ∃ (r : ℕ) (D : RelEffCartierDiv f r x), D.I = I := by
  classical
  let C : Scheme.{u} := pullback f x
  let c : C ⟶ Spec (CommRingCat.of k) := pullback.snd f x
  have : IsProper c := inferInstance
  let g : I.subscheme ⟶ Spec (CommRingCat.of k) := I.subschemeι ≫ c
  have : Finite ↥(I.subscheme) := by
    have : Finite (I.support : Set C) := hfin.to_subtype
    refine Finite.of_injective (fun z => (⟨I.subschemeι.base z, ?_⟩ : (I.support : Set C))) ?_
    · rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨z, rfl⟩
    · intro a b hab
      exact I.subschemeι.isClosedEmbedding.injective (congrArg Subtype.val hab)
  have : LocallyQuasiFinite g :=
    LocallyQuasiFinite.of_finite_preimage_singleton g fun y => Set.toFinite _
  have : IsProper g := inferInstance
  have hgfin : IsFinite g := IsFinite.of_isProper_of_locallyQuasiFinite g
  have : Flat g := inferInstance
  have hlofp : LocallyOfFinitePresentation g := by
    have : IsAffine I.subscheme := isAffine_of_isAffineHom g
    rw [HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation)]
    have hft : g.appTop.hom.Finite := g.finite_appTop
    let := g.appTop.hom.toAlgebra
    have : Module.Finite Γ(Spec (CommRingCat.of k), ⊤) Γ(I.subscheme, ⊤) := hft
    have : IsNoetherianRing Γ(Spec (CommRingCat.of k), ⊤) :=
      isNoetherianRing_of_ringEquiv k (Scheme.ΓSpecIso (CommRingCat.of
        k)).symm.commRingCatIsoToRingEquiv
    exact Algebra.FinitePresentation.of_finiteType.mp inferInstance
  obtain ⟨t₀⟩ : Nonempty ↥(Spec (CommRingCat.of k)) := inferInstance
  refine ⟨g.finrank t₀, ⟨I, hgfin, inferInstance, hlofp, fun t => ?_⟩, rfl⟩
  rw [Subsingleton.elim t t₀]
end RelEffCartierDiv_exists_I_eq_of_isProper_of_support_finite
end AlgebraicCurves.RelativeDivisors.Proofs
end ProofImplementation
