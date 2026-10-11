/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_ker_lift_and_supportedIn_of_finite_etale.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.LinearAlgebra.Dimension.Constructions
import AlgebraicCurves.Geometry.Picard.Functor
import AlgebraicCurves.RelativeDivisors.RelEffCartierDiv
import AlgebraicCurves.RelativeDivisors.RelEffCartierDivSupportedIn
import AlgebraicCurves.RelativeDivisors.RelEffCartierDivSum
import AlgebraicCurves.Geometry.Sheaves.RelativeSectionTwist
import AlgebraicCurves.Geometry.Picard.ChartSections
import AlgebraicCurves.Geometry.Sheaves.IdealSheafModule
import AlgebraicCurves.Geometry.Curves.SmoothProperCurveBase
import SchemeTheory.Modules.Monoidal

/-!
# Rel Eff Cartier Div exists I eq ker lift and supported In of finite etale
-/

section ProofImplementation

namespace AlgebraicCurves.RelativeDivisors.Proofs
namespace RelEffCartierDiv_exists_I_eq_ker_lift_and_supportedIn_of_finite_etale

universe u


open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open _root_.NeronModelInfra
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry.SmoothProperCurve
open _root_.TensorProduct


theorem
  _root_.AlgebraicGeometry.RelEffCartierDiv.exists_I_eq_ker_lift_and_supportedIn_of_finite_etale
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated c]
    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    (A : Type u) [CommRing A] [Algebra R A] [Module.Finite R A] [Module.FaithfullyFlat R A]
    (B : Type u) [CommRing B] [Algebra R B] [Module.Finite R B] [Algebra.Etale R B]
    (d : ℕ) (φ : TensorProduct R A B ≃ₐ[A] (Fin d → A))
    (z : Spec (CommRingCat.of B) ⟶ C) [IsClosedImmersion z]
    (hz : z ≫ c = Spec.map (CommRingCat.ofHom (algebraMap R B)))
    (hzU : Set.range z.base ⊆ (U : Set C)) :
    ∃ Z : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of R))),
      Z.I = (pullback.lift z (Spec.map (CommRingCat.ofHom (algebraMap R B)))
        (by rw [Category.comp_id]; exact hz)).ker ∧ Z.SupportedIn U := by
  classical
  set zl : Spec (CommRingCat.of B) ⟶ pullback c (𝟙 (Spec (CommRingCat.of R))) :=
    pullback.lift z (Spec.map (CommRingCat.ofHom (algebraMap R B)))
      (by rw [Category.comp_id]; exact hz) with hzl
  have hzl_fst : zl ≫ pullback.fst c (𝟙 _) = z := pullback.lift_fst _ _ _
  have hzl_snd : zl ≫ pullback.snd c (𝟙 _) = Spec.map (CommRingCat.ofHom (algebraMap R B)) :=
    pullback.lift_snd _ _ _
  have : IsClosedImmersion (zl ≫ pullback.fst c (𝟙 _)) := by rw [hzl_fst]; infer_instance
  have hzlc : IsClosedImmersion zl := IsClosedImmersion.of_comp zl (pullback.fst c (𝟙 _))
  have hstr : zl.ker.subschemeι ≫ pullback.snd c (𝟙 _) =
      inv zl.toImage ≫ Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
    rw [← hzl_snd, ← Category.assoc]
    congr 1
    rw [IsIso.eq_inv_comp, Scheme.Hom.toImage_imageι]
  have : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R B))) :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  have : Flat (Spec.map (CommRingCat.ofHom (algebraMap R B))) :=
    Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  have : LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap R B))) :=
    (LocallyOfFinitePresentation.SpecMap_iff _).mpr (RingHom.finitePresentation_algebraMap.mpr
      inferInstance)
  refine ⟨⟨zl.ker, ?_, ?_, ?_, ?_⟩, rfl, ?_⟩
  · rw [hstr]; infer_instance
  · rw [hstr]; infer_instance
  · rw [hstr]; infer_instance
  · intro t
    rw [hstr, Scheme.Hom.finrank_comp_left_of_isIso]
    erw [Scheme.Hom.finrank_SpecMap_algebraMap R B]
    obtain ⟨q, hq⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := R) (B := A) t
    have : Nontrivial A := q.nontrivial
    rw [← hq, ← Module.rankAtStalk_baseChange, Module.rankAtStalk_eq_of_equiv φ.toLinearEquiv,
      Module.rankAtStalk_eq_finrank_of_free, Module.finrank_fin_fun]
    simp
  · change (zl.ker.support : Set ↥(pullback c (𝟙 (Spec (CommRingCat.of R))))) ⊆ _
    rw [Scheme.Hom.support_ker, zl.isClosedEmbedding.isClosed_range.closure_eq]
    rintro _ ⟨b, rfl⟩
    change (pullback.fst c (𝟙 _)).base (zl.base b) ∈ (U : Set C)
    rw [← Scheme.Hom.comp_apply, hzl_fst]
    exact hzU ⟨b, rfl⟩
end RelEffCartierDiv_exists_I_eq_ker_lift_and_supportedIn_of_finite_etale
end AlgebraicCurves.RelativeDivisors.Proofs
end ProofImplementation
