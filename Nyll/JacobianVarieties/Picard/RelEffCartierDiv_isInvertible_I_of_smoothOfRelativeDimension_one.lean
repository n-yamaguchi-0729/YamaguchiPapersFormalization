/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I_of_smoothOfRelativeDimension_one.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv
import Nyll.AlgebraicCurves.RelativeDivisors.Cartier
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv_isInvertible_I
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_of_forall_comap_openCover

/-!
# Invertibility of a relative effective divisor on a smooth curve
-/


section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.SmoothCurveCartier
attribute [-instance]
  AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one
  AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd
  AlgebraicGeometry.isClosedImmersion_graphOver
attribute [-simp]
  AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp
  AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst
  AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd
  AlgebraicGeometry.graphOver_snd_assoc

universe u

namespace GenCartier

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem main
    {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} {K : Type u} [Field K] {gK : Spec (CommRingCat.of K) ⟶ S}
    [IsSeparated (pullback.snd f gK)] [SmoothOfRelativeDimension 1 (pullback.snd f gK)]
    {r : ℕ} (E : RelEffCartierDiv f r gK) :
    E.I.IsInvertible := by
  let e : pullback (pullback.snd f gK) (𝟙 (Spec (CommRingCat.of K))) ⟶ pullback f gK :=
    pullback.fst (pullback.snd f gK) (𝟙 _)
  have sq1 : IsPullback ((E.I.comapIso e).hom ≫ pullback.snd e E.I.subschemeι)
      (E.I.comap e).subschemeι
      E.I.subschemeι e := by
    refine (IsPullback.of_iso_pullback ⟨?_⟩ (E.I.comapIso e) ?_ ?_).flip
    · simp only [Scheme.IdealSheafData.comapIso_hom_snd,
        Scheme.IdealSheafData.subschemeMap_subschemeι]
    · exact E.I.comapIso_hom_fst e
    · rfl
  have sq2 : IsPullback e (pullback.snd (pullback.snd f gK) (𝟙 _)) (pullback.snd f gK) (𝟙 _) :=
    IsPullback.of_hasPullback (pullback.snd f gK) (𝟙 _)
  have sq := sq1.paste_vert sq2
  have := E.isFinite
  have := E.flat
  have := E.locallyOfFinitePresentation
  let D' : RelEffCartierDiv (pullback.snd f gK) r (𝟙 (Spec (CommRingCat.of K))) :=
    { I := E.I.comap e
      isFinite := MorphismProperty.of_isPullback sq ‹_›
      flat := MorphismProperty.of_isPullback sq ‹_›
      locallyOfFinitePresentation := MorphismProperty.of_isPullback sq ‹_›
      finrank_eq := fun t => by
        rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ sq t]
        exact E.finrank_eq _ }
  have hD' : (E.I.comap e).IsInvertible := RelEffCartierDiv.isInvertible_I D'
  refine Scheme.IdealSheafData.IsInvertible.of_forall_comap_openCover
    (Scheme.coverOfIsIso.{u, u} e) E.I ?_
  intro i
  exact hD'

end GenCartier

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry in
theorem _root_.AlgebraicGeometry.RelEffCartierDiv.isInvertible_I_of_smoothOfRelativeDimension_one
    {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} {K : Type u} [Field K] {gK : Spec (CommRingCat.of K) ⟶ S}
    [IsSeparated (pullback.snd f gK)] [SmoothOfRelativeDimension 1 (pullback.snd f gK)]
    {r : ℕ} (E : RelEffCartierDiv f r gK) :
    E.I.IsInvertible :=
  GenCartier.main E
end JacobianVarieties.Picard.Proofs.SmoothCurveCartier
end ProofImplementation
