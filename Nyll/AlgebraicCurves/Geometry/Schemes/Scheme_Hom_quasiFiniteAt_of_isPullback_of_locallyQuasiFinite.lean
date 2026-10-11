/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Hom_quasiFiniteAt_of_isPullback_of_locallyQuasiFinite.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Schemes.LocallyQuasiFinite_descendsAlong_surjective_inf_flat_inf_quasiCompact

/-!
# Scheme Hom quasi Finite At of is Pullback of locally Quasi Finite
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace Scheme_Hom_quasiFiniteAt_of_isPullback_of_locallyQuasiFinite

universe u

open CategoryTheory hiding IsDiscrete
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MorphismProperty
open _root_.AlgebraicGeometry

namespace QFPtDesc

theorem sfq {X Y : Scheme.{u}} (q : X ⟶ Y) (x : X) :
    (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) (Spec.map
      (q.residueFieldMap x)) := by
  refine ⟨⟨⟨fun z => ⟨default, Subsingleton.elim _ _⟩⟩, ?_⟩, inferInstance⟩
  rw [HasRingHomProperty.Spec_iff (P := @Flat)]
  let := (q.residueFieldMap x).hom.toAlgebra
  change Module.Flat (Y.residueField (q x)) (X.residueField x)
  infer_instance

theorem locallyQuasiFinite_fiberToSpecResidueField
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'} {p : X' ⟶ X} {q : Y' ⟶ Y}
    (sq : IsPullback p f' f q) [LocallyQuasiFinite f'] (y' : Y') :
    LocallyQuasiFinite (f.fiberToSpecResidueField (q y')) := by
  have :=
    AlgebraicGeometry.LocallyQuasiFinite.descendsAlong_surjective_inf_flat_inf_quasiCompact.{u}
  have sq' := isPullback_fiberToSpecResidueField_of_isPullback sq y'
  have hf' : LocallyQuasiFinite (f'.fiberToSpecResidueField y') :=
    MorphismProperty.of_isPullback (P := @LocallyQuasiFinite)
      (IsPullback.of_hasPullback f' (Y'.fromSpecResidueField y')) inferInstance
  exact MorphismProperty.of_isPullback_of_descendsAlong (P := @LocallyQuasiFinite)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) sq'.flip (sfq q y') hf'

theorem main
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'} {p : X' ⟶ X} {q : Y' ⟶ Y}
    (sq : IsPullback p f' f q) [LocallyOfFiniteType f] [LocallyQuasiFinite f'] (y' : Y') (x : X)
    (hx : f x = q y') : f.QuasiFiniteAt x := by
  rw [Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber]
  have hlqf : LocallyQuasiFinite (f.fiberToSpecResidueField (f x)) := by
    rw [hx]; exact locallyQuasiFinite_fiberToSpecResidueField sq y'
  have hdisc : _root_.IsDiscrete ((f.fiberToSpecResidueField (f x)) ⁻¹'
      {(f.fiberToSpecResidueField (f x)) (f.asFiber x)}) :=
    (f.fiberToSpecResidueField (f x)).isDiscrete_preimage_singleton _
  have huniv : ((f.fiberToSpecResidueField (f x)) ⁻¹'
      {(f.fiberToSpecResidueField (f x)) (f.asFiber x)}) = Set.univ := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    exact Subsingleton.elim _ _
  rw [huniv, isDiscrete_univ_iff] at hdisc
  exact isOpen_discrete _

end QFPtDesc

theorem _root_.AlgebraicGeometry.Scheme.Hom.quasiFiniteAt_of_isPullback_of_locallyQuasiFinite
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'} {p : X' ⟶ X} {q : Y' ⟶ Y}
    (sq : IsPullback p f' f q) [LocallyOfFiniteType f] [LocallyQuasiFinite f'] (y' : Y') (x : X)
    (hx : f x = q y') : f.QuasiFiniteAt x :=
  QFPtDesc.main sq y' x hx
end Scheme_Hom_quasiFiniteAt_of_isPullback_of_locallyQuasiFinite
end AlgebraicCurves.Geometry.Schemes.Proofs
end ProofImplementation
