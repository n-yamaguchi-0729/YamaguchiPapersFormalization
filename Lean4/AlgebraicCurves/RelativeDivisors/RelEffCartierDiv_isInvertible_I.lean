/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import AlgebraicCurves.RelativeDivisors.RelEffCartierDivOfPoint
import AlgebraicCurves.RelativeDivisors.Cartier
import AlgebraicCurves.Geometry.Schemes.Scheme_Hom_isInvertible_ker_of_comp_eq_id
import AlgebraicCurves.RelativeDivisors.RelEffCartierDiv_exists_I_eq_ker_graphOver_mul
import AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_isInvertible_of_isInvertible_comap
import AlgebraicCurves.RelativeDivisors.RelEffCartierDiv

/-!
# Invertibility of relative divisor ideals

Shows local invertibility of the defining ideal of a relative effective Cartier divisor.
-/

section ProofImplementation

namespace AlgebraicCurves.RelativeDivisors.Proofs.RelEffCartierDiv_isInvertible_I

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace RelEffCartierDiv
open _root_.AlgebraicGeometry.RelEffCartierDiv
namespace CartierInduction
open _root_.AlgebraicGeometry.RelEffCartierDiv
open _root_.AlgebraicGeometry

variable {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} [IsSeparated f] [SmoothOfRelativeDimension 1 f]

omit [IsSeparated f] [SmoothOfRelativeDimension 1 f] in
theorem I_eq_top_of_degree_zero {T : Scheme.{u}} {g : T ⟶ S} (D : RelEffCartierDiv f 0 g) :
    D.I = ⊤ := by
  have := D.isFinite
  have := D.flat
  have hempty : IsEmpty ↥D.I.subscheme := by
    by_contra h
    rw [not_isEmpty_iff] at h
    obtain ⟨x⟩ := h
    have h1 := Scheme.Hom.one_le_finrank_map (D.I.subschemeι ≫ pullback.snd f g) x
    rw [D.finrank_eq] at h1
    exact Nat.not_succ_le_zero 0 h1
  rw [← D.I.ker_subschemeι]
  exact Scheme.ker_eq_top_of_isEmpty _

theorem step (r : ℕ)
    (ih : ∀ {T : Scheme.{u}} {g : T ⟶ S} (E : RelEffCartierDiv f r g), E.I.IsInvertible)
    {T : Scheme.{u}} {g : T ⟶ S} (D : RelEffCartierDiv f (r + 1) g) : D.I.IsInvertible := by
  have := D.isFinite
  have := D.flat
  have := D.locallyOfFinitePresentation
  let π : D.I.subscheme ⟶ T := D.I.subschemeι ≫ pullback.snd f g
  have : Surjective π := by
    refine (Scheme.Hom.one_le_finrank_iff_surjective π).mp fun t => ?_
    change 1 ≤ (D.I.subschemeι ≫ pullback.snd f g).finrank t
    rw [D.finrank_eq t]
    exact Nat.succ_le_succ (Nat.zero_le r)
  let g' : D.I.subscheme ⟶ S := π ≫ g
  have hπ : π ≫ g = g' := rfl
  let D' : RelEffCartierDiv f (r + 1) g' := D.pullbackAlong π hπ
  let a : D.I.subscheme ⟶ 𝒞 := D.I.subschemeι ≫ pullback.fst f g
  have ha : a ≫ f = g' := by
    simp only [a, g', π, Category.assoc, pullback.condition]
  have hgraph : graphOver f a ha ≫ mapOnProdOver f π hπ = D.I.subschemeι := by
    apply pullback.hom_ext
    · rw [Category.assoc, mapOnProdOver_fst, graphOver_fst]
    · rw [Category.assoc, mapOnProdOver_snd, graphOver_snd_assoc]
  have hle : D'.I ≤ (graphOver f a ha).ker := by
    change D.I.comap (mapOnProdOver f π hπ) ≤ _
    have hcomap : D.I.comap (mapOnProdOver f π hπ) =
        (pullback.fst (mapOnProdOver f π hπ) D.I.subschemeι).ker := by
      rw [Scheme.IdealSheafData.ker_fst_of_isClosedImmersion, Scheme.IdealSheafData.ker_subschemeι]
    rw [hcomap]
    have hfac : pullback.lift (graphOver f a ha) (𝟙 _) (by rw [hgraph, Category.id_comp]) ≫
        pullback.fst (mapOnProdOver f π hπ) D.I.subschemeι = graphOver f a ha :=
      pullback.lift_fst _ _ _
    exact le_of_le_of_eq (Scheme.Hom.le_ker_comp _ _) (congrArg Scheme.Hom.ker hfac)
  obtain ⟨E, hE⟩ := RelEffCartierDiv.exists_I_eq_ker_graphOver_mul D' a ha hle
  have hgr : (graphOver f a ha).ker.IsInvertible := by
    have : MorphismProperty.IsStableUnderBaseChange
        (C := Scheme.{u}) (fun {_ _} h => SmoothOfRelativeDimension 1 h) :=
      smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
    have : SmoothOfRelativeDimension 1 (pullback.snd f g') :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (P := fun {_ _ : Scheme.{u}} h => SmoothOfRelativeDimension 1 h)
        (IsPullback.of_hasPullback f g') inferInstance
    exact Scheme.Hom.isInvertible_ker_of_comp_eq_id (graphOver f a ha) (graphOver_snd f a ha)
  have hD' : (D.I.comap (mapOnProdOver f π hπ)).IsInvertible := by
    change D'.I.IsInvertible
    rw [hE]
    exact hgr.mul (ih E)
  have hbc := (isPullback_mapOnProdOver f π hπ).flip
  have : IsFinite (mapOnProdOver f π hπ) := MorphismProperty.of_isPullback hbc inferInstance
  have : Flat (mapOnProdOver f π hπ) := MorphismProperty.of_isPullback hbc inferInstance
  have : Surjective (mapOnProdOver f π hπ) := MorphismProperty.of_isPullback hbc inferInstance
  exact Scheme.IdealSheafData.isInvertible_of_isInvertible_comap (mapOnProdOver f π hπ) D.I hD'

theorem isInvertible : ∀ (r : ℕ) {T : Scheme.{u}} {g : T ⟶ S} (D : RelEffCartierDiv f r g),
    D.I.IsInvertible
  | 0, _, _, D => by
    rw [I_eq_top_of_degree_zero D]
    exact Scheme.IdealSheafData.isInvertible_top
  | r + 1, _, _, D => step r (fun E => isInvertible r E) D

end AlgebraicGeometry.RelEffCartierDiv.CartierInduction

theorem _root_.AlgebraicGeometry.RelEffCartierDiv.isInvertible_I {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S}
  [IsSeparated f] [SmoothOfRelativeDimension 1 f]
    {r : ℕ} {T : Scheme.{u}} {g : T ⟶ S} (D : RelEffCartierDiv f r g) : D.I.IsInvertible :=
  AlgebraicGeometry.RelEffCartierDiv.CartierInduction.isInvertible r D
end AlgebraicCurves.RelativeDivisors.Proofs.RelEffCartierDiv_isInvertible_I
end ProofImplementation

attribute [-instance]
  AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one
  AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd
  AlgebraicGeometry.isClosedImmersion_graphOver
attribute [-simp] AlgebraicGeometry.graphOver_fst_assoc
  AlgebraicGeometry.RelEffCartierDiv.toPoint_comp
  AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst
  AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd
  AlgebraicGeometry.graphOver_snd_assoc
