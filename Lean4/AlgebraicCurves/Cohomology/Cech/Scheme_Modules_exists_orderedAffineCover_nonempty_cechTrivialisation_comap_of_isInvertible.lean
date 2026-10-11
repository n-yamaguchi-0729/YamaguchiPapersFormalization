/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_exists_orderedAffineCover_nonempty_cechTrivialisation_comap_of_isInvertible.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Topology.Sheaves.SheafCondition.Sites
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.Topology.Compactness.Compact
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Order.Basic
import SchemeTheory.Cohomology.Cech.OrderedAffineCoverCech
import AlgebraicCurves.Geometry.Schemes.OrderedAffineCoverComap
import AlgebraicCurves.Cohomology.Sheaves.OrderedAffineCoverCochainPullback
import AlgebraicCurves.Geometry.Picard.Functor
import AlgebraicCurves.Geometry.Picard.CechObstruction

/-!
# Scheme Modules exists ordered Affine Cover nonempty cech Trivialisation comap of is
Invertible
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Cech.Proofs.InvertibleAffineTrivialisation

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.IsLocalRing
open _root_.AlgebraicGeometry.SmallExtension
open _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover


universe u

namespace TrivCoverPen

open TopologicalSpace Opposite

/-- Restrict a trivialisation from an open subscheme to a smaller open. -/
noncomputable def restrictTriv {Y : Scheme.{u}} {M : Y.Modules} {V W : Y.Opens} (h : W ≤ V)
    (τ : (Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit ((V :
      Scheme.{u})).ringCatSheaf) :
    (Scheme.Modules.pullback W.ι).obj M ≅ SheafOfModules.unit ((W : Scheme.{u})).ringCatSheaf :=
  ((Scheme.Modules.pullbackCongr (Y.homOfLE_ι h)).app M).symm ≪≫
    ((Scheme.Modules.pullbackComp (Y.homOfLE h) V.ι).app M).symm ≪≫
    (Scheme.Modules.pullback (Y.homOfLE h)).mapIso τ ≪≫
    Scheme.Modules.pullbackUnitIso (Y.homOfLE h)

theorem isZero_of_isEmpty {Y : Scheme.{u}} [IsEmpty Y] (M : SheafOfModules.{u} Y.ringCatSheaf) :
    Limits.IsZero M := by
  rw [Limits.IsZero.iff_id_eq_zero]
  apply (SheafOfModules.toSheaf Y.ringCatSheaf).map_injective
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]
  apply Sheaf.hom_ext
  refine NatTrans.ext (funext fun U => ?_)
  have hU : U.unop = ⊥ := by
    ext y; exact (IsEmpty.false y).elim
  have hT := TopCat.Sheaf.isTerminalOfEqEmpty (X := Y.carrier)
    ((SheafOfModules.toSheaf Y.ringCatSheaf).obj M) hU
  exact hT.hom_ext _ _

theorem nonempty_iso_of_isEmpty {Y : Scheme.{u}} [IsEmpty Y] (M N : Y.Modules) : Nonempty (M ≅
  N) := by
  let e : @Iso (SheafOfModules.{u} Y.ringCatSheaf) _ M N := (isZero_of_isEmpty M).iso
    (isZero_of_isEmpty N)
  exact ⟨⟨e.hom, e.inv, e.hom_inv_id, e.inv_hom_id⟩⟩

end TrivCoverPen

end AlgebraicCurves.Cohomology.Cech.Proofs.InvertibleAffineTrivialisation

section PublicStatement

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.IsLocalRing
open _root_.AlgebraicGeometry.SmallExtension
open _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover
universe u
open _root_.AlgebraicCurves.Cohomology.Cech.Proofs.InvertibleAffineTrivialisation

namespace AlgebraicGeometry.Scheme.Modules

theorem exists_orderedAffineCover_nonempty_cechTrivialisation_comap_of_isInvertible
    {X X₀ : Scheme.{u}} [CompactSpace X] (g : X₀ ⟶ X) [IsClosedImmersion g]
    (𝓛₀ : X₀.Modules) (h𝓛₀ : Scheme.Modules.IsInvertible 𝓛₀) :
    ∃ 𝒰 : X.OrderedAffineCover, Nonempty (Scheme.Modules.CechTrivialisation (𝒰.comap g) 𝓛₀) := by
  classical
  have htriv := h𝓛₀.exists_trivialization
  have key : ∀ x : X, ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback (g ⁻¹ᵁ U).ι).obj 𝓛₀ ≅
        SheafOfModules.unit ((g ⁻¹ᵁ U : Scheme.{u})).ringCatSheaf) := by
    intro x
    by_cases hx : x ∈ Set.range g.base
    · obtain ⟨x₀, rfl⟩ := hx
      obtain ⟨V₀, hxV₀, ⟨τ⟩⟩ := htriv x₀
      obtain ⟨V', hV'open, hV'⟩ := g.isClosedEmbedding.isInducing.isOpen_iff.mp V₀.isOpen
      have hxV' : g.base x₀ ∈ V' := by
        rw [← Set.mem_preimage, hV']; exact hxV₀
      obtain ⟨_, ⟨U, hUaff, rfl⟩, hxU, hUV'⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
        hxV' hV'open
      refine ⟨U, hUaff, hxU, ⟨TrivCoverPen.restrictTriv ?_ τ⟩⟩
      intro y hy
      have hy' : g.base y ∈ V' := hUV' hy
      rw [← Set.mem_preimage, hV'] at hy'
      exact hy'
    · obtain ⟨_, ⟨U, hUaff, rfl⟩, hxU, hUc⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
        (show x ∈ (Set.range g.base)ᶜ from hx) g.isClosedEmbedding.isClosed_range.isOpen_compl
      refine ⟨U, hUaff, hxU, ?_⟩
      have hbot : g ⁻¹ᵁ U = ⊥ := le_bot_iff.mp fun y hy => (hUc hy ⟨y, rfl⟩).elim
      by_cases hne : Nonempty X₀
      · obtain ⟨x₁⟩ := hne
        obtain ⟨V₁, -, ⟨τ₁⟩⟩ := htriv x₁
        exact ⟨TrivCoverPen.restrictTriv (show g ⁻¹ᵁ U ≤ V₁ from hbot ▸ bot_le) τ₁⟩
      · have : IsEmpty ((g ⁻¹ᵁ U : X₀.Opens) : Scheme.{u}) := ⟨fun y => hne ⟨(g ⁻¹ᵁ U).ι.base y⟩⟩
        exact TrivCoverPen.nonempty_iso_of_isEmpty _ _
  choose U hUaff hxU hτ using key
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x : X => (U x : Set X))
    (fun x => (U x).isOpen) (fun x _ => Set.mem_iUnion.mpr ⟨x, hxU x⟩)
  let : LinearOrder (↥t) := LinearOrder.lift' (Fintype.equivFin (↥t)) (Fintype.equivFin
    (↥t)).injective
  refine ⟨{ ι := ↥t
            U := fun w => U w.1
            isAffineOpen := fun w => hUaff w.1
            iSup_eq_top := ?_ }, ⟨fun w => (hτ w.1).some⟩⟩
  refine top_le_iff.mp fun y _ => ?_
  obtain ⟨w, hw, hyw⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ y))
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨w, hw⟩, hyw⟩

end AlgebraicGeometry.Scheme.Modules

end PublicStatement
end ProofImplementation
