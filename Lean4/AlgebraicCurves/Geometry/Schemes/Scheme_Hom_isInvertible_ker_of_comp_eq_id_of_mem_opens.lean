/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id_of_mem_opens.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.RingTheory.Spectrum.Prime.Topology
import AlgebraicCurves.RelativeDivisors.Cartier
import AlgebraicCurves.Geometry.Schemes.Scheme_Hom_isInvertible_ker_of_comp_eq_id
import AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_of_comap_of_support_subset_range

/-!
# Scheme Hom is Invertible ker of comp eq id of mem opens
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace Scheme_Hom_isInvertible_ker_of_comp_eq_id_of_mem_opens

universe u


open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry


namespace AlgebraicGeometry

export _root_.AlgebraicGeometry (Scheme.Hom.ker_comp_of_isIso IsOpenImmersion.lift
  SmoothOfRelativeDimension Scheme.Opens.range_ι Scheme.Hom Scheme.Hom.support_ker Spec Scheme
  IsOpenImmersion Scheme.IdealSheafData.ker_fst_of_isClosedImmersion IsClosedImmersion IsSeparated
  Scheme.Hom.opensRange_of_isIso Scheme.Opens IsOpenImmersion.lift_fac IsOpenImmersion.isPullback
  Scheme.Opens.opensRange_ι Scheme.IdealSheafData Scheme.IdealSheafData.IsInvertible
  Scheme.Hom.isInvertible_ker_of_comp_eq_id
  Scheme.IdealSheafData.IsInvertible.of_comap_of_support_subset_range)


open _root_.AlgebraicGeometry


namespace Scheme
export _root_.AlgebraicGeometry.Scheme (Hom.ker_comp_of_isIso Opens.range_ι Hom Hom.support_ker
  IdealSheafData.ker_fst_of_isClosedImmersion Hom.opensRange_of_isIso Opens Opens.opensRange_ι
  IdealSheafData IdealSheafData.IsInvertible Hom.isInvertible_ker_of_comp_eq_id
  IdealSheafData.IsInvertible.of_comap_of_support_subset_range)
namespace IdealSheafData
export _root_.AlgebraicGeometry.Scheme.IdealSheafData (map subscheme ker_fst_of_isClosedImmersion
  ideal comap IsInvertible IsInvertible.of_comap_of_support_subset_range)
end Scheme.IdealSheafData

open scoped _root_.AlgebraicGeometry.Scheme in
open scoped _root_.AlgebraicGeometry.Scheme.IdealSheafData in
theorem Scheme.IdealSheafData.ker_eq_comap_of_isPullback' {P X' Y Z : Scheme.{u}} {fst : P ⟶ X'}
  {snd : P ⟶ Y}
    {f : X' ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g) [IsClosedImmersion g] : fst.ker =
      g.ker.comap f := by
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion, ← h.isoPullback_hom_fst,
    Scheme.Hom.ker_comp_of_isIso]

namespace Scheme
export _root_.AlgebraicGeometry.Scheme (Hom.ker_comp_of_isIso Opens.range_ι Hom Hom.support_ker
  IdealSheafData.ker_fst_of_isClosedImmersion Hom.opensRange_of_isIso Opens Opens.opensRange_ι
  IdealSheafData IdealSheafData.IsInvertible Hom.isInvertible_ker_of_comp_eq_id
  IdealSheafData.IsInvertible.of_comap_of_support_subset_range)
namespace Hom
export _root_.AlgebraicGeometry.Scheme.Hom (ker_comp_of_isIso support_ker opensRange_of_isIso
  continuous opensRange ker isClosedEmbedding isInvertible_ker_of_comp_eq_id)
end Scheme.Hom

open scoped _root_.AlgebraicGeometry.Scheme in
open scoped _root_.AlgebraicGeometry.Scheme.Hom in
theorem Scheme.Hom.isInvertible_ker_of_comp_eq_id_of_mem_opens_aux
    {O : Type u} [CommRing O] [IsLocalRing O] {Y : Scheme.{u}} (πY : Y ⟶ Spec (CommRingCat.of O))
      [IsSeparated πY]
    (W : Y.Opens) [SmoothOfRelativeDimension 1 (W.ι ≫ πY)]
    (σ : Spec (CommRingCat.of O) ⟶ Y) (hσ : σ ≫ πY = 𝟙 _) (hW : σ.base (IsLocalRing.closedPoint O)
      ∈ W) :
    σ.ker.IsInvertible := by
  have hrange : Set.range σ.base ⊆ (W : Set Y) := by
    rintro _ ⟨x, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint x).map σ.continuous).mem_open W.2 hW
  let σ' : Spec (CommRingCat.of O) ⟶ W := IsOpenImmersion.lift W.ι σ (by rwa [Scheme.Opens.range_ι])
  have hσ' : σ' ≫ W.ι = σ := IsOpenImmersion.lift_fac _ _ _
  have hsec : σ' ≫ (W.ι ≫ πY) = 𝟙 _ := by rw [← Category.assoc, hσ', hσ]
  have h1 : σ'.ker.IsInvertible := Scheme.Hom.isInvertible_ker_of_comp_eq_id σ' hsec
  have : IsClosedImmersion σ := by
    have : IsClosedImmersion (σ ≫ πY) := by rw [hσ]; infer_instance
    exact .of_comp σ πY
  have hpre : σ ⁻¹ᵁ W.ι.opensRange = ⊤ := by
    rw [Scheme.Opens.opensRange_ι]
    exact top_le_iff.mp fun x _ => hrange ⟨x, rfl⟩
  have H : IsPullback σ' (𝟙 _) W.ι σ :=
    IsOpenImmersion.isPullback _ _ _ _
      (by rw [Category.id_comp, hσ']) (by rw [hpre, Scheme.Hom.opensRange_of_isIso])
  have h2 : σ'.ker = σ.ker.comap W.ι := Scheme.IdealSheafData.ker_eq_comap_of_isPullback' H
  apply Scheme.IdealSheafData.IsInvertible.of_comap_of_support_subset_range W.ι σ.ker
  · rw [Scheme.Hom.support_ker, σ.isClosedEmbedding.isClosed_range.closure_eq, Scheme.Opens.range_ι]
    exact hrange
  · rw [← h2]; exact h1

end AlgebraicGeometry

theorem _root_.AlgebraicGeometry.Scheme.Hom.isInvertible_ker_of_comp_eq_id_of_mem_opens
    {O : Type u} [CommRing O] [IsLocalRing O] {Y : Scheme.{u}} (πY : Y ⟶ Spec (CommRingCat.of O))
      [IsSeparated πY]
    (W : Y.Opens) [SmoothOfRelativeDimension 1 (W.ι ≫ πY)]
    (σ : Spec (CommRingCat.of O) ⟶ Y) (hσ : σ ≫ πY = 𝟙 _) (hW : σ.base (IsLocalRing.closedPoint O)
      ∈ W) :
    σ.ker.IsInvertible :=
  AlgebraicGeometry.Scheme.Hom.isInvertible_ker_of_comp_eq_id_of_mem_opens_aux πY W σ hσ hW
end AlgebraicCurves.Geometry.Schemes.Proofs.Scheme_Hom_isInvertible_ker_of_comp_eq_id_of_mem_opens
end ProofImplementation
