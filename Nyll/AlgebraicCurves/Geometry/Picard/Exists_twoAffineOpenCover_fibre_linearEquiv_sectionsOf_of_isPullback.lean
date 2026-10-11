/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_exists_twoAffineOpenCover_fibre_linearEquiv_sectionsOf_of_isPullback.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Util.WithWeakNamespace
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroCut
import Nyll.AlgebraicCurves.Geometry.Sheaves.RelativeSectionTwist
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveFiniteMapData
import Nyll.SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
import Nyll.AlgebraicCurves.Cohomology.Cech.TwoChartCechSectionsOf
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv
import Nyll.AlgebraicCurves.Geometry.Sheaves.IdealSheafModule
import Nyll.SchemeTheory.Modules.Monoidal
import Nyll.AlgebraicCurves.Geometry.Schemes.Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso

/-!
# Transporting two-chart fibre cohomology along a Cartesian square

A Cartesian identification of a fibre transports a two-affine-open cover and induces
linear equivalences on the zeroth and first cohomology of the corresponding modules.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Picard.Proofs
namespace Exists_twoAffineOpenCover_fibre_linearEquiv_sectionsOf_of_isPullback

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open _root_.NeronModelInfra
open _root_.AlgebraicGeometry.SmoothProperCurve

noncomputable section

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace RelPicard
open _root_.AlgebraicGeometry.RelPicard
namespace TransportGen
open _root_.AlgebraicGeometry.RelPicard
open _root_.AlgebraicGeometry

variable {R : Type u} [CommRing R] {C T : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
  (t : T ⟶ Spec (CommRingCat.of R)) (M : (pullback c t).Modules)
  {k : Type u} [Field k] (s : Spec (CommRingCat.of k) ⟶ T)
  {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of k)) (g' : Y ⟶ pullback c t)
  (hcart : IsPullback g' y (pullback.snd c t) s)

/-- The pullback identification of the geometric fibre with the given Cartesian scheme. -/
def φ : pullback (pullback.snd c t) s ≅ Y := hcart.isoPullback.symm

theorem φ_hom_y : (φ c t s y g' hcart).hom ≫ y = fibreAt c t s := by
  rw [φ, Iso.symm_hom, IsPullback.isoPullback_inv_snd]
  rfl

/-- The module comparison obtained by transport along the Cartesian identification and
    composition of pullback functors. -/
def modIso : fibreModule c t s M ≅ (Scheme.Modules.pullback (φ c t s y g' hcart).hom).obj
    ((Scheme.Modules.pullback g').obj M) :=
  (Scheme.Modules.pullbackCongr (hcart.isoPullback_inv_fst).symm).app M ≪≫
    (Scheme.Modules.pullbackComp (φ c t s y g' hcart).hom g').symm.app M

include hcart in
theorem main (F : Y.Modules) (e : F ≅ (Scheme.Modules.pullback g').obj M) (𝒱 :
    Y.TwoAffineOpenCover) :
    ∃ 𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover,
      Nonempty ((𝒱.sectionsOf y F).H0 ≃ₗ[k] (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s
          M)).H0) ∧
      Nonempty ((𝒱.sectionsOf y F).H1 ≃ₗ[k] (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s
          M)).H1) := by
  obtain ⟨𝒲, -, -, ⟨eH0⟩, ⟨eH1⟩⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
    (fibreAt c t s) y (φ c t s y g' hcart) (φ_hom_y c t s y g' hcart)
    𝒱 F (fibreModule c t s M)
    (modIso c t M s y g' hcart ≪≫ (Scheme.Modules.pullback (φ c t s y g' hcart).hom).mapIso e.symm)
  exact ⟨𝒲, ⟨eH0.symm⟩, ⟨eH1.symm⟩⟩

end AlgebraicGeometry.RelPicard.TransportGen

end

open AlgebraicGeometry.RelPicard in
with_weak_namespace _root_.AlgebraicGeometry.RelPicard
theorem exists_twoAffineOpenCover_fibre_linearEquiv_sectionsOf_of_isPullback
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : (pullback c t).Modules)
    {k : Type u} [Field k] (s : Spec (CommRingCat.of k) ⟶ T)
    {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of k)) (g' : Y ⟶ pullback c t)
    (hcart : IsPullback g' y (pullback.snd c t) s)
    (F : Y.Modules) (e : F ≅ (Scheme.Modules.pullback g').obj M) (𝒱 : Y.TwoAffineOpenCover) :
    ∃ 𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover,
      Nonempty ((𝒱.sectionsOf y F).H0 ≃ₗ[k] (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s
          M)).H0) ∧
      Nonempty ((𝒱.sectionsOf y F).H1 ≃ₗ[k] (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s
          M)).H1) :=
  TransportGen.main c t M s y g' hcart F e 𝒱
end Exists_twoAffineOpenCover_fibre_linearEquiv_sectionsOf_of_isPullback
end AlgebraicCurves.Geometry.Picard.Proofs
end ProofImplementation
