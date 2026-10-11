/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_exists_finiteBySections_tensorPow_of_forall_geometricFibre.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Geometry.Picard.Functor
import SchemeTheory.Modules.Monoidal
import AlgebraicCurves.Geometry.Sheaves.ModulesTensorPow
import SchemeTheory.Modules.ProjectivePresentation
import SchemeTheory.Cohomology.Cech.OrderedAffineCoverCech
import AlgebraicCurves.Cohomology.Sheaves.OModulePresheafOfModules
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_nonempty_pullback_tensorPow_iso
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_FiniteBySections_of_iso
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_tensorPow
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_exists_away_finiteBySections_tensorPow_of_forall_geometricFibre
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_nonempty_tensorPow_mul_iso
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_FiniteBySections_tensorPow
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_FiniteBySections_of_forall_mem_finset_away

/-!
# Finite presentation by sections of tensor powers from geometric fibres
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_exists_finiteBySections_tensorPow_of_forall_geometricFibre
open PresheafOfModules.PullbackMonoidal in
attribute [-instance]
  AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback_monoidal
  AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization'
  AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal
  AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.sheafifyPullback_lifting
  PresheafOfModules.PullbackMonoidal.pullback_monoidal
  PresheafOfModules.PullbackMonoidal.isIso_δ
  PresheafOfModules.pushforward_laxMonoidal
  PresheafOfModules.PullbackMonoidal.isIso_η
  PresheafOfModules.free_monoidal
  PresheafOfModules.restrictScalars_laxMonoidal
  PresheafOfModules.PullbackMonoidal.isIso_δ_gS
  PresheafOfModules.pullback_oplaxMonoidal
  instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb
  PresheafOfModules.pullback_monoidal'
attribute [-simp] PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app
  TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply
  TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply
  AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right
  AlgebraicGeometry.Scheme.Modules.map_unitSection
  AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply
  AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

attribute [local instance] MvPolynomial.gradedAlgebra

namespace W2FINSketch

/-- The isomorphism on tensor powers induced by an isomorphism of modules. -/
noncomputable def tensorPowIso {X : Scheme.{u}} {L L' : X.Modules} (e : L ≅ L') :
    (b : ℕ) → (L.tensorPow b ≅ L'.tensorPow b)
  | 0 => Iso.refl _
  | b + 1 => tensorPowIso e b ⊗ᵢ e

end W2FINSketch

open W2FINSketch in
theorem
  _root_.AlgebraicGeometry.Scheme.Modules.exists_finiteBySections_tensorPow_of_forall_geometricFibre
    (R : Type u) [CommRing R] [IsNoetherianRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    [IsProper f] [Flat f] (L : X.Modules) (hL : Scheme.Modules.IsInvertible L)
    (hfin : ∀ (𝒰 : X.OrderedAffineCover) (n : ℕ), (OModulePresheaf.ofModules f (L.tensorPow
      n)).CechFinite 𝒰)
    (hfib : ∀ (K : Type u) [Field K] [IsAlgClosed K] [Algebra R K], ∃ n : ℕ,
      Scheme.Modules.FiniteBySections
          ((Scheme.Modules.pullback
              (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))))).obj
                (L.tensorPow n))
          (Limits.pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ∧
      ∀ 𝒲 : (Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K)))).OrderedAffineCover,
        Subsingleton
          ((OModulePresheaf.ofModules (Limits.pullback.snd f (Spec.map (CommRingCat.ofHom
            (algebraMap R K))))
              ((Scheme.Modules.pullback
                  (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))))).obj
                (L.tensorPow n))).HSucc 𝒲 0)) :
    ∃ n : ℕ, Scheme.Modules.FiniteBySections (L.tensorPow n) f := by
  classical
  have loc := fun 𝔭 : PrimeSpectrum R =>
    Scheme.Modules.exists_away_finiteBySections_tensorPow_of_forall_geometricFibre R f L hL hfin
      hfib 𝔭
  choose g hg n hn hFBS using loc
  have hcover : (Set.univ : Set (PrimeSpectrum R)) ⊆
      ⋃ 𝔭 : PrimeSpectrum R, ((PrimeSpectrum.basicOpen (g 𝔭) : TopologicalSpace.Opens
        (PrimeSpectrum R)) :
        Set (PrimeSpectrum R)) :=
    fun 𝔭 _ => Set.mem_iUnion.2 ⟨𝔭, hg 𝔭⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun 𝔭 : PrimeSpectrum R => ((PrimeSpectrum.basicOpen (g 𝔭) : TopologicalSpace.Opens
      (PrimeSpectrum R)) :
      Set (PrimeSpectrum R)))
    (fun 𝔭 => (PrimeSpectrum.basicOpen (g 𝔭)).isOpen) hcover
  set s : Finset R := t.image g with hs_def
  have hs : Ideal.span (s : Set R) = ⊤ := by
    rw [← PrimeSpectrum.zeroLocus_empty_iff_eq_top, PrimeSpectrum.zeroLocus_span,
      Set.eq_empty_iff_forall_notMem]
    intro 𝔮 h𝔮
    obtain ⟨𝔭, h𝔭t, hmem⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ 𝔮))
    have hgs : g 𝔭 ∈ (s : Set R) := by
      rw [hs_def, Finset.coe_image]
      exact ⟨𝔭, h𝔭t, rfl⟩
    exact hmem (h𝔮 hgs)
  have hNpos : 0 < ∏ 𝔭 ∈ t, n 𝔭 := Finset.prod_pos fun 𝔭 _ => hn 𝔭
  refine ⟨∏ 𝔭 ∈ t, n 𝔭, Scheme.Modules.FiniteBySections.of_forall_mem_finset_away f (L.tensorPow _)
    (hL.tensorPow _) s hs ?_⟩
  intro r hr
  obtain ⟨𝔭, h𝔭t, rfl⟩ := Finset.mem_image.1 hr
  obtain ⟨b, hb⟩ := Finset.dvd_prod_of_mem n h𝔭t
  rw [hb] at hNpos ⊢
  have hbpos : 0 < b := Nat.pos_of_ne_zero (by
    intro hb0
    rw [hb0, mul_zero] at hNpos
    exact Nat.lt_irrefl 0 hNpos)
  set ι := Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (g 𝔭))))
  set p := Limits.pullback.fst f ι
  set f' := Limits.pullback.snd f ι
  have hV := Scheme.Modules.FiniteBySections.tensorPow (f := f') (hFBS 𝔭) hbpos
  refine Scheme.Modules.FiniteBySections.of_iso ?_ hV
  exact tensorPowIso (Scheme.Modules.nonempty_pullback_tensorPow_iso p L (n 𝔭)).some b ≪≫
    (Scheme.Modules.nonempty_tensorPow_mul_iso ((Scheme.Modules.pullback p).obj L) (n 𝔭)
      b).some.symm ≪≫
    (Scheme.Modules.nonempty_pullback_tensorPow_iso p L (n 𝔭 * b)).some.symm
end Scheme_Modules_exists_finiteBySections_tensorPow_of_forall_geometricFibre
end AlgebraicCurves.Geometry.Sheaves.Proofs
end ProofImplementation
