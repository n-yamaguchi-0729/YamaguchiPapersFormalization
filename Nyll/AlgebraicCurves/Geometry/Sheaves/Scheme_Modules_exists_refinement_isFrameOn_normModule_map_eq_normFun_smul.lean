/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_exists_refinement_isFrameOn_normModule_map_eq_normFun_smul.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.Norm.Defs
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Ext
import Nyll.SchemeTheory.Modules.TensorSections
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesNormModule
import Nyll.SchemeTheory.Modules.Monoidal
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesLocallyFreeOfRank
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_isLocallyFreeOfRank_pushforward_of_isFinite_of_flat_of_locallyTrivialOver
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsLocallyFreeOfRank_exists_basis
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_exists_isFrameOn_normModule_forall_map_eq_norm_smul_of_isFrameOn_preimage

/-!
# Scheme Modules exists refinement is Frame On norm Module map eq norm Fun smul
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_exists_refinement_isFrameOn_normModule_map_eq_normFun_smul
open _root_.PresheafOfModules.PullbackMonoidal in
attribute [-instance]
  AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback_monoidal
  AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization'
  AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal
  AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.sheafifyPullback_lifting
  pullback_monoidal
  isIso_δ
  PresheafOfModules.pushforward_laxMonoidal
  isIso_η
  PresheafOfModules.free_monoidal
  PresheafOfModules.restrictScalars_laxMonoidal
  isIso_δ_gS
  PresheafOfModules.pullback_oplaxMonoidal
  instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb
  PresheafOfModules.pullback_monoidal'
  SheafOfModules.isIso_ihomModelToIhom
attribute [-simp] PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app
  AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app
  PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom
  SheafOfModules.ihomSectionsEquivFamily_unit
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left
  AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply
  SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply


open _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.Opposite
open _root_.TopologicalSpace


universe u

namespace AlgebraicGeometry

export _root_.AlgebraicGeometry (Surjective Scheme.Modules.pushforward Scheme.Hom IsFinite
  IsIntegral Scheme Flat Scheme.Hom.preimage_mono exists_isAffineOpen_mem_and_subset IsAffineOpen
  Scheme.Modules LocallyOfFinitePresentation Scheme.Modules.map_smul Scheme.Modules.IsFrameOn
  Scheme.Modules.normModule Scheme.Modules.IsLocallyFreeOfRank Scheme.Modules.pullbackUnitIso
  Scheme.Modules.isLocallyFreeOfRank_pushforward_of_isFinite_of_flat_of_locallyTrivialOver
  Scheme.Modules.exists_isFrameOn_normModule_forall_map_eq_norm_smul_of_isFrameOn_preimage)

namespace Scheme

export _root_.AlgebraicGeometry.Scheme (Modules.pushforward Hom Γ Hom.preimage_mono Modules Opens
  Modules.map_smul restrict Modules.IsFrameOn Modules.normModule Modules.IsLocallyFreeOfRank
  Modules.pullbackUnitIso
  Modules.isLocallyFreeOfRank_pushforward_of_isFinite_of_flat_of_locallyTrivialOver
  Modules.exists_isFrameOn_normModule_forall_map_eq_norm_smul_of_isFrameOn_preimage)

namespace Modules

export _root_.AlgebraicGeometry.Scheme.Modules (pushforward presheaf Hom restrict map_smul
  IsFrameOn normModule IsLocallyFreeOfRank pullbackUnitIso
  isLocallyFreeOfRank_pushforward_of_isFinite_of_flat_of_locallyTrivialOver
  exists_isFrameOn_normModule_forall_map_eq_norm_smul_of_isFrameOn_preimage)

namespace NormFLF

open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry


variable {X Y : Scheme.{u}} (π : X ⟶ Y)

/-- The pushforward of the structure module along the finite morphism. -/
noncomputable abbrev E : Y.Modules := (Scheme.Modules.pushforward π).obj (𝟙_ X.Modules)

/-- Restriction of functions between two opens of the base scheme. -/
noncomputable abbrev rY {A B : Y.Opens} (h : B ≤ A) : Γ(Y, A) →+* Γ(Y, B) := (Y.presheaf.map
  (homOfLE h).op).hom

/-- Restriction of functions between the inverse images of two opens of the base scheme. -/
noncomputable abbrev rX {A B : Y.Opens} (h : B ≤ A) : Γ(X, π ⁻¹ᵁ A) →+* Γ(X, π ⁻¹ᵁ B) :=
  (X.presheaf.map (homOfLE (Scheme.Hom.preimage_mono π h)).op).hom

theorem rY_rY {A B C : Y.Opens} (hBA : B ≤ A) (hCB : C ≤ B) (g : Γ(Y, A)) :
    rY hCB (rY hBA g) = rY (hCB.trans hBA) g := by
  change (Y.presheaf.map (homOfLE hBA).op ≫ Y.presheaf.map (homOfLE hCB).op).hom g = _
  rw [← Functor.map_comp]; rfl

theorem rX_rX {A B C : Y.Opens} (hBA : B ≤ A) (hCB : C ≤ B) (g : Γ(X, π ⁻¹ᵁ A)) :
    rX π hCB (rX π hBA g) = rX π (hCB.trans hBA) g := by
  change (X.presheaf.map (homOfLE _).op ≫ X.presheaf.map (homOfLE _).op).hom g = _
  rw [← Functor.map_comp]; rfl

theorem norm_map {A B : Y.Opens} (h : B ≤ A) {d : ℕ}
    (bA : letI := (π.app A).hom.toAlgebra; Module.Basis (Fin d) Γ(Y, A) Γ(X, π ⁻¹ᵁ A))
    (bB : letI := (π.app B).hom.toAlgebra; Module.Basis (Fin d) Γ(Y, B) Γ(X, π ⁻¹ᵁ B))
    (hb : ∀ i, bB i = rX π h (bA i)) (x : Γ(X, π ⁻¹ᵁ A)) :
    letI := (π.app A).hom.toAlgebra; letI := (π.app B).hom.toAlgebra
    rY h (Algebra.norm Γ(Y, A) x) = Algebra.norm Γ(Y, B) (rX π h x) := by
  let algA : Algebra Γ(Y, A) Γ(X, π ⁻¹ᵁ A) := (π.app A).hom.toAlgebra
  let algB : Algebra Γ(Y, B) Γ(X, π ⁻¹ᵁ B) := (π.app B).hom.toAlgebra
  have hsemi : ∀ (c : Γ(Y, A)) (m : Γ(X, π ⁻¹ᵁ A)), rX π h (c • m) = rY h c • rX π h m := by
    intro c m
    change rX π h (π.app A c * m) = π.app B (rY h c) * rX π h m
    rw [map_mul]
    congr 1
    have := CategoryTheory.ConcreteCategory.congr_hom (π.naturality (homOfLE h).op) c
    rw [CategoryTheory.ConcreteCategory.comp_apply, CategoryTheory.ConcreteCategory.comp_apply]
      at this
    exact this.symm
  have hcoord : ∀ (y : Γ(X, π ⁻¹ᵁ A)) (i : Fin d), rY h (bA.repr y i) = bB.repr (rX π h y) i := by
    intro y i
    have hy : rX π h y = ∑ j, rY h (bA.repr y j) • bB j := by
      conv_lhs => rw [← bA.sum_repr y]
      rw [map_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [hsemi, hb]
    rw [hy, bB.repr_sum_self]
  have hmat : (rY h).mapMatrix (Algebra.leftMulMatrix bA x) = Algebra.leftMulMatrix bB (rX π h x)
    := by
    ext i j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul,
      Algebra.leftMulMatrix_eq_repr_mul,
      hcoord, map_mul, ← hb]
  rw [Algebra.norm_eq_matrix_det bA, Algebra.norm_eq_matrix_det bB, RingHom.map_det, hmat]

end AlgebraicGeometry.Scheme.Modules.NormFLF

open AlgebraicGeometry.Scheme.Modules.NormFLF in
theorem
  _root_.AlgebraicGeometry.Scheme.Modules.exists_refinement_isFrameOn_normModule_map_eq_normFun_smul
    {X Y : Scheme.{u}} (π : X ⟶ Y) [IsFinite π] [Flat π] [LocallyOfFinitePresentation π]
      [Surjective π]
    [IsIntegral X] [IsIntegral Y]
    (d : ℕ) (hd : ∀ y : Y, π.finrank y = d)
    (Nf : ∀ W : Y.Opens, Γ(X, π ⁻¹ᵁ W) → Γ(Y, W))
    (h2 : ∀ (W W' : Y.Opens) (h : W' ≤ W) (a : Γ(X, π ⁻¹ᵁ W)),
      Nf W' (X.presheaf.map (homOfLE (Scheme.Hom.preimage_mono π h)).op a) = Y.presheaf.map
        (homOfLE h).op (Nf W a))
    (h3 : ∀ (W : Y.Opens), IsAffineOpen W →
      letI : Algebra Γ(Y, W) Γ(X, π ⁻¹ᵁ W) := (π.app W).hom.toAlgebra
      ∀ [Module.Free Γ(Y, W) Γ(X, π ⁻¹ᵁ W)] [Module.Finite Γ(Y, W) Γ(X, π ⁻¹ᵁ W)],
      ∀ a : Γ(X, π ⁻¹ᵁ W), Nf W a = Algebra.norm Γ(Y, W) a)
    {ι : Type u} (U : ι → Y.Opens) (L : X.Modules) (s : ∀ i, Γ(L, π ⁻¹ᵁ U i))
    (hs : ∀ i, Scheme.Modules.IsFrameOn (s i) (π ⁻¹ᵁ U i))
    (u : ∀ i j, Γ(X, π ⁻¹ᵁ (U i ⊓ U j)))
    (hu : ∀ i j, L.presheaf.map (homOfLE (Scheme.Hom.preimage_mono π inf_le_right)).op (s j) =
      u i j • L.presheaf.map (homOfLE (Scheme.Hom.preimage_mono π inf_le_left)).op (s i)) :
    ∃ (κ : Type u) (T : κ → Y.Opens) (r : κ → ι), (⨆ k, T k) = ⨆ i, U i ∧ (∀ k, T k ≤ U (r k)) ∧
      ∃ Ω : ∀ k, Γ(Scheme.Modules.normModule π d L, T k),
        (∀ k, Scheme.Modules.IsFrameOn (Ω k) (T k)) ∧
        ∀ (k l : κ) (hkl : T k ⊓ T l ≤ U (r k) ⊓ U (r l)),
          (Scheme.Modules.normModule π d L).presheaf.map (homOfLE inf_le_right).op (Ω l) =
            Y.presheaf.map (homOfLE hkl).op (Nf (U (r k) ⊓ U (r l)) (u (r k) (r l))) •
              (Scheme.Modules.normModule π d L).presheaf.map (homOfLE inf_le_left).op (Ω k) := by
  classical
  have hLF : Scheme.Modules.IsLocallyFreeOfRank d ((Scheme.Modules.pushforward π).obj (𝟙_
    X.Modules)) :=
    Scheme.Modules.isLocallyFreeOfRank_pushforward_of_isFinite_of_flat_of_locallyTrivialOver π d hd
      _
      (fun y => ⟨⊤, trivial, ⟨Scheme.Modules.pullbackUnitIso _⟩⟩)
  choose V hyV e he using fun y : Y => hLF.exists_basis y
  let κ : Type u := Σ i : ι, ↥(U i)
  let T : κ → Y.Opens := fun k => U k.1 ⊓ V k.2.1
  let r : κ → ι := fun k => k.1
  have hTU : ∀ k, T k ≤ U (r k) := fun k => inf_le_left
  have hTV : ∀ k, T k ≤ V k.2.1 := fun k => inf_le_right
  have hsup : (⨆ k, T k) = ⨆ i, U i := by
    apply le_antisymm
    · exact iSup_le fun k => (hTU k).trans (le_iSup U (r k))
    · refine iSup_le fun i => fun y hy => ?_
      exact Opens.mem_iSup.mpr ⟨⟨i, ⟨y, hy⟩⟩, ⟨hy, hyV y⟩⟩
  let e' : ∀ k, Fin d → Γ((Scheme.Modules.pushforward π).obj (𝟙_ X.Modules), T k) := fun k i =>
    ((Scheme.Modules.pushforward π).obj (𝟙_ X.Modules)).presheaf.map (homOfLE (hTV k)).op (e k.2.1
      i)
  have he' : ∀ (k : κ) (W : Y.Opens) (hW : W ≤ T k),
      ∃ b : Module.Basis (Fin d) Γ(Y, W) Γ((Scheme.Modules.pushforward π).obj (𝟙_ X.Modules), W),
        ∀ i, b i = ((Scheme.Modules.pushforward π).obj (𝟙_ X.Modules)).presheaf.map (homOfLE hW).op
          (e' k i) := by
    intro k W hW
    obtain ⟨b, hb⟩ := he k.2.1 W (hW.trans (hTV k))
    refine ⟨b, fun i => ?_⟩
    rw [hb i]
    simp only [e', ← CategoryTheory.comp_apply, ← Functor.map_comp]
    rfl
  let s' : ∀ k, Γ(L, π ⁻¹ᵁ T k) := fun k => L.presheaf.map (homOfLE (Scheme.Hom.preimage_mono π
    (hTU k))).op (s (r k))
  have hs' : ∀ k, Scheme.Modules.IsFrameOn (s' k) (π ⁻¹ᵁ T k) := fun k =>
    ((hs (r k)).mono (Scheme.Hom.preimage_mono π (hTU k))).map _
  let u' : ∀ k l, Γ(X, π ⁻¹ᵁ (T k ⊓ T l)) := fun k l => rX π (inf_le_inf (hTU k) (hTU l)) (u (r k)
    (r l))
  have hu' : ∀ k l, L.presheaf.map (homOfLE (Scheme.Hom.preimage_mono π inf_le_right)).op (s' l) =
      u' k l • L.presheaf.map (homOfLE (Scheme.Hom.preimage_mono π inf_le_left)).op (s' k) := by
    intro k l
    have hkl : T k ⊓ T l ≤ U (r k) ⊓ U (r l) := inf_le_inf (hTU k) (hTU l)
    have h := congrArg (L.presheaf.map (homOfLE (Scheme.Hom.preimage_mono π hkl)).op) (hu (r k) (r
      l))
    rw [Scheme.Modules.map_smul] at h
    simp only [s', u', ← CategoryTheory.comp_apply, ← Functor.map_comp] at h ⊢
    exact h
  obtain ⟨Ω, hΩ, hΩtrans⟩ :=
    Scheme.Modules.exists_isFrameOn_normModule_forall_map_eq_norm_smul_of_isFrameOn_preimage π d T
      e' he' L s' hs' u' hu'
  refine ⟨κ, T, r, hsup, hTU, Ω, hΩ, fun k l hkl => ?_⟩
  rw [hΩtrans k l]
  congr 1
  let algO : Algebra Γ(Y, T k ⊓ T l) Γ(X, π ⁻¹ᵁ (T k ⊓ T l)) := (π.app (T k ⊓ T l)).hom.toAlgebra
  obtain ⟨bO, hbO⟩ := he' k (T k ⊓ T l) inf_le_left
  let bA : Module.Basis (Fin d) Γ(Y, T k ⊓ T l) Γ(X, π ⁻¹ᵁ (T k ⊓ T l)) := bO
  let A := {W : Y.Opens // W ≤ T k ⊓ T l ∧ IsAffineOpen W}
  have hcov : T k ⊓ T l ≤ ⨆ a : A, a.1 := by
    intro y hy
    obtain ⟨W', hW', hyW', hW'le⟩ := exists_isAffineOpen_mem_and_subset (X := Y) (x := y) (U := T k
      ⊓ T l) hy
    exact Opens.mem_iSup.mpr ⟨⟨W', hW'le, hW'⟩, hyW'⟩
  apply Y.sheaf.eq_of_locally_eq' (fun a : A => a.1) (T k ⊓ T l) (fun a => homOfLE a.2.1) hcov
  rintro ⟨W', hW', hW'aff⟩
  change rY hW' (Algebra.norm Γ(Y, T k ⊓ T l) (u' k l)) = rY hW' (rY hkl (Nf (U (r k) ⊓ U (r l)) (u
    (r k) (r l))))
  let algW : Algebra Γ(Y, W') Γ(X, π ⁻¹ᵁ W') := (π.app W').hom.toAlgebra
  obtain ⟨bW, hbW⟩ := he' k W' (hW'.trans inf_le_left)
  let bB : Module.Basis (Fin d) Γ(Y, W') Γ(X, π ⁻¹ᵁ W') := bW
  have hb : ∀ i, bB i = rX π hW' (bA i) := by
    intro i
    have : bW i = ((Scheme.Modules.pushforward π).obj (𝟙_ X.Modules)).presheaf.map (homOfLE hW').op
      (bO i) := by
      rw [hbW i, hbO i]
      simp only [e', ← CategoryTheory.comp_apply, ← Functor.map_comp]
      rfl
    exact this
  rw [norm_map π hW' bA bB hb (u' k l)]
  have : Module.Free Γ(Y, W') Γ(X, π ⁻¹ᵁ W') := Module.Free.of_basis bB
  have : Module.Finite Γ(Y, W') Γ(X, π ⁻¹ᵁ W') := Module.Finite.of_basis bB
  have eR : rY hW' (rY hkl (Nf (U (r k) ⊓ U (r l)) (u (r k) (r l)))) =
      Nf W' (rX π (hW'.trans hkl) (u (r k) (r l))) := by
    rw [rY_rY]
    exact (h2 (U (r k) ⊓ U (r l)) W' (hW'.trans hkl) (u (r k) (r l))).symm
  have eL : rX π hW' (u' k l) = rX π (hW'.trans hkl) (u (r k) (r l)) := by
    simp only [u', rX_rX]
  rw [eR, eL, h3 W' hW'aff]
end Scheme_Modules_exists_refinement_isFrameOn_normModule_map_eq_normFun_smul
end AlgebraicCurves.Geometry.Sheaves.Proofs
end ProofImplementation

attribute [-instance] AlgebraicGeometry.Scheme.Hom.opensMapFinal
  AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid
  AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited TwoChartCech.Sections.M0_moduleA
  TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra
  TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module
  TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower
  TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing
  TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module
  TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup
  TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower
  CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup
  CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup
  CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite
  CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free
  AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback_monoidal
  AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization'
  AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal
  AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.sheafifyPullback_lifting
  PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ
  PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η
open _root_.PresheafOfModules.PullbackMonoidal in
attribute [-instance]
  PresheafOfModules.free_monoidal
  PresheafOfModules.restrictScalars_laxMonoidal
  isIso_δ_gS
  PresheafOfModules.pullback_oplaxMonoidal
  instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb
  PresheafOfModules.pullback_monoidal'
  SheafOfModules.isIso_ihomModelToIhom
attribute [-simp] AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec
  AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq
  TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq
  TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec
  TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec
  TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec
  CoherentBaseChange.TwoTermComplex.mk.injEq PresheafOfModules.freeεIso_hom_app
  PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app
  PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom
  SheafOfModules.ihomSectionsEquivFamily_unit
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left
  AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply
  SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply
