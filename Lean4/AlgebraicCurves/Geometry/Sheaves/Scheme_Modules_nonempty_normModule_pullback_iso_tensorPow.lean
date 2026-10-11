/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_nonempty_normModule_pullback_iso_tensorPow.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.RingTheory.Norm.Defs
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Ext
import AlgebraicCurves.Geometry.Picard.Functor
import AlgebraicCurves.Geometry.Sheaves.ModulesNormModule
import AlgebraicCurves.Geometry.Sheaves.ModulesTensorPow
import SchemeTheory.Modules.TensorSections
import SchemeTheory.Modules.PullbackLocalSection
import AlgebraicCurves.Geometry.Sheaves.ModulesLocallyFreeOfRank
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_exists_isFrameOn_normModule_forall_map_eq_norm_smul_of_isFrameOn_preimage
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_exists_iso_app_eq_of_isFrameOn_of_eq_smul
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsFrameOn_tensorPowSection
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsFrameOn_pullbackLocalSection
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_isLocallyFreeOfRank_pushforward_of_isFinite_of_flat_of_locallyTrivialOver
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsLocallyFreeOfRank_exists_basis
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_exists_isFrameOn

/-!
# Scheme Modules nonempty norm Module pullback iso tensor Pow
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_nonempty_normModule_pullback_iso_tensorPow
open _root_.PresheafOfModules.PullbackMonoidal in
attribute [-instance]
  SheafOfModules.isIso_ihomModelToIhom
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
  AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback_monoidal
  AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization'
  AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal
  AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.sheafifyPullback_lifting
attribute [-simp] PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom
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
  PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app
  AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app


open _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory
open _root_.Opposite
open _root_.TopologicalSpace
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.Modules


universe u

namespace NPPBody

variable {X Y : Scheme.{u}}

/-- Restriction of a module section along an inclusion of open subsets. -/
noncomputable abbrev res (M : Y.Modules) {W' W : Y.Opens} (h : W' ≤ W) (s : Γ(M, W)) : Γ(M, W') :=
  M.presheaf.map (homOfLE h).op s

lemma res_res (M : Y.Modules) {W₁ W₂ W₃ : Y.Opens} (h₂₁ : W₂ ≤ W₁) (h₃₂ : W₃ ≤ W₂) (s : Γ(M, W₁)) :
    res M h₃₂ (res M h₂₁ s) = res M (h₃₂.trans h₂₁) s := by
  change (M.presheaf.map (homOfLE h₂₁).op ≫ M.presheaf.map (homOfLE h₃₂).op) s = _
  rw [← Functor.map_comp]
  rfl

lemma res_smul (M : Y.Modules) {W' W : Y.Opens} (h : W' ≤ W) (r : Γ(Y, W)) (s : Γ(M, W)) :
    res M h (r • s) = Y.presheaf.map (homOfLE h).op r • res M h s :=
  AlgebraicGeometry.Scheme.Modules.map_smul M (homOfLE h) r s

lemma res_self (M : Y.Modules) {W : Y.Opens} (x : Γ(M, W)) : res M (le_refl W) x = x := by
  change M.presheaf.map (homOfLE (le_refl W)).op x = x
  rw [Subsingleton.elim (homOfLE (le_refl W)) (𝟙 W), op_id, M.presheaf.map_id]; rfl

lemma resFun_pow {W' W : Y.Opens} (h : W' ≤ W) (r : Γ(Y, W)) (n : ℕ) :
    Y.presheaf.map (homOfLE h).op (r ^ n) = (Y.presheaf.map (homOfLE h).op r) ^ n :=
  map_pow (Y.presheaf.map (homOfLE h).op).hom r n

lemma tensorPowSection_smul {L : Y.Modules} {U : Y.Opens} (g : Γ(Y, U)) (s : Γ(L, U)) (n : ℕ) :
    tensorPowSection (g • s) n = g ^ n • tensorPowSection s n := by
  induction n with
  | zero =>
      change (unitSection U : Γ(𝟙_ Y.Modules, U)) = g ^ 0 • unitSection U
      rw [pow_zero, one_smul]
  | succ n ih =>
    rw [tensorPowSection_succ, tensorPowSection_succ, ih, tensorSections_smul_left,
      tensorSections_smul_right,
      smul_smul, pow_succ]
    rfl

/-- The direct image of the structure sheaf, viewed as a module sheaf on the target. -/
noncomputable abbrev OX (π : X ⟶ Y) : Y.Modules := (pushforward π).obj (𝟙_ X.Modules)

/-- The chosen sections restrict to a basis on every smaller open subset. -/
def BasisClause (π : X ⟶ Y) (d : ℕ) (W : Y.Opens) (e : Fin d → Γ(OX π, W)) : Prop :=
  ∀ (W' : Y.Opens) (h : W' ≤ W), ∃ b : Module.Basis (Fin d) Γ(Y, W') Γ(OX π, W'),
    ∀ k, b k = (OX π).presheaf.map (homOfLE h).op (e k)

theorem basisClause_res (π : X ⟶ Y) (d : ℕ) {W W' : Y.Opens} {e : Fin d → Γ(OX π, W)}
    (he : BasisClause π d W e) (h : W' ≤ W) :
    BasisClause π d W' (fun k => (OX π).presheaf.map (homOfLE h).op (e k)) := by
  intro W'' h''
  obtain ⟨b, hb⟩ := he W'' (h''.trans h)
  refine ⟨b, fun k => ?_⟩
  rw [hb k]
  exact (res_res (OX π) h h'' (e k)).symm

/--
Local data consisting of an open subset, a frame of the line bundle and a restriction-compatible
basis of the pushed-forward structure sheaf.
-/
structure Idx (π : X ⟶ Y) (d : ℕ) (L : Y.Modules) : Type u where
  /-- The open on which the module and the finite morphism admit the chosen frames. -/
  W : Y.Opens
  /-- The local section used to trivialize the invertible module. -/
  ℓ : Γ(L, W)
  /-- The chosen section is a frame on the open. -/
  hℓ : IsFrameOn ℓ W
  /-- The indexed sections of the pushed-forward structure sheaf. -/
  e : Fin d → Γ(OX π, W)
  /-- The chosen sections form the basis required by the finite-morphism basis clause. -/
  he : BasisClause π d W e

theorem exists_idx (π : X ⟶ Y) [IsFinite π] [Flat π] [LocallyOfFinitePresentation π] (d : ℕ)
    (hd : ∀ y : Y, π.finrank y = d) {L : Y.Modules} (hL : IsInvertible L) (y : Y) :
    ∃ i : Idx π d L, y ∈ i.W := by
  obtain ⟨W₁, ℓ, hy₁, hℓ⟩ := hL.exists_isFrameOn y
  have hN : ∀ t : Y, ∃ W : Y.Opens, t ∈ W ∧
      Nonempty ((Scheme.Modules.pullback (π ⁻¹ᵁ W).ι).obj (𝟙_ X.Modules) ≅ 𝟙_ (↑(π ⁻¹ᵁ W) :
        Scheme.{u}).Modules) :=
    fun t => ⟨⊤, trivial, ⟨Scheme.Modules.pullbackUnitIso _⟩⟩
  have hE : IsLocallyFreeOfRank d (OX π) :=
    isLocallyFreeOfRank_pushforward_of_isFinite_of_flat_of_locallyTrivialOver π d hd _ hN
  obtain ⟨W₂, hy₂, e, he⟩ := hE.exists_basis y
  refine ⟨⟨W₁ ⊓ W₂, res L inf_le_left ℓ, (hℓ.map _).mono inf_le_left,
    fun k => res (OX π) inf_le_right (e k), basisClause_res π d he inf_le_right⟩, hy₁, hy₂⟩

theorem norm_app_eq_pow (π : X ⟶ Y) (d : ℕ) {W : Y.Opens} {e : Fin d → Γ(OX π, W)} (he :
  BasisClause π d W e)
    (g : Γ(Y, W)) :
    letI : Algebra Γ(Y, W) Γ(X, π ⁻¹ᵁ W) := (π.app W).hom.toAlgebra
    Algebra.norm Γ(Y, W) (π.app W g) = g ^ d := by
  let : Algebra Γ(Y, W) Γ(X, π ⁻¹ᵁ W) := (π.app W).hom.toAlgebra
  obtain ⟨b₀, -⟩ := he W (le_refl W)
  let idl : Γ(X, π ⁻¹ᵁ W) ≃ₗ[Γ(Y, W)] Γ(OX π, W) :=
    { toFun := fun x => (show Γ(OX π, W) from x)
      invFun := fun x => (show Γ(X, π ⁻¹ᵁ W) from x)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let b : Module.Basis (Fin d) Γ(Y, W) Γ(X, π ⁻¹ᵁ W) := Module.Basis.ofRepr (idl.trans b₀.repr)
  have h := Algebra.norm_algebraMap_of_basis b g
  rw [Fintype.card_fin] at h
  exact h

theorem nonempty_normModule_pullback_iso_tensorPow
    (π : X ⟶ Y) [IsFinite π] [Flat π] [LocallyOfFinitePresentation π]
    (d : ℕ) (hd : ∀ y : Y, π.finrank y = d) {L : Y.Modules} (hL : IsInvertible L) :
    Nonempty (normModule π d ((Scheme.Modules.pullback π).obj L) ≅ L.tensorPow d) := by
  classical
  let L' : X.Modules := (Scheme.Modules.pullback π).obj L
  let N : Y.Modules := normModule π d L'
  let Q : Y.Modules := L.tensorPow d
  have hg : ∀ i j : Idx π d L, ∃ g : Γ(Y, i.W ⊓ j.W), g • res L inf_le_left i.ℓ = res L
    inf_le_right j.ℓ :=
    fun i j => (i.hℓ.existsUnique (inf_le_left : i.W ⊓ j.W ≤ i.W) inf_le_left (res L inf_le_right
      j.ℓ)).exists
  choose g hg using hg
  obtain ⟨Ω, hΩ, hΩt⟩ :=
    exists_isFrameOn_normModule_forall_map_eq_norm_smul_of_isFrameOn_preimage π d (fun i : Idx π d
      L => i.W)
      (fun i => i.e) (fun i => i.he) L' (fun i => pullbackLocalSection π i.ℓ)
      (fun i => i.hℓ.pullbackLocalSection π)
      (fun i j => π.app (i.W ⊓ j.W) (g i j))
      (fun i j => by
        change ((Scheme.Modules.pullback π).obj L).presheaf.map (homOfLE (π.preimage_mono
          inf_le_right)).op
            (pullbackLocalSection π j.ℓ) =
          π.app (i.W ⊓ j.W) (g i j) •
            ((Scheme.Modules.pullback π).obj L).presheaf.map (homOfLE (π.preimage_mono
              inf_le_left)).op
              (pullbackLocalSection π i.ℓ)
        rw [map_homOfLE_pullbackLocalSection π inf_le_right, map_homOfLE_pullbackLocalSection π
          inf_le_left,
          ← pullbackLocalSection_smul, hg])
  have hΩt' : ∀ i j, res N inf_le_right (Ω j) = (g i j) ^ d • res N inf_le_left (Ω i) := by
    intro i j
    have h := hΩt i j
    rw [norm_app_eq_pow π d (basisClause_res π d i.he inf_le_left) (g i j)] at h
    exact h
  let q : ∀ i : Idx π d L, Γ(Q, i.W) := fun i => tensorPowSection i.ℓ d
  have hq : ∀ i, IsFrameOn (q i) i.W := fun i => i.hℓ.tensorPowSection d
  have hqt : ∀ i j, res Q inf_le_right (q j) = (g i j) ^ d • res Q inf_le_left (q i) := by
    intro i j
    change Q.presheaf.map (homOfLE inf_le_right).op (tensorPowSection j.ℓ d) =
      (g i j) ^ d • Q.presheaf.map (homOfLE inf_le_left).op (tensorPowSection i.ℓ d)
    rw [map_tensorPowSection, map_tensorPowSection, ← tensorPowSection_smul]
    congr 1
    exact (hg i j).symm
  let S : ∀ W : Y.Opens, Set (Γ(N, W) × Γ(Q, W)) := fun W =>
    {pq | ∃ (i : Idx π d L) (h : W ≤ i.W), pq.1 = res N h (Ω i) ∧ pq.2 = res Q h (q i)}
  obtain ⟨e, -⟩ := exists_iso_app_eq_of_isFrameOn_of_eq_smul S
    (by
      rintro W pq ⟨i, h, h1, h2⟩
      rw [h1, h2]
      exact ⟨((hΩ i).map _).mono h, ((hq i).map _).mono h⟩)
    (by
      intro y
      obtain ⟨i, hy⟩ := exists_idx π d hd hL y
      exact ⟨i.W, hy, ⟨(res N (le_refl _) (Ω i), res Q (le_refl _) (q i)), i, le_refl _, rfl, rfl⟩⟩)
    (by
      rintro W W' h' pq ⟨i, h, h1, h2⟩
      refine ⟨i, h'.trans h, ?_, ?_⟩
      · change res N h' pq.1 = _
        rw [h1, res_res]
      · change res Q h' pq.2 = _
        rw [h2, res_res])
    (by
      rintro W pq pq' ⟨i, h, h1, h2⟩ ⟨j, h', h1', h2'⟩
      refine ⟨(Y.presheaf.map (homOfLE (le_inf h h' : W ≤ i.W ⊓ j.W)).op (g i j)) ^ d, ?_, ?_⟩
      · rw [h1', h1, ← resFun_pow, ← res_res N (inf_le_left : i.W ⊓ j.W ≤ i.W) (le_inf h h'), ←
          res_smul,
          ← hΩt', res_res]
      · rw [h2', h2, ← resFun_pow, ← res_res Q (inf_le_left : i.W ⊓ j.W ≤ i.W) (le_inf h h'), ←
          res_smul,
          ← hqt, res_res])
  exact ⟨e⟩

end NPPBody

theorem _root_.AlgebraicGeometry.Scheme.Modules.nonempty_normModule_pullback_iso_tensorPow
    {X Y : Scheme.{u}} (π : X ⟶ Y) [IsFinite π] [Flat π] [LocallyOfFinitePresentation π]
    (d : ℕ) (hd : ∀ y : Y, π.finrank y = d)
    {L : Y.Modules} (hL : Scheme.Modules.IsInvertible L) :
    Nonempty (Scheme.Modules.normModule π d ((Scheme.Modules.pullback π).obj L) ≅ L.tensorPow d) :=
  NPPBody.nonempty_normModule_pullback_iso_tensorPow π d hd hL
end Scheme_Modules_nonempty_normModule_pullback_iso_tensorPow
end AlgebraicCurves.Geometry.Sheaves.Proofs
end ProofImplementation

open _root_.PresheafOfModules.PullbackMonoidal in
attribute [-instance]
  TwoChartCech.Sections.M0_moduleA
  TwoChartCech.Sections.M1_module
  TwoChartCech.Cover.A01_algebra
  TwoChartCech.Cover.A0_algebra
  TwoChartCech.Cover.A1_commRing
  TwoChartCech.Cover.A1_algebra
  TwoChartCech.Sections.M01_module
  TwoChartCech.Sections.M0_addCommGroup
  TwoChartCech.Sections.M0_tower
  TwoChartCech.Sections.M01_addCommGroup
  TwoChartCech.Cover.A0_commRing
  TwoChartCech.Sections.M1_tower
  TwoChartCech.Sections.M01_moduleA
  TwoChartCech.Sections.M0_module
  TwoChartCech.Sections.M1_moduleA
  TwoChartCech.Sections.M1_addCommGroup
  TwoChartCech.Cover.A01_commRing
  TwoChartCech.Sections.M01_tower
  CoherentBaseChange.TwoTermComplex.C0_module
  CoherentBaseChange.TwoTermComplex.C0_addCommGroup
  CoherentBaseChange.TwoTermComplex.C1_module
  CoherentBaseChange.TwoTermComplex.C1_addCommGroup
  CoherentBaseChange.TwoTermComplex.C0_free
  CoherentBaseChange.TwoTermComplex.C1_finite
  CoherentBaseChange.TwoTermComplex.C0_finite
  CoherentBaseChange.TwoTermComplex.C1_free
  SheafOfModules.isIso_ihomModelToIhom
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
  AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback_monoidal
  AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization'
attribute [-instance] AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal
  AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.sheafifyPullback_lifting
attribute [-simp] AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right
  AlgebraicGeometry.Scheme.Modules.map_unitSection
  AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply
  AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq
  TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq
  TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec
  TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec
  TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec
  CoherentBaseChange.TwoTermComplex.mk.injEq
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
  PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app
  AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app
