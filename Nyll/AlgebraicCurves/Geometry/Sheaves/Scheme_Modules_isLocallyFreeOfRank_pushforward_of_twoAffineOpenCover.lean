/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_isLocallyFreeOfRank_pushforward_of_twoAffineOpenCover.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Util.WithWeakNamespace
import Nyll.AlgebraicCurves.Cohomology.Cech.TwoChartCechSectionsOf
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesLocallyFreeOfRank
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_isIso_fromTildeGamma_pushforward_of_locallyTrivial
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_isLocallyFreeOfRank_tilde
import Nyll.AlgebraicCurves.Cohomology.Cech.TwoChartCech_Mumford_projective_ker_of_fibre_surjective
import Nyll.AlgebraicCurves.Geometry.Projective.Scheme_Modules_projective_sections_of_locallyTrivial
import Nyll.AlgebraicCurves.Geometry.Schemes.Scheme_TwoAffineOpenCover_flat_sections_of_flat
import Nyll.AlgebraicCurves.Geometry.Schemes.Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_H0
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsLocallyFreeOfRank_of_iso
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_exists_linearEquiv_sections_baseChange_of_locallyTrivial

/-!
# Local freeness of pushforward from two-chart cohomology

Finite two-chart cohomology, vanishing fibre first cohomology and constant fibre rank
give local freeness of the pushforward of a locally trivial module.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_isLocallyFreeOfRank_pushforward_of_twoAffineOpenCover
attribute [-simp]
  AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app
  TwoChartCech.Mumford.dK_apply
  TwoChartCech.Mumford.ι0_apply
  TwoChartCech.Mumford.ι1_apply
  TwoChartCech.KerCoprod.dK_apply
  TwoChartCech.KerCoprod.ι1_apply
  TwoChartCech.KerCoprod.ι0_apply

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.Opposite
open _root_.TopologicalSpace
open _root_.TensorProduct

namespace TwoChartCech
open _root_.TwoChartCech
open _root_.TwoChartCech

theorem surjective_baseChange_and_finrank_ker_of_comm
    {A : Type u} [CommRing A] {K : Type u} [Field K] [Algebra A K]
    {C0 C1 : Type u} [AddCommGroup C0] [Module A C0] [AddCommGroup C1] [Module A C1]
    {C0' C1' : Type u} [AddCommGroup C0'] [Module K C0'] [AddCommGroup C1'] [Module K C1']
    (d : C0 →ₗ[A] C1) (d' : C0' →ₗ[K] C1')
    (e0 : K ⊗[A] C0 ≃ₗ[K] C0') (e1 : K ⊗[A] C1 ≃ₗ[K] C1')
    (h : d' ∘ₗ e0.toLinearMap = e1.toLinearMap ∘ₗ d.baseChange K) :
    (Function.Surjective d' → Function.Surjective (d.baseChange K)) ∧
      Module.finrank K (LinearMap.ker (d.baseChange K)) = Module.finrank K (LinearMap.ker d') := by
  have hd : d.baseChange K = e1.symm.toLinearMap ∘ₗ d' ∘ₗ e0.toLinearMap := by
    rw [h]
    ext x
    change d.baseChange K ((1 : K) ⊗ₜ[A] x) =
      e1.symm (e1 (d.baseChange K ((1 : K) ⊗ₜ[A] x)))
    exact (e1.symm_apply_apply _).symm
  refine ⟨fun hs => ?_, ?_⟩
  · rw [hd]
    exact e1.symm.surjective.comp (hs.comp e0.surjective)
  · have hk : LinearMap.ker (d.baseChange K) = (LinearMap.ker d').comap e0.toLinearMap := by
      rw [hd]
      ext x
      change e1.symm (d' (e0 x)) = 0 ↔ d' (e0 x) = 0
      constructor
      · intro hx
        exact e1.symm.injective (hx.trans (map_zero e1.symm).symm)
      · intro hx
        rw [hx, map_zero]
    rw [hk, Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq]

end TwoChartCech

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

open _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (π : X ⟶ Spec (.of A))

namespace Hom
open _root_.AlgebraicGeometry.Scheme.Modules.Hom
end Hom
open scoped _root_.AlgebraicGeometry.Scheme.Modules.Hom in
omit π in
lemma Hom.app_presheaf_map {F G : X.Modules} (η : F ⟶ G) {U V : X.Opens} (i : V ⟶ U) (s : Γ(F, U)) :
    (η.app V).hom (F.presheaf.map i.op s) = G.presheaf.map i.op ((η.app U).hom s) := by
  have h := η.mapPresheaf.naturality i.op
  simp only [Scheme.Modules.mapPresheaf_app] at h
  simpa only [CategoryTheory.comp_apply] using ConcreteCategory.congr_hom h s

/-- The module over the affine base ring obtained by taking global sections of the pushforward. -/
noncomputable abbrev globalSectionsModule (F : X.Modules) : ModuleCat A :=
  ((modulesSpecToSheaf (R := .of A)).obj ((Scheme.Modules.pushforward π).obj F)).presheaf.obj (op ⊤)

/-- The linear equivalence from the affine pushforward section module to the original global
    sections. -/
noncomputable def globalSectionsEquiv (F : X.Modules) :
    letI := moduleSectionsOfHom π F ⊤
    globalSectionsModule π F ≃ₗ[A] Γ(F, ⊤) :=
  let := moduleSectionsOfHom π F ⊤
  { toFun := fun s => (show Γ(F, ⊤) from s)
    invFun := fun s => (show globalSectionsModule π F from s)
    map_add' := fun _ _ => rfl
    map_smul' := fun a s => by
      change (show Γ(X, ⊤) from ((π.app ⊤).hom ((((Spec (CommRingCat.of A)).presheaf.map
          (homOfLE (le_top (a := ⊤))).op).hom) ((Scheme.ΓSpecIso (.of A)).inv.hom a)))) • (show
              Γ(F, ⊤) from s) =
        ((π.appLE ⊤ ⊤ le_top).hom ((Scheme.ΓSpecIso (.of A)).inv.hom a)) • (show Γ(F, ⊤) from s)
      congr 1
      have h1 : (homOfLE (le_top : (⊤ : (Spec (CommRingCat.of A)).Opens) ≤ ⊤)) = 𝟙 _ :=
        Subsingleton.elim _ _
      have e1 : (Spec (CommRingCat.of A)).presheaf.map (homOfLE (le_top (a := (⊤ : (Spec
          (CommRingCat.of A)).Opens)))).op = 𝟙 _ := by
        rw [h1, op_id, CategoryTheory.Functor.map_id]
      have e2 : π.appLE ⊤ ⊤ le_top = π.app ⊤ := Scheme.Hom.appLE_eq_app _
      rw [e2, e1]
      rfl
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
omit π in
private theorem _root_.Module.Flat.prod_of_flat {R : Type u} [CommRing R] (M N : Type u)
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module.Flat R M] [Module.Flat R N] : Module.Flat R (M × N) := by
  rw [Module.Flat.iff_rTensor_preserves_injective_linearMap]
  intro P Q _ _ _ _ f hf
  have h1 := Module.Flat.rTensor_preserves_injective_linearMap (M := M) f hf
  have h2 := Module.Flat.rTensor_preserves_injective_linearMap (M := N) f hf
  have hsq : ∀ x, TensorProduct.prodRight R R Q M N (f.rTensor (M × N) x) =
      ((f.rTensor M).prodMap (f.rTensor N)) (TensorProduct.prodRight R R P M N x) := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul p mn => simp only [LinearMap.rTensor_tmul, LinearMap.prodMap_apply,
        TensorProduct.prodRight_tmul]
    | add x y hx hy => simp only [map_add, hx, hy]
  intro x y hxy
  have h := congrArg (TensorProduct.prodRight R R Q M N) hxy
  rw [hsq, hsq] at h
  have hinj : Function.Injective ((f.rTensor M).prodMap (f.rTensor N)) := h1.prodMap h2
  exact (TensorProduct.prodRight R R P M N).injective (hinj h)
alias Module.Flat.prod_of_flat := _root_.Module.Flat.prod_of_flat

theorem isLocallyFreeOfRank_pushforward_of_twoAffineOpenCover_aux
    [IsNoetherianRing A] [Flat π] (𝒱 : X.TwoAffineOpenCover) (F : X.Modules)
    (htriv : ∀ x : X, ∃ (V : X.Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj F ≅ SheafOfModules.unit V.toScheme.ringCatSheaf))
    (hfin : Module.Finite A (𝒱.sectionsOf π F).H0 ∧ Module.Finite A (𝒱.sectionsOf π F).H1) (n : ℕ)
    (hfib : ∀ (K : Type u) [Field K] [Algebra A K],
      Subsingleton ((𝒱.pullback π K).sectionsOf (pullback.snd π (specMap A K))
        ((Scheme.Modules.pullback (pullback.fst π (specMap A K))).obj F)).H1 ∧
      Module.finrank K ((𝒱.pullback π K).sectionsOf (pullback.snd π (specMap A K))
        ((Scheme.Modules.pullback (pullback.fst π (specMap A K))).obj F)).H0 = n) :
    Scheme.Modules.IsLocallyFreeOfRank n ((Scheme.Modules.pushforward π).obj F) := by
  classical
  set S := 𝒱.sectionsOf π F with hS
  have flat_sections : ∀ (U : X.Opens), IsAffineOpen U →
      letI := moduleSectionsOfHom π F U; Module.Flat A Γ(F, U) := by
    intro U hU
    let := algebraOfHom π U
    let := moduleSectionsOfHom π F U
    have : IsScalarTower A Γ(X, U) Γ(F, U) := isScalarTower_sections π F U
    have : Module.Flat A Γ(X, U) := flat_sections_of_flat π U hU
    have : Module.Projective Γ(X, U) Γ(F, U) := projective_sections_of_locallyTrivial F htriv
        ⟨U, hU⟩
    exact Module.Flat.trans A Γ(X, U) Γ(F, U)
  have : Module.Flat A S.M0 := flat_sections 𝒱.U0 𝒱.isAffineOpen_U0
  have : Module.Flat A S.M1 := flat_sections 𝒱.U1 𝒱.isAffineOpen_U1
  have : Module.Flat A S.M01 := flat_sections (𝒱.U0 ⊓ 𝒱.U1) 𝒱.isAffineOpen_inf
  have : Module.Flat A (S.M0 × S.M1) := Module.Flat.prod_of_flat S.M0 S.M1
  have : Module.Finite A (LinearMap.ker S.cechDiff) := hfin.1
  have : Module.Finite A (S.M01 ⧸ LinearMap.range S.cechDiff) := hfin.2
  have hsq : ∀ (K : Type u) [Field K] [Algebra A K],
      Function.Surjective (S.cechDiff.baseChange K) ∧
        Module.finrank K (LinearMap.ker (S.cechDiff.baseChange K)) = n := by
    intro K _ _
    obtain ⟨hH1, hH0⟩ := hfib K
    set fK := pullback.fst π (specMap A K) with hfK
    set FK : (Limits.pullback π (specMap A K)).Modules := (Scheme.Modules.pullback fK).obj F
        with hFK
    set SK := (𝒱.pullback π K).sectionsOf (pullback.snd π (specMap A K)) FK with hSK
    let η := (Scheme.Modules.pullbackPushforwardAdjunction fK).unit.app F
    let := moduleSectionsOfHom π F 𝒱.U0
    let := moduleSectionsOfHom π F 𝒱.U1
    let := moduleSectionsOfHom π F (𝒱.U0 ⊓ 𝒱.U1)
    let := moduleSectionsOfHom (pullback.snd π (specMap A K)) FK (fK ⁻¹ᵁ 𝒱.U0)
    let := moduleSectionsOfHom (pullback.snd π (specMap A K)) FK (fK ⁻¹ᵁ 𝒱.U1)
    let := moduleSectionsOfHom (pullback.snd π (specMap A K)) FK (fK ⁻¹ᵁ (𝒱.U0 ⊓ 𝒱.U1))
    obtain ⟨ε0, hε0⟩ := exists_linearEquiv_sections_baseChange_of_locallyTrivial π F htriv 𝒱.U0
      𝒱.isAffineOpen_U0 K
    obtain ⟨ε1, hε1⟩ := exists_linearEquiv_sections_baseChange_of_locallyTrivial π F htriv 𝒱.U1
      𝒱.isAffineOpen_U1 K
    obtain ⟨ε01, hε01⟩ := exists_linearEquiv_sections_baseChange_of_locallyTrivial π F htriv
        (𝒱.U0 ⊓ 𝒱.U1)
      𝒱.isAffineOpen_inf K
    let e0 : K ⊗[A] (S.M0 × S.M1) ≃ₗ[K] (SK.M0 × SK.M1) :=
      (TensorProduct.prodRight A K K S.M0 S.M1).trans (ε0.prodCongr ε1)
    let e1 : K ⊗[A] S.M01 ≃ₗ[K] SK.M01 := ε01
    have hr0 : ∀ s : S.M0, SK.r0 (ε0 ((1 : K) ⊗ₜ[A] s)) = ε01 ((1 : K) ⊗ₜ[A] (S.r0 s)) := by
      intro s
      erw [hε0, hε01]
      exact (Hom.app_presheaf_map η (homOfLE inf_le_left) s).symm
    have hr1 : ∀ s : S.M1, SK.r1 (ε1 ((1 : K) ⊗ₜ[A] s)) = ε01 ((1 : K) ⊗ₜ[A] (S.r1 s)) := by
      intro s
      erw [hε1, hε01]
      exact (Hom.app_presheaf_map η (homOfLE inf_le_right) s).symm
    have hcomm : SK.cechDiff ∘ₗ e0.toLinearMap = e1.toLinearMap ∘ₗ S.cechDiff.baseChange K := by
      refine LinearMap.ext fun x => ?_
      induction x using TensorProduct.inductionOn with
      | add x y hx hy => simp only [map_add] at hx hy ⊢; rw [hx, hy]
      | tmul k x => ?_
      obtain ⟨s0, s1⟩ := x
      have hk : ∀ {N : Type u} [AddCommGroup N] [Module A N] (y : N),
          (k ⊗ₜ[A] y : K ⊗[A] N) = k • ((1 : K) ⊗ₜ[A] y) := fun y => by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
      rw [hk, _root_.map_smul, _root_.map_smul, _root_.map_smul, _root_.map_smul]
      congr 1
      have he0 : e0 ((1 : K) ⊗ₜ[A] (s0, s1)) = (ε0 ((1 : K) ⊗ₜ[A] s0), ε1 ((1 : K) ⊗ₜ[A] s1)) := by
        simp only [e0]
        rfl
      have he1 : ∀ y, e1 y = ε01 y := fun _ => rfl
      rw [he0, he1, LinearMap.baseChange_tmul]
      erw [TwoChartCech.Sections.cechDiff_apply,
        TwoChartCech.Sections.cechDiff_apply]
      dsimp only
      rw [TensorProduct.tmul_sub, hr0, hr1]
      exact (map_sub ε01 _ _).symm
    have key := TwoChartCech.surjective_baseChange_and_finrank_ker_of_comm S.cechDiff
        SK.cechDiff e0 e1 hcomm
    refine ⟨key.1 ?_, key.2.trans hH0⟩
    rw [← LinearMap.range_eq_top, ← Submodule.Quotient.subsingleton_iff]
    exact hH1
  obtain ⟨hproj, -, hrank⟩ := TwoChartCech.Mumford.projective_ker_of_fibre_surjective S.cechDiff
    (fun K _ _ => (hsq K).1)
  obtain ⟨e0, he0⟩ := exists_linearEquiv_sectionsOf_H0 𝒱 π F
  let e : globalSectionsModule π F ≃ₗ[A] LinearMap.ker S.cechDiff := (globalSectionsEquiv π
      F).trans e0
  have : Module.Projective A (globalSectionsModule π F) := Module.Projective.of_equiv e.symm
  have : Module.Finite A (globalSectionsModule π F) := Module.Finite.equiv e.symm
  have hrk : ∀ (K : Type u) [Field K] [Algebra A K],
      Module.finrank K (K ⊗[A] globalSectionsModule π F) = n := by
    intro K _ _
    rw [(LinearEquiv.baseChange A K _ _ e).finrank_eq, hrank K, (hsq K).2]
  have hLF := isLocallyFreeOfRank_tilde (R := .of A) (globalSectionsModule π F) n hrk
  have := isIso_fromTildeGamma_pushforward_of_locallyTrivial π 𝒱 F htriv
  exact IsLocallyFreeOfRank.of_iso (asIso (Scheme.Modules.fromTildeΓ (R := .of A)
    ((Scheme.Modules.pushforward π).obj F))) hLF

end AlgebraicGeometry.Scheme.Modules

with_weak_namespace _root_.AlgebraicCurves.Geometry.Sheaves.Proofs
with_weak_namespace Scheme_Modules_isLocallyFreeOfRank_pushforward_of_twoAffineOpenCover
with_weak_namespace AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.Modules Modules in
with_weak_namespace _root_.AlgebraicCurves.Geometry.Sheaves.Proofs
with_weak_namespace Scheme_Modules_isLocallyFreeOfRank_pushforward_of_twoAffineOpenCover
theorem
    _root_.AlgebraicGeometry.Scheme.Modules.isLocallyFreeOfRank_pushforward_of_twoAffineOpenCover
    {A : Type u} [CommRing A] [IsNoetherianRing A] {X : Scheme.{u}} (π : X ⟶ Spec (.of A)) [Flat π]
    (𝒱 : X.TwoAffineOpenCover) (F : X.Modules)
    (htriv : ∀ x : X, ∃ (V : X.Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj F ≅ SheafOfModules.unit V.toScheme.ringCatSheaf))
    (hfin : Module.Finite A (𝒱.sectionsOf π F).H0 ∧ Module.Finite A (𝒱.sectionsOf π F).H1) (n : ℕ)
    (hfib : ∀ (K : Type u) [Field K] [Algebra A K],
      Subsingleton ((𝒱.pullback π K).sectionsOf (pullback.snd π
          (Scheme.TwoAffineOpenCover.specMap A K))
        ((Scheme.Modules.pullback (pullback.fst π (Scheme.TwoAffineOpenCover.specMap A K))).obj
            F)).H1 ∧
      Module.finrank K ((𝒱.pullback π K).sectionsOf (pullback.snd π
          (Scheme.TwoAffineOpenCover.specMap A K))
        ((Scheme.Modules.pullback (pullback.fst π (Scheme.TwoAffineOpenCover.specMap A K))).obj
            F)).H0 = n) :
    Scheme.Modules.IsLocallyFreeOfRank n ((Scheme.Modules.pushforward π).obj F) :=
  isLocallyFreeOfRank_pushforward_of_twoAffineOpenCover_aux π 𝒱 F htriv hfin n hfib

end Scheme_Modules_isLocallyFreeOfRank_pushforward_of_twoAffineOpenCover
end AlgebraicCurves.Geometry.Sheaves.Proofs
end ProofImplementation
