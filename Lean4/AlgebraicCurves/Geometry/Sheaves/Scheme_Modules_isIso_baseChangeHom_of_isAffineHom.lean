/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_isIso_baseChangeHom_of_isAffineHom.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Cohomology.Cech.TwoChartCechSectionsOf
import AlgebraicCurves.Geometry.Sheaves.ModulesBaseChangeHom
import AlgebraicCurves.Geometry.Sheaves.ModulesTildePullback
import AlgebraicCurves.Geometry.Picard.Functor
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_isIso_fromTildeGamma_pushforward_of_locallyTrivial
import AlgebraicCurves.Cohomology.Cech.TwoChartCech_Mumford_projective_ker_of_fibre_surjective
import AlgebraicCurves.Geometry.Projective.Scheme_Modules_projective_sections_of_locallyTrivial
import AlgebraicCurves.Geometry.Schemes.Scheme_TwoAffineOpenCover_flat_sections_of_flat
import AlgebraicCurves.Geometry.Schemes.Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_H0
import AlgebraicCurves.Geometry.Schemes.SchemeHomOverBaseChange
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_exists_linearEquiv_sections_baseChange_of_locallyTrivial
import AlgebraicCurves.Geometry.Sheaves.tilde_pullbackSpecIso_hom_app_top_unit_toOpen
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_isIso_baseChange_sections_of_isIso_fromTildeGamma
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_isIso_baseChangeHom_iff_of_isPullback
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_isIso_baseChangeHom_of_forall_exists_isPullback

/-!
# Base change for affine pushforward

The comparison is an isomorphism for locally trivial modules along an affine morphism.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_isIso_baseChangeHom_of_isAffineHom
attribute [-simp] TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply
  TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply
  TwoChartCech.KerCoprod.ι0_apply

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.Opposite
open _root_.TopologicalSpace
open _root_.TensorProduct

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

theorem isIso_of_isIso_moduleSpecΓFunctor_map {A : Type u} [CommRing A]
    {M N : (Spec (CommRingCat.of A)).Modules}
    (hM : IsIso (Scheme.Modules.fromTildeΓ (R := .of A) M)) (hN : IsIso (Scheme.Modules.fromTildeΓ
      (R := .of A) N))
    (f : M ⟶ N) (hf : IsIso ((moduleSpecΓFunctor (R := .of A)).map f)) : IsIso f := by
  have hnat : (tilde.functor (.of A)).map ((moduleSpecΓFunctor (R := .of A)).map f) ≫
      Scheme.Modules.fromTildeΓ (R := .of A) N = Scheme.Modules.fromTildeΓ (R := .of A) M ≫ f :=
    (tilde.adjunction (R := .of A)).counit.naturality f
  let eM := asIso (Scheme.Modules.fromTildeΓ (R := .of A) M)
  let ef := asIso ((moduleSpecΓFunctor (R := .of A)).map f)
  let eN := asIso (Scheme.Modules.fromTildeΓ (R := .of A) N)
  let e : M ≅ N := eM.symm ≪≫ (tilde.functor (.of A)).mapIso ef ≪≫ eN
  have he : e.hom = f := by
    simp only [e, eM, ef, eN, Iso.trans_hom, Iso.symm_hom, asIso_inv]
    exact (IsIso.inv_comp_eq (Scheme.Modules.fromTildeΓ (R := .of A) M)).mpr hnat
  rw [← he]
  infer_instance

namespace Hom
open _root_.AlgebraicGeometry.Scheme.Modules.Hom
end Hom
open scoped _root_.AlgebraicGeometry.Scheme.Modules.Hom in
lemma Hom.app_presheaf_map {X : Scheme.{u}} {F G : X.Modules} (η : F ⟶ G) {U V : X.Opens} (i : V ⟶
  U) (s : Γ(F, U)) :
    (η.app V).hom (F.presheaf.map i.op s) = G.presheaf.map i.op ((η.app U).hom s) := by
  have h := η.mapPresheaf.naturality i.op
  simp only [Scheme.Modules.mapPresheaf_app] at h
  simpa only [CategoryTheory.comp_apply] using ConcreteCategory.congr_hom h s

lemma baseChangeHom_app_top_unit {X X' T T' : Scheme.{u}}
    (π : X ⟶ T) (ψ : T' ⟶ T) (π' : X' ⟶ T') (g : X' ⟶ X)
    (h : g ≫ π = π' ≫ ψ) (F : X.Modules) (s : Γ((pushforward π).obj F, ⊤)) :
    (Scheme.Modules.baseChangeHom h F).app ⊤
        (((pullbackPushforwardAdjunction ψ).unit.app ((pushforward π).obj F)).app ⊤ s) =
      ((pullbackPushforwardAdjunction g).unit.app F).app ⊤ s := by
  have hi : (eqToHom (show (π' ≫ ψ) ⁻¹ᵁ ⊤ = (g ≫ π) ⁻¹ᵁ ⊤ by rw [h])) =
      𝟙 (⊤ : X'.Opens) := Subsingleton.elim _ _
  have hmap : ((Scheme.Modules.pullback g).obj F).presheaf.map
      (eqToHom (show (π' ≫ ψ) ⁻¹ᵁ ⊤ = (g ≫ π) ⁻¹ᵁ ⊤ by rw [h])).op = 𝟙 _ := by
    rw [hi]
    exact ((Scheme.Modules.pullback g).obj F).presheaf.map_id (op ⊤)
  have hm := (unit_app_app_comp_baseChangeHom_app π ψ π' g h F ⊤).trans
    ((congrArg (fun t => ((pullbackPushforwardAdjunction g).unit.app F).app (π ⁻¹ᵁ ⊤) ≫ t)
      hmap).trans (Category.comp_id _))
  exact ConcreteCategory.congr_hom hm s

section resM
variable {X : Scheme.{u}} (M : X.Modules)

/-- Restriction of a module section along an inclusion of opens. -/
noncomputable abbrev resM {W W' : X.Opens} (h : W' ≤ W) : Γ(M, W) → Γ(M, W') :=
  fun s => M.presheaf.map (homOfLE h).op s

variable {M}

lemma map_eq_resM {W W' : X.Opens} (i : W' ⟶ W) (s : Γ(M, W)) : M.presheaf.map i.op s = resM M i.le
  s := by
  rw [Subsingleton.elim i (homOfLE i.le)]

lemma resM_resM {W W' W'' : X.Opens} (h : W' ≤ W) (h' : W'' ≤ W') (s : Γ(M, W)) :
    resM M h' (resM M h s) = resM M (h'.trans h) s := by
  change (M.presheaf.map (homOfLE h).op ≫ M.presheaf.map (homOfLE h').op) s = _
  rw [← Functor.map_comp, ← op_comp]
  rfl

lemma resM_refl {W : X.Opens} (h : W ≤ W) (s : Γ(M, W)) : resM M h s = s := by
  change M.presheaf.map (homOfLE h).op s = s
  rw [Subsingleton.elim (homOfLE h) (𝟙 W), op_id, CategoryTheory.Functor.map_id]
  rfl

lemma presheaf_map_map_eq (M : X.Modules) {U V W : X.Opens} (a : V ⟶ U) (b : W ⟶ V) (c : W ⟶ U)
    (s : Γ(M, U)) : M.presheaf.map b.op (M.presheaf.map a.op s) = M.presheaf.map c.op s := by
  rw [← CategoryTheory.comp_apply, ← Functor.map_comp, ← op_comp, Subsingleton.elim (b ≫ a) c]

end resM

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
    | tmul p mn =>
        simp only [LinearMap.rTensor_tmul, LinearMap.prodMap_apply, TensorProduct.prodRight_tmul]
    | add x y hx hy => simp only [map_add, hx, hy]
  intro x y hxy
  have h := congrArg (TensorProduct.prodRight R R Q M N) hxy
  rw [hsq, hsq] at h
  have hinj : Function.Injective ((f.rTensor M).prodMap (f.rTensor N)) := h1.prodMap h2
  exact (TensorProduct.prodRight R R P M N).injective (hinj h)
alias Module.Flat.prod_of_flat := _root_.Module.Flat.prod_of_flat

section bridge
variable {A : Type u} [CommRing A] (A' : Type u) [CommRing A'] [Algebra A A']

/-- The identity linear equivalence on the scalar-restricted coefficient module. -/
noncomputable def restrictScalarsSelfEquiv :
    A' ≃ₗ[A'] ((ModuleCat.restrictScalars (CommRingCat.ofHom (algebraMap A A')).hom).obj
      (ModuleCat.of A' A')) :=
  LinearEquiv.refl A' A'

scoped instance : IsScalarTower A A'
    ((ModuleCat.restrictScalars (CommRingCat.ofHom (algebraMap A A')).hom).obj (ModuleCat.of A'
      A')) :=
  ⟨fun a a' x => by
    change (a • a') • x = ((algebraMap A A') a) • (a' • x)
    rw [Algebra.smul_def, mul_smul]⟩

/-- The equivalence between the tensor and categorical scalar extensions. -/
noncomputable def extendScalarsAlgebraMapEquiv (N : ModuleCat.{u} A) :
    (A' ⊗[A] N) ≃ₗ[A'] (ModuleCat.extendScalars (CommRingCat.ofHom (algebraMap A A')).hom).obj N :=
  TensorProduct.AlgebraTensorModule.congr (restrictScalarsSelfEquiv (A := A) A') (LinearEquiv.refl
    A N)

theorem extendScalarsAlgebraMapEquiv_tmul (N : ModuleCat.{u} A) (a' : A') (n : N) :
    extendScalarsAlgebraMapEquiv (A := A) A' N (a' ⊗ₜ n) =
      ((a' : ((ModuleCat.restrictScalars (CommRingCat.ofHom (algebraMap A A')).hom).obj
        (ModuleCat.of A' A'))) ⊗ₜ[A] n :
        (ModuleCat.extendScalars (CommRingCat.ofHom (algebraMap A A')).hom).obj N) := by
  rfl

end bridge

section main

open _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (π : X ⟶ Spec (.of A))

/-- Global sections of the pushforward as a module over the base ring. -/
noncomputable abbrev globalSectionsModule (F : X.Modules) : ModuleCat A :=
  ((modulesSpecToSheaf (R := .of A)).obj ((Scheme.Modules.pushforward π).obj F)).presheaf.obj (op ⊤)

/-- Global sections identified with sections of the original module. -/
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

/-- The module of global sections of a module on an affine scheme. -/
noncomputable abbrev ΓMod (N : (Spec (CommRingCat.of A)).Modules) : ModuleCat A :=
  (moduleSpecΓFunctor (R := .of A)).obj N

variable (A' : Type u) [CommRing A'] [Algebra A A']

/-- The coefficient algebra map as a morphism of commutative rings. -/
noncomputable abbrev φA : CommRingCat.of A ⟶ CommRingCat.of A' := CommRingCat.ofHom (algebraMap A
  A')

lemma specMap_eq : Scheme.TwoAffineOpenCover.specMap A A' = Spec.map (φA (A := A) A') := rfl

theorem exists_linearEquiv_tensor_ΓMod_pullback (N : (Spec (CommRingCat.of A)).Modules)
    (hN : IsIso (Scheme.Modules.fromTildeΓ (R := .of A) N)) :
    ∃ σ : A' ⊗[A] (ΓMod N) ≃ₗ[A']
        ((moduleSpecΓFunctor (R := .of A')).obj ((Scheme.Modules.pullback (Spec.map (φA (A := A)
          A'))).obj N)),
      ∀ m : ΓMod N, σ ((1 : A') ⊗ₜ[A] m) =
        ((((pullbackPushforwardAdjunction (Spec.map (φA (A := A) A'))).unit.app N).app ⊤).hom m :)
          := by
  have hiso := isIso_baseChange_sections_of_isIso_fromTildeGamma (φA (A := A) A') N hN
  let τ := asIso (((ModuleCat.extendRestrictScalarsAdj (φA (A := A) A').hom).homEquiv
    (ΓMod N) ((moduleSpecΓFunctor (R := .of A')).obj
      ((Scheme.Modules.pullback (Spec.map (φA (A := A) A'))).obj N))).symm
        ((moduleSpecΓFunctor (R := .of A)).map
          ((pullbackPushforwardAdjunction (Spec.map (φA (A := A) A'))).unit.app N) ≫
          (Scheme.Modules.pushforwardSpecCompΓIso (φA (A := A) A')).hom.app
            ((Scheme.Modules.pullback (Spec.map (φA (A := A) A'))).obj N)))
  refine ⟨(extendScalarsAlgebraMapEquiv (A := A) A' (ΓMod N)).trans τ.toLinearEquiv, fun m => ?_⟩
  rw [LinearEquiv.trans_apply, extendScalarsAlgebraMapEquiv_tmul]
  refine Eq.trans (ModuleCat.extendRestrictScalarsAdj_homEquiv_apply τ.hom m).symm ?_
  simp only [τ, asIso_hom, Equiv.apply_symm_apply]
  rfl

theorem exists_linearEquiv_ker_baseChange_cechDiff (𝒱 : X.TwoAffineOpenCover) (F : X.Modules)
    (htriv : ∀ x : X, ∃ (V : X.Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj F ≅
        SheafOfModules.unit V.toScheme.ringCatSheaf))
        :
    (Function.Surjective ((𝒱.pullback π A').sectionsOf
          (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap A A'))
          ((Scheme.Modules.pullback (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap A
            A'))).obj F)).cechDiff →
      Function.Surjective ((𝒱.sectionsOf π F).cechDiff.baseChange A')) ∧
    ∃ κ : LinearMap.ker ((𝒱.sectionsOf π F).cechDiff.baseChange A') ≃ₗ[A']
        LinearMap.ker ((𝒱.pullback π A').sectionsOf
          (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap A A'))
          ((Scheme.Modules.pullback (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap A
            A'))).obj F)).cechDiff,
      ∀ (x : (𝒱.sectionsOf π F).M0 × (𝒱.sectionsOf π F).M1)
        (hx : (1 : A') ⊗ₜ[A] x ∈ LinearMap.ker ((𝒱.sectionsOf π F).cechDiff.baseChange A')),
        (κ ⟨(1 : A') ⊗ₜ[A] x, hx⟩).1 =
          ((((Scheme.Modules.pullbackPushforwardAdjunction
              (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap A A'))).unit.app F).app
                𝒱.U0).hom x.1,
           (((Scheme.Modules.pullbackPushforwardAdjunction
              (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap A A'))).unit.app F).app
                𝒱.U1).hom x.2) := by
  classical
  set S := 𝒱.sectionsOf π F with hS
  set fK := Limits.pullback.fst π (specMap A A') with hfK
  set FK : (Limits.pullback π (specMap A A')).Modules := (Scheme.Modules.pullback fK).obj F with hFK
  set SK := (𝒱.pullback π A').sectionsOf (Limits.pullback.snd π (specMap A A')) FK with hSK
  let η := (Scheme.Modules.pullbackPushforwardAdjunction fK).unit.app F
  let := moduleSectionsOfHom π F 𝒱.U0
  let := moduleSectionsOfHom π F 𝒱.U1
  let := moduleSectionsOfHom π F (𝒱.U0 ⊓ 𝒱.U1)
  let := moduleSectionsOfHom (Limits.pullback.snd π (specMap A A')) FK (fK ⁻¹ᵁ 𝒱.U0)
  let := moduleSectionsOfHom (Limits.pullback.snd π (specMap A A')) FK (fK ⁻¹ᵁ 𝒱.U1)
  let := moduleSectionsOfHom (Limits.pullback.snd π (specMap A A')) FK (fK ⁻¹ᵁ (𝒱.U0 ⊓ 𝒱.U1))
  obtain ⟨ε0, hε0⟩ := exists_linearEquiv_sections_baseChange_of_locallyTrivial π F htriv 𝒱.U0
    𝒱.isAffineOpen_U0 A'
  obtain ⟨ε1, hε1⟩ := exists_linearEquiv_sections_baseChange_of_locallyTrivial π F htriv 𝒱.U1
    𝒱.isAffineOpen_U1 A'
  obtain ⟨ε01, hε01⟩ := exists_linearEquiv_sections_baseChange_of_locallyTrivial π F htriv (𝒱.U0 ⊓
    𝒱.U1)
    𝒱.isAffineOpen_inf A'
  let e0 : A' ⊗[A] (S.M0 × S.M1) ≃ₗ[A'] (SK.M0 × SK.M1) :=
    (TensorProduct.prodRight A A' A' S.M0 S.M1).trans (ε0.prodCongr ε1)
  let e1 : A' ⊗[A] S.M01 ≃ₗ[A'] SK.M01 := ε01
  have hr0 : ∀ s : S.M0, SK.r0 (ε0 ((1 : A') ⊗ₜ[A] s)) = ε01 ((1 : A') ⊗ₜ[A] (S.r0 s)) := by
    intro s
    exact (congrArg SK.r0 (hε0 s)).trans
      ((Hom.app_presheaf_map η (homOfLE inf_le_left) s).symm.trans (hε01 (S.r0 s)).symm)
  have hr1 : ∀ s : S.M1, SK.r1 (ε1 ((1 : A') ⊗ₜ[A] s)) = ε01 ((1 : A') ⊗ₜ[A] (S.r1 s)) := by
    intro s
    exact (congrArg SK.r1 (hε1 s)).trans
      ((Hom.app_presheaf_map η (homOfLE inf_le_right) s).symm.trans (hε01 (S.r1 s)).symm)
  have he0 : ∀ (s0 : S.M0) (s1 : S.M1),
      e0 ((1 : A') ⊗ₜ[A] (s0, s1)) = (ε0 ((1 : A') ⊗ₜ[A] s0), ε1 ((1 : A') ⊗ₜ[A] s1)) := by
    intro s0 s1
    simp only [e0]
    rfl
  have hcomm : SK.cechDiff ∘ₗ e0.toLinearMap = e1.toLinearMap ∘ₗ S.cechDiff.baseChange A' := by
    refine LinearMap.ext fun x => ?_
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add] at hx hy ⊢; rw [hx, hy]
    | tmul k x => ?_
    obtain ⟨s0, s1⟩ := x
    have hk : ∀ {N : Type u} [AddCommGroup N] [Module A N] (y : N),
        (k ⊗ₜ[A] y : A' ⊗[A] N) = k • ((1 : A') ⊗ₜ[A] y) := fun y => by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
    rw [hk, _root_.map_smul, _root_.map_smul, _root_.map_smul, _root_.map_smul]
    congr 1
    have he1 : ∀ y, e1 y = ε01 y := fun _ => rfl
    rw [he0, he1, LinearMap.baseChange_tmul]
    erw [TwoChartCech.Sections.cechDiff_apply, TwoChartCech.Sections.cechDiff_apply]
    erw [TensorProduct.tmul_sub, hr0, hr1]
    exact (map_sub ε01 _ _).symm
  have hmem : ∀ y, y ∈ LinearMap.ker (S.cechDiff.baseChange A') ↔ e0 y ∈ LinearMap.ker SK.cechDiff
    := by
    intro y
    rw [LinearMap.mem_ker, LinearMap.mem_ker]
    have h1 : SK.cechDiff (e0 y) = e1 (S.cechDiff.baseChange A' y) :=
      congrArg (fun φ : _ →ₗ[A'] _ => φ y) hcomm
    rw [h1]
    exact ⟨fun h => by rw [h, map_zero], fun h => e1.injective (by rw [h, map_zero])⟩
  let κ₀ : LinearMap.ker (S.cechDiff.baseChange A') →ₗ[A'] LinearMap.ker SK.cechDiff :=
    (e0.toLinearMap ∘ₗ (LinearMap.ker (S.cechDiff.baseChange A')).subtype).codRestrict _
      (fun y => (hmem y.1).mp y.2)
  have hκ₀ : Function.Bijective κ₀ := by
    refine ⟨fun y z h => Subtype.ext (e0.injective (congrArg Subtype.val h)), fun z => ?_⟩
    refine ⟨⟨e0.symm z.1, (hmem _).mpr (by rw [LinearEquiv.apply_symm_apply]; exact z.2)⟩, ?_⟩
    exact Subtype.ext (e0.apply_symm_apply z.1)
  refine ⟨fun hs => ?_, LinearEquiv.ofBijective κ₀ hκ₀, fun x hx => ?_⟩
  · have hd : ∀ y, S.cechDiff.baseChange A' y = e1.symm (SK.cechDiff (e0 y)) := fun y => by
      have h1 : SK.cechDiff (e0 y) = e1 (S.cechDiff.baseChange A' y) :=
        congrArg (fun φ : _ →ₗ[A'] _ => φ y) hcomm
      rw [h1, LinearEquiv.symm_apply_apply]
    intro z
    obtain ⟨w, hw⟩ := hs (e1 z)
    exact ⟨e0.symm w, by rw [hd, LinearEquiv.apply_symm_apply, hw, LinearEquiv.symm_apply_apply]⟩
  obtain ⟨s0, s1⟩ := x
  rw [LinearEquiv.ofBijective_apply]
  change e0 ((1 : A') ⊗ₜ[A] (s0, s1)) = _
  exact (he0 s0 s1).trans (congrArg₂ Prod.mk (hε0 s0) (hε1 s1))


theorem isIso_fromTildeΓ_pullback_pushforward (F : X.Modules)
    (hF : IsIso (Scheme.Modules.fromTildeΓ (R := .of A) ((pushforward π).obj F))) :
    IsIso (Scheme.Modules.fromTildeΓ (R := .of A')
      ((Scheme.Modules.pullback (Spec.map (φA (A := A) A'))).obj ((pushforward π).obj F))) := by
  rw [isIso_fromTildeΓ_iff]
  let H : ModuleCat A := ΓMod ((pushforward π).obj F)
  let e1 := asIso (Scheme.Modules.fromTildeΓ (R := .of A) ((pushforward π).obj F))
  let e2 : (Scheme.Modules.pullback (Spec.map (φA (A := A) A'))).obj (tilde H) ≅
      tilde ((ModuleCat.extendScalars (φA (A := A) A').hom).obj H) := tilde.pullbackSpecIso (φA (A
        := A) A') H
  refine ⟨(ModuleCat.extendScalars (φA (A := A) A').hom).obj H, ⟨?_⟩⟩
  exact e2.symm ≪≫ (Scheme.Modules.pullback (Spec.map (φA (A := A) A'))).mapIso e1


theorem affine_core [IsAffine X] (F : X.Modules)
    (htriv : ∀ x : X, ∃ (V : X.Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj F ≅
        SheafOfModules.unit V.toScheme.ringCatSheaf))
        :
    IsIso (Scheme.Modules.baseChangeHom
      (Limits.pullback.condition (f := π) (g := Scheme.TwoAffineOpenCover.specMap A A')) F) := by
  set ψ := Scheme.TwoAffineOpenCover.specMap A A' with hψ
  set fA := Limits.pullback.fst π ψ
  set sA := Limits.pullback.snd π ψ
  set FA := (Scheme.Modules.pullback fA).obj F
  let 𝒱 : X.TwoAffineOpenCover :=
    { U0 := ⊤, U1 := ⊤, isAffineOpen_U0 := isAffineOpen_top X,
      isAffineOpen_U1 := isAffineOpen_top X,
      sup_eq_top := sup_idem _, isAffineOpen_inf := by rw [inf_idem]; exact isAffineOpen_top X }
  have hsrc : IsIso (Scheme.Modules.fromTildeΓ (R := .of A') ((Scheme.Modules.pullback ψ).obj
    ((pushforward π).obj F))) :=
    isIso_fromTildeΓ_pullback_pushforward π A' F
      (isIso_fromTildeGamma_pushforward_of_locallyTrivial π 𝒱 F htriv)
  have htrivA : ∀ x : (Limits.pullback π ψ : Scheme.{u}), ∃ (V : (Limits.pullback π ψ).Opens), x ∈
    V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj FA ≅ SheafOfModules.unit V.toScheme.ringCatSheaf)
        :=
    ((⟨htriv⟩ : Scheme.Modules.IsInvertible F).pullback fA).exists_trivialization
  have htgt : IsIso (Scheme.Modules.fromTildeΓ (R := .of A') ((pushforward sA).obj FA)) :=
    isIso_fromTildeGamma_pushforward_of_locallyTrivial sA (𝒱.pullback π A') FA htrivA
  have key : IsIso ((moduleSpecΓFunctor (R := .of A')).map
      (Scheme.Modules.baseChangeHom (Limits.pullback.condition (f := π) (g := ψ)) F)) := by
    classical
    set β := Scheme.Modules.baseChangeHom (Limits.pullback.condition (f := π) (g := ψ)) F with hβ
    obtain ⟨σ, hσ⟩ := exists_linearEquiv_tensor_ΓMod_pullback A' ((pushforward π).obj F)
      (isIso_fromTildeGamma_pushforward_of_locallyTrivial π 𝒱 F htriv)
    let := moduleSectionsOfHom π F ⊤
    let := moduleSectionsOfHom sA FA ⊤
    let := moduleSectionsOfHom sA FA (fA ⁻¹ᵁ ⊤)
    obtain ⟨e, he⟩ := exists_linearEquiv_sections_baseChange_of_locallyTrivial π F htriv ⊤
      (isAffineOpen_top X) A'
    let gX : ΓMod ((pushforward π).obj F) ≃ₗ[A] Γ(F, ⊤) := globalSectionsEquiv π F
    let gP : ΓMod ((pushforward sA).obj FA) ≃ₗ[A'] Γ(FA, ⊤) :=
      globalSectionsEquiv sA FA
    let Γβ : ΓMod ((Scheme.Modules.pullback ψ).obj ((pushforward π).obj F)) →ₗ[A'] ΓMod
      ((pushforward sA).obj FA) :=
      ((moduleSpecΓFunctor (R := .of A')).map β).hom
    let L₁ : A' ⊗[A] (ΓMod ((pushforward π).obj F)) →ₗ[A'] Γ(FA, ⊤) :=
      gP.toLinearMap ∘ₗ Γβ ∘ₗ σ.toLinearMap
    let L₂ : A' ⊗[A] (ΓMod ((pushforward π).obj F)) →ₗ[A'] Γ(FA, fA ⁻¹ᵁ ⊤) :=
      e.toLinearMap ∘ₗ (LinearEquiv.baseChange A A' _ _ gX).toLinearMap
    have hL : ∀ x, (L₁ x : Γ(FA, ⊤)) = (L₂ x : Γ(FA, fA ⁻¹ᵁ ⊤)) := by
      intro x
      induction x using TensorProduct.inductionOn with
      | add x y hx hy => simp only [map_add]; rw [hx, hy]; rfl
      | tmul a' m => ?_
      have hk : (a' ⊗ₜ[A] m : A' ⊗[A] (ΓMod ((pushforward π).obj F))) = a' • ((1 : A') ⊗ₜ[A] m) :=
        by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [hk, _root_.map_smul, _root_.map_smul]
      congr 1
      have hR : (L₂ ((1 : A') ⊗ₜ[A] m) : Γ(FA, fA ⁻¹ᵁ ⊤)) =
          (((pullbackPushforwardAdjunction fA).unit.app F).app ⊤).hom m := by
        change e ((LinearEquiv.baseChange A A' _ _ gX) ((1 : A') ⊗ₜ[A] m)) = _
        exact (congrArg e (LinearEquiv.baseChange_tmul (R := A) (A := A')
          (M := ΓMod ((pushforward π).obj F)) (N := Γ(F, ⊤)) (e := gX) 1 m)).trans
          (he (gX m))
      have hLft : (L₁ ((1 : A') ⊗ₜ[A] m) : Γ(FA, ⊤)) =
          (((pullbackPushforwardAdjunction fA).unit.app F).app ⊤).hom m := by
        change gP (Γβ (σ ((1 : A') ⊗ₜ[A] m))) = _
        rw [hσ m]
        exact baseChangeHom_app_top_unit π ψ sA fA
          (Limits.pullback.condition (f := π) (g := ψ)) F m
      exact hLft.trans hR.symm
    have h2 : Function.Bijective L₂ := e.bijective.comp (LinearEquiv.baseChange A A' _ _
      gX).bijective
    have hΓβ' : ∀ x, Γβ x = gP.symm (L₂ (σ.symm x)) := fun x => by
      have hx := hL (σ.symm x)
      simp only [L₁, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
        LinearEquiv.apply_symm_apply] at hx
      rw [← hx, LinearEquiv.symm_apply_apply]
    have hbij : Function.Bijective Γβ := by
      have hfun : (Γβ : _ → _) = gP.symm ∘ L₂ ∘ σ.symm := funext hΓβ'
      rw [hfun]
      exact gP.symm.bijective.comp (h2.comp σ.symm.bijective)
    exact (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  exact isIso_of_isIso_moduleSpecΓFunctor_map hsrc htgt _ key

end main

end AlgebraicGeometry.Scheme.Modules

open _root_.AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules in
theorem _root_.AlgebraicGeometry.Scheme.Modules.isIso_baseChangeHom_of_isAffineHom
    {X T X' T' : Scheme.{u}} {π : X ⟶ T} {ψ : T' ⟶ T} {π' : X' ⟶ T'} {g' : X' ⟶ X}
    (hcart : IsPullback g' π' π ψ) [IsAffineHom π] (F : X.Modules)
    (htriv : ∀ x : X, ∃ (V : X.Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj F ≅
        SheafOfModules.unit V.toScheme.ringCatSheaf))
        :
    IsIso (Scheme.Modules.baseChangeHom hcart.w F) := by
  refine Scheme.Modules.isIso_baseChangeHom_of_forall_exists_isPullback hcart F ?_
  intro y
  obtain ⟨W, hW, hyW, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp T.isBasis_affineOpens
    (show ψ.base y ∈ (⊤ : T.Opens) from trivial)
  obtain ⟨W', hW', hyW', hle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp T'.isBasis_affineOpens
    (show y ∈ ψ ⁻¹ᵁ W from hyW)
  change IsAffineOpen W at hW
  change IsAffineOpen W' at hW'
  let algW : Algebra Γ(T, W) Γ(T', W') := (ψ.appLE W W' hle).hom.toAlgebra
  have hφ : (hW'.isoSpec.symm.hom ≫ Scheme.Opens.ι W') ≫ ψ =
      Scheme.TwoAffineOpenCover.specMap Γ(T, W) Γ(T', W') ≫ hW.isoSpec.symm.hom ≫ Scheme.Opens.ι W
        := by
    rw [Iso.symm_hom, Iso.symm_hom, IsAffineOpen.isoSpec_inv_ι, IsAffineOpen.isoSpec_inv_ι]
    change _ = Spec.map (CommRingCat.ofHom (ψ.appLE W W' hle).hom) ≫ hW.fromSpec
    rw [CommRingCat.ofHom_hom]
    exact (IsAffineOpen.SpecMap_appLE_fromSpec ψ hW hW' hle).symm
  have hu : IsPullback (Limits.pullback.fst π hW.fromSpec) (Limits.pullback.snd π hW.fromSpec) π
      (hW.isoSpec.symm.hom ≫ Scheme.Opens.ι W) := by
    rw [Iso.symm_hom, IsAffineOpen.isoSpec_inv_ι]
    exact IsPullback.of_hasPullback _ _
  have : IsAffineHom (Limits.pullback.snd π hW.fromSpec) := inferInstance
  have : IsAffine (Limits.pullback π hW.fromSpec) := isAffine_of_isAffineHom (Limits.pullback.snd π
    hW.fromSpec)
  refine ⟨W, W', hyW', Spec (CommRingCat.of Γ(T, W)), Spec (CommRingCat.of Γ(T', W')),
    Limits.pullback π hW.fromSpec,
    Limits.pullback (Limits.pullback.snd π hW.fromSpec) (Scheme.TwoAffineOpenCover.specMap Γ(T, W)
      Γ(T', W')),
    hW.isoSpec.symm, hW'.isoSpec.symm, Scheme.TwoAffineOpenCover.specMap Γ(T, W) Γ(T', W'), hφ,
    Limits.pullback.snd π hW.fromSpec, Limits.pullback.fst π hW.fromSpec, hu,
    Limits.pullback.snd _ _, Limits.pullback.fst _ _, IsPullback.of_hasPullback _ _, ?_⟩
  exact affine_core (Limits.pullback.snd π hW.fromSpec) Γ(T', W')
    ((Scheme.Modules.pullback (Limits.pullback.fst π hW.fromSpec)).obj F)
    (((⟨htriv⟩ : Scheme.Modules.IsInvertible F).pullback (Limits.pullback.fst π
      hW.fromSpec)).exists_trivialization)
end AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_isIso_baseChangeHom_of_isAffineHom
end ProofImplementation

attribute [-instance] TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module
  TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing
  TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module
  TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower
  TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing
  TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module
  TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup
  TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower
  CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup
  CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup
  CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite
  CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free
  AlgebraicGeometry.Scheme.Hom.opensMapFinal
  AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid
  AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited
attribute [-simp] AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq
  TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq
  TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec
  TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec
  TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec
  CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app
  AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec
  AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq
  NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd
  NeronModelInfra.genericFibreRestrict_coe_comp_fst TwoChartCech.Mumford.dK_apply
  TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply
  TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply
