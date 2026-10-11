/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_exists_forall_geomFibreH0Finrank_tensorPow_eq_hilbertFunctionOf_of_point_geomFibre.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Picard.RelativeGroupLaw
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.SchemeTheory.Modules.ProjectivePresentation
import Nyll.AlgebraicCurves.Geometry.Picard.PolarisedAbelianScheme
import Nyll.AlgebraicCurves.Foundations.Algebra.SheafOfModules_MonoidalV2
import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Nyll.AlgebraicCurves.Hilbert.Functor.Basic
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesPullbackMonoidalV2
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_ProjPresentation_exists_projPresentation_pullback_sigma_eq_toProj_eq
import Nyll.AlgebraicCurves.Hilbert.exists_forall_geomFibreH0Finrank_tensorPow_eq_hilbertFunctionOf_of_point
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_geomFibreH0Finrank_eq_of_isPullback
import Nyll.SchemeTheory.ProjectiveSpace.StandardChartsBaseChange
import Nyll.AlgebraicCurves.Geometry.Projective.ProjSpace_restrictFun_app_app_awayToSection_eq_app_awayToSection_map

/-!
# exists forall geom Fibre H0 Finrank tensor Pow eq hilbert Function Of of point geom Fibre
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace exists_forall_geomFibreH0Finrank_tensorPow_eq_hilbertFunctionOf_of_point_geomFibre
attribute [-instance] AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx
attribute [-simp] AlgebraicGeometry.Scheme.Modules.tensorPow_zero
  AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.OModulePresheaf.prod_obj
  AlgebraicGeometry.OModulePresheaf.restrOpen_obj
  AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq
  AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj
  AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app
  AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj
  AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U
  AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq
  AlgebraicGeometry.OModulePresheaf.Hom.id_app
  AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply
  AlgebraicGeometry.OModulePresheaf.AffHom.comp_app
  AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe
  AlgebraicGeometry.OModulePresheaf.AffHom.id_app
  AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app
  AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq
  AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq
  AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply
  AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq
  AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq
  AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right
  AlgebraicGeometry.Scheme.Modules.map_unitSection
  AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply
  AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left

open MvPolynomial CategoryTheory CategoryTheory.Limits AlgebraicGeometry
  AlgebraicGeometry.HilbertFunctor NeronModelInfra GoodReductionJacobian

open _root_.CategoryTheory.MonoidalCategory

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace F3Sol

universe u

theorem smul_map_eq_of_eq {X : Scheme.{u}} (M : X.Modules) {W W' : X.Opens} (ρ : W' ⟶ W) (e : W =
  W')
    (s t : Γ(M, ⊤)) (g : Γ(X, W))
    (h : g • M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op s = M.presheaf.map (homOfLE (le_top : W ≤
      ⊤)).op t) :
    (X.presheaf.map ρ.op g) • M.presheaf.map (homOfLE (le_top : W' ≤ ⊤)).op s =
      M.presheaf.map (homOfLE (le_top : W' ≤ ⊤)).op t := by
  subst e
  have hρ : ρ = 𝟙 _ := Subsingleton.elim _ _
  rw [hρ, op_id, CategoryTheory.Functor.map_id]
  exact h

theorem descend {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] {X : Scheme.{u}}
    {f₁ : X ⟶ Spec (.of R)} {M : X.Modules} {N : ℕ} (𝔓 : M.ProjPresentation f₁ N)
    (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A))
    (hφ : 𝔓.toProj = φ ≫ ProjSpace.map R A N) :
    ∃ 𝔓' : M.ProjPresentation (φ ≫ ProjSpace.π A N) N, (∀ i, 𝔓'.σ i = 𝔓.σ i) ∧ 𝔓'.toProj = φ := by
  obtain ⟨σ, toProj, hπ, frame, ratio⟩ := 𝔓
  dsimp only at hφ
  subst hφ
  have hpre : ∀ i : Fin (N + 1),
      (φ ≫ ProjSpace.map R A N) ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1))
        R) (MvPolynomial.X i) =
        φ ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A) (MvPolynomial.X i)
          := by
    intro i
    rw [← ProjSpace.map_preimage_basicOpen_X R A N i]
    rfl
  refine ⟨{ σ := σ
            toProj := φ
            toProj_π := rfl
            frame := ?_
            app_ratio_smul := ?_ }, fun i => rfl, rfl⟩
  · intro i V hV
    exact frame i V (by rw [hpre]; exact hV)
  · intro i j
    have hle : Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A) (MvPolynomial.X
      i) ≤
        ProjSpace.map R A N ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
          (MvPolynomial.X i) :=
      (ProjSpace.map_preimage_basicOpen_X R A N i).symm.le
    have key :=
      AlgebraicGeometry.ProjSpace.restrictFun_app_app_awayToSection_eq_app_awayToSection_map
      (𝟙 _) A (𝟙 _) (ProjSpace.map R A N)
        (by simp) 1 (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X R j) i
      (by simpa using hle)
    have key' : ((Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)).presheaf.map (homOfLE
      hle).op)
        ((ProjSpace.map R A N).app _ (Proj.awayToSection _ (MvPolynomial.X i) (ProjSpace.ratio R N
          i j))) =
        Proj.awayToSection _ (MvPolynomial.X i) (ProjSpace.ratio A N i j) := by
      have k := key
      erw [Scheme.Hom.id_app, Scheme.Hom.id_app] at k
      convert k using 3
      all_goals first
        | rfl
        | (erw [CategoryTheory.id_apply]
           congr 1
           apply HomogeneousLocalization.val_injective
           simp [ProjSpace.ratio, HomogeneousLocalization.Away.val_mk,
             HomogeneousLocalization.val_mk, MvPolynomial.map_X])
    have T := smul_map_eq_of_eq M ((TopologicalSpace.Opens.map φ.base).map (homOfLE hle)) (hpre i)
      (σ i) (σ j) _ (ratio i j)
    convert T using 2
    rw [← key', Scheme.Hom.comp_app]
    have nat0 := Scheme.Hom.naturality φ (homOfLE hle).op
    have h2 := CategoryTheory.ConcreteCategory.congr_hom nat0
      ((ProjSpace.map R A N).app _ (Proj.awayToSection _ (MvPolynomial.X i) (ProjSpace.ratio R N i
        j)))
    rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply] at h2
    refine h2.trans ?_
    rfl

/--
The pullback comparison for iterated tensor powers, transported through the given module
isomorphism.
-/
noncomputable def powIso {X Y : Scheme.{u}} (p : X ⟶ Y) (𝓜 : Y.Modules) (𝓜' : X.Modules)
    (η : (Scheme.Modules.pullback p).obj 𝓜 ≅ 𝓜') :
    ∀ d : ℕ, (Scheme.Modules.pullback p).obj
        (Nat.rec (motive := fun _ => Y.Modules) (𝟙_ Y.Modules) (fun _ M => M ⊗ 𝓜) d) ≅
        Nat.rec (motive := fun _ => X.Modules) (𝟙_ X.Modules) (fun _ M => M ⊗ 𝓜') d
  | 0 => Scheme.Modules.pullbackTensorUnitObjIso p
  | d + 1 => Scheme.Modules.pullbackTensorObjIso p _ 𝓜 ≪≫ (powIso p 𝓜 𝓜' η d ⊗ᵢ η)

end F3Sol

end

end exists_forall_geomFibreH0Finrank_tensorPow_eq_hilbertFunctionOf_of_point_geomFibre
end AlgebraicCurves.Geometry.Schemes.Proofs

namespace AlgebraicGeometry

open MvPolynomial CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry.HilbertFunctor NeronModelInfra GoodReductionJacobian

attribute [local instance] MvPolynomial.gradedAlgebra

open _root_.AlgebraicCurves.Geometry.Schemes.Proofs in
open exists_forall_geomFibreH0Finrank_tensorPow_eq_hilbertFunctionOf_of_point_geomFibre in
open F3Sol in
theorem exists_forall_geomFibreH0Finrank_tensorPow_eq_hilbertFunctionOf_of_point_geomFibre
    (S : Type) [CommRing S] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of S))
    (𝓛X : X.Modules) (hX₁ : Scheme.Modules.IsInvertible 𝓛X)
    {n : ℕ} (𝔓 : Scheme.Modules.ProjPresentation 𝓛X f n)
    (S' : Type) [CommRing S'] (ψ : S →+* S')
    (Z : Scheme.{0}) (ι : Z ⟶ pullback f (Spec.map (CommRingCat.ofHom ψ)))
    (j : pullback f (Spec.map (CommRingCat.ofHom ψ)) ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin
      (n + 1)) S'))
    (hj₂ : (letI : Algebra S S' := ψ.toAlgebra; j ≫ ProjSpace.map S S' n) =
      pullback.fst f (Spec.map (CommRingCat.ofHom ψ)) ≫ 𝔓.toProj)
    (k : Type) [Field k] [IsAlgClosed k] (sk : S' →+* k)
    (P' : Polynomial ℚ) (m' : ℕ) (q : Point k n (hilbertFunctionOf n P' m'))
    (Zk : Scheme.{0}) (ιk : Zk ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)) (hιk :
      IsClosedImmersion ιk)
    (e : Zk ⟶ Z)
    (he₁ : IsPullback e (ιk ≫ ProjSpace.π k n) (ι ≫ pullback.snd f (Spec.map (CommRingCat.ofHom ψ)))
      (Spec.map (CommRingCat.ofHom sk)))
    (he₂ : (letI : Algebra S' k := sk.toAlgebra; ιk ≫ ProjSpace.map S' k n) = e ≫ ι ≫ j)
    (hZk : ∀ d : ℕ, m' ≤ d → ∀ (F : MvPolynomial (Fin (n + 1)) k) (hF : F.IsHomogeneous d),
      (F ∈ q.I ↔ ∀ i : Fin (n + 1),
        (ιk.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X
          i)))
          ((Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X
            i))
            (HomogeneousLocalization.mk
              { deg := d
                num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
                  (MvPolynomial.isHomogeneous_X_pow i d)⟩
                den_mem := ⟨d, rfl⟩ })) = 0)) :
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
      Scheme.Modules.geomFibreH0Finrank (ι ≫ pullback.snd f (Spec.map (CommRingCat.ofHom ψ)))
        (Nat.rec (motive := fun _ => Z.Modules) (𝟙_ Z.Modules)
          (fun _ M => M ⊗ (Scheme.Modules.pullback (ι ≫ pullback.fst f (Spec.map (CommRingCat.ofHom
            ψ)))).obj 𝓛X) d) k sk =
      hilbertFunctionOf n P' m' d := by
  let instSS' : Algebra S S' := ψ.toAlgebra
  let instS'k : Algebra S' k := sk.toAlgebra
  obtain ⟨𝔓a, -, h𝔓a⟩ :=
    Scheme.Modules.ProjPresentation.exists_projPresentation_pullback_sigma_eq_toProj_eq
      (pullback.fst f (Spec.map (CommRingCat.ofHom ψ))) 𝔓
  obtain ⟨𝔓b, -, h𝔓b⟩ := descend 𝔓a j (by rw [h𝔓a]; exact hj₂.symm)
  obtain ⟨𝔓c, -, h𝔓c⟩ :=
    Scheme.Modules.ProjPresentation.exists_projPresentation_pullback_sigma_eq_toProj_eq
      (e ≫ ι) 𝔓b
  obtain ⟨𝔓d, -, h𝔓d⟩ := descend 𝔓c ιk (by rw [h𝔓c, h𝔓b, Category.assoc]; exact he₂.symm)
  have h𝓛k : Scheme.Modules.IsInvertible
      ((Scheme.Modules.pullback (e ≫ ι)).obj
        ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom ψ)))).obj 𝓛X)) :=
    (hX₁.pullback _).pullback _
  obtain ⟨d₀, hd₀⟩ :=
    exists_forall_geomFibreH0Finrank_tensorPow_eq_hilbertFunctionOf_of_point
      n P' m' k q Zk ιk hιk hZk _ h𝓛k 𝔓d h𝔓d
  refine ⟨d₀, fun d hd => ?_⟩
  have η : (Scheme.Modules.pullback e).obj
        ((Scheme.Modules.pullback (ι ≫ pullback.fst f (Spec.map (CommRingCat.ofHom ψ)))).obj 𝓛X) ≅
      (Scheme.Modules.pullback (e ≫ ι)).obj
        ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom ψ)))).obj 𝓛X) :=
    (Scheme.Modules.pullbackComp e (ι ≫ pullback.fst f (Spec.map (CommRingCat.ofHom ψ)))).app 𝓛X ≪≫
      eqToIso (by rw [Category.assoc]) ≪≫
      ((Scheme.Modules.pullbackComp (e ≫ ι) (pullback.fst f (Spec.map (CommRingCat.ofHom ψ)))).app
        𝓛X).symm
  have key := AlgebraicGeometry.Scheme.Modules.geomFibreH0Finrank_eq_of_isPullback sk
    (ι ≫ pullback.snd f (Spec.map (CommRingCat.ofHom ψ))) (ιk ≫ ProjSpace.π k n) e he₁ _ _
    (powIso e _ _ η d) k (RingHom.id k)
  rw [RingHom.id_comp] at key
  rw [← key]
  exact hd₀ d hd
end AlgebraicGeometry
end ProofImplementation

open PresheafOfModules.PullbackMonoidal in
attribute [-instance]
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
  AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback_monoidal
  AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization'
  AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal
  AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.sheafifyPullback_lifting
  AlgebraicGeometry.OModulePresheaf.isScalarTower
  AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder
  AlgebraicGeometry.OModulePresheaf.module
  AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype
  AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx
  AlgebraicGeometry.OModulePresheaf.addCommGroup
  AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx
  AlgebraicGeometry.OModulePresheaf.moduleSections
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
attribute [-instance] TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing
  TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module
  CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module
  CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free
  CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite
  CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.ProjSpace.twistObj.addCommGroup
  AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module
  AlgebraicGeometry.ProjSpace.twistObj.moduleSections
  AlgebraicGeometry.ProjSpace.twistFam.addCommGroup ProjSpaceCech.GradedModule.H.module
  ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd
  ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg
  ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR
  ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup
  ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ
  ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module
  ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup
  ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq
  ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule
  AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx
attribute [-simp] PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app
  AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq
  AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq
  TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq
  TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec
  TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec
  TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec
  CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.mk.injEq
  AlgebraicGeometry.ProjSpace.twistObj.zero_val AlgebraicGeometry.ProjSpace.twistObj.add_val
  AlgebraicGeometry.ProjSpace.twist_res_val AlgebraicGeometry.ProjSpace.twist_smul_val
  AlgebraicGeometry.ProjSpace.twistGradeToObj_val AlgebraicGeometry.ProjSpace.twistObj.smul_val
  AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val
  AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec ProjSpaceCech.GradedModule.mk.injEq
  ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq
  ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.Scheme.Modules.tensorPow_zero
  AlgebraicGeometry.Scheme.Modules.tensorPow_succ
attribute [-simp] AlgebraicGeometry.OModulePresheaf.prod_obj
  AlgebraicGeometry.OModulePresheaf.restrOpen_obj
  AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq
  AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj
  AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app
  AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj
  AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U
  AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq
  AlgebraicGeometry.OModulePresheaf.Hom.id_app
  AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply
  AlgebraicGeometry.OModulePresheaf.AffHom.comp_app
  AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe
  AlgebraicGeometry.OModulePresheaf.AffHom.id_app
  AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app
  AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq
  AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq
  AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply
  AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq
  AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq
  AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right
  AlgebraicGeometry.Scheme.Modules.map_unitSection
  AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply
  AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left
