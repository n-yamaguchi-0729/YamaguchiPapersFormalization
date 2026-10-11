/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_finite_projective_sections_and_exists_linearEquiv_tensorProduct_pullbackLocalSection_of_forall_subsingleton_HSucc.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Nyll.AlgebraicCurves.Cohomology.Sheaves.OModulePresheafOfModules
import Nyll.SchemeTheory.Modules.PullbackLocalSection
import Nyll.AlgebraicCurves.Geometry.Schemes.OrderedAffineCoverComap
import Nyll.SchemeTheory.Cohomology.Cech.TwoChartCech
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.AlgebraicCurves.Foundations.Algebra.Module_Flat_projective_ker_and_bijective_kerBaseChangeHom_of_forall_ker_baseChange_le_range
import Nyll.AlgebraicCurves.Cohomology.Cech.OModulePresheaf_nonempty_cech_baseChange_equiv_of_locallyTrivial
import Nyll.AlgebraicCurves.Cohomology.Sheaves.OModulePresheaf_flat_cochain_ofModules_of_locallyTrivial
import Nyll.SchemeTheory.Cohomology.Sheaves.OModulePresheaf_d_comp_d
import Nyll.AlgebraicCurves.Cohomology.Cech.OModulePresheaf_cechFinite_ofModules_of_locallyTrivial
import Nyll.AlgebraicCurves.Cohomology.Sheaves.OModulePresheaf_exists_cochain_baseChange_equiv_of_locallyTrivial
import Nyll.AlgebraicCurves.Cohomology.Sheaves.OModulePresheaf_d_zero_ofModules_eq_zero_iff_existsUnique
import Nyll.AlgebraicCurves.Cohomology.Sheaves.OModulePresheaf_isQuasicoherent_ofModules_of_locallyTrivial
import Nyll.AlgebraicCurves.Cohomology.Cech.OModulePresheaf_nonempty_cechEquiv_ofModules_of_isQuasicoherent_of_isSeparated

/-!
# Scheme Modules finite projective sections and exists linear Equiv tensor Product pullback
Local Section of forall subsingleton HSucc
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Proofs.ProjectiveSectionsBaseChange
attribute [-instance] AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero
  AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower
  AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ
  AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ
  AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp
  AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ
  AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul
  AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower
  AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul
  AlgebraicGeometry.OModulePresheaf.Leray.biC_module
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I
  DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II
  DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I
  AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed
  AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU
  AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway
  AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU
  AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial
  ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup
  ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg
  ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid
  ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule
  ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero
attribute [-instance] ProjSpaceCech.GradedModule.Presentation.fJ
  ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module
  ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup
  ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq
  ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule
attribute [-simp] AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app
  AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj
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
  AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U
  AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq
  AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq
  DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq
  DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec
  DoubleComplex.SubQuot.mk.injEq
attribute [-simp] AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec
  AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq
  AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq
  ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq
  ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Hom.mk.injEq

universe u

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace TensorProduct

namespace P2mSectionsBaseChangeH0

section Cover

/-- A finite ordered affine cover extracted from compactness of the scheme. -/
def coverOfCompact (X : Scheme.{u}) [CompactSpace X] : X.OrderedAffineCover :=
  let 𝒰 := X.affineCover.finiteSubcover
  { ι := 𝒰.I₀
    instFintype := inferInstance
    instLinearOrder := LinearOrder.lift' (Fintype.equivFin 𝒰.I₀) (Fintype.equivFin 𝒰.I₀).injective
    U := fun i => (𝒰.f i).opensRange
    isAffineOpen := fun i => isAffineOpen_opensRange (𝒰.f i)
    iSup_eq_top := 𝒰.iSup_opensRange }

end Cover

section H0

variable {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) (M : V.Modules)
  (K : V.OrderedAffineCover)

/-- Restricts a global section to the degree-zero Cech cochain on the ordered affine cover. -/
def toCochain :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π M ⊤
    Γ(M, ⊤) →ₗ[R] (OModulePresheaf.ofModules π M).cochain K 0 :=
  let := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π M ⊤
  LinearMap.pi fun s => (OModulePresheaf.ofModules π M).res (le_top : K.inter s ≤ ⊤)

theorem toCochain_apply (x : Γ(M, ⊤)) (s : K.Idx 0) :
    toCochain π M K x s = M.presheaf.map (homOfLE (le_top : K.inter s ≤ ⊤)).op x := rfl

theorem toCochain_apply' (x : Γ(M, ⊤)) (s : K.Idx 0) :
    toCochain π M K x s = (OModulePresheaf.ofModules π M).res (le_top : K.inter s ≤ ⊤)
      (show (OModulePresheaf.ofModules π M).obj ⊤ from x) := rfl

theorem d_toCochain (x : Γ(M, ⊤)) :
    (OModulePresheaf.ofModules π M).d K 0 (toCochain π M K x) = 0 := by
  funext s
  rw [OModulePresheaf.d_apply, Fin.sum_univ_two]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul, toCochain_apply',
    Pi.zero_apply]
  have h0 := (OModulePresheaf.ofModules π M).res_res
    (K.inter_le_inter_face s (0 : Fin 2)) (le_top : K.inter (K.face s 0) ≤ ⊤)
    (show (OModulePresheaf.ofModules π M).obj ⊤ from x)
  have h1 := (OModulePresheaf.ofModules π M).res_res
    (K.inter_le_inter_face s (1 : Fin 2)) (le_top : K.inter (K.face s 1) ≤ ⊤)
    (show (OModulePresheaf.ofModules π M).obj ⊤ from x)
  exact (congrArg₂
    (fun a b : (OModulePresheaf.ofModules π M).obj (K.inter s) => a + -b) h0 h1).trans
      (add_neg_cancel _)

theorem toCochain_mem (x : Γ(M, ⊤)) : toCochain π M K x ∈ (OModulePresheaf.ofModules π M).H0 K :=
  d_toCochain π M K x

theorem toCochain_injective : Function.Injective (toCochain π M K) := by
  intro x y hxy
  obtain ⟨z, -, huniq⟩ := (OModulePresheaf.d_zero_ofModules_eq_zero_iff_existsUnique π M K _).mp
    (d_toCochain π M K x)
  exact (huniq x fun s => rfl).trans (huniq y fun s => by rw [hxy]; rfl).symm

theorem exists_toCochain_eq (c : (OModulePresheaf.ofModules π M).cochain K 0)
    (hc : c ∈ (OModulePresheaf.ofModules π M).H0 K) : ∃ x : Γ(M, ⊤), toCochain π M K x = c := by
  obtain ⟨x, hx, -⟩ := (OModulePresheaf.d_zero_ofModules_eq_zero_iff_existsUnique π M K c).mp hc
  exact ⟨x, funext fun s => (hx s).symm⟩

/-- Identifies global sections with degree-zero Cech cocycles on the affine cover. -/
def sectionsEquivH0 :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π M ⊤
    Γ(M, ⊤) ≃ₗ[R] (OModulePresheaf.ofModules π M).H0 K :=
  let := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π M ⊤
  LinearEquiv.ofBijective (LinearMap.codRestrict ((OModulePresheaf.ofModules π M).H0 K)
      (toCochain π M K) (toCochain_mem π M K))
    ⟨fun x y h => toCochain_injective π M K (congrArg Subtype.val h),
     fun ⟨c, hc⟩ => by
      obtain ⟨x, rfl⟩ := exists_toCochain_eq π M K c hc
      exact ⟨x, rfl⟩⟩

theorem coe_sectionsEquivH0 (x : Γ(M, ⊤)) :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π M ⊤
    ((sectionsEquivH0 π M K x : (OModulePresheaf.ofModules π M).H0 K) :
      (OModulePresheaf.ofModules π M).cochain K 0) = toCochain π M K x := rfl

end H0

section Unit

variable {X Y : Scheme.{u}} (p : Y ⟶ X)

lemma app_map {N N' : X.Modules} (φ : N ⟶ N') {W W' : X.Opens} (i : W' ⟶ W) (n : Γ(N, W)) :
    φ.app W' (N.presheaf.map i.op n) = N'.presheaf.map i.op (φ.app W n) := by
  have h := φ.mapPresheaf.naturality i.op
  exact ConcreteCategory.congr_hom h n

lemma map_map (N : X.Modules) {W W' W'' : X.Opens} (i : W' ⟶ W) (j : W'' ⟶ W') (k : W'' ⟶ W)
    (n : Γ(N, W)) :
    N.presheaf.map j.op (N.presheaf.map i.op n) = N.presheaf.map k.op n := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  obtain rfl : k = j ≫ i := Subsingleton.elim _ _
  rfl

/-- The section of the pullback module obtained from the unit of pullback and pushforward. -/
abbrev unitApp (M : X.Modules) (U : X.Opens) (e : Γ(M, U)) :
    Γ((Scheme.Modules.pullback p).obj M, p ⁻¹ᵁ U) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M).app U e

lemma unitApp_map (M : X.Modules) {U W : X.Opens} (i : W ⟶ U) (k : p ⁻¹ᵁ W ⟶ p ⁻¹ᵁ U) (e : Γ(M, U))
  :
    unitApp p M W (M.presheaf.map i.op e)
      = ((Scheme.Modules.pullback p).obj M).presheaf.map k.op (unitApp p M U e) := by
  have h := app_map ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M) i e
  refine h.trans ?_
  obtain rfl : k = (Opens.map p.base).map i := Subsingleton.elim _ _
  rfl

end Unit

section KerTransfer

variable {R : Type u} [CommRing R]
variable {K0 K1 C0 C1 : Type u} [AddCommGroup K0] [Module R K0] [AddCommGroup K1] [Module R K1]
  [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]

theorem lid_baseChange_apply (f : C0 →ₗ[R] C1) (x : R ⊗[R] C0) :
    TensorProduct.lid R C1 (f.baseChange R x) = f (TensorProduct.lid R C0 x) := by
  induction x using TensorProduct.inductionOn with
  | tmul r m =>
      rw [LinearMap.baseChange_tmul, TensorProduct.lid_tmul, TensorProduct.lid_tmul, map_smul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

variable (dK : K0 →ₗ[R] K1) (d : C0 →ₗ[R] C1) (ι0 : K0 →ₗ[R] C0) (ι1 : K1 →ₗ[R] C1)
  (comm : d ∘ₗ ι0 = ι1 ∘ₗ dK)

theorem tmul_one_mem_ker {N P : Type u} [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
    (f : N →ₗ[R] P) (x : LinearMap.ker f) :
    (1 : R) ⊗ₜ[R] (x : N) ∈ LinearMap.ker (f.baseChange R) := by
  rw [LinearMap.mem_ker, LinearMap.baseChange_tmul, LinearMap.mem_ker.mp x.2, tmul_zero]

theorem kerMap_bijective (h : Function.Bijective (TwoChartCech.kerMapBaseChange dK d ι0 ι1 comm R))
  :
    Function.Bijective (TwoChartCech.kerMap dK d ι0 ι1 comm) := by
  constructor
  · intro x y hxy
    have hv : ι0 x = ι0 y := congrArg Subtype.val hxy
    have h1 : TwoChartCech.kerMapBaseChange dK d ι0 ι1 comm R ⟨_, tmul_one_mem_ker dK x⟩
        = TwoChartCech.kerMapBaseChange dK d ι0 ι1 comm R ⟨_, tmul_one_mem_ker dK y⟩ := by
      apply Subtype.ext
      change ι0.baseChange R ((1 : R) ⊗ₜ[R] (x : K0)) = ι0.baseChange R ((1 : R) ⊗ₜ[R] (y : K0))
      rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, hv]
    have h2 := congrArg (fun z => TensorProduct.lid R K0 (Subtype.val z)) (h.1 h1)
    simp only [TensorProduct.lid_tmul, one_smul] at h2
    exact Subtype.ext h2
  · intro y
    obtain ⟨x, hx⟩ := h.2 ⟨_, tmul_one_mem_ker d y⟩
    have hxv : ι0.baseChange R (x : R ⊗[R] K0) = (1 : R) ⊗ₜ[R] (y : C0) := congrArg Subtype.val hx
    refine ⟨⟨TensorProduct.lid R K0 x, ?_⟩, Subtype.ext ?_⟩
    · rw [LinearMap.mem_ker, ← lid_baseChange_apply, LinearMap.mem_ker.mp x.2, map_zero]
    · change ι0 (TensorProduct.lid R K0 x) = y
      rw [← lid_baseChange_apply, hxv, TensorProduct.lid_tmul, one_smul]

end KerTransfer

section KerOfEquiv

variable {R : Type u} [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
variable {C0 C1 D0 D1 : Type u} [AddCommGroup C0] [Module A C0] [AddCommGroup C1] [Module A C1]
  [AddCommGroup D0] [Module A D0] [AddCommGroup D1] [Module A D1]

/-- The equivalence of kernels induced by a commuting square of linear equivalences. -/
def kerEquivOfEquiv (d : C0 →ₗ[A] C1) (d' : D0 →ₗ[A] D1) (E0 : C0 ≃ₗ[A] D0) (E1 : C1 ≃ₗ[A] D1)
    (h : E1.toLinearMap ∘ₗ d = d' ∘ₗ E0.toLinearMap) :
    LinearMap.ker d ≃ₗ[A] LinearMap.ker d' :=
  (LinearEquiv.ofEq _ _ (by
    rw [← LinearEquiv.ker_comp E1 d, h, LinearMap.ker_comp])).trans (E0.ofSubmodule' (LinearMap.ker
      d'))

theorem coe_kerEquivOfEquiv (d : C0 →ₗ[A] C1) (d' : D0 →ₗ[A] D1) (E0 : C0 ≃ₗ[A] D0) (E1 : C1 ≃ₗ[A]
  D1)
    (h : E1.toLinearMap ∘ₗ d = d' ∘ₗ E0.toLinearMap) (x : LinearMap.ker d) :
    (kerEquivOfEquiv d d' E0 E1 h x : D0) = E0 x := rfl

theorem coe_kerEquivOfEquiv_symm (d : C0 →ₗ[A] C1) (d' : D0 →ₗ[A] D1) (E0 : C0 ≃ₗ[A] D0)
    (E1 : C1 ≃ₗ[A] D1) (h : E1.toLinearMap ∘ₗ d = d' ∘ₗ E0.toLinearMap) (y : LinearMap.ker d') :
    ((kerEquivOfEquiv d d' E0 E1 h).symm y : C0) = E0.symm y := by
  set x := (kerEquivOfEquiv d d' E0 E1 h).symm y with hx
  have hy : (kerEquivOfEquiv d d' E0 E1 h) x = y := LinearEquiv.apply_symm_apply _ _
  have hcoe : E0 (x : C0) = (y : D0) := by
    rw [← coe_kerEquivOfEquiv d d' E0 E1 h x, hy]
  rw [← hcoe, LinearEquiv.symm_apply_apply]

end KerOfEquiv

end P2mSectionsBaseChangeH0

namespace Engine19


open _root_.AlgebraicCurves.Cohomology.Proofs.ProjectiveSectionsBaseChange.P2mSectionsBaseChangeH0
open _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover


theorem isEmpty_idx {X : Scheme.{u}} (𝒰 : X.OrderedAffineCover) (i : ℕ) (hi : Fintype.card 𝒰.ι < i
  + 1) :
    IsEmpty (𝒰.Idx i) := by
  refine ⟨fun s => ?_⟩
  have h := Fintype.card_le_of_injective s.1 s.2.injective
  rw [Fintype.card_fin] at h
  omega

theorem subsingleton_cochain {R : Type u} [CommRing R] {X : Scheme.{u}} {π : X ⟶ Spec (.of R)}
    (F : OModulePresheaf π) (𝒰 : X.OrderedAffineCover) (i : ℕ) (hi : Fintype.card 𝒰.ι ≤ i) :
    Subsingleton (F.cochain 𝒰 i) := by
  have : IsEmpty (𝒰.Idx i) := isEmpty_idx 𝒰 i (by omega)
  change Subsingleton (∀ s : 𝒰.Idx i, F.obj (𝒰.inter s))
  infer_instance

theorem ker_le_range_of_subsingleton {A : Type u} [CommRing A] {C0 C1 C2 H : Type u}
    [AddCommGroup C0] [Module A C0] [AddCommGroup C1] [Module A C1] [AddCommGroup C2] [Module A C2]
    [AddCommGroup H] [Module A H] [Subsingleton H]
    (d0 : C0 →ₗ[A] C1) (d1 : C1 →ₗ[A] C2) (φ : LinearMap.ker d1 →ₗ[A] H)
    (hφ : LinearMap.ker φ = (LinearMap.range d0).comap (LinearMap.ker d1).subtype) :
    LinearMap.ker d1 ≤ LinearMap.range d0 := by
  intro x hx
  have h1 : (⟨x, hx⟩ : LinearMap.ker d1) ∈ LinearMap.ker φ := by
    rw [LinearMap.mem_ker]; exact Subsingleton.elim _ _
  rw [hφ] at h1
  exact h1

theorem main
    {R : Type u} [CommRing R] [IsNoetherianRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    [IsProper f] [Flat f] (M : X.Modules)
    (htriv : ∀ x : X, ∃ (U : X.Opens), x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.unit U.toScheme.ringCatSheaf))
    (hH : ∀ (K : Type u) [Field K] [Algebra R K],
      ∃ 𝒲 : (Limits.pullback f (Scheme.TwoAffineOpenCover.specMap R K)).OrderedAffineCover, ∀ i : ℕ,
        Subsingleton ((OModulePresheaf.ofModules (Limits.pullback.snd f
          (Scheme.TwoAffineOpenCover.specMap R K))
          ((Scheme.Modules.pullback (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R
            K))).obj M)).HSucc 𝒲 i)) :
    (letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom f M ⊤
     Module.Finite R Γ(M, ⊤) ∧ Module.Projective R Γ(M, ⊤)) ∧
    ∀ (A : Type u) [CommRing A] [Algebra R A],
      letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom f M ⊤
      letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom
        (Limits.pullback.snd f (Scheme.TwoAffineOpenCover.specMap R A))
        ((Scheme.Modules.pullback (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R
          A))).obj M)
        ((Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R A)) ⁻¹ᵁ ⊤)
      ∃ e : A ⊗[R] Γ(M, ⊤) ≃ₗ[A]
          Γ((Scheme.Modules.pullback (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R
            A))).obj M, (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R A)) ⁻¹ᵁ ⊤),
        ∀ (a : A) (m : Γ(M, ⊤)),
          e (a ⊗ₜ[R] m) = a • Scheme.Modules.pullbackLocalSection (Limits.pullback.fst f
            (Scheme.TwoAffineOpenCover.specMap R A)) m := by
  classical
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let 𝒰 := coverOfCompact X
  let F := OModulePresheaf.ofModules f M
  let instM := Scheme.TwoAffineOpenCover.moduleSectionsOfHom f M ⊤
  have : ∀ i, Module.Flat R (F.cochain 𝒰 i) := fun i =>
    OModulePresheaf.flat_cochain_ofModules_of_locallyTrivial f M htriv 𝒰 i
  have hdd : ∀ i, F.d 𝒰 (i + 1) ∘ₗ F.d 𝒰 i = 0 := fun i => OModulePresheaf.d_comp_d F 𝒰 i
  have hbd : ∀ i, Fintype.card 𝒰.ι ≤ i → Subsingleton (F.cochain 𝒰 i) := fun i hi =>
    subsingleton_cochain F 𝒰 i hi
  have hCF : F.CechFinite 𝒰 := OModulePresheaf.cechFinite_ofModules_of_locallyTrivial f M htriv 𝒰
  have hMinv : Scheme.Modules.IsInvertible M := ⟨htriv⟩
  have hfib : ∀ (K : Type u) [Field K] [Algebra R K] (i : ℕ),
      LinearMap.ker ((F.d 𝒰 (i + 1)).baseChange K) ≤ LinearMap.range ((F.d 𝒰 i).baseChange K) := by
    intro K _ _ i
    obtain ⟨𝒲, h𝒲⟩ := hH K
    let p₁ := Limits.pullback.fst f (specMap R K)
    let p₂ := Limits.pullback.snd f (specMap R K)
    let MK : (Limits.pullback f (specMap R K)).Modules := (Scheme.Modules.pullback p₁).obj M
    have htrivK := (hMinv.pullback p₁).1
    have hq := OModulePresheaf.isQuasicoherent_ofModules_of_locallyTrivial p₂ MK htrivK
    obtain ⟨eK⟩ := (OModulePresheaf.nonempty_cechEquiv_ofModules_of_isQuasicoherent_of_isSeparated
      p₂ MK hq
      (𝒰.baseChange f K) 𝒲).2 i
    have := h𝒲 i
    have : Subsingleton ((OModulePresheaf.ofModules p₂ MK).HSucc (𝒰.baseChange f K) i) :=
      eK.toEquiv.subsingleton
    obtain ⟨φ, -, hφ⟩ := (OModulePresheaf.nonempty_cech_baseChange_equiv_of_locallyTrivial f 𝒰 M
      htriv K).1.2 i
    exact ker_le_range_of_subsingleton _ _ φ hφ
  obtain ⟨hproj, hbij, -⟩ :=
    Module.Flat.projective_ker_and_bijective_kerBaseChangeHom_of_forall_ker_baseChange_le_range
      (fun i => F.cochain 𝒰 i) (fun i => F.d 𝒰 i) hdd (Fintype.card 𝒰.ι) hbd hCF.1 hCF.2 hfib
  let ε₀ : Γ(M, ⊤) ≃ₗ[R] F.H0 𝒰 := sectionsEquivH0 f M 𝒰
  have : Module.Finite R (F.H0 𝒰) := hCF.1
  have : Module.Projective R (F.H0 𝒰) := hproj
  refine ⟨⟨Module.Finite.equiv ε₀.symm, Module.Projective.of_equiv ε₀.symm⟩, ?_⟩
  intro A _ _
  let p₁ := Limits.pullback.fst f (specMap R A)
  let p₂ := Limits.pullback.snd f (specMap R A)
  let MA : (Limits.pullback f (specMap R A)).Modules := (Scheme.Modules.pullback p₁).obj M
  let FA := OModulePresheaf.ofModules p₂ MA
  let instMA := Scheme.TwoAffineOpenCover.moduleSectionsOfHom p₂ MA ⊤
  obtain ⟨E, hEd, hEf⟩ := OModulePresheaf.exists_cochain_baseChange_equiv_of_locallyTrivial f 𝒰 M
    htriv A
  let e1 : Γ(MA, ⊤) ≃ₗ[A] FA.H0 (𝒰.baseChange f A) := sectionsEquivH0 p₂ MA (𝒰.baseChange f A)
  let e2 : LinearMap.ker ((F.d 𝒰 0).baseChange A) ≃ₗ[A] FA.H0 (𝒰.baseChange f A) :=
    kerEquivOfEquiv ((F.d 𝒰 0).baseChange A) (FA.d (𝒰.baseChange f A) 0) (E 0) (E 1) (hEd 0)
  let e3 : A ⊗[R] F.H0 𝒰 ≃ₗ[A] LinearMap.ker ((F.d 𝒰 0).baseChange A) :=
    LinearEquiv.ofBijective (TwoChartCech.kerBaseChangeHom (F.d 𝒰 0) A) (hbij A)
  let e0 : A ⊗[R] Γ(M, ⊤) ≃ₗ[A] A ⊗[R] F.H0 𝒰 := ε₀.baseChange R A _ _
  let e : A ⊗[R] Γ(M, ⊤) ≃ₗ[A] Γ(MA, ⊤) := e0.trans (e3.trans (e2.trans e1.symm))
  have key : ∀ m : Γ(M, ⊤), e1 (unitApp p₁ M ⊤ m) = e2 (e3 ((1 : A) ⊗ₜ[R] ε₀ m)) := by
    intro m
    apply Subtype.ext
    rw [coe_kerEquivOfEquiv]
    change ((e1 _ : FA.H0 (𝒰.baseChange f A)) : FA.cochain (𝒰.baseChange f A) 0) =
      E 0 ((TwoChartCech.kerBaseChangeHom (F.d 𝒰 0) A ((1 : A) ⊗ₜ[R] ε₀ m) : A ⊗[R] F.cochain 𝒰 0))
    dsimp only [e1]
    rw [TwoChartCech.kerBaseChangeHom_apply_coe, LinearMap.baseChange_tmul, Submodule.subtype_apply,
      coe_sectionsEquivH0]
    funext s
    rw [hEf 0 1 (toCochain f M 𝒰 m) s, one_smul]
    have h2 := unitApp_map p₁ M (homOfLE (le_top : 𝒰.inter s ≤ ⊤))
      (homOfLE (le_top : p₁ ⁻¹ᵁ 𝒰.inter s ≤ p₁ ⁻¹ᵁ ⊤)) m
    change MA.presheaf.map (homOfLE (le_top : (𝒰.baseChange f A).inter s ≤ ⊤)).op (unitApp p₁ M ⊤ m)
      = FA.res (𝒰.baseChange_inter_le f A s)
        (unitApp p₁ M (𝒰.inter s) (M.presheaf.map (homOfLE (le_top : 𝒰.inter s ≤ ⊤)).op m))
    rw [h2, OModulePresheaf.ofModules_res_apply]
    exact (map_map MA _ _ _ _).symm
  have key1 : ∀ m : Γ(M, ⊤), e ((1 : A) ⊗ₜ[R] m) = unitApp p₁ M ⊤ m := by
    intro m
    have h0 : e0 ((1 : A) ⊗ₜ[R] m) = (1 : A) ⊗ₜ[R] ε₀ m :=
      by simp only [e0, LinearEquiv.baseChange_tmul]
    exact (congrArg (fun z => e1.symm (e2 (e3 z))) h0).trans
      ((congrArg e1.symm (key m).symm).trans
        (e1.symm_apply_apply (show Γ(MA, ⊤) from unitApp p₁ M ⊤ m)))
  have key2 : ∀ (a : A) (m : Γ(M, ⊤)), e (a ⊗ₜ[R] m) = a • (show Γ(MA, ⊤) from unitApp p₁ M ⊤ m) :=
    by
    intro a m
    have hsm : a ⊗ₜ[R] m = a • ((1 : A) ⊗ₜ[R] m) :=
      by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [hsm, map_smul, key1]
  exact ⟨e, fun a m => key2 a m⟩

end Engine19

end
end AlgebraicCurves.Cohomology.Proofs.ProjectiveSectionsBaseChange

namespace AlgebraicGeometry.Scheme.Modules

open _root_.AlgebraicCurves.Cohomology.Proofs.ProjectiveSectionsBaseChange
universe u


open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
  _root_.TensorProduct in
theorem finite_projective_sections_and_baseChange_equiv_of_subsingleton_HSucc
    {R : Type u} [CommRing R] [IsNoetherianRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    [IsProper f] [Flat f] (M : X.Modules)
    (htriv : ∀ x : X, ∃ (U : X.Opens), x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.unit U.toScheme.ringCatSheaf))
    (hH : ∀ (K : Type u) [Field K] [Algebra R K],
      ∃ 𝒲 : (Limits.pullback f (Scheme.TwoAffineOpenCover.specMap R K)).OrderedAffineCover, ∀ i : ℕ,
        Subsingleton ((OModulePresheaf.ofModules (Limits.pullback.snd f
          (Scheme.TwoAffineOpenCover.specMap R K))
          ((Scheme.Modules.pullback (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R
            K))).obj M)).HSucc 𝒲 i)) :
    (letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom f M ⊤
     Module.Finite R Γ(M, ⊤) ∧ Module.Projective R Γ(M, ⊤)) ∧
    ∀ (A : Type u) [CommRing A] [Algebra R A],
      letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom f M ⊤
      letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom
        (Limits.pullback.snd f (Scheme.TwoAffineOpenCover.specMap R A))
        ((Scheme.Modules.pullback (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R
          A))).obj M)
        ((Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R A)) ⁻¹ᵁ ⊤)
      ∃ e : A ⊗[R] Γ(M, ⊤) ≃ₗ[A]
          Γ((Scheme.Modules.pullback (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R
            A))).obj M, (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R A)) ⁻¹ᵁ ⊤),
        ∀ (a : A) (m : Γ(M, ⊤)),
          e (a ⊗ₜ[R] m) = a • Scheme.Modules.pullbackLocalSection (Limits.pullback.fst f
            (Scheme.TwoAffineOpenCover.specMap R A)) m :=
  Engine19.main f M htriv hH
end AlgebraicGeometry.Scheme.Modules
end ProofImplementation

attribute [-instance] AlgebraicGeometry.Scheme.Hom.opensMapFinal
  AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid
  AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited
  AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero
  AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower
  AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ
  AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ
  AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp
  AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ
  AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul
  AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower
  AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul
  AlgebraicGeometry.OModulePresheaf.Leray.biC_module
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I
  DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II
  DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I
  AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed
  AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU
  AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway
  AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU
  AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial
  ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup
  ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg
  ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid
  ProjSpaceCech.GradedModule.modR
attribute [-instance] ProjSpaceCech.GradedModule.sec.instModule
  ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero
  ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul
  ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup
  ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq
  ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule
attribute [-simp] AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec
  AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq
  AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.OModulePresheaf.prod_obj
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
  AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U
  AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq
  AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq
attribute [-simp] DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq
  DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec
  DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec
  AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq
  AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq
  ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq
  ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Hom.mk.injEq
