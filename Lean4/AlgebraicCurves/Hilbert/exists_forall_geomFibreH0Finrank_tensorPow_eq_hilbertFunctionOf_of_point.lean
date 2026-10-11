/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_HilbertFunctor_exists_forall_geomFibreH0Finrank_tensorPow_eq_hilbertFunctionOf_of_point.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.Tactic.Ext
import SchemeTheory.ProjectiveSpace.Basic
import AlgebraicCurves.Hilbert.Functor.Basic
import AlgebraicCurves.Geometry.Picard.PolarisedAbelianScheme
import AlgebraicCurves.Foundations.Algebra.SheafOfModules_MonoidalV2
import SchemeTheory.ProjectiveSpace.Cover
import AlgebraicCurves.Geometry.Projective.ProjTwistDatum
import SchemeTheory.Modules.ProjectivePresentation
import SchemeTheory.Modules.TensorPowers
import AlgebraicCurves.Cohomology.Sheaves.OModulePresheafOfModules
import AlgebraicCurves.Geometry.Picard.Functor
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_geomFibreH0Finrank_id_eq_finrank_sections
import AlgebraicCurves.Cohomology.Sheaves.OModulePresheaf_nonempty_sections_top_equiv_H0_ofModules
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_tensorPow_monoidalV2
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_ProjPresentation_exists_linearMap_sections_tensorPow_twistObj_monoidalV2
import AlgebraicCurves.Foundations.Algebra.LinearMap_nonempty_kerModRange_equiv_of_equiv_comm
import AlgebraicCurves.Geometry.Projective.ProjSpace_exists_linearMap_homogeneousSubmodule_twistObj_top_val_eq
import AlgebraicCurves.Geometry.Projective.ProjSpace_exists_forall_H0_twist_exists_isHomogeneous_forall_val_eq_of_isClosedImmersion

/-!
# exists forall geom Fibre H0 Finrank tensor Pow eq hilbert Function Of of point
-/

section ProofImplementation

namespace AlgebraicCurves.Hilbert.Proofs.HilbertFibreRankFunction
open PresheafOfModules.PullbackMonoidal in
attribute [-instance]
  AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx
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
  AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U PresheafOfModules.freeεIso_hom_app
  PresheafOfModules.freeμIso_hom_app

universe u


open _root_.MvPolynomial
open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.HilbertFunctor
open _root_.TensorProduct


attribute [local instance] MvPolynomial.gradedAlgebra

namespace H0AB

section Transport

open _root_.AlgebraicGeometry.OModulePresheaf hiding twist tensor ker zero


variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}

/-- A natural family of additive maps of presheaf modules compatible with the base-ring action. -/
structure NatFamily (F G : OModulePresheaf π) where
  /-- The additive map on sections over each open. -/
  app : ∀ U : V.Opens, F.obj U →+ G.obj U
  /-- The maps preserve scalar multiplication by the base ring. -/
  smul : ∀ (U : V.Opens) (r : R) (x : F.obj U), app U (r • x) = r • app U x
  /-- The maps commute with restriction to smaller opens. -/
  natural : ∀ {U U' : V.Opens} (h : U ≤ U') (x : F.obj U'), app U (F.res h x) = G.res h (app U' x)

variable {F G : OModulePresheaf π} (η : NatFamily F G) (K : V.OrderedAffineCover)

/-- The component of the natural family as a base-ring linear map on sections. -/
def appₗ (U : V.Opens) : F.obj U →ₗ[R] G.obj U :=
  { toFun := η.app U, map_add' := map_add (η.app U), map_smul' := η.smul U }

/-- The induced linear map on Cech cochains obtained by applying the family on each
intersection. -/
def cochainMap (i : ℕ) : F.cochain K i →ₗ[R] G.cochain K i :=
  LinearMap.pi fun s => (appₗ η (K.inter s)).comp (LinearMap.proj s)

theorem cochainMap_apply (i : ℕ) (c : F.cochain K i) (s : K.Idx i) :
    cochainMap η K i c s = η.app (K.inter s) (c s) := rfl

theorem cochainMap_d (i : ℕ) (c : F.cochain K i) :
    cochainMap η K (i + 1) (F.d K i c) = G.d K i (cochainMap η K i c) := by
  funext s
  rw [cochainMap_apply, d_apply, d_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul, η.natural, cochainMap_apply]

theorem cochainMap_bijective (hη : ∀ (i : ℕ) (s : K.Idx i), Function.Bijective (η.app (K.inter s)))
  (i : ℕ) :
    Function.Bijective (cochainMap η K i) := by
  constructor
  · intro c c' h
    funext s
    exact (hη i s).1 (by rw [← cochainMap_apply, ← cochainMap_apply, h])
  · intro c
    refine ⟨fun s => (Equiv.ofBijective _ (hη i s)).symm (c s), funext fun s => ?_⟩
    rw [cochainMap_apply]
    exact Equiv.ofBijective_apply_symm_apply _ (hη i s) (c s)

theorem nonempty_H0_equiv_of_natFamily (hη : ∀ (i : ℕ) (s : K.Idx i), Function.Bijective (η.app
  (K.inter s))) :
    Nonempty (F.H0 K ≃ₗ[R] G.H0 K) :=
  (LinearMap.nonempty_kerModRange_equiv_of_equiv_comm (F.d K) (G.d K)
    (fun i => LinearEquiv.ofBijective (cochainMap η K i) (cochainMap_bijective η K hη i))
    (fun i x => cochainMap_d η K i x)).1

end Transport

section Theta

variable {n : ℕ} {k : Type u} [Field k] {Zk : Scheme.{u}}
  (ιk : Zk ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)) [IsAffineHom ιk] (d : ℕ)

/-- The section on a pulled-back projective chart obtained from the homogeneous polynomial. -/
noncomputable def chartVal (F : MvPolynomial (Fin (n + 1)) k) (hF : F.IsHomogeneous d) (i : Fin (n
  + 1)) :
    Γ(Zk, ProjSpace.pullbackChart ιk i) :=
  (ιk.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)))
    (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)
      (HomogeneousLocalization.mk
        { deg := d
          num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
          den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
            (MvPolynomial.isHomogeneous_X_pow i d)⟩
          den_mem := ⟨d, rfl⟩ }))

theorem isHomogeneous_of_mem (F : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k d)) :
    (F : MvPolynomial (Fin (n + 1)) k).IsHomogeneous d :=
  (MvPolynomial.mem_homogeneousSubmodule d _).mp F.2

/-- The degree-zero Cech index corresponding to the selected standard projective chart. -/
def vertex (i : Fin (n + 1)) : (ProjSpace.stdCoverPullback ιk).Idx 0 :=
  ⟨fun _ => ULift.up i, fun a b hab => absurd (Fin.lt_def.mp hab)
    (by have := a.isLt; have := b.isLt; omega)⟩

theorem chart_le_inter_vertex (i : Fin (n + 1)) :
    ProjSpace.pullbackChart ιk i ≤ (ProjSpace.stdCoverPullback ιk).inter (vertex ιk i) ⊓
      ProjSpace.pullbackChart ιk i :=
  le_inf (le_iInf fun _ => le_rfl) le_rfl

theorem exists_theta :
    ∃ Θ : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k d) →ₗ[k]
        ↥((ProjSpace.twist (ιk ≫ ProjSpace.π k n) ιk d).H0 (ProjSpace.stdCoverPullback ιk)),
      ∀ (F : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k d))
        (s : (ProjSpace.stdCoverPullback ιk).Idx 0) (i : Fin (n + 1)),
        ((Θ F : (ProjSpace.twist (ιk ≫ ProjSpace.π k n) ιk d).cochain (ProjSpace.stdCoverPullback
          ιk) 0) s).val i =
          ProjSpace.restrictFun
            (inf_le_right : (ProjSpace.stdCoverPullback ιk).inter s ⊓ ProjSpace.pullbackChart ιk i
              ≤ ProjSpace.pullbackChart ιk i)
            (chartVal ιk d F (isHomogeneous_of_mem d F) i) := by
  obtain ⟨θ, hθ, -⟩ := ProjSpace.exists_linearMap_homogeneousSubmodule_twistObj_top_val_eq ιk d
  let T := ProjSpace.twist (ιk ≫ ProjSpace.π k n) ιk d
  let K := ProjSpace.stdCoverPullback ιk
  let Θ₀ : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k d) →ₗ[k] T.cochain K 0 :=
    LinearMap.pi fun s => (T.res (le_top : K.inter s ≤ ⊤)).comp θ
  have hΘ₀ : ∀ F s, Θ₀ F s = T.res (le_top : K.inter s ≤ ⊤) (θ F) := fun F s => rfl
  have hcoc : ∀ F, Θ₀ F ∈ T.H0 K := by
    intro F
    rw [LinearMap.mem_ker]
    funext s
    change T.d K 0 (Θ₀ F) s = (0 : T.obj (K.inter s))
    rw [OModulePresheaf.d_apply, Fin.sum_univ_two]
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul, hΘ₀]
    have h0 : T.res (K.inter_le_inter_face s 0)
        (T.res (le_top : K.inter (K.face s 0) ≤ ⊤) (θ F)) =
        T.res (le_top : K.inter s ≤ ⊤) (θ F) := T.res_res _ _ (θ F)
    have h1 : T.res (K.inter_le_inter_face s 1)
        (T.res (le_top : K.inter (K.face s 1) ≤ ⊤) (θ F)) =
        T.res (le_top : K.inter s ≤ ⊤) (θ F) := T.res_res _ _ (θ F)
    exact (congrArg₂ (fun a b : T.obj (K.inter s) => a + -b) h0 h1).trans
      (add_neg_cancel (T.res (le_top : K.inter s ≤ ⊤) (θ F)))
  refine ⟨LinearMap.codRestrict (T.H0 K) Θ₀ hcoc, fun F s i => ?_⟩
  rw [LinearMap.codRestrict_apply, hΘ₀]
  change (ProjSpace.twistRes (ιk ≫ ProjSpace.π k n) ιk d (le_top : K.inter s ≤ ⊤) (θ F)).val i = _
  rw [ProjSpace.twistRes_val]
  have hF := hθ F.1 (isHomogeneous_of_mem d F) i
  rw [show (⟨F.1, (MvPolynomial.mem_homogeneousSubmodule d F.1).mpr (isHomogeneous_of_mem d F)⟩ :
      ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k d)) = F from Subtype.ext rfl] at hF
  have hF' : (θ F).val i =
      ProjSpace.restrictFun
        (inf_le_right : (⊤ : Zk.Opens) ⊓ ProjSpace.pullbackChart ιk i ≤ ProjSpace.pullbackChart ιk
          i)
        (chartVal ιk d F (isHomogeneous_of_mem d F) i) := hF
  exact (congrArg (ProjSpace.restrictFun
      (inf_le_inf_right (ProjSpace.pullbackChart ιk i) (le_top : K.inter s ≤ ⊤))) hF').trans
    (ProjSpace.restrictFun_restrictFun _ _ (chartVal ιk d F (isHomogeneous_of_mem d F) i))

variable {ιk d}

theorem theta_eq_zero_iff
    (Θ : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k d) →ₗ[k]
        ↥((ProjSpace.twist (ιk ≫ ProjSpace.π k n) ιk d).H0 (ProjSpace.stdCoverPullback ιk)))
    (hΘ : ∀ (F : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k d))
        (s : (ProjSpace.stdCoverPullback ιk).Idx 0) (i : Fin (n + 1)),
        ((Θ F : (ProjSpace.twist (ιk ≫ ProjSpace.π k n) ιk d).cochain (ProjSpace.stdCoverPullback
          ιk) 0) s).val i =
          ProjSpace.restrictFun
            (inf_le_right : (ProjSpace.stdCoverPullback ιk).inter s ⊓ ProjSpace.pullbackChart ιk i
              ≤ ProjSpace.pullbackChart ιk i)
            (chartVal ιk d F (isHomogeneous_of_mem d F) i))
    (F : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k d)) :
    Θ F = 0 ↔ ∀ i : Fin (n + 1), chartVal ιk d F (isHomogeneous_of_mem d F) i = 0 := by
  constructor
  · intro h i
    have h1 := hΘ F (vertex ιk i) i
    rw [h] at h1
    have h2 : ProjSpace.restrictFun (chart_le_inter_vertex ιk i)
        (ProjSpace.restrictFun
          (inf_le_right : (ProjSpace.stdCoverPullback ιk).inter (vertex ιk i) ⊓
            ProjSpace.pullbackChart ιk i ≤
            ProjSpace.pullbackChart ιk i)
          (chartVal ιk d F (isHomogeneous_of_mem d F) i)) = chartVal ιk d F (isHomogeneous_of_mem d
            F) i := by
      rw [ProjSpace.restrictFun_restrictFun]; exact ProjSpace.restrictFun_refl _
    rw [← h2, ← h1]
    have hz : (((0 : ↥((ProjSpace.twist (ιk ≫ ProjSpace.π k n) ιk d).H0 (ProjSpace.stdCoverPullback
      ιk))) :
        (ProjSpace.twist (ιk ≫ ProjSpace.π k n) ιk d).cochain (ProjSpace.stdCoverPullback ιk) 0)
          (vertex ιk i)).val i
        = 0 := rfl
    rw [hz, map_zero]
  · intro h
    apply Subtype.ext
    funext s
    refine ProjSpace.twistObj.ext (funext fun i => ?_)
    rw [hΘ, h i, map_zero]
    rfl

end Theta

end H0AB

open _root_.AlgebraicGeometry.ProjSpace in
theorem H0AB.exists_forall_geomFibreH0Finrank_eq_finrank_piece
    (n : ℕ) (P : Polynomial ℚ) (m : ℕ) (k : Type) [Field k] [IsAlgClosed k]
    (q : Point k n (hilbertFunctionOf n P m))
    (Z : Scheme.{0}) (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k))
    (hι : IsClosedImmersion ι)
    (hZ : ∀ d : ℕ, m ≤ d → ∀ (F : MvPolynomial (Fin (n + 1)) k) (hF : F.IsHomogeneous d),
      (F ∈ q.I ↔ ∀ i : Fin (n + 1),
        (ι.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X
          i)))
          (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)
            (HomogeneousLocalization.mk
              { deg := d
                num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
                  (MvPolynomial.isHomogeneous_X_pow i d)⟩
                den_mem := ⟨d, rfl⟩ })) = 0))
    (𝓛 : Z.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (𝔓 : Scheme.Modules.ProjPresentation 𝓛 (ι ≫ ProjSpace.π k n) n) (h𝔓 : 𝔓.toProj = ι) :
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
      Scheme.Modules.geomFibreH0Finrank (ι ≫ ProjSpace.π k n)
          (Nat.rec (motive := fun _ => Z.Modules) (𝟙_ Z.Modules) (fun _ M => M ⊗ 𝓛) d) k
            (RingHom.id k) =
        Module.finrank k (piece q.I d) := by
  classical
  have := hι
  have hrec : ∀ d : ℕ, (Nat.rec (motive := fun _ => Z.Modules) (𝟙_ Z.Modules) (fun _ M => M ⊗ 𝓛) d)
    = 𝓛.tensorPow d := by
    intro d
    induction d with
    | zero => rfl
    | succ d ih =>
        change (Nat.rec (motive := fun _ => Z.Modules) (𝟙_ Z.Modules) (fun _ M => M ⊗ 𝓛) d) ⊗ 𝓛 =
          𝓛.tensorPow d ⊗ 𝓛
        rw [ih]
  obtain ⟨d₂, hd₂⟩ :=
    exists_forall_H0_twist_exists_isHomogeneous_forall_val_eq_of_isClosedImmersion ι
  refine ⟨max m d₂, fun d hd => ?_⟩
  have hdm : m ≤ d := (le_max_left _ _).trans hd
  have hdd : d₂ ≤ d := (le_max_right _ _).trans hd
  let := Scheme.TwoAffineOpenCover.moduleSectionsOfHom (ι ≫ ProjSpace.π k n) (𝓛.tensorPow d) ⊤
  rw [hrec d, Scheme.Modules.geomFibreH0Finrank_id_eq_finrank_sections k (ι ≫ ProjSpace.π k n)
    (𝓛.tensorPow d)
    (h𝓛.tensorPow_monoidalV2 d)]
  obtain ⟨e1⟩ := AlgebraicGeometry.OModulePresheaf.nonempty_sections_top_equiv_H0_ofModules (ι ≫
    ProjSpace.π k n)
    (𝓛.tensorPow d) (ProjSpace.stdCoverPullback ι)
  rw [e1.finrank_eq]
  have key : ∀ (φ : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)) [IsAffineHom φ],
    𝔓.toProj = φ →
      Nonempty (↥((OModulePresheaf.ofModules (ι ≫ ProjSpace.π k n) (𝓛.tensorPow d)).H0
        (ProjSpace.stdCoverPullback φ)) ≃ₗ[k]
        ↥((ProjSpace.twist (ι ≫ ProjSpace.π k n) φ d).H0 (ProjSpace.stdCoverPullback φ))) := by
    intro φ _ hφ
    subst hφ
    obtain ⟨e, -, hnat, hbij⟩ :=
      Scheme.Modules.ProjPresentation.exists_linearMap_sections_tensorPow_twistObj_monoidalV2 𝔓 d
    refine H0AB.nonempty_H0_equiv_of_natFamily (F := OModulePresheaf.ofModules _ (𝓛.tensorPow d))
      (G := ProjSpace.twist _ 𝔓.toProj d)
      { app := fun U => (e U).toAddMonoidHom
        smul := fun U r x => ?_
        natural := fun h x => hnat _ _ h x } (ProjSpace.stdCoverPullback 𝔓.toProj) ?_
    · let := Scheme.TwoAffineOpenCover.algebraOfHom (ι ≫ ProjSpace.π k n) U
      change e U (r • x) = r • e U x
      rw [OModulePresheaf.ofModules_algebraMap_smul]
      erw [(e U).map_smul]
      exact (ProjSpace.twistObj.algebraMap_smul r (e U x)).symm
    · intro i s
      exact hbij _ (s.1 0).down ((ProjSpace.stdCoverPullback 𝔓.toProj).inter_le s 0)
  obtain ⟨e2⟩ := key ι h𝔓
  rw [e2.finrank_eq]
  obtain ⟨Θ, hΘ⟩ := H0AB.exists_theta ι d
  have hker : LinearMap.ker Θ =
      Submodule.comap (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k d).subtype
        (q.I.restrictScalars k) := by
    ext F
    rw [LinearMap.mem_ker, H0AB.theta_eq_zero_iff Θ hΘ F, Submodule.mem_comap,
      Submodule.restrictScalars_mem]
    exact (hZ d hdm F.1 (H0AB.isHomogeneous_of_mem d F)).symm
  have htop : LinearMap.range Θ = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨y, hy⟩ -
    obtain ⟨F, hF, hform⟩ := hd₂ d hdd y hy
    refine ⟨⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩, Subtype.ext (funext fun s =>
      ?_)⟩
    refine ProjSpace.twistObj.ext (funext fun i => ?_)
    rw [hΘ]
    exact (hform s i).symm
  rw [← finrank_top k ↥((ProjSpace.twist (ι ≫ ProjSpace.π k n) ι d).H0 (ProjSpace.stdCoverPullback
    ι)), ← htop]
  exact (Θ.quotKerEquivRange.symm.trans (Submodule.quotEquivOfEq _ _ hker)).finrank_eq

namespace H0SOL

theorem finrank_piece_eq_of_point {k : Type} [Field k] {n : ℕ} {h : ℕ → ℕ} (q : Point k n h) (d :
  ℕ) :
    Module.finrank k (piece q.I d) = h d := by
  have : Module.Finite k (piece q.I d) := q.finite_piece d
  have hfree : Module.Free k (piece q.I d) := Module.Free.of_divisionRing k _
  have := q.rankAtStalk_piece d ⟨⊥, Ideal.isPrime_bot⟩
  rwa [Module.rankAtStalk_eq_finrank_of_free] at this

end H0SOL

end AlgebraicCurves.Hilbert.Proofs.HilbertFibreRankFunction

namespace AlgebraicGeometry.HilbertFunctor

open MvPolynomial CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

open _root_.AlgebraicCurves.Hilbert.Proofs.HilbertFibreRankFunction in
theorem exists_forall_geomFibreH0Finrank_tensorPow_eq_hilbertFunctionOf_of_point
    (n : ℕ) (P : Polynomial ℚ) (m : ℕ) (k : Type) [Field k] [IsAlgClosed k]
    (q : Point k n (hilbertFunctionOf n P m))
    (Z : Scheme.{0}) (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k))
    (hι : IsClosedImmersion ι)
    (hZ : ∀ d : ℕ, m ≤ d → ∀ (F : MvPolynomial (Fin (n + 1)) k) (hF : F.IsHomogeneous d),
      (F ∈ q.I ↔ ∀ i : Fin (n + 1),
        (ι.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X
          i)))
          (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)
            (HomogeneousLocalization.mk
              { deg := d
                num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
                  (MvPolynomial.isHomogeneous_X_pow i d)⟩
                den_mem := ⟨d, rfl⟩ })) = 0))
    (𝓛 : Z.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (𝔓 : Scheme.Modules.ProjPresentation 𝓛 (ι ≫ ProjSpace.π k n) n) (h𝔓 : 𝔓.toProj = ι) :
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
      Scheme.Modules.geomFibreH0Finrank (ι ≫ ProjSpace.π k n)
          (Nat.rec (motive := fun _ => Z.Modules) (𝟙_ Z.Modules) (fun _ M => M ⊗ 𝓛) d) k
            (RingHom.id k) =
        hilbertFunctionOf n P m d := by
  obtain ⟨d₀, hd₀⟩ := H0AB.exists_forall_geomFibreH0Finrank_eq_finrank_piece n P m k q Z ι hι hZ 𝓛
    h𝓛 𝔓 h𝔓
  exact ⟨d₀, fun d hd => (hd₀ d hd).trans (H0SOL.finrank_piece_eq_of_point q d)⟩
end AlgebraicGeometry.HilbertFunctor
end ProofImplementation

attribute [-instance] AlgebraicGeometry.OModulePresheaf.isScalarTower
  AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder
  AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype
  AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx
  AlgebraicGeometry.OModulePresheaf.addCommGroup
  AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx
  AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA
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
  AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module
  AlgebraicGeometry.ProjSpace.twistObj.module AlgebraicGeometry.ProjSpace.twistObj.moduleSections
  AlgebraicGeometry.ProjSpace.twistFam.addCommGroup ProjSpaceCech.GradedModule.H.module
open PresheafOfModules.PullbackMonoidal in
attribute [-instance]
  ProjSpaceCech.GradedModule.H.addCommGroup
  ProjSpaceCech.GradedModule.sec.instAdd
  ProjSpaceCech.GradedModule.sec.instNeg
  ProjSpaceCech.GradedModule.acg
  ProjSpaceCech.GradedModule.Frac.setoid
  ProjSpaceCech.GradedModule.modR
  ProjSpaceCech.GradedModule.sec.instModule
  ProjSpaceCech.GradedModule.sec.instAddCommGroup
  ProjSpaceCech.GradedModule.sec.instZero
  ProjSpaceCech.GradedModule.Presentation.fJ
  ProjSpaceCech.GradedModule.sec.instSMul
  ProjSpaceCech.Twist.H.module
  ProjSpaceCech.Idx.instFintype
  ProjSpaceCech.Twist.H.addCommGroup
  ProjSpaceCech.Idx.instDecidableEq
  ProjSpaceCech.Twist.Mon.instDecidableEq
  ProjSpaceCech.Twist.cochain.instAddCommGroup
  ProjSpaceCech.Twist.cochain.instModule
  AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx
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
attribute [-simp] AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq
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
  AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.OModulePresheaf.prod_obj
  AlgebraicGeometry.OModulePresheaf.restrOpen_obj
attribute [-simp] AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq
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
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left PresheafOfModules.freeεIso_hom_app
  PresheafOfModules.freeμIso_hom_app
