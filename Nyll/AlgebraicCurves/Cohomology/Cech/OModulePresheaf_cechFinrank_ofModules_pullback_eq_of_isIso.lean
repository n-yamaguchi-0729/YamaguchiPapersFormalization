/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_cechFinrank_ofModules_pullback_eq_of_isIso.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.SchemeTheory.Cohomology.Cech.OrderedAffineCoverCech
import Nyll.AlgebraicCurves.Cohomology.Sheaves.OModulePresheafOfModules
import Nyll.AlgebraicCurves.Cohomology.Sheaves.OModulePresheafEulerChar
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.AlgebraicCurves.Geometry.Schemes.OrderedAffineCoverComap
import Nyll.AlgebraicCurves.Cohomology.Sheaves.OModulePresheafTensor
import Nyll.SchemeTheory.Cohomology.Sheaves.OModulePresheafConstructions
import Nyll.SchemeTheory.Cohomology.Sheaves.OModulePresheafHom
import Nyll.AlgebraicCurves.Cohomology.Cech.OModulePresheaf_nonempty_cechEquiv_ofModules_of_isQuasicoherent_of_isSeparated
import Nyll.AlgebraicCurves.Cohomology.Cech.OModulePresheaf_nonempty_cechEquiv_ofModules_pullback_comap_twist_pushforwardUnit
import Nyll.AlgebraicCurves.Cohomology.Sheaves.OModulePresheaf_isQuasicoherent_ofModules_of_locallyTrivial

/-!
# OModule Presheaf cech Finrank of Modules pullback eq of is Iso
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Cech.Proofs
namespace OModulePresheaf_cechFinrank_ofModules_pullback_eq_of_isIso
attribute [-instance] AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx
attribute [-instance] AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype
attribute [-instance] AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder
attribute [-instance] AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx
attribute [-simp] AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq
  AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace P2mAutInv


open _root_.AlgebraicGeometry.OModulePresheaf
open _root_.TensorProduct


theorem cechEquiv_of_affHom_inverse
    {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (CommRingCat.of R)} [IsSeparated π]
    {F G : OModulePresheaf π} (φ : AffHom F G) (ψ : AffHom G F)
    (h₁ : ∀ (U : V.affineOpens) (x : F.obj U.1), ψ.app U (φ.app U x) = x)
    (h₂ : ∀ (U : V.affineOpens) (y : G.obj U.1), φ.app U (ψ.app U y) = y)
    (K : V.OrderedAffineCover) :
    Nonempty (F.H0 K ≃ₗ[R] G.H0 K) ∧ ∀ i : ℕ, Nonempty (F.HSucc K i ≃ₗ[R] G.HSucc K i) := by
  have hc₁ : ∀ (i : ℕ) (f : F.cochain K i), ψ.cochainMap K i (φ.cochainMap K i f) = f := by
    intro i f; funext s; simp only [AffHom.cochainMap_apply, h₁]
  have hc₂ : ∀ (i : ℕ) (g : G.cochain K i), φ.cochainMap K i (ψ.cochainMap K i g) = g := by
    intro i g; funext s; simp only [AffHom.cochainMap_apply, h₂]
  refine ⟨⟨LinearEquiv.ofLinearMap (φ.H0Map K) (ψ.H0Map K) ?_ ?_⟩, fun i =>
    ⟨LinearEquiv.ofLinearMap (φ.HSuccMap K i) (ψ.HSuccMap K i) ?_ ?_⟩⟩
  · refine LinearMap.ext fun x => Subtype.ext ?_
    change φ.cochainMap K 0 (ψ.cochainMap K 0 x.1) = x.1
    exact hc₂ 0 x.1
  · refine LinearMap.ext fun x => Subtype.ext ?_
    change ψ.cochainMap K 0 (φ.cochainMap K 0 x.1) = x.1
    exact hc₁ 0 x.1
  · refine LinearMap.ext fun x => ?_
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      rw [LinearMap.comp_apply, AffHom.HSuccMap_mk, AffHom.HSuccMap_mk, LinearMap.id_apply]
      congr 1
      exact Subtype.ext (hc₂ (i + 1) x.1)
  · refine LinearMap.ext fun x => ?_
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      rw [LinearMap.comp_apply, AffHom.HSuccMap_mk, AffHom.HSuccMap_mk, LinearMap.id_apply]
      congr 1
      exact Subtype.ext (hc₁ (i + 1) x.1)

section twistIso

variable {R : Type u} [CommRing R] {P P' : Scheme.{u}} (π' : P' ⟶ Spec (CommRingCat.of R))
  (Φ : P ⟶ P') [IsIso Φ] (N : P'.Modules)

/-- The pullback homomorphism on sections over an open subset. -/
abbrev eU (U : P'.Opens) : Γ(P', U) →+* Γ(P, Φ ⁻¹ᵁ U) := (Φ.appLE U (Φ ⁻¹ᵁ U) le_rfl).hom

omit [IsIso Φ] in
theorem eU_eq (U : P'.Opens) : eU Φ U = (Φ.app U).hom := by
  change (Φ.appLE U (Φ ⁻¹ᵁ U) le_rfl).hom = (Φ.app U).hom
  rw [Scheme.Hom.app_eq_appLE]

theorem eU_bijective (U : P'.Opens) : Function.Bijective (eU Φ U) := by
  rw [eU_eq]
  exact ConcreteCategory.bijective_of_isIso (Φ.app U)

/-- The section ring equivalence induced by the scheme isomorphism. -/
noncomputable def eEquiv (U : P'.Opens) : Γ(P', U) ≃+* Γ(P, Φ ⁻¹ᵁ U) :=
  RingEquiv.ofBijective (eU Φ U) (eU_bijective Φ U)

omit [IsIso Φ] in
theorem pf_smul (U : P'.Opens) (a : Γ(P', U)) (b : (OModulePresheaf.pushforwardUnit π' Φ).obj U) :
    a • b = (show (OModulePresheaf.pushforwardUnit π' Φ).obj U from eU Φ U a * (show Γ(P, Φ ⁻¹ᵁ U)
      from b)) := rfl

/-- The unit section of the pushed forward structure sheaf. -/
def onePf (U : P'.Opens) : (OModulePresheaf.pushforwardUnit π' Φ).obj U := (1 : Γ(P, Φ ⁻¹ᵁ U))

omit [IsIso Φ] in
theorem eU_mul_onePf (U : P'.Opens) (a : (P'.presheaf.obj (Opposite.op U))) :
    a • onePf π' Φ U = (eU Φ U a : (OModulePresheaf.pushforwardUnit π' Φ).obj U) := by
  change eU Φ U a * 1 = eU Φ U a
  exact mul_one _

/-- Send a module section to its tensor product with the unit section. -/
noncomputable def fwd (U : P'.Opens) :
    (OModulePresheaf.ofModules π' N).obj U →ₗ[R] ((OModulePresheaf.pushforwardUnit π' Φ).twist
      N).obj U :=
  letI := Scheme.TwoAffineOpenCover.algebraOfHom π' U
  { toFun := fun m => (show ((OModulePresheaf.pushforwardUnit π' Φ).twist N).obj U from onePf π' Φ
    U ⊗ₜ[(P'.presheaf.obj (Opposite.op U))] m)
    map_add' := fun x y => TensorProduct.tmul_add _ x y
    map_smul' := fun r m => by
      change onePf π' Φ U ⊗ₜ[(P'.presheaf.obj (Opposite.op U))] (algebraMap R (P'.presheaf.obj
        (Opposite.op U)) r • m) =
        algebraMap R (P'.presheaf.obj (Opposite.op U)) r • (onePf π' Φ U ⊗ₜ[(P'.presheaf.obj
          (Opposite.op U))] m)
      rw [TensorProduct.tmul_smul] }

omit [IsIso Φ] in
theorem fwd_apply (U : P'.Opens) (m : (OModulePresheaf.ofModules π' N).obj U) :
    fwd π' Φ N U m = (onePf π' Φ U ⊗ₜ[(P'.presheaf.obj (Opposite.op U))] m :
      ((OModulePresheaf.pushforwardUnit π' Φ).twist N).obj U) := rfl

omit [IsIso Φ] in
theorem fwd_smul_sections (U : P'.Opens) (a : (P'.presheaf.obj (Opposite.op U))) (m :
  (OModulePresheaf.ofModules π' N).obj U) :
    fwd π' Φ N U (a • m) = a • fwd π' Φ N U m := by
  rw [fwd_apply, fwd_apply, TensorProduct.tmul_smul]
  rfl

/-- Evaluate a pushed forward section through the inverse section ring map. -/
noncomputable def bwdBil (U : P'.Opens) :
    (OModulePresheaf.pushforwardUnit π' Φ).obj U →ₗ[(P'.presheaf.obj (Opposite.op U))]
      ((OModulePresheaf.ofModules π' N).obj U →ₗ[(P'.presheaf.obj (Opposite.op U))]
        (OModulePresheaf.ofModules π' N).obj U) :=
  LinearMap.mk₂ (P'.presheaf.obj (Opposite.op U))
    (fun (b : (OModulePresheaf.pushforwardUnit π' Φ).obj U) (m : (OModulePresheaf.ofModules π'
      N).obj U) =>
      (eEquiv Φ U).symm (show Γ(P, Φ ⁻¹ᵁ U) from b) • m)
    (fun b₁ b₂ m => by
      change (eEquiv Φ U).symm ((show Γ(P, Φ ⁻¹ᵁ U) from b₁) + (show Γ(P, Φ ⁻¹ᵁ U) from b₂)) • m = _
      rw [map_add, add_smul])
    (fun a b m => by
      change (eEquiv Φ U).symm (eU Φ U a * (show Γ(P, Φ ⁻¹ᵁ U) from b)) • m = a • ((eEquiv Φ
        U).symm _ • m)
      rw [map_mul, show (eEquiv Φ U).symm (eU Φ U a) = a from (eEquiv Φ U).symm_apply_apply a,
        mul_smul])
    (fun b m₁ m₂ => smul_add _ _ _)
    (fun a b m => by rw [smul_comm])

/-- Contract the structure sheaf tensor factor through the section ring equivalence. -/
noncomputable def bwd (U : P'.Opens) :
    ((OModulePresheaf.pushforwardUnit π' Φ).twist N).obj U →ₗ[R] (OModulePresheaf.ofModules π'
      N).obj U :=
  letI := Scheme.TwoAffineOpenCover.algebraOfHom π' U
  { toFun := TensorProduct.lift (bwdBil π' Φ N U)
    map_add' := fun x y => map_add _ x y
    map_smul' := fun r t => by
      change TensorProduct.lift (bwdBil π' Φ N U) (algebraMap R (P'.presheaf.obj (Opposite.op U)) r
        • t) =
        r • TensorProduct.lift (bwdBil π' Φ N U) t
      have h := (TensorProduct.lift (bwdBil π' Φ N U)).map_smul (algebraMap R (P'.presheaf.obj
        (Opposite.op U)) r) t
      exact h.trans (algebraMap_smul _ r _) }

theorem bwd_tmul (U : P'.Opens) (b : (OModulePresheaf.pushforwardUnit π' Φ).obj U) (m :
  (OModulePresheaf.ofModules π' N).obj U) :
    bwd π' Φ N U (b ⊗ₜ[(P'.presheaf.obj (Opposite.op U))] m : ((OModulePresheaf.pushforwardUnit π'
      Φ).twist N).obj U) =
      ((eEquiv Φ U).symm b) • m := by
  change TensorProduct.lift (bwdBil π' Φ N U) (b ⊗ₜ[(P'.presheaf.obj (Opposite.op U))] m) = _
  rw [TensorProduct.lift.tmul]; rfl

theorem bwd_fwd (U : P'.Opens) (m : (OModulePresheaf.ofModules π' N).obj U) : bwd π' Φ N U (fwd π'
  Φ N U m) = m := by
  rw [fwd_apply, bwd_tmul]
  change (eEquiv Φ U).symm 1 • m = m
  rw [map_one, one_smul]

theorem fwd_bwd (U : P'.Opens) (t : ((OModulePresheaf.pushforwardUnit π' Φ).twist N).obj U) :
    fwd π' Φ N U (bwd π' Φ N U t) = t := by
  induction t using TensorProduct.inductionOn with
  | tmul b m =>
    rw [bwd_tmul, fwd_smul_sections, fwd_apply]
    change ((((eEquiv Φ U).symm b) • onePf π' Φ U) ⊗ₜ[(P'.presheaf.obj (Opposite.op U))] m :
      ((OModulePresheaf.pushforwardUnit π' Φ).twist N).obj U) = _
    rw [eU_mul_onePf]
    congr 1
    exact (eEquiv Φ U).apply_symm_apply b
  | add x y hx hy =>
    refine (((fwd π' Φ N U).comp (bwd π' Φ N U)).map_add x y).trans ?_
    exact congrArg₂ (fun a b : ((OModulePresheaf.pushforwardUnit π' Φ).twist N).obj U => a + b)
      hx hy

/-- The affine presheaf morphism given by tensoring with the unit. -/
noncomputable def fwdHom : AffHom (OModulePresheaf.ofModules π' N)
  ((OModulePresheaf.pushforwardUnit π' Φ).twist N) where
  app U := fwd π' Φ N U.1
  app_smul U a m := fwd_smul_sections π' Φ N U.1 a m
  naturality {U U'} h := by
    refine LinearMap.ext fun m => ?_
    change (OModulePresheaf.ofModules π' N).obj U'.1 at m
    rw [LinearMap.comp_apply, LinearMap.comp_apply, fwd_apply, fwd_apply]
    refine Eq.trans ?_ (OModulePresheaf.tensor_res_tmul
      (OModulePresheaf.pushforwardUnit π' Φ) (OModulePresheaf.ofModules π' N)
      h (onePf π' Φ U'.1) m).symm
    congr 1
    symm
    change (P.presheaf.map (homOfLE _).op).hom 1 = 1
    exact map_one _

/-- The inverse affine presheaf morphism given by contracting the tensor factor. -/
noncomputable def bwdHom : AffHom ((OModulePresheaf.pushforwardUnit π' Φ).twist N)
  (OModulePresheaf.ofModules π' N) where
  app U := bwd π' Φ N U.1
  app_smul U a t := by
    have hinj : Function.Injective (fwd π' Φ N U.1) :=
      Function.LeftInverse.injective (g := bwd π' Φ N U.1) (bwd_fwd π' Φ N U.1)
    apply hinj
    have hs : ∀ m : (OModulePresheaf.ofModules π' N).obj U.1, fwd π' Φ N U.1 (a • m) = a • fwd π' Φ
      N U.1 m :=
      (fwdHom π' Φ N).app_smul U a
    rw [hs, fwd_bwd, fwd_bwd]
  naturality {U U'} h := by
    refine LinearMap.ext fun t => ?_
    have hinj : Function.Injective (fwd π' Φ N U.1) :=
      Function.LeftInverse.injective (g := bwd π' Φ N U.1) (bwd_fwd π' Φ N U.1)
    apply hinj
    rw [LinearMap.comp_apply, LinearMap.comp_apply, fwd_bwd]
    have hn : fwd π' Φ N U.1 ((OModulePresheaf.ofModules π' N).res h (bwd π' Φ N U'.1 t)) =
        ((OModulePresheaf.pushforwardUnit π' Φ).twist N).res h (fwd π' Φ N U'.1 (bwd π' Φ N U'.1
          t)) :=
      congrArg (fun f => f (bwd π' Φ N U'.1 t)) ((fwdHom π' Φ N).naturality h)
    rw [hn, fwd_bwd]

end twistIso

theorem cechEquiv_twist_pushforwardUnit_of_isIso
    {R : Type u} [CommRing R] {P P' : Scheme.{u}} (π' : P' ⟶ Spec (CommRingCat.of R)) [IsSeparated
      π']
    (Φ : P ⟶ P') [IsIso Φ] (N : P'.Modules) (𝔚' : P'.OrderedAffineCover) :
    Nonempty (((OModulePresheaf.pushforwardUnit π' Φ).twist N).H0 𝔚' ≃ₗ[R]
      (OModulePresheaf.ofModules π' N).H0 𝔚') ∧
      ∀ i : ℕ, Nonempty (((OModulePresheaf.pushforwardUnit π' Φ).twist N).HSucc 𝔚' i ≃ₗ[R]
        (OModulePresheaf.ofModules π' N).HSucc 𝔚' i) :=
  cechEquiv_of_affHom_inverse (bwdHom π' Φ N) (fwdHom π' Φ N)
    (fun U t => fwd_bwd π' Φ N U.1 t) (fun U m => bwd_fwd π' Φ N U.1 m) 𝔚'

end P2mAutInv

end

open P2mAutInv in
theorem _root_.AlgebraicGeometry.OModulePresheaf.cechFinrank_ofModules_pullback_eq_of_isIso
    {R : Type u} [CommRing R] {P P' : Scheme.{u}} (π' : P' ⟶ Spec (CommRingCat.of R)) [IsSeparated
      π']
    (Φ : P ⟶ P') [IsIso Φ]
    (N : P'.Modules) (hN : Scheme.Modules.IsInvertible N)
    (𝔚 : P.OrderedAffineCover) (𝔚' : P'.OrderedAffineCover) (n : ℕ) :
    (OModulePresheaf.ofModules (Φ ≫ π') ((Scheme.Modules.pullback Φ).obj N)).cechFinrank 𝔚 n =
      (OModulePresheaf.ofModules π' N).cechFinrank 𝔚' n := by
  classical
  have htriv := hN.exists_trivialization
  have htrivP : ∀ x : P, ∃ U : P.Opens, x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj ((Scheme.Modules.pullback Φ).obj N) ≅
        SheafOfModules.unit U.toScheme.ringCatSheaf) := (hN.pullback Φ).exists_trivialization
  have : IsSeparated (Φ ≫ π') := inferInstance
  have hq := OModulePresheaf.isQuasicoherent_ofModules_of_locallyTrivial (Φ ≫ π')
    ((Scheme.Modules.pullback Φ).obj N) htrivP
  obtain ⟨⟨e0⟩, eS⟩ :=
    OModulePresheaf.nonempty_cechEquiv_ofModules_of_isQuasicoherent_of_isSeparated (Φ ≫ π')
    ((Scheme.Modules.pullback Φ).obj N) hq 𝔚 (𝔚'.comap Φ)
  obtain ⟨⟨f0⟩, fS⟩ :=
    OModulePresheaf.nonempty_cechEquiv_ofModules_pullback_comap_twist_pushforwardUnit π' Φ 𝔚' N
    htriv
  obtain ⟨⟨g0⟩, gS⟩ := cechEquiv_twist_pushforwardUnit_of_isIso π' Φ N 𝔚'
  cases n with
  | zero =>
    rw [OModulePresheaf.cechFinrank_zero, OModulePresheaf.cechFinrank_zero]
    exact ((e0.trans f0).trans g0).finrank_eq
  | succ i =>
    rw [OModulePresheaf.cechFinrank_succ, OModulePresheaf.cechFinrank_succ]
    obtain ⟨e⟩ := eS i; obtain ⟨f⟩ := fS i; obtain ⟨g⟩ := gS i
    exact ((e.trans f).trans g).finrank_eq
end OModulePresheaf_cechFinrank_ofModules_pullback_eq_of_isIso
end AlgebraicCurves.Cohomology.Cech.Proofs
end ProofImplementation

attribute [-instance] AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero
attribute [-instance] AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx
attribute [-instance] AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype
attribute [-instance] AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder
attribute [-instance] AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx
attribute [-simp] AlgebraicGeometry.OModulePresheaf.prod_obj
  AlgebraicGeometry.OModulePresheaf.restrOpen_obj
  AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq
  AlgebraicGeometry.OModulePresheaf.pushforward_obj
  AlgebraicGeometry.OModulePresheaf.im_obj
  AlgebraicGeometry.OModulePresheaf.pow_obj
  AlgebraicGeometry.OModulePresheaf.fstHom_app
  AlgebraicGeometry.OModulePresheaf.ker_obj
  AlgebraicGeometry.OModulePresheaf.coker_obj
  AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U
  AlgebraicGeometry.OModulePresheaf.sndHom_app
  AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq
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
  AlgebraicGeometry.OModulePresheaf.Hom.comp_app
  AlgebraicGeometry.OModulePresheaf.SES.mk.injEq
  AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq
  AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply
  AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq
  AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq
  AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U
