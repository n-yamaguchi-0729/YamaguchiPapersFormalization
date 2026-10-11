/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_iso.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Cohomology.Sheaves.OModulePresheafOfModules

/-!
# OModule Presheaf nonempty cech Equiv of Modules of iso
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Cech.Proofs.OModulePresheaf_nonempty_cechEquiv_ofModules_of_iso

noncomputable section

universe u

open _root_.CategoryTheory
open _root_.AlgebraicGeometry
open _root_.Opposite

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace OModulePresheaf
open _root_.AlgebraicGeometry.OModulePresheaf
open _root_.AlgebraicGeometry.OModulePresheaf
open _root_.AlgebraicGeometry
namespace IsoTransfer

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}

/-- A family of linear equivalences on sections commuting with restriction. -/
structure LinIso (F G : OModulePresheaf π) where
  /-- The linear equivalence on the sections of each open. -/
  app : ∀ U : V.Opens, F.obj U ≃ₗ[R] G.obj U
  /-- The section equivalences commute with restriction maps. -/
  res_app : ∀ {U U' : V.Opens} (h : U ≤ U') (x : F.obj U'), G.res h (app U' x) = app U (F.res h x)

variable {F G : OModulePresheaf π} (φ : LinIso F G) (K : V.OrderedAffineCover)

/-- The pointwise linear equivalence induced on the ordered-cover cochains. -/
def cochainEquiv (i : ℕ) : F.cochain K i ≃ₗ[R] G.cochain K i :=
  LinearEquiv.piCongrRight fun s => φ.app (K.inter s)

theorem cochainEquiv_apply (i : ℕ) (c : F.cochain K i) (s : K.Idx i) :
    cochainEquiv φ K i c s = φ.app (K.inter s) (c s) := rfl

theorem d_cochainEquiv (i : ℕ) (c : F.cochain K i) :
    G.d K i (cochainEquiv φ K i c) = cochainEquiv φ K (i + 1) (F.d K i c) := by
  funext s
  rw [d_apply, cochainEquiv_apply, d_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [cochainEquiv_apply, φ.res_app, map_zsmul]

theorem d_comp_cochainEquiv (i : ℕ) :
    G.d K i ∘ₗ (cochainEquiv φ K i).toLinearMap = (cochainEquiv φ K (i + 1)).toLinearMap ∘ₗ F.d
      K i :=
  LinearMap.ext fun c => d_cochainEquiv φ K i c

theorem map_ker (i : ℕ) :
    Submodule.map (cochainEquiv φ K i).toLinearMap (LinearMap.ker (F.d K i)) = LinearMap.ker
      (G.d K i) := by
  ext c
  rw [Submodule.mem_map_equiv, LinearMap.mem_ker, LinearMap.mem_ker]
  constructor
  · intro h
    have : c = cochainEquiv φ K i ((cochainEquiv φ K i).symm c) := ((cochainEquiv φ K
      i).apply_symm_apply c).symm
    rw [this, d_cochainEquiv, h, map_zero]
  · intro h
    apply (cochainEquiv φ K (i + 1)).injective
    rw [← d_cochainEquiv, LinearEquiv.apply_symm_apply, h, map_zero]

/-- The induced linear equivalence on degree-zero cohomology. -/
def H0Equiv : F.H0 K ≃ₗ[R] G.H0 K :=
  (cochainEquiv φ K 0).ofSubmodules _ _ (map_ker φ K 0)

/-- The linear equivalence on the kernels of corresponding Čech differentials. -/
def kerEquiv (i : ℕ) : LinearMap.ker (F.d K (i + 1)) ≃ₗ[R] LinearMap.ker (G.d K (i + 1)) :=
  (cochainEquiv φ K (i + 1)).ofSubmodules _ _ (map_ker φ K (i + 1))

theorem kerEquiv_apply_coe (i : ℕ) (x : LinearMap.ker (F.d K (i + 1))) :
    ((kerEquiv φ K i x : LinearMap.ker (G.d K (i + 1))) : G.cochain K (i + 1)) = cochainEquiv φ
      K (i + 1) x := rfl

theorem map_boundaries (i : ℕ) :
    Submodule.map (kerEquiv φ K i).toLinearMap
        ((LinearMap.range (F.d K i)).comap (LinearMap.ker (F.d K (i + 1))).subtype)
      = (LinearMap.range (G.d K i)).comap (LinearMap.ker (G.d K (i + 1))).subtype := by
  ext y
  rw [Submodule.mem_map_equiv, Submodule.mem_comap, Submodule.mem_comap, Submodule.subtype_apply,
    Submodule.subtype_apply, LinearMap.mem_range, LinearMap.mem_range]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨cochainEquiv φ K i c, ?_⟩
    rw [d_cochainEquiv, hc]
    have : kerEquiv φ K i ((kerEquiv φ K i).symm y) = y := (kerEquiv φ K i).apply_symm_apply y
    exact (congrArg (fun z : LinearMap.ker (G.d K (i + 1)) => (z : G.cochain K (i + 1))) this)
  · rintro ⟨c, hc⟩
    refine ⟨(cochainEquiv φ K i).symm c, ?_⟩
    apply (cochainEquiv φ K (i + 1)).injective
    rw [← d_cochainEquiv, LinearEquiv.apply_symm_apply, hc]
    exact (congrArg (fun z : LinearMap.ker (G.d K (i + 1)) => (z : G.cochain K (i + 1)))
      ((kerEquiv φ K i).apply_symm_apply y)).symm

/-- The induced linear equivalence on positive-degree Čech cohomology. -/
def HSuccEquiv (i : ℕ) : F.HSucc K i ≃ₗ[R] G.HSucc K i :=
  Submodule.Quotient.equiv _ _ (kerEquiv φ K i) (map_boundaries φ K i)
include φ in
private theorem cechFinite_iff : F.CechFinite K ↔ G.CechFinite K := by
  rw [OModulePresheaf.cechFinite_iff, OModulePresheaf.cechFinite_iff]
  exact and_congr (⟨fun _ => Module.Finite.equiv (H0Equiv φ K), fun _ => Module.Finite.equiv
    (H0Equiv φ K).symm⟩)
    (forall_congr' fun i => ⟨fun _ => Module.Finite.equiv (HSuccEquiv φ K i),
      fun _ => Module.Finite.equiv (HSuccEquiv φ K i).symm⟩)

/-- The restriction-compatible linear equivalences induced by an isomorphism of scheme modules. -/
def ofIso {M M' : V.Modules} (e : M ≅ M') : LinIso (ofModules π M) (ofModules π M') where
  app U :=
    { toFun := fun x => (e.hom.app U).hom x
      invFun := fun y => (e.inv.app U).hom y
      map_add' := fun x y => (e.hom.app U).hom.map_add x y
      map_smul' := fun r x => by
        exact (congrArg (fun y : (ofModules π M).obj U => (e.hom.app U).hom y)
          (ofModules_algebraMap_smul π M U r x)).trans
          ((Scheme.Modules.Hom.app_smul e.hom
            ((Scheme.TwoAffineOpenCover.algebraOfHom π U).algebraMap r)
            (show Γ(M, U) from x)).trans
            (ofModules_algebraMap_smul π M' U r
              (show (ofModules π M').obj U from (e.hom.app U).hom x)).symm)
      left_inv := fun x => by
        change (e.hom.app U ≫ e.inv.app U).hom x = x
        rw [← Scheme.Modules.Hom.comp_app, e.hom_inv_id, Scheme.Modules.Hom.id_app]; rfl
      right_inv := fun y => by
        change (e.inv.app U ≫ e.hom.app U).hom y = y
        rw [← Scheme.Modules.Hom.comp_app, e.inv_hom_id, Scheme.Modules.Hom.id_app]; rfl }
  res_app {U U'} h x := by
    change (M'.presheaf.map (homOfLE h).op) ((e.hom.app U').hom x) = (e.hom.app U).hom
      ((M.presheaf.map (homOfLE h).op) x)
    have hnat := e.hom.mapPresheaf.naturality (homOfLE h).op
    have hx := ConcreteCategory.congr_hom hnat x
    simp only [Scheme.Modules.mapPresheaf_app] at hx
    exact hx.symm

end IsoTransfer
end AlgebraicGeometry.OModulePresheaf

open AlgebraicGeometry.OModulePresheaf.IsoTransfer in
theorem _root_.AlgebraicGeometry.OModulePresheaf.nonempty_cechEquiv_ofModules_of_iso
    {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) {M M' : V.Modules} (e : M
      ≅ M')
    (K : V.OrderedAffineCover) :
    Nonempty ((OModulePresheaf.ofModules π M).H0 K ≃ₗ[R] (OModulePresheaf.ofModules π M').H0 K) ∧
      (∀ i : ℕ, Nonempty ((OModulePresheaf.ofModules π M).HSucc K i ≃ₗ[R]
        (OModulePresheaf.ofModules π M').HSucc K i)) ∧
      ((OModulePresheaf.ofModules π M).CechFinite K ↔ (OModulePresheaf.ofModules π
        M').CechFinite K) :=
  ⟨⟨H0Equiv (ofIso (π := π) e) K⟩, fun i => ⟨HSuccEquiv (ofIso (π := π) e) K i⟩, cechFinite_iff
    (ofIso (π := π) e) K⟩

end
end AlgebraicCurves.Cohomology.Cech.Proofs.OModulePresheaf_nonempty_cechEquiv_ofModules_of_iso
end ProofImplementation
