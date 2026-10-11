/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_exists_cochain_baseChange_equiv_of_locallyTrivial.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.LinearAlgebra.TensorProduct.Pi
import AlgebraicCurves.Geometry.Schemes.OrderedAffineCoverComap
import AlgebraicCurves.Cohomology.Sheaves.OModulePresheafOfModules
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_exists_linearEquiv_sections_baseChange_of_locallyTrivial

/-! Base change for Čech cochains of locally trivial sheaves of modules. -/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Sheaves.Proofs.CochainBaseChange
attribute [-simp] AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.TensorProduct
open _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover

noncomputable section

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace OModulePresheaf
open _root_.AlgebraicGeometry.OModulePresheaf
namespace CechBaseChange
open _root_.AlgebraicGeometry.OModulePresheaf
open _root_.AlgebraicGeometry

section EqRes
variable {R : Type u} [CommRing R] {Y : Scheme.{u}} {ρ : Y ⟶ Spec (.of R)} (G : OModulePresheaf ρ)

/-- The linear equivalence transporting sections along equality of open subsets. -/
def eqRes {U U' : Y.Opens} (h : U = U') : G.obj U' ≃ₗ[R] G.obj U :=
  LinearEquiv.ofLinearMap (G.res h.le) (G.res h.ge)
    (by rw [← G.res_comp h.le h.ge]; exact G.res_refl U)
    (by rw [← G.res_comp h.ge h.le]; exact G.res_refl U')

theorem eqRes_apply {U U' : Y.Opens} (h : U = U') (x : G.obj U') : eqRes G h x = G.res h.le x := rfl

theorem res_res_eq_res_res {U V V' W : Y.Opens} (h₁ : U ≤ V) (h₂ : V ≤ W) (h₃ : U ≤ V')
    (h₄ : V' ≤ W) (x : G.obj W) :
    G.res h₁ (G.res h₂ x) = G.res h₃ (G.res h₄ x) := by
  rw [G.res_res, G.res_res]

end EqRes

section Affine
variable {R : Type u} [CommRing R] {X : Scheme.{u}} (π : X ⟶ Spec (.of R))
  (𝒰 : X.OrderedAffineCover)

theorem isAffineOpen_inf_of_isSeparated' [IsSeparated π] {U W : X.Opens} (hU : IsAffineOpen U)
    (hW : IsAffineOpen W) : IsAffineOpen (U ⊓ W) := by
  have : IsAffineHom (pullback.diagonal π) := inferInstance
  exact isAffineHom_diagonal_iff.mp this ⊤ (isAffineOpen_top _)
    U (by rw [Scheme.Hom.preimage_top]; exact le_top)
    W (by rw [Scheme.Hom.preimage_top]; exact le_top) hU hW

theorem isAffineOpen_inter' [IsSeparated π] {i : ℕ} (s : 𝒰.Idx i) : IsAffineOpen (𝒰.inter s) := by
  suffices h : ∀ (n : ℕ) (t : Fin (n + 1) → 𝒰.ι), IsAffineOpen (⨅ j, 𝒰.U (t j)) from h i s.1
  intro n
  induction n with
  | zero =>
    intro t
    have h1 : (⨅ j : Fin 1, 𝒰.U (t j)) = 𝒰.U (t 0) :=
      le_antisymm (iInf_le _ 0) (le_iInf fun j => by fin_cases j; exact le_rfl)
    rw [h1]; exact 𝒰.isAffineOpen (t 0)
  | succ m ih =>
    intro t
    have hsplit : (⨅ j : Fin (m + 2), 𝒰.U (t j))
        = 𝒰.U (t 0) ⊓ (⨅ j : Fin (m + 1), 𝒰.U (t j.succ)) :=
      le_antisymm (le_inf (iInf_le _ 0) (le_iInf fun j => iInf_le _ j.succ))
        (le_iInf fun j => Fin.cases inf_le_left (fun k => inf_le_right.trans (iInf_le _ k)) j)
    rw [hsplit]
    exact isAffineOpen_inf_of_isSeparated' π (𝒰.isAffineOpen (t 0)) (ih (t ∘ Fin.succ))

end Affine

section Main

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (π : X ⟶ Spec (.of R)) (M : X.Modules)
  (A : Type u) [CommRing A] [Algebra R A]

/-- The adjunction unit, with both section types owned by the module presheaves. -/
def unitSections (U : X.Opens) :
    (OModulePresheaf.ofModules π M).obj U →+
      (OModulePresheaf.ofModules (Limits.pullback.snd π (specMap R A))
        ((Scheme.Modules.pullback (Limits.pullback.fst π (specMap R A))).obj M)).obj
          ((Limits.pullback.fst π (specMap R A)) ⁻¹ᵁ U) :=
  (((Scheme.Modules.pullbackPushforwardAdjunction
    (Limits.pullback.fst π (specMap R A))).unit.app M).app U).hom

theorem unit_res {U U' : X.Opens} (h : U' ≤ U)
    (h' : (Limits.pullback.fst π (specMap R A)) ⁻¹ᵁ U'
      ≤ (Limits.pullback.fst π (specMap R A)) ⁻¹ᵁ U)
    (m : (OModulePresheaf.ofModules π M).obj U) :
    unitSections π M A U' ((OModulePresheaf.ofModules π M).res h m)
      = (OModulePresheaf.ofModules (Limits.pullback.snd π (specMap R A))
          ((Scheme.Modules.pullback (Limits.pullback.fst π (specMap R A))).obj M)).res h'
            (unitSections π M A U m) := by
  have hn := ((Scheme.Modules.pullbackPushforwardAdjunction
    (Limits.pullback.fst π (specMap R A))).unit.app M).mapPresheaf.naturality (homOfLE h).op
  have hx := ConcreteCategory.congr_hom hn m
  refine hx.trans ?_
  have : ((TopologicalSpace.Opens.map (Limits.pullback.fst π (specMap R A)).base).map (homOfLE h))
      = homOfLE h' :=
    Subsingleton.elim _ _
  change (((Scheme.Modules.pullback (Limits.pullback.fst π (specMap R A))).obj M).presheaf.map
    ((TopologicalSpace.Opens.map (Limits.pullback.fst π (specMap R A)).base).map
      (homOfLE h)).op) _ = _
  rw [this]
  rfl

theorem tmul_eq_smul_one_tmul {N : Type u} [AddCommGroup N] [Module R N] (a : A) (n : N) :
    a ⊗ₜ[R] n = a • ((1 : A) ⊗ₜ[R] n) := by
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

variable [IsSeparated π] (𝒰 : X.OrderedAffineCover)
  (htriv : ∀ x : X, ∃ (V : X.Opens), x ∈ V ∧
    Nonempty ((Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit V.toScheme.ringCatSheaf))

omit [IsSeparated π] in
/-- Base change preserves the increasing tuple indexing an intersection. -/
def idxEquiv (i : ℕ) : 𝒰.Idx i ≃ (𝒰.baseChange π A).Idx i where
  toFun s := s
  invFun s := s
  left_inv _ := rfl
  right_inv _ := rfl

omit [IsSeparated π] in
theorem idxEquiv_face {i : ℕ} (s : 𝒰.Idx (i + 1)) (j : Fin (i + 2)) :
    idxEquiv π A 𝒰 i (𝒰.face s j)
      = (𝒰.baseChange π A).face (idxEquiv π A 𝒰 (i + 1) s) j :=
  rfl

omit [IsSeparated π] in
theorem inter_idxEquiv {i : ℕ} (s : 𝒰.Idx i) :
    (𝒰.baseChange π A).inter (idxEquiv π A 𝒰 i s)
      = (Limits.pullback.fst π (specMap R A)) ⁻¹ᵁ 𝒰.inter s :=
  𝒰.baseChange_inter π A s

omit [IsSeparated π] in
/-- The pullback unit on the intersection indexed by a Čech simplex. -/
def unitAt {i : ℕ} (s : 𝒰.Idx i) :
    (OModulePresheaf.ofModules π M).obj (𝒰.inter s) →+
      (OModulePresheaf.ofModules (Limits.pullback.snd π (specMap R A))
        ((Scheme.Modules.pullback (Limits.pullback.fst π (specMap R A))).obj M)).obj
          ((𝒰.baseChange π A).inter (idxEquiv π A 𝒰 i s)) :=
  ((OModulePresheaf.ofModules (Limits.pullback.snd π (specMap R A))
      ((Scheme.Modules.pullback (Limits.pullback.fst π (specMap R A))).obj M)).res
      (inter_idxEquiv π A 𝒰 s).le).toAddMonoidHom.comp
    (unitSections π M A (𝒰.inter s))

omit [IsSeparated π] in
theorem unitAt_apply {i : ℕ} (s : 𝒰.Idx i) (m : (OModulePresheaf.ofModules π M).obj (𝒰.inter s)) :
    unitAt π M A 𝒰 s m
      = (OModulePresheaf.ofModules (Limits.pullback.snd π (specMap R A))
          ((Scheme.Modules.pullback (Limits.pullback.fst π (specMap R A))).obj M)).res
            (inter_idxEquiv π A 𝒰 s).le
          (unitSections π M A (𝒰.inter s) m) :=
  rfl

include htriv in
theorem exists_eSimplex {i : ℕ} (s : 𝒰.Idx i) :
    ∃ e : A ⊗[R] (OModulePresheaf.ofModules π M).obj (𝒰.inter s) ≃ₗ[A]
        (OModulePresheaf.ofModules (Limits.pullback.snd π (specMap R A))
          ((Scheme.Modules.pullback (Limits.pullback.fst π (specMap R A))).obj M)).obj
            ((𝒰.baseChange π A).inter (idxEquiv π A 𝒰 i s)),
      ∀ m, e ((1 : A) ⊗ₜ[R] m) = unitAt π M A 𝒰 s m := by
  obtain ⟨e, he⟩ := Scheme.Modules.exists_linearEquiv_sections_baseChange_of_locallyTrivial
    π M htriv
    (𝒰.inter s) (isAffineOpen_inter' π 𝒰 s) A
  refine ⟨e.trans (eqRes (OModulePresheaf.ofModules (Limits.pullback.snd π (specMap R A))
      ((Scheme.Modules.pullback (Limits.pullback.fst π (specMap R A))).obj M))
        (inter_idxEquiv π A 𝒰 s)),
    fun m => ?_⟩
  exact congrArg ((OModulePresheaf.ofModules (Limits.pullback.snd π (specMap R A))
      ((Scheme.Modules.pullback (Limits.pullback.fst π (specMap R A))).obj M)).res
        (inter_idxEquiv π A 𝒰 s).le)
    (he m)

/-- The base-change equivalence on the affine intersection of a Čech simplex. -/
def eSimplex {i : ℕ} (s : 𝒰.Idx i) :
    A ⊗[R] (OModulePresheaf.ofModules π M).obj (𝒰.inter s) ≃ₗ[A]
      (OModulePresheaf.ofModules (Limits.pullback.snd π (specMap R A))
        ((Scheme.Modules.pullback (Limits.pullback.fst π (specMap R A))).obj M)).obj
          ((𝒰.baseChange π A).inter (idxEquiv π A 𝒰 i s)) :=
  (exists_eSimplex π M A 𝒰 htriv s).choose

theorem eSimplex_one_tmul {i : ℕ} (s : 𝒰.Idx i)
    (m : (OModulePresheaf.ofModules π M).obj (𝒰.inter s)) :
    eSimplex π M A 𝒰 htriv s ((1 : A) ⊗ₜ[R] m) = unitAt π M A 𝒰 s m :=
  (exists_eSimplex π M A 𝒰 htriv s).choose_spec m

theorem eSimplex_tmul {i : ℕ} (s : 𝒰.Idx i) (a : A)
    (m : (OModulePresheaf.ofModules π M).obj (𝒰.inter s)) :
    eSimplex π M A 𝒰 htriv s (a ⊗ₜ[R] m) = a • unitAt π M A 𝒰 s m := by
  rw [tmul_eq_smul_one_tmul (R := R) A a m, map_smul, eSimplex_one_tmul]

/-- The degreewise base-change equivalence for Čech cochains. -/
def E (i : ℕ) :
    A ⊗[R] (OModulePresheaf.ofModules π M).cochain 𝒰 i ≃ₗ[A]
      (OModulePresheaf.ofModules (Limits.pullback.snd π (specMap R A))
        ((Scheme.Modules.pullback (Limits.pullback.fst π (specMap R A))).obj M)).cochain
          (𝒰.baseChange π A) i :=
  ((TensorProduct.piRight R A A
    (fun s : 𝒰.Idx i => (OModulePresheaf.ofModules π M).obj (𝒰.inter s))).trans
    (LinearEquiv.piCongrRight fun s : 𝒰.Idx i => eSimplex π M A 𝒰 htriv s)).trans
      (LinearEquiv.piCongrLeft A
        (fun s : (𝒰.baseChange π A).Idx i =>
          (OModulePresheaf.ofModules (Limits.pullback.snd π (specMap R A))
            ((Scheme.Modules.pullback (Limits.pullback.fst π (specMap R A))).obj M)).obj
              ((𝒰.baseChange π A).inter s))
        (idxEquiv π A 𝒰 i))

theorem E_tmul (i : ℕ) (a : A) (c : (OModulePresheaf.ofModules π M).cochain 𝒰 i) (s : 𝒰.Idx i) :
    E π M A 𝒰 htriv i (a ⊗ₜ[R] c) (idxEquiv π A 𝒰 i s)
      = a • unitAt π M A 𝒰 s (c s) := by
  change eSimplex π M A 𝒰 htriv s
      (TensorProduct.piRight R A A
        (fun s : 𝒰.Idx i => (OModulePresheaf.ofModules π M).obj (𝒰.inter s))
        (a ⊗ₜ[R] c) s) = _
  rw [TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul, eSimplex_tmul]

theorem E_one_tmul (i : ℕ) (c : (OModulePresheaf.ofModules π M).cochain 𝒰 i) (s : 𝒰.Idx i) :
    E π M A 𝒰 htriv i ((1 : A) ⊗ₜ[R] c) (idxEquiv π A 𝒰 i s)
      = unitAt π M A 𝒰 s (c s) := by
  rw [E_tmul, one_smul]

omit [IsSeparated π] in
theorem unitAt_res {i i' : ℕ} (s : 𝒰.Idx i) (t : 𝒰.Idx i') (h : 𝒰.inter t ≤ 𝒰.inter s)
    (hA : (𝒰.baseChange π A).inter (idxEquiv π A 𝒰 i' t)
      ≤ (𝒰.baseChange π A).inter (idxEquiv π A 𝒰 i s))
    (m : (OModulePresheaf.ofModules π M).obj (𝒰.inter s)) :
    unitAt π M A 𝒰 t ((OModulePresheaf.ofModules π M).res h m)
      = (OModulePresheaf.ofModules (Limits.pullback.snd π (specMap R A))
          ((Scheme.Modules.pullback (Limits.pullback.fst π (specMap R A))).obj M)).res hA
            (unitAt π M A 𝒰 s m) := by
  rw [unitAt_apply, unitAt_apply, OModulePresheaf.res_res]
  have h' : (Limits.pullback.fst π (specMap R A)) ⁻¹ᵁ 𝒰.inter t
    ≤ (Limits.pullback.fst π (specMap R A)) ⁻¹ᵁ 𝒰.inter s :=
    Scheme.Hom.preimage_mono _ h
  rw [unit_res π M A h h' m, OModulePresheaf.res_res]

theorem E_d_one_tmul (i : ℕ) (c : (OModulePresheaf.ofModules π M).cochain 𝒰 i) :
    E π M A 𝒰 htriv (i + 1) ((1 : A) ⊗ₜ[R] (OModulePresheaf.ofModules π M).d 𝒰 i c)
      = (OModulePresheaf.ofModules (Limits.pullback.snd π (specMap R A))
          ((Scheme.Modules.pullback (Limits.pullback.fst π (specMap R A))).obj M)).d
            (𝒰.baseChange π A) i
          (E π M A 𝒰 htriv i ((1 : A) ⊗ₜ[R] c)) := by
  funext t
  obtain ⟨t, rfl⟩ := (idxEquiv π A 𝒰 (i + 1)).surjective t
  rw [E_one_tmul, OModulePresheaf.d_apply, OModulePresheaf.d_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul]
  have hA : (𝒰.baseChange π A).inter (idxEquiv π A 𝒰 (i + 1) t)
      ≤ (𝒰.baseChange π A).inter (idxEquiv π A 𝒰 i (𝒰.face t j)) :=
    (𝒰.baseChange π A).inter_le_inter_face (idxEquiv π A 𝒰 (i + 1) t) j
  have hu := unitAt_res π M A 𝒰 (𝒰.face t j) t (𝒰.inter_le_inter_face t j)
    hA (c (𝒰.face t j))
  have he := congrArg
    ((OModulePresheaf.ofModules (Limits.pullback.snd π (specMap R A))
      ((Scheme.Modules.pullback (Limits.pullback.fst π (specMap R A))).obj M)).res hA)
    (E_one_tmul π M A 𝒰 htriv i c (𝒰.face t j))
  exact congrArg
    (fun x : (OModulePresheaf.ofModules (Limits.pullback.snd π (specMap R A))
      ((Scheme.Modules.pullback (Limits.pullback.fst π (specMap R A))).obj M)).obj
        ((𝒰.baseChange π A).inter (idxEquiv π A 𝒰 (i + 1) t)) =>
      ((-1 : ℤ) ^ (j : ℕ)) • x)
    (hu.trans he.symm)

theorem E_d (i : ℕ) :
    (E π M A 𝒰 htriv (i + 1)).toLinearMap ∘ₗ ((OModulePresheaf.ofModules π M).d 𝒰 i).baseChange A
      = (OModulePresheaf.ofModules (Limits.pullback.snd π (specMap R A))
          ((Scheme.Modules.pullback (Limits.pullback.fst π (specMap R A))).obj M)).d
            (𝒰.baseChange π A) i
        ∘ₗ (E π M A 𝒰 htriv i).toLinearMap := by
  refine LinearMap.ext fun x => ?_
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a c =>
    simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul]
    rw [tmul_eq_smul_one_tmul (R := R) A a, tmul_eq_smul_one_tmul (R := R) A a c,
      map_smul, map_smul, map_smul]
    exact congrArg
      (fun x : (OModulePresheaf.ofModules (Limits.pullback.snd π (specMap R A))
        ((Scheme.Modules.pullback (Limits.pullback.fst π (specMap R A))).obj M)).cochain
          (𝒰.baseChange π A) (i + 1) => a • x)
      (E_d_one_tmul π M A 𝒰 htriv i c)

end Main

end AlgebraicGeometry.OModulePresheaf.CechBaseChange

end

open AlgebraicGeometry.OModulePresheaf.CechBaseChange in
theorem _root_.AlgebraicGeometry.OModulePresheaf.exists_cochain_baseChange_equiv_of_locallyTrivial
    {R : Type u} [CommRing R] {X : Scheme.{u}} (π : X ⟶ Spec (.of R)) [IsSeparated π]
    (𝒰 : X.OrderedAffineCover) (M : X.Modules)
    (htriv : ∀ x : X, ∃ (V : X.Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit V.toScheme.ringCatSheaf))
    (A : Type u) [CommRing A] [Algebra R A] :
    ∃ E : ∀ i : ℕ, A ⊗[R] (OModulePresheaf.ofModules π M).cochain 𝒰 i ≃ₗ[A]
        (OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R A))
          ((Scheme.Modules.pullback
            (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).cochain
              (𝒰.baseChange π A) i,
      (∀ i : ℕ, (E (i + 1)).toLinearMap ∘ₗ ((OModulePresheaf.ofModules π M).d 𝒰 i).baseChange A
        = (OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R A))
            ((Scheme.Modules.pullback
              (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).d
                (𝒰.baseChange π A) i
          ∘ₗ (E i).toLinearMap) ∧
      (∀ (i : ℕ) (a : A) (c : (OModulePresheaf.ofModules π M).cochain 𝒰 i) (s : 𝒰.Idx i),
        E i (a ⊗ₜ[R] c) s
          = a • (OModulePresheaf.ofModules
            (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R A))
              ((Scheme.Modules.pullback
                (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).res
              (𝒰.baseChange_inter_le π A s)
              ((((Scheme.Modules.pullbackPushforwardAdjunction
                (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R A))).unit.app M).app
                (𝒰.inter s)).hom (c s))) :=
  ⟨E π M A 𝒰 htriv, E_d π M A 𝒰 htriv, E_tmul π M A 𝒰 htriv⟩
end AlgebraicCurves.Cohomology.Sheaves.Proofs.CochainBaseChange
end ProofImplementation
