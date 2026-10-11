/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_exteriorPower_map_app_unit_iotaMulti_eq_det_smul.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.LinearAlgebra.Determinant
import AlgebraicCurves.Geometry.Sheaves.ModulesDet

/-!
# Scheme Modules exterior Power map app unit iota Multi eq det smul
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs.ExteriorPowerDeterminant

universe u

open _root_.CategoryTheory
open _root_.AlgebraicGeometry
open _root_.Opposite

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace Modules
open _root_.AlgebraicGeometry.Scheme.Modules
namespace Ws31H2
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

open _root_.CategoryTheory
open _root_.AlgebraicGeometry
open _root_.Opposite

lemma alternatingMap_apply_matrix_smul {A : Type*} [CommRing A] {M N : Type*} [AddCommGroup M]
    [Module A M] [AddCommGroup N] [Module A N] {n : ℕ} (g : M [⋀^Fin n]→ₗ[A] N) (f : Fin n → M)
    (a : Matrix (Fin n) (Fin n) A) :
    g (fun j => ∑ i, a i j • f i) = a.det • g f := by
  classical
  let L : (Fin n → A) →ₗ[A] M := Fintype.linearCombination A f
  let b : Module.Basis (Fin n) A (Fin n → A) := Pi.basisFun A (Fin n)
  have hL : ∀ i, L (b i) = f i := fun i => by
    simp [L, b, Fintype.linearCombination_apply_single]
  have key : g.compLinearMap L = b.det.smulRight (g f) := by
    refine Module.Basis.ext_alternating b fun v hv => ?_
    let σ : Equiv.Perm (Fin n) := Equiv.ofBijective v (Finite.injective_iff_bijective.1 hv)
    have h1 : (fun i => L (b (v i))) = f ∘ σ := funext fun i => hL (v i)
    have h2 : (fun i => b (v i)) = b ∘ σ := rfl
    rw [AlternatingMap.compLinearMap_apply, h1, AlternatingMap.map_perm,
      AlternatingMap.smulRight_apply,
      h2, AlternatingMap.map_perm, Module.Basis.det_self]
    simp [Units.smul_def, Int.cast_smul_eq_zsmul]
  have h3 : (fun j => ∑ i, a i j • f i) = fun j => L (a.transpose j) := by
    funext j
    simp [L, Fintype.linearCombination_apply, Matrix.transpose_apply]
  have h4 := congrArg (fun G : (Fin n → A) [⋀^Fin n]→ₗ[A] N => G (fun j => a.transpose j)) key
  simp only [AlternatingMap.compLinearMap_apply, AlternatingMap.smulRight_apply] at h4
  rw [h3, h4]
  have hdet : b.det (fun j => a.transpose j) = a.det :=
    (Pi.basisFun_det_apply (R := A) (fun j i => a i j)).trans (Matrix.det_transpose a)
  exact congrArg (fun r : A => r • g f) hdet

variable {X : Scheme.{u}} (n : ℕ)

/-- The presheaf exterior power of a module sheaf. -/
noncomputable abbrev pre (M : X.Modules) : X.PresheafOfModules :=
  (presheafExteriorPower X n).obj M.val

/-- The map from exterior powers of local sections to sections of the determinant sheaf. -/
noncomputable def toSh (M : X.Modules) (W : X.Opens) :
    (⋀[Γ(X, W)]^n Γ(M, W)) → Γ(det n M, W) :=
  fun w => ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app (pre n
    M)).app
    (op W) (show (pre n M).obj (op W) from w)

lemma toSh_smul (M : X.Modules) (W : X.Opens) (r : Γ(X, W)) (w : ⋀[Γ(X, W)]^n Γ(M, W)) :
    toSh n M W (r • w) = r • toSh n M W w :=
  (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app (pre n M)).app
    (op W)).hom.map_smul r _

/-- The exterior power map on local sections induced by a morphism of module sheaves. -/
noncomputable def preApp {M N : X.Modules} (φ : M ⟶ N) (W : X.Opens) (w : ⋀[Γ(X, W)]^n Γ(M, W)) :
    ⋀[Γ(X, W)]^n Γ(N, W) :=
  show ⋀[Γ(X, W)]^n Γ(N, W) from
    ((presheafExteriorPower X n).map φ.val).app (op W) (show (pre n M).obj (op W) from w)

lemma map_app_toSh {M N : X.Modules} (φ : M ⟶ N) (W : X.Opens) (w : ⋀[Γ(X, W)]^n Γ(M, W)) :
    ((exteriorPower X n).map φ).app W (toSh n M W w) = toSh n N W (preApp n φ W w) := by
  have hnat := (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.naturality
    ((presheafExteriorPower X n).map φ.val)
  have hx := congrArg (fun θ => (PresheafOfModules.Hom.app θ (op W)).hom (show (pre n M).obj (op
    W) from w))
    hnat
  exact hx.symm

lemma preApp_ιMulti {M N : X.Modules} (φ : M ⟶ N) (W : X.Opens) (m : Fin n → Γ(M, W)) :
    preApp n φ W (exteriorPower.ιMulti Γ(X, W) n m) = exteriorPower.ιMulti Γ(X, W) n (fun i =>
      φ.app W (m i)) :=
  PresheafOfModules.exteriorPowerMap_app_ιMulti n φ.val (op W) m

theorem map_app_toSh_ιMulti_eq_det_smul {M N : X.Modules} (φ : M ⟶ N) {U : X.Opens}
    (e : Fin n → Γ(M, U)) (f : Fin n → Γ(N, U)) (a : Matrix (Fin n) (Fin n) Γ(X, U))
    (ha : ∀ j, φ.app U (e j) = ∑ i, a i j • f i) :
    ((exteriorPower X n).map φ).app U (toSh n M U (exteriorPower.ιMulti Γ(X, U) n e)) =
      a.det • toSh n N U (exteriorPower.ιMulti Γ(X, U) n f) := by
  rw [map_app_toSh, preApp_ιMulti, show (fun i => φ.app U (e i)) = fun j => ∑ i, a i j • f i from
    funext ha,
    alternatingMap_apply_matrix_smul, toSh_smul]

end AlgebraicGeometry.Scheme.Modules.Ws31H2

theorem _root_.AlgebraicGeometry.Scheme.Modules.exteriorPower_map_app_unit_iotaMulti_eq_det_smul
    {X : Scheme.{u}} {n : ℕ} {M N : X.Modules} (φ : M ⟶ N) {U : X.Opens}
    (e : Fin n → Γ(M, U)) (f : Fin n → Γ(N, U)) (a : Matrix (Fin n) (Fin n) Γ(X, U))
    (ha : ∀ j, φ.app U (e j) = ∑ i, a i j • f i) :
    ((Scheme.Modules.exteriorPower X n).map φ).app U
        (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
            ((Scheme.Modules.presheafExteriorPower X n).obj M.val)).app (op U)
          (show ((Scheme.Modules.presheafExteriorPower X n).obj M.val).obj (op U) from
            exteriorPower.ιMulti (M := Γ(M, U)) Γ(X, U) n e)) =
      a.det • (show Γ(Scheme.Modules.det n N, U) from
        (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
            ((Scheme.Modules.presheafExteriorPower X n).obj N.val)).app (op U)
          (show ((Scheme.Modules.presheafExteriorPower X n).obj N.val).obj (op U) from
            exteriorPower.ιMulti (M := Γ(N, U)) Γ(X, U) n f))) :=
  AlgebraicGeometry.Scheme.Modules.Ws31H2.map_app_toSh_ιMulti_eq_det_smul n φ e f a ha
end AlgebraicCurves.Geometry.Sheaves.Proofs.ExteriorPowerDeterminant
end ProofImplementation
