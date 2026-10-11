/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_normModule_and_app_eq_norm_smul.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.Norm.Defs
import Nyll.SchemeTheory.Modules.Monoidal
import Nyll.SchemeTheory.Modules.TensorSections
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesIhomSections
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesDet
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesNormModule
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesSectionZeroScheme
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsFrameOn_exists_isFrameOn_normModule
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_exteriorPower_map_app_unit_iotaMulti_eq_det_smul
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_whiskerRight_app_tensorSections

/-!
# Norms of local frames

The determinant of multiplication computes the coefficient of a norm-module frame.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_exists_isFrameOn_normModule_and_app_eq_norm_smul

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.Opposite

theorem _root_.AlgebraicGeometry.Scheme.Modules.exists_isFrameOn_normModule_and_app_eq_norm_smul
    {X X' : Scheme.{u}} (π : X' ⟶ X) (d : ℕ) [IsIso (Scheme.Modules.normModuleUnitEval π d)]
    {P : X'.Modules} (ι' : 𝟙_ X'.Modules ⟶ P) (U : X.Opens)
    (e : Fin d → Γ((Scheme.Modules.pushforward π).obj (𝟙_ X'.Modules), U))
    (he : ∀ (W : X.Opens) (hW : W ≤ U),
      ∃ b : Module.Basis (Fin d) Γ(X, W) Γ((Scheme.Modules.pushforward π).obj (𝟙_ X'.Modules), W),
        ∀ i, b i = ((Scheme.Modules.pushforward π).obj (𝟙_ X'.Modules)).presheaf.map (homOfLE
          hW).op (e i))
    (s : Γ(P, π ⁻¹ᵁ U)) (hs : Scheme.Modules.IsFrameOn s (π ⁻¹ᵁ U))
    (g : Γ(X', π ⁻¹ᵁ U)) (hg : ι'.app (π ⁻¹ᵁ U) (Scheme.Modules.toUnitSection _ 1) = g • s) :
    let : Algebra Γ(X, U) Γ(X', π ⁻¹ᵁ U) := (π.app U).hom.toAlgebra
    ∃ Ω : Γ(Scheme.Modules.normModule π d P, U), Scheme.Modules.IsFrameOn Ω U ∧
      (inv (Scheme.Modules.normModuleUnitEval π d) ≫ (Scheme.Modules.normModuleFunctor π d).map
        ι').app U
          (Scheme.Modules.toUnitSection U 1) = (Algebra.norm Γ(X, U) g) • Ω := by
  classical
  intro alg
  obtain ⟨q, hq, hq1, hΩ⟩ := Scheme.Modules.IsFrameOn.exists_isFrameOn_normModule π d e he hs
  refine ⟨_, hΩ, ?_⟩
  obtain ⟨b₀, hb₀⟩ := he U le_rfl
  have he' : ∀ i, b₀ i = e i := fun i => by
    rw [hb₀ i, show (homOfLE (le_refl U)).op = 𝟙 _ from Subsingleton.elim _ _,
      CategoryTheory.Functor.map_id]; rfl
  let b₁ : Module.Basis (Fin d) Γ(X, U) Γ(X', π ⁻¹ᵁ U) := Module.Basis.ofRepr
    { toFun := fun x => b₀.repr x
      invFun := fun c => b₀.repr.symm c
      map_add' := fun x y => b₀.repr.map_add x y
      map_smul' := fun r x => b₀.repr.map_smul r x
      left_inv := fun x => b₀.repr.symm_apply_apply x
      right_inv := fun c => b₀.repr.apply_symm_apply c }
  have hb₁ : ∀ i, b₁ i = (show Γ(X', π ⁻¹ᵁ U) from e i) := fun i => by
    change b₀.repr.symm (Finsupp.single i 1) = _
    rw [Module.Basis.repr_symm_single_one, he']
  set a : Matrix (Fin d) (Fin d) Γ(X, U) := Algebra.leftMulMatrix b₁ g with ha_def
  have hg' : ι'.app (π ⁻¹ᵁ U) (Scheme.Modules.unitSection (π ⁻¹ᵁ U)) = g • s := hg
  have h3 : ∀ j, (∑ i, (π.app U).hom (a i j) * (show Γ(X', π ⁻¹ᵁ U) from e i)) =
      g * (show Γ(X', π ⁻¹ᵁ U) from e j) := fun j => by
    have h := b₁.sum_repr (g * b₁ j)
    simp_rw [hb₁] at h
    refine (Finset.sum_congr rfl fun i _ => ?_).trans h
    rw [ha_def, Algebra.leftMulMatrix_eq_repr_mul, hb₁]
    rfl
  have ha : ∀ j, ((Scheme.Modules.pushforward π).map ι').app U (e j) = ∑ i, a i j • (fun i => (show
    Γ((Scheme.Modules.pushforward π).obj P, U) from (show Γ(X', π ⁻¹ᵁ U) from e i) • s)) i := by
    intro j
    rw [Scheme.Modules.pushforward_map_app]
    have happ := Scheme.Modules.Hom.app_smul ι' (show Γ(X', π ⁻¹ᵁ U) from e j)
      (Scheme.Modules.unitSection (π ⁻¹ᵁ U))
    rw [Scheme.Modules.smul_unitSection] at happ
    refine happ.trans ?_
    rw [hg', smul_smul]
    symm
    calc ∑ i, a i j • (fun i => (show Γ((Scheme.Modules.pushforward π).obj P, U) from (show Γ(X', π
      ⁻¹ᵁ U) from e i) • s)) i
        = ∑ i, (show Γ((Scheme.Modules.pushforward π).obj P, U) from
            ((π.app U).hom (a i j) * (show Γ(X', π ⁻¹ᵁ U) from e i)) • s) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          change (π.app U).hom (a i j) • ((show Γ(X', π ⁻¹ᵁ U) from e i) • s) = _
          rw [smul_smul]
      _ = (show Γ((Scheme.Modules.pushforward π).obj P, U) from
            (∑ i, (π.app U).hom (a i j) * (show Γ(X', π ⁻¹ᵁ U) from e i)) • s) := by
          change _ = (∑ i, (π.app U).hom (a i j) * (show Γ(X', π ⁻¹ᵁ U) from e i)) • s
          rw [Finset.sum_smul]
          rfl
      _ = (show Γ((Scheme.Modules.pushforward π).obj P, U) from
            ((show Γ(X', π ⁻¹ᵁ U) from e j) * g) • s) := by
          rw [h3 j, mul_comm]
  have key := Scheme.Modules.exteriorPower_map_app_unit_iotaMulti_eq_det_smul
    ((Scheme.Modules.pushforward π).map ι') (U := U) e (fun i => (show
      Γ((Scheme.Modules.pushforward π).obj P, U) from (show Γ(X', π ⁻¹ᵁ U) from e i) • s)) a ha
  have hdet : a.det = Algebra.norm Γ(X, U) g := (Algebra.norm_eq_matrix_det b₁ g).symm
  have hev : (Scheme.Modules.normModuleUnitEval π d).app U (Scheme.Modules.tensorSections
    (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
            ((Scheme.Modules.presheafExteriorPower X d).obj ((Scheme.Modules.pushforward π).obj (𝟙_
              X'.Modules)).val)).app
          (op U)
          (show ((Scheme.Modules.presheafExteriorPower X d).obj
              ((Scheme.Modules.pushforward π).obj (𝟙_ X'.Modules)).val).obj (op U) from
                exteriorPower.ιMulti Γ(X, U) (M := Γ((Scheme.Modules.pushforward π).obj (𝟙_
                X'.Modules), U)) d e)) q) =
      Scheme.Modules.toUnitSection U 1 := by
    change ((ihom.ev (Scheme.Modules.det d ((Scheme.Modules.pushforward π).obj (𝟙_
      X'.Modules)))).app
      (𝟙_ X.Modules)).app U (Scheme.Modules.tensorSections
        (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
            ((Scheme.Modules.presheafExteriorPower X d).obj ((Scheme.Modules.pushforward π).obj (𝟙_
              X'.Modules)).val)).app
          (op U)
          (show ((Scheme.Modules.presheafExteriorPower X d).obj
              ((Scheme.Modules.pushforward π).obj (𝟙_ X'.Modules)).val).obj (op U) from
                exteriorPower.ιMulti Γ(X, U) (M := Γ((Scheme.Modules.pushforward π).obj (𝟙_
                X'.Modules), U)) d e)) q) = _
    exact (Scheme.Modules.ihom_ev_app_tensorSections
      (M := Scheme.Modules.det d ((Scheme.Modules.pushforward π).obj (𝟙_ X'.Modules)))
      (N := 𝟙_ X.Modules) U _ q).trans hq1
  have hinv : (inv (Scheme.Modules.normModuleUnitEval π d)).app U (Scheme.Modules.toUnitSection U
    1) =
      Scheme.Modules.tensorSections (((PresheafOfModules.sheafificationAdjunction (𝟙
        X.ringCatSheaf.obj)).unit.app
            ((Scheme.Modules.presheafExteriorPower X d).obj ((Scheme.Modules.pushforward π).obj (𝟙_
              X'.Modules)).val)).app
          (op U)
          (show ((Scheme.Modules.presheafExteriorPower X d).obj
              ((Scheme.Modules.pushforward π).obj (𝟙_ X'.Modules)).val).obj (op U) from
                exteriorPower.ιMulti Γ(X, U) (M := Γ((Scheme.Modules.pushforward π).obj (𝟙_
                X'.Modules), U)) d e)) q := by
    have hcancel (z : Γ(Scheme.Modules.normModule π d (𝟙_ X'.Modules), U)) :
        (inv (Scheme.Modules.normModuleUnitEval π d)).app U
          ((Scheme.Modules.normModuleUnitEval π d).app U z) = z :=
      congrArg
        (fun f : Scheme.Modules.normModule π d (𝟙_ X'.Modules) ⟶
            Scheme.Modules.normModule π d (𝟙_ X'.Modules) => f.app U z)
        (IsIso.hom_inv_id (Scheme.Modules.normModuleUnitEval π d))
    exact (congrArg
      (fun z : Γ(𝟙_ X.Modules, U) =>
        (inv (Scheme.Modules.normModuleUnitEval π d)).app U z) hev).symm.trans
      (hcancel (Scheme.Modules.tensorSections
        (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
          ((Scheme.Modules.presheafExteriorPower X d).obj
            ((Scheme.Modules.pushforward π).obj (𝟙_ X'.Modules)).val)).app (op U)
          (show ((Scheme.Modules.presheafExteriorPower X d).obj
            ((Scheme.Modules.pushforward π).obj (𝟙_ X'.Modules)).val).obj (op U) from
              exteriorPower.ιMulti Γ(X, U) (M := Γ((Scheme.Modules.pushforward π).obj (𝟙_
                X'.Modules), U)) d e)) q))
  let w₀ : Γ(Scheme.Modules.det d ((Scheme.Modules.pushforward π).obj (𝟙_ X'.Modules)), U) :=
    (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
      ((Scheme.Modules.presheafExteriorPower X d).obj
        ((Scheme.Modules.pushforward π).obj (𝟙_ X'.Modules)).val)).app (op U)
      (show ((Scheme.Modules.presheafExteriorPower X d).obj
        ((Scheme.Modules.pushforward π).obj (𝟙_ X'.Modules)).val).obj (op U) from
          exteriorPower.ιMulti Γ(X, U) (M := Γ((Scheme.Modules.pushforward π).obj (𝟙_ X'.Modules),
            U)) d e))
  let wP : Γ(Scheme.Modules.det d ((Scheme.Modules.pushforward π).obj P), U) :=
    (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
      ((Scheme.Modules.presheafExteriorPower X d).obj ((Scheme.Modules.pushforward π).obj
        P).val)).app
      (op U)
      (show ((Scheme.Modules.presheafExteriorPower X d).obj
        ((Scheme.Modules.pushforward π).obj P).val).obj (op U) from
          exteriorPower.ιMulti Γ(X, U) (M := Γ((Scheme.Modules.pushforward π).obj P, U)) d
            (fun i => (show Γ((Scheme.Modules.pushforward π).obj P, U) from
              (show Γ(X', π ⁻¹ᵁ U) from e i) • s))))
  have hinvSections :
      (inv (Scheme.Modules.normModuleUnitEval π d)).app U (Scheme.Modules.toUnitSection U 1) =
        Scheme.Modules.tensorSections w₀ q := hinv
  have hkeySections :
      ((Scheme.Modules.exteriorPower X d).map ((Scheme.Modules.pushforward π).map ι')).app U w₀ =
        a.det • wP := key
  refine (congrArg
    (fun z : Γ(Scheme.Modules.normModule π d (𝟙_ X'.Modules), U) =>
      ((Scheme.Modules.normModuleFunctor π d).map ι').app U z) hinvSections).trans ?_
  refine (Scheme.Modules.whiskerRight_app_tensorSections
    ((Scheme.Modules.exteriorPower X d).map ((Scheme.Modules.pushforward π).map ι'))
    (Scheme.Modules.dual (Scheme.Modules.det d ((Scheme.Modules.pushforward π).obj
      (𝟙_ X'.Modules)))) w₀ q).trans ?_
  refine (congrArg
    (fun z : Γ(Scheme.Modules.det d ((Scheme.Modules.pushforward π).obj P), U) =>
      Scheme.Modules.tensorSections z q) hkeySections).trans ?_
  refine (Scheme.Modules.tensorSections_smul_left a.det wP q).trans ?_
  exact congrArg (fun r : Γ(X, U) => r • Scheme.Modules.tensorSections wP q) hdet
end Scheme_Modules_exists_isFrameOn_normModule_and_app_eq_norm_smul
end AlgebraicCurves.Geometry.Sheaves.Proofs
end ProofImplementation
