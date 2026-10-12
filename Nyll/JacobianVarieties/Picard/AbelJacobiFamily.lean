/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_RelPicardAbelJacobiFamily.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroCut
import Nyll.AlgebraicCurves.Geometry.Sheaves.IdealSheafModule
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDivOfPoint
import Nyll.AlgebraicCurves.RelativeDivisors.Cartier
import Nyll.SchemeTheory.Modules.Monoidal
import Nyll.SchemeTheory.Modules.PullbackMonoidal
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv_isInvertible_I
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_isInvertible_module
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_dual
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_tensor

/-!
# Relative Picard varieties and fibre cohomology

Construct the Abel–Jacobi family from the line bundle defined by a moving point and the fixed
basepoint.
-/

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
  AlgebraicGeometry.RelPicard
  NeronModelInfra GoodReductionJacobian

noncomputable section

namespace AlgebraicGeometry.RelPicard

variable {k : Type u} [Field k] {A : Scheme.{u}} (a : A ⟶ Spec (CommRingCat.of k))

/-- The canonical map to the pullback of the structure morphism along the identity. -/
def toProdSpec : A ⟶ Limits.pullback a (𝟙 (Spec (CommRingCat.of k))) :=
  pullback.lift (𝟙 A) a ((Category.id_comp a).trans (Category.comp_id a).symm)

@[reassoc (attr := simp)]
theorem toProdSpec_fst : toProdSpec a ≫ pullback.fst a (𝟙 _) = 𝟙 A := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem fst_toProdSpec : pullback.fst a (𝟙 _) ≫ toProdSpec a = 𝟙 _ := by
  apply pullback.hom_ext
  · simp only [toProdSpec, Category.assoc, pullback.lift_fst, Category.comp_id, Category.id_comp]
  · simp only [toProdSpec, Category.assoc, pullback.lift_snd, Category.id_comp]
    rw [pullback.condition, Category.comp_id]

/-- Pulling a module along the canonical map and then the first projection recovers it. -/
def fstPullbackToProdSpecPullbackIso (N : (Limits.pullback a (𝟙 (Spec
  (CommRingCat.of k)))).Modules) :
    (Scheme.Modules.pullback (pullback.fst a (𝟙 _))).obj ((Scheme.Modules.pullback
      (toProdSpec a)).obj N) ≅ N :=
  (Scheme.Modules.pullbackComp _ _).app N ≪≫ (Scheme.Modules.pullbackCongr
    (fst_toProdSpec a)).app N ≪≫
    (Scheme.Modules.pullbackId _).app N

/-- Pulling a module along the first projection and then the canonical map recovers it. -/
def toProdSpecPullbackFstPullbackIso (L : A.Modules) :
    (Scheme.Modules.pullback (toProdSpec a)).obj ((Scheme.Modules.pullback (pullback.fst a
      (𝟙 _))).obj L) ≅ L :=
  (Scheme.Modules.pullbackComp _ _).app L ≪≫ (Scheme.Modules.pullbackCongr
    (toProdSpec_fst a)).app L ≪≫
    (Scheme.Modules.pullbackId _).app L

variable {a}

theorem baseChangeSnd_eq_mapOnProdOver {T' : Scheme.{u}} {h : T' ⟶ Spec (CommRingCat.of k)}
    (t : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) h) : baseChangeSnd a t =
      mapOnProdOver a t.1 t.2 := rfl

theorem IsAlgEquivZero.tensorUnit (a : A ⟶ Spec (CommRingCat.of k)) : IsAlgEquivZero a
  (𝟙_ A.Modules) := by
  refine ⟨Spec (CommRingCat.of k), 𝟙 _, inferInstance, geometricallyIntegral_id_Spec k,
    SheafOfModules.unit (Limits.pullback a (𝟙 (Spec (CommRingCat.of k)))).ringCatSheaf,
      Scheme.Modules.isInvertible_unit _,
    ⟨𝟙 _, Category.comp_id _⟩, ⟨𝟙 _, Category.comp_id _⟩,
    ⟨Scheme.Modules.pullbackUnitIso _⟩, ⟨?_⟩⟩
  exact Scheme.Modules.pullbackUnitIso _ ≪≫ (Scheme.Modules.pullbackTensorUnitObjIso _).symm

theorem IsAlgEquivZero.of_fst_pullback_iso {L : A.Modules}
    {N : (Limits.pullback a (𝟙 (Spec (CommRingCat.of k)))).Modules}
    (e : (Scheme.Modules.pullback (pullback.fst a (𝟙 _))).obj L ≅ N)
    (hN : IsAlgEquivZero a ((Scheme.Modules.pullback (toProdSpec a)).obj N)) : IsAlgEquivZero a L :=
  IsAlgEquivZero.of_iso ((Scheme.Modules.pullback (toProdSpec a)).mapIso e.symm ≪≫
    toProdSpecPullbackFstPullbackIso a L) hN

theorem RelEffCartierDiv.ofPoint_congr {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) [IsSeparated f] {T :
  Scheme.{u}}
    {g : T ⟶ S} {x y : T ⟶ 𝒞} (h : x = y) (hx : x ≫ f = g) (hy : y ≫ f = g) :
    RelEffCartierDiv.ofPoint f x hx = RelEffCartierDiv.ofPoint f y hy := by
  subst h; rfl

theorem Scheme.IdealSheafData.IsInvertible.nonempty_invModule_tensor_module_iso {X : Scheme.{u}}
    {I : X.IdealSheafData} (hI : I.IsInvertible) : Nonempty
      (I.invModule ⊗ I.module ≅ 𝟙_ X.Modules) :=
  ⟨β_ _ _ ≪≫ (hI.isInvertible_module.dual).2.some⟩

section
variable [IsSeparated a]

/-- The line module of a point tensored with the ideal module of the base point. -/
abbrev pointSubBasepointModule (t ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) a) :
    (Limits.pullback a (𝟙 (Spec (CommRingCat.of k)))).Modules :=
  (RelEffCartierDiv.ofPoint a t.1 t.2).lineBundle ⊗ (RelEffCartierDiv.ofPoint a ε.1 ε.2).idealModule

/-- The tensor product of the point-minus-base-point modules associated to a list of points. -/
def pointsSubBasepointModule (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) a) :
    List (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) a) → (Limits.pullback a (𝟙 (Spec
      (CommRingCat.of k)))).Modules
  | [] => 𝟙_ _
  | P :: Ps => pointSubBasepointModule (a := a) P ε ⊗ pointsSubBasepointModule ε Ps

@[simp] theorem pointsSubBasepointModule_nil (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) a) :
    pointsSubBasepointModule (a := a) ε [] = 𝟙_ _ := rfl

@[simp] theorem pointsSubBasepointModule_cons (ε P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) a)
    (Ps : List (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) a)) :
    pointsSubBasepointModule (a := a) ε (P :: Ps) = pointSubBasepointModule (a :=
      a) P ε ⊗ pointsSubBasepointModule ε Ps :=
  rfl

/-- The relative effective Cartier divisor defined by the diagonal section. -/
abbrev diagDiv : RelEffCartierDiv a 1 a := RelEffCartierDiv.ofPoint a (𝟙 A) (Category.id_comp a)

omit [IsSeparated a] in
theorem comp_point_comp (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) a) : (a ≫ ε.1) ≫ a =
  a := by
  rw [Category.assoc, ε.2, Category.comp_id]

/-- The relative effective Cartier divisor defined by the constant base-point section. -/
abbrev constDiv (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) a) : RelEffCartierDiv a 1 a :=
  RelEffCartierDiv.ofPoint a (a ≫ ε.1) (comp_point_comp ε)

/-- The Abel–Jacobi family obtained from the diagonal divisor and the constant base-point
  divisor. -/
def ajFamily (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) a) : (Limits.pullback a a).Modules :=
  (diagDiv (a := a)).lineBundle ⊗ (constDiv (a := a) ε).idealModule

theorem isInvertible_ajFamily [SmoothOfRelativeDimension 1 a] (ε : SchemeHomOver (𝟙 (Spec
  (CommRingCat.of k))) a) :
    Scheme.Modules.IsInvertible (ajFamily (a := a) ε) :=
  (RelEffCartierDiv.isInvertible_I _).isInvertible_invModule.tensor
    (RelEffCartierDiv.isInvertible_I _).isInvertible_module

end

end AlgebraicGeometry.RelPicard

end
