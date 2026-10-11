/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.StrictHenselian.GeometricStalk
import EtaleFundamentalGroups.StrictHenselian.GeometricStalkStructure
import EtaleFundamentalGroups.StrictHenselian.GeometricStalkFlat
import EtaleFundamentalGroups.StrictHenselian.GeometricStalkAlgebraColimit
import EtaleFundamentalGroups.StrictHenselian.GeometricStalkFractionFieldMap
import EtaleFundamentalGroups.StrictHenselian.GeometricStalkGenericColimit
import EtaleFundamentalGroups.GenericTensor.FilteredColimit.AlgEquivDescent
import EtaleFundamentalGroups.GenericTensor.FilteredColimit.ScalarExtension
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Category.Ring.Under.Basic
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Filtered.FinallySmall
import Mathlib.CategoryTheory.Sites.Point.Basic
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.TensorProduct.Pi


/-!
# Strict generic equivalences on actual pointed affine neighborhoods

The real generic-neighborhood algebras retain their existing `Under K` scalar
maps. Compactness over K first supplies an actual pointed neighborhood. A
geometric affine refinement then extends that equivalence along its actual
section map. Both forward and inverse squares remain the literal generic
germ squares. No finite presentation of K over R is required.

This is a prerequisite for Stacks Project, Tag 0BSM (https://stacks.math.columbia.edu/tag/0BSM). The separate
principal-localization model construction is not used in this route.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

namespace EtaleFundamentalGroups.StrictHenselian

universe u

section Neighborhood

variable (R : Type u) [CommRing R]

/-- The actual section algebra of an étale neighborhood of `Spec R`, with
its structure map recorded as an object under R. -/
def geometricNeighborhoodAlgebra (W : (Spec (CommRingCat.of R)).Etale) :
    Under (CommRingCat.of R) :=
  Under.mk ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ W.hom.appTop)

/-- Pullback of sections along an actual morphism of étale neighborhoods. -/
def geometricNeighborhoodAlgebraMap
    {W V : (Spec (CommRingCat.of R)).Etale} (j : V ⟶ W) :
    geometricNeighborhoodAlgebra R W ⟶ geometricNeighborhoodAlgebra R V :=
  Under.homMk j.left.appTop (by
    change ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ W.hom.appTop) ≫
      j.left.appTop = (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ V.hom.appTop
    rw [Category.assoc, ← Scheme.Hom.comp_appTop]
    have hj : j.left ≫ (show W.left ⟶ Spec (CommRingCat.of R) from W.hom) =
        (show V.left ⟶ Spec (CommRingCat.of R) from V.hom) := j.w
    exact congrArg (fun f => (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop) hj)

/-- The actual generic fiber of the section algebra, with its one existing
K-algebra structure retained in `Under K`. -/
def geometricNeighborhoodGenericAlgebra (W : (Spec (CommRingCat.of R)).Etale) :
    Under (CommRingCat.of (FractionRing R)) :=
  (CommRingCat.tensorProd (CommRingCat.of R) (CommRingCat.of (FractionRing R))).obj
    (geometricNeighborhoodAlgebra R W)

/-- The literal generic section map of an actual neighborhood morphism. -/
def geometricNeighborhoodGenericMap
    {W V : (Spec (CommRingCat.of R)).Etale} (j : V ⟶ W) :
    geometricNeighborhoodGenericAlgebra R W ⟶ geometricNeighborhoodGenericAlgebra R V :=
  (CommRingCat.tensorProd (CommRingCat.of R) (CommRingCat.of (FractionRing R))).map
    (geometricNeighborhoodAlgebraMap R j)

end Neighborhood

variable {R Ω : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [IsLocalRing R] [Field Ω] [IsSepClosed Ω] (φ : R →+* Ω) [IsLocalHom φ]

/-- The actual germ map as a morphism under R. -/
def geometricNeighborhoodGerm (W : (Spec (CommRingCat.of R)).Etale)
    (t : (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.obj W) :
    geometricNeighborhoodAlgebra R W ⟶ (geometricStalkSmallAlgebraCocone φ).pt :=
  Under.homMk (geometricStalkGerm (Spec.map (CommRingCat.ofHom φ)) W t) (by
    apply CommRingCat.hom_ext
    exact geometricStalkGerm_comp_structure φ W t)

/-- The actual generic germ map into the constructed strict generic field. -/
def geometricNeighborhoodGenericGerm (W : (Spec (CommRingCat.of R)).Etale)
    (t : (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.obj W) :
    geometricNeighborhoodGenericAlgebra R W ⟶
      Under.mk (CommRingCat.ofHom (geometricStalkFractionFieldMap φ)) := by
  let e : (CommRingCat.tensorProd (CommRingCat.of R) (CommRingCat.of (FractionRing R))).obj
      (geometricStalkSmallAlgebraCocone φ).pt ≅
        Under.mk (CommRingCat.ofHom (geometricStalkFractionFieldMap φ)) :=
    geometricStalkGenericFieldVertexIso φ
  exact (CommRingCat.tensorProd (CommRingCat.of R) (CommRingCat.of (FractionRing R))).map
    (geometricNeighborhoodGerm φ W t) ≫ e.hom

/-- Generic germs commute with the actual section map of a pointed refinement. -/
theorem geometricNeighborhoodGenericGerm_naturality
    {W V : (Spec (CommRingCat.of R)).Etale} (j : V ⟶ W)
    (v : (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.obj V)
    (t : (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.obj W)
    (hj : (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.map j v = t) :
    geometricNeighborhoodGenericMap R j ≫ geometricNeighborhoodGenericGerm φ V v =
      geometricNeighborhoodGenericGerm φ W t := by
  have hbase : geometricNeighborhoodAlgebraMap R j ≫ geometricNeighborhoodGerm φ V v =
      geometricNeighborhoodGerm φ W t := by
    apply Under.UnderMorphism.ext
    change j.left.appTop ≫ geometricStalkGerm (Spec.map (CommRingCat.ofHom φ)) V v =
      geometricStalkGerm (Spec.map (CommRingCat.ofHom φ)) W t
    have h := (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).toPresheafFiber_w
      j v (etaleSections (Spec (CommRingCat.of R)))
    rw [hj] at h
    exact h
  let e : (CommRingCat.tensorProd (CommRingCat.of R) (CommRingCat.of (FractionRing R))).obj
      (geometricStalkSmallAlgebraCocone φ).pt ≅
        Under.mk (CommRingCat.ofHom (geometricStalkFractionFieldMap φ)) :=
    geometricStalkGenericFieldVertexIso φ
  change (CommRingCat.tensorProd (CommRingCat.of R) (CommRingCat.of (FractionRing R))).map
      (geometricNeighborhoodAlgebraMap R j) ≫
        ((CommRingCat.tensorProd (CommRingCat.of R) (CommRingCat.of (FractionRing R))).map
          (geometricNeighborhoodGerm φ V v) ≫ e.hom) =
    (CommRingCat.tensorProd (CommRingCat.of R) (CommRingCat.of (FractionRing R))).map
      (geometricNeighborhoodGerm φ W t) ≫ e.hom
  rw [← Category.assoc, ← Functor.map_comp, hbase]

private def scalarExtendUnderEquiv
    {K : CommRingCat.{u}} {B D : Type u} [CommRing B] [CommRing D]
    [Algebra K B] [Algebra K D]
    (E T : Under K) (η : E ⟶ T)
    (e : (E ⊗[K] B) ≃ₐ[E] (E ⊗[K] D)) :
    (T ⊗[K] B) ≃ₐ[T] (T ⊗[K] D) :=
  tensorScalarExtendAlgEquiv (CommRingCat.toAlgHom η) e

private theorem scalarExtendUnderEquiv_squares
    {K : CommRingCat.{u}} {B D : Type u} [CommRing B] [CommRing D]
    [Algebra K B] [Algebra K D]
    (E T F : Under K) (η : E ⟶ T) (σ : T ⟶ F) (μ : E ⟶ F)
    (hμ : η ≫ σ = μ) :
    ∀ (e : (E ⊗[K] B) ≃ₐ[E] (E ⊗[K] D))
      (q : (F ⊗[K] B) ≃ₐ[F] (F ⊗[K] D)),
      (Algebra.TensorProduct.map (CommRingCat.toAlgHom μ) (AlgHom.id K D)).comp
          (e.toAlgHom.restrictScalars K) = (q.toAlgHom.restrictScalars K).comp
            (Algebra.TensorProduct.map (CommRingCat.toAlgHom μ) (AlgHom.id K B)) →
      (Algebra.TensorProduct.map (CommRingCat.toAlgHom μ) (AlgHom.id K B)).comp
          (e.symm.toAlgHom.restrictScalars K) = (q.symm.toAlgHom.restrictScalars K).comp
            (Algebra.TensorProduct.map (CommRingCat.toAlgHom μ) (AlgHom.id K D)) →
      (Algebra.TensorProduct.map (CommRingCat.toAlgHom σ) (AlgHom.id K D)).comp
          ((scalarExtendUnderEquiv E T η e).toAlgHom.restrictScalars K) =
        (q.toAlgHom.restrictScalars K).comp
          (Algebra.TensorProduct.map (CommRingCat.toAlgHom σ) (AlgHom.id K B)) ∧
      (Algebra.TensorProduct.map (CommRingCat.toAlgHom σ) (AlgHom.id K B)).comp
          ((scalarExtendUnderEquiv E T η e).symm.toAlgHom.restrictScalars K) =
        (q.symm.toAlgHom.restrictScalars K).comp
          (Algebra.TensorProduct.map (CommRingCat.toAlgHom σ) (AlgHom.id K D)) := by
  intro e q hf hi
  have hcomp : (CommRingCat.toAlgHom σ).comp (CommRingCat.toAlgHom η) =
      CommRingCat.toAlgHom μ := by
    rw [← CommRingCat.toAlgHom_comp, hμ]
  rw [← hcomp] at hf hi
  exact tensorScalarExtendAlgEquiv_squares (CommRingCat.toAlgHom η)
    (CommRingCat.toAlgHom σ) e q hf hi

/-- Compactness first supplies a genuine pointed neighborhood. The stage
algebra and germ map are the actual objects and maps of the constructed
small colimit, rather than additional comparison data. -/
private theorem exists_pointed_generic_equiv
    {B D : Type u} [CommRing B] [CommRing D]
    [Algebra (FractionRing R) B] [Algebra (FractionRing R) D]
    [Algebra.FinitePresentation (FractionRing R) B]
    [Algebra.FinitePresentation (FractionRing R) D] :
    let : Algebra (FractionRing R)
        (FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom φ)))) :=
      (geometricStalkFractionFieldMap φ).toAlgebra
    ∀ e : ((FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom φ)))) ⊗[FractionRing R] B)
      ≃ₐ[(FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom φ))))]
      ((FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom φ)))) ⊗[FractionRing R] D),
    ∃ (W : (Spec (CommRingCat.of R)).Etale)
      (t : (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.obj W),
      let : Algebra (FractionRing R) (geometricNeighborhoodGenericAlgebra R W).right :=
        (geometricNeighborhoodGenericAlgebra R W).hom.hom.toAlgebra
      ∃ eW : ((geometricNeighborhoodGenericAlgebra R W) ⊗[FractionRing R] B)
        ≃ₐ[(geometricNeighborhoodGenericAlgebra R W)]
          ((geometricNeighborhoodGenericAlgebra R W) ⊗[FractionRing R] D),
        (Algebra.TensorProduct.map
          (show (geometricNeighborhoodGenericAlgebra R W) →ₐ[FractionRing R]
            FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom φ))) from
          CommRingCat.toAlgHom (geometricNeighborhoodGenericGerm φ W t))
            (AlgHom.id (FractionRing R) D)).comp
            (eW.toAlgHom.restrictScalars (FractionRing R)) =
          (e.toAlgHom.restrictScalars (FractionRing R)).comp
            (Algebra.TensorProduct.map
              (show (geometricNeighborhoodGenericAlgebra R W) →ₐ[FractionRing R]
            FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom φ))) from
          CommRingCat.toAlgHom (geometricNeighborhoodGenericGerm φ W t))
            (AlgHom.id (FractionRing R) B)) ∧
        (Algebra.TensorProduct.map
          (show (geometricNeighborhoodGenericAlgebra R W) →ₐ[FractionRing R]
            FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom φ))) from
          CommRingCat.toAlgHom (geometricNeighborhoodGenericGerm φ W t))
            (AlgHom.id (FractionRing R) B)).comp
            (eW.symm.toAlgHom.restrictScalars (FractionRing R)) =
          (e.symm.toAlgHom.restrictScalars (FractionRing R)).comp
            (Algebra.TensorProduct.map
              (show (geometricNeighborhoodGenericAlgebra R W) →ₐ[FractionRing R]
            FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom φ))) from
          CommRingCat.toAlgHom (geometricNeighborhoodGenericGerm φ W t))
            (AlgHom.id (FractionRing R) D)) := by
  intro scalarAction e
  obtain ⟨i, eᵢ, hforward, hinverse⟩ := exists_tensorProduct_algEquiv_stage_of_filteredColimit
    (geometricStalkSmallGenericAlgebraDiagram φ) (geometricStalkGenericFieldCocone φ)
      (geometricStalkGenericFieldCoconeIsColimit φ) e
  let j := (FinallySmall.fromFilteredFinalModel
    (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.Elementsᵒᵖ).obj i
  let W : (Spec (CommRingCat.of R)).Etale := j.unop.obj
  let t : (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.obj W := j.unop.val
  refine ⟨W, t, ?_⟩
  intro stageAction
  exact ⟨eᵢ, hforward, hinverse⟩

/-- An equivalence over the actual strict generic field descends to the
actual generic fibers of a pointed affine étale neighborhood. Both literal
forward and inverse generic-germ compatibility squares are retained. -/
theorem geometricStalk_exists_affine_generic_tensorProduct_algEquiv
    {B D : Type u} [CommRing B] [CommRing D]
    [Algebra (FractionRing R) B] [Algebra (FractionRing R) D]
    [Algebra.FinitePresentation (FractionRing R) B]
    [Algebra.FinitePresentation (FractionRing R) D] :
    let : Algebra (FractionRing R)
        (FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom φ)))) :=
      (geometricStalkFractionFieldMap φ).toAlgebra
    ∀ e : ((FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom φ)))) ⊗[FractionRing R] B)
      ≃ₐ[(FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom φ))))]
      ((FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom φ)))) ⊗[FractionRing R] D),
    ∃ (V : (Spec (CommRingCat.of R)).Etale)
      (v : (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.obj V),
      IsAffine V.left ∧
      let : Algebra (FractionRing R) (geometricNeighborhoodGenericAlgebra R V).right :=
        (geometricNeighborhoodGenericAlgebra R V).hom.hom.toAlgebra
      ∃ eV : ((geometricNeighborhoodGenericAlgebra R V) ⊗[FractionRing R] B)
        ≃ₐ[(geometricNeighborhoodGenericAlgebra R V)]
          ((geometricNeighborhoodGenericAlgebra R V) ⊗[FractionRing R] D),
        (Algebra.TensorProduct.map
          (show (geometricNeighborhoodGenericAlgebra R V) →ₐ[FractionRing R]
            FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom φ))) from
          CommRingCat.toAlgHom (geometricNeighborhoodGenericGerm φ V v))
            (AlgHom.id (FractionRing R) D)).comp
            (eV.toAlgHom.restrictScalars (FractionRing R)) =
          (e.toAlgHom.restrictScalars (FractionRing R)).comp
            (Algebra.TensorProduct.map
              (show (geometricNeighborhoodGenericAlgebra R V) →ₐ[FractionRing R]
            FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom φ))) from
          CommRingCat.toAlgHom (geometricNeighborhoodGenericGerm φ V v))
            (AlgHom.id (FractionRing R) B)) ∧
        (Algebra.TensorProduct.map
          (show (geometricNeighborhoodGenericAlgebra R V) →ₐ[FractionRing R]
            FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom φ))) from
          CommRingCat.toAlgHom (geometricNeighborhoodGenericGerm φ V v))
            (AlgHom.id (FractionRing R) B)).comp
            (eV.symm.toAlgHom.restrictScalars (FractionRing R)) =
          (e.symm.toAlgHom.restrictScalars (FractionRing R)).comp
            (Algebra.TensorProduct.map
              (show (geometricNeighborhoodGenericAlgebra R V) →ₐ[FractionRing R]
            FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom φ))) from
          CommRingCat.toAlgHom (geometricNeighborhoodGenericGerm φ V v))
            (AlgHom.id (FractionRing R) D)) := by
  intro scalarAction e
  obtain ⟨W, t, eW, hforward, hinverse⟩ := exists_pointed_generic_equiv φ e
  obtain ⟨V, v, j, hV, hj⟩ := geometricStalk_exists_affine_refinement
    (Spec.map (CommRingCat.ofHom φ)) W t
  refine ⟨V, v, hV, ?_⟩
  intro stageAction
  exact ⟨scalarExtendUnderEquiv (geometricNeighborhoodGenericAlgebra R W)
      (geometricNeighborhoodGenericAlgebra R V) (geometricNeighborhoodGenericMap R j) eW,
    scalarExtendUnderEquiv_squares (geometricNeighborhoodGenericAlgebra R W)
      (geometricNeighborhoodGenericAlgebra R V)
      (Under.mk (CommRingCat.ofHom (geometricStalkFractionFieldMap φ)))
      (geometricNeighborhoodGenericMap R j) (geometricNeighborhoodGenericGerm φ V v)
      (geometricNeighborhoodGenericGerm φ W t)
      (geometricNeighborhoodGenericGerm_naturality φ j v t hj)
      eW e hforward hinverse⟩

private theorem piScalarRight_naturality
    {K E F ι : Type u} [CommRing K] [CommRing E] [CommRing F]
    [Algebra K E] [Algebra K F] [Fintype ι] [DecidableEq ι]
    (σ : E →ₐ[K] F) (x : E ⊗[K] (ι → K)) :
    Algebra.TensorProduct.piScalarRight K F F ι
        (Algebra.TensorProduct.map σ (AlgHom.id K (ι → K)) x) =
      fun i => σ (Algebra.TensorProduct.piScalarRight K E E ι x i) := by
  induction x using TensorProduct.inductionOn with
  | tmul e f =>
    funext i
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      Algebra.TensorProduct.piScalarRight_tmul_apply,
      Algebra.TensorProduct.piScalarRight_tmul_apply]
    exact (σ.toLinearMap.map_smul (f i) e).symm
  | add x y hx hy =>
    funext i
    simpa only [map_add, Pi.add_apply] using
      congrArg₂ (fun a b => a + b) (congrFun hx i) (congrFun hy i)

private theorem exists_pi_equiv_of_tensor_squares
    {K E F B ι : Type u} [CommRing K] [CommRing E] [CommRing F] [CommRing B]
    [Algebra K E] [Algebra K F] [Algebra K B] [Fintype ι] [DecidableEq ι]
    (σ : E →ₐ[K] F) (eTensor : (E ⊗[K] B) ≃ₐ[E] (E ⊗[K] (ι → K)))
    (eSplit : (F ⊗[K] B) ≃ₐ[F] (ι → F))
    (hf : (Algebra.TensorProduct.map σ (AlgHom.id K (ι → K))).comp
        (eTensor.toAlgHom.restrictScalars K) =
      ((eSplit.trans
        (Algebra.TensorProduct.piScalarRight K F F ι).symm).toAlgHom.restrictScalars K).comp
        (Algebra.TensorProduct.map σ (AlgHom.id K B)))
    (hi : (Algebra.TensorProduct.map σ (AlgHom.id K B)).comp
        (eTensor.symm.toAlgHom.restrictScalars K) =
      ((eSplit.trans
        (Algebra.TensorProduct.piScalarRight K F F ι).symm).symm.toAlgHom.restrictScalars K).comp
        (Algebra.TensorProduct.map σ (AlgHom.id K (ι → K)))) :
    ∃ eProd : (E ⊗[K] B) ≃ₐ[E] (ι → E),
      (∀ x, (fun i => σ (eProd x i)) =
        eSplit (Algebra.TensorProduct.map σ (AlgHom.id K B) x)) ∧
      (∀ y, Algebra.TensorProduct.map σ (AlgHom.id K B) (eProd.symm y) =
        eSplit.symm (fun i => σ (y i))) := by
  let ePi : (F ⊗[K] (ι → K)) ≃ₐ[F] (ι → F) :=
    Algebra.TensorProduct.piScalarRight K F F ι
  let ePiE : (E ⊗[K] (ι → K)) ≃ₐ[E] (ι → E) :=
    Algebra.TensorProduct.piScalarRight K E E ι
  refine ⟨eTensor.trans ePiE, ?_, ?_⟩
  · intro x
    change (fun i => σ (ePiE (eTensor x) i)) =
      eSplit (Algebra.TensorProduct.map σ (AlgHom.id K B) x)
    calc
      (fun i => σ (ePiE (eTensor x) i)) =
        ePi (Algebra.TensorProduct.map σ (AlgHom.id K (ι → K)) (eTensor x)) :=
          (piScalarRight_naturality σ (eTensor x)).symm
      _ = ePi ((eSplit.trans ePi.symm)
          (Algebra.TensorProduct.map σ (AlgHom.id K B) x)) :=
            congrArg ePi (AlgHom.congr_fun hf x)
      _ = eSplit (Algebra.TensorProduct.map σ (AlgHom.id K B) x) :=
        ePi.apply_symm_apply _
  · intro y
    change Algebra.TensorProduct.map σ (AlgHom.id K B) (eTensor.symm (ePiE.symm y)) =
      eSplit.symm (fun i => σ (y i))
    calc
      Algebra.TensorProduct.map σ (AlgHom.id K B) (eTensor.symm (ePiE.symm y)) =
        (eSplit.trans ePi.symm).symm
          (Algebra.TensorProduct.map σ (AlgHom.id K (ι → K)) (ePiE.symm y)) :=
            AlgHom.congr_fun hi (ePiE.symm y)
      _ = eSplit.symm (fun i => σ (y i)) := by
        change eSplit.symm (ePi (Algebra.TensorProduct.map σ
          (AlgHom.id K (ι → K)) (ePiE.symm y))) = eSplit.symm (fun i => σ (y i))
        apply congrArg eSplit.symm
        calc
          ePi (Algebra.TensorProduct.map σ (AlgHom.id K (ι → K)) (ePiE.symm y)) =
              fun i => σ (ePiE (ePiE.symm y) i) := piScalarRight_naturality σ _
          _ = fun i => σ (y i) := by rw [ePiE.apply_symm_apply]

/-- A strict-generic splitting of a finite fraction-field algebra occurs on
the actual generic fiber of a pointed affine étale neighborhood. The two
pointwise formulas are the literal forward and inverse splitting squares. -/
theorem geometricStalk_exists_affine_generic_split
    {B : Type u} [CommRing B] [Algebra (FractionRing R) B]
    [Module.Finite (FractionRing R) B] (ι : Type u) [Finite ι] :
    let : Algebra (FractionRing R)
        (FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom φ)))) :=
      (geometricStalkFractionFieldMap φ).toAlgebra
    ∀ e :
      (FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom φ))) ⊗[FractionRing R] B)
        ≃ₐ[FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom φ)))]
          (ι → FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom φ)))),
    ∃ (V : (Spec (CommRingCat.of R)).Etale)
      (v : (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.obj V),
      IsAffine V.left ∧
      let : Algebra (FractionRing R) (geometricNeighborhoodGenericAlgebra R V).right :=
        (geometricNeighborhoodGenericAlgebra R V).hom.hom.toAlgebra
      ∃ eV : ((geometricNeighborhoodGenericAlgebra R V) ⊗[FractionRing R] B)
          ≃ₐ[geometricNeighborhoodGenericAlgebra R V]
            (ι → geometricNeighborhoodGenericAlgebra R V),
        (∀ x, (fun i => (show (geometricNeighborhoodGenericAlgebra R V) →ₐ[FractionRing R]
            FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom φ))) from
          CommRingCat.toAlgHom (geometricNeighborhoodGenericGerm φ V v))
              (eV x i)) = e (Algebra.TensorProduct.map
                (show (geometricNeighborhoodGenericAlgebra R V) →ₐ[FractionRing R]
            FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom φ))) from
          CommRingCat.toAlgHom (geometricNeighborhoodGenericGerm φ V v))
                (AlgHom.id (FractionRing R) B) x)) ∧
        (∀ y, Algebra.TensorProduct.map
            (show (geometricNeighborhoodGenericAlgebra R V) →ₐ[FractionRing R]
            FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom φ))) from
          CommRingCat.toAlgHom (geometricNeighborhoodGenericGerm φ V v))
            (AlgHom.id (FractionRing R) B) (eV.symm y) =
          e.symm (fun i => (show (geometricNeighborhoodGenericAlgebra R V) →ₐ[FractionRing R]
            FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom φ))) from
          CommRingCat.toAlgHom (geometricNeighborhoodGenericGerm φ V v)) (y i))) := by
  intro scalarAction e
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let K := FractionRing R
  let F := FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom φ)))
  have : Algebra.FinitePresentation K B := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have : Algebra.FinitePresentation K (ι → K) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let ePi : (F ⊗[K] (ι → K)) ≃ₐ[F] (ι → F) :=
    Algebra.TensorProduct.piScalarRight K F F ι
  obtain ⟨V, v, hV, eV, hf, hi⟩ :=
    geometricStalk_exists_affine_generic_tensorProduct_algEquiv φ (e.trans ePi.symm)
  refine ⟨V, v, hV, ?_⟩
  intro stageAction
  exact exists_pi_equiv_of_tensor_squares
    (show (geometricNeighborhoodGenericAlgebra R V) →ₐ[FractionRing R]
            FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom φ))) from
          CommRingCat.toAlgHom (geometricNeighborhoodGenericGerm φ V v)) eV e hf hi

end EtaleFundamentalGroups.StrictHenselian
