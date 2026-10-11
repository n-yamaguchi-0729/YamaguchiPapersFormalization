/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.AlgebraicCurves.Geometry.Schemes.Scheme_exists_isOpenImmersion_of_functionField_iso
import Nyll.AlgebraicCurves.Geometry.Schemes.Scheme_exists_iso_comp_eq_of_isOpenImmersion_of_isProper
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.Algebra.CharP.Algebra
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.RingHom.PurelyInseparable
import Mathlib.Topology.JacobsonSpace

/-!
# Isomorphisms of proper smooth curves from rational points in characteristic zero

For a morphism from an integral proper smooth curve to an integral proper smooth
scheme over an algebraically closed field of characteristic zero, bijectivity on
rational points implies that the original morphism is an isomorphism.

The proof uses the actual diagonal and residue-field maps.  After constructing the
generic-stalk isomorphism, it uses the imported extension theorems for proper smooth
curves.  Those suppliers retain their Anthropic FLT upstream notices in their own
source files.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

universe u

private theorem surjective_of_contains_closedPoints
    {X Y : Scheme.{u}} (f : X ⟶ Y) [UniversallyClosed f] [JacobsonSpace Y]
    (h : closedPoints Y ⊆ Set.range f) : Surjective f := by
  have hd : Dense (closedPoints Y) := by
    rw [dense_iff_closure_eq]
    have hc := JacobsonSpace.closure_inter_closedPoints_eq_closure
      (X := Y) (S := Set.univ) isOpen_univ.isLocallyClosed
    simpa only [Set.univ_inter, closure_univ] using hc
  have : IsDominant f := ⟨hd.mono h⟩
  exact surjective_of_isDominant_of_isClosed_range f f.isClosedMap.isClosed_range

private theorem surjective_of_surjective_rationalPoints
    {K : Type u} [Field K] [IsAlgClosed K] {X Y : Scheme.{u}}
    (c : X ⟶ Spec (CommRingCat.of K)) (d : Y ⟶ Spec (CommRingCat.of K))
    [IsProper c] [IsProper d] (f : Over.mk c ⟶ Over.mk d)
    (h : Function.Surjective
      (fun p : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ Over.mk c => p ≫ f)) :
    Surjective f.left := by
  let g : X ⟶ Y := f.left
  have hgbase : g ≫ d = c := f.w
  have : IsProper (g ≫ d) := by rw [hgbase]; infer_instance
  have : IsProper g := IsProper.of_comp g d
  have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace d
  change Surjective g
  apply surjective_of_contains_closedPoints (X := X) (Y := Y) g
  intro y hy
  let q : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ Over.mk d :=
    Over.homMk (pointOfClosedPoint d y hy) (pointOfClosedPoint_comp d y hy)
  obtain ⟨p, hp⟩ := h q
  refine ⟨p.left (IsLocalRing.closedPoint K), ?_⟩
  calc
    g (p.left (IsLocalRing.closedPoint K)) =
        (p ≫ f).left (IsLocalRing.closedPoint K) :=
      (Scheme.Hom.comp_apply p.left g (IsLocalRing.closedPoint K)).symm
    _ = q.left (IsLocalRing.closedPoint K) :=
      congrArg (fun r => r.left (IsLocalRing.closedPoint K)) hp
    _ = y := pointOfClosedPoint_apply d y hy (IsLocalRing.closedPoint K)

private theorem universallyInjective_of_injective_rationalPoints
    {K : Type u} [Field K] [IsAlgClosed K] {X Y : Scheme.{u}}
    (c : X ⟶ Spec (CommRingCat.of K)) (d : Y ⟶ Spec (CommRingCat.of K))
    [IsProper c] [IsProper d] (f : Over.mk c ⟶ Over.mk d)
    (h : Function.Injective
      (fun p : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ Over.mk c => p ≫ f)) :
    UniversallyInjective f.left := by
  let g : X ⟶ Y := f.left
  have hgbase : g ≫ d = c := f.w
  have : IsProper (g ≫ d) := by rw [hgbase]; infer_instance
  have : IsProper g := IsProper.of_comp g d
  let b : pullback g g ⟶ Spec (CommRingCat.of K) :=
    pullback.fst g g ≫ c
  have : LocallyOfFiniteType b := inferInstance
  have : JacobsonSpace ↥(pullback g g : Scheme.{u}) :=
    LocallyOfFiniteType.jacobsonSpace b
  rw [UniversallyInjective.iff_diagonal]
  apply surjective_of_contains_closedPoints (pullback.diagonal g)
  intro z hz
  let q : Spec (CommRingCat.of K) ⟶ pullback g g :=
    pointOfClosedPoint b z hz
  have hq : q ≫ b = 𝟙 _ := pointOfClosedPoint_comp b z hz
  have hbase : pullback.snd g g ≫ c = pullback.fst g g ≫ c := by
    calc
      pullback.snd g g ≫ c =
          (pullback.snd g g ≫ g) ≫ d := by rw [Category.assoc, hgbase]
      _ = (pullback.fst g g ≫ g) ≫ d :=
        congrArg (fun r => r ≫ d) (pullback.condition (f := g) (g := g)).symm
      _ = pullback.fst g g ≫ c := by rw [Category.assoc, hgbase]
  let p₁ : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ Over.mk c :=
    Over.homMk (q ≫ pullback.fst g g) (by
      rw [Category.assoc]
      exact hq)
  let p₂ : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ Over.mk c :=
    Over.homMk (q ≫ pullback.snd g g) (by
      change (q ≫ pullback.snd g g) ≫ c = 𝟙 _
      rw [Category.assoc, hbase]
      exact hq)
  have hp : p₁ ≫ f = p₂ ≫ f := by
    apply Over.OverMorphism.ext
    change (q ≫ pullback.fst g g) ≫ g =
      (q ≫ pullback.snd g g) ≫ g
    rw [Category.assoc, Category.assoc, pullback.condition]
  have heq : q ≫ pullback.fst g g = q ≫ pullback.snd g g :=
    congrArg Over.Hom.left (h hp)
  have hdiag : (q ≫ pullback.fst g g) ≫ pullback.diagonal g = q := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.diagonal_fst, Category.comp_id]
    · rw [Category.assoc, pullback.diagonal_snd, Category.comp_id, heq]
  refine ⟨(q ≫ pullback.fst g g) (IsLocalRing.closedPoint K), ?_⟩
  calc
    pullback.diagonal g
        ((q ≫ pullback.fst g g) (IsLocalRing.closedPoint K)) =
        ((q ≫ pullback.fst g g) ≫ pullback.diagonal g)
          (IsLocalRing.closedPoint K) :=
      (Scheme.Hom.comp_apply (q ≫ pullback.fst g g) (pullback.diagonal g)
        (IsLocalRing.closedPoint K)).symm
    _ = q (IsLocalRing.closedPoint K) :=
      congrArg (fun r => r (IsLocalRing.closedPoint K)) hdiag
    _ = z := pointOfClosedPoint_apply b z hz (IsLocalRing.closedPoint K)

private theorem residueFieldMap_isIso_of_universallyInjective_charZero
    {K : Type u} [Field K] [CharZero K] {X Y : Scheme.{u}}
    (d : Y ⟶ Spec (CommRingCat.of K)) (f : X ⟶ Y) [UniversallyInjective f]
    (x : X) : IsIso (f.residueFieldMap x) := by
  let b : CommRingCat.of K ⟶ Y.residueField (f x) :=
    Spec.preimage (Y.fromSpecResidueField (f x) ≫ d)
  have : CharZero (Y.residueField (f x)) := charZero_of_injective_ringHom b.hom.injective
  let : Algebra (Y.residueField (f x)) (X.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  have hfres : Function.Injective f ∧
      ∀ y : X, (f.residueFieldMap y).hom.IsPurelyInseparable :=
    ((tfae_universallyInjective f).out 1 3).mp (inferInstance : UniversallyInjective f)
  have hp : (f.residueFieldMap x).hom.IsPurelyInseparable := hfres.2 x
  have : IsPurelyInseparable (Y.residueField (f x)) (X.residueField x) := hp
  rw [ConcreteCategory.isIso_iff_bijective]
  exact ⟨(f.residueFieldMap x).hom.injective,
    IsPurelyInseparable.surjective_algebraMap_of_isSeparable
      (Y.residueField (f x)) (X.residueField x)⟩

private theorem residue_genericPoint_isIso (X : Scheme.{u}) [IsIntegral X] :
    IsIso (X.residue (genericPoint X)) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  exact ⟨(X.residue (genericPoint X)).hom.injective, X.residue_surjective (genericPoint X)⟩

/-- A morphism from an integral proper smooth curve to an integral proper smooth
scheme over an algebraically closed field of characteristic zero is an isomorphism
if its actual map on rational points is bijective. -/
theorem Scheme.Hom.isIso_of_bijective_points_of_charZero
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] {X Y : Scheme.{u}}
    (c : X ⟶ Spec (CommRingCat.of K)) (d : Y ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [IsProper c] [SmoothOfRelativeDimension 1 c]
    [IsIntegral Y] [IsProper d] [Smooth d] (f : Over.mk c ⟶ Over.mk d)
    (h : Function.Bijective
      (fun p : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ Over.mk c => p ≫ f)) :
    IsIso f.left := by
  let g : X ⟶ Y := f.left
  have hgbase : g ≫ d = c := f.w
  have : Surjective g := surjective_of_surjective_rationalPoints c d f h.2
  have : UniversallyInjective g := universallyInjective_of_injective_rationalPoints c d f h.1
  have hη : g (genericPoint X) = genericPoint Y := by
    apply IsGenericPoint.eq _ (genericPoint_spec Y)
    have hg := (genericPoint_spec X).image g.continuous
    rw [Set.image_univ, g.surjective.range_eq, closure_univ] at hg
    exact hg
  have : IsIso (X.residue (genericPoint X)) := residue_genericPoint_isIso X
  have : IsIso (Y.residue (g (genericPoint X))) := by
    rw [hη]
    exact residue_genericPoint_isIso Y
  have : IsIso (g.residueFieldMap (genericPoint X)) :=
    residueFieldMap_isIso_of_universallyInjective_charZero d g (genericPoint X)
  have hcomp : IsIso (g.stalkMap (genericPoint X) ≫ X.residue (genericPoint X)) := by
    rw [← Scheme.residue_residueFieldMap]
    infer_instance
  have : IsIso (g.stalkMap (genericPoint X)) :=
    (isIso_comp_right_iff (g.stalkMap (genericPoint X))
      (X.residue (genericPoint X))).mp hcomp
  let eη : Y.presheaf.stalk (g (genericPoint X)) ≅ Y.functionField :=
    Y.presheaf.stalkCongr (Inseparable.of_eq hη)
  let ψ : X.functionField ≅ Y.functionField :=
    (asIso (g.stalkMap (genericPoint X))).symm ≪≫ eη
  have hgeneric : Spec.map ψ.inv ≫ Y.fromSpecStalk (genericPoint Y) =
      X.fromSpecStalk (genericPoint X) ≫ g := by
    change Spec.map (eη.inv ≫ g.stalkMap (genericPoint X)) ≫
      Y.fromSpecStalk (genericPoint Y) = _
    rw [Spec.map_comp, Category.assoc]
    change Spec.map (g.stalkMap (genericPoint X)) ≫
      Spec.map (Y.presheaf.stalkSpecializes (Inseparable.of_eq hη).specializes) ≫
        Y.fromSpecStalk (genericPoint Y) = _
    rw [Scheme.SpecMap_stalkSpecializes_fromSpecStalk, Scheme.SpecMap_stalkMap_fromSpecStalk]
  have hψ : Spec.map ψ.inv ≫ Y.fromSpecStalk (genericPoint Y) ≫ d =
      X.fromSpecStalk (genericPoint X) ≫ c := by
    rw [← Category.assoc, hgeneric, Category.assoc, hgbase]
  obtain ⟨U, hU, j, hjopen, hjbase, hjgeneric⟩ :=
    Scheme.exists_isOpenImmersion_of_functionField_iso c d ψ hψ
  have : IsOpenImmersion j := hjopen
  obtain ⟨e, hebase, heU⟩ :=
    Scheme.exists_iso_comp_eq_of_isOpenImmersion_of_isProper c d U ⟨genericPoint X, hU⟩ j hjbase
  have hegeneric : X.fromSpecStalk (genericPoint X) ≫ e.hom =
      X.fromSpecStalk (genericPoint X) ≫ g := by
    calc
      X.fromSpecStalk (genericPoint X) ≫ e.hom =
          (U.fromSpecStalkOfMem (genericPoint X) hU ≫ U.ι) ≫ e.hom :=
        congrArg (fun r => r ≫ e.hom)
          (U.fromSpecStalkOfMem_ι (genericPoint X) hU).symm
      _ = U.fromSpecStalkOfMem (genericPoint X) hU ≫ j := by rw [Category.assoc, heU]
      _ = Spec.map ψ.inv ≫ Y.fromSpecStalk (genericPoint Y) := hjgeneric
      _ = X.fromSpecStalk (genericPoint X) ≫ g := hgeneric
  have : IsDominant (X.fromSpecStalk (genericPoint X)) := by
    have hd : Dense ({genericPoint X} : Set X) :=
      dense_iff_closure_eq.mpr (genericPoint_spec X).def
    refine ⟨hd.mono (Set.singleton_subset_iff.mpr ?_)⟩
    exact ⟨IsLocalRing.closedPoint X.functionField, Scheme.fromSpecStalk_closedPoint⟩
  have he : e.hom = g :=
    ext_of_isDominant_of_isSeparated d (hebase.trans hgbase.symm)
      (X.fromSpecStalk (genericPoint X)) hegeneric
  change IsIso g
  rw [← he]
  infer_instance

end AlgebraicGeometry
