/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Cohomology.H1FiberPullback
import EtaleFundamentalGroups.Cohomology.IntegerExtensionShear

/-!
# Coefficient equivariance of geometric pullback of H¹ lift sheaves

Translations on the fiber over one are restrictions of additive shears.
Their compatibility with inverse image therefore follows from the genuine
abelian inverse-image functor and its constant-coefficient comparison.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite EtaleCohomology

universe u

namespace EtaleFundamentalGroups.Cohomology

instance extensionFiberInclusion_mono {X : Scheme.{u}}
    (S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))
    (t : (Functor.const X.Etaleᵒᵖ).obj PUnit ⟶ S.X₃.obj ⋙ forget AddCommGrpCat.{u}) :
    Mono (extensionFiberInclusion S t) where
  right_cancellation {B} a b hab := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    apply ConcreteCategory.hom_ext
    intro z
    apply Subtype.ext
    exact congrArg (fun k => k.hom.app U z) hab

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (A : AddCommGrpCat.{u})
  {E : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}}
  (i : (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj A ⟶ E)
  (p : E ⟶ (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift.{u} ℤ)))
  (h : i ≫ p = 0)

/-- The actual lift-sheaf comparison preserves translation by every original
coefficient, without any imposed equivariance hypothesis. -/
theorem schemePullbackH1Extension_fiberIso_translation (a : A) :
    (etaleSetPullback f).map
        (constantFiberTranslation A i p h (integerUnitSection Y) a) ≫
      (schemePullbackH1Extension_fiberIso f A i p h).hom =
    (schemePullbackH1Extension_fiberIso f A i p h).hom ≫
      constantFiberTranslation A (schemePullbackH1Extension f A i p h).f
        (schemePullbackH1Extension f A i p h).g
        (schemePullbackH1Extension f A i p h).zero (integerUnitSection X) a := by
  let S := ShortComplex.mk i p h
  let S' := schemePullbackH1Extension f A i p h
  let L := etaleSetPullback f
  let FA := etaleAbelianPullback f
  let UY := sheafCompose Y.smallEtaleTopology (forget AddCommGrpCat.{u})
  let UX := sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{u})
  let b : L.obj (UY.obj E) ⟶ UX.obj (FA.obj E) :=
    (abelianPullbackUnderlyingMateIso f).inv.app E
  let e := schemePullbackH1Extension_fiberIso f A i p h
  let j : extensionFiber S (integerUnitSection Y) ⟶ UY.obj E :=
    extensionFiberInclusion S (integerUnitSection Y)
  let j' : extensionFiber S' (integerUnitSection X) ⟶ UX.obj (FA.obj E) :=
    extensionFiberInclusion S' (integerUnitSection X)
  let τ := constantFiberTranslation A i p h (integerUnitSection Y) a
  let τ' := constantFiberTranslation A S'.f S'.g S'.zero (integerUnitSection X) a
  let m : E ⟶ E := integerExtensionShear A i p a
  let m' : FA.obj E ⟶ FA.obj E := integerExtensionShear A S'.f S'.g a
  have he : e.hom ≫ j' = L.map j ≫ b :=
    schemePullbackH1Extension_fiberIso_hom_inclusion f A i p h
  have ht : τ ≫ j = j ≫ UY.map m :=
    constantFiberTranslation_inclusion_eq_shear A i p h a
  have ht' : τ' ≫ j' = j' ≫ UX.map m' :=
    constantFiberTranslation_inclusion_eq_shear A S'.f S'.g S'.zero a
  have hn : L.map (UY.map m) ≫ b = b ≫ UX.map (FA.map m) :=
    (abelianPullbackUnderlyingMateIso f).inv.naturality m
  have hm : FA.map m = m' := integerExtensionShear_pullback A i p f h a
  change L.map τ ≫ e.hom = e.hom ≫ τ'
  have : Mono j' := extensionFiberInclusion_mono S' (integerUnitSection X)
  apply (cancel_mono j').1
  calc
    (L.map τ ≫ e.hom) ≫ j' = L.map τ ≫ (L.map j ≫ b) := by
      rw [Category.assoc, he]
    _ = L.map (τ ≫ j) ≫ b := by rw [L.map_comp, Category.assoc]
    _ = L.map (j ≫ UY.map m) ≫ b := congrArg (fun k => L.map k ≫ b) ht
    _ = (L.map j ≫ b) ≫ UX.map (FA.map m) := by
      rw [L.map_comp, Category.assoc, hn, ← Category.assoc]
    _ = (e.hom ≫ j') ≫ UX.map m' := by rw [← he, hm]
    _ = (e.hom ≫ τ') ≫ j' := by rw [Category.assoc, ← ht', ← Category.assoc]

end EtaleFundamentalGroups.Cohomology
