/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Cohomology.ConstantStalk
import EtaleFundamentalGroups.Cohomology.FiberStalkComparison
import Mathlib.CategoryTheory.Sites.Sheafification

/-!
# Constant coefficient translations on the sheaf of lifts

Every original coefficient acts by a morphism of the actual fiber sheaf.
On a geometric stalk this is translation by the same coefficient under the
canonical constant-stalk isomorphism. Naturality of these sheaf morphisms
will give commutation with geometric monodromy.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace EtaleFundamentalGroups.Cohomology

variable {X : Scheme.{u}} (A : AddCommGrpCat.{u})
  {E Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}}
  (i : (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A ⟶ E)
  (p : E ⟶ Q) (h : i ≫ p = 0)
  (t : (Functor.const X.Etaleᵒᵖ).obj PUnit ⟶ Q.obj ⋙ forget AddCommGrpCat.{u})

private abbrev constantSection (U : X.Etaleᵒᵖ) (a : A) :=
  (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj A)).app U a

/-- Adding the image of a constant coefficient defines an endomorphism of the
fiber sheaf itself, before any geometric point or monodromy is chosen. -/
def constantFiberTranslation (a : A) :
    extensionFiber (ShortComplex.mk i p h) t ⟶
      extensionFiber (ShortComplex.mk i p h) t where
  hom :=
    { app := fun U => ↾fun (e : {b : E.obj.obj U // p.hom.app U b = t.app U PUnit.unit}) =>
        ⟨i.hom.app U (constantSection A U a) + e.val, by
        change p.hom.app U (i.hom.app U (constantSection A U a) + e.val) =
          t.app U PUnit.unit
        rw [map_add]
        have hz := ConcreteCategory.congr_hom
          (congrArg (fun k : (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A ⟶ Q =>
            k.hom.app U) h) (constantSection A U a)
        change p.hom.app U (i.hom.app U (constantSection A U a)) = 0 at hz
        rw [hz, zero_add]
        exact e.property⟩
      naturality := fun U V f => by
        apply ConcreteCategory.hom_ext
        intro (e : {b : E.obj.obj U // p.hom.app U b = t.app U PUnit.unit})
        apply Subtype.ext
        symm
        change E.obj.map f (i.hom.app U (constantSection A U a) + e.val) =
          i.hom.app V (constantSection A V a) + E.obj.map f e.val
        rw [map_add]
        apply congrArg (· + E.obj.map f e.val)
        have hi := ConcreteCategory.congr_hom (i.hom.naturality f) (constantSection A U a)
        have ha := ConcreteCategory.congr_hom
          ((toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj A)).naturality f) a
        exact hi.symm.trans (congrArg (i.hom.app V) ha.symm) }

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ X)

/-- The stalk action of a constant translation uses the original inclusion and
the actual coefficient, not a separately reconstructed stalk structure. -/
theorem constantFiberTranslation_stalk (a : A)
    (q : (Scheme.pointSmallEtale ξ).sheafFiber.obj
      (extensionFiber (ShortComplex.mk i p h) t)) :
    (extensionFiberStalkEquiv (ShortComplex.mk i p h) t ξ
      ((Scheme.pointSmallEtale ξ).sheafFiber.map (constantFiberTranslation A i p h t a) q)).val =
      (Scheme.pointSmallEtale ξ).sheafFiber.map i ((constantAbelianStalkIso ξ A).inv a) +
        (extensionFiberStalkEquiv (ShortComplex.mk i p h) t ξ q).val := by
  let Φ := Scheme.pointSmallEtale ξ
  obtain ⟨U, x, e, rfl⟩ := Φ.toPresheafFiber_jointly_surjective
    (P := (extensionFiber (ShortComplex.mk i p h) t).obj) q
  change {b : E.obj.obj (op U) // p.hom.app (op U) b = t.app (op U) PUnit.unit} at e
  have hn := Φ.toPresheafFiber_naturality_apply
    (constantFiberTranslation A i p h t a).hom U x e
  change (extensionFiberStalkEquiv (ShortComplex.mk i p h) t ξ
    (Φ.presheafFiber.map (constantFiberTranslation A i p h t a).hom
      (Φ.toPresheafFiber U x (extensionFiber (ShortComplex.mk i p h) t).obj e))).val = _
  rw [hn, extensionFiberStalkEquiv_toFiber, extensionFiberStalkEquiv_toFiber]
  change Φ.toPresheafFiber U x E.obj
      (i.hom.app (op U) (constantSection A (op U) a) + e.val) = _
  rw [map_add]
  apply congrArg (· + Φ.toPresheafFiber U x E.obj e.val)
  have hi := Φ.toPresheafFiber_naturality_apply i.hom U x (constantSection A (op U) a)
  have ha : Φ.toPresheafFiber U x
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A).obj
      (constantSection A (op U) a) = (constantAbelianStalkIso ξ A).inv a := by
    apply (ConcreteCategory.bijective_of_isIso (constantAbelianStalkIso ξ A).hom).1
    exact (ConcreteCategory.congr_hom (constantAbelianStalkIso_unit ξ A U x) a).trans
      ((constantAbelianStalkIso ξ A).inv_hom_id_apply a).symm
  exact hi.symm.trans (congrArg (Φ.sheafFiber.map i) ha)

end EtaleFundamentalGroups.Cohomology
