/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.EtaleFundamentalGroups.GeometricFiber.GenericPointSurjective
import Nyll.EtaleFundamentalGroups.GeometricFiber.AlgebraicClosure
import Nyll.EtaleFundamentalGroups.GeometricFiber.Functoriality
import Nyll.EtaleFundamentalGroups.GaloisCategories.Functoriality
import Mathlib.FieldTheory.IsSepClosed

/-!
# The actual generic Galois map at the separable geometric point

The canonical extension from the separable closure to the algebraic closure
compares the two actual generic fiber functors. Under this comparison, the
canonical generic absolute Galois map is exactly the scheme-induced map of
the original field monodromy action.
-/

noncomputable section

universe u u₀ v₀ u₁ v₁ w

open CategoryTheory CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.FiniteEtale

private theorem conjugate_induced_aut
    {C : Type u₀} [Category.{v₀} C] {D : Type u₁} [Category.{v₁} D]
    (H : C ⥤ D) {F G : C ⥤ FintypeCat.{w}} {F' G' : D ⥤ FintypeCat.{w}}
    (r : H ⋙ F' ≅ F) (t : H ⋙ G' ≅ G) (e : F' ≅ G') (a : Aut F') :
    (r.symm ≪≫ Functor.isoWhiskerLeft H e ≪≫ t).conjAut
      (autHomOfCompIso H r a) = autHomOfCompIso H t (e.conjAut a) := by
  have hw :
      (Functor.isoWhiskerLeft H e).conjAut
          (((Functor.whiskeringLeft C D FintypeCat.{w}).obj H).mapAut F' a) =
        (((Functor.whiskeringLeft C D FintypeCat.{w}).obj H).mapAut G' (e.conjAut a)) := by
    apply Iso.ext
    apply NatTrans.ext
    funext A
    simp only [Iso.conjAut_hom, Iso.conj_apply, NatTrans.comp_app]
    rfl
  change (r.symm ≪≫ Functor.isoWhiskerLeft H e ≪≫ t).conjAut
      (r.conjAut (((Functor.whiskeringLeft C D FintypeCat.{w}).obj H).mapAut F' a)) =
    t.conjAut (((Functor.whiskeringLeft C D FintypeCat.{w}).obj H).mapAut G' (e.conjAut a))
  rw [← Iso.trans_conjAut, Iso.self_symm_id_assoc, Iso.trans_conjAut, hw]

/-- The generic fiber comparison is induced by the actual inclusion of the
separable closure in the algebraic closure and by the actual pullback fibers. -/
def genericSeparableFiberIso (X : Scheme.{u}) [IsIntegral X] :
    fiber (X.genericExtensionMorphism (SeparableClosure X.functionField)) ≅
      fiber (X.genericExtensionMorphism (AlgebraicClosure X.functionField)) :=
  (pullbackFiberIso (X.fromSpecStalk (genericPoint X))
    (ξ X.functionField (SeparableClosure X.functionField))).symm ≪≫
      Functor.isoWhiskerLeft (pullback (X.fromSpecStalk (genericPoint X)))
        (fieldFiberExtensionIso X.functionField (SeparableClosure X.functionField)
          (AlgebraicClosure X.functionField)) ≪≫
      pullbackFiberIso (X.fromSpecStalk (genericPoint X))
        (ξ X.functionField (AlgebraicClosure X.functionField))

/-- The canonical generic absolute Galois map is the actual scheme-induced
separable field action transported by the canonical fiber comparison. -/
theorem genericAbsoluteGaloisHom_eq_separable
    (X : Scheme.{u}) [IsIntegral X]
    (σ : Gal(SeparableClosure X.functionField/X.functionField)) :
    let : IsSepClosure X.functionField (SeparableClosure X.functionField) :=
      separableClosure.isSepClosure X.functionField (AlgebraicClosure X.functionField)
    genericAbsoluteGaloisHom X σ =
      (genericSeparableFiberIso X).conjAut
        (fundamentalGroupHom (X.fromSpecStalk (genericPoint X))
          (ξ X.functionField (SeparableClosure X.functionField))
          (toAut (fib X.functionField (SeparableClosure X.functionField))
            Gal(SeparableClosure X.functionField/X.functionField) σ)) := by
  intro hclosure
  let j := X.fromSpecStalk (genericPoint X)
  let e := fieldFiberExtensionIso X.functionField (SeparableClosure X.functionField)
    (AlgebraicClosure X.functionField)
  let a := toAut (fib X.functionField (SeparableClosure X.functionField))
    Gal(SeparableClosure X.functionField/X.functionField) σ
  have hfield : absoluteGaloisEquivFundamentalGroup X.functionField σ = e.conjAut a := rfl
  change fundamentalGroupHom j (ξ X.functionField (AlgebraicClosure X.functionField))
      (absoluteGaloisEquivFundamentalGroup X.functionField σ) = _
  rw [hfield]
  exact (conjugate_induced_aut (pullback j)
    (pullbackFiberIso j (ξ X.functionField (SeparableClosure X.functionField)))
    (pullbackFiberIso j (ξ X.functionField (AlgebraicClosure X.functionField))) e a).symm

end AlgebraicGeometry.FiniteEtale
