/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GeometricFiber.FieldSourceGalois
import Nyll.EtaleFundamentalGroups.GeometricFiber.FieldFundamentalGroupConjugacy
import Nyll.EtaleFundamentalGroups.GeometricFiber.BasePoint

/-!
# Comparing the strict-fraction and canonical fraction-point maps

The actual field comparison used for the inertia image is whiskered through
the original scheme pullback. This constructs the target base-point
comparison and proves the map square exactly, including its inner conjugator.
-/

noncomputable section

open CategoryTheory CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.FiniteEtale

universe u

private theorem fundamentalGroupHom_conjAut
    {S X : Scheme.{u}} {Ω Ω' : Type u} [Field Ω] [Field Ω']
    (r : S ⟶ X) (p : Spec (.of Ω) ⟶ S) (p' : Spec (.of Ω') ⟶ S)
    (s : fiber p ≅ fiber p') (τ : π₁ᵉᵗ(p)) :
    ((pullbackFiberIso r p).symm ≪≫
      Functor.isoWhiskerLeft (pullback r) s ≪≫ pullbackFiberIso r p').conjAut
        (fundamentalGroupHom r p τ) =
      fundamentalGroupHom r p' (s.conjAut τ) := by
  let W := (Functor.whiskeringLeft (FiniteEtale X) (FiniteEtale S) FintypeCat).obj
    (pullback r)
  let t := (pullbackFiberIso r p).symm ≪≫
    Functor.isoWhiskerLeft (pullback r) s ≪≫ pullbackFiberIso r p'
  change t.conjAut ((pullbackFiberIso r p).conjAut (W.mapAut (fiber p) τ)) =
    (pullbackFiberIso r p').conjAut (W.mapAut (fiber p') (s.conjAut τ))
  rw [← Iso.trans_conjAut]
  have ht : pullbackFiberIso r p ≪≫ t =
      Functor.isoWhiskerLeft (pullback r) s ≪≫ pullbackFiberIso r p' := by
    dsimp only [t]
    rw [← Iso.trans_assoc, Iso.self_symm_id, Iso.refl_trans]
  rw [ht, Iso.trans_conjAut]
  exact congrArg (pullbackFiberIso r p').conjAut
    (Functor.map_conjAut W s τ).symm

variable (F E L : Type u) [Field F] [Field E] [Field L]
  [Algebra F E] [Algebra E L] [Algebra F L] [IsScalarTower F E L]
  [IsSepClosure F L] [IsSepClosed L]
  {X : Scheme.{u}} (r : Spec (.of F) ⟶ X)

/-- The base-point comparison on X induced by the actual field comparison
used to identify the strict fraction-field inertia image. -/
def fieldSourceComparisonFiberIso :
    fiber ((ξ E L ≫ ξ F E) ≫ r) ≅ fiber (ξ F L ≫ r) :=
  (pullbackFiberIso r (ξ E L ≫ ξ F E)).symm ≪≫
    Functor.isoWhiskerLeft (pullback r)
      (fieldBasePointFiberIso F E L ≪≫ fieldFundamentalGroupComparisonAut F E L) ≪≫
    pullbackFiberIso r (ξ F L)

/-- The canonical Galois map and the strict-fraction comparison commute
under the explicitly constructed target fibre isomorphism. -/
theorem fieldSourceAbsoluteGaloisHom_comparison
    (τ : π₁ᵉᵗ(ξ E L ≫ ξ F E)) :
    (fieldSourceComparisonFiberIso F E L r).conjAut
        (fundamentalGroupHom r (ξ E L ≫ ξ F E) τ) =
      fieldSourceAbsoluteGaloisHom F L r
        (((fieldBasePointFiberIso F E L).conjAut.trans
          (MulAut.conj (fieldFundamentalGroupComparisonAut F E L))).trans
            (absoluteGaloisToFiberAutMulEquiv F L inferInstance).symm τ) := by
  let p : fiber (ξ E L ≫ ξ F E) ≅ fib F L := fieldBasePointFiberIso F E L
  let a : Aut (fib F L) := fieldFundamentalGroupComparisonAut F E L
  have h := fundamentalGroupHom_conjAut r (ξ E L ≫ ξ F E) (ξ F L) (p ≪≫ a) τ
  have hinner (b c : Aut (fib F L)) : b.conjAut c = MulAut.conj b c := by
    apply Aut.ext
    rfl
  have hs : (p ≪≫ a).conjAut τ = MulAut.conj a (p.conjAut τ) :=
    (Iso.trans_conjAut p a τ).trans (hinner a (p.conjAut τ))
  have hmap := h.trans (congrArg (fundamentalGroupHom r (ξ F L)) hs)
  let absolute := absoluteGaloisToFiberAutMulEquiv F L inferInstance
  have habsolute : suppliedGaloisEquivFundamentalGroup F L
        (absolute.symm (MulAut.conj a (p.conjAut τ))) = MulAut.conj a (p.conjAut τ) := by
    exact (show suppliedGaloisEquivFundamentalGroup F L
        (absolute.symm (MulAut.conj a (p.conjAut τ))) =
      absolute (absolute.symm (MulAut.conj a (p.conjAut τ))) from rfl).trans
        (absolute.apply_symm_apply (MulAut.conj a (p.conjAut τ)))
  exact hmap.trans (congrArg (fundamentalGroupHom r (ξ F L)) habsolute).symm

end AlgebraicGeometry.FiniteEtale
