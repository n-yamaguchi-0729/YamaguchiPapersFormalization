/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GeometricFiber.FieldSourceGaloisPoint
import Nyll.EtaleFundamentalGroups.GeometricFiber.HenselianSpecializationConjugacy

/-!
# The complete point calculation for a transported actual field-source map

The supplied Galois comparison, the actual scheme-induced map, equality of
geometric points, and the final projection to a geometric point are computed
at abstract field and scheme structures. A caller supplies its proved actual
automorphism and coefficient equalities, with no concrete fiber expansion.
-/

noncomputable section

open CategoryTheory CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.FiniteEtale

universe u

variable (F Ω : Type u) [Field F] [Field Ω] [Algebra F Ω]
  [IsSepClosure F Ω] [IsSepClosed Ω]
  {S : Scheme.{u}}

/-- The complete actual field-source point action, after the specified
geometric-point equality and the proved automorphism computation. -/
theorem transportedFieldSourceAbsoluteGaloisHom_point
    (j : Spec (.of F) ⟶ S) (t : Spec (.of Ω) ⟶ S)
    (hpoint : ξ F Ω ≫ j = t)
    (σ : Gal(Ω/F)) (ρ : Ω →+* Ω) (hσ : σ.toRingHom = ρ)
    (a : π₁ᵉᵗ(t))
    (ha : a = continuousConjAut (eqToIso (congrArg fiber hpoint))
      (fieldSourceAbsoluteGaloisHom F Ω j σ))
    (X : FiniteEtale S) (x : (fiber t).obj X) :
    (fiberObjEquivHom t X (a.hom.app X x)).left =
      Spec.map (CommRingCat.ofHom ρ) ≫ (fiberObjEquivHom t X x).left := by
  have hsource (Y : FiniteEtale (Spec (.of F))) (y : (fib F Ω).obj Y) :
      (fiberObjEquivHom (ξ F Ω) Y
        ((suppliedGaloisEquivFundamentalGroup F Ω σ).hom.app Y y)).left =
        Spec.map (CommRingCat.ofHom ρ) ≫ (fiberObjEquivHom (ξ F Ω) Y y).left :=
    (suppliedGaloisEquivFundamentalGroup_point F Ω σ Y y).trans
      (congrArg (fun r : Ω →+* Ω => Spec.map (CommRingCat.ofHom r) ≫
        (fiberObjEquivHom (ξ F Ω) Y y).left) hσ)
  exact (congrArg (fun b : π₁ᵉᵗ(t) =>
    (fiberObjEquivHom t X (b.hom.app X x)).left) ha).trans
      (point_action_of_eqToIso hpoint (fieldSourceAbsoluteGaloisHom F Ω j σ) ρ
        (fundamentalGroupHom_point_of_point_action j (ξ F Ω)
          (suppliedGaloisEquivFundamentalGroup F Ω σ) ρ hsource) X x)

end AlgebraicGeometry.FiniteEtale
