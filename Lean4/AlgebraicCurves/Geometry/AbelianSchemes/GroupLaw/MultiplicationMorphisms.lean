/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.Kernel
import AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.Translation
import AlgebraicCurves.Geometry.Picard.RelativeGroupLaw
import AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# The multiplication morphism of a relative group law

The existing morphism `G.mulRight f idPoint` represents multiplication on
every test scheme. Naturality supplies its unit identities and its relation
to the actual multiplication-by-an-integer morphisms, over any commutative base ring.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

namespace GoodReductionJacobian.RelativeGroupLaw

universe u

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
variable (G : RelativeGroupLaw R f)

/-- The existing multiplication morphism evaluates a pair of relative points
by the given group law. -/
theorem pullback_lift_comp_mulRight_idPoint {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f) :
    pullback.lift x.1 y.1 (x.2.trans y.2.symm) ≫ G.mulRight f idPoint =
      (G.mul t x y).1 := by
  let l : T ⟶ pullback f f := pullback.lift x.1 y.1 (x.2.trans y.2.symm)
  have hl : l ≫ (pullback.snd f f ≫ f) = t := by
    rw [← Category.assoc, pullback.lift_snd, y.2]
  have hx : GoodReductionJacobian.schemeHomOverComp l hl (G.fstPoint f) = x := by
    apply Subtype.ext
    exact pullback.lift_fst _ _ _
  have hy : GoodReductionJacobian.schemeHomOverComp l hl (G.sndPoint f idPoint) = y := by
    apply Subtype.ext
    change l ≫ (pullback.snd f f ≫ 𝟙 A) = y.1
    rw [Category.comp_id, pullback.lift_snd]
  have h := G.mul_natural (pullback.snd f f ≫ f) t l hl
    (G.fstPoint f) (G.sndPoint f idPoint)
  rw [hx, hy] at h
  exact congrArg Subtype.val h

private theorem one_coe_eq_comp_one {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) :
    (G.one t).1 = t ≫ (G.one (𝟙 (Spec (CommRingCat.of R)))).1 := by
  have h := G.one_natural (𝟙 (Spec (CommRingCat.of R))) t t (Category.comp_id t)
  exact (congrArg Subtype.val h).symm

/-- Inserting the unit in the first coordinate followed by multiplication
is the identity scheme morphism. -/
theorem leftUnit_comp_mulRight_idPoint :
    pullback.lift (f ≫ (G.one (𝟙 (Spec (CommRingCat.of R)))).1) (𝟙 A)
      (by rw [Category.assoc, (G.one (𝟙 _)).2, Category.comp_id, Category.id_comp]) ≫
        G.mulRight f idPoint = 𝟙 A := by
  let e : SchemeHomOver f f := ⟨f ≫ (G.one (𝟙 (Spec (CommRingCat.of R)))).1,
    by rw [Category.assoc, (G.one (𝟙 _)).2, Category.comp_id]⟩
  have he : e = G.one f := Subtype.ext (G.one_coe_eq_comp_one f).symm
  have hm : G.mul f e idPoint = idPoint := by rw [he, G.one_mul]
  exact (G.pullback_lift_comp_mulRight_idPoint f e idPoint).trans (congrArg Subtype.val hm)

/-- Inserting the unit in the second coordinate followed by multiplication
is the identity scheme morphism. -/
theorem rightUnit_comp_mulRight_idPoint :
    pullback.lift (𝟙 A) (f ≫ (G.one (𝟙 (Spec (CommRingCat.of R)))).1)
      (by rw [Category.assoc, (G.one (𝟙 _)).2, Category.comp_id, Category.id_comp]) ≫
        G.mulRight f idPoint = 𝟙 A := by
  let e : SchemeHomOver f f := ⟨f ≫ (G.one (𝟙 (Spec (CommRingCat.of R)))).1,
    by rw [Category.assoc, (G.one (𝟙 _)).2, Category.comp_id]⟩
  have he : e = G.one f := Subtype.ext (G.one_coe_eq_comp_one f).symm
  have hm : G.mul f idPoint e = idPoint := by rw [he, G.mul_one]
  exact (G.pullback_lift_comp_mulRight_idPoint f idPoint e).trans (congrArg Subtype.val hm)

/-- The product unit point is sent to the unit by the actual multiplication morphism. -/
theorem unitPoint_comp_mulRight_idPoint :
    pullback.lift (G.one (𝟙 (Spec (CommRingCat.of R)))).1
      (G.one (𝟙 (Spec (CommRingCat.of R)))).1 rfl ≫ G.mulRight f idPoint =
        (G.one (𝟙 (Spec (CommRingCat.of R)))).1 := by
  have h := G.pullback_lift_comp_mulRight_idPoint (𝟙 (Spec (CommRingCat.of R)))
    (G.one (𝟙 _)) (G.one (𝟙 _))
  rw [G.one_mul] at h
  exact h

/-- Pairing multiplication by `n` with the identity and then multiplying
gives the actual multiplication-by-`n+1` morphism. -/
theorem schemeNsmul_pair_id_comp_mulRight (n : ℕ) :
    pullback.lift (G.schemeNsmul n) (𝟙 A)
      ((G.schemeNsmul_over n).trans (Category.id_comp f).symm) ≫
        G.mulRight f idPoint = G.schemeNsmul (n + 1) := by
  change pullback.lift (G.schemeNsmul n) (𝟙 A) _ ≫ G.mulRight f idPoint =
    (G.nsmul f (n + 1) idPoint).1
  rw [G.nsmul_succ]
  exact G.pullback_lift_comp_mulRight_idPoint f (G.nsmul f n idPoint) idPoint

/-- Every multiplication-by-an-integer morphism fixes the unit section. -/
theorem unit_comp_schemeNsmul (n : ℕ) :
    (G.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ G.schemeNsmul n =
      (G.one (𝟙 (Spec (CommRingCat.of R)))).1 := by
  let e : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f := G.one (𝟙 _)
  have he : GoodReductionJacobian.schemeHomOverComp e.1 e.2
      (idPoint : SchemeHomOver f f) = e := by
    apply Subtype.ext
    exact Category.comp_id e.1
  have h := G.nsmul_natural f (𝟙 (Spec (CommRingCat.of R))) e.1 e.2 n idPoint
  rw [he, G.nsmul_unit] at h
  exact congrArg Subtype.val h

end GoodReductionJacobian.RelativeGroupLaw
