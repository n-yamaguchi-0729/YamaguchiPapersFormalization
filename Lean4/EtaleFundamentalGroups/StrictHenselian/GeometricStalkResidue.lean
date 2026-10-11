/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.StrictHenselian.GeometricStalkHenselian
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.LocalRing.RingHom.Basic


/-!
# The separably closed residue field of the geometric étale stalk

Evaluation of the constructed stalk in the geometric field is a local
homomorphism, so it induces an embedding of its actual residue field into that
field. For a monic separable irreducible residue polynomial, lift its coefficients
to the stalk. Its simple root in the geometric field lifts to a root in the
stalk by the concrete standard étale neighborhood from
`GeometricStalkHenselian`. Reduction of this root proves that the residue field
is separably closed.

Thus the constructed ring is strictly local: it is Henselian with separably
closed residue field. This does not yet identify it with a separately chosen
strict henselization, or establish the manuscript's inertia comparison.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Polynomial

namespace EtaleFundamentalGroups.StrictHenselian

universe u

variable {S : Scheme.{u}} {Ω : Type u} [Field Ω]
  (s : Spec (.of Ω) ⟶ S)

/-- Evaluation is local because its nonzero values are precisely the units
of the constructed geometric stalk. -/
instance geometricStalkEvaluation_isLocalHom :
    IsLocalHom (geometricStalkEvaluation s).hom where
  map_nonunit a ha := geometricStalk_isUnit_of_evaluation_ne_zero s a ha.ne_zero

/-- The embedding of the actual residue field of the geometric étale stalk
into the chosen geometric field. -/
def geometricStalkResidueEmbedding :
    IsLocalRing.ResidueField (geometricStalk s) →+* Ω :=
  IsLocalRing.ResidueField.lift (geometricStalkEvaluation s).hom

/-- Every monic separable irreducible residue polynomial has a root, obtained
by adjoining a simple root in an actual pointed étale neighborhood. -/
instance geometricStalk_residueField_isSepClosed [IsSepClosed Ω] :
    IsSepClosed (IsLocalRing.ResidueField (geometricStalk s)) := by
  apply IsSepClosed.of_exists_root
  intro p hp hirr hsep
  obtain ⟨q, hqp, _, hq⟩ := Polynomial.lifts_and_degree_eq_and_monic
    (Polynomial.mem_lifts_of_surjective
      (IsLocalRing.residue_surjective (R := geometricStalk s)) p) hp
  let i : IsLocalRing.ResidueField (geometricStalk s) →+* Ω :=
    geometricStalkResidueEmbedding s
  obtain ⟨α, hα⟩ := IsSepClosed.exists_eval₂_eq_zero i p
    (Polynomial.degree_pos_of_irreducible hirr).ne' hsep
  have hmap : q.map (geometricStalkEvaluation s).hom = p.map i := by
    rw [← hqp, Polynomial.map_map]
    change q.map (geometricStalkEvaluation s).hom = q.map
      ((IsLocalRing.ResidueField.lift (geometricStalkEvaluation s).hom).comp
        (IsLocalRing.residue (geometricStalk s)))
    rw [IsLocalRing.ResidueField.lift_comp_residue]
  have hroot : (q.map (geometricStalkEvaluation s).hom).eval α = 0 := by
    rw [hmap, eval_map]
    exact hα
  have hderivative : (q.derivative.map (geometricStalkEvaluation s).hom).eval α ≠ 0 := by
    rw [← derivative_map, hmap, derivative_map, eval_map]
    exact hsep.eval₂_derivative_ne_zero i hα
  obtain ⟨a, ha, _⟩ :=
    geometricStalk_exists_root_of_evaluation_simpleRoot s q hq α hroot hderivative
  refine ⟨IsLocalRing.residue (geometricStalk s) a, ?_⟩
  change q.eval a = 0 at ha
  rw [← hqp, eval_map_apply, ha, map_zero]

end EtaleFundamentalGroups.StrictHenselian
