/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkStructure
import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkResidueSeparable
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.Algebra.Polynomial.Lifts

/-!
# Identifying the geometric stalk's residue field with the chosen closure

Let the geometric field be a separably closed separable algebraic extension
of the residue field of a local ring. Every element of that field is a simple
root of its minimal polynomial. Lift the coefficients to the local ring and
then to its actual geometric étale stalk. The standard étale root construction
produces a germ with exactly the prescribed value at the geometric point.

Consequently evaluation induces a bijection from the stalk's residue field
to the chosen separable closure. For residue characteristic zero this applies
to the algebraic closure used by the manuscript. No residue-field comparison
is supplied as an assumption.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Polynomial

namespace EtaleFundamentalGroups.StrictHenselian

universe u

/-- Every element separable over the base residue field lies in the actual
stalk residue image. The simple-root construction does not require the whole
geometric overfield to be separable over that residue field. -/
theorem geometricStalkResidueEmbedding_mem_range_of_isSeparable
    (R Ω : Type u) [CommRing R] [IsLocalRing R] [Field Ω] [IsSepClosed Ω]
    [Algebra (IsLocalRing.ResidueField R) Ω]
    (α : Ω) (hsepα : IsSeparable (IsLocalRing.ResidueField R) α) :
    α ∈ Set.range (geometricStalkResidueEmbedding
      (Spec.map (CommRingCat.ofHom
        ((algebraMap (IsLocalRing.ResidueField R) Ω).comp
          (IsLocalRing.residue R))))) := by
  let k := IsLocalRing.ResidueField R
  let φ : R →+* Ω := (algebraMap k Ω).comp (IsLocalRing.residue R)
  let s : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of R) :=
    Spec.map (CommRingCat.ofHom φ)
  have hα : IsIntegral k α := hsepα.isIntegral
  let p : k[X] := minpoly k α
  have hp : p.Monic := minpoly.monic hα
  have hsep : p.Separable := hsepα
  obtain ⟨q, hqp, _, hq⟩ := Polynomial.lifts_and_degree_eq_and_monic
    (Polynomial.mem_lifts_of_surjective
      (IsLocalRing.residue_surjective (R := R)) p) hp
  let P : (geometricStalk s)[X] := q.map (geometricStalkStructureMap φ)
  have hP : P.Monic := hq.map _
  have hmap : P.map (geometricStalkEvaluation s).hom =
      p.map (algebraMap k Ω) := by
    change (q.map (geometricStalkStructureMap φ)).map
      (geometricStalkEvaluation s).hom = _
    rw [Polynomial.map_map, geometricStalkStructureMap_evaluation]
    change q.map ((algebraMap k Ω).comp (IsLocalRing.residue R)) = _
    rw [← Polynomial.map_map, hqp]
  have hrootp : p.eval₂ (algebraMap k Ω) α = 0 := minpoly.aeval k α
  have hroot : (P.map (geometricStalkEvaluation s).hom).eval α = 0 := by
    rw [hmap, eval_map]
    exact hrootp
  have hderivative :
      (P.derivative.map (geometricStalkEvaluation s).hom).eval α ≠ 0 := by
    rw [← derivative_map, hmap, derivative_map, eval_map]
    exact hsep.eval₂_derivative_ne_zero (algebraMap k Ω) hrootp
  obtain ⟨a, _, ha⟩ :=
    geometricStalk_exists_root_of_evaluation_simpleRoot s P hP α hroot hderivative
  refine ⟨IsLocalRing.residue (geometricStalk s) a, ?_⟩
  change IsLocalRing.ResidueField.lift (geometricStalkEvaluation s).hom
    (IsLocalRing.residue (geometricStalk s) a) = α
  rw [IsLocalRing.ResidueField.lift_residue_apply]
  exact ha

/-- The residue embedding of the actual geometric étale stalk is onto a
chosen separable closure, by the actual simple-root preimages above. -/
theorem geometricStalkResidueEmbedding_bijective
    (R Ω : Type u) [CommRing R] [IsLocalRing R] [Field Ω] [IsSepClosed Ω]
    [Algebra (IsLocalRing.ResidueField R) Ω]
    [Algebra.IsSeparable (IsLocalRing.ResidueField R) Ω] :
    Function.Bijective (geometricStalkResidueEmbedding
      (Spec.map (CommRingCat.ofHom
        ((algebraMap (IsLocalRing.ResidueField R) Ω).comp
          (IsLocalRing.residue R))))) :=
  ⟨(geometricStalkResidueEmbedding _).injective,
    fun α => geometricStalkResidueEmbedding_mem_range_of_isSeparable R Ω α
      (Algebra.IsSeparable.isSeparable (IsLocalRing.ResidueField R) α)⟩

/-- The actual residue embedding is linear over the original residue field,
as witnessed on residues of original coefficients. -/
def geometricStalkResidueAlgHom
    (R Ω : Type u) [CommRing R] [IsLocalRing R] [Field Ω] [IsSepClosed Ω]
    [Algebra (IsLocalRing.ResidueField R) Ω] :
    let φ := (algebraMap (IsLocalRing.ResidueField R) Ω).comp (IsLocalRing.residue R)
    let : Algebra R (geometricStalk (Spec.map (CommRingCat.ofHom φ))) :=
      (geometricStalkStructureMap φ).toAlgebra
    let : IsLocalHom (algebraMap R (geometricStalk (Spec.map (CommRingCat.ofHom φ)))) := by
      change IsLocalHom (geometricStalkStructureMap φ)
      exact geometricStalkStructureMap_isLocalHom φ
    IsLocalRing.ResidueField (geometricStalk (Spec.map (CommRingCat.ofHom φ))) →ₐ[
      IsLocalRing.ResidueField R] Ω := by
  intro φ actualStructureAlgebra actualStructureLocal
  refine { geometricStalkResidueEmbedding (Spec.map (CommRingCat.ofHom φ)) with
    commutes' := ?_ }
  intro x
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective (R := R) x
  change geometricStalkEvaluation (Spec.map (CommRingCat.ofHom φ))
    (geometricStalkStructureMap φ a) = algebraMap (IsLocalRing.ResidueField R) Ω
      (IsLocalRing.residue R a)
  exact geometricStalkStructureMap_evaluation_apply φ a

/-- The image of the actual geometric-stalk residue consists exactly of
separable elements over the original residue field. -/
theorem geometricStalkResidueEmbedding_mem_range_iff
    (R Ω : Type u) [CommRing R] [IsLocalRing R] [Field Ω] [IsSepClosed Ω]
    [Algebra (IsLocalRing.ResidueField R) Ω] (α : Ω) :
    α ∈ Set.range (geometricStalkResidueEmbedding
      (Spec.map (CommRingCat.ofHom
        ((algebraMap (IsLocalRing.ResidueField R) Ω).comp (IsLocalRing.residue R))))) ↔
      IsSeparable (IsLocalRing.ResidueField R) α := by
  let φ := (algebraMap (IsLocalRing.ResidueField R) Ω).comp (IsLocalRing.residue R)
  let : Algebra R (geometricStalk (Spec.map (CommRingCat.ofHom φ))) :=
    (geometricStalkStructureMap φ).toAlgebra
  have : IsLocalHom (algebraMap R (geometricStalk (Spec.map (CommRingCat.ofHom φ)))) := by
    change IsLocalHom (geometricStalkStructureMap φ)
    exact geometricStalkStructureMap_isLocalHom φ
  have : Algebra.IsSeparable (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField (geometricStalk (Spec.map (CommRingCat.ofHom φ)))) :=
    geometricStalk_residue_isSeparable R Ω φ
  constructor
  · rintro ⟨x, rfl⟩
    exact (Algebra.IsSeparable.isSeparable (IsLocalRing.ResidueField R) x).map
      (geometricStalkResidueAlgHom R Ω) (geometricStalkResidueAlgHom R Ω).injective
  · exact geometricStalkResidueEmbedding_mem_range_of_isSeparable R Ω α

/-- The actual residue image is precisely the separable part of the geometric
field. In particular this statement applies to the normalization residue
field even when it contains inseparable elements over the base residue field. -/
theorem geometricStalkResidueAlgHom_fieldRange
    (R Ω : Type u) [CommRing R] [IsLocalRing R] [Field Ω] [IsSepClosed Ω]
    [Algebra (IsLocalRing.ResidueField R) Ω] :
    let φ := (algebraMap (IsLocalRing.ResidueField R) Ω).comp (IsLocalRing.residue R)
    let : Algebra R (geometricStalk (Spec.map (CommRingCat.ofHom φ))) :=
      (geometricStalkStructureMap φ).toAlgebra
    let : IsLocalHom (algebraMap R (geometricStalk (Spec.map (CommRingCat.ofHom φ)))) := by
      change IsLocalHom (geometricStalkStructureMap φ)
      exact geometricStalkStructureMap_isLocalHom φ
    (geometricStalkResidueAlgHom R Ω).fieldRange =
      separableClosure (IsLocalRing.ResidueField R) Ω := by
  intro φ actualStructureAlgebra actualStructureLocal
  apply IntermediateField.ext
  intro α
  exact geometricStalkResidueEmbedding_mem_range_iff R Ω α

/-- The constructed stalk residue is the actual separable closure inside the
chosen geometric field, with the original residue coefficient action. -/
def geometricStalkResidueSeparableClosureEquiv
    (R Ω : Type u) [CommRing R] [IsLocalRing R] [Field Ω] [IsSepClosed Ω]
    [Algebra (IsLocalRing.ResidueField R) Ω] :
    let φ := (algebraMap (IsLocalRing.ResidueField R) Ω).comp (IsLocalRing.residue R)
    let : Algebra R (geometricStalk (Spec.map (CommRingCat.ofHom φ))) :=
      (geometricStalkStructureMap φ).toAlgebra
    let : IsLocalHom (algebraMap R (geometricStalk (Spec.map (CommRingCat.ofHom φ)))) := by
      change IsLocalHom (geometricStalkStructureMap φ)
      exact geometricStalkStructureMap_isLocalHom φ
    IsLocalRing.ResidueField (geometricStalk (Spec.map (CommRingCat.ofHom φ))) ≃ₐ[
      IsLocalRing.ResidueField R] separableClosure (IsLocalRing.ResidueField R) Ω := by
  intro φ actualStructureAlgebra actualStructureLocal
  exact (geometricStalkResidueAlgHom R Ω).equivFieldRange.trans
    (IntermediateField.equivOfEq (geometricStalkResidueAlgHom_fieldRange R Ω))

/-- The residue comparison retains the literal embedding into the chosen
geometric field. -/
theorem geometricStalkResidueSeparableClosureEquiv_apply
    (R Ω : Type u) [CommRing R] [IsLocalRing R] [Field Ω] [IsSepClosed Ω]
    [Algebra (IsLocalRing.ResidueField R) Ω] :
    let φ := (algebraMap (IsLocalRing.ResidueField R) Ω).comp (IsLocalRing.residue R)
    let : Algebra R (geometricStalk (Spec.map (CommRingCat.ofHom φ))) :=
      (geometricStalkStructureMap φ).toAlgebra
    let : IsLocalHom (algebraMap R (geometricStalk (Spec.map (CommRingCat.ofHom φ)))) := by
      change IsLocalHom (geometricStalkStructureMap φ)
      exact geometricStalkStructureMap_isLocalHom φ
    ∀ x : IsLocalRing.ResidueField (geometricStalk (Spec.map (CommRingCat.ofHom φ))),
      ((geometricStalkResidueSeparableClosureEquiv R Ω x :
        separableClosure (IsLocalRing.ResidueField R) Ω) : Ω) =
          geometricStalkResidueEmbedding (Spec.map (CommRingCat.ofHom φ)) x := by
  intro φ actualStructureAlgebra actualStructureLocal x
  rfl

/-- In residue characteristic zero the residue field of the constructed
geometric stalk is canonically identified with the very algebraic closure
used to define its closed geometric point. -/
def geometricStalkResidueAlgebraicClosureEquiv
    (R : Type u) [CommRing R] [IsLocalRing R]
    [CharZero (IsLocalRing.ResidueField R)] :
    IsLocalRing.ResidueField
      (geometricStalk (Spec.map (CommRingCat.ofHom
        ((algebraMap (IsLocalRing.ResidueField R)
            (AlgebraicClosure (IsLocalRing.ResidueField R))).comp
          (IsLocalRing.residue R))))) ≃+*
      AlgebraicClosure (IsLocalRing.ResidueField R) :=
  RingEquiv.ofBijective _ (geometricStalkResidueEmbedding_bijective R
    (AlgebraicClosure (IsLocalRing.ResidueField R)))

end EtaleFundamentalGroups.StrictHenselian
