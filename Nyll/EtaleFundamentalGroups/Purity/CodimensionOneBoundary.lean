/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.LocalGeometry.GenericComplementPuncture
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.Order.KrullDimension
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.Topology.Inseparable
import Mathlib.Topology.Irreducible
import Mathlib.Topology.Closure
import Mathlib.Topology.KrullDimension
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.Sober
import Mathlib.Tactic.NormNum

/-!
# Codimension-one points of a dense-open boundary

A point with one-dimensional stalk outside a dense open in a locally
Noetherian scheme is a generic point of that open's complement. Indeed,
in an affine neighbourhood, every irreducible component meets the dense
open. A proper generization still outside the open would therefore give
a chain of two strict generizations, contradicting the stalk dimension.

Consequently the actual pullback of the dense open to this stalk is its
punctured spectrum. This supplies the generic-boundary hypothesis needed
for the DVR extension step in Stacks Project, Lemma 58.31.2:
https://stacks.math.columbia.edu/tag/0H2W

Neither regularity nor an assumed extension of a cover is used here.
-/

noncomputable section

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme

universe u

private theorem genericPoint_mem_dense_open
    {X : Scheme.{u}} [NoetherianSpace X] (U : X.Opens)
    (hU : Dense (U : Set X)) (η : genericPoints X) : η.1 ∈ U := by
  obtain ⟨O, hO, hOne, hOcomponent⟩ :=
    NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent
      (closure {η.1}) η.2
  obtain ⟨z, hzO, hzU⟩ := hU.inter_open_nonempty O hO hOne
  apply ((genericPoints.isGenericPoint η).mem_open_set_iff U.isOpen).mpr
  exact ⟨z, hOcomponent hzO, hzU⟩

/-- Every proper generization of a point with one-dimensional stalk belongs
to any dense open that omits that point. The proof is affine-local, so the
ambient scheme need only be locally Noetherian. -/
theorem mem_dense_open_of_specializes_of_stalk_dimension_one
    {X : Scheme.{u}} [IsLocallyNoetherian X] (U : X.Opens)
    (hU : Dense (U : Set X)) (x : X)
    (hdim : ringKrullDim (X.presheaf.stalk x) = (1 : WithBot ℕ∞))
    (y : X) (hyx : y ⤳ x) (hne : y ≠ x) : y ∈ U := by
  by_contra hyU
  obtain ⟨A, hA, hxA, _⟩ := exists_isAffineOpen_mem_and_subset
    (U := (⊤ : X.Opens)) (x := x) (by trivial)
  have : IsNoetherianRing Γ(X, A) :=
    IsLocallyNoetherian.component_noetherian ⟨A, hA⟩
  have : NoetherianSpace A.toScheme := noetherianSpace_of_isAffineOpen A hA
  let xA : A.toScheme := ⟨x, hxA⟩
  let yA : A.toScheme := ⟨y, hyx.mem_open A.isOpen hxA⟩
  let UA : A.toScheme.Opens := A.ι ⁻¹ᵁ U
  have hUA : Dense (UA : Set A.toScheme) :=
    hU.preimage A.ι.isOpenEmbedding.isOpenMap
  let C : irreducibleComponents A.toScheme :=
    ⟨irreducibleComponent yA, irreducibleComponent_mem_irreducibleComponents yA⟩
  let η : genericPoints A.toScheme := genericPoints.ofComponent C
  have hηU : η.1 ∈ UA := genericPoint_mem_dense_open UA hUA η
  have hηy : η.1 ⤳ yA :=
    (genericPoints.isGenericPoint_ofComponent C).specializes mem_irreducibleComponent
  have hxy : xA < yA := by
    refine ⟨(subtype_specializes_iff yA xA).mpr hyx, ?_⟩
    intro h
    have hxy' : x ⤳ y := (subtype_specializes_iff xA yA).mp h
    exact hne (hyx.antisymm hxy').eq
  have hyη : yA < η.1 := by
    refine ⟨hηy, ?_⟩
    intro h
    have hyU' : yA ∈ UA := (show yA ⤳ η.1 from h).mem_open UA.isOpen hηU
    exact hyU hyU'
  have hxheight : Order.coheight xA = (1 : ℕ∞) := by
    apply WithBot.coe_eq_coe.mp
    calc
      ((Order.coheight xA : ℕ∞) : WithBot ℕ∞) =
          ((Order.coheight x : ℕ∞) : WithBot ℕ∞) :=
        congrArg (fun n : ℕ∞ ↦ (n : WithBot ℕ∞))
          (coheight_eq_of_isOpenImmersion (x := xA) A.ι).symm
      _ = ringKrullDim (X.presheaf.stalk x) :=
        (ringKrullDim_stalk_eq_coheight x).symm
      _ = ((1 : ℕ∞) : WithBot ℕ∞) := hdim
  have hyheight : (1 : ℕ∞) ≤ Order.coheight yA := by
    calc
      (1 : ℕ∞) = 0 + 1 := (zero_add 1).symm
      _ ≤ Order.coheight η.1 + 1 :=
        add_le_add_left (show (0 : ℕ∞) ≤ Order.coheight η.1 from zero_le) 1
      _ ≤ Order.coheight yA := Order.coheight_add_one_le hyη
  have htwo : (2 : ℕ∞) ≤ Order.coheight xA := by
    calc
      (2 : ℕ∞) = 1 + 1 := by norm_num
      _ ≤ Order.coheight yA + 1 := add_le_add_left hyheight 1
      _ ≤ Order.coheight xA := Order.coheight_add_one_le hxy
  rw [hxheight] at htwo
  norm_num at htwo

/-- A codimension-one boundary point of a dense open is a generic point of
an irreducible component of the complement. No regularity is required. -/
theorem mem_genericPoints_complement_of_stalk_dimension_one
    {X : Scheme.{u}} [IsLocallyNoetherian X] (U : X.Opens)
    (hU : Dense (U : Set X)) (x : X) (hx : x ∉ U)
    (hdim : ringKrullDim (X.presheaf.stalk x) = (1 : WithBot ℕ∞)) :
    (⟨x, hx⟩ : {z : X // z ∉ U}) ∈ genericPoints {z : X // z ∉ U} := by
  have hclosed : IsClosed {z : X | z ∉ U} := U.isOpen.isClosed_compl
  have : QuasiSober {z : X // z ∉ U} :=
    hclosed.isClosedEmbedding_subtypeVal.quasiSober
  rw [genericPoints]
  refine ⟨isIrreducible_singleton.closure, ?_⟩
  intro Z hZ hsub
  let y : {z : X // z ∉ U} := hZ.genericPoint
  have hy : IsGenericPoint y (closure Z) := hZ.isGenericPoint_genericPoint_closure
  have hyx : y ⤳ (⟨x, hx⟩ : {z : X // z ∉ U}) := by
    apply hy.specializes
    exact subset_closure (hsub (subset_closure (Set.mem_singleton _)))
  have hyval : y.1 = x := by
    by_contra hne
    exact y.2 (mem_dense_open_of_specializes_of_stalk_dimension_one U hU x hdim
      y.1 ((subtype_specializes_iff y ⟨x, hx⟩).mp hyx) hne)
  have hyeq : y = (⟨x, hx⟩ : {z : X // z ∉ U}) := Subtype.ext hyval
  calc
    Z ⊆ closure Z := subset_closure
    _ = closure {y} := hy.def.symm
    _ = closure {(⟨x, hx⟩ : {z : X // z ∉ U})} := by rw [hyeq]

/-- At every codimension-one point outside a dense open, the inverse image
of that open in the actual stalk spectrum is exactly the puncture. -/
theorem fromSpecStalk_preimage_dense_open_eq_puncturedSpectrumOpen
    {X : Scheme.{u}} [IsLocallyNoetherian X] (U : X.Opens)
    (hU : Dense (U : Set X)) (x : X) (hx : x ∉ U)
    (hdim : ringKrullDim (X.presheaf.stalk x) = (1 : WithBot ℕ∞)) :
    X.fromSpecStalk x ⁻¹ᵁ U = puncturedSpectrumOpen (X.presheaf.stalk x) :=
  fromSpecStalk_preimage_open_eq_puncturedSpectrumOpen U
    ⟨⟨x, hx⟩, mem_genericPoints_complement_of_stalk_dimension_one U hU x hx hdim⟩

end AlgebraicGeometry.Scheme
