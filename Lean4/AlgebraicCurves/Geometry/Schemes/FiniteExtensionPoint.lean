/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
The finite residue-field calculation follows the existing adapted source:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_ext_of_forall_comp_eq_of_isAlgClosed.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Copyright (c) 2026 Naganori Yamaguchi.
Released under Apache 2.0 license as described in the file LICENSE.
Authors of the finite-extension point construction: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.Topology.JacobsonSpace
import AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import AlgebraicCurves.Geometry.Curves.SmoothProperCurveBase

/-!
# A point after a finite extension of the ground field

A closed point of a nonempty scheme locally of finite type has a finite residue field.
Its actual residue-field morphism gives a section after base change. No separability
or characteristic assumption enters the construction.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.SmoothProperCurve NeronModelInfra

namespace AlgebraicGeometry.Scheme

variable {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K))

/-- The ground-field algebra structure on the residue field induced by the structure map. -/
@[instance_reducible]
noncomputable def pointResidueAlgebra (x : X) : Algebra K (X.residueField x) :=
  (Spec.preimage (X.fromSpecResidueField x ≫ f)).hom.toAlgebra

theorem pointResidueAlgebra_specMap (x : X) :
    let _ : Algebra K (X.residueField x) := pointResidueAlgebra f x
    specMap K (X.residueField x) = X.fromSpecResidueField x ≫ f := by
  intro a
  exact Spec.map_preimage (X.fromSpecResidueField x ≫ f)

/-- The residue-field point gives an actual section of the base-changed scheme. -/
noncomputable def pointResidueSection (x : X) :
    let _ : Algebra K (X.residueField x) := pointResidueAlgebra f x
    SchemeHomOver (𝟙 (Spec (CommRingCat.of (X.residueField x))))
      (baseChange K f (X.residueField x)) := by
  intro a
  exact ⟨pullback.lift (X.fromSpecResidueField x) (𝟙 _)
    (by rw [Category.id_comp, pointResidueAlgebra_specMap f x]), pullback.lift_snd _ _ _⟩

theorem pointResidueAlgebra_finite [LocallyOfFiniteType f] (x : X)
    (hx : IsClosed ({x} : Set X)) :
    let _ : Algebra K (X.residueField x) := pointResidueAlgebra f x
    Module.Finite K (X.residueField x) := by
  intro a
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  have : LocallyOfFiniteType (X.fromSpecResidueField x) :=
    isClosed_singleton_iff_locallyOfFiniteType.1 hx
  have hφ : LocallyOfFiniteType (Spec.map (Spec.preimage (X.fromSpecResidueField x ≫ f))) := by
    rw [Spec.map_preimage]
    infer_instance
  have hft : RingHom.FiniteType (Spec.preimage (X.fromSpecResidueField x ≫ f)).hom :=
    HasRingHomProperty.Spec_iff.mp hφ
  have : Algebra.FiniteType K (X.residueField x) := hft
  exact finite_of_finite_type_of_isJacobsonRing K (X.residueField x)

/-- A nonempty scheme locally of finite type over a field has a closed point with
finite residue extension, with the algebra structure fixed by its actual point map. -/
theorem exists_finite_pointResidueAlgebra [LocallyOfFiniteType f] [Nonempty X] :
    ∃ x : X, IsClosed ({x} : Set X) ∧
      let _ : Algebra K (X.residueField x) := pointResidueAlgebra f x
      Module.Finite K (X.residueField x) := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  obtain ⟨x, -, hx⟩ := nonempty_inter_closedPoints
    (Set.univ_nonempty : (Set.univ : Set X).Nonempty) isClosed_univ.isLocallyClosed
  exact ⟨x, hx, pointResidueAlgebra_finite f x hx⟩

end AlgebraicGeometry.Scheme
