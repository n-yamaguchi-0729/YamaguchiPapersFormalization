/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Ring.Action.Basic
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# Ideal inertia and affine geometric-point stabilizers

Let a group `G` act on a commutative ring `B`. A geometric point
`Spec Ω ⟶ Spec B` represented by `φ : B →+* Ω` is fixed by an element of
`G` exactly when that element acts trivially modulo `ker φ`. Thus the
scheme-theoretic geometric-point stabilizer is ideal inertia, rather than
the decomposition group that merely preserves the underlying prime.

For the geometric point obtained by embedding the residue field of a prime
`P` into its algebraic closure, the kernel is `P`, so the comparison gives
the usual ideal-inertia subgroup without any additional compatibility input.
The statements apply in particular to the affine charts of a normalization.

This is the affine geometric-point/ideal-inertia part of the divisorial
comparison. It does not identify either group with the image of the
fundamental group of the fraction field of a strict henselization; that
identification additionally requires the construction and local properties
of the strict henselization.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace EtaleFundamentalGroups.Inertia

universe u v

/-- An element fixes an affine geometric point precisely when its action on
the coordinate ring is trivial modulo the point's prime kernel. -/
theorem mem_idealInertia_iff_fixes_affineGeometricPoint
    (G : Type v) [Group G]
    {B Ω : Type u} [CommRing B] [Field Ω] [MulSemiringAction G B]
    (φ : B →+* Ω) (σ : G) :
    σ ∈ (RingHom.ker φ).inertia G ↔
      Spec.map (CommRingCat.ofHom φ) ≫
          Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom G B σ)) =
        Spec.map (CommRingCat.ofHom φ) := by
  rw [← Spec.map_comp, Spec.map_inj]
  constructor
  · intro hσ
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro b
    exact (RingHom.sub_mem_ker_iff φ).mp (Ideal.mem_inertia.mp hσ b)
  · intro hσ
    apply Ideal.mem_inertia.mpr
    intro b
    apply (RingHom.sub_mem_ker_iff φ).mpr
    exact RingHom.congr_fun (congrArg CommRingCat.Hom.hom hσ) b

/-- The geometric point obtained from the algebraic closure of the residue
field at `P` has stabilizer exactly the ideal-inertia subgroup at `P`.
Fixing the geometric point includes acting trivially on its residue field. -/
theorem mem_idealInertia_iff_fixes_residueGeometricPoint
    (G : Type v) [Group G]
    {B : Type u} [CommRing B] [MulSemiringAction G B]
    (P : Ideal B) [P.IsPrime] (σ : G) :
    σ ∈ P.inertia G ↔
      Spec.map (CommRingCat.ofHom
        ((algebraMap P.ResidueField (AlgebraicClosure P.ResidueField)).comp
          (algebraMap B P.ResidueField))) ≫
          Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom G B σ)) =
        Spec.map (CommRingCat.ofHom
          ((algebraMap P.ResidueField (AlgebraicClosure P.ResidueField)).comp
            (algebraMap B P.ResidueField))) := by
  have hker :
      RingHom.ker
          ((algebraMap P.ResidueField (AlgebraicClosure P.ResidueField)).comp
            (algebraMap B P.ResidueField)) = P := by
    rw [RingHom.ker_comp_of_injective (algebraMap B P.ResidueField)
      (algebraMap P.ResidueField (AlgebraicClosure P.ResidueField)).injective,
      Ideal.ker_algebraMap_residueField]
  simpa only [hker] using
    (mem_idealInertia_iff_fixes_affineGeometricPoint G
      ((algebraMap P.ResidueField (AlgebraicClosure P.ResidueField)).comp
        (algebraMap B P.ResidueField)) σ)

end EtaleFundamentalGroups.Inertia
