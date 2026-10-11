/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_RigKerDualNumber.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.AbelianSchemePropertyBundle
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.AlgebraicCurves.Geometry.Picard.SubPicCondition
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroCut
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroGroupCut
import Nyll.AlgebraicCurves.Geometry.Picard.RelSubPic.Group
import Nyll.SchemeTheory.Cohomology.Cech.TwoAffineOpenCover

/-!
# Rig Ker Dual Number
-/

universe u

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
  AlgebraicGeometry.RelPicard NeronModelInfra
  GoodReductionJacobian

namespace AlgebraicGeometry.RelPicard

section Thickening

variable (R : Type u) [CommRing R] (A : Type u) [CommRing A] [Algebra R A]

/-- The Spec morphism induced by projection from dual numbers to the base algebra. -/
abbrev dualNumberReduction : Spec (.of A) ⟶ Spec (.of (DualNumber A)) :=
  Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R A A).toRingHom)

theorem dualNumberReduction_comp_specMap :
    dualNumberReduction R A ≫ Scheme.TwoAffineOpenCover.specMap R (DualNumber A)
      = Scheme.TwoAffineOpenCover.specMap R A := by
  change Spec.map _ ≫ Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber A))) =
    Spec.map (CommRingCat.ofHom (algebraMap R A))
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  try exact (TrivSqZeroExt.fstHom R A A).comp_algebraMap

/-- The reduction morphism of dual numbers viewed over the original base scheme. -/
abbrev dualNumberReductionOver :
    SchemeHomOver (Scheme.TwoAffineOpenCover.specMap R A) (Scheme.TwoAffineOpenCover.specMap R
      (DualNumber A)) :=
  ⟨dualNumberReduction R A, dualNumberReduction_comp_specMap R A⟩

theorem dualNumberReduction_catches_geometric_points
    (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (.of k) ⟶ Spec (.of (DualNumber A))) :
    ∃ s₀ : Spec (.of k) ⟶ Spec (.of A), s₀ ≫ dualNumberReduction R A = s := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective s
  have hε : φ.hom DualNumber.eps = 0 := by
    have h2 : φ.hom DualNumber.eps * φ.hom DualNumber.eps = 0 := by
      rw [← map_mul, DualNumber.eps_mul_eps, map_zero]
    exact mul_self_eq_zero.mp h2
  let φ₀ : A →+* k := φ.hom.comp (algebraMap A (DualNumber A))
  refine ⟨Spec.map (CommRingCat.ofHom φ₀), ?_⟩
  change Spec.map _ ≫ Spec.map _ = Spec.map φ
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  rw [CommRingCat.hom_comp, CommRingCat.hom_ofHom, CommRingCat.hom_ofHom]
  refine DualNumber.ringHom_ext ?_ ?_
  · ext a
    simp only [φ₀, RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      TrivSqZeroExt.fstHom_apply, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_inl]
  · simp only [φ₀, RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      TrivSqZeroExt.fstHom_apply, DualNumber.fst_eps, map_zero, hε]

end Thickening

section Kernel

variable {R : Type u} [CommRing R] {C : Scheme.{u}}
variable (c : C ⟶ Spec (.of R)) (ε : SchemeHomOver (𝟙 (Spec (.of R))) c)
variable (A : Type u) [CommRing A] [Algebra R A]

/-- Rigidified dual number line bundles whose underlying line bundle becomes trivial after
reduction. -/
def RigKerDualNumber.Carrier : Type (u + 1) :=
  { M : RigidifiedLineBundle c ε (Scheme.TwoAffineOpenCover.specMap R (DualNumber A)) //
      Nonempty ((M.pullbackAlong (dualNumberReductionOver R A)).L ≅
        (RigidifiedLineBundle.unit (c := c) (ε := ε) (Scheme.TwoAffineOpenCover.specMap R A)).L) }

instance RigKerDualNumber.setoid : Setoid (RigKerDualNumber.Carrier c ε A) :=
  (RigidifiedLineBundle.setoid (c := c) (ε := ε) (Scheme.TwoAffineOpenCover.specMap R (DualNumber
    A))).comap
    Subtype.val

/-- Classes of rigidified dual number line bundles with trivial underlying reduction. -/
def RigKerDualNumber : Type (u + 1) := Quotient (RigKerDualNumber.setoid c ε A)

theorem RigKerDualNumber.tensor_mem (M N : RigKerDualNumber.Carrier c ε A) :
    Nonempty (((M.1.tensor N.1).pullbackAlong (dualNumberReductionOver R A)).L ≅
      (RigidifiedLineBundle.unit (c := c) (ε := ε) (Scheme.TwoAffineOpenCover.specMap R A)).L) :=
  ⟨(RigidifiedLineBundle.nonempty_tensor_pullbackAlong_iso (dualNumberReductionOver R A) M.1
    N.1).some ≪≫
    (M.2.some ⊗ᵢ N.2.some) ≪≫ λ_ _⟩

theorem RigKerDualNumber.unit_mem :
    Nonempty (((RigidifiedLineBundle.unit (c := c) (ε := ε)
        (Scheme.TwoAffineOpenCover.specMap R (DualNumber A))).pullbackAlong
          (dualNumberReductionOver R A)).L ≅
      (RigidifiedLineBundle.unit (c := c) (ε := ε) (Scheme.TwoAffineOpenCover.specMap R A)).L) :=
  ⟨Scheme.Modules.pullbackUnitIso _⟩

/-- Multiplication of dual number kernel classes induced by tensor product of rigidified line
bundles. -/
def RigKerDualNumber.mul : RigKerDualNumber c ε A → RigKerDualNumber c ε A → RigKerDualNumber c ε A
  :=
  Quotient.map₂ (fun M N => ⟨M.1.tensor N.1, RigKerDualNumber.tensor_mem c ε A M N⟩)
    (fun _ _ hM _ _ hN => RigidifiedLineBundle.tensor_congr hM hN)

/-- The dual number kernel class of the unit rigidified line bundle. -/
def RigKerDualNumber.one : RigKerDualNumber c ε A :=
  Quotient.mk _ ⟨RigidifiedLineBundle.unit (Scheme.TwoAffineOpenCover.specMap R (DualNumber A)),
    RigKerDualNumber.unit_mem c ε A⟩

end Kernel

end AlgebraicGeometry.RelPicard

end
