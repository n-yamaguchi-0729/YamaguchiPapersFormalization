/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.TensorProduct.Maps
import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic
import Nyll.SchemeTheory.FiniteEtale.AffineEquivalence
import Nyll.SchemeTheory.FiniteEtale.Algebra.FiniteFieldModel

/-!
# Affine finite-field models of finite étale schemes

An actual finite étale cover of `Spec (R ⊗[k] L)` for an algebraic extension
`L/k` is the pullback of an actual finite étale cover over a finite constant
extension. The pullback uses the literal tensor map of the field inclusion.
-/

noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.FiniteEtale

variable (k L R : Type u) [Field k] [Field L] [CommRing R]
variable [Algebra k L] [Algebra k R]

/-- An actual finite étale cover of an affine constant extension descends
along the literal coefficient inclusion to an actual finite intermediate field. -/
theorem exists_finiteIntermediateField_affine_model
    [Algebra.IsAlgebraic k L]
    (X : AlgebraicGeometry.FiniteEtale (Spec (CommRingCat.of (R ⊗[k] L)))) :
    ∃ F : IntermediateField k L, FiniteDimensional k F ∧
      ∃ X₀ : AlgebraicGeometry.FiniteEtale (Spec (CommRingCat.of (R ⊗[k] F))),
        Nonempty ((AlgebraicGeometry.FiniteEtale.pullback
          (Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.map (R := k) (S := R) (AlgHom.id R R) F.val).toRingHom))).obj
              X₀ ≅ X) := by
  let eL := AlgebraicGeometry.FiniteEtale.affineEquivalence (CommRingCat.of (R ⊗[k] L))
  let A : CommAlgCat.FiniteEtale (R ⊗[k] L) := eL.functor.obj (Opposite.op X)
  obtain ⟨F, hF, A₀, ⟨eA⟩⟩ := Algebra.FiniteEtale.exists_finiteIntermediateField_model k L R A
  let : Algebra (R ⊗[k] F) (R ⊗[k] L) :=
    (Algebra.TensorProduct.map (R := k) (S := R) (AlgHom.id R R) F.val).toRingHom.toAlgebra
  let eF := AlgebraicGeometry.FiniteEtale.affineEquivalence (CommRingCat.of (R ⊗[k] F))
  let X₀ : AlgebraicGeometry.FiniteEtale (Spec (CommRingCat.of (R ⊗[k] F))) :=
    (eF.inverse.obj A₀).unop
  let b : CommAlgCat.FiniteEtale (R ⊗[k] F) ⥤ CommAlgCat.FiniteEtale (R ⊗[k] L) :=
    CommAlgCat.FiniteEtale.baseChange (R ⊗[k] F) (R ⊗[k] L)
  let p := AlgebraicGeometry.FiniteEtale.pullback
    (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.map (R := k) (S := R) (AlgHom.id R R) F.val).toRingHom))
  let ea : A ≅ b.obj A₀ :=
    ObjectProperty.isoMk _ (CommAlgCat.isoMk (by with_unfolding_all exact eA))
  let en : b.obj (eF.functor.obj (Opposite.op X₀)) ≅
      eL.functor.obj (Opposite.op (p.obj X₀)) :=
    (AlgebraicGeometry.FiniteEtale.affineEquivalenceCompBaseChangeIso
      (R ⊗[k] F) (R ⊗[k] L)).app (Opposite.op X₀)
  let eb : eL.functor.obj (Opposite.op (p.obj X₀)) ≅ eL.functor.obj (Opposite.op X) :=
    en.symm ≪≫ b.mapIso (eF.counitIso.app A₀) ≪≫ ea.symm
  let es : Opposite.op (p.obj X₀) ≅ Opposite.op X := eL.functor.preimageIso eb
  exact ⟨F, hF, X₀, ⟨es.unop.symm⟩⟩

end AlgebraicGeometry.FiniteEtale
end
