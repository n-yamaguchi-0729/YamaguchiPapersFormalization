/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.StrictHenselian.GeometricStalkAlgebraColimit
import EtaleFundamentalGroups.StrictHenselian.GeometricStalkFlat
import EtaleFundamentalGroups.GenericTensor.FilteredColimit.AlgEquivDescent

/-!
# Descending an actual geometric-stalk tensor equivalence

An equivalence between finitely presented algebras after scalar extension to
the actual geometric stalk descends to an actual affine pointed étale
neighborhood. Both inverse equations descend through the small filtered
algebra presentation. An affine refinement is then obtained geometrically,
and the descended equivalence is extended to its ring of sections.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

namespace EtaleFundamentalGroups.StrictHenselian

universe u

/-- An actual geometric-stalk equivalence of two finitely presented algebras
already exists on an actual affine pointed étale neighborhood. -/
theorem geometricStalk_exists_affine_tensorProduct_algEquiv
    {R Ω B D : Type u} [CommRing R] [Field Ω] [IsSepClosed Ω]
    [CommRing B] [CommRing D] [Algebra R B] [Algebra R D]
    [Algebra.FinitePresentation R B] [Algebra.FinitePresentation R D]
    (φ : R →+* Ω) :
    letI : Algebra R (geometricStalk (Spec.map (CommRingCat.ofHom φ))) :=
      (geometricStalkStructureMap φ).toAlgebra
    Nonempty ((geometricStalk (Spec.map (CommRingCat.ofHom φ)) ⊗[R] B) ≃ₐ[
      geometricStalk (Spec.map (CommRingCat.ofHom φ))]
        (geometricStalk (Spec.map (CommRingCat.ofHom φ)) ⊗[R] D)) →
    ∃ (V : (Spec (CommRingCat.of R)).Etale)
      (_ : (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.obj V),
      IsAffine V.left ∧
      letI : Algebra R Γ(V.left, ⊤) :=
        (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ V.hom.appTop).hom).toAlgebra
      Nonempty ((Γ(V.left, ⊤) ⊗[R] B) ≃ₐ[Γ(V.left, ⊤)] (Γ(V.left, ⊤) ⊗[R] D)) := by
  let : Algebra R (geometricStalk (Spec.map (CommRingCat.ofHom φ))) :=
    (geometricStalkStructureMap φ).toAlgebra
  rintro ⟨e⟩
  obtain ⟨k, ek, _, _⟩ := exists_tensorProduct_algEquiv_stage_of_filteredColimit
    (geometricStalkSmallAlgebraDiagram φ) (geometricStalkSmallAlgebraCocone φ)
      (geometricStalkSmallAlgebraCoconeIsColimit φ) e
  let j := (FinallySmall.fromFilteredFinalModel
    (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.Elementsᵒᵖ).obj k
  let W : (Spec (CommRingCat.of R)).Etale := j.unop.obj
  let t : (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.obj W := j.unop.val
  let : Algebra R Γ(W.left, ⊤) :=
    (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ W.hom.appTop).hom).toAlgebra
  let eW : (Γ(W.left, ⊤) ⊗[R] B) ≃ₐ[Γ(W.left, ⊤)] (Γ(W.left, ⊤) ⊗[R] D) := ek
  obtain ⟨V, v, f, hV, _⟩ := geometricStalk_exists_affine_refinement
    (Spec.map (CommRingCat.ofHom φ)) W t
  refine ⟨V, v, hV, ?_⟩
  let : Algebra R Γ(V.left, ⊤) :=
    (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ V.hom.appTop).hom).toAlgebra
  let : Algebra Γ(W.left, ⊤) Γ(V.left, ⊤) := f.left.appTop.hom.toAlgebra
  have hbase : f.left.appTop.hom.comp
      (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ W.hom.appTop).hom) =
    (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ V.hom.appTop).hom) := by
    change ((((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ W.hom.appTop) ≫
      f.left.appTop).hom) = _
    apply congrArg CommRingCat.Hom.hom
    rw [Category.assoc, ← Scheme.Hom.comp_appTop]
    have hf : f.left ≫ (show W.left ⟶ Spec (CommRingCat.of R) from W.hom) =
        (show V.left ⟶ Spec (CommRingCat.of R) from V.hom) := f.w
    exact congrArg (fun g => (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ g.appTop) hf
  let : IsScalarTower R Γ(W.left, ⊤) Γ(V.left, ⊤) :=
    IsScalarTower.of_algebraMap_eq fun r => (RingHom.congr_fun hbase r).symm
  exact ⟨(Algebra.TensorProduct.cancelBaseChange R Γ(W.left, ⊤) Γ(V.left, ⊤)
      Γ(V.left, ⊤) B).symm |>.trans
    ((Algebra.TensorProduct.congr
      (AlgEquiv.refl : Γ(V.left, ⊤) ≃ₐ[Γ(V.left, ⊤)] Γ(V.left, ⊤)) eW).trans
      (Algebra.TensorProduct.cancelBaseChange R Γ(W.left, ⊤) Γ(V.left, ⊤) Γ(V.left, ⊤) D))⟩

end EtaleFundamentalGroups.StrictHenselian
