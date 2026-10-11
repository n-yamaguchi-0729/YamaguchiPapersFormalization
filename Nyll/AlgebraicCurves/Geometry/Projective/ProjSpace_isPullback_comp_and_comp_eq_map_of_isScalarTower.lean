/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_ProjSpace_isPullback_comp_and_comp_eq_map_of_isScalarTower.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Nyll.SchemeTheory.ProjectiveSpace.Cover
import Nyll.AlgebraicCurves.Geometry.Projective.ProjTwistDatum
import Nyll.AlgebraicCurves.Hilbert.Functor.Basic

/-!
# Proj Space is Pullback comp and comp eq map of is Scalar Tower
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Projective.Proofs
namespace ProjSpace_isPullback_comp_and_comp_eq_map_of_isScalarTower

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

namespace P2mK4G

theorem projMap_congr {A C : Type u} [CommRing A] [CommRing C] {n : ℕ}
    (φ ψ : MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A →+*ᵍ MvPolynomial.homogeneousSubmodule
      (Fin (n + 1)) C)
    (hφ : HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) C) ≤
      (HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)).map φ)
    (hψ : HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) C) ≤
      (HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)).map ψ) (h :
        φ = ψ) :
    Proj.map φ hφ = Proj.map ψ hψ := by
  subst h; rfl

theorem mvMapGraded_comp (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] (n : ℕ) :
    (ProjSpace.mvMapGraded B C n).comp (ProjSpace.mvMapGraded A B n) = ProjSpace.mvMapGraded A C n
      := by
  ext p : 1
  change MvPolynomial.map (algebraMap B C) (MvPolynomial.map (algebraMap A B) p) = MvPolynomial.map
    (algebraMap A C) p
  rw [MvPolynomial.map_map, ← IsScalarTower.algebraMap_eq]

theorem map_comp_map (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] (n : ℕ) :
    ProjSpace.map B C n ≫ ProjSpace.map A B n = ProjSpace.map A C n := by
  rw [ProjSpace.map_eq, ProjSpace.map_eq, ProjSpace.map_eq, ← Proj.map_comp]
  exact projMap_congr _ _ _ _ (mvMapGraded_comp A B C n)

theorem specMap_comp (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] :
    Spec.map (CommRingCat.ofHom (algebraMap B C)) ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)) =
      Spec.map (CommRingCat.ofHom (algebraMap A C)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

end P2mK4G

theorem _root_.AlgebraicGeometry.ProjSpace.isPullback_comp_and_comp_eq_map_of_isScalarTower
    {A : Type u} [CommRing A] (B C : Type u) [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] {n : ℕ}
    {Z ZB ZC : Scheme.{u}}
    (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)) (ιB : ZB ⟶ Proj
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) B)) (ιC : ZC ⟶ Proj
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) C))
    (e : ZB ⟶ Z) (f : ZC ⟶ ZB)
    (hpb : IsPullback e (ιB ≫ ProjSpace.π B n) (ι ≫ ProjSpace.π A n) (Spec.map (CommRingCat.ofHom
      (algebraMap A B))))
    (hcomp : e ≫ ι = ιB ≫ ProjSpace.map A B n)
    (hpb' : IsPullback f (ιC ≫ ProjSpace.π C n) (ιB ≫ ProjSpace.π B n) (Spec.map (CommRingCat.ofHom
      (algebraMap B C))))
    (hcomp' : f ≫ ιB = ιC ≫ ProjSpace.map B C n) :
    IsPullback (f ≫ e) (ιC ≫ ProjSpace.π C n) (ι ≫ ProjSpace.π A n) (Spec.map (CommRingCat.ofHom
      (algebraMap A C))) ∧
    (f ≫ e) ≫ ι = ιC ≫ ProjSpace.map A C n := by
  refine ⟨?_, ?_⟩
  · have h := hpb'.paste_horiz hpb
    rwa [P2mK4G.specMap_comp A B C] at h
  · rw [Category.assoc, hcomp, ← Category.assoc, hcomp', Category.assoc, P2mK4G.map_comp_map A B C
      n]
end ProjSpace_isPullback_comp_and_comp_eq_map_of_isScalarTower
end AlgebraicCurves.Geometry.Projective.Proofs
end ProofImplementation
