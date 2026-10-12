/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_unit_pullback_rigSection_of_squareZero_of_pullback_iso.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroCut
import Nyll.SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
import Nyll.AlgebraicCurves.Cohomology.Cech.TwoChartCechSectionsOf
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_nonempty_iso_unit_of_pullback_squareZero
import Mathlib.Util.WithWeakNamespace

/-!
# Relative Picard varieties and fibre cohomology

Construct a unit isomorphism of rigidified line bundles over a square-zero thickening from the
given pullback isomorphism.
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs
namespace RigidifiedLineBundle_nonempty_iso_unit_pullback_rigSection_of_squareZero_of_pullback_iso
attribute [-simp] AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
  NeronModelInfra TensorProduct

open RigidifiedLineBundle_nonempty_iso_unit_pullback_rigSection_of_squareZero_of_pullback_iso in
with_weak_namespace _root_.AlgebraicGeometry.RelPicard.RigidifiedLineBundle
theorem nonempty_iso_unit_pullback_rigSection_of_squareZero_of_pullback_iso
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    {B : Type u} [CommRing B] [Algebra R B] (I : Ideal B) (hI : I ^ 2 = ⊥)
    (ι : SchemeHomOver
      (Spec.map (CommRingCat.ofHom (algebraMap R (B ⧸ I))))
      (Spec.map (CommRingCat.ofHom (algebraMap R B))))
    (hι : ι.1 = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
    (M : RigidifiedLineBundle c ε (Spec.map (CommRingCat.ofHom (algebraMap R (B ⧸ I)))))
    (L' : (pullback c (Spec.map (CommRingCat.ofHom (algebraMap R B)))).Modules)
    (hL' : Scheme.Modules.IsInvertible L')
    (isoL : Nonempty ((Scheme.Modules.pullback (baseChangeSnd c ι)).obj L' ≅ M.L)) :
    Nonempty
      ((Scheme.Modules.pullback (rigSection c (Spec.map (CommRingCat.ofHom
        (algebraMap R B))) ε)).obj L'
        ≅ SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf) := by
  have hεL'inv : Scheme.Modules.IsInvertible
      ((Scheme.Modules.pullback
        (rigSection c (Spec.map (CommRingCat.ofHom (algebraMap R B))) ε)).obj L') :=
    hL'.pullback _
  have step1 :
      (Scheme.Modules.pullback ι.1).obj
        ((Scheme.Modules.pullback
          (rigSection c (Spec.map (CommRingCat.ofHom (algebraMap R B))) ε)).obj L')
        ≅ SheafOfModules.unit (Spec (CommRingCat.of (B ⧸ I))).ringCatSheaf :=
    (Scheme.Modules.pullbackComp _ _).app L' ≪≫
      (Scheme.Modules.pullbackCongr (rigSection_baseChangeSnd c ε ι).symm).app L' ≪≫
      ((Scheme.Modules.pullbackComp _ _).app L').symm ≪≫
      (Scheme.Modules.pullback _).mapIso isoL.some ≪≫
      M.rigidified.some
  have htriv : Nonempty ((Scheme.Modules.pullback
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).obj
        ((Scheme.Modules.pullback
          (rigSection c (Spec.map (CommRingCat.ofHom (algebraMap R B))) ε)).obj L')
        ≅ SheafOfModules.unit (Spec (CommRingCat.of (B ⧸ I))).ringCatSheaf) := by
    rw [← hι]; exact ⟨step1⟩
  exact Scheme.Modules.IsInvertible.nonempty_iso_unit_of_pullback_squareZero I hI _ hεL'inv htriv
end RigidifiedLineBundle_nonempty_iso_unit_pullback_rigSection_of_squareZero_of_pullback_iso
end JacobianVarieties.Picard.Proofs
end ProofImplementation
