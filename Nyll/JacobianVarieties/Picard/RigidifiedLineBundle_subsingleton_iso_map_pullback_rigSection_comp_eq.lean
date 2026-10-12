/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Anthropic FLT source material is identified by code comparison;
the exact source-file correspondence remains unresolved.
Upstream repository: https://github.com/anthropics/fermats-last-theorem
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
import Nyll.AlgebraicCurves.Geometry.Picard.RigidifiedLineBundle_iso_eq_of_map_pullback_rigSection_comp_eq
import Mathlib.Util.WithWeakNamespace

/-!
Show that the type of line bundle isomorphisms respecting fixed rigidifications is a
subsingleton.
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs
namespace RigidifiedLineBundle_subsingleton_iso_map_pullback_rigSection_comp_eq

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
    NeronModelInfra

with_weak_namespace _root_.AlgebraicGeometry.RelPicard.RigidifiedLineBundle
theorem subsingleton_iso_map_pullback_rigSection_comp_eq
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (hH0 : ∀ (A : Type u) [CommRing A] [Algebra R A],
      let _ : Algebra A Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), ⊤) :=
        Scheme.TwoAffineOpenCover.algebraOfHom
          (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ⊤
      Function.Bijective (algebraMap A Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R
        A), ⊤)))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M M' : RigidifiedLineBundle c ε t)
    (α : (Scheme.Modules.pullback (rigSection c t ε)).obj M.L ≅ SheafOfModules.unit T.ringCatSheaf)
    (α' : (Scheme.Modules.pullback (rigSection c t ε)).obj M'.L ≅ SheafOfModules.unit
      T.ringCatSheaf) :
    Subsingleton {φ : M.L ≅ M'.L // (Scheme.Modules.pullback (rigSection c t ε)).mapIso φ ≪≫ α'
      = α} :=
  ⟨fun a b => Subtype.ext
    (AlgebraicGeometry.RelPicard.RigidifiedLineBundle.iso_eq_of_map_pullback_rigSection_comp_eq
      R c ε hH0 t M M' α α' a.1 b.1 a.2 b.2)⟩
end RigidifiedLineBundle_subsingleton_iso_map_pullback_rigSection_comp_eq
end JacobianVarieties.Picard.Proofs
end ProofImplementation
