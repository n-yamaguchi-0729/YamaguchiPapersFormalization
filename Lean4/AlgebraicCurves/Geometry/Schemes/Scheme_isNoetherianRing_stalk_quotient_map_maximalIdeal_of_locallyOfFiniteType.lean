/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_isNoetherianRing_stalk_quotient_map_maximalIdeal_of_locallyOfFiniteType.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.RingTheory.EssentialFiniteness
import Mathlib.RingTheory.Localization.Submodule

/-!
# Scheme is Noetherian Ring stalk quotient map maximal Ideal of locally Of Finite Type
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace Scheme_isNoetherianRing_stalk_quotient_map_maximalIdeal_of_locallyOfFiniteType

open AlgebraicGeometry CategoryTheory IsLocalRing

namespace FibreNoethAux

theorem isNoetherianRing_of_essFiniteType (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.EssFiniteType R S] [IsNoetherianRing R] : IsNoetherianRing S := by
  have h : IsNoetherianRing (Algebra.EssFiniteType.subalgebra R S) :=
    Algebra.FiniteType.isNoetherianRing R _
  exact IsLocalization.isNoetherianRing (Algebra.EssFiniteType.submonoid R S) S h

theorem essFiniteType_toStalk (A : Type) [CommRing A] (p : PrimeSpectrum A) :
    (StructureSheaf.toStalk A p).hom.EssFiniteType := by
  change (algebraMap A ((Spec.structureSheaf A).presheaf.stalk p)).EssFiniteType
  rw [RingHom.essFiniteType_algebraMap]
  exact Algebra.EssFiniteType.of_isLocalization _ p.asIdeal.primeCompl

theorem const_eq_comp (A : Type) [CommRing A]
    (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of A)) (x : X) :
    (X.presheaf.germ ⊤ x trivial).hom.comp (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of
      A)).inv.hom) =
      (f.stalkMap x).hom.comp (StructureSheaf.toStalk A (f.base x)).hom := by
  have h1 : (Spec (CommRingCat.of A)).presheaf.germ ⊤ (f.base x) trivial ≫ f.stalkMap x =
      f.appTop ≫ X.presheaf.germ ⊤ x trivial :=
    Scheme.Hom.germ_stalkMap f ⊤ x trivial
  have h2 : (X.presheaf.germ ⊤ x trivial).hom.comp (f.appTop.hom.comp (Scheme.ΓSpecIso
    (CommRingCat.of A)).inv.hom) =
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop ≫ X.presheaf.germ ⊤ x trivial).hom := by
    simp only [CommRingCat.hom_comp, RingHom.comp_assoc]
  rw [h2, ← h1]
  rfl

theorem essFiniteType_const (A : Type) [CommRing A]
    (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of A)) [LocallyOfFiniteType f] (x : X) :
    ((X.presheaf.germ ⊤ x trivial).hom.comp
      (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).EssFiniteType := by
  rw [const_eq_comp]
  exact RingHom.EssFiniteType.comp (essFiniteType_toStalk A (f.base x))
    (LocallyOfFiniteType.stalkMap f x)

end FibreNoethAux

end Scheme_isNoetherianRing_stalk_quotient_map_maximalIdeal_of_locallyOfFiniteType
end AlgebraicCurves.Geometry.Schemes.Proofs

namespace AlgebraicGeometry.Scheme



open _root_.AlgebraicCurves.Geometry.Schemes.Proofs in
open Scheme_isNoetherianRing_stalk_quotient_map_maximalIdeal_of_locallyOfFiniteType in
open AlgebraicGeometry CategoryTheory IsLocalRing in
theorem isNoetherianRing_stalk_quotient_map_maximalIdeal_of_locallyOfFiniteType
    (A : Type) [CommRing A] [IsLocalRing A]
    (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of A)) [LocallyOfFiniteType f]
    (x : X) (_hx : f.base x = closedPoint A) :
    IsNoetherianRing
      ((X.presheaf.stalk x) ⧸ Ideal.map
        ((X.presheaf.germ ⊤ x trivial).hom.comp (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of
          A)).inv.hom))
        (maximalIdeal A)) := by
  have hc := FibreNoethAux.essFiniteType_const A X f x
  let alg : Algebra A (X.presheaf.stalk x) :=
    ((X.presheaf.germ ⊤ x trivial).hom.comp
      (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).toAlgebra
  have hE : Algebra.EssFiniteType A (X.presheaf.stalk x) := hc
  have hq := Algebra.EssFiniteType.quotient_map (R := A) (S := X.presheaf.stalk x) (maximalIdeal A)
  let fld : Field (A ⧸ maximalIdeal A) := Ideal.Quotient.field (maximalIdeal A)
  have : IsNoetherianRing (A ⧸ maximalIdeal A) := inferInstance
  have hN := @FibreNoethAux.isNoetherianRing_of_essFiniteType (A ⧸ maximalIdeal A)
    ((X.presheaf.stalk x) ⧸ (maximalIdeal A).map (algebraMap A (X.presheaf.stalk x))) _ _ _ hq
      inferInstance
  exact hN
end AlgebraicGeometry.Scheme
end ProofImplementation
