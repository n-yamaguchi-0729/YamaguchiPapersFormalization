/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.FiniteEtale.Local.OfTargetLocalizations
import Nyll.SchemeTheory.LocalGeometry.EtaleStalkPrimeLocalization
import Mathlib.AlgebraicGeometry.Noetherian
import Nyll.SchemeTheory.FiniteEtale.Basic

/-!
# Finite etaleness from the punctured locus and boundary stalks

For a morphism of finite presentation, formal etaleness of every stalk is
enough to recover etaleness.  Combining this with the finite-presentation
consequence of finiteness over a locally Noetherian target gives a boundary
criterion: a finite morphism which is etale on an open set is finite etale as
soon as its stalk maps at the complementary points are formally etale.

The local input is deliberately only formal etaleness.  In applications to a
normalization, this is the part supplied by punctured purity after identifying
the localized normalization with the canonical local extension.
-/

noncomputable section

open CategoryTheory

namespace EtaleFundamentalGroups

universe u

open AlgebraicGeometry

/-- A bijective ring map is formally etale. -/
lemma RingHom.FormallyEtale.of_bijective
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Bijective f) : f.FormallyEtale := by
  algebraize [f]
  exact Algebra.FormallyEtale.of_equiv (AlgEquiv.ofBijective (Algebra.ofId R S) hf)

/-- Formal etaleness of ring maps is invariant under isomorphisms of arrows. -/
lemma RingHom.FormallyEtale.respectsIso :
    RingHom.RespectsIso @RingHom.FormallyEtale := by
  have hcomp : RingHom.StableUnderComposition @RingHom.FormallyEtale :=
    by
      intro R S T _ _ _ f g hf hg
      exact RingHom.FormallyEtale.comp hf hg
  exact hcomp.respectsIso
    (fun e ↦ RingHom.FormallyEtale.of_bijective e.toRingHom e.bijective)

/-- A locally finitely presented scheme morphism whose stalk maps are all
formally etale is etale. -/
theorem etale_of_stalkMap_formallyEtale
    {Y X : Scheme.{u}} (f : Y ⟶ X) [LocallyOfFinitePresentation f]
    (hstalk : ∀ y : Y, (f.stalkMap y).hom.FormallyEtale) :
    Etale f := by
  let P := stalkwise @RingHom.FormallyEtale
  let : P.RespectsIso :=
    stalkwise_respectsIso RingHom.FormallyEtale.respectsIso
  let : IsZariskiLocalAtTarget P :=
    stalkwiseIsZariskiLocalAtTarget_of_respectsIso
      RingHom.FormallyEtale.respectsIso
  let : IsZariskiLocalAtSource P :=
    stalkwise_isZariskiLocalAtSource_of_respectsIso
      RingHom.FormallyEtale.respectsIso
  refine ⟨fun {U} hU {V} hV hVU ↦ ?_⟩
  apply ringHom_etale_of_formallyEtale_localizationsAtPrime_all_primeIdeals
    (f.appLE U V hVU).hom (f.finitePresentation_appLE hU hV hVU)
  intro Q hQ
  have hres : P (f.resLE U V hVU) :=
    IsZariskiLocalAtSource.resLE hVU hstalk
  let e : Arrow.mk (f.resLE U V hVU) ≅
    Arrow.mk (Spec.map (CommRingCat.ofHom (f.appLE U V hVU).hom)) :=
    Arrow.isoMk hV.isoSpec hU.isoSpec (by
      change V.toSpecΓ ≫ Spec.map (f.appLE U V hVU) =
        f.resLE U V hVU ≫ U.toSpecΓ
      exact Scheme.Opens.toSpecΓ_SpecMap_appLE f U V hVU)
  have hspec : P (Spec.map (CommRingCat.ofHom (f.appLE U V hVU).hom)) :=
    (P.arrow_mk_iso_iff e).mp hres
  change (Localization.localRingHom
    (Ideal.comap (f.appLE U V hVU).hom Q) Q
    (f.appLE U V hVU).hom rfl).FormallyEtale
  exact (stalkwise_SpecMap_iff RingHom.FormallyEtale.respectsIso
    (CommRingCat.ofHom (f.appLE U V hVU).hom)).mp hspec Q hQ

/-- A finite morphism over a locally Noetherian target is finite etale if all
of its stalk maps are formally etale. -/
theorem isFiniteEtale_of_isFinite_of_stalkMap_formallyEtale
    {Y X : Scheme.{u}} [IsLocallyNoetherian X]
    (f : Y ⟶ X) [IsFinite f]
    (hstalk : ∀ y : Y, (f.stalkMap y).hom.FormallyEtale) :
    IsFiniteEtale f := by
  let : Etale f := etale_of_stalkMap_formallyEtale f hstalk
  exact ⟨⟩

/-- Boundary criterion for finite etaleness.  It is enough to know etaleness
over an open set and formal etaleness of the original stalk maps over its
complement. -/
theorem isFiniteEtale_of_isFinite_of_restrict_etale_of_boundary_stalkMap_formallyEtale
    {Y X : Scheme.{u}} [IsLocallyNoetherian X]
    (f : Y ⟶ X) [IsFinite f] (U : X.Opens)
    (hU : Etale (f ∣_ U))
    (hboundary : ∀ y : Y, f y ∉ U → (f.stalkMap y).hom.FormallyEtale) :
    IsFiniteEtale f := by
  apply isFiniteEtale_of_isFinite_of_stalkMap_formallyEtale f
  intro y
  by_cases hy : f y ∈ U
  · let yU : f ⁻¹ᵁ U := ⟨y, hy⟩
    let : Etale (f ∣_ U) := hU
    have hlocal : ((f ∣_ U).stalkMap yU).hom.FormallyEtale := by
      change @Algebra.FormallyEtale _ _ _ _
        ((f ∣_ U).stalkMap yU).hom.toAlgebra
      exact (f ∣_ U).stalkMap_formallyEtale_of_etale yU
    exact (RingHom.FormallyEtale.respectsIso.arrow_mk_iso_iff
      (morphismRestrictStalkMap f U yU)).mp hlocal
  · exact hboundary y hy

end EtaleFundamentalGroups

end
