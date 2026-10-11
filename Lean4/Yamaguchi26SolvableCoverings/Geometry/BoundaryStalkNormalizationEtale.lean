/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Yamaguchi26SolvableCoverings.Geometry.BoundaryStalkComponentHeightOne
import EtaleFundamentalGroups.Purity.FiniteEtaleAwayNormalization
import EtaleFundamentalGroups.Inertia.NormalizationEtaleOfGaloisComponents
import SchemeTheory.RingTheory.RegularLocalTrace
import SchemeTheory.FiniteEtale.Basic
import SchemeTheory.RingTheory.RegularLocalDomain
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Finite etale normalization at every boundary stalk

Choose an actual local Cartier equation. Every connected Galois component of
the pulled-back cover has etale normalization by purity: height-one etaleness
comes from the original boundary components, and regularity is transferred
through the actual stalk-localization isomorphism. The normalized components
cover the whole normalization. Its integral structure map is therefore
finite etale, and the canonical localization comparison returns the actual
base change of the original relative normalization.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.PreGaloisCategory AlgebraicGeometry.FiniteEtale
open EtaleFundamentalGroups EtaleFundamentalGroups.Inertia

namespace Yamaguchi26SolvableCoverings

private theorem exists_nonzero_stalk_cartier_equation
    {X : Scheme.{0}} (D : X.EffectiveCartierDivisor) (x : X)
    [IsDomain (X.presheaf.stalk x)] :
    ∃ d : X.presheaf.stalk x, d ≠ 0 ∧ D.1.stalkIdeal x = Ideal.span {d} := by
  obtain ⟨U, hx, t, ht, hI⟩ := D.2 x
  let : Algebra Γ(X, U.1) (X.presheaf.stalk x) :=
    (X.presheaf.germ U.1 x hx).hom.toAlgebra
  let := U.2.isLocalization_stalk ⟨x, hx⟩
  let d : X.presheaf.stalk x := (X.presheaf.germ U.1 x hx) t
  have hd : d ∈ nonZeroDivisors (X.presheaf.stalk x) :=
    IsLocalization.nonZeroDivisors_le_comap
      (U.2.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl (X.presheaf.stalk x)
      ht.mem_nonZeroDivisors
  refine ⟨d, mem_nonZeroDivisors_iff_ne_zero.mp hd, ?_⟩
  rw [Scheme.IdealSheafData.stalkIdeal_eq_map_ideal D.1 x U hx, hI,
    Ideal.map_span, Set.image_singleton]

variable {X : Scheme.{0}} [IsLocallyNoetherian X]

/-- At every point of the regular Cartier boundary, the actual relative
normalization of a Galois cover is finite etale if it is etale at
each generic component stalk. -/
theorem normalization_boundaryStalk_finiteEtale_of_componentStalks
    (D : X.EffectiveCartierDivisor) (hreg : D.IsAmbientRegularAlongSupport)
    [ConnectedSpace D.1.supportComplement]
    (W : FiniteEtale D.1.supportComplement) (hW : IsGalois W)
    (hgeneric : ∀ E : Component D,
      Etale (pullback.snd (W.hom ≫ D.1.supportComplement.ι).fromNormalization
        (X.fromSpecStalk (componentPoint D E))))
    (x : X) (hx : x ∈ D.1.support) :
    IsFiniteEtale (pullback.snd (W.hom ≫ D.1.supportComplement.ι).fromNormalization
      (X.fromSpecStalk x)) := by
  let R := X.presheaf.stalk x
  let : IsRegularLocalRing R := hreg x hx
  let : IsDomain R := IsRegularLocalRing.isDomain R
  let : IsIntegrallyClosed R := SchemeTheory.isIntegrallyClosed_of_isRegularLocalRing R
  obtain ⟨d, hd, hD⟩ := exists_nonzero_stalk_cartier_equation D x
  let S := Localization.Away d
  let : IsDomain S := IsLocalization.Away.isDomain S hd
  let c := D.1.stalkAwayToSupportComplement x d hD
  let A := (FiniteEtale.pullback c).obj W
  let a := Spec.map (CommRingCat.ofHom (algebraMap R S))
  let b := X.fromSpecStalk x
  let f : A.left ⟶ Spec (.of R) := (show A.left ⟶ Spec (.of S) from A.hom) ≫ a
  let F : W.left ⟶ X := W.hom ≫ D.1.supportComplement.ι
  have hregular : ∀ p : PrimeSpectrum R, d ∈ p.asIdeal →
      IsRegularLocalRing (Localization.AtPrime p.asIdeal) := by
    intro p hp
    have hDp : D.1.stalkIdeal x ≤ p.asIdeal := by
      rw [hD, Ideal.span_le, Set.singleton_subset_iff]
      exact hp
    have hsupport : X.fromSpecStalk x p ∈ D.1.support :=
      D.1.mem_support_fromSpecStalk_of_stalkIdeal_le x p hDp
    let : IsRegularLocalRing (X.presheaf.stalk (X.fromSpecStalk x p)) :=
      hreg (X.fromSpecStalk x p) hsupport
    exact IsRegularLocalRing.of_ringEquiv (X.stalkFromSpecStalkEquivLocalization x p)
  let xi : Spec (.of (AlgebraicClosure (FractionRing S))) ⟶ Spec (.of S) :=
    Spec.map (CommRingCat.ofHom
      ((algebraMap (FractionRing S) (AlgebraicClosure (FractionRing S))).comp
        (algebraMap S (FractionRing S))))
  have hf : Etale f.fromNormalization := by
    apply etale_normalization_of_galoisComponents c xi W hW f
    intro _w Y i _v _hiv hY hi
    let : IsGalois Y := hY
    let : Mono i := hi
    have hYEt : Etale ((show Y.left ⟶ Spec (.of S) from Y.hom) ≫ a).fromNormalization := by
      apply finiteEtaleAway_normalization_etale_of_regular_boundary d hd Y hregular
      intro p _ hp hdp
      have hDp : D.1.stalkIdeal x ≤ p := by
        rw [hD, Ideal.span_le, Set.singleton_subset_iff]
        exact hdp
      exact normalization_stalkComponent_heightOne_etale_of_componentStalks
        D W hgeneric x d hD Y i p hp hDp
    have hiw : i.left ≫ (show A.left ⟶ Spec (.of S) from A.hom) =
        (show Y.left ⟶ Spec (.of S) from Y.hom) := i.w
    have hiF : i.left ≫ f = (show Y.left ⟶ Spec (.of S) from Y.hom) ≫ a :=
      (Category.assoc _ _ _).symm.trans (congrArg (fun k => k ≫ a) hiw)
    exact Eq.mp (congrArg (fun k : Y.left ⟶ Spec (.of R) => Etale k.fromNormalization)
      hiF.symm) hYEt
  have H : IsPullback (pullback.fst W.hom c) f F b :=
    (IsPullback.of_hasPullback W.hom c).paste_vert
      (D.1.isPullback_stalkAwayToSupportComplement x d hD)
  let e : pullback F b ≅ A.left := (IsPullback.of_hasPullback F b).isoIsPullback _ _ H
  have he : e.hom ≫ f = pullback.snd F b :=
    IsPullback.isoIsPullback_hom_snd W.left (Spec (.of R))
      (IsPullback.of_hasPullback F b) H
  let en := Inertia.normalizationSourceIso (pullback.snd F b) f e he
  have hPB : Etale (pullback.snd F b).fromNormalization := by
    have ht : Etale (en.hom ≫ f.fromNormalization) := inferInstance
    rw [Inertia.normalizationSourceIso_hom_fromNormalization] at ht
    exact ht
  let : IsIso (F.normalizationPullback b) := isIso_normalizationPullback_fromSpecStalk F x
  have heq : pullback.snd F.fromNormalization b =
      inv (F.normalizationPullback b) ≫ (pullback.snd F b).fromNormalization := by
    exact (IsIso.inv_hom_id_assoc (F.normalizationPullback b)
      (pullback.snd F.fromNormalization b)).symm.trans
        (congrArg (fun k => inv (F.normalizationPullback b) ≫ k)
          (Scheme.Hom.normalizationPullback_snd F b))
  have hEt : Etale (pullback.snd F.fromNormalization b) := by
    rw [heq]
    infer_instance
  have hFin : IsFinite (pullback.snd F.fromNormalization b) :=
    (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType _).mpr ⟨inferInstance, inferInstance⟩
  exact ⟨⟩

/-- At every point of the regular Cartier boundary, the actual relative
normalization of a boundary-unramified Galois cover is finite etale. -/
theorem boundaryUnramified_normalization_boundaryStalk_finiteEtale
    (D : X.EffectiveCartierDivisor) (hreg : D.IsAmbientRegularAlongSupport)
    [ConnectedSpace D.1.supportComplement]
    (W : FiniteEtale D.1.supportComplement) (hW : IsGalois W)
    (hU : IsBoundaryUnramified D W) (x : X) (hx : x ∈ D.1.support) :
    IsFiniteEtale (pullback.snd (W.hom ≫ D.1.supportComplement.ι).fromNormalization
      (X.fromSpecStalk x)) := by
  exact normalization_boundaryStalk_finiteEtale_of_componentStalks D hreg W hW
    (boundaryUnramified_normalization_componentStalk_etale D hreg W hW hU) x hx

end Yamaguchi26SolvableCoverings
