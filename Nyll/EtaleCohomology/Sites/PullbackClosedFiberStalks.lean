/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.EtaleCohomology.Sites.ClosedZariskiComparison
import Nyll.EtaleCohomology.Sites.ModuleSetComparison
import Nyll.EtaleCohomology.Sites.PullbackStalks
import Nyll.EtaleCohomology.Sites.ClosedAdjunction
import Nyll.EtaleCohomology.Sites.ZariskiModuleBaseChange
import Nyll.EtaleCohomology.Sites.SheafFunctors
import Nyll.SchemeTheory.Morphisms.ClosedImmersionLift
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.CategoryTheory.Sites.Point.Basic
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Topology.Sheaves.Stalks

/-!
# Stalks of the pulled-back original closed-fiber unit

At a point over the closed point of the original local base, its geometric
point factors through the actual original closed fiber. The existing
inverse-image stalk isomorphism and closed-unit stalk isomorphism therefore
make the pulled-back original unit an isomorphism on that geometric stalk.
Its underlying Zariski stalk map is consequently a monomorphism.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits

namespace EtaleCohomology

/-- Pulling the original closed-fiber unit along an arbitrary scheme map
keeps its Zariski stalk map injective at all points over the closed point. -/
theorem etalePullbackClosedFiberUnit_zariskiStalk_mono
    (R : Type u) [CommRing R] [IsLocalRing R]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (q : Y ⟶ X)
    (Λ : Type u) [CommRing Λ] (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))
    (y : Y) (hy : f (q y) = IsLocalRing.closedPoint R) :
    let r : Spec (CommRingCat.of (IsLocalRing.ResidueField R)) ⟶ Spec (CommRingCat.of R) :=
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
    let i : pullback f r ⟶ X := pullback.fst f r
    let η : F ⟶ (etalePushforward i Λ).obj ((etalePullback i Λ).obj F) :=
      (etalePullbackPushforwardAdjunction i Λ).unit.app F
    Mono ((TopCat.Presheaf.stalkFunctor (Type u) y).map
      ((etaleModuleZariskiRestriction Y Λ).map ((etalePullback q Λ).map η)).hom) := by
  intro r i η
  have : IsClosedImmersion r := IsClosedImmersion.spec_of_surjective
    (CommRingCat.ofHom (IsLocalRing.residue R)) IsLocalRing.residue_surjective
  have : IsClosedImmersion i := inferInstanceAs (IsClosedImmersion (pullback.fst f r))
  let Ω : Type u := SeparableClosure (Y.residueField y)
  let s : Spec (CommRingCat.of Ω) ⟶ Y :=
    Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) Ω)) ≫
      Y.fromSpecResidueField y
  let ξ : Spec (CommRingCat.of Ω) := default
  have hs : s ξ = y := by
    rw [Scheme.Hom.comp_apply]
    exact Scheme.fromSpecResidueField_apply y _
  let x₀ : Spec (CommRingCat.of (IsLocalRing.ResidueField R)) := default
  have hr : r x₀ = IsLocalRing.closedPoint R :=
    IsLocalRing.PrimeSpectrum.comap_residue R x₀
  have hRange : Set.range (s ≫ q) ⊆ Set.range i := by
    rintro x ⟨t, rfl⟩
    have ht : s t = y := (congrArg s (Subsingleton.elim t ξ)).trans hs
    have hbase : f ((s ≫ q) t) = r x₀ :=
      (congrArg f ((Scheme.Hom.comp_apply s q t).trans (congrArg q ht))).trans
        (hy.trans hr.symm)
    obtain ⟨z, hzi, _⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := f) (g := r) ((s ≫ q) t) x₀ hbase
    exact ⟨z, hzi⟩
  obtain ⟨sZ, hsZ⟩ := IsClosedImmersion.exists_lift_of_isReduced_of_range_subset
    i (s ≫ q) hRange
  have hη : IsIso ((Scheme.pointSmallEtale (s ≫ q)).sheafFiber.map η) := by
    rw [← hsZ]
    exact etalePushforwardClosed_unit_stalk_isIso i Λ sZ F
  let μ := (etalePullback q Λ).map η
  let Φ := Scheme.pointSmallEtale s
  have hμ : IsIso (Φ.sheafFiber.map μ) :=
    (NatIso.isIso_map_iff (etalePullbackStalkIso q s Λ) η).mpr hη
  let μ₀ := (etaleModuleUnderlying Y Λ).map μ
  have hμ₀ : IsIso (Φ.sheafFiber.map μ₀) :=
    (NatIso.isIso_map_iff (Φ.sheafFiberCompIso (forget (ModuleCat.{u} Λ))) μ).mpr
      (inferInstanceAs (IsIso ((forget (ModuleCat.{u} Λ)).map (Φ.sheafFiber.map μ))))
  have : Mono (Φ.presheafFiber.map μ₀.hom) := inferInstanceAs (Mono (Φ.sheafFiber.map μ₀))
  rw [← hs]
  exact etaleZariski_stalk_map_mono_of_geometric s ξ μ₀

end EtaleCohomology
