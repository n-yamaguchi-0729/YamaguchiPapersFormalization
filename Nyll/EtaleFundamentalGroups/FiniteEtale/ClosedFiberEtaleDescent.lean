/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.ProperSectionsEtaleFieldDescent
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# The étale closed-fibre algebra of an actual local model

For an actual cartesian model along a local map, the two closed fibres
are related by the native residue-field extension. Geometric reducedness
of the original family therefore supplies the étale section algebra of
the model's closed fibre, without a condition on its other fibres.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

/-- An actual proper model along a local map has an étale closed-fibre
section algebra if its pullback family is geometrically reduced. -/
theorem etale_closedFiber_sections_of_isPullback_of_geometricallyReduced
    {S R : Type u} [CommRing S] [CommRing R] [IsLocalRing S] [IsLocalRing R]
    [Algebra S R] [IsLocalHom (algebraMap S R)]
    {Y X : Scheme.{u}} (g : Y ⟶ Spec (CommRingCat.of S)) [IsProper g]
    (f : X ⟶ Spec (CommRingCat.of R)) [GeometricallyReduced f] (p : X ⟶ Y)
    (hModel : IsPullback p f g (Spec.map (CommRingCat.ofHom (algebraMap S R)))) :
    let qS := Spec.map (CommRingCat.ofHom (IsLocalRing.residue S))
    let : Algebra (IsLocalRing.ResidueField S) Γ(pullback g qS, ⊤) :=
      ((Scheme.ΓSpecIso (CommRingCat.of (IsLocalRing.ResidueField S))).inv ≫
        (pullback.snd g qS).appTop).hom.toAlgebra
    Algebra.Etale (IsLocalRing.ResidueField S) Γ(pullback g qS, ⊤) := by
  intro qS hκ
  let qR := Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
  let b := Spec.map (CommRingCat.ofHom (algebraMap S R))
  let r := Spec.map (CommRingCat.ofHom
    (algebraMap (IsLocalRing.ResidueField S) (IsLocalRing.ResidueField R)))
  have hResidueMap : algebraMap (IsLocalRing.ResidueField S) (IsLocalRing.ResidueField R) =
      IsLocalRing.ResidueField.map (algebraMap S R) := by
    ext x
    obtain ⟨s, rfl⟩ := IsLocalRing.residue_surjective x
    rw [IsLocalRing.ResidueField.algebraMap_residue, IsLocalRing.ResidueField.map_residue]
  have hBase : qR ≫ b = r ≫ qS := by
    dsimp only [qR, b, r, qS]
    rw [hResidueMap, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp, IsLocalRing.ResidueField.map_comp_residue]
  let t : pullback f qR ⟶ pullback g qS :=
    pullback.lift (pullback.fst f qR ≫ p) (pullback.snd f qR ≫ r) (by
      rw [Category.assoc, hModel.w, ← Category.assoc, pullback.condition,
        Category.assoc, hBase, ← Category.assoc])
  have hFiber : IsPullback t (pullback.snd f qR) (pullback.snd g qS) r :=
    hModel.paste_twist_right (IsPullback.of_hasPullback g qS) qR r hBase
      (pullback.fst f qR) (pullback.snd f qR) (IsPullback.of_hasPullback f qR)
      (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
  have hGeometric : GeometricallyReduced (pullback.snd (pullback.snd g qS) r) := by
    refine ((show MorphismProperty Scheme.{u} from @GeometricallyReduced).cancel_left_of_respectsIso
      hFiber.isoPullback.hom (pullback.snd (pullback.snd g qS) r)).mp ?_
    rw [hFiber.isoPullback_hom_snd]
    infer_instance
  have hEtale : (pullback.snd g qS).appTop.hom.Etale :=
    etale_appTop_of_isProper_of_geometricallyReduced_field_baseChange
      (L := IsLocalRing.ResidueField R) (pullback.snd g qS)
  exact (RingHom.Etale.respectsIso.cancel_left_isIso
    (Scheme.ΓSpecIso (CommRingCat.of (IsLocalRing.ResidueField S))).inv
      (pullback.snd g qS).appTop).mpr hEtale

end AlgebraicGeometry
