/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.FiniteEtale.DominantPreimmersionPullback
import SchemeTheory.FiniteEtale.DensePullback

/-!
# Abelian Galois covers under dense preimmersion pullback

Pullback along a dominant quasi-compact preimmersion preserves not only the
Galois property but also commutativity of the cover automorphism group.  The
automorphism map is injective by faithfulness and is surjective because both
Galois automorphism groups have the same finite-etale rank.
-/

noncomputable section

open CategoryTheory Limits
open CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.FiniteEtale

universe u

/-- A connected abelian Galois cover remains abelian Galois after pullback
along a dominant quasi-compact preimmersion into a normal integral locally
Noetherian scheme. -/
theorem pullback_obj_aut_isMulCommutative_of_isPreimmersion_of_isDominant
    {U X : Scheme.{u}}
    [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X]
    [ConnectedSpace U]
    (j : U ⟶ X) [IsPreimmersion j] [IsDominant j] [QuasiCompact j]
    (W : FiniteEtale X) (hW : IsGalois W)
    [IsMulCommutative (Aut W)] :
    let P : FiniteEtale U := (pullback j).obj W
    let hP : IsGalois P :=
      pullback_obj_isGalois_of_isPreimmersion_of_isDominant j W hW
    letI : IsGalois P := hP
    IsMulCommutative (Aut P) := by
  dsimp only
  let : IsGalois W := hW
  let P : FiniteEtale U := (pullback j).obj W
  have hP : IsGalois P :=
    pullback_obj_isGalois_of_isPreimmersion_of_isDominant j W hW
  let : IsGalois P := hP
  let : IsSchemeTheoreticallyDominant j :=
    IsSchemeTheoreticallyDominant.of_isDominant j
  let F := pullback j
  let : F.Faithful := AlgebraicGeometry.FiniteEtale.pullback_faithful_of_isDominant j
  have hAutInj : Function.Injective (F.mapAut W) := by
    intro σ τ hστ
    apply Aut.ext
    apply F.map_injective
    exact congrArg Iso.hom hστ
  let u : U := Classical.choice (inferInstance : Nonempty U)
  let Omega := AlgebraicClosure (U.residueField u)
  let xi : Spec (.of Omega) ⟶ U :=
    Spec.map (CommRingCat.ofHom
      (algebraMap (U.residueField u) Omega)) ≫
      U.fromSpecResidueField u
  let xOmega := IsLocalRing.closedPoint Omega
  have hWcard : Nat.card (Aut W) =
      W.hom.finrank ((xi ≫ j) xOmega) :=
    (isGalois_iff_card_aut_eq_finrank (xi ≫ j) W).mp hW
  have hPcard : Nat.card (Aut P) = P.hom.finrank (xi xOmega) :=
    (isGalois_iff_card_aut_eq_finrank xi P).mp hP
  have hrank : P.hom.finrank (xi xOmega) =
      W.hom.finrank ((xi ≫ j) xOmega) := by
    change (pullback.snd W.hom j).finrank (xi xOmega) =
      W.hom.finrank (j (xi xOmega))
    have hpb : IsPullback
        (pullback.fst W.hom j) (pullback.snd W.hom j) W.hom j :=
      IsPullback.of_hasPullback W.hom j
    exact Scheme.Hom.finrank_of_isPullback
      (pullback.fst W.hom j) (pullback.snd W.hom j)
      W.hom j hpb (xi xOmega)
  have hcard : Nat.card (Aut W) = Nat.card (Aut P) := by
    calc
      Nat.card (Aut W) = W.hom.finrank ((xi ≫ j) xOmega) := hWcard
      _ = P.hom.finrank (xi xOmega) := hrank.symm
      _ = Nat.card (Aut P) := hPcard.symm
  have hAutSurj : Function.Surjective (F.mapAut W) :=
    ((Nat.bijective_iff_injective_and_card (F.mapAut W)).mpr
      ⟨hAutInj, hcard⟩).2
  exact IsMulCommutative.of_comm fun σ τ ↦ by
    obtain ⟨σ₀, rfl⟩ := hAutSurj σ
    obtain ⟨τ₀, rfl⟩ := hAutSurj τ
    simpa only [map_mul] using
      congrArg (F.mapAut W) (IsMulCommutative.is_comm.comm σ₀ τ₀)

end AlgebraicGeometry.FiniteEtale

end
