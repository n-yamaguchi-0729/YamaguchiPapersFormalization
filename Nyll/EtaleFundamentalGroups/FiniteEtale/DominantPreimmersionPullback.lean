/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.Integral
import Nyll.EtaleFundamentalGroups.GaloisCovers.Basic
import Nyll.SchemeTheory.FiniteEtale.DensePullback
import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# Finite-etale pullback along dominant preimmersions

A dominant quasi-compact preimmersion from a connected scheme into a normal
integral scheme preserves connected finite-etale covers.
If the original cover is a Galois object, faithfulness of pullback and
invariance of the finite-etale rank show that the pulled-back connected cover
is again Galois.
-/

noncomputable section

open CategoryTheory Limits MorphismProperty
open CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry

universe u

/-- A dominant preimmersion into an irreducible scheme has irreducible
source. -/
theorem irreducibleSpace_of_isPreimmersion_of_isDominant
    {U X : Scheme.{u}} (f : U ⟶ X)
    [IsPreimmersion f] [IsDominant f] [IrreducibleSpace X] :
    IrreducibleSpace U := by
  let : Nonempty U := f.denseRange.nonempty
  let hpre : PreirreducibleSpace U :=
    PreirreducibleSpace.of_forall_nonempty_inter
      (fun {A B} hA hB hAne hBne ↦ by
        obtain ⟨A', hA'open, hA'⟩ :=
          f.isEmbedding.isInducing.isOpen_iff.mp hA
        obtain ⟨B', hB'open, hB'⟩ :=
          f.isEmbedding.isInducing.isOpen_iff.mp hB
        have hA'ne : A'.Nonempty := by
          obtain ⟨a, ha⟩ := hAne
          refine ⟨f a, ?_⟩
          change a ∈ f ⁻¹' A'
          rwa [hA']
        have hB'ne : B'.Nonempty := by
          obtain ⟨b, hb⟩ := hBne
          refine ⟨f b, ?_⟩
          change b ∈ f ⁻¹' B'
          rwa [hB']
        have hAB'ne : (A' ∩ B').Nonempty :=
          nonempty_preirreducible_inter hA'open hB'open hA'ne hB'ne
        obtain ⟨a, ha⟩ :=
          f.denseRange.exists_mem_open (hA'open.inter hB'open) hAB'ne
        refine ⟨a, ?_, ?_⟩
        · rw [← hA']
          exact ha.1
        · rw [← hB']
          exact ha.2)
  exact { toPreirreducibleSpace := hpre, toNonempty := inferInstance }

namespace FiniteEtale

local instance preimmersionStableUnderBaseChangeAlongDominant
    {S T : Scheme.{u}} (f : S ⟶ T) :
    MorphismProperty.IsStableUnderBaseChangeAlong
      (@IsPreimmersion : MorphismProperty Scheme.{u}) f :=
  ⟨fun h hf ↦ MorphismProperty.of_isPullback
    (P := (@IsPreimmersion : MorphismProperty Scheme.{u})) h hf⟩

local instance quasiCompactStableUnderBaseChangeAlongDominant
    {S T : Scheme.{u}} (f : S ⟶ T) :
    MorphismProperty.IsStableUnderBaseChangeAlong
      (@QuasiCompact : MorphismProperty Scheme.{u}) f :=
  ⟨fun h hf ↦ MorphismProperty.of_isPullback
    (P := (@QuasiCompact : MorphismProperty Scheme.{u})) h hf⟩

/-- A dominant quasi-compact preimmersion from a connected scheme into a
normal integral base preserves connectedness of connected
finite-etale covers. -/
theorem pullback_obj_isConnected_of_isPreimmersion_of_isDominant
    {U X : Scheme.{u}}
    [IsIntegral X] [IsNormalIntegral X]
    [ConnectedSpace U]
    (j : U ⟶ X) [hjpre : IsPreimmersion j]
    [hjdom : IsDominant j] [hjqc : QuasiCompact j]
    (W : FiniteEtale X) [IsConnected W] :
    IsConnected ((pullback j).obj W) := by
  let : IsIntegral W.left :=
    EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale W
  let P : FiniteEtale U := (pullback j).obj W
  let iP : P.left ⟶ W.left := Limits.pullback.fst W.hom j
  let : IsPreimmersion iP := by
    dsimp only [iP]
    exact MorphismProperty.pullback_fst (P := @IsPreimmersion)
      W.hom j hjpre
  let hstd : IsSchemeTheoreticallyDominant j :=
    IsSchemeTheoreticallyDominant.of_isDominant j
  let hflat : Flat W.hom :=
    Etale.iff_flat_and_formallyUnramified.mp W.prop.toEtale |>.1
  let : IsSchemeTheoreticallyDominant iP := by
    dsimp only [iP]
    exact @IsSchemeTheoreticallyDominant.pullbackFst _ _ _
      W.hom j hstd hjqc hflat
  let : QuasiCompact iP := by
    dsimp only [iP]
    exact MorphismProperty.pullback_fst (P := @QuasiCompact)
      W.hom j hjqc
  let : IsDominant iP := inferInstance
  let : IrreducibleSpace P.left :=
    irreducibleSpace_of_isPreimmersion_of_isDominant iP
  let : ConnectedSpace P.left := inferInstance
  exact isConnected_of_connectedSpace_left P

/-- Under the same dense-preimmersion hypotheses, pullback preserves
categorical Galois covers. -/
theorem pullback_obj_isGalois_of_isPreimmersion_of_isDominant
    {U X : Scheme.{u}}
    [IsIntegral X] [IsNormalIntegral X]
    [ConnectedSpace U]
    (j : U ⟶ X) [hjpre : IsPreimmersion j]
    [hjdom : IsDominant j] [hjqc : QuasiCompact j]
    (W : FiniteEtale X) (hW : IsGalois W) :
    IsGalois ((pullback j).obj W) := by
  let : IsGalois W := hW
  let P : FiniteEtale U := (pullback j).obj W
  have hPconn : IsConnected P :=
    pullback_obj_isConnected_of_isPreimmersion_of_isDominant j W
  let : IsConnected P := hPconn
  let : IsSchemeTheoreticallyDominant j :=
    IsSchemeTheoreticallyDominant.of_isDominant j
  let F := pullback j
  let : F.Faithful := pullback_faithful_of_isDominant j
  have hAutInj : Function.Injective (F.mapAut W) := by
    intro σ τ hστ
    apply Aut.ext
    apply F.map_injective
    exact congrArg Iso.hom hστ
  have hAutLe : Nat.card (Aut W) ≤ Nat.card (Aut P) :=
    Nat.card_le_card_of_injective (F.mapAut W) hAutInj
  let u : U := Classical.choice j.denseRange.nonempty
  let Ω := AlgebraicClosure (U.residueField u)
  let ξ : Spec (.of Ω) ⟶ U :=
    Spec.map (CommRingCat.ofHom
      (algebraMap (U.residueField u) Ω)) ≫
      U.fromSpecResidueField u
  let xΩ := IsLocalRing.closedPoint Ω
  have hWcard : Nat.card (Aut W) =
      W.hom.finrank ((ξ ≫ j) xΩ) :=
    (isGalois_iff_card_aut_eq_finrank (ξ ≫ j) W).mp hW
  have hrank : P.hom.finrank (ξ xΩ) =
      W.hom.finrank ((ξ ≫ j) xΩ) := by
    change (Limits.pullback.snd W.hom j).finrank (ξ xΩ) =
      W.hom.finrank (j (ξ xΩ))
    have hpb : IsPullback
        (Limits.pullback.fst W.hom j)
        (Limits.pullback.snd W.hom j) W.hom j :=
      IsPullback.of_hasPullback W.hom j
    exact Scheme.Hom.finrank_of_isPullback
      (Limits.pullback.fst W.hom j)
      (Limits.pullback.snd W.hom j) W.hom j hpb (ξ xΩ)
  have hUpper : Nat.card (Aut P) ≤ P.hom.finrank (ξ xΩ) := by
    have h := card_aut_le_card_fiber_of_connected (fiber ξ) P
    rwa [natCard_fiber_eq_finrank ξ P] at h
  apply (isGalois_iff_card_aut_eq_finrank ξ P).mpr
  apply Nat.le_antisymm hUpper
  calc
    P.hom.finrank (ξ xΩ) = W.hom.finrank ((ξ ≫ j) xΩ) := hrank
    _ = Nat.card (Aut W) := hWcard.symm
    _ ≤ Nat.card (Aut P) := hAutLe

end FiniteEtale

end AlgebraicGeometry

end
