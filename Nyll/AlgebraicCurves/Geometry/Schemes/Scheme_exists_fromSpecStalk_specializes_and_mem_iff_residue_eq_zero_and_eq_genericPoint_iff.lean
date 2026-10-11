/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_exists_fromSpecStalk_specializes_and_mem_iff_residue_eq_zero_and_eq_genericPoint_iff.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.AlgebraicGeometry.ResidueField

/-!
# Scheme exists from Spec Stalk specializes and mem iff residue eq zero and eq generic Point
iff
-/

section ProofImplementation

namespace AlgebraicGeometry.Scheme

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem exists_fromSpecStalk_specializes_and_mem_iff_residue_eq_zero_and_eq_genericPoint_iff
    {X : Scheme.{u}} [IsIntegral X] (x : X) (P : Ideal (X.presheaf.stalk x)) [hP : P.IsPrime] :
    ∃ hη : (X.fromSpecStalk x).base ⟨P, hP⟩ ⤳ x,
      (∀ b : X.presheaf.stalk x,
        b ∈ P ↔ X.residue ((X.fromSpecStalk x).base ⟨P, hP⟩) ((X.presheaf.stalkSpecializes hη).hom
          b) = 0) ∧
      ((X.fromSpecStalk x).base ⟨P, hP⟩ = genericPoint X ↔ P = ⊥)  := by
  classical
  let p : Spec (X.presheaf.stalk x) := ⟨P, hP⟩
  let q : Spec (X.presheaf.stalk x) := IsLocalRing.closedPoint (X.presheaf.stalk x)
  have hη : (X.fromSpecStalk x).base p ⤳ x := by
    have : (X.fromSpecStalk x).base p ∈ Set.range (X.fromSpecStalk x).base := ⟨_, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  refine ⟨hη, fun b => ?_, ?_⟩
  · have hqc : (p : Spec (X.presheaf.stalk x)) ⤳ q :=
      IsLocalRing.specializes_closedPoint _
    have hins : Inseparable ((X.fromSpecStalk x).base (q)) x := by
      rw [Scheme.fromSpecStalk_closedPoint]
    have key : X.presheaf.stalkSpecializes hη ≫ (X.fromSpecStalk x).stalkMap p =
        StructureSheaf.toStalk (X.presheaf.stalk x) p := by
      have hmap : (X.fromSpecStalk x) p ⤳ (X.fromSpecStalk x) q :=
        (X.fromSpecStalk x).base.hom.map_specializes hqc
      have hqx : (X.fromSpecStalk x) q ⤳ x := hins.le
      let e : X.presheaf.stalk ((X.fromSpecStalk x) q) ≅ X.presheaf.stalk x :=
        X.presheaf.stalkCongr hins
      have h1 : X.presheaf.stalkSpecializes hmap ≫ (X.fromSpecStalk x).stalkMap p =
          (X.fromSpecStalk x).stalkMap q ≫
            (Spec (X.presheaf.stalk x)).presheaf.stalkSpecializes hqc :=
        (X.fromSpecStalk x).stalkSpecializes_stalkMap _ _ hqc
      have h2 : X.presheaf.stalkSpecializes hη = e.inv ≫
          X.presheaf.stalkSpecializes hmap :=
        (X.presheaf.stalkSpecializes_comp hmap hqx).symm
      have hclose : Scheme.stalkClosedPointTo (X.fromSpecStalk x) = e.hom :=
        Scheme.stalkClosedPointTo_fromSpecStalk x
      have h3 : (X.fromSpecStalk x).stalkMap q = e.hom ≫
          StructureSheaf.toStalk (X.presheaf.stalk x) q := by
        have hz : (X.fromSpecStalk x).stalkMap q ≫
            (stalkClosedPointIso (X.presheaf.stalk x)).hom = e.hom := hclose
        have hzi : (X.fromSpecStalk x).stalkMap q =
            e.hom ≫ (stalkClosedPointIso (X.presheaf.stalk x)).inv :=
          ((stalkClosedPointIso (X.presheaf.stalk x)).eq_comp_inv).2 hz
        exact hzi.trans (congrArg (fun g : X.presheaf.stalk x ⟶
          (Spec (X.presheaf.stalk x)).presheaf.stalk q => e.hom ≫ g)
          (stalkClosedPointIso_inv (X.presheaf.stalk x)))
      let g : X.presheaf.stalk x ⟶ (Spec (X.presheaf.stalk x)).presheaf.stalk q :=
        StructureSheaf.toStalk (X.presheaf.stalk x) q
      let s : (Spec (X.presheaf.stalk x)).presheaf.stalk q ⟶
          (Spec (X.presheaf.stalk x)).presheaf.stalk p :=
        (Spec (X.presheaf.stalk x)).presheaf.stalkSpecializes hqc
      have hc : e.inv ≫ (e.hom ≫ g) = g := e.inv_hom_id_assoc g
      have hcancel : e.inv ≫ ((e.hom ≫ g) ≫ s) = g ≫ s :=
        (Category.assoc e.inv (e.hom ≫ g) s).symm.trans
          (congrArg (fun k : X.presheaf.stalk x ⟶
            (Spec (X.presheaf.stalk x)).presheaf.stalk q => k ≫ s) hc)
      have h1' : X.presheaf.stalkSpecializes hmap ≫ (X.fromSpecStalk x).stalkMap p =
          (X.fromSpecStalk x).stalkMap q ≫ s := h1
      have h3' : (X.fromSpecStalk x).stalkMap q = e.hom ≫ g := h3
      have hfinal : g ≫ s = StructureSheaf.toStalk (X.presheaf.stalk x) p :=
        StructureSheaf.toStalk_stalkSpecializes hqc
      exact (congrArg (fun k : X.presheaf.stalk x ⟶ X.presheaf.stalk ((X.fromSpecStalk x) p) =>
          k ≫ (X.fromSpecStalk x).stalkMap p) h2).trans
        ((Category.assoc e.inv (X.presheaf.stalkSpecializes hmap) ((X.fromSpecStalk x).stalkMap
          p)).trans
          ((congrArg (fun k : X.presheaf.stalk ((X.fromSpecStalk x) q) ⟶
            (Spec (X.presheaf.stalk x)).presheaf.stalk p => e.inv ≫ k) h1').trans
            ((congrArg (fun k : X.presheaf.stalk ((X.fromSpecStalk x) q) ⟶
              (Spec (X.presheaf.stalk x)).presheaf.stalk q => e.inv ≫ (k ≫ s)) h3').trans
              (hcancel.trans hfinal))))
    have keyb : ((X.fromSpecStalk x).stalkMap p).hom ((X.presheaf.stalkSpecializes hη).hom b) =
        (StructureSheaf.toStalk (X.presheaf.stalk x) p).hom b := by
      have := congrArg (fun φ => φ.hom b) key
      simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at this
      exact this
    let : Algebra (X.presheaf.stalk x) ((Spec (X.presheaf.stalk x)).presheaf.stalk p) :=
      StructureSheaf.stalkAlgebra (R := X.presheaf.stalk x) p
    have : IsLocalization.AtPrime ((Spec (X.presheaf.stalk x)).presheaf.stalk p)
        (p : PrimeSpectrum (X.presheaf.stalk x)).asIdeal :=
      StructureSheaf.IsLocalization.to_stalk (X.presheaf.stalk x) p
    have hloc : b ∈ P ↔ (StructureSheaf.toStalk (X.presheaf.stalk x) p).hom b ∈
        IsLocalRing.maximalIdeal ((Spec (X.presheaf.stalk x)).presheaf.stalk p) :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff ((Spec (X.presheaf.stalk x)).presheaf.stalk p)
        (p : PrimeSpectrum (X.presheaf.stalk x)).asIdeal b).symm
    rw [hloc, ← keyb]
    refine (IsLocalRing.mem_maximalIdeal (R := (Spec (X.presheaf.stalk x)).presheaf.stalk p)
      _).trans ?_
    refine mem_nonunits_iff.trans ?_
    refine (isUnit_map_iff ((X.fromSpecStalk x).stalkMap p).hom _).not.trans ?_
    refine mem_nonunits_iff.symm.trans ?_
    refine (IsLocalRing.mem_maximalIdeal _).symm.trans ?_
    exact (IsLocalRing.residue_eq_zero_iff _).symm
  · have hgen : (X.fromSpecStalk x).base (⊥ : PrimeSpectrum (X.presheaf.stalk x)) = genericPoint X
      := by
      obtain ⟨q₀, hq₀⟩ : genericPoint X ∈ Set.range (X.fromSpecStalk x).base := by
        rw [Scheme.range_fromSpecStalk]; exact genericPoint_specializes x
      have hb : (⊥ : PrimeSpectrum (X.presheaf.stalk x)) ⤳ q₀ := by
        have := genericPoint_specializes q₀
        rwa [genericPoint_eq_bot_of_affine] at this
      have h1 : (X.fromSpecStalk x).base (⊥ : PrimeSpectrum (X.presheaf.stalk x)) ⤳ genericPoint X
        :=
        hq₀ ▸ hb.map (X.fromSpecStalk x).base.hom.continuous
      exact (h1.antisymm (genericPoint_specializes _)).eq
    constructor
    · intro h
      have := (X.fromSpecStalk x).isEmbedding.injective (h.trans hgen.symm)
      exact congrArg PrimeSpectrum.asIdeal this
    · intro h
      have hp : (p : PrimeSpectrum (X.presheaf.stalk x)) =
          (⊥ : PrimeSpectrum (X.presheaf.stalk x)) := PrimeSpectrum.ext h
      exact (congrArg (fun t : Spec (X.presheaf.stalk x) => (X.fromSpecStalk x) t) hp).trans hgen
end AlgebraicGeometry.Scheme
end ProofImplementation
