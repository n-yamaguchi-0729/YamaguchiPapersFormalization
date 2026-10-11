/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.StrictHenselianFractionNormalizationPoint
import Nyll.EtaleFundamentalGroups.Inertia.NormalizationSquare
import Nyll.EtaleFundamentalGroups.GaloisCovers.PullbackComponentEquivariance

/-!
# Strict local monodromy fixes an actual normalization point

Select the pointed Galois component of the actual generic pullback. Its
normalization over the strict-Henselian DVR has a point fixed by every deck
transformation over the prescribed residue-field embedding. The actual
commuting square maps this point to the original relative normalization.
The canonical component quotient and its proved equivariance show that the
entire local monodromy image fixes the resulting point.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.PreGaloisCategory

namespace EtaleFundamentalGroups.Inertia

universe u

/-- The finite monodromy image from a strict-Henselian fraction field fixes
an actual point of the original normalization, over the specified closed
geometric point of the local model. -/
theorem exists_normalizationPoint_fixed_by_strictHenselian_finiteImage
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HenselianLocalRing R] [IsSepClosed (IsLocalRing.ResidueField R)]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {X U : Scheme.{u}} [ConnectedSpace U]
    (u : U ⟶ X) [QuasiCompact u] [QuasiSeparated u]
    (b : Spec (.of R) ⟶ X) (j : Spec (.of K) ⟶ U)
    (hjb : j ≫ u = Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ b)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (ψ : R →+* Ω) [IsLocalHom ψ]
    {Ξ : Type u} [Field Ξ] [IsSepClosed Ξ]
    (xi : Spec (.of Ξ) ⟶ Spec (.of K))
    (W : FiniteEtale U) (hW : IsGalois W)
    (w : (FiniteEtale.fiber (xi ≫ j)).obj W) :
    ∃ z : Spec (.of Ω) ⟶ (W.hom ≫ u).normalization,
      z ≫ (W.hom ≫ u).fromNormalization = Spec.map (CommRingCat.ofHom ψ) ≫ b ∧
      ∀ σ : (Aut W)ᵐᵒᵖ,
        σ ∈ (finiteEtaleGaloisCoverQuotientOfMorphism j xi W hW w).range →
        z ≫ normalizationEndomorphism (W.hom ≫ u) σ.unop.hom.left
          (by
            rw [← Category.assoc]
            exact congrArg (fun k => k ≫ u) σ.unop.hom.w) = z := by
  obtain ⟨Z, i, point, hiz, hZ, hi⟩ :=
    FiniteEtale.exists_galoisComponent_pullback j xi W hW w
  let : IsGalois Z := hZ
  let : Mono i := hi
  let g := Spec.map (CommRingCat.ofHom (algebraMap R K))
  let f : Z.left ⟶ Spec (.of R) := (show Z.left ⟶ Spec (.of K) from Z.hom) ≫ g
  let F : W.left ⟶ X := W.hom ≫ u
  let a : Z.left ⟶ W.left := i.left ≫ pullback.fst W.hom j
  have haW : a ≫ W.hom = (show Z.left ⟶ Spec (.of K) from Z.hom) ≫ j := by
    have hiw : i.left ≫ pullback.snd W.hom j =
        (show Z.left ⟶ Spec (.of K) from Z.hom) := i.w
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun k => i.left ≫ k) (pullback.condition (f := W.hom) (g := j))).trans
        ((Category.assoc _ _ _).symm.trans (congrArg (fun k => k ≫ j) hiw)))
  have ha : a ≫ F = f ≫ b := by
    change a ≫ (W.hom ≫ u) =
      ((show Z.left ⟶ Spec (.of K) from Z.hom) ≫ g) ≫ b
    rw [← Category.assoc, haW, Category.assoc, hjb, ← Category.assoc]
  obtain ⟨q, hqbase, hqfixed⟩ :=
    exists_fractionCover_normalizationPoint_fixed_of_strictHenselian R K Z ψ
  let n : f.normalization ⟶ F.normalization := normalizationMapOfSquare f F a b ha
  let z : Spec (.of Ω) ⟶ F.normalization := q ≫ n
  refine ⟨z, ?_, ?_⟩
  · change (q ≫ n) ≫ F.fromNormalization = Spec.map (CommRingCat.ofHom ψ) ≫ b
    rw [Category.assoc, normalizationMapOfSquare_base, ← Category.assoc, hqbase]
  · intro σ hσ
    let μ := FiniteEtale.galoisPullbackComponentQuotientMonoidHom
      j xi W hW w Z i point hiz hZ hi
    have hrange : μ.range = (finiteEtaleGaloisCoverQuotientOfMorphism j xi W hW w).range :=
      FiniteEtale.galoisPullbackComponentQuotientMonoidHom_range
        j xi W hW w Z i point hiz hZ hi
    obtain ⟨τ, rfl⟩ := (show σ ∈ μ.range from hrange.symm ▸ hσ)
    have hτ : τ.unop.hom.left ≫ f = f := by
      have hw : τ.unop.hom.left ≫ (show Z.left ⟶ Spec (.of K) from Z.hom) =
          (show Z.left ⟶ Spec (.of K) from Z.hom) := τ.unop.hom.w
      exact (Category.assoc _ _ _).symm.trans (congrArg (fun k => k ≫ g) hw)
    have hμ : (μ τ).unop.hom.left ≫ F = F := by
      have hw : (μ τ).unop.hom.left ≫ W.hom = W.hom := (μ τ).unop.hom.w
      exact (Category.assoc _ _ _).symm.trans (congrArg (fun k => k ≫ u) hw)
    have he : τ.unop.hom.left ≫ a = a ≫ (μ τ).unop.hom.left := by
      have hiEquiv := congrArg
        (fun k : Z ⟶ (FiniteEtale.pullback j).obj W => k.left)
        (FiniteEtale.galoisPullbackComponentQuotientMonoidHom_equivariant
          j xi W hW w Z i point hiz hZ hi τ)
      change τ.unop.hom.left ≫ i.left =
        i.left ≫ ((FiniteEtale.pullback j).map (μ τ).unop.hom).left at hiEquiv
      have hfst : ((FiniteEtale.pullback j).map (μ τ).unop.hom).left ≫
          pullback.fst W.hom j = pullback.fst W.hom j ≫ (μ τ).unop.hom.left :=
        pullback.lift_fst _ _ _
      change τ.unop.hom.left ≫ (i.left ≫ pullback.fst W.hom j) =
        (i.left ≫ pullback.fst W.hom j) ≫ (μ τ).unop.hom.left
      exact (Category.assoc τ.unop.hom.left i.left (pullback.fst W.hom j)).symm.trans
        ((congrArg (fun k => k ≫ pullback.fst W.hom j) hiEquiv).trans
          ((Category.assoc _ _ _).trans
            ((congrArg (fun k => i.left ≫ k) hfst).trans (Category.assoc _ _ _).symm)))
    have hn : normalizationEndomorphism f τ.unop.hom.left hτ ≫ n =
        n ≫ normalizationEndomorphism F (μ τ).unop.hom.left hμ :=
      normalizationMapOfSquare_endomorphism f F a b ha
        τ.unop.hom.left hτ (μ τ).unop.hom.left hμ he
    change (q ≫ n) ≫ normalizationEndomorphism F (μ τ).unop.hom.left hμ = q ≫ n
    rw [Category.assoc, ← hn, ← Category.assoc, hqfixed τ.unop]

end EtaleFundamentalGroups.Inertia
