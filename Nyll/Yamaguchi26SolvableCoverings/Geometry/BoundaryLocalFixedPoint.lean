/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.Yamaguchi26SolvableCoverings.Geometry.BoundaryInertia
import Nyll.EtaleFundamentalGroups.Inertia.CartierLocalFractionField
import Nyll.EtaleFundamentalGroups.Inertia.NormalizationSquare
import Nyll.EtaleFundamentalGroups.GaloisCovers.PullbackComponentEquivariance

/-!
# Boundary-unramifiedness on an actual local Galois component

A normalized geometric point of a component over the fraction stalk maps to
the original cover's normalization. Equivariance and injectivity of the
canonical component quotient transfer the original boundary condition to
this point. No normality assumption on the ambient scheme is used.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.PreGaloisCategory AlgebraicGeometry.FiniteEtale
open EtaleFundamentalGroups.Inertia

namespace Yamaguchi26SolvableCoverings

variable {X : Scheme.{0}} [IsLocallyNoetherian X]
  (D : X.EffectiveCartierDivisor) (E : Component D)
  [IsDomain (X.presheaf.stalk (componentPoint D E))]
  [ConnectedSpace D.1.supportComplement]

local notation "R" => X.presheaf.stalk (componentPoint D E)
local notation "K" => FractionRing R
local notation "c" =>
  Scheme.IdealSheafData.IsEffectiveCartier.fractionStalkToSupportComplement
    (Subtype.property D) (componentPoint D E)
local notation "a₀" => Spec.map (CommRingCat.ofHom (algebraMap R K))

/-- The original boundary-unramified condition forces the actual normalized
fixed-point stabilizers of every pointed local Galois component to be trivial. -/
theorem boundaryUnramified_localComponent_fixed_eq_one
    {Ω : Type} [Field Ω] [IsSepClosed Ω]
    (xi : Spec (.of Ω) ⟶ Spec (.of K))
    (W : FiniteEtale D.1.supportComplement) (hW : IsGalois W)
    (hU : IsBoundaryUnramified D W)
    (w : (fiber (xi ≫ c)).obj W)
    (Z : FiniteEtale (Spec (.of K))) (i : Z ⟶ (FiniteEtale.pullback c).obj W)
    (v : (fiber xi).obj Z)
    (hiv : (fiber xi).map i v =
      transportedPointOfCompIso (FiniteEtale.pullback c)
        (pullbackFiberIso c xi) W w)
    (hZ : IsGalois Z) (hi : Mono i)
    (z : Spec (.of (AlgebraicClosure (X.residueField (componentPoint D E)))) ⟶
      ((show Z.left ⟶ Spec (.of K) from Z.hom) ≫ a₀).normalization)
    (hz : z ≫ ((show Z.left ⟶ Spec (.of K) from Z.hom) ≫ a₀).fromNormalization =
      Spec.map (CommRingCat.ofHom
        ((algebraMap (X.residueField (componentPoint D E))
          (AlgebraicClosure (X.residueField (componentPoint D E)))).comp
            (IsLocalRing.residue R))))
    (τ : Aut Z)
    (hτ : z ≫ normalizationEndomorphism
      ((show Z.left ⟶ Spec (.of K) from Z.hom) ≫ a₀) τ.hom.left
      (by
        have hw : τ.hom.left ≫ (show Z.left ⟶ Spec (.of K) from Z.hom) =
            (show Z.left ⟶ Spec (.of K) from Z.hom) := τ.hom.w
        exact (Category.assoc τ.hom.left (show Z.left ⟶ Spec (.of K) from Z.hom) a₀).symm.trans
          (congrArg (fun k => k ≫ a₀) hw)) = z) :
    τ = 1 := by
  let f : Z.left ⟶ Spec (.of R) := (show Z.left ⟶ Spec (.of K) from Z.hom) ≫ a₀
  let g : W.left ⟶ X := W.hom ≫ D.1.supportComplement.ι
  let a : Z.left ⟶ W.left := i.left ≫ Limits.pullback.fst W.hom c
  let b : Spec (.of R) ⟶ X := X.fromSpecStalk (componentPoint D E)
  have hiw : i.left ≫ Limits.pullback.snd W.hom c =
      (show Z.left ⟶ Spec (.of K) from Z.hom) := i.w
  have hsquare : a ≫ g = f ≫ b := by
    calc
      a ≫ g = i.left ≫ (Limits.pullback.fst W.hom c ≫ W.hom) ≫
          D.1.supportComplement.ι :=
        (Category.assoc i.left (Limits.pullback.fst W.hom c)
          (W.hom ≫ D.1.supportComplement.ι)).trans
          (congrArg (fun k => i.left ≫ k)
            (Category.assoc (Limits.pullback.fst W.hom c) W.hom
              D.1.supportComplement.ι).symm)
      _ = i.left ≫ (Limits.pullback.snd W.hom c ≫ c) ≫
          D.1.supportComplement.ι :=
        congrArg (fun k => i.left ≫ k ≫ D.1.supportComplement.ι)
          (Limits.pullback.condition (f := W.hom) (g := c))
      _ = (i.left ≫ Limits.pullback.snd W.hom c) ≫
          (c ≫ D.1.supportComplement.ι) :=
        (congrArg (fun k => i.left ≫ k)
          (Category.assoc (Limits.pullback.snd W.hom c) c D.1.supportComplement.ι)).trans
          (Category.assoc i.left (Limits.pullback.snd W.hom c)
            (c ≫ D.1.supportComplement.ι)).symm
      _ = (show Z.left ⟶ Spec (.of K) from Z.hom) ≫
          (c ≫ D.1.supportComplement.ι) :=
        congrArg (fun k => k ≫ (c ≫ D.1.supportComplement.ι)) hiw
      _ = (show Z.left ⟶ Spec (.of K) from Z.hom) ≫ (a₀ ≫ b) :=
        congrArg (fun k => (show Z.left ⟶ Spec (.of K) from Z.hom) ≫ k)
          (D.2.fractionStalkToSupportComplement_comp_ι (componentPoint D E))
      _ = f ≫ b := (Category.assoc _ _ _).symm
  let q := galoisPullbackComponentQuotientMonoidHom c xi W hW w Z i v hiv hZ hi
  let σ : Aut W := (q (MulOpposite.op τ)).unop
  have hσ : σ.hom.left ≫ g = g := by
    have hw : σ.hom.left ≫ (show W.left ⟶ D.1.supportComplement from W.hom) =
        (show W.left ⟶ D.1.supportComplement from W.hom) := σ.hom.w
    exact (Category.assoc _ _ _).symm.trans
      (congrArg (fun k => k ≫ D.1.supportComplement.ι) hw)
  have hequiv : τ.hom.left ≫ a = a ≫ σ.hom.left := by
    have hh := congrArg (fun k : Z ⟶ (FiniteEtale.pullback c).obj W => k.left)
      (galoisPullbackComponentQuotientMonoidHom_equivariant
        c xi W hW w Z i v hiv hZ hi (MulOpposite.op τ))
    change τ.hom.left ≫ i.left =
      i.left ≫ ((FiniteEtale.pullback c).map σ.hom).left at hh
    have hmap : ((FiniteEtale.pullback c).map σ.hom).left ≫
        Limits.pullback.fst W.hom c = Limits.pullback.fst W.hom c ≫ σ.hom.left :=
      Limits.pullback.lift_fst _ _ _
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ Limits.pullback.fst W.hom c) hh).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun k => i.left ≫ k) hmap).trans (Category.assoc _ _ _).symm)))
  let n := normalizationMapOfSquare f g a b hsquare
  have hnbase : (z ≫ n) ≫ g.fromNormalization = componentGeometricPoint D E := by
    rw [Category.assoc, normalizationMapOfSquare_base, ← Category.assoc, hz]
    dsimp only [componentGeometricPoint, Scheme.fromSpecResidueField,
      Scheme.residue, b]
    exact (congrArg (fun k => k ≫ X.fromSpecStalk (componentPoint D E))
      (Spec.map_comp (CommRingCat.ofHom (IsLocalRing.residue R))
        (CommRingCat.ofHom (algebraMap (X.residueField (componentPoint D E))
          (AlgebraicClosure (X.residueField (componentPoint D E))))))).trans
      (Category.assoc _ _ _)
  have hτf : τ.hom.left ≫ f = f := by
    have hw : τ.hom.left ≫ (show Z.left ⟶ Spec (.of K) from Z.hom) =
        (show Z.left ⟶ Spec (.of K) from Z.hom) := τ.hom.w
    exact (Category.assoc _ _ _).symm.trans (congrArg (fun k => k ≫ a₀) hw)
  have hnfix : (z ≫ n) ≫ normalizationDeck D W σ = z ≫ n := by
    change (z ≫ n) ≫ normalizationEndomorphism g σ.hom.left hσ = z ≫ n
    rw [Category.assoc, ← normalizationMapOfSquare_endomorphism
      f g a b hsquare τ.hom.left hτf
      σ.hom.left hσ hequiv, ← Category.assoc, hτ]
  have hσone : σ = 1 := by
    have hm : σ ∈ finiteCoverInertia D W E (z ≫ n) := hnfix
    rw [hU E (z ≫ n) hnbase] at hm
    exact Subgroup.mem_bot.mp hm
  apply MulOpposite.op_injective
  apply galoisPullbackComponentQuotientMonoidHom_injective c xi W hW w Z i v hiv hZ hi
  change q (MulOpposite.op τ) = q 1
  rw [map_one]
  exact MulOpposite.unop_injective hσone

end Yamaguchi26SolvableCoverings
