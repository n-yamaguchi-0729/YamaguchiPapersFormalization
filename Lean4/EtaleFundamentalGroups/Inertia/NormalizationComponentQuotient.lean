/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.NormalizationComponentLift
import EtaleFundamentalGroups.GaloisCovers.PullbackComponentStabilizer

/-!
# Normalized component stabilizers and the canonical deck quotient

The lift of a deck transformation fixing a point of a normalized component
maps to the prescribed deck transformation under the actual pointed-component
quotient. The map is the canonical quotient already defined using the two
fundamental-group quotients; equivariance determines its value uniquely.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.PreGaloisCategory
open EtaleFundamentalGroups.Inertia

namespace AlgebraicGeometry.FiniteEtale

universe u

variable {X Y S : Scheme.{u}} [ConnectedSpace X] [ConnectedSpace Y]
variable {Omega : Type u} [Field Omega] [IsSepClosed Omega]

variable (f : X ⟶ Y) (xi : Spec (.of Omega) ⟶ X)
  (W : FiniteEtale Y) (hW : IsGalois W)
  (w : (fiber (xi ≫ f)).obj W)
  (Z : FiniteEtale X) (i : Z ⟶ (pullback f).obj W)
  (z : (fiber xi).obj Z)
  (hiz : (fiber xi).map i z =
    transportedPointOfCompIso (pullback f) (pullbackFiberIso f xi) W w)
  (hZ : IsGalois Z) (hi : Mono i)

/-- Equivariance identifies a given lift with its actual pointed-component
quotient image. The only lifting input is the displayed equality of actual
cover maps, which is supplied geometrically below. -/
theorem galoisPullbackComponentQuotient_eq_of_equivariant
    (tau : Aut Z) (sigma : Aut W)
    (htau : tau.hom ≫ i = i ≫ (pullback f).map sigma.hom) :
    galoisPullbackComponentQuotientMonoidHom
        f xi W hW w Z i z hiz hZ hi (MulOpposite.op tau) =
      MulOpposite.op sigma := by
  let : Mono i := hi
  have hmem : (fiber xi).map ((pullback f).map sigma.hom)
      ((fiber xi).map i z) ∈ Set.range ((fiber xi).map i) := by
    refine ⟨(fiber xi).map tau.hom z, ?_⟩
    have h := congrArg (fun k : Z ⟶ (pullback f).obj W => (fiber xi).map k z) htau
    simpa only [Functor.map_comp, FintypeCat.comp_apply] using h
  obtain ⟨tau', hphi, hequiv⟩ :=
    galoisPullbackComponentQuotient_exists_lift_of_mem_range
      f xi W hW w Z i z hiz hZ hi (MulOpposite.op sigma) hmem
  have heq : tau'.unop = tau := by
    apply Iso.ext
    exact (cancel_mono i).mp (hequiv.trans htau.symm)
  have heqOp : tau' = MulOpposite.op tau :=
    MulOpposite.unop_injective heq
  exact (congrArg
    (galoisPullbackComponentQuotientMonoidHom f xi W hW w Z i z hiz hZ hi)
    heqOp).symm.trans hphi

/-- A normalized geometric-point stabilizer lifts to the component stabilizer,
and its image under the actual canonical component quotient is the original
deck transformation. -/
theorem galoisPullbackComponentQuotient_exists_normalized_fixed_lift
    (g : ((pullback f).obj W).left ⟶ S) [QuasiCompact g] [QuasiSeparated g]
    [IsIntegral Z.left]
    {Omega' : Type u} [Field Omega']
    (q : Spec (.of Omega') ⟶ (i.left ≫ g).normalization)
    (sigma : Aut W)
    (hsigma : ((pullback f).map sigma.hom).left ≫ g = g)
    (hfix : q ≫ normalizationComponentInclusion g i ≫
        normalizationEndomorphism g ((pullback f).map sigma.hom).left hsigma =
      q ≫ normalizationComponentInclusion g i) :
    ∃ (tau : Aut Z)
      (htau : tau.hom ≫ i = i ≫ (pullback f).map sigma.hom),
      galoisPullbackComponentQuotientMonoidHom
          f xi W hW w Z i z hiz hZ hi (MulOpposite.op tau) =
        MulOpposite.op sigma ∧
      q ≫ normalizationEndomorphism (i.left ≫ g) tau.hom.left (by
        have h := congrArg (fun k : Z ⟶ (pullback f).obj W => k.left) htau
        change tau.hom.left ≫ i.left =
          i.left ≫ ((pullback f).map sigma.hom).left at h
        rw [← Category.assoc, h, Category.assoc, hsigma]) = q := by
  let : Mono i := hi
  let : IsGalois Z := hZ
  obtain ⟨tau, htau, hfixed⟩ :=
    exists_aut_component_lift_of_fixes_normalized_geometricPoint
      g i q ((pullback f).mapIso sigma) hsigma hfix
  exact ⟨tau, htau,
    galoisPullbackComponentQuotient_eq_of_equivariant
      f xi W hW w Z i z hiz hZ hi tau sigma htau,
    hfixed⟩

end AlgebraicGeometry.FiniteEtale
