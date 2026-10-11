/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.GaloisCovers.PullbackComponentEquivariance
import Mathlib.CategoryTheory.Galois.GaloisObjects

/-!
# The deck group of a pullback component and its setwise stabilizer

The image of the canonical deck-group homomorphism for a pointed Galois
pullback component consists exactly of the original deck transformations
preserving the component's geometric-fiber range. In fact, it suffices that
the distinguished point is mapped back into that range: transitivity of the
component deck group constructs a lift, and evaluation on the original
connected cover proves that its image is the prescribed transformation.

This is a statement about actual cover automorphisms and their fiber actions.
No lifting or equivariance assumption is introduced. To use it for inertia
on a normalization, one must still prove geometrically that fixing the
chosen normalization point preserves the relevant component.
-/

noncomputable section


open AlgebraicGeometry CategoryTheory
open CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.FiniteEtale

universe u

variable {X Y : Scheme.{u}} [ConnectedSpace X] [ConnectedSpace Y]
variable {Omega : Type u} [Field Omega] [IsSepClosed Omega]

variable (f : X ⟶ Y) (xi : Spec (.of Omega) ⟶ X)
  (W : FiniteEtale Y) (hW : IsGalois W)
  (w : (fiber (xi ≫ f)).obj W)
  (Z : FiniteEtale X) (i : Z ⟶ (pullback f).obj W)
  (z : (fiber xi).obj Z)
  (hiz : (fiber xi).map i z =
    transportedPointOfCompIso (pullback f) (pullbackFiberIso f xi) W w)
  (hZ : IsGalois Z) (hi : Mono i)

/-- An original deck transformation lifts to the chosen Galois component as
soon as it maps the distinguished fiber point back into that component.
The lift is constructed using the transitive component deck action. -/
theorem galoisPullbackComponentQuotient_exists_lift_of_mem_range
    (sigma : (Aut W)ᵐᵒᵖ)
    (hsigma : (fiber xi).map ((pullback f).map sigma.unop.hom)
      ((fiber xi).map i z) ∈ Set.range ((fiber xi).map i)) :
    ∃ tau : (Aut Z)ᵐᵒᵖ,
      galoisPullbackComponentQuotientMonoidHom
          f xi W hW w Z i z hiz hZ hi tau = sigma ∧
        tau.unop.hom ≫ i = i ≫ (pullback f).map sigma.unop.hom := by
  let : IsGalois W := hW
  let : IsGalois Z := hZ
  let F := fiber (xi ≫ f)
  let F' := fiber xi
  let H := pullback f
  let t := pullbackFiberIso f xi
  let phi := galoisPullbackComponentQuotientMonoidHom
    f xi W hW w Z i z hiz hZ hi
  obtain ⟨z', hz'⟩ := hsigma
  obtain ⟨tau, htau⟩ := evaluation_aut_surjective_of_isGalois F' Z z z'
  have hequiv : tau.hom ≫ i = i ≫ H.map ((phi (MulOpposite.op tau)).unop.hom) :=
    galoisPullbackComponentQuotientMonoidHom_equivariant
      f xi W hW w Z i z hiz hZ hi (MulOpposite.op tau)
  have heval :
      F'.map (H.map ((phi (MulOpposite.op tau)).unop.hom)) (F'.map i z) =
        F'.map (H.map sigma.unop.hom) (F'.map i z) := by
    calc
      F'.map (H.map ((phi (MulOpposite.op tau)).unop.hom)) (F'.map i z) =
          F'.map i (F'.map tau.hom z) := by
        have h := congrArg (fun k ↦ F'.map k z) hequiv
        simpa only [Functor.map_comp, FintypeCat.comp_apply] using h.symm
      _ = F'.map i z' := congrArg (F'.map i) htau
      _ = F'.map (H.map sigma.unop.hom) (F'.map i z) := hz'
  have hnat (a : (Aut W)ᵐᵒᵖ) :
      (t.inv.app W) (F.map a.unop.hom w) =
        F'.map (H.map a.unop.hom) (F'.map i z) := by
    have h := ConcreteCategory.congr_hom (t.inv.naturality a.unop.hom) w
    change (t.inv.app W) (F.map a.unop.hom w) =
      F'.map (H.map a.unop.hom)
        (transportedPointOfCompIso H t W w) at h
    rw [← hiz] at h
    exact h
  have hphi : phi (MulOpposite.op tau) = sigma := by
    apply MulOpposite.unop_injective
    apply evaluation_aut_injective_of_isConnected F W w
    have h := congrArg (t.hom.app W)
      ((hnat (phi (MulOpposite.op tau))).trans (heval.trans (hnat sigma).symm))
    have hinv (x : F.obj W) : (t.hom.app W) ((t.inv.app W) x) = x :=
      FintypeCat.inv_hom_id_apply (t.app W) x
    simpa only [hinv] using h
  refine ⟨MulOpposite.op tau, hphi, ?_⟩
  exact hequiv.trans (congrArg (fun a : (Aut W)ᵐᵒᵖ ↦ i ≫ H.map a.unop.hom) hphi)

/-- The image of the component deck group is precisely the setwise
stabilizer of its geometric-fiber range under original deck transformations.
Both directions concern the actual pullback action on the fiber. -/
theorem galoisPullbackComponentQuotientMonoidHom_mem_range_iff_preserves_component
    (sigma : (Aut W)ᵐᵒᵖ) :
    sigma ∈ (galoisPullbackComponentQuotientMonoidHom
        f xi W hW w Z i z hiz hZ hi).range ↔
      (fiber xi).map ((pullback f).map sigma.unop.hom) ''
          Set.range ((fiber xi).map i) = Set.range ((fiber xi).map i) := by
  let F' := fiber xi
  let H := pullback f
  let phi := galoisPullbackComponentQuotientMonoidHom
    f xi W hW w Z i z hiz hZ hi
  constructor
  · rintro ⟨tau, rfl⟩
    have hpoint (a : F'.obj Z) :
        F'.map (H.map ((phi tau).unop.hom)) (F'.map i a) =
          F'.map i (F'.map tau.unop.hom a) := by
      have h := congrArg (fun k ↦ F'.map k a)
        (galoisPullbackComponentQuotientMonoidHom_equivariant
          f xi W hW w Z i z hiz hZ hi tau)
      simpa only [Functor.map_comp, FintypeCat.comp_apply] using h.symm
    apply Set.ext
    intro a
    constructor
    · rintro ⟨b, ⟨c, rfl⟩, rfl⟩
      exact ⟨F'.map tau.unop.hom c, (hpoint c).symm⟩
    · rintro ⟨b, rfl⟩
      refine ⟨F'.map i (F'.map tau.unop.inv b),
        ⟨F'.map tau.unop.inv b, rfl⟩, ?_⟩
      rw [hpoint]
      exact congrArg (F'.map i)
        (FintypeCat.inv_hom_id_apply (F'.mapIso tau.unop) b)
  · intro hset
    have hmem : F'.map (H.map sigma.unop.hom) (F'.map i z) ∈
        Set.range (F'.map i) := by
      rw [← hset]
      exact ⟨F'.map i z, ⟨z, rfl⟩, rfl⟩
    obtain ⟨tau, htau, _⟩ :=
      galoisPullbackComponentQuotient_exists_lift_of_mem_range
        f xi W hW w Z i z hiz hZ hi sigma hmem
    exact ⟨tau, htau⟩

end AlgebraicGeometry.FiniteEtale
