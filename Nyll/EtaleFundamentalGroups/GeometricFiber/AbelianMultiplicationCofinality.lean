/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.MultiplicationMorphisms
import Nyll.EtaleFundamentalGroups.FiniteEtale.Connected
import Nyll.EtaleFundamentalGroups.GeometricFiber.AbelianMultiplicationCover
import Nyll.EtaleFundamentalGroups.GeometricFiber.CanonicalPointedMaps
import Nyll.EtaleFundamentalGroups.GeometricFiber.FundamentalGroup
import Nyll.EtaleFundamentalGroups.GeometricFiber.Functoriality
import Nyll.EtaleFundamentalGroups.GeometricFiber.ProperGroupScheme
import Nyll.EtaleFundamentalGroups.FiniteEtale.TrivialBaseChangeAlgebra
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.CategoryTheory.Galois.Full
import Mathlib.CategoryTheory.Galois.Topology
import Mathlib.GroupTheory.OrderOfElement

/-!
# Cofinality of multiplication covers

Multiplication by the order of a finite fibre permutation group kills its
monodromy action. The actual pullback cover consequently has a section,
constructed by fullness of the finite monodromy functor. This gives an
actual morphism from a multiplication cover to every connected finite
étale cover of the proper smooth group scheme.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory
open AlgebraicGeometry AlgebraicGeometry.FiniteEtale

namespace GoodReductionJacobian.RelativeGroupLaw

private theorem pullback_fixed_of_pointed_fixed
    {X Y : Scheme} {K : Type} [Field K] [IsSepClosed K]
    (f : X ⟶ Y) (x : Spec (.of K) ⟶ X) (y : Spec (.of K) ⟶ Y)
    (h : x ≫ f = y) (W : FiniteEtale Y)
    (hf : ∀ (g : π₁ᵉᵗ(x)) (w : (fiber y).obj W),
      pointedFundamentalGroupHom f x y h g • w = w) :
    ∀ (g : π₁ᵉᵗ(x)) (w : (fiber x).obj ((FiniteEtale.pullback f).obj W)),
      g • w = w := by
  subst y
  exact pullback_fiber_fixed_of_image_fixed f x W hf

variable {K : Type} [Field K] [IsAlgClosed K] [CharZero K]
  {A : Scheme} {f : A ⟶ Spec (.of K)}
  [IsProper f] [Smooth f] [GeometricallyConnected f]
  (G : RelativeGroupLaw K f) (hc : G.IsCommutative)

/-- Every connected finite étale cover is dominated by an actual positive
multiplication cover. No classification of the given cover as an isogeny
is assumed. -/
theorem exists_multiplicationCover_hom (W : FiniteEtale A) [IsConnected W] :
    ∃ n : ℕ+, Nonempty (G.multiplicationCover hc n ⟶ W) := by
  have : ConnectedSpace A := GeometricallyConnected.connectedSpace f f.isOpenMap
  let e : Spec (.of K) ⟶ A := (G.one (𝟙 (Spec (.of K)))).1
  let F := fiber e
  let ev : Aut F →* Aut (F.obj W) :=
    (Pi.evalMonoidHom (fun Z : FiniteEtale A => Aut (F.obj Z)) W).comp (autEmbedding F)
  let n : ℕ+ := ⟨Nat.card (Aut (F.obj W)), Nat.card_pos⟩
  have hfixed : ∀ (g : π₁ᵉᵗ(e)) (w : F.obj W),
      pointedFundamentalGroupHom (G.schemeNsmul (n : ℕ)) e e
        (G.unit_comp_schemeNsmul (n : ℕ)) g • w = w := by
    intro g w
    rw [G.pointedFundamentalGroupHom_schemeNsmul]
    have hv : ev (g ^ (n : ℕ)) = 1 := by
      rw [map_pow]
      exact pow_card_eq_one'
    change (ev (g ^ (n : ℕ))).hom w = w
    rw [hv]
    rfl
  let P : FiniteEtale A := (FiniteEtale.pullback (G.schemeNsmul (n : ℕ))).obj W
  have hp : ∀ (g : π₁ᵉᵗ(e)) (w : F.obj P), g • w = w :=
    pullback_fixed_of_pointed_fixed (G.schemeNsmul (n : ℕ)) e e
      (G.unit_comp_schemeNsmul (n : ℕ)) W hfixed
  have hnon : Nonempty ((fiber (e ≫ G.schemeNsmul (n : ℕ))).obj W) := by
    rw [G.unit_comp_schemeNsmul]
    infer_instance
  let t := pullbackFiberIso (G.schemeNsmul (n : ℕ)) e
  let p : F.obj P := (t.app W).inv (Classical.choice hnon)
  have : IsFiniteEtale (𝟙 A) := IsFiniteEtale.mk
  let T : FiniteEtale A := FiniteEtale.mk (𝟙 A)
  let M := functorToAction F
  let q : M.obj T ⟶ M.obj P :=
    { hom := FintypeCat.homMk (fun _ => p)
      comm := fun g => by
        apply ConcreteCategory.hom_ext
        intro z
        exact (hp g p).symm }
  let s : T ⟶ P := M.preimage q
  let sectionMap : A ⟶ Limits.pullback W.hom (G.schemeNsmul (n : ℕ)) := s.left
  have hs : sectionMap ≫ pullback.snd W.hom (G.schemeNsmul (n : ℕ)) = 𝟙 A := s.w
  refine ⟨n, ⟨MorphismProperty.Over.homMk
    (sectionMap ≫ pullback.fst W.hom (G.schemeNsmul (n : ℕ))) ?_⟩⟩
  change (sectionMap ≫ pullback.fst W.hom (G.schemeNsmul (n : ℕ))) ≫ W.hom =
    G.schemeNsmul (n : ℕ)
  rw [Category.assoc, pullback.condition, ← Category.assoc, hs, Category.id_comp]

end GoodReductionJacobian.RelativeGroupLaw
