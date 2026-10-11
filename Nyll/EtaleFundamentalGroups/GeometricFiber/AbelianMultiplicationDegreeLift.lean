/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GeometricFiber.ProperGroupScheme
import Nyll.EtaleFundamentalGroups.GeometricFiber.Functoriality
import Nyll.EtaleFundamentalGroups.FiniteEtale.Connected
import Nyll.EtaleFundamentalGroups.FiniteEtale.TrivialBaseChangeAlgebra
import Mathlib.CategoryTheory.Galois.Full
import Mathlib.CategoryTheory.Galois.Topology
import Mathlib.GroupTheory.OrderOfElement

/-!
# Lifting multiplication by the degree through a connected cover

In every characteristic, a connected finite étale cover of a proper smooth
geometrically connected group is dominated by multiplication by its actual
geometric fibre cardinality. Commutativity of the fundamental group makes
its finite monodromy image act freely and transitively; its order is therefore
the degree, without replacing the degree by a factorial.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory
open AlgebraicGeometry AlgebraicGeometry.FiniteEtale

namespace GoodReductionJacobian.RelativeGroupLaw

private theorem pullback_fixed_of_pointed
    {X Y : Scheme} {K : Type} [Field K] [IsSepClosed K]
    (a : X ⟶ Y) (x : Spec (.of K) ⟶ X) (y : Spec (.of K) ⟶ Y)
    (h : x ≫ a = y) (W : FiniteEtale Y)
    (hf : ∀ (g : π₁ᵉᵗ(x)) (w : (fiber y).obj W),
      pointedFundamentalGroupHom a x y h g • w = w) :
    ∀ (g : π₁ᵉᵗ(x)) (w : (fiber x).obj ((FiniteEtale.pullback a).obj W)), g • w = w := by
  subst y
  exact pullback_fiber_fixed_of_image_fixed a x W hf

variable {K : Type} [Field K] [IsSepClosed K]
  {A : Scheme} {f : A ⟶ Spec (.of K)}
  [IsProper f] [Smooth f] [GeometricallyConnected f]
  (G : RelativeGroupLaw K f)

/-- Multiplication by the actual degree lifts to the original connected cover.
No characteristic restriction or isogeny classification of the cover is assumed. -/
theorem exists_schemeNsmul_lift_degree (W : FiniteEtale A) [IsConnected W] :
    ∃ a : A ⟶ W.left,
      a ≫ W.hom = G.schemeNsmul
        (Nat.card ((fiber (G.one (𝟙 (Spec (.of K)))).1).obj W)) := by
  have : ConnectedSpace A := GeometricallyConnected.connectedSpace f f.isOpenMap
  let e : Spec (.of K) ⟶ A := (G.one (𝟙 (Spec (.of K)))).1
  let F := fiber e
  let ev : Aut F →* Aut (F.obj W) :=
    (Pi.evalMonoidHom (fun Z : FiniteEtale A => Aut (F.obj Z)) W).comp (autEmbedding F)
  let x : F.obj W := Classical.choice inferInstance
  let evaluation : ev.range → F.obj W := fun a => a.val.hom x
  have hcomm (a b : ev.range) : a * b = b * a := by
    obtain ⟨g, hg⟩ := a.property
    obtain ⟨h, hh⟩ := b.property
    apply Subtype.ext
    change a.val * b.val = b.val * a.val
    rw [← hg, ← hh, ← map_mul, ← map_mul, G.fundamentalGroup_mul_comm g h]
  have hsurj : Function.Surjective evaluation := by
    intro y
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Aut F) x y
    exact ⟨⟨ev g, ⟨g, rfl⟩⟩, hg⟩
  have hinj : Function.Injective evaluation := by
    intro a b hab
    apply Subtype.ext
    apply Aut.ext
    ext y
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Aut F) x y
    let c : ev.range := ⟨ev g, ⟨g, rfl⟩⟩
    have hy : c.val.hom x = y := hg
    have hac : a.val.hom (c.val.hom x) = c.val.hom (a.val.hom x) :=
      congrArg (fun d : ev.range => d.val.hom x) (hcomm a c)
    have hbc : b.val.hom (c.val.hom x) = c.val.hom (b.val.hom x) :=
      congrArg (fun d : ev.range => d.val.hom x) (hcomm b c)
    rw [← hy, hac, hbc]
    exact congrArg c.val.hom hab
  have hcard : Nat.card ev.range = Nat.card (F.obj W) :=
    Nat.card_congr (Equiv.ofBijective evaluation ⟨hinj, hsurj⟩)
  let n : ℕ := Nat.card (F.obj W)
  have hfixed : ∀ (g : π₁ᵉᵗ(e)) (w : F.obj W),
      pointedFundamentalGroupHom (G.schemeNsmul n) e e
        (G.unit_comp_schemeNsmul n) g • w = w := by
    intro g w
    rw [G.pointedFundamentalGroupHom_schemeNsmul]
    let v : ev.range := ⟨ev g, ⟨g, rfl⟩⟩
    have hp : v ^ n = 1 := by
      have horder : v ^ Nat.card ev.range = 1 := pow_card_eq_one'
      rw [hcard] at horder
      exact horder
    have hv : ev (g ^ n) = 1 := by
      rw [map_pow]
      exact congrArg Subtype.val hp
    change (ev (g ^ n)).hom w = w
    rw [hv]
    rfl
  let P : FiniteEtale A := (FiniteEtale.pullback (G.schemeNsmul n)).obj W
  have hp : ∀ (g : π₁ᵉᵗ(e)) (w : F.obj P), g • w = w :=
    pullback_fixed_of_pointed (G.schemeNsmul n) e e (G.unit_comp_schemeNsmul n) W hfixed
  have hnon : Nonempty ((fiber (e ≫ G.schemeNsmul n)).obj W) := by
    rw [G.unit_comp_schemeNsmul]
    infer_instance
  let t := pullbackFiberIso (G.schemeNsmul n) e
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
  let sectionMap : T ⟶ P := M.preimage q
  let a : A ⟶ Limits.pullback W.hom (G.schemeNsmul n) := sectionMap.left
  have ha : a ≫ pullback.snd W.hom (G.schemeNsmul n) = 𝟙 A := sectionMap.w
  refine ⟨a ≫ pullback.fst W.hom (G.schemeNsmul n), ?_⟩
  change (a ≫ pullback.fst W.hom (G.schemeNsmul n)) ≫ W.hom = G.schemeNsmul n
  rw [Category.assoc, pullback.condition, ← Category.assoc, ha, Category.id_comp]

end GoodReductionJacobian.RelativeGroupLaw
