/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.GeometricFundamentalGroup.LaurentKummerCovers
import Nyll.AnabelianGeometry.GeometricFundamentalGroup.LaurentFundamentalGroupQuotients
import Nyll.EtaleFundamentalGroups.FiniteEtale.Connected
import Nyll.EtaleFundamentalGroups.Pi1.FiniteEtale.GaloisCategory
import Mathlib.CategoryTheory.Galois.Topology
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Cyclic quotients of every order of the actual Laurent fundamental group

The degree-`n` Kummer cover supplies a transitive action on `n` actual geometric points.
Its finite image is cyclic by the already proved geometric quotient theorem. Evaluation
at one point is then injective as well as surjective, so this image has order `n`.
-/

noncomputable section

open CategoryTheory CategoryTheory.PreGaloisCategory
open AlgebraicGeometry AlgebraicGeometry.FiniteEtale
open scoped IsMulCommutative

namespace AnabelianGeometry.GeometricFundamentalGroup

/-- The actual etale fundamental group of the Laurent chart has a cyclic open normal
quotient of every positive order. The quotient is constructed from a Kummer cover. -/
theorem exists_openNormalQuotient_fundamentalGroup_laurent_card
    {K Ω : Type} [Field K] [IsAlgClosed K] [CharZero K] [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of (LaurentPolynomial K)))
    {n : ℕ} (hn : 0 < n) :
    ∃ U : OpenNormalSubgroup π₁ᵉᵗ(ξ),
      IsCyclic (π₁ᵉᵗ(ξ) ⧸ (U : Subgroup π₁ᵉᵗ(ξ))) ∧
        Nat.card (π₁ᵉᵗ(ξ) ⧸ (U : Subgroup π₁ᵉᵗ(ξ))) = n := by
  obtain ⟨Y, hconnected, hdegree⟩ := exists_connected_finite_etale_laurent_of_degree K hn
  have connected : IsConnected Y := isConnected_of_connectedSpace_left Y
  let F := fiber ξ
  let ev : Aut F →* Aut (F.obj Y) :=
    (Pi.evalMonoidHom (fun Z : FiniteEtale (Spec (CommRingCat.of (LaurentPolynomial K))) =>
      Aut (F.obj Z)) Y).comp (autEmbedding F)
  have hev : Continuous ev :=
    (continuous_apply Y).comp (autEmbedding_isClosedEmbedding F).continuous
  have hopen : IsOpen (ev.ker : Set (Aut F)) := by
    change IsOpen (ev ⁻¹' {1})
    exact hev.isOpen_preimage {1} (isOpen_discrete {1})
  let U : OpenNormalSubgroup (Aut F) :=
    { toOpenSubgroup := { toSubgroup := ev.ker, isOpen' := hopen }
      isNormal' := inferInstance }
  have cyclicQuotient : IsCyclic (Aut F ⧸ (U : Subgroup (Aut F))) :=
    isCyclic_openNormalQuotient_fundamentalGroup_laurent ξ U
  let e : (Aut F ⧸ ev.ker) ≃* ev.range := QuotientGroup.quotientKerEquivRange ev
  have cyclicImage : IsCyclic ev.range := isCyclic_of_surjective e.toMonoidHom e.surjective
  let x : F.obj Y := Classical.choice inferInstance
  let evaluation : ev.range → F.obj Y := fun a => a.val.hom x
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
    have hac : a.val.hom (c.val.hom x) = c.val.hom (a.val.hom x) := by
      exact congrArg (fun d : ev.range => d.val.hom x) (mul_comm a c)
    have hbc : b.val.hom (c.val.hom x) = c.val.hom (b.val.hom x) := by
      exact congrArg (fun d : ev.range => d.val.hom x) (mul_comm b c)
    rw [← hy, hac, hbc]
    exact congrArg c.val.hom hab
  refine ⟨U, cyclicQuotient, ?_⟩
  exact (Nat.card_congr e.toEquiv).trans
    ((Nat.card_congr (Equiv.ofBijective evaluation ⟨hinj, hsurj⟩)).trans (hdegree Ω ξ))

end AnabelianGeometry.GeometricFundamentalGroup
