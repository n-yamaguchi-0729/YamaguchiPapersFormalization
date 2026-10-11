/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.GaloisCategories.TrivialComposite
import EtaleFundamentalGroups.GeometricFiber.FundamentalGroup
import SchemeTheory.FiniteEtale.Forget.FiniteCoproducts
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.CategoryTheory.Limits.Shapes.Products


/-!
# The algebra of a trivial finite etale cover

The finite terminal-coproduct decomposition supplied by the Galois category
is transported to the actual spectrum of a finite product of the base ring.
-/

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace AlgebraicGeometry.FiniteEtale

universe u


private theorem coproductComparison_component
    {C D : Type*} [Category C] [Category D]
    {ι : Type*} [HasColimitsOfShape (Discrete ι) C] [HasColimitsOfShape (Discrete ι) D]
    (H : C ⥤ D) [PreservesColimitsOfShape (Discrete ι) H]
    {A B W : C} (t : A ≅ B) (e : (∐ fun _ : ι => A) ≅ W) (i : ι) :
    Sigma.ι (fun _ : ι => H.obj B) i ≫
        ((Sigma.mapIso (fun _ : ι => H.mapIso t)).inv ≫
          sigmaComparison H (fun _ : ι => A) ≫ (H.mapIso e).hom) =
      H.map (t.inv ≫ Sigma.ι (fun _ : ι => A) i ≫ e.hom) := by
  simp only [Sigma.ι_mapIso_inv_assoc, Functor.mapIso_inv,
    ι_comp_sigmaComparison_assoc, Functor.mapIso_hom, Functor.map_comp]

/-- A terminal-coproduct decomposition gives an actual spectrum isomorphism
commuting with the structure maps to the affine base. -/
theorem exists_specPi_iso_of_terminal_coproduct
    (R : Type u) [CommRing R] (W : FiniteEtale (Spec (.of R)))
    (ι : Type u) [Finite ι]
    (e : (∐ fun _ : ι => ⊤_ (FiniteEtale (Spec (.of R)))) ≅ W) :
    ∃ E : Spec (.of (ι → R)) ≅ W.left,
      E.hom ≫ W.hom = Spec.map (CommRingCat.ofHom (algebraMap R (ι → R))) := by
  let X := Spec (.of R)
  let H := forget X ⋙ Over.forget X
  let : IsFiniteEtale (𝟙 X) := .mk
  let T : FiniteEtale X := mk (𝟙 X)
  let t : ⊤_ (FiniteEtale X) ≅ T := terminalIsTerminal.uniqueUpToIso
    (MorphismProperty.Over.mkIdTerminal (@IsFiniteEtale : MorphismProperty Scheme.{u}) X)
  let s : (∐ fun _ : ι => X) ≅ W.left :=
    (Sigma.mapIso (fun _ : ι => H.mapIso t)).symm ≪≫
      asIso (sigmaComparison H (fun _ : ι => ⊤_ (FiniteEtale X))) ≪≫ H.mapIso e
  have hs (i : ι) : Sigma.ι (fun _ : ι => X) i ≫ s.hom ≫ W.hom = 𝟙 X := by
    have hi := coproductComparison_component H t e i
    change Sigma.ι (fun _ : ι => X) i ≫ s.hom =
      (t.inv ≫ Sigma.ι (fun _ : ι => ⊤_ (FiniteEtale X)) i ≫ e.hom).left at hi
    have hw : (t.inv ≫ Sigma.ι (fun _ : ι => ⊤_ (FiniteEtale X)) i ≫ e.hom).left ≫
        W.hom = 𝟙 X := (t.inv ≫ Sigma.ι (fun _ : ι => ⊤_ (FiniteEtale X)) i ≫ e.hom).w
    exact (Category.assoc _ _ _).symm.trans ((congrArg (fun f => f ≫ W.hom) hi).trans hw)
  have hd : s.hom ≫ W.hom = sigmaSpec (fun _ : ι => CommRingCat.of R) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (ι → R))) := by
    apply Sigma.hom_ext
    intro i
    have hpi : Sigma.ι (fun _ : ι => X) i ≫ sigmaSpec (fun _ : ι => CommRingCat.of R) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (ι → R))) = 𝟙 X := by
      rw [ι_sigmaSpec_assoc, ← Spec.map_comp]
      exact Spec.map_id _
    exact (hs i).trans hpi.symm
  refine ⟨(asIso (sigmaSpec (fun _ : ι => CommRingCat.of R))).symm ≪≫ s, ?_⟩
  exact (Category.assoc _ _ _).trans
    ((Iso.inv_comp_eq (asIso (sigmaSpec (fun _ : ι => CommRingCat.of R)))).mpr hd)

/-- A finite etale cover on which every fiber automorphism acts trivially is
an actual finite disjoint union of copies of its affine base. -/
theorem exists_specPi_iso_of_fiber_fixed
    (R : Type u) [CommRing R] [ConnectedSpace (Spec (.of R))]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (point : Spec (.of Ω) ⟶ Spec (.of R))
    (W : FiniteEtale (Spec (.of R)))
    (hfixed : ∀ (g : Aut (fiber point)) (w : (fiber point).obj W), g • w = w) :
    ∃ (ι : Type u) (_ : Finite ι) (E : Spec (.of (ι → R)) ≅ W.left),
      E.hom ≫ W.hom = Spec.map (CommRingCat.ofHom (algebraMap R (ι → R))) := by
  obtain ⟨ι, hι, ⟨e⟩⟩ :=
    (PreGaloisCategory.exists_iso_finite_coproduct_terminal_iff_fixed
      (F'' := fiber point) W).mpr hfixed
  let : Finite ι := hι
  let eLift : (∐ fun _ : ULift.{u} ι => ⊤_ (FiniteEtale (Spec (.of R)))) ≅ W :=
    Sigma.reindex (Equiv.ulift : ULift.{u} ι ≃ ι)
      (fun _ : ι => ⊤_ (FiniteEtale (Spec (.of R)))) ≪≫ e
  obtain ⟨E, hE⟩ :=
    exists_specPi_iso_of_terminal_coproduct R W (ULift.{u} ι) eLift
  exact ⟨ULift.{u} ι, inferInstance, E, hE⟩

/-- The coordinate algebra of an actual affine finite etale cover with
trivial fiber action is a finite product of copies of the base ring. -/
theorem exists_algEquiv_pi_of_fiber_fixed
    (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
    [IsFiniteEtale (Spec.map (CommRingCat.ofHom (algebraMap R B)))]
    [ConnectedSpace (Spec (.of R))]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (point : Spec (.of Ω) ⟶ Spec (.of R))
    (hfixed : ∀ (g : Aut (fiber point))
      (w : (fiber point).obj (mk (Spec.map (CommRingCat.ofHom (algebraMap R B))))),
      g • w = w) :
    ∃ (ι : Type u) (_ : Finite ι), Nonempty (B ≃ₐ[R] (ι → R)) := by
  let W : FiniteEtale (Spec (.of R)) :=
    mk (Spec.map (CommRingCat.ofHom (algebraMap R B)))
  obtain ⟨ι, hι, E, hE⟩ := exists_specPi_iso_of_fiber_fixed R point W hfixed
  let : Finite ι := hι
  let eA : CommRingCat.of B ≅ CommRingCat.of (ι → R) :=
    (Scheme.Spec.preimageIso E).unop
  have hmap : Spec.map eA.hom = E.hom := by
    change Scheme.Spec.map (Scheme.Spec.preimage E.hom) = E.hom
    exact Scheme.Spec.map_preimage E.hom
  have hbase : CommRingCat.ofHom (algebraMap R B) ≫ eA.hom =
      CommRingCat.ofHom (algebraMap R (ι → R)) := by
    have hop : (CommRingCat.ofHom (algebraMap R B) ≫ eA.hom).op =
        (CommRingCat.ofHom (algebraMap R (ι → R))).op := by
      apply Scheme.Spec.map_injective
      change Spec.map (CommRingCat.ofHom (algebraMap R B) ≫ eA.hom) = _
      rw [Spec.map_comp, hmap]
      exact hE
    exact congrArg Quiver.Hom.unop hop
  exact ⟨ι, hι, ⟨{ eA.commRingCatIsoToRingEquiv with
    commutes' := fun r => ConcreteCategory.congr_hom hbase r }⟩⟩

end AlgebraicGeometry.FiniteEtale
