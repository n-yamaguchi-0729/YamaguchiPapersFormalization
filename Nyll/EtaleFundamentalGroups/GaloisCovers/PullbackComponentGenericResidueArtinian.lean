/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GaloisCovers.FiniteEtaleGenericResidue
import Nyll.SchemeTheory.FiniteEtale.BaseChange.PullbackResidueArtinian

/-!
# Artinian generic residue tensors of pullback components

For a connected component of the pullback of a connected finite-etale
cover along a dense morphism, the residue tensor at the component's generic
point is Artinian.  This is the pointwise finiteness input for comparing the
generic tensor product with the function field of the selected component.
-/

noncomputable section

open CategoryTheory Limits TopologicalSpace
open CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.FiniteEtale

universe u

variable {X Y : Scheme.{u}}

/-- At the generic point of a connected component of a finite-etale
pullback, the categorical tensor of the two projected residue fields is
Artinian. -/
theorem pullbackComponent_genericPoint_tensor_isArtinian
    [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X]
    [IsIntegral Y] [IsNormalIntegral Y] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) (hf : DenseRange f)
    (W : FiniteEtale Y) [IsConnected W]
    (Z : FiniteEtale X) [IsConnected Z]
    (i : Z ⟶ (FiniteEtale.pullback f).obj W) [Mono i] :
    letI : IsIntegral W.left :=
      EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale W
    letI : IsIntegral Z.left :=
      EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale Z
    IsArtinianRing
      (Scheme.Pullback.Triplet.ofPoint
        (i.left (genericPoint Z.left))).tensor := by
  let : IsIntegral W.left :=
    EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale W
  let : IsIntegral Z.left :=
    EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale Z
  let g : Z.left ⟶ W.left :=
    i.left ≫ Limits.pullback.fst W.hom f
  let zHom : Z.left ⟶ X := Z.hom
  let wHom : W.left ⟶ Y := W.hom
  have hZ : DenseRange zHom := by
    let : IsFiniteEtale zHom := by
      simpa only [zHom] using Z.2
    let : Surjective zHom := IsFiniteEtale.surjective zHom
    exact zHom.surjective.denseRange
  have hW : DenseRange wHom := by
    let : IsFiniteEtale wHom := by
      simpa only [wHom] using W.2
    let : Surjective wHom := IsFiniteEtale.surjective wHom
    exact wHom.surjective.denseRange
  have hZf : DenseRange (zHom ≫ f) := by
    change DenseRange (f.base ∘ zHom.base)
    exact hf.comp hZ f.continuous
  have hgW : g ≫ wHom = zHom ≫ f := by
    exact (Category.assoc i.left (Limits.pullback.fst W.hom f) W.hom).trans
      ((congrArg (fun k : Limits.pullback W.hom f ⟶ Y => i.left ≫ k)
        (Limits.pullback.condition (f := W.hom) (g := f))).trans
        ((Category.assoc i.left (Limits.pullback.snd W.hom f) f).symm.trans
          (congrArg (fun k : Z.left ⟶ X => k ≫ f) i.w)))
  have hsource :
      wHom (g (genericPoint Z.left)) = genericPoint Y := by
    change (g ≫ wHom) (genericPoint Z.left) = genericPoint Y
    rw [hgW]
    exact (zHom ≫ f).map_genericPoint_of_denseRange hZf
  have htarget : wHom (genericPoint W.left) = genericPoint Y :=
    wHom.map_genericPoint_of_denseRange hW
  have hgeneric : g (genericPoint Z.left) = genericPoint W.left := by
    symm
    apply (wHom.isDiscrete_preimage_singleton
      (genericPoint Y)).eq_of_specializes
      (genericPoint_specializes (g (genericPoint Z.left)))
    · exact htarget
    · exact hsource
  let t : ((FiniteEtale.pullback f).obj W).left :=
    i.left (genericPoint Z.left)
  let T := Scheme.Pullback.Triplet.ofPoint t
  let T₀ : Scheme.Pullback.Triplet wHom f := {
    x := genericPoint W.left
    y := genericPoint X
    s := wHom (genericPoint W.left)
    hx := rfl
    hy := (f.map_genericPoint_of_denseRange hf).trans htarget.symm }
  have hTx : T.x = genericPoint W.left := by
    change g (genericPoint Z.left) = genericPoint W.left
    exact hgeneric
  have hTy : T.y = genericPoint X := by
    change ((FiniteEtale.pullback f).obj W).hom
      (i.left (genericPoint Z.left)) = genericPoint X
    have hiw := congrArg
      (fun q : Z.left ⟶ X ↦ q (genericPoint Z.left)) i.w
    exact hiw.trans (zHom.map_genericPoint_of_denseRange hZ)
  have hT : T = T₀ := Scheme.Pullback.Triplet.ext hTx hTy
  have hArtinian₀ : IsArtinianRing T₀.tensor := by
    let : Algebra (Y.residueField T₀.s)
        (W.left.residueField T₀.x) :=
      (((Y.residueFieldCongr T₀.hx).inv ≫
        wHom.residueFieldMap T₀.x).hom).toAlgebra
    let : FiniteDimensional (Y.residueField T₀.s)
        (W.left.residueField T₀.x) := by
      dsimp only [T₀, wHom]
      exact
        EtaleFundamentalGroups.finiteDimensional_genericResidueField_of_finiteEtale_isConnected W
    exact
      Scheme.Pullback.Triplet.tensor_isArtinian_of_finiteDimensional_left T₀
  change IsArtinianRing T.tensor
  exact hT.symm ▸ hArtinian₀

end AlgebraicGeometry.FiniteEtale

end
