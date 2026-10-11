/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GaloisCovers.SelfProduct
import Nyll.EtaleFundamentalGroups.FiniteEtale.Connected
import Nyll.SchemeTheory.FiniteEtale.Forget.FiniteLimits
import Nyll.SchemeTheory.FiniteEtale.Forget.FiniteCoproducts
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-!
# Actual Galois descent of small-etale sheaf sections

A section on a finite etale Galois cover descends exactly when it is fixed
by its deck transformations. The proof uses actual sheaf descent and the
proved decomposition of the cover's self-product into deck graphs.
No Galois/etale cohomology comparison is assumed.
-/

noncomputable section
universe u v
open AlgebraicGeometry CategoryTheory Limits Opposite
open CategoryTheory.PreGaloisCategory

namespace EtaleCohomology

/-- The canonical inclusion of finite etale objects into the small etale site. -/
abbrev finiteEtaleInclusion (X : Scheme.{u}) : FiniteEtale X ⥤ X.Etale :=
  MorphismProperty.Over.changeProp X
    (show (@IsFiniteEtale : MorphismProperty Scheme.{u}) ≤
      (@Etale : MorphismProperty Scheme.{u}) from fun _ _ _ h => h.toEtale)
    (le_refl ⊤)

instance finiteEtaleInclusion_preservesFiniteLimits (X : Scheme.{u}) :
    PreservesFiniteLimits (finiteEtaleInclusion X) := by
  constructor
  intro J _ _
  have : PreservesLimitsOfShape J
      (finiteEtaleInclusion X ⋙ Scheme.Etale.forget X) := by
    change PreservesLimitsOfShape J (FiniteEtale.forget X)
    infer_instance
  exact preservesLimitsOfShape_of_reflects_of_preserves
    (finiteEtaleInclusion X) (Scheme.Etale.forget X)

/-- The actual structure map of a finite etale object to the base site object. -/
abbrev finiteEtaleCoverBaseMap (X : Scheme.{u}) (Y : FiniteEtale X) :
    (finiteEtaleInclusion X).obj Y ⟶ Scheme.Etale.mk (𝟙 X) :=
  MorphismProperty.Over.homMk Y.hom (Category.comp_id Y.hom)

/-- A surjective finite etale structure map is a singleton cover of the base. -/
theorem finiteEtaleCoverBaseMap_covering (X : Scheme.{u}) (Y : FiniteEtale X)
    [Surjective Y.hom] :
    Sieve.generate (Presieve.singleton (finiteEtaleCoverBaseMap X Y)) ∈
      X.smallEtaleTopology (Scheme.Etale.mk (𝟙 X)) := by
  let f := finiteEtaleCoverBaseMap X Y
  have hc : Sieve.ofArrows (fun _ : Unit => (finiteEtaleInclusion X).obj Y)
      (fun _ => f) ∈ X.smallEtaleTopology (Scheme.Etale.mk (𝟙 X)) := by
    apply (Scheme.ofArrows_mem_smallEtaleTopology_iff (fun _ : Unit => f)).mpr
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨y, hy⟩ := Y.hom.surjective x
    exact Set.mem_iUnion.mpr ⟨(), y, hy⟩
  apply X.smallEtaleTopology.superset_covering (R := _) ?_ hc
  intro V g hg
  obtain ⟨a, k, rfl⟩ :=
    (Sieve.mem_ofArrows_iff (fun _ : Unit => (finiteEtaleInclusion X).obj Y)
      (fun _ => f) g).mp hg
  exact (Sieve.generate (Presieve.singleton f)).downward_closed
    (Sieve.le_generate _ _ _ (Presieve.singleton_self _)) k

/-- Restriction to an actual finite etale surjective cover is injective. -/
theorem finiteEtaleSheaf_restrict_injective
    (X : Scheme.{u}) (F : Sheaf X.smallEtaleTopology (Type u))
    (Y : FiniteEtale X) [Surjective Y.hom] :
    Function.Injective (F.obj.map (finiteEtaleCoverBaseMap X Y).op) := by
  have hF : Presieve.IsSheafFor F.obj
      (Presieve.singleton (finiteEtaleCoverBaseMap X Y)) :=
    (Presieve.isSheafFor_iff_generate _).mpr
      ((isSheaf_iff_isSheaf_of_type _ _).mp F.property _
        (finiteEtaleCoverBaseMap_covering X Y))
  exact Presieve.isSeparatedFor_singleton.mp hF.isSeparatedFor

/-- A section pulled back from the base is fixed by every actual deck transformation. -/
theorem finiteEtaleSheaf_restrict_invariant
    (X : Scheme.{u}) (F : Sheaf X.smallEtaleTopology (Type u))
    (Y : FiniteEtale X) (t : F.obj.obj (op (Scheme.Etale.mk (𝟙 X))))
    (σ : Aut Y) :
    F.obj.map ((finiteEtaleInclusion X).map σ.hom).op
      (F.obj.map (finiteEtaleCoverBaseMap X Y).op t) =
        F.obj.map (finiteEtaleCoverBaseMap X Y).op t := by
  have h : (finiteEtaleInclusion X).map σ.hom ≫ finiteEtaleCoverBaseMap X Y =
      finiteEtaleCoverBaseMap X Y := by
    apply MorphismProperty.Over.Hom.ext
    exact σ.hom.w
  rw [← ConcreteCategory.comp_apply, ← F.obj.map_comp, ← op_comp, h]

/-- Sections on the actual finite coproduct are determined by their
restrictions to its summands. Covering is proved on the underlying schemes. -/
theorem finiteEtale_sheaf_coproduct_sections_ext
    (X : Scheme.{u}) (F : Sheaf X.smallEtaleTopology (Type u))
    {ι : Type v} [Finite ι] (A : ι → FiniteEtale X)
    (s t : F.obj.obj (op ((finiteEtaleInclusion X).obj (∐ A))))
    (h : ∀ i, F.obj.map ((finiteEtaleInclusion X).map (Sigma.ι A i)).op s =
      F.obj.map ((finiteEtaleInclusion X).map (Sigma.ι A i)).op t) : s = t := by
  let I : FiniteEtale X ⥤ X.Etale := finiteEtaleInclusion X
  let T : FiniteEtale X ⥤ Type u :=
    FiniteEtale.forget X ⋙ Over.forget X ⋙ Scheme.forgetToTop ⋙ forget TopCat
  let j : ∀ i, I.obj (A i) ⟶ I.obj (∐ A) := fun i => I.map (Sigma.ι A i)
  have hcover : Sieve.ofArrows (fun i => I.obj (A i)) j ∈
      X.smallEtaleTopology (I.obj (∐ A)) := by
    apply (Scheme.ofArrows_mem_smallEtaleTopology_iff j).mpr
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨i, a, ha⟩ := Types.jointly_surjective_of_isColimit
      (isColimitOfHasCoproductOfPreservesColimit T A) x
    exact Set.mem_iUnion.mpr ⟨i.as, a, ha⟩
  apply (((isSheaf_iff_isSheaf_of_type _ _).mp F.property).isSeparated _ hcover).ext
  intro V g hg
  obtain ⟨i, k, rfl⟩ := (Sieve.mem_ofArrows_iff (fun i => I.obj (A i)) j g).mp hg
  rw [op_comp, F.obj.map_comp]
  exact congrArg (F.obj.map k.op) (h i)

/-- Every deck-invariant section on an actual finite etale Galois cover
descends uniquely to the base in the actual small etale sheaf. -/
theorem existsUnique_section_of_galois_invariant
    (X : Scheme.{u}) [ConnectedSpace X]
    (F : Sheaf X.smallEtaleTopology (Type u))
    (Y : FiniteEtale X) [IsGalois Y]
    (s : F.obj.obj (op ((finiteEtaleInclusion X).obj Y)))
    (hs : ∀ σ : Aut Y,
      F.obj.map ((finiteEtaleInclusion X).map σ.hom).op s = s) :
    ∃! t : F.obj.obj (op (Scheme.Etale.mk (𝟙 X))),
      F.obj.map (finiteEtaleCoverBaseMap X Y).op t = s := by
  let I : FiniteEtale X ⥤ X.Etale := finiteEtaleInclusion X
  have hcompat : F.obj.map (I.map (prod.fst : Y ⨯ Y ⟶ Y)).op s =
      F.obj.map (I.map (prod.snd : Y ⨯ Y ⟶ Y)).op s := by
    apply (F.obj.mapIso (I.mapIso (galoisSelfProductIso Y)).op).toEquiv.injective
    apply finiteEtale_sheaf_coproduct_sections_ext X F (fun _ : Aut Y => Y)
    intro σ
    have hl : Sigma.ι (fun _ : Aut Y => Y) σ ≫
        (galoisSelfProductIso Y).hom ≫ prod.fst = 𝟙 Y := by
      rw [← Category.assoc, galoisSelfProductIso_ι, prod.lift_fst]
    have hr : Sigma.ι (fun _ : Aut Y => Y) σ ≫
        (galoisSelfProductIso Y).hom ≫ prod.snd = σ.hom := by
      rw [← Category.assoc, galoisSelfProductIso_ι, prod.lift_snd]
    change F.obj.map (I.map (Sigma.ι (fun _ : Aut Y => Y) σ)).op
        (F.obj.map (I.map (galoisSelfProductIso Y).hom).op
          (F.obj.map (I.map prod.fst).op s)) =
      F.obj.map (I.map (Sigma.ι (fun _ : Aut Y => Y) σ)).op
        (F.obj.map (I.map (galoisSelfProductIso Y).hom).op
          (F.obj.map (I.map prod.snd).op s))
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
      hl, hr]
    rw [I.map_id, op_id, F.obj.map_id]
    exact (hs σ).symm
  have : ConnectedSpace Y.left := FiniteEtale.connectedSpace_left_of_isConnected Y
  have : Surjective Y.hom :=
    IsFiniteEtale.surjective (show Y.left ⟶ X from Y.hom)
  have hF : Presieve.IsSheafFor F.obj
      (Presieve.singleton (finiteEtaleCoverBaseMap X Y)) :=
    (Presieve.isSheafFor_iff_generate _).mpr
      ((isSheaf_iff_isSheaf_of_type _ _).mp F.property _
        (finiteEtaleCoverBaseMap_covering X Y))
  apply (Presieve.isSheafFor_singleton.mp hF) s
  intro Z p q _hpq
  let hlim := isLimitOfHasBinaryProductOfPreservesLimit I Y Y
  let l : Z ⟶ I.obj (Y ⨯ Y) := hlim.lift (BinaryFan.mk p q)
  have hp : l ≫ I.map prod.fst = p := hlim.fac (BinaryFan.mk p q) ⟨.left⟩
  have hq : l ≫ I.map prod.snd = q := hlim.fac (BinaryFan.mk p q) ⟨.right⟩
  calc
    F.obj.map p.op s = F.obj.map l.op (F.obj.map (I.map prod.fst).op s) := by
      rw [← hp, op_comp, F.obj.map_comp]
      rfl
    _ = F.obj.map l.op (F.obj.map (I.map prod.snd).op s) := congrArg _ hcompat
    _ = F.obj.map q.op s := by
      rw [← hq, op_comp, F.obj.map_comp]
      rfl

end EtaleCohomology
