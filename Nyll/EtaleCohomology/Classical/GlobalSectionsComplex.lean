/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
import Mathlib.Algebra.Category.Grp.Ulift
import Mathlib.Algebra.Homology.Additive
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Sheaf


/-!
# The constant-integer Hom complex and actual global sections

For a complex `K` of abelian sheaves on the small étale site, the Hom complex
from the constant integer sheaf in degree zero identifies naturally with
the complex obtained by taking actual global sections degreewise.

The raw Hom complex lives in the universe of sheaf morphisms, `u + 1`.
The existing sections remain in `AddCommGrpCat.{u}`; the target uses the
canonical `AddCommGrpCat.uliftFunctor` to express that universe boundary.
No new sheaf-cohomology definition or derived comparison is assumed.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite
open CochainComplex HomComplex

namespace EtaleCohomology

private lemma uliftIntegerHomEquiv_naturality
    {A B : AddCommGrpCat.{u}} (a : AddCommGrpCat.of (ULift.{u} ℤ) ⟶ A) (f : A ⟶ B) :
    AddCommGrpCat.uliftZMultiplesAddEquiv B (a ≫ f) =
      f (AddCommGrpCat.uliftZMultiplesAddEquiv A a) := by
  change (a ≫ f) (ULift.up (1 : ℤ)) = f (a (ULift.up (1 : ℤ)))
  exact CategoryTheory.comp_apply a f (ULift.up (1 : ℤ))

variable (X : Scheme.{u})

local notation "T" => (⊤_ X.Etale)

private def integerHomSectionsEquiv (F : (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})) :
    (((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ))) ⟶ F) ≃+ F.obj.obj (op T) :=
  ((constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u} terminalIsTerminal).homAddEquiv
    (AddCommGrpCat.of (ULift.{u} ℤ)) F).trans (AddCommGrpCat.uliftZMultiplesAddEquiv _)

private lemma integerHomSectionsEquiv_naturality
    {F G : (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})}
    (a : ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ))) ⟶ F) (φ : F ⟶ G) :
    integerHomSectionsEquiv X G (a ≫ φ) =
      φ.hom.app (op T) (integerHomSectionsEquiv X F a) := by
  change (AddCommGrpCat.uliftZMultiplesAddEquiv _)
      ((constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u} terminalIsTerminal).homEquiv
        (AddCommGrpCat.of (ULift.{u} ℤ)) G (a ≫ φ)) =
    φ.hom.app (op T) ((AddCommGrpCat.uliftZMultiplesAddEquiv _)
      ((constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u} terminalIsTerminal).homEquiv
        (AddCommGrpCat.of (ULift.{u} ℤ)) F a))
  rw [Adjunction.homEquiv_naturality_right]
  exact uliftIntegerHomEquiv_naturality
    (A := F.obj.obj (op T)) (B := G.obj.obj (op T))
    ((constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u} terminalIsTerminal).homEquiv
      (AddCommGrpCat.of (ULift.{u} ℤ)) F a) (φ.hom.app (op T))

private def cochainSectionsEquiv
    (K : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) ℤ) (n : ℤ) :
    Cochain ((CochainComplex.singleFunctor (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) 0).obj
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ)))) K n ≃+
      (K.X n).obj.obj (op T) :=
  (Cochain.fromSingleEquiv (zero_add n)).trans (integerHomSectionsEquiv X (K.X n))

private lemma cochainSectionsEquiv_d
    (K : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) ℤ) (i j : ℤ)
    (z : Cochain
      ((CochainComplex.singleFunctor (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) 0).obj
        ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
          (AddCommGrpCat.of (ULift.{u} ℤ)))) K i) :
    cochainSectionsEquiv X K j (HomComplex.δ i j z) =
      (K.d i j).hom.app (op T) (cochainSectionsEquiv X K i z) := by
  obtain ⟨a, rfl⟩ := Cochain.fromSingleMk_surjective z i (zero_add i)
  have hδ : HomComplex.δ i j (Cochain.fromSingleMk a (zero_add i)) =
      Cochain.fromSingleMk (a ≫ K.d i j) (zero_add j) :=
    Cochain.δ_fromSingleMk a (zero_add i) j j (zero_add j)
  simp only [cochainSectionsEquiv, AddEquiv.trans_apply, hδ,
    Cochain.fromSingleEquiv_fromSingleMk]
  exact integerHomSectionsEquiv_naturality X a (K.d i j)

private lemma cochainSectionsEquiv_postcomp
    {K L : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) ℤ} (φ : K ⟶ L) (n : ℤ)
    (z : Cochain
      ((CochainComplex.singleFunctor (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) 0).obj
        ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
          (AddCommGrpCat.of (ULift.{u} ℤ)))) K n) :
    cochainSectionsEquiv X L n (z.comp (Cochain.ofHom φ) (add_zero n)) =
      (φ.f n).hom.app (op T) (cochainSectionsEquiv X K n z) := by
  obtain ⟨a, rfl⟩ := Cochain.fromSingleMk_surjective z n (zero_add n)
  rw [← Cochain.fromSingleMk_postcomp]
  simp only [cochainSectionsEquiv, AddEquiv.trans_apply, Cochain.fromSingleEquiv_fromSingleMk]
  exact integerHomSectionsEquiv_naturality X a (φ.f n)

/-- The actual Hom complex from the constant integer sheaf in degree zero.
Its maps are ordinary postcomposition of cochains by the given chain map. -/
def etaleHomFromIntegerFunctor :
    CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) ℤ ⥤
      CochainComplex AddCommGrpCat.{u + 1} ℤ where
  obj K := CochainComplex.HomComplex
    ((CochainComplex.singleFunctor (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) 0).obj
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ)))) K
  map φ :=
    { f := fun n => AddCommGrpCat.ofHom
        { toFun := fun z => z.comp (Cochain.ofHom φ) (add_zero n)
          map_zero' := Cochain.zero_comp _ _
          map_add' := fun z w => Cochain.add_comp z w (Cochain.ofHom φ) (add_zero n) }
      comm' := fun i j _ => by
        apply AddCommGrpCat.hom_ext
        apply AddMonoidHom.ext
        intro z
        exact HomComplex.δ_comp_ofHom z φ j }
  map_id K := by
    apply HomologicalComplex.hom_ext
    intro n
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro z
    exact Cochain.comp_id z
  map_comp φ ψ := by
    apply HomologicalComplex.hom_ext
    intro n
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro z
    change z.comp (Cochain.ofHom (φ ≫ ψ)) (add_zero n) =
      (z.comp (Cochain.ofHom φ) (add_zero n)).comp (Cochain.ofHom ψ) (add_zero n)
    rw [Cochain.ofHom_comp]
    exact (Cochain.comp_assoc_of_second_is_zero_cochain z
      (Cochain.ofHom φ) (Cochain.ofHom ψ) (add_zero n)).symm

private def homFromIntegerSectionsIso
    (K : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) ℤ) :
    (etaleHomFromIntegerFunctor X).obj K ≅
      ((((sheafSections X.smallEtaleTopology AddCommGrpCat.{u}).obj (op T)) ⋙
        AddCommGrpCat.uliftFunctor.{u + 1, u}).mapHomologicalComplex (ComplexShape.up ℤ)).obj K :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => ((cochainSectionsEquiv X K n).trans AddEquiv.ulift.symm).toAddCommGrpIso)
    (by
      intro i j _
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro z
      change ULift.up ((K.d i j).hom.app (op T) (cochainSectionsEquiv X K i z)) =
        ULift.up (cochainSectionsEquiv X K j (HomComplex.δ i j z))
      exact congrArg ULift.up (cochainSectionsEquiv_d X K i j z).symm)

/-- The natural cochain isomorphism from the raw constant-integer Hom complex
to the canonical universe lift of the existing global-sections complex.
The underlying coefficient sheaves and their section groups remain in universe `u`. -/
def etaleHomFromIntegerSectionsIso :
    etaleHomFromIntegerFunctor X ≅
      (((sheafSections X.smallEtaleTopology AddCommGrpCat.{u}).obj (op T)) ⋙
        AddCommGrpCat.uliftFunctor.{u + 1, u}).mapHomologicalComplex (ComplexShape.up ℤ) :=
  NatIso.ofComponents (homFromIntegerSectionsIso X) (by
    intro K L φ
    apply HomologicalComplex.hom_ext
    intro n
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro z
    change ULift.up (cochainSectionsEquiv X L n
        (z.comp (Cochain.ofHom φ) (add_zero n))) =
      ULift.up ((φ.f n).hom.app (op T) (cochainSectionsEquiv X K n z))
    exact congrArg ULift.up (cochainSectionsEquiv_postcomp X φ n z))

end EtaleCohomology
