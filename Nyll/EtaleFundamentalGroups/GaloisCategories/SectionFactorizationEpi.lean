/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# Section Factorization Epi

Actual factorizations of all terminal sections assemble to an epimorphism
from the image whenever the target becomes a finite coproduct of terminals.
-/

noncomputable section
open CategoryTheory Limits
universe u₁ v₁ u₂ v₂ u₃ v₃
namespace CategoryTheory

/-- Actual factorizations of all terminal sections assemble to an epimorphism
from the image whenever the target becomes a finite coproduct of terminals. -/
theorem exists_epi_of_terminal_section_factorizations
    {C : Type u₁} [Category.{v₁} C] [HasFiniteCoproducts C]
    {D : Type u₂} [Category.{v₂} D] [HasFiniteCoproducts D]
    {E : Type u₃} [Category.{v₃} E] [HasFiniteCoproducts E] [HasTerminal E]
    (H : C ⥤ D) [PreservesFiniteCoproducts H] (K : D ⥤ E) [K.Faithful]
    (Y : D)
    (hsections : ∀ s : ⊤_ E ⟶ K.obj Y,
      ∃ (A : C) (q : H.obj A ⟶ Y) (r : ⊤_ E ⟶ K.obj (H.obj A)),
        r ≫ K.map q = s)
    (hY : ∃ (ι : Type) (_ : Finite ι), Nonempty ((∐ fun _ : ι => ⊤_ E) ≅ K.obj Y)) :
    ∃ (A : C) (q : H.obj A ⟶ Y), Epi q := by
  obtain ⟨ι, hfin, ⟨e⟩⟩ := hY
  let : Finite ι := hfin
  choose A q r hr using fun i : ι => hsections (Sigma.ι (fun _ : ι => ⊤_ E) i ≫ e.hom)
  let qsum : H.obj (∐ A) ⟶ Y := inv (sigmaComparison H A) ≫ Sigma.desc q
  have hq (i : ι) : H.map (Sigma.ι A i) ≫ qsum = q i := by
    dsimp only [qsum]
    rw [map_ι_comp_inv_sigmaComparison_assoc, Sigma.ι_comp_desc]
  refine ⟨∐ A, qsum, ⟨?_⟩⟩
  intro W u v huv
  apply K.map_injective
  apply (cancel_epi e.hom).mp
  apply Sigma.hom_ext
  intro i
  have hi : q i ≫ u = q i ≫ v := by
    have h := congrArg (fun z => H.map (Sigma.ι A i) ≫ z) huv
    simpa only [← Category.assoc, hq i] using h
  calc
    Sigma.ι (fun _ : ι => ⊤_ E) i ≫ e.hom ≫ K.map u =
        r i ≫ K.map (q i) ≫ K.map u := by
      simpa only [Category.assoc] using (congrArg (fun z => z ≫ K.map u) (hr i)).symm
    _ = r i ≫ K.map (q i ≫ u) := by rw [K.map_comp]
    _ = r i ≫ K.map (q i ≫ v) := by rw [hi]
    _ = Sigma.ι (fun _ : ι => ⊤_ E) i ≫ e.hom ≫ K.map v := by
      rw [K.map_comp, ← Category.assoc, hr i, Category.assoc]

end CategoryTheory
