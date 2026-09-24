import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.Flasque.Stacks09sy

/-! # Constant sheaves on irreducible spaces are acyclic (Stacks 02UW)

Stacks 02UW: on an irreducible topological space the higher cohomology of a constant sheaf vanishes
(constant sheaves are flasque).

Source: Stacks 02UW (used in the proof of 02UZ for `d = 0` and for `H^p(X, ℤ_X) = 0`).

## Route

* `TopCat.Sheaf.isFlasque_constantSheaf_of_irreducible`: the constant sheaf
  `A_X = sheafify (const A)` on an irreducible space is flasque. Instead of computing the
  sheafification explicitly we use Mathlib's facts that the unit `φ = toSheafify : const A ⟶ A_X`
  is locally injective and locally surjective, together with separatedness of the sheaf `A_X`:
  given `V ≤ U` and `s ∈ A_X(V)` with `V ≠ ∅`, local surjectivity gives a non-empty `W ⊆ V` and
  `a ∈ A` with `φ_W a = s|_W`; for any other `W' ⊆ V` in the image sieve with witness `t`, either
  `W' = ∅` (then `A_X(W')` is a singleton, being separated for the empty cover) or `W ∩ W' ≠ ∅`
  (irreducibility), and local injectivity on `W ∩ W'` forces `a = t`. Separatedness for the image
  sieve then gives `φ_V a = s`, and `φ_U a ∈ A_X(U)` restricts to `s`. Restrictions into
  `A_X(∅)` are onto because `A_X(∅)` is a singleton.
* `TopCat.Sheaf.H_constantSheaf_subsingleton_of_irreducible`: flasque ⇒ acyclic
  (Stacks 09SY, `TopCat.Sheaf.H_subsingleton_of_isFlasque`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace TopCat.Sheaf

/-- On a sheaf of abelian groups the sections over an open set with no points form a singleton:
the empty sieve covers such an open, and sheaves are separated. -/
theorem subsingleton_obj_of_eq_empty {X : TopCat.{u}}
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (W : Opens X) (hW : (W : Set X) = ∅) (x y : F.obj.obj (op W)) : x = y := by
  refine Sheaf.isSeparated F W ⊥ ?_ x y ?_
  · intro z hz
    have hz' : z ∈ (W : Set X) := hz
    rw [hW] at hz'
    exact hz'.elim
  · intro Y f hf
    exact hf.elim

/-- Stacks 02UW (first half): on an irreducible space the constant sheaf is flasque. -/
theorem isFlasque_constantSheaf_of_irreducible {X : TopCat.{u}} [IrreducibleSpace X]
    (A : AddCommGrpCat.{u}) :
    TopCat.Sheaf.IsFlasque
      ((CategoryTheory.constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj A) := by
  classical
  set J := Opens.grothendieckTopology X with hJ
  let P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u} := (Functor.const _).obj A
  let F : CategoryTheory.Sheaf J AddCommGrpCat.{u} := (constantSheaf J AddCommGrpCat.{u}).obj A
  let φ : P ⟶ F.obj := toSheafify J P
  have hφi : CategoryTheory.Presheaf.IsLocallyInjective J φ :=
    inferInstanceAs (CategoryTheory.Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      (toSheafify (Opens.grothendieckTopology X) ((Functor.const _).obj A)))
  have hφs : CategoryTheory.Presheaf.IsLocallySurjective J φ :=
    inferInstanceAs (CategoryTheory.Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      (toSheafify (Opens.grothendieckTopology X) ((Functor.const _).obj A)))
  -- constant presheaf: restriction maps are the identity
  have hP : ∀ {W W' : (Opens X)ᵒᵖ} (g : W ⟶ W') (a : P.obj W), P.map g a = a := by
    intro W W' g a
    simp [P]
  -- local injectivity of `φ` over a non-empty open
  have hinj : ∀ (W : Opens X) (a b : A), (W : Set X).Nonempty →
      φ.app (op W) a = φ.app (op W) b → a = b := by
    intro W a b ⟨z, hz⟩ h
    have hmem := CategoryTheory.Presheaf.equalizerSieve_mem J φ a b h
    rw [Opens.mem_grothendieckTopology] at hmem
    obtain ⟨W', g, hg, _⟩ := hmem z hz
    have hg' : P.map g.op a = P.map g.op b := hg
    rwa [hP, hP] at hg'
  -- two non-empty opens meet
  have hmeet : ∀ (W W' : Opens X), (W : Set X).Nonempty → (W' : Set X).Nonempty →
      ((W ⊓ W' : Opens X) : Set X).Nonempty := by
    intro W W' hW hW'
    have := (IrreducibleSpace.isIrreducible_univ X).2 W.1 W'.1 W.2 W'.2
      (by simpa using hW) (by simpa using hW')
    simpa using this
  constructor
  intro U V i
  rw [AddCommGrpCat.epi_iff_surjective]
  intro s
  by_cases hV : (V.unop : Set X) = ∅
  · exact ⟨0, subsingleton_obj_of_eq_empty F V.unop hV _ _⟩
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hV
  have hs := CategoryTheory.Presheaf.imageSieve_mem J φ s
  rw [Opens.mem_grothendieckTopology] at hs
  obtain ⟨W, f, ⟨a, ha⟩, hxW⟩ := hs x hx
  -- `ha : φ.app (op W) a = F.obj.map f.op s`
  refine ⟨φ.app U a, ?_⟩
  have key : φ.app V a = s := by
    refine Sheaf.isSeparated F V.unop (CategoryTheory.Presheaf.imageSieve φ s)
      (CategoryTheory.Presheaf.imageSieve_mem J φ s) _ _ ?_
    intro W' f' ⟨t, ht⟩
    -- goal: F.obj.map f'.op (φ.app V a) = F.obj.map f'.op s
    rw [← ht, ← NatTrans.naturality_apply, hP]
    by_cases hW' : (W' : Set X) = ∅
    · exact subsingleton_obj_of_eq_empty F W' hW' _ _
    obtain ⟨y, hy⟩ := Set.nonempty_iff_ne_empty.mpr hW'
    have hat : a = t := by
      apply hinj (W ⊓ W') a t (hmeet W W' ⟨x, hxW⟩ ⟨y, hy⟩)
      have e1 : φ.app (op (W ⊓ W')) a =
          F.obj.map (homOfLE (inf_le_left : W ⊓ W' ≤ W) ≫ f).op s := by
        rw [op_comp, F.obj.map_comp, ConcreteCategory.comp_apply, ← ha,
          ← NatTrans.naturality_apply, hP]
      have e2 : φ.app (op (W ⊓ W')) t =
          F.obj.map (homOfLE (inf_le_right : W ⊓ W' ≤ W') ≫ f').op s := by
        rw [op_comp, F.obj.map_comp, ConcreteCategory.comp_apply, ← ht,
          ← NatTrans.naturality_apply, hP]
      rw [e1, e2]
      congr 2
    rw [hat]
  rw [← NatTrans.naturality_apply, hP, key]

end TopCat.Sheaf

/-- Stacks 02UW: on an irreducible space the higher cohomology of a constant sheaf vanishes. -/
theorem TopCat.Sheaf.H_constantSheaf_subsingleton_of_irreducible {X : TopCat.{u}} [IrreducibleSpace X]
    (A : AddCommGrpCat.{u}) (p : ℕ) (hp : 0 < p) :
    Subsingleton (CategoryTheory.Sheaf.H
      ((CategoryTheory.constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj A) p) := by
  have := TopCat.Sheaf.isFlasque_constantSheaf_of_irreducible (X := X) A
  exact TopCat.Sheaf.H_subsingleton_of_isFlasque _ p hp

end
