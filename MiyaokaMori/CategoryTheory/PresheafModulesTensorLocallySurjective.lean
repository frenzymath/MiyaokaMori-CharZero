import MiyaokaMori.Prelude

/-! # Tensoring a locally surjective map of presheaves of modules stays locally surjective

Let `(C, J)` be a site, `R` a presheaf of commutative rings on `C`, and `f : M ⟶ N` a morphism of
`R`-presheaves of modules that is locally surjective (every section of `N(U)` lifts to `M` on some
covering sieve of `J`). Then for every presheaf of modules `P`, `f ▷ P : M ⊗ P ⟶ N ⊗ P` (sectionwise
tensor product `M(U) ⊗_{R(U)} P(U)`) is locally surjective.

Proof:
1. For `z ∈ N(U) ⊗ P(U)`, show by induction on tensors (`TensorProduct.induction_on`) that the image
   sieve `imageSieve (f ▷ P) z` is covering.
2. `z = 0`: the image sieve is `⊤`.
3. `z = n ⊗ p`: `imageSieve f n` is covering; for `i : V ⟶ U` in it choose `m' ∈ M(V)` with
   `f(m') = n|_V`; then `(f ▷ P)(m' ⊗ p|_V) = n|_V ⊗ p|_V = (n ⊗ p)|_V` (restriction on pure tensors:
   `PresheafOfModules.Monoidal.tensorObj_map_tmul`), so `imageSieve f n ≤ imageSieve (f ▷ P) (n ⊗ p)`.
4. `z = z₁ + z₂`: the intersection of two covering sieves is covering, and on it the sum of lifts of
   `z₁`, `z₂` lifts `z`.

Reference: the standard argument preceding Stacks 01CB, on a general site.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory MonoidalCategory Opposite
open scoped TensorProduct

theorem PresheafOfModules.isLocallySurjective_whiskerRight
    {C : Type*} [Category* C] (J : GrothendieckTopology C) {R : Cᵒᵖ ⥤ CommRingCat.{u}}
    {M N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)} (f : M ⟶ N)
    (P : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))
    [hf : Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf _).map f)] :
    Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf _).map (f ▷ P)) := by
  let f' := (PresheafOfModules.toPresheaf (R ⋙ forget₂ CommRingCat RingCat)).map f
  let t' := (PresheafOfModules.toPresheaf (R ⋙ forget₂ CommRingCat RingCat)).map (f ▷ P)
  refine ⟨fun {U} z ↦ ?_⟩
  change Presheaf.imageSieve t' z ∈ J U
  induction z using TensorProduct.induction_on with
  | zero =>
    apply J.superset_covering (S := ⊤) ?_ (J.top_mem U)
    intro V i _
    exact ⟨0, (map_zero (ConcreteCategory.hom (t'.app (op V)))).trans
      (map_zero (ConcreteCategory.hom (((PresheafOfModules.toPresheaf _).obj (N ⊗ P)).map i.op))).symm⟩
  | tmul n p =>
    apply J.superset_covering ?_ (Presheaf.imageSieve_mem J f' n)
    intro V i hi
    obtain ⟨m', hm'⟩ := hi
    change f.app (op V) m' = N.map i.op n at hm'
    refine ⟨m' ⊗ₜ P.map i.op p, ?_⟩
    change f.app (op V) m' ⊗ₜ[R.obj (op V)] P.map i.op p =
      N.map i.op n ⊗ₜ[R.obj (op V)] P.map i.op p
    rw [hm']
  | add z w hz hw =>
    apply J.superset_covering ?_ (J.intersection_covering hz hw)
    intro V i hi
    obtain ⟨z', hz'⟩ := hi.1
    obtain ⟨w', hw'⟩ := hi.2
    refine ⟨z' + w', ?_⟩
    simp only [map_add, hz', hw']
