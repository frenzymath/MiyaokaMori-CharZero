import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.GeneratedInDegreeOne
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.OfGradedQCAlgebra
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.TwistPowerIsoSectionsGeneration

/-! # Generated in degree one, on sections

Sections version of "generated in degree one": if the graded quasi-coherent algebra `S` on `X`
is generated in degree one (`S.GeneratedInDegreeOne`: `S_1^{⊗ℓ} → S_ℓ` is an epimorphism of
sheaves for every `ℓ > 0`), then on every affine open `U` the ring of sections
`S(U) = ⊕_m Γ(S_m, U)` is generated, as a ring, by the image of `Γ(X, U)` (the structure map
`sectionsUnitHom`) together with the degree-one part `S(U)_1`.

Source: Stacks 01N0 (constructions-lemma-generated-degree-one-proj-from-sheaf-of-modules /
the definition "generated in degree one" taken on sections).
Used for Stacks 01WC (a projective morphism is proper): it gives the finite-type
hypothesis for Mathlib's `IsProper (Proj.toSpecZero 𝒜)` chart by chart.

Route: the same local-to-affine argument as
`SufficientlyDivisible.toGradedAffineAlgebra` (`TwistPowerIsoSectionsGeneration.lean`, which treats
the Veronese subalgebra and the generating set `A(U)_0 ∪ A(U)_m`), specialised to `S` itself and to
the smaller generating set `range (sectionsUnitHom U) ∪ A(U)_1`. It does **not** use
"epi of quasi-coherent sheaves ⇒ surjective on affine sections" nor
"`Γ(U, F ⊗ G) = Γ(U, F) ⊗ Γ(U, G)`"; it only uses local surjectivity of epimorphisms, the local
description of sections of a sheafification, and the two quasi-coherence facts on basic opens
(`exists_pow_smul_eq_map_basicOpen`, `A(D(f)) = A(U)[1/f]`), plus `IsAffineOpen.isLocalization_basicOpen`
for the structure sheaf.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
open scoped CategoryTheory.MonoidalCategory TensorProduct

noncomputable section

namespace AlgebraicGeometry.Scheme.GradedQCAlgebra

variable {X : AlgebraicGeometry.Scheme.{u}} (S : X.GradedQCAlgebra)

/-- The generating set `range (sectionsUnitHom U) ∪ A(U)_1` of the target statement. -/
def degOneGenSet (U : X.Opens) : Set (S.sectionsRing U) :=
  Set.range (S.sectionsUnitHom U) ∪ (S.sectionsGrading U 1 : Set (S.sectionsRing U))

theorem sectionsUnitHom_mem_closure_degOne (U : X.Opens) (r : Γ(X, U)) :
    S.sectionsUnitHom U r ∈ Subring.closure (S.degOneGenSet U) :=
  Subring.subset_closure (Or.inl ⟨r, rfl⟩)

theorem ofPiece_one_mem_closure_degOne (U : X.Opens) (b : S.sectionsPiece U 1) :
    S.ofPiece U 1 b ∈ Subring.closure (S.degOneGenSet U) :=
  Subring.subset_closure (Or.inr ⟨b, rfl⟩)

/-- Restriction maps `closure(range unit_V ∪ A(V)_1)` into `closure(range unit_U ∪ A(U)_1)`
(`sectionsUnitHom_naturality` for the unit, `sectionsRestrict.map_mem` for the degree-one part). -/
theorem sectionsRestrictHom_mem_closure_degOne {U V : X.Opens} (h : U ≤ V) {x : S.sectionsRing V}
    (hx : x ∈ Subring.closure (S.degOneGenSet V)) :
    S.sectionsRestrictHom h x ∈ Subring.closure (S.degOneGenSet U) := by
  have h1 := Subring.mem_closure_image_of (S.sectionsRestrictHom h) hx
  refine Subring.closure_mono ?_ h1
  rintro y ⟨z, hz, rfl⟩
  rcases hz with ⟨r, rfl⟩ | hz
  · rw [S.sectionsUnitHom_naturality h r]
    exact Or.inl ⟨_, rfl⟩
  · exact Or.inr ((S.sectionsRestrict h).map_mem hz)

/-- `mulPowOne 0 = S.one`; put into the sections ring it is the structure map. -/
theorem ofPiece_mulPowOne_zero_app (C : X.Opens)
    (r : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow (S.part 1) 0, C)) :
    S.ofPiece C 0 ((S.mulPowOne 0).app C r) = S.sectionsUnitHom C r := rfl

/-- `mulPowOne (ℓ+1)` on a pure tensor `y ⊗ b`, put into the sections ring: the product
`mulPowOne ℓ y · b` (`mulPowOne_succ_app'` + `DirectSum.of_mul_of`). -/
theorem ofPiece_mulPowOne_succ_app (ℓ : ℕ) (C : X.Opens)
    (y : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow (S.part 1) ℓ, C)) (b : Γ(S.part 1, C)) :
    S.ofPiece C (ℓ + 1) ((S.mulPowOne (ℓ + 1)).app C
        ((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj
          (AlgebraicGeometry.Scheme.Modules.tensorPow (S.part 1) ℓ) (S.part 1)).inv.app C
          (AlgebraicGeometry.Scheme.Modules.tensorSections
            (AlgebraicGeometry.Scheme.Modules.tensorPow (S.part 1) ℓ) (S.part 1) C y b))) =
      S.ofPiece C ℓ ((S.mulPowOne ℓ).app C y) * S.ofPiece C 1 b := by
  rw [S.mulPowOne_succ_app' ℓ C y b]
  exact (DirectSum.of_mul_of (A := S.sectionsPiece C) ((S.mulPowOne ℓ).app C y) b).symm

/-! ## Local closure predicate and induction on `ℓ` -/

/-- The `mulPowOne ℓ`-image of the section `y`, put into the sections ring, lies in
`closure(range unit_W ∪ A(W)_1)`. -/
def InClOne (ℓ : ℕ) (W : X.Opens)
    (y : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow (S.part 1) ℓ, W)) : Prop :=
  S.ofPiece W ℓ ((S.mulPowOne ℓ).app W y) ∈ Subring.closure (S.degOneGenSet W)

/-- `InClOne` holds near every point. -/
def GoodOne (ℓ : ℕ) (W : X.Opens)
    (y : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow (S.part 1) ℓ, W)) : Prop :=
  ∀ p ∈ W, ∃ (W' : X.Opens) (h : W' ≤ W), p ∈ W' ∧
    S.InClOne ℓ W' ((AlgebraicGeometry.Scheme.Modules.tensorPow (S.part 1) ℓ).presheaf.map
      (homOfLE h).op y)

variable {S}

theorem InClOne.restrict {ℓ : ℕ} {W : X.Opens}
    {y : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow (S.part 1) ℓ, W)}
    (hy : S.InClOne ℓ W y) {W₀ : X.Opens} (h : W₀ ≤ W) :
    S.InClOne ℓ W₀ ((AlgebraicGeometry.Scheme.Modules.tensorPow (S.part 1) ℓ).presheaf.map
      (homOfLE h).op y) := by
  unfold InClOne at hy ⊢
  rw [GenAux.app_map_res]
  have e : S.ofPiece W₀ ℓ ((S.part ℓ).presheaf.map (homOfLE h).op ((S.mulPowOne ℓ).app W y))
      = S.sectionsRestrictHom h (S.ofPiece W ℓ ((S.mulPowOne ℓ).app W y)) :=
    (S.sectionsRestrictHom_ofPiece h ℓ _).symm
  rw [e]
  exact S.sectionsRestrictHom_mem_closure_degOne h hy

theorem InClOne.zero (S : X.GradedQCAlgebra) (ℓ : ℕ) (W : X.Opens) : S.InClOne ℓ W 0 := by
  unfold InClOne
  refine Set.mem_of_eq_of_mem ?_ (Subring.zero_mem _)
  exact (congrArg (S.ofPiece W ℓ)
    (map_zero (ConcreteCategory.hom ((S.mulPowOne ℓ).app W)))).trans
    (map_zero (DirectSum.of (S.sectionsPiece W) ℓ))

theorem InClOne.add {ℓ : ℕ} {W : X.Opens}
    {y₁ y₂ : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow (S.part 1) ℓ, W)}
    (h₁ : S.InClOne ℓ W y₁) (h₂ : S.InClOne ℓ W y₂) : S.InClOne ℓ W (y₁ + y₂) := by
  unfold InClOne at h₁ h₂ ⊢
  refine Set.mem_of_eq_of_mem ?_ (Subring.add_mem _ h₁ h₂)
  exact (congrArg (S.ofPiece W ℓ)
    (map_add (ConcreteCategory.hom ((S.mulPowOne ℓ).app W)) y₁ y₂)).trans
    (map_add (DirectSum.of (S.sectionsPiece W) ℓ) _ _)

theorem GoodOne.of_inClOne {ℓ : ℕ} {W : X.Opens}
    {y : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow (S.part 1) ℓ, W)}
    (hy : S.InClOne ℓ W y) : S.GoodOne ℓ W y :=
  fun _ hp => ⟨W, le_rfl, hp, hy.restrict le_rfl⟩

theorem GoodOne.zero (S : X.GradedQCAlgebra) (ℓ : ℕ) (W : X.Opens) : S.GoodOne ℓ W 0 :=
  GoodOne.of_inClOne (InClOne.zero S ℓ W)

theorem GoodOne.add {ℓ : ℕ} {W : X.Opens}
    {y₁ y₂ : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow (S.part 1) ℓ, W)}
    (h₁ : S.GoodOne ℓ W y₁) (h₂ : S.GoodOne ℓ W y₂) : S.GoodOne ℓ W (y₁ + y₂) := by
  intro p hp
  obtain ⟨W₁, hW₁, hp₁, hIn₁⟩ := h₁ p hp
  obtain ⟨W₂, hW₂, hp₂, hIn₂⟩ := h₂ p hp
  refine ⟨W₁ ⊓ W₂, inf_le_left.trans hW₁, ⟨hp₁, hp₂⟩, ?_⟩
  rw [map_add]
  have e₁ := hIn₁.restrict (W₀ := W₁ ⊓ W₂) inf_le_left
  have e₂ := hIn₂.restrict (W₀ := W₁ ⊓ W₂) inf_le_right
  rw [GenAux.map_map_res] at e₁ e₂
  exact e₁.add e₂

/-- Pure tensors: if `a` satisfies `GoodOne ℓ`, then `a ⊗ b` (put back into `tensorPow (ℓ+1)` via
`tensorIsoTensorObj.inv`) satisfies `GoodOne (ℓ+1)`, since its image is `(image of a) · b` with
`b ∈ A_1`. -/
theorem GoodOne.tmul {ℓ : ℕ} {W : X.Opens}
    {a : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow (S.part 1) ℓ, W)}
    (ha : S.GoodOne ℓ W a) (b : Γ(S.part 1, W)) :
    S.GoodOne (ℓ + 1) W ((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj
        (AlgebraicGeometry.Scheme.Modules.tensorPow (S.part 1) ℓ) (S.part 1)).inv.app W
      (AlgebraicGeometry.Scheme.Modules.tensorSections
        (AlgebraicGeometry.Scheme.Modules.tensorPow (S.part 1) ℓ) (S.part 1) W a b)) := by
  intro p hp
  obtain ⟨W', hW', hpW', hIn⟩ := ha p hp
  refine ⟨W', hW', hpW', ?_⟩
  unfold InClOne at hIn ⊢
  set a' := (AlgebraicGeometry.Scheme.Modules.tensorPow (S.part 1) ℓ).presheaf.map
    (homOfLE hW').op a with ha'
  set b' := (S.part 1).presheaf.map (homOfLE hW').op b with hb'
  have e0 := (GenAux.app_map_res (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj
    (AlgebraicGeometry.Scheme.Modules.tensorPow (S.part 1) ℓ) (S.part 1)).inv
    hW' (AlgebraicGeometry.Scheme.Modules.tensorSections
      (AlgebraicGeometry.Scheme.Modules.tensorPow (S.part 1) ℓ) (S.part 1) W a b)).symm
  rw [GenAux.tensorSections_map] at e0
  have e1 := S.ofPiece_mulPowOne_succ_app ℓ W' a' b'
  refine Set.mem_of_eq_of_mem ((congrArg (fun t => S.ofPiece W' (ℓ + 1)
    ((S.mulPowOne (ℓ + 1)).app W' t)) e0).trans e1) ?_
  exact Subring.mul_mem _ hIn (S.ofPiece_one_mem_closure_degOne W' b')

/-- **Main induction**: every section of `tensorPow (S_1) ℓ` satisfies `GoodOne ℓ`.
`ℓ = 0`: `mulPowOne 0 = S.one`, whose image is `sectionsUnitHom`.
`ℓ + 1`: sections of `Modules.tensor` locally come from the presheaf tensor product (the
sheafification unit is locally surjective); pure tensors by `GoodOne.tmul` and the induction
hypothesis, sums by `GoodOne.add`. -/
theorem goodOne_all (S : X.GradedQCAlgebra) (ℓ : ℕ) : ∀ (W : X.Opens)
    (y : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow (S.part 1) ℓ, W)),
    S.GoodOne ℓ W y := by
  induction ℓ with
  | zero =>
    intro W y
    apply GoodOne.of_inClOne
    unfold InClOne
    rw [S.ofPiece_mulPowOne_zero_app W y]
    exact S.sectionsUnitHom_mem_closure_degOne W y
  | succ ℓ ih =>
    intro W y p hp
    obtain ⟨V, hVW, hpV, z, hz⟩ := GenAux.exists_tensor_unit_app_eq_map
      (AlgebraicGeometry.Scheme.Modules.tensorPow (S.part 1) ℓ) (S.part 1) W y p hp
    have key : ∀ z, S.GoodOne (ℓ + 1) V
        (((_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
          (CategoryTheory.MonoidalCategoryStruct.tensorObj
            ((SheafOfModules.forget X.ringCatSheaf ⋙
              _root_.PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj
                (AlgebraicGeometry.Scheme.Modules.tensorPow (S.part 1) ℓ))
            ((SheafOfModules.forget X.ringCatSheaf ⋙
              _root_.PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj
                (S.part 1)))).app (op V) z) := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero =>
        exact (congrArg (S.GoodOne (ℓ + 1) V) (map_zero _)).mpr (GoodOne.zero S (ℓ + 1) V)
      | tmul a b =>
        exact (congrArg (S.GoodOne (ℓ + 1) V)
          (AlgebraicGeometry.Scheme.Modules.tensorToSheafify_tensorSections _ _ V a b)).mp
          ((ih V a).tmul b)
      | add z₁ z₂ h₁ h₂ =>
        exact (congrArg (S.GoodOne (ℓ + 1) V) (map_add _ z₁ z₂)).mpr (h₁.add h₂)
    have hk := key z
    rw [hz] at hk
    have hk' : S.GoodOne (ℓ + 1) V
        ((AlgebraicGeometry.Scheme.Modules.tensorPow (S.part 1) (ℓ + 1)).presheaf.map
          (homOfLE hVW).op y) := hk
    obtain ⟨W', hW', hpW', hIn⟩ := hk' p hpV
    refine ⟨W', hW'.trans hVW, hpW', ?_⟩
    rw [GenAux.map_map_res] at hIn
    exact hIn

/-! ## Localisation: from `D(f)` back to the affine open `U` -/

variable (S)

/-- Structure-sheaf lift: a section `r ∈ Γ(X, D(f))` becomes, after multiplication by a power of
`f`, the restriction of a section over the affine `U` (`IsAffineOpen.isLocalization_basicOpen`);
stated through `sectionsUnitHom`. -/
theorem exists_pow_mul_eq_restrict_sectionsUnitHom {U : X.Opens}
    (hU : AlgebraicGeometry.IsAffineOpen U) (f : Γ(X, U)) (r : Γ(X, X.basicOpen f)) :
    ∃ (n : ℕ) (r' : Γ(X, U)),
      S.sectionsRestrictHom (X.basicOpen_le f) (S.sectionsUnitHom U r') =
        S.sectionsUnitHom (X.basicOpen f) (X.presheaf.map (homOfLE (X.basicOpen_le f)).op f) ^ n *
          S.sectionsUnitHom (X.basicOpen f) r := by
  have hloc : IsLocalization.Away f Γ(X, X.basicOpen f) := hU.isLocalization_basicOpen f
  obtain ⟨⟨r', ⟨_, n, rfl⟩⟩, hr⟩ := IsLocalization.surj (Submonoid.powers f) r
  refine ⟨n, r', ?_⟩
  rw [S.sectionsUnitHom_naturality (X.basicOpen_le f) r']
  have e : (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom r' =
      r * ((X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom f) ^ n := by
    rw [← map_pow]
    exact hr.symm
  rw [e, map_mul, map_pow]
  exact _root_.mul_comm _ _

/-- **Localisation lift**: an element of the closure over `D(f)`, multiplied by a power of `f`,
is the restriction of an element of the closure over `U`. Induction over `Subring.closure`;
generators by `exists_pow_mul_eq_restrict_sectionsUnitHom` (unit) and
`exists_pow_mul_eq_restrict_ofPiece` (degree one); sums take the sum of the exponents. -/
theorem exists_pow_mul_eq_restrict_of_mem_closure_degOne {U : X.Opens}
    (hU : AlgebraicGeometry.IsAffineOpen U) (f : Γ(X, U)) {z : S.sectionsRing (X.basicOpen f)}
    (hz : z ∈ Subring.closure (S.degOneGenSet (X.basicOpen f))) :
    ∃ (n : ℕ) (w : S.sectionsRing U), w ∈ Subring.closure (S.degOneGenSet U) ∧
      S.sectionsRestrictHom (X.basicOpen_le f) w =
        S.sectionsUnitHom (X.basicOpen f) (X.presheaf.map (homOfLE (X.basicOpen_le f)).op f) ^ n * z := by
  have hres : S.sectionsRestrictHom (X.basicOpen_le f) (S.sectionsUnitHom U f) =
      S.sectionsUnitHom (X.basicOpen f) (X.presheaf.map (homOfLE (X.basicOpen_le f)).op f) :=
    S.sectionsUnitHom_naturality (X.basicOpen_le f) f
  induction hz using Subring.closure_induction with
  | mem y hy =>
    rcases hy with ⟨r, rfl⟩ | ⟨t, rfl⟩
    · obtain ⟨n, r', hr'⟩ := S.exists_pow_mul_eq_restrict_sectionsUnitHom hU f r
      exact ⟨n, S.sectionsUnitHom U r', S.sectionsUnitHom_mem_closure_degOne U r', hr'⟩
    · obtain ⟨n, t', ht'⟩ := S.exists_pow_mul_eq_restrict_ofPiece hU f 1 t
      exact ⟨n, S.ofPiece U 1 t', S.ofPiece_one_mem_closure_degOne U t', ht'⟩
  | zero => exact ⟨0, 0, Subring.zero_mem _, by rw [map_zero, mul_zero]⟩
  | one => exact ⟨0, 1, Subring.one_mem _, by rw [map_one, pow_zero, _root_.one_mul]⟩
  | add y₁ y₂ _ _ ih₁ ih₂ =>
    obtain ⟨n₁, w₁, hw₁, e₁⟩ := ih₁
    obtain ⟨n₂, w₂, hw₂, e₂⟩ := ih₂
    refine ⟨n₁ + n₂, S.sectionsUnitHom U f ^ n₂ * w₁ + S.sectionsUnitHom U f ^ n₁ * w₂, ?_, ?_⟩
    · exact Subring.add_mem _
        (Subring.mul_mem _ (Subring.pow_mem _ (S.sectionsUnitHom_mem_closure_degOne U f) _) hw₁)
        (Subring.mul_mem _ (Subring.pow_mem _ (S.sectionsUnitHom_mem_closure_degOne U f) _) hw₂)
    · rw [map_add, map_mul, map_mul, map_pow, map_pow, hres, e₁, e₂]
      ring
  | neg y _ ih =>
    obtain ⟨n, w, hw, e⟩ := ih
    exact ⟨n, -w, Subring.neg_mem _ hw, by rw [map_neg, e, mul_neg]⟩
  | mul y₁ y₂ _ _ ih₁ ih₂ =>
    obtain ⟨n₁, w₁, hw₁, e₁⟩ := ih₁
    obtain ⟨n₂, w₂, hw₂, e₂⟩ := ih₂
    refine ⟨n₁ + n₂, w₁ * w₂, Subring.mul_mem _ hw₁ hw₂, ?_⟩
    rw [map_mul, e₁, e₂, pow_add]
    ring

end AlgebraicGeometry.Scheme.GradedQCAlgebra

/-- **Generated in degree one, on affine sections.** Let `A = Γ(X, U)`, `S_m(U) = Γ(S.part m, U)`;
`S.sectionsRing U = ⊕_m S_m(U)`, with product induced by `S.mul` (`sectionsGMul`), and
`S.sectionsUnitHom U : A → S(U)` the structure map (`r ↦ of 0 (S.one.app U r)`).

Proof (formalized; Stacks 01N0 taken on sections, with the Stacks 01I8-type localisation
`A(D(f)) = A(U)[1/f]` in place of the H^1-vanishing route):
1. `x = ofPiece ℓ s` with `s ∈ Γ(U, S_ℓ)`. `mulPowOne ℓ : S_1^{⊗ℓ} → S_ℓ` is an epimorphism
   (`hS`), hence locally surjective on sections (`epi_iff_locally_surjective_sections`): every
   `p ∈ U` has a neighbourhood `V` with `s|_V = mulPowOne ℓ (y)`.
2. `goodOne_all`: for every section `y` of the tensor power, near every point the image
   `ofPiece ℓ (mulPowOne ℓ y)` lies in `closure(range unit ∪ A_1)`. Induction on `ℓ`: sections of
   the sheafified tensor product are locally images of the presheaf tensor product
   (Mathlib `isLocallySurjective_toSheafify`), so locally sums of pure tensors;
   `mulPowOne_succ_app'` turns a pure tensor `y ⊗ b` into the product `mulPowOne ℓ y · b`.
3. Shrink to a basic open `D(f) ∋ p` inside `U` (`IsAffineOpen.exists_basicOpen_le`):
   `ofPiece ℓ (s|_{D(f)}) ∈ closure(A(D(f)))`. `exists_pow_mul_eq_restrict_of_mem_closure_degOne`
   lifts: `f^n s` agrees on `D(f)` with some `w ∈ closure(A(U))` (degree-one generators lift by
   quasi-coherence of `S_1`, unit generators by `IsAffineOpen.isLocalization_basicOpen`);
   `exists_pow_mul_eq_zero_of_restrict_eq_zero` (`A(D(f)) = A(U)[1/f]`): `f^N (w − f^n s) = 0`,
   so `f^{N+n} x ∈ closure`.
4. `I := {r ∈ Γ(X, U) | unit(r) · x ∈ closure}` is an ideal containing some `f_p^{e_p}` (`e_p ≥ 1`)
   for every `p`, so the `D(f_p^{e_p})` cover `U`; `U` affine
   (`IsAffineOpen.self_le_iSup_basicOpen_iff`) gives `I = ⊤`, hence `x ∈ closure`.

Edge cases: `U = ∅` — `A(U)` is the zero ring, trivial; `S_1 = 0` — `hS` forces `S_ℓ = 0` for
`ℓ > 0`, trivial; nothing is claimed about degree `0` (`GeneratedInDegreeOne` quantifies only over
`ℓ > 0`), and nothing is needed there. -/
theorem AlgebraicGeometry.Scheme.GradedQCAlgebra.GeneratedInDegreeOne.sectionsGrading_mem_closure
    {X : AlgebraicGeometry.Scheme.{u}} {S : X.GradedQCAlgebra} (hS : S.GeneratedInDegreeOne)
    {U : X.Opens} (hU : AlgebraicGeometry.IsAffineOpen U) {ℓ : ℕ} (hℓ : 0 < ℓ)
    {x : S.sectionsRing U} (hx : x ∈ S.sectionsGrading U ℓ) :
    x ∈ Subring.closure
      (Set.range (S.sectionsUnitHom U) ∪ (S.sectionsGrading U 1 : Set (S.sectionsRing U))) := by
  obtain ⟨s, rfl⟩ := hx
  change S.ofPiece U ℓ s ∈ Subring.closure (S.degOneGenSet U)
  have hepi := (AlgebraicGeometry.Scheme.Modules.epi_iff_locally_surjective_sections
    (S.mulPowOne ℓ)).mp (hS ℓ hℓ)
  -- the ideal `I = {r | unit(r) · x ∈ closure}`
  let I : Ideal Γ(X, U) :=
    { carrier := {r | S.sectionsUnitHom U r * S.ofPiece U ℓ s ∈
        Subring.closure (S.degOneGenSet U)}
      zero_mem' := by
        rw [Set.mem_ofPred_eq, map_zero, zero_mul]
        exact Subring.zero_mem _
      add_mem' := by
        intro r₁ r₂ h₁ h₂
        rw [Set.mem_ofPred_eq] at h₁ h₂ ⊢
        rw [map_add, add_mul]
        exact Subring.add_mem _ h₁ h₂
      smul_mem' := by
        intro c r h
        rw [Set.mem_ofPred_eq] at h ⊢
        rw [smul_eq_mul, map_mul, _root_.mul_assoc]
        exact Subring.mul_mem _ (S.sectionsUnitHom_mem_closure_degOne U c) h }
  have hpt : ∀ p ∈ U, ∃ g : Γ(X, U), g ∈ I ∧ p ∈ X.basicOpen g := by
    intro p hp
    obtain ⟨V, hVU, hpV, y, hy⟩ := hepi U s p hp
    obtain ⟨W', hW'V, hpW', hIn⟩ := S.goodOne_all ℓ V y p hpV
    obtain ⟨f, hfW', hpf⟩ := hU.exists_basicOpen_le (V := W') ⟨p, hpW'⟩ hp
    have hV : X.basicOpen f ≤ U := X.basicOpen_le f
    have hres : S.sectionsRestrictHom hV (S.sectionsUnitHom U f) =
        S.sectionsUnitHom (X.basicOpen f) (X.presheaf.map (homOfLE hV).op f) :=
      S.sectionsUnitHom_naturality hV f
    have hIn2 := hIn.restrict (W₀ := X.basicOpen f) hfW'
    unfold AlgebraicGeometry.Scheme.GradedQCAlgebra.InClOne at hIn2
    rw [AlgebraicGeometry.Scheme.GradedQCAlgebra.GenAux.map_map_res] at hIn2
    have hs : (S.mulPowOne ℓ).app (X.basicOpen f)
        ((AlgebraicGeometry.Scheme.Modules.tensorPow (S.part 1) ℓ).presheaf.map
          (homOfLE (hfW'.trans hW'V)).op y) =
        (S.part ℓ).presheaf.map (homOfLE hV).op s :=
      (AlgebraicGeometry.Scheme.GradedQCAlgebra.GenAux.app_map_res (S.mulPowOne ℓ)
        (hfW'.trans hW'V) y).trans
        ((congrArg (fun t => (S.part ℓ).presheaf.map (homOfLE (hfW'.trans hW'V)).op t) hy).trans
          (AlgebraicGeometry.Scheme.GradedQCAlgebra.GenAux.map_map_res (M := S.part ℓ)
            (hfW'.trans hW'V) hVU s))
    have hIn3 : S.ofPiece (X.basicOpen f) ℓ ((S.part ℓ).presheaf.map (homOfLE hV).op s)
        ∈ Subring.closure (S.degOneGenSet (X.basicOpen f)) :=
      Set.mem_of_eq_of_mem (congrArg (S.ofPiece (X.basicOpen f) ℓ) hs).symm hIn2
    obtain ⟨n, w, hw, hwe⟩ := S.exists_pow_mul_eq_restrict_of_mem_closure_degOne hU f hIn3
    have e4 : S.sectionsRestrictHom hV (S.sectionsUnitHom U f ^ n * S.ofPiece U ℓ s) =
        S.sectionsUnitHom (X.basicOpen f) (X.presheaf.map (homOfLE hV).op f) ^ n *
          S.ofPiece (X.basicOpen f) ℓ ((S.part ℓ).presheaf.map (homOfLE hV).op s) := by
      rw [map_mul, map_pow, hres]
      exact congrArg (S.sectionsUnitHom (X.basicOpen f) (X.presheaf.map (homOfLE hV).op f) ^ n * ·)
        (S.sectionsRestrictHom_ofPiece hV ℓ s)
    have e5 : S.sectionsRestrictHom hV
        (w - S.sectionsUnitHom U f ^ n * S.ofPiece U ℓ s) = 0 := by
      rw [map_sub, hwe, e4, sub_self]
    obtain ⟨N, hN⟩ := S.exists_pow_mul_eq_zero_of_restrict_eq_zero ⟨U, hU⟩ f _ e5
    have e6 : S.sectionsUnitHom U f ^ N * (S.sectionsUnitHom U f ^ n * S.ofPiece U ℓ s) =
        S.sectionsUnitHom U f ^ N * w := by
      rw [mul_sub, sub_eq_zero] at hN
      exact hN.symm
    have hmem : S.sectionsUnitHom U (f ^ (N + n)) * S.ofPiece U ℓ s ∈
        Subring.closure (S.degOneGenSet U) := by
      rw [map_pow, pow_add, _root_.mul_assoc, e6]
      exact Subring.mul_mem _
        (Subring.pow_mem _ (S.sectionsUnitHom_mem_closure_degOne U f) N) hw
    refine ⟨f ^ (N + n + 1), ?_, ?_⟩
    · have : f ^ (N + n) ∈ I := hmem
      rw [pow_succ]
      exact I.mul_mem_right f this
    · rw [X.basicOpen_pow f (Nat.succ_pos _)]
      exact hpf
  have hcov : U ≤ ⨆ g : (I : Set Γ(X, U)), X.basicOpen g.1 := by
    intro p hp
    obtain ⟨g, hgI, hpg⟩ := hpt p hp
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨g, hgI⟩, hpg⟩
  have hspan : Ideal.span (I : Set Γ(X, U)) = ⊤ := hU.self_le_iSup_basicOpen_iff.mp hcov
  rw [Ideal.span_eq] at hspan
  have h1 : (1 : Γ(X, U)) ∈ I := hspan ▸ Submodule.mem_top
  have h1' : S.sectionsUnitHom U 1 * S.ofPiece U ℓ s ∈
      Subring.closure (S.degOneGenSet U) := h1
  rw [map_one, _root_.one_mul] at h1'
  exact h1'

end
