import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjLiftEvaluationTwistFamilyAbsoluteFracGerm

/-! # The section maps `θ_n : Γ(U, O(n)) → Γ(φ⁻¹U, O_Y)`, `a/d ↦ Φ(a)Φ(d)⁻¹` (Stacks 01O4 (2))

Helper module for `RelativeProjLiftEvaluationTwistFamilyAbsolute.lean` (existence of the twist family). Setting: `𝒜` a graded ring, `Φ : A →+* Γ(Y, O)` with
`Φ(irrelevant) = (1)`, `φ := Proj.fromOfGlobalSections 𝒜 Φ hΦ : Y ⟶ Proj 𝒜`.

For `g ∈ Γ(U, O(n))` we construct `θ_n g ∈ Γ(φ⁻¹U, O_Y)`, characterized by the **germ predicate** `ThetaPred`:
whenever `g` is the fraction `a/d` on an open `W ∋ φ(t)` (`d` of positive degree), `germ_t(θ_n g) · Φ(d) = Φ(a)`
in `O_{Y,t}`.
* Uniqueness (`thetaPred_unique`): `Φ(d)` is a unit at `t ∈ φ⁻¹D₊(d)`, every section is locally such a fraction
  (`exists_res_eq_res_fracSection`), and sections of `O_Y` are determined by their germs.
* Existence (`thetaPred_exists`): the local sections `Φ(a)Φ(d)⁻¹` on `φ⁻¹W` glue (sheaf axiom); they are compatible
  because two fraction representations of `g` satisfy `Φ(a)Φ(d') = Φ(a')Φ(d)` at every germ (`germ_mul_eq_of_res_fracSection_eq`).
* `thetaPredAt_of_rep`: one representation suffices to verify the predicate at `t`.
* Properties, all by uniqueness: additive (`thetaSection_add`), `φ^♯`-linear (`thetaSection_smul`, through the bridge
  `germ_app_mul_eq_of_res_eq_mk`), natural in `U` (`thetaSection_res`), multiplicative for the pointwise product of
  fractions (`thetaSection_mul`, Stacks 01MO), and `θ_n(a/1) = Φ(a)` (`thetaSection_twistSection`).

The morphisms `θ_n : O(n) ⟶ φ_*O_Y` and their transposes `χ_n : φ^*O(n) ⟶ O_Y` are assembled in
`…AbsoluteThetaHom.lean`. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Proj.TwistFamily

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
  {Y : AlgebraicGeometry.Scheme.{u}} (Φ : A →+* Γ(Y, ⊤))
  (hΦ : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map Φ = ⊤)

/-- Restriction of sections of `O(n)` in two steps. -/
theorem res_res_twist (n : ℤ) {U₁ U₂ U₃ : (AlgebraicGeometry.Proj 𝒜).Opens} (h : U₂ ≤ U₁) (h' : U₃ ≤ U₂)
    (x : Γ(AlgebraicGeometry.Proj.twist 𝒜 n, U₁)) :
    (AlgebraicGeometry.Proj.twist 𝒜 n).presheaf.map (homOfLE h').op
        ((AlgebraicGeometry.Proj.twist 𝒜 n).presheaf.map (homOfLE h).op x) =
      (AlgebraicGeometry.Proj.twist 𝒜 n).presheaf.map (homOfLE (h'.trans h)).op x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- Cancellation in a commutative ring: `x·D = a`, `x'·D' = a'`, `a·D' = a'·D` with `D, D'` units give `x = x'`. -/
theorem cancel_aux {R : Type*} [CommRing R] {x x' D D' a a' : R} (hD : IsUnit D) (hD' : IsUnit D')
    (h : x * D = a) (h' : x' * D' = a') (hk : a * D' = a' * D) : x = x' := by
  apply (hD.mul hD').mul_left_injective
  show x * (D * D') = x' * (D * D')
  linear_combination D' * h - D * h' + hk

/-- **The germ predicate at `t`** for `r ∈ Γ(B, O_Y)` to be "`θ_n g` at `t`": for every open `W ≤ U` containing
`φ(t)` on which `g` is the fraction `a/d` (`a ∈ 𝒜 p`, `d ∈ 𝒜 q`, `p = q + n`, `0 < q`, `W ≤ D₊(d)`),
`germ_t r · germ_t Φ(d) = germ_t Φ(a)` in `O_{Y,t}`. -/
def ThetaPredAt (n : ℕ) {U : (AlgebraicGeometry.Proj 𝒜).Opens} (g : Γ(AlgebraicGeometry.Proj.twist 𝒜 (n : ℤ), U))
    {B : Y.Opens} (r : Γ(Y, B)) (t : Y) (ht : t ∈ B) : Prop :=
  ∀ (W : (AlgebraicGeometry.Proj 𝒜).Opens) (hWU : W ≤ U) (p q : ℕ) (a d : A) (ha : a ∈ 𝒜 p) (hd : d ∈ 𝒜 q)
    (hpq : (p : ℤ) = q + n), 0 < q → ∀ (hW : W ≤ AlgebraicGeometry.Proj.basicOpen 𝒜 d),
    (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ).base t ∈ W →
    (AlgebraicGeometry.Proj.twist 𝒜 (n : ℤ)).presheaf.map (homOfLE hWU).op g =
      (AlgebraicGeometry.Proj.twist 𝒜 (n : ℤ)).presheaf.map (homOfLE hW).op
        (AlgebraicGeometry.Proj.fracSection 𝒜 (n : ℤ) a d ha hd hpq) →
    Y.presheaf.germ B t ht r * Y.presheaf.germ ⊤ t trivial (Φ d) = Y.presheaf.germ ⊤ t trivial (Φ a)

/-- **The germ predicate** on `B`: `ThetaPredAt` at every point of `B`. -/
def ThetaPred (n : ℕ) {U : (AlgebraicGeometry.Proj 𝒜).Opens} (g : Γ(AlgebraicGeometry.Proj.twist 𝒜 (n : ℤ), U))
    (B : Y.Opens) (r : Γ(Y, B)) : Prop :=
  ∀ (t : Y) (ht : t ∈ B), ThetaPredAt 𝒜 Φ hΦ n g r t ht

variable {𝒜 Φ hΦ}

/-- **One representation suffices.** If `g` is the fraction `α/δ` on some open `W₀ ∋ φ(t)`, `Φ(δ)` is a unit at `t`
and `germ_t r · Φ(δ) = Φ(α)`, then the predicate holds at `t` for every representation: two representations of `g`
near `φ(t)` satisfy `Φ(a)Φ(δ) = Φ(α)Φ(d)` at `t` (`germ_mul_eq_of_res_fracSection_eq`), and `Φ(δ)` cancels. -/
theorem thetaPredAt_of_rep (n : ℕ) {U : (AlgebraicGeometry.Proj 𝒜).Opens}
    (g : Γ(AlgebraicGeometry.Proj.twist 𝒜 (n : ℤ), U)) {B : Y.Opens} (r : Γ(Y, B)) (t : Y) (ht : t ∈ B)
    {W₀ : (AlgebraicGeometry.Proj 𝒜).Opens} (hW₀U : W₀ ≤ U) {p₀ q₀ : ℕ} {α δ : A} (hα : α ∈ 𝒜 p₀) (hδ : δ ∈ 𝒜 q₀)
    (hpq₀ : (p₀ : ℤ) = q₀ + n) (hW₀ : W₀ ≤ AlgebraicGeometry.Proj.basicOpen 𝒜 δ)
    (htW₀ : (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ).base t ∈ W₀)
    (hrep : (AlgebraicGeometry.Proj.twist 𝒜 (n : ℤ)).presheaf.map (homOfLE hW₀U).op g =
      (AlgebraicGeometry.Proj.twist 𝒜 (n : ℤ)).presheaf.map (homOfLE hW₀).op
        (AlgebraicGeometry.Proj.fracSection 𝒜 (n : ℤ) α δ hα hδ hpq₀))
    (hunit : IsUnit (Y.presheaf.germ ⊤ t trivial (Φ δ)))
    (heq : Y.presheaf.germ B t ht r * Y.presheaf.germ ⊤ t trivial (Φ δ) = Y.presheaf.germ ⊤ t trivial (Φ α)) :
    ThetaPredAt 𝒜 Φ hΦ n g r t ht := by
  intro W hWU p q a d ha hd hpq _ hW htW hg
  have e1 := congrArg ((AlgebraicGeometry.Proj.twist 𝒜 (n : ℤ)).presheaf.map
    (homOfLE (inf_le_left : W ⊓ W₀ ≤ W)).op) hg
  have e2 := congrArg ((AlgebraicGeometry.Proj.twist 𝒜 (n : ℤ)).presheaf.map
    (homOfLE (inf_le_right : W ⊓ W₀ ≤ W₀)).op) hrep
  simp only at e1 e2
  rw [res_res_twist, res_res_twist] at e1 e2
  have hkey := germ_mul_eq_of_res_fracSection_eq 𝒜 Φ hΦ (n : ℤ) ha hd hpq hα hδ hpq₀
    (inf_le_left.trans hW) (inf_le_right.trans hW₀) (e1.symm.trans e2) t ⟨htW, htW₀⟩
  apply hunit.mul_left_injective
  show Y.presheaf.germ B t ht r * Y.presheaf.germ ⊤ t trivial (Φ d) * Y.presheaf.germ ⊤ t trivial (Φ δ) =
    Y.presheaf.germ ⊤ t trivial (Φ a) * Y.presheaf.germ ⊤ t trivial (Φ δ)
  linear_combination (Y.presheaf.germ ⊤ t trivial (Φ d)) * heq - hkey

/-- **Uniqueness**: two sections of `O_Y` over `B ≤ φ⁻¹U` satisfying the germ predicate for `g` are equal. -/
theorem thetaPred_unique (n : ℕ) {U : (AlgebraicGeometry.Proj 𝒜).Opens}
    (g : Γ(AlgebraicGeometry.Proj.twist 𝒜 (n : ℤ), U)) {B : Y.Opens}
    (hB : B ≤ AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ ⁻¹ᵁ U) {r r' : Γ(Y, B)}
    (h : ThetaPred 𝒜 Φ hΦ n g B r) (h' : ThetaPred 𝒜 Φ hΦ n g B r') : r = r' := by
  apply TopCat.Presheaf.section_ext Y.sheaf B r r'
  intro t ht
  obtain ⟨W, htW, hWU, p, q, a, d, ha, hd, hpq, hq, hW, hg⟩ := exists_res_eq_res_fracSection 𝒜 Φ hΦ n g t (hB ht)
  have hu : IsUnit (Y.presheaf.germ ⊤ t trivial (Φ d)) := isUnit_germ_of_not_mem 𝒜 Φ hΦ hq hd t (hW htW)
  apply hu.mul_left_injective
  exact (h t ht W hWU p q a d ha hd hpq hq hW htW hg).trans (h' t ht W hWU p q a d ha hd hpq hq hW htW hg).symm

/-- **Existence**: there is a section of `O_Y` over `φ⁻¹U` satisfying the germ predicate for `g`. Near each
`t ∈ φ⁻¹U` write `g = a/d` on `W ∋ φ(t)` and take `Φ(a)Φ(d)⁻¹` on `φ⁻¹W ≤ Y.basicOpen (Φ d)`; these local sections
are compatible (`cancel_aux` with the key identity at every germ) and glue. -/
theorem thetaPred_exists (n : ℕ) {U : (AlgebraicGeometry.Proj 𝒜).Opens}
    (g : Γ(AlgebraicGeometry.Proj.twist 𝒜 (n : ℤ), U)) :
    ∃ r : Γ(Y, AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ ⁻¹ᵁ U),
      ThetaPred 𝒜 Φ hΦ n g (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ ⁻¹ᵁ U) r := by
  choose W htW hWU p q a d ha hd hpq hq hW hg using
    fun t : (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ ⁻¹ᵁ U : Y.Opens) =>
      exists_res_eq_res_fracSection 𝒜 Φ hΦ n g t.1 t.2
  let V : (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ ⁻¹ᵁ U : Y.Opens) → Y.Opens :=
    fun i => AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ ⁻¹ᵁ W i
  have hV : ∀ i, V i ≤ AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ ⁻¹ᵁ U := fun i _ hx => hWU i hx
  have hVd : ∀ i, V i ≤ AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ ⁻¹ᵁ
      AlgebraicGeometry.Proj.basicOpen 𝒜 (d i) := fun i _ hx => hW i hx
  have hu : ∀ i, IsUnit (Y.presheaf.map (homOfLE le_top).op (Φ (d i)) : Γ(Y, V i)) :=
    fun i => isUnit_res_of_le_preimage_basicOpen 𝒜 Φ hΦ (hq i) (hd i) (hVd i)
  let sf : ∀ i, Γ(Y, V i) := fun i =>
    (Y.presheaf.map (homOfLE (le_top : V i ≤ ⊤)).op (Φ (a i)) : Γ(Y, V i)) * (↑((hu i).unit⁻¹) : Γ(Y, V i))
  have hsf : ∀ i, sf i * Y.presheaf.map (homOfLE le_top).op (Φ (d i)) = Y.presheaf.map (homOfLE le_top).op (Φ (a i)) := by
    intro i
    have := Units.inv_mul_cancel_right (Y.presheaf.map (homOfLE (le_top : V i ≤ ⊤)).op (Φ (a i)) : Γ(Y, V i))
      (hu i).unit
    rwa [(hu i).unit_spec] at this
  -- germ form of `hsf`
  have hsfg : ∀ (i) (t : Y) (ht : t ∈ V i),
      Y.presheaf.germ (V i) t ht (sf i) * Y.presheaf.germ ⊤ t trivial (Φ (d i)) =
        Y.presheaf.germ ⊤ t trivial (Φ (a i)) := by
    intro i t ht
    have := congrArg (Y.presheaf.germ (V i) t ht) (hsf i)
    rwa [map_mul, TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply] at this
  have hcompat : ∀ i j, Y.presheaf.map (Opens.infLELeft (V i) (V j)).op (sf i) =
      Y.presheaf.map (Opens.infLERight (V i) (V j)).op (sf j) := by
    intro i j
    apply TopCat.Presheaf.section_ext Y.sheaf
    intro t ht
    show Y.presheaf.germ (V i ⊓ V j) t ht (Y.presheaf.map (Opens.infLELeft (V i) (V j)).op (sf i)) =
      Y.presheaf.germ (V i ⊓ V j) t ht (Y.presheaf.map (Opens.infLERight (V i) (V j)).op (sf j))
    rw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]
    have e1 := congrArg ((AlgebraicGeometry.Proj.twist 𝒜 (n : ℤ)).presheaf.map
      (homOfLE (inf_le_left : W i ⊓ W j ≤ W i)).op) (hg i)
    have e2 := congrArg ((AlgebraicGeometry.Proj.twist 𝒜 (n : ℤ)).presheaf.map
      (homOfLE (inf_le_right : W i ⊓ W j ≤ W j)).op) (hg j)
    simp only at e1 e2
    rw [res_res_twist, res_res_twist] at e1 e2
    have hkey := germ_mul_eq_of_res_fracSection_eq 𝒜 Φ hΦ (n : ℤ) (ha i) (hd i) (hpq i) (ha j) (hd j) (hpq j)
      (inf_le_left.trans (hW i)) (inf_le_right.trans (hW j)) (e1.symm.trans e2) t ⟨ht.1, ht.2⟩
    exact cancel_aux (isUnit_germ_of_not_mem 𝒜 Φ hΦ (hq i) (hd i) t (hW i ht.1))
      (isUnit_germ_of_not_mem 𝒜 Φ hΦ (hq j) (hd j) t (hW j ht.2)) (hsfg i t ht.1) (hsfg j t ht.2) hkey
  obtain ⟨s, hs'⟩ : ∃ s : Γ(Y, AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ ⁻¹ᵁ U),
      ∀ i, Y.presheaf.map (homOfLE (hV i)).op s = sf i := by
    obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' Y.sheaf V _ (fun i => homOfLE (hV i))
      (fun x hx => TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨x, hx⟩, htW ⟨x, hx⟩⟩) sf hcompat
    exact ⟨s, hs⟩
  refine ⟨s, fun t ht => ?_⟩
  have htV : t ∈ V ⟨t, ht⟩ := htW ⟨t, ht⟩
  refine thetaPredAt_of_rep n g s t ht (hWU ⟨t, ht⟩) (ha ⟨t, ht⟩) (hd ⟨t, ht⟩) (hpq ⟨t, ht⟩) (hW ⟨t, ht⟩)
    (htW ⟨t, ht⟩) (hg ⟨t, ht⟩) (isUnit_germ_of_not_mem 𝒜 Φ hΦ (hq _) (hd _) t (hW _ (htW ⟨t, ht⟩))) ?_
  have h1 : Y.presheaf.germ _ t ht s = Y.presheaf.germ (V ⟨t, ht⟩) t htV (sf ⟨t, ht⟩) := by
    rw [← hs' ⟨t, ht⟩, TopCat.Presheaf.germ_res_apply]
  rw [h1]
  exact hsfg ⟨t, ht⟩ t htV

variable (𝒜 Φ hΦ)

/-- **The section map `θ_n : Γ(U, O(n)) → Γ(φ⁻¹U, O_Y)`**, `a/d ↦ Φ(a)Φ(d)⁻¹`: the unique section satisfying the
germ predicate (`thetaPred_exists`, `thetaPred_unique`). -/
def thetaSection (n : ℕ) (U : (AlgebraicGeometry.Proj 𝒜).Opens)
    (g : Γ(AlgebraicGeometry.Proj.twist 𝒜 (n : ℤ), U)) :
    Γ(Y, AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ ⁻¹ᵁ U) :=
  Classical.choose (thetaPred_exists (𝒜 := 𝒜) (Φ := Φ) (hΦ := hΦ) n g)

theorem thetaPred_thetaSection (n : ℕ) (U : (AlgebraicGeometry.Proj 𝒜).Opens)
    (g : Γ(AlgebraicGeometry.Proj.twist 𝒜 (n : ℤ), U)) :
    ThetaPred 𝒜 Φ hΦ n g (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ ⁻¹ᵁ U) (thetaSection 𝒜 Φ hΦ n U g) :=
  Classical.choose_spec (thetaPred_exists (𝒜 := 𝒜) (Φ := Φ) (hΦ := hΦ) n g)

variable {𝒜 Φ hΦ}

theorem thetaSection_unique (n : ℕ) {U : (AlgebraicGeometry.Proj 𝒜).Opens}
    (g : Γ(AlgebraicGeometry.Proj.twist 𝒜 (n : ℤ), U))
    {r : Γ(Y, AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ ⁻¹ᵁ U)}
    (h : ThetaPred 𝒜 Φ hΦ n g (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ ⁻¹ᵁ U) r) :
    r = thetaSection 𝒜 Φ hΦ n U g :=
  thetaPred_unique n g le_rfl h (thetaPred_thetaSection 𝒜 Φ hΦ n U g)

/-- `germ_t(θ_n g) · Φ(d) = Φ(a)` for a fraction representation `g = a/d` on `W ∋ φ(t)`. -/
theorem germ_thetaSection_mul (n : ℕ) {U : (AlgebraicGeometry.Proj 𝒜).Opens}
    (g : Γ(AlgebraicGeometry.Proj.twist 𝒜 (n : ℤ), U)) (t : Y)
    (ht : t ∈ AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ ⁻¹ᵁ U)
    {W : (AlgebraicGeometry.Proj 𝒜).Opens} (hWU : W ≤ U) {p q : ℕ} {a d : A} (ha : a ∈ 𝒜 p) (hd : d ∈ 𝒜 q)
    (hpq : (p : ℤ) = q + n) (hq : 0 < q) (hW : W ≤ AlgebraicGeometry.Proj.basicOpen 𝒜 d)
    (htW : (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ).base t ∈ W)
    (hg : (AlgebraicGeometry.Proj.twist 𝒜 (n : ℤ)).presheaf.map (homOfLE hWU).op g =
      (AlgebraicGeometry.Proj.twist 𝒜 (n : ℤ)).presheaf.map (homOfLE hW).op
        (AlgebraicGeometry.Proj.fracSection 𝒜 (n : ℤ) a d ha hd hpq)) :
    Y.presheaf.germ _ t ht (thetaSection 𝒜 Φ hΦ n U g) * Y.presheaf.germ ⊤ t trivial (Φ d) =
      Y.presheaf.germ ⊤ t trivial (Φ a) :=
  thetaPred_thetaSection 𝒜 Φ hΦ n U g t ht W hWU p q a d ha hd hpq hq hW htW hg

/-! ## Properties of `θ_n` -/

/-- Pointwise value of a restricted section of `O(n)`, from a fraction representation. -/
theorem res_apply_of_res_eq (n : ℤ) {U W : (AlgebraicGeometry.Proj 𝒜).Opens} (hWU : W ≤ U)
    (g : Γ(AlgebraicGeometry.Proj.twist 𝒜 n, U)) {p q : ℕ} {a d : A} (ha : a ∈ 𝒜 p) (hd : d ∈ 𝒜 q)
    (hpq : (p : ℤ) = q + n) (hW : W ≤ AlgebraicGeometry.Proj.basicOpen 𝒜 d)
    (hg : (AlgebraicGeometry.Proj.twist 𝒜 n).presheaf.map (homOfLE hWU).op g =
      (AlgebraicGeometry.Proj.twist 𝒜 n).presheaf.map (homOfLE hW).op
        (AlgebraicGeometry.Proj.fracSection 𝒜 n a d ha hd hpq))
    (w : W) : g.1 ⟨w.1, hWU w.2⟩ = Localization.mk a ⟨d, hW w.2⟩ :=
  congrArg (fun s => s.1 w) hg

/-- **`θ_n` is additive.** -/
theorem thetaSection_add (n : ℕ) (U : (AlgebraicGeometry.Proj 𝒜).Opens)
    (g g' : Γ(AlgebraicGeometry.Proj.twist 𝒜 (n : ℤ), U)) :
    thetaSection 𝒜 Φ hΦ n U (g + g') = thetaSection 𝒜 Φ hΦ n U g + thetaSection 𝒜 Φ hΦ n U g' := by
  symm
  apply thetaSection_unique
  intro t ht
  obtain ⟨W₁, htW₁, hW₁U, p₁, q₁, a₁, d₁, ha₁, hd₁, hpq₁, hq₁, hW₁, hg₁⟩ :=
    exists_res_eq_res_fracSection 𝒜 Φ hΦ n g t ht
  obtain ⟨W₂, htW₂, hW₂U, p₂, q₂, a₂, d₂, ha₂, hd₂, hpq₂, hq₂, hW₂, hg₂⟩ :=
    exists_res_eq_res_fracSection 𝒜 Φ hΦ n g' t ht
  have hdeg : p₂ + q₁ = p₁ + q₂ := by omega
  have hα : a₁ * d₂ + a₂ * d₁ ∈ 𝒜 (p₁ + q₂) :=
    add_mem (SetLike.mul_mem_graded ha₁ hd₂) (hdeg ▸ SetLike.mul_mem_graded ha₂ hd₁)
  have hδ : d₁ * d₂ ∈ 𝒜 (q₁ + q₂) := SetLike.mul_mem_graded hd₁ hd₂
  have hpq : ((p₁ + q₂ : ℕ) : ℤ) = ((q₁ + q₂ : ℕ) : ℤ) + n := by push_cast; omega
  have hW : W₁ ⊓ W₂ ≤ AlgebraicGeometry.Proj.basicOpen 𝒜 (d₁ * d₂) := by
    rw [AlgebraicGeometry.Proj.basicOpen_mul]
    exact inf_le_inf hW₁ hW₂
  refine thetaPredAt_of_rep n (g + g') _ t ht (inf_le_left.trans hW₁U) hα hδ hpq hW ⟨htW₁, htW₂⟩ ?_ ?_ ?_
  · apply Subtype.ext
    funext w
    change g.1 ⟨w.1, hW₁U w.2.1⟩ + g'.1 ⟨w.1, hW₂U w.2.2⟩ = Localization.mk (a₁ * d₂ + a₂ * d₁) ⟨d₁ * d₂, hW w.2⟩
    rw [res_apply_of_res_eq (n : ℤ) hW₁U g ha₁ hd₁ hpq₁ hW₁ hg₁ ⟨w.1, w.2.1⟩,
      res_apply_of_res_eq (n : ℤ) hW₂U g' ha₂ hd₂ hpq₂ hW₂ hg₂ ⟨w.1, w.2.2⟩, Localization.add_mk,
      Localization.mk_eq_mk_iff]
    apply Localization.r_of_eq
    simp only [Submonoid.coe_mul]
    ring
  · rw [map_mul, map_mul]
    exact (isUnit_germ_of_not_mem 𝒜 Φ hΦ hq₁ hd₁ t (hW₁ htW₁)).mul
      (isUnit_germ_of_not_mem 𝒜 Φ hΦ hq₂ hd₂ t (hW₂ htW₂))
  · have h₁ := germ_thetaSection_mul n g t ht hW₁U ha₁ hd₁ hpq₁ hq₁ hW₁ htW₁ hg₁
    have h₂ := germ_thetaSection_mul n g' t ht hW₂U ha₂ hd₂ hpq₂ hq₂ hW₂ htW₂ hg₂
    simp only [map_add, map_mul]
    linear_combination (Y.presheaf.germ ⊤ t trivial (Φ d₂)) * h₁ + (Y.presheaf.germ ⊤ t trivial (Φ d₁)) * h₂

/-- `θ_n 0 = 0`. -/
theorem thetaSection_zero (n : ℕ) (U : (AlgebraicGeometry.Proj 𝒜).Opens) :
    thetaSection 𝒜 Φ hΦ n U 0 = 0 := by
  have h := thetaSection_add (𝒜 := 𝒜) (Φ := Φ) (hΦ := hΦ) n U 0 0
  rw [add_zero] at h
  exact (add_left_cancel (a := thetaSection 𝒜 Φ hΦ n U 0) (by rw [add_zero]; exact h)).symm


/-- **`θ_n` is `φ^♯`-linear**: `θ_n(r • g) = φ^♯(r) · θ_n(g)` for `r ∈ Γ(U, O_Proj)`. Near `φ(t)` write `g = a₁/d₁`
and `r = c/e` (`c, e ∈ 𝒜 k`; multiply both by a chart element `s` to make the degree positive); then
`r • g = (csa₁)/(esd₁)`, and `germ_t(φ^♯ r) · Φ(es) = Φ(cs)` is the bridge `germ_app_mul_eq_of_res_eq_mk`. -/
theorem thetaSection_smul (n : ℕ) (U : (AlgebraicGeometry.Proj 𝒜).Opens) (r : Γ(AlgebraicGeometry.Proj 𝒜, U))
    (g : Γ(AlgebraicGeometry.Proj.twist 𝒜 (n : ℤ), U)) :
    thetaSection 𝒜 Φ hΦ n U (r • g) =
      (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ).app U r * thetaSection 𝒜 Φ hΦ n U g := by
  symm
  apply thetaSection_unique
  intro t ht
  obtain ⟨W₁, htW₁, hW₁U, p₁, q₁, a₁, d₁, ha₁, hd₁, hpq₁, hq₁, hW₁, hg₁⟩ :=
    exists_res_eq_res_fracSection 𝒜 Φ hΦ n g t ht
  obtain ⟨V, hV, i, k, c, e, he, hr⟩ := r.2 ⟨(AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ).base t, ht⟩
  obtain ⟨e', s, he', hs, hts⟩ := exists_mem_basicOpen_of_irrelevant' 𝒜 Φ hΦ t
  have hs' : s ∉ ((AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ).base t).asHomogeneousIdeal :=
    (mem_basicOpen_iff_not_mem 𝒜 Φ hΦ he' hs t).mp hts
  have htW : (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ).base t ∈
      W₁ ⊓ V ⊓ AlgebraicGeometry.Proj.basicOpen 𝒜 s := ⟨⟨htW₁, hV⟩, hs'⟩
  have hWU : W₁ ⊓ V ⊓ AlgebraicGeometry.Proj.basicOpen 𝒜 s ≤ U := fun x hx => leOfHom i hx.1.2
  have hWW₁ : W₁ ⊓ V ⊓ AlgebraicGeometry.Proj.basicOpen 𝒜 s ≤ W₁ := inf_le_left.trans inf_le_left
  have hWe : W₁ ⊓ V ⊓ AlgebraicGeometry.Proj.basicOpen 𝒜 s ≤ AlgebraicGeometry.Proj.basicOpen 𝒜 (e.1 * s) := by
    intro x hx
    rw [AlgebraicGeometry.Proj.mem_basicOpen]
    intro h
    exact ((ProjectiveSpectrum.isPrime x).mem_or_mem h).elim (he ⟨x, hx.1.2⟩) hx.2
  have hce : c.1 * s ∈ 𝒜 (k + e') := SetLike.mul_mem_graded c.2 hs
  have hes : e.1 * s ∈ 𝒜 (k + e') := SetLike.mul_mem_graded e.2 hs
  have hr' : ∀ w : (W₁ ⊓ V ⊓ AlgebraicGeometry.Proj.basicOpen 𝒜 s : (AlgebraicGeometry.Proj 𝒜).Opens),
      r.1 ⟨w.1, hWU w.2⟩ = HomogeneousLocalization.mk ⟨k + e', ⟨c.1 * s, hce⟩, ⟨e.1 * s, hes⟩, hWe w.2⟩ := by
    intro w
    apply HomogeneousLocalization.val_injective
    rw [show r.1 ⟨w.1, hWU w.2⟩ = HomogeneousLocalization.mk ⟨k, c, e, he ⟨w.1, w.2.1.2⟩⟩ from hr ⟨w.1, w.2.1.2⟩,
      HomogeneousLocalization.val_mk, HomogeneousLocalization.val_mk, Localization.mk_eq_mk_iff]
    apply Localization.r_of_eq
    simp only
    ring
  have hα : c.1 * s * a₁ ∈ 𝒜 (k + e' + p₁) := SetLike.mul_mem_graded hce ha₁
  have hδ : e.1 * s * d₁ ∈ 𝒜 (k + e' + q₁) := SetLike.mul_mem_graded hes hd₁
  have hpq : ((k + e' + p₁ : ℕ) : ℤ) = ((k + e' + q₁ : ℕ) : ℤ) + n := by push_cast; omega
  have hW : W₁ ⊓ V ⊓ AlgebraicGeometry.Proj.basicOpen 𝒜 s ≤ AlgebraicGeometry.Proj.basicOpen 𝒜 (e.1 * s * d₁) := by
    rw [AlgebraicGeometry.Proj.basicOpen_mul]
    exact le_inf hWe (hWW₁.trans hW₁)
  refine thetaPredAt_of_rep n (r • g) _ t ht hWU hα hδ hpq hW htW ?_ ?_ ?_
  · apply Subtype.ext
    funext w
    change (r.1 ⟨w.1, hWU w.2⟩).val * g.1 ⟨w.1, hW₁U w.2.1.1⟩ =
      Localization.mk (c.1 * s * a₁) ⟨e.1 * s * d₁, hW w.2⟩
    rw [hr' w, HomogeneousLocalization.val_mk,
      res_apply_of_res_eq (n : ℤ) hW₁U g ha₁ hd₁ hpq₁ hW₁ hg₁ ⟨w.1, w.2.1.1⟩, Localization.mk_mul]
    rfl
  · rw [map_mul, map_mul]
    exact (isUnit_germ_of_not_mem 𝒜 Φ hΦ (by omega) hes t (hWe htW)).mul
      (isUnit_germ_of_not_mem 𝒜 Φ hΦ hq₁ hd₁ t (hW₁ htW₁))
  · have hb := germ_app_mul_eq_of_res_eq_mk 𝒜 Φ hΦ r (k := k + e') (by omega) hce hes hWU hWe hr' t ht htW
    have h₁ := germ_thetaSection_mul n g t ht hW₁U ha₁ hd₁ hpq₁ hq₁ hW₁ htW₁ hg₁
    simp only [map_mul] at hb ⊢
    linear_combination (Y.presheaf.germ _ t ht (thetaSection 𝒜 Φ hΦ n U g) *
      Y.presheaf.germ ⊤ t trivial (Φ d₁)) * hb +
      (Y.presheaf.germ ⊤ t trivial (Φ c) * Y.presheaf.germ ⊤ t trivial (Φ s)) * h₁

/-- **`θ_n` is natural**: `θ_n(g|_{U'}) = θ_n(g)|_{φ⁻¹U'}`. -/
theorem thetaSection_res (n : ℕ) {U U' : (AlgebraicGeometry.Proj 𝒜).Opens} (hU : U' ≤ U)
    (g : Γ(AlgebraicGeometry.Proj.twist 𝒜 (n : ℤ), U)) :
    thetaSection 𝒜 Φ hΦ n U' ((AlgebraicGeometry.Proj.twist 𝒜 (n : ℤ)).presheaf.map (homOfLE hU).op g) =
      Y.presheaf.map (homOfLE (show AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ ⁻¹ᵁ U' ≤
        AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ ⁻¹ᵁ U from fun _ hx => hU hx)).op
        (thetaSection 𝒜 Φ hΦ n U g) := by
  symm
  apply thetaSection_unique
  intro t ht W hWU' p q a d ha hd hpq hq hW htW hg
  rw [res_res_twist] at hg
  rw [TopCat.Presheaf.germ_res_apply]
  exact germ_thetaSection_mul n g t (hU ht) (hWU'.trans hU) ha hd hpq hq hW htW hg

/-- **`θ_{a+b}` is multiplicative** for the pointwise product of sections (Stacks 01MO):
`θ_{a+b}(g · h) = θ_a(g) · θ_b(h)`. -/
theorem thetaSection_mul (a b : ℕ) (U : (AlgebraicGeometry.Proj 𝒜).Opens)
    (g : Γ(AlgebraicGeometry.Proj.twist 𝒜 (a : ℤ), U)) (h : Γ(AlgebraicGeometry.Proj.twist 𝒜 (b : ℤ), U)) :
    thetaSection 𝒜 Φ hΦ (a + b) U (AlgebraicGeometry.Proj.twistSectionMul 𝒜 (a : ℤ) (b : ℤ) U g h) =
      thetaSection 𝒜 Φ hΦ a U g * thetaSection 𝒜 Φ hΦ b U h := by
  symm
  apply thetaSection_unique
  intro t ht
  obtain ⟨W₁, htW₁, hW₁U, p₁, q₁, a₁, d₁, ha₁, hd₁, hpq₁, hq₁, hW₁, hg₁⟩ :=
    exists_res_eq_res_fracSection 𝒜 Φ hΦ a g t ht
  obtain ⟨W₂, htW₂, hW₂U, p₂, q₂, a₂, d₂, ha₂, hd₂, hpq₂, hq₂, hW₂, hg₂⟩ :=
    exists_res_eq_res_fracSection 𝒜 Φ hΦ b h t ht
  have hα : a₁ * a₂ ∈ 𝒜 (p₁ + p₂) := SetLike.mul_mem_graded ha₁ ha₂
  have hδ : d₁ * d₂ ∈ 𝒜 (q₁ + q₂) := SetLike.mul_mem_graded hd₁ hd₂
  have hpq : ((p₁ + p₂ : ℕ) : ℤ) = ((q₁ + q₂ : ℕ) : ℤ) + ((a + b : ℕ) : ℤ) := by push_cast; omega
  have hW : W₁ ⊓ W₂ ≤ AlgebraicGeometry.Proj.basicOpen 𝒜 (d₁ * d₂) := by
    rw [AlgebraicGeometry.Proj.basicOpen_mul]
    exact inf_le_inf hW₁ hW₂
  refine thetaPredAt_of_rep (a + b) _ _ t ht (inf_le_left.trans hW₁U) hα hδ hpq hW ⟨htW₁, htW₂⟩ ?_ ?_ ?_
  · apply Subtype.ext
    funext w
    change g.1 ⟨w.1, hW₁U w.2.1⟩ * h.1 ⟨w.1, hW₂U w.2.2⟩ = Localization.mk (a₁ * a₂) ⟨d₁ * d₂, hW w.2⟩
    rw [res_apply_of_res_eq (a : ℤ) hW₁U g ha₁ hd₁ hpq₁ hW₁ hg₁ ⟨w.1, w.2.1⟩,
      res_apply_of_res_eq (b : ℤ) hW₂U h ha₂ hd₂ hpq₂ hW₂ hg₂ ⟨w.1, w.2.2⟩, Localization.mk_mul]
    rfl
  · rw [map_mul, map_mul]
    exact (isUnit_germ_of_not_mem 𝒜 Φ hΦ hq₁ hd₁ t (hW₁ htW₁)).mul
      (isUnit_germ_of_not_mem 𝒜 Φ hΦ hq₂ hd₂ t (hW₂ htW₂))
  · have h₁ := germ_thetaSection_mul a g t ht hW₁U ha₁ hd₁ hpq₁ hq₁ hW₁ htW₁ hg₁
    have h₂ := germ_thetaSection_mul b h t ht hW₂U ha₂ hd₂ hpq₂ hq₂ hW₂ htW₂ hg₂
    simp only [map_mul]
    linear_combination (Y.presheaf.germ _ t ht (thetaSection 𝒜 Φ hΦ b U h) * Y.presheaf.germ ⊤ t trivial (Φ d₂)) * h₁ +
      (Y.presheaf.germ ⊤ t trivial (Φ a₁)) * h₂

/-- **`θ_n(a/1) = Φ(a)`** for `a ∈ 𝒜 n`: the global section `twistSection 𝒜 a` goes to `Φ(a)|_{φ⁻¹⊤}`. -/
theorem thetaSection_twistSection (n : ℕ) (a : A) (ha : a ∈ 𝒜 n) :
    thetaSection 𝒜 Φ hΦ n ⊤ (AlgebraicGeometry.Proj.twistSection 𝒜 a ha) =
      Y.presheaf.map (homOfLE le_top).op (Φ a) := by
  symm
  apply thetaSection_unique
  intro t ht
  have h1 : (1 : A) ∈ 𝒜 0 := SetLike.one_mem_graded 𝒜
  have hpq : (n : ℤ) = ((0 : ℕ) : ℤ) + n := by simp
  have hW : (⊤ : (AlgebraicGeometry.Proj 𝒜).Opens) ≤ AlgebraicGeometry.Proj.basicOpen 𝒜 1 := by
    rw [AlgebraicGeometry.Proj.basicOpen_one]
  refine thetaPredAt_of_rep n _ _ t ht le_rfl ha h1 hpq hW trivial rfl ?_ ?_
  · rw [map_one, map_one]; exact isUnit_one
  · rw [map_one, map_one, mul_one, TopCat.Presheaf.germ_res_apply]

end AlgebraicGeometry.Proj.TwistFamily

end
