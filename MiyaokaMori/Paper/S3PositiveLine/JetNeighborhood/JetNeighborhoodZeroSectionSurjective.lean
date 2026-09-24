import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.RelativeSpecOfAlgebraMapSections
import MiyaokaMori.AlgebraicGeometry.Modules.RelativeSpecAffine
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.JetZeroSection
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.JetNeighborhoodZeroSectionSurjectiveNilpotent

/-! # The zero section of the jet neighbourhood is surjective on points

Statement: the zero section `C̃ → C̃_(κ)(L)` of the jet neighbourhood is surjective on
underlying points, i.e. every point of the infinitesimal neighbourhood lies on the zero
section (the neighbourhood is a nilpotent thickening of `C̃`).

Source: §3 of the paper (definition of `C̃_(k)(L)`): a frame of `L` on an affine open `V ⊆ C̃` identifies
`C̃_(κ)(L)|_V` with `Spec (O(V)[t]/(t^{κ+1}))`.

Used for the compatibility of the morphism near the zero jet: the morphisms `ν : C̃_(κ)(L) → U` and
`ȷ^× : C̃_(κ)(L) → Z^×` are obtained by `IsOpenImmersion.lift`, whose range hypothesis is checked point by
point; every point of `C̃_(κ)(L)` is a zero-section point.

Route actually used (no local model, no frame): with `p := p_κ`, `σ` the zero
section and `σ ≫ p = 𝟙`, it suffices that `p` is injective on points over each affine open
`V ⊆ C̃`. Over `W := p⁻¹V` (affine, `p` is an affine morphism) `p` is `Spec` of
`φ := p^♯ : O(V) → O(W)`, which has the retraction `ψ := σ^♯ : O(W) → O(V)` (`ψ ∘ φ = id`) with
nilpotent kernel (`O(W) = 𝒜(V)` via `relativeSpec.structureHom`, `ψ` = weight-`0` projection,
positive weights are nilpotent: `truncatedJetAlgebra.pow_succ_eq_zero_of_π₀_eq_zero`). Then every
prime `P` of `O(W)` equals `ψ⁻¹(φ⁻¹ P)`, so `Spec φ` is injective (Stacks 00EK-type argument).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
noncomputable section

/-- **Spec of a ring map with a nil-kernel retraction is injective.** If `ψ ∘ φ = id` and every
element of `ker ψ` is nilpotent, then `Spec φ : Spec S → Spec R` is injective: a prime `P` of `S`
contains `s − φ(ψ s)` (nilpotent) for every `s`, hence `s ∈ P ↔ ψ s ∈ φ⁻¹P`, i.e. `P = ψ⁻¹(φ⁻¹ P)`
is determined by `φ⁻¹ P`. (Stacks 00EK: `Spec (A/I) → Spec A` is bijective for `I` nil.) -/
theorem PrimeSpectrum.comap_injective_of_retraction_of_nilpotent {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (ψ : S →+* R) (hψφ : ∀ r, ψ (φ r) = r) (hnil : ∀ s, ψ s = 0 → IsNilpotent s) :
    Function.Injective (PrimeSpectrum.comap φ) := by
  have key : ∀ (P : PrimeSpectrum S) (s : S),
      s ∈ P.asIdeal ↔ ψ s ∈ (PrimeSpectrum.comap φ P).asIdeal := by
    intro P s
    rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
    have hn : s - φ (ψ s) ∈ P.asIdeal := by
      obtain ⟨n, hn⟩ := hnil (s - φ (ψ s)) (by rw [map_sub, hψφ, sub_self])
      exact P.isPrime.mem_of_pow_mem n (by rw [hn]; exact zero_mem _)
    constructor
    · intro hs
      have := P.asIdeal.sub_mem hs hn
      rwa [sub_sub_cancel] at this
    · intro h
      have := P.asIdeal.add_mem hn h
      rwa [sub_add_cancel] at this
  intro P Q hPQ
  ext s
  rw [key P s, key Q s, hPQ]

/-- `V ≤ σ⁻¹(p⁻¹ V)` since `σ ≫ p = 𝟙`. -/
theorem jetNeighborhood.le_zeroSection_preimage_proj_preimage {k : Type u} [Field k]
    {Ct : SmoothProjectiveCurve k} (L : LineBundle Ct.toVariety) (κ : ℕ) (V : Ct.toScheme.Opens) :
    V ≤ jetNeighborhood.zeroSection L κ ⁻¹ᵁ (jetNeighborhood.proj L κ ⁻¹ᵁ V) := by
  change V ≤ (jetNeighborhood.zeroSection L κ ≫ jetNeighborhood.proj L κ) ⁻¹ᵁ V
  rw [jetNeighborhood.zeroSection_proj]
  exact le_rfl

/-- `appLE` of a morphism equal to the identity is the identity. -/
theorem AlgebraicGeometry.Scheme.Hom.appLE_eq_id_of_eq_id {X : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ X) (hf : f = CategoryTheory.CategoryStruct.id X) (V : X.Opens) (e : V ≤ f ⁻¹ᵁ V) :
    f.appLE V V e = CategoryTheory.CategoryStruct.id _ := by
  subst hf
  simp only [AlgebraicGeometry.Scheme.Hom.appLE, AlgebraicGeometry.Scheme.Hom.id_app]
  exact X.presheaf.map_id _

/-- `σ^♯ ∘ p^♯ = id` on `Γ(V)` (from `σ ≫ p = 𝟙`). -/
theorem jetNeighborhood.zeroSection_appLE_proj_appLE {k : Type u} [Field k]
    {Ct : SmoothProjectiveCurve k} (L : LineBundle Ct.toVariety) (κ : ℕ) (V : Ct.toScheme.Opens)
    (r : Γ(Ct.toScheme, V)) :
    ((jetNeighborhood.zeroSection L κ).appLE (jetNeighborhood.proj L κ ⁻¹ᵁ V) V
        (jetNeighborhood.le_zeroSection_preimage_proj_preimage L κ V)).hom
      (((jetNeighborhood.proj L κ).appLE V (jetNeighborhood.proj L κ ⁻¹ᵁ V) le_rfl).hom r) = r := by
  have h := AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE (jetNeighborhood.zeroSection L κ)
    (jetNeighborhood.proj L κ) V (jetNeighborhood.proj L κ ⁻¹ᵁ V) V le_rfl
    (jetNeighborhood.le_zeroSection_preimage_proj_preimage L κ V)
  rw [AlgebraicGeometry.Scheme.Hom.appLE_eq_id_of_eq_id _ (jetNeighborhood.zeroSection_proj L κ)] at h
  exact congrArg (fun ψ : Γ(Ct.toScheme, V) ⟶ Γ(Ct.toScheme, V) => ψ.hom r) h

/-- The structure map `𝒜 → p_* O_{C̃_(κ)(L)}` is an algebra map (second component of the
universal property at the identity). -/
theorem jetNeighborhood.structureHom_isAlgebraMap {k : Type u} [Field k]
    {Ct : SmoothProjectiveCurve k} (L : LineBundle Ct.toVariety) (κ : ℕ) :
    (truncatedJetAlgebra L κ).IsAlgebraMapToPushforward (jetNeighborhood.proj L κ)
      (AlgebraicGeometry.Scheme.relativeSpec.structureHom (truncatedJetAlgebra L κ)) :=
  (AlgebraicGeometry.Scheme.relativeSpecHomEquiv (truncatedJetAlgebra L κ)
    (AlgebraicGeometry.Scheme.relativeSpec (truncatedJetAlgebra L κ)) (CategoryTheory.CategoryStruct.id _)).2

/-- **The kernel of `σ^♯ : Γ(p⁻¹V) → Γ(V)` is nilpotent** for affine `V`: `Γ(p⁻¹V) = 𝒜(V)` via
`structureHom` (bijective on affine opens), `σ^♯` is the augmentation = weight-`0` projection
(`ofAlgebraMap_appLE_structureHom`), and positive weights are nilpotent
(`truncatedJetAlgebra.pow_succ_eq_zero_of_π₀_eq_zero`). -/
theorem jetNeighborhood.pow_succ_eq_zero_of_zeroSection_appLE_eq_zero {k : Type u} [Field k]
    {Ct : SmoothProjectiveCurve k} (L : LineBundle Ct.toVariety) (κ : ℕ) (V : Ct.toScheme.affineOpens)
    (u : Γ((jetNeighborhood L κ).left, jetNeighborhood.proj L κ ⁻¹ᵁ V.1))
    (hu : ((jetNeighborhood.zeroSection L κ).appLE (jetNeighborhood.proj L κ ⁻¹ᵁ V.1) V.1
        (jetNeighborhood.le_zeroSection_preimage_proj_preimage L κ V.1)).hom u = 0) :
    u ^ (κ + 1) = 0 := by
  -- the ring hom `𝒜(V) → Γ(p⁻¹V)` underlying `structureHom` (bijective on the affine `V`)
  let F : (truncatedJetAlgebra L κ).sectionsRing V.1 →+*
      Γ((jetNeighborhood L κ).left, jetNeighborhood.proj L κ ⁻¹ᵁ V.1) :=
    (truncatedJetAlgebra L κ).algebraMapSections (jetNeighborhood.proj L κ)
      (AlgebraicGeometry.Scheme.relativeSpec.structureHom (truncatedJetAlgebra L κ))
      (jetNeighborhood.structureHom_isAlgebraMap L κ) V.1
  obtain ⟨a, ha⟩ : ∃ a : (truncatedJetAlgebra L κ).sectionsRing V.1, F a = u := by
    obtain ⟨a₀, ha₀⟩ := (AlgebraicGeometry.Scheme.relativeSpec.structureHom_app_bijective
      (truncatedJetAlgebra L κ) V).2 u
    exact ⟨a₀, ha₀⟩
  have hD := AlgebraicGeometry.Scheme.relativeSpec.ofAlgebraMap_appLE_structureHom
    (truncatedJetAlgebra L κ) (CategoryTheory.Over.mk (CategoryTheory.CategoryStruct.id Ct.toScheme))
    (jetNeighborhood.augmentation L κ) (jetNeighborhood.augmentation_isAlgebraMap L κ) V.1 a
    (jetNeighborhood.le_zeroSection_preimage_proj_preimage L κ V.1)
  -- the weight-0 component of `a` vanishes
  have hπ : (CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
      ⟨0, Nat.succ_pos κ⟩).app V.1 a = 0 := by
    have h1 : ((jetNeighborhood.zeroSection L κ).appLE (jetNeighborhood.proj L κ ⁻¹ᵁ V.1) V.1
        (jetNeighborhood.le_zeroSection_preimage_proj_preimage L κ V.1)).hom (F a) = 0 := by
      rw [ha]; exact hu
    exact hD.symm.trans h1
  have hnil := truncatedJetAlgebra.pow_succ_eq_zero_of_π₀_eq_zero L κ V.1 a hπ
  -- transport along `F`
  rw [← ha, ← map_pow, hnil, map_zero]

/-- **`p` is injective on points over an affine open `V ⊆ C̃`.** Over `W = p⁻¹V` (affine), `p` is
`Spec` of `p^♯ : Γ(V) → Γ(W)` (`IsAffineOpen.SpecMap_appLE_fromSpec`), which is injective on
primes by `PrimeSpectrum.comap_injective_of_retraction_of_nilpotent` with the retraction `σ^♯`. -/
theorem jetNeighborhood.proj_base_injOn_preimage_affine {k : Type u} [Field k]
    {Ct : SmoothProjectiveCurve k} (L : LineBundle Ct.toVariety) (κ : ℕ) (V : Ct.toScheme.affineOpens)
    {y₁ y₂ : (jetNeighborhood L κ).left}
    (h₁ : (jetNeighborhood.proj L κ).base y₁ ∈ V.1) (h₂ : (jetNeighborhood.proj L κ).base y₂ ∈ V.1)
    (h : (jetNeighborhood.proj L κ).base y₁ = (jetNeighborhood.proj L κ).base y₂) : y₁ = y₂ := by
  have : AlgebraicGeometry.IsAffineHom (jetNeighborhood.proj L κ) :=
    AlgebraicGeometry.Scheme.relativeSpec_isAffineHom (truncatedJetAlgebra L κ)
  have hW : AlgebraicGeometry.IsAffineOpen (jetNeighborhood.proj L κ ⁻¹ᵁ V.1) :=
    V.2.preimage (jetNeighborhood.proj L κ)
  have hnat := AlgebraicGeometry.IsAffineOpen.SpecMap_appLE_fromSpec (jetNeighborhood.proj L κ) V.2 hW le_rfl
  have hy₁ : y₁ ∈ Set.range hW.fromSpec := by rw [hW.range_fromSpec]; exact h₁
  have hy₂ : y₂ ∈ Set.range hW.fromSpec := by rw [hW.range_fromSpec]; exact h₂
  obtain ⟨z₁, hz₁⟩ := hy₁
  obtain ⟨z₂, hz₂⟩ := hy₂
  have hcomm : ∀ z, (jetNeighborhood.proj L κ).base (hW.fromSpec.base z) =
      V.2.fromSpec.base ((AlgebraicGeometry.Spec.map
        ((jetNeighborhood.proj L κ).appLE V.1 (jetNeighborhood.proj L κ ⁻¹ᵁ V.1) le_rfl)).base z) :=
    fun z => (congrArg (fun f => f.base z) hnat).symm
  have hz : (AlgebraicGeometry.Spec.map
        ((jetNeighborhood.proj L κ).appLE V.1 (jetNeighborhood.proj L κ ⁻¹ᵁ V.1) le_rfl)).base z₁ =
      (AlgebraicGeometry.Spec.map
        ((jetNeighborhood.proj L κ).appLE V.1 (jetNeighborhood.proj L κ ⁻¹ᵁ V.1) le_rfl)).base z₂ := by
    have hoi : AlgebraicGeometry.IsOpenImmersion V.2.fromSpec :=
      AlgebraicGeometry.IsAffineOpen.isOpenImmersion_fromSpec V.2
    apply V.2.fromSpec.isOpenEmbedding.isEmbedding.injective
    rw [← hcomm, ← hcomm]
    rw [hz₁, hz₂]
    exact h
  have hinj := PrimeSpectrum.comap_injective_of_retraction_of_nilpotent
    ((jetNeighborhood.proj L κ).appLE V.1 (jetNeighborhood.proj L κ ⁻¹ᵁ V.1) le_rfl).hom
    ((jetNeighborhood.zeroSection L κ).appLE (jetNeighborhood.proj L κ ⁻¹ᵁ V.1) V.1
      (jetNeighborhood.le_zeroSection_preimage_proj_preimage L κ V.1)).hom
    (jetNeighborhood.zeroSection_appLE_proj_appLE L κ V.1)
    (fun u hu => ⟨κ + 1, jetNeighborhood.pow_succ_eq_zero_of_zeroSection_appLE_eq_zero L κ V u hu⟩)
  have hz' : z₁ = z₂ := hinj hz
  rw [← hz₁, ← hz₂, hz']

/-- **Every point of the jet neighbourhood lies on its zero section.**

Source: §3 of the paper (local model `Spec (O(V)[t]/(t^{κ+1}))` of `C̃_(κ)(L)`), together
with `jetNeighborhood.zeroSection_proj` (`σ ≫ p_κ = 𝟙`).

Proof. Write `p := jetNeighborhood.proj L κ`, `σ := jetNeighborhood.zeroSection L κ`; `σ ≫ p = 𝟙`.
For `y ∈ C̃_(κ)(L)` pick an affine open `V ∋ p y`; then `y` and `σ (p y)` both lie over `V` and have
the same image under `p`, so they coincide by `jetNeighborhood.proj_base_injOn_preimage_affine`
(`p` is injective on points over affine opens: `p⁻¹V = Spec 𝒜(V) → Spec O(V)` is `Spec` of a ring map
with a retraction `σ^♯` whose kernel — the positive-weight part of `𝒜(V)` — is nilpotent). -/
theorem jetNeighborhood.zeroSection_base_surjective {k : Type u} [Field k]
    {Ct : SmoothProjectiveCurve k} (L : LineBundle Ct.toVariety) (κ : ℕ) :
    Function.Surjective (jetNeighborhood.zeroSection L κ).base := by
  intro y
  have hpσ : ∀ x, (jetNeighborhood.proj L κ).base ((jetNeighborhood.zeroSection L κ).base x) = x :=
    fun x => congrArg (fun f => f.base x) (jetNeighborhood.zeroSection_proj L κ)
  obtain ⟨V, hV, hyV, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp Ct.toScheme.isBasis_affineOpens
    (show (jetNeighborhood.proj L κ).base y ∈ (⊤ : Ct.toScheme.Opens) from trivial)
  refine ⟨(jetNeighborhood.proj L κ).base y, ?_⟩
  refine jetNeighborhood.proj_base_injOn_preimage_affine L κ ⟨V, hV⟩ ?_ hyV ?_
  · rw [hpσ]; exact hyV
  · exact hpσ _

end
