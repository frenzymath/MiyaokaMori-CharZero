import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.Cech.CechComplexAlternating
import MiyaokaMori.AlgebraicGeometry.Cohomology.Cech.CechComplexAlternatingElementwise
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.ModulesExactIffLocallyLift

/-! # Functoriality of the alternating Čech complex

Functoriality of the alternating Čech complex in the module: `φ : M ⟶ N` induces a chain map
`cechComplexAltMap U φ : Č_alt(U, M) ⟶ Č_alt(U, N)` (termwise `∏_σ φ(U_σ)`), preserving identities,
composition and zero, and acting componentwise by `φ(U_σ)` on families of sections.

Proof: the termwise map `cechTermAltMap` is `Pi.map`; commutation with restriction maps
(`sectionsOverTopMap_restrict`) is the naturality of `φ`; commutation with the differential holds
because both sides are `Σ_k (-1)^k res ∘ φ ∘ π_{τ∘δ_k}` on the component `τ`.

Source: Hartshorne III.4 (pp. 218–219, functoriality of the Čech complex in the sheaf).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}} {n : ℕ} (U : Fin n → X.Opens)

/-- The map of `φ` on sections over an open `V`, as a `Γ(X, ⊤)`-linear map. -/
def sectionsOverTopMap {M N : X.Modules} (φ : M ⟶ N) (V : X.Opens) :
    M.sectionsOverTop V ⟶ N.sectionsOverTop V :=
  (ModuleCat.restrictScalars
    (X.ringCatSheaf.obj.map (CategoryTheory.homOfLE (le_top : V ≤ ⊤)).op).hom).map
    (φ.val.app (Opposite.op V))

theorem sectionsOverTopMap_apply {M N : X.Modules} (φ : M ⟶ N) (V : X.Opens)
    (x : M.sectionsOverTop V) :
    (sectionsOverTopMap φ V).hom x = (φ.val.app (Opposite.op V)).hom x := rfl

/-- The map on sections commutes with restriction (naturality of `φ`). -/
theorem sectionsOverTopMap_restrict {M N : X.Modules} (φ : M ⟶ N) {V W : X.Opens} (h : W ≤ V) :
    sectionsOverTopMap φ V ≫ N.sectionsOverTopRestrict h =
      M.sectionsOverTopRestrict h ≫ sectionsOverTopMap φ W := by
  ext x
  exact (ConcreteCategory.congr_hom (φ.val.naturality (homOfLE h).op) x).symm

/-- The termwise map `∏_σ φ(U_σ)`. -/
def cechTermAltMap {M N : X.Modules} (φ : M ⟶ N) (p : ℕ) :
    cechTermAlt U M p ⟶ cechTermAlt U N p :=
  Limits.Pi.map fun σ : Fin (p + 1) ↪o Fin n => sectionsOverTopMap φ (⨅ k, U (σ k))

/-- `Pi.map` commutes with a `Pi.lift` of "signed sums of components" type. -/
theorem pi_map_lift_sum {C : Type*} [Category C] [Preadditive C] {ι κ : Type} {m : ℕ}
    {Z Z' : ι → C} {W W' : κ → C} [HasProduct Z] [HasProduct Z'] [HasProduct W] [HasProduct W']
    (a : κ → Fin m → ι) (ε : Fin m → ℤ)
    (r : ∀ (τ : κ) (k : Fin m), Z (a τ k) ⟶ W τ) (r' : ∀ (τ : κ) (k : Fin m), Z' (a τ k) ⟶ W' τ)
    (f : ∀ i, Z i ⟶ Z' i) (g : ∀ τ, W τ ⟶ W' τ)
    (h : ∀ τ k, f (a τ k) ≫ r' τ k = r τ k ≫ g τ) :
    Limits.Pi.map f ≫ (Pi.lift fun τ : κ => ∑ k : Fin m, ε k • (Pi.π Z' (a τ k) ≫ r' τ k)) =
      (Pi.lift fun τ : κ => ∑ k : Fin m, ε k • (Pi.π Z (a τ k) ≫ r τ k)) ≫ Limits.Pi.map g := by
  refine Limits.Pi.hom_ext _ _ fun τ => ?_
  rw [Category.assoc, Category.assoc, Limits.Pi.lift_π, Limits.Pi.map_π, Preadditive.comp_sum,
    Limits.Pi.lift_π_assoc, Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Preadditive.comp_zsmul, Preadditive.zsmul_comp, Limits.Pi.map_π_assoc, Category.assoc, h]

theorem cechTermAltMap_comm {M N : X.Modules} (φ : M ⟶ N) (p : ℕ) :
    cechTermAltMap U φ p ≫ cechDiffAlt U N p = cechDiffAlt U M p ≫ cechTermAltMap U φ (p + 1) :=
  pi_map_lift_sum (fun (τ : Fin (p + 2) ↪o Fin n) k => (Fin.succAboveOrderEmb k).trans τ)
    (fun k => (-1 : ℤ) ^ (k : ℕ)) (fun τ k => M.sectionsOverTopRestrict (cech_face_le U τ k))
    (fun τ k => N.sectionsOverTopRestrict (cech_face_le U τ k))
    (fun σ => sectionsOverTopMap φ (⨅ k, U (σ k))) (fun τ => sectionsOverTopMap φ (⨅ k, U (τ k)))
    (fun τ k => sectionsOverTopMap_restrict φ (cech_face_le U τ k))

/-- The `ℤ`-graded termwise map: zero in negative degrees. -/
def cechTermAltZMap {M N : X.Modules} (φ : M ⟶ N) :
    ∀ i : ℤ, cechTermAltZ U M i ⟶ cechTermAltZ U N i
  | Int.ofNat p => cechTermAltMap U φ p
  | Int.negSucc _ => 0

theorem cechTermAltZMap_comm {M N : X.Modules} (φ : M ⟶ N) (i j : ℤ)
    (hij : (ComplexShape.up ℤ).Rel i j) :
    cechTermAltZMap U φ i ≫ (cechComplexAlt U N).d i j =
      (cechComplexAlt U M).d i j ≫ cechTermAltZMap U φ j := by
  obtain rfl : i + 1 = j := hij
  cases i with
  | ofNat p =>
    rw [show (cechComplexAlt U N).d (Int.ofNat p) (Int.ofNat p + 1) = cechDiffAlt U N p from
        cechComplexAlt_d U N p,
      show (cechComplexAlt U M).d (Int.ofNat p) (Int.ofNat p + 1) = cechDiffAlt U M p from
        cechComplexAlt_d U M p]
    exact cechTermAltMap_comm U φ p
  | negSucc k =>
    exact (Limits.zero_comp).trans
      ((ModuleCat.isZero_of_subsingleton (ModuleCat.of Γ(X, ⊤) PUnit)).eq_of_src _ _)

/-- The chain map `Č_alt(U, M) ⟶ Č_alt(U, N)`. -/
def cechComplexAltMap {M N : X.Modules} (φ : M ⟶ N) : cechComplexAlt U M ⟶ cechComplexAlt U N where
  f := cechTermAltZMap U φ
  comm' := cechTermAltZMap_comm U φ

theorem cechComplexAltMap_f_ofNat {M N : X.Modules} (φ : M ⟶ N) (p : ℕ) :
    (cechComplexAltMap U φ).f (p : ℤ) = cechTermAltMap U φ p := rfl

/-- On families of sections, the chain map acts componentwise by `φ(U_σ)`. -/
theorem cechToFamily_map {M N : X.Modules} (φ : M ⟶ N) (p : ℕ) (x : cechTermAlt U M p)
    (σ : Fin (p + 1) ↪o Fin n) :
    cechToFamily U N p ((cechTermAltMap U φ p).hom x) σ = φ.app _ (cechToFamily U M p x σ) := by
  have h : cechTermAltMap U φ p ≫ Pi.π (fun σ : Fin (p + 1) ↪o Fin n =>
      N.sectionsOverTop (⨅ k, U (σ k))) σ = Pi.π _ σ ≫ sectionsOverTopMap φ (⨅ k, U (σ k)) :=
    Limits.Pi.map_π _ σ
  exact congrArg (fun ψ => ψ.hom x) h

theorem cechTermAltMap_comp {M N P : X.Modules} (φ : M ⟶ N) (ψ : N ⟶ P) (p : ℕ) :
    cechTermAltMap U (φ ≫ ψ) p = cechTermAltMap U φ p ≫ cechTermAltMap U ψ p := by
  ext x
  apply (cechToFamily_bijective U P p).1
  funext σ
  show cechToFamily U P p ((cechTermAltMap U (φ ≫ ψ) p).hom x) σ =
    cechToFamily U P p ((cechTermAltMap U ψ p).hom ((cechTermAltMap U φ p).hom x)) σ
  rw [cechToFamily_map, cechToFamily_map, cechToFamily_map]
  rfl

theorem cechTermAltMap_zero (M N : X.Modules) (p : ℕ) :
    cechTermAltMap U (0 : M ⟶ N) p = 0 := by
  ext x
  apply (cechToFamily_bijective U N p).1
  funext σ
  show cechToFamily U N p ((cechTermAltMap U (0 : M ⟶ N) p).hom x) σ = cechToFamily U N p 0 σ
  rw [cechToFamily_map]
  exact (map_zero _).symm

theorem cechComplexAltMap_comp {M N P : X.Modules} (φ : M ⟶ N) (ψ : N ⟶ P) :
    cechComplexAltMap U (φ ≫ ψ) = cechComplexAltMap U φ ≫ cechComplexAltMap U ψ := by
  refine HomologicalComplex.hom_ext _ _ fun i => ?_
  cases i with
  | ofNat p => exact cechTermAltMap_comp U φ ψ p
  | negSucc k => exact (ModuleCat.isZero_of_subsingleton (ModuleCat.of Γ(X, ⊤) PUnit)).eq_of_src _ _

theorem cechComplexAltMap_zero (M N : X.Modules) :
    cechComplexAltMap U (0 : M ⟶ N) = 0 := by
  refine HomologicalComplex.hom_ext _ _ fun i => ?_
  cases i with
  | ofNat p => exact cechTermAltMap_zero U M N p
  | negSucc k => exact (ModuleCat.isZero_of_subsingleton (ModuleCat.of Γ(X, ⊤) PUnit)).eq_of_src _ _

/-- The short complex of Čech complexes induced by a short complex of modules. -/
def cechShortComplex (S : ShortComplex X.Modules) :
    ShortComplex (CochainComplex (ModuleCat.{u} Γ(X, ⊤)) ℤ) :=
  ShortComplex.mk (cechComplexAltMap U S.f) (cechComplexAltMap U S.g)
    (by rw [← cechComplexAltMap_comp, S.zero, cechComplexAltMap_zero])

/-- Degreewise: `0 → ∏F(U_σ) → ∏G(U_σ) → ∏R(U_σ) → 0` is short exact. -/
theorem cechTermAlt_shortExact (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (hsurj : ∀ (q : ℕ) (σ : Fin (q + 1) ↪o Fin n), Function.Surjective (S.g.app (⨅ k, U (σ k))))
    (p : ℕ) :
    (ShortComplex.mk (cechTermAltMap U S.f p) (cechTermAltMap U S.g p)
      (by rw [← cechTermAltMap_comp, S.zero, cechTermAltMap_zero])).ShortExact := by
  have hmono : Mono S.f := hS.mono_f
  refine
    { exact := ?_
      mono_f := ?_
      epi_g := ?_ }
  · rw [ShortComplex.moduleCat_exact_iff]
    intro x hx
    obtain ⟨x', rfl⟩ : ∃ x' : ↑(cechTermAlt U S.X₂ p), x' = x := ⟨x, rfl⟩
    have hx' : ∀ σ, S.g.app _ (cechToFamily U S.X₂ p x' σ) = 0 := by
      intro σ
      rw [← cechToFamily_map]
      exact (congrArg (fun y => cechToFamily U S.X₃ p y σ) hx).trans (map_zero _)
    choose z hz using fun σ =>
      (ModulesLocLiftAux.sections_of_exact_mono S hS.exact _).2 _ (hx' σ)
    obtain ⟨y, rfl⟩ := (cechToFamily_bijective U S.X₁ p).2 z
    refine ⟨y, (cechToFamily_bijective U S.X₂ p).1 (funext fun σ => ?_)⟩
    exact (cechToFamily_map U S.f p y σ).trans (hz σ)
  · refine (ModuleCat.mono_iff_injective _).2 fun x y hxy => ?_
    obtain ⟨x', rfl⟩ : ∃ x' : ↑(cechTermAlt U S.X₁ p), x' = x := ⟨x, rfl⟩
    obtain ⟨y', rfl⟩ : ∃ y' : ↑(cechTermAlt U S.X₁ p), y' = y := ⟨y, rfl⟩
    apply (cechToFamily_bijective U S.X₁ p).1
    funext σ
    apply (ModulesLocLiftAux.sections_of_exact_mono S hS.exact _).1
    rw [← cechToFamily_map, ← cechToFamily_map]
    exact congrArg (fun y => cechToFamily U S.X₂ p y σ) hxy
  · refine (ModuleCat.epi_iff_surjective _).2 fun y => ?_
    obtain ⟨y', rfl⟩ : ∃ y' : ↑(cechTermAlt U S.X₃ p), y' = y := ⟨y, rfl⟩
    choose z hz using fun σ => hsurj p σ (cechToFamily U S.X₃ p y' σ)
    obtain ⟨x, rfl⟩ := (cechToFamily_bijective U S.X₂ p).2 z
    refine ⟨x, (cechToFamily_bijective U S.X₃ p).1 (funext fun σ => ?_)⟩
    exact (cechToFamily_map U S.g p x σ).trans (hz σ)

/-- Step 2 of the proof of Hartshorne III.4.5: if `0 → F → G → R → 0` is exact and
`G(U_σ) → R(U_σ)` is surjective for every `σ`, then the sequence of Čech complexes
`0 → C(F) → C(G) → C(R) → 0` is exact (degreewise a product of the exact sequences
`0 → F(U_σ) → G(U_σ) → R(U_σ) → 0`). -/
theorem cechShortComplex_shortExact (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (hsurj : ∀ (q : ℕ) (σ : Fin (q + 1) ↪o Fin n), Function.Surjective (S.g.app (⨅ k, U (σ k)))) :
    (cechShortComplex U S).ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun i => ?_
  cases i with
  | negSucc k =>
    have hz : ∀ M : X.Modules, IsZero ((cechComplexAlt U M).X (Int.negSucc k)) := fun M =>
      ModuleCat.isZero_of_subsingleton (ModuleCat.of Γ(X, ⊤) PUnit)
    exact
      { exact := ShortComplex.exact_of_isZero_X₂ _ (hz S.X₂)
        mono_f := ⟨fun _ _ _ => (hz S.X₁).eq_of_tgt _ _⟩
        epi_g := ⟨fun _ _ _ => (hz S.X₃).eq_of_src _ _⟩ }
  | ofNat p => exact cechTermAlt_shortExact U S hS hsurj p

end AlgebraicGeometry.Scheme.Modules

end
