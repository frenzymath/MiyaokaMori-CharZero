import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModulesStalkExact
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModulesStalkFunctor
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModulesSupport
import MiyaokaMori.AlgebraicGeometry.Varieties.Points.PointClosureSubscheme
import MiyaokaMori.AlgebraicGeometry.Cohomology.EulerCharacteristic.EulerCharacteristic
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.ModulesLineBundleZpow
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.IsLineBundleZpow
import MiyaokaMori.AlgebraicGeometry.Chow.Snapper.SnapperFullSupportStep
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModulesSupportBasics
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.TwistByLineBundleList
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.CoherentStalkLengthAtMaximalPoint
import Mathlib.Topology.KrullDimension

/-! # Bookkeeping for the low-degree defect in Stacks 0BEN

Bookkeeping for Stacks 0BEN: the invariant

  `defect F n := χ(X, F ⊗ L^n) − Σ_{ξ : dim closure{ξ} = d} (length F_ξ).toNat · χ(Z_ξ, (L|_{Z_ξ})^n)`

(`Z_ξ = X.pointClosure ξ`, `L^n = L₁^{n₁} ⊗ ⋯ ⊗ L_r^{n_r}` as `twistList`), the property
`Good F := defect F is given by a polynomial that is 0 or of total degree < d`, and the facts about
them used in the dévissage:

* topology: `topologicalKrullDim` is monotone in the subset; a point `ξ` with `dim closure{ξ} = d`
  in a closed `T` with `dim T ≤ d` has no proper generalization in `T` (`Order.height_add_one_le`);
  the set of such `ξ` is finite (they are generic points of irreducible components of the Noetherian
  space `T`);
* support: the support of a quotient is contained in the support (the stalk functor preserves colimits);
  a point outside the support has a subsingleton stalk;
* length: `length` of stalks is additive on short exact sequences (the stalk functor is exact,
  `Module.length_eq_add_of_exact`), hence so is `mult := (length).toNat` when the lengths are finite;
* `χ` of the twist of a zero object is `0` (additivity on `0 → F → F → F → 0`);
* `defect` is additive on short exact sequences of coherent sheaves supported in a closed `T` of
  dimension `≤ d` (Stacks 0BEN, proof, "additivity" paragraph: `χ` additive by 08AA after twisting,
  lengths additive by 00IV);
* `IsLowDegree` is closed under `+`, `−`.

Source: Stacks 0BEN (proof, first two paragraphs).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Topology
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Stacks0ben

/-! ### Low-degree polynomials -/

/-- `Q = 0` or `totalDegree Q < d`. -/
def IsLowDegree {r : ℕ} (d : ℕ) (Q : MvPolynomial (Fin r) ℚ) : Prop := Q = 0 ∨ Q.totalDegree < d

theorem isLowDegree_zero {r : ℕ} (d : ℕ) : IsLowDegree d (0 : MvPolynomial (Fin r) ℚ) := Or.inl rfl

theorem isLowDegree_of_totalDegree_le {r : ℕ} {d e : ℕ} {Q : MvPolynomial (Fin r) ℚ}
    (hQ : Q.totalDegree ≤ e) (he : e < d) : IsLowDegree d Q := Or.inr (lt_of_le_of_lt hQ he)

theorem isLowDegree_add {r : ℕ} {d : ℕ} {P Q : MvPolynomial (Fin r) ℚ} (hP : IsLowDegree d P)
    (hQ : IsLowDegree d Q) : IsLowDegree d (P + Q) := by
  rcases hP with rfl | hP
  · simpa using hQ
  rcases hQ with rfl | hQ
  · rw [add_zero]; exact Or.inr hP
  exact Or.inr (lt_of_le_of_lt (MvPolynomial.totalDegree_add P Q) (max_lt hP hQ))

theorem isLowDegree_neg {r : ℕ} {d : ℕ} {P : MvPolynomial (Fin r) ℚ} (hP : IsLowDegree d P) :
    IsLowDegree d (-P) := by
  rcases hP with rfl | hP
  · exact Or.inl (neg_zero)
  · exact Or.inr (by rwa [MvPolynomial.totalDegree_neg])

theorem isLowDegree_sub {r : ℕ} {d : ℕ} {P Q : MvPolynomial (Fin r) ℚ} (hP : IsLowDegree d P)
    (hQ : IsLowDegree d Q) : IsLowDegree d (P - Q) := by
  rw [sub_eq_add_neg]
  exact isLowDegree_add hP (isLowDegree_neg hQ)

/-! ### Topology -/

/-- `topologicalKrullDim` is monotone in the subset. -/
theorem topologicalKrullDim_mono {Y : Type*} [TopologicalSpace Y] {S S' : Set Y} (h : S ⊆ S') :
    topologicalKrullDim S ≤ topologicalKrullDim S' := by
  let g : S → S' := fun s => ⟨s.1, h s.2⟩
  have hg : Continuous g := continuous_subtype_val.subtype_mk _
  have hcomp : IsInducing ((Subtype.val : S' → Y) ∘ g) := by
    have : (Subtype.val : S' → Y) ∘ g = (Subtype.val : S → Y) := funext fun _ => rfl
    rw [this]
    exact IsInducing.subtypeVal
  exact (IsInducing.of_comp hg continuous_subtype_val hcomp).topologicalKrullDim_le

/-- A point `ξ` with `dim closure{ξ} = d` inside a closed set `T` of dimension `≤ d` has no proper
generalization in `T` (Stacks 0BEN, proof, first paragraph: "`ξ` is a generic point of an irreducible
component of `Supp F`"). -/
theorem eq_of_specializes_of_dim_closure_eq {X : AlgebraicGeometry.Scheme.{u}} {T : Set X}
    (hT : IsClosed T) {d : ℕ} (hTd : topologicalKrullDim T ≤ (d : WithBot ℕ∞)) {ξ η : X}
    (hξ : topologicalKrullDim (closure {ξ} : Set X) = (d : WithBot ℕ∞)) (hη : η ∈ T)
    (hηξ : η ⤳ ξ) : η = ξ := by
  by_contra hne
  have hle : ξ ≤ η := hηξ
  have hlt : ξ < η := lt_of_le_not_ge hle fun h => hne (hηξ.antisymm h).eq
  have h1 : Order.height ξ + 1 ≤ Order.height η := Order.height_add_one_le hlt
  have hξh : ((Order.height ξ : ℕ∞) : WithBot ℕ∞) = (d : WithBot ℕ∞) :=
    (AlgebraicGeometry.Intersection.pointClosureDimension_eq_topologicalKrullDim_closure X ξ).trans hξ
  have hξd : Order.height ξ = (d : ℕ∞) := by exact_mod_cast hξh
  have hηsub : (closure {η} : Set X) ⊆ T :=
    hT.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hη)
  have hηh : ((Order.height η : ℕ∞) : WithBot ℕ∞) ≤ (d : WithBot ℕ∞) := by
    rw [show ((Order.height η : ℕ∞) : WithBot ℕ∞) = topologicalKrullDim (closure {η} : Set X) from
      AlgebraicGeometry.Intersection.pointClosureDimension_eq_topologicalKrullDim_closure X η]
    exact le_trans (topologicalKrullDim_mono hηsub) hTd
  have hηd : Order.height η ≤ (d : ℕ∞) := by exact_mod_cast hηh
  rw [hξd] at h1
  have h2 : ((d + 1 : ℕ) : ℕ∞) ≤ (d : ℕ∞) := by
    push_cast
    exact h1.trans hηd
  have h3 : d + 1 ≤ d := by exact_mod_cast h2
  omega

/-- Two points whose closures have the same finite dimension `d`, one specializing to the other, are
equal. -/
theorem eq_of_mem_closure_of_dim_closure_eq {X : AlgebraicGeometry.Scheme.{u}} {d : ℕ} {ξ η : X}
    (hξ : topologicalKrullDim (closure {ξ} : Set X) = (d : WithBot ℕ∞))
    (hη : topologicalKrullDim (closure {η} : Set X) = (d : WithBot ℕ∞))
    (hmem : η ∈ closure ({ξ} : Set X)) : η = ξ := by
  have hξη : ξ ⤳ η := specializes_iff_mem_closure.mpr hmem
  exact (eq_of_specializes_of_dim_closure_eq isClosed_closure hξ.le hη (subset_closure rfl) hξη).symm

/-- In a Noetherian scheme, the points `ξ` of a closed set `T` with `dim T ≤ d` and
`dim closure{ξ} = d` are finitely many (generic points of irreducible components of `T`). -/
theorem finite_setOf_dim_closure_eq {X : AlgebraicGeometry.Scheme.{u}} [NoetherianSpace X]
    {T : Set X} (hT : IsClosed T) {d : ℕ} (hTd : topologicalKrullDim T ≤ (d : WithBot ℕ∞)) :
    {ξ : X | ξ ∈ T ∧ topologicalKrullDim (closure {ξ} : Set X) = (d : WithBot ℕ∞)}.Finite := by
  classical
  have hqs : QuasiSober T := hT.isClosedEmbedding_subtypeVal.quasiSober
  have hfin : (genericPoints T).Finite :=
    genericPoints.finite (NoetherianSpace.finite_irreducibleComponents (α := T))
  refine (hfin.image Subtype.val).subset ?_
  rintro ξ ⟨hξT, hξd⟩
  refine ⟨⟨ξ, hξT⟩, ?_, rfl⟩
  -- `closure {⟨ξ, _⟩}` is an irreducible component of `T`
  show closure ({⟨ξ, hξT⟩} : Set T) ∈ irreducibleComponents T
  refine ⟨isIrreducible_singleton.closure, fun t ht hsub => ?_⟩
  -- `t ⊆ closure t = closure {γ}` for the generic point `γ` of `closure t`; `γ ⤳ ξ`, so `γ = ξ`
  have hγ : IsGenericPoint ht.genericPoint (closure t) := ht.isGenericPoint_genericPoint_closure
  have hξt : (⟨ξ, hξT⟩ : T) ∈ closure t := subset_closure (hsub (subset_closure rfl))
  have hγξ : ht.genericPoint ⤳ (⟨ξ, hξT⟩ : T) := hγ.specializes hξt
  have hγξ' : (ht.genericPoint : X) ⤳ ξ := hγξ.map continuous_subtype_val
  have heq : (ht.genericPoint : X) = ξ :=
    eq_of_specializes_of_dim_closure_eq hT hTd hξd ht.genericPoint.2 hγξ'
  have heq' : ht.genericPoint = (⟨ξ, hξT⟩ : T) := Subtype.ext heq
  calc t ⊆ closure t := subset_closure
    _ = closure {ht.genericPoint} := hγ.def.symm
    _ = closure {(⟨ξ, hξT⟩ : T)} := by rw [heq']

/-! ### Support and stalks -/

/-- Points outside the support have subsingleton stalks. -/
theorem subsingleton_stalk_of_notMem_support {X : AlgebraicGeometry.Scheme.{u}} (F : X.Modules)
    {x : X} (hx : x ∉ F.support) : Subsingleton (F.stalk x) :=
  not_nontrivial_iff_subsingleton.mp hx

/-- A quotient has smaller support (the stalk functor preserves colimits, so epi ↦ surjective). -/
theorem support_subset_of_epi {X : AlgebraicGeometry.Scheme.{u}} {F G : X.Modules} (π : F ⟶ G)
    [Epi π] : G.support ⊆ F.support := by
  intro x hx
  rw [Scheme.Modules.mem_support_iff] at hx ⊢
  have hpres : PreservesColimits (AlgebraicGeometry.Scheme.Modules.stalkFunctor x) :=
    (Scheme.Modules.stalk_preservesFiniteLimits_colimits x).2
  have hepi : Epi ((AlgebraicGeometry.Scheme.Modules.stalkFunctor x).map π) :=
    preserves_epi_of_preservesColimit _ π
  have hsurj : Function.Surjective ((AlgebraicGeometry.Scheme.Modules.stalkFunctor x).map π) :=
    (ModuleCat.epi_iff_surjective _).mp hepi
  have hG : Nontrivial ((AlgebraicGeometry.Scheme.Modules.stalkFunctor x).obj G) := hx
  exact hsurj.nontrivial

/-- The stalk of a zero object is a subsingleton. -/
theorem subsingleton_stalk_of_isZero {X : AlgebraicGeometry.Scheme.{u}} {F : X.Modules}
    (hF : IsZero F) (x : X) : Subsingleton (F.stalk x) := by
  have hpres : PreservesFiniteLimits (AlgebraicGeometry.Scheme.Modules.stalkFunctor x) :=
    (Scheme.Modules.stalk_preservesFiniteLimits_colimits x).1
  have hz : IsZero ((AlgebraicGeometry.Scheme.Modules.stalkFunctor x).obj F) :=
    (AlgebraicGeometry.Scheme.Modules.stalkFunctor x).map_isZero hF
  exact ModuleCat.isZero_iff_subsingleton.mp hz

/-- Length of stalks is additive on short exact sequences (the stalk functor is exact). -/
theorem length_stalk_add_of_shortExact {X : AlgebraicGeometry.Scheme.{u}}
    (S : CategoryTheory.ShortComplex X.Modules) (hS : S.ShortExact) (x : X) :
    Module.length (X.presheaf.stalk x) (S.X₂.stalk x) =
      Module.length (X.presheaf.stalk x) (S.X₁.stalk x) +
        Module.length (X.presheaf.stalk x) (S.X₃.stalk x) := by
  have hpres1 : PreservesFiniteLimits (AlgebraicGeometry.Scheme.Modules.stalkFunctor x) :=
    (Scheme.Modules.stalk_preservesFiniteLimits_colimits x).1
  have hpres2 : PreservesColimits (AlgebraicGeometry.Scheme.Modules.stalkFunctor x) :=
    (Scheme.Modules.stalk_preservesFiniteLimits_colimits x).2
  have hmono : Mono S.f := hS.mono_f
  have hepi : Epi S.g := hS.epi_g
  have hmono' : Mono ((AlgebraicGeometry.Scheme.Modules.stalkFunctor x).map S.f) :=
    preserves_mono_of_preservesLimit _ S.f
  have hepi' : Epi ((AlgebraicGeometry.Scheme.Modules.stalkFunctor x).map S.g) :=
    preserves_epi_of_preservesColimit _ S.g
  have hS' : (S.map (AlgebraicGeometry.Scheme.Modules.stalkFunctor x)).ShortExact :=
    hS.map (AlgebraicGeometry.Scheme.Modules.stalkFunctor x)
  have hinj : Function.Injective (S.map (AlgebraicGeometry.Scheme.Modules.stalkFunctor x)).f :=
    hS'.moduleCat_injective_f
  have hsurj : Function.Surjective (S.map (AlgebraicGeometry.Scheme.Modules.stalkFunctor x)).g :=
    hS'.moduleCat_surjective_g
  have hex : Function.Exact (S.map (AlgebraicGeometry.Scheme.Modules.stalkFunctor x)).f
      (S.map (AlgebraicGeometry.Scheme.Modules.stalkFunctor x)).g :=
    (CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hS'.exact
  exact Module.length_eq_add_of_exact
    (S.map (AlgebraicGeometry.Scheme.Modules.stalkFunctor x)).f.hom
    (S.map (AlgebraicGeometry.Scheme.Modules.stalkFunctor x)).g.hom hinj hsurj hex

/-! ### The 0BEN invariant -/

variable (k : Type u) [Field k] (X : AlgebraicGeometry.Scheme.{u})
  [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]

/-- `χ(Z_ξ, (L₁|_{Z_ξ})^{n₁} ⊗ ⋯ ⊗ (L_r|_{Z_ξ})^{n_r})` for `Z_ξ = X.pointClosure ξ` with the `k`-structure
`pointClosureι ξ ≫ (X ↘ Spec k)`. -/
def componentChi {r : ℕ} (L : Fin r → X.Modules) (ξ : X) (n : Fin r → ℤ) : ℚ :=
  letI : (AlgebraicGeometry.Scheme.pointClosure ξ).Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨AlgebraicGeometry.Scheme.pointClosureι ξ ≫ (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  (AlgebraicGeometry.sheafEulerCharacteristic (k := k) (AlgebraicGeometry.Scheme.pointClosure ξ)
    (Scheme.Modules.twistList
      (fun i => (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.pointClosureι ξ)).obj
        (L i) ^ n i)
      (List.finRange r) (SheafOfModules.unit (AlgebraicGeometry.Scheme.pointClosure ξ).ringCatSheaf)) : ℚ)

/-- The multiplicity `(length_{O_{X,ξ}} F_ξ).toNat`, as a rational number. -/
def mult (F : X.Modules) (ξ : X) : ℚ :=
  ((Module.length (X.presheaf.stalk ξ) (F.stalk ξ)).toNat : ℚ)

/-- The 0BEN invariant `χ(X, F ⊗ L^n) − Σ_{dim closure{ξ} = d} mult F ξ · χ(Z_ξ, (L|_{Z_ξ})^n)`. -/
def defect {r : ℕ} (L : Fin r → X.Modules) (d : ℕ) (F : X.Modules) (n : Fin r → ℤ) : ℚ :=
  (AlgebraicGeometry.sheafEulerCharacteristic (k := k) X
      (Scheme.Modules.twistList (fun i => L i ^ n i) (List.finRange r) F) : ℚ)
    - ∑ᶠ (ξ : X) (_ : topologicalKrullDim (closure {ξ} : Set X) = (d : WithBot ℕ∞)),
        mult X F ξ * componentChi k X L ξ n

/-- `defect F` is given by a polynomial that is `0` or of total degree `< d`. -/
def Good {r : ℕ} (L : Fin r → X.Modules) (d : ℕ) (F : X.Modules) : Prop :=
  ∃ Q : MvPolynomial (Fin r) ℚ, IsLowDegree d Q ∧
    ∀ n : Fin r → ℤ, defect k X L d F n = MvPolynomial.eval (fun i => (n i : ℚ)) Q

variable {X}

theorem mult_eq_zero_of_notMem_support (F : X.Modules) {ξ : X} (hξ : ξ ∉ F.support) :
    mult X F ξ = 0 := by
  have := subsingleton_stalk_of_notMem_support F hξ
  unfold mult
  rw [Module.length_eq_zero]
  simp

theorem mult_eq_zero_of_isZero {F : X.Modules} (hF : IsZero F) (ξ : X) : mult X F ξ = 0 := by
  have := subsingleton_stalk_of_isZero hF ξ
  unfold mult
  rw [Module.length_eq_zero]
  simp

/-- `χ` of the twist of a zero object vanishes: additivity on `0 → F → F → F → 0`. -/
theorem sheafEulerCharacteristic_twistList_of_isZero (hX : IsProperOver k X) {r : ℕ}
    (𝓜 : Fin r → X.Modules) [∀ i, (𝓜 i).IsLineBundle] (l : List (Fin r)) (F : X.Modules)
    [F.IsCoherent] (hF : IsZero F) :
    AlgebraicGeometry.sheafEulerCharacteristic (k := k) X (Scheme.Modules.twistList 𝓜 l F) = 0 := by
  let S : CategoryTheory.ShortComplex X.Modules :=
    CategoryTheory.ShortComplex.mk (𝟙 F) (𝟙 F) (hF.eq_of_src _ _)
  have hS : S.ShortExact :=
    { exact := CategoryTheory.ShortComplex.exact_of_isZero_X₂ S hF
      mono_f := inferInstanceAs (Mono (𝟙 F))
      epi_g := inferInstanceAs (Epi (𝟙 F)) }
  have : S.X₁.IsCoherent := ‹F.IsCoherent›
  have : S.X₂.IsCoherent := ‹F.IsCoherent›
  have : S.X₃.IsCoherent := ‹F.IsCoherent›
  have h := Scheme.Modules.sheafEulerCharacteristic_twistList_shortExact hX 𝓜 l S hS
  change AlgebraicGeometry.sheafEulerCharacteristic (k := k) X (Scheme.Modules.twistList 𝓜 l F)
    = AlgebraicGeometry.sheafEulerCharacteristic (k := k) X (Scheme.Modules.twistList 𝓜 l F)
      + AlgebraicGeometry.sheafEulerCharacteristic (k := k) X (Scheme.Modules.twistList 𝓜 l F) at h
  linarith

/-- The zero object is `Good` (its defect is identically `0`). -/
theorem good_of_isZero (hX : IsProperOver k X) {r : ℕ} (L : Fin r → X.Modules)
    [∀ i, (L i).IsLineBundle] (d : ℕ) (F : X.Modules) [F.IsCoherent] (hF : IsZero F) :
    Good k X L d F := by
  refine ⟨0, isLowDegree_zero d, fun n => ?_⟩
  unfold defect
  rw [sheafEulerCharacteristic_twistList_of_isZero k hX (fun i => L i ^ n i) (List.finRange r) F hF]
  simp [mult_eq_zero_of_isZero hF]

/-- Additivity of `mult` at a point `ξ` with `dim closure{ξ} = d` for a short exact sequence of coherent
sheaves supported in a closed `T` with `dim T ≤ d` (lengths finite at a maximal point of `T`,
additive by `length_stalk_add_of_shortExact`). -/
theorem mult_add_of_shortExact [AlgebraicGeometry.IsLocallyNoetherian X]
    (S : CategoryTheory.ShortComplex X.Modules) (hS : S.ShortExact)
    [S.X₁.IsCoherent] [S.X₃.IsCoherent] {T : Set X} (hT : IsClosed T) {d : ℕ}
    (hTd : topologicalKrullDim T ≤ (d : WithBot ℕ∞)) (h₁ : S.X₁.support ⊆ T) (h₃ : S.X₃.support ⊆ T)
    {ξ : X} (hξ : topologicalKrullDim (closure {ξ} : Set X) = (d : WithBot ℕ∞)) :
    mult X S.X₂ ξ = mult X S.X₁ ξ + mult X S.X₃ ξ := by
  have hfin : ∀ (F : X.Modules) [F.IsCoherent], F.support ⊆ T →
      Module.length (X.presheaf.stalk ξ) (F.stalk ξ) ≠ ⊤ := fun F _ hF =>
    Scheme.Modules.length_stalk_ne_top_of_forall_specializes F ξ fun η hηξ hη =>
      eq_of_specializes_of_dim_closure_eq hT hTd hξ (hF hη) hηξ
  have h1 := hfin S.X₁ h₁
  have h3 := hfin S.X₃ h₃
  unfold mult
  rw [length_stalk_add_of_shortExact S hS ξ, ENat.toNat_add h1 h3]
  push_cast
  ring

/-- **Additivity of the 0BEN invariant** on short exact sequences of coherent sheaves supported in a
closed set of dimension `≤ d` (Stacks 0BEN, proof, "additivity" paragraph). -/
theorem defect_add (hX : IsProperOver k X) {r : ℕ} (L : Fin r → X.Modules)
    [∀ i, (L i).IsLineBundle] (d : ℕ) (S : CategoryTheory.ShortComplex X.Modules) (hS : S.ShortExact)
    [S.X₁.IsCoherent] [S.X₂.IsCoherent] [S.X₃.IsCoherent] {T : Set X} (hT : IsClosed T)
    (hTd : topologicalKrullDim T ≤ (d : WithBot ℕ∞)) (h₁ : S.X₁.support ⊆ T) (h₃ : S.X₃.support ⊆ T)
    (n : Fin r → ℤ) :
    defect k X L d S.X₂ n = defect k X L d S.X₁ n + defect k X L d S.X₃ n := by
  have hloc : AlgebraicGeometry.IsLocallyNoetherian X := isLocallyNoetherian_of_isProperOver X hX
  have hnoeth : NoetherianSpace X := noetherianSpace_of_isProperOver X hX
  have hχ := Scheme.Modules.sheafEulerCharacteristic_twistList_shortExact hX (fun i => L i ^ n i)
    (List.finRange r) S hS
  -- finiteness of the supports of the summands
  have hfinT := finite_setOf_dim_closure_eq hT hTd
  have hsupp : ∀ (F : X.Modules), F.support ⊆ T →
      ({ξ : X | topologicalKrullDim (closure {ξ} : Set X) = (d : WithBot ℕ∞)} ∩
        Function.support (fun ξ => mult X F ξ * componentChi k X L ξ n)).Finite := fun F hF => by
    refine hfinT.subset ?_
    rintro ξ ⟨hξd, hξs⟩
    refine ⟨?_, hξd⟩
    by_contra hξT
    have hξF : ξ ∉ F.support := fun h => hξT (hF h)
    refine hξs ?_
    show mult X F ξ * componentChi k X L ξ n = 0
    rw [mult_eq_zero_of_notMem_support F hξF, zero_mul]
  have hsum : (∑ᶠ (ξ : X) (_ : topologicalKrullDim (closure {ξ} : Set X) = (d : WithBot ℕ∞)),
      mult X S.X₂ ξ * componentChi k X L ξ n)
      = (∑ᶠ (ξ : X) (_ : topologicalKrullDim (closure {ξ} : Set X) = (d : WithBot ℕ∞)),
          mult X S.X₁ ξ * componentChi k X L ξ n)
        + ∑ᶠ (ξ : X) (_ : topologicalKrullDim (closure {ξ} : Set X) = (d : WithBot ℕ∞)),
          mult X S.X₃ ξ * componentChi k X L ξ n := by
    change (∑ᶠ (ξ : X) (_ : ξ ∈ {ξ : X | topologicalKrullDim (closure {ξ} : Set X) = (d : WithBot ℕ∞)}),
        mult X S.X₂ ξ * componentChi k X L ξ n)
      = (∑ᶠ (ξ : X) (_ : ξ ∈ {ξ : X | topologicalKrullDim (closure {ξ} : Set X) = (d : WithBot ℕ∞)}),
          mult X S.X₁ ξ * componentChi k X L ξ n)
        + ∑ᶠ (ξ : X) (_ : ξ ∈ {ξ : X | topologicalKrullDim (closure {ξ} : Set X) = (d : WithBot ℕ∞)}),
          mult X S.X₃ ξ * componentChi k X L ξ n
    rw [← finsum_mem_add_distrib' (hsupp S.X₁ h₁) (hsupp S.X₃ h₃)]
    refine finsum_mem_congr rfl fun ξ hξ => ?_
    rw [mult_add_of_shortExact S hS hT hTd h₁ h₃ hξ]
    ring
  unfold defect
  rw [hχ, hsum]
  push_cast
  ring

end AlgebraicGeometry.Stacks0ben

end
