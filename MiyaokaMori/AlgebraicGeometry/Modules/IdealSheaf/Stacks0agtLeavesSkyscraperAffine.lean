import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.Stacks0agtLeavesQuotFamilies
import MiyaokaMori.RingTheory.Stacks0agtLeavesSkyscraperLocalizedQuot

/-! # Affine-local step of the skyscraper decomposition

`X` locally Noetherian, `J ≤ K` ideal sheaves, `T` a finite set of closed points with `K_x = J_x`
for `x ∉ T`. For an affine open `V` with `B := Γ(X, V)` and `G_V := K(V)/J(V)` (the
`B`-submodule `Submodule.map (J V).mkQ (K V)` of `B/J(V)`), the germ map
`G_V → Π_{x ∈ T ∩ V} K_x/J_x` is bijective (`quotGermLoc_pi_bijective`, stated over the set of
primes `primesOfPoints V T = {𝔭_x : x ∈ T ∩ V}` of `B`), hence
* `quotGerm_injective_of_stalkIdeal_eq`: two elements of `G_V` with the same germs at all
  `x ∈ T ∩ V` are equal;
* `exists_quotGerm_eq_of_stalkIdeal_eq`: any family of germs `(n_x)_{x ∈ T}`, `n_x ∈ K_x/J_x`,
  is realized on `V` by some `g ∈ G_V`.

Dictionary used (all Mathlib): `O_{X,x} = B_{𝔭_x}` (`IsAffineOpen.isLocalization_stalk'`),
`𝔭_x := primeIdealOf x`, every prime `q` of `B` is `𝔭_y` for `y := fromSpec q ∈ V`
(`range_fromSpec`, `fromSpec_primeIdealOf`), closed points give maximal ideals
(`primeIdealOf_isMaximal_of_isClosed`), and `K_x = K(V)·O_{X,x}` (`stalkIdeal_eq_map_germ`).

Used by `Stacks0agtLeavesSkyscraper`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
open scoped AlgebraicGeometry.Scheme.IdealSheafData.QuotFamilies0agt

noncomputable section

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : AlgebraicGeometry.Scheme.{u}}

/-! ### The prime ↔ point dictionary on an affine open -/

theorem fromSpec_mem_affineOpens (V : X.affineOpens) (q : PrimeSpectrum Γ(X, V)) :
    V.2.fromSpec q ∈ V.1 := by
  have : V.2.fromSpec q ∈ Set.range V.2.fromSpec := Set.mem_range_self q
  rwa [V.2.range_fromSpec] at this

theorem primeIdealOf_fromSpec_affineOpens (V : X.affineOpens) (q : PrimeSpectrum Γ(X, V)) :
    V.2.primeIdealOf ⟨V.2.fromSpec q, fromSpec_mem_affineOpens V q⟩ = q := by
  have hV : AlgebraicGeometry.IsAffineOpen V.1 := V.2
  apply hV.fromSpec.isOpenEmbedding.injective
  exact hV.fromSpec_primeIdealOf ⟨hV.fromSpec q, fromSpec_mem_affineOpens V q⟩

/-- The primes `𝔭_x` of `Γ(X, V)` of the points `x ∈ T ∩ V`. -/
def primesOfPoints (V : X.affineOpens) (T : Finset X) : Set (PrimeSpectrum Γ(X, V)) :=
  (fun x : V.1 => V.2.primeIdealOf x) '' {x : V.1 | x.1 ∈ T}

theorem primesOfPoints_finite (V : X.affineOpens) (T : Finset X) : (primesOfPoints V T).Finite :=
  Set.Finite.image _ (T.finite_toSet.preimage Subtype.val_injective.injOn)

theorem fromSpec_mem_of_mem_primesOfPoints (V : X.affineOpens) (T : Finset X)
    {q : PrimeSpectrum Γ(X, V)} (hq : q ∈ primesOfPoints V T) : V.2.fromSpec q ∈ T := by
  obtain ⟨x, hxT, rfl⟩ := hq
  rw [V.2.fromSpec_primeIdealOf x]
  exact hxT

/-! ### The germ map `K(V)/J(V) → K_x/J_x` as a `Γ(X, V)`-linear localization map -/

variable (J K : X.IdealSheafData)

theorem stalkIdeal_eq_map_algebraMap (V : X.affineOpens) (x : V.1) :
    J.stalkIdeal x.1 = (J.ideal V).map (algebraMap Γ(X, V) (X.presheaf.stalk x.1)) :=
  J.stalkIdeal_eq_map_germ x.1 V x.2

/-- The germ map `K(V)/J(V) → K_x/J_x` (`x ∈ V`) as a `Γ(X, V)`-linear map. -/
def quotGermLoc (V : X.affineOpens) (x : V.1) :
    Submodule.map (J.ideal V).mkQ (K.ideal V) →ₗ[Γ(X, V)]
      (J.stalkPiece K x.1).restrictScalars Γ(X, V) :=
  MiyaokaMori.Skyscraper0agt.quotLocMap (J.ideal V) (K.ideal V) (J.stalkIdeal x.1) (K.stalkIdeal x.1)
    (J.stalkIdeal_eq_map_algebraMap V x).ge (K.stalkIdeal_eq_map_algebraMap V x).ge

theorem quotGermLoc_coe_apply (V : X.affineOpens) (x : V.1)
    (g : Submodule.map (J.ideal V).mkQ (K.ideal V)) :
    ((J.quotGermLoc K V x g : (J.stalkPiece K x.1).restrictScalars Γ(X, V)) :
      X.presheaf.stalk x.1 ⧸ J.stalkIdeal x.1) = J.quotGerm V x.2 g.1 := by
  obtain ⟨_, k, hk, rfl⟩ := g
  rfl

/-- `O_{X,x} = Γ(X, V)_q` for the prime `q = 𝔭_y` of a point `y = fromSpec q ∈ V`, in the form
`IsLocalization.AtPrime (O_{X,x}) q` with the algebra structure `algebra_section_stalk` of the
point `⟨fromSpec q, _⟩ : V` (Mathlib's `isLocalization_stalk'` carries a syntactically different
point; `isLocalization_stalk` + `primeIdealOf_fromSpec_affineOpens` avoids that). -/
theorem isLocalization_stalk_fromSpec (V : X.affineOpens) (q : PrimeSpectrum Γ(X, V)) :
    @IsLocalization.AtPrime Γ(X, V) _ (X.presheaf.stalk (V.2.fromSpec q)) _
      (X.presheaf.algebra_section_stalk ⟨V.2.fromSpec q, fromSpec_mem_affineOpens V q⟩)
      q.asIdeal _ := by
  have := V.2.isLocalization_stalk ⟨V.2.fromSpec q, fromSpec_mem_affineOpens V q⟩
  rwa [primeIdealOf_fromSpec_affineOpens V q] at this

theorem mem_stalkPiece_restrictScalars (V : X.affineOpens) (x : V.1)
    {m : X.presheaf.stalk x.1 ⧸ J.stalkIdeal x.1} (hm : m ∈ J.stalkPiece K x.1) :
    m ∈ (J.stalkPiece K x.1).restrictScalars Γ(X, V) := hm

theorem isLocalizedModule_quotGermLoc (V : X.affineOpens) (x : V.1) (q : PrimeSpectrum Γ(X, V))
    (hloc : IsLocalization.AtPrime (X.presheaf.stalk x.1) q.asIdeal) :
    IsLocalizedModule q.asIdeal.primeCompl (J.quotGermLoc K V x) :=
  haveI := hloc
  MiyaokaMori.Skyscraper0agt.isLocalizedModule_quotLocMap _ _ _ _ q.asIdeal.primeCompl
    (J.stalkIdeal_eq_map_algebraMap V x) (K.stalkIdeal_eq_map_algebraMap V x)

theorem notMem_support_of_stalkIdeal_eq (V : X.affineOpens) (x : V.1) (q : PrimeSpectrum Γ(X, V))
    (hloc : IsLocalization.AtPrime (X.presheaf.stalk x.1) q.asIdeal)
    (h : K.stalkIdeal x.1 = J.stalkIdeal x.1) :
    q ∉ Module.support Γ(X, V) (Submodule.map (J.ideal V).mkQ (K.ideal V)) :=
  haveI := hloc
  MiyaokaMori.Skyscraper0agt.notMem_support_quot_of_eq _ _ _ _ q
    (J.stalkIdeal_eq_map_algebraMap V x) (K.stalkIdeal_eq_map_algebraMap V x) h

/-! ### The decomposition on an affine open -/

/-- **Skyscraper decomposition on an affine open.** `G_V = K(V)/J(V) → Π_{q ∈ primesOfPoints V T}
K_{y_q}/J_{y_q}` (`y_q := fromSpec q`) is bijective.

Proof: `B := Γ(X, V)` is Noetherian, `G_V` finitely generated. For `q ∈ primesOfPoints V T`,
`q = 𝔭_x` with `x ∈ T` closed, so `q` is maximal. For a prime `q ∉ primesOfPoints V T`, the point
`y := fromSpec q ∈ V` is not in `T` (else `q = 𝔭_y ∈ primesOfPoints V T`), so `K_y = J_y` and
`q ∉ supp G_V` (`notMem_support_of_stalkIdeal_eq`, using `O_{X,y} = B_q`). Each germ map
`G_V → K_{y_q}/J_{y_q}` is the localization at `q` (`isLocalizedModule_quotGermLoc`), so
`bijective_pi_of_isLocalizedModule` (the finite-support decomposition) applies. -/
theorem quotGermLoc_pi_bijective [AlgebraicGeometry.IsLocallyNoetherian X] (V : X.affineOpens)
    (T : Finset X) (hT : ∀ x ∈ T, IsClosed ({x} : Set X))
    (hsupp : ∀ x : X, x ∉ T → K.stalkIdeal x = J.stalkIdeal x) :
    Function.Bijective (fun (g : Submodule.map (J.ideal V).mkQ (K.ideal V))
      (q : primesOfPoints V T) =>
        J.quotGermLoc K V ⟨V.2.fromSpec q.1, fromSpec_mem_affineOpens V q.1⟩ g) := by
  have : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian V
  refine MiyaokaMori.Skyscraper0agt.bijective_pi_of_isLocalizedModule _ (primesOfPoints V T)
    (primesOfPoints_finite V T) ?_ ?_ _
    (fun q => J.quotGermLoc K V ⟨V.2.fromSpec q.1, fromSpec_mem_affineOpens V q.1⟩) ?_
  · rintro q ⟨x, hxT, rfl⟩
    exact V.2.primeIdealOf_isMaximal_of_isClosed x (hT x.1 hxT)
  · intro q hq
    by_contra hqS
    have hyT : V.2.fromSpec q ∉ T := by
      intro hyT
      exact hqS ⟨⟨V.2.fromSpec q, fromSpec_mem_affineOpens V q⟩, hyT,
        primeIdealOf_fromSpec_affineOpens V q⟩
    exact J.notMem_support_of_stalkIdeal_eq K V ⟨V.2.fromSpec q, fromSpec_mem_affineOpens V q⟩ q
      (isLocalization_stalk_fromSpec V q) (hsupp _ hyT) hq
  · intro q
    exact J.isLocalizedModule_quotGermLoc K V _ q.1 (isLocalization_stalk_fromSpec V q.1)

/-- Two elements of `K(V)/J(V)` with the same germ at every `x ∈ T ∩ V` are equal. -/
theorem quotGerm_injective_of_stalkIdeal_eq [AlgebraicGeometry.IsLocallyNoetherian X]
    (V : X.affineOpens) (T : Finset X) (hT : ∀ x ∈ T, IsClosed ({x} : Set X))
    (hsupp : ∀ x : X, x ∉ T → K.stalkIdeal x = J.stalkIdeal x)
    (g₁ g₂ : Submodule.map (J.ideal V).mkQ (K.ideal V))
    (h : ∀ x : V.1, x.1 ∈ T → J.quotGerm V x.2 g₁.1 = J.quotGerm V x.2 g₂.1) : g₁ = g₂ := by
  apply (J.quotGermLoc_pi_bijective K V T hT hsupp).1
  funext q
  apply Subtype.ext
  rw [quotGermLoc_coe_apply, quotGermLoc_coe_apply]
  exact h ⟨V.2.fromSpec q.1, fromSpec_mem_affineOpens V q.1⟩
    (fromSpec_mem_of_mem_primesOfPoints V T q.2)

/-- Every family of germs `(n_x)_{x ∈ T}` with `n_x ∈ K_x/J_x` is realized on `V` by an element of
`K(V)/J(V)`. -/
theorem exists_quotGerm_eq_of_stalkIdeal_eq [AlgebraicGeometry.IsLocallyNoetherian X]
    (V : X.affineOpens) (T : Finset X) (hT : ∀ x ∈ T, IsClosed ({x} : Set X))
    (hsupp : ∀ x : X, x ∉ T → K.stalkIdeal x = J.stalkIdeal x)
    (n : ∀ x : T, X.presheaf.stalk x.1 ⧸ J.stalkIdeal x.1) (hn : ∀ x, n x ∈ J.stalkPiece K x.1) :
    ∃ g : Submodule.map (J.ideal V).mkQ (K.ideal V),
      ∀ (x : V.1) (hxT : x.1 ∈ T), J.quotGerm V x.2 g.1 = n ⟨x.1, hxT⟩ := by
  obtain ⟨g, hg⟩ := (J.quotGermLoc_pi_bijective K V T hT hsupp).2
    (fun q => ⟨n ⟨V.2.fromSpec q.1, fromSpec_mem_of_mem_primesOfPoints V T q.2⟩,
      J.mem_stalkPiece_restrictScalars K V ⟨V.2.fromSpec q.1, fromSpec_mem_affineOpens V q.1⟩
        (hn ⟨V.2.fromSpec q.1, fromSpec_mem_of_mem_primesOfPoints V T q.2⟩)⟩)
  refine ⟨g, fun x hxT => ?_⟩
  have hq : V.2.primeIdealOf x ∈ primesOfPoints V T := ⟨x, hxT, rfl⟩
  have h1 := congrArg Subtype.val (congrFun hg ⟨V.2.primeIdealOf x, hq⟩)
  rw [quotGermLoc_coe_apply] at h1
  -- `h1 : quotGerm V _ g.1 = n ⟨fromSpec 𝔭_x, _⟩`; transport along `fromSpec 𝔭_x = x`
  have key : ∀ (y : X) (hy : y ∈ V.1) (hyT : y ∈ T), y = x.1 →
      J.quotGerm V hy g.1 = n ⟨y, hyT⟩ → J.quotGerm V x.2 g.1 = n ⟨x.1, hxT⟩ := by
    rintro y hy hyT rfl h
    exact h
  exact key _ _ _ (V.2.fromSpec_primeIdealOf x) h1

end AlgebraicGeometry.Scheme.IdealSheafData

end
