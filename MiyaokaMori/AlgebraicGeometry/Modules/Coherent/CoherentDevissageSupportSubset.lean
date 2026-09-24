import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModuleSheafStalk
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModulesSupport
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModulesStalkFunctor
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.CoherentSheaf
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModulesSupportBasics
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.ModuleSupportGenericPoints
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.CoherentStalkLengthAtMaximalPoint
import MiyaokaMori.RingTheory.Length.SimpleModuleIntoFiniteLength
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.CoherentDevissageSheafLemmas
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.CoherentHomOfStalkLinearMap

/-! # Dévissage of coherent sheaves with support in a given set

**Dévissage of coherent sheaves supported in a subset** (Stacks 01YI, proof, run inside `Supp F`).

`X` Noetherian, `T ⊆ X` any set, `P` a property of `X.Modules`. Assume
1. `hzero`: `P` holds for coherent zero objects;
2. `h23` (two out of three, *only for sequences supported in `T`*): for a short exact sequence
   `0 → F₁ → F₂ → F₃ → 0` of coherent sheaves with `Supp Fᵢ ⊆ T`, if two of the three have `P`, so does
   the third;
3. `hgen` (generators, *only at points of `T`*): for every `ξ ∈ T` there is a coherent `G` with
   `Supp G = closure {ξ}`, `m_ξ · G_ξ = 0`, `length_{O_{X,ξ}} G_ξ = 1` and `P G`.

Then `P F` for every coherent `F` with `Supp F ⊆ T`.

With `T = X` this is exactly Stacks 01YI (`coherent_devissage`, with the harmless
extra hypothesis `F.IsCoherent` in `hzero`); the Stacks proof of 01YI never leaves `Supp F`, which is why
the restricted form holds by the same argument. The restricted form is what Stacks 0BEN
needs: the 0BEN invariant `E_d(F) = χ(F ⊗ L^n) − Σ m_ξ χ(Z_ξ, L^n)` is only
meaningful for `dim Supp F ≤ d`, and two-out-of-three fails for it on all of `X` (a sheaf of support
dimension `d` is a quotient of `O_X`), so the dévissage has to be run inside `T = Supp F`.

## Proof: Noetherian induction on `Supp F`, then induction on `length F_ξ`

This is the Stacks 01YI argument with one simplification: instead of filtering `F` by `𝓘^j F` for the
ideal sheaf `𝓘` of `closure {ξ}` (which needs the products `𝓘 F`, Stacks 01YB, absent from the library)
and comparing a sheaf killed by `𝓘` with `G^{⊕ r}`, we induct on the (finite) length of the stalk `F_ξ`
and compare `F` with a single copy of `G` through a *simple submodule* of `F_ξ`. Every sheaf appearing is
supported in `Supp F ⊆ T`, so `h23` applies.

**Proof.** By Noetherian induction on the closed set
`Z := Supp F` (closed: Stacks 01B4, `isClosed_support_of_isCoherent`; `X` is a Noetherian space, so
`Closeds X` is well-founded, Mathlib `WellFoundedLT (Closeds X)`): assume `P F'` for every coherent `F'`
with `Supp F' ⊆ Z' ⊊ Z`, `Supp F' ⊆ T`, and prove `P F` for coherent `F` with `Supp F ⊆ Z`, `Supp F ⊆ T`.
* If `Supp F ⊊ Z`, this is the induction hypothesis. So assume `Supp F = Z`.
* If `Z = ∅`, all stalks vanish, `F` is a zero object (`isZero_of_support_eq_empty`) and `hzero` applies.
* Otherwise choose `ξ ∈ Z` minimal for specialization in `Z` (a generic point of an irreducible component;
  `exists_mem_genericPoints_specializes`, Stacks 004W/0052). Then `F_ξ` has finite length `n`
  (`length_stalk_ne_top_of_forall_specializes`, `CoherentStalkLengthAtMaximalPoint`).
  **Claim (inner induction on `n`):** for every coherent `H` with `Supp H ⊆ Z`, `Supp H ⊆ T` and
  `length H_ξ ≤ n`, `P H`.
  - `n = 0`: `H_ξ = 0`, so `ξ ∉ Supp H`, so `Supp H ⊊ Z` (a closed subset of `Z` missing `ξ ∈ Z`): outer
    induction hypothesis (`outer` below).
  - `n + 1`: if `ξ ∉ Supp H`, as before. Otherwise `H_ξ ≠ 0` has finite length, and `hgen ξ` gives `G`
    (`ξ ∈ Supp H ⊆ T`) with `G_ξ` of length `1` and `P G`. By
    `exists_injective_linearMap_of_length_eq_one` (`SimpleModuleIntoFiniteLength`) there is an injective
    `O_{X,ξ}`-linear
    `f : G_ξ → H_ξ` (a simple module embeds into the socle of a nonzero Artinian module). By
    `exists_coherent_hom_of_stalk_linearMap` (Stacks 01BN + 01Y8, `CoherentHomOfStalkLinearMap`) there
    are a coherent `G'` with
    `Supp G' ⊆ Supp G ∪ Supp H`, `ι : G' → G` bijective on stalks at `ξ`, and `ψ : G' → H` with
    `ψ_ξ = f ∘ ι_ξ` (injective). All sheaves below are supported in `Supp H` (note
    `Supp G = closure {ξ} ⊆ Supp H` as `Supp H` is closed) hence in `Z ∩ T`.
    1. `ker ι`, `coker ι`, `ker ψ` have zero stalk at `ξ` (`ι_ξ` bijective, `ψ_ξ` injective; the stalk
       functor is exact), so `P` holds for them by the outer induction hypothesis.
    2. `P G` and `P (coker ι)` give `P (im ι)` (sequence `0 → im ι → G → coker ι → 0`); `im ι ≅ coim ι`;
       `P (ker ι)` and `P (coim ι)` give `P G'` (sequence `0 → ker ι → G' → coim ι → 0`).
    3. `P (ker ψ)` and `P G'` give `P (coim ψ)` (sequence `0 → ker ψ → G' → coim ψ → 0`), hence
       `P (im ψ)`.
    4. Lengths at `ξ`: `length G'_ξ = length G_ξ = 1`, `length (ker ψ)_ξ = 0`, so `length (coim ψ)_ξ =
       length (im ψ)_ξ = 1`; from `0 → im ψ → H → coker ψ → 0`, `length H_ξ = 1 + length (coker ψ)_ξ`,
       so `length (coker ψ)_ξ ≤ n`: `P (coker ψ)` by the inner induction hypothesis.
    5. `P (im ψ)` and `P (coker ψ)` give `P H`.
  Applying the claim to `H = F` proves `P F`.
  (`P` is invariant under isomorphism of coherent sheaves supported in `T`: for `e : A ≅ B`, the sequence
  `0 → A → B → coker e → 0` is short exact with `coker e = 0`, `hzero` and `h23`.)

**Edge cases.** `X = ∅`: every sheaf is zero, `hzero`. `T = ∅`: then `Supp F = ∅`, `F ≅ 0`, `hzero`
(this is why `hzero` is a separate hypothesis: with `T = ∅` there are no generators). `T` not closed:
harmless, only `Supp F ⊆ T` is used. `F` with `Supp F ⊊ T`: fine, the induction is on `Supp F`. The
hypothesis `m_ξ ≤ Ann G_ξ` of `hgen` is not used: it follows from `length G_ξ = 1` (a simple module over
a local ring is killed by the maximal ideal).

The ingredients are `CoherentStalkLengthAtMaximalPoint` (finite length of the stalk at `ξ`),
`CoherentHomOfStalkLinearMap` (Stacks 01BN + 01Y8), the sheaf-level lemmas of
`CoherentDevissageSheafLemmas` and the algebraic lemma on simple submodules.

Source: Stacks 01YI (coherent-lemma-property), proof.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open MiyaokaMori.CoherentDevissage in
/-- Stacks 01YI restricted to coherent sheaves supported in `T` (see the module docstring for the
proof). With `T = Set.univ` it is `coherent_devissage` (`Stacks01yi`). -/
theorem AlgebraicGeometry.Scheme.Modules.coherent_devissage_of_support_subset
    {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsNoetherian X] (T : Set X)
    (P : X.Modules → Prop)
    (hzero : ∀ F : X.Modules, F.IsCoherent → CategoryTheory.Limits.IsZero F → P F)
    (h23 : ∀ S : CategoryTheory.ShortComplex X.Modules, S.ShortExact →
      S.X₁.IsCoherent → S.X₂.IsCoherent → S.X₃.IsCoherent →
      S.X₁.support ⊆ T → S.X₂.support ⊆ T → S.X₃.support ⊆ T →
      (P S.X₁ → P S.X₂ → P S.X₃) ∧ (P S.X₁ → P S.X₃ → P S.X₂) ∧ (P S.X₂ → P S.X₃ → P S.X₁))
    (hgen : ∀ ξ ∈ T, ∃ G : X.Modules, G.IsCoherent ∧ G.support = closure {ξ} ∧
      IsLocalRing.maximalIdeal (X.presheaf.stalk ξ) ≤
        Module.annihilator (X.presheaf.stalk ξ) (G.stalk ξ) ∧
      Module.length (X.presheaf.stalk ξ) (G.stalk ξ) = 1 ∧ P G)
    (F : X.Modules) [F.IsCoherent] (hF : F.support ⊆ T) : P F := by
  classical
  have hcl : ∀ (H : X.Modules) [H.IsCoherent], IsClosed H.support :=
    fun H _ => isClosed_support_of_isCoherent H
  -- packaged two-out-of-three
  have h23' : ∀ (S : ShortComplex X.Modules), S.ShortExact →
      (S.X₁.IsCoherent ∧ S.X₂.IsCoherent ∧ S.X₃.IsCoherent) →
      (S.X₁.support ⊆ T ∧ S.X₂.support ⊆ T ∧ S.X₃.support ⊆ T) →
      (P S.X₁ → P S.X₂ → P S.X₃) ∧ (P S.X₁ → P S.X₃ → P S.X₂) ∧ (P S.X₂ → P S.X₃ → P S.X₁) :=
    fun S hS hc hs => h23 S hS hc.1 hc.2.1 hc.2.2 hs.1 hs.2.1 hs.2.2
  have hsuppT : ∀ {A B C : X.Modules} {W : Set X}, (A.support ⊆ W ∧ B.support ⊆ W ∧ C.support ⊆ W) →
      W ⊆ T → (A.support ⊆ T ∧ B.support ⊆ T ∧ C.support ⊆ T) :=
    fun h hW => ⟨h.1.trans hW, h.2.1.trans hW, h.2.2.trans hW⟩
  -- `P` is invariant under isomorphisms of coherent sheaves supported in `T`
  have hiso : ∀ {A B : X.Modules} (e : A ≅ B), A.IsCoherent → A.support ⊆ T → P A → P B := by
    intro A B e hA hAT hPA
    have := hA
    have hB : B.IsCoherent := isCoherent_of_iso e
    have hC : (cokernel e.hom).IsCoherent := isCoherent_cokernel e.hom
    have hCz : IsZero (cokernel e.hom) := isZero_cokernel_of_epi e.hom
    have hCsupp : (cokernel e.hom).support ⊆ T := by
      rw [support_eq_empty_of_isZero hCz]; exact Set.empty_subset _
    have hBsupp : B.support ⊆ T := (support_eq_of_iso e).symm ▸ hAT
    exact (h23' (ShortComplex.cokernelSequence e.hom) (cokernelSequence_shortExact e.hom)
      ⟨hA, hB, hC⟩ ⟨hAT, hBsupp, hCsupp⟩).2.1 hPA (hzero _ hC hCz)
  -- Noetherian induction on the closed support
  suffices key : ∀ Z : Closeds X, ∀ (H : X.Modules), H.IsCoherent → H.support ⊆ (Z : Set X) →
      H.support ⊆ T → P H from key ⟨F.support, hcl F⟩ F inferInstance le_rfl hF
  intro Z
  refine WellFounded.induction (C := fun Z : Closeds X => ∀ (H : X.Modules), H.IsCoherent →
    H.support ⊆ (Z : Set X) → H.support ⊆ T → P H) (wellFounded_lt (α := Closeds X)) Z ?_
  clear Z
  intro Z IH F' hF'coh hF'Z hF'T
  have := hF'coh
  -- sheaves whose support misses a point of `Z` have support strictly inside `Z`
  have outer : ∀ (H : X.Modules), H.IsCoherent → H.support ⊆ (Z : Set X) → H.support ⊆ T →
      (∃ ξ ∈ (Z : Set X), ξ ∉ H.support) → P H := by
    intro H hH hHZ hHT hξ
    obtain ⟨ξ, hξZ, hξH⟩ := hξ
    have := hH
    have hle : (⟨H.support, hcl H⟩ : Closeds X) ≤ Z := hHZ
    have hne : (⟨H.support, hcl H⟩ : Closeds X) ≠ Z := by
      intro heq
      apply hξH
      have : H.support = (Z : Set X) := congrArg SetLike.coe heq
      rw [this]; exact hξZ
    exact IH _ (lt_of_le_of_ne hle hne) H hH le_rfl hHT
  by_cases hZF : F'.support = (Z : Set X)
  swap
  · obtain ⟨ξ, hξZ, hξF⟩ : ∃ ξ ∈ (Z : Set X), ξ ∉ F'.support := by
      by_contra hcon
      push Not at hcon
      exact hZF (Set.Subset.antisymm hF'Z hcon)
    exact outer F' hF'coh hF'Z hF'T ⟨ξ, hξZ, hξF⟩
  rcases (Z : Set X).eq_empty_or_nonempty with hemp | ⟨x, hx⟩
  · exact hzero F' hF'coh (isZero_of_support_eq_empty F' (hZF.trans hemp))
  -- a generic point `ξ` of `Z = Supp F'`
  have hxF : x ∈ F'.support := by rw [hZF]; exact hx
  obtain ⟨ξ, hξgen, -⟩ := exists_mem_genericPoints_specializes F' hxF
  have hξZ : ξ ∈ (Z : Set X) := by rw [← hZF]; exact hξgen.1
  have hξmin : ∀ η ∈ (Z : Set X), η ⤳ ξ → η = ξ := by
    intro η hη hs
    rw [← hZF] at hη
    exact hξgen.2 η hη hs
  -- inner induction on the length of the stalk at `ξ`
  have inner : ∀ n : ℕ, ∀ (H : X.Modules), H.IsCoherent → H.support ⊆ (Z : Set X) → H.support ⊆ T →
      Module.length (X.presheaf.stalk ξ) (H.stalk ξ) ≤ n → P H := by
    intro n
    induction n with
    | zero =>
      intro H hH hHZ hHT hlen
      have hlen0 : Module.length (X.presheaf.stalk ξ) (H.stalk ξ) = 0 :=
        le_antisymm (by exact_mod_cast hlen) bot_le
      have hsub : Subsingleton (H.stalk ξ) := Module.length_eq_zero_iff.mp hlen0
      exact outer H hH hHZ hHT ⟨ξ, hξZ, not_nontrivial_iff_subsingleton.mpr hsub⟩
    | succ n ihn =>
      intro H hH hHZ hHT hlen
      have := hH
      by_cases hξH : ξ ∈ H.support
      swap
      · exact outer H hH hHZ hHT ⟨ξ, hξZ, hξH⟩
      -- the generator at `ξ` and the injective map `G_ξ → H_ξ`
      obtain ⟨G, hGcoh, hGsupp, -, hGlen, hPG⟩ := hgen ξ (hHT hξH)
      have := hGcoh
      have hHnt : Nontrivial (H.stalk ξ) := hξH
      have hHfin : Module.length (X.presheaf.stalk ξ) (H.stalk ξ) ≠ ⊤ :=
        ne_top_of_le_ne_top (ENat.natCast_ne_top _) hlen
      obtain ⟨f, hfinj⟩ := exists_injective_linearMap_of_length_eq_one hGlen hHfin
      obtain ⟨G', ι, ψ, hG'coh, hG'supp, hιbij, hψι⟩ :=
        AlgebraicGeometry.Scheme.Modules.exists_coherent_hom_of_stalk_linearMap G H ξ f
      have := hG'coh
      -- supports: everything lives inside `Supp H ⊆ Z ∩ T`
      have hclosure : closure {ξ} ⊆ H.support :=
        (hcl H).closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hξH)
      have hGH : G.support ⊆ H.support := by rw [hGsupp]; exact hclosure
      have hG'H : G'.support ⊆ H.support := hG'supp.trans (Set.union_subset hGH le_rfl)
      have hHZT : H.support ⊆ (Z : Set X) ∩ T := Set.subset_inter hHZ hHT
      -- stalk maps at `ξ`
      have hψinj : Function.Injective ((AlgebraicGeometry.Scheme.Modules.stalkFunctor ξ).map ψ).hom := by
        intro a b hab
        apply hιbij.1
        apply hfinj
        exact (hψι a).symm.trans (hab.trans (hψι b))
      -- Step 1: `P` for the sheaves with zero stalk at `ξ`
      have hPcokι : P (cokernel ι) :=
        outer _ (isCoherent_cokernel ι) ((support_subset_of_epi (cokernel.π ι)).trans (hGH.trans hHZ))
          ((support_subset_of_epi (cokernel.π ι)).trans (hGH.trans hHT))
          ⟨ξ, hξZ, notMem_support_cokernel_of_surjective ι ξ hιbij.2⟩
      have hPkerι : P (kernel ι) :=
        outer _ (isCoherent_kernel ι) ((support_subset_of_mono (kernel.ι ι)).trans (hG'H.trans hHZ))
          ((support_subset_of_mono (kernel.ι ι)).trans (hG'H.trans hHT))
          ⟨ξ, hξZ, notMem_support_kernel_of_injective ι ξ hιbij.1⟩
      have hPkerψ : P (kernel ψ) :=
        outer _ (isCoherent_kernel ψ) ((support_subset_of_mono (kernel.ι ψ)).trans (hG'H.trans hHZ))
          ((support_subset_of_mono (kernel.ι ψ)).trans (hG'H.trans hHT))
          ⟨ξ, hξZ, notMem_support_kernel_of_injective ψ ξ hψinj⟩
      -- Step 2: `P G'`
      have hPimι : P (Abelian.image ι) :=
        (h23' _ (imageSequence_shortExact ι) (imageSequence_isCoherent ι)
          (hsuppT (imageSequence_support ι) (hGH.trans hHT))).2.2 hPG hPcokι
      have hPcoimι : P (Abelian.coimage ι) :=
        hiso (Abelian.coimageIsoImage ι).symm (isCoherent_image ι)
          ((support_subset_of_mono (kernel.ι (cokernel.π ι))).trans (hGH.trans hHT)) hPimι
      have hPG' : P G' :=
        (h23' _ (coimageSequence_shortExact ι) (coimageSequence_isCoherent ι)
          (hsuppT (coimageSequence_support ι) (hG'H.trans hHT))).2.1 hPkerι hPcoimι
      -- Step 3: `P (im ψ)`
      have hPcoimψ : P (Abelian.coimage ψ) :=
        (h23' _ (coimageSequence_shortExact ψ) (coimageSequence_isCoherent ψ)
          (hsuppT (coimageSequence_support ψ) (hG'H.trans hHT))).1 hPkerψ hPG'
      have hPimψ : P (Abelian.image ψ) :=
        hiso (Abelian.coimageIsoImage ψ) (isCoherent_coimage ψ)
          ((support_subset_of_epi (cokernel.π (kernel.ι ψ))).trans (hG'H.trans hHT)) hPcoimψ
      -- Step 4: lengths at `ξ`
      have hlenG' : Module.length (X.presheaf.stalk ξ) (G'.stalk ξ) = 1 :=
        (length_stalk_eq_of_bijective ι ξ hιbij).trans hGlen
      have hlenkerψ : Module.length (X.presheaf.stalk ξ) ((kernel ψ).stalk ξ) = 0 :=
        Module.length_eq_zero_iff.mpr (subsingleton_stalk_kernel_of_injective ψ ξ hψinj)
      have h1 := length_stalk_add_of_shortExact _ (coimageSequence_shortExact ψ) ξ
      have hlencoim : Module.length (X.presheaf.stalk ξ) ((Abelian.coimage ψ).stalk ξ) = 1 := by
        have h1' : Module.length (X.presheaf.stalk ξ) (G'.stalk ξ) =
            Module.length (X.presheaf.stalk ξ) ((kernel ψ).stalk ξ) +
              Module.length (X.presheaf.stalk ξ) ((Abelian.coimage ψ).stalk ξ) := h1
        rw [hlenG', hlenkerψ, zero_add] at h1'
        exact h1'.symm
      have hlenim : Module.length (X.presheaf.stalk ξ) ((Abelian.image ψ).stalk ξ) = 1 :=
        (length_stalk_eq_of_iso (Abelian.coimageIsoImage ψ) ξ).symm.trans hlencoim
      have h2 := length_stalk_add_of_shortExact _ (imageSequence_shortExact ψ) ξ
      have hlencok : Module.length (X.presheaf.stalk ξ) ((cokernel ψ).stalk ξ) ≤ n := by
        have h2' : Module.length (X.presheaf.stalk ξ) (H.stalk ξ) =
            Module.length (X.presheaf.stalk ξ) ((Abelian.image ψ).stalk ξ) +
              Module.length (X.presheaf.stalk ξ) ((cokernel ψ).stalk ξ) := h2
        rw [h2', hlenim] at hlen
        have hcast : ((n + 1 : ℕ) : ℕ∞) = 1 + (n : ℕ∞) := by
          push_cast
          ring
        rw [hcast] at hlen
        exact (ENat.add_le_add_iff_left ENat.one_ne_top).mp hlen
      have hPcokψ : P (cokernel ψ) :=
        ihn _ (isCoherent_cokernel ψ) ((support_subset_of_epi (cokernel.π ψ)).trans hHZ)
          ((support_subset_of_epi (cokernel.π ψ)).trans hHT) hlencok
      -- Step 5: `P H`
      exact (h23' _ (imageSequence_shortExact ψ) (imageSequence_isCoherent ψ)
        (hsuppT (imageSequence_support ψ) hHT)).2.1 hPimψ hPcokψ
  -- finite length of `F'_ξ`
  have hfin : Module.length (X.presheaf.stalk ξ) (F'.stalk ξ) ≠ ⊤ :=
    AlgebraicGeometry.Scheme.Modules.length_stalk_ne_top_of_forall_specializes F' ξ
      (fun η hs hη => hξgen.2 η hη hs)
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfin
  exact inner n F' hF'coh hF'Z hF'T hn.symm.le

end
