import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.BasicOpenRestrictionKernel

/-! # Sections supported on a closed subset (Stacks 07ZP)

Stacks 07ZP: the sections supported on a closed subset `Z` (with retrocompact complement) form a
quasi-coherent ideal sheaf `H_Z(O_X)`, given on `U` by `ker(O(U) → O(U∖Z))`; on an affine `U` it
equals `{x | ∃ n, J^n x = 0}` where `J` is finitely generated with `V(J) = Z ∩ U`.

References: Stacks 07ZP; Stacks 080D (definition of the strict transform ideal).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

noncomputable def AlgebraicGeometry.Scheme.IdealSheafData.supportedOn {X : AlgebraicGeometry.Scheme.{u}}
    (Z : TopologicalSpace.Closeds X)
    [AlgebraicGeometry.QuasiCompact
      (AlgebraicGeometry.Scheme.Opens.ι (⟨(Z : Set X)ᶜ, Z.isClosed.isOpen_compl⟩ : X.Opens))] :
    X.IdealSheafData :=
  /- `H_Z(O_X) = ker(O_X → j_*O_{X∖Z})` with `j` the open immersion of `Zᶜ`: Mathlib's
     `Scheme.Hom.ker` (the `QuasiCompact` hypothesis makes it, on an affine `U`, exactly the kernel
     of the restriction `O(U) → O(U ∖ Z)`, `Scheme.Hom.ker_apply`). -/
  (AlgebraicGeometry.Scheme.Opens.ι (⟨(Z : Set X)ᶜ, Z.isClosed.isOpen_compl⟩ : X.Opens)).ker

/-- **Stacks 07ZP(2)** (the case `F = O_X`): on an affine open `U`, the sections supported in `Z`
are exactly the elements killed by some power of `(g₁,…,g_m)`.

Reference: Stacks 07ZP, `lemma-sections-supported-on-closed-subset` part (2):
`F'(U) = {x ∈ M | I^n x = 0 for some n}` with `I` finitely generated and `Z ∩ U = V(I)`; here
`I = (g₁,…,g_m)`. (Part (1), that `Z ∩ U` is the zero locus of a finitely generated ideal on an
affine open, is the hypothesis `hZ`; part (3), quasi-coherence, is built into `Scheme.Hom.ker`.)

Proof sketch: let `j : Zᶜ ↪ X` be the open immersion (the `QuasiCompact` instance says it is
quasi-compact).
1. `supportedOn Z = j.ker`, and `Scheme.Hom.ker_apply` gives `j.ker.ideal U = ker (j.app U)`, where
   `j.app U : Γ(X, U) → Γ(X, U ⊓ Zᶜ)` is the restriction map (`Scheme.Opens.ι_app`).
2. By `hZ`, `U ∖ Z = ⋃ᵢ D(gᵢ)` (each `X.basicOpen (g i) ≤ U` since `gᵢ ∈ Γ(X,U)`).
3. `⊆`: if `x|_{U∖Z} = 0` then `x|_{D(gᵢ)} = 0` for all `i`; since `Γ(X, D(gᵢ))` is the localization
   of `Γ(X,U)` at `gᵢ` (`IsAffineOpen.isLocalization_basicOpen`), this gives `nᵢ` with
   `gᵢ^{nᵢ} x = 0`; take `n = max nᵢ`.
4. `⊇`: if `gᵢ^n x = 0` for all `i`, then `x` vanishes on each `D(gᵢ)`, which cover `U ∖ Z`; by the
   separatedness of the sheaf `O_X` (`TopCat.Sheaf.eq_of_locally_eq'`), `x|_{U∖Z} = 0`.
5. The boundary case `m = 0`: `hZ` says `U ⊆ Z`, so `U ∖ Z = ∅` and both sides are `⊤`.
The localization step in 3–4 is `mem_ker_restriction_iff_pow_mul_eq_zero` (the principal case). -/
theorem AlgebraicGeometry.Scheme.IdealSheafData.supportedOn_ideal {X : AlgebraicGeometry.Scheme.{u}}
    (Z : TopologicalSpace.Closeds X)
    [AlgebraicGeometry.QuasiCompact
      (AlgebraicGeometry.Scheme.Opens.ι (⟨(Z : Set X)ᶜ, Z.isClosed.isOpen_compl⟩ : X.Opens))]
    (U : X.affineOpens) {m : ℕ} (g : Fin m → Γ(X, (U : X.Opens)))
    (hZ : (Z : Set X) ∩ (U : Set X) = (U : Set X) \ ⋃ i, (X.basicOpen (g i) : Set X)) :
    (AlgebraicGeometry.Scheme.IdealSheafData.supportedOn Z).ideal U = {x | ∃ n : ℕ, ∀ i, g i ^ n * x = 0} := by
  classical
  -- Step 1: `Hom.ker_apply` turns the left side into the kernel of the restriction map to `W`.
  set V : X.Opens := ⟨(Z : Set X)ᶜ, Z.isClosed.isOpen_compl⟩ with hV
  unfold AlgebraicGeometry.Scheme.IdealSheafData.supportedOn
  rw [AlgebraicGeometry.Scheme.Hom.ker_apply, AlgebraicGeometry.Scheme.Opens.ι_app]
  set W : X.Opens := V.ι ''ᵁ V.ι ⁻¹ᵁ (U : X.Opens) with hW
  have hWU : W ≤ (U : X.Opens) := Set.image_preimage_subset _ _
  -- Step 2: `W = U ∖ Z = ⋃ᵢ D(gᵢ)`.
  have hWsup : W = ⨆ i, X.basicOpen (g i) := by
    apply TopologicalSpace.Opens.ext
    rw [hW, AlgebraicGeometry.Scheme.Hom.image_preimage_eq_opensRange_inf,
      AlgebraicGeometry.Scheme.Opens.opensRange_ι, TopologicalSpace.Opens.coe_iSup,
      TopologicalSpace.Opens.coe_inf]
    have hZ' := Set.ext_iff.mp hZ
    ext x
    simp only [Set.mem_inter_iff, Set.mem_sdiff, Set.mem_iUnion, hV, TopologicalSpace.Opens.coe_mk,
      Set.mem_compl_iff] at hZ' ⊢
    constructor
    · rintro ⟨hxZ, hxU⟩
      by_contra hx
      exact hxZ ((hZ' x).mpr ⟨hxU, hx⟩).1
    · rintro ⟨i, hi⟩
      have hxU : x ∈ (U : Set X) := X.basicOpen_le (g i) hi
      refine ⟨fun hxZ => ?_, hxU⟩
      exact ((hZ' x).mp ⟨hxZ, hxU⟩).2 ⟨i, hi⟩
  have hDW : ∀ i, X.basicOpen (g i) ≤ W := fun i => hWsup ▸ le_iSup (fun i => X.basicOpen (g i)) i
  -- Steps 3–4: on the affine `U`, `x|_{D(gᵢ)} = 0 ⟺ ∃ n, gᵢ^n x = 0` (the principal case).
  have hloc : ∀ (i : Fin m) (x : Γ(X, (U : X.Opens))),
      (X.presheaf.map (homOfLE (X.basicOpen_le (g i))).op).hom x = 0 ↔ ∃ n : ℕ, g i ^ n * x = 0 :=
    fun i x => AlgebraicGeometry.Scheme.Modules.BasicOpenRestrictionKernel.mem_ker_restriction_iff_pow_mul_eq_zero
      X U (g i) (X.basicOpen (g i)) (X.basicOpen_le (g i)) rfl x
  -- restriction to `D(gᵢ)` factors through `W`
  have hres : ∀ (i : Fin m) (x : Γ(X, (U : X.Opens))),
      (X.presheaf.map (homOfLE (X.basicOpen_le (g i))).op).hom x =
        (X.presheaf.map (homOfLE (hDW i)).op).hom ((X.presheaf.map (homOfLE hWU).op).hom x) := by
    intro i x
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl
  ext x
  simp only [SetLike.mem_coe, RingHom.mem_ker, Set.mem_ofPred_eq]
  change (X.presheaf.map (homOfLE hWU).op).hom x = 0 ↔ _
  constructor
  · intro hx
    have hi : ∀ i, ∃ n : ℕ, g i ^ n * x = 0 := fun i =>
      (hloc i x).mp (by rw [hres i x, hx, map_zero])
    choose n hn using hi
    refine ⟨Finset.univ.sup n, fun i => ?_⟩
    have := congr_arg (fun y => g i ^ (Finset.univ.sup n - n i) * y) (hn i)
    simp only [mul_zero, ← mul_assoc, ← pow_add] at this
    rwa [tsub_add_cancel_of_le (Finset.le_sup (Finset.mem_univ i))] at this
  · rintro ⟨n, hn⟩
    apply TopCat.Sheaf.eq_of_locally_eq' X.sheaf (fun i => X.basicOpen (g i)) W
      (fun i => homOfLE (hDW i)) hWsup.le
    intro i
    change (X.presheaf.map (homOfLE (hDW i)).op).hom ((X.presheaf.map (homOfLE hWU).op).hom x) =
      (X.presheaf.map (homOfLE (hDW i)).op).hom 0
    rw [map_zero, ← hres i x]
    exact (hloc i x).mpr ⟨n, hn i⟩

end
