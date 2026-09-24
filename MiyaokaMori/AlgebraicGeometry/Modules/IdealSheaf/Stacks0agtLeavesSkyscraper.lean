import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.Stacks0agtLeavesQuotFamilies
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.Stacks0agtLeavesSkyscraperAffine

/-! # Sections of `K/J` with finite support surject onto the stalks

`X` locally Noetherian, `J ≤ K` ideal sheaves with `K_x = J_x` outside a finite set `T` of closed
points. Then the germ map from the compatible families of sections of `K/J`
(`IdealSheafData.subFamilies J K`) to `Π_{x ∈ T} K_x/J_x` is surjective (in fact bijective, but
only surjectivity is needed).

This is "a coherent sheaf supported on finitely many closed points is the direct sum of its stalks
(skyscrapers)", Stacks 0AGT step 2 (`Γ(X, O_X(−dE)/I·O_X) = ⊕ᵢ O_{X,xᵢ}/I'_{xᵢ}`), stated for the
sheaf-free model `quotFamilies`. Used in the length inequality of Stacks 0AGT.

The affine-local content is in `Stacks0agtLeavesSkyscraperAffine` (bijectivity of
`K(V)/J(V) → Π_{x ∈ T ∩ V} K_x/J_x` for every affine `V`, from the finite-support decomposition
`Module.bijective_pi_localizedModule_of_support_subset` via `Stacks0agtLeavesSkyscraperLocalizedQuot`);
this file only glues the local preimages into a compatible family.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
open scoped AlgebraicGeometry.Scheme.IdealSheafData.QuotFamilies0agt

noncomputable section

namespace AlgebraicGeometry.Scheme.IdealSheafData

-- `hJK` is part of the locked statement (used by `Stacks0agtLeavesLengthCore`) but not needed.
set_option linter.unusedVariables false in
/-- **Skyscraper decomposition (surjectivity onto the stalks).** `X` locally Noetherian, `J ≤ K`
ideal sheaves, `T` a finite set of closed points with `K_x = J_x` for `x ∉ T`. Then
`subFamiliesGerm J K T : subFamilies J K → Π_{x ∈ T} K_x/J_x` is surjective.

Source: Hartshorne III Ex. 2.3 / Stacks 01AW-type argument ("a sheaf with finite closed support is
the sum of its stalks"); here in the algebraic form of
`Module.bijective_pi_localizedModule_of_support_subset`.

Proof sketch:
1. **Local model.** Fix an affine open `U`, `B := Γ(X, U)` (Noetherian:
   `IsLocallyNoetherian.component_noetherian`), and `G_U := K(U)/J(U)` viewed as the
   `B`-submodule `Submodule.map (J U).mkQ (K U)` of `B/J(U)` (finitely generated: image of the
   finitely generated ideal `K(U)`). For `x ∈ U` with prime `𝔭_x := primeIdealOf x`, the stalk
   `O_{X,x}` is the localization `B_{𝔭_x}` (`IsAffineOpen.isLocalization_stalk`) and
   `K_x = K(U)·O_{X,x}`, `J_x = J(U)·O_{X,x}` (`stalkIdeal_eq_map_germ`); hence the germ map
   `quotGerm : G_U → K_x/J_x = stalkPiece J K x` is the localization of `G_U` at `𝔭_x`
   (`isLocalizedModule_quotGermLoc`: localization commutes with quotients of ideals —
   `Skyscraper0agt.isLocalizedModule_quotLocMap`, `(K(U)/J(U))_𝔭 = K(U)_𝔭/J(U)_𝔭`).
2. **Support.** Every prime of `B` is `𝔭_y` for a unique `y ∈ U` (`IsAffineOpen.fromSpec`,
   `primeIdealOf`, `range_fromSpec`). For `y ∈ U ∖ T`, `K_y = J_y` (hypothesis), so
   `(G_U)_{𝔭_y} = K_y/J_y = 0`; thus `supp G_U ⊆ {𝔭_x : x ∈ T ∩ U}` (`Module.notMem_support_iff'`),
   a finite set of **maximal** ideals (`primeIdealOf_isMaximal_of_isClosed`, `T` closed points).
3. **Decomposition on `U`.** By `Module.bijective_pi_localizedModule_of_support_subset`,
   `G_U → Π_{x ∈ T ∩ U} (G_U)_{𝔭_x}` is
   bijective; via step 1 (`IsLocalizedModule.iso`) so is `G_U → Π_{x ∈ T ∩ U} K_x/J_x`,
   `g ↦ (quotGerm g)_x` (`quotGermLoc_pi_bijective`; consequences
   `quotGerm_injective_of_stalkIdeal_eq`, `exists_quotGerm_eq_of_stalkIdeal_eq`).
4. **The family.** Given `(g_x)_{x ∈ T}` with `g_x ∈ K_x/J_x`, choose for each affine `U` an
   `s_U ∈ G_U ⊆ Γ(U)/J(U)` with germs `g_x` at all `x ∈ T ∩ U` (step 3, surjectivity).
   Compatibility: for affine `V ≤ U`, both `quotRes (s_U)` and `s_V` lie in `G_V` and have germ
   `g_x` at every `x ∈ T ∩ V` (`quotGerm_quotRes`), so they agree by the injectivity in step 3
   for `V`. Hence `s := (s_U)_U ∈ subFamilies J K`, and `subFamiliesGerm J K T s = (g_x)_x`
   (`germ_eq`).

The hypothesis `hJK` is not logically necessary (replace `K` by `K ⊔ J`) but is free in the
application (`J = E^d·I' ≤ E^d = K`); it is not used in the formal proof. -/
theorem subFamiliesGerm_surjective {X : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsLocallyNoetherian X] (J K : X.IdealSheafData) (hJK : J ≤ K)
    (T : Finset X) (hT : ∀ x ∈ T, IsClosed ({x} : Set X))
    (hsupp : ∀ x : X, x ∉ T → K.stalkIdeal x = J.stalkIdeal x) :
    Function.Surjective (J.subFamiliesGerm K T) := by
  intro n
  -- the target germs, as elements of `O_{X,x}/J_x`
  let n' : ∀ x : T, X.presheaf.stalk x.1 ⧸ J.stalkIdeal x.1 := fun x => (n x).1
  have hn' : ∀ x : T, n' x ∈ J.stalkPiece K x.1 := fun x => (n x).2
  -- step 4: local preimages on every affine open
  have hex := fun U : X.affineOpens => J.exists_quotGerm_eq_of_stalkIdeal_eq K U T hT hsupp n' hn'
  choose g hg using hex
  -- compatibility under restriction
  have hcompat : ∀ (U V : X.affineOpens) (h : U ≤ V), J.quotRes h (g V).1 = (g U).1 := by
    intro U V h
    -- `quotRes h (g V).1 ∈ K(U)/J(U)`
    have hmem : J.quotRes h (g V).1 ∈ Submodule.map (J.ideal U).mkQ (K.ideal U) := by
      obtain ⟨_, k, hk, rfl⟩ := g V
      refine ⟨X.presheaf.map (homOfLE h).op k, Ideal.mem_comap.mp (K.ideal_le_comap_ideal h hk), ?_⟩
      exact (J.quotRes_mk h k).symm
    have := J.quotGerm_injective_of_stalkIdeal_eq K U T hT hsupp ⟨_, hmem⟩ (g U) (fun x hxT => by
      show J.quotGerm U x.2 (J.quotRes h (g V).1) = J.quotGerm U x.2 (g U).1
      rw [J.quotGerm_quotRes h x.2, hg V ⟨x.1, h x.2⟩ hxT, hg U x hxT])
    exact congrArg Subtype.val this
  let s : J.quotFamilies := ⟨fun U => (g U).1, fun U V h => hcompat U V h⟩
  have hs : s ∈ J.subFamilies K := fun U => (g U).2
  refine ⟨⟨s, hs⟩, ?_⟩
  funext x
  apply Subtype.ext
  rw [subFamiliesGerm_apply_coe, J.germ_eq _ (affineOpenOf x.1) (mem_affineOpenOf x.1)]
  exact hg (affineOpenOf x.1) ⟨x.1, mem_affineOpenOf x.1⟩ x.2

end AlgebraicGeometry.Scheme.IdealSheafData

end
