import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.Cech.CechAltFunctorial
import MiyaokaMori.Algebra.HomologyZeroKer
import MiyaokaMori.AlgebraicGeometry.Cohomology.Cech.Stacks01eu

/-! # `H^0` of the alternating Čech complex

If `U : Fin n → X.Opens` covers `X` (`⨆ U_i = ⊤`) and `N` is an `O_X`-module, then `H^0` of the
alternating Čech complex is `Γ(X, O_X)`-linearly isomorphic to the global sections `Γ(N, X)`,
naturally in `φ : N → N'` (`H^0(Č(φ))` corresponds to `φ(X)`).

Proof: `H^0(Č) = ker d^0`; `ker d^0` is the set of families of sections agreeing on pairwise
intersections, which is `Γ(N, X)` by the sheaf axiom (`cechAlt_sections_equiv_ker`); naturality
follows from the componentwise action of the chain map on families (`cechToFamily_map`) and the
compatibility of `φ` with restriction (`app_map`).

Source: Hartshorne III.4.1 (p. 219, "`Ȟ^0(𝔘, F) = Γ(X, F)`", by the sheaf axiom).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}} {n : ℕ} (U : Fin n → X.Opens)

/-- Hartshorne III.4.1 (sheaf axiom): over a cover `U`, global sections are in bijection with Čech
`0`-cocycles, `s ↦ (s|_{U_σ})_σ`, `Γ(X, O_X)`-linearly.

Proof sketch:
1. The map `ρ : Γ(N, ⊤) → C^0`, `ρ(s)_σ = s|_{U_σ}` (`σ : Fin 1 ↪o Fin n`, `U_σ = ⨅ k, U (σ k) = U_{σ 0}`),
   transported to `cechTermAlt U N 0` via `cechToFamily_bijective U N 0`. `Γ(X,⊤)`-linearity: the
   `σ`-th factor of `C^0` is `N.sectionsOverTop U_σ`, a scalar `r` acts by `r|_{U_σ}`, and
   `(r • s)|_{U_σ} = r|_{U_σ} • s|_{U_σ}` (`Scheme.Modules.map_smul`).
2. `d ρ(s) = 0`: `cechToFamily_diff` turns `d` into `cechFamilyD`; for `p = 0`,
   `(d t)_τ = t_{τ∘δ_0}|_{U_τ} − t_{τ∘δ_1}|_{U_τ}` (`Fin.sum_univ_two`), and both terms are `s|_{U_τ}`.
3. Injective: `ρ(s) = 0` ⇒ `s` vanishes on every `U_i` (take `σ = singleEmb i`, `U_σ = U_i`);
   `⨆ U_i = ⊤` and separatedness of the sheaf (`TopCat.Sheaf.eq_of_locally_eq'`).
4. Onto the kernel: `t ∈ ker d^0` ⇒ for `i < j`, `t_i|_{U_i ∩ U_j} = t_j|_{U_i ∩ U_j}`
   (`τ = pairEmb i j h`, `face_pair_zero`/`face_pair_one`); `i = j` is trivial and `i > j` symmetric;
   gluing (`TopCat.Sheaf.existsUnique_gluing'`) produces `s`.

Edge cases: for `n = 0`, `hcov` gives `⊤ = ⊥`, `Γ(N, ⊤) = 0` (sections over the empty set are
unique), `C^0` is the empty product `= 0`, and the claim holds (steps 3 and 4 go through for the empty
index set); for `n = 1`, `C^1 = 0` and `ker d^0 = C^0 = Γ(N, U_0) = Γ(N, ⊤)`. -/
theorem cechAlt_sections_equiv_ker (hcov : ⨆ i, U i = ⊤) (N : X.Modules) :
    ∃ e : Γ(N, ⊤) ≃ₗ[Γ(X, ⊤)] LinearMap.ker (cechDiffAlt U N 0).hom,
      ∀ (s : Γ(N, ⊤)) (σ : Fin (0 + 1) ↪o Fin n),
        cechToFamily U N 0 ((e s : LinearMap.ker (cechDiffAlt U N 0).hom) : cechTermAlt U N 0) σ =
          N.presheaf.map (homOfLE (le_top : (⨅ k, U (σ k)) ≤ ⊤)).op s := by
  classical
  open Stacks01euAux in
  -- `ρ : Γ(N, ⊤) → C^0`, `s ↦ (s|_{U_σ})_σ`
  let ρ₀ : N.sectionsOverTop ⊤ ⟶ cechTermAlt U N 0 :=
    Pi.lift fun σ : Fin (0 + 1) ↪o Fin n => N.sectionsOverTopRestrict (le_top : (⨅ k, U (σ k)) ≤ ⊤)
  have hρ₀ : ∀ (s : Γ(N, ⊤)) (σ : Fin (0 + 1) ↪o Fin n),
      cechToFamily U N 0 (ρ₀.hom s) σ =
        N.presheaf.map (homOfLE (le_top : (⨅ k, U (σ k)) ≤ ⊤)).op s := by
    intro s σ
    have h : ρ₀ ≫ Pi.π (fun σ : Fin (0 + 1) ↪o Fin n => N.sectionsOverTop (⨅ k, U (σ k))) σ =
        N.sectionsOverTopRestrict (le_top : (⨅ k, U (σ k)) ≤ ⊤) := Limits.Pi.lift_π _ σ
    exact congrArg (fun ψ => ψ.hom s) h
  have hker : ∀ s : Γ(N, ⊤), (cechDiffAlt U N 0).hom (ρ₀.hom s) = 0 := by
    intro s
    apply (cechToFamily_bijective U N 1).1
    rw [cechToFamily_diff]
    funext τ
    show ∑ k : Fin 2, ((-1 : ℤ) ^ (k : ℕ)) • N.presheaf.map _ (cechToFamily U N 0 (ρ₀.hom s) _) =
      cechToFamily U N 1 0 τ
    rw [Fin.sum_univ_two, hρ₀, hρ₀]
    have e0 := famRes_comp N (le_top : (⨅ k, U ((CechAltAlg.face τ 0) k)) ≤ ⊤) (cech_face_le U τ 0) s
    have e1 := famRes_comp N (le_top : (⨅ k, U ((CechAltAlg.face τ 1) k)) ≤ ⊤) (cech_face_le U τ 1) s
    refine (congrArg₂ (fun a b => ((-1 : ℤ) ^ ((0 : Fin 2) : ℕ)) • a + ((-1 : ℤ) ^ ((1 : Fin 2) : ℕ)) • b)
      e0 e1).trans ?_
    have hz : cechToFamily U N 1 0 τ = 0 := map_zero _
    rw [hz]
    simp
  -- the cover `W' i = ⨅ k, U (singleEmb i k)`
  let W' : Fin n → X.Opens := fun i => ⨅ k, U (singleEmb i k)
  have hW'le : ∀ i, W' i ≤ U i := fun i => iInf_le (fun k => U (singleEmb i k)) 0
  have hW'ge : ∀ i, U i ≤ W' i := fun i => le_iInf fun _ => le_rfl
  have hcover : (⊤ : X.Opens) ≤ iSup W' := by
    rw [← hcov]
    exact iSup_mono hW'ge
  have hσ : ∀ σ : Fin (0 + 1) ↪o Fin n, singleEmb (σ 0) = σ := by
    intro σ
    apply RelEmbedding.ext
    intro m
    have : m = 0 := Fin.fin_one_eq_zero m
    subst this
    rfl
  -- the linear map into the kernel
  let ρ : Γ(N, ⊤) →ₗ[Γ(X, ⊤)] LinearMap.ker (cechDiffAlt U N 0).hom :=
    { toFun := fun s => ⟨ρ₀.hom s, hker s⟩
      map_add' := fun s t => Subtype.ext (map_add ρ₀.hom s t)
      map_smul' := fun r s => Subtype.ext (by
        have e : (r • (show ↑(N.sectionsOverTop ⊤) from s) : ↑(N.sectionsOverTop ⊤)) =
            (show ↑(N.sectionsOverTop ⊤) from (r • s : Γ(N, ⊤))) := by
          change X.presheaf.map (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op r • s = r • s
          rw [show (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)) = 𝟙 _ from Subsingleton.elim _ _, op_id,
            X.presheaf.map_id]
          rfl
        show ρ₀.hom (r • s : Γ(N, ⊤)) = r • ρ₀.hom s
        exact (congrArg ρ₀.hom e).symm.trans (LinearMap.map_smul ρ₀.hom r s)) }
  have hρ : ∀ (s : Γ(N, ⊤)) (σ : Fin (0 + 1) ↪o Fin n),
      cechToFamily U N 0 ((ρ s : LinearMap.ker (cechDiffAlt U N 0).hom) : cechTermAlt U N 0) σ =
        N.presheaf.map (homOfLE (le_top : (⨅ k, U (σ k)) ≤ ⊤)).op s := hρ₀
  have hinj : Function.Injective ρ := by
    intro s t hst
    apply TopCat.Sheaf.eq_of_locally_eq' (F := N.toAddCommGrpSheaf) W' ⊤
      (fun i => homOfLE le_top) hcover
    intro i
    have h1 := hρ s (singleEmb i)
    have h2 := hρ t (singleEmb i)
    rw [hst] at h1
    exact h1.symm.trans h2
  have hsurj : Function.Surjective ρ := by
    rintro ⟨t, ht⟩
    have ht' : (cechDiffAlt U N 0).hom t = 0 := ht
    let tf : CechFamily U N 0 := cechToFamily U N 0 t
    have hd1 : cechFamilyD U N 0 tf = 0 := by
      rw [← cechToFamily_diff, ht']
      funext τ
      exact map_zero _
    let sf : ∀ i, Γ(N, W' i) := fun i => tf (singleEmb i)
    have hlt : ∀ (i k : Fin n) (h : i < k) (T : X.Opens) (hi : T ≤ W' i) (hk : T ≤ W' k),
        famRes N hi (sf i) = famRes N hk (sf k) := by
      intro i k h T hi hk
      have hT : T ≤ ⨅ m, U (pairEmb i k h m) := by
        refine le_iInf fun m => ?_
        fin_cases m
        · exact hi.trans (hW'le i)
        · exact hk.trans (hW'le k)
      have h0 := congrFun hd1 (pairEmb i k h)
      change ∑ m : Fin 2, ((-1 : ℤ) ^ (m : ℕ)) • famRes N (cech_face_le U (pairEmb i k h) m)
        (tf (CechAltAlg.face (pairEmb i k h) m)) = 0 at h0
      rw [Fin.sum_univ_two] at h0
      have hle0 : (⨅ m, U (pairEmb i k h m)) ≤ W' k :=
        le_iInf fun _ => iInf_le (fun m => U (pairEmb i k h m)) 1
      have hle1 : (⨅ m, U (pairEmb i k h m)) ≤ W' i :=
        le_iInf fun _ => iInf_le (fun m => U (pairEmb i k h m)) 0
      rw [CechAltAlg.transport_res (A := ℤ) (fun q (σ : Fin (q + 1) ↪o Fin n) => ⨅ k, U (σ k))
          (fun W : X.Opens => Γ(N, W)) (fun h => famRes N h) tf (face_pair_zero i k h)
          (cech_face_le U (pairEmb i k h) 0) hle0,
        CechAltAlg.transport_res (A := ℤ) (fun q (σ : Fin (q + 1) ↪o Fin n) => ⨅ k, U (σ k))
          (fun W : X.Opens => Γ(N, W)) (fun h => famRes N h) tf (face_pair_one i k h)
          (cech_face_le U (pairEmb i k h) 1) hle1] at h0
      simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul] at h0
      rw [← sub_eq_add_neg, sub_eq_zero] at h0
      have h1 := congrArg (famRes N hT) h0
      rw [famRes_comp, famRes_comp] at h1
      exact h1.symm
    have hcompat : TopCat.Presheaf.IsCompatible N.toAddCommGrpSheaf.obj W' sf := by
      intro i k
      rcases lt_trichotomy i k with h | h | h
      · exact hlt i k h _ inf_le_left inf_le_right
      · subst h
        rfl
      · exact (hlt k i h _ inf_le_right inf_le_left).symm
    obtain ⟨u, hu, -⟩ := TopCat.Sheaf.existsUnique_gluing' (F := N.toAddCommGrpSheaf) W' ⊤
      (fun i => homOfLE le_top) hcover sf hcompat
    refine ⟨u, Subtype.ext ?_⟩
    apply (cechToFamily_bijective U N 0).1
    funext σ
    refine (hρ u σ).trans ?_
    have h3 := hu (σ 0)
    have h4 : ∀ (σ' : Fin (0 + 1) ↪o Fin n) (e : σ' = σ),
        N.presheaf.map (homOfLE (le_top : (⨅ k, U (σ' k)) ≤ ⊤)).op u = tf σ' →
        N.presheaf.map (homOfLE (le_top : (⨅ k, U (σ k)) ≤ ⊤)).op u = tf σ := by
      rintro σ' rfl h
      exact h
    exact h4 (singleEmb (σ 0)) (hσ σ) h3
  refine ⟨LinearEquiv.ofBijective ρ ⟨hinj, hsurj⟩, fun s σ => hρ s σ⟩

/-- `H^0(Č_alt(U, N)) ≃ ker d^0`, naturally in `φ` (specialization of
`CochainComplex.exists_homologyZero_equiv_ker`). -/
theorem cechAlt_homologyZero_equiv_ker {N N' : X.Modules} (φ : N ⟶ N') :
    ∃ (a : (cechComplexAlt U N).homology 0 ≃ₗ[Γ(X, ⊤)] LinearMap.ker (cechDiffAlt U N 0).hom)
      (a' : (cechComplexAlt U N').homology 0 ≃ₗ[Γ(X, ⊤)] LinearMap.ker (cechDiffAlt U N' 0).hom),
      ∀ x : (cechComplexAlt U N).homology 0,
        ((a' ((HomologicalComplex.homologyMap (cechComplexAltMap U φ) 0).hom x) :
            LinearMap.ker (cechDiffAlt U N' 0).hom) : cechTermAlt U N' 0) =
          (cechTermAltMap U φ 0).hom ((a x : LinearMap.ker (cechDiffAlt U N 0).hom) :
            cechTermAlt U N 0) :=
  CochainComplex.exists_homologyZero_equiv_ker (cechComplexAltMap U φ)
    (ModuleCat.isZero_of_subsingleton (ModuleCat.of Γ(X, ⊤) PUnit))
    (ModuleCat.isZero_of_subsingleton (ModuleCat.of Γ(X, ⊤) PUnit))

/-- Linear, natural version of Hartshorne III.4.1: `Ȟ^0(U, N) ≃ Γ(N, X)`. -/
theorem cechAlt_homologyZero_equiv_sections (hcov : ⨆ i, U i = ⊤) {N N' : X.Modules} (φ : N ⟶ N') :
    ∃ (e : (cechComplexAlt U N).homology 0 ≃ₗ[Γ(X, ⊤)] Γ(N, ⊤))
      (e' : (cechComplexAlt U N').homology 0 ≃ₗ[Γ(X, ⊤)] Γ(N', ⊤)),
      ∀ x : (cechComplexAlt U N).homology 0,
        e' ((HomologicalComplex.homologyMap (cechComplexAltMap U φ) 0).hom x) = φ.app ⊤ (e x) := by
  obtain ⟨a, a', ha⟩ := cechAlt_homologyZero_equiv_ker U φ
  obtain ⟨b, hb⟩ := cechAlt_sections_equiv_ker U hcov N
  obtain ⟨b', hb'⟩ := cechAlt_sections_equiv_ker U hcov N'
  refine ⟨a.trans b.symm, a'.trans b'.symm, fun x => ?_⟩
  show b'.symm (a' _) = φ.app ⊤ (b.symm (a x))
  rw [LinearEquiv.symm_apply_eq]
  apply Subtype.ext
  apply (cechToFamily_bijective U N' 0).1
  funext σ
  rw [hb', ha, cechToFamily_map, ← app_map]
  congr 1
  rw [← hb, LinearEquiv.apply_symm_apply]

end AlgebraicGeometry.Scheme.Modules

end
