/-
Assembly: from the certificate facts to the Poincaré inequality (paper Theorem 1.1), by the mean value theorem on each
θ-interval (see README.md, Presentation).
-/
import Poincare11a.CertSound

namespace Poincare11a

open Finset Poincare11a.Cert

variable {n : ℕ}

/-- Homogeneity of `Φ`. -/
lemma Phi_smul (m c r : ℝ) (lam : Fin n → ℝ) : Phi m c (fun j => r * lam j) = |r| * Phi m c lam := by
  simp only [Phi, Ex, Ssum]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  have : ∑ j, r * lam j * dl m c (z j) = r * ∑ j, lam j * dl m c (z j) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [this, abs_mul]; ring

lemma Phi_zero_of_psum (m c : ℝ) (a : Fin n → ℝ) (ha : psum a 2 = 0) : Phi m c a = 0 := by
  have hz : ∀ j, a j = 0 := by
    intro j
    have h := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (a i))).1 ha j (Finset.mem_univ j)
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h
  unfold Phi Ex Ssum
  simp [hz]

/-- The certificate bound for an arbitrary vector `a` (scaled by `|a|`), indexed by the positions of the partition. -/
theorem grad_bound (lib : LibT) (hlib : lib.allPos = true) (ivs : List Ivl) (hpart : partOK ivs = true)
    (t : QT) (ht : t.OK lib ivs 0 0 0) (a : Fin n → ℝ) :
    ∃ U : Fin ivs.length → ℝ,
      (∀ i : Fin ivs.length, ∀ θ ∈ Set.Ioo (thetaOf ivs[i.1].TL) (thetaOf ivs[i.1].TR),
        Phi (Real.sin θ) (Real.cos θ) a ≤ Real.sqrt (psum a 2) * U i) ∧
      ∑ i : Fin ivs.length, (thetaOf ivs[i.1].TR - thetaOf ivs[i.1].TL) * U i ≤ 71 / 50 := by
  by_cases ha : psum a 2 = 0
  · refine ⟨fun _ => 0, fun i θ _ => ?_, by norm_num⟩
    rw [Phi_zero_of_psum _ _ a ha]; simp
  · have hpos : 0 < psum a 2 := lt_of_le_of_ne (psum_even_nonneg a 1) (Ne.symm ha)
    set r := Real.sqrt (psum a 2)
    have hr : 0 < r := Real.sqrt_pos.2 hpos
    set lam : Fin n → ℝ := fun j => a j / r
    have hl : psum lam 2 = 1 := by
      simp only [psum, lam, div_pow, ← Finset.sum_div]
      rw [Real.sq_sqrt hpos.le]; exact div_self ha
    have ha' : a = fun j => r * lam j := funext fun j => by simp only [lam]; field_simp
    obtain ⟨L, hL, hb, hs⟩ := cert_sound lib hlib ivs hpart t ht lam hl
    subst hL
    have hlen : (L.map Prod.fst).length = L.length := List.length_map ..
    refine ⟨fun i => (L[i.1]'(hlen ▸ i.2)).2, fun i θ hθ => ?_, ?_⟩
    · have hi : (L.map Prod.fst)[i.1] = (L[i.1]'(hlen ▸ i.2)).1 := List.getElem_map ..
      rw [hi] at hθ
      have hx := hb (L[i.1]'(hlen ▸ i.2)) (List.getElem_mem ..)
      rw [ha', Phi_smul, abs_of_pos hr]
      exact mul_le_mul_of_nonneg_left (hx.2 θ hθ) hr.le
    · calc ∑ i : Fin (L.map Prod.fst).length, (thetaOf (L.map Prod.fst)[i.1].TR - thetaOf (L.map Prod.fst)[i.1].TL) *
            (L[i.1]'(hlen ▸ i.2)).2
          = ∑ i : Fin L.length, (thetaOf L[i.1].1.TR - thetaOf L[i.1].1.TL) * L[i.1].2 := by
            refine Fintype.sum_equiv (finCongr hlen) _ _ (fun i => ?_)
            simp [List.getElem_map]
        _ = (L.map (fun x => (thetaOf x.1.TR - thetaOf x.1.TL) * x.2)).sum :=
            Fin.sum_univ_fun_getElem L (fun x => (thetaOf x.1.TR - thetaOf x.1.TL) * x.2)
        _ ≤ 71 / 50 := hs

/-- Mean value step on one θ-interval, with a fixed sign vector. -/
lemma mvt_interval (f : Cube n → ℝ) {θ1 θ2 M : ℝ} (h12 : θ1 < θ2)
    (hM : ∀ θ ∈ Set.Ioo θ1 θ2, ∑ x, |Real.cos θ * dPsg f (Real.sin θ) x| ≤ M) :
    ∑ x, |Psg f (Real.sin θ2) x - Psg f (Real.sin θ1) x| ≤ (θ2 - θ1) * M := by
  set Δ : Cube n → ℝ := fun x => Psg f (Real.sin θ2) x - Psg f (Real.sin θ1) x
  set s : Cube n → ℝ := fun x => if 0 ≤ Δ x then 1 else -1
  have hs : ∀ x, s x * Δ x = |Δ x| := fun x => by
    simp only [s]; split_ifs with h
    · rw [one_mul, abs_of_nonneg h]
    · rw [abs_of_neg (not_le.1 h)]; ring
  have hs1 : ∀ x, |s x| ≤ 1 := fun x => by simp only [s]; split_ifs <;> simp
  let ψ : ℝ → ℝ := fun θ => ∑ x, s x * (Psg f (Real.sin θ) x - Psg f (Real.sin θ1) x)
  let ψ' : ℝ → ℝ := fun θ => ∑ x, s x * (Real.cos θ * dPsg f (Real.sin θ) x)
  have hd : ∀ θ, HasDerivAt ψ (ψ' θ) θ := fun θ => by
    apply HasDerivAt.fun_sum
    intro x _
    exact ((hasDerivAt_Psg_sin f x θ).sub_const _).const_mul (s x)
  have hcont : ContinuousOn ψ (Set.Icc θ1 θ2) := fun θ _ => (hd θ).continuousAt.continuousWithinAt
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope ψ ψ' h12 hcont (fun θ _ => hd θ)
  have hψ1 : ψ θ1 = 0 := by simp [ψ]
  have hψ2 : ψ θ2 = ∑ x, |Δ x| := Finset.sum_congr rfl (fun x _ => hs x)
  have hψ' : ψ' c ≤ M := by
    refine le_trans (Finset.sum_le_sum (fun x _ => ?_)) (hM c hc)
    calc s x * (Real.cos c * dPsg f (Real.sin c) x) ≤ |s x * (Real.cos c * dPsg f (Real.sin c) x)| := le_abs_self _
      _ = |s x| * |Real.cos c * dPsg f (Real.sin c) x| := abs_mul _ _
      _ ≤ 1 * |Real.cos c * dPsg f (Real.sin c) x| := mul_le_mul_of_nonneg_right (hs1 x) (abs_nonneg _)
      _ = |Real.cos c * dPsg f (Real.sin c) x| := one_mul _
  rw [hψ1, hψ2, sub_zero] at hslope
  rw [hslope, div_le_iff₀ (sub_pos.2 h12)] at hψ'
  calc ∑ x, |Δ x| ≤ M * (θ2 - θ1) := hψ'
    _ = (θ2 - θ1) * M := mul_comm _ _

lemma chain_telescope (F : Int → ℝ) : ∀ (t : Int) (ivs : List Ivl), chainOK t ivs = true →
    (ivs.map (fun iv => F iv.TR - F iv.TL)).sum = F P32 - F t
  | t, [], h => by
    simp only [chainOK, decide_eq_true_eq] at h
    subst h; simp
  | t, iv :: ivs, h => by
    simp only [chainOK, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨h1, -⟩, h3⟩ := h
    simp only [List.map_cons, List.sum_cons, chain_telescope F iv.TR ivs h3, h1]; ring

lemma gradNorm_eq (f : Cube n → ℝ) (y : Cube n) : gradNorm f y = Real.sqrt (psum (grad f y) 2) := rfl

/-- Theorem 1.1 from the certificate facts (the data enter only through the three hypotheses). -/
theorem poincare_of_cert (lib : LibT) (hlib : lib.allPos = true) (ivs : List Ivl) (hpart : partOK ivs = true)
    (t : QT) (ht : t.OK lib ivs 0 0 0) (f : Cube n → ℝ) :
    avg (fun x => |f x - avg f|) ≤ 71 / 50 * avg (gradNorm f) := by
  choose U hU hsum using fun y => grad_bound lib hlib ivs hpart t ht (grad f y)
  have hpart' := hpart
  simp only [partOK, Bool.and_eq_true, decide_eq_true_eq] at hpart'
  obtain ⟨-, hchain⟩ := hpart'
  obtain ⟨hivs, -⟩ := chain_facts 0 ivs hchain
  -- one interval
  have hstep : ∀ i : Fin ivs.length,
      ∑ x, |Psg f (Real.sin (thetaOf ivs[i.1].TR)) x - Psg f (Real.sin (thetaOf ivs[i.1].TL)) x| ≤
        (thetaOf ivs[i.1].TR - thetaOf ivs[i.1].TL) * ∑ y, gradNorm f y * U y i := by
    intro i
    have hiv : ivs[i.1].ok = true := hivs _ (List.getElem_mem ..)
    apply mvt_interval f (thetaOf_strictMono (ivs[i.1].ok_facts hiv).2.1)
    intro θ hθ
    obtain ⟨hc, hcm⟩ := cos_facts ivs[i.1] hiv θ hθ
    calc ∑ x, |Real.cos θ * dPsg f (Real.sin θ) x| ≤ ∑ y, Phi (Real.sin θ) (Real.cos θ) (grad f y) :=
          sum_abs_dPsg_le hc.ne' hcm (Real.neg_one_le_sin θ) (Real.sin_le_one θ) f
      _ ≤ ∑ y, gradNorm f y * U y i :=
          Finset.sum_le_sum (fun y _ => by rw [gradNorm_eq]; exact hU y i θ hθ)
  -- telescoping over the partition
  have htel : ∀ x, f x - avg f =
      ∑ i : Fin ivs.length, (Psg f (Real.sin (thetaOf ivs[i.1].TR)) x - Psg f (Real.sin (thetaOf ivs[i.1].TL)) x) := by
    intro x
    rw [Fin.sum_univ_fun_getElem ivs (fun iv => Psg f (Real.sin (thetaOf iv.TR)) x -
      Psg f (Real.sin (thetaOf iv.TL)) x)]
    rw [chain_telescope (fun T => Psg f (Real.sin (thetaOf T)) x) 0 ivs hchain]
    simp only [thetaOf_P32, thetaOf_zero, Real.sin_pi_div_two, Real.sin_zero, Psg_one, Psg_zero]
  have hg0 : ∀ y, 0 ≤ gradNorm f y := fun y => Real.sqrt_nonneg _
  -- assemble
  have main : ∑ x, |f x - avg f| ≤ 71 / 50 * ∑ y, gradNorm f y := by
    calc ∑ x, |f x - avg f|
        ≤ ∑ x, ∑ i : Fin ivs.length, |Psg f (Real.sin (thetaOf ivs[i.1].TR)) x - Psg f (Real.sin (thetaOf ivs[i.1].TL)) x| :=
          Finset.sum_le_sum (fun x _ => by rw [htel x]; exact Finset.abs_sum_le_sum_abs _ _)
      _ = ∑ i : Fin ivs.length, ∑ x, |Psg f (Real.sin (thetaOf ivs[i.1].TR)) x - Psg f (Real.sin (thetaOf ivs[i.1].TL)) x| :=
          Finset.sum_comm
      _ ≤ ∑ i : Fin ivs.length, (thetaOf ivs[i.1].TR - thetaOf ivs[i.1].TL) * ∑ y, gradNorm f y * U y i :=
          Finset.sum_le_sum (fun i _ => hstep i)
      _ = ∑ y, gradNorm f y * ∑ i : Fin ivs.length, (thetaOf ivs[i.1].TR - thetaOf ivs[i.1].TL) * U y i := by
          simp only [Finset.mul_sum]; rw [Finset.sum_comm]
          exact Finset.sum_congr rfl (fun y _ => Finset.sum_congr rfl (fun i _ => by ring))
      _ ≤ ∑ y, gradNorm f y * (71 / 50) :=
          Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_left (hsum y) (hg0 y))
      _ = 71 / 50 * ∑ y, gradNorm f y := by rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun y _ => by ring)
  unfold avg
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  rw [mul_div_assoc', div_le_div_iff_of_pos_right h2]
  exact main

end Poincare11a
