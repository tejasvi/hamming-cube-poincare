/-
Per-frequency Theorem A (PFA), part 1: the functional `C(θ; τ)`, the derivatives of `f_c` in `q` and in `c`,
and the transport identity `d/dt [G_{τ(t)} F_{θ - t}] = i s G ∂_q F` along the equal-subtraction path.
-/
import Poincare11b.FcBounds

namespace Poincare11b

open Complex Real MeasureTheory Set Filter Finset

variable {n : ℕ}

/-- `G_τ(q) = exp(-τ q(1-q)/2)`. -/
noncomputable def Gt (τ q : ℝ) : ℝ := Real.exp (-(τ * (q * (1 - q)) / 2))

/-- `C(θ; τ) = ∫_0^1 (1 - G_τ(q) Re F_θ(q)) dq/(q(1-q))`. -/
noncomputable def Cth (θ : Fin n → ℝ) (τ : ℝ) : ℝ :=
  ∫ q in Ioo (0 : ℝ) 1, (1 - Gt τ q * (Fth θ q).re) / (q * (1 - q))

/-- `C_G` in the variable `T = r²`. -/
noncomputable def CGt (T : ℝ) : ℝ := ∫ q in Ioo (0 : ℝ) 1, (1 - Gt T q) / (q * (1 - q))

/-- `g_c(q) = e^{icq} - e^{-ic(1-q)}`. -/
noncomputable def gc (c q : ℝ) : ℂ := Complex.exp (c * q * I) - Complex.exp (-(c * (1 - q)) * I)

/-- `∂_q f_c(q) = ic f_c(q) - g_c(q)`. -/
noncomputable def fcq (c q : ℝ) : ℂ := I * c * fc c q - gc c q

/-- `∂_c f_c(q) = i q(1-q) g_c(q)`. -/
noncomputable def fcc (c q : ℝ) : ℂ := I * (q * (1 - q)) * gc c q

lemma hasDerivAt_cexp_lin (a b : ℂ) (x : ℝ) :
    HasDerivAt (fun x : ℝ => Complex.exp ((a * x + b) * I)) (a * I * Complex.exp ((a * x + b) * I)) x := by
  have h1 : HasDerivAt (fun x : ℝ => (a * x + b) * I) (a * I) x := by
    have := (((hasDerivAt_id x).ofReal_comp).const_mul a).add_const b
    have := this.mul_const I
    simpa using this
  have := h1.cexp
  convert this using 1; ring

lemma hasDerivAt_fc_q (c q : ℝ) : HasDerivAt (fun q => fc c q) (fcq c q) q := by
  have e : (fun q : ℝ => fc c q) = fun q : ℝ => (1 - (q : ℂ)) * Complex.exp (((c : ℂ) * q + 0) * I) +
      (q : ℂ) * Complex.exp (((c : ℂ) * q + -(c : ℂ)) * I) := by
    funext q; unfold fc; congr 2 <;> ring_nf
  rw [e]
  have h1 : HasDerivAt (fun q : ℝ => 1 - (q : ℂ)) (-1) q := by
    simpa using ((hasDerivAt_id q).ofReal_comp).const_sub (1 : ℂ)
  have h2 : HasDerivAt (fun q : ℝ => (q : ℂ)) 1 q := by simpa using (hasDerivAt_id q).ofReal_comp
  have := (h1.mul (hasDerivAt_cexp_lin c 0 q)).add (h2.mul (hasDerivAt_cexp_lin c (-c) q))
  convert this using 1
  unfold fcq gc fc
  ring_nf

lemma hasDerivAt_fc_c (c q : ℝ) : HasDerivAt (fun c => fc c q) (fcc c q) c := by
  have e : (fun c : ℝ => fc c q) = fun c : ℝ => (1 - (q : ℂ)) * Complex.exp (((q : ℂ) * c + 0) * I) +
      (q : ℂ) * Complex.exp (((-(1 - (q : ℂ))) * c + 0) * I) := by
    funext c; unfold fc; congr 2 <;> ring_nf
  rw [e]
  have := ((hasDerivAt_cexp_lin (q : ℂ) 0 c).const_mul (1 - (q : ℂ))).add
    ((hasDerivAt_cexp_lin (-(1 - (q : ℂ))) 0 c).const_mul (q : ℂ))
  convert this using 1
  unfold fcc gc
  ring_nf

lemma hasDerivAt_fc_sub (a q t : ℝ) : HasDerivAt (fun t => fc (a - t) q) (-fcc (a - t) q) t := by
  have e : (fun t : ℝ => fc (a - t) q) = fun t : ℝ =>
      (1 - (q : ℂ)) * Complex.exp (((-(q : ℂ)) * t + (q : ℂ) * a) * I) +
      (q : ℂ) * Complex.exp (((1 - (q : ℂ)) * t + (-(1 - (q : ℂ)) * a)) * I) := by
    funext t; unfold fc; push_cast; congr 2 <;> ring_nf
  rw [e]
  have := ((hasDerivAt_cexp_lin (-(q : ℂ)) ((q : ℂ) * a) t).const_mul (1 - (q : ℂ))).add
    ((hasDerivAt_cexp_lin (1 - (q : ℂ)) (-(1 - (q : ℂ)) * a) t).const_mul (q : ℂ))
  convert this using 1
  unfold fcc gc
  push_cast
  ring_nf

/-- The per-coordinate identity behind the transport identity: `-∂_c f_c = s c f_c + i s ∂_q f_c`. -/
lemma neg_fcc_eq (c q : ℝ) : -fcc c q = (q * (1 - q) : ℝ) * c * fc c q + I * (q * (1 - q) : ℝ) * fcq c q := by
  unfold fcc fcq
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-- `∂_q F_c(q)`. -/
noncomputable def Fq (c : Fin n → ℝ) (q : ℝ) : ℂ := ∑ j, (∏ l ∈ univ.erase j, fc (c l) q) * fcq (c j) q

lemma hasDerivAt_Fth_q (c : Fin n → ℝ) (q : ℝ) : HasDerivAt (Fth c) (Fq c q) q := by
  have := HasDerivAt.fun_finsetProd (u := univ) (f := fun j q => fc (c j) q) (f' := fun j => fcq (c j) q)
    (x := q) (fun j _ => hasDerivAt_fc_q (c j) q)
  simp only [smul_eq_mul] at this
  exact this

lemma path_deriv_eq (c : Fin n → ℝ) (q : ℝ) :
    ∑ i, (∏ l ∈ univ.erase i, fc (c l) q) * (-fcc (c i) q) =
      (q * (1 - q) : ℝ) * (∑ j, c j : ℝ) * Fth c q + I * (q * (1 - q) : ℝ) * Fq c q := by
  have h : ∀ i, (∏ l ∈ univ.erase i, fc (c l) q) * (-fcc (c i) q) =
      ((q * (1 - q) : ℝ) * (c i : ℂ)) * Fth c q +
        I * (q * (1 - q) : ℝ) * ((∏ l ∈ univ.erase i, fc (c l) q) * fcq (c i) q) := by
    intro i
    have hP : (∏ l ∈ univ.erase i, fc (c l) q) * fc (c i) q = Fth c q :=
      Finset.prod_erase_mul _ _ (mem_univ i)
    rw [neg_fcc_eq, ← hP]; ring
  rw [Finset.sum_congr rfl (fun i _ => h i), Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
    ← Finset.mul_sum]
  unfold Fq
  push_cast
  ring

/-- `d/dt F_{θ - t}(q) = -∑_j (∏_{l ≠ j} f_l) ∂_c f_j = s (∑_j c_j) F + i s ∂_q F`, `c = θ - t`. -/
lemma hasDerivAt_Fth_path (θ : Fin n → ℝ) (q t : ℝ) :
    HasDerivAt (fun t => Fth (fun j => θ j - t) q)
      ((q * (1 - q) : ℝ) * (∑ j, (θ j - t) : ℝ) * Fth (fun j => θ j - t) q +
        I * (q * (1 - q) : ℝ) * Fq (fun j => θ j - t) q) t := by
  have hj : ∀ j ∈ (univ : Finset (Fin n)), HasDerivAt (fun t => fc (θ j - t) q) (-fcc (θ j - t) q) t := by
    intro j _
    exact hasDerivAt_fc_sub (θ j) q t
  have := HasDerivAt.fun_finsetProd (u := univ) (f := fun j t => fc (θ j - t) q)
    (f' := fun j => -fcc (θ j - t) q) (x := t) hj
  simp only [smul_eq_mul] at this
  have key := path_deriv_eq (fun j => θ j - t) q
  rw [key] at this
  exact this

/-- `τ(t) = τ₀ + |θ|² - |θ - t|²`. -/
noncomputable def tauPath (θ : Fin n → ℝ) (τ₀ t : ℝ) : ℝ := τ₀ + ∑ j, θ j ^ 2 - ∑ j, (θ j - t) ^ 2

lemma hasDerivAt_tauPath (θ : Fin n → ℝ) (τ₀ t : ℝ) :
    HasDerivAt (tauPath θ τ₀) (2 * ∑ j, (θ j - t)) t := by
  unfold tauPath
  have hj : ∀ j ∈ (univ : Finset (Fin n)), HasDerivAt (fun t => (θ j - t) ^ 2) (-(2 * (θ j - t))) t := by
    intro j _
    have h1 : HasDerivAt (fun t : ℝ => θ j - t) (-1) t := by simpa using (hasDerivAt_id t).const_sub (θ j)
    have := h1.pow 2
    convert this using 1; push_cast; ring
  have := (HasDerivAt.fun_sum hj).const_sub (τ₀ + ∑ j, θ j ^ 2)
  convert this using 1
  rw [Finset.sum_neg_distrib, neg_neg, Finset.mul_sum]

lemma hasDerivAt_Gt_path (θ : Fin n → ℝ) (τ₀ q t : ℝ) :
    HasDerivAt (fun t => Gt (tauPath θ τ₀ t) q)
      (Gt (tauPath θ τ₀ t) q * (-((q * (1 - q)) * ∑ j, (θ j - t)))) t := by
  have h1 : HasDerivAt (fun t => -(tauPath θ τ₀ t * (q * (1 - q)) / 2))
      (-((2 * ∑ j, (θ j - t)) * (q * (1 - q)) / 2)) t :=
    (((hasDerivAt_tauPath θ τ₀ t).mul_const (q * (1 - q))).div_const 2).fun_neg
  have h2 := h1.exp
  rw [show -((2 * ∑ j, (θ j - t)) * (q * (1 - q)) / 2) = -((q * (1 - q)) * ∑ j, (θ j - t)) by ring] at h2
  unfold Gt
  exact h2

/-- The transport identity: `d/dt [G_{τ(t)} F_{θ - t}](q) = i s G ∂_q F`. -/
lemma hasDerivAt_transport (θ : Fin n → ℝ) (τ₀ q t : ℝ) :
    HasDerivAt (fun t => (Gt (tauPath θ τ₀ t) q : ℂ) * Fth (fun j => θ j - t) q)
      (I * (q * (1 - q) : ℝ) * (Gt (tauPath θ τ₀ t) q : ℂ) * Fq (fun j => θ j - t) q) t := by
  have hG := (hasDerivAt_Gt_path θ τ₀ q t).ofReal_comp
  have := hG.mul (hasDerivAt_Fth_path θ q t)
  convert this using 1
  push_cast
  ring

/-- The `t`-derivative of the integrand of `C(θ - t; τ(t))` at `q ∈ (0,1)`. -/
lemma hasDerivAt_integrand (θ : Fin n → ℝ) (τ₀ t : ℝ) {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun t => (1 - Gt (tauPath θ τ₀ t) q * (Fth (fun j => θ j - t) q).re) / (q * (1 - q)))
      (Gt (tauPath θ τ₀ t) q * (Fq (fun j => θ j - t) q).im) t := by
  have hs : q * (1 - q) ≠ 0 := (mul_pos hq.1 (by linarith [hq.2])).ne'
  have h1 := (hasDerivAt_transport θ τ₀ q t)
  have h2 : HasDerivAt (fun t => ((Gt (tauPath θ τ₀ t) q : ℂ) * Fth (fun j => θ j - t) q).re)
      (I * (q * (1 - q) : ℝ) * (Gt (tauPath θ τ₀ t) q : ℂ) * Fq (fun j => θ j - t) q).re t :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt t h1
  have h3 := (h2.const_sub 1).div_const (q * (1 - q))
  set Fv := Fq (fun j => θ j - t) q with hFv
  set Gv := Gt (tauPath θ τ₀ t) q with hGv
  convert h3 using 1
  · funext t
    congr 1; congr 1
    rw [Complex.re_ofReal_mul]
  · rw [show I * ((q * (1 - q) : ℝ) : ℂ) * (Gv : ℂ) * Fv = ((q * (1 - q) * Gv : ℝ) : ℂ) * (I * Fv) by
      push_cast; ring, Complex.re_ofReal_mul, Complex.mul_re, Complex.I_re, Complex.I_im]
    rw [eq_div_iff hs]
    ring

end Poincare11b
