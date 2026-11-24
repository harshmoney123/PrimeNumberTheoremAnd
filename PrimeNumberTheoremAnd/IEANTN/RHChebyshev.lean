module

public import Architect
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.NumberTheory.Harmonic.Bounds
public import PrimeNumberTheoremAnd.Defs

@[expose] public section

open Real Filter Asymptotics Finset
open scoped Chebyshev

blueprint_comment /--
\section{Chebyshev error bounds under the Riemann Hypothesis}\label{rh-chebyshev-sec}

This section is the entry point for RH-conditional explicit bounds on $\psi$.  The two
bounds below are \emph{stated as propositions} (not yet proved: the project has no explicit
formula for $\psi$ in terms of the zeroes of $\zeta$).  Downstream RH-conditional results can take
them as hypotheses, and the implication from Schoenfeld's explicit form to von Koch's $O$-form is
proved.
-/

@[blueprint
  "rh-psi-schoenfeld-bound"
  (title := "Schoenfeld's explicit bound for $\\psi$ under RH")
  (statement := /-- Assuming the Riemann Hypothesis, for all $x \geq 73.2$,
  \[ |\psi(x) - x| < \frac{\sqrt{x}\,\log^2 x}{8\pi}, \]
  see \cite[Corollary~1 of Theorem~10]{RS-chebyshev-II}. This is the statement of the
  proposition only; it is not proved here. -/)
  (latexEnv := "definition")]
def RHPsiSchoenfeldBound : Prop :=
  RiemannHypothesis → ∀ x : ℝ, 73.2 ≤ x → |ψ x - x| < √x * (log x) ^ 2 / (8 * π)

@[blueprint
  "rh-psi-von-koch-bound"
  (title := "von Koch's bound for $\\psi$ under RH")
  (statement := /-- Assuming the Riemann Hypothesis,
  $\psi(x) = x + O(\sqrt{x}\log^2 x)$ as $x \to \infty$ (von Koch 1901). This is the statement of
  the proposition only; it is not proved here. -/)
  (latexEnv := "definition")]
def RHPsiVonKochBound : Prop :=
  RiemannHypothesis → (fun x : ℝ ↦ ψ x - x) =O[atTop] fun x : ℝ ↦ √x * (log x) ^ 2

@[blueprint
  "rh-psi-von-koch-of-schoenfeld"
  (title := "Von Koch's bound from Schoenfeld's explicit bound")
  (statement := /-- Schoenfeld's explicit bound $|\psi(x)-x| < \sqrt{x}\log^2 x/(8\pi)$ for
  $x \ge 73.2$ implies von Koch's $\psi(x) = x + O(\sqrt{x}\log^2 x)$. -/)
  (proof := /-- Take the constant $1/(8\pi)$ and the eventual range $x \ge 73.2$. -/)
  (uses := ["rh-psi-schoenfeld-bound", "rh-psi-von-koch-bound"])
  (latexEnv := "theorem")]
theorem RHPsiVonKochBound_of_schoenfeld (h : RHPsiSchoenfeldBound) : RHPsiVonKochBound := by
  intro RH
  refine IsBigO.of_bound (1 / (8 * π)) ?_
  filter_upwards [eventually_ge_atTop (73.2 : ℝ)] with x hx
  have h1 := (h RH x hx).le
  have hx0 : 0 ≤ √x * (log x) ^ 2 := by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hx0]
  calc |ψ x - x| ≤ √x * (log x) ^ 2 / (8 * π) := h1
    _ = 1 / (8 * π) * (√x * (log x) ^ 2) := by ring

@[blueprint
  "rh-norm-cpow-zero"
  (title := "Modulus of $x^\\rho$ under RH")
  (statement := /-- Assuming the Riemann Hypothesis, if $\rho$ is a nontrivial zero of $\zeta$
  and $x > 0$, then $|x^\rho| = \sqrt{x}$. This is the size of each term of the explicit
  formula $\psi(x) = x - \sum_\rho x^\rho/\rho - \cdots$. -/)
  (proof := /-- $|x^\rho| = x^{\Re\rho}$ and $\Re \rho = 1/2$. -/)
  (latexEnv := "lemma")]
lemma RiemannHypothesis.norm_cpow_nontrivialZero (RH : RiemannHypothesis) {ρ : ℂ}
    (hρ : riemannZeta ρ = 0) (htriv : ¬∃ n : ℕ, ρ = -2 * (n + 1)) (h1 : ρ ≠ 1)
    {x : ℝ} (hx : 0 < x) : ‖(x : ℂ) ^ ρ‖ = √x := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx, RH ρ hρ htriv h1, Real.sqrt_eq_rpow]

@[blueprint
  "rh-theta-von-koch-bound"
  (title := "von Koch's bound for $\\theta$ under RH")
  (statement := /-- Assuming the Riemann Hypothesis,
  $\theta(x) = x + O(\sqrt{x}\log^2 x)$ as $x \to \infty$. This is the statement of the
  proposition only; it is not proved here. -/)
  (latexEnv := "definition")]
def RHThetaVonKochBound : Prop :=
  RiemannHypothesis → (fun x : ℝ ↦ θ x - x) =O[atTop] fun x : ℝ ↦ √x * (log x) ^ 2

@[blueprint
  "rh-theta-von-koch-of-psi"
  (title := "Von Koch's bound for $\\theta$ from that for $\\psi$")
  (statement := /-- The $O(\sqrt{x}\log^2 x)$ bound for $\psi(x)-x$ implies the same for
  $\theta(x)-x$. -/)
  (proof := /-- $0 \le \psi(x)-\theta(x) \le 2\sqrt{x}\log x \le 2\sqrt{x}\log^2 x$ for $x \ge e$,
  so $|\theta(x)-x| \le |\psi(x)-x| + 2\sqrt{x}\log^2 x$. -/)
  (uses := ["rh-psi-von-koch-bound", "rh-theta-von-koch-bound"])
  (latexEnv := "theorem")]
theorem RHThetaVonKochBound_of_psi (h : RHPsiVonKochBound) : RHThetaVonKochBound := by
  intro RH
  obtain ⟨C, hC⟩ := (h RH).bound
  refine IsBigO.of_bound (C + 2) ?_
  filter_upwards [hC, eventually_ge_atTop (3 : ℝ)] with x hxC hx3
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hlog : 1 ≤ log x := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_three
    linarith
  have hs : 0 ≤ √x := Real.sqrt_nonneg x
  have hd := Chebyshev.psi_sub_theta_le hx1
  have hd0 := sub_nonneg.mpr (Chebyshev.theta_le_psi x)
  have hpos : 0 ≤ √x * (log x) ^ 2 := by positivity
  have h2 : 2 * √x * log x ≤ 2 * (√x * (log x) ^ 2) := by
    nlinarith [mul_nonneg hs (sub_nonneg.mpr hlog), mul_nonneg hs (mul_nonneg (sub_nonneg.mpr hlog) (by linarith : (0:ℝ) ≤ log x))]
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hpos] at hxC ⊢
  have : |θ x - x| ≤ |ψ x - x| + (ψ x - θ x) := by
    rw [abs_le]; constructor <;> cases abs_cases (ψ x - x) <;> linarith [neg_abs_le (ψ x - x), le_abs_self (ψ x - x)]
  nlinarith

@[blueprint
  "rh-norm-cpow-div-zero"
  (title := "Size of an explicit-formula term under RH")
  (statement := /-- Assuming the Riemann Hypothesis, if $\rho$ is a nontrivial zero of $\zeta$ and
  $x>0$, then $|x^\rho/\rho| = \sqrt{x}/|\rho|$, which is at most $2\sqrt{x}$, and at most
  $\sqrt{x}/|\Im\rho|$ when $\Im\rho \ne 0$. These bound the terms of the explicit formula
  $\psi(x) = x - \sum_\rho x^\rho/\rho - \cdots$. -/)
  (proof := /-- $|x^\rho| = \sqrt{x}$ by the previous lemma, and $|\rho| \ge |\Re\rho| = 1/2$ and
  $|\rho| \ge |\Im\rho|$. -/)
  (uses := ["rh-norm-cpow-zero"])
  (latexEnv := "lemma")]
lemma RiemannHypothesis.norm_cpow_div_nontrivialZero (RH : RiemannHypothesis) {ρ : ℂ}
    (hρ : riemannZeta ρ = 0) (htriv : ¬∃ n : ℕ, ρ = -2 * (n + 1)) (h1 : ρ ≠ 1)
    {x : ℝ} (hx : 0 < x) :
    ‖(x : ℂ) ^ ρ / ρ‖ = √x / ‖ρ‖ ∧ ‖(x : ℂ) ^ ρ / ρ‖ ≤ 2 * √x ∧
      (ρ.im ≠ 0 → ‖(x : ℂ) ^ ρ / ρ‖ ≤ √x / |ρ.im|) := by
  have hre : ρ.re = 1 / 2 := RH ρ hρ htriv h1
  have hn : ‖(x : ℂ) ^ ρ‖ = √x := RH.norm_cpow_nontrivialZero hρ htriv h1 hx
  have hhalf : 1 / 2 ≤ ‖ρ‖ := by
    have := Complex.abs_re_le_norm ρ
    rw [hre, abs_of_pos (by norm_num)] at this
    exact this
  have hpos : 0 < ‖ρ‖ := by linarith
  have hs : 0 ≤ √x := Real.sqrt_nonneg x
  have heq : ‖(x : ℂ) ^ ρ / ρ‖ = √x / ‖ρ‖ := by rw [norm_div, hn]
  refine ⟨heq, ?_, fun him => ?_⟩
  · rw [heq, div_le_iff₀ hpos]; nlinarith
  · rw [heq]
    exact div_le_div_of_nonneg_left hs (abs_pos.mpr him) (Complex.abs_im_le_norm ρ)

@[blueprint
  "rh-sum-inv-heights-le"
  (title := "Sum of $1/|\\gamma|$ from a unit-window count")
  (statement := /-- Let $T \ge 1$ and let $\gamma_i$ ($i$ in a finite set) be heights with $1 \le |\gamma_i| \le T$,
  and suppose that for each integer $k \ge 1$ at most $A\log(k+2)$ of them satisfy
  $k \le |\gamma_i| < k+1$ (the Riemann--von Mangoldt count $N(t+1)-N(t) = O(\log t)$). Then
  $\sum_i 1/|\gamma_i| \le A\log(T+2)\,(1+\log T)$. This is the zero-sum step of von Koch's
  argument, isolated from the zeta function. -/)
  (proof := /-- Group by $k=\lfloor|\gamma_i|\rfloor$; each group contributes at most
  $A\log(k+2)/k \le A\log(T+2)/k$, and $\sum_{k\le T}1/k \le 1+\log T$. -/)
  (latexEnv := "lemma")]
lemma sum_inv_abs_le_of_window_count {ι : Type*} (s : Finset ι) (γ : ι → ℝ) {T A : ℝ}
    (hA : 0 ≤ A) (hT1 : 1 ≤ T) (hT : ∀ i ∈ s, 1 ≤ |γ i| ∧ |γ i| ≤ T)
    (hcount : ∀ k : ℕ, (#{i ∈ s | ⌊|γ i|⌋₊ = k} : ℝ) ≤ A * log (k + 2)) :
    ∑ i ∈ s, 1 / |γ i| ≤ A * log (T + 2) * (1 + log T) := by
  classical
  have hmaps : ∀ i ∈ s, ⌊|γ i|⌋₊ ∈ Icc 1 ⌊T⌋₊ := fun i hi => by
    rw [mem_Icc]
    exact ⟨Nat.le_floor (by simpa using (hT i hi).1), Nat.floor_le_floor (hT i hi).2⟩
  have hlogT : 0 ≤ log (T + 2) := Real.log_nonneg (by linarith)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  calc ∑ k ∈ Icc 1 ⌊T⌋₊, ∑ i ∈ s with ⌊|γ i|⌋₊ = k, 1 / |γ i|
      ≤ ∑ k ∈ Icc 1 ⌊T⌋₊, A * log (T + 2) * (1 / (k : ℝ)) := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (mem_Icc.mp hk).1
        have hkT : (k : ℝ) ≤ T := (Nat.le_floor_iff (by linarith)).mp (mem_Icc.mp hk).2
        have hterm : ∀ i ∈ ({i ∈ s | ⌊|γ i|⌋₊ = k} : Finset ι), 1 / |γ i| ≤ 1 / (k : ℝ) := by
          intro i hi
          have hik := (mem_filter.mp hi).2
          have : (k : ℝ) ≤ |γ i| := by rw [← hik]; exact Nat.floor_le (abs_nonneg _)
          exact one_div_le_one_div_of_le (by linarith) this
        calc ∑ i ∈ s with ⌊|γ i|⌋₊ = k, 1 / |γ i|
            ≤ #{i ∈ s | ⌊|γ i|⌋₊ = k} • (1 / (k : ℝ)) := Finset.sum_le_card_nsmul _ _ _ hterm
          _ = (#{i ∈ s | ⌊|γ i|⌋₊ = k} : ℝ) * (1 / (k : ℝ)) := by rw [nsmul_eq_mul]
          _ ≤ (A * log (k + 2)) * (1 / (k : ℝ)) :=
              mul_le_mul_of_nonneg_right (hcount k) (by positivity)
          _ ≤ A * log (T + 2) * (1 / (k : ℝ)) := by
              gcongr
    _ = A * log (T + 2) * (harmonic ⌊T⌋₊ : ℝ) := by
        rw [← Finset.mul_sum, harmonic_eq_sum_Icc]
        simp
    _ ≤ A * log (T + 2) * (1 + log T) := by
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hA hlogT)
        refine (harmonic_le_one_add_log _).trans ?_
        have : (⌊T⌋₊ : ℝ) ≤ T := Nat.floor_le (by linarith)
        have hpos : (0 : ℝ) < ⌊T⌋₊ := by
          have : 1 ≤ ⌊T⌋₊ := Nat.le_floor (by simpa using hT1)
          exact_mod_cast this
        have := Real.log_le_log hpos this
        linarith
