module

public import Architect
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.NumberTheory.Harmonic.Bounds
public import PrimeNumberTheoremAnd.Defs
public import PrimeNumberTheoremAnd.IEANTN.ZetaDefinitions

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

@[blueprint
  "rh-zero-sum-sqrt-height"
  (title := "Zero sum truncated at height $\\sqrt{x}$")
  (statement := /-- In the setting of the previous lemma with $T=\sqrt{x}$ and $x \ge 16$,
  $\sqrt{x}\sum_i 1/|\gamma_i| \le A\sqrt{x}\log^2 x$. With each term of the explicit formula
  bounded by $\sqrt{x}/|\gamma_i|$ under RH, this is the $O(\sqrt{x}\log^2 x)$ contribution of
  the zeros with $|\gamma|\le\sqrt{x}$ in von Koch's theorem. -/)
  (proof := /-- Apply the previous lemma; $\log(\sqrt{x}+2) \le \log(2\sqrt{x}) \le \log x$ and
  $1+\log\sqrt{x} \le \log x$ for $x \ge 16$. -/)
  (uses := ["rh-sum-inv-heights-le"])
  (latexEnv := "lemma")]
lemma sqrt_mul_sum_inv_abs_le {ι : Type*} (s : Finset ι) (γ : ι → ℝ) {x A : ℝ}
    (hA : 0 ≤ A) (hx : 16 ≤ x) (hT : ∀ i ∈ s, 1 ≤ |γ i| ∧ |γ i| ≤ √x)
    (hcount : ∀ k : ℕ, (#{i ∈ s | ⌊|γ i|⌋₊ = k} : ℝ) ≤ A * log (k + 2)) :
    √x * ∑ i ∈ s, 1 / |γ i| ≤ A * (√x * (log x) ^ 2) := by
  have hs4 : (4 : ℝ) ≤ √x := by
    rw [show (4 : ℝ) = √16 by rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hx
  have hmain := sum_inv_abs_le_of_window_count s γ hA (by linarith) hT hcount
  have hlog2 : log 2 ≤ log x / 2 := by
    have h4 : log 4 ≤ log x := Real.log_le_log (by norm_num) (by linarith)
    have : log 4 = 2 * log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    linarith
  have hlogs : log (√x) = log x / 2 := by
    rw [Real.log_sqrt (by linarith)]
  have hlogx2 : 2 ≤ log x := by
    have h16 : log 16 ≤ log x := Real.log_le_log (by norm_num) hx
    have : log 16 = 4 * log 2 := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
    have h2 : (0.69 : ℝ) < log 2 := by
      have := Real.log_two_gt_d9; linarith
    linarith
  have hA1 : log (√x + 2) ≤ log x := by
    have : log (√x + 2) ≤ log (2 * √x) := Real.log_le_log (by linarith) (by linarith)
    rw [Real.log_mul (by norm_num) (by linarith), hlogs] at this
    linarith
  have hB : 1 + log (√x) ≤ log x := by rw [hlogs]; linarith
  have hsq : 0 ≤ √x := by linarith
  have hlogpos : 0 ≤ log x := by linarith
  calc √x * ∑ i ∈ s, 1 / |γ i| ≤ √x * (A * log (√x + 2) * (1 + log √x)) :=
        mul_le_mul_of_nonneg_left hmain hsq
    _ ≤ √x * (A * log x * log x) := by
        refine mul_le_mul_of_nonneg_left ?_ hsq
        have h1 : 0 ≤ log (√x + 2) := Real.log_nonneg (by linarith)
        have h2 : 0 ≤ 1 + log (√x) := by rw [hlogs]; linarith
        calc A * log (√x + 2) * (1 + log √x) ≤ A * log x * (1 + log √x) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA1 hA) h2
          _ ≤ A * log x * log x :=
              mul_le_mul_of_nonneg_left hB (mul_nonneg hA hlogpos)
    _ = A * (√x * (log x) ^ 2) := by ring

@[blueprint
  "rh-psi-von-koch-of-explicit-formula"
  (title := "Von Koch from an explicit-formula bound and the window count")
  (statement := /-- Assume RH. Let $(\rho_i)_{i\in\iota}$ be nontrivial zeros of $\zeta$ and, for each
  $x\ge16$, let $s_x$ be a finite subset of indices with $1\le|\Im\rho_i|\le\sqrt{x}$ for $i\in s_x$.
  Suppose
  \[ |\psi(x)-x| \le \sum_{i\in s_x}|x^{\rho_i}/\rho_i| + C\sqrt{x}\log^2 x \quad(x\ge16)\]
  (the shape of the truncated explicit formula at height $\sqrt{x}$, with the zeros of height
  $<1$ and the truncation tail absorbed in $C\sqrt{x}\log^2 x$), and that at most $A\log(k+2)$
  indices of $s_x$ have $\lfloor|\Im\rho_i|\rfloor=k$. Then $\psi(x)=x+O(\sqrt{x}\log^2 x)$.
  The explicit-formula hypothesis is \emph{not} proved here. -/)
  (proof := /-- Bound each term by $\sqrt{x}/|\Im\rho_i|$ and apply the previous lemma. -/)
  (uses := ["rh-norm-cpow-div-zero", "rh-zero-sum-sqrt-height", "rh-psi-von-koch-bound"])
  (latexEnv := "theorem")]
theorem psi_sub_self_isBigO_of_explicit_formula (RH : RiemannHypothesis) {ι : Type*}
    (ρ : ι → ℂ) (hρ : ∀ i, riemannZeta (ρ i) = 0)
    (htriv : ∀ i, ¬∃ n : ℕ, ρ i = -2 * (n + 1)) (h1 : ∀ i, ρ i ≠ 1)
    (s : ℝ → Finset ι) {A C : ℝ} (hA : 0 ≤ A)
    (hs : ∀ x, 16 ≤ x → ∀ i ∈ s x, 1 ≤ |(ρ i).im| ∧ |(ρ i).im| ≤ √x)
    (hexp : ∀ x, 16 ≤ x →
      |ψ x - x| ≤ ∑ i ∈ s x, ‖(x : ℂ) ^ ρ i / ρ i‖ + C * (√x * (log x) ^ 2))
    (hcount : ∀ x, 16 ≤ x → ∀ k : ℕ,
      (#{i ∈ s x | ⌊|(ρ i).im|⌋₊ = k} : ℝ) ≤ A * log (k + 2)) :
    (fun x : ℝ ↦ ψ x - x) =O[atTop] fun x : ℝ ↦ √x * (log x) ^ 2 := by
  refine IsBigO.of_bound (A + C) ?_
  filter_upwards [eventually_ge_atTop (16 : ℝ)] with x hx
  have hsq : 0 ≤ √x := Real.sqrt_nonneg x
  have hpos : 0 ≤ √x * (log x) ^ 2 := by positivity
  have hx0 : 0 < x := by linarith
  have hterm : ∀ i ∈ s x, ‖(x : ℂ) ^ ρ i / ρ i‖ ≤ √x * (1 / |(ρ i).im|) := by
    intro i hi
    have him : (ρ i).im ≠ 0 := by
      have := (hs x hx i hi).1
      intro h0; rw [h0] at this; simp at this; linarith
    have := (RH.norm_cpow_div_nontrivialZero (hρ i) (htriv i) (h1 i) hx0).2.2 him
    rw [mul_one_div]; exact this
  have hsum : ∑ i ∈ s x, ‖(x : ℂ) ^ ρ i / ρ i‖ ≤ A * (√x * (log x) ^ 2) := by
    calc ∑ i ∈ s x, ‖(x : ℂ) ^ ρ i / ρ i‖ ≤ ∑ i ∈ s x, √x * (1 / |(ρ i).im|) :=
          Finset.sum_le_sum hterm
      _ = √x * ∑ i ∈ s x, 1 / |(ρ i).im| := by rw [← Finset.mul_sum]
      _ ≤ A * (√x * (log x) ^ 2) :=
          sqrt_mul_sum_inv_abs_le (s x) (fun i => (ρ i).im) hA hx (hs x hx) (hcount x hx)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hpos]
  linarith [hexp x hx]

@[blueprint
  "rh-window-count-of-rvm"
  (title := "Unit-window zero count from a Riemann--von Mangoldt estimate")
  (statement := /-- If $|N(T)-\frac{T}{2\pi}\log\frac{T}{2\pi e}-\frac78| \le b_1\log T+b_2\log\log T+b_3$
  for all $T\ge2$ with $b_1,b_2,b_3\ge0$, then for all $T\ge2$
  \[ N(T+1)-N(T) \le A\log(T+2),\qquad A = 1+2b_1+2b_2+2b_3/\log 2. \] -/)
  (proof := /-- Subtract the two estimates. The main terms differ by at most
  $\frac1{2\pi}\log\frac{T+1}{2\pi}$ since $\log(1+1/T)\le1/T$, and each error term is at most
  $(b_1+b_2)\log(T+2)+b_3$. -/)
  (uses := ["Riemann-von-Mangoldt-estimate"])
  (latexEnv := "lemma")]
lemma riemannZeta.N_add_one_sub_N_le {b₁ b₂ b₃ : ℝ} (h1 : 0 ≤ b₁) (h2 : 0 ≤ b₂) (h3 : 0 ≤ b₃)
    (hR : riemannZeta.Riemann_vonMangoldt_bound b₁ b₂ b₃) {T : ℝ} (hT : 2 ≤ T) :
    riemannZeta.N (T + 1) - riemannZeta.N T ≤
      (1 + 2 * b₁ + 2 * b₂ + 2 * b₃ / log 2) * log (T + 2) := by
  have hT0 : 0 < T := by linarith
  have hπ : 1 < 2 * π := by linarith [Real.pi_gt_three]
  have hπ0 : 0 < 2 * π := by linarith
  set L := log (T + 2) with hL
  have hL2 : log 2 ≤ L := Real.log_le_log (by norm_num) (by linarith)
  have hlog2 : 0 < log 2 := Real.log_pos (by norm_num)
  have hLpos : 0 ≤ L := by linarith
  have hlogT : log T ≤ L := Real.log_le_log hT0 (by linarith)
  have hlogT1 : log (T + 1) ≤ L := Real.log_le_log (by linarith) (by linarith)
  have hlogT_nonneg : 0 ≤ log T := Real.log_nonneg (by linarith)
  have hlogT1_nonneg : 0 ≤ log (T + 1) := Real.log_nonneg (by linarith)
  have hll : log (log T) ≤ L :=
    (Real.log_le_self hlogT_nonneg).trans hlogT
  have hll1 : log (log (T + 1)) ≤ L :=
    (Real.log_le_self hlogT1_nonneg).trans hlogT1
  have hb3 : b₃ ≤ b₃ / log 2 * L := by
    calc b₃ = b₃ / log 2 * log 2 := by field_simp
      _ ≤ b₃ / log 2 * L := mul_le_mul_of_nonneg_left hL2 (by positivity)
  have e1 := hR (T + 1) (by linarith)
  have e0 := hR T hT
  unfold riemannZeta.RvM at e1 e0
  have hmain : (T + 1) / (2 * π) * log ((T + 1) / (2 * π)) - T / (2 * π) * log (T / (2 * π))
      - 1 / (2 * π) ≤ 1 / (2 * π) * log (T + 1) := by
    have hdiff : log ((T + 1) / (2 * π)) - log (T / (2 * π)) ≤ 1 / T := by
      rw [← Real.log_div (by positivity) (by positivity)]
      have := Real.log_le_sub_one_of_pos (show 0 < (T + 1) / (2 * π) / (T / (2 * π)) by positivity)
      have heq : (T + 1) / (2 * π) / (T / (2 * π)) = 1 + 1 / T := by field_simp
      rw [heq] at this ⊢; linarith
    have ha : log ((T + 1) / (2 * π)) ≤ log (T + 1) :=
      Real.log_le_log (by positivity) (by rw [div_le_iff₀ hπ0]; nlinarith)
    have key : (T + 1) * log ((T + 1) / (2 * π)) - T * log (T / (2 * π)) ≤
        log ((T + 1) / (2 * π)) + 1 := by
      have := mul_le_mul_of_nonneg_left hdiff hT0.le
      rw [mul_one_div_cancel hT0.ne'] at this
      nlinarith
    have : (T + 1) / (2 * π) * log ((T + 1) / (2 * π)) - T / (2 * π) * log (T / (2 * π))
        - 1 / (2 * π) = ((T + 1) * log ((T + 1) / (2 * π)) - T * log (T / (2 * π)) - 1) / (2 * π) := by
      field_simp
    rw [this, div_le_iff₀ hπ0]
    have : 1 / (2 * π) * log (T + 1) * (2 * π) = log (T + 1) := by field_simp
    linarith
  have hπinv : 1 / (2 * π) ≤ 1 := by rw [div_le_one hπ0]; exact hπ.le
  have hA : 1 / (2 * π) * log (T + 1) ≤ L := by
    calc 1 / (2 * π) * log (T + 1) ≤ 1 * log (T + 1) :=
          mul_le_mul_of_nonneg_right hπinv hlogT1_nonneg
      _ ≤ L := by linarith
  have hb1 : b₁ * log (T + 1) ≤ b₁ * L := mul_le_mul_of_nonneg_left hlogT1 h1
  have hb1' : b₁ * log T ≤ b₁ * L := mul_le_mul_of_nonneg_left hlogT h1
  have hb2 : b₂ * log (log (T + 1)) ≤ b₂ * L := mul_le_mul_of_nonneg_left hll1 h2
  have hb2' : b₂ * log (log T) ≤ b₂ * L := mul_le_mul_of_nonneg_left hll h2
  have habs1 := (abs_le.mp e1).2
  have habs0 := (abs_le.mp e0).1
  have hexpand : (1 + 2 * b₁ + 2 * b₂ + 2 * b₃ / log 2) * L =
      L + 2 * (b₁ * L) + 2 * (b₂ * L) + 2 * (b₃ / log 2 * L) := by ring
  have hid : (T + 1) / (2 * π) = T / (2 * π) + 1 / (2 * π) := by ring
  rw [hexpand]
  linarith
