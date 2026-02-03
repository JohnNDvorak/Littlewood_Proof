# Aristotle Prompts for Remaining Sorries

Updated 2026-02-02. The 8 active Aristotle/CoreLemma sorries across 5 files.

---

## PROMPT 1: HardyApproxFunctionalEq (1 sorry) -- CRITICAL PATH

**File:** `Littlewood/Aristotle/HardyApproxFunctionalEq.lean`
**Topic:** Approximate functional equation for the Hardy Z function

```
Prove approx_functional_eq in Lean 4 with Mathlib.

The theorem states: there exist positive constants k, C such that for large T:
  integral_1^T Z(t)^2 dt >= k * integral_1^T |S_N(t)|^2 dt - C * T

where Z(t) is the Hardy Z-function and S_N(t) = sum_{n<=N} n^{-1/2-it}.

This is the approximate functional equation link between the mean square of
zeta on the critical line and the mean square of its partial Dirichlet series.

Mathematical reference: Titchmarsh, Theory of the Riemann Zeta-Function,
Chapter 7 (approximate functional equation).
```

---

## PROMPT 2: PhragmenLindelof -- critical line bound (1 sorry)

**File:** `Littlewood/Aristotle/PhragmenLindelof.lean`
**Line:** ~153
**Topic:** |zeta(1/2+it)| <= C|t|^{1/4+epsilon}

```
Prove the critical line zeta bound in Lean 4 with Mathlib.

For every epsilon > 0, there exists C > 0 such that for |t| >= 1:
  |zeta(1/2 + it)| <= C * |t|^{1/4 + epsilon}

This follows from:
1. |zeta(sigma + it)| = O(1) for sigma > 1 (Dirichlet series bound)
2. Functional equation: zeta(s) = chi(s) * zeta(1-s)
3. Stirling's formula for chi(s) gives growth rate
4. Phragmen-Lindelof interpolation between sigma=0 and sigma=1

The Stirling/chi factor gives exponent (1-sigma)/2 at sigma = 1/2,
yielding the 1/4 exponent.
```

---

## PROMPT 3: PhragmenLindelof -- convexity bound (1 sorry)

**File:** `Littlewood/Aristotle/PhragmenLindelof.lean`
**Line:** ~167
**Topic:** |zeta(sigma+it)| <= C|t|^{mu(sigma)+epsilon} for 0 <= sigma <= 1

```
Prove zeta_convexity_bound in Lean 4 with Mathlib.

For 0 <= sigma <= 1, epsilon > 0, there exists C > 0 such that for |t| >= 1:
  |zeta(sigma + it)| <= C * |t|^{(1-sigma)/2 + epsilon}

This is the general convexity bound from the Phragmen-Lindelof principle,
interpolating between sigma = 1 (where zeta is O(1)) and sigma = 0
(where zeta is O(|t|^{1/2}) via the functional equation).
```

---

## PROMPT 4: PhragmenLindelof -- Gamma growth (1 sorry)

**File:** `Littlewood/Aristotle/PhragmenLindelof.lean`
**Line:** ~177
**Topic:** Stirling's approximation for |Gamma(sigma+it)|

```
Prove gamma_growth in Lean 4 with Mathlib.

For sigma > 0, there exist C1, C2 > 0 such that for |t| >= 1:
  C1 * |t|^{sigma-1/2} * exp(-pi*|t|/2)
    <= |Gamma(sigma + it)|
    <= C2 * |t|^{sigma-1/2} * exp(-pi*|t|/2)

This is Stirling's approximation for the Gamma function in vertical strips.
Mathlib has Complex.Gamma and some basic properties. The key challenge is
establishing the asymptotic expansion.

Reference: Titchmarsh, Theory of the Riemann Zeta-Function, Chapter 4.
```

---

## PROMPT 5: ZeroCounting -- N(T) argument principle (1 sorry)

**File:** `Littlewood/Aristotle/ZeroCounting.lean`
**Line:** ~120
**Topic:** N(T) via argument of xi

```
Prove zetaZeroCount_via_argument in Lean 4 with Mathlib.

The theorem: for T > 0, there exists S with |S| <= log T such that
  N(T) = (1/pi) * arg(xi(1/2 + Ti)) + 1 + S

where xi is the completed zeta function and N(T) counts zeros with 0 < Im < T.

This requires the argument principle applied to xi in a rectangle.
```

---

## PROMPT 6: ZeroCounting -- N(T) asymptotic (1 sorry)

**File:** `Littlewood/Aristotle/ZeroCounting.lean`
**Line:** ~132
**Topic:** Riemann-von Mangoldt asymptotic

```
Prove zetaZeroCount_asymp in Lean 4 with Mathlib.

The theorem: N(T) - (T/2pi) * log T = O(log T)

This is the Riemann-von Mangoldt formula. It follows from PROMPT 6
combined with Stirling's approximation for the Gamma function
(which gives the main term of arg(xi)).
```

---

## PROMPT 7: PartialSummation (1 sorry)

**File:** `Littlewood/Aristotle/PartialSummation.lean`
**Line:** ~238
**Topic:** psi oscillation implies pi-li oscillation

```
Prove psi_oscillation_implies_pi_li_oscillation in Lean 4 with Mathlib.

Given:
- h_psi_pos: for all M, exists x > M with psi(x) - x > 0
- h_psi_neg: for all M, exists x > M with psi(x) - x < 0

Prove: same sign-change property for pi(x) - li(x).

The decomposition is already proved (pi_sub_li_decomposition):
  pi(x) - li(x) = (psi(x) - x)/log(x) - T(x) + integral_2^x ... + 2/log(2)

The key is showing that when psi(x) - x is positive/negative with sufficient
magnitude (which follows from psi(x) - x > 0 at arbitrarily large x),
the main term (psi(x)-x)/log(x) dominates the error terms T(x) and the
integral for sufficiently large x.

Error bound needed: T(x) = O(sqrt(x)/log(x)) and the integral term
is O(sqrt(x)/log(x)^2), both dominated by the main term when
psi(x) - x = Omega(sqrt(x)).
```

---

## PROMPT 8: LandauLemma (1 sorry)

**File:** `Littlewood/CoreLemmas/LandauLemma.lean`
**Line:** ~395
**Topic:** Identity theorem for von Mangoldt L-series

```
Prove zeta_zero_implies_vonMangoldt_singularity in Lean 4 with Mathlib.

Given:
- rho with zeta(rho) = 0, 0 < Re(rho) < 1
- hpole: NOT AnalyticAt (-zeta'/zeta) at rho (from ZetaLogDerivPoleHyp)
- hanalytic: AnalyticAt (LSeries vonMangoldt) at rho (to be contradicted)

Derive: False

The argument: LSeries(vonMangoldt, s) = -zeta'(s)/zeta(s) for Re(s) > 1.
Both are analytic on {Re(s) > 1}. If LSeries were analytic at rho, by the
identity theorem (Mathlib: AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq),
it would provide an analytic extension of -zeta'/zeta to a neighborhood of rho,
contradicting the pole.

Main challenge: establishing LSeries(vonMangoldt, s) = -zeta'(s)/zeta(s) for
Re(s) > 1 in Lean. This is the von Mangoldt identity (logarithmic derivative
of the Euler product).
```
