# Verification record

Date: 8 October 2026.

## Statement checked

The final declaration is `Kusner5.kusner_five_exact` in `Kusner5/Main.lean`. Its upper clause ranges over every set of real five-coordinate points and every positive real common distance. It returns both finiteness and cardinality at most ten. Its lower clause gives a finite ten-point set at distance one.

The unit-distance exclusion also has a literal expanded statement, `Kusner5.no_eleven_unit_explicit`:

```lean
theorem no_eleven_unit_explicit (x : Fin 11 → Fin 5 → ℝ) :
    ¬ (∀ i j : Fin 11, i ≠ j →
      (∑ k : Fin 5, |x i k - x j k|) = 1)
```

There is no auxiliary structural assumption in either public conclusion. The quartet width inequality, the forest classification, and every other bridge used in the final assembly are proved within the development.

## Pinned dependencies

| Component | Version or revision |
| --- | --- |
| Lean | `4.34.0` |
| Lean revision | `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b` |
| Lake | `5.0.0-src+293d5d0` |
| mathlib | `5ed2965256430c3649e86755f9576b54eca72435` |

`lean-toolchain`, `lakefile.toml`, and `lake-manifest.json` provide the build configuration. The manifest records the exact mathlib revision and the eight transitive package revisions.

## Completed checks

- The complete project was built successfully with `lake --no-ansi --no-cache build`. All 24 proof and audit modules, together with the top-level `Kusner5.lean` import, produced Lean artifacts.
- The project sources were compiled into a fresh project build directory. Pinned precompiled dependency artifacts were reused. This record does not assert a source rebuild of all dependency libraries.
- A subsequent `lake --no-build build` check succeeded.
- `python3 scripts/check_axioms.py` succeeded and checked all 48 declarations listed in `Kusner5/Audit.lean`.
- Four explicit type assignments in the audit were compiled, covering the literal eleven-point obstruction, the finite-set upper bound, the arbitrary-set upper bound, and the ten-point witness.
- Every printed transitive axiom dependency belongs to `propext`, `Classical.choice`, or `Quot.sound`. Universe annotations in printed names are canonicalized before comparison. The check does not allow `sorryAx`, `Lean.ofReduceBool`, or an additional mathematical axiom.
- The proof sources contain no admitted proof or new mathematical axiom.

The [canonical axiom audit output](axiom-audit.txt) records each audited declaration. [verification.json](verification.json) records the source hashes and the corresponding check outcomes. [SHA256SUMS](../SHA256SUMS) covers the files in this distribution.

## Manuscript checks

The complete manuscript was reviewed against the unrestricted theorem and the formal declaration interfaces. The review covered every forest branch, the shared-vertex path estimate, the original quartet equations, the projections and physical perimeter degeneracies, and the exact closing arithmetic. A subsequent comparison confirmed that the final layout repairs preserved the mathematical content.

The abstract was subsequently shortened, and the detailed proof outline was moved to Section 1. The mathematical proof body and all Lean sources are unchanged. This editorial revision was checked independently.

The supplied LaTeX source and bibliography compiled successfully with Tectonic `0.17.0`. The final log contains no overfull or underfull boxes, undefined references, or missing-character diagnostics. All 23 PDF pages were rendered and visually inspected. The PDF retains only its title and author in its document-information metadata; its page text was checked unchanged by that metadata cleanup.

## Reproduction

Run the commands in the repository [README](../README.md). To inspect the full expanded types and transitive dependencies directly, run:

```sh
lake env lean Kusner5/Audit.lean
```

The trust boundary is the Lean kernel, the standard foundations listed above, and the declared Lean and mathlib dependencies. The accompanying article is a mathematical manuscript; its formal correspondence table identifies the declarations implementing its principal steps.
