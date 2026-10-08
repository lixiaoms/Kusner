# Kusner's Conjecture in $\ell_1^5$

**Xiao Li**

This repository contains a complete mathematical manuscript and its Lean formalization of

$$
e(\ell_1^5)=10.
$$

Every equilateral subset of $\mathbb R^5$ for the distance
$\sum_{k=1}^5 |x_k-y_k|$ is finite and has at most ten elements, for any positive common distance. The ten points $\{\pm e_k/2:1\leq k\leq5\}$ attain the bound at distance one. The theorem imposes no integrality, general-position, coordinate-value, or a priori finiteness assumption.

## Contents

- [Manuscript (PDF)](paper/main.pdf)
- [Manuscript (LaTeX)](paper/main.tex) and [bibliography](paper/references.bib)
- [Final theorem](Kusner5/Main.lean) and [type and axiom audit](Kusner5/Audit.lean)
- [Proof guide](docs/proof-guide.md)
- [Verification record](docs/verification.md)
- [File checksums](SHA256SUMS)

## Check the formal proof

Install Lean through [elan](https://github.com/leanprover/elan), and run the following commands from the repository root:

```sh
lake update
lake exe cache get
lake build
python3 scripts/check_axioms.py
```

The toolchain is pinned in `lean-toolchain`, and all dependency revisions are pinned in `lake-manifest.json`. The `cache get` command obtains precompiled dependency artifacts; the project proofs are compiled from the supplied source. An ordinary dependency source build is also possible without this cache command.

The public declarations include:

```lean
Kusner5.no_eleven_unit_explicit
Kusner5.equilateral_set_finite_card_le_ten
Kusner5.exists_equilateral_ten
Kusner5.kusner_five_exact
```

`Kusner5/Audit.lean` also checks literal expanded types and prints the transitive axiom dependencies of 48 selected declarations. The audit script requires that each printed dependency belongs to `propext`, `Classical.choice`, or `Quot.sound`.

## Compile the paper

With a LaTeX distribution that provides `latexmk`, run:

```sh
cd paper
latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
```

Alternatively, [Tectonic](https://tectonic-typesetting.github.io/) compiles the manuscript and bibliography with:

```sh
cd paper
tectonic main.tex
```

The included PDF is generated from the included manuscript source.

## Check this distribution

```sh
python3 scripts/check_release.py
```

This compares all distribution files against `SHA256SUMS`. Generated build artifacts are excluded from the distribution.

For citation metadata, see [CITATION.cff](CITATION.cff). The manuscript is a preprint.
