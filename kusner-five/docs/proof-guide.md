# Proof guide

The distance throughout the development is

$$
d_1(x,y)=\sum_{k=1}^{5}|x_k-y_k|.
$$

The main contradiction starts with eleven arbitrary real points and the 55 pairwise unit-distance equations. Equal coordinate values, zero coordinate gaps, and constant coordinates are retained. All reductions used by the final theorem are proved from these equations.

## Mathematical structure

1. Sort each physical coordinate and express its scalar distance matrix as a nonnegative sum of cut matrices. Centering gives exact trace and energy identities on the same eleven labels.
2. A coordinate range greater than one half determines a unique pair of extreme labels. These extreme pairs form a forest. Median and overlap arguments bound every range by five sixths; profile estimates force at least four wide coordinates and at least two isolated edges.
3. Five possible forest patterns remain. Exact profile inequalities exclude four patterns, including the path with three isolated edges.
4. For any four original points, prove that their total coordinate width is at least `37/24`. The proof uses the same seven outsiders, signed overlap equations, projections with their full displacement accounted for, and perimeter bounds in the original five physical coordinates.
5. Apply that quartet inequality to the five-edge matching. The resulting deficit inequality and an exact positive arithmetic margin, `33541/10560000`, contradict the energy identity.
6. Normalize any positive common distance, lift the eleven-point obstruction to arbitrary sets, and construct the ten points `±e_k/2`.

The manuscript gives the complete mathematical argument. The source modules below implement its steps.

## Source organization

| Module | Role |
| --- | --- |
| `Kusner5/Basic.lean` | Real points, the literal Manhattan distance, equilateral configurations, and normalization |
| `Kusner5/Orders.lean` | Actual coordinate orders, gaps, and scalar cuts |
| `Kusner5/CutEnergy.lean` | Cut decomposition, trace identities, and exact energy equations |
| `Kusner5/Profiles.lean` | Root profiles, shifted profiles, and their arithmetic estimates |
| `Kusner5/RangeGeometry.lean` | Medians, wide-coordinate geometry, and the range bound |
| `Kusner5/ForestMatching.lean` | Forest structure, exhaustive patterns, and two exclusions |
| `Kusner5/Exclusions.lean` | Original-equation bridges for the forest exclusions |
| `Kusner5/FourMatchingAssembly.lean` | Exclusion of the four-edge matching |
| `Kusner5/PathAssembly.lean` | Exclusion of the five-edge pattern with three isolated edges |
| `Kusner5/Quartet.lean` | Quartet cut totals and overlap equations |
| `Kusner5/QuartetOutsiders.lean` | Relations between the quartet and its seven original outsiders |
| `Kusner5/QuartetProjection.lean` | Exact projection and displacement estimates |
| `Kusner5/QuartetFaceProjection.lean` | Projection to faces, including boundary cases |
| `Kusner5/QuartetPhysicalSlots.lean` | Classification using the five physical coordinate slots |
| `Kusner5/QuartetPerimeter.lean` | Plane-section perimeter geometry |
| `Kusner5/QuartetDoublePerimeter.lean` | The two-double-slot perimeter case |
| `Kusner5/QuartetBoundary.lean` | Boundary tours and the seven-cycle comparison |
| `Kusner5/QuartetLowerBound.lean` | The original quartet width bound `37/24` |
| `Kusner5/MatchingArithmetic.lean` | Exact radical and rational inequalities |
| `Kusner5/MatchingAssembly.lean` | Matching energy bound and final contradiction |
| `Kusner5/Cardinality.lean` | Cardinality lifting to finite and arbitrary sets |
| `Kusner5/LowerWitness.lean` | The explicit ten-point construction |
| `Kusner5/Main.lean` | Assembly and the final public statements |
| `Kusner5/Audit.lean` | Literal type checks and transitive axiom inspection |

## Public statements

`Kusner5.no_eleven_unit_explicit` states directly that no function
`Fin 11 → Fin 5 → ℝ` satisfies the literal sum-of-absolute-values equation for every distinct pair of labels.

`Kusner5.equilateral_set_finite_card_le_ten` quantifies over an arbitrary set and a positive real common distance. Its conclusion supplies finiteness and the bound ten.

`Kusner5.exists_equilateral_ten` supplies a finite set of cardinality ten with common distance one.

`Kusner5.kusner_five_exact` combines the arbitrary-set upper bound and the explicit lower witness. The exact source type is in `Kusner5/Main.lean`; it has no unproved structural hypothesis.
