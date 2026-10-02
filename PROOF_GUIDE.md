# Proof organization and correspondence with the article

The proof uses the original real Manhattan distance throughout. It passes from
finite sets to arbitrary nonempty sets only after proving the finite
enclosing-radius assertion.

## Common contact reduction

Basic.lean defines the explicit sum of absolute coordinate differences.
ContactGeometry.lean proves the existence of a minimizing center and shows
that zero belongs to the convex hull of its active norming signs: a separating
functional would otherwise give a strict descent direction.
ContactExtraction.lean extracts at most d+1 active terms. Zero weights fill
unused indices. ContactAlgebra.lean proves the weight bound and the lower
bound for the sum of contact distances from any center.

In dimension 2p-1, a radius above (2p-3)/(2p-2) makes every weight less than
1/(2p-2). Each sign class has total weight 1/2, so each must contain at least
p indices. There are at most 2p indices; hence both classes have exactly p.
This gives unweighted sign balance without assuming equal convex weights.
The general proof is in Jung/ContactCounting.lean.

## General cut estimate for k >= 2

Set p = 2k+1. Then p is odd and p >= 5. Jung/Cut.lean proves the indexed cut
estimate using a balanced index C of maximum weight. With balanced total
weight W and at most 2p-1 positive balanced indices,

~~~text
W <= (2p-1) * w_C
Q_C >= W + (p^2-1) * w_C >= c_p * W
Q_C <= 2p^2 - T,
where c_p = 1 + (p^2-1)/(2p-1).
~~~

The oddness of p makes the squared sign sum of every balanced shore at least
one. The chosen index contributes p^2. These estimates yield

~~~text
Phi <= B_p = p^3(2p-1)/(p^3+p-1).
~~~

CutAlgebra.lean proves that B_p is strictly less than
2p(2p-3)/(2p-2) for p >= 5. The article uses this same maximum-weight
argument.

## Coordinate gaps and the median contradiction

Gap.lean proves the ordered-coordinate telescoping identities. GapBridge.lean
keeps a separate cut index for each coordinate and gap position. Repeated cuts
are allowed. Only the middle gap in a coordinate is balanced, so there are at
most d positive balanced indices. The cut distance equals every original
point distance, and the objective equals the sum of distances to a coordinate
median. The implementation chooses the lower median; the article proves the
same identity for every median in the central interval.

Finite.lean combines the contact lower bound with the cut/median upper bound
to obtain a contradiction above the claimed enclosing radius.

## Five-dimensional case

The general quadratic estimate is insufficient when p = 3. Jung5/ instead
proves the sharper six-label bound 9/2. Equal unordered cuts are combined.
Among the ten balanced cuts, at most five have positive weight.

CertificateData.lean provides nonnegative integer pair weights in units of
1/60. Certificates.lean checks all 638 balanced supports of cardinality at
most five by kernel reduction. For each support, the total coefficient is at
most 270, and every relevant cut has capacity at least 60 times its smaller
shore size. Dividing by 60 proves the objective bound 9/2 from the original
pairwise upper bounds.

The article presents the same capacity inequality with three support
representatives and three explicit rational certificates. Those three
certificates also occur in the exact Lean witness data. The support graph
classification is an analytic presentation in the article; it is not a
separate Lean theorem. Lean verifies the complete finite capacity statement
without needing that classification.

The six-contact lower bound would exceed 9/2 if R > 3/4. The median upper
bound rules this out. Sharpness.lean verifies the four quarter-scaled points
with first three sign coordinates

~~~text
( 1,  1,  1), ( 1, -1, -1), (-1,  1, -1), (-1, -1,  1),
~~~

and last two coordinates zero. Every distinct pair has distance one. Their
distance from zero is 3/4, and their total distance from any ambient center is
at least three.

## Arbitrary sets and the unified statement

Extension.lean scales the finite diameter-one result, handles D = 0, and
uses the finite-intersection property inside a compact ball to find a common
center for arbitrary nonempty sets. Jung/Main.lean combines k = 1 from Jung5
with the general k >= 2 result.

Audit.lean prints the public theorem types and the transitive axioms of all
151 audited declarations. It introduces no extra mathematical theorem or
assumption.
