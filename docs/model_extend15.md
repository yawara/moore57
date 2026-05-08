# The 14-to-15 block extension model

Let the current 14-block local cover have fibers

\[
S=\{0,1,\dots,13\}
\]

with sheet set \(X=\{0,\dots,55\}\). We append a new fiber \(\nu=14\). The new fiber is fixed to the four anchor fibers \(0,1,2,3\) by the star-factor certificate. The unknown permutations are

\[
R_i=P_{\nu i}\in S_{56}, \qquad i=4,\dots,13.
\]

The Boolean variable is

\[
x_{i,a,b}=1 \iff R_i(a)=b.
\]

## Constraints

### Permutation constraints

For each unknown permutation \(R_i\),

\[
\sum_b x_{i,a,b}=1,\qquad \sum_a x_{i,a,b}=1.
\]

### Unary forbidden cells

The cell \(R_i(a)=b\) is forbidden if an already-fixed path of length 2 or 3 from \(\nu\) to \(i\) maps \(a\) to \(b\). Adding the direct edge would close a triangle or square.

### Binary same-row nogoods

For two unknown fibers \(i,j\), values

\[
R_i(a)=b,\qquad R_j(a)=c
\]

are incompatible if a fixed path of length 1 or 2 from \(i\) to \(j\) maps \(b\) to \(c\). Adding both new edges would close a triangle or square through \(\nu\).

CNF clauses have the form

\[
\lnot x_{i,a,b}\lor \lnot x_{j,a,c}.
\]

## Interpretation

A satisfying assignment gives a 15-fiber local cover satisfying all triangle and square voltage derangement constraints. It is a necessary local condition for a degree-57 Moore graph, not a sufficient condition for the full graph.
