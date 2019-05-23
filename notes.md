A history independent description of the beach line
=======
The Fortune algorithm (FA) works by constructing progressively the beach
line at each event.  We need to have an alternative definition of the
beach line to write lemmas expressing that the beach line computed by
the FA is correct.

The purpose of this section is to experiment with yet another
definition of the beach line, which introduces directly an ordered
sequence of arcs, and is independent of the history of the FA.

Prerequisite: define the parabola function:

For a given position y<sub>s</sub> of the sweep line and given site
p define the function par(y<sub>s</sub>, p, x), such that (x, par(y<sub>s</sub>, p, x))
is equidistant from the sweep line and p.  I don't bother writing the definition of par here, it is already in `fortune.v`, as part of the function `vertical_intersection.`

We can already define the beach function as the maximum of all parabola functions.

Show the existence of two sequences s = {s<sub>0</sub>, s<sub>1</sub>, ..., s<sub>n</sub>} (focal points, or sites)
and m = {m<sub>0</sub>, m<sub>1</sub>, ..., m<sub>n-1</sub>}
(meet points between successive arcs) such that:

    forall i, i <= n -> s_i \in {p_i | p_i_x < y_s}

    forall i, i < n -> m_i < m_{i+1}

    forall i, i < n - 1 -> forall x, m_i <= x <= m_{i+1} ->
     bf(x) = par(y_s, s_{i + 1}, x)

    forall x, x <= m_0 -> bf(x) = par(y_s, s_0, x)

    forall x, m_{n-1} <= x -> bf (x) = par(y_s, s_n, x)

Base case. If there is no site, nothing to do, the beach line is
empty.

If there is a single site, the beach line consists of a single arc
whose focal point is this site.

For a set of sites {p<sub>i</sub> | i < n'} with 2 < n', consider the
predicate top-meet
 (i, j) => bf(pick-sol(y<sub>s</sub>, i, j) = par(y<sub>s</sub>, p<sub>i</sub>, pick_sol(y<sub>s</sub>, i, j))

Filter the sequence {(i, j) | i &lt; n, j &lt; n, i != j} by the predicate `top-meet` and order this sequence.  The result is the sequence m.  Now to determine the sequence s, you only need to look at the value of bf at the mid-points between all the m<sub>i</sub> and m<sub>i+1</sub> and, if we name x one such mid-point, we only need to find one k, such that

  bf(x)=par(y<sub>s</sub>, p<sub>k</sub>, x)

As a last step, I wish you to prove that for every i if x an y are between
m<sub>i</sub> and m<sub>i+1</sub> then b(x)= par(y<sub>s</sub>, p<sub>i+1</sub>, x)
***Proof.***
Without loss of generality assume (m<sub>i</sub> + m<sub>i+1</sub>)/2 < x (in what follows we write a = (m<sub>i</sub> + m<sub>i+1</sub>)/2).
Take the set {(i,j) | a < pick_sol(y<sub>s</sub>, i, j) < x}  This set is finite.  Let k be such that bf(a) = par(y<sub>s</sub>, p<sub>k</sub>, a), if there are two such k, then the hypothesis that there is no break meets of parabolas on the beach line between m<sub>i</sub> m<sub>i+1</sub> and is violated.  So k is unique.
Now, assume that for x with bf(x) = par(y<sub>s</sub>, p<sub>k'</sub>, x) with k != k'.  In that case, the function g defined as
g(t) = par(y<sub>s</sub>, p<sub>k'</sub>, t) - par(y<sub>s</sub>, p<sub>k</sub>, t) is positive in x and negative in a, so by poly-ivt, it must have a root between a and x.
call x<sub>1</sub> this root.  At this root, the two parabolas for p<sub>k</sub> p<sub>k'</sub> meet.  so x<sub>1</sub>=pick-sol(y<sub>s</sub>, k, k') or x<sub>1</sub>=pick-sol(y<sub>s</sub>, k', k).   By construction of m<sub>i</sub> and m<sub>i+1</sub> we have par(y<sub>s</sub>, p<sub>k</sub>, x<sub>1</sub>) != bf(x<sub>1</sub>), so there must be a value k<sub>1</sub> such that bf(x<sub>1</sub>) = k<sub>1</sub>.  Reproducing this argument, there should be an infinity of (i,j) such that pick(y<sub>s</sub>, i, j) is between a and x.  ***Qed***

How to draw parabolas using Bezier curves
=====
This part has not been verified.

Input: y<sub>s</sub> second coordinate of the (horizontal) directrix,
x<sub>0</sub>, y<sub>0</sub> coordinates of the focal point.

y = (x - x<sub>0</sub>) <sup>2</sup> / (2 * (y<sub>s</sub> - y<sub>0</sub>)) + (y<sub>s</sub> + y<sub>0</sub>)
/ 2

(y - y_s) ^ 2 =  (x - x_0) ^ 2 + (y - y_0) ^ 2
 -  2 * y * y_s + y_s ^ 2 = (x - x_0) ^ 2 - 2 y * y_0 + y_0 ^ 2
    2 * (y * (y_0 - y_s)) ^ 2 = (x - x_0) ^ 2 + y_0 ^ 2 - y_s ^ 2
	     y = (x - x_0) ^ 2/ (2 * (y_0 - y_s)) + (y_0 + y_s) / 2
		 y' = (x - x_0)/(y_0 - y_s)
