A history independent description of the beach line
=======
The Fortune algorithm (FA) works by constructing progressively the beach
line at each event.  We need to have an alternative definition of the
beach line to write lemmas expressing that the beach line computed by
the FA is correct.  In the week between 1st and 8th May, 2019, we
experimented on the white board with defining the beach line
point-wise, but this quite unsatisfactory for two reasons.

  1. the point-wise definition does not introduce the parabola arcs and
    the continuity conditions that come with it.

  2. It is quite difficult to verify express the properties of the
     points that are equidistant to two or more points.

The purpose of this section is to experiment withf yet another
definition of the beach line, which introduces directly an ordered
sequence of arcs, and is independent of the history of the FA.

Prerequisite: define the parabola function:

For a given position `y<sub>s</sub>` of the sweepline and given site
`p` define the function par(y<sub>s</sub>, p, x), such that (x, par(y<sub>s</sub>, p, x))
is equidistant from the sweepline and p.  I don't bother writing the
definition of par here, it is already in you code, as part of the
function `vertical_intersection.`

A lemma can be useful: when two parabolas meet, they cross.  In other
words:  if  par(x_0, y_s, p, x) = 
Base case. If there is no site, nothing to do, the beach line is
empty.

If there is a single site, the beach line consists of a single arc
whose focal point is this site.

For a set of sites {p<sub>i</sub> | i < n} with 2 < n, consider the value
v = max{`pick_sol`(p<sub>i</sub>, p<sub>j</sub>) with i <> j}.  This
is the maximum of a finite set of numbers.
This finite set is non-empty because there are at
least two sites.  Let I and J be the two indices such that
`pick_sol`(p<sub>I</sub>, p<sub>J</sub>) = v.  Then for all x, v < x, we should be able to
prove that par(Y, p<sub>J</sub>, x) = max{par(Y, p<sub>i</sub>, x) | i < n}
Actually, we should be able to prove that p<sub>J</sub> is one of the points
with the minimal p<sub>y</sub>.  

Recursive case.

How to draw parabolas using Bezier curves
=====
Input: y<sub>s</sub> second coordinate of the (horizontal) directrix,
x<sub>0</sub>, y<sub>0</sub> coordinates of the focal point.

y = (x - x<sub>0</sub>) <sup>2</sup> / (2 * (y<sub>s</sub> - y<sub>0</sub>)) + (y<sub>s</sub> + y<sub>0</sub>)
/ 2

(y - y_s) ^ 2 =  (x - x_0) ^ 2 + (y - y_0) ^ 2
 -  2 * y * y_s + y_s ^ 2 = (x - x_0) ^ 2 - 2 y * y_0 + y_0 ^ 2
    2 * (y * (y_0 - y_s)) ^ 2 = (x - x_0) ^ 2 + y_0 ^ 2 - y_s ^ 2
	     y = (x - x_0) ^ 2/ (2 * (y_0 - y_s)) + (y_0 + y_s) / 2
		 y' = (x - x_0)/(y_0 - y_s)
