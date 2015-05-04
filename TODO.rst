
SAT encoding
------------

See the paper.


SMT Encoding 1: same as the SAT encoding
----------------------------------------

* Associate every event e and condition b with an integer variable
  x_e and x_b

* equivalence ::
  nothing to do :)

* subset (X, Y) ::
  AND_{x in X} ( OR_{y in Y} (x_x = x_y ) )

* labelling ::
  for every two events e, e' with different label:
  x_e != x_e'

* pre ::
  for every two events (with equal label!)
  (x_e == x_e') implies
  subset (pre e, pre e') and
  subset (pre e', pre e)

* post ::
  as for pre

* co ::
  for every two concurrent conditions b, b'
  x_b != x_b'

* bound(k) ::
  for all events e,
  x_e <= k

SMT Encoding 2: using labels
--------------------------

* associate every event e with an integer variable x_e
* associate every condition b with an integer variable x_b
* associate every label a with an integer variable x_a

let ``h : E -> A`` be the labelling of events with actions
let ``h': A -> 2^E`` be the inverse function

* subset (X, Y, v) ::
  v => AND_{x in X} ( OR_{y in Y} (x_x = x_y ) )

* equivalence ::
  nothing to do :)

* labelling ::
  nothing to do :) !!!

* pre ::
  for every two events with equal label:
  (x_e == x_e') implies
  subset (pre e, pre e', true) and
  subset (pre e', pre e, true)

* post ::
  analogous to pre

* co ::
  for every two concurrent conditions b, b'
  if there exists some label a such that
    (
      h' (a) \cap post(b) != empty
      and
      h' (a) \cap post(b') != empty)
    )
    or
    (
      h' (a) \cap pre(b) != empty
      and
      h' (a) \cap pre(b') != empty)
    )
  then add the constraint:
  x_b != x_b'

* bound(k) ::
  x_{a1} + ... x_{an} <= k
  and
  for every label a and every event e in h'(a) :
  0 <= x_e < x_a


TODO (old items on the old SMT/SAT encodings)
---------------------------------------------
 * use (distinct x y) on preset and postset of every event
 * better encoding for the counting on each label, with bit vectors??
 * switch to old encoding for conditions: v_b1,b2, if some number is small ??
 * generate \bot event when going from the partial orders to the event structure
 * if one event cannot be merged with any other event, you don't need to
   generate (distinct x y) for x,y in its preset
 * most events have a label different than anyone else, ie, cannot be merged
   with any one. Remove them from the encoding!!

TODO
----

* x improving extract-dependence (post \cap post is unnecessary)
*  accounting for exact nr. of places when merging postsets
*  using 'events-only', devise a (huge!) reduction of SMT encodings
*  in the IP encoding, search for cliques of independent transitions and use
   (distinct x y z) for, e.g., the presets of them

* equivalence relation 'only-events'
* mode to extract logs


IP incompatibilities
--------------------

The current IP encoding is unable to merge conditions for
mcc/CircadianClock-PT-000001.pnml with the following log::

 Idx  Len Sequence
 ---- --- ----------------------------------------
   0  12 [transc_dr, transl_r, transc_da, deg_ma, deg_r, deg_mr, transc_da, deg_ma, transc_dr, transl_r, deg_mr, deg_r]
   1   9 [transc_da, transl_a, deg_a, deg_ma, transc_dr, transl_r, deg_mr, transc_dr, deg_mr]

The problem is that the last event by deg_mr in the second sequence forces to
merge the presets of e1 and e9, both events of transl_r, which forces
dependencies between other transitions that were originally independent.

The underlying problem is the condition generation algorithm we are using :(

Here is the log::
 <log openxes.version="1.0RC7" xes.features="" xes.version="1.0" xmlns="http://www.xes-standard.org/">
 <extension name="Concept" prefix="concept" uri="http://www.xes-standard.org/concept.xesext" />
 <string key="concept:name" value="Aha!" />
 <trace>
 	<string key="concept:name" value="seq0" />
 	<event>
 	<string key="concept:name" value="transc_dr" />
 	</event>
 	<event>
 	<string key="concept:name" value="transl_r" />
 	</event>
 	<event>
 	<string key="concept:name" value="transc_da" />
 	</event>
 	<event>
 	<string key="concept:name" value="deg_ma" />
 	</event>
 	<event>
 	<string key="concept:name" value="deg_r" />
 	</event>
 	<event>
 	<string key="concept:name" value="deg_mr" />
 	</event>
 	<event>
 	<string key="concept:name" value="transc_da" />
 	</event>
 	<event>
 	<string key="concept:name" value="deg_ma" />
 	</event>
 	<event>
 	<string key="concept:name" value="transc_dr" />
 	</event>
 	<event>
 	<string key="concept:name" value="transl_r" />
 	</event>
 	<event>
 	<string key="concept:name" value="deg_mr" />
 	</event>
 	<event>
 	<string key="concept:name" value="deg_r" />
 	</event>
 </trace>
 <trace>
 	<string key="concept:name" value="seq1" />
 	<event>
 	<string key="concept:name" value="transc_da" />
 	</event>
 	<event>
 	<string key="concept:name" value="transl_a" />
 	</event>
 	<event>
 	<string key="concept:name" value="deg_a" />
 	</event>
 	<event>
 	<string key="concept:name" value="deg_ma" />
 	</event>
 	<event>
 	<string key="concept:name" value="transc_dr" />
 	</event>
 	<event>
 	<string key="concept:name" value="transl_r" />
 	</event>
 	<event>
 	<string key="concept:name" value="deg_mr" />
 	</event>
 	<event>
 	<string key="concept:name" value="transc_dr" />
 	</event>
 
 	<!-- this is the bad guy -->
 	<event>
 	<string key="concept:name" value="deg_mr" />
 	</event>
 </trace>
 </log>

