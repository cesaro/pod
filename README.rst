hello world

SAT encoding
------------

See the paper.


SMT Encoding 1: same as the SAT encoding
------------

- associate every event e and condition b with an integer variable
  x_e and x_b

equivalence ::
  nothing to do :)

subset (X, Y) ::
  AND_{x in X} ( OR_{y in Y} (x_x = x_y ) )

labelling ::
  for every two events e, e' with different label:
  x_e != x_e'

pre ::
  for every two events (with equal label!)
  (x_e == x_e') implies
  subset (pre e, pre e') and
  subset (pre e', pre e)

post ::
  as for pre

co ::
  for every two concurrent conditions b, b'
  x_b != x_b'

bound(k) ::
  for all events e,
  x_e <= k

SMT Encoding 2: using labels
--------------------------

- associate every event e with an integer variable x_e
- associate every condition b with an integer variable x_b
- associate every label a with an integer variable x_a

let h : E -> A be the labelling of events with actions
let h': A -> 2^E be the inverse function

subset (X, Y, v) ::
  v => AND_{x in X} ( OR_{y in Y} (x_x = x_y ) )

equivalence ::
  nothing to do :)

labelling ::
  nothing to do :) !!!

pre ::
  for every two events with equal label:
  (x_e == x_e') implies
  subset (pre e, pre e', true) and
  subset (pre e', pre e, true)

post ::
  analogous to pre

co ::
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

bound(k) ::
  x_{a1} + ... x_{an} <= k
  and
  for every label a and every event e in h'(a) :
  0 <= x_e < x_a


TODO
----
 - use (distinct x y) on preset and postset of every event
 - better encoding for the counting on each label, with bit vectors??
 - switch to old encoding for conditions: v_b1,b2, if some number is small ??
 - generate \bot event when going from the partial orders to the event structure
 - if one event cannot be merged with any other event, you don't need to
   generate (distinct x y) for x,y in its preset
 - most events have a label different than anyone else, ie, cannot be merged
   with any one. Remove them from the encoding!!

Commandline syntax
==================


pod [OPTIONS] dependence-extract PNML
pod [OPTIONS] dump-log LOGFILE
pod [OPTIONS] dump-pes LOGFILE INDEPFILE
pod [OPTIONS] dump-bp LOGFILE INDEPFILE
pod [OPTIONS] dump-encoding LOGFILE INDEPFILE
pod [OPTIONS] dump-merge LOGFILE INDEPFILE
pod [OPTIONS] merge LOGFILE INDEPFILE


OPTIONS:

--log-first=n
--log-only=1,2,4
--log-exclude=7,23
--output=PATH
--format={pdf,dot,pnml}

