hello world

SMT Encoding
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
  for every two events (with different label!)
  (x_e == x_e') implies
  subset (pre e, pre e') and
  subset (pre e', pre e)

co ::
  for every two concurrent conditions b, b'
  x_b != x_b'

bound(k) ::
  for all events e,
  x_e <= k

