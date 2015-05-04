
=============================
Pod - Partial-Order Discovery
=============================

*Pod* is a tool to perform partial-order based
`process discovery <http://en.wikipedia.org/wiki/Business_process_discovery>`__.
Process discovery aims at building a formal model
(in this case, a **Petri net**) that faithfully represents a system from which we
only know a set of behaviours (in this case, a set of **logs**).
*Pod*, in addition to the set of logs, also receives as input an independence
relation on the set of actions happening on the logs.

Note that *Pod* uses Microsoft's Z3 SMT solver, which is not free for commercial
use. Please see `<src/z3/LICENSE.txt>`__ for further information.

The tool can perform various tasks, all related with process discovery, and
works in different modes. Here you have a couple of examples:

* Displaying the contents of a log file, only the first 10 executions::

   pod dump-log benchmarks/more/a22.xes --log-trunc 10

* Generating the independence relation of a Petri net and writing it to the file
  ``relation.dep``::

   pod extract-dependence benchmarks/more/a22.pnml --out relation.dep

* Perform process discovery on the same log, using the generated independence,
  doing very simple heuristics for generalization step (more info with ``-h``)::

   pod discover benchmarks/more/a22.xes relation.dep --eq sp-pre-max --out result.pnml

Requirements
============

* Python 2.7
* Packages
  ``resource``,
  ``random``,
  ``networkx``,
  ``argparse``
  (I guess that last two are the only ones not coming by default).

Installation
============

The tool is in active development, there is not installation procedure at this
moment. You need to execute it as ::

  ./src/pod.py

Observe that, in addition to the packages listed in the Requirements section,
*Pod* also uses the Z3 binding for python, and the packages ``ptnet``, ``pes``,
``sat``, and all located in the ``src/`` folder.

Usage
====

Run the tool without arguments, or run it with the ``-h`` option to the
command-line invocation syntax::

Formats
=======

*Pod* reads and writes a number of files in various formats:

* Logs: `XES <http://www.xes-standard.org/>`__ format.
* Petri nets: `PNML <http://www.pnml.org/>`__ format.

The dependence relation read by the ``merge`` mode (and written by the
``extract-dependence`` mode)
Dependence relation: private format, the relevant reading and writing code is
located in methods ``cmd_extract_dependence`` and ``__load_indep`` of class
``Main``, in file ``src/pod/main.py``. Essentially these methods read and
write a plain text file where lines starting with ``#`` are comments and where
every line contains two words, separated by one space, stating the names of two
transitions that are *dependent*. Here is one example::

 # Dependence relation on transition names, automatically extracted from:
 # benchmarks/atva15/a32.pnml
 b f
 f m
 j j
 [...]


Author and Contact
==================

Developed and maintained by
`César Rodríguez <http://lipn.univ-paris13.fr/~rodriguez/>`__.
Please feel free to contact me in case of questions or to send feedback.

