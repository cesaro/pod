
import os
import sys
import time
import math

import ptnet
import pes
import sat
import z3

from util import *
from log import *
from merging import *

def test1 () :
    n = ptnet.net.Net (True)
    n.read (sys.stdin, 'pnml')
    n.write (sys.stdout, 'pnml')

def test2 () :
    u = ptnet.unfolding.Unfolding (True)
    f = open ('benchmarks/nets/small/dme2.cuf', 'r')
    u.read (f)
    print 'x' * 80
    print 'events'
    for e in u.events :
        print e
    print 'x' * 80
    print 'conditions'
    for c in u.conds :
        print c

    print 'x' * 80
    print 'dot'
    u.write (sys.stdout, 'dot')

def test3 () :
    u = ptnet.unfolding.Unfolding (True)
    f = open ('benchmarks/nets/small/gas_station.cuf', 'r')
    u.read (f)

    print 'x' * 80
    print "before removing condition"
    u.write (sys.stdout, 'dot')
    print "condition"
    print u.conds[1]
    u.remove_cond (u.conds[1].nr)

    print 'x' * 80
    print "after removing condition"
    u.write (sys.stdout, 'dot')

    print 'x' * 80
    print "event"
    print u.events[0]
    u.remove_event (u.events[0].nr)
    print "after removing event"
    u.write (sys.stdout, 'dot')

def test4 () :
    #f = open ('benchmarks/nets/small/gas_station.cuf', 'r')
    #f = open ('benchmarks/nets/small/dme2.cuf', 'r')
    f = open ('benchmarks/nets/small/ab_gesc.cuf', 'r')
    u = ptnet.unfolding.Unfolding (True)
    u.read (f)
    u.prune_by_depth (2)
    u.write (sys.stdout, 'dot')

    finder = merging.EquivalenceEncoding (u)
    print
    finder.sat_encode (1)
    print
    #f = open ('/tmp/out.cnf', 'w')
    print repr (finder.satf)

def test5 () :
    for k in range (1, 6) :
        u = ptnet.unfolding.Unfolding (True)
        f = open ('benchmarks/nets/small/dme2.cuf', 'r')
        u.read (f)
        u.prune_by_depth (k)
        ff = open ('dme2-pref%d.dot' % k, 'w')
        u.write (ff, 'dot')

def test6 () :
    phi = sat.Cnf ()

    a = sat.Integer (phi, "first", 4)
    b = sat.Integer (phi, "second", 4)
    v = a.encode_lt (b)
    print 'returned', v

    print repr (phi)

    phi.add ([v])
    a.encode_eq_constant (5)
    b.encode_eq_constant (4)

    solver = sat.SatSolver ()

    model = solver.solve (phi)
    print 'SAT  ', model.is_sat ()
    print 'UNSAT', model.is_unsat ()
    print 'UNDEF', model.is_undef ()

    print 'model'
    print model

def test7 () :

    #switch = 'sat'
    #switch = 'smt1'
    switch = 'smt2'

    # events, conditions, k, vars, clauses, minisat time, answer
    results = []

    for depth in range (1, 20) :
        u = ptnet.unfolding.Unfolding (True)
        #f = open ('benchmarks/nets/small/dme2.cuf', 'r')
        f = open ('benchmarks/nets/small/ab_gesc.cuf', 'r')
        u.read (f)
        u.prune_by_depth (depth)

        stat_events = len (u.events)
        stat_conds = len (u.conds)
        
        k100 = len (u.events)
        k75 = len (u.events) * 0.75
        k50 = len (u.events) * 0.50
        k25 = len (u.events) * 0.25

        for k in [k100, k75, k50, k25] :
        #for k in [k100, k75, k25] :
        #for k in [len (u.net.trans)] :
            k = int (k)
            enc = EquivalenceEncoding (u)

            stat_k = k
            stat_labels = len (u.net.trans)

            if switch == 'sat' :
                enc.sat_encode (k)

                stat_nvars = len (enc.satf.varmap)
                stat_nclss = len (enc.satf.clsset)
                solver = sat.SatSolver ()

                tstart = time.time ()
                model = solver.solve (enc.satf, 60)
                tend = time.time ()

                stat_answer = model.result

            elif switch == 'smt2' :
                enc.smt_encode_2 (k)

                stat_nvars = 0
                stat_nclss = len (enc.z3.assertions ())

                enc.z3.set ("timeout", 1000 * 60)
                tstart = time.time ()
                result = enc.z3.check ()
                tend = time.time ()

                if result == z3.sat :
                    stat_answer = 'sat'
                elif result == z3.unsat :
                    stat_answer = 'unsat'
                else :
                    stat_answer = '?'

            stat_runtime = tend - tstart

            res = (depth,
                    stat_events, \
                    stat_conds, \
                    stat_labels, \
                    stat_k, \
                    stat_nvars, \
                    stat_nclss, \
                    stat_runtime, \
                    stat_answer)
            results.append (res)

        print "depth\tevents\tconds\tlabels\tk\tnvars\tnclaus\truntime\tanswer"
        for (d, nre, nrc, nrl, k, nv, nc, t, a) in results :
            s = "%d\t%d\t%d\t%d\t%d\t%d\t%d\t%.2f\t%s" % \
                    (d, nre, nrc, nrl, k, nv, nc, t, a)
            print s

def test8 () :
    
    x = z3.Int ('x')
    y = z3.Int ('y')
    s = z3.Solver ()

    print 'id of x     :', id (x)
    print 'id of y     :', id (y)
    print 'id of x (1) :', id (z3.Int ('x'))
    print 'id of y (1) :', id (z3.Int ('y'))

    z1 = z3.Int ('z')
    z2 = z3.Int ('z')

    print 'id of z1 :', id (z1)
    print 'id of z2 :', id (z2)

    s.add (y != x)
    s.add (x >= y)
    s.add (z1 == z2)

    expr = z3.Or ([z3.Int ('i%d' % i) == y for i in range (4)])
    print 'final expression', expr
    s.add (expr)
    expr = z3.Or (x == y)
    expr = z3.Or (expr, x == z1)
    expr = z3.Or (expr, x == z2)
    s.add (expr)
    print 'second final expression', expr

    print 'constraints to solve:', s

    c = s.check ()
    print 'result:', c
    if c == z3.sat :
        m = s.model ()
        print 'model:', m

        print m[0]
        print 'type 0', type (m[0])
        print 'type constrain', type (y > 1023)
        print 'type m[x]', type (m[x])
        print 'type m[x].as_long', type (m[x].as_long ())
        print 'type m[x].as_string', type (m[x].as_string ())

        print 'value m[y].as_long', m[y].as_long ()

        n = z3.Int ('new_var')
        print m[n]

def test9 () :
    import z3

    s = z3.Solver ()

    x = z3.Int ('x')
    y = z3.Int ('y')
    z = z3.Int ('z')

    p = z3.Bool ('p')

    s.add (p == (x == y))
    s.add (x == y)
    s.add (z3.Not (p))
    s.add (0 <= sum ([y, z], x))

    print 'solving', s
    r = s.check ()
    print 'result:', r
    if r == z3.sat :
        m = s.model ()
        print 'model:', m

def test10 () :
    f = open ('benchmarks/nets/small/ab_gesc.cuf', 'r')
    u = ptnet.unfolding.Unfolding (True)
    u.read (f)
    print 'prunning'
    u.prune_by_depth (1)
    #u.write (sys.stdout, 'dot')

    enc = EquivalenceEncoding (u)
    print 'building encoding'
    enc.smt_encode_2 (43)
    print 'xxxxxxxxxxxxxxxxxxxxxxxxxx'
    #for cons in enc.z3.assertions () : print '(', cons, ')'
    #print enc.z3.to_smt2 ()
    print 'xxxxxxxxxxxxxxxxxxxxxxxxxx'

    print_stats (sys.stdout, enc.stats ())

    print 'solvingggggggggggggggggggggggggggggggggggggggggggggggggg'
    enc.z3.set ("timeout", 1000 * 50)
    tstart = time.time ()
    r = enc.z3.check ()
    tend = time.time ()

    print 'result:', r
    if r == z3.sat :
        m = enc.z3.model ()
        #print 'model:', m

    print 'z3 running time: %.2f' % (tend - tstart)
    print 'z3 satistics'
    print enc.z3.statistics ()

def test11 () :
    f = open ('benchmarks/nets/small/ab_gesc.cuf', 'r')
    u = ptnet.unfolding.Unfolding (True)
    u.read (f)
    print 'prunning'
    u.prune_by_depth (1)
    u.add_bottom ()
    #u.write (sys.stdout, 'dot')
    print  u.events

    solver = EquivalenceSolver (u)
    print 'building encoding'
    me = solver.find_with_measure (11)
    if me != None :
        print 'merging, me', me
        po = Podisc ()
        net = po.merge (u, me)
        net.write (sys.stdout, 'dot')
    else :
        print 'merging: no!!!'

def test12 () :
    print log_from_xes ('benchmarks/logs/a22f0n00_1.xes', all_info=True,only_uniq_cases=False)
    print log_from_xes ('benchmarks/logs/a22f0n00_1.xes')

def test13 () :
    l = Log ()
    #f = open ('benchmarks/logs/a22f0n00_1.xes')
    f = open ('benchmarks/logs/incidenttelco.anon.xes')
    l.read (f, 'xes')

def test14 () :
    p = pes.PES ()
    a = p.add_event ("a")
    b = p.add_event ("b")
    c = p.add_event ("c")
    d = p.add_event ("d")
    c.pre_add (a)
    c.pre_add (b)
    c.cfl_add (d)
    p.update_minimal ()

    print 'all events', a, b, c, d
    print 'structure', p

    con = p.get_empty_config ()
    print 'config', con
    print 'enabled', con.enabled ()
    con.add (a)
    print 'after adding a', con
    con.add (b)
    print 'after adding b', con
    con.add (d)
    print 'after adding d', con
    #con.add (c) # exception expected
    #print 'after adding c', con

    p.write (sys.stdout, 'dot')

# vi:ts=4:sw=4:et:
