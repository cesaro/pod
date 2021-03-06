
import os
import sys
import time
import math
import networkx

import ptnet
import pes
import sat
import z3

from util import *
from log import *
from folding import *
from pod import *

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
        print '0 class', m[0].__class__
        print 'type constrain', type (y > 1023)
        print 'type m[x]', type (m[x])
        print 'type m[x].as_long', type (m[x].as_long ())
        print 'type m[x].as_string', type (m[x].as_string ())

        print 'value m[y].as_long', m[y].as_long ()

        n = z3.Int ('new_var')
        print m[n]

def test9 () :

    s = z3.Solver ()

    x = z3.Int ('x')
    y = z3.Int ('y')
    z = z3.Int ('z')

    p = z3.Bool ('p')

    s.add (p == (x == y))
    s.add (x == y)
    #s.add (z3.Not (p))
    s.add (0 <= sum ([y, z], x))
    s.add (True)
    s.add (z3.Distinct ([x, y, z]))

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

def test15 () :
    l = Log ()
    #l.read ('benchmarks/logs/incidenttelco.anon.xes')
    l.read ('benchmarks/logs/a22f0n00_1.xes')
    l.traces = l.traces[0:10]
    print 'log', l

    indep = Indep ()
    #es = l.to_pes (indep)
    #es.write ('empty.dot', 'dot')

    n = ptnet.Net ()
    n.read ('benchmarks/logs/a22f0n00_1.pnml')
    n.write ('a22.dot', 'dot')
    print 'net', n
    indep = l.extract_indep_from_net (n)
    print 'indep', indep
    es = l.to_pes (indep)
    es.write ('full.dot', 'dot')
    print 'log', l
    print 'es', es
    print 'indep', indep

def test16 () :
    g = networkx.Graph ()
    g.add_edge (1, 2)
    g.add_edge (3, 4)
    g.add_edge (3, 6)
    g.add_edge (4, 6)
    g.add_edge (5, 6)
    g.add_edge (6, 7)
    g.add_edge (6, 8)
    g.add_edge (7, 8)
    g.add_edge (8, 7)
    g.add_nodes_from (range (1, 12))

    print 'edges', g.edges ()
    print 'maximal cliques', list (networkx.find_cliques (g))
    # [[1, 2], [6, 8, 7], [6, 3, 4], [6, 5]]

def test17 () :
    # configurations, intersection, get_local_config
    l = Log ()
    l.read ('benchmarks/logs/a22f0n00_1.xes')
    l.traces = l.traces[0:2]
    print 'log', l

    n = ptnet.Net ()
    n.read ('benchmarks/logs/a22f0n00_1.pnml')
    indep = l.extract_indep_from_net (n)
    es = l.to_pes (indep)
    es.write ('full.dot', 'dot')

    print 'xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx'
    print 'PES', es
    e = es.events[3]
    c1 = es.get_local_config (e)
    print 'c1', c1
    e = es.events[17]
    c2 = es.get_local_config (e)
    print 'c2', c2
    c3 = c1.intersect_with (c2)
    print 'xxxxxxxxxxx after intersection:'
    print 'c2', c2
    print 'c1', c1
    print 'c3', c3

    print 'xxxxxxxxxxxxxxxxxxxxxx'
    c4 = es.get_config_from_set (es.events[i] for i in [0, 1, 2, 3, 5, 6])
    print 'c4', c4
    c5 = es.get_config_from_set (es.events[i] for i in [6, 4])
    print 'c5', c5
    c6 = es.get_config_from_set (es.events[i] for i in [0, 1, 2, 17, 6])
    print 'c6', c6

def test18 () :
    # configurations, intersection, get_local_config
    l = Log ()
    l.read ('benchmarks/logs/a22f0n00_1.xes')
    #l.traces = l.traces[0:30]
    print 'log', l

    n = ptnet.Net ()
    n.read ('benchmarks/logs/a22f0n00_1.pnml')
    indep = l.extract_indep_from_net (n)
    es = l.to_pes (indep)
    es.write ('pes.dot', 'dot')

    pod = Pod ()
    print 'es (before)', es, 'nr actions', len (l.action_tab)
    print 'xxxxxxxxxxxxxxx'
    unf = pod.pes_to_bp (es, indep)
    print 'yyyyyyyyyyyyyyyyyy'
    print 'es (after) ', es
    print 'unf.events', unf.events
    print 'unf.conds', unf.conds
    print 'unf.net.trans', unf.net.trans, 'size', len (unf.net.trans)
    print 'unf.net.places', unf.net.places

    m = unf.new_mark ()
    #unf.mark_context (m, [unf.events[i] for i in [12,26]], 3)
    #unf.mark_local_config (m, [unf.events[i] for i in [265,280]])
    unf.mark_context (m, unf.get_set_from_mark (m), 1)
    #unf.write ('unf.dot', 'dot', m)
    unf.write ('unf.dot', 'dot')

def test19 () :
    
    x = z3.Int ('x')
    y = z3.Int ('y')
    z = z3.Int ('z')
    s = z3.Solver ()

    cons = z3.Or ([])
    print 'cons', cons
    print 'simplify', z3.simplify (cons)
    s.add (cons)
    s.add (z3.Or (x == y, x == z))

    print 'constraints to solve:', s

    c = s.check ()
    print 'result:', c
    if c == z3.sat :
        m = s.model ()
        print 'model:', m

# vi:ts=4:sw=4:et:
