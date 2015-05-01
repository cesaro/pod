
import networkx

import ptnet
import pes

from log import *
from util import *
from encoding import *
from equivalence import *

def log_to_pes (log, indep) :
    es = pes.PES ()
    i = 0
    for seq in log.traces :
        __seq_to_pes (es, i, seq, indep)
        i += 1
    print "pod: log > pes: done, %d events, %d minimal, %.2f avg. preset size" % \
            (len (es.events),
            len (es.minimal),
            avg_iter (len (e.pre) for e in es.events))
    return es

def __seq_to_pes (es, i, seq, indep) :
    skip_from = 10
    if i < skip_from :
        print 'pod: log > pes: seq %d len %d %s' % \
                (i, len (seq), long_list (seq, 10))
    elif i == skip_from :
        print 'pod: log > pes: ... skipping debug info for remaining log sequences'
    c = es.get_empty_config ()
    j = 0
    #print 'pes', es
    for logev in seq :
        a = logev.action
        #print '==============================='
        #print "c", c
        #print "a '%s' dependent with %s" % (a, indep.dependent_with (a))
        l = [e for e in c.enabled () if e.label == a]
        assert (len (l) == 0 or len (l) == 1)
        if l :
            e = l[0]
        else :
            max_events = c.find_h0 (a, indep)
            e = es.add_event (a, max_events)
            es.set_cfls (e, indep)
            c.update_enabled_hint (e)
            if i < skip_from: print "pod: log > pes:  %s i %d" % (e, j)
        c.add (e)
        if len (e.pre) == 0 :
            es.update_minimal_hint (e)
        j += 1


def pes_to_bp (es, indep, equalize_postsets=False) :
    unf = ptnet.Unfolding ()

    # generate the events of the unfolding
    ev_tab = __pes_to_bp_gen_events (es, unf)
    #print 'ev_tab', ev_tab

    # search for the cliques in the conflict relation and make a table
    cfl_tab = __pes_to_bp_build_conflict_table (es)
    cfl_tab = __pes_to_bp_conflict_table_pick_single (es, cfl_tab)
    #print 'cfl_tab', cfl_tab

    # generate one condition and related causalities for every clique 
    pre_tab = __pes_to_bp_gen_conds_cfl (es, unf, cfl_tab, ev_tab)

    # for every two events in causal relation in the PES, generate
    # conditions (skiping causalities already introduced before)
    pre_tab = __pes_to_bp_gen_conds_pre_clique_based (es, unf, ev_tab, pre_tab, indep)
    #pre_tab = __pes_to_bp_gen_conds_pre (es, unf, ev_tab, pre_tab)

    # for every maximal event, generate a single condition in the postset
    if equalize_postsets :
        __pes_to_bp_equalize_postsets (es, unf)

    # we are done!
    s = "with" if equalize_postsets else "without"
    print "pod: pes > bp: done, %d events, %d conditions, %s postset equalization" % \
            (len (unf.events), len (unf.conds), s)
    #unf.write ('unf.dot', 'dot')
    return unf

def __pes_to_bp_equalize_postsets (es, unf) :
    print 'pod: pes > bp: equalization of event postsets'
    for a in unf.net.trans :
        m = max ([1] + [len (e.post) for e in a.inverse_label])
        for e in a.inverse_label :
            if len (e.post) == m : continue
            j = m - len (e.post)
            print 'pod: pes > bp: equalization: %d new for event %s' % (j, repr (e))
            for i in range (j) :
                unf.cond_add (None, [e])

def __pes_to_bp_gen_events (es, unf) :
    # translate all events, collect an action set and store it in
    # unf.net.trans (this is hack, but should work), and do the inverse
    # labellig
    ev_tab = {}
    action_set = set ()
    for e in es.events :
        unfe = unf.event_add (e.label)
        ev_tab[e] = unfe

        if e.label not in action_set :
            action_set.add (e.label)
            e.label.inverse_label = set ([unfe])
        else :
            e.label.inverse_label.add (unfe)

    unf.net.trans = list (action_set)
    return ev_tab

def __pes_to_bp_build_conflict_table (es) :
    # - create an undirected graph representing the conflicts
    # - find all maximal cliques
    # - for each one of them, find the list of maximal events in
    #   intersection of local configurations of the events in the clique
    # - build the table

    g = networkx.Graph ()
    tab = {}
    for e in es.events :
        for ep in e.cfl :
            g.add_edge (e, ep)
    for clique in networkx.find_cliques (g) :
        local_configs = [es.get_local_config (e) for e in clique]
        c = reduce (lambda c1, c2 : c1.intersect_with (c2), local_configs)
        tup = (tuple (c.maximal ()), tuple (clique))
        #print "pod: pes > bp: cfl clique %s maxevs %s" % (clique, c.maximal ())
        for e in clique :
            tab[e] = tup
    return tab

def __pes_to_bp_conflict_table_pick_single (es, cfl_tab) :
    tab = {}
    for (maxevs, clique) in cfl_tab.values () :
        if len (maxevs) >= 2 :
            print "pod: pes > bp: cfl clique %s pick %s" % \
                    (clique, maxevs)
        e = maxevs[0] if len (maxevs) else None
        tup = (e, clique)
        for e in clique :
            tab[e] = tup
    return tab

def __pes_to_bp_gen_conds_cfl (es, unf, cfl_tab, ev_tab) :
    pre_tab = {}
    for (epre, clique) in set (cfl_tab.values ()) :
        pre = [ev_tab[epre]] if epre != None else []
        post = [ev_tab[e] for e in clique]
        c = unf.cond_add (None, pre, post)
        for e in clique :
            pre_tab[epre, e] = c
    return pre_tab

def __pes_to_bp_gen_conds_pre (es, unf, ev_tab, pre_tab) :
    for e in es.events :
        for ep in e.pre :
            if (ep, e) not in pre_tab :
                c = unf.cond_add (None, [ev_tab[ep]], [ev_tab[e]])
                pre_tab[ep, e] = c
        if len (e.pre) == 0 :
            if (None, e) not in pre_tab :
                c = unf.cond_add (None, [], [ev_tab[e]])
                pre_tab[None, e] = c
    return pre_tab

def __pes_to_bp_gen_conds_pre_clique_based (es, unf, ev_tab, pre_tab, indep) :
    for e in es.events :
        # for all events in e.post, build graph whose edges are
        # the dependence relation
        g = networkx.Graph ()
        g.add_nodes_from (e.post)
        for e1 in e.post :
            for e2 in e.post :
                if e1 != e2 and not indep[e1.label, e2.label] :
                    g.add_edge (e1, e2)
        # for every clique, generate one condition
        for clique in networkx.find_cliques (g) :
            # remove events for which there is already condition
            for ep in [ep for ep in clique if (e, ep) in pre_tab] :
                clique.remove (ep)
            if len (clique) == 0 : continue
            unfpostevs = [ev_tab[ep] for ep in clique]
            c = unf.cond_add (None, [ev_tab[e]], unfpostevs)
            for ep in clique :
                pre_tab[e, ep] = c
        # events with empty preset will never occurr in previous
        # search, deal with them separately
        if len (e.pre) == 0 :
            if (None, e) not in pre_tab :
                c = unf.cond_add (None, [], [ev_tab[e]])
                pre_tab[None, e] = c
    return pre_tab

def bp_to_net (unf, meq) :
    # this function does the actual marging of unf, using the merging
    # equivalence me, and returns the resulting ptnet.Net
    __bp_to_net_assert_pre (unf, meq)

    net = ptnet.Net (True)
    e2t = {}
    c2p = {}

    # merge events
    print 'pod: bp > net: folding events:'
    single_t = []
    for eqclass in meq.classes () :
        assert (len (eqclass) >= 1)
        e = next (iter (eqclass))
        if not isinstance (e, ptnet.Event) : continue
        t = net.trans_add (e.label)
        for e in eqclass : e2t[e] = t
        if len (eqclass) == 1 :
            single_t.append (next (iter (eqclass)))
        else :
            print "pod: bp > net: * ac %s, %d events: %s" % \
                    (t.name, len (eqclass), long_list (eqclass, 10))
    print "pod: bp > net: * ... %d events didn't merge: %s" % \
            (len (single_t), long_list (single_t, 15))
    

    # merge conditions
    print 'pod: bp > net: folding conditions:'
    single_p = []
    i = 0
    for eqclass in meq.classes () :
        assert (len (eqclass) >= 1)
        c = next (iter (eqclass))
        if not isinstance (c, ptnet.Condition) : continue
        #p = net.place_add (long_list (eqclass, 2))
        #p = net.place_add (repr (c))
        p = net.place_add ('p%d' % i)
        i += 1
        for c in eqclass : c2p[c] = p
        if len (eqclass) == 1 :
            single_p.append (next (iter (eqclass)))
        else :
            print "pod: bp > net: * %d conds: %s" % \
                    (len (eqclass), long_list (eqclass, 20))

    print "pod: bp > net: * ... %d conditions didn't merge: %s" % \
            (len (single_p), long_list (single_p, -15))
    print "pod: bp > net: summary: transitions: %d singleton classes, %d non-singleton" % \
            (len (single_t), len (net.trans) - len (single_t))
    print "pod: bp > net: summary: places: %d singleton classes, %d non-singleton" % \
            (len (single_p), len (net.places) - len (single_p))

    # build flow
    print 'pod: bp > net: folding flow relation'
    for e in e2t :
        for c in e.pre :
            e2t[e].pre_add (c2p[c])
        for c in e.post :
            e2t[e].post_add (c2p[c])

    # build initial marking
    for c in unf.m0 :
        net.m0[c2p[c]] = 1

    print "pod: bp > net: done, %d transitions, %d places" \
            % (len (net.trans), len (net.places))
    return (net, e2t, c2p)

def __bp_to_net_assert_pre (unf, meq) :

    # all events have non-empty preset
    for e in unf.events :
        assert (len (e.pre))

def bp_to_net_assert_sp (unf, meq, e2t, c2p) :

    print 'pod: bp > net: asserting correctness: checking that folding was SP...'

    assert (len (e2t) == len (unf.events))
    assert (len (c2p) == len (unf.conds))

    # if two events were merged, then the two sets of equivalence
    # classes for conditions in their presets are the same
    for e,t in e2t.items () :
        for ee in e2t :
            if e2t[ee] == t :
                assert (meq.are_merged (e, ee))
                #print 'pod: e %s ee %s' % (e, ee)
                __bp_to_net_assert_subset (meq, e.pre, ee.pre)
                __bp_to_net_assert_subset (meq, ee.pre, e.pre)

    # same but checked differently: if two events were merged, then the set of
    # equivalence classes in their preset is equal
    for e,t in e2t.items () :
        for ee in e2t :
            if e2t[ee] == t :
                eqclasses_e = set (frozenset (meq.class_of (c)) for c in e.pre)
                eqclasses_ee = set (frozenset (meq.class_of (c)) for c in ee.pre)
                assert (eqclasses_e == eqclasses_ee)
                # and again differently :)
                _eqclasses_e = set (c2p[c] for c in e.pre)
                _eqclasses_ee = set (c2p[c] for c in ee.pre)
                assert (_eqclasses_e == _eqclasses_ee)
                assert (len (_eqclasses_e) == len (eqclasses_e))
                assert (len (_eqclasses_ee) == len (eqclasses_ee))

    # if two conditions gave the same place, then they were equivalent
    # ...
    for c,p in c2p.items () :
        for cc in c2p :
            if c2p[cc] == p :
                assert (meq.are_merged (c, cc))

def __bp_to_net_assert_subset (meq, x, y) :
    # every condition in x has been merged to some condition of y
    for c in x :
        #print 'pod: c %s x %s y %s' % (c, x, y)
        assert (any (map (lambda cc : meq.are_merged (c, cc), y)))

# vi:ts=4:sw=4:et:
