
try :
    import os
    import sys
    import resource
    import networkx

    import util
    import merging
    import log

    import z3
    import ptnet
    import pes
except ImportError, e:
    util.error_missing_package (e)

if sys.version_info < (2, 7, 0) or sys.version_info >= (3, 0, 0) :
    print ("")
    print ("*** ERROR ***")
    print ("This tool relies on Python 2.7!!")
    print ("Install Python 2.7 or modify the first line of the file 'po-discovery.py' so that it calls Python 2.7")
    print ("")
    sys.exit (1)

class Pod :
    def __init__ (self) :
        pass

    def main (self, args) :
        pass

    def __assert_merge_pre (self, unf, me) :

        # has a bottom event
        # it is the unflding in the me
        assert (len (unf.events[0].pre) == 0)
        assert (unf == me.enc.unf)

        # inverse labelling is good
        m = unf.new_mark ()
        for a in unf.net.trans :
            assert (len (a.inverse_label) >= 1)
            for e in a.inverse_label :
                assert (e.m != m)
                e.m = m
        for e in unf.events :
            assert (e.m == m)

    def __assert_merge_post (self, unf, me, e2t, c2p) :

        assert (len (e2t) == len (unf.events))
        assert (len (c2p) == len (unf.conds))

        for e,t in e2t.items () :
            for ee in e2t :
                if e2t[ee] == t :
                    assert (me.are_merged (e, ee))
                    self.__assert_merge_subset (me, e, ee)
                    self.__assert_merge_subset (me, ee, e)
        for c,p in c2p.items () :
            for cc in c2p :
                if c2p[cc] == p :
                    assert (me.are_merged (c, cc))
    
    def __assert_merge_subset (self, me, e, ee) :
        # all events in preset and postset of e are merged with at least
        # one of ee
        for x,y in [(e.pre, ee.pre), (e.post, ee.post)] :
            for c in x :
                assert (reduce (lambda a, b : a or b, \
                        map (lambda cc : me.are_merged (c, cc), y)))

    def merge (self, unf, me) :
        self.__assert_merge_pre (unf, me)
        net = ptnet.Net (True)

        # merge events
        e2t = {}
        c2p = {}
        for a in unf.net.trans :
            d = {}
            for e in a.inverse_label :
                found = False
                for ee in d :
                    if me.are_merged (e, ee) :
                        d[ee].add (e)
                        found = True
                        break
                if not found :
                    d[e] = set ([e])
            print "podisc: merging: label", repr (a), "result:", d.values ()
            for e,evs in d.items () :
                t = net.trans_add (repr ((a, evs)))
                for ee in evs : e2t[ee] = t

        # merge transitions
        d = {}
        for c in unf.conds :
            found = False
            for cc in d :
                if me.are_merged (c, cc) :
                    d[cc].add (c)
                    found = True
                    break
            if not found :
                d[c] = set ([c])
        print "podisc: merging: conditions:", d.values ()
        for c,conds in d.items () :
            p = net.place_add (repr (conds))
            for c in conds : c2p[c] = p

        self.__assert_merge_post (unf, me, e2t, c2p)

        # build flow
        for e in e2t :
            for c in e.pre :
                e2t[e].pre_add (c2p[c])
            for c in e.post :
                e2t[e].post_add (c2p[c])

        # build initial marking
        for c in unf.events[0].post :
            net.m0[c2p[c]] = 1

        return net

    def pes_to_bp (self, es) :
        unf = ptnet.Unfolding ()

        # generate the events of the unfolding
        ev_tab = self.__pes_to_bp_gen_events (es, unf)
        print 'ev_tab', ev_tab

        # search for the cliques in the conflict relation and make a table
        cfl_tab = self.__pes_to_bp_build_conflict_table (es)
        cfl_tab = self.__pes_to_bp_conflict_table_pick_single (es, cfl_tab)
        print 'cfl_tab', cfl_tab

        # generate one condition and related causalities for every clique 
        pre_tab = self.__pes_to_bp_gen_conds_cfl (es, unf, cfl_tab, ev_tab)

        # for every two events in causal relation in the PES, generate
        # conditions (skiping causalities already introduced before)
        pre_tab = self.__pes_to_bp_gen_conds_pre (es, unf, ev_tab, pre_tab)
        return unf

        # we are done!
        return unf

    def __pes_to_bp_gen_events (self, es, unf) :
        ev_tab = {}
        action_set = set ()
        for e in es.events :
            action_set.add (e.label)
            unfe = unf.event_add (e.label)
            ev_tab[e] = unfe

        # XXX - this is somehow a hack, but it will hopefully work
        unf.net.trans = list (action_set)
        return ev_tab

    def __pes_to_bp_build_conflict_table (self, es) :
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
            for e in clique :
                tab[e] = tup
        return tab

    def __pes_to_bp_conflict_table_pick_single (self, es, cfl_tab) :
        tab = {}
        for (maxevs, clique) in cfl_tab.values () :
            e = maxevs[0] if len (maxevs) else None
            tup = (e, clique)
            for e in clique :
                tab[e] = tup
        return tab

    def __pes_to_bp_gen_conds_cfl (self, es, unf, cfl_tab, ev_tab) :
        pre_tab = {}
        for (epre, clique) in set (cfl_tab.values ()) :
            pre = [ev_tab[epre]] if epre != None else []
            post = [ev_tab[e] for e in clique]
            c = unf.cond_add (None, pre, post)
            for e in clique :
                pre_tab[epre, e] = c
        return pre_tab

    def __pes_to_bp_gen_conds_pre (self, es, unf, ev_tab, pre_tab) :
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

def main () :
    # parse arguments (import argparse)
    # assert that input net is 1-safe!!

    # TODO
    # x support for reading the model
    # x and building a Merge_equivalence
    # - support for merging the unfolding given a Merge_equivalence
    # - debug on some small example, start with gas_station.cuf, depth=2,3,4

    pass

# vi:ts=4:sw=4:et:
