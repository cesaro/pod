
try :
    import os
    import sys
    import resource

    import util
    import merging
    import log

    import ptnet
    import z3
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
        net = ptnet.net.Net (True)

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
