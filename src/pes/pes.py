
import sys

class Event :
    def __init__ (self, nr, label) :
        self.pre = set ()
        self.post = set ()
        self.cfl = set ()
        self.label = label
        self.nr = nr
        self.m = 0
    
    def pre_add (self, e) :
        if e in self.pre : return
        self.pre.add (e)
        e.post_add (self)

    def post_add (self, e) :
        if e in self.post : return
        self.post.add (e)
        e.pre_add (self)

    def cfl_add (self, e) :
        if e in self.cfl : return
        self.cfl.add (e)
        e.cfl_add (self)

    def __repr__ (self) :
        return "e%d:%s" % (self.nr, repr (self.label))

    def __str__ (self) :
        s = "e%d:%s" % (self.nr, repr (self.label))
        s += " m " + str (self.m)
        s += " pre " + str (list (self.pre))
        s += " post " + str (list (self.post))
        s += " cfl " + str (list (self.cfl)) + ";"
        return s

class PES :
    def __init__ (self) :
        self.events = []
        self.m = 0
        self.minimal = set ()

    def add_event (self, label=None, pre=set(), cfl=set()) :
        e = Event (len (self.events), label)
        for ep in pre : e.pre_add (ep)
        for ep in cfl : e.cfl_add (ep)
        self.events.append (e)
        return e

    def update_minimal (self) :
        self.minimal = set ()
        for e in self.events :
            if len (e.pre) == 0 :
                self.minimal.add (e)

    def update_minimal_hint (self, e) :
        if len (e.pre) == 0 :
            self.minimal.add (e)

    def new_mark (self) :
        self.m += 1
        return self.m

    def get_empty_config (self) :
        return Configuration (self)

    def mark_local_config (self, events, m) :
        work = events
        while len (work) :
            e = work.pop ()
            e.m = m
            for ep in e.pre :
                if ep.m != m : work.append (ep)

    def set_cfls (self, e, indep) :

        if len (e.post) :
            raise Exception, "Trying to compute conflicts for non maximal event %s" % repr (e)

        # mark in red local configuration
        # mark in blue all immediate conflicts of those in local config
        mred = self.new_mark ()
        mblue = self.new_mark ()
        mgreen = self.new_mark ()
        work = [e]
        l = []
        ll = []
        while len (work) :
            ep = work.pop ()
            ep.m = mred
            l.append (ep)
            for epp in ep.pre :
                if epp.m != mred : work.append (epp)
            for epp in ep.cfl :
                epp.m = mblue
                ll.append (epp)
        #print 'red', l
        #print 'blue', ll
        #print 'mred', mred, 'mblue', mblue, 'mgreen', mgreen

        # for remaining events, process them once their local config is
        # processed, color them in green
        work = list (self.minimal)
        while len (work) :
            ep = work.pop ()
            #print 'at', ep
            assert (ep.m != mgreen)
            if ep.m == mblue : continue
            if ep.m != mred :
                #print '  are indep %s %s %s' % (repr (e), repr (ep), indep.get (e.label, ep.label))
                if not indep.get (e.label, ep.label) :
                    e.cfl_add (ep)
                    continue
            ep.m = mgreen
            for e2 in ep.post :
                # if every event in e2's preset is green or red, e2 is ready
                found = False
                for e3 in e2.pre :
                    if e3.m != mgreen :
                        found = True
                        break
                if not found :
                    #print '  adding', e2
                    work.append (e2)

    def write (self, f, fmt='dot') :
        if isinstance (f, basestring) : f = open (f, 'w')
        if fmt == 'dot' : return self.__write_dot (f)
        raise Exception, "'%s': unknown output format" % fmt

    def __write_dot (self, f) :
        f.write ('digraph {\n')
        f.write ('\t/* events */\n')
        f.write ('\tnode\t[shape=box style=filled fillcolor=gray80];\n')
        for e in self.events :
            f.write ('\t%s [label="%s"];\n' % (id (e), repr (e)))

        f.write ('\n\t/* causality and conflict */\n')
        nrpre, nrcfl = 0, 0
        for e in self.events :
            for ep in e.pre :
                f.write ('\t%s -> %s;\n' % (id (ep), id (e)))
                nrpre += 1
            for ep in e.cfl :
                if id (e) < id (ep) : continue
                f.write ('\t%s -> %s [style=dashed arrowhead=none color=red];\n' % (id (ep), id (e)))
                nrcfl += 1
        f.write ('\n\tgraph [label="%d events\\n%d causalities\\n%d conflicts"];\n}\n' % \
                (len (self.events), nrpre, nrcfl))

    def __repr__ (self) :
        return repr (self.events)

    def __str__ (self) :
        return repr (self.events)
    
class Configuration :
    #def __init__ (self, pes, events=set()) :
    def __init__ (self, pes) :
        self.pes = pes
        self.events = set ()
        self.__en = set (pes.minimal)
        self.__max = set ()

    def enabled (self) :
        return self.__en

    def extensions (self) :
        # returns ex(C)
        pass

    def add (self, e) :
        if e not in self.__en :
            raise ValueError, "Event %s is not enabled cand cannot be added" % repr (e)

        # add it
        self.events.add (e)

        # update maximal events
        self.__max -= e.pre
        self.__max.add (e)

        # update enabled events; first all those enabled in conflict with
        # e must go away, as well as e
        self.__en.remove (e)
        self.__en -= e.cfl

        # second, we add events enabled by the new addition, all of which
        # are in e's postset (if their history is in the configuration and
        # no conflict is in there)
        for ep in e.post :
            if self.__is_enabled (ep) :
                self.__en.add (ep)

    def __is_enabled (self, e) :
        # computes if an event is enabled, the hard way, e's history shall
        # be in the configuration and no conflict of it can be
        return e.pre <= self.events and e.cfl.isdisjoint (self.events)

    def update_enabled_hint (self, e) :
        # updates __en with this event if it is not in __en (eg, because it
        # has been added after creating this configuration)
        if self.__is_enabled (e) :
            self.__en.add (e)

    def find_h0 (self, t, indep) :
        # find the largest history in this configuration for t under indep
        # discarding the hippies (checking if e.post is in what remains)
        # returns set of concurrent (maximal) events

        # keep two lists, move dependent events to dep; mark hippies with m
        m = self.pes.new_mark ()
        dep = []
        work = list (self.__max)
        while len (work) :
            e = work.pop ()
            assert (e.m != m)
            if not indep.get (e.label, t) :
                dep.append (e)
                continue
            e.m = m
            for ep in e.pre :
                # ep is ready iff ep.post is all marked
                found = False
                for epp in ep.post :
                    if epp.m != m :
                        found = True
                        break
                if not found :
                    work.append (ep)
        return dep

    def is_ex (self, e) :
        # return whether e is an extension of the configuration
        pass

    def is_en (self, e) :
        return e in self.__en

    def __iter__ (self) :
        iter (events)

    def __repr__ (self) :
        return repr (list (self.events))

    def __str__ (self) :
        return "conf %s max %s en %s" % (list(self.events), list(self.__max), list(self.__en))

# vi:ts=4:sw=4:et:
