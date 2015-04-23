
import sys

class Event :
    next_nr = 0
    def __init__ (self, label) :
        self.pre = set ()
        self.post = set ()
        self.cfl = set ()
        self.label = label
        self.nr = nr
        self.m = 0
        nr += 1
    
    def pre_add (self, e) :
        # like for unfoldings
        pass

    def post_add (self, e) :
        # like for unfoldings
        pass

    def cfl_add (self, e) :
        pass

    def __repr__ (self) :
        return "%d:%s" % (self.nr, repr (self.label))

    def __str__ (self) :
        s = "%d:%s " % (self.nr, repr (self.label))
        s += "pre" + " ".join (self.pre)
        s += "cfl" + " ".join (self.cfl)
        return s

class PES :
    def __init__ (self) :
        self.events = []
        self.m = 0

    def add_event (self, label=None, pre=set(), cfl=set()) :
        e = Event (label)
        for ep in pre : e.pre_add (ep)
        for ep in cfl : e.cfl_add (ep)
        self.events.append (e)
        return e

    def new_mark (self) :
        self.m += 1
        return self.m

    def get_empty_config (self) :
        # returns an empty configuration
        pass

    def mark_local_config (self, events, m) :
        # mark the local configurations of these guys
        pass

    def set_cfls (self, e, indep) :
        # set conflicts by a linear scan of the structure, avoiding the local
        # config
        pass

    def write (self, f, fmt='dot') :
        if fmt == 'dot' : return self.__write_dot (f)
        raise Exception, "'%s': unknown output format" % fmt

    def __repr__ (self) :
        return repr (self.events)

    def __str__ (self) :
        return repr (self.events)
    
    def normalize_immediate_conflicts (self) :
        # remove from event.cfl those events in indirect conflict
        pass

class Configuration :
    def __init__ (self, pes, events=set()) :
        self.pes = pes
        self.events = set (events)
        self.__en = set ()
        self.__max = set ()

    def enabled (self) :
        # returns set of enabled events
        pass

    def extensions (self) :
        # returns ex(C)
        pass

    def add (self, e) :
        # adds one enabled event

        # - verify that e is in __en
        # - add it to envents
        # - update enabled
        pass

    def update_enabled (self, e) :
        # updates __en if this event is enabled (it has been added to the pes)
        pass

    def find_h0 (self, t, indep) :
        # find the largest history in this configuration for t under indep
        # discarding the hippies (checking if e.post is in what remains)
        # returns set of concurrent (maximal) events

        # keep two lists, move dependent ones to the second
        pass

    def is_ex (self, e) :
        # return whether e is an extension of the configuration
        pass

    def is_en (self, e) :
        # return whether e is in __en
        pass


    def __iter__ (self) :
        iter (events)

    def __repr__ (self) :
        return repr (self.events)

    def __str__ (self) :
        # FIXME add enabled
        return repr (self.events)

# vi:ts=4:sw=4:et:
