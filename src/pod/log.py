
import pes
import xml.etree.ElementTree

class Action :
    def __init__ (self, name) :
        self.name = name

    def __repr__ (self) :
        return self.name

    def __str__ (self) :
        return repr (self)

class ActionSet :
    def __init__ (self) :
        self.tab = {}

    def lookup (self, name) :
        return self.tab.get (name)

    def lookup_or_create (self, name) :
        try :
            return self.tab[name]
        except KeyError :
            a = Action (name)
            self.tab[name] = a
            return a

    def __iter__ (self) :
        iter (self.tab.values ())
    def __len__ (self) :
        len (self.tab)

class Event :
    def __init__ (self, action, attr) :
        self.action = action
        self.attr = attr

    def __repr__ (self) :
        return repr (self.action)

    def __str__ (self) :
        s = "[%s " % repr (self)
        s += " ".join ("%s='%s'" % (k, v) for k,v in self.attr.items ())
        return s + "]"

class Log :
    def __init__ (self) :
        self.traces = []
        self.action_tab = {}

    def find_or_create_action (self, name) :
        try :
            return self.action_tab[name]
        except KeyError :
            a = Action (name)
            self.action_tab[name] = a
            return a

    def read (self, f, fmt='xes') :
        if isinstance (f, basestring) : f = open (f, 'r')
        if fmt == 'xes' : return self.__read_xes (f)
        raise ValueError, "'%s': unknown input format" % fmt

    def __read_xes (self, f) :
        tree = xml.etree.ElementTree.parse (f)
        root = tree.getroot()
        xmltraces = root.findall('{http://www.xes-standard.org/}trace')
        uniq_cases = {}
        nre = 0
        for trace in xmltraces:
            seq = []
            for xmlev in trace:
                if xmlev.tag != '{http://www.xes-standard.org/}event' : continue
                d = {s.attrib['key'] : s.attrib['value'] for s in xmlev}
                if 'concept:name' not in d :
                    raise Exception, 'XES file has one event with no "concept:name" key'
                a = self.find_or_create_action (d['concept:name'])
                del d['concept:name']
                e = Event (a, d)
                seq.append (e)
            self.traces.append (seq)
            nre += len (seq)

    def to_pes (self, indep) :
        es = pes.PES ()
        for seq in self.traces :
            self.__trace_to_pes (es, seq, indep)
        return es

    def __trace_to_pes (self, es, seq, indep) :
        c = es.get_empty_config ()
        print 'xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx'
        #print 'pes', es
        #print 'seq', seq
        i = 0
        for logev in seq :
            a = logev.action
            l = [e for e in c.enabled () if e.label == a]
            print '-------------------------'
            print 'action', a
            #print 'configuration', c
            print 'l', l
            assert (len (l) == 0 or len (l) == 1)
            if l :
                e = l[0]
            else :
                max_events = c.find_h0 (a, indep)
                e = es.add_event (a, max_events)
                es.set_cfls (e, indep)
                c.update_enabled_hint (e)
            print 'firing', e
            c.add (e)
            if i == 0 :
                es.update_minimal_hint (e)
                i += 1

    def extract_indep_from_net (self, net) :
        # XXX - this method assumes that the net contains exactly one
        # transition whose name equals the action's name, for every action
        # occurring in the log
        td = Depen ()
        td.from_net (net)
        d = Depen ()
        for a1 in self.action_tab :
            for a2 in self.action_tab :
                # retrieve the *unique* transitions labelled by a1 and a2
                #print 'a1 a2', a1, a2
                t1 = net.trans_lookup_name (a1)
                t2 = net.trans_lookup_name (a2)
                assert (t1 != None and t2 != None)
                #print 't1 t2 depen', t1, t2, td.get (t1, t2)
                if td.get (t1, t2) :
                    d.set (self.action_tab[a1], self.action_tab[a2])
        #print 'on transitions', td
        #print 'on actions', d
        indep = Indep ()
        indep.from_depen (d)
        return indep

    def __str__ (self) :
        return "traces %s actions %s" % (self.traces, self.action_tab.values ())

class SymmetricRelation :
    def __init__ (self, domain) :
        self.pairs = set ()
        self.negate = False
        self.domain = domain

    def set (self, t1, t2) :
        if id (t1) < id (t2) :
            self.pairs.add ((t1, t2))
        else :
            self.pairs.add ((t2, t1))

    def get (self, t1, t2) :
        if id (t1) < id (t2) :
            r = (t1, t2) in self.pairs
        else :
            r = (t2, t1) in self.pairs
        return not r if self.negate else r

    def __getitem__ (self, (t1, t2)) :
        return self.get (t1, t2)

    def __iter__ (self) :
        return iter (self.pairs)
    def __len__ (self) :
        return len (self.pairs)

    def __repr__ (self) :
        return "%d pairs tab %s negate %s" % (len (self.pairs), list (self.pairs), 'yes' if self.negate else 'no')
    def __str__ (self) :
        return repr (self)

class Indep (SymmetricRelation) :
    def __init__ (self, domain) :
        SymmetricRelation.__init__ (self, domain)

    def from_indep (self, indep) :
        self.pairs = indep.pairs
        self.negate = indep.negate
        self.domain = indep.domain

    def from_depen (self, depen) :
        self.pairs = depen.pairs
        self.negate = not depen.negate
        self.domain = depen.domain

    def check_is_independence (self) :
        # it is symmetric by construction, check it is irreflexive
        for x in self.domain :
            if self.get (x, x) :
                raise Exception, "Not irreflexive: has pair (%s, %s)" % (repr (x), repr (x))

    def from_net (self, n, action_set=None) :
        d = Depen (action_set, action_set)
        d.from_net (n)
        self.from_depen (d)

    def __repr__ (self) :
        return SymmetricRelation.__repr__ (self)
    def __str__ (self) :
        return SymmetricRelation.__str__ (self)

class Depen (SymmetricRelation) :
    def __init__ (self) :
        SymmetricRelation.__init__ (self)

    def from_indep (self, indep) :
        self.pairs = indep.pairs
        self.negate = not indep.negate
        self.domain = indep.domain

    def from_depen (self, depen) :
        self.pairs = depen.pairs
        self.negate = depen.negate
        self.domain = indep.domain

    def check_is_dependence (self) :
        # it is symmetric by construction, check it is reflexive
        for x in self.domain :
            if not self.get (x, x) :
                raise Exception, "Not reflexive: missing pair (%s, %s)" % (repr (x), repr (x))

    def from_net (self, n, action_set=None) :
        if action_set == None :
            action_set = Actionset ()
        for t in n.trans : action_set.lookup_or_create (t.name)
        d = Depen (action_set)
        for p in n.places :
            for t1 in p.post | p.pre :
                for t2 in p.post | p.pre :
                    d.set (t1, t2)
        self.from_depen (d)

    def __repr__ (self) :
        return SymmetricRelation.__repr__ (self)
    def __str__ (self) :
        return SymmetricRelation.__str__ (self)

def log_from_xes(filename, all_info=False, only_uniq_cases=True):
    """Load a log in the XES format.

    [filename] can be a file or a filename.
    If [all_info] then all XES information for the events is stored in a
    dictionary. This option is incompatible with [only_uniq_cases], and returns
    an EnhancedLog.
    If [only_uniq_cases] is True, then we discard all other information and we
    keep only the unique cases."""
    #xml = parse('steps.mxml')
    if isinstance(filename, basestring): #a filename
        name=filename
    else:
        name=filename.name
    if all_info and only_uniq_cases:
        raise ValueError, 'Incompatible arguments in log_from_xes'
    tr = {'concept:name':'name', 'lifecycle:transition':'transition',
            'time:timestamp':'timestamp'}
    tree = xml.etree.ElementTree.parse (filename)
    root = tree.getroot()
    traces = root.findall('{http://www.xes-standard.org/}trace')
    cases = []
    #uniq_cases = defaultdict(int) # cesar
    uniq_cases = {}
    for t in traces:
        case = []
        for c in t:
            if c.tag == '{http://www.xes-standard.org/}event':
                if all_info:
                    dict = {tr.get(s.attrib['key'],s.attrib['key']):s.attrib['value'] for s in c}
                    print dict
                    case.append(dict)
                else:
                    for s in c:
                        if s.attrib['key'] == 'concept:name':
                            case.append(s.attrib['value'])
        if only_uniq_cases:
            try :
                uniq_cases[ tuple(case) ] += 1
            except KeyError :
                uniq_cases[ tuple(case) ] = 1
        else:
            cases.append(case)
    return cases, uniq_cases
    if all_info:
        log = EnhancedLog(filename=name, format='xes', cases=cases)
    else:
        log = Log(filename=name, format='xes', cases=cases,
                uniq_cases=uniq_cases)
    return log

# vi:ts=4:sw=4:et:
