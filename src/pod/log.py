
import pes
import xml.etree.ElementTree

class Action :
    def __init__ (self, name) :
        self.name = name

    def __repr__ (self) :
        return str (self.name)

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

    def clone (self) :
        # we duplicate the dictionary self.tab, but not the actions
        nacs = ActionSet ();
        nacs.tab = dict (self.tab)
        return nacs

    def union (self, other) :
        if id (self) == id (other) : return
        # we don't do anything complex here, we refuse to unite if there is
        # a collision in the tables (union of logs should address this by a
        # substitution of one action for the other, but this should be done
        # in Log.union, not here)
        for (k,v) in other.tab.items () :
            if k in self.tab :
                raise Exception, "'%s': action in both logs, refusing to unite" % k
            self.tab[k] = v
        return self

    def __iter__ (self) :
        return iter (self.tab.values ())

    def __len__ (self) :
        return len (self.tab)

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
    def __init__ (self, actionset=None) :
        if actionset == None :
            actionset = ActionSet ()
        self.traces = []
        self.actionset = actionset

    def read (self, f, fmt='xes') :
        if isinstance (f, basestring) : f = open (f, 'r')
        if fmt == 'xes' : return self.__read_xes (f)
        raise ValueError, "'%s': unknown input format" % fmt

    def __read_xes (self, f) :
        tree = xml.etree.ElementTree.parse (f)
        root = tree.getroot()
        xmltraces = root.findall('{http://www.xes-standard.org/}trace')
        for trace in xmltraces:
            seq = []
            for xmlev in trace:
                if xmlev.tag != '{http://www.xes-standard.org/}event' : continue
                d = {s.attrib['key'] : s.attrib['value'] for s in xmlev}
                if 'concept:name' not in d :
                    raise Exception, 'XES file has one event with no "concept:name" key'
                a = self.actionset.lookup_or_create (d['concept:name'])
                del d['concept:name']
                e = Event (a, d)
                seq.append (e)
            self.traces.append (seq)

    def clone (self) :
        # we duplicate the actions set (but not the actions, just the set
        # containing them), and we also duplicate the list self.traces (but
        # not the sequences contained, nor the events contained in those
        # sequences)
        nacs = self.actionset.clone ()
        l = Log (nacs)
        l.traces = list (self.traces)
        return l

    def union (self, other) :
        if id (self) == id (other) : return
        self.actionset.union (other.actionset)
        # the next line will add new slots to self.traces, but will not
        # duplicate the sequences, nor the events they contain (nor the
        # actions)
        self.traces.extend (other.traces)
        return self

    def to_pes (self, indep) :
        es = pes.PES ()
        i = 0
        for seq in self.traces :
            self.__trace_to_pes (es, i, seq, indep)
            i += 1
        return es

    def __trace_to_pes (self, es, i, seq, indep) :
        c = es.get_empty_config ()
        print 'pod: log > pes: seq %d len %d first %s' % \
                (i, len (seq), seq[:15])
        #print 'pes', es
        j = 0
        for logev in seq :
            a = logev.action
            l = [e for e in c.enabled () if e.label == a]
            assert (len (l) == 0 or len (l) == 1)
            if l :
                e = l[0]
            else :
                max_events = c.find_h0 (a, indep)
                e = es.add_event (a, max_events)
                es.set_cfls (e, indep)
                c.update_enabled_hint (e)
                print "pod: log > pes:  %s i %d" % (e, j)
            c.add (e)
            if len (e.pre) == 0 :
                es.update_minimal_hint (e)
            j += 1

    def extract_indep_from_net (self, net) :
        # FIXME -- remove this, funcitonality is now in
        # Depen.from_net_names

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

    def __repr__ (self) :
        nre = sum (len (seq) for seq in self.traces)
        return "id %s, %d traces, %d events, %d actions" % \
            (id (self), len (self.traces), nre, len (self.actionset))
    def __str__ (self) :
        return "traces %s actions %s" % (self.traces, list (self.actionset))

class SymmetricRelation :
    def __init__ (self, domain) :
        self.pairs = set ()
        self.negate = False
        self.domain = domain

    def __is_in_domain (self, it) :
        for x in it :
            if x not in self.domain :
                raise LookupError, "'%s' is not in the domain" % repr (x)

    def set (self, x, y) :
        self.__is_in_domain ([x, y])
        if id (x) < id (y) :
            self.pairs.add ((x, y))
        else :
            self.pairs.add ((y, x))

    def get (self, x, y) :
        self.__is_in_domain ([x, y])
        if id (x) < id (y) :
            r = (x, y) in self.pairs
        else :
            r = (y, x) in self.pairs
        return not r if self.negate else r

    def __getitem__ (self, (x, y)) :
        return self.get (x, y)

    def __iter__ (self) :
        return iter (self.pairs)
    def __len__ (self) :
        return len (self.pairs)

    def __repr__ (self) :
        return "domain %d pairs %d tab %s negate %s" \
                % (len (self.domain), len (self.pairs),
                list (self.pairs),
                'yes' if self.negate else 'no')
    def __str__ (self) :
        return repr (self)

class Indep (SymmetricRelation) :
    def __init__ (self, domain=None) :
        if domain == None :
            domain = ActionSet ()
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

    def from_net_transitions (self, net) :
        d = Depen (self.domain)
        d.from_net_transitions (net)
        self.from_depen (d)

    def from_net_names (self, net) :
        d = Depen (self.domain)
        d.from_net_names (net)
        self.from_depen (d)

    def from_list (self, l) :
        d = Depen (self.domain)
        d.from_file (l)
        self.from_depen (d)

class Depen (SymmetricRelation) :
    def __init__ (self, domain=None) :
        if domain == None :
            domain = ActionSet ()
        SymmetricRelation.__init__ (self, domain)

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
                raise Exception, "Not reflexive: missing pair (%s, %s)" \
                        % (repr (x), repr (x))

    def from_net_transitions (self, net) :
        # fill the domain (an ActionSet) with all transitions, creating one
        # new Action for every transition (should this be here??)
        for t in net.trans :
            a = self.domain.lookup_or_create (t)
            self.set (a, a)
        # transitions with non-disjunct preset and postset
        for p in net.places :
            for t1 in p.post | p.pre :
                for t2 in p.post | p.pre :
                    a1 = self.domain.lookup (t1)
                    a2 = self.domain.lookup (t2)
                    self.set (a1, a2)

    def from_net_names (self, net) :
        # fill the domain (an ActionSet) with one Action for every name in
        # the net (there could be less names than transitions, or not)
        for t in net.trans :
            a = self.domain.lookup_or_create (t.name)
            self.set (a, a)
        # same as before but with the names; this means that two names will
        # be declared dependent iff there exists two transitions, resp.
        # labelled by them, that are dependent (in the non-disjoint-context
        # sense); unfolding the net with (the projection of this relation
        # on transitions, ie, t1 t2 dependentn iff their labels so are)
        # is safe, ie, the projection is a valid dependence relation
        for p in net.places :
            for t1 in p.post | p.pre :
                for t2 in p.post | p.pre :
                    a1 = self.domain.lookup (t1.name)
                    a2 = self.domain.lookup (t2.name)
                    self.set (a1, a2)

    def from_list (self, l) :
        for (x1, x2) in l :
            a1 = self.domain.lookup_or_create (x1)
            a2 = self.domain.lookup_or_create (x2)
            self.set (a1, a2)

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
