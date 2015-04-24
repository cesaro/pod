
import pes
import xml.etree.ElementTree

class Action :
    def __init__ (self, name) :
        self.name = name

    def __repr__ (self) :
        return self.name

    def __str__ (self) :
        return repr (self)

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
        print 'pod: xes: done, %d logs, %d log events, %d distinct actions' \
                % (len (self.traces), nre, len (self.action_tab))

    def to_pes (self, indep) :
        es = pes.PES ()
        for seq in self.traces :
            self.__trace_to_pes (self, pes, seq, indep)

    def __trace_to_pes (self, pes, seq, indep) :
        c = pes.get_empty_config ()
        for logev in seq :
            a = logev.action
            l = [e for e in c.enabled () if e.label == a]
            assert (len (l) == 0 or len (l) == 1)
            if l :
                e = c.add (l[0])
            else :
                max_events = c.find_h0 (a, indep)
                e = pes.add_event (a, max_events)
                pes.set_cfls (e, indep)
                c.update_enabled_hint (e)
            c.add (e)


class Indep :
    def __init__ (self) :
        pass
    def __getitem__ (self, t1, t2) :
        return False



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
