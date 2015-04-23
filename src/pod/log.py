
import pes

class Log :
    def __init__ (self) :
        print 'Log from log.py'
        pass

    def read (self, f, fmt='txt') :
        pass

    def to_pes (self, indep) :
        pass

class Indep :
    def __init__ (self) :
        pass
    def __getitem__ (self, t1, t2) :
        pass



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
    tree = xmltree.parse(filename)
    root = tree.getroot()
    traces = root.findall('{http://www.xes-standard.org/}trace')
    cases = []
    uniq_cases = defaultdict(int)
    for t in traces:
        case = []
        for c in t:
            if c.tag == '{http://www.xes-standard.org/}event':
                if all_info:
                    dict = {tr.get(s.attrib['key'],s.attrib['key']):s.attrib['value'] for s in c}
                    case.append(dict)
                else:
                    for s in c:
                        if s.attrib['key'] == 'concept:name':
                            case.append(s.attrib['value'])
        if only_uniq_cases:
            uniq_cases[ tuple(case) ] += 1
        else:
            cases.append(case)
    if all_info:
        log = EnhancedLog(filename=name, format='xes', cases=cases)
    else:
        log = Log(filename=name, format='xes', cases=cases,
                uniq_cases=uniq_cases)
    return log


# vi:ts=4:sw=4:et:
