#!/usr/bin/env python

if __name__ == '__main__' :

    #import pod
    #import sys
    #m = pod.Main ()
    #m.main ()
    #sys.exit (0)

    try :
        import sys
        import pod
        m = pod.Main ()
        m.main ()
        #pod.test.test19 ()
    except KeyboardInterrupt :
        print 'pod: interrupted'
        sys.exit (1)
    except Exception as e :
        print 'pod: error: %s' % str (e)
        sys.exit (1)
    sys.exit (0)

# vi:ts=4:sw=4:et:
