#!/usr/bin/env python

import sys
import ptnet

if __name__ == '__main__' :
    n = ptnet.Net (True)
    n.read (sys.stdin, 'pnml')
    n.write (sys.stdout, 'dot')

# vi:ts=4:sw=4:et:
