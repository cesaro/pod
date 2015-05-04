
include defs.mk

.PHONY: all tags

all:
	-./src/pod.py --help

tags : $(SRCS)
	ctags -R src/

-include $(DEPS)

