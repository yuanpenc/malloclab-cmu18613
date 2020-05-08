#
# Makefile for the malloc lab driver
#
SHELL = /bin/bash
DOC = doxygen
COURSECODE = 15213-s20

# C Compiler
CLANG = clang
LLVM_PATH = /usr/local/depot/llvm-7.0/bin/
CC = $(LLVM_PATH)$(CLANG)

ifneq (,$(wildcard /usr/lib/llvm-7/bin/))
  LLVM_PATH = /usr/lib/llvm-7/bin/
endif

# Additional flags used to compile mdriver-dbg
# You can edit these freely to change how your debug binary compiles.
COPT_DBG = -O0
CFLAGS_DBG = -DDEBUG=1

# Flags used to compile normally
COPT = -O3
CFLAGS = -Wall -Wextra -Werror $(COPT) -g -DDRIVER -Wno-unused-function -Wno-unused-parameter

# Build configuration
FILES = mdriver mdriver-dbg mdriver-emulate
LDLIBS = -lm -lrt
COBJS = memlib.o fcyc.o clock.o stree.o
MDRIVER_HEADERS = fcyc.h clock.h memlib.h config.h mm.h stree.h

MC = ./macro-check.pl
MCHECK = $(MC) -i dbg_

# Default rule
.PHONY: all
all: $(FILES)

# Regular driver
mdriver: mdriver.o mm-native.o $(COBJS)
	$(CC) -o $@ $^ $(LDLIBS)

# Debug driver
mdriver-dbg: COPT = $(COPT_DBG)
mdriver-dbg: CFLAGS += $(CFLAGS_DBG)
mdriver-dbg: mdriver.o mm-native-dbg.o $(COBJS)
	$(CC) -o $@ $^ $(LDLIBS)

# Sparse-mode driver for checking 64-bit capability
mdriver-emulate: mdriver-sparse.o mm-emulate.o $(COBJS)
	$(CC) -o $@ $^ $(LDLIBS)

# Version of memory manager with memory references converted to function calls
mm-emulate.o: mm.c mm.h memlib.h MLabInst.so check-format
	$(LLVM_PATH)$(CLANG) $(CFLAGS) -fno-vectorize -emit-llvm -S mm.c -o mm.bc
	$(LLVM_PATH)opt -load=./MLabInst.so -MLabInst mm.bc -o mm_ct.bc
	$(LLVM_PATH)$(CLANG) -c $(CFLAGS) -o mm-emulate.o mm_ct.bc

mm-native.o: mm.c mm.h memlib.h $(MC) check-format
	$(MCHECK) -f $<
	$(LLVM_PATH)$(CLANG) $(CFLAGS) -c -o $@ $<

mm-native-dbg.o: mm.c mm.h memlib.h $(MC) check-format
	$(LLVM_PATH)$(CLANG) $(CFLAGS) -c -o $@ $<

mdriver-sparse.o: mdriver.c $(MDRIVER_HEADERS)
	$(CC) -g $(CFLAGS) -DSPARSE_MODE -c mdriver.c -o mdriver-sparse.o

mdriver.o: mdriver.c $(MDRIVER_HEADERS)
memlib.o: memlib.c memlib.h
mm.o: mm.c mm.h memlib.h format
fcyc.o: fcyc.c fcyc.h
ftimer.o: ftimer.c ftimer.h config.h
clock.o: clock.c clock.h
stree.o: stree.c stree.h


.PHONY: submit
submit:
	@read -n 1 -p "Submit to malloclab CHECKPOINT or FINAL [c/f]? " && echo && case $$REPLY in c | C) $(MAKE) -s submit-checkpoint ;; f | F) $(MAKE) -s submit-final ;; *) exit 1; esac


.PHONY: submit-checkpoint
submit-checkpoint: mm.c check-format
	@echo
	@echo "***************************************"
	@echo "* Submitting to malloclab CHECKPOINT. *"
	@echo "***************************************"
	@echo
	@echo "I affirm that I have complied with this course's academic integrity policy as"
	@read -n 1 -p "defined at https://www.cs.cmu.edu/~213/academicintegrity.html [y/N]: " && echo && echo $$REPLY | grep -iq "^y"
	@autolab submit $(COURSECODE):malloclabcheckpoint $< -f


.PHONY: submit-final
submit-final: mm.c check-format
	@echo
	@echo "**********************************"
	@echo "* Submitting to malloclab FINAL. *"
	@echo "**********************************"
	@echo
	@echo "I affirm that I have complied with this course's academic integrity policy as"
	@read -n 1 -p "defined at https://www.cs.cmu.edu/~213/academicintegrity.html [y/N]: " && echo && echo $$REPLY | grep -iq "^y"
	@autolab submit $(COURSECODE):malloclab $< -f


.PHONY: format
format: mm.c
	$(LLVM_PATH)clang-format -style=file -i mm.c


.PHONY: check-format
check-format: mm.c
	@$(LLVM_PATH)clang-format -style=file mm.c | cmp --silent mm.c - || (echo; echo "ERROR: The formatting of mm.c is inconsistent with clang-format."; echo "       For information about clang-format, see the writeup."; echo "       To reformat your code, run \"make format\"."; echo; exit 1)


.PHONY: doc
doc: doxygen.conf mm.c mm.h memlib.h
	$(DOC) $<


.PHONY: clean
clean:
	rm -f *~ *.o *.bc *.ll
	rm -f $(FILES)
