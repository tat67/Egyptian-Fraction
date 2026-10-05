# Build all programs.  GMP: only the shared library libgmp.so.10 is needed (gmpz.h declares the few
# functions used), so no GMP development package is required.
GMP ?= /usr/lib/x86_64-linux-gnu/libgmp.so.10
CXX ?= g++
CXXFLAGS ?= -O2 -march=native -std=c++17

all: q2exact complete_dump complete_ind test_compl brute_core q2k q2b

q2exact: q2exact.cpp compl.h ind2.h gmpz.h msclock.h
	$(CXX) $(CXXFLAGS) -pthread -o $@ q2exact.cpp $(GMP)
complete_dump: complete_dump.cpp compl.h gmpz.h msclock.h
	$(CXX) $(CXXFLAGS) -o $@ complete_dump.cpp $(GMP)
complete_ind: complete_ind.cpp ind2.h gmpz.h msclock.h
	$(CXX) $(CXXFLAGS) -o $@ complete_ind.cpp $(GMP)
test_compl: test_compl.cpp compl.h gmpz.h msclock.h
	$(CXX) $(CXXFLAGS) -o $@ test_compl.cpp $(GMP)
brute_core: brute_core.cpp
	$(CXX) $(CXXFLAGS) -o $@ brute_core.cpp
q2k: q2k.cpp gmpz.h msclock.h
	$(CXX) $(CXXFLAGS) -o $@ q2k.cpp $(GMP)
q2b: q2b.cpp compl.h gmpz.h msclock.h
	$(CXX) $(CXXFLAGS) -o $@ q2b.cpp $(GMP)

clean:
	rm -f q2exact complete_dump complete_ind test_compl brute_core q2k q2b
