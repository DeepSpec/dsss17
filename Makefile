EASYDIRS = SF/lf SF/vfa compiler vminus auto

MOREDIRS = $(EASYDIRS) Stlc qc Metalib Stlc

all:
	@set -e; for d in $(EASYDIRS); \
                   do echo Building $$d...; \
                   $(MAKE) -C $$d; \
                 done
	echo Building Metalib...
	(cd Metalib; make; make install; make doc)
	echo Building Stlc...
	(cd Stlc; make; make html)
	echo Building qc...
	$(MAKE) qc-depends
	$(MAKE) -C qc

clean:
	@set -e; for d in $(MOREDIRS); \
                   do echo Cleaning $$d...; \
                   $(MAKE) -C $$d clean; \
                 done

qc-depends:
	@command -v quickChick >/dev/null 2>&1 || \
           { echo Please install QuickChick:; \
             echo   git clone https://github.com/QuickChick/QuickChick.git \
             echo and then see README.md for installation instructions \
             exit 1; }
	@if ! (opam list | grep --quiet ext-lib); then \
	   echo Please install coq-ext-lib:; \
           echo   opam repo add coq-released https://coq.inria.fr/opam/released \
           echo   opam update \
           echo   opam install coq-ext-lib \
           exit 1; \
        fi
