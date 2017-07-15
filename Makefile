SUBDIRS=SF/lf SF/vfa compiler  # qc is currently broken

all:
	@set -e; for d in $(SUBDIRS); do $(MAKE) -C $$d; done
	(cd Metalib; make; make install; make doc)
	(cd Stlc; make; make html)

clean:
	@set -e; for d in $(SUBDIRS); do $(MAKE) -C $$d clean; done
