SUBDIRS=SF/lf SF/vfa compiler   # qc is currently broken

all:
	@set -e; for d in $(SUBDIRS); do $(MAKE) -C $$d; done

clean:
	@set -e; for d in $(SUBDIRS); do $(MAKE) -C $$d clean; done
