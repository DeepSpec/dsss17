# Written by Lucas Adam Michael Paul <lucas.paul+certikos@yale.edu>

COQDOCFLAGS := -interpolate -utf8 -parse-comments

DSSSMakefile: DSSSCoqProject compcert/Makefile.config
	-mv -f $@ $@.bak
	"$(COQBIN)coq_makefile" -f $< -o $@

include DSSSMakefile

# Before we can recurse into compcert/ or coqrel/, we need to configure
compcert/Makefile.config coqrel/Makefile:
	@echo "You need to run ./configure first"
	@false

# Some files in compcert require preprocessing
VPFILES:=compcert/arm/ConstpropOp.vp\
  compcert/arm/SelectLong.vp\
  compcert/arm/SelectOp.vp\
  compcert/backend/SelectDiv.vp\
  compcert/backend/SplitLong.vp\
  compcert/powerpc/ConstpropOp.vp\
  compcert/powerpc/SelectLong.vp\
  compcert/powerpc/SelectOp.vp\
  compcert/x86/ConstpropOp.vp\
  compcert/x86/SelectLong.vp\
  compcert/x86/SelectOp.vp

VGENFILES=$(VPFILES:.vp=.v)

$(VGENFILES): .depend-stamp

.depend-stamp: %.v: compcert/Makefile.config %.vp
	make -C compcert $(patsubst compcert/%,%,$(VGENFILES))
	touch .depend-stamp

clean::
	- rm .depend-stamp

$(addsuffix .d,$(VFILES)): $(VGENFILES)

depend: $(addsuffix .d,$(VFILES))
