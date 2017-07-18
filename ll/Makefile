OCBFLAGS := -lib nums
OCB := ocamlbuild $(OCBFLAGS)

.PHONY: all debug clean top profile

all: factorial64.ll factorial64.s
debug: all 

%.cma: .FORCE
	$(OCB) $@

%.cmxa: .FORCE
	$(OCB) $@

%.native: .FORCE
	$(OCB) $@

%.byte: .FORCE
	$(OCB) $@

factorial64.ll:
	gcc -fno-asynchronous-unwind-tables -S -emit-llvm factorial64.c

factorial64.s:
	gcc -fno-asynchronous-unwind-tables -S factorial64.c


.FORCE:

clean:
	$(OCB) -clean
	rm factorial64.s factorial64.ll 

top: x86.byte
	utop

