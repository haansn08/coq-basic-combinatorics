all: CoqMakefile
	$(MAKE) -f CoqMakefile

CoqMakefile: _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o CoqMakefile
	
