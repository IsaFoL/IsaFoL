MLTON = mlton

all: isasat

isasat:
	$(MLTON) -verbose 1 -default-type int64 -output IsaSAT -profile alloc -profile-branch true -codegen native -inline 700 -cc-opt -O3 IsaSAT.mlb

example:
	echo "\nsimply print the SAT or UNSAT:\n\n" &&	./IsaSAT AProVE09-21.cnf && echo "\n\n"
	echo "\n\nwith the model:\n" && ./IsaSAT --verbose AProVE09-21.cnf

clean:
	rm -f IsaSAT