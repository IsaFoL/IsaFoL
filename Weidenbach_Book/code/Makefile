MLTON = mlton

all: isasat restart

isasat:
	$(MLTON) -const 'MLton.safe false' -verbose 1 -default-type int64 -output IsaSAT -codegen native -inline 700 -cc-opt -O3 IsaSAT.mlb

restart:
	$(MLTON) -const 'MLton.safe false' -verbose 1 -default-type int64 -output IsaSAT_restart -codegen native -inline 700 -cc-opt -O3 IsaSAT_restart.mlb

example:
	echo "\nsimply print the SAT or UNSAT:\n\n" &&	./IsaSAT AProVE09-21.cnf && echo "\n\n"
	echo "\n\nwith the model:\n" && ./IsaSAT --verbose AProVE09-21.cnf

clean:
	rm -f IsaSAT IsaSAT_restart