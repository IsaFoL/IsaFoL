MLTON = mlton

all: isasat

isasat:
	$(MLTON) -const 'MLton.safe false' -verbose 1 -default-type int64 -output IsaSAT -codegen native -inline 700 -cc-opt -O3 IsaSAT.mlb

bounded:
	$(MLTON) -const 'MLton.safe false' -verbose 1 -default-type int64 -output IsaSAT_bounded -codegen native -inline 700 -cc-opt -O3 IsaSAT_bounded.mlb
