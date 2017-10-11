MLTON = mlton

all:
	$(MLTON) -verbose 1 -default-type int64 -output IsaSAT -profile alloc -profile-branch true -codegen native -inline 700 -cc-opt -O3 IsaSAT.mlb

clean:
	rm -f IsaSAT