all:
	mlton -verbose 1 -default-type int64 -output IsaSAT -codegen native -cc-opt -O3 full_SAT_Trail_solver_with_init.mlb

profile:
	mlton -verbose 1 -default-type int64 -output IsaSAT -profile time -profile-branch true -codegen native full_SAT_Trail_solver_with_init.mlb

clean:
	rm -rf IsaSAT mlmont.out