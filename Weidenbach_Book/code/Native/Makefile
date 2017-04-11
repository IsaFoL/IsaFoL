all:
	mlton -verbose 1 -default-type int64 -output full_SAT_Trail -codegen native -cc-opt -O3 full_SAT_Trail_solver_with_init.mlb

profile:
	mlton -verbose 1 -default-type int64 -output full_SAT_Trail -profile time -profile-branch true -codegen native full_SAT_Trail_solver_with_init.mlb

clean:
	full_SAT_Trail