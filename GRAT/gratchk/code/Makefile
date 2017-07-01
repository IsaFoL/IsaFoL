all: gratchk

gratchk: gratchk.mlb gratchk.sml gratchk_export.sml dimacs_parser.sml Unsynchronized.sml
	mlton -verbose 1 -default-type int64 -output gratchk gratchk.mlb

install: gratchk
	cp gratchk "$(HOME)/bin/"
