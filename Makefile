all:
	../../isafol-private/Other/update_refs.pl  --unsafe
	/home/zmaths/isabelle/isabelle/bin/isabelle build -o browser_info -o "document=pdf" -o "document_variants=document:outline=/proof,/ML;userguide" -c -v -D .
