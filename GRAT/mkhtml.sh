#!/bin/bash

BASEDIR=$PWD

REBUILD=false
UPLOAD=false

while [[ $# -gt 0 ]]
do
key="$1"

case $key in
    -r|--rebuild)
    REBUILD=true
    ;;
    -u|--upload)
    UPLOAD=true
    ;;
    *)
    echo "Unknown command line argument $1"        # unknown option
    exit 1
    ;;
esac
shift # past argument or value
done



if $REBUILD; then
cd gratgen
doxygen
./mkpkg.sh
cd $BASEDIR

cd gratchk/code
./mkpkg.sh
cd $BASEDIR

cd gratchk
isabelle build -d '$AFP' -D .
./mkpkg.sh
cd $BASEDIR

fi


rm -rf html
mkdir -p html


cp README.md html/
cp examples.tgz html/
cp -a archive html/

cp gratgen/gratgen.tgz html/
cp gratchk/gratchk.tgz html/
cp gratchk/code/gratchk-sml.tgz html/

cp -a gratgen/doc/html html/gratgen-doc

cp gratchk/output/outline.pdf html/
cp gratchk/output/document.pdf html/

cp evaluation/sat.csv html/
# cp evaluation/logs/2017-05-combined/rawdata.csv html/unsat.csv

cp evaluation/logs/{2017-06-combined_logs.tgz,2018-01-logs.tgz} html/

cp LICENSE html/

# cp evaluation/unsat.csv html/
# cp evaluation/big_unsat.csv html/


pandoc -V pagetitle="GRAT -- Efficient Formally Verified SAT Solver Certification Tool Chain" -s index.md > html/index.html


if $UPLOAD; then
  LOCAL_DEST=~/devel/www21-lammich/grat
  rm -rf $LOCAL_DEST
  cp -a html $LOCAL_DEST
  cd $LOCAL_DEST
  echo ADD
  hg add .
  echo COMMIT
  hg commit -m "Automatic update of GRAT" .
  echo PUSH
  hg push
  echo DONE
  cd $BASEDIR
fi


