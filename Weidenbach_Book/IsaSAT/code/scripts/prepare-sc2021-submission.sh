#!/bin/sh
set -e

cd `dirname $0`/..
root=`pwd`
tmp=/tmp/prepare-isasat-sc2022-submission.log
VERSION="sc2022"
rm -f $tmp
##########################################################################
echo "make-src-release.sh"
cd $root
./scripts/make-src-release.sh >$tmp || exit 1
tar=`awk '{print $2}' $tmp |sed -e "s,',,g"`
echo `cat $tmp`
printf "$tar\n"
##########################################################################
echo "now starexec"
cd $root
base=isasat-${VERSION}-starexec
dir=/tmp/$base
printf "dir = $dir; tar = $tar"
rm -rf $dir
echo "mkdir"
mkdir $dir
mkdir $dir/bin
# cp ./src/isasat $dir/bin/
mkdir $dir/build
# cp ~/Documents/repos/cadical/build/cadical $dir/build/isasat
#cp src/isasat $dir/build
mkdir $dir/archives
printf "cp to archives $tar\n"
printf "cp to archives $dir\n"
cp -a $tar $dir/archives
echo "build script"
cat <<EOF >$dir/build/build.sh
#!/bin/sh
# compilation flag
tar xf ../archives/isasat*
mv isasat* isasat
cd isasat/src
# enable clang on starexec
echo "activating llvm & running make"
scl enable llvm-toolset-7.0 'make competition'
install -s isasat ../../../bin/isasat
EOF
chmod 755 $dir/build/build.sh
echo "starexec_build script"
cat <<EOF >$dir/starexec_build
#!/bin/sh
cd build
exec ./build.sh
EOF
chmod 755 $dir/starexec_build
echo "run script"
cat <<EOF >$dir/bin/starexec_run_default
#!/bin/sh
exec ./isasat \$1 \$2/proof.out
EOF
chmod 755 $dir/bin/starexec_run_default
description=$dir/starexec_description.txt
echo "IsaSAT is a verified SAT solving using the proof assistant Isabelle" > $description
archive=/tmp/$base.zip
rm -f $archive
cd $dir
zip -r $archive .
cd /tmp/
ls -l $archive
rm -f $tmp
rm -rf $dir/
