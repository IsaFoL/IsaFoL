#!/bin/sh
set -e

cd `dirname $0`/..
root=`pwd`
tmp=/tmp/prepare-isasat-sc2021-submission.log
VERSION="sc2021"
rm -f $tmp
##########################################################################
echo "make-src-release.sh"
cd $root
./scripts/make-src-release.sh >$tmp || exit 1
echo "make-src-release.sh"
tar=`awk '{print $2}' $tmp |sed -e "s,',,g"`
##########################################################################
echo "now starexec"
cd $root
base=isasat-${VERSION}-starexec
dir=/tmp/$base
echo "dir = $dir"
rm -rf $dir
mkdir $dir
mkdir $dir/bin
mkdir $dir/build
mkdir $dir/archives
cp -a $tar $dir/archives
cat <<EOF >$dir/build/build.sh
#!/bin/sh
tar xf ../archives/isasat*
mv isasat* isasat
cd isasat
make isallvm
install -s build/isasat ../../bin/
EOF
chmod 755 $dir/build/build.sh
cat <<EOF >$dir/starexec_build
#!/bin/sh
cd build
exec ./build.sh
EOF
chmod 755 $dir/starexec_build
cat <<EOF >$dir/bin/starexec_run_default
#!/bin/sh
exec ./isasat \$1
EOF
chmod 755 $dir/bin/starexec_run_default
description=$dir/starexec_description.txt
grep '^Isasat' README.md|head -1 >$description
cat $description
archive=/tmp/$base.zip
rm -f $archive
cd $dir
zip -r $archive .
cd /tmp/
ls -l $archive
rm -f $tmp
rm -rf $dir/
