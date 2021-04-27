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
mkdir $dir/build
mkdir $dir/archives
printf "cp to archives $tar\n"
printf "cp to archives $dir\n"
cp -a $tar $dir/archives
cp -a ~/Downloads/clang12-shrink2.tar.xz $dir/archives
echo "build script"
cat <<EOF >$dir/build/build.sh
#!/bin/sh
tar xf ../archives/isasat*
tar xf ../archives/clang*
mv isasat* isasat
cd isasat/src
make CLANG=../../clang+llvm-12.0.0-x86_64-linux-gnu-ubuntu-20.04/bin/clang-12 isallvm
install -s isasat ../../../bin/
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
exec ./isasat \$1
EOF
chmod 755 $dir/bin/starexec_run_default
archive=/tmp/$base.zip
rm -f $archive
cd $dir
zip -r $archive .
cd /tmp/
ls -l $archive
rm -f $tmp
rm -rf $dir/
