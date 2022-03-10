#!/bin/sh
set -e

die () {
  echo "make-src-release.sh: error: $*" 1>&2
  exit 1
}


cd `dirname $0`/..
version="`./src/isasat --version 2>/dev/null|awk '{print $1}'`"
fullgitid="`./scripts/get-git-id.sh`"
gitid="`echo $fullgitid|sed -e 's,^\(.......\).*,\1,'`"
branch=`git branch|grep '^\*'|head -1|awk '{print $2}'`
[ "$branch" = "" ] && die "could not get branch from 'git'"
name=isasat-${version}-${gitid}
[ "$branch" = "master" ] || name="$name-$branch"
dir=/tmp/$name
tar=/tmp/$name.tar.xz
rm -rf $dir
mkdir $dir || exit 1
git archive $branch | tar -x -C $dir
cat >$dir/scripts/get-git-id.sh <<EOF
#!/bin/sh
echo "$fullgitid"
EOF
chmod 755 $dir/scripts/*.sh
mkdir -p /tmp/$name/binary
cp ./src/isasat /tmp/$name/binary/
cd /tmp
rm -rf /tmp/$name/.git /tmp/$name/ML
tar cJf $tar $name
bytes="`ls --block-size=1 -s $tar 2>/dev/null |awk '{print $1}'`"
echo "generated '$tar' of $bytes bytes"
rm -rf $dir
