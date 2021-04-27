#!/bin/sh
set -e

echo "prepare src release"

die () {
  echo "make-src-release.sh: error: $*" 1>&2
  exit 1
}

echo "$0 = $0"

cd `dirname $0`/..
version="7653da1c"
echo "version = $version"
fullgitid="`./scripts/get-git-id.sh`"
gitid="`echo $fullgitid|sed -e 's,^\(.......\).*,\1,'`"
branch=`git branch|grep '^\*'|head -1|awk '{print $2}'`
[ "$branch" = "" ] && die "could not get branch from 'git'"
name=isasat-${version}-${gitid}
[ "$branch" = "master" ] || name="$name-$branch"
echo "name = $name"
dir=/tmp/$name
tar=/tmp/$name.tar.xz
echo "dir = $dir"
rm -rf $dir
mkdir $dir || exit 1
git archive $branch | tar -x -C $dir
cat >$dir/scripts/get-git-id.sh <<EOF
#!/bin/sh
echo "$fullgitid"
EOF
sed -i -e "s,IDENTIFIER 0$,IDENTIFIER \"$fullgitid\"," $dir/src/version.cpp
chmod 755 $dir/scripts/*.sh
cd /tmp
echo "dir = $dir"
rm -rf /tmp/$name/.git
tar cJf $tar $name
bytes="`ls --block-size=1 -s $tar 2>/dev/null |awk '{print $1}'`"
echo "generated '$tar' of $bytes bytes"
rm -rf $dir
