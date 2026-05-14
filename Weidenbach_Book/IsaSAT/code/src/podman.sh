#!/bin/sh
exec podman \
  run --rm -i -t --volume=`pwd`:/tool --workdir=/tool \
  registry.gitlab.com/sosy-lab/benchmarking/competition-scripts/user:latest \
  $*
