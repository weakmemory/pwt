#! /bin/bash
git submodule update --init --recursive
./prepare_archive.sh
cp -f artifact.zip vagrant/
(cd vagrant; vagrant up)
# (cd vagrant; vagrant reload --provision)
