#! /bin/bash

proofs=$(find src -name '*.v')
vagrant_files="vagrant/Vagrantfile vagrant/pg_config/emacs_config vagrant/pg_config/install_packages.el vagrant/pg_config/setup_emacs.sh vagrant/coqide.desktop"
top_files="configure Makefile README.md LICENSE.md"
pwter="pomsets-with-predicate-transformers/"

rm artifact.zip || true
zip artifact -r $proofs $vagrant_files $top_files $pwter
