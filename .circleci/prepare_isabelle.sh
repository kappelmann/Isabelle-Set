#!/bin/bash
#
# Download and install the given version of Isabelle, if not already present.
#
# To be used in the build environment only.

set -x
set -e

ISABELLE_VERSION=$(cat ~/project/ISABELLE_VERSION)
if [ ! -d "$HOME/Isabelle" ]; then

  mkdir ~/Isabelle;
  cd ~/Isabelle;
  curl -v https://isabelle.in.tum.de/repos/isabelle/archive/$ISABELLE_VERSION.tar.gz -o isabelle.tar.gz
  tar -xz --strip-components=1 -f isabelle.tar.gz;
  ~/Isabelle/bin/isabelle components -I;
  ~/Isabelle/bin/isabelle components -a;
  # Do not eat too much memory to avoid being killed.
  echo 'ML_OPTIONS="--maxheap 2000"' >> ~/.isabelle/etc/settings;
  cat ~/.isabelle/etc/settings;
fi

