#!/bin/bash
#
# Download and install the given version of Isabelle, if not already present.
#
# To be used in the build environment only.

ISABELLE_VERSION=$(cat ~/project/ISABELLE_VERSION)
if [ ! -d "$HOME/Isabelle" ]; then

  mkdir ~/Isabelle;
  cd ~/Isabelle;
  curl -sS https://bitbucket.org/akrauss/isabelle-soft-types/get/$ISABELLE_VERSION.tar.gz | tar -xz --strip-components=1;
  ~/Isabelle/bin/isabelle components -I;
  ~/Isabelle/bin/isabelle components -a;
  # Do not eat too much memory, to avoid being killed.
  echo 'ML_OPTIONS="--maxheap 2000"' >> ~/.isabelle/etc/settings;
  cat ~/.isabelle/etc/settings;
fi

