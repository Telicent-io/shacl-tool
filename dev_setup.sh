#!/bin/sh

NO_PRE=false

for arg in "$@"; do
   if [ "$arg" = "--force" ]; then
       DEFAULT_VIRTUAL_ENV=${VIRTUAL_ENV:-NO_ENV}
       [ -n "${VIRTUAL_ENV}" ] && echo 'Installing outside virtual environment'
   fi

   # Check if argument is "--no-pre"
   if [ "$arg" = "--no-pre" ]; then
       NO_PRE=true
       echo 'Skipping pre-commit installation'
   fi
done

if [ -n "${VIRTUAL_ENV:-$DEFAULT_VIRTUAL_ENV}" ]; then
   echo "Using virtualenv: ${VIRTUAL_ENV:-$DEFAULT_VIRTUAL_ENV}"
else
   echo 'Must specify virtualenv'
   exit 1
fi

python3 -m pip install --upgrade pip
python3 -m pip install pip-tools
python3 -m piptools compile --all-extras -o requirements.txt pyproject.toml
python3 -m pip install -r requirements.txt

if ! $NO_PRE; then
   pre-commit install
fi
