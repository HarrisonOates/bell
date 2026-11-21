#!/bin/sh
# Copyright 2026 Harrison Oates
# SPDX-License-Identifier: Apache-2.0

set -eu
cd "$(dirname "$0")/.."
mkdir -p target/validation-note
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  -outdir=target/validation-note output/pdf/bell-validation.tex
cp target/validation-note/bell-validation.pdf output/pdf/bell-validation.pdf
