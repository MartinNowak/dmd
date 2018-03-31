#!/usr/bin/env bash

YEAR=$(date +%Y)
sed "s/__YEAR__/${YEAR}/" ${EXTRA_FILES}/${TEST_NAME}.html > ${OUTPUT_BASE}.html.1
grep -v "Generated by Ddoc from" ${OUTPUT_BASE}.html > ${OUTPUT_BASE}.html.2
diff --strip-trailing-cr ${OUTPUT_BASE}.html.1 ${OUTPUT_BASE}.html.2

rm ${OUTPUT_BASE}.html{,.1,.2}
