# x86lean artifact image, stage 1: the Lean toolchain and the repository at the pin (CAV 2027 AE, STATUS row 63 act 3).
# Built for linux/amd64. Stage 2 (below) adds the pinned reference model, ACL2 x86isa, certified.
# Nothing here needs a credential: every download is a public URL.
FROM ubuntu:24.04

ENV DEBIAN_FRONTEND=noninteractive
RUN apt-get update && apt-get install -y --no-install-recommends \
        ca-certificates curl git python3 time build-essential \
    && rm -rf /var/lib/apt/lists/*

# elan, then the exact toolchain the repository pins in `lean-toolchain` (read from the copied tree, not retyped here).
ENV ELAN_HOME=/opt/elan PATH=/opt/elan/bin:$PATH
RUN curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
        | sh -s -- -y --no-modify-path --default-toolchain none

WORKDIR /x86lean
COPY . /x86lean
RUN elan toolchain install "$(cat lean-toolchain)" && elan default "$(cat lean-toolchain)" && lean --version

# Stage 2: the reference model, at the pinned ACL2 commit (scripts/oracle_revision.txt), built and x86isa certified by
# the repository's own recipe. Baked into the image so the reviewer never pays the certification; timed here.
RUN apt-get update && apt-get install -y --no-install-recommends sbcl && rm -rf /var/lib/apt/lists/* && sbcl --version
RUN start=$(date +%s) && J=4 bash scripts/setup_oracle.sh > /tmp/oracle.log 2>&1; rc=$?; \
    echo "MEASURE oracle-setup rc=$rc secs=$(( $(date +%s) - start ))"; tail -3 /tmp/oracle.log; exit $rc

# The build is NOT run here: the AE reviewer runs it, and the measurement step times it (artifact/measure.sh).
CMD ["bash", "artifact/measure.sh"]
