# Isabelle/jEdit in a browser, with the formalization already checked.
#
#   docker build -t vsp .
#   docker run --rm -p 127.0.0.1:6080:6080 --shm-size=2g vsp
#   open http://localhost:6080/vnc.html
#
# See docker/README.md for memory requirements and for the variables that
# control the image.  Building this needs roughly 24 GB of RAM available to
# the Docker daemon; it will fail in confusing ways with less.

FROM ubuntu:24.04

ARG ISABELLE_VERSION=Isabelle2025-2

# isabelle.in.tum.de resolves over IPv6 only, which a default Docker bridge
# cannot reach.  This official mirror is reachable over IPv4 and carries both
# the x86_64 and the ARM build.
ARG ISABELLE_MIRROR=https://proofcraft.systems/isabelle/dist

# The AFP publishes only a rolling afp-current.tar.gz, which silently becomes
# a different AFP the moment a new release is cut.  The isabelle-prover org
# mirrors each Isabelle release branch as a git repository, so a commit SHA
# there is a genuine pin.  This one is the head of the Isabelle2025-2 branch
# on 2026-01-19, matching the AFP this formalization was checked against.
ARG AFP_REPO=isabelle-prover/mirror-afp-2025-2
ARG AFP_COMMIT=7f01619ff623215e6f04f455697a102ce25b3ee6

# Options for the batch check.  show_states makes the Isar toplevel emit the
# proof state after every command even outside interactive mode, so the states
# land in the session databases and can be dumped later with `isabelle
# build_log` without re-checking anything.  timeout_scale absorbs the slowdown
# from running under a container.
ARG BUILD_OPTIONS="-o show_states -o timeout_scale=4"

ARG SESSION=Dataplane

ENV DEBIAN_FRONTEND=noninteractive

# Package list: the first group is what the formalization itself needs (see
# README.md), the second is the X/VNC stack for jEdit.
RUN apt-get update && apt-get install -y --no-install-recommends \
      ca-certificates curl unzip \
      fontconfig libfontconfig1 fonts-dejavu-core \
      xz-utils make build-essential \
      libgmp-dev libnuma-dev libncurses-dev zlib1g-dev \
      xvfb x11vnc fluxbox novnc python3-websockify x11-utils \
      libxrender1 libxtst6 libxi6 libxext6 \
      procps \
 && rm -rf /var/lib/apt/lists/*

# ubuntu:24.04 ships a stock `ubuntu` account already holding uid 1000.
RUN (userdel -r ubuntu 2>/dev/null || true) \
 && useradd -m -u 1000 -s /bin/bash isabelle

USER isabelle
WORKDIR /home/isabelle
ENV HOME=/home/isabelle
ENV PATH=/home/isabelle/bin:$PATH
RUN mkdir -p /home/isabelle/bin

# 1. Isabelle.  TARGETARCH is supplied by BuildKit, so the same Dockerfile
#    produces a native image on both x86_64 and Apple Silicon.  Do not build
#    the amd64 image and run it on an M1 under emulation: replaying proofs is
#    CPU bound and Poly/ML is exactly the kind of workload emulation handles
#    worst.
ARG TARGETARCH
RUN case "$TARGETARCH" in \
      amd64) archive="${ISABELLE_VERSION}_linux.tar.gz" ;; \
      arm64) archive="${ISABELLE_VERSION}_linux_arm.tar.gz" ;; \
      *) echo "unsupported architecture: ${TARGETARCH}" >&2; exit 1 ;; \
    esac \
 && curl -fsSL "${ISABELLE_MIRROR}/${archive}" | tar xz \
 && ln -s "/home/isabelle/${ISABELLE_VERSION}/bin/isabelle" /home/isabelle/bin/isabelle \
 && isabelle version

# 2. The AFP at a pinned commit, registered as an Isabelle component.
#    --strip-components=1 drops the archive's top-level directory, so this
#    does not depend on how GitHub happens to name it.
RUN mkdir -p /home/isabelle/afp \
 && curl -fsSL "https://github.com/${AFP_REPO}/archive/${AFP_COMMIT}.tar.gz" \
    | tar xz --strip-components=1 -C /home/isabelle/afp \
 && test -d /home/isabelle/afp/thys \
 && isabelle components -u /home/isabelle/afp/thys

# 3. GHC.  Required, not optional: several theories use `value [GHC]`.
RUN isabelle ghc_setup

# Poly/ML heap ceiling.  Isabelle otherwise sizes this from the *host's* RAM,
# which a container's cgroup limit then makes it exceed, and the build is
# OOM-killed.
#
# Must stay at or below 16G.  Isabelle's bundled Poly/ML runs as
# ML_PLATFORM=x86_64_32-linux, which uses 32-bit pointers and rejects
# "--maxheap" above 16 Gbytes outright ("Value of --maxheap option must not
# exceeed 16Gbytes"), failing every session immediately.  That mode also needs
# roughly half the memory of the 64-bit one for the same heap content, so this
# is not as tight as it sounds.
#
# Declared here rather than with the other build arguments at the top: an ARG
# invalidates every layer after it, and tuning the heap should not re-download
# Isabelle, the AFP and GHC.
ARG ML_MAXHEAP=15G

# Cap the ML heap.  Kept here, after the expensive downloads, so that tuning it
# does not invalidate the Isabelle, AFP and GHC layers above.  Written so both
# values stay overridable at run time with `docker run -e ML_MAXHEAP=8G`.
# The resolved values are printed: if Poly/ML refuses to start, the symptom is
# every session failing at once, and these two lines are what explain it.
RUN mkdir -p "$(isabelle getenv -b ISABELLE_HOME_USER)/etc" \
 && printf '%s\n' \
      'ML_OPTIONS="--minheap ${ML_MINHEAP:-1G} --maxheap ${ML_MAXHEAP:-'"${ML_MAXHEAP}"'}"' \
      >> "$(isabelle getenv -b ISABELLE_HOME_USER)/etc/settings" \
 && isabelle getenv ML_OPTIONS ML_PLATFORM

# 4. The formalization, and the batch check that produces the heaps.
#    This is the expensive layer, so it comes last: editing a theory does not
#    invalidate the Isabelle/AFP/GHC layers above.
COPY --chown=isabelle:isabelle . /home/isabelle/verified_stream_processing
WORKDIR /home/isabelle/verified_stream_processing

RUN isabelle build -d . -b -v ${BUILD_OPTIONS} ${SESSION}

ENV REPO_DIR=/home/isabelle/verified_stream_processing

# `-l Dataplane` loads the session as the logic image, so every theory of the
# formalization, the case studies included, is already in the heap and nothing
# is re-checked when a file is opened.  This is a read-only view: jEdit serves
# the buffer from the session database instead of the prover, so editing a
# theory invalidates its markup.  Switch to `-R Dataplane` to work on the case
# studies, see docker/README.md.
ENV SESSION_ARGS="-l Dataplane"

# show_states is what put the proof states into the database at build time.
# editor_output_state is what makes the editor display those stored states:
# the State panel is inert in this mode, so without it the Output panel shows
# messages only and never a goal.  It defaults to false.
ENV ISABELLE_OPTIONS="-o show_states -o editor_output_state=true"
ENV GEOMETRY=1920x1080
ENV NOVNC_PORT=6080

COPY --chown=isabelle:isabelle docker/entrypoint.sh /home/isabelle/entrypoint.sh

EXPOSE 6080
ENTRYPOINT ["/home/isabelle/entrypoint.sh"]
