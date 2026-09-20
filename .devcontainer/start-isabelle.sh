#!/usr/bin/env bash
# Start the image's own entrypoint (Xvfb, fluxbox, x11vnc, websockify and
# Isabelle/jEdit) detached, so that the codespace does not depend on it.
#
# devcontainer.json keeps overrideCommand at its default of true, which means
# the container runs a sleep loop instead of the image's ENTRYPOINT.  This
# script supplies the entrypoint afterwards.  Running it this way rather than
# as the container's main process means a jEdit crash leaves the codespace
# alive and this script rerunnable from a terminal.
#
# Run on every codespace start (postStartCommand), so it has to be safe to
# call when the stack is already up.
set -u

LOG=/tmp/isabelle-novnc.log
ENTRYPOINT=/home/isabelle/entrypoint.sh

# docker exec inherits the image's ENV, but do not rely on it: the entrypoint
# resolves `isabelle` through PATH and writes the VNC password under $HOME.
export PATH="/home/isabelle/bin:${PATH}"
export HOME="${HOME:-/home/isabelle}"

if [ ! -x "$ENTRYPOINT" ]; then
  echo "start-isabelle: $ENTRYPOINT is missing or not executable." >&2
  echo "start-isabelle: this codespace is probably not running the published" >&2
  echo "start-isabelle: image.  Check the \"image\" field in devcontainer.json." >&2
  exit 1
fi

if pgrep -u "$(id -u)" -f websockify >/dev/null 2>&1; then
  echo "start-isabelle: already running, see $LOG"
  exit 0
fi

nohup "$ENTRYPOINT" >"$LOG" 2>&1 &
echo "start-isabelle: launched $ENTRYPOINT (pid $!), logging to $LOG"
echo "start-isabelle: noVNC will serve /vnc.html on port ${NOVNC_PORT:-6080}"
exit 0
