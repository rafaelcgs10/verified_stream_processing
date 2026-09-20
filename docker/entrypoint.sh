#!/bin/bash
# Start a virtual X display, a VNC server and a noVNC web endpoint, then run
# Isabelle/jEdit on it.  Everything is a child of this script so that stopping
# the container tears the whole stack down.
set -euo pipefail

: "${VNC_PASSWORD:=isabelle}"
: "${GEOMETRY:=1920x1080}"
: "${NOVNC_PORT:=6080}"
: "${SESSION_ARGS:=-R Dataplane}"
: "${ISABELLE_OPTIONS:=-o show_states}"
: "${REPO_DIR:=/home/isabelle/verified_stream_processing}"

export DISPLAY=:1

cleanup() { pkill -P $$ >/dev/null 2>&1 || true; }
trap cleanup EXIT INT TERM

Xvfb "$DISPLAY" -screen 0 "${GEOMETRY}x24" -nolisten tcp &

# Wait for the display rather than sleeping a fixed amount: jEdit fails to
# start if it comes up before Xvfb is accepting connections.
for _ in $(seq 1 100); do
  if xdpyinfo -display "$DISPLAY" >/dev/null 2>&1; then break; fi
  sleep 0.2
done
if ! xdpyinfo -display "$DISPLAY" >/dev/null 2>&1; then
  echo "entrypoint: Xvfb failed to start on $DISPLAY" >&2
  exit 1
fi

# jEdit needs a window manager, or dialogs come up unmanaged and unmovable.
fluxbox >/dev/null 2>&1 &

mkdir -p "$HOME/.vnc"
x11vnc -storepasswd "$VNC_PASSWORD" "$HOME/.vnc/passwd" >/dev/null 2>&1
x11vnc -display "$DISPLAY" -rfbauth "$HOME/.vnc/passwd" \
       -forever -shared -rfbport 5900 -quiet &

websockify --web=/usr/share/novnc "$NOVNC_PORT" localhost:5900 &

echo "entrypoint: open http://localhost:${NOVNC_PORT}/vnc.html (password: ${VNC_PASSWORD})"

cd "$REPO_DIR"
# SESSION_ARGS and ISABELLE_OPTIONS are deliberately unquoted: they carry
# multiple words.
# shellcheck disable=SC2086
exec isabelle jedit -d . $SESSION_ARGS $ISABELLE_OPTIONS "$@"
