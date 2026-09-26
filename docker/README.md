# Isabelle/jEdit in a browser

A container image with Isabelle2025-2, the AFP, and this formalization
already checked, running Isabelle/jEdit on a virtual X display that is
served to a web browser over VNC.  A reader needs a browser, not an
Isabelle installation.

```
docker run --rm -p 127.0.0.1:6080:6080 --shm-size=2g IMAGE
```

then open <http://localhost:6080/vnc.html> (default password `isabelle`).

## Memory

This is the constraint that decides everything else.

| | RAM |
|---|---|
| Building the image | about 24 GB available to the Docker daemon |
| Running it | about 12 to 16 GB, tunable with `ML_MAXHEAP` |

The build runs `isabelle build` over the whole formalization, and the ML
process alone peaks near 16 GB.  With less, the build does not fail
cleanly, it is OOM-killed or times out somewhere in the middle.

On Docker Desktop (macOS and Windows) the VM defaults to far less than
this.  Raise it under *Settings > Resources > Memory* before building.
On native Linux there is no daemon-level limit by default.

`ML_MAXHEAP` must stay at or below **16G**.  Isabelle's bundled Poly/ML runs
as `ML_PLATFORM=x86_64_32-linux`, which uses 32-bit pointers and rejects a
larger `--maxheap` outright:

    Value of --maxheap option must not exceeed 16Gbytes

The symptom is not a clear error but every session failing within seconds of
the build starting.  That mode also needs roughly half the memory of the
64-bit one for the same heap content, so 15G is less tight than it looks.

## Apple Silicon

Isabelle2025-2 ships a native ARM build (`Isabelle2025-2_linux_arm.tar.gz`),
and the official installation notes say ARM "is supported as well (e.g. for
Apple M1)".  The Dockerfile picks the right archive from BuildKit's
`TARGETARCH`, so the same file produces a native image on both
architectures.

Two things follow:

1. **Do not run the amd64 image on an M1 under emulation.**  Replaying
   proofs is CPU bound, and Poly/ML is close to the worst case for
   emulation.  Docker Desktop's Rosetta backend helps, but not enough to
   make this pleasant.  Publish and pull a native `linux/arm64` image.

2. **Prefer native hardware over cross-building.**  A native build takes
   about an hour and a half.  Going through qemu on an x86_64 host costs
   several times that, and the sharper risk is that Poly/ML manages its
   own heap with mmap and signal handling, which emulation does not always
   reproduce faithfully.  Free arm64 runners are available to public
   repositories on GitHub Actions (`ubuntu-24.04-arm`), though their 14 GB
   of disk needs clearing first and `ML_MAXHEAP` has to come down to fit
   16 GB of RAM.  An ARM instance rented by the hour avoids both problems.

   Build each architecture on its own hardware and join them into one
   manifest afterwards:

   ```
   # on an x86_64 machine with >= 24 GB
   docker buildx build --platform linux/amd64 -t IMAGE:amd64 --push .
   # on an Apple Silicon machine or an ARM cloud instance with >= 24 GB
   docker buildx build --platform linux/arm64 -t IMAGE:arm64 --push .
   # from anywhere
   docker buildx imagetools create -t IMAGE:latest IMAGE:amd64 IMAGE:arm64
   ```

A 16 GB M1 laptop can comfortably *run* the published image but cannot
build it.  That is the intended split: you build once on a large machine,
readers only ever pull and run.

## Pinned inputs

`afp-current.tar.gz` is a rolling URL and becomes a different AFP whenever
a release is cut, which would make the image silently unreproducible.  The
`isabelle-prover` organisation mirrors each Isabelle release branch as a
git repository, so a commit SHA there is a real pin.  The default is the
head of the Isabelle2025-2 branch on 2026-01-19, chosen to match the AFP
this formalization was checked against.

Override with `--build-arg AFP_COMMIT=...` to move it.

## Proof states

Both the batch check and the editor run with `-o show_states`.  In batch
mode this makes the Isar toplevel emit the proof state after every command
even though it is not interactive, so the states are written into the
session databases, as `PIDE/messages` exports.  This is what the editor then
displays: under `-l Dataplane` nothing is re-checked, so every state on
screen is one of these, and `editor_output_state=true` is what makes the
*Output* panel print them.  It defaults to false.  A normal build already
writes those, no extra option is needed, and it does not depend on `-b`:
the heap image and the database are separate artifacts, so a session that
is checked without keeping its heap still gets a full database.

Retrieving them is meant to go through `isabelle build_log -v`, but note
that `-v` is required (without it the tool prints only warnings and
errors) and that this path has not been verified end to end against a
build actually made with `show_states`.  Verify it once on a single
theory before relying on it.

Two caveats:

- `show_states` does not put proof states into the HTML produced by
  `browser_info`, which renders source markup only.
- It pretty-prints the state after *every* command, which inflates the
  session databases considerably.  These end up inside the image, so
  check the size cost before enabling it for the whole formalization.

## Variables

Build arguments:

| Name | Default | Meaning |
|---|---|---|
| `ISABELLE_VERSION` | `Isabelle2025-2` | |
| `ISABELLE_MIRROR` | proofcraft.systems | isabelle.in.tum.de is IPv6 only |
| `AFP_REPO` | `isabelle-prover/mirror-afp-2025-2` | |
| `AFP_COMMIT` | `7f01619...` | the pin |
| `ML_MAXHEAP` | `15G` | Poly/ML ceiling, must stay <= 16G |
| `BUILD_OPTIONS` | `-o show_states -o timeout_scale=4` | |
| `SESSION` | `Dataplane` | |

Run-time environment:

| Name | Default | Meaning |
|---|---|---|
| `VNC_PASSWORD` | `isabelle` | |
| `GEOMETRY` | `1920x1080` | |
| `NOVNC_PORT` | `6080` | |
| `ML_MAXHEAP` | `15G` | lower it on a smaller machine, never above 16G |
| `SESSION_ARGS` | `-l Dataplane` | what jEdit opens; `-R Dataplane` to edit |
| `ISABELLE_OPTIONS` | `-o show_states -o editor_output_state=true` | |

## Browsing with `-l`, editing with `-R`

`SESSION_ARGS` picks between the two ways `isabelle jedit` can be pointed at
a session.  They differ in which base `Sessions.Background.load` loads (see
`src/Pure/Build/sessions.scala`): under `-R S` it loads the base of `S`'s
*ancestor*, under `-l S` the base of `S` *itself*.

**`-l Dataplane`, the default here.**  The session is the logic image, so all
of it is heap resident, the 19 theories under `Examples/` included.  Isabelle
sees those as already loaded and sends nothing about them to the prover; the
buffer is reconstructed from the session database as one read-only snippet.
Opening a case study therefore costs nothing and re-checks nothing.

The catch is in the same sentence: nothing reaches the prover, so this is a
reading view.  Editing such a theory does not re-check it, it invalidates its
markup ("Changed sources for loaded theory").  The *State* panel is inert for
the same reason, which is why `editor_output_state=true` is set: it makes the
*Output* panel show the states recorded at build time, and without it no goal
is displayed anywhere.

**`-R Dataplane`, to work on the case studies.**  Now the theories of
`Dataplane` itself are on the editable source path and everything below comes
from the `Dataplane_Core` heap.  Editing a case study re-checks it, and only
it and its neighbours under `Examples/`.  Start the container with
`-e SESSION_ARGS="-R Dataplane"` for this.

`-l` needs the heap of `Dataplane` itself, which a plain `isabelle build`
does not keep, only those of the ancestors.  Hence the `-b` on the build
line: without it the editor would rebuild the whole session on every
container start.  `-R` needs only the `Dataplane_Core` heap and would be
fine either way.

## Why `-R Dataplane` starts instantly

`isabelle jedit -R Dataplane` does not automatically reuse the parent heap.
If a session imports theories that are not in its parent, Isabelle
synthesises a session called `Dataplane_requirements(<parent>)` and builds
it before the editor appears (see `Sessions.Background.load` in
`src/Pure/Build/sessions.scala`).  No batch tool builds that image, so it
would be paid on every container start.

`ROOT` therefore layers the sessions:

    Dataplane_Base    external AFP imports only
      Dataplane_Core  Lib, Timely, Correctness, Common_Operators
        Dataplane     the case studies under Examples/

`Dataplane_Base` makes the synthetic session come out empty.  `Dataplane_Core`
means that opening a case study takes the whole infrastructure from a heap
instead of replaying it: only the theories under `Examples/` stay on the
editable source path.  Building `Dataplane` still checks everything, through
its parents.

If you add an import from a new AFP session to any theory under
`dataplane/`, add it to `dataplane/Base/Dataplane_Base.thy` as well, or the
synthetic image quietly comes back.  Imports from `Examples/` into the
infrastructure must be written session-qualified (`Dataplane_Core.Consumes`),
not as relative paths: Isabelle rejects a cross-session file-path import.

## Security

The example above binds to `127.0.0.1` on purpose.  The VNC password is a
default and the stack is not hardened.  Do not expose it to a network
without putting a real proxy and real credentials in front of it.
