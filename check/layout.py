"""Where lean-surfaces is: svGolf's two layouts, detected, never configured.

svGolf runs in two layouts and every path to lean-surfaces goes through this file:

  inside      svGolf is the `svgolf/` directory of a lean-surfaces checkout (the development
              layout). lean-surfaces is the parent directory; svgolf/lakefile.toml requires it by
              path and sets `packagesDir` to the parent's `.lake/packages`, so the packages
              (mathlib and friends) are the parent's, pinned by the parent's `lake-manifest.json`.
  standalone  svGolf is its own repository, which requires lean-surfaces as the Lake git
              dependency `lean-models`. lean-surfaces is `.lake/packages/lean-models`, and the
              packages are svGolf's own `.lake/packages`, pinned by its own `lake-manifest.json`
              (the root manifest, which lists the dependency's packages too).

The layout is `inside` exactly when the parent directory is a lean-surfaces checkout (it has
`LeanModels/Sv/` and `extractors/sv/extract.py`), else `standalone`. Either way lean-surfaces'
build products are under `LS_ROOT/.lake/build` (a path dependency builds in the parent's
directory, a git dependency in its own checkout).

Environment overrides: SVGOLF_LS_ROOT (the lean-surfaces root) and SVGOLF_PACKAGES (the package
directory). Standard library only; importable by path from any of svGolf's scripts.
"""

import os

DEPENDENCY = "lean-models"          # lean-surfaces' Lake package name, the `require` of svGolf
SVGOLF = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def is_lean_surfaces(path):
    """True if `path` is a lean-surfaces checkout: it has the ls-sv semantics and extractor."""
    return (os.path.isdir(os.path.join(path, "LeanModels", "Sv"))
            and os.path.isfile(os.path.join(path, "extractors", "sv", "extract.py")))


def detect(svgolf=SVGOLF, environ=None):
    """The layout of the svGolf tree at `svgolf`: a dict with `layout` ("inside" or
    "standalone"), `ls_root`, `packages` and `manifest` (the `lake-manifest.json` that pins the
    packages), all absolute. A pure function of the directory tree and `environ`."""
    environ = os.environ if environ is None else environ
    svgolf = os.path.abspath(svgolf)
    parent = os.path.dirname(svgolf)
    layout = "inside" if is_lean_surfaces(parent) else "standalone"
    ls_root = os.path.abspath(environ.get("SVGOLF_LS_ROOT")
                              or (parent if layout == "inside"
                                  else os.path.join(svgolf, ".lake", "packages", DEPENDENCY)))
    return {"layout": layout, "ls_root": ls_root,
            "packages": os.path.abspath(packages_dir(layout, svgolf, ls_root, environ)),
            "manifest": manifest_path(layout, svgolf, ls_root)}


def packages_dir(layout, svgolf, ls_root, environ=None):
    """The package directory of a layout: SVGOLF_PACKAGES, else `ls_root`'s packages inside (the
    parent's, where svgolf/lakefile.toml's `packagesDir` points) and svGolf's own standalone."""
    environ = os.environ if environ is None else environ
    if environ.get("SVGOLF_PACKAGES"):
        return environ["SVGOLF_PACKAGES"]
    return os.path.join(ls_root if layout == "inside" else svgolf, ".lake", "packages")


def manifest_path(layout, svgolf, ls_root):
    """The `lake-manifest.json` that pins the packages for a given layout."""
    return os.path.join(ls_root if layout == "inside" else svgolf, "lake-manifest.json")


_HERE = detect()
LAYOUT = _HERE["layout"]
LS_ROOT = _HERE["ls_root"]
PACKAGES = _HERE["packages"]
MANIFEST = _HERE["manifest"]
