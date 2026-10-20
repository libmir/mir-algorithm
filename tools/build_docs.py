#!/usr/bin/env python3
"""Build a documentation preview with the existing Mir templates on Linux.

Requires Git, g++, Ninja, Python 3.9+ with pip, and LDC/ldmd2 1.36.0.
Usage: python3 tools/build_docs.py build/docs
The output directory must not exist. HTML is written to OUTPUT/site; build
inputs and logs are retained alongside it. This builds HTML only: it does not
run library tests or the old template's extracted documentation tests.
Use --tests-only to build and run the Meson D and C++ tests instead of HTML.
Use --tests-with-examples to also build HTML and run extracted examples.
"""

import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys


ASSETS_REV = "83c5fa355ccdbd3b6ab4260f5816367ea299b8d2"
CORE_REV = "4397b03a804b0368100e99252016c7b32aa562d1"
LDC_VERSION = "1.36.0"


def copy_build_inputs(repo, source):
    """Overlay tracked working-tree inputs, including staged deletions."""
    tracked = set(subprocess.check_output(["git", "ls-files", "-z"], cwd=repo).decode().split("\0"))
    committed = set(subprocess.check_output(
        ["git", "ls-tree", "-r", "--name-only", "-z", "HEAD"], cwd=repo).decode().split("\0"))
    for name in sorted(tracked | committed):
        if name in ("meson.build", "index.d") or name.startswith(("source/", "include/", "cpp_example/", "subprojects/")):
            destination = source / name
            if name in tracked and (repo / name).is_file():
                destination.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(repo / name, destination)
            elif destination.is_file():
                destination.unlink()


def validate_test_results(results, configured_tests=None):
    """Require the D and C++ tests and successful results for the entire suite."""
    required = {"mir-algorithm-test", "mir-algorithm-cpp-test"}
    if not required.issubset({r["name"] for r in results}):
        raise RuntimeError("expected both Meson D and C++ tests to run")
    if any(r["result"] != "OK" for r in results):
        raise RuntimeError("expected all Meson tests to pass")
    if configured_tests is not None:
        expected = {test["name"] for test in configured_tests}
        if not any(name.endswith(" documented unittest") for name in expected):
            raise RuntimeError("Meson configured no extracted documentation tests")
        if expected != {r["name"] for r in results}:
            raise RuntimeError("test results do not match the configured Meson tests")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument("--tests-only", action="store_true",
                        help="Run Meson D and C++ tests without HTML or extracted examples")
    modes.add_argument("--tests-with-examples", action="store_true",
                       help="Build HTML and run Meson D, C++, and extracted documentation tests")
    parser.add_argument("--assets", default="https://github.com/libmir/circle-dlang.git",
                        help="Asset repository URL or local clone; revision remains pinned")
    parser.add_argument("--mir-core", default="https://github.com/libmir/mir-core.git",
                        help="Dependency URL or local clone; revision remains pinned")
    args = parser.parse_args()
    run_tests = args.tests_only or args.tests_with_examples
    repo = Path(__file__).resolve().parents[1]
    output = args.output.resolve()
    if output.exists():
        parser.error("output directory already exists; choose a fresh directory")
    compiler = shutil.which("ldc2")
    if not compiler or not shutil.which("ldmd2"):
        parser.error("ldc2 and ldmd2 must be on PATH")
    version = subprocess.check_output([compiler, "--version"], text=True)
    if f"({LDC_VERSION})" not in version.splitlines()[0]:
        parser.error(f"this documentation build requires LDC {LDC_VERSION}")
    for command in ("git", "g++", "ninja"):
        if not shutil.which(command):
            parser.error(f"missing prerequisite: {command}")
    output.mkdir(parents=True)
    env = os.environ.copy()
    env["DC"] = compiler
    env["CXX"] = shutil.which("g++")

    def run(command, log, cwd=output):
        print("Running:", " ".join(map(str, command)), flush=True)
        with (output / log).open("a", encoding="utf-8") as stream:
            result = subprocess.run(list(map(str, command)), cwd=cwd, env=env,
                                    stdout=stream, stderr=subprocess.STDOUT)
        if result.returncode:
            print((output / log).read_text(encoding="utf-8", errors="replace")[-12000:],
                  file=sys.stderr)
            raise RuntimeError(f"command failed; see {output / log}")

    def clone(url, name, revision=None):
        target = output / name
        run(["git", "clone", "--no-hardlinks", url, target], "prepare.log")
        if revision:
            run(["git", "checkout", "--detach", revision], "prepare.log", target)
        return target

    assets = clone(args.assets, "assets", ASSETS_REV)
    # The asset repository stores this binary without executable permission.
    # Its Dockerfile supplies that permission; reproduce it for native builds.
    if not args.tests_only:
        extractor = assets / "dtools_tests_extractor"
        extractor.chmod(extractor.stat().st_mode | 0o111)
    source = clone(str(repo), "source")
    # Include current working-tree edits for local validation without modifying
    # the original checkout. Copy only tracked build inputs, not build products.
    copy_build_inputs(repo, source)
    clone(args.mir_core, "source/subprojects/mir-core", CORE_REV)
    run([sys.executable, "-m", "pip", "install", "--disable-pip-version-check",
         "--target", output / "python", "meson==0.61.1", "semver==2.13.0"], "prepare.log")
    env["PYTHONPATH"] = str(output / "python")
    env["PATH"] = os.pathsep.join((str(output / "python/bin"), str(assets), env["PATH"]))
    if not args.tests_only:
        for directory in ("docgen", "web"):
            shutil.copytree(assets / directory, source / directory)
    with (source / "meson.build").open("a", encoding="utf-8") as stream:
        stream.write((assets / "meson.build.1").read_text(encoding="utf-8"))
    shutil.copy2(assets / "meson_options.txt.1", source / "meson_options.txt")
    # The asset template enables extracted examples together with HTML.
    run(["meson", "setup", "_build_dir_", "--default-library=static",
         "-Dwith_test=" + str(run_tests).lower(),
         "-Dwith_doc=" + str(not args.tests_only).lower(),
         "-Dcompany=libmir"], "configure.log", source)
    build = source / "_build_dir_"
    if run_tests:
        configured_tests = None
        if args.tests_with_examples:
            configured_tests = json.loads((build / "meson-info/intro-tests.json").read_text())
            # Single-file extraction writes to stdout, but the pinned extractor
            # still creates ./out. Create it once before parallel jobs can race.
            (build / "out").mkdir(exist_ok=True)
        run(["ninja", "-C", build, "-j2"], "build.log", source)
        run(["meson", "test", "-C", build, "--no-rebuild", "--print-errorlogs"],
            "test.log", source)
        results = [json.loads(line) for line in
                   (build / "meson-logs/testlog.json").read_text().splitlines() if line.strip()]
        validate_test_results(results, configured_tests)
        if args.tests_with_examples:
            print(f"All {len(results)} Meson tests passed, including extracted documentation examples.")
        else:
            print("Meson D and C++ tests passed; HTML and extracted examples were not built.")
        return
    targets = json.loads((build / "meson-info/intro-targets.json").read_text())
    html = [Path(t["filename"][0]).name for t in targets if t["name"].startswith("doc_target_")]
    if not html:
        raise RuntimeError("Meson configured no HTML targets")
    run(["ninja", "-C", build, "-j2", *html], "html.log", source)
    for name in html:
        if not (build / "web" / name).is_file() or not (build / "web" / name).stat().st_size:
            raise RuntimeError(f"missing or empty HTML output: {name}")
    shutil.copytree(build / "web", output / "site")
    shutil.copytree(source / "web", output / "site", dirs_exist_ok=True)
    manifest = {
        "source_commit": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=repo, text=True).strip(),
        "working_tree_build_inputs": True,
        "assets_commit": ASSETS_REV, "mir_core_commit": CORE_REV,
        "ldc": LDC_VERSION, "meson": "0.61.1", "semver": "2.13.0",
        "html_pages": len(html), "tests_run": False,
    }
    (output / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    print(f"Built {len(html)} pages in {output / 'site'}; tests were not run.")


if __name__ == "__main__":
    main()
