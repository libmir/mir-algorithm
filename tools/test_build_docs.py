"""Regression check for the working-tree snapshot used by documentation builds."""
from pathlib import Path
import subprocess
import tempfile
import unittest

from build_docs import copy_build_inputs


class BuildInputsTest(unittest.TestCase):
    def test_working_tree_changes_and_staged_deletions(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            repo = root / "repo"
            repo.mkdir()

            def git(*args):
                return subprocess.run(["git", *args], cwd=repo, check=True,
                                      stdout=subprocess.PIPE, stderr=subprocess.PIPE)

            git("init")
            (repo / "source").mkdir()
            for name in ("edited.d", "deleted.d", "untracked-later.d", "missing.d"):
                (repo / "source" / name).write_text("original\n")
            (repo / "meson.build").write_text("original\n")
            git("add", ".")
            # This commit exists only inside the temporary test fixture.
            git("-c", "user.name=Test", "-c", "user.email=test@example.invalid",
                "-c", "commit.gpgsign=false", "commit", "-m", "Fixture")
            snapshot = root / "snapshot"
            git("clone", "--no-hardlinks", str(repo), str(snapshot))

            (repo / "source/edited.d").write_text("edited\n")
            (repo / "meson.build").write_text("edited build\n")
            git("rm", "source/deleted.d")
            git("rm", "--cached", "source/untracked-later.d")
            (repo / "source/missing.d").unlink()
            (repo / "source/added.d").write_text("added\n")
            git("add", "source/added.d")
            (repo / "source/scratch.d").write_text("untracked\n")

            copy_build_inputs(repo, snapshot)

            self.assertEqual((snapshot / "source/edited.d").read_text(), "edited\n")
            self.assertEqual((snapshot / "meson.build").read_text(), "edited build\n")
            self.assertEqual((snapshot / "source/added.d").read_text(), "added\n")
            for name in ("deleted.d", "untracked-later.d", "missing.d", "scratch.d"):
                self.assertFalse((snapshot / "source" / name).exists(), name)
            self.assertTrue((repo / "source/untracked-later.d").is_file())
            self.assertTrue((repo / "source/scratch.d").is_file())


if __name__ == "__main__":
    unittest.main()
