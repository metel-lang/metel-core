#!/usr/bin/env python3
"""Self-test for tools/push_scope.py: builds real git repositories in a temp directory, no network."""

import os
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0, os.path.dirname(__file__))
import push_scope  # noqa: E402


def run(cwd, *args):
    env = dict(os.environ, GIT_AUTHOR_NAME="t", GIT_AUTHOR_EMAIL="t@t", GIT_COMMITTER_NAME="t", GIT_COMMITTER_EMAIL="t@t")
    return subprocess.run(["git", *args], cwd=cwd, env=env, check=True, capture_output=True, text=True).stdout.strip()


class PushScope(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.repo = self.tmp.name
        run(self.repo, "init", "-q", "-b", "develop")
        self.write("src/lib.rs", "fn main() {}\n")
        self.write("ROADMAP.md", "# roadmap\n")
        run(self.repo, "add", "-A")
        run(self.repo, "commit", "-q", "-m", "base")
        self.base = run(self.repo, "rev-parse", "HEAD")
        self.old = os.getcwd()
        os.chdir(self.repo)

    def tearDown(self):
        os.chdir(self.old)
        self.tmp.cleanup()

    def write(self, path, text):
        full = os.path.join(self.repo, path)
        os.makedirs(os.path.dirname(full), exist_ok=True)
        with open(full, "w") as f:
            f.write(text)

    def commit(self, *paths):
        for path in paths:
            self.write(path, f"changed {path}\n")
        run(self.repo, "add", "-A")
        run(self.repo, "commit", "-q", "-m", "change")
        return run(self.repo, "rev-parse", "HEAD")

    def line(self, local, remote=None):
        return f"refs/heads/b {local} refs/heads/b {remote or push_scope.ZERO}"

    def test_roadmap_only_is_docs_only(self):
        tip = self.commit("ROADMAP.md")
        self.assertTrue(push_scope.push_is_docs_only([self.line(tip, self.base)]))

    def test_process_documents_and_docs_dir_are_docs_only(self):
        tip = self.commit("AGENTS.md", "docs/x.md")
        self.assertTrue(push_scope.push_is_docs_only([self.line(tip, self.base)]))

    def test_code_change_is_code(self):
        tip = self.commit("ROADMAP.md", "src/lib.rs")
        self.assertFalse(push_scope.push_is_docs_only([self.line(tip, self.base)]))

    def test_readme_is_code(self):
        tip = self.commit("README.md")
        self.assertFalse(push_scope.push_is_docs_only([self.line(tip, self.base)]))

    def test_new_branch_is_measured_against_develop(self):
        run(self.repo, "checkout", "-q", "-b", "feature")
        tip = self.commit("ROADMAP.md")
        self.assertTrue(push_scope.push_is_docs_only([self.line(tip)]))
        tip = self.commit("src/lib.rs")
        self.assertFalse(push_scope.push_is_docs_only([self.line(tip)]))

    def test_gitlink_pin_is_docs_only(self):
        # A submodule bump changes the `docs` entry only.
        run(self.repo, "update-index", "--add", "--cacheinfo", f"160000,{self.base},docs")
        run(self.repo, "commit", "-q", "-m", "pin")
        tip = run(self.repo, "rev-parse", "HEAD")
        self.assertTrue(push_scope.push_is_docs_only([self.line(tip, self.base)]))

    def test_delete_is_docs_only_and_empty_input_is_code(self):
        delete = f"(delete) {push_scope.ZERO} refs/heads/b {self.base}"
        self.assertTrue(push_scope.push_is_docs_only([delete]))
        self.assertFalse(push_scope.push_is_docs_only([]))

    def test_unknown_base_is_code(self):
        tip = self.commit("ROADMAP.md")
        bogus = "1" * 40
        self.assertFalse(push_scope.push_is_docs_only([self.line(tip, bogus)]))

    def test_any_code_ref_makes_the_push_code(self):
        docs = self.commit("ROADMAP.md")
        run(self.repo, "checkout", "-q", "-b", "other", self.base)
        code = self.commit("src/lib.rs")
        lines = [self.line(docs, self.base), self.line(code, self.base)]
        self.assertFalse(push_scope.push_is_docs_only(lines))


if __name__ == "__main__":
    unittest.main()
