#!/usr/bin/env python3
"""Self-tests for tools/sweep_pub.py (metel-core#1849). Run: python3 tools/test_sweep_pub.py"""

import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import sweep_pub as sp  # noqa: E402


class SweepMetel(unittest.TestCase):
    def test_rewrites_the_keyword_at_every_declaration_site(self):
        src = "public struct P { public x: i64 }\npublic fun f() {}\npublic copy struct Q {}\n"
        new, n = sp.sweep_metel(src)
        self.assertEqual(new, "pub struct P { pub x: i64 }\npub fun f() {}\npub copy struct Q {}\n")
        self.assertEqual(n, 4)

    def test_identifiers_containing_the_word_are_untouched(self):
        src = "fun public_api() {}\nlet is_public := 1;\nlet publicity := 2;\nlet x_public := 3;\n"
        self.assertEqual(sp.sweep_metel(src), (src, 0))

    def test_plain_comment_prose_is_untouched(self):
        src = "// public fun in a comment\n/* public\n   struct */\npublic fun f() {}\n"
        new, n = sp.sweep_metel(src)
        self.assertEqual(n, 1)
        self.assertIn("// public fun in a comment", new)
        self.assertIn("/* public\n   struct */", new)
        self.assertIn("\npub fun f() {}", new)

    def test_inline_code_spans_in_comments_are_rewritten(self):
        src = "// A `public` field and a `public fun f` and the public API.\n/* see `public struct S` */\nfun f() {}\n"
        new, n = sp.sweep_metel(src)
        self.assertEqual(n, 3)
        self.assertEqual(new, "// A `pub` field and a `pub fun f` and the public API.\n/* see `pub struct S` */\nfun f() {}\n")

    def test_comment_spans_that_only_mention_the_word_are_untouched(self):
        src = "// a `public_api` helper and `publicly`\nfun f() {}\n"
        self.assertEqual(sp.sweep_metel(src), (src, 0))

    def test_strings_and_interpolation_are_untouched(self):
        src = 'let s := "a public b";\nlet t := "x ${f("public")} y";\npublic fun g() {}\n'
        new, n = sp.sweep_metel(src)
        self.assertEqual(n, 1)
        self.assertIn('"a public b"', new)
        self.assertIn('"x ${f("public")} y"', new)

    def test_escaped_quote_does_not_end_the_string(self):
        src = 'let s := "say \\"public\\" now";\npublic fun g() {}\n'
        new, n = sp.sweep_metel(src)
        self.assertEqual(n, 1)
        self.assertIn('"say \\"public\\" now"', new)

    def test_char_literals_and_anchors(self):
        src = "let c := 'p';\nlet d := '\\n';\nfun f<'a>(x: &'a i64) {}\npublic fun g() {}\n"
        new, n = sp.sweep_metel(src)
        self.assertEqual(n, 1)
        self.assertTrue(new.endswith("pub fun g() {}\n"))

    def test_crlf_is_preserved(self):
        src = "public fun f() {}\r\n// public\r\npublic struct S {}\r\n"
        new, n = sp.sweep_metel(src)
        self.assertEqual(new, "pub fun f() {}\r\n// public\r\npub struct S {}\r\n")
        self.assertEqual(n, 2)

    def test_idempotent(self):
        once, _ = sp.sweep_metel("public fun f() {}\n")
        self.assertEqual(sp.sweep_metel(once), (once, 0))


class SweepMarkdown(unittest.TestCase):
    def test_metel_fence_is_swept_and_other_fences_are_not(self):
        text = (
            "Intro public text.\n\n"
            "```metel\npublic fun f() {}\n```\n\n"
            "```rust\npublic fn f() {}\n```\n\n"
            "```text\npublic\n```\n"
        )
        new, fence, inline, untagged = sp.sweep_markdown(text)
        self.assertEqual((fence, inline, untagged), (1, 0, 0))
        self.assertIn("```metel\npub fun f() {}\n```", new)
        self.assertIn("```rust\npublic fn f() {}\n```", new)
        self.assertIn("```text\npublic\n```", new)
        self.assertIn("Intro public text.", new)

    def test_english_prose_is_untouched_but_inline_code_spans_are_swept(self):
        text = "The public API is annotated with `public`, as in `public fun f` or `public struct S { }`.\n"
        new, fence, inline, _ = sp.sweep_markdown(text)
        self.assertEqual(inline, 3)
        self.assertEqual(
            new,
            "The public API is annotated with `pub`, as in `pub fun f` or `pub struct S { }`.\n",
        )

    def test_inline_spans_that_merely_mention_the_word_are_untouched(self):
        text = "A `public_api` helper and a `publicly` named thing and `public x` are not keywords.\n"
        new, _, inline, _ = sp.sweep_markdown(text)
        self.assertEqual((new, inline), (text, 0))

    def test_no_inline_flag(self):
        text = "Use `public` here.\n"
        new, _, inline, _ = sp.sweep_markdown(text, inline=False)
        self.assertEqual((new, inline), (text, 0))

    def test_untagged_fence_is_reported_not_rewritten(self):
        text = "```\npublic fun f() {}\n```\n"
        new, fence, inline, untagged = sp.sweep_markdown(text)
        self.assertEqual((new, fence, untagged), (text, 0, 1))

    def test_fence_inside_longer_fence_and_tilde_fences(self):
        text = "~~~metel\npublic fun f() {}\n~~~\n\n````metel\npublic fun g() {}\n````\n"
        new, fence, _, _ = sp.sweep_markdown(text)
        self.assertEqual(fence, 2)
        self.assertEqual(new, "~~~metel\npub fun f() {}\n~~~\n\n````metel\npub fun g() {}\n````\n")

    def test_crlf_in_markdown(self):
        text = "Use `public`.\r\n```metel\r\npublic fun f() {}\r\n```\r\n"
        new, fence, inline, _ = sp.sweep_markdown(text)
        self.assertEqual(new, "Use `pub`.\r\n```metel\r\npub fun f() {}\r\n```\r\n")
        self.assertEqual((fence, inline), (1, 1))


class Cli(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)

    def tearDown(self):
        self.tmp.cleanup()

    def put(self, rel, text):
        p = self.root / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        with open(p, "w", encoding="utf-8", newline="") as f:
            f.write(text)
        return p

    def test_dry_run_changes_nothing_and_apply_rewrites(self):
        f = self.put("a/b.mtl", "public fun f() {}\n")
        self.assertEqual(sp.main([str(self.root)]), 0)
        self.assertEqual(f.read_text(), "public fun f() {}\n")
        self.assertEqual(sp.main(["--apply", str(self.root)]), 0)
        self.assertEqual(f.read_text(), "pub fun f() {}\n")

    def test_check_fails_until_swept(self):
        self.put("a.mtl", "public fun f() {}\n")
        self.assertEqual(sp.main(["--check", str(self.root)]), 1)
        sp.main(["--apply", str(self.root)])
        self.assertEqual(sp.main(["--check", str(self.root)]), 0)

    def test_default_excludes_leave_dated_documents_alone(self):
        keep = self.put("release-notes/changelog.md", "```metel\npublic fun f() {}\n```\n")
        keep2 = self.put("rfcs/6-refused/rfc-0001.md", "```metel\npublic fun f() {}\n```\n")
        keep3 = self.put("architecture/decisions/adr-1.md", "Use `public`.\n")
        swept = self.put("rfcs/1-under-review/rfc-0002.md", "```metel\npublic fun f() {}\n```\n")
        sp.main(["--apply", str(self.root)])
        for p in (keep, keep2, keep3):
            self.assertIn("public", p.read_text())
        self.assertIn("pub fun", swept.read_text())

    def test_no_default_excludes(self):
        f = self.put("release-notes/x.md", "```metel\npublic fun f() {}\n```\n")
        sp.main(["--apply", "--no-default-excludes", str(self.root)])
        self.assertIn("pub fun", f.read_text())

    def test_other_file_kinds_are_not_touched(self):
        f = self.put("t.toml", 'contains = "public field `x`"\n')
        g = self.put("lib.rs", 'let s = "public fun f() {}";\n')
        sp.main(["--apply", str(self.root)])
        self.assertIn("public", f.read_text())
        self.assertIn("public", g.read_text())

    def test_report_rust_lists_candidates_without_changing_them(self):
        g = self.put("lib.rs", 'let s = "public fun f() {}";\nlet t = "a public thing";\n')
        self.assertEqual(sp.main(["--report-rust", str(self.root)]), 0)
        self.assertIn("public fun", g.read_text())


if __name__ == "__main__":
    unittest.main()
