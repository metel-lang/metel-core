import unittest
from pathlib import Path

from tools import check_no_copy_by_name as scan


class CopyByNameScan(unittest.TestCase):
    def test_flags_a_literal(self):
        self.assertEqual(scan.findings_in('if name == "Copy" {}', Path("x.rs")), [1])

    def test_ignores_diagnostic_text(self):
        self.assertEqual(scan.findings_in('format!("`Copy` is sealed")', Path("x.rs")), [])

    def test_allows_an_annotated_site(self):
        text = '// copy-by-name-allow: prelude-less path\nif name == "Copy" {}'
        self.assertEqual(scan.findings_in(text, Path("x.rs")), [])

    def test_stops_at_the_test_module(self):
        self.assertEqual(scan.findings_in('#[cfg(test)]\nmod t { "Copy" }', Path("x.rs")), [])

    def test_repository_is_clean(self):
        self.assertEqual(scan.scan(), [])


if __name__ == "__main__":
    unittest.main()
