import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from tools import check_no_semantic_name_lookup as scanner


class SemanticNameLookupTests(unittest.TestCase):
    def scan_lines(self, text):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            path = root / "example.rs"
            path.write_text(text)
            with patch.object(scanner, "REPO_ROOT", root), patch.object(scanner, "SCAN_FILES", [path]):
                return scanner.scan()

    def test_sets_and_nested_sets_are_detected(self):
        findings = self.scan_lines(
            "owned: Vec<HashSet<String>>,\n"
            "nested: HashMap<BindingId, HashSet<Span>>,\n"
            "safe: HashSet<BindingId>,\n"
            "values: HashMap<BindingId, String>,\n"
            "// HashSet<String> is only a comment\n"
        )
        self.assertEqual([(line, key) for _, line, _, key in findings], [(1, "String"), (2, "Span")])

    def test_maps_and_justified_sets(self):
        findings = self.scan_lines(
            "map: HashMap<Vec<String>, i32>,\n"
            "// resolution-freeze-allow: scoped names only\n"
            "scoped: HashSet<String>,\n"
            "other: BTreeMap<Span, i32>, // resolution-freeze-allow: position index\n"
        )
        self.assertEqual([(line, key) for _, line, _, key in findings], [(1, "Vec<String>")])


if __name__ == "__main__":
    unittest.main()
