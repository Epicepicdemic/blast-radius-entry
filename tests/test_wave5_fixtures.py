"""A JSON fixture receipt must observe the reconstructed bytes on the opened path."""
import json
import os
from pathlib import Path
from types import SimpleNamespace

from fixture_overlay import Fixtures


def test_json_postimage_is_opened(tmp_path, monkeypatch):
    original = tmp_path / 'tests/fixtures/example.json'
    original.parent.mkdir(parents=True)
    original.write_text('{"answer": 1}')
    change = SimpleNamespace(path='tests/fixtures/example.json', after=b'{"answer": 2}')
    fs = Fixtures(tmp_path, [change])
    assert set(fs.files) == {str(original)} and not fs.seen
    import builtins
    import io
    monkeypatch.setattr(builtins, 'open', builtins.open)
    monkeypatch.setattr(io, 'open', io.open)
    try:
        fs.install()
        with original.open() as stream:
            assert json.load(stream) == {'answer': 2}
        assert fs.seen == {str(original)}
    finally:
        for path in fs.files.values():
            os.close(int(Path(path).name))
