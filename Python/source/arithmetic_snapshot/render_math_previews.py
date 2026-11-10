"""Keep generated Markdown readable in viewers without a math renderer."""
from pathlib import Path
import shutil
import subprocess


def render(paths):
    node=shutil.which("node")
    if not node:
        bundled=(Path.home()/".cache/codex-runtimes/codex-primary-runtime/"
                 "dependencies/node/bin/node.exe")
        if bundled.exists():
            node=str(bundled)
    if not node:
        raise RuntimeError("Node.js is required for local formula previews.")
    script=Path(__file__).with_suffix(".cjs")
    subprocess.run([node,str(script),*[str(Path(p).resolve()) for p in paths]],check=True)
