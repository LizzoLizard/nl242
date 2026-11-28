#!/usr/bin/env python3
"""Create a new version of the nl242 Zenodo record (same style as det3_zenodo_upload.py).

Token: $ZENODO_TOKEN or ~/.zenodo_token (never printed).

  python3 zenodo_new_version.py --draft          # new-version draft of record 24456946, replace files, set version
  python3 zenodo_new_version.py --publish ID     # publish draft ID (permanent DOI; cannot be deleted)
"""
import json, os, sys, urllib.request, urllib.error

HERE = os.path.dirname(os.path.abspath(__file__))
BASE = "https://zenodo.org/api"
LATEST_RECORD = "24456946"
FILES = [os.path.join(HERE, "nl242_release_v4.zip"), os.path.join(HERE, "nl242_paper_v4.pdf")]
VERSION = "v4"
NOTE = ("<p><strong>Version 4:</strong> presentation-only revision of the paper (paper/paper_v2.tex): "
        "shorter title and abstract, a roadmap table of all agreement counts t, Section 6.1 restructured by case, "
        "code identifiers removed from theorem headers, and a Declarations section added. "
        "No mathematical content changed. The submitted-manuscript source with the journal technical-check fixes "
        "is included as paper/paper_journal_r1.tex; the original paper/paper.tex is unchanged.</p>")


def token():
    t = os.environ.get("ZENODO_TOKEN")
    if not t:
        p = os.path.expanduser("~/.zenodo_token")
        if os.path.exists(p):
            t = open(p).read().strip()
    if not t:
        sys.exit("No token: set ZENODO_TOKEN or write it to ~/.zenodo_token")
    return t


def call(method, url, tok, body=None, raw=None, ctype="application/json"):
    data = raw if raw is not None else (json.dumps(body).encode() if body is not None else None)
    req = urllib.request.Request(url, data=data, method=method)
    req.add_header("Authorization", f"Bearer {tok}")
    if data is not None:
        req.add_header("Content-Type", ctype)
    try:
        with urllib.request.urlopen(req) as r:
            txt = r.read().decode()
            return json.loads(txt) if txt else {}
    except urllib.error.HTTPError as e:
        sys.exit(f"{method} {url.split('?')[0]} failed: HTTP {e.code}\n{e.read().decode()[:2000]}")


def main():
    a = sys.argv[1:]
    tok = token()
    if "--draft" in a:
        for f in FILES:
            if not os.path.exists(f):
                sys.exit(f"missing file: {f}")
        r = call("POST", f"{BASE}/deposit/depositions/{LATEST_RECORD}/actions/newversion", tok)
        draft_url = r["links"]["latest_draft"]
        dep = call("GET", draft_url, tok)
        dep_id = dep["id"]
        for f in dep.get("files", []):
            call("DELETE", f"{BASE}/deposit/depositions/{dep_id}/files/{f['id']}", tok)
            print("removed inherited file", f["filename"])
        bucket = dep["links"]["bucket"]
        for path in FILES:
            with open(path, "rb") as fh:
                call("PUT", f"{bucket}/{os.path.basename(path)}", tok, raw=fh.read(),
                     ctype="application/octet-stream")
            print("uploaded", os.path.basename(path))
        md = dep["metadata"]
        md["version"] = VERSION
        md.pop("doi", None)
        md.pop("prereserve_doi", None)
        md.pop("publication_date", None)
        if "Version 4:" not in md.get("description", ""):
            md["description"] = md.get("description", "") + NOTE
        dep = call("PUT", f"{BASE}/deposit/depositions/{dep_id}", tok, body={"metadata": md})
        print("DRAFT ready (not published).")
        print("  deposition id:", dep_id)
        print("  title:        ", dep["metadata"]["title"])
        print("  version:      ", dep["metadata"].get("version"))
        print("  files:        ", [f["filename"] for f in call("GET", f"{BASE}/deposit/depositions/{dep_id}/files", tok)])
        print("  preview:      ", dep["links"].get("html"))
    elif "--publish" in a:
        dep_id = a[a.index("--publish") + 1]
        r = call("POST", f"{BASE}/deposit/depositions/{dep_id}/actions/publish", tok)
        print("PUBLISHED. DOI:", r.get("doi"), " record:", r.get("links", {}).get("html"))
    else:
        sys.exit(__doc__)


if __name__ == "__main__":
    main()
