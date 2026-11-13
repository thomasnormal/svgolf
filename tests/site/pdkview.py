"""A page as the reader of one course sees it (the course selector, decided 2026-11-09; its second course since
2026-11-12 is ASAP7 placed and routed, `asap7pnr`): site/build.py puts every golf score on a page twice, in an element of
class `pdk-sky130` and one of class `pdk-asap7pnr`, and style.css shows the one <html data-pdk> names (sky130 without
JavaScript). `view_of(html, "sky130")` is the page without the `pdk-asap7pnr` elements, `view_of(html, "asap7pnr")`
without the `pdk-sky130` ones: what each reader has on screen. Written for the tests, independently of the generator
(no code of site/build.py is used)."""

import re

OTHER = {"sky130": "pdk-asap7pnr", "asap7pnr": "pdk-sky130"}
_OPEN = re.compile(r'<([a-zA-Z][a-zA-Z0-9]*)\b[^>]*\bclass="([^"]*)"[^>]*>')


def view_of(page_html, pdk):
    """`page_html` without every element whose class list holds the other library's class (its whole subtree, found
    by the nesting of its own tag name)."""
    drop = OTHER[pdk]
    out, at = [], 0
    pos = 0
    while True:
        m = next((m for m in _OPEN.finditer(page_html, pos) if drop in m.group(2).split()), None)
        if m is None:
            break
        tag = m.group(1)
        depth, end = 1, None
        for t in re.compile(rf"<(/?){tag}\b[^>]*>").finditer(page_html, m.end()):
            depth += -1 if t.group(1) else 1
            if depth == 0:
                end = t.end()
                break
        if end is None:
            raise AssertionError(f"<{tag} class={m.group(2)!r}> is not closed")
        out.append(page_html[at:m.start()])
        at = pos = end
    out.append(page_html[at:])
    return "".join(out)


def both_views(page_html):
    """{library: the page in its view} for both libraries."""
    return {pdk: view_of(page_html, pdk) for pdk in OTHER}
