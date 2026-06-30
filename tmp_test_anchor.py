import sys
sys.path.insert(0, 'scripts')
from fix_docs_links_correct import strip_inline_formatting, strip_explicit_anchor, unescape_md

text = "8.1 `#[doc]` 属性 {#81-doc-属性}"
heading = "8.1 `#[doc]` 属性"
link_key = strip_inline_formatting(unescape_md(strip_explicit_anchor(text).strip()))
heading_key = strip_inline_formatting(heading)
print("link key:", repr(link_key))
print("heading key:", repr(heading_key))
print("match:", link_key == heading_key)
