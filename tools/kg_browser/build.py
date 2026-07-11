#!/usr/bin/env python3
"""
构建可直接在浏览器打开的 KG 浏览器。

将 kg_data_v3.json 和 kg_links.json 内嵌到单个 index.html 中，
避免 file:// 协议下的 CORS 限制。
"""
from __future__ import annotations

import html
import json
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent.parent.parent
KG_PATH = ROOT / "concept" / "00_meta" / "kg_data_v3.json"
LINKS_PATH = ROOT / "tools" / "kg_browser" / "kg_links.json"
OUT_PATH = ROOT / "tools" / "kg_browser" / "index.html"


def load_json(path: Path) -> Any:
    with open(path, "r", encoding="utf-8") as f:
        return json.load(f)


def short_id(uri: str) -> str:
    return uri.removeprefix("ex:")


def build_html(kg: dict[str, Any], links: dict[str, str | None]) -> str:
    kg_json = json.dumps(kg, ensure_ascii=False)
    links_json = json.dumps(links, ensure_ascii=False)

    return f"""<!DOCTYPE html>
<html lang="zh-CN">
<head>
  <meta charset="UTF-8" />
  <meta name="viewport" content="width=device-width, initial-scale=1.0" />
  <title>Rust 知识图谱浏览器</title>
  <script src="https://d3js.org/d3.v7.min.js"></script>
  <style>
    :root {{
      --bg: #f8f9fa;
      --panel: #ffffff;
      --text: #212529;
      --muted: #6c757d;
      --border: #dee2e6;
      --concept: #0d6efd;
      --theory: #6610f2;
      --property: #198754;
      --rule: #dc3545;
      --depends: #6c757d;
      --equivalent: #198754;
      --mutex: #dc3545;
    }}
    * {{ box-sizing: border-box; }}
    body {{
      margin: 0;
      font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, "Helvetica Neue", Arial, sans-serif;
      background: var(--bg);
      color: var(--text);
      display: flex;
      height: 100vh;
      overflow: hidden;
    }}
    #graph {{
      flex: 1;
      position: relative;
    }}
    #graph svg {{ width: 100%; height: 100%; }}
    #sidebar {{
      width: 360px;
      background: var(--panel);
      border-left: 1px solid var(--border);
      padding: 1rem;
      overflow-y: auto;
      box-shadow: -2px 0 8px rgba(0,0,0,0.05);
    }}
    h1 {{ font-size: 1.25rem; margin: 0 0 0.75rem; }}
    h2 {{ font-size: 1rem; margin: 1.25rem 0 0.5rem; }}
    .controls {{
      background: var(--bg);
      border-radius: 0.5rem;
      padding: 0.75rem;
      margin-bottom: 1rem;
    }}
    .controls label {{
      display: flex;
      align-items: center;
      gap: 0.5rem;
      margin: 0.35rem 0;
      cursor: pointer;
      font-size: 0.9rem;
    }}
    .controls input[type="checkbox"] {{ cursor: pointer; }}
    .legend-dot {{
      display: inline-block;
      width: 10px; height: 10px;
      border-radius: 50%;
      margin-right: 0.35rem;
    }}
    #search {{
      width: 100%;
      padding: 0.5rem;
      border: 1px solid var(--border);
      border-radius: 0.375rem;
      font-size: 0.9rem;
    }}
    .node circle {{
      stroke: #fff;
      stroke-width: 2px;
      cursor: pointer;
      transition: all 0.2s;
    }}
    .node:hover circle {{ stroke: #000; stroke-width: 3px; }}
    .node text {{
      font-size: 11px;
      pointer-events: none;
      text-shadow: 0 1px 3px rgba(255,255,255,0.8);
    }}
    .link {{
      stroke-opacity: 0.7;
      transition: stroke-opacity 0.2s;
    }}
    .link.dependsOn {{ stroke: var(--depends); }}
    .link.equivalentTo {{ stroke: var(--equivalent); stroke-dasharray: 5,5; }}
    .link.mutexWith {{ stroke: var(--mutex); stroke-dasharray: 2,2; }}
    .link.appliesTo {{ stroke: #fd7e14; }}
    .link.entails {{ stroke: #0dcaf0; }}
    .link.refines {{ stroke: #6f42c1; }}
    .link.instanceOf {{ stroke: #20c997; }}
    .link.counterExample {{ stroke: #d63384; }}

    #details {{
      font-size: 0.9rem;
      line-height: 1.5;
    }}
    #details .empty {{ color: var(--muted); font-style: italic; }}
    #details dt {{ font-weight: 600; margin-top: 0.75rem; }}
    #details dd {{ margin: 0.25rem 0 0; color: var(--text); }}
    #details .badge {{
      display: inline-block;
      padding: 0.15rem 0.5rem;
      border-radius: 999px;
      background: var(--bg);
      border: 1px solid var(--border);
      font-size: 0.8rem;
      margin-right: 0.35rem;
    }}
    #details a {{
      color: var(--concept);
      text-decoration: none;
    }}
    #details a:hover {{ text-decoration: underline; }}
    .stats {{
      font-size: 0.8rem;
      color: var(--muted);
      margin-top: 0.5rem;
    }}
  </style>
</head>
<body>
  <div id="graph"></div>
  <aside id="sidebar">
    <h1>🦀 Rust 知识图谱浏览器</h1>
    <div class="controls">
      <label>
        <input type="text" id="search" placeholder="搜索 concept..." />
      </label>
      <h2>关系过滤</h2>
      <label><input type="checkbox" class="filter" value="dependsOn" checked /> <span class="legend-dot" style="background:var(--depends)"></span>dependsOn</label>
      <label><input type="checkbox" class="filter" value="equivalentTo" checked /> <span class="legend-dot" style="background:var(--equivalent)"></span>equivalentTo</label>
      <label><input type="checkbox" class="filter" value="mutexWith" checked /> <span class="legend-dot" style="background:var(--mutex)"></span>mutexWith</label>
      <label><input type="checkbox" class="filter" value="appliesTo" checked /> <span class="legend-dot" style="background:#fd7e14"></span>appliesTo</label>
      <label><input type="checkbox" class="filter" value="entails" checked /> <span class="legend-dot" style="background:#0dcaf0"></span>entails</label>
      <label><input type="checkbox" class="filter" value="refines" checked /> <span class="legend-dot" style="background:#6f42c1"></span>refines</label>
      <label><input type="checkbox" class="filter" value="instanceOf" checked /> <span class="legend-dot" style="background:#20c997"></span>instanceOf</label>
      <label><input type="checkbox" class="filter" value="counterExample" checked /> <span class="legend-dot" style="background:#d63384"></span>counterExample</label>
      <label><input type="checkbox" class="filter" value="relatedTo" checked /> <span class="legend-dot" style="background:#adb5bd"></span>relatedTo</label>
      <h2>图例</h2>
      <div><span class="legend-dot" style="background:var(--concept)"></span>Concept</div>
      <div><span class="legend-dot" style="background:var(--theory)"></span>Theory</div>
      <div><span class="legend-dot" style="background:var(--property)"></span>Property</div>
      <div><span class="legend-dot" style="background:var(--rule)"></span>Rule</div>
      <div class="stats" id="stats"></div>
    </div>
    <div id="details">
      <p class="empty">点击节点查看详情</p>
    </div>
  </aside>

  <script>
    const kgData = {kg_json};
    const linksMap = {links_json};

    function getLang(values, lang) {{
      if (!Array.isArray(values)) return "";
      const v = values.find(x => x["@language"] === lang);
      return v ? v["@value"] : "";
    }}

    function shortId(uri) {{
      return uri.replace(/^ex:/, "");
    }}

    function predicateShort(uri) {{
      return uri.replace(/^ex:/, "");
    }}

    // Flatten entities from v3 flat list.
    function inferCategory(types) {{
      if (!Array.isArray(types)) types = [types];
      if (types.includes("ex:Theory")) return "theories";
      if (types.includes("ex:Property")) return "properties";
      if (types.includes("ex:Rule")) return "rules";
      if (types.includes("ex:Model")) return "concepts";
      return "concepts";
    }}

    const nodes = [];
    const nodeById = {{}};
    for (const item of kgData.entities || []) {{
      const id = item["@id"];
      const category = inferCategory(item["@type"]);
      const node = {{
        id,
        shortId: shortId(id),
        category,
        label: getLang(item["skos:prefLabel"], "en") || shortId(id),
        labelZh: getLang(item["skos:prefLabel"], "zh"),
        definition: getLang(item["skos:scopeNote"], "en") || getLang(item["skos:scopeNote"], "zh"),
        definitionZh: "",
        layer: item["ex:layer"] || "",
        bloom: item["ex:bloomLevel"] || "",
        asp: item["ex:asp"] || "",
        markdown: linksMap[id] || null,
      }};
      nodes.push(node);
      nodeById[id] = node;
    }}

    // Build links.
    const allLinks = (kgData.relations || []).map(rel => ({{
      source: rel["ex:subject"],
      target: rel["ex:object"],
      predicate: rel["ex:predicate"],
      predicateShort: predicateShort(rel["ex:predicate"]),
      sourceRef: rel["ex:source"] || "",
      confidence: rel["ex:confidence"],
    }})).filter(l => nodeById[l.source] && nodeById[l.target]);

    // D3 setup.
    const container = document.getElementById("graph");
    const width = container.clientWidth;
    const height = container.clientHeight;

    const svg = d3.select("#graph").append("svg")
      .attr("viewBox", [0, 0, width, height]);

    svg.append("defs").append("marker")
      .attr("id", "arrow")
      .attr("viewBox", "0 -5 10 10")
      .attr("refX", 22)
      .attr("refY", 0)
      .attr("markerWidth", 6)
      .attr("markerHeight", 6)
      .attr("orient", "auto")
      .append("path")
      .attr("d", "M0,-5L10,0L0,5")
      .attr("fill", "#999");

    const g = svg.append("g");
    svg.call(d3.zoom().on("zoom", (event) => {{
      g.attr("transform", event.transform);
    }}));

    const colorScale = {{
      concepts: "var(--concept)",
      theories: "var(--theory)",
      properties: "var(--property)",
      rules: "var(--rule)",
    }};

    const simulation = d3.forceSimulation(nodes)
      .force("link", d3.forceLink(allLinks).id(d => d.id).distance(140))
      .force("charge", d3.forceManyBody().strength(-400))
      .force("center", d3.forceCenter(width / 2, height / 2))
      .force("collide", d3.forceCollide().radius(35));

    let linkSel = g.append("g").attr("class", "links").selectAll("line");
    let nodeSel = g.append("g").attr("class", "nodes").selectAll("g");

    function render(activePredicates) {{
      const visibleLinks = allLinks.filter(l => activePredicates.has(l.predicateShort));

      linkSel = linkSel.data(visibleLinks, d => d.source.id + "-" + d.target.id + "-" + d.predicate);
      linkSel.exit().remove();
      const linkEnter = linkSel.enter().append("line")
        .attr("class", d => "link " + d.predicateShort)
        .attr("stroke-width", 2)
        .attr("marker-end", d => d.predicateShort === "dependsOn" ? "url(#arrow)" : null);
      linkSel = linkEnter.merge(linkSel);

      nodeSel = nodeSel.data(nodes, d => d.id);
      nodeSel.exit().remove();
      const nodeEnter = nodeSel.enter().append("g")
        .attr("class", "node")
        .call(d3.drag()
          .on("start", dragstarted)
          .on("drag", dragged)
          .on("end", dragended));

      nodeEnter.append("circle")
        .attr("r", d => d.category === "concepts" ? 10 : 8)
        .attr("fill", d => colorScale[d.category] || "#888");

      nodeEnter.append("text")
        .attr("dx", 14)
        .attr("dy", 4)
        .text(d => d.shortId);

      nodeEnter.on("click", (event, d) => showDetails(d));
      nodeSel = nodeEnter.merge(nodeSel);

      simulation.nodes(nodes).on("tick", ticked);
      simulation.force("link").links(visibleLinks);
      simulation.alpha(1).restart();

      document.getElementById("stats").textContent =
        `节点 ${{nodes.length}} | 显示关系 ${{visibleLinks.length}} / ${{allLinks.length}}`;
    }}

    function ticked() {{
      linkSel
        .attr("x1", d => d.source.x)
        .attr("y1", d => d.source.y)
        .attr("x2", d => d.target.x)
        .attr("y2", d => d.target.y);

      nodeSel
        .attr("transform", d => `translate(${{d.x}},${{d.y}})`);
    }}

    function dragstarted(event, d) {{
      if (!event.active) simulation.alphaTarget(0.3).restart();
      d.fx = d.x; d.fy = d.y;
    }}
    function dragged(event, d) {{
      d.fx = event.x; d.fy = event.y;
    }}
    function dragended(event, d) {{
      if (!event.active) simulation.alphaTarget(0);
      d.fx = null; d.fy = null;
    }}

    function showDetails(d) {{
      const mdLink = d.markdown
        ? `<a href="../../${{d.markdown}}" target="_blank">${{d.markdown}}</a>`
        : "<span class='muted'>未匹配到 Markdown</span>";
      const html = `
        <h2>${{d.label}}</h2>
        <dl>
          <dt>ID</dt><dd>${{d.shortId}}</dd>
          <dt>类别</dt><dd><span class="badge">${{d.category}}</span></dd>
          ${{
            d.labelZh ? `<dt>中文标签</dt><dd>${{d.labelZh}}</dd>` : ""
          }}
          ${{
            d.layer ? `<dt>层级</dt><dd><span class="badge">${{d.layer}}</span></dd>` : ""
          }}
          ${{
            d.bloom ? `<dt>Bloom</dt><dd><span class="badge">${{d.bloom}}</span></dd>` : ""
          }}
          ${{
            d.asp ? `<dt>ASP</dt><dd><span class="badge">${{d.asp}}</span></dd>` : ""
          }}
          <dt>定义（EN）</dt><dd>${{d.definition || "—"}}</dd>
          ${{
            d.definitionZh ? `<dt>定义（ZH）</dt><dd>${{d.definitionZh}}</dd>` : ""
          }}
          <dt>对应 Markdown</dt><dd>${{mdLink}}</dd>
        </dl>
        <h2>相关关系</h2>
        <ul>
          ${{
            allLinks
              .filter(l => l.source.id === d.id || l.target.id === d.id)
              .map(l => {{
                const isSrc = l.source.id === d.id;
                const other = isSrc ? l.target : l.source;
                return `<li>${{isSrc ? "→" : "←"}} <strong>${{l.predicateShort}}</strong> ${{
                  other.label}} (${{other.shortId}}) ${{l.confidence !== undefined ? `[置信度 ${{l.confidence}}]` : ""}}</li>`;
              }}).join("")
          }}
        </ul>
      `;
      document.getElementById("details").innerHTML = html;
    }}

    // Filter handling.
    function getActivePredicates() {{
      return new Set(Array.from(document.querySelectorAll(".filter:checked")).map(cb => cb.value));
    }}
    document.querySelectorAll(".filter").forEach(cb => {{
      cb.addEventListener("change", () => render(getActivePredicates()));
    }});

    // Search handling.
    document.getElementById("search").addEventListener("input", (e) => {{
      const term = e.target.value.toLowerCase();
      nodeSel.selectAll("circle").attr("stroke", d => {{
        const match = !term ||
          d.label.toLowerCase().includes(term) ||
          d.shortId.toLowerCase().includes(term) ||
          (d.labelZh && d.labelZh.toLowerCase().includes(term));
        return match ? "#000" : "#fff";
      }}).attr("stroke-width", d => {{
        const match = !term ||
          d.label.toLowerCase().includes(term) ||
          d.shortId.toLowerCase().includes(term) ||
          (d.labelZh && d.labelZh.toLowerCase().includes(term));
        return match ? 4 : 2;
      }});
    }});

    render(getActivePredicates());
  </script>
</body>
</html>
"""


def main() -> int:
    kg = load_json(KG_PATH)
    links = load_json(LINKS_PATH)
    html = build_html(kg, links)
    OUT_PATH.write_text(html, encoding="utf-8")
    print(f"[build_browser] Wrote {OUT_PATH}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
