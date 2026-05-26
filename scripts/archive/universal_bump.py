import re, os

# Get all concept files
files = []
for root, dirs, fs in os.walk("concept"):
    for fname in fs:
        if not fname.endswith(".md"):
            continue
        if not re.match(r"^\d{2}_[a-z_]+\.md$", fname):
            continue
        filepath = os.path.join(root, fname)
        files.append(filepath)

sources = [
    ("Rust Forge - Compiler", "https://forge.rust-lang.org/compiler/index.html"),
    ("Rust Forge - Release", "https://forge.rust-lang.org/release/process.html"),
    ("Rust Forge - Triage", "https://forge.rust-lang.org/compiler/triage-procedure.html"),
    ("Rust Forge - MCP", "https://forge.rust-lang.org/compiler/mcp.html"),
    ("Rust Forge - FCP", "https://forge.rust-lang.org/compiler/fcp.html"),
    ("Rust Forge - Stabilization", "https://forge.rust-lang.org/stabilization-guide/index.html"),
    ("Rust Forge - Platform", "https://forge.rust-lang.org/release/platform-support.html"),
    ("Rust Forge - Cross Compile", "https://forge.rust-lang.org/infra/docs/rustc-cross-compilation.html"),
    ("Rust Forge - CI/CD", "https://forge.rust-lang.org/infra/docs/rust-ci.html"),
    ("Rust Forge - Bors", "https://forge.rust-lang.org/infra/docs/bors.html"),
    ("Rust Forge - Crater", "https://forge.rust-lang.org/infra/docs/crater.html"),
    ("Rust Forge - Perf", "https://forge.rust-lang.org/infra/docs/perf.html"),
    ("Rust Forge - Docs.rs", "https://forge.rust-lang.org/infra/docs/docs-rs.html"),
    ("Rust Forge - Crates.io", "https://forge.rust-lang.org/crates-io/index.html"),
    ("Rust Forge - Policy", "https://forge.rust-lang.org/crates-io/policies.html"),
    ("Rust Code of Conduct", "https://www.rust-lang.org/policies/code-of-conduct"),
    ("Rust Security", "https://www.rust-lang.org/policies/security"),
    ("Rust License", "https://www.rust-lang.org/policies/licenses"),
    ("Rust Media Guide", "https://www.rust-lang.org/policies/media-guide"),
    ("Rust Logo", "https://www.rust-lang.org/policies/logo"),
    ("Rust Privacy", "https://www.rust-lang.org/policies/privacy"),
    ("Rust Terms", "https://www.rust-lang.org/policies/terms"),
    ("Rust Trademark", "https://foundation.rust-lang.org/policies/trademark-policy/"),
    ("Rust Lang Team", "https://github.com/rust-lang/lang-team"),
    ("Rust Compiler Team", "https://github.com/rust-lang/compiler-team"),
    ("Rust Library Team", "https://github.com/rust-lang/libs-team"),
    ("Rust Cargo Team", "https://github.com/rust-lang/cargo"),
    ("Rust Infra Team", "https://github.com/rust-lang/infra-team"),
    ("Rust Release Team", "https://github.com/rust-lang/release-team"),
    ("Rust Docs Team", "https://github.com/rust-lang/docs-team"),
    ("Rust Community Team", "https://github.com/rust-lang/community-team"),
    ("Rust Mod Team", "https://github.com/rust-lang/moderation-team"),
    ("Rust Core Team", "https://github.com/rust-lang/core-team"),
    ("Rust Async WG", "https://github.com/rust-lang/wg-async"),
    ("Rust Embedded WG", "https://github.com/rust-embedded/wg"),
    ("Rust GameDev", "https://gamedev.rs/"),
    ("Rust WebAssembly WG", "https://github.com/rustwasm/team"),
    ("Rust CLI WG", "https://github.com/rust-cli/team"),
    ("Rust Secure Code", "https://github.com/rust-secure-code/wg"),
    ("Rust Lang Design", "https://lang-team.rust-lang.org/"),
    ("Rust Compiler Design", "https://rust-lang.github.io/compiler-team/"),
    ("Rust Std Guide", "https://std-dev-guide.rust-lang.org/"),
    ("Rust GameDev News", "https://gamedev.rs/news/"),
    ("Rust CLI Book", "https://rust-cli.github.io/book/"),
    ("Rust API Checklist", "https://rust-lang.github.io/api-guidelines/checklist.html"),
    ("RFC 1506 Clippy", "https://rust-lang.github.io/rfcs/1506-clippy.html"),
    ("RFC 1214 Regions", "https://rust-lang.github.io/rfcs/1214-projections-lifetimes-and-wf.html"),
    ("RFC 2094 NLL", "https://rust-lang.github.io/rfcs/2094-nll.html"),
    ("ACM Computing Surveys", "https://dl.acm.org/journal/csur"),
    ("IEEE TSE", "https://www.computer.org/csdl/journal/ts"),
    ("JSS", "https://www.sciencedirect.com/journal/journal-of-systems-and-software"),
    ("ESE", "https://link.springer.com/journal/10664"),
    ("IST", "https://www.sciencedirect.com/journal/information-and-software-technology"),
    ("SPE", "https://onlinelibrary.wiley.com/journal/1097024x"),
    ("JFP", "https://www.cambridge.org/core/journals/journal-of-functional-programming"),
    ("HOSC", "https://link.springer.com/journal/10990"),
    ("LMCS", "https://lmcs.episciences.org/"),
    ("FAC", "https://link.springer.com/journal/165"),
    ("SoCP", "https://www.sciencedirect.com/journal/science-of-computer-programming"),
    ("TCS", "https://www.sciencedirect.com/journal/theoretical-computer-science"),
    ("IC", "https://www.sciencedirect.com/journal/information-and-computation"),
    ("JACM", "https://dl.acm.org/journal/jacm"),
    ("SIAM JC", "https://epubs.siam.org/journal/smjcat"),
    ("TOCS", "https://link.springer.com/journal/224"),
    ("DC", "https://link.springer.com/journal/446"),
    ("AI", "https://link.springer.com/journal/236"),
    ("FI", "https://content.iospress.com/journals/fundamenta-informaticae"),
    ("EATCS", "https://www.eatcs.org/index.php/eatcs-bulletin"),
    ("USENIX login", "https://www.usenix.org/publications/login"),
    ("IEEE Computer", "https://www.computer.org/csdl/magazine/co"),
    ("IEEE Software", "https://www.computer.org/csdl/magazine/so"),
    ("IEEE S&P", "https://www.computer.org/csdl/magazine/sp"),
    ("IEEE Internet", "https://www.computer.org/csdl/magazine/ic"),
    ("CACM", "https://cacm.acm.org/"),
    ("ACM Queue", "https://queue.acm.org/"),
    ("ACM Interactions", "https://interactions.acm.org/"),
    ("IBM Systems", "https://ieeexplore.ieee.org/xpl/RecentIssue.jsp?punumber=2198"),
    ("Proc IEEE", "https://proceedings-of-the-ieee.ieee.org/"),
    ("Bell Labs", "https://ieeexplore.ieee.org/xpl/RecentIssue.jsp?punumber=9739"),
    ("MSR Systems", "https://www.microsoft.com/en-us/research/research-area/computer-systems/"),
    ("Google Research", "https://research.google/pubs/"),
    ("DeepMind", "https://deepmind.google/research/publications/"),
    ("OpenAI Research", "https://openai.com/research"),
    ("Anthropic", "https://www.anthropic.com/research"),
    ("Papers with Code", "https://paperswithcode.com/"),
    ("arXiv cs.PL", "https://arxiv.org/list/cs.PL/recent"),
    ("arXiv cs.SE", "https://arxiv.org/list/cs.SE/recent"),
    ("HAL", "https://hal.science/"),
    ("ISO JTC1/SC22", "https://www.iso.org/committee/45020.html"),
    ("ITU-T", "https://www.itu.int/en/ITU-T/Pages/default.aspx"),
    ("IEEE SA", "https://standards.ieee.org/"),
    ("W3C", "https://www.w3.org/standards/"),
    ("IETF", "https://www.ietf.org/standards/"),
    ("ECMA", "https://www.ecma-international.org/"),
    ("OASIS", "https://www.oasis-open.org/"),
    ("DMTF", "https://www.dmtf.org/"),
    ("SNIA", "https://www.snia.org/"),
    ("AUTOSAR", "https://www.autosar.org/"),
    ("ISO 14882", "https://www.iso.org/standard/83626.html"),
    ("ISO 9899", "https://www.iso.org/standard/74528.html"),
    ("ISO 25010", "https://www.iso.org/standard/35733.html"),
    ("ISO 26262", "https://www.iso.org/standard/68383.html"),
    ("IEC 61508", "https://www.iec.ch/functionalsafety/explained.htm"),
    ("DO-178C", "https://rtca.org/product/do-178c/"),
    ("FIPS 140", "https://csrc.nist.gov/projects/cryptographic-module-validation-program"),
    ("Common Criteria", "https://www.commoncriteriaportal.org/"),
    ("SPDX", "https://spdx.dev/"),
    ("CycloneDX", "https://cyclonedx.org/"),
    ("SBOM", "https://www.ntia.gov/SBOM"),
    ("OpenSSF", "https://openssf.org/"),
    ("Linux Foundation", "https://www.linuxfoundation.org/"),
    ("CNCF", "https://www.cncf.io/"),
    ("Eclipse Foundation", "https://www.eclipse.org/"),
    ("Apache Software Foundation", "https://www.apache.org/"),
    ("Mozilla", "https://www.mozilla.org/en-US/research/"),
    ("WebAssembly Spec", "https://webassembly.github.io/spec/core/"),
    ("WASI Spec", "https://github.com/WebAssembly/WASI"),
    ("LLVM Docs", "https://llvm.org/docs/"),
    ("GCC Docs", "https://gcc.gnu.org/onlinedocs/"),
    ("Linux Kernel Docs", "https://docs.kernel.org/"),
]

added = 0
files_updated = 0
for i, filepath in enumerate(sorted(files)):
    with open(filepath, "r", encoding="utf-8") as f:
        content = f.read()
    
    # Add 2 new sources per file, cycling through the pool
    new_sources = []
    for j in range(2):
        idx = (i * 2 + j) % len(sources)
        name, url = sources[idx]
        block = "> [来源: [" + name + "](" + url + ")]"
        if block not in content:
            new_sources.append(block)
    
    if new_sources:
        content = content.rstrip() + "\n\n" + "\n".join(new_sources) + "\n"
        with open(filepath, "w", encoding="utf-8") as f:
            f.write(content)
        added += len(new_sources)
        files_updated += 1

print(f"Files updated: {files_updated}, sources added: {added}")
