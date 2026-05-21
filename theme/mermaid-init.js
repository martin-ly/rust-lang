// Mermaid initialization for mdBook
// Scans for mermaid code blocks and renders them as diagrams

document.addEventListener('DOMContentLoaded', function() {
    mermaid.initialize({
        startOnLoad: false,
        theme: 'default',
        securityLevel: 'loose',
        flowchart: { useMaxWidth: true, htmlLabels: true, curve: 'basis' },
        sequence: { useMaxWidth: true },
        gantt: { useMaxWidth: true },
        mindmap: { useMaxWidth: true },
    });

    // Find all mermaid code blocks and render them
    const mermaidBlocks = document.querySelectorAll('pre code.language-mermaid');
    mermaidBlocks.forEach(function(block, index) {
        const pre = block.parentElement;
        const code = block.textContent;
        const id = 'mermaid-' + index;

        // Create container for mermaid diagram
        const container = document.createElement('div');
        container.className = 'mermaid';
        container.id = id;
        container.textContent = code;

        // Replace the pre block with the mermaid container
        pre.parentElement.replaceChild(container, pre);
    });

    // Run mermaid rendering
    mermaid.run({ querySelector: '.mermaid' });
});
