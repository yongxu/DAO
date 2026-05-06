(function () {
  const data = window.SSBX_DATA;

  if (!data) {
    document.body.innerHTML = '<main class="empty-state">缺少 web/data.js。</main>';
    return;
  }

  const els = {
    searchInput: document.getElementById('searchInput'),
    modeTabs: Array.from(document.querySelectorAll('.mode-tab')),
    itemList: document.getElementById('itemList'),
    sectionLabel: document.getElementById('sectionLabel'),
    contentTitle: document.getElementById('contentTitle'),
    contentMeta: document.getElementById('contentMeta'),
    statsGrid: document.getElementById('statsGrid'),
    diagramView: document.getElementById('diagramView'),
    textView: document.getElementById('textView'),
    formalView: document.getElementById('formalView'),
    diagramPath: document.getElementById('diagramPath'),
    diagramViewport: document.getElementById('diagramViewport'),
    diagramCanvas: document.getElementById('diagramCanvas'),
    diagramImage: document.getElementById('diagramImage'),
    diagramSource: document.getElementById('diagramSource'),
    markdownContent: document.getElementById('markdownContent'),
    formalContent: document.getElementById('formalContent'),
    zoomOut: document.getElementById('zoomOut'),
    zoomReset: document.getElementById('zoomReset'),
    zoomFit: document.getElementById('zoomFit'),
    zoomIn: document.getElementById('zoomIn')
  };

  const collections = {
    diagrams: data.diagrams || [],
    texts: data.texts || [],
    formal: data.formal || []
  };

  const modeLabels = {
    diagrams: '图谱',
    texts: '文本',
    formal: '形式'
  };

  const state = {
    mode: 'diagrams',
    query: '',
    selected: {
      diagrams: collections.diagrams[0]?.id,
      texts: collections.texts[0]?.id,
      formal: collections.formal[0]?.id
    },
    zoom: 1
  };

  function formatNumber(value) {
    return new Intl.NumberFormat('zh-CN').format(value || 0);
  }

  function escapeHtml(value) {
    return String(value)
      .replaceAll('&', '&amp;')
      .replaceAll('<', '&lt;')
      .replaceAll('>', '&gt;')
      .replaceAll('"', '&quot;')
      .replaceAll("'", '&#39;');
  }

  function stat(label, value) {
    return `<div class="stat"><strong>${formatNumber(value)}</strong><span>${label}</span></div>`;
  }

  function renderStats() {
    const textLines = collections.texts.reduce((sum, item) => sum + item.lines, 0);
    const formalLines = collections.formal.reduce((sum, item) => sum + item.lines, 0);
    const diagramEdges = collections.diagrams.reduce((sum, item) => sum + item.edges, 0);

    els.statsGrid.innerHTML = [
      stat('文本', collections.texts.length),
      stat('图谱', collections.diagrams.length),
      stat('形式文件', collections.formal.length),
      stat('图边', diagramEdges),
      stat('文本行', textLines),
      stat('形式行', formalLines),
      stat('Mermaid 行', collections.diagrams.reduce((sum, item) => sum + item.lines, 0)),
      stat('本地文件', data.meta?.fileCount || 0)
    ].join('');
  }

  function searchableText(item) {
    return [item.title, item.path, item.summary, item.content].filter(Boolean).join('\n').toLowerCase();
  }

  function currentItems() {
    const query = state.query.trim().toLowerCase();
    const items = collections[state.mode] || [];
    if (!query) return items;
    return items.filter((item) => searchableText(item).includes(query));
  }

  function itemMeta(item) {
    if (state.mode === 'diagrams') {
      return `${formatNumber(item.nodes)} 节点 / ${formatNumber(item.edges)} 边 / ${formatNumber(item.lines)} 行`;
    }
    return `${formatNumber(item.lines)} 行 / ${formatNumber(item.words)} 字符`;
  }

  function renderList() {
    const items = currentItems();
    const selectedId = state.selected[state.mode];

    if (!items.length) {
      els.itemList.innerHTML = '<div class="empty-state">没有匹配项。</div>';
      return;
    }

    els.itemList.innerHTML = items.map((item) => {
      const active = item.id === selectedId ? ' is-active' : '';
      return `
        <button class="list-item${active}" type="button" data-id="${escapeHtml(item.id)}">
          <span class="item-title">${escapeHtml(item.title)}</span>
          <span class="item-path">${escapeHtml(item.path)}</span>
          <span class="item-meta">${escapeHtml(itemMeta(item))}</span>
        </button>
      `;
    }).join('');

    Array.from(els.itemList.querySelectorAll('.list-item')).forEach((button) => {
      button.addEventListener('click', () => {
        state.selected[state.mode] = button.dataset.id;
        render();
      });
    });
  }

  function selectFirstVisibleIfNeeded() {
    const items = currentItems();
    const selectedId = state.selected[state.mode];
    if (!items.some((item) => item.id === selectedId)) {
      state.selected[state.mode] = items[0]?.id;
    }
  }

  function activeItem() {
    const selectedId = state.selected[state.mode];
    return (collections[state.mode] || []).find((item) => item.id === selectedId);
  }

  function showView(mode) {
    els.diagramView.hidden = mode !== 'diagrams';
    els.textView.hidden = mode !== 'texts';
    els.formalView.hidden = mode !== 'formal';
  }

  function setHeader(item) {
    els.sectionLabel.textContent = modeLabels[state.mode];
    els.contentTitle.textContent = item?.title || modeLabels[state.mode];
    els.contentMeta.textContent = item ? `${item.path} · ${itemMeta(item)}` : '';
  }

  function setZoom(value) {
    const item = activeItem();
    if (!item || state.mode !== 'diagrams') return;

    state.zoom = Math.max(0.01, Math.min(5, value));
    const width = Math.max(1, Math.round((item.width || 1200) * state.zoom));
    const height = Math.max(1, Math.round((item.height || 800) * state.zoom));
    els.diagramCanvas.style.width = `${width}px`;
    els.diagramCanvas.style.height = `${height}px`;
    els.zoomReset.textContent = `${Math.round(state.zoom * 100)}%`;
  }

  function fitDiagram() {
    const item = activeItem();
    if (!item || state.mode !== 'diagrams') return;

    const pad = 56;
    const availableWidth = Math.max(160, els.diagramViewport.clientWidth - pad);
    const availableHeight = Math.max(160, els.diagramViewport.clientHeight - pad);
    const widthZoom = availableWidth / (item.width || 1200);
    const heightZoom = availableHeight / (item.height || 800);
    setZoom(Math.min(2, widthZoom, heightZoom));
    els.diagramViewport.scrollTo({ left: 0, top: 0 });
  }

  function renderDiagram(item) {
    if (!item) return;
    state.zoom = 1;
    els.diagramPath.textContent = item.path;
    els.diagramImage.src = item.svg;
    els.diagramImage.alt = item.title;
    els.diagramSource.textContent = item.content || '';
    setZoom(1);
    requestAnimationFrame(fitDiagram);
  }

  function tokenStore() {
    const tokens = [];
    return {
      hold(html) {
        const index = tokens.push(html) - 1;
        return `\u0000TOKEN${index}\u0000`;
      },
      restore(value) {
        return value.replace(/\u0000TOKEN(\d+)\u0000/g, (_, index) => tokens[Number(index)] || '');
      }
    };
  }

  function safeHref(value) {
    const href = String(value || '').trim();
    if (/^javascript:/i.test(href)) return '#';
    return href;
  }

  function renderInline(text) {
    const store = tokenStore();
    let work = String(text || '');

    work = work.replace(/`([^`]+)`/g, (_, code) => store.hold(`<code>${escapeHtml(code)}</code>`));
    work = work.replace(/\$([^$\n]+)\$/g, (_, math) => store.hold(`<span class="math-inline">${escapeHtml(math.trim())}</span>`));
    work = work.replace(/!\[([^\]]*)\]\(([^)\s]+)(?:\s+"[^"]*")?\)/g, (_, alt, src) => {
      return store.hold(`<img src="${escapeHtml(safeHref(src))}" alt="${escapeHtml(alt)}" />`);
    });
    work = work.replace(/\[([^\]]+)\]\(([^)\s]+)(?:\s+"[^"]*")?\)/g, (_, label, href) => {
      return store.hold(`<a href="${escapeHtml(safeHref(href))}">${renderInline(label)}</a>`);
    });

    work = escapeHtml(work);
    work = work.replace(/\*\*([^*\n]+)\*\*/g, '<strong>$1</strong>');
    work = work.replace(/__([^_\n]+)__/g, '<strong>$1</strong>');
    work = work.replace(/(^|[\s([{，。；：、])\*([^*\n]+)\*/g, '$1<em>$2</em>');
    work = work.replace(/(^|[\s([{，。；：、])_([^_\n]+)_/g, '$1<em>$2</em>');
    return store.restore(work);
  }

  function renderParagraph(lines) {
    const text = lines.join('\n').trim();
    if (!text) return '';
    return `<p>${renderInline(text).replace(/\n/g, '<br>')}</p>`;
  }

  function isTableLine(line) {
    const trimmed = line.trim();
    return trimmed.startsWith('|') && trimmed.endsWith('|') && trimmed.includes('|');
  }

  function isTableSeparator(line) {
    return /^\s*\|?\s*:?-{3,}:?\s*(\|\s*:?-{3,}:?\s*)+\|?\s*$/.test(line);
  }

  function splitTableRow(line) {
    return line.trim().replace(/^\|/, '').replace(/\|$/, '').split('|').map((cell) => cell.trim());
  }

  function renderTable(rows) {
    if (!rows.length) return '';
    const header = splitTableRow(rows[0]);
    const bodyRows = rows.slice(isTableSeparator(rows[1] || '') ? 2 : 1);
    const thead = `<thead><tr>${header.map((cell) => `<th>${renderInline(cell)}</th>`).join('')}</tr></thead>`;
    const tbody = bodyRows.length
      ? `<tbody>${bodyRows.map((row) => `<tr>${splitTableRow(row).map((cell) => `<td>${renderInline(cell)}</td>`).join('')}</tr>`).join('')}</tbody>`
      : '';
    return `<div class="table-wrap"><table>${thead}${tbody}</table></div>`;
  }

  function renderCodeBlock(lines, lang) {
    const className = lang ? ` class="language-${escapeHtml(lang)}"` : '';
    return `<pre class="md-code"><code${className}>${escapeHtml(lines.join('\n'))}</code></pre>`;
  }

  function renderMathBlock(lines) {
    return `<pre class="math-block">${escapeHtml(lines.join('\n').trim())}</pre>`;
  }

  function renderQuote(lines) {
    return `<blockquote>${lines.map((line) => renderInline(line)).join('<br>')}</blockquote>`;
  }

  function renderMermaidLink(code, item) {
    const exact = data.diagrams.find((entry) => entry.content.trim() === code.trim());
    const byDoc = data.diagrams.find((entry) => entry.sourceDoc === item.path);
    const diagram = exact || byDoc;
    if (!diagram) return renderCodeBlock(code.split(/\r?\n/), 'mermaid');
    return `<a class="inline-diagram-link" href="#" data-diagram-id="${escapeHtml(diagram.id)}">打开图谱：${escapeHtml(diagram.title)}</a>`;
  }

  function markdownToHtml(markdown, item) {
    const lines = markdown.split(/\r?\n/);
    const html = [];
    let paragraph = [];
    let inCode = false;
    let codeLang = '';
    let codeLines = [];
    let inMath = false;
    let mathLines = [];
    let inList = false;
    let listType = '';
    let quoteLines = [];

    function flushParagraph() {
      if (paragraph.length) {
        html.push(renderParagraph(paragraph));
        paragraph = [];
      }
    }

    function flushQuote() {
      if (quoteLines.length) {
        html.push(renderQuote(quoteLines));
        quoteLines = [];
      }
    }

    function closeList() {
      if (inList) {
        html.push(`</${listType}>`);
        inList = false;
        listType = '';
      }
    }

    function openList(type) {
      if (!inList || listType !== type) {
        closeList();
        html.push(`<${type}>`);
        inList = true;
        listType = type;
      }
    }

    function flushBlocks() {
      flushParagraph();
      flushQuote();
      closeList();
    }

    for (let index = 0; index < lines.length; index += 1) {
      const line = lines[index];
      const trimmed = line.trim();
      const fence = line.match(/^```([A-Za-z0-9_-]+)?\s*$/);

      if (fence) {
        if (inCode) {
          const code = codeLines.join('\n');
          html.push(codeLang === 'mermaid' ? renderMermaidLink(code, item) : renderCodeBlock(codeLines, codeLang));
          inCode = false;
          codeLang = '';
          codeLines = [];
        } else {
          flushBlocks();
          inCode = true;
          codeLang = fence[1] || '';
          codeLines = [];
        }
        continue;
      }

      if (inCode) {
        codeLines.push(line);
        continue;
      }

      if (trimmed === '$$') {
        if (inMath) {
          html.push(renderMathBlock(mathLines));
          inMath = false;
          mathLines = [];
        } else {
          flushBlocks();
          inMath = true;
          mathLines = [];
        }
        continue;
      }

      if (inMath) {
        mathLines.push(line);
        continue;
      }

      if (!trimmed) {
        flushBlocks();
        continue;
      }

      if (isTableLine(line) && isTableSeparator(lines[index + 1] || '')) {
        flushBlocks();
        const tableRows = [line, lines[index + 1]];
        index += 2;
        while (index < lines.length && isTableLine(lines[index])) {
          tableRows.push(lines[index]);
          index += 1;
        }
        index -= 1;
        html.push(renderTable(tableRows));
        continue;
      }

      const heading = line.match(/^(#{1,6})\s+(.+)$/);
      if (heading) {
        flushBlocks();
        const level = heading[1].length;
        html.push(`<h${level}>${renderInline(heading[2])}</h${level}>`);
        continue;
      }

      if (/^ {0,3}(-{3,}|\*{3,}|_{3,})\s*$/.test(line)) {
        flushBlocks();
        html.push('<hr>');
        continue;
      }

      const quote = line.match(/^>\s?(.*)$/);
      if (quote) {
        flushParagraph();
        closeList();
        quoteLines.push(quote[1]);
        continue;
      }

      const unordered = line.match(/^\s*[-*]\s+(.+)$/);
      if (unordered) {
        flushParagraph();
        flushQuote();
        openList('ul');
        html.push(`<li>${renderInline(unordered[1])}</li>`);
        continue;
      }

      const ordered = line.match(/^\s*\d+\.\s+(.+)$/);
      if (ordered) {
        flushParagraph();
        flushQuote();
        openList('ol');
        html.push(`<li>${renderInline(ordered[1])}</li>`);
        continue;
      }

      flushQuote();
      closeList();
      paragraph.push(line);
    }

    if (inCode) html.push(renderCodeBlock(codeLines, codeLang));
    if (inMath) html.push(renderMathBlock(mathLines));
    flushBlocks();

    return html.join('\n');
  }

  function bindInlineDiagramLinks() {
    Array.from(els.markdownContent.querySelectorAll('.inline-diagram-link')).forEach((link) => {
      link.addEventListener('click', (event) => {
        event.preventDefault();
        const id = link.dataset.diagramId;
        if (!id) return;
        state.mode = 'diagrams';
        state.selected.diagrams = id;
        state.query = '';
        els.searchInput.value = '';
        render();
      });
    });
  }

  function renderText(item) {
    els.markdownContent.innerHTML = item ? markdownToHtml(item.content, item) : '<p>没有内容。</p>';
    bindInlineDiagramLinks();
  }

  function highlightLeanCode(raw) {
    const store = tokenStore();
    let work = raw;

    work = work.replace(/"([^"\\]|\\.)*"/g, (value) => store.hold(`<span class="lean-string">${escapeHtml(value)}</span>`));
    work = work.replace(/^(\s*)(import)\s+(.+)$/, (_, indent, keyword, moduleName) => {
      return `${indent}${store.hold(`<span class="lean-keyword">${keyword}</span> <span class="lean-module">${escapeHtml(moduleName)}</span>`)}`;
    });
    work = work.replace(/\b(def|theorem|lemma|axiom|inductive|structure|class|instance|abbrev|opaque|constant)\s+([A-Za-z0-9_'.@\u0370-\u03ff\u4e00-\u9fff]+)/g, (_, keyword, name) => {
      return store.hold(`<span class="lean-keyword">${keyword}</span> <span class="lean-decl">${escapeHtml(name)}</span>`);
    });

    work = escapeHtml(work);
    work = work.replace(/\b(namespace|section|variable|universe|open|where|deriving|mutual|end|by|let|have|show|exact|apply|intro|simp|rw|cases|constructor|match|with|if|then|else|Type|Prop)\b/g, '<span class="lean-keyword">$1</span>');
    return store.restore(work);
  }

  function highlightLeanLine(line, state) {
    if (state.inBlockComment) {
      const end = line.indexOf('-/');
      if (end === -1) return `<span class="lean-comment">${escapeHtml(line)}</span>`;
      state.inBlockComment = false;
      return `<span class="lean-comment">${escapeHtml(line.slice(0, end + 2))}</span>${highlightLeanLine(line.slice(end + 2), state)}`;
    }

    const blockStart = line.indexOf('/-');
    const lineComment = line.indexOf('--');
    const firstComment = [blockStart, lineComment].filter((index) => index >= 0).sort((a, b) => a - b)[0];
    if (firstComment === undefined) return highlightLeanCode(line);

    const before = line.slice(0, firstComment);
    if (firstComment === lineComment) {
      return `${highlightLeanCode(before)}<span class="lean-comment">${escapeHtml(line.slice(firstComment))}</span>`;
    }

    const afterStart = line.slice(firstComment);
    const end = afterStart.indexOf('-/');
    if (end === -1) {
      state.inBlockComment = true;
      return `${highlightLeanCode(before)}<span class="lean-comment">${escapeHtml(afterStart)}</span>`;
    }

    const comment = afterStart.slice(0, end + 2);
    const after = afterStart.slice(end + 2);
    return `${highlightLeanCode(before)}<span class="lean-comment">${escapeHtml(comment)}</span>${highlightLeanLine(after, state)}`;
  }

  function renderFormal(item) {
    if (!item) {
      els.formalContent.innerHTML = '<div class="empty-state">没有内容。</div>';
      return;
    }

    const lines = item.content.split(/\r?\n/);
    const state = { inBlockComment: false };
    els.formalContent.innerHTML = `
      <div class="code-table" role="table" aria-label="${escapeHtml(item.title)}">
        ${lines.map((line, index) => `
          <div class="code-line" role="row">
            <span class="line-number" role="cell">${index + 1}</span>
            <code class="line-code" role="cell">${highlightLeanLine(line, state)}</code>
          </div>
        `).join('')}
      </div>
    `;
  }

  function renderContent() {
    const item = activeItem();
    showView(state.mode);
    setHeader(item);

    if (state.mode === 'diagrams') renderDiagram(item);
    if (state.mode === 'texts') renderText(item);
    if (state.mode === 'formal') renderFormal(item);
  }

  function renderTabs() {
    els.modeTabs.forEach((button) => {
      button.classList.toggle('is-active', button.dataset.mode === state.mode);
    });
  }

  function render() {
    selectFirstVisibleIfNeeded();
    renderTabs();
    renderList();
    renderContent();
  }

  els.modeTabs.forEach((button) => {
    button.addEventListener('click', () => {
      state.mode = button.dataset.mode;
      render();
    });
  });

  els.searchInput.addEventListener('input', () => {
    state.query = els.searchInput.value;
    render();
  });

  els.zoomOut.addEventListener('click', () => setZoom(state.zoom / 1.25));
  els.zoomIn.addEventListener('click', () => setZoom(state.zoom * 1.25));
  els.zoomReset.addEventListener('click', () => {
    setZoom(1);
    els.diagramViewport.scrollTo({ left: 0, top: 0 });
  });
  els.zoomFit.addEventListener('click', fitDiagram);

  els.diagramViewport.addEventListener('wheel', (event) => {
    if (!event.ctrlKey && !event.metaKey) return;
    event.preventDefault();
    const next = event.deltaY > 0 ? state.zoom / 1.12 : state.zoom * 1.12;
    setZoom(next);
  }, { passive: false });

  let dragging = false;
  let dragStart = null;

  els.diagramViewport.addEventListener('pointerdown', (event) => {
    if (event.button !== 0) return;
    dragging = true;
    dragStart = {
      x: event.clientX,
      y: event.clientY,
      left: els.diagramViewport.scrollLeft,
      top: els.diagramViewport.scrollTop
    };
    els.diagramViewport.setPointerCapture(event.pointerId);
  });

  els.diagramViewport.addEventListener('pointermove', (event) => {
    if (!dragging || !dragStart) return;
    els.diagramViewport.scrollLeft = dragStart.left - (event.clientX - dragStart.x);
    els.diagramViewport.scrollTop = dragStart.top - (event.clientY - dragStart.y);
  });

  els.diagramViewport.addEventListener('pointerup', () => {
    dragging = false;
    dragStart = null;
  });

  window.addEventListener('resize', () => {
    if (state.mode === 'diagrams') fitDiagram();
  });

  renderStats();
  render();
})();
