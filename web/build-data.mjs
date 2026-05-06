import fs from 'node:fs';
import path from 'node:path';

const root = path.resolve(import.meta.dirname, '..');
const webRoot = path.join(root, 'web');

// 第一版 (v1.0) — 现行 canon. 三层骨架: formal + 义理 + 基础表 + 工程笔记.
// 已 archive 至 史料/ 之早期文档不再列入 web 之主体, 仅以入口指针保留.

const textFiles = [
  // 项目入口
  'README.md',
  '义理/README.md',
  '史料/README.md',

  // 义理篇 — 26 卷 A–Z (与 Foundation/Wen/Kernel.lean 之 45 层对齐)
  '义理/A_经典易传.md',
  '义理/B_六征体系.md',
  '义理/C_实虚史真.md',
  '义理/D_算子代数.md',
  '义理/E_古代源流.md',
  '义理/F_物理现象学.md',
  '义理/G_完整算子系统_八卦互通与归一.md',
  '义理/H_证明报告.md',
  '义理/I_八卦全集.md',
  '义理/J_理之不完备_哥德尔在192.md',
  '义理/K_完备性审计.md',
  '义理/L_文道一也_自释与微核.md',
  '义理/M_证明报告_192_理之不完备.md',
  '义理/N_儒家从元到圣.md',
  '义理/O_进化非道者生存_三视证.md',
  '义理/P_道家从无到化.md',
  '义理/Q_佛家从苦到觉.md',
  '义理/R_与生生不息对齐之必然.md',
  '义理/S_先秦百家.md',
  '义理/T_西哲与亚伯拉罕.md',
  '义理/U_反诛心信诚之形式.md',
  '义理/V_现代政治哲学.md',
  '义理/W_非道之形式.md',
  '义理/X_反施密特.md',
  '义理/Y_对齐失败.md',
  '义理/Z_经济博弈.md',

  // 八衍 (Eight 衍) — 由 元 至 衍 之 8 卷
  '义理/数与算术 · 从元到数.md',
  '义理/形式逻辑 · 从元到推.md',
  '义理/统计 · 从元到测.md',
  '义理/几何位 · 从元到形.md',
  '义理/类与映 · 从元到映.md',
  '义理/动力 · 从元到行.md',
  '义理/心智 · 从元到识.md',
  '义理/物理 · 从元到象.md',

  // 义理 · 跨卷
  '义理/算子别名总表.md',
  '义理/人类命运共同体_共同体之证.md',

  // 六表 — 基础结构表
  '六表_实虚史真/表一_六征本表.md',
  '六表_实虚史真/表二_史维三态.md',
  '六表_实虚史真/表三_实虚modal三态.md',
  '六表_实虚史真/表四_真假认识三态.md',
  '六表_实虚史真/表五_三轴27格.md',
  '六表_实虚史真/表六_192格全表.md',

  // 算子集 (Lean Text/WenyanOperators.lean 数据源)
  'wenyan-operators.md',

  // 形式化伴随 — 工程笔记 (formal/SSBX/notes/)
  'formal/SSBX/README.md',
  'formal/SSBX/notes/ConceptDAG.md',
  'formal/SSBX/notes/ConstructionDAG.md',
  'formal/SSBX/notes/MonadDAG.md',
  'formal/SSBX/notes/JianOntology.md',
  'formal/SSBX/notes/HumanAlignment.md',
  'formal/SSBX/notes/Attention.md',
  'formal/SSBX/notes/atom-naming.md',
  'formal/SSBX/notes/baguaWen-spec.md',
  'formal/SSBX/notes/math-axiom-map.md',
  'formal/SSBX/notes/monad-root-plan.md',
  'formal/SSBX/notes/MissingGlyphRootReport.md'
];

const diagramFiles = [
  ['ConceptDAG.core',     'formal/SSBX/diagrams/ConceptDAG.core.mmd',     'formal/SSBX/notes/ConceptDAG.md'],
  ['ConceptDAG.layered',  'formal/SSBX/diagrams/ConceptDAG.layered.mmd',  'formal/SSBX/notes/ConceptDAG.md'],
  ['ConceptDAG.complete', 'formal/SSBX/diagrams/ConceptDAG.complete.mmd', 'formal/SSBX/notes/ConceptDAG.md'],
  ['ConceptDAG.full',     'formal/SSBX/diagrams/ConceptDAG.full.mmd',     'formal/SSBX/notes/ConceptDAG.md'],
  ['ConstructionDAG',     'formal/SSBX/diagrams/ConstructionDAG.mmd',     'formal/SSBX/notes/ConstructionDAG.md'],
  ['MonadDAG',            'formal/SSBX/diagrams/MonadDAG.mmd',            'formal/SSBX/notes/MonadDAG.md'],
  ['HumanAlignmentDAG',   'formal/SSBX/diagrams/HumanAlignmentDAG.mmd',   'formal/SSBX/notes/HumanAlignment.md'],
  ['AttentionDAG',        'formal/SSBX/diagrams/AttentionDAG.mmd',        'formal/SSBX/notes/Attention.md']
];

function read(relativePath) {
  return fs.readFileSync(path.join(root, relativePath), 'utf8');
}

function lineCount(content) {
  if (!content) return 0;
  return content.split(/\r?\n/).length;
}

function titleFromMarkdown(content, fallback) {
  const heading = content.match(/^#\s+(.+)$/m);
  return heading ? heading[1].trim() : fallback;
}

function titleFromPath(relativePath) {
  return path.basename(relativePath, path.extname(relativePath));
}

function summarizeMarkdown(content) {
  return content
    .split(/\r?\n/)
    .map((line) => line.trim())
    .find((line) => line && !line.startsWith('#') && !line.startsWith('```')) || '';
}

function svgSize(relativeSvgPath) {
  const absolute = path.join(webRoot, relativeSvgPath);
  if (!fs.existsSync(absolute)) return { width: 1200, height: 800 };
  const svg = fs.readFileSync(absolute, 'utf8');
  const viewBox = svg.match(/viewBox="([^"]+)"/);
  if (viewBox) {
    const [, , width, height] = viewBox[1].split(/\s+/).map(Number);
    if (Number.isFinite(width) && Number.isFinite(height)) {
      return { width, height };
    }
  }
  const width = Number(svg.match(/width="([\d.]+)"/)?.[1]);
  const height = Number(svg.match(/height="([\d.]+)"/)?.[1]);
  return {
    width: Number.isFinite(width) ? width : 1200,
    height: Number.isFinite(height) ? height : 800
  };
}

function mermaidCounts(content) {
  const edgeMatches = content.match(/[-.=]+>/g) || [];
  const nodeMatches = content.match(/^\s*[A-Za-z0-9_一-鿿]+(?:\[[^\]]+\]|\([^)]+\)|\{[^}]+\})/gm) || [];
  return {
    nodes: nodeMatches.length,
    edges: edgeMatches.length
  };
}

function leanFiles(dir) {
  return fs.readdirSync(dir, { withFileTypes: true }).flatMap((entry) => {
    const absolute = path.join(dir, entry.name);
    if (entry.isDirectory()) return leanFiles(absolute);
    if (entry.isFile() && entry.name.endsWith('.lean')) {
      return [path.relative(root, absolute)];
    }
    return [];
  }).sort((a, b) => a.localeCompare(b, 'zh-Hans-CN'));
}

function documentRecord(relativePath) {
  const content = read(relativePath);
  return {
    id: relativePath,
    title: titleFromMarkdown(content, titleFromPath(relativePath)),
    path: relativePath,
    summary: summarizeMarkdown(content),
    lines: lineCount(content),
    words: [...content].length,
    content
  };
}

function diagramRecord([id, relativePath, sourceDoc]) {
  const content = read(relativePath);
  const svg = `assets/diagrams/${id}.svg`;
  const size = svgSize(svg);
  const counts = mermaidCounts(content);
  return {
    id,
    title: id.replaceAll('.', ' / '),
    path: relativePath,
    sourceDoc,
    svg,
    width: size.width,
    height: size.height,
    nodes: counts.nodes,
    edges: counts.edges,
    lines: lineCount(content),
    words: [...content].length,
    content
  };
}

function formalRecord(relativePath) {
  const content = read(relativePath);
  return {
    id: relativePath,
    title: titleFromPath(relativePath),
    path: relativePath,
    summary: content.split(/\r?\n/).find((line) => line.trim().startsWith('--')) || '',
    lines: lineCount(content),
    words: [...content].length,
    content
  };
}

const missing = textFiles.filter((file) => !fs.existsSync(path.join(root, file)));
if (missing.length > 0) {
  console.warn(`[warn] ${missing.length} text file(s) referenced but missing:`);
  for (const f of missing) console.warn(`  - ${f}`);
}

const texts = textFiles.filter((file) => fs.existsSync(path.join(root, file))).map(documentRecord);
const diagrams = diagramFiles.filter(([, file]) => fs.existsSync(path.join(root, file))).map(diagramRecord);
const formal = leanFiles(path.join(root, 'formal')).map(formalRecord);

const payload = {
  meta: {
    generatedAt: new Date().toISOString(),
    fileCount: texts.length + diagrams.length + formal.length,
    rootName: path.basename(root),
    version: 'v1.0',
    note: '生生不息 第一版. formal 收口于 Lean 4 + Mathlib HEAD; 义理 28+ 卷 (A-Z) 与 Kernel 45 层对齐.'
  },
  texts,
  diagrams,
  formal
};

fs.writeFileSync(
  path.join(webRoot, 'data.js'),
  `window.SSBX_DATA = ${JSON.stringify(payload, null, 2)};\n`,
  'utf8'
);

console.log(`Wrote web/data.js with ${texts.length} texts, ${diagrams.length} diagrams, ${formal.length} formal files.`);
