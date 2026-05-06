import fs from 'node:fs';
import path from 'node:path';

const root = path.resolve(import.meta.dirname, '..');
const webRoot = path.join(root, 'web');

const textFiles = [
  '间生论_主篇.md',
  '生生不息论_间开本_致知版.md',
  '生生不息论_三本文完整版.md',
  '生生不息论_v14_形式证明骨架版.md',
  '生生不息论_v13.2_形式项总清与类型校正版.md',
  'wenyan-operators.md',
  'docs/间本体论_元三相与场修订稿.md',
  'formal/SSBX/README.md',
  'formal/SSBX/JianOntology.md',
  'formal/SSBX/ConceptDAG.md',
  'formal/SSBX/ConstructionDAG.md',
  'formal/SSBX/MonadDAG.md',
  'formal/SSBX/HumanAlignment.md',
  'formal/SSBX/Attention.md'
];

const diagramFiles = [
  ['ConceptDAG.core', 'formal/SSBX/ConceptDAG.core.mmd', 'formal/SSBX/ConceptDAG.md'],
  ['ConceptDAG.layered', 'formal/SSBX/ConceptDAG.layered.mmd', 'formal/SSBX/ConceptDAG.md'],
  ['ConceptDAG.complete', 'formal/SSBX/ConceptDAG.complete.mmd', 'formal/SSBX/ConceptDAG.md'],
  ['ConceptDAG.full', 'formal/SSBX/ConceptDAG.full.mmd', 'formal/SSBX/ConceptDAG.md'],
  ['ConstructionDAG', 'formal/SSBX/ConstructionDAG.mmd', 'formal/SSBX/ConstructionDAG.md'],
  ['MonadDAG', 'formal/SSBX/MonadDAG.mmd', 'formal/SSBX/MonadDAG.md'],
  ['HumanAlignmentDAG', 'formal/SSBX/HumanAlignmentDAG.mmd', 'formal/SSBX/HumanAlignment.md'],
  ['AttentionDAG', 'formal/SSBX/AttentionDAG.mmd', 'formal/SSBX/Attention.md']
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
  const nodeMatches = content.match(/^\s*[A-Za-z0-9_\u4e00-\u9fff]+(?:\[[^\]]+\]|\([^)]+\)|\{[^}]+\})/gm) || [];
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

const texts = textFiles.filter((file) => fs.existsSync(path.join(root, file))).map(documentRecord);
const diagrams = diagramFiles.filter(([, file]) => fs.existsSync(path.join(root, file))).map(diagramRecord);
const formal = leanFiles(path.join(root, 'formal')).map(formalRecord);

const payload = {
  meta: {
    generatedAt: new Date().toISOString(),
    fileCount: texts.length + diagrams.length + formal.length,
    rootName: path.basename(root)
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
