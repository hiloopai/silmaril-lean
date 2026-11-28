# Explorer vendor scripts (`tools/silmaril-project/src/project/explore/vendor/`)

`sil project explore` bundles two third-party MIT libraries for offline inline
documentation and diagram rendering without runtime CDN requests:

| Included file | Upstream release | SHA-256 | License |
| --- | --- | --- | --- |
| `tools/silmaril-project/src/project/explore/vendor/marked.js` | [`marked` 18.0.11 (`lib/marked.umd.js`)](https://github.com/markedjs/marked/releases/tag/v18.0.11) | `f66c1a25b7e57cf67b96b868186c43abcf915efbf150d5c8c26e37f1fc0db662` (original UMD); `<!--` escaped as `<\x21--` and `sourceMappingURL` stripped for inline `<script>` bundling | [LICENSE-marked.txt](LICENSE-marked.txt) |
| `tools/silmaril-project/src/project/explore/vendor/mermaid.min.js` | [`mermaid` 11.17.2 (`dist/mermaid.min.js`)](https://github.com/mermaid-js/mermaid/releases/tag/v11.17.2) | `581ed7d74bd9048d0e3a91363927d72ef22942d7722546b27f7cc29e35390eb8` | [LICENSE-mermaid.txt](LICENSE-mermaid.txt) |
