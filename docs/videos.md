# Videos in a blueprint

A paper with a video shows one player at the top of its **At a glance** section. Its cover is visible when the page opens. Playback starts only when the reader presses Play. English is selected by default; the selector above the player switches to Spanish. The video stays on the same blueprint page, so each paper needs only one page. Links to the bilingual file on Hugging Face and to YouTube can appear below the player.

See [Quantum memory](../memory-floors/) and [Quantum relay](../relay-floors/) for published examples.

## Configure a paper

Lemmario reads an optional `[video]` section from the paper's `lemmario.toml` when it builds the blueprint:

```toml
[video]
en = 'https://example.org/paper_en.mp4'
es = 'https://example.org/paper_es.mp4'
poster_en = 'https://example.org/poster_en.jpg'
poster_es = 'https://example.org/poster_es.jpg'
huggingface = 'https://huggingface.co/datasets/example/video/blob/main/paper_bilingual.mp4'
youtube = 'https://www.youtube.com/watch?v=example'
```

The four language and cover URLs are required if `[video]` is present. `huggingface` and `youtube` are optional. The URLs must use HTTP or HTTPS. Lemmario adds the player to the map and the classic blueprint overview during the build; papers without `[video]` do not get a player. The HTML uses `preload="none"` and no `autoplay` attribute.
