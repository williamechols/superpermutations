# n=14 superpermutation with length 93,904,804,516

Found by GPT-6.1 Sol xhigh on October 18, 2026. Improves the [previous repository record](../93904936032/) by 131,516 symbols, by optimizing group openings and joins while retaining the same seed.

The complete recipe is [93904804516.spg.xz](93904804516.spg.xz), using the alphabet `123456789ABCDE`. 

## Usage

To generate the complete 93.9 GB text file:

```sh
python3 decode.py 93904804516.spg.xz 93904804516.txt
```

## Attribution

The recipe embeds Jakub Halfar's unchanged selection C from [`arrange/data/n12t-selection.txt.xz`](https://github.com/jhalfar/superpermutations/blob/c9cb923057f757efa7c0f0e4c4cc1677ef3e6d3b/arrange/data/n12t-selection.txt.xz). Its original comments and [Apache License, Version 2.0](LICENSE) are retained. Halfar credits published weight-two cuts and chains to [rumstd](https://github.com/rumstd).

Jay Pantone developed the slices, transport, completion, and closed trails in [superperm-upper-43-80](https://github.com/jaypantone/superperm-upper-43-80/tree/c8fb7ffdd69be1375580710ae11b47a295b1f0f6).

[NOTICE](NOTICE) retains Halfar's upstream notice and identifies this repository's changes. The embedded seed was checked byte for byte against the pinned upstream archive.
