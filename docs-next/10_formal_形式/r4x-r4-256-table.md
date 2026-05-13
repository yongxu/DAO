# R4 x R4 256-Cell Projection Table

> Status: structural working table (2026-05-12)
>
> Purpose: read an 8-bit cell as two R4 positions, then expose the R1..R6 prefix projections. R7 and R8 are intentionally left blank in this table.
>
> Character-facing companion: [`r4x-r4-256-table-zi.md`](./r4x-r4-256-table-zi.md).

## Coordinate Rule

This table uses a two-dimensional carrier:

```text
R4_high = y1 y2 y3 y4
R4_low  = y5 y6 y7 y8
cell    = R4_high ++ R4_low
```

The populated projections are only the prefix layers:

| Layer | Projection | Status |
|---|---|---|
| R1 | first 1 bit(s) of `cell` | filled |
| R2 | first 2 bit(s) of `cell` | filled |
| R3 | first 3 bit(s) of `cell` | filled |
| R4 | first 4 bit(s) of `cell` | filled |
| R5 | first 5 bit(s) of `cell` | filled |
| R6 | first 6 bit(s) of `cell` | filled |
| R7 | first 7 bits of `cell` | blank for now |
| R8 | all 8 bits of `cell` | blank for now |

This is a sheet of 16 x 16 = 256 cells. The row and column are both R4 positions. R1..R6 are projections of the resulting 8-bit coordinate; R7/R8 interpretation is deferred.

## R4 Order

Both axes use the same lexicographic `o/x` order:

```text
oooo ooox ooxo ooxx oxoo oxox oxxo oxxx xooo xoox xoxo xoxx xxoo xxox xxxo xxxx
```

## 16 x 16 R6 Matrix

Each matrix entry is the filled R6 prefix `y1..y6`. The remaining low-coordinate bits `y7 y8` are not read here.

| R4_high \ R4_low | `oooo` | `ooox` | `ooxo` | `ooxx` | `oxoo` | `oxox` | `oxxo` | `oxxx` | `xooo` | `xoox` | `xoxo` | `xoxx` | `xxoo` | `xxox` | `xxxo` | `xxxx` |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `oooo` | `oooooo` | `oooooo` | `oooooo` | `oooooo` | `ooooox` | `ooooox` | `ooooox` | `ooooox` | `ooooxo` | `ooooxo` | `ooooxo` | `ooooxo` | `ooooxx` | `ooooxx` | `ooooxx` | `ooooxx` |
| `ooox` | `oooxoo` | `oooxoo` | `oooxoo` | `oooxoo` | `oooxox` | `oooxox` | `oooxox` | `oooxox` | `oooxxo` | `oooxxo` | `oooxxo` | `oooxxo` | `oooxxx` | `oooxxx` | `oooxxx` | `oooxxx` |
| `ooxo` | `ooxooo` | `ooxooo` | `ooxooo` | `ooxooo` | `ooxoox` | `ooxoox` | `ooxoox` | `ooxoox` | `ooxoxo` | `ooxoxo` | `ooxoxo` | `ooxoxo` | `ooxoxx` | `ooxoxx` | `ooxoxx` | `ooxoxx` |
| `ooxx` | `ooxxoo` | `ooxxoo` | `ooxxoo` | `ooxxoo` | `ooxxox` | `ooxxox` | `ooxxox` | `ooxxox` | `ooxxxo` | `ooxxxo` | `ooxxxo` | `ooxxxo` | `ooxxxx` | `ooxxxx` | `ooxxxx` | `ooxxxx` |
| `oxoo` | `oxoooo` | `oxoooo` | `oxoooo` | `oxoooo` | `oxooox` | `oxooox` | `oxooox` | `oxooox` | `oxooxo` | `oxooxo` | `oxooxo` | `oxooxo` | `oxooxx` | `oxooxx` | `oxooxx` | `oxooxx` |
| `oxox` | `oxoxoo` | `oxoxoo` | `oxoxoo` | `oxoxoo` | `oxoxox` | `oxoxox` | `oxoxox` | `oxoxox` | `oxoxxo` | `oxoxxo` | `oxoxxo` | `oxoxxo` | `oxoxxx` | `oxoxxx` | `oxoxxx` | `oxoxxx` |
| `oxxo` | `oxxooo` | `oxxooo` | `oxxooo` | `oxxooo` | `oxxoox` | `oxxoox` | `oxxoox` | `oxxoox` | `oxxoxo` | `oxxoxo` | `oxxoxo` | `oxxoxo` | `oxxoxx` | `oxxoxx` | `oxxoxx` | `oxxoxx` |
| `oxxx` | `oxxxoo` | `oxxxoo` | `oxxxoo` | `oxxxoo` | `oxxxox` | `oxxxox` | `oxxxox` | `oxxxox` | `oxxxxo` | `oxxxxo` | `oxxxxo` | `oxxxxo` | `oxxxxx` | `oxxxxx` | `oxxxxx` | `oxxxxx` |
| `xooo` | `xooooo` | `xooooo` | `xooooo` | `xooooo` | `xoooox` | `xoooox` | `xoooox` | `xoooox` | `xoooxo` | `xoooxo` | `xoooxo` | `xoooxo` | `xoooxx` | `xoooxx` | `xoooxx` | `xoooxx` |
| `xoox` | `xooxoo` | `xooxoo` | `xooxoo` | `xooxoo` | `xooxox` | `xooxox` | `xooxox` | `xooxox` | `xooxxo` | `xooxxo` | `xooxxo` | `xooxxo` | `xooxxx` | `xooxxx` | `xooxxx` | `xooxxx` |
| `xoxo` | `xoxooo` | `xoxooo` | `xoxooo` | `xoxooo` | `xoxoox` | `xoxoox` | `xoxoox` | `xoxoox` | `xoxoxo` | `xoxoxo` | `xoxoxo` | `xoxoxo` | `xoxoxx` | `xoxoxx` | `xoxoxx` | `xoxoxx` |
| `xoxx` | `xoxxoo` | `xoxxoo` | `xoxxoo` | `xoxxoo` | `xoxxox` | `xoxxox` | `xoxxox` | `xoxxox` | `xoxxxo` | `xoxxxo` | `xoxxxo` | `xoxxxo` | `xoxxxx` | `xoxxxx` | `xoxxxx` | `xoxxxx` |
| `xxoo` | `xxoooo` | `xxoooo` | `xxoooo` | `xxoooo` | `xxooox` | `xxooox` | `xxooox` | `xxooox` | `xxooxo` | `xxooxo` | `xxooxo` | `xxooxo` | `xxooxx` | `xxooxx` | `xxooxx` | `xxooxx` |
| `xxox` | `xxoxoo` | `xxoxoo` | `xxoxoo` | `xxoxoo` | `xxoxox` | `xxoxox` | `xxoxox` | `xxoxox` | `xxoxxo` | `xxoxxo` | `xxoxxo` | `xxoxxo` | `xxoxxx` | `xxoxxx` | `xxoxxx` | `xxoxxx` |
| `xxxo` | `xxxooo` | `xxxooo` | `xxxooo` | `xxxooo` | `xxxoox` | `xxxoox` | `xxxoox` | `xxxoox` | `xxxoxo` | `xxxoxo` | `xxxoxo` | `xxxoxo` | `xxxoxx` | `xxxoxx` | `xxxoxx` | `xxxoxx` |
| `xxxx` | `xxxxoo` | `xxxxoo` | `xxxxoo` | `xxxxoo` | `xxxxox` | `xxxxox` | `xxxxox` | `xxxxox` | `xxxxxo` | `xxxxxo` | `xxxxxo` | `xxxxxo` | `xxxxxx` | `xxxxxx` | `xxxxxx` | `xxxxxx` |

## Expanded Audit Ledger

Blank R7/R8 cells are deliberate. They reserve the two upper projections for the later R7/R8 interpretation without mixing that decision into this R1..R6 sheet.

| R4_high | R4_low | R1 | R2 | R3 | R4 | R5 | R6 | R7 | R8 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `oooo` | `oooo` | `o` | `oo` | `ooo` | `oooo` | `ooooo` | `oooooo` |  |  |
| `oooo` | `ooox` | `o` | `oo` | `ooo` | `oooo` | `ooooo` | `oooooo` |  |  |
| `oooo` | `ooxo` | `o` | `oo` | `ooo` | `oooo` | `ooooo` | `oooooo` |  |  |
| `oooo` | `ooxx` | `o` | `oo` | `ooo` | `oooo` | `ooooo` | `oooooo` |  |  |
| `oooo` | `oxoo` | `o` | `oo` | `ooo` | `oooo` | `ooooo` | `ooooox` |  |  |
| `oooo` | `oxox` | `o` | `oo` | `ooo` | `oooo` | `ooooo` | `ooooox` |  |  |
| `oooo` | `oxxo` | `o` | `oo` | `ooo` | `oooo` | `ooooo` | `ooooox` |  |  |
| `oooo` | `oxxx` | `o` | `oo` | `ooo` | `oooo` | `ooooo` | `ooooox` |  |  |
| `oooo` | `xooo` | `o` | `oo` | `ooo` | `oooo` | `oooox` | `ooooxo` |  |  |
| `oooo` | `xoox` | `o` | `oo` | `ooo` | `oooo` | `oooox` | `ooooxo` |  |  |
| `oooo` | `xoxo` | `o` | `oo` | `ooo` | `oooo` | `oooox` | `ooooxo` |  |  |
| `oooo` | `xoxx` | `o` | `oo` | `ooo` | `oooo` | `oooox` | `ooooxo` |  |  |
| `oooo` | `xxoo` | `o` | `oo` | `ooo` | `oooo` | `oooox` | `ooooxx` |  |  |
| `oooo` | `xxox` | `o` | `oo` | `ooo` | `oooo` | `oooox` | `ooooxx` |  |  |
| `oooo` | `xxxo` | `o` | `oo` | `ooo` | `oooo` | `oooox` | `ooooxx` |  |  |
| `oooo` | `xxxx` | `o` | `oo` | `ooo` | `oooo` | `oooox` | `ooooxx` |  |  |
| `ooox` | `oooo` | `o` | `oo` | `ooo` | `ooox` | `oooxo` | `oooxoo` |  |  |
| `ooox` | `ooox` | `o` | `oo` | `ooo` | `ooox` | `oooxo` | `oooxoo` |  |  |
| `ooox` | `ooxo` | `o` | `oo` | `ooo` | `ooox` | `oooxo` | `oooxoo` |  |  |
| `ooox` | `ooxx` | `o` | `oo` | `ooo` | `ooox` | `oooxo` | `oooxoo` |  |  |
| `ooox` | `oxoo` | `o` | `oo` | `ooo` | `ooox` | `oooxo` | `oooxox` |  |  |
| `ooox` | `oxox` | `o` | `oo` | `ooo` | `ooox` | `oooxo` | `oooxox` |  |  |
| `ooox` | `oxxo` | `o` | `oo` | `ooo` | `ooox` | `oooxo` | `oooxox` |  |  |
| `ooox` | `oxxx` | `o` | `oo` | `ooo` | `ooox` | `oooxo` | `oooxox` |  |  |
| `ooox` | `xooo` | `o` | `oo` | `ooo` | `ooox` | `oooxx` | `oooxxo` |  |  |
| `ooox` | `xoox` | `o` | `oo` | `ooo` | `ooox` | `oooxx` | `oooxxo` |  |  |
| `ooox` | `xoxo` | `o` | `oo` | `ooo` | `ooox` | `oooxx` | `oooxxo` |  |  |
| `ooox` | `xoxx` | `o` | `oo` | `ooo` | `ooox` | `oooxx` | `oooxxo` |  |  |
| `ooox` | `xxoo` | `o` | `oo` | `ooo` | `ooox` | `oooxx` | `oooxxx` |  |  |
| `ooox` | `xxox` | `o` | `oo` | `ooo` | `ooox` | `oooxx` | `oooxxx` |  |  |
| `ooox` | `xxxo` | `o` | `oo` | `ooo` | `ooox` | `oooxx` | `oooxxx` |  |  |
| `ooox` | `xxxx` | `o` | `oo` | `ooo` | `ooox` | `oooxx` | `oooxxx` |  |  |
| `ooxo` | `oooo` | `o` | `oo` | `oox` | `ooxo` | `ooxoo` | `ooxooo` |  |  |
| `ooxo` | `ooox` | `o` | `oo` | `oox` | `ooxo` | `ooxoo` | `ooxooo` |  |  |
| `ooxo` | `ooxo` | `o` | `oo` | `oox` | `ooxo` | `ooxoo` | `ooxooo` |  |  |
| `ooxo` | `ooxx` | `o` | `oo` | `oox` | `ooxo` | `ooxoo` | `ooxooo` |  |  |
| `ooxo` | `oxoo` | `o` | `oo` | `oox` | `ooxo` | `ooxoo` | `ooxoox` |  |  |
| `ooxo` | `oxox` | `o` | `oo` | `oox` | `ooxo` | `ooxoo` | `ooxoox` |  |  |
| `ooxo` | `oxxo` | `o` | `oo` | `oox` | `ooxo` | `ooxoo` | `ooxoox` |  |  |
| `ooxo` | `oxxx` | `o` | `oo` | `oox` | `ooxo` | `ooxoo` | `ooxoox` |  |  |
| `ooxo` | `xooo` | `o` | `oo` | `oox` | `ooxo` | `ooxox` | `ooxoxo` |  |  |
| `ooxo` | `xoox` | `o` | `oo` | `oox` | `ooxo` | `ooxox` | `ooxoxo` |  |  |
| `ooxo` | `xoxo` | `o` | `oo` | `oox` | `ooxo` | `ooxox` | `ooxoxo` |  |  |
| `ooxo` | `xoxx` | `o` | `oo` | `oox` | `ooxo` | `ooxox` | `ooxoxo` |  |  |
| `ooxo` | `xxoo` | `o` | `oo` | `oox` | `ooxo` | `ooxox` | `ooxoxx` |  |  |
| `ooxo` | `xxox` | `o` | `oo` | `oox` | `ooxo` | `ooxox` | `ooxoxx` |  |  |
| `ooxo` | `xxxo` | `o` | `oo` | `oox` | `ooxo` | `ooxox` | `ooxoxx` |  |  |
| `ooxo` | `xxxx` | `o` | `oo` | `oox` | `ooxo` | `ooxox` | `ooxoxx` |  |  |
| `ooxx` | `oooo` | `o` | `oo` | `oox` | `ooxx` | `ooxxo` | `ooxxoo` |  |  |
| `ooxx` | `ooox` | `o` | `oo` | `oox` | `ooxx` | `ooxxo` | `ooxxoo` |  |  |
| `ooxx` | `ooxo` | `o` | `oo` | `oox` | `ooxx` | `ooxxo` | `ooxxoo` |  |  |
| `ooxx` | `ooxx` | `o` | `oo` | `oox` | `ooxx` | `ooxxo` | `ooxxoo` |  |  |
| `ooxx` | `oxoo` | `o` | `oo` | `oox` | `ooxx` | `ooxxo` | `ooxxox` |  |  |
| `ooxx` | `oxox` | `o` | `oo` | `oox` | `ooxx` | `ooxxo` | `ooxxox` |  |  |
| `ooxx` | `oxxo` | `o` | `oo` | `oox` | `ooxx` | `ooxxo` | `ooxxox` |  |  |
| `ooxx` | `oxxx` | `o` | `oo` | `oox` | `ooxx` | `ooxxo` | `ooxxox` |  |  |
| `ooxx` | `xooo` | `o` | `oo` | `oox` | `ooxx` | `ooxxx` | `ooxxxo` |  |  |
| `ooxx` | `xoox` | `o` | `oo` | `oox` | `ooxx` | `ooxxx` | `ooxxxo` |  |  |
| `ooxx` | `xoxo` | `o` | `oo` | `oox` | `ooxx` | `ooxxx` | `ooxxxo` |  |  |
| `ooxx` | `xoxx` | `o` | `oo` | `oox` | `ooxx` | `ooxxx` | `ooxxxo` |  |  |
| `ooxx` | `xxoo` | `o` | `oo` | `oox` | `ooxx` | `ooxxx` | `ooxxxx` |  |  |
| `ooxx` | `xxox` | `o` | `oo` | `oox` | `ooxx` | `ooxxx` | `ooxxxx` |  |  |
| `ooxx` | `xxxo` | `o` | `oo` | `oox` | `ooxx` | `ooxxx` | `ooxxxx` |  |  |
| `ooxx` | `xxxx` | `o` | `oo` | `oox` | `ooxx` | `ooxxx` | `ooxxxx` |  |  |
| `oxoo` | `oooo` | `o` | `ox` | `oxo` | `oxoo` | `oxooo` | `oxoooo` |  |  |
| `oxoo` | `ooox` | `o` | `ox` | `oxo` | `oxoo` | `oxooo` | `oxoooo` |  |  |
| `oxoo` | `ooxo` | `o` | `ox` | `oxo` | `oxoo` | `oxooo` | `oxoooo` |  |  |
| `oxoo` | `ooxx` | `o` | `ox` | `oxo` | `oxoo` | `oxooo` | `oxoooo` |  |  |
| `oxoo` | `oxoo` | `o` | `ox` | `oxo` | `oxoo` | `oxooo` | `oxooox` |  |  |
| `oxoo` | `oxox` | `o` | `ox` | `oxo` | `oxoo` | `oxooo` | `oxooox` |  |  |
| `oxoo` | `oxxo` | `o` | `ox` | `oxo` | `oxoo` | `oxooo` | `oxooox` |  |  |
| `oxoo` | `oxxx` | `o` | `ox` | `oxo` | `oxoo` | `oxooo` | `oxooox` |  |  |
| `oxoo` | `xooo` | `o` | `ox` | `oxo` | `oxoo` | `oxoox` | `oxooxo` |  |  |
| `oxoo` | `xoox` | `o` | `ox` | `oxo` | `oxoo` | `oxoox` | `oxooxo` |  |  |
| `oxoo` | `xoxo` | `o` | `ox` | `oxo` | `oxoo` | `oxoox` | `oxooxo` |  |  |
| `oxoo` | `xoxx` | `o` | `ox` | `oxo` | `oxoo` | `oxoox` | `oxooxo` |  |  |
| `oxoo` | `xxoo` | `o` | `ox` | `oxo` | `oxoo` | `oxoox` | `oxooxx` |  |  |
| `oxoo` | `xxox` | `o` | `ox` | `oxo` | `oxoo` | `oxoox` | `oxooxx` |  |  |
| `oxoo` | `xxxo` | `o` | `ox` | `oxo` | `oxoo` | `oxoox` | `oxooxx` |  |  |
| `oxoo` | `xxxx` | `o` | `ox` | `oxo` | `oxoo` | `oxoox` | `oxooxx` |  |  |
| `oxox` | `oooo` | `o` | `ox` | `oxo` | `oxox` | `oxoxo` | `oxoxoo` |  |  |
| `oxox` | `ooox` | `o` | `ox` | `oxo` | `oxox` | `oxoxo` | `oxoxoo` |  |  |
| `oxox` | `ooxo` | `o` | `ox` | `oxo` | `oxox` | `oxoxo` | `oxoxoo` |  |  |
| `oxox` | `ooxx` | `o` | `ox` | `oxo` | `oxox` | `oxoxo` | `oxoxoo` |  |  |
| `oxox` | `oxoo` | `o` | `ox` | `oxo` | `oxox` | `oxoxo` | `oxoxox` |  |  |
| `oxox` | `oxox` | `o` | `ox` | `oxo` | `oxox` | `oxoxo` | `oxoxox` |  |  |
| `oxox` | `oxxo` | `o` | `ox` | `oxo` | `oxox` | `oxoxo` | `oxoxox` |  |  |
| `oxox` | `oxxx` | `o` | `ox` | `oxo` | `oxox` | `oxoxo` | `oxoxox` |  |  |
| `oxox` | `xooo` | `o` | `ox` | `oxo` | `oxox` | `oxoxx` | `oxoxxo` |  |  |
| `oxox` | `xoox` | `o` | `ox` | `oxo` | `oxox` | `oxoxx` | `oxoxxo` |  |  |
| `oxox` | `xoxo` | `o` | `ox` | `oxo` | `oxox` | `oxoxx` | `oxoxxo` |  |  |
| `oxox` | `xoxx` | `o` | `ox` | `oxo` | `oxox` | `oxoxx` | `oxoxxo` |  |  |
| `oxox` | `xxoo` | `o` | `ox` | `oxo` | `oxox` | `oxoxx` | `oxoxxx` |  |  |
| `oxox` | `xxox` | `o` | `ox` | `oxo` | `oxox` | `oxoxx` | `oxoxxx` |  |  |
| `oxox` | `xxxo` | `o` | `ox` | `oxo` | `oxox` | `oxoxx` | `oxoxxx` |  |  |
| `oxox` | `xxxx` | `o` | `ox` | `oxo` | `oxox` | `oxoxx` | `oxoxxx` |  |  |
| `oxxo` | `oooo` | `o` | `ox` | `oxx` | `oxxo` | `oxxoo` | `oxxooo` |  |  |
| `oxxo` | `ooox` | `o` | `ox` | `oxx` | `oxxo` | `oxxoo` | `oxxooo` |  |  |
| `oxxo` | `ooxo` | `o` | `ox` | `oxx` | `oxxo` | `oxxoo` | `oxxooo` |  |  |
| `oxxo` | `ooxx` | `o` | `ox` | `oxx` | `oxxo` | `oxxoo` | `oxxooo` |  |  |
| `oxxo` | `oxoo` | `o` | `ox` | `oxx` | `oxxo` | `oxxoo` | `oxxoox` |  |  |
| `oxxo` | `oxox` | `o` | `ox` | `oxx` | `oxxo` | `oxxoo` | `oxxoox` |  |  |
| `oxxo` | `oxxo` | `o` | `ox` | `oxx` | `oxxo` | `oxxoo` | `oxxoox` |  |  |
| `oxxo` | `oxxx` | `o` | `ox` | `oxx` | `oxxo` | `oxxoo` | `oxxoox` |  |  |
| `oxxo` | `xooo` | `o` | `ox` | `oxx` | `oxxo` | `oxxox` | `oxxoxo` |  |  |
| `oxxo` | `xoox` | `o` | `ox` | `oxx` | `oxxo` | `oxxox` | `oxxoxo` |  |  |
| `oxxo` | `xoxo` | `o` | `ox` | `oxx` | `oxxo` | `oxxox` | `oxxoxo` |  |  |
| `oxxo` | `xoxx` | `o` | `ox` | `oxx` | `oxxo` | `oxxox` | `oxxoxo` |  |  |
| `oxxo` | `xxoo` | `o` | `ox` | `oxx` | `oxxo` | `oxxox` | `oxxoxx` |  |  |
| `oxxo` | `xxox` | `o` | `ox` | `oxx` | `oxxo` | `oxxox` | `oxxoxx` |  |  |
| `oxxo` | `xxxo` | `o` | `ox` | `oxx` | `oxxo` | `oxxox` | `oxxoxx` |  |  |
| `oxxo` | `xxxx` | `o` | `ox` | `oxx` | `oxxo` | `oxxox` | `oxxoxx` |  |  |
| `oxxx` | `oooo` | `o` | `ox` | `oxx` | `oxxx` | `oxxxo` | `oxxxoo` |  |  |
| `oxxx` | `ooox` | `o` | `ox` | `oxx` | `oxxx` | `oxxxo` | `oxxxoo` |  |  |
| `oxxx` | `ooxo` | `o` | `ox` | `oxx` | `oxxx` | `oxxxo` | `oxxxoo` |  |  |
| `oxxx` | `ooxx` | `o` | `ox` | `oxx` | `oxxx` | `oxxxo` | `oxxxoo` |  |  |
| `oxxx` | `oxoo` | `o` | `ox` | `oxx` | `oxxx` | `oxxxo` | `oxxxox` |  |  |
| `oxxx` | `oxox` | `o` | `ox` | `oxx` | `oxxx` | `oxxxo` | `oxxxox` |  |  |
| `oxxx` | `oxxo` | `o` | `ox` | `oxx` | `oxxx` | `oxxxo` | `oxxxox` |  |  |
| `oxxx` | `oxxx` | `o` | `ox` | `oxx` | `oxxx` | `oxxxo` | `oxxxox` |  |  |
| `oxxx` | `xooo` | `o` | `ox` | `oxx` | `oxxx` | `oxxxx` | `oxxxxo` |  |  |
| `oxxx` | `xoox` | `o` | `ox` | `oxx` | `oxxx` | `oxxxx` | `oxxxxo` |  |  |
| `oxxx` | `xoxo` | `o` | `ox` | `oxx` | `oxxx` | `oxxxx` | `oxxxxo` |  |  |
| `oxxx` | `xoxx` | `o` | `ox` | `oxx` | `oxxx` | `oxxxx` | `oxxxxo` |  |  |
| `oxxx` | `xxoo` | `o` | `ox` | `oxx` | `oxxx` | `oxxxx` | `oxxxxx` |  |  |
| `oxxx` | `xxox` | `o` | `ox` | `oxx` | `oxxx` | `oxxxx` | `oxxxxx` |  |  |
| `oxxx` | `xxxo` | `o` | `ox` | `oxx` | `oxxx` | `oxxxx` | `oxxxxx` |  |  |
| `oxxx` | `xxxx` | `o` | `ox` | `oxx` | `oxxx` | `oxxxx` | `oxxxxx` |  |  |
| `xooo` | `oooo` | `x` | `xo` | `xoo` | `xooo` | `xoooo` | `xooooo` |  |  |
| `xooo` | `ooox` | `x` | `xo` | `xoo` | `xooo` | `xoooo` | `xooooo` |  |  |
| `xooo` | `ooxo` | `x` | `xo` | `xoo` | `xooo` | `xoooo` | `xooooo` |  |  |
| `xooo` | `ooxx` | `x` | `xo` | `xoo` | `xooo` | `xoooo` | `xooooo` |  |  |
| `xooo` | `oxoo` | `x` | `xo` | `xoo` | `xooo` | `xoooo` | `xoooox` |  |  |
| `xooo` | `oxox` | `x` | `xo` | `xoo` | `xooo` | `xoooo` | `xoooox` |  |  |
| `xooo` | `oxxo` | `x` | `xo` | `xoo` | `xooo` | `xoooo` | `xoooox` |  |  |
| `xooo` | `oxxx` | `x` | `xo` | `xoo` | `xooo` | `xoooo` | `xoooox` |  |  |
| `xooo` | `xooo` | `x` | `xo` | `xoo` | `xooo` | `xooox` | `xoooxo` |  |  |
| `xooo` | `xoox` | `x` | `xo` | `xoo` | `xooo` | `xooox` | `xoooxo` |  |  |
| `xooo` | `xoxo` | `x` | `xo` | `xoo` | `xooo` | `xooox` | `xoooxo` |  |  |
| `xooo` | `xoxx` | `x` | `xo` | `xoo` | `xooo` | `xooox` | `xoooxo` |  |  |
| `xooo` | `xxoo` | `x` | `xo` | `xoo` | `xooo` | `xooox` | `xoooxx` |  |  |
| `xooo` | `xxox` | `x` | `xo` | `xoo` | `xooo` | `xooox` | `xoooxx` |  |  |
| `xooo` | `xxxo` | `x` | `xo` | `xoo` | `xooo` | `xooox` | `xoooxx` |  |  |
| `xooo` | `xxxx` | `x` | `xo` | `xoo` | `xooo` | `xooox` | `xoooxx` |  |  |
| `xoox` | `oooo` | `x` | `xo` | `xoo` | `xoox` | `xooxo` | `xooxoo` |  |  |
| `xoox` | `ooox` | `x` | `xo` | `xoo` | `xoox` | `xooxo` | `xooxoo` |  |  |
| `xoox` | `ooxo` | `x` | `xo` | `xoo` | `xoox` | `xooxo` | `xooxoo` |  |  |
| `xoox` | `ooxx` | `x` | `xo` | `xoo` | `xoox` | `xooxo` | `xooxoo` |  |  |
| `xoox` | `oxoo` | `x` | `xo` | `xoo` | `xoox` | `xooxo` | `xooxox` |  |  |
| `xoox` | `oxox` | `x` | `xo` | `xoo` | `xoox` | `xooxo` | `xooxox` |  |  |
| `xoox` | `oxxo` | `x` | `xo` | `xoo` | `xoox` | `xooxo` | `xooxox` |  |  |
| `xoox` | `oxxx` | `x` | `xo` | `xoo` | `xoox` | `xooxo` | `xooxox` |  |  |
| `xoox` | `xooo` | `x` | `xo` | `xoo` | `xoox` | `xooxx` | `xooxxo` |  |  |
| `xoox` | `xoox` | `x` | `xo` | `xoo` | `xoox` | `xooxx` | `xooxxo` |  |  |
| `xoox` | `xoxo` | `x` | `xo` | `xoo` | `xoox` | `xooxx` | `xooxxo` |  |  |
| `xoox` | `xoxx` | `x` | `xo` | `xoo` | `xoox` | `xooxx` | `xooxxo` |  |  |
| `xoox` | `xxoo` | `x` | `xo` | `xoo` | `xoox` | `xooxx` | `xooxxx` |  |  |
| `xoox` | `xxox` | `x` | `xo` | `xoo` | `xoox` | `xooxx` | `xooxxx` |  |  |
| `xoox` | `xxxo` | `x` | `xo` | `xoo` | `xoox` | `xooxx` | `xooxxx` |  |  |
| `xoox` | `xxxx` | `x` | `xo` | `xoo` | `xoox` | `xooxx` | `xooxxx` |  |  |
| `xoxo` | `oooo` | `x` | `xo` | `xox` | `xoxo` | `xoxoo` | `xoxooo` |  |  |
| `xoxo` | `ooox` | `x` | `xo` | `xox` | `xoxo` | `xoxoo` | `xoxooo` |  |  |
| `xoxo` | `ooxo` | `x` | `xo` | `xox` | `xoxo` | `xoxoo` | `xoxooo` |  |  |
| `xoxo` | `ooxx` | `x` | `xo` | `xox` | `xoxo` | `xoxoo` | `xoxooo` |  |  |
| `xoxo` | `oxoo` | `x` | `xo` | `xox` | `xoxo` | `xoxoo` | `xoxoox` |  |  |
| `xoxo` | `oxox` | `x` | `xo` | `xox` | `xoxo` | `xoxoo` | `xoxoox` |  |  |
| `xoxo` | `oxxo` | `x` | `xo` | `xox` | `xoxo` | `xoxoo` | `xoxoox` |  |  |
| `xoxo` | `oxxx` | `x` | `xo` | `xox` | `xoxo` | `xoxoo` | `xoxoox` |  |  |
| `xoxo` | `xooo` | `x` | `xo` | `xox` | `xoxo` | `xoxox` | `xoxoxo` |  |  |
| `xoxo` | `xoox` | `x` | `xo` | `xox` | `xoxo` | `xoxox` | `xoxoxo` |  |  |
| `xoxo` | `xoxo` | `x` | `xo` | `xox` | `xoxo` | `xoxox` | `xoxoxo` |  |  |
| `xoxo` | `xoxx` | `x` | `xo` | `xox` | `xoxo` | `xoxox` | `xoxoxo` |  |  |
| `xoxo` | `xxoo` | `x` | `xo` | `xox` | `xoxo` | `xoxox` | `xoxoxx` |  |  |
| `xoxo` | `xxox` | `x` | `xo` | `xox` | `xoxo` | `xoxox` | `xoxoxx` |  |  |
| `xoxo` | `xxxo` | `x` | `xo` | `xox` | `xoxo` | `xoxox` | `xoxoxx` |  |  |
| `xoxo` | `xxxx` | `x` | `xo` | `xox` | `xoxo` | `xoxox` | `xoxoxx` |  |  |
| `xoxx` | `oooo` | `x` | `xo` | `xox` | `xoxx` | `xoxxo` | `xoxxoo` |  |  |
| `xoxx` | `ooox` | `x` | `xo` | `xox` | `xoxx` | `xoxxo` | `xoxxoo` |  |  |
| `xoxx` | `ooxo` | `x` | `xo` | `xox` | `xoxx` | `xoxxo` | `xoxxoo` |  |  |
| `xoxx` | `ooxx` | `x` | `xo` | `xox` | `xoxx` | `xoxxo` | `xoxxoo` |  |  |
| `xoxx` | `oxoo` | `x` | `xo` | `xox` | `xoxx` | `xoxxo` | `xoxxox` |  |  |
| `xoxx` | `oxox` | `x` | `xo` | `xox` | `xoxx` | `xoxxo` | `xoxxox` |  |  |
| `xoxx` | `oxxo` | `x` | `xo` | `xox` | `xoxx` | `xoxxo` | `xoxxox` |  |  |
| `xoxx` | `oxxx` | `x` | `xo` | `xox` | `xoxx` | `xoxxo` | `xoxxox` |  |  |
| `xoxx` | `xooo` | `x` | `xo` | `xox` | `xoxx` | `xoxxx` | `xoxxxo` |  |  |
| `xoxx` | `xoox` | `x` | `xo` | `xox` | `xoxx` | `xoxxx` | `xoxxxo` |  |  |
| `xoxx` | `xoxo` | `x` | `xo` | `xox` | `xoxx` | `xoxxx` | `xoxxxo` |  |  |
| `xoxx` | `xoxx` | `x` | `xo` | `xox` | `xoxx` | `xoxxx` | `xoxxxo` |  |  |
| `xoxx` | `xxoo` | `x` | `xo` | `xox` | `xoxx` | `xoxxx` | `xoxxxx` |  |  |
| `xoxx` | `xxox` | `x` | `xo` | `xox` | `xoxx` | `xoxxx` | `xoxxxx` |  |  |
| `xoxx` | `xxxo` | `x` | `xo` | `xox` | `xoxx` | `xoxxx` | `xoxxxx` |  |  |
| `xoxx` | `xxxx` | `x` | `xo` | `xox` | `xoxx` | `xoxxx` | `xoxxxx` |  |  |
| `xxoo` | `oooo` | `x` | `xx` | `xxo` | `xxoo` | `xxooo` | `xxoooo` |  |  |
| `xxoo` | `ooox` | `x` | `xx` | `xxo` | `xxoo` | `xxooo` | `xxoooo` |  |  |
| `xxoo` | `ooxo` | `x` | `xx` | `xxo` | `xxoo` | `xxooo` | `xxoooo` |  |  |
| `xxoo` | `ooxx` | `x` | `xx` | `xxo` | `xxoo` | `xxooo` | `xxoooo` |  |  |
| `xxoo` | `oxoo` | `x` | `xx` | `xxo` | `xxoo` | `xxooo` | `xxooox` |  |  |
| `xxoo` | `oxox` | `x` | `xx` | `xxo` | `xxoo` | `xxooo` | `xxooox` |  |  |
| `xxoo` | `oxxo` | `x` | `xx` | `xxo` | `xxoo` | `xxooo` | `xxooox` |  |  |
| `xxoo` | `oxxx` | `x` | `xx` | `xxo` | `xxoo` | `xxooo` | `xxooox` |  |  |
| `xxoo` | `xooo` | `x` | `xx` | `xxo` | `xxoo` | `xxoox` | `xxooxo` |  |  |
| `xxoo` | `xoox` | `x` | `xx` | `xxo` | `xxoo` | `xxoox` | `xxooxo` |  |  |
| `xxoo` | `xoxo` | `x` | `xx` | `xxo` | `xxoo` | `xxoox` | `xxooxo` |  |  |
| `xxoo` | `xoxx` | `x` | `xx` | `xxo` | `xxoo` | `xxoox` | `xxooxo` |  |  |
| `xxoo` | `xxoo` | `x` | `xx` | `xxo` | `xxoo` | `xxoox` | `xxooxx` |  |  |
| `xxoo` | `xxox` | `x` | `xx` | `xxo` | `xxoo` | `xxoox` | `xxooxx` |  |  |
| `xxoo` | `xxxo` | `x` | `xx` | `xxo` | `xxoo` | `xxoox` | `xxooxx` |  |  |
| `xxoo` | `xxxx` | `x` | `xx` | `xxo` | `xxoo` | `xxoox` | `xxooxx` |  |  |
| `xxox` | `oooo` | `x` | `xx` | `xxo` | `xxox` | `xxoxo` | `xxoxoo` |  |  |
| `xxox` | `ooox` | `x` | `xx` | `xxo` | `xxox` | `xxoxo` | `xxoxoo` |  |  |
| `xxox` | `ooxo` | `x` | `xx` | `xxo` | `xxox` | `xxoxo` | `xxoxoo` |  |  |
| `xxox` | `ooxx` | `x` | `xx` | `xxo` | `xxox` | `xxoxo` | `xxoxoo` |  |  |
| `xxox` | `oxoo` | `x` | `xx` | `xxo` | `xxox` | `xxoxo` | `xxoxox` |  |  |
| `xxox` | `oxox` | `x` | `xx` | `xxo` | `xxox` | `xxoxo` | `xxoxox` |  |  |
| `xxox` | `oxxo` | `x` | `xx` | `xxo` | `xxox` | `xxoxo` | `xxoxox` |  |  |
| `xxox` | `oxxx` | `x` | `xx` | `xxo` | `xxox` | `xxoxo` | `xxoxox` |  |  |
| `xxox` | `xooo` | `x` | `xx` | `xxo` | `xxox` | `xxoxx` | `xxoxxo` |  |  |
| `xxox` | `xoox` | `x` | `xx` | `xxo` | `xxox` | `xxoxx` | `xxoxxo` |  |  |
| `xxox` | `xoxo` | `x` | `xx` | `xxo` | `xxox` | `xxoxx` | `xxoxxo` |  |  |
| `xxox` | `xoxx` | `x` | `xx` | `xxo` | `xxox` | `xxoxx` | `xxoxxo` |  |  |
| `xxox` | `xxoo` | `x` | `xx` | `xxo` | `xxox` | `xxoxx` | `xxoxxx` |  |  |
| `xxox` | `xxox` | `x` | `xx` | `xxo` | `xxox` | `xxoxx` | `xxoxxx` |  |  |
| `xxox` | `xxxo` | `x` | `xx` | `xxo` | `xxox` | `xxoxx` | `xxoxxx` |  |  |
| `xxox` | `xxxx` | `x` | `xx` | `xxo` | `xxox` | `xxoxx` | `xxoxxx` |  |  |
| `xxxo` | `oooo` | `x` | `xx` | `xxx` | `xxxo` | `xxxoo` | `xxxooo` |  |  |
| `xxxo` | `ooox` | `x` | `xx` | `xxx` | `xxxo` | `xxxoo` | `xxxooo` |  |  |
| `xxxo` | `ooxo` | `x` | `xx` | `xxx` | `xxxo` | `xxxoo` | `xxxooo` |  |  |
| `xxxo` | `ooxx` | `x` | `xx` | `xxx` | `xxxo` | `xxxoo` | `xxxooo` |  |  |
| `xxxo` | `oxoo` | `x` | `xx` | `xxx` | `xxxo` | `xxxoo` | `xxxoox` |  |  |
| `xxxo` | `oxox` | `x` | `xx` | `xxx` | `xxxo` | `xxxoo` | `xxxoox` |  |  |
| `xxxo` | `oxxo` | `x` | `xx` | `xxx` | `xxxo` | `xxxoo` | `xxxoox` |  |  |
| `xxxo` | `oxxx` | `x` | `xx` | `xxx` | `xxxo` | `xxxoo` | `xxxoox` |  |  |
| `xxxo` | `xooo` | `x` | `xx` | `xxx` | `xxxo` | `xxxox` | `xxxoxo` |  |  |
| `xxxo` | `xoox` | `x` | `xx` | `xxx` | `xxxo` | `xxxox` | `xxxoxo` |  |  |
| `xxxo` | `xoxo` | `x` | `xx` | `xxx` | `xxxo` | `xxxox` | `xxxoxo` |  |  |
| `xxxo` | `xoxx` | `x` | `xx` | `xxx` | `xxxo` | `xxxox` | `xxxoxo` |  |  |
| `xxxo` | `xxoo` | `x` | `xx` | `xxx` | `xxxo` | `xxxox` | `xxxoxx` |  |  |
| `xxxo` | `xxox` | `x` | `xx` | `xxx` | `xxxo` | `xxxox` | `xxxoxx` |  |  |
| `xxxo` | `xxxo` | `x` | `xx` | `xxx` | `xxxo` | `xxxox` | `xxxoxx` |  |  |
| `xxxo` | `xxxx` | `x` | `xx` | `xxx` | `xxxo` | `xxxox` | `xxxoxx` |  |  |
| `xxxx` | `oooo` | `x` | `xx` | `xxx` | `xxxx` | `xxxxo` | `xxxxoo` |  |  |
| `xxxx` | `ooox` | `x` | `xx` | `xxx` | `xxxx` | `xxxxo` | `xxxxoo` |  |  |
| `xxxx` | `ooxo` | `x` | `xx` | `xxx` | `xxxx` | `xxxxo` | `xxxxoo` |  |  |
| `xxxx` | `ooxx` | `x` | `xx` | `xxx` | `xxxx` | `xxxxo` | `xxxxoo` |  |  |
| `xxxx` | `oxoo` | `x` | `xx` | `xxx` | `xxxx` | `xxxxo` | `xxxxox` |  |  |
| `xxxx` | `oxox` | `x` | `xx` | `xxx` | `xxxx` | `xxxxo` | `xxxxox` |  |  |
| `xxxx` | `oxxo` | `x` | `xx` | `xxx` | `xxxx` | `xxxxo` | `xxxxox` |  |  |
| `xxxx` | `oxxx` | `x` | `xx` | `xxx` | `xxxx` | `xxxxo` | `xxxxox` |  |  |
| `xxxx` | `xooo` | `x` | `xx` | `xxx` | `xxxx` | `xxxxx` | `xxxxxo` |  |  |
| `xxxx` | `xoox` | `x` | `xx` | `xxx` | `xxxx` | `xxxxx` | `xxxxxo` |  |  |
| `xxxx` | `xoxo` | `x` | `xx` | `xxx` | `xxxx` | `xxxxx` | `xxxxxo` |  |  |
| `xxxx` | `xoxx` | `x` | `xx` | `xxx` | `xxxx` | `xxxxx` | `xxxxxo` |  |  |
| `xxxx` | `xxoo` | `x` | `xx` | `xxx` | `xxxx` | `xxxxx` | `xxxxxx` |  |  |
| `xxxx` | `xxox` | `x` | `xx` | `xxx` | `xxxx` | `xxxxx` | `xxxxxx` |  |  |
| `xxxx` | `xxxo` | `x` | `xx` | `xxx` | `xxxx` | `xxxxx` | `xxxxxx` |  |  |
| `xxxx` | `xxxx` | `x` | `xx` | `xxx` | `xxxx` | `xxxxx` | `xxxxxx` |  |  |

## Formal Anchors

- R4 carrier: `formal/SSBX/Foundation/Hierarchy/R4_Mian.lean` and `formal/SSBX/Foundation/Bagua/BenZheng.lean`.
- R5 view: `formal/SSBX/Foundation/Wen/V4Kernel/WenR5.lean`, where R5 is `V4 x V4 x Bool`.
- R6 view: `formal/SSBX/Foundation/Wen/V4Kernel/WenR6.lean`, where R6 is the full `Word64 = V4 x V4 x V4` and bridges to `Hexagram`.
- This table is a documentation-level projection sheet. It does not define R7 or R8 semantics.
