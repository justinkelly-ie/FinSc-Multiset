# Stage 1 Carrier Refactoring Log

## Overview
This log documents the constructivist architectural improvements, deforestation, and type-driven generalizations applied to `Stage1/Carrier` in `FinSc-Multiset`, satisfying **Rule 01** (elaborator reflection), **Rule 02** (toolbox workflow), **Rule 03** (constructivist physical laws), and **Rule 04** (QTT & performance scaling).

---

## 1. Generalized Inner Product (`CellMultiset.idr`)
- **Dimension-Polymorphic Inner Product**:
  Generalized inner product from 1D-restricted vectors to arbitrary dimension-indexed multisets:
  ```idris
  public export
  dotCellMultiset : {dim : Nat} -> CellMultiset dim -> CellMultiset dim -> BoxInt
  ```
  Computed via the intersection multiset $\mathcal{M}_1 \cap \mathcal{M}_2$ and summing component coordinate products.
- **Deforested Support Streams**:
  Exported `supportCellMultisetStream`, `supportVexelStream`, and `supportMaxelStream` operating in $O(1)$ auxiliary registers without intermediate `List` materialization (Rule 04 §8).
- **Stream Conversions**:
  Added zero-allocation tree steppers `streamCellMultiset` and accumulator `streamToCellMultiset` alongside `dotCellMultisetStream`.

---

## 2. Dedicated Dimension Carrier Hierarchy (1D Vexel, 2D Maxel, 3D Boxel, 4D HyperBoxel)
Created dedicated coordinate modules with backward-compatible aliases for downstream packages:

### `Stage1.Carrier.Vexel` (1D Vector Carrier)
- **Specialized 1D Operations**: `dotProduct`, `dotProductStream`, `scaleVexel`, `addVexel`, `subVexel`, `normL1Vexel`, `emptyVexel`, `compressVexel`.
- **Constructors & Aliases**:
  - `MkVexelTree : BoxMultisetTree Unixel -> Vexel` (used in `FinSc-Thermodynamics`)
  - `MkVexel`, `mkVexel : List (Unixel, BoxInt) -> Vexel` (used in `FinSc-Action-Dynamics`, `FinSc-Cosmos`)
  - `canonicalizeVexel : Vexel -> Vexel`
  - `vexelTerms`, `terms : Vexel -> List (Unixel, BoxInt)`
  - `nucleonQuarkVexel : Vexel` (Baryon singlet color charges [1], [2], [3])

### `Stage1.Carrier.Maxel` (2D Discrete Matrix Carrier)
- **Specialized 2D Operations**: `dotProduct`, `mul`, `mulMaxelStream`, `mulStream`, `scaleMaxel`, `addMaxel`, `subMaxel`, `normL1Maxel`, `emptyMaxel`.
- **Deforested Matrix Multiplication**:
  `mulMaxelStream` streams matrix products via `streamTensorProduct` without intermediate matrix tree allocations.
- **Constructors & Aliases**:
  - `MkMaxelTree : BoxMultisetTree Pixel -> Maxel`
  - `MkMaxel`, `mkMaxel : List (Pixel, BoxInt) -> Maxel`
  - `canonicalizeMaxel : Maxel -> Maxel`
  - `maxelPixels`, `pixels : Maxel -> List (Pixel, BoxInt)`
  - `waterMoleculeBonds : Maxel` (molecular bond connectivity)

### `Stage1.Carrier.Boxel` (3D Discrete Volume Carrier)
- **Specialized 3D Operations**: `dotProduct`, `dotBoxel`, `dotProductStream`, `scaleBoxel`, `addBoxel`, `subBoxel`, `normL1Boxel`, `totalBoxelWeight`, `emptyBoxel`, `compressBoxel`.
- **Constructors & Aliases**:
  - `MkBoxelTree : BoxMultisetTree Voxel -> Boxel`
  - `MkBoxel`, `mkBoxel : List (Voxel, BoxInt) -> Boxel`
  - `canonicalizeBoxel : Boxel -> Boxel`
  - `voxels : Boxel -> List (Voxel, BoxInt)`
  - `lookupVoxel : Voxel -> Boxel -> BoxInt`
- **Projections & Products**:
  - `wedgeVexelMaxel : Vexel -> Maxel -> Boxel`
  - `outerProductVexelMaxel : Vexel -> Maxel -> Boxel`
  - `sliceBoxelZ`, `sliceBoxelY`, `sliceBoxelX : Nat -> Boxel -> Maxel`

### `Stage1.Carrier.HyperBoxel` (4D Spatiotemporal Tensor Carrier)
- **Specialized 4D Operations**: `dotProduct`, `dotHyperBoxel`, `dotProductStream`, `scaleHyperBoxel`, `addHyperBoxel`, `subHyperBoxel`, `normL1HyperBoxel`, `totalHyperBoxelWeight`, `emptyHyperBoxel`, `compressHyperBoxel`.
- **Constructors & Aliases**:
  - `MkHyperBoxelTree : BoxMultisetTree Tesseract -> HyperBoxel`
  - `MkHyperBoxel`, `mkHyperBoxel : List (Tesseract, BoxInt) -> HyperBoxel`
  - `canonicalizeHyperBoxel : HyperBoxel -> HyperBoxel`
  - `hyperBoxels : HyperBoxel -> List (Tesseract, BoxInt)`
  - `lookupTesseract : Tesseract -> HyperBoxel -> BoxInt`
- **Spatiotemporal Products & Slicing**:
  - `sliceHyperBoxelT : Nat -> HyperBoxel -> Boxel`
  - `outerProductVexelBoxel : Vexel -> Boxel -> HyperBoxel`
  - `auditHyperBoxelSliceProof : Bool`

---

## 3. Logarithmic Scaling & Active Consolidation (`SquareMaxel.idr`)
- **Rule 04 §9 Compliance**:
  - Implemented `compressSquareMaxel` to prune zero-weight entries and collapse duplicate coordinates.
  - Enforced active support consolidation after every squaring step in `fastSquareMaxelPower`:
    ```idris
    let half = fastSquareMaxelPower fuel m (halfExp n)
        halfSq = compressSquareMaxel (mulSquareMaxel half half)
    ```
    Bounding representation size to at most $\text{dim}^2$ terms during $O(\log N)$ repeated squaring.
- **Model-Derived Cyclotomic Goh Fuel**:
  - Added `fastSquareMaxelPowerGoh` using `gohFuelNat (dim * dim + exp)`.

---

## 4. Deforestation & Elimination of `Data.List` (`BalanceArray.idr`)
- Removed unused legacy list utility `allFinList`.
- Removed `import Data.List`.
- Added deforested streaming linear combination `linearComboVexelStream`.
- Verified zero occurrences of `import Data.List` across the entire `Stage1/Carrier` subsystem.

---

## 5. Downstream Ecosystem Alignment & Prototype Graduation
- **Prototype Graduation (Rule 04 §11)**:
  Graduated prototype implementations of `streamCellMultiset` and `streamToCellMultiset` into canonical `CellMultiset.idr`, pruning duplicate local prototypes from `FinSc-Metric-Substrate/src/Stage1/VexelStream.idr` to eliminate ambiguous elaboration.
- **Full Verification**:
  Rebuilt and installed `FinSc-Multiset`, `FinSc-Metric-Substrate`, `FinSc-Thermodynamics`, and `FinSc-Action-Dynamics`, followed by ecosystem-wide verification via `build-all.sh`.
