# Massive amplitude reduction

Keep the folder structure intact. Python constructs catalogs; Mathematica reduces supplied amplitudes. These are independent workflows.

## Mathematica examples

Open Mathematica/AmplitudeReduceExamples.nb and evaluate its input cells in order in a fresh kernel (Wolfram 14.2). It runs the three manuscript benchmarks: a four-vector open chain, a two-fermion/two-vector trace, and a five-point four-vector/scalar amplitude, with interactive reduction histories. Expected collected term counts are 15, 22, 31, and sequential derivation lengths are 14, 24, 37. Keep the four accompanying .m packages and JSON data together. Initial loading is separate from reduction.

The default catalog is four-point. After loading the package, select any supplied catalog using:

```wolfram
LoadRuleCatalog[FileNameJoin[{NotebookDirectory[], "NativeRules_n3.json"}]]
```

Replace n3 with n4 or n5 to switch particle count. Switching catalogs clears the previous in-memory preparations and loads compatible supplied preparations.

Use ab[i,j], sb[i,j], s[i,j] = 2 p_i.p_j, SpinorChain and TensorTrace as illustrated in the notebooks. Masses remain symbolic. AmplitudeReduce[amp, AutoSavePreparedData -> False] returns the reduced expression without saving newly prepared replacements. UsePreparedData -> False bypasses existing preparations for that query; preparing new contractions can be substantially slower, particularly at five points. The implementation accepts bracket degree up to 16, but this is not a guarantee of complete catalog coverage. Generic five-point native preparation remains experimental.

By default, compatible preparations are reused for the same complete tensor monomial and contraction pattern. Enabling automatic saving merges new preparations into an existing compatible preparation file. No three-point preparation file is bundled; its preparations are held in memory. ReductionSteps displays recorded histories. PreparationProofs.json contains the derivations behind supplied prepared applications, not additional independent rules.

## Python catalog construction

From the Python directory, use Python 3 with SymPy:

```sh
python -m venv .venv
# Activate .venv for your operating system.
python -m pip install -r requirements.txt
python source/run_compact_queue.py --particles 3 --degree 4 --out runs/n3_d4
python source/run_compact_queue.py --particles 4 --degree 8 --out runs/n4_d8
python source/run_parallel_s_capped.py --particles 5 --degree 6 --workers 1 --s-workers 1 --out runs/n5_d6
```

Use a new output directory for each fresh construction. Add --resume to the same command to continue a saved run. Construction can take hours and substantial disk space. Keep the complete generated run directory for resumption.

The degree argument bounds retained-rule degree. The five-point driver additionally bounds common overlaps at degree seven. The supplied four-point catalog was extracted from the extended degree-eight run, with 179 retained identities through degree six. The compact catalogs are reference outputs, not restart checkpoints; their summaries record the finite search scope and stopping status. Finite searches do not establish unrestricted completeness.

The source directory retains the imported dependencies of the two construction drivers. Its other modules are implementation dependencies, not additional commands readers need to run.

## Supplied data

Catalogs/n3_d4.json, n4_d6.json and n5_d6.json contain 27, 179 and 1077 identity records, respectively, in construction format. Mathematica uses separate indexed exports: NativeRules_n3.json, NativeRules_n4.json and NativeRules_n5.json. The construction exports cannot be substituted directly for these Mathematica files.
