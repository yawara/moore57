# Instances

The extend15 tooling expects the following fixtures:

```text
instances/star35/star_factor_heuristic_partial.json
instances/seed14/dfs_extend_t10_solution.json
instances/seed14/verified_broad_t10.json
```

`verified_broad_t10.json` is included in this PR. The larger `star35` and `seed14` JSON artifacts are generated from the previous local search run and should be copied from the accompanying scaffold tarball if they are not already present.

The loader in `src/moore57/io.py` also supports chunked base64 fixtures named like:

```text
foo.json.b64.00
foo.json.b64.01
...
```

and will reconstruct `foo.json` logically when `read_json("foo.json")` is called.
