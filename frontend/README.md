# Shared Transport Frontend

`wire.ml` parses the Lean4export v3.1.0 NDJSON transport into shared immutable OCaml syntax. It performs no typing, conversion, positivity, primitive recognition, or other logical judgment. Each port must independently validate declarations and exported redundant fields.

The frontend preserves structured names, unbounded natural literals, all inductive/constructor/recursor metadata, definition safety, and reducibility hints. Anonymous name and zero level are implicit table entries at index 0. Expressions have no implicit index-0 entry. References must point to existing entries; duplicate IDs/JSON keys and invalid UTF-8 are rejected.

Interface: `Wire.read_file : string -> Wire.export`; `"-"` means stdin. `Wire.export.declarations` contains `(source_line, declaration)` pairs. Input errors carry a line, category and diagnostic. Malformed input maps to exit 1, unsupported format or address/memory/stack limits to exit 2. Unexpected IO/internal faults must be handled separately by each executable wrapper. No file-size cutoff is imposed.

This parser is currently an explicitly trusted transport component; it is not a proved bytes-to-syntax decoder. Formal core theorems must not be described as covering it until a decoder refinement theorem exists. Adapter conversions must preserve all fields or make the relevant feature explicitly unsupported. A successful parse is never a successful proof check.

Dependencies: OCaml, Yojson, Zarith. Build details depend on the project-local toolchain setup. Focused parser tests live here to remain separate from the Arena corpus infrastructure.
