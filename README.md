# satsha3finalists
Benchmarks and source code for the paper

O. Zaikin, V. Davydov, A. Kiryanova. SAT-based analysis of SHA-3 competition finalists // Numerical Methods and Programming. 2024 (in press).

The benchmarks are CNFs which encode preimage attacks on the following round-reduced finalists of the NIST hash function competition:
- BLAKE
- Grøstl
- JH
- Keccak
- Skein

The CNFs were generated via C Bounded Model Checker (CBMC). The corresponding programs for CBMC are provided as well.
