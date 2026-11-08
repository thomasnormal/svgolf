IEEE 754 division for every binary format at once: the exponent width `W` and the precision `P` are
parameters, a value is `W + P` bits, and the divider must be right for every `W ≥ 2` and `P ≥ 2`
(binary16 is `(5, 11)`, bfloat16 `(8, 8)`, binary32 `(8, 24)`). Rounding is to nearest with ties to even,
subnormals are kept, and every NaN result is the format's canonical quiet NaN, exactly as the trusted
function `SvGolf.IEEE754.divide` says.

Run-time `/ % **` are banned. The score is taken at `(W, P) = (5, 11)`. The first proved reference, a
word-level netlist with the normalizer and the restoring steps as generate loops, has {{fdivp.area}} and a
{{fdivp.time}} critical path on sky130 ({{fdivp.ge}}, depth {{fdivp.depth}}); par is the proved radix-4 SRT
divider, {{fdivp_srt.area}} at {{fdivp_srt.time}}, {{fdivp_srt.score}}. Each proof covers every format and
every pair of operands.
