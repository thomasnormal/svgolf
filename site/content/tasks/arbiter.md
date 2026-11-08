Give the grant to at most one of `N` requesters per cycle, only to one that asks, to someone whenever
anyone asks, and never let a requester ask `N` cycles in a row without being granted. This is svGolf's
first reactive task: a controller that runs for ever, specified by a safety property on every cycle and a
bounded response over the whole input trace, with no assumption about the requesters. The proof covers
every `N` with `1 ≤ N` and `N·N < 2^31`; the score is taken at `N = 8`.

The grant is registered, a Moore output: a clock edge samples `req`, and the grant it decides is on `gnt`
for the whole next clock period, so a grant follows its request by one cycle. No output may depend
combinationally on an input. The claims hold from every power-up value of every register, the first reset
included, so a register that is never reset may only hold a value that does not matter; no construct may
create an unknown value, and a register that is never loaded is refused. Run-time `/ % **` are banned. Any
fair policy is allowed (round-robin pointer or mask, rotating priority, a matrix), so the task is the
policy and its state. The score is the area, flip-flops included, times the register-to-register clock
period, one decision per cycle. The bound `N` is tight: no design can serve every persistent requester
within `N - 1` cycles.
