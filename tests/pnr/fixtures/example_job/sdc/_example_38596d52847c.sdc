# A0' asap7 timing setup as SDC (combinational): virtual clock at the A0' delay x 1.0
current_design band
create_clock -name vclk -period 56.0
set_input_delay 0 -clock vclk [all_inputs]
set_output_delay 0 -clock vclk [all_outputs]
set_driving_cell -lib_cell BUFx8_ASAP7_75t_R -pin Y -input_transition_rise 20 -input_transition_fall 20 [all_inputs]
set_load 2.5 [all_outputs]
