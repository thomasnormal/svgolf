# layout.tcl : read a finished run's 6_final.odb (read-only mount) and draw it with OpenROAD's own GUI renderer,
# off-screen, the way the flow's final_outputs.tcl does (gui::show "source save_images.tcl" false).
puts "layout.tcl: ODB_FILE=$::env(ODB_FILE) OUT_PNG=$::env(OUT_PNG) IMG_WIDTH=$::env(IMG_WIDTH)"
read_db $::env(ODB_FILE)
set block [ord::get_db_block]
set die [$block getDieArea]
set core [$block getCoreArea]
puts [format "layout.tcl: dbu_per_micron %d die %d %d %d %d core %d %d %d %d" [$block getDbUnitsPerMicron] \
  [$die xMin] [$die yMin] [$die xMax] [$die yMax] [$core xMin] [$core yMin] [$core xMax] [$core yMax]]
gui::show "source /work/tools/draw.tcl" false
puts "layout.tcl: done"
