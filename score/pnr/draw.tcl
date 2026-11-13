# draw.tcl : the flow's "routing view" (the image's scripts/save_images.tcl, its first two save_image calls: every layer,
# net, instance and shape type visible, the instance-misc overlays off but pins and blockages, the scale bar on, then
# power and ground nets hidden), saved once at a fixed pixel width instead of the flow's height/1000 um per pixel.
gui::clear_highlights -1
gui::clear_selections
gui::fit
gui::set_display_controls "*" visible false
gui::set_display_controls "Layers/*" visible true
gui::set_display_controls "Nets/*" visible true
gui::set_display_controls "Instances/*" visible true
gui::set_display_controls "Shape Types/*" visible true
gui::set_display_controls "Misc/Instances/*" visible false
gui::set_display_controls "Misc/Instances/Pins" visible true
gui::set_display_controls "Misc/Instances/Blockages" visible true
gui::set_display_controls "Misc/Scale bar" visible true
gui::set_display_controls "Misc/Highlight selected" visible true
gui::set_display_controls "Misc/Detailed view" visible true
gui::set_display_controls "Nets/Power" visible false
gui::set_display_controls "Nets/Ground" visible false
save_image -width $::env(IMG_WIDTH) $::env(OUT_PNG)
