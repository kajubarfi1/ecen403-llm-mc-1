# render_gds.rb — PNG of a finished GDS, using the platform layer colours.
#
# usage (inside the ORFS container):
#   klayout -z -nc -rd in_gds=<gds> -rd out_png=<png> [-rd lyp=<file.lyp>]
#           [-rd size=2400] [-rd hide=71,72] [-rd box=x1,y1,x2,y2] -r render_gds.rb
#
#   hide : GDS layer numbers to switch off, e.g. 71,72 hides met4/met5 so the
#          routing underneath is visible (a full-stack view is mostly top metal).
#   box  : zoom to this window in microns instead of the whole die.
#
# -z hides the window, -nc skips the user config, so it works headless
# (with QT_QPA_PLATFORM=offscreen).

size = ($size || "2400").to_i

app = RBA::Application.instance
mw = app.main_window
mw.load_layout($in_gds, 1)
view = mw.current_view

if $lyp && File.exist?($lyp)
  view.load_layer_props($lyp)
  puts "layer properties: #{$lyp}"
end

view.max_hier

if $hide
  hidden = $hide.split(",").map { |s| s.strip.to_i }
  n = 0
  view.each_layer do |lp|
    if hidden.include?(lp.source_layer)
      lp.visible = false
      n += 1
    end
  end
  puts "hidden layers #{hidden.inspect}: #{n} entries"
end

cell = view.active_cellview.cell
full = cell.dbbox
if $box
  x1, y1, x2, y2 = $box.split(",").map { |s| s.strip.to_f }
  view.zoom_box(RBA::DBox.new(x1, y1, x2, y2))
  puts format("zoom: %.1f,%.1f to %.1f,%.1f um", x1, y1, x2, y2)
else
  view.zoom_fit
end
view.update_content

puts format("cell %s  die %.1f x %.1f um", cell.name, full.width, full.height)
view.save_image($out_png, size, size)
puts "wrote #{$out_png} (#{size}x#{size})"
