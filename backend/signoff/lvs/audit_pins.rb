# LVS blind-spot audit. KLayout's comparison ignores nets that touch only pins
# (feedthroughs, unused ports). Check them directly against the layout netlist:
#   - every schematic top-level pin exists as a label on some layout net
#   - both ends of every pin-to-pin assign are the same layout net
# Control: rotated (deliberately wrong) pairings must not be accepted.
#
# usage: klayout -b -rd lvsdb=<lvs.lvsdb> -rd b=<design> [-rd base=<results/.../base>] -r audit_pins.rb
require 'set'
b = $b
base = ($base.nil? || $base.to_s.empty?) ? "/OpenROAD-flow-scripts/flow/results/sky130hd/#{b}/base" : $base
lvs = RBA::LayoutVsSchematic.new
lvs.read($lvsdb)
top = nil
lvs.netlist.each_circuit { |c| top = c if c.name.downcase == b.downcase }
if top.nil?
  puts "AUDIT error=no_top_circuit"
else
  netof = {}
  k = 0
  top.each_net { |n| k += 1; n.name.to_s.split(",").each { |l| netof[l.strip] = k } }
  cdl = File.read("#{base}/6_final.cdl").gsub(/\n\+/, " ")
  pins = cdl[/^\.SUBCKT\s+#{Regexp.escape(b)}\s+(.*)$/i, 1].to_s.split
  ps = pins.to_set
  pairs = File.read("#{base}/6_final.v")
              .scan(/^\s*assign\s+(\S+)\s*=\s*([A-Za-z_][\w$]*(?:\[\d+\])?)\s*;/)
              .select { |a, c| ps.include?(a) && ps.include?(c) }
  same = pairs.count { |a, c| netof[a] && netof[a] == netof[c] }
  rot = pairs.each_with_index.map { |(a, _), i| [a, pairs[(i + 1) % pairs.size][1]] }
  wrong = pairs.size > 1 ? rot.count { |a, c| netof[a] && netof[a] == netof[c] } : 0
  miss = pins.reject { |p| netof.key?(p) }
  puts "AUDIT pins_in_layout=#{pins.size - miss.size}/#{pins.size} pin_to_pin_feedthroughs=#{same}/#{pairs.size} control_wrong_pairs_accepted=#{wrong}"
  puts "AUDIT_MISSING #{miss.first(10).join(' ')}" unless miss.empty?
end
