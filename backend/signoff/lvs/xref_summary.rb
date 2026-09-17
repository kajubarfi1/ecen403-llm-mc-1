lvs = RBA::LayoutVsSchematic.new; lvs.read($lvsdb); x = lvs.xref
top = $b.upcase
x.each_circuit_pair do |cp|
  nm = (cp.second ? cp.second.name : cp.first.name).upcase
  st = cp.status.to_s
  if nm == top
    d = n = p = 0; x.each_device_pair(cp) { d += 1 }; x.each_net_pair(cp) { n += 1 }; x.each_pin_pair(cp) { p += 1 }
    puts "XREF top #{st} compared: devices=#{d} nets=#{n} pins=#{p}"
  elsif st != "Match"
    ex = []; x.each_net_pair(cp) { |q| next if q.status.to_s == "Match"; ex << "#{q.first ? q.first.expanded_name : '-'}<->#{q.second ? q.second.expanded_name : '-'}" if ex.size < 3 }
    puts "XREF cell #{nm} #{st} #{ex.join(' | ')}"
  end
end
