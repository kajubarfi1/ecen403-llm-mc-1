set -u
cd /OpenROAD-flow-scripts/flow
W=/work/drcneg; SRC=results/sky130hd/config_regs/base/6_final.gds
cat > /tmp/inject.rb <<'RB'
ly = RBA::Layout.new; ly.read($src); top = ly.top_cell
m1 = ly.layer(68, 20)
top.shapes(m1).insert(RBA::Box.new(-6000, -6000, -5950, -5950))   # 0.05um square: < 0.14um min width
top.shapes(m1).insert(RBA::Box.new(-9000, -6000, -8800, -5800))   # two 0.2um squares
top.shapes(m1).insert(RBA::Box.new(-8780, -6000, -8580, -5800))   # 0.02um apart: < 0.14um min spacing
ly.write($out); puts "INJECT wrote #{$out}: 3 illegal met1 shapes (1 width, 1 spacing pair)"
RB
klayout -b -rd src=$SP_DUMMY$SRC -rd out=$W/bad.gds -r /tmp/inject.rb 2>&1 | grep INJECT
for tag in clean bad; do
  g=$SRC; [ $tag = bad ] && g=$W/bad.gds
  scripts/klayout.sh -zz -rd in_gds="$g" -rd report_file=$W/$tag.lyrdb -r platforms/sky130hd/drc/sky130hd.lydrc > $W/$tag.log 2>&1
  items=$(grep -c "<item>" $W/$tag.lyrdb); values=$(grep -c "<value>" $W/$tag.lyrdb)
  cats=$(python3 -c "
import collections, xml.etree.ElementTree as ET
r=ET.parse('$W/$tag.lyrdb').getroot()
c=collections.Counter((i.findtext('category') or '?').strip(\"'\") for i in r.iter('item'))
print(', '.join(f'{k}={v}' for k,v in c.most_common()))")
  echo "DRCNEG $tag  items=$items  orfs_grep_values=$values  categories: ${cats:-none}"
done
