#!/bin/bash
# olympus_vmanager.sh — start the vManager server + GUI on an Olympus
# COMPUTE node. Run inside an interactive allocation with X11:
#
#     srun --partition=adademic --qos=olympus-academic --x11 --pty bash -l
#     bash ~/olympus_vmanager.sh
#
# One-time setup (user-local postgres db on port 5488 + server profile on
# port 8088) was already created under ~/vmgr; this just brings it up.
# The Cadence tree is mounted on compute nodes only — this will not work
# on olympus-login.
#
# ONE-TIME after first launch: coverage analysis needs the project's
# Simulator Version set. From the Mac:
#     ssh -L 8088:<compute-node>:8088 jacobz@olympus.ece.tamu.edu
# then browse http://localhost:8088 (login vmgr/vmgrpass) ->
# System Settings -> Projects -> Simulator Version =
# /opt/coe/cadence/XCELIUM240. Stored in the ~/vmgr database; survives
# restarts. GUI login uses the same vmgr/vmgrpass credentials.

VM=/opt/coe/cadence/VMANAGER/tools.lnx86

# License environment — the server dies with LMC-01902 ("license server
# search path is null") without this. Same setup every xrun run sources.
source /opt/coe/ncsu/ncsu-cdk-1.6.0.beta/ncsu.sh 2>/dev/null

# Xcelium on PATH, inherited by every run and scan the server spawns.
# vm_scan.pl resolves filter files by searching $PATH (vm_scan.pl:1000), and
# xrun reports its own filter, cdns_sim.flt, which ships in tools.lnx86/bin.
# Without this the scan step dies with "Filter file cdns_sim.flt does not
# exist" and every run is marked failed regardless of what it simulated.
export PATH=/opt/coe/cadence/XCELIUM240/tools.lnx86/bin:/opt/coe/cadence/XCELIUM240/tools/bin:$PATH

echo "== starting postgres (db ~/vmgr/db, port 5488)"
if ! $VM/vmgr/postgresql-13.4/bin/pg_ctl -D ~/vmgr/db status >/dev/null 2>&1; then
    $VM/vmgr/postgresql-13.4/bin/pg_ctl -D ~/vmgr/db -l ~/vmgr/pg.log \
        -o "-p 5488" start
    sleep 2
else
    echo "   (already running)"
fi

echo "== starting vManager server (profile ~/vmgr/profile, port 8088)"
$VM/vmgr/admin/vmgrserver -profile ~/vmgr/profile -start
$VM/vmgr/admin/vmgrserver -profile ~/vmgr/profile -status

echo "== launching GUI (connects to localhost:8088)"
$VM/bin/vmanager -gui -server localhost:8088 &

echo ""
echo "When done, shut down cleanly with:"
echo "  $VM/vmgr/admin/vmgrserver -profile ~/vmgr/profile -stop"
echo "  $VM/vmgr/postgresql-13.4/bin/pg_ctl -D ~/vmgr/db stop"
