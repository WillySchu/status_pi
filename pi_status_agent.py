#!/usr/bin/env python3
"""Status agent for the Pi status board.

Run this on each Raspberry Pi you want to watch. It answers GET /status with a
JSON snapshot: uptime, CPU temperature, memory, disk, the state of the systemd
units you name, and optional DNS lookups. It is read-only and needs no root.

Examples:
    pi_status_agent.py --unit pihole-FTL cloudflared --dns 127.0.0.1
    pi_status_agent.py --unit seattle-permits.timer

Unit names without a suffix are treated as services. For a timer, the agent
also looks at the service it triggers, so a failed run shows up as a problem.

Each DNS check asks the given server for a random name that has never been
looked up before, so the answer cannot come from a cache: any real reply
(including "no such domain") proves the whole chain to the upstream resolver
works. Lookups run in the background every --dns-interval seconds (every 30
seconds while one is failing), which keeps query logs quiet.
"""

import argparse
import json
import os
import shutil
import socket
import struct
import subprocess
import threading
import time
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

UNIT_SUFFIXES = (".service", ".timer", ".socket", ".mount", ".path", ".target")
UINT64_MAX = 2**64 - 1
DNS_TIMEOUT = 3
DNS_RETRY_INTERVAL = 30  # seconds between lookups while one is failing
DNS_RCODES = {0: "NOERROR", 1: "FORMERR", 2: "SERVFAIL", 3: "NXDOMAIN", 5: "REFUSED"}

UNIT_PROPS = ["LoadState", "ActiveState", "SubState", "Unit"]
SERVICE_PROPS = [
    "LoadState", "ActiveState", "SubState", "Type", "Result", "ExecMainStatus",
    "ActiveEnterTimestampMonotonic", "InactiveEnterTimestampMonotonic",
    "ExecMainExitTimestampMonotonic",
]


# ---------------------------------------------------------------- helpers

def run(cmd):
    """Run a command. Return (stdout, problem), where problem is '' or why it failed."""
    try:
        result = subprocess.run(
            cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            universal_newlines=True, timeout=5, env=dict(os.environ, LC_ALL="C"),
        )
    except FileNotFoundError:
        return "", "%s is not installed or not on PATH" % cmd[0]
    except subprocess.TimeoutExpired:
        return "", "%s did not respond within 5 s" % cmd[0]
    except (OSError, subprocess.SubprocessError) as err:
        return "", "%s: %s" % (cmd[0], err)

    problem = ""
    if result.returncode != 0 or not result.stdout.strip():
        lines = result.stderr.strip().splitlines()
        reason = lines[0] if lines else "exit status %d, no output" % result.returncode
        problem = ("%s: %s" % (cmd[0], reason))[:200]
    return result.stdout, problem


def read_file(path):
    try:
        with open(path) as f:
            return f.read()
    except OSError:
        return ""


def monotonic_to_epoch(usec):
    """Convert a systemd monotonic timestamp (microseconds since boot) to Unix time."""
    try:
        usec = int(usec)
    except (TypeError, ValueError):
        return None
    if usec <= 0 or usec >= UINT64_MAX:
        return None
    age = time.clock_gettime(time.CLOCK_MONOTONIC) - usec / 1e6
    return round(time.time() - age)


# ---------------------------------------------------------------- systemd

def systemctl_show(unit, props):
    """Return (properties, problem) for a unit; properties is {} if systemd could not be asked."""
    out, problem = run(["systemctl", "show", unit, "--property=" + ",".join(props)])
    return dict(line.split("=", 1) for line in out.splitlines() if "=" in line), problem


def bus_path(unit):
    """D-Bus object path systemd uses for a unit (non-alphanumerics become _xx)."""
    escaped = "".join(
        c if c.isascii() and c.isalnum() and not (i == 0 and c.isdigit()) else "_%02x" % ord(c)
        for i, c in enumerate(unit)
    )
    return "/org/freedesktop/systemd1/unit/" + escaped


def timer_times(unit):
    """Return (last_trigger, next_run) for a timer as Unix times, or None where unknown.

    Read over D-Bus because it gives raw numbers on every systemd version,
    where `systemctl show` gives locale- and version-dependent date strings.
    """
    out, _ = run([
        "busctl", "get-property", "org.freedesktop.systemd1", bus_path(unit),
        "org.freedesktop.systemd1.Timer",
        "LastTriggerUSec", "NextElapseUSecRealtime", "NextElapseUSecMonotonic",
    ])
    values = []
    for line in out.splitlines():
        parts = line.split()
        if len(parts) == 2 and parts[0] == "t" and parts[1].isdigit():
            values.append(int(parts[1]))
    if len(values) != 3:
        return None, None

    last, next_realtime, next_monotonic = values
    last_trigger = round(last / 1e6) if 0 < last < UINT64_MAX else None
    if 0 < next_realtime < UINT64_MAX:
        next_run = round(next_realtime / 1e6)
    else:
        next_run = monotonic_to_epoch(next_monotonic)
    return last_trigger, next_run


def exit_status(props):
    if props.get("Result") == "exit-code" and props.get("ExecMainStatus", "").isdigit():
        return int(props["ExecMainStatus"])
    return None


def service_status(props):
    active, sub = props.get("ActiveState", "unknown"), props.get("SubState", "")
    info = {"kind": "service", "state": active, "sub": sub}

    if active == "active":
        info.update(ok=True, since=monotonic_to_epoch(props.get("ActiveEnterTimestampMonotonic")))
    elif active == "activating" and sub != "auto-restart":
        info.update(ok=True)  # starting up, or a one-shot job mid-run
    elif props.get("Type") == "oneshot" and active == "inactive" and props.get("Result") == "success":
        # A one-shot job is normally inactive between runs; that is healthy.
        info.update(ok=True, kind="oneshot",
                    last_run=monotonic_to_epoch(props.get("ExecMainExitTimestampMonotonic")))
    else:
        info.update(ok=False, since=monotonic_to_epoch(props.get("InactiveEnterTimestampMonotonic")),
                    exit_status=exit_status(props))
    return info


def timer_status(name, props):
    service = props.get("Unit") or name[: -len(".timer")] + ".service"
    svc, _ = systemctl_show(service, SERVICE_PROPS)
    last_trigger, next_run = timer_times(name)

    finished = monotonic_to_epoch(svc.get("ExecMainExitTimestampMonotonic"))
    failed = svc.get("ActiveState") == "failed" or svc.get("Result", "success") != "success"
    scheduled = props.get("ActiveState") == "active"
    return {
        "kind": "timer",
        "state": props.get("ActiveState", "unknown"),
        "sub": props.get("SubState", ""),
        "triggers": service,
        "running": svc.get("ActiveState") == "activating",
        "last_run": finished or last_trigger,
        "last_ok": None if (finished is None and not failed) else not failed,
        "exit_status": exit_status(svc),
        "next_run": next_run,
        "ok": scheduled and not failed,
    }


def unit_status(name):
    props, problem = systemctl_show(name, UNIT_PROPS)
    if not props:
        return {"name": name, "kind": "unknown", "state": "unknown", "ok": False,
                "error": problem or "systemctl returned nothing"}
    if props.get("LoadState") != "loaded":
        return {"name": name, "kind": "unknown", "state": props.get("LoadState", "unknown"),
                "ok": False, "error": "no unit with this name"}

    if name.endswith(".timer"):
        info = timer_status(name, props)
    elif name.endswith(".service"):
        info = service_status(systemctl_show(name, SERVICE_PROPS)[0])
    else:
        info = {"kind": "other", "state": props.get("ActiveState", "unknown"),
                "sub": props.get("SubState", ""), "ok": props.get("ActiveState") == "active"}
    info["name"] = name
    return info


# -------------------------------------------------------------------- DNS

def dns_lookup(host, port):
    """Send one A query for a fresh random name and report whether a real answer came back."""
    qname = "sb-%s.example.com" % os.urandom(4).hex()
    query_id = os.urandom(2)
    packet = query_id + struct.pack(">HHHHH", 0x0100, 1, 0, 0, 0)  # recursion desired, 1 question
    packet += b"".join(bytes([len(label)]) + label.encode() for label in qname.split(".")) + b"\0"
    packet += struct.pack(">HH", 1, 1)  # type A, class IN

    result = {"target": "%s:%d" % (host, port), "checked": round(time.time())}
    try:
        family, _, _, _, address = socket.getaddrinfo(host, port, type=socket.SOCK_DGRAM)[0]
        started = time.monotonic()
        with socket.socket(family, socket.SOCK_DGRAM) as sock:
            sock.settimeout(DNS_TIMEOUT)
            sock.sendto(packet, address)
            while True:
                reply, _ = sock.recvfrom(512)
                if len(reply) >= 4 and reply[:2] == query_id:
                    break
        rcode = reply[3] & 0x0F
        result.update(
            ok=rcode in (0, 3),  # NOERROR or NXDOMAIN: the upstream resolver answered
            ms=round((time.monotonic() - started) * 1000),
            detail=DNS_RCODES.get(rcode, "RCODE %d" % rcode),
        )
    except socket.timeout:
        result.update(ok=False, detail="no reply within %d s" % DNS_TIMEOUT)
    except OSError as err:
        result.update(ok=False, detail=err.strerror or str(err))
    return result


# --------------------------------------------------------------- snapshot

class Agent:
    def __init__(self, name, units, dns_targets, dns_interval):
        self.name = name
        self.units = units
        self.dns_targets = dns_targets
        self.dns_interval = dns_interval
        self.dns_results = []
        self.lock = threading.Lock()

    def refresh_dns(self):
        self.dns_results = [dns_lookup(host, port) for host, port in self.dns_targets]

    def dns_loop(self):
        """Repeat the lookups in the background so a dead server never delays /status."""
        while True:
            healthy = all(result["ok"] for result in self.dns_results)
            time.sleep(self.dns_interval if healthy else min(self.dns_interval, DNS_RETRY_INTERVAL))
            self.refresh_dns()

    def snapshot(self):
        with self.lock:  # one collection at a time, so slow checks can't pile up
            meminfo = {}
            for line in read_file("/proc/meminfo").splitlines():
                key, _, rest = line.partition(":")
                if rest.split():
                    meminfo[key] = int(rest.split()[0])
            total, available = meminfo.get("MemTotal"), meminfo.get("MemAvailable")

            temp = read_file("/sys/class/thermal/thermal_zone0/temp").strip()
            uptime = read_file("/proc/uptime").split()
            disk = shutil.disk_usage("/")

            return {
                "name": self.name,
                "time": round(time.time()),
                "uptime": round(float(uptime[0])) if uptime else None,
                "temp_c": round(int(temp) / 1000, 1) if temp.lstrip("-").isdigit() else None,
                "mem_used_pct": round(100 * (1 - available / total)) if total and available is not None else None,
                "disk_used_pct": round(100 * disk.used / (disk.used + disk.free)) if disk.used + disk.free else None,
                "load1": round(os.getloadavg()[0], 2),
                "cpus": os.cpu_count(),
                "units": [unit_status(unit) for unit in self.units],
                "dns": self.dns_results,
            }


def make_handler(agent):
    class Handler(BaseHTTPRequestHandler):
        def send_cors_headers(self):
            # The board is a local page in a browser on another machine, so it needs CORS.
            self.send_header("Access-Control-Allow-Origin", "*")
            self.send_header("Access-Control-Allow-Private-Network", "true")

        def do_OPTIONS(self):
            self.send_response(204)
            self.send_cors_headers()
            self.send_header("Access-Control-Allow-Methods", "GET")
            self.end_headers()

        def do_GET(self):
            if self.path.split("?")[0] not in ("/", "/status"):
                self.send_error(404)
                return
            body = json.dumps(agent.snapshot()).encode()
            self.send_response(200)
            self.send_cors_headers()
            self.send_header("Content-Type", "application/json")
            self.send_header("Cache-Control", "no-store")
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            self.wfile.write(body)

        def log_message(self, *args):
            pass  # the board polls every few seconds; don't fill the journal

    return Handler


def parse_dns_target(value):
    host, sep, port = value.rpartition(":")
    if sep and port.isdigit() and ":" not in host:
        return host, int(port)
    return value, 53


def main():
    parser = argparse.ArgumentParser(description="Serve this machine's status for the Pi status board.")
    parser.add_argument("--unit", nargs="+", action="append", default=[], metavar="NAME",
                        help="systemd units to report, e.g. pihole-FTL seattle-permits.timer")
    parser.add_argument("--dns", nargs="+", action="append", default=[], metavar="HOST[:PORT]",
                        help="DNS servers to test with a lookup, e.g. 127.0.0.1")
    parser.add_argument("--dns-interval", type=int, default=300, metavar="SECONDS",
                        help="how often to repeat each DNS lookup (default: 300)")
    parser.add_argument("--name", default=socket.gethostname(), help="name shown on the board (default: hostname)")
    parser.add_argument("--port", type=int, default=8787, help="port to listen on (default: 8787)")
    parser.add_argument("--bind", default="0.0.0.0", help="address to listen on (default: all interfaces)")
    args = parser.parse_args()

    units = [u if u.endswith(UNIT_SUFFIXES) else u + ".service" for group in args.unit for u in group]
    dns_targets = [parse_dns_target(t) for group in args.dns for t in group]

    agent = Agent(args.name, units, dns_targets, args.dns_interval)
    if dns_targets:
        agent.refresh_dns()
        threading.Thread(target=agent.dns_loop, daemon=True).start()
    server = ThreadingHTTPServer((args.bind, args.port), make_handler(agent))
    print("serving status for %s on %s:%d" % (args.name, args.bind, args.port), flush=True)
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        pass


if __name__ == "__main__":
    main()
