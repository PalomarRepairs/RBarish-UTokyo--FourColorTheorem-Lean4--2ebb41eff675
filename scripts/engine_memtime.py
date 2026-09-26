#!/usr/bin/env python3
"""Run a command and report its wall time, CPU time and peak memory.

Usage: engine_memtime.py [--timeout SECONDS] [--label L] -- cmd args...
Prints a line: MEMTIME label wall=..s cpu=..s maxrss=..MB anon=..MB rc=..

* cpu is the user + system time of the command and of all its waited-for descendants.
* maxrss / anon are the peaks, sampled every 0.2 s, of the summed resident / private memory of
  the command and all its descendants.  On Linux the descendants are found through the parent
  links of /proc (so that processes started by other threads, such as `lean` under `lake`, are
  counted); maxrss includes the memory-mapped .olean files, anon is the private memory.  On
  macOS they are found with `ps` (every 0.5 s) and anon is not available (reported as 0).
  maxrss is at least the peak of the largest single descendant (getrusage).
* With --timeout, the command and its descendants are killed after SECONDS (rc=TIMEOUT).
Exit status: 0 if the command succeeded, 1 otherwise.
"""
import os, resource, signal, subprocess, sys, time

LINUX = os.path.isdir('/proc/self')


def descendants_linux(root):
    par, st = {}, {}
    for d in os.listdir('/proc'):
        if not d.isdigit():
            continue
        try:
            with open(f'/proc/{d}/status') as f:
                kv = dict(l.split(':', 1) for l in f if ':' in l)
            par[int(d)] = int(kv['PPid'])
            st[int(d)] = kv
        except Exception:
            pass
    rss = anon = 0
    for p, kv in st.items():
        q = p
        while q in par and q != root and q > 1:
            q = par[q]
        if q == root:
            rss += int(kv.get('VmRSS', '0 kB').split()[0])
            anon += int(kv.get('RssAnon', '0 kB').split()[0])
    return rss, anon  # kB


def descendants_ps(root):
    try:
        out = subprocess.run(['ps', '-A', '-o', 'pid=,ppid=,rss='], capture_output=True,
                             text=True, timeout=5).stdout
    except Exception:
        return 0, 0
    par, rss = {}, {}
    for line in out.splitlines():
        parts = line.split()
        if len(parts) == 3 and all(x.isdigit() for x in parts):
            p, pp, r = map(int, parts)
            par[p] = pp
            rss[p] = r
    total = 0
    for p, r in rss.items():
        q = p
        while q in par and q != root and q > 1:
            q = par[q]
        if q == root:
            total += r
    return total, 0  # kB


def kill_tree(p):
    try:
        os.killpg(p.pid, signal.SIGKILL)
    except Exception:
        try:
            p.kill()
        except Exception:
            pass


def main():
    args = sys.argv[1:]
    timeout = None
    label = ''
    while args and args[0] != '--':
        if args[0] == '--timeout':
            timeout = float(args[1]); args = args[2:]
        elif args[0] == '--label':
            label = args[1]; args = args[2:]
        else:
            break
    if args and args[0] == '--':
        args = args[1:]
    sample = descendants_linux if LINUX else descendants_ps
    period = 0.2 if LINUX else 0.5
    t0 = time.time()
    # A new process group, so that a timeout or Ctrl-C can stop the whole tree.
    p = subprocess.Popen(args, start_new_session=True)
    peak = peak_anon = 0
    rc = None
    try:
        while True:
            try:
                rc = p.wait(timeout=period)
                break
            except subprocess.TimeoutExpired:
                r, a = sample(p.pid)
                peak = max(peak, r)
                peak_anon = max(peak_anon, a)
                if timeout and time.time() - t0 > timeout:
                    kill_tree(p)
                    p.wait()
                    rc = 'TIMEOUT'
                    break
    except KeyboardInterrupt:
        kill_tree(p)
        p.wait()
        print(f'MEMTIME {label} interrupted', flush=True)
        sys.exit(130)
    wall = time.time() - t0
    ru = resource.getrusage(resource.RUSAGE_CHILDREN)
    # ru_maxrss is in kilobytes on Linux and in bytes on macOS.
    ru_kb = ru.ru_maxrss / 1024 if sys.platform == 'darwin' else ru.ru_maxrss
    peak = max(peak, ru_kb)
    print(f'MEMTIME {label} wall={wall:.2f}s cpu={ru.ru_utime + ru.ru_stime:.2f}s '
          f'maxrss={peak / 1024:.1f}MB anon={peak_anon / 1024:.1f}MB rc={rc}', flush=True)
    sys.exit(0 if rc == 0 else 1)


if __name__ == '__main__':
    main()
