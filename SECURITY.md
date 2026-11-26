# Security

## Soundness

A theorem exists only because the kernel in `core/` built it, and the
corpus is trusted because every member replays through that kernel. A
way around this is the most serious defect XuGo can have: a proof of
`⊥`, a theorem whose statement is not the one its entry registers, a
replay or a gate that passes where it should refuse.

A soundness defect is not a secret, and nobody is safer for its being
kept one. Open an issue with the smallest Go test that shows it.

## The session server

`xugo serve` is a development tool for one user on one machine.

- It listens on the loopback address `127.0.0.1` only.
- It has no authentication. Whoever can reach the port can create and
  drive sessions, and so can any program running as you.
- A web page is not such a program. A command a browser sends for a
  page of another origin is refused, and so is a request addressed to
  any name but `127.0.0.1` or `localhost`, which is what a page sends
  once its own name has been pointed at this machine.
- It keeps its sessions under the directory `--data-dir` names: the
  lineages, and the refutation certificates they record.

Do not forward or proxy the port, and do not run the server on a machine
shared with users you would not hand a session to.

## Reporting a vulnerability

For anything that should not be public before it is fixed, use GitHub's
private reporting: **Report a vulnerability** under the repository's
Security tab. Say what an attacker can do and how to reproduce it.
