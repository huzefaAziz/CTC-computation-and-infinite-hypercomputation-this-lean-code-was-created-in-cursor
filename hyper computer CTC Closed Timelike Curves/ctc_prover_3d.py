#!/usr/bin/env python3
"""
CTC proof search in 3D  (pygame only, software 3D projection)

Visual version of CTCProver.lean:
  * The loop state is "candidate proof number x" (16 nodes on a timelike worldline).
  * The kernel checks the node under the token.  Accepted -> the history is consistent
    (x -> x), the token locks.  Rejected -> the next candidate goes around the loop.
  * Candidate N-1 wraps to 0 through the cyan->magenta "bridge": the jump back in time.

Controls
  1  a valid proof exists (node 11)      2  no proof exists (grandfather paradox)
  3  Deutsch mixture: no proof, uniform  R  reset      SPACE  pause
  UP/DOWN  speed       mouse drag  orbit      wheel  zoom      ESC  quit

pip install pygame
"""
import math
import os
import random
import sys

if "--shot" in sys.argv:                      # headless screenshot for testing
    os.environ["SDL_VIDEODRIVER"] = "dummy"
import pygame

W, H = 1100, 720
N, WITNESS = 16, 11
R, HT, BULGE = 1.0, 3.4, 1.5                  # helix radius, half-height, bridge bulge
CHECK_T, MOVE_T = 0.55, 0.65                  # seconds per kernel check / hop
BG = (9, 11, 22)
MODES = {1: "valid proof exists  ->  consistent history",
         2: "no proof  ->  paradox: no consistent history",
         3: "no proof  ->  Deutsch mixture: uniform over candidates"}


def curve(s):
    """Closed worldline. x,y = space, z = time. s in [0,1]."""
    s %= 1.0 if s != 1.0 else 2.0
    if s < 0.75:
        a = s / 0.75 * 2 * math.pi
        return (R * math.cos(a), R * math.sin(a), -HT + 2 * HT * s / 0.75)
    u = (s - 0.75) / 0.25                     # the time-jump bridge, back down
    return (R + BULGE * math.sin(math.pi * u), 0.0, HT - 2 * HT * u)


def node_s(k):
    return 0.75 * k / (N - 1)


class Cam:
    yaw, pitch, dist, f = 0.9, 0.5, 10.5, 720.0

    def proj(self, p):
        x, y, z = p
        c, s = math.cos(self.yaw), math.sin(self.yaw)
        x1, y1 = x * c - y * s, x * s + y * c
        cp, sp = math.cos(self.pitch), math.sin(self.pitch)
        y2, z2 = y1 * cp - z * sp, y1 * sp + z * cp
        d = self.dist + y2
        k = self.f / d
        return W / 2 + x1 * k, H / 2 + 45 - z2 * k, d, k


class Sim:
    def __init__(self):
        self.mode, self.speed, self.paused = 1, 1.0, False
        self.reset()

    def reset(self):
        self.x, self.phase, self.t = 0, "check", 0.0
        self.status = ["unknown"] * N
        self.laps, self.s, self.src, self.dst, self.sample = 0, node_s(0), 0, 0, None

    def ok(self, x):                          # stands in for "Lean's kernel accepts proof #x"
        return self.mode == 1 and x == WITNESS

    def update(self, dt):
        if self.paused:
            return
        dt *= self.speed
        self.t += dt
        if self.phase == "locked":
            return
        if self.mode == 3:                    # mixed fixed point: random candidate, always rejected
            if self.t > 0.8:
                self.t, self.sample = 0.0, random.randrange(N)
                self.status[self.sample] = "rejected"
                self.laps += 1
            return
        if self.phase == "check" and self.t >= CHECK_T:
            if self.ok(self.x):
                self.status[self.x], self.phase = "accepted", "locked"
            else:
                self.status[self.x], self.phase = "rejected", "move"
                self.src, self.dst, self.t = self.x, (self.x + 1) % N, 0.0
        elif self.phase == "move":
            f = min(1.0, self.t / MOVE_T)
            f = f * f * (3 - 2 * f)
            a = node_s(self.src)
            b = 1.0 if self.dst == 0 else node_s(self.dst)
            self.s = a + (b - a) * f
            if f >= 1.0:
                self.x, self.phase, self.t = self.dst, "check", 0.0
                self.s = node_s(self.x)
                self.laps += self.x == 0


def shade(c, d, near=7.0, far=14.0):
    k = max(0.25, min(1.0, 1.0 - (d - near) / (far - near) * 0.75))
    return tuple(int(v * k) for v in c)


def draw(screen, sim, cam, font, small):
    screen.fill(BG)
    # time axis
    a, b = cam.proj((0, 0, -HT - 0.6)), cam.proj((0, 0, HT + 0.9))
    pygame.draw.line(screen, (70, 80, 120), a[:2], b[:2], 1)
    screen.blit(small.render("time", True, (120, 135, 190)), (b[0] + 6, b[1] - 8))
    # ground grid (space)
    for g in range(-3, 4):
        for p, q in (((g, -3, -HT - 0.6), (g, 3, -HT - 0.6)), ((-3, g, -HT - 0.6), (3, g, -HT - 0.6))):
            pa, pb = cam.proj(p), cam.proj(q)
            pygame.draw.line(screen, (22, 26, 46), pa[:2], pb[:2], 1)
    # the closed worldline
    prev = cam.proj(curve(0))
    for i in range(1, 361):
        s = i / 360
        cur = cam.proj(curve(s))
        col = (255, 90, 200) if s > 0.75 else (60, 200, 255)
        pygame.draw.line(screen, shade(col, cur[2]), prev[:2], cur[:2], 3 if s > 0.75 else 2)
        prev = cur

    tok = curve(sim.s)
    items = []
    for k in range(N):
        items.append((cam.proj(curve(node_s(k)))[2], "node", k))
    items.append((cam.proj(tok)[2], "token", None))
    items.sort(reverse=True)

    # light cone through the token (future / past)
    if sim.mode != 3:
        tp = cam.proj(tok)
        for sign in (1, -1):
            for j in range(12):
                ang = j / 12 * 2 * math.pi
                q = cam.proj((tok[0] + math.cos(ang), tok[1] + math.sin(ang), tok[2] + sign))
                pygame.draw.line(screen, (38, 44, 78), tp[:2], q[:2], 1)

    for _, kind, k in items:
        if kind == "node":
            sx, sy, d, sc = cam.proj(curve(node_s(k)))
            st = sim.status[k]
            col = {"unknown": (120, 140, 190), "rejected": (190, 60, 70), "accepted": (70, 255, 140)}[st]
            if sim.mode == 3:
                glow = 0.72 + 0.28 * math.sin(pygame.time.get_ticks() / 300 + k)
                col = tuple(int(v * glow) for v in (90, 200, 255)) if st == "unknown" else col
            r = max(4, int(0.11 * sc))
            if sim.mode == 3 and sim.sample == k:
                r += 5 + int(3 * math.sin(sim.t * 20))
            pygame.draw.circle(screen, shade(col, d), (sx, sy), r)
            lab = small.render(str(k), True, shade((200, 210, 240), d))
            screen.blit(lab, (sx + r + 3, sy - 7))
        elif sim.mode != 3:
            sx, sy, d, sc = cam.proj(tok)
            locked = sim.phase == "locked"
            pulse = 1 + 0.25 * math.sin(sim.t * 8) if locked else 1
            col = (80, 255, 150) if locked else (255, 220, 80)
            pygame.draw.circle(screen, col, (sx, sy), int(0.2 * sc * pulse))
            pygame.draw.circle(screen, (255, 255, 255), (sx, sy), int(0.2 * sc * pulse), 2)
            if sim.phase == "check":          # kernel scan ring
                rr = int(0.2 * sc + (sim.t / CHECK_T) * 0.5 * sc)
                pygame.draw.circle(screen, (255, 255, 255), (sx, sy), rr, 1)

    # HUD
    if sim.mode == 3:
        verdict = f"device emits random candidate {sim.sample}; kernel rejects" if sim.sample is not None else "..."
    elif sim.phase == "locked":
        verdict = f"candidate {sim.x}: kernel ACCEPTS  ->  step(x) = x, consistent history"
    elif sim.phase == "check":
        verdict = f"kernel checking candidate {sim.x} ..."
    else:
        verdict = f"candidate {sim.x}: REJECTED  ->  passes {sim.dst} around the loop"
    lines = [("CTC as an untrusted prover, Lean kernel as the checker", (235, 240, 255)),
             (f"mode {sim.mode}: {MODES[sim.mode]}", (150, 200, 255)),
             (verdict, (255, 225, 120) if sim.phase != "locked" else (110, 255, 160)),
             (f"laps through the time jump: {sim.laps}    speed x{sim.speed:.1f}"
              + ("   [paused]" if sim.paused else ""), (150, 160, 190))]
    for i, (t, c) in enumerate(lines):
        screen.blit((font if i == 0 else small).render(t, True, c), (18, 14 + i * 24))
    if sim.mode == 2 and all(s == "rejected" for s in sim.status):
        screen.blit(font.render("every candidate refuted: the deterministic loop has no consistent history",
                                True, (255, 110, 110)), (18, H - 62))
    screen.blit(small.render("1/2/3 mode   R reset   SPACE pause   UP/DOWN speed   drag to orbit   wheel zoom",
                             True, (110, 120, 155)), (18, H - 30))


def main():
    shot = sys.argv[sys.argv.index("--shot") + 1] if "--shot" in sys.argv else None
    frames = int(sys.argv[sys.argv.index("--frames") + 1]) if "--frames" in sys.argv else 0
    mode0 = int(sys.argv[sys.argv.index("--mode") + 1]) if "--mode" in sys.argv else 1
    pygame.init()
    screen = pygame.display.set_mode((W, H))
    pygame.display.set_caption("CTC proof search in 3D")
    font, small = pygame.font.Font(None, 30), pygame.font.Font(None, 22)
    clock, cam, sim = pygame.time.Clock(), Cam(), Sim()
    sim.mode = mode0
    dragging, n = False, 0
    while True:
        dt = 1 / 60 if shot else clock.tick(60) / 1000
        for e in pygame.event.get():
            if e.type == pygame.QUIT or (e.type == pygame.KEYDOWN and e.key == pygame.K_ESCAPE):
                pygame.quit()
                return
            if e.type == pygame.KEYDOWN:
                if e.key in (pygame.K_1, pygame.K_2, pygame.K_3):
                    sim.mode = e.key - pygame.K_0
                    sim.reset()
                elif e.key == pygame.K_r:
                    sim.reset()
                elif e.key == pygame.K_SPACE:
                    sim.paused = not sim.paused
                elif e.key == pygame.K_UP:
                    sim.speed = min(8.0, sim.speed * 1.5)
                elif e.key == pygame.K_DOWN:
                    sim.speed = max(0.2, sim.speed / 1.5)
            elif e.type == pygame.MOUSEBUTTONDOWN and e.button == 1:
                dragging = True
            elif e.type == pygame.MOUSEBUTTONUP and e.button == 1:
                dragging = False
            elif e.type == pygame.MOUSEMOTION and dragging:
                cam.yaw -= e.rel[0] * 0.008
                cam.pitch = max(-1.2, min(1.4, cam.pitch + e.rel[1] * 0.008))
            elif e.type == pygame.MOUSEWHEEL:
                cam.dist = max(5.0, min(20.0, cam.dist - e.y * 0.6))
        if not dragging:
            cam.yaw += 0.12 * dt
        sim.update(dt)
        draw(screen, sim, cam, font, small)
        pygame.display.flip()
        n += 1
        if shot and n >= frames:
            pygame.image.save(screen, shot)
            pygame.quit()
            return


if __name__ == "__main__":
    main()
