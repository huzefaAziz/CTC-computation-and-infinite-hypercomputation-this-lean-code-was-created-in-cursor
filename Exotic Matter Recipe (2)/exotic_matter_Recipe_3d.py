#!/usr/bin/env python3
"""
Exotic-matter recipe -- 3D energy-condition explorer (pygame)

A Python/pygame port of ExoticMatterRecipe.lean.  Same recipe, same maths, but you
can *see* it.

The 3D graph lives in "stress-energy space":

    x axis : rho    (energy density)
    y axis : p_xy   (pressure in the x and y directions)
    z axis : p_z    (pressure along the plate normal)

all in micro-joules per cubic metre, drawn on a symmetric-log scale so that ordinary
matter and the Casimir vacuum fit on the same graph.

  * cyan  surface : rho + p_z  = 0   (NEC edge, z direction)
  * magenta surface: rho + p_xy = 0  (NEC edge, x/y directions)
  * green rays    : ordinary matter (dust, radiation, stiff) -- never exotic
  * red ray       : the Casimir vacuum as the plate gap shrinks.  It sits ON the
                    magenta surface but dives BELOW the cyan one: rho + p_z < 0.
                    That is a null-energy-condition violation = exotic matter.

Cook it yourself -- the steps behave exactly like `Step.run` in the Lean file:
    pumpDown      : evacuated := true
    coolToGround  : cold      := evacuated
    insertPlates  : plates    := evacuated && cold
Only a lab that is evacuated AND cold AND has plates serves up the Casimir tensor;
anything else serves plain vacuum.

Controls
    1 / 2 / 3     pumpDown / coolToGround / insertPlates
    SPACE         run the recipe automatically
    X             run the WRONG order (plates first) -> plain vacuum
    R             reset the lab
    UP / DOWN     change the plate gap (0.5 - 3.0 um)
    mouse drag    rotate        mouse wheel   zoom
    A             toggle auto-rotate      H   toggle help      ESC   quit

Requires:  pip install pygame
Run:       python exotic_matter_3d.py
"""
from __future__ import annotations

import argparse
import math
import os
from dataclasses import dataclass

import pygame

# ---------------------------------------------------------------------------
# 1. Physics -- a mirror of the Lean file
# ---------------------------------------------------------------------------
HBAR = 1.054571817e-34       # J s
LIGHT_C = 299792458.0        # m/s
UJ = 1.0e6                   # J/m^3 -> uJ/m^3

Tensor = tuple               # (rho, px, py, pz)
PLAIN_VACUUM: Tensor = (0.0, 0.0, 0.0, 0.0)


def casimir_rho(gap_m: float) -> float:
    """rho = -pi^2 hbar c / (720 a^4)   (J/m^3)"""
    return -(math.pi ** 2 * HBAR * LIGHT_C) / (720.0 * gap_m ** 4)


def casimir_tensor(gap_m: float) -> Tensor:
    """T = rho * diag(1, -1, -1, 3): traceless, z perpendicular to the plates."""
    r = casimir_rho(gap_m)
    return (r, -r, -r, 3.0 * r)


def nec(t: Tensor) -> bool:
    rho, px, py, pz = t
    return rho + px >= 0 and rho + py >= 0 and rho + pz >= 0


def wec(t: Tensor) -> bool:
    return t[0] >= 0 and nec(t)


def sec(t: Tensor) -> bool:
    return nec(t) and sum(t) >= 0


def dec(t: Tensor) -> bool:
    rho, px, py, pz = t
    return abs(px) <= rho and abs(py) <= rho and abs(pz) <= rho


def exotic(t: Tensor) -> bool:
    """Exotic matter = violates the null energy condition."""
    return not nec(t)


@dataclass
class Kitchen:
    evacuated: bool = False
    cold: bool = False
    plates: bool = False

    def run(self, step: str) -> None:
        if step == "pumpDown":
            self.evacuated = True
        elif step == "coolToGround":
            self.cold = self.evacuated
        elif step == "insertPlates":
            self.plates = self.evacuated and self.cold

    @property
    def ready(self) -> bool:
        return self.evacuated and self.cold and self.plates


def serve(k: Kitchen, gap_m: float) -> Tensor:
    return casimir_tensor(gap_m) if k.ready else PLAIN_VACUUM


RECIPE = ["pumpDown", "coolToGround", "insertPlates"]
WRONG_ORDER = ["insertPlates", "pumpDown", "coolToGround"]

# ---------------------------------------------------------------------------
# 2. Scene mapping: symmetric-log axes so everything fits in [-1, 1]
# ---------------------------------------------------------------------------
V_MAX = 30000.0              # axis half-range in uJ/m^3
LOG_S = 50.0                 # linear region around zero
_NORM = math.asinh(V_MAX / LOG_S)


def sym(v: float) -> float:
    return math.asinh(v / LOG_S) / _NORM


def scene(rho: float, pxy: float, pz: float) -> tuple:
    return (sym(rho), sym(pxy), sym(pz))


MESH_VALUES = sorted({0.0} | {s * v for s in (-1, 1)
                              for v in (100, 300, 1000, 3000, 10000, 30000)})

BG = (9, 11, 20)
PANEL_BG = (16, 19, 34)
WHITE = (235, 238, 245)
GREY = (120, 128, 150)
CYAN = (45, 165, 195)
MAGENTA = (190, 65, 165)
GREEN = (90, 220, 120)
RED = (255, 85, 70)
GOLD = (255, 205, 80)


def shade(color, depth, dist):
    t = (depth - (dist - 1.8)) / 3.6
    f = max(0.30, min(1.15, 1.15 - 0.80 * t))
    return tuple(min(255, int(c * f)) for c in color)


# ---------------------------------------------------------------------------
# 3. A tiny software 3D camera
# ---------------------------------------------------------------------------
class Camera:
    def __init__(self):
        self.yaw = -0.80
        self.pitch = 0.42
        self.dist = 4.3

    def project(self, p, cx, cy, scale):
        x, y, z = p
        cyw, syw = math.cos(self.yaw), math.sin(self.yaw)
        x1 = cyw * x - syw * y
        y1 = syw * x + cyw * y
        cp, sp = math.cos(self.pitch), math.sin(self.pitch)
        y2 = cp * y1 - sp * z
        z2 = sp * y1 + cp * z
        depth = y2 + self.dist
        k = scale * self.dist / depth
        return cx + x1 * k, cy - z2 * k, depth


# ---------------------------------------------------------------------------
# 4. The app
# ---------------------------------------------------------------------------
class App:
    PANEL_W = 360

    def __init__(self, size=(1200, 760)):
        pygame.init()
        self.W, self.H = size
        self.screen = pygame.display.set_mode(size)
        pygame.display.set_caption("Exotic matter recipe - 3D energy-condition explorer")
        self.fonts = {s: pygame.font.Font(None, s) for s in (18, 21, 25, 34)}
        self._text_cache = {}
        self.cam = Camera()
        self.auto_rotate = True
        self.dragging = False
        self.show_help = True
        self.reset()
        self._build_static()

    # -- state ---------------------------------------------------------
    def reset(self):
        self.kitchen = Kitchen()
        self.history = []
        self.queue = []
        self.queue_timer = 0.0
        self.gap = 1.0e-6
        self.blend = 0.0
        self.t = 0.0
        self.msg = "SPACE follows the recipe.  1 / 2 / 3 cook by hand."

    def do_step(self, name):
        self.kitchen.run(name)
        self.history.append(name)
        if name == "insertPlates" and not self.kitchen.plates:
            self.msg = "Plates need vacuum AND cold first: plain vacuum only."
        elif self.kitchen.ready:
            self.msg = "Lab ready: the Casimir vacuum is exotic matter!"
        else:
            self.msg = f"Did: {name}"

    def start(self, steps):
        self.reset()
        self.queue = list(steps)
        self.queue_timer = 0.6

    def update(self, dt):
        self.t += dt
        if self.queue:
            self.queue_timer -= dt
            if self.queue_timer <= 0:
                self.do_step(self.queue.pop(0))
                self.queue_timer = 0.9
        target = 1.0 if self.kitchen.ready else 0.0
        self.blend += (target - self.blend) * min(1.0, dt * 3.5)
        if self.auto_rotate and not self.dragging:
            self.cam.yaw += dt * 0.22

    # -- static geometry (built once, in scene coordinates) ------------
    def _build_static(self):
        v = MESH_VALUES
        self.mesh_a = self._mesh([[scene(r, p, -r) for p in v] for r in v])   # p_z  = -rho
        self.mesh_b = self._mesh([[scene(r, -r, z) for z in v] for r in v])   # p_xy = -rho
        corners = [(sx, sy, sz) for sx in (-1, 1) for sy in (-1, 1) for sz in (-1, 1)]
        self.box = [(a, b) for a in corners for b in corners
                    if a < b and sum(i != j for i, j in zip(a, b)) == 1]
        pos = [0.0] + [30000.0 * (0.78 ** n) for n in range(30, -1, -1)]
        self.rays = []
        for w, name, col in ((0.0, "dust  p=0", (70, 190, 100)),
                             (1 / 3, "radiation  p=rho/3", GREEN),
                             (1.0, "stiff  p=rho", (150, 245, 150))):
            pts = [scene(r, w * r, w * r) for r in sorted(pos)]
            self.rays.append((pts, name, col, scene(V_MAX, w * V_MAX, w * V_MAX)))
        gaps = [3.0e-6 * (0.5e-6 / 3.0e-6) ** (i / 44) for i in range(45)]
        self.casimir_curve = [scene(*[x * UJ for x in (casimir_tensor(a)[0],
                                                       casimir_tensor(a)[1],
                                                       casimir_tensor(a)[3])]) for a in gaps]
        self.gap_ticks = [(a, scene(casimir_tensor(a * 1e-6)[0] * UJ,
                                    casimir_tensor(a * 1e-6)[1] * UJ,
                                    casimir_tensor(a * 1e-6)[3] * UJ))
                          for a in (0.5, 0.7, 1.0, 1.5, 2.0, 3.0)]
        self.axis_ticks = [(vv, lab) for vv, lab in ((100, "100"), (1000, "1k"), (10000, "10k"))]

    @staticmethod
    def _mesh(grid):
        segs = []
        n = len(grid)
        for i in range(n):
            for j in range(n):
                if j + 1 < n:
                    segs.append((grid[i][j], grid[i][j + 1]))
                if i + 1 < n:
                    segs.append((grid[i][j], grid[i + 1][j]))
        return segs

    # -- text helper -----------------------------------------------------
    def text(self, s, pos, color=WHITE, size=21, anchor="topleft"):
        key = (s, color, size)
        surf = self._text_cache.get(key)
        if surf is None:
            surf = self.fonts[size].render(s, True, color)
            if len(self._text_cache) > 600:
                self._text_cache.clear()
            self._text_cache[key] = surf
        rect = surf.get_rect(**{anchor: pos})
        self.screen.blit(surf, rect)
        return rect

    # -- drawing -----------------------------------------------------------
    def draw(self):
        scr = self.screen
        scr.fill(BG)
        vw = self.W - self.PANEL_W
        view = pygame.Rect(self.PANEL_W, 0, vw, self.H)
        cx, cy = view.centerx, view.centery + 18
        scale = 0.31 * min(vw, self.H)
        cam = self.cam
        P = lambda p: cam.project(p, cx, cy, scale)

        scr.set_clip(view)
        prims, labels = [], []

        def line(a, b, col, w=1, bias=0.0):
            x0, y0, d0 = P(a)
            x1, y1, d1 = P(b)
            prims.append(((d0 + d1) / 2 + bias, 0, (x0, y0, x1, y1, col, w)))

        def dot(p, col, r, bias=0.0):
            x, y, d = P(p)
            prims.append((d + bias, 1, (x, y, col, max(2, int(r * cam.dist / d)))))

        def label(p, s, col=WHITE, size=18, anchor="midleft", dx=6, dy=0, flat=False):
            x, y, d = P(p)
            labels.append((d, s, (x + dx, y + dy), col if flat else shade(col, d, cam.dist),
                           size, anchor))

        # bounding box + axes
        for a, b in self.box:
            line(a, b, (38, 44, 66))
        line((-1, 0, 0), (1, 0, 0), GREY, 1)
        line((0, -1, 0), (0, 1, 0), GREY, 1)
        line((0, 0, -1), (0, 0, 1), GREY, 1)
        label((1.06, 0, 0), "ρ", GOLD, 34, "midleft", 4, -16, flat=True)
        label((0, 1.06, 0), "p_xy", GOLD, 25, "midleft", 4, -8, flat=True)
        label((0, 0, 1.04), "p_z", GOLD, 25, "midbottom", 0, -4, flat=True)
        for vv, lab in self.axis_ticks:
            for sgn in (-1, 1):
                label((sym(sgn * vv), 0, 0), ("-" if sgn < 0 else "") + lab, GREY, 18, "midtop", 0, 4)
                label((0, 0, sym(sgn * vv)), ("-" if sgn < 0 else "") + lab, GREY, 18, "midright", -6)

        # NEC edge surfaces
        for a, b in self.mesh_a:
            line(a, b, CYAN)
        for a, b in self.mesh_b:
            line(a, b, MAGENTA)

        # ordinary matter
        for (pts, name, col, tip), dy in zip(self.rays, (14, 0, -6)):
            for a, b in zip(pts, pts[1:]):
                line(a, b, col, 3, bias=-0.02)
            label(tip, name, col, 18, "midleft", 6, dy)

        # Casimir ray
        for a, b in zip(self.casimir_curve, self.casimir_curve[1:]):
            line(a, b, RED, 3, bias=-0.03)
        for gap_um, p in self.gap_ticks:
            dot(p, (255, 150, 130), 3, -0.04)
            if not (self.kitchen.ready and abs(gap_um - self.gap * 1e6) < 0.12):
                label(p, f"{gap_um:g} µm", (255, 160, 140), 18, "midright", -8)

        # the current state of the lab
        T = serve(self.kitchen, self.gap)
        rho, px, py, pz = (x * UJ for x in T)
        tip = scene(rho, px, pz)
        cur = (tip[0] * self.blend, tip[1] * self.blend, tip[2] * self.blend)
        if self.blend > 0.02:
            surf_z = sym(-rho)                       # where the cyan NEC surface is, above the point
            line(cur, (cur[0], cur[1], surf_z * self.blend + cur[2] * (1 - self.blend)), GOLD, 3, -0.05)
        dot(cur, RED if self.kitchen.ready else WHITE, 8, -0.06)
        if self.kitchen.ready and self.blend > 0.6:
            label(cur, f"Casimir vacuum, a = {self.gap * 1e6:.2f} µm", GOLD, 21, "midleft", 14, -14)
        elif not self.kitchen.ready:
            label(cur, "plain vacuum", WHITE, 21, "midleft", 12, -12)

        prims.sort(key=lambda p: -p[0])
        for depth, kind, a in prims:
            if kind == 0:
                x0, y0, x1, y1, col, w = a
                pygame.draw.line(scr, shade(col, depth, cam.dist), (x0, y0), (x1, y1), w)
            else:
                x, y, col, r = a
                pygame.draw.circle(scr, shade(col, depth, cam.dist), (x, y), r)
                pygame.draw.circle(scr, (255, 255, 255), (x, y), max(1, r // 3))
        labels.sort(key=lambda l: -l[0])
        for _, s, pos, col, size, anchor in labels:
            if s:
                self.text(s, pos, col, size, anchor)
        scr.set_clip(None)

        self._draw_panel(T)
        pygame.display.flip()

    # -- the left-hand panel ---------------------------------------------
    def _draw_panel(self, T):
        scr = self.screen
        pygame.draw.rect(scr, PANEL_BG, (0, 0, self.PANEL_W, self.H))
        pygame.draw.line(scr, (45, 52, 80), (self.PANEL_W - 1, 0), (self.PANEL_W - 1, self.H))
        x, y = 18, 14
        self.text("EXOTIC MATTER RECIPE", (x, y), GOLD, 34)
        y += 30
        self.text("Casimir-vacuum energy-condition explorer", (x, y), GREY, 18)
        y += 34

        # lab state
        self.text("LAB", (x, y), WHITE, 25)
        y += 26
        for name, ok in (("evacuated", self.kitchen.evacuated),
                         ("cold", self.kitchen.cold),
                         ("plates", self.kitchen.plates)):
            pygame.draw.rect(scr, GREEN if ok else (70, 76, 100), (x + 2, y + 2, 14, 14), 0 if ok else 2)
            self.text(name, (x + 26, y), WHITE if ok else GREY, 21)
            y += 22
        steps = " > ".join(self.history[-3:]) if self.history else "(no steps yet)"
        self.text("steps: " + steps, (x, y + 2), GREY, 18)
        y += 30

        # plate schematic
        top = y
        gap_px = int(14 + (self.gap * 1e6 - 0.5) / 2.5 * 52)
        px0, pw = x + 30, 200
        plates_in = self.kitchen.plates
        colr = (150, 160, 190) if plates_in else (62, 68, 92)
        pygame.draw.rect(scr, colr, (px0, top + 4, pw, 9), 0 if plates_in else 1)
        pygame.draw.rect(scr, colr, (px0, top + 13 + gap_px, pw, 9), 0 if plates_in else 1)
        if self.kitchen.ready:
            band = pygame.Surface((pw, gap_px), pygame.SRCALPHA)
            a = int(60 + 40 * math.sin(self.t * 4))
            band.fill((255, 70, 60, a))
            scr.blit(band, (px0, top + 13))
        self.text(f"a = {self.gap * 1e6:.2f} µm", (px0 + pw + 12, top + 13 + gap_px // 2 - 8), WHITE, 21)
        y = top + 13 + gap_px + 22 + 10

        # stress-energy readout
        self.text("STRESS-ENERGY  (µJ/m³)", (x, y), WHITE, 25)
        y += 26
        rho, px, py, pz = (v * UJ for v in T)
        for name, val in (("ρ", rho), ("p_x", px), ("p_y", py), ("p_z", pz)):
            self.text(name, (x, y), WHITE, 21)
            self.text(f"{val:+.1f}", (x + 150, y), WHITE, 21, "topright")
            y += 21
        y += 6
        self.text("NEC:  ρ + p_i ≥ 0 ?", (x, y), WHITE, 21)
        y += 22
        for name, val in (("ρ + p_x", rho + px), ("ρ + p_y", rho + py), ("ρ + p_z", rho + pz)):
            ok = val >= -1e-9
            col = GREEN if ok else RED
            self.text(name, (x, y), col, 21)
            self.text(f"{val:+.1f}", (x + 150, y), col, 21, "topright")
            self.text("ok" if ok else "VIOLATED", (x + 168, y), col, 21)
            y += 21
        y += 8
        xx = x
        for name, f in (("NEC", nec), ("WEC", wec), ("SEC", sec), ("DEC", dec)):
            ok = f(T)
            r = self.text(name, (xx, y), GREEN if ok else RED, 25)
            self.text("holds" if ok else "broken", (xx, y + 20), GREEN if ok else RED, 18)
            xx += 84
        y += 52

        # verdict
        if exotic(T):
            box, col, head = (70, 18, 22), RED, "EXOTIC MATTER"
            sub = "NEC violated along z (plate normal)"
        else:
            box, col, head = (22, 30, 44), GREY, "ordinary: not exotic"
            sub = "all null-energy conditions hold"
        pygame.draw.rect(scr, box, (x - 6, y - 4, self.PANEL_W - 24, 56), border_radius=8)
        pygame.draw.rect(scr, col, (x - 6, y - 4, self.PANEL_W - 24, 56), 2, border_radius=8)
        self.text(head, (x + 4, y + 2), col, 25)
        self.text(sub, (x + 4, y + 30), col, 18)
        y += 68

        self.text(self.msg, (x, y), GOLD, 18)
        y += 26

        # legend
        for col, s in ((CYAN, "cyan:  ρ + p_z = 0   (NEC edge)"),
                       (MAGENTA, "magenta:  ρ + p_xy = 0   (NEC edge)"),
                       (GREEN, "green:  ordinary matter"),
                       (RED, "red:  Casimir vacuum (smaller gap -> deeper)"),
                       (GOLD, "gold:  NEC violation depth")):
            pygame.draw.line(scr, col, (x, y + 8), (x + 22, y + 8), 3)
            self.text(s, (x + 30, y), GREY, 18)
            y += 18

        if self.show_help:
            hx = self.PANEL_W + 16
            self.text("1 / 2 / 3  cook step by step     SPACE  recipe     X  wrong order     R  reset",
                      (hx, self.H - 46), (150, 158, 185), 18)
            self.text("UP / DOWN  plate gap     drag  rotate     wheel  zoom     A  auto-rotate"
                      "     H  hide help     ESC  quit", (hx, self.H - 26), (150, 158, 185), 18)

    # -- events / main loop ------------------------------------------------
    def handle(self, ev) -> bool:
        if ev.type == pygame.QUIT:
            return False
        if ev.type == pygame.KEYDOWN:
            k = ev.key
            if k == pygame.K_ESCAPE:
                return False
            elif k == pygame.K_1:
                self.do_step("pumpDown")
            elif k == pygame.K_2:
                self.do_step("coolToGround")
            elif k == pygame.K_3:
                self.do_step("insertPlates")
            elif k == pygame.K_SPACE:
                self.start(RECIPE)
            elif k == pygame.K_x:
                self.start(WRONG_ORDER)
            elif k == pygame.K_r:
                self.reset()
            elif k == pygame.K_a:
                self.auto_rotate = not self.auto_rotate
            elif k == pygame.K_h:
                self.show_help = not self.show_help
        elif ev.type == pygame.MOUSEBUTTONDOWN and ev.button == 1:
            self.dragging = True
        elif ev.type == pygame.MOUSEBUTTONUP and ev.button == 1:
            self.dragging = False
        elif ev.type == pygame.MOUSEMOTION and self.dragging:
            self.cam.yaw += ev.rel[0] * 0.008
            self.cam.pitch = max(-1.4, min(1.4, self.cam.pitch + ev.rel[1] * 0.008))
        elif ev.type == pygame.MOUSEWHEEL:
            self.cam.dist = max(2.8, min(9.0, self.cam.dist - ev.y * 0.2))
        return True

    def run(self):
        clock = pygame.time.Clock()
        running = True
        while running:
            dt = clock.tick(60) / 1000.0
            for ev in pygame.event.get():
                running = self.handle(ev) and running
            keys = pygame.key.get_pressed()
            if keys[pygame.K_UP]:
                self.gap = max(0.5e-6, self.gap / (1 + 0.8 * dt))
            if keys[pygame.K_DOWN]:
                self.gap = min(3.0e-6, self.gap * (1 + 0.8 * dt))
            self.update(dt)
            self.draw()
        pygame.quit()


def main():
    ap = argparse.ArgumentParser(description="3D exotic-matter recipe explorer")
    ap.add_argument("--selftest", metavar="PNG",
                    help="run headless, simulate the demo, save a screenshot and exit")
    ap.add_argument("--demo", choices=("recipe", "wrong"), default="recipe")
    args = ap.parse_args()
    if args.selftest:
        os.environ.setdefault("SDL_VIDEODRIVER", "dummy")
    app = App()
    if args.selftest:
        app.start(RECIPE if args.demo == "recipe" else WRONG_ORDER)
        for _ in range(210):
            app.update(1 / 30)
            app.draw()
        pygame.image.save(app.screen, args.selftest)
        print("saved", args.selftest, "| ready:", app.kitchen.ready,
              "| exotic:", exotic(serve(app.kitchen, app.gap)))
        pygame.quit()
    else:
        app.run()


if __name__ == "__main__":
    main()
