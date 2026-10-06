"""Exotic matter in 3D (pygame port of ExoticMatter.lean).

Every fluid (rho, p1, p2, p3) is classified by the first energy condition it breaks,
exactly as `Fluid.classify` does in the Lean file. The plot's axes are
    horizontal: p1 (first principal pressure)
    vertical:   rho (energy density)
    depth:      p_t = (p2 + p3) / 2 (mean transverse pressure)
The background cloud uses p2 = p3 = p_t; the named fluids use their true p2, p3.

Controls: drag = rotate | wheel = zoom | SPACE = auto-rotate | C = toggle cloud | ESC = quit
Run:      pip install pygame && python exotic_matter_3d.py
          python exotic_matter_3d.py --shot frame.png   (render one frame and exit)
"""
import math
import os
import sys

if "--shot" in sys.argv:
    os.environ.setdefault("SDL_VIDEODRIVER", "dummy")
import pygame

# ---- physics: same definitions as the Lean file -------------------------------------
def nec(r, p1, p2, p3): return all(r + p >= 0 for p in (p1, p2, p3))
def wec(r, p1, p2, p3): return r >= 0 and nec(r, p1, p2, p3)
def sec(r, p1, p2, p3): return r + p1 + p2 + p3 >= 0 and nec(r, p1, p2, p3)
def dec(r, p1, p2, p3): return all(-r <= p <= r for p in (p1, p2, p3))

CLASSES = [  # (test, label, colour) -- first failing test wins
    (nec, "breaks NEC (wormhole / warp-drive grade)", (255, 70, 70)),
    (wec, "negative energy density", (230, 80, 230)),
    (sec, "gravitationally repulsive", (255, 160, 50)),
    (dec, "superluminal energy flow", (240, 230, 70)),
]
ORDINARY = ("ordinary", (80, 220, 120))

def classify(T):
    for test, label, colour in CLASSES:
        if not test(*T):
            return label, colour
    return ORDINARY

ZOO = {
    "dust": (1, 0, 0, 0),
    "radiation": (3, 1, 1, 1),
    "dark energy": (1, -1, -1, -1),
    "AdS vacuum": (-1, 1, 1, 1),
    "phantom": (2, -3, -3, -3),
    "Casimir": (-1, 1, 1, -3),
    "wormhole throat": (2, -4, 1, 1),
}

# ---- 3D helpers ---------------------------------------------------------------------
R = 4  # plotted range is [-R, R] on each axis

def world(T):
    r, p1, p2, p3 = T
    return (p1, r, (p2 + p3) / 2)  # (x, y=up, z)

class Camera:
    def __init__(self):
        self.yaw, self.pitch, self.zoom = 0.7, 0.35, 68.0

    def project(self, p, w, h):
        x, y, z = p
        cy, sy = math.cos(self.yaw), math.sin(self.yaw)
        x, z = x * cy + z * sy, -x * sy + z * cy
        cp, sp = math.cos(self.pitch), math.sin(self.pitch)
        y, z = y * cp - z * sp, y * sp + z * cp
        f = 14 / (14 + z)
        return (w / 2 + x * self.zoom * f, h / 2 - y * self.zoom * f), z, f

def shade(colour, f):
    k = max(0.35, min(1.0, f * 0.95))
    return tuple(int(c * k) for c in colour)

# ---- main ---------------------------------------------------------------------------
def main():
    pygame.init()
    W, H = 1100, 760
    screen = pygame.display.set_mode((W, H))
    pygame.display.set_caption("Exotic matter in 3D")
    font = pygame.font.SysFont("dejavusans,arial", 15)
    big = pygame.font.SysFont("dejavusans,arial", 20, bold=True)
    cam, clock = Camera(), pygame.time.Clock()

    cloud = [(w, classify((w[1], w[0], w[2], w[2]))[1])
             for w in ((x, y, z) for x in range(-R, R + 1)
                       for y in range(-R, R + 1) for z in range(-R, R + 1))]
    zoo = [(n, world(T), *classify(T)) for n, T in ZOO.items()]

    show_cloud, auto, drag = True, True, False
    shot = sys.argv[sys.argv.index("--shot") + 1] if "--shot" in sys.argv else None
    frames = 0

    while True:
        for e in pygame.event.get():
            if e.type == pygame.QUIT or (e.type == pygame.KEYDOWN and e.key == pygame.K_ESCAPE):
                return
            if e.type == pygame.KEYDOWN:
                if e.key == pygame.K_SPACE: auto = not auto
                if e.key == pygame.K_c: show_cloud = not show_cloud
            if e.type == pygame.MOUSEBUTTONDOWN and e.button == 1: drag = True
            if e.type == pygame.MOUSEBUTTONUP and e.button == 1: drag = False
            if e.type == pygame.MOUSEMOTION and drag:
                cam.yaw += e.rel[0] * 0.01
                cam.pitch = max(-1.5, min(1.5, cam.pitch + e.rel[1] * 0.01))
            if e.type == pygame.MOUSEWHEEL:
                cam.zoom = max(30, min(220, cam.zoom + e.y * 5))
        if auto and not drag:
            cam.yaw += 0.006

        screen.fill((12, 14, 22))
        P = lambda p: cam.project(p, W, H)

        # axes + faint rho = 0 square
        for a, b, col, name in [((-R, 0, 0), (R, 0, 0), (170, 90, 90), "p1"),
                                ((0, -R, 0), (0, R, 0), (90, 170, 90), "rho"),
                                ((0, 0, -R), (0, 0, R), (90, 120, 200), "p_t")]:
            pygame.draw.line(screen, col, P(a)[0], P(b)[0], 2)
            screen.blit(font.render(name, True, col), P(b)[0])
        sq = [(-R, 0, -R), (R, 0, -R), (R, 0, R), (-R, 0, R)]
        pygame.draw.polygon(screen, (40, 46, 66), [P(c)[0] for c in sq], 1)

        # painter's algorithm: far points first
        items = []
        if show_cloud:
            for w, colour in cloud:
                pos, z, f = P(w)
                items.append((z, pos, 3 * f, shade(colour, f), None))
        for name, w, label, colour in zoo:
            pos, z, f = P(w)
            items.append((z, pos, 9 * f, colour, name))
        for z, pos, rad, colour, name in sorted(items, key=lambda i: -i[0]):
            if name:
                pygame.draw.circle(screen, (255, 255, 255), pos, int(rad) + 2)
            pygame.draw.circle(screen, colour, pos, max(1, int(rad)))
            if name:
                screen.blit(font.render(name, True, (235, 235, 245)), (pos[0] + 12, pos[1] - 8))

        # legend
        screen.blit(big.render("Exotic matter: energy-condition space", True, (235, 235, 245)), (16, 12))
        y = 46
        for label, colour in [ORDINARY] + [(l, c) for _, l, c in reversed(CLASSES)]:
            pygame.draw.circle(screen, colour, (24, y + 8), 6)
            screen.blit(font.render(label, True, (210, 210, 225)), (38, y))
            y += 22
        screen.blit(font.render("drag: rotate   wheel: zoom   space: spin   c: cloud",
                                True, (130, 135, 160)), (16, H - 28))

        pygame.display.flip()
        clock.tick(60)
        frames += 1
        if shot and frames >= 2:
            pygame.image.save(screen, shot)
            return

if __name__ == "__main__":
    main()
