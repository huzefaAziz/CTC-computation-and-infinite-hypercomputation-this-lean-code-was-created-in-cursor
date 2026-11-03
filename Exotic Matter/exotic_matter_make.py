# exotic_pygame.py — a live, clickable version of the Lean `Fluid` structure.
import pygame, sys, math

WIDTH, HEIGHT = 1120, 720
BG     = (18, 18, 24)
PANEL  = (28, 28, 36)
FG     = (230, 230, 235)
DIM    = (140, 140, 155)
GREEN  = ( 90, 220, 130)
RED    = (235,  90,  90)
YELLOW = (240, 200,  70)
BLUE   = (120, 180, 255)

# ---------------------------------------------------------------------------
# Physics core — line-for-line translation of the Lean `Fluid` namespace.
# ---------------------------------------------------------------------------
class Fluid:
    def __init__(self, rho, p1, p2, p3):
        self.rho = rho
        self.p1, self.p2, self.p3 = p1, p2, p3

    def NEC(self):                       # 0 ≤ ρ+pᵢ for all i
        return (0 <= self.rho + self.p1 and
                0 <= self.rho + self.p2 and
                0 <= self.rho + self.p3)

    def WEC(self):                       # 0 ≤ ρ  ∧  NEC
        return 0 <= self.rho and self.NEC()

    def SEC(self):                       # 0 ≤ ρ+Σpᵢ  ∧  NEC
        return 0 <= self.rho + self.p1 + self.p2 + self.p3 and self.NEC()

    def DEC(self):                       # |pᵢ| ≤ ρ
        r = self.rho
        return (-r <= self.p1 <= r) and (-r <= self.p2 <= r) and (-r <= self.p3 <= r)

    def Ordinary(self):                  # NEC ∧ WEC ∧ SEC ∧ DEC
        return self.NEC() and self.WEC() and self.SEC() and self.DEC()

    def Exotic(self):
        return not self.Ordinary()

    def classify(self):                  # same strings as the Lean `classify`
        if not self.NEC(): return "exotic: breaks NEC (wormhole / warp-drive grade)"
        if not self.WEC(): return "exotic: negative energy density"
        if not self.SEC(): return "exotic: gravitationally repulsive"
        if not self.DEC(): return "exotic: superluminal energy flow"
        return "ordinary"


# Presets from the Lean "zoo": dust, radiation, cosmoConst 1, adsVacuum,
# phantom, casimir 1, wormholeThroat.
PRESETS = [
    ("dust",            ( 1,  0,  0,  0)),
    ("radiation",       ( 3,  1,  1,  1)),
    ("dark energy",     ( 1, -1, -1, -1)),
    ("AdS vacuum",      (-1,  1,  1,  1)),
    ("phantom",         ( 2, -3, -3, -3)),
    ("Casimir vacuum",  (-1,  1,  1, -3)),
    ("wormhole throat", ( 2, -4,  1,  1)),
]

state = {"rho": 1, "p1": 0, "p2": 0, "p3": 0}
KEYS  = {pygame.K_UP:("rho",+1), pygame.K_DOWN:("rho",-1),
         pygame.K_w:("p1", +1),  pygame.K_s:   ("p1", -1),
         pygame.K_e:("p2", +1),  pygame.K_d:   ("p2", -1),
         pygame.K_r:("p3", +1),  pygame.K_f:   ("p3", -1)}

def clamp(v): return max(-9, min(9, v))
def fluid():  return Fluid(state["rho"], state["p1"], state["p2"], state["p3"])


def draw_warp(screen, T, cx, cy):
    """Warped grid + radial null rays. Growth sign mirrors the condition broken."""
    pygame.draw.circle(screen, (24, 24, 30), (cx, cy), 310)
    pygame.draw.circle(screen, (40, 40, 52), (cx, cy), 310, 2)

    if   not T.NEC(): grow, ray =  0.55, RED        # flare-out (wormhole)
    elif not T.SEC(): grow, ray =  0.30, YELLOW     # expansion (dark energy)
    elif not T.DEC(): grow, ray =  0.15, BLUE       # mild; superluminal flow
    else:             grow, ray = -0.25, GREEN      # contraction (ordinary)

    N, spacing = 12, 46
    for i in range(-N, N + 1):
        for j in range(-N, N + 1):
            x0, y0 = i * spacing, j * spacing
            r = math.hypot(x0, y0)
            if r > 320: continue
            s = 1.0 + grow * (1 - math.exp(-r / 130))
            px, py = cx + x0 * s, cy + y0 * s
            if (px - cx)**2 + (py - cy)**2 > 295**2: continue
            t = r / 320
            c = (int(70 + 120*t), int(70 + 80*t), int(90 + 110*t))
            pygame.draw.circle(screen, c, (int(px), int(py)), 2)

    for ang in range(0, 360, 10):
        a = math.radians(ang)
        pts = [(cx, cy)]
        for k in range(1, 30):
            r0 = k * 9
            s  = 1.0 + grow * (1 - math.exp(-r0 / 130))
            r1 = r0 * s
            pts.append((cx + math.cos(a) * r1, cy + math.sin(a) * r1))
        pygame.draw.aalines(screen, ray, False, [(int(x), int(y)) for x, y in pts])

    pygame.draw.circle(screen, (250, 250, 250), (cx, cy), 3)


def main():
    pygame.init()
    screen = pygame.display.set_mode((WIDTH, HEIGHT))
    pygame.display.set_caption("Exotic matter — Lean `Fluid` in Pygame")
    clock = pygame.time.Clock()
    F  = pygame.font.SysFont("Menlo,monospace", 17)
    FB = pygame.font.SysFont("Menlo,monospace", 20, bold=True)
    FS = pygame.font.SysFont("Menlo,monospace", 14)

    fields = ["rho", "p1", "p2", "p3"]
    labels = {"rho": "ρ  ", "p1": "p₁ ", "p2": "p₂ ", "p3": "p₃ "}
    y0 = 128

    minus_r = {f: pygame.Rect(110, y0 + i*48, 34, 34) for i, f in enumerate(fields)}
    plus_r  = {f: pygame.Rect(300, y0 + i*48, 34, 34) for i, f in enumerate(fields)}

    presets_y = y0 + 4*48 + 26
    preset_r  = []
    for i in range(len(PRESETS)):
        col, row = i % 2, i // 2
        preset_r.append(pygame.Rect(40 + col*220, presets_y + 24 + row*32, 210, 26))

    while True:
        mp = pygame.mouse.get_pos()
        for e in pygame.event.get():
            if e.type == pygame.QUIT:
                pygame.quit(); return
            if e.type == pygame.KEYDOWN:
                if e.key == pygame.K_ESCAPE:
                    pygame.quit(); return
                if e.key in KEYS:
                    f, d = KEYS[e.key]
                    state[f] = clamp(state[f] + d)
            if e.type == pygame.MOUSEBUTTONDOWN and e.button == 1:
                for f in fields:
                    if minus_r[f].collidepoint(e.pos): state[f] = clamp(state[f] - 1)
                    if plus_r [f].collidepoint(e.pos): state[f] = clamp(state[f] + 1)
                for (name, v), r in zip(PRESETS, preset_r):
                    if r.collidepoint(e.pos):
                        state["rho"], state["p1"], state["p2"], state["p3"] = v

        T = fluid()
        screen.fill(BG)

        # ---- left panel ----
        pygame.draw.rect(screen, PANEL, pygame.Rect(20, 20, 500, HEIGHT - 40), border_radius=12)
        screen.blit(FB.render("Stress–energy  (ρ, p₁, p₂, p₃)", True, FG), (40, 34))
        screen.blit(FS.render("keys: ↑↓ ρ   w/s p₁   e/d p₂   r/f p₃", True, DIM), (40, 66))

        for i, f in enumerate(fields):
            y = y0 + i*48
            screen.blit(F.render(labels[f], True, FG), (44, y + 6))
            pygame.draw.rect(screen, (55, 55, 70), minus_r[f], border_radius=6)
            screen.blit(F.render("−", True, FG), (minus_r[f].x + 11, minus_r[f].y + 2))
            v = state[f]; col = YELLOW if v < 0 else FG
            screen.blit(F.render(f"{v:+d}", True, col), (165, y + 6))
            pygame.draw.rect(screen, (55, 55, 70), plus_r[f], border_radius=6)
            screen.blit(F.render("+", True, FG), (plus_r[f].x + 11, plus_r[f].y + 2))

        screen.blit(FS.render("Presets (click):", True, DIM), (40, presets_y))
        for (name, v), r in zip(PRESETS, preset_r):
            hovered = r.collidepoint(mp)
            pygame.draw.rect(screen, (50, 50, 65) if hovered else (38, 38, 50), r, border_radius=5)
            screen.blit(FS.render(name, True, FG), (r.x + 8, r.y + 4))

        # ---- conditions table ----
        cy_cond = presets_y + 24 + 4*32 + 14
        screen.blit(FB.render("Energy conditions", True, FG), (40, cy_cond))
        conds = [("NEC", T.NEC()), ("WEC", T.WEC()), ("SEC", T.SEC()),
                 ("DEC", T.DEC()), ("Ordinary", T.Ordinary())]
        for i, (nm, ok) in enumerate(conds):
            y = cy_cond + 30 + i*26
            screen.blit(F.render(nm, True, FG), (56, y))
            screen.blit(F.render("OK" if ok else " X", True, GREEN if ok else RED), (210, y))
        screen.blit(FS.render("Ordinary ⇔ SEC ∧ DEC   (Lean: ordinary_iff)",
                              True, DIM), (56, cy_cond + 30 + 5*26 + 6))

        # ---- classify banner (identical strings to Lean) ----
        cl = T.classify()
        if   cl == "ordinary":        col = GREEN
        elif "NEC" in cl:             col = RED
        elif "negative" in cl:        col = RED
        elif "repulsive" in cl:       col = YELLOW
        else:                         col = BLUE
        pygame.draw.rect(screen, (0, 0, 0), pygame.Rect(20, HEIGHT - 68, 500, 48),
                         border_radius=8)
        screen.blit(FB.render(cl, True, col), (36, HEIGHT - 58))

        # ---- right panel: warp view ----
        draw_warp(screen, T, 830, 360)
        screen.blit(FB.render(
            f"ρ={T.rho:+d}   p₁={T.p1:+d}   p₂={T.p2:+d}   p₃={T.p3:+d}",
            True, FG), (620, 22))
        screen.blit(FS.render("grid + radial null rays warp by the fluid's conditions",
                              True, DIM), (620, 50))

        pygame.display.flip()
        clock.tick(60)


if __name__ == "__main__":
    main()