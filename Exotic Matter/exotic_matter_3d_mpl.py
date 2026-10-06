"""Exotic matter in 3D (matplotlib port of ExoticMatter.lean).

Every fluid (rho, p1, p2, p3) is classified by the first energy condition it breaks,
exactly as `Fluid.classify` does in the Lean file.
    x: p1 (first principal pressure)   y: p_t = (p2 + p3) / 2   z: rho (energy density)
The background cloud uses p2 = p3 = p_t; the named fluids use their true p2, p3.

Run:  pip install matplotlib numpy && python exotic_matter_3d_mpl.py
      (drag to rotate, right-drag or wheel to zoom, press `c` to toggle the cloud)
      python exotic_matter_3d_mpl.py --save plot.png   (no window, just write an image)
"""
import itertools
import sys

import matplotlib
if "--save" in sys.argv:
    matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

# ---- physics: same definitions as the Lean file -------------------------------------
def nec(r, p1, p2, p3): return all(r + p >= 0 for p in (p1, p2, p3))
def wec(r, p1, p2, p3): return r >= 0 and nec(r, p1, p2, p3)
def sec(r, p1, p2, p3): return r + p1 + p2 + p3 >= 0 and nec(r, p1, p2, p3)
def dec(r, p1, p2, p3): return all(-r <= p <= r for p in (p1, p2, p3))

CLASSES = [  # (test, label, colour) -- first failing test wins
    (nec, "breaks NEC (wormhole / warp-drive grade)", "#ff4646"),
    (wec, "negative energy density", "#e650e6"),
    (sec, "gravitationally repulsive", "#ffa032"),
    (dec, "superluminal energy flow", "#f0e646"),
]
ORDINARY = ("ordinary", "#50dc78")

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

R = 4  # plotted range is [-R, R] on each axis

def coords(T):
    r, p1, p2, p3 = T
    return p1, (p2 + p3) / 2, r  # (x, y, z=up)

# ---- plot ---------------------------------------------------------------------------
def main():
    plt.style.use("dark_background")
    fig = plt.figure(figsize=(11, 8))
    ax = fig.add_subplot(projection="3d")

    # background cloud, one scatter per class so the legend is free
    grid = range(-R, R + 1)
    buckets = {}
    for r, p1, pt in itertools.product(grid, grid, grid):
        label, colour = classify((r, p1, pt, pt))
        buckets.setdefault((label, colour), []).append((p1, pt, r))
    order = [ORDINARY] + [(l, c) for _, l, c in reversed(CLASSES)]
    cloud = []
    for label, colour in order:
        xs, ys, zs = zip(*buckets[(label, colour)])
        cloud.append(ax.scatter(xs, ys, zs, c=colour, s=14, alpha=0.55,
                                depthshade=True, label=label))

    # faint rho = 0 plane
    g = np.linspace(-R, R, 2)
    X, Y = np.meshgrid(g, g)
    ax.plot_surface(X, Y, np.zeros_like(X), color="white", alpha=0.06, linewidth=0)

    # named fluids: big marker + label, coloured by their true classification
    for name, T in ZOO.items():
        x, y, z = coords(T)
        _, colour = classify(T)
        ax.scatter([x], [y], [z], c=colour, s=170, edgecolors="white",
                   linewidths=1.5, depthshade=False)
        ax.text(x + 0.2, y + 0.2, z + 0.25, name, color="white", fontsize=10)

    ax.set_xlabel(r"$p_1$  (first principal pressure)")
    ax.set_ylabel(r"$p_t$  (mean transverse pressure)")
    ax.set_zlabel(r"$\rho$  (energy density)")
    ax.set_xlim(-R, R); ax.set_ylim(-R, R); ax.set_zlim(-R, R)
    ax.set_box_aspect((1, 1, 1))
    for axis in (ax.xaxis, ax.yaxis, ax.zaxis):
        axis.set_pane_color((0.05, 0.06, 0.10, 1.0))
        axis._axinfo["grid"]["color"] = (1, 1, 1, 0.12)
    ax.view_init(elev=22, azim=-55)
    ax.set_title("Exotic matter: energy-condition space", fontsize=15, pad=14)
    ax.legend(loc="upper left", fontsize=9, framealpha=0.25)

    def on_key(event):
        if event.key == "c":
            for c in cloud:
                c.set_visible(not c.get_visible())
            fig.canvas.draw_idle()
    fig.canvas.mpl_connect("key_press_event", on_key)

    fig.tight_layout()
    if "--save" in sys.argv:
        out = sys.argv[sys.argv.index("--save") + 1]
        fig.savefig(out, dpi=140)
    else:
        plt.show()

if __name__ == "__main__":
    main()
