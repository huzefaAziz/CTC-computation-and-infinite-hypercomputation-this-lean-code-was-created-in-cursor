"""
Exotic-Matter Physics Visualizer
==================================
Three physically grounded computations:

  Panels A–D  Electron density  ρ_e(r)
              Slater-type 1s AO superposition on RDKit nuclear geometry.
              ρ_e ≥ 0 everywhere — this is ordinary matter, no exotic energy.

  Panel E     Alcubierre (1994) exotic-matter requirement  T₀₀
              T₀₀ = −(vₛ²/32π) · (Y²/r²) · (df_s/dr)²
              Derived from G_μν = 8πT_μν for the warp metric.
              T₀₀ ≤ 0 everywhere (genuine WEC violation).
              Units: Planck  (c = G = ħ = 1).  vₛ animated 0.1 → 0.9 c.

  Panel F     Casimir (1948) energy density  ρ = −π²ħc / (720 d⁴)
              Exact leading-order QED result for ideal parallel plates.
              d animated 2 → 150 nm.  Values in SI (J m⁻³).

References:
  Alcubierre, M. (1994). Class. Quantum Grav. 11, L73–L77.
  Casimir, H.B.G. (1948). Proc. K. Ned. Akad. Wet. 51, 793.

Requirements:
    pip install rdkit matplotlib numpy
"""

from rdkit import Chem
from rdkit.Chem import AllChem
import matplotlib.pyplot as plt
import matplotlib.animation as animation
from matplotlib.colors import LinearSegmentedColormap
from matplotlib.collections import LineCollection
import numpy as np

# ── Physical constants (SI) ───────────────────────────────────────────────────
HBAR_C_SI = 1.0546e-34 * 2.998e8   # ħc = 3.162 × 10⁻²⁶  J·m

# ── Colour maps ───────────────────────────────────────────────────────────────
DENSITY_CMAP = LinearSegmentedColormap.from_list(
    "density",
    ["#000010", "#001a4d", "#003d99", "#0099cc", "#66ddff", "#ffffff"],
    N=512,
)
# Exotic cmap: black (ρ=0) → bright purple (most negative T₀₀)
EXOTIC_CMAP = LinearSegmentedColormap.from_list(
    "exotic",
    ["#000000", "#000033", "#000099", "#6600cc", "#cc00ff"],
    N=512,
)

# ── Molecules ─────────────────────────────────────────────────────────────────
SMILES_LIST = [
    ("Benzene",    "c1ccccc1"),
    ("Azulene",    "C1=CC2=CC=CC=CC2=C1"),
    ("Anthracene", "c1ccc2cc3ccccc3cc2c1"),
    ("Naphthalene","c1ccc2ccccc2c1"),
]

def get_molecule(smiles):
    """RDKit: 2-D nuclear positions, bond list, atomic numbers."""
    mol = Chem.MolFromSmiles(smiles)
    if mol is None:
        return np.zeros((1, 2)), [], [6]
    AllChem.Compute2DCoords(mol)
    conf = mol.GetConformer()
    pos = np.array([[conf.GetAtomPosition(i).x,
                     conf.GetAtomPosition(i).y]
                    for i in range(mol.GetNumAtoms())])
    rng = pos.max(0) - pos.min(0)
    rng[rng == 0] = 1.0
    pos = (pos - pos.mean(0)) / rng.max() * 1.8
    bonds = [(b.GetBeginAtomIdx(), b.GetEndAtomIdx()) for b in mol.GetBonds()]
    Z = [mol.GetAtomWithIdx(i).GetAtomicNum() for i in range(mol.GetNumAtoms())]
    return pos, bonds, Z

molecules = [(name, *get_molecule(smi)) for name, smi in SMILES_LIST]

# ── Physics functions ─────────────────────────────────────────────────────────

def electron_density(X, Y, pos, Z_list):
    """
    Slater-type 1s orbital superposition.

        ρ_e(r) = Σᵢ  Zᵢ · exp(−αᵢ · |r − rᵢ|)     αᵢ = Zᵢ · 0.4

    Always ρ_e ≥ 0.  Qualitatively correct topology (higher Z → more compact).
    Not a full DFT/HF calculation; RDKit supplies nuclear positions only.
    """
    rho = np.zeros_like(X)
    for (ax, ay), Z in zip(pos, Z_list):
        r = np.sqrt((X - ax)**2 + (Y - ay)**2)
        rho += Z * np.exp(-Z * 0.4 * r)
    return rho


def df_dr(r, R=1.5, sigma=0.5):
    """
    Derivative of Alcubierre (1994) shape function f(rₛ):

        f(rₛ) = [tanh(σ(rₛ+R)) − tanh(σ(rₛ−R))] / [2·tanh(σR)]

        df/drₛ = σ · [sech²(σ(rₛ+R)) − sech²(σ(rₛ−R))] / [2·tanh(σR)]
    """
    norm  = 2.0 * np.tanh(sigma * R)
    sech2_plus  = 1.0 - np.tanh(sigma * (r + R))**2
    sech2_minus = 1.0 - np.tanh(sigma * (r - R))**2
    return sigma * (sech2_plus - sech2_minus) / norm


def alcubierre_T00(X, Y, vs, R=1.5, sigma=0.5):
    """
    Exotic-matter energy density required by the Alcubierre warp metric.

    From Einstein's equations G_μν = 8πT_μν applied to:
        ds² = −dt² + (dx − vₛ f(rₛ) dt)² + dy² + dz²

    The Eulerian-observer energy density is:
        T₀₀ = −(vₛ²/32π) · (Y²/r²) · (df/dr)²

    Reference: Alcubierre (1994), eq. (8), natural units c=G=1.

    T₀₀ ≤ 0 everywhere → WEC (and NEC) violated at every point in the
    bubble wall.  Zero only where Y = 0 (the axis of travel).
    """
    r    = np.sqrt(X**2 + Y**2)
    r    = np.where(r < 1e-9, 1e-9, r)
    dfdr = df_dr(r, R, sigma)
    return -(vs**2 / (32.0 * np.pi)) * (Y**2 / r**2) * dfdr**2


def casimir_rho(d_nm):
    """
    Casimir energy density between two ideal parallel conducting plates.

        ρ_Cas = −π²ħc / (720 d⁴)

    Exact leading-order QED result (zero-temperature, perfect conductors).
    d_nm: plate separation in nanometres.  Returns J m⁻³.
    """
    d = d_nm * 1e-9
    return -(np.pi**2 * HBAR_C_SI) / (720.0 * d**4)


# ── Grid ──────────────────────────────────────────────────────────────────────
N = 200
x = np.linspace(-2.5, 2.5, N)
y = np.linspace(-2.5, 2.5, N)
X, Y = np.meshgrid(x, y)

# Fixed colour scale for T₀₀ based on vs = 0.9 (worst case)
T00_SCALE = float(alcubierre_T00(X, Y, 0.9).min())

# ── Figure ────────────────────────────────────────────────────────────────────
fig = plt.figure(figsize=(18, 10), facecolor="#000008")
fig.suptitle(
    "Exotic-Matter Physics Visualizer  ·  Physically grounded computation",
    fontsize=13, color="#aaddff", fontweight="bold", y=0.98,
)

gs = fig.add_gridspec(2, 4, hspace=0.50, wspace=0.30,
                      left=0.05, right=0.96, top=0.93, bottom=0.07)

mol_axes = [fig.add_subplot(gs[0, i]) for i in range(4)]
warp_ax  = fig.add_subplot(gs[1, 0:2])
cas_ax   = fig.add_subplot(gs[1, 2:4])

for ax in mol_axes + [warp_ax, cas_ax]:
    ax.set_facecolor("#000010")
    for sp in ax.spines.values():
        sp.set_color("#002244")

# ── Molecular electron-density panels ────────────────────────────────────────
mol_data = []   # (imshow_artist, pos0, bonds, Z_list)
mol_lcs  = []
mol_scs  = []

for i, (name, pos0, bonds, Z) in enumerate(molecules):
    ax = mol_axes[i]
    ax.set_xlim(-2.6, 2.6); ax.set_ylim(-2.6, 2.6)
    ax.set_aspect("equal"); ax.axis("off")
    ax.set_title(f"{name}\nElectron density  ρ_e(r)  [STO approx.]",
                 color="#88ccff", fontsize=8, pad=3)

    rho0   = electron_density(X, Y, pos0, Z)
    rho_hi = rho0.max() * 0.65

    im = ax.imshow(rho0, extent=[-2.5, 2.5, -2.5, 2.5],
                   origin="lower", cmap=DENSITY_CMAP,
                   vmin=0, vmax=rho_hi, animated=True)
    mol_data.append((im, pos0, bonds, Z))

    lc = LineCollection([[pos0[a], pos0[b]] for a, b in bonds],
                        colors="#ffffff", linewidths=1.0, alpha=0.45, zorder=3)
    ax.add_collection(lc)
    mol_lcs.append(lc)

    sizes = [15 + 4 * z for z in Z]
    sc = ax.scatter(pos0[:, 0], pos0[:, 1], s=sizes,
                    c="#ffdd88", zorder=4, edgecolors="#ffffff", linewidths=0.4)
    mol_scs.append(sc)

    ax.text(0.02, 0.02, "ρ_e ≥ 0  (ordinary matter)",
            transform=ax.transAxes, color="#445566", fontsize=6, style="italic")

# ── Alcubierre T₀₀ panel ─────────────────────────────────────────────────────
warp_ax.set_title(
    "Alcubierre (1994)   T₀₀ = −(vₛ²/32π)·(Y²/r²)·(df/dr)²\n"
    "from  G_μν = 8πT_μν   ·   Planck units   ·   T₀₀ ≤ 0  (WEC violated)",
    color="#ffcc44", fontsize=8,
)
warp_ax.set_xlim(-2.5, 2.5); warp_ax.set_ylim(-2.5, 2.5)
warp_ax.set_aspect("equal"); warp_ax.axis("off")

T00_init = alcubierre_T00(X, Y, 0.3)
warp_im = warp_ax.imshow(
    T00_init, extent=[-2.5, 2.5, -2.5, 2.5],
    origin="lower", cmap=EXOTIC_CMAP,
    vmin=T00_SCALE, vmax=0.0,
    alpha=0.95, animated=True,
)
cb = fig.colorbar(warp_im, ax=warp_ax, fraction=0.03, pad=0.01)
cb.set_label("T₀₀  [Planck units]", color="#ffcc44", fontsize=7)
cb.ax.yaxis.set_tick_params(color="#ffcc44", labelsize=6)
plt.setp(cb.ax.yaxis.get_ticklabels(), color="#ffcc44")

warp_cont = [warp_ax.contour(X, Y, T00_init, levels=7,
                              colors="#ffff66", alpha=0.5, linewidths=0.5)]
bubble_ring = plt.Circle((0, 0), 1.5, fill=False,
                          edgecolor="#ff8800", linewidth=1.5, linestyle="--")
warp_ax.add_patch(bubble_ring)
warp_txt = warp_ax.text(-2.4, 2.1, "", color="#ffcc44", fontsize=8,
                         family="monospace")

# ── Casimir panel ─────────────────────────────────────────────────────────────
cas_ax.set_title(
    "Casimir (1948)   ρ = −π²ħc / (720 d⁴)   ·   QED, parallel conducting plates\n"
    "d animated 2 → 150 nm   ·   SI units (J m⁻³)   ·   ρ < 0",
    color="#88ffcc", fontsize=8,
)
cas_ax.axis("off")

# Inset axes for the log plot
cas_inner = cas_ax.inset_axes([0.06, 0.12, 0.88, 0.82])
cas_inner.set_facecolor("#000010")
for sp in cas_inner.spines.values():
    sp.set_color("#334455")
cas_inner.tick_params(colors="#88ffcc", labelsize=7)
cas_inner.set_xlabel("Plate separation  d  (nm)", color="#88ffcc", fontsize=8)
cas_inner.set_ylabel("|ρ_Cas|  (J m⁻³)", color="#88ffcc", fontsize=8)
cas_inner.grid(True, alpha=0.15, color="#334455")

d_curve = np.linspace(2.0, 150.0, 500)
rho_curve = -casimir_rho(d_curve)   # positive for plotting on log scale
cas_inner.semilogy(d_curve, rho_curve, color="#00ffaa", linewidth=1.5,
                   label=r"$|\rho_{\rm Cas}| = \pi^2\hbar c\,/\,(720\,d^4)$")

# Reference lines
for d_ref, label in [(10, "10 nm"), (50, "50 nm"), (100, "100 nm")]:
    r_ref = -casimir_rho(d_ref)
    cas_inner.axvline(d_ref, color="#334455", linewidth=0.6, linestyle=":")
    cas_inner.axhline(r_ref, color="#334455", linewidth=0.6, linestyle=":")

cas_inner.set_xlim(2, 150)
cas_inner.set_ylim(1e-2, 1e9)
cas_inner.legend(fontsize=7, facecolor="#001122", labelcolor="#88ffcc",
                 loc="upper right")

# Animated marker
cas_dot,  = cas_inner.semilogy([], [], "o", color="#ff4444", ms=7, zorder=5)
cas_vline = cas_inner.axvline(2, color="#ff4444", linewidth=1.0,
                               linestyle="--", alpha=0.6)
cas_txt = cas_inner.text(0.97, 0.95, "", transform=cas_inner.transAxes,
                          ha="right", va="top", color="#ff4444",
                          fontsize=7.5, family="monospace")

# ── Animation ─────────────────────────────────────────────────────────────────
FRAMES = 300

def vibrate(pos, t, idx, amp=0.025):
    """Small sinusoidal displacement (zero-point-like vibration)."""
    n  = len(pos)
    dx = amp * np.sin(t * 1.3 + np.arange(n) * 0.7 + idx)
    dy = amp * np.cos(t * 1.1 + np.arange(n) * 0.9 + idx * 1.3)
    return pos + np.column_stack([dx, dy])

def update(frame):
    t   = frame * 0.06
    out = []

    # -- Electron density panels --
    for i, (im, pos0, bonds, Z) in enumerate(mol_data):
        pos = vibrate(pos0, t, i)
        im.set_data(electron_density(X, Y, pos, Z))
        out.append(im)

        mol_lcs[i].set_segments([[pos[a], pos[b]] for a, b in bonds])
        out.append(mol_lcs[i])

        mol_scs[i].set_offsets(pos)
        out.append(mol_scs[i])

    # -- Alcubierre T₀₀: animate vₛ 0.1 → 0.9 c --
    vs  = 0.1 + 0.8 * 0.5 * (1.0 - np.cos(t * 0.25))
    T00 = alcubierre_T00(X, Y, vs)
    warp_im.set_data(T00)
    out.append(warp_im)

    try:
        warp_cont[0].remove()
    except Exception:
        for coll in getattr(warp_cont[0], "collections", []):
            try:
                coll.remove()
            except Exception:
                pass
    warp_cont[0] = warp_ax.contour(X, Y, T00, levels=7,
                                    colors="#ffff66", alpha=0.4, linewidths=0.4)

    warp_txt.set_text(
        f"vₛ = {vs:.3f} c\n"
        f"T₀₀_min = {float(T00.min()):.5f}  [Planck]"
    )
    out.append(warp_txt)
    out.append(bubble_ring)

    # -- Casimir: log-sweep d 2 → 150 nm --
    phase = (frame % FRAMES) / FRAMES
    d_now = 2.0 * (75.0 ** phase)          # log sweep 2 → 150 nm
    rho_now = casimir_rho(d_now)

    cas_dot.set_data([d_now], [-rho_now])
    cas_vline.set_xdata([d_now, d_now])
    cas_txt.set_text(
        f"d  = {d_now:.1f} nm\n"
        f"ρ  = {rho_now:.3e} J/m³"
    )
    out += [cas_dot, cas_vline]

    return out

ani = animation.FuncAnimation(
    fig, update,
    frames=FRAMES,
    interval=40,
    blit=False,
)

plt.show()
exotic matter negative energy this is correct