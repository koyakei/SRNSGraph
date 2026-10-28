import numpy as np
import matplotlib.pyplot as plt
from matplotlib.patches import Patch

# 日本語フォントの設定（OS環境に応じた自動フォールバック）
plt.rcParams['font.sans-serif'] = [
    'Hiragino Sans', 'Hiragino Kaku Gothic ProN', 'Yu Gothic',
    'Meiryo', 'Noto Sans CJK JP', 'IPAexGothic', 'TakaoPGothic', 'DejaVu Sans'
]
plt.rcParams['axes.unicode_minus'] = False


def plot_evaluation_system_dynamics():
    fig, axes = plt.subplots(2, 2, figsize=(16, 12), dpi=120)
    plt.subplots_adjust(wspace=0.25, hspace=0.32)

    # =========================================================================
    # パネル1 (左上): 相図（検索離れ率 ν_t × 制度的減衰率 λ_inst における4つの運命）
    # =========================================================================
    ax1 = axes[0, 0]
    nu = np.linspace(0.0, 0.98, 400)
    lam = np.linspace(0.01, 0.99, 400)
    NU, LAM = np.meshgrid(nu, lam)

    # 下限: ゾンビ化・破壊的リセット(D)阻止ライン \lambda_{inst}^{min}(\nu_t)
    lam_lower = 0.12 + 0.35 * (nu ** 1.4) + 0.15 * (nu / (1.05 - nu))
    # 上限: ゲーミング横行・認知精度崩壊阻止ライン \lambda_{inst}^{max}(\nu_t)
    lam_upper = 0.82 - 0.38 * (nu ** 1.2)

    # 破壊的リセット(D)すら不採算になる廃墟化(A)境界 \nu_t^{irrev}
    # C_destroy が高止まりする一方、再起動レントが縮小して交差する境界
    nu_ruin_boundary = 0.72 - 0.12 * ((LAM - 0.45) ** 2)

    # 領域分類マップの作成
    # 1: 健全な新陳代謝(C), 2: 制度疲労・破壊的リセット(D), 3: ゲーミング・精度崩壊, 4: 完全放置・廃墟化(A)
    phase_map = np.zeros_like(NU)
    lower_2d = 0.12 + 0.35 * (NU ** 1.4) + 0.15 * (NU / (1.05 - NU))
    upper_2d = 0.82 - 0.38 * (NU ** 1.2)

    phase_map[(LAM >= lower_2d) & (LAM <= upper_2d) & (NU < nu_ruin_boundary)] = 1  # 勢力C (黄金の回廊)
    phase_map[(LAM < lower_2d) & (NU < nu_ruin_boundary)] = 2                       # 勢力D (破壊的リセット)
    phase_map[(LAM > upper_2d) & (NU < nu_ruin_boundary)] = 3                       # ゲーミング崩壊
    phase_map[NU >= nu_ruin_boundary] = 4                                           # 廃墟化均衡A

    # カラーマップ描画
    from matplotlib.colors import ListedColormap
    cmap = ListedColormap(['#d4efdf', '#f5b7b1', '#fdebd0', '#d5d8dc'])
    ax1.pcolormesh(NU, LAM, phase_map, cmap=cmap, shading='auto', alpha=0.85)

    # 境界線のプロット
    valid_idx = lam_lower < lam_upper
    ax1.plot(nu[valid_idx], lam_lower[valid_idx], color='#c0392b', lw=2.2,
             label=r'下限 $\lambda_{\mathrm{inst}}^{\min}$ (破壊 $\mathcal{D}$ 阻止境界)')
    ax1.plot(nu[valid_idx], lam_upper[valid_idx], color='#d35400', lw=2.2, ls='--',
             label=r'上限 $\lambda_{\mathrm{inst}}^{\max}$ (対ゲーミング・精度境界)')
    ax1.axvline(0.72, color='#566573', lw=2.0, ls=':',
                label=r'廃墟化境界 $\nu_t^{\mathrm{irrev}}$ (条件 A-2 崩壊)')

    # 動的適応フィードバック軌道のプロット
    nu_traj = np.linspace(0.0, 0.58, 100)
    lam_opt_traj = 0.28 + 0.42 * (nu_traj ** 1.3)
    ax1.plot(nu_traj, lam_opt_traj, color='#1b4f72', lw=2.8,
             label=r'最適適応フィードバック軌道 $\lambda_{\mathrm{inst}}^*(t)$')

    ax1.set_title('① 評価システムの相図（4つの運命と黄金の回廊）', fontsize=12, fontweight='bold')
    ax1.set_xlabel(r'検索離れ率・不可逆離脱率 $\nu_t$', fontsize=11)
    ax1.set_ylabel(r'評価・既得権の計画的減衰率 $\lambda_{\mathrm{inst}}$', fontsize=11)
    ax1.set_xlim(0, 0.98)
    ax1.set_ylim(0.01, 0.99)

    # 領域ラベルの配置
    ax1.text(0.25, 0.48, '【1. 健全な新陳代謝 (勢力 C)】\n黄金の回廊 (Goldilocks Corridor)',
             fontsize=9.5, fontweight='bold', color='#145a32', ha='center',
             bbox=dict(boxstyle='round,pad=0.3', facecolor='white', alpha=0.8))
    ax1.text(0.32, 0.12, '【2/3. ゾンビ化 → 破壊的リセット (勢力 D)】\n既得権・負債の固定化 ($D_{i,t}$ 爆発)',
             fontsize=9, fontweight='bold', color='#78281f', ha='center')
    ax1.text(0.28, 0.86, '【精度崩壊・ゲーミング領域】\n忘却過多による条件②-b崩壊',
             fontsize=9, fontweight='bold', color='#7e5109', ha='center')
    ax1.text(0.85, 0.50, '【4. 完全放置・廃墟化 (A)】\nGhost Archive\n(破壊すら不採算)',
             fontsize=9, fontweight='bold', color='#2c3e50', ha='center', rotation=90)
    ax1.legend(loc='lower left', fontsize=8.5, framealpha=0.9)
    ax1.grid(True, linestyle=':', alpha=0.4)

    # =========================================================================
    # パネル2 (右上): 最適減衰率 \lambda_{inst}^* の限界均衡条件（条件Ⅰ・Ⅲの可視化）
    # =========================================================================
    ax2 = axes[0, 1]
    lam_grid = np.linspace(0.04, 0.96, 300)

    # 忘却を速める限界便益 MB(\lambda_{inst}): スティグマ軽減 + 首位交代促進 + 検索離れ防止
    MB = 1.8 / (lam_grid + 0.12) + 1.2 * np.exp(-2.5 * lam_grid)
    # 忘却を速める限界費用 MC(\lambda_{inst}): 推計ノイズ増大 + 短期的ゲーミング急増
    MC = 0.6 + 2.2 * (lam_grid ** 1.8) + 1.5 / (1.02 - lam_grid)

    # 純価値 V_net(\lambda_{inst}) (スケーリング表示)
    V_net = 8.5 - 0.8 / (lam_grid + 0.05) - 1.4 / (1.02 - lam_grid) + 2.5 * np.sin(np.pi * lam_grid)

    # 均衡点 \lambda_{inst}^* の算出
    opt_idx = np.argmin(np.abs(MB - MC))
    lam_star = lam_grid[opt_idx]
    mb_star = MB[opt_idx]

    lam_min_bound = 0.22
    lam_max_bound = 0.74

    ax2.axvspan(lam_min_bound, lam_max_bound, color='#d4efdf', alpha=0.5,
                label=r'許容帯域 $[\lambda_{\mathrm{inst}}^{\min},\, \lambda_{\mathrm{inst}}^{\max})$')
    ax2.plot(lam_grid, MB, color='#2874a6', lw=2.5,
             label=r'限界便益 $MB(\lambda_{\mathrm{inst}})$：負債軽減＋新陳代謝促進')
    ax2.plot(lam_grid, MC, color='#cb4335', lw=2.5,
             label=r'限界費用 $MC(\lambda_{\mathrm{inst}})$：ノイズ増＋ゲーミング損失')
    ax2.plot(lam_grid, V_net, color='#1e8449', lw=2.0, ls='-.',
             label=r'システム長期純価値 $W(\lambda_{\mathrm{inst}})$')

    ax2.scatter([lam_star], [mb_star], color='black', zorder=5, s=70)
    ax2.axvline(lam_star, color='black', ls=':', lw=1.5)
    ax2.axvline(lam_min_bound, color='#c0392b', ls='--', lw=1.2)
    ax2.axvline(lam_max_bound, color='#d35400', ls='--', lw=1.2)

    ax2.annotate(f'最適減衰率 $\\lambda_{{\\mathrm{{inst}}}}^* \\approx {lam_star:.2f}$\n($MB = MC$)',
                 xy=(lam_star, mb_star), xytext=(lam_star + 0.08, mb_star + 2.5),
                 arrowprops=dict(arrowstyle='->', lw=1.5),
                 fontsize=9.5, fontweight='bold',
                 bbox=dict(boxstyle='round,pad=0.3', facecolor='#fef9e7'))

    ax2.set_title(r'② 最適制度減衰率 $\lambda_{\mathrm{inst}}^*$ の限界均衡条件（条件Ⅰ・Ⅲ）', fontsize=12, fontweight='bold')
    ax2.set_xlabel(r'制度的減衰率 $\lambda_{\mathrm{inst}}$', fontsize=11)
    ax2.set_ylabel('限界価値・限界コスト / 純価値', fontsize=11)
    ax2.set_xlim(0.04, 0.96)
    ax2.set_ylim(0, 12)
    ax2.legend(loc='upper center', fontsize=8.5, framealpha=0.9)
    ax2.grid(True, linestyle=':', alpha=0.5)

    # =========================================================================
    # パネル3 (左下): 検索離れ \nu_t に伴う勢力 C・勢力 D・廃墟化 A の純利得比較
    # =========================================================================
    ax3 = axes[1, 0]
    nu_x = np.linspace(0, 0.95, 300)

    # 1) 減衰・圧縮なし(硬直システム)での勢力Cの純利得: 維持費C_mig+C_enfが重く早期にマイナスへ
    pi_C_rigid = 6.5 * ((1 - nu_x) ** 1.3) - 3.8
    # 2) 破壊的独占勢力Dの純利得: 社会破壊 \delta_{soc} はあるが過去ログ維持費を踏み倒し独占レントを得る
    #    ただし不可逆離脱が進むと C_destroy(下限硬直) を回収できずマイナスへ
    pi_D_mono = 5.2 * ((1 - 0.85 * nu_x) ** 1.6) - 2.1
    # 3) 計画的減衰・動的圧縮 (\lambda_{inst}^*, \kappa_{comp}^*) 導入時の勢力Cの純利得
    #    検索離れに応じてアーカイブ圧縮 \kappa_{comp} が働き維持費が削減され、シグナル効力も維持される
    pi_C_adaptive = 7.2 * ((1 - 0.65 * nu_x) ** 1.1) - 1.5 * (1 - 0.5 * nu_x)

    ax3.plot(nu_x, pi_C_rigid, color='#2e86c1', lw=2.2, ls='--',
             label=r'勢力 $\mathcal{C}$ 純利得（減衰・圧縮なし：硬直システム）')
    ax3.plot(nu_x, pi_D_mono, color='#c0392b', lw=2.5,
             label=r'勢力 $\mathcal{D}$ 純利得（記録抹消・破壊的独占リセット）')
    ax3.plot(nu_x, pi_C_adaptive, color='#27ae60', lw=2.8,
             label=r'勢力 $\mathcal{C}$ 純利得（計画的減衰 $\lambda_{\mathrm{inst}}^*$・圧縮 $\kappa_{\mathrm{comp}}^*$ 導入）')
    ax3.axhline(0, color='black', lw=1.5, ls='-', label=r'参入・維持採算ライン ($\Pi^{\mathrm{alt}} = 0$)')

    # 硬直システムにおいて D が C を逆転する点、および D も 0 を割って廃墟化する点
    idx_C_to_D = np.argmin(np.abs(pi_C_rigid - pi_D_mono))
    idx_D_to_A = np.argmin(np.abs(pi_D_mono - 0.0))

    ax3.scatter([nu_x[idx_C_to_D]], [pi_D_mono[idx_C_to_D]], color='#c0392b', s=60, zorder=5)
    ax3.scatter([nu_x[idx_D_to_A]], [0.0], color='#566573', s=60, zorder=5)

    ax3.axvspan(nu_x[idx_C_to_D], nu_x[idx_D_to_A], color='#f5b7b1', alpha=0.25,
                label='硬直時に破壊(D)が正当化される領域')
    ax3.axvspan(nu_x[idx_D_to_A], 0.95, color='#d5d8dc', alpha=0.45,
                label='完全放置・廃墟化領域 (A)')

    ax3.set_title(r'③ 勢力 $\mathcal{C}$・勢力 $\mathcal{D}$・廃墟化 $\mathcal{A}$ の期待純利得と相転移', fontsize=12, fontweight='bold')
    ax3.set_xlabel(r'検索離れ率 $\nu_t$', fontsize=11)
    ax3.set_ylabel('各主体の期待純利得 $\Pi - \Pi^{\mathrm{alt}}$', fontsize=11)
    ax3.set_xlim(0, 0.95)
    ax3.set_ylim(-3.5, 6.5)
    ax3.legend(loc='upper right', fontsize=8.0, framealpha=0.9)
    ax3.grid(True, linestyle=':', alpha=0.5)

    # =========================================================================
    # パネル4 (右下): 時間発展シミュレーション（動的適応フィードバック則 vs 固定ルール）
    # =========================================================================
    ax4 = axes[1, 1]
    T = 100
    t_steps = np.arange(T)

    # 環境ショック: t=30〜60 にかけて人間の忘却率 \lambda_{mem}(t) が上昇（トレンド激化ショック）
    lam_mem_t = 0.15 + 0.25 / (1 + np.exp(-0.25 * (t_steps - 35)))

    # シミュレーション配列 [A: 固定ルール(低減衰), B: 動的適応フィードバック則]
    V_rigid = np.zeros(T)
    V_adapt = np.zeros(T)
    debt_rigid = np.zeros(T)
    debt_adapt = np.zeros(T)

    V_rigid[0], V_adapt[0] = 8.0, 8.0
    debt_rigid[0], debt_adapt[0] = 1.0, 1.0

    lam_fixed = 0.06  # 固定の低い制度減衰率

    for t in range(1, T):
        # --- ケースA: 固定ルール ---
        # 既得権・負債ストック \Omega_{debt} が累積し、検索離れが加速
        debt_rigid[t] = (1 - lam_fixed) * debt_rigid[t - 1] + 1.0
        gap_rigid = max(0, debt_rigid[t] * lam_mem_t[t] - 1.2)
        V_rigid[t] = max(0.2, V_rigid[t - 1] + 0.35 - 0.12 * gap_rigid - 0.015 * t)

        # --- ケースB: 動的適応フィードバック則 (\lambda_{inst}(t), \kappa_{comp}(t)) ---
        # 新陳代謝の低下や \lambda_{mem}(t) の上昇を検知して減衰率を自動引き上げ
        lam_inst_t = np.clip(0.22 + 0.85 * (lam_mem_t[t] - 0.15) + 0.04 * max(0, 6.5 - V_adapt[t - 1]), 0.15, 0.70)
        debt_adapt[t] = (1 - lam_inst_t) * debt_adapt[t - 1] + 1.0
        gap_adapt = max(0, debt_adapt[t] * lam_mem_t[t] - 1.2)
        # アーカイブ圧縮 \kappa_{comp}(t) により維持費膨張も抑制
        V_adapt[t] = min(8.8, max(1.0, V_adapt[t - 1] + 0.42 * (1 - V_adapt[t - 1] / 9.5) - 0.08 * gap_adapt))

    # 閾値ライン
    threshold_D = 3.5  # これを下回ると破壊的リセット(D)が優位に
    threshold_A = 1.2  # これを下回ると完全廃墟化(A)へ

    ax4.plot(t_steps, V_adapt, color='#27ae60', lw=2.8,
             label=r'システム価値 $V_{g,t}^{\mathcal{H}}$（動的適応フィードバック則：勢力 $\mathcal{C}$ 維持）')
    ax4.plot(t_steps, V_rigid, color='#2e86c1', lw=2.4, ls='--',
             label=r'システム価値 $V_{g,t}^{\mathcal{H}}$（減衰不全・固定ルール：ゾンビ化 $\to$ 崩壊）')
    ax4.plot(t_steps, debt_rigid * 0.4, color='#8e44ad', lw=1.6, ls=':',
             label=r'既得権・負債ストック $\Omega_{\mathrm{debt}}(t)$（固定ルール時・スケール表示）')

    ax4.axhline(threshold_D, color='#c0392b', lw=1.5, ls='-.',
                label='破壊的リセット正当化ライン (条件Ⅰ〜Ⅳ発火)')
    ax4.axhline(threshold_A, color='#566573', lw=1.5, ls=':',
                label='完全放置・廃墟化ライン (条件 A-1〜A-5発火)')
    ax4.axvspan(30, 55, color='#fdebd0', alpha=0.4, label=r'環境変化ショック期 ($\lambda_{\mathrm{mem}}(t) \uparrow$)')

    ax4.set_title('④ 時間発展シミュレーション（動的適応フィードバック則 vs 硬直ルール）', fontsize=12, fontweight='bold')
    ax4.set_xlabel('経過期間 $t$ (ステップ)', fontsize=11)
    ax4.set_ylabel('評価システムの有効価値 / 負債ストック', fontsize=11)
    ax4.set_xlim(0, T - 1)
    ax4.set_ylim(0, 9.5)
    ax4.legend(loc='lower left', fontsize=8.0, framealpha=0.9)
    ax4.grid(True, linestyle=':', alpha=0.5)

    plt.suptitle('公開評価システムの新陳代謝・破壊的リセット・廃墟化および最適減衰プロトコルの数理動態',
                 fontsize=15, fontweight='bold', y=0.98)
    plt.savefig('evaluation_system_dynamics.png', bbox_inches='tight')
    plt.show()


if __name__ == '__main__':
    plot_evaluation_system_dynamics()