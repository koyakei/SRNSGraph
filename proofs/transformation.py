import numpy as np
import matplotlib.pyplot as plt

# 日本語フォントの設定
plt.rcParams['font.sans-serif'] = [
    'Hiragino Sans', 'Hiragino Kaku Gothic ProN', 'Yu Gothic',
    'Meiryo', 'Noto Sans CJK JP', 'DejaVu Sans'
]
plt.rcParams['axes.unicode_minus'] = False

def simulate_transition_rent_with_fork_risk():
    T = 60
    t_steps = np.arange(T)

    # 1. 開放度・透明化スケジュール k_t (プログレッシブ・ディセントラライゼーション)
    k_t = 1.0 / (1.0 + np.exp(-0.12 * (t_steps - 25)))

    # 2. 変数・パラメータの設定
    pi_old_base = 8.0     # 閉鎖体制での旧特権層の既得権益ベースライン
    conflict_base = 5.5   # 抵抗コストのベースライン
    open_value_max = 12.0 # オープン化による市場全体の最大純利得

    # 補償ポリシーの比較シナリオ:
    # シナリオA: 最適な移行レント給付 R_opt(t) （完全な軟着陸）
    # シナリオB: 補償不足（50%カット） R_under(t) （不十分な買収）
    # シナリオC: ゼロ補償 R_zero(t) （硬直的な即時開放 / ショック療法）

    loss_of_privilege = pi_old_base * k_t
    conflict_cost = conflict_base * (1.0 - k_t) * (1.0 + 2.0 * k_t)
    max_affordable = open_value_max * k_t * (1.0 - 0.2 * k_t)

    # 必要な最低補償額 (特権喪失と対立コストをカバーする水準)
    r_required = np.maximum(loss_of_privilege * 0.85, conflict_cost)

    # シナリオごとの実際の給付レント
    r_opt = np.minimum(r_required, max_affordable)
    r_under = r_opt * 0.45
    r_zero = np.zeros(T)

    # 3. フォーク（内戦・不当分裂）確率 P_fork(t) の動的計算
    # 補償不足ギャップ Gap(t) = max(0, r_required - r_given)
    # P_fork(t) = 1 - exp(- beta * Gap(t) * k_t)
    beta = 0.35 # フォーク感応度

    gap_opt = np.maximum(0, r_required - r_opt)
    gap_under = np.maximum(0, r_required - r_under)
    gap_zero = np.maximum(0, r_required - r_zero)

    p_fork_opt = (1.0 - np.exp(-beta * gap_opt * k_t)) * 100
    p_fork_under = (1.0 - np.exp(-beta * gap_under * k_t)) * 100
    p_fork_zero = (1.0 - np.exp(-beta * gap_zero * k_t)) * 100

    # -------------------------------------------------------------------------
    # 2パネルグラフ描画
    # -------------------------------------------------------------------------
    fig, (ax1, ax2) = plt.subplots(2, 1, figsize=(11, 9.5), dpi=120, sharex=True)
    plt.subplots_adjust(hspace=0.25)

    # パネル1: 移行レントの推移と補償不足ギャップ
    ax1.plot(t_steps, k_t * 10, color='#7f8c8d', lw=1.8, ls=':', label='開放度 $k_t$ (×10)')
    ax1.plot(t_steps, r_required, color='#c0392b', lw=2.2, ls='--', label='必要最低補償額 $R_{\mathrm{req}}(t)$')
    ax1.plot(t_steps, r_opt, color='#1b4f72', lw=2.8, label='シナリオA: 最適移行レント $R_{\mathrm{opt}}(t)$ (完全給付)')
    ax1.plot(t_steps, r_under, color='#e67e22', lw=2.4, label='シナリオB: 補償不足 $R_{\mathrm{under}}(t)$ (55%カット)')
    ax1.plot(t_steps, r_zero, color='#95a5a6', lw=2.0, label='シナリオC: ゼロ補償 $R_{\mathrm{zero}}(t)$ (ショック療法)')

    ax1.set_title('① 移行プロセスの開放度 $k_t$ と移行レント $R_{\mathrm{transition}}(t)$ の給付シナリオ', fontsize=12, fontweight='bold')
    ax1.set_ylabel('経済的価値・レントの大きさ', fontsize=11)
    ax1.set_ylim(0, 10.5)
    ax1.legend(loc='upper right', fontsize=8.5, framealpha=0.9)
    ax1.grid(True, linestyle=':', alpha=0.5)

    # パネル2: フォーク（内戦・分裂）確率 P_fork(t) の動的変動
    ax2.plot(t_steps, p_fork_opt, color='#1b4f72', lw=2.8, label='シナリオA (最適給付): フォークリスク $P_{\mathrm{fork}}$ (抑止成功)')
    ax2.plot(t_steps, p_fork_under, color='#e67e22', lw=2.8, label='シナリオB (補償不足): フォークリスク $P_{\mathrm{fork}}$ (高リスク)')
    ax2.plot(t_steps, p_fork_zero, color='#c0392b', lw=3.2, ls='-', label='シナリオC (ゼロ補償): フォークリスク $P_{\mathrm{fork}}$ (内戦・分裂不可避)')

    ax2.axhline(50, color='#73c6b6', ls='-.', lw=1.2, label='危険ライン (分裂確立 50%)')

    # 注釈
    peak_zero_idx = np.argmax(p_fork_zero)
    ax2.scatter([t_steps[peak_zero_idx]], [p_fork_zero[peak_zero_idx]], color='#c0392b', s=70, zorder=5)
    ax2.annotate(f'ゼロ補償時の分裂リスク最大化\n($P_{{\mathrm{{fork}}}} \\approx {p_fork_zero[peak_zero_idx]:.1f}\\%$)',
                xy=(t_steps[peak_zero_idx], p_fork_zero[peak_zero_idx]),
                xytext=(t_steps[peak_zero_idx] - 18, p_fork_zero[peak_zero_idx] - 22),
                arrowprops=dict(arrowstyle='->', lw=1.5, color='#c0392b'),
                fontsize=9.5, fontweight='bold',
                bbox=dict(boxstyle='round,pad=0.3', facecolor='#fadbd8'))

    ax2.set_title('② 補償ギャップに依存するフォーク（内戦・不当分裂）確率 $P_{\mathrm{fork}}(t)$ の動的推移', fontsize=12, fontweight='bold')
    ax2.set_xlabel('経過期間 $t$ (ステップ)', fontsize=11)
    ax2.set_ylabel('フォーク発生確率 $P_{\mathrm{fork}}(t)$ (%)', fontsize=11)
    ax2.set_xlim(0, T - 1)
    ax2.set_ylim(-2, 105)
    ax2.legend(loc='center left', fontsize=8.5, framealpha=0.9)
    ax2.grid(True, linestyle=':', alpha=0.5)

    plt.suptitle('移行レント補償の成否とプロトコル分裂（フォーク）リスクの相互作用モデル', fontsize=14, fontweight='bold', y=0.98)
    
    filename = 'transition_rent_fork_simulation.png'
    plt.savefig(filename, bbox_inches='tight')
    plt.show()
    return filename

simulate_transition_rent_with_fork_risk()