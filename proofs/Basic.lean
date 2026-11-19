-- Lean 4 による評価システムの動的ガバナンス・公開条件・いじめ/テロ均衡・
-- 3ガチャAI動学・フロンティア相転移の数理モデル形式化

-- ============================================================================
-- セクション 0: 基本モデル（記録継承定理 / Condition C-1）
-- ============================================================================

/-- 評価システムの構造パラメータ群（型による不変条件の強制） -/
structure SystemParams where
  V_H      : Int  -- 記録継承時のシステム価値 V_{g,t+1}^{\mathcal{H}}
  V_empty  : Int  -- 記録抹消時のシステム価値 V_{g,t+1}^{\emptyset}
  theta_c  : Int  -- ルール内競争マージン \theta_{comp}
  theta_m  : Int  -- 破壊的独占マージン \theta_{mono}
  C_mig    : Int  -- 圧縮後の記録移行コスト C_{mig}(L_{eff})
  C_enf    : Int  -- 暴力装置維持コスト C_{enf}^{maint}
  C_raw    : Int  -- 新規評価発行コスト |S'_{c,t}| c_{raw,c}
  C_dest   : Int  -- 記録抹消・破壊コスト C_{destroy}(\alpha_{log})
  -- 公理（定義域の制約）
  h_val    : V_H > V_empty ∧ V_empty ≥ 0
  h_theta  : 0 < theta_c ∧ theta_c ≤ theta_m ∧ theta_m ≤ 1

/-- 勢力 C（記録継承・新規評価発行）の期待純利得 -/
def netPayoffC (p : SystemParams) : Int :=
  p.theta_c * p.V_H - p.C_mig - p.C_enf - p.C_raw

/-- 勢力 D（記録抹消・破壊的独占）の期待純利得 -/
def netPayoffD (p : SystemParams) : Int :=
  p.theta_m * p.V_empty - p.C_dest

/--
  【定理】記録・制度の破壊抑止条件 (Condition C-1):
  公開性 \alpha_{log} による破壊コスト C_dest が、独占レントの増分と
  ルール内維持・新規発行コストの合計を上回るとき、必ず勢力 C は勢力 D を凌駕する。
-/
theorem constitutional_dominates_destructive
    (p : SystemParams)
    (h_anti_erasure :
      p.theta_c * p.V_H + p.C_dest >
      p.theta_m * p.V_empty + p.C_mig + p.C_enf + p.C_raw) :
    netPayoffC p > netPayoffD p := by
  unfold netPayoffC netPayoffD
  omega

/-- サンプルパラメータ例（4race.py の動態モデルに基づく数値例） -/
def sampleParams : SystemParams where
  V_H := 100
  V_empty := 10
  theta_c := 1
  theta_m := 1
  C_mig := 5
  C_enf := 10
  C_raw := 15
  C_dest := 50
  h_val := by decide
  h_theta := by decide

-- ============================================================================
-- セクション 1: 三層の非排他的役割選択・公開度設計・血脈継承 vs 状態引き継ぎ
-- ============================================================================

/-- 三層 R = {cons, cur, adm} における主体 k の個体別純利得 -/
structure RolePayoffs where
  cons : Int  -- 利用者層純利得 \Pi_{k,t}^{cons}(g) = \Delta C_k(g)
  cur  : Int  -- キュレーター層純利得 \Pi_{k,t}^{cur}(g)
  adm  : Int  -- 評価管理者層純利得 \Pi_{k,t}^{adm}(g)
  deriving Repr

/-- 利用者層にとっての他層転向利得（機会費用）\Pi_{k,t}^{alt(-cons)} -/
def altForCons (rp : RolePayoffs) : Int := max rp.cur rp.adm

/-- キュレーターにとっての他層転向利得（機会費用）\Pi_{k,t}^{alt(-cur)} -/
def altForCur (rp : RolePayoffs) : Int := max rp.cons rp.adm

/-- 評価管理者にとっての他層転向利得（機会費用）\Pi_{k,t}^{alt(-adm)} -/
def altForAdm (rp : RolePayoffs) : Int := max rp.cons rp.cur

/-- 各層への参入・残留条件（非排他的部分集合 N_t^cons, N_t^cur, N_t^adm） -/
def canEnterCons (rp : RolePayoffs) : Prop := rp.cons ≥ altForCons rp
def canEnterCur (rp : RolePayoffs) : Prop := rp.cur ≥ altForCur rp
def canEnterAdm (rp : RolePayoffs) : Prop := rp.adm ≥ altForAdm rp

/-- 一人の主体 k が三層すべてを同時に兼任可能な状態 (N_t^cons ∩ N_t^cur ∩ N_t^adm ≠ ∅) -/
def isNonExclusiveMultiRole (rp : RolePayoffs) : Prop :=
  canEnterCons rp ∧ canEnterCur rp ∧ canEnterAdm rp

/-- 三層の純利得が等しい主体は、すべての層に同時参入・兼任可能である -/
theorem non_exclusive_joint_equilibrium
    (rp : RolePayoffs)
    (h_tie : rp.cons = rp.cur ∧ rp.cur = rp.adm) :
    isNonExclusiveMultiRole rp := by
  unfold isNonExclusiveMultiRole canEnterCons canEnterCur canEnterAdm
  unfold altForCons altForCur altForAdm
  omega

/-- 任意の主体 k は必ず少なくとも1つの最良層（外部オプション以上）を選択できる -/
theorem exists_optimal_layer (rp : RolePayoffs) :
    canEnterCons rp ∨ canEnterCur rp ∨ canEnterAdm rp := by
  unfold canEnterCons canEnterCur canEnterAdm altForCons altForCur altForAdm
  omega

/-- 記録保存期間 L と 2種類の公開度 (\alpha_{log}, \alpha_{mech}) を含むガバナンス設計パラメータ -/
structure DisclosureGovernanceParams where
  L                       : Nat  -- 記録保存期間（アーカイブ長）L
  alphaLog                : Int  -- 行動履歴の公開度 \alpha_{log} \in [0, 100]
  alphaMech               : Int  -- 管理手段の公開度 \alpha_{mech} \in [0, 100]
  betaLin                 : Int  -- 血縁割引率 \beta_{lin} \in [0, 100]
  consEffectiveVal        : Int  -- 利用者の有効便益 (1 - O(\rho)) |S_base| c_{raw}
  consSigCost             : Int  -- シグナル読解コスト M_{G_i} c_{sig}
  consAltMax              : Int  -- 利用者の他層転向利得 \max(\Pi^{cur}, \Pi^{adm})
  V_cur                   : Int  -- 当期システム付加価値 V_{g,t}
  p_gt                    : Int  -- 権限価格 p_{g,t}
  C_raw_cur               : Int  -- キュレーター原データ検証コスト |S'_{j,t}| c_{raw,j}
  R_retaliation           : Int  -- 公開に伴う萎縮・報復・模倣コスト R_j(\alpha_{log}, L)
  altCur                  : Int  -- 当期キュレーター転向利得 \Pi_{j,t}^{alt(-cur)}(\alpha_{mech})
  V_H_next                : Int  -- 履歴継承時の次期価値 V_{g,t+1}(\rho_t^* | H_{g,t}(L))
  V_empty_next            : Int  -- 履歴破棄時の次期価値 V_{g,t+1}(\rho_t^* | \emptyset)
  p_renew                 : Int  -- 次期更新価格 p_{g,t+1}^{renew}
  altCurNext              : Int  -- 次期キュレーター転向利得 \Pi_{j,t+1}^{alt(-cur)}(\alpha_{mech})
  deltaDet                : Int  -- 監査検知感度 \delta \Delta P(\omega_{g,t+1} | L, \alpha_{log})
  b_bribe                 : Int  -- 買収・忖度圧力 b_t(\alpha_{log}, L)
  openContinuationSurplus : Int  -- 開放環境での継続期待余剰 \Gamma^{open} \Delta \Pi^{adm}
  deltaGammaLin           : Int  -- 血脈継承による実効割引因子の増分効果 \Delta \Gamma_{lin}
  predatoryGain           : Int  -- 短期収奪超過利得 p_{g,t}^{pred} - p_{g,t}^*
  C_store                 : Int  -- アーカイブ維持コスト C_{store}(L)
  C_mig                   : Int  -- 管理者交代時の記録移行コスト C_{mig}(L, \alpha_{mech})
  B_adm                   : Int  -- 管理者供託金（ボンド）B_{adm}
  altAdmNext              : Int  -- 次期管理者の他層転向利得 \Pi_{m',t+1}^{alt(-adm)}
  deriving Repr

/-- 条件 ①: 公開下における利用者の有効認知・残留条件 -/
def cond1_consumer (d : DisclosureGovernanceParams) : Prop :=
  d.consEffectiveVal > d.consSigCost ∧
  d.consEffectiveVal - d.consSigCost ≥ d.consAltMax

/-- 条件 ②-a: 公開下におけるキュレーター参入維持条件 -/
def cond2a_curator_entry (d : DisclosureGovernanceParams) : Prop :=
  d.p_gt ≤ d.V_cur - d.C_raw_cur - d.R_retaliation - d.altCur

/-- 条件 ②-b: 公開下におけるキュレーター精度維持・対ゲーミング耐性条件 -/
def cond2b_curator_accuracy (d : DisclosureGovernanceParams) : Prop :=
  d.deltaDet * (d.V_H_next - d.p_renew - d.R_retaliation - d.altCurNext) >
    d.C_raw_cur + d.b_bribe

/-- 条件 ③-a（開放系）: 供託金 B_{adm} を含む現職管理者の非収奪・アーカイブ維持条件 -/
def cond3a_incumbent_no_hit_and_run (d : DisclosureGovernanceParams) : Prop :=
  d.openContinuationSurplus + d.B_adm ≥ d.predatoryGain + d.C_store

/-- 条件 ③-a（秘匿・血脈系）: 血縁割引効果 \Delta\Gamma_{lin} による非収奪・維持条件 -/
def cond3a_dynastic_no_hit_and_run (d : DisclosureGovernanceParams) : Prop :=
  d.openContinuationSurplus + d.deltaGammaLin ≥ d.predatoryGain + d.C_store

/-- 条件 ③-b: 管理者交代時の記録継承・不滅条件 (State Handover Condition) -/
def cond3b_state_handover (d : DisclosureGovernanceParams) : Prop :=
  d.V_H_next - d.C_mig - d.C_store ≥ max d.V_empty_next d.altAdmNext

/-- 公開型ガバナンスの完全安定条件（①, ②-a, ②-b, ③-a, ③-b の同時成立） -/
def FullOpenStability (d : DisclosureGovernanceParams) : Prop :=
  cond1_consumer d ∧
  cond2a_curator_entry d ∧
  cond2b_curator_accuracy d ∧
  cond3a_incumbent_no_hit_and_run d ∧
  cond3b_state_handover d

/--
  【定理 1.1】秘匿・血脈継承による Hit-and-Run 収奪の抑止:
  無担保の開放環境（B_adm = 0）で生存確率の低下により条件 ③-a が破綻する場合でも、
  管理手段の非公開（\alpha_{mech} = 0）と血縁割引（\beta_{lin} > 0）による
  将来価値増分 \Delta\Gamma_{lin} > 0 が十分大きければ、記録維持条件 ③-a が成立する。
-/
theorem dynastic_prevents_hit_and_run
    (d : DisclosureGovernanceParams)
    (_h_secret : d.alphaMech = 0)
    (_h_kin : d.betaLin > 0)
    (h_unbonded_fails : d.openContinuationSurplus < d.predatoryGain + d.C_store)
    (h_dynastic_holds : d.openContinuationSurplus + d.deltaGammaLin ≥ d.predatoryGain + d.C_store) :
    ¬ cond3a_incumbent_no_hit_and_run { d with B_adm := 0 } ∧
    cond3a_dynastic_no_hit_and_run d ∧
    d.deltaGammaLin > 0 := by
  unfold cond3a_incumbent_no_hit_and_run cond3a_dynastic_no_hit_and_run
  dsimp
  omega

/--
  【定理 1.2】状態引き継ぎ条件 (Condition ③-b) による管理者交代と記録消滅の分離:
  履歴のネットワーク効果 \Delta V(L) = V_H - V_empty が移行・維持費 C_{mig} + C_{store} 以上で、
  他層への転向利得も上回るとき、新管理者 m' は履歴 \mathcal{H} の継承を選択し、
  管理者交代が起きても評価記録は消滅しない。
-/
theorem state_handover_preserves_archive
    (d : DisclosureGovernanceParams)
    (h_store_pos : d.C_store > 0)
    (h_net_effect : d.V_H_next - d.V_empty_next ≥ d.C_mig + d.C_store)
    (h_beats_alt : d.V_H_next - d.C_mig - d.C_store ≥ d.altAdmNext) :
    cond3b_state_handover d ∧ (d.V_H_next - d.C_mig > d.V_empty_next) := by
  unfold cond3b_state_handover
  omega

/--
  【定理 1.3】公開しても評価システムが壊れないための拡張連立条件:
  非対称公開（遅延ログ・ゼロ知識検証等）による R_j, b_t の抑制、ボンド B_{adm} による
  短期収奪の抑止、および標準化による C_{mig} の低減が満たされれば、
  公開下でも全5条件 (FullOpenStability) が同時に成立する。
-/
theorem open_system_stability_with_handover
    (d : DisclosureGovernanceParams)
    (h1_benefit : d.consEffectiveVal > d.consSigCost)
    (h1_stay : d.consEffectiveVal - d.consSigCost ≥ d.consAltMax)
    (h2a_cap : d.p_gt ≤ d.V_cur - d.C_raw_cur - d.R_retaliation - d.altCur)
    (h2b_audit : d.deltaDet * (d.V_H_next - d.p_renew - d.R_retaliation - d.altCurNext) >
      d.C_raw_cur + d.b_bribe)
    (h3a_bond : d.openContinuationSurplus + d.B_adm ≥ d.predatoryGain + d.C_store)
    (h3b_network : d.V_H_next - d.V_empty_next ≥ d.C_mig + d.C_store)
    (h3b_alt : d.V_H_next - d.C_mig - d.C_store ≥ d.altAdmNext) :
    FullOpenStability d := by
  unfold FullOpenStability cond1_consumer cond2a_curator_entry cond2b_curator_accuracy
  unfold cond3a_incumbent_no_hit_and_run cond3b_state_handover
  refine ⟨⟨h1_benefit, h1_stay⟩, h2a_cap, h2b_audit, h3a_bond, ?_⟩
  omega

/-- 状態分離・検証公開型ガバナンスの検証済み数値例 -/
def sampleOpenGovernance : DisclosureGovernanceParams where
  L := 12
  alphaLog := 70
  alphaMech := 100
  betaLin := 0
  consEffectiveVal := 80
  consSigCost := 20
  consAltMax := 45
  V_cur := 120
  p_gt := 40
  C_raw_cur := 15
  R_retaliation := 10
  altCur := 30
  V_H_next := 140
  V_empty_next := 25
  p_renew := 35
  altCurNext := 25
  deltaDet := 3
  b_bribe := 20
  openContinuationSurplus := 30
  deltaGammaLin := 0
  predatoryGain := 45
  C_store := 15
  C_mig := 10
  B_adm := 35
  altAdmNext := 50

theorem sample_open_governance_stable : FullOpenStability sampleOpenGovernance := by
  unfold FullOpenStability cond1_consumer cond2a_curator_entry cond2b_curator_accuracy
  unfold cond3a_incumbent_no_hit_and_run cond3b_state_handover
  decide

-- ============================================================================
-- セクション 2: 価値観コピー（いじめ圧力 s）とテロ誘因の均衡条件
-- ============================================================================

/-- いじめ（同調制裁 s）に直面する個体 k の選択肢パラメータ -/
structure BullyingTerrorParams where
  pi_in          : Int  -- 集団基準順応時の便益 \Pi_k^{in}(\bar{\epsilon}(s))
  C_copy         : Int  -- 矯正・努力コスト C_{copy,k}(s)
  S_harm         : Int  -- 残留いじめ被害 s \cdot \epsilon_k(s)
  pi_altSys      : Int  -- 別の評価体系での利得 \max_{g' \neq g} \Pi_k^{in}(g')
  C_exit         : Int  -- 別体系への移動・離脱コスト C_{exit,k}
  pi_ruin        : Int  -- 体系崩壊後の自然状態利得 \Pi_k^{ruin}
  R_ressentiment : Int  -- 報復・道連れ効用 \Lambda_k(s, d_{k,0}) \cdot \Delta V_{destroy}(g)
  c_atk          : Int  -- テロ実行コスト・処罰リスク c_{atk,k}
  deriving Repr

/-- ① 順応（価値観コピー受容）の純利得 \Pi_k^{Copy}(s) -/
def payoffCopy (p : BullyingTerrorParams) : Int :=
  p.pi_in - p.C_copy - p.S_harm

/-- ② 平和的離脱（外部オプション）の純利得 \Pi_k^{Exit} -/
def payoffExit (p : BullyingTerrorParams) : Int :=
  p.pi_altSys - p.C_exit

/-- ③ テロ（評価体系の破壊）の純利得 \Pi_k^{Terror}(s) -/
def payoffTerror (p : BullyingTerrorParams) : Int :=
  p.pi_ruin + p.R_ressentiment - p.c_atk

/-- テロ抑止条件 (No-Terrorism Condition): \max(\Pi^{Copy}, \Pi^{Exit}) \ge \Pi^{Terror} -/
def noTerrorismCondition (p : BullyingTerrorParams) : Prop :=
  max (payoffCopy p) (payoffExit p) ≥ payoffTerror p

/--
  【定理 2.1】閉鎖空間での過剰ないじめによるテロ相転移:
  移動コストが高く離脱が塞がれた環境（\Pi^{Exit} < \Pi^{Terror}）で、
  矯正コスト・いじめ被害・報復効用の和が許容上限を超えるとき、
  一人の主体にとってテロが順応・離脱を厳密に上回る。
-/
theorem closed_system_excess_bullying_triggers_terror
    (p : BullyingTerrorParams)
    (h_closed : payoffExit p < payoffTerror p)
    (h_excess : p.C_copy + p.S_harm + p.R_ressentiment > (p.pi_in - p.pi_ruin) + p.c_atk) :
    payoffTerror p > max (payoffCopy p) (payoffExit p) := by
  unfold payoffTerror payoffCopy payoffExit at *
  omega

/--
  【定理 2.2】処方箋 ①（評価体系の多層化と移動コスト C_{exit} 低減）によるテロ消滅:
  集団基準に順応できない個体（\Pi^{Copy} < \Pi^{Terror}）に対しても、
  移動コストを C_{exit\_low} まで下げて外部オプションを確保すれば、テロは完全に抑止される。
-/
theorem multi_layered_exit_eliminates_terror
    (p : BullyingTerrorParams)
    (C_exit_low : Int)
    (_h_trapped : payoffCopy p < payoffTerror p)
    (h_low_exit : p.pi_altSys - C_exit_low ≥ payoffTerror p) :
    noTerrorismCondition { p with C_exit := C_exit_low } := by
  unfold noTerrorismCondition payoffCopy payoffExit payoffTerror at *
  dsimp
  omega

/--
  【定理 2.3】処方箋 ②〜⑤（インフラ整備・恣意的同調の排除・単一障害点排除）の効果:
  生活習慣インフラによる矯正コスト削減 (\Delta C_{infra})、恣意的同調制裁の撤廃 (\Delta S_{arb})、
  および破壊威力減衰 (\Delta R_{robust}) によってギャップを埋めれば、
  離脱不可能な閉鎖空間であっても順応がテロを上回る。
-/
theorem five_prescriptions_prevent_terror
    (p : BullyingTerrorParams)
    (deltaC_infra deltaS_arb deltaR_robust : Int)
    (_h_infra : deltaC_infra ≥ 0)
    (_h_arb : deltaS_arb ≥ 0)
    (_h_robust : deltaR_robust ≥ 0)
    (h_gap_closed : deltaC_infra + deltaS_arb + deltaR_robust ≥ payoffTerror p - payoffCopy p) :
    let p_imp : BullyingTerrorParams :=
      { p with
        C_copy := p.C_copy - deltaC_infra
        S_harm := p.S_harm - deltaS_arb
        R_ressentiment := p.R_ressentiment - deltaR_robust }
    payoffCopy p_imp ≥ payoffTerror p_imp ∧ noTerrorismCondition p_imp := by
  intro p_imp
  unfold noTerrorismCondition payoffCopy payoffTerror at *
  dsimp [p_imp] at *
  omega

-- ============================================================================
-- セクション 3: 3つのガチャ（遺伝・親・環境）・事前抹殺 vs 包摂・AI時代動学
-- ============================================================================

/-- ガチャ不適合個体 z_k > z_{th} に対する3政策（放置・援助・事前抹殺）の比較パラメータ -/
structure GachaAIPolicyParams where
  pi_terror      : Int  -- テロ選択時の利得 \Pi_k^{Terror}(s | z_k)
  pi_copy        : Int  -- 順応選択時の利得 \Pi_k^{Copy}(s | z_k)
  L_terror       : Int  -- 無援助放置時の期待テロ破壊損失 \lambda_{terror}(z_k, s) \Delta V_{destroy}
  y_homo         : Int  -- 定常的な労働・協調貢献 y_{homo}(z_k)
  B_breakthrough : Int  -- 非連続なブレイクスルー期待価値 \delta B_t^{human} q(z_k)
  C_erase        : Int  -- 事前抹殺・早期スクリーニングコスト C_{erase}(\tau)
  deriving Repr

/-- テロを抑止するために必要な最低援助額 T_{min} = \max(0, \Pi^{Terror} - \Pi^{Copy}) -/
def T_min (g : GachaAIPolicyParams) : Int :=
  max 0 (g.pi_terror - g.pi_copy)

/-- ① 無援助・放置 (Neglect) の社会効用 -/
def uNeglect (g : GachaAIPolicyParams) : Int :=
  -g.L_terror

/-- ② 援助・再分配による包摂 (Support) の社会効用 -/
def uSupport (g : GachaAIPolicyParams) : Int :=
  g.y_homo + g.B_breakthrough - T_min g

/-- ③ 事前社会的抹殺・切り捨て (Preemptive Erasure) の社会効用 -/
def uErase (g : GachaAIPolicyParams) : Int :=
  -g.C_erase

/--
  【定理 3.1】ブレイクスルー価値が高い場合の包摂優位:
  定常貢献とブレイクスルー期待価値の和が純節約コスト (T_{min} - C_{erase}) を上回るとき、
  社会は事前抹殺ではなく援助による包摂を選択する。
-/
theorem support_dominates_erasures_when_breakthrough_high
    (g : GachaAIPolicyParams)
    (h_bt : T_min g - g.C_erase < g.y_homo + g.B_breakthrough) :
    uSupport g > uErase g := by
  unfold uSupport uErase
  omega

/--
  【定理 3.2】AI時代における近視眼的「早期遺伝子・親スクリーニング」への誘惑:
  AIにより人間の定常貢献 (y_{homo} \le 0) とブレイクスルー希少価値 (B_{breakthrough} = 0) が消失し、
  出生前・親審査コスト C_{erase} が誕生後の援助コスト T_{min} を下回るとき、
  近視眼的な効率性基準では事前切り捨てが援助を上回る。
-/
theorem myopic_ai_culling_temptation
    (g : GachaAIPolicyParams)
    (h_yhomo : g.y_homo ≤ 0)
    (h_bt_zero : g.B_breakthrough = 0)
    (h_cheap_screen : g.C_erase < T_min g) :
    uErase g > uSupport g := by
  unfold uErase uSupport
  omega

/-- スクリーニング基準のインフレによる中間・準エリート層の予防的テロパラメータ -/
structure IncumbentCullingRisk where
  pi_stay_safe         : Int  -- 切り捨てられず残留できた場合の利得
  L_cull_loss          : Int  -- 来期以降に自分が不適格判定され排除される期待損失
  pi_preemptive_terror : Int  -- 排除前にAI管理機構・評価系を破壊する予防的テロの利得
  deriving Repr

/-- 残留時の期待利得 -/
def expectedStayPayoff (r : IncumbentCullingRisk) : Int :=
  r.pi_stay_safe - r.L_cull_loss

/--
  【定理 3.3】切り捨て基準の動的インフレ (p_{min}(t+1) > p_{min}(t)) による予防的テロの発火:
  下位切り捨てに伴い要求基準がインフレして現存の中間層に排除確率が生じ、
  期待排除損失の増加 \Delta_{inflation} が防衛閾値を超えると、
  資源・能力を持つ中間層自身が予防的テロ（反乱）へ転化する。
-/
theorem culling_inflation_triggers_preemptive_elite_terror
    (r : IncumbentCullingRisk)
    (delta_inflation : Int)
    (_h_stable_before : r.pi_preemptive_terror ≤ expectedStayPayoff r)
    (h_inflation_exceeds : delta_inflation > expectedStayPayoff r - r.pi_preemptive_terror) :
    let r_inflated : IncumbentCullingRisk := { r with L_cull_loss := r.L_cull_loss + delta_inflation }
    r_inflated.pi_preemptive_terror > expectedStayPayoff r_inflated := by
  intro r_inflated
  unfold expectedStayPayoff at *
  dsimp [r_inflated] at *
  omega

/-- 環境の非定常ショックとAI包摂戦略を比較する長期期待厚生パラメータ -/
structure AILongRunParams where
  y_homo             : Int  -- 定常貢献
  B_breakthrough     : Int  -- 人間ブレイクスルー価値
  V_diversityOption  : Int  -- 多様性分散 Var(\omega_t) 維持による適応オプション価値
  T_min_AI           : Int  -- AIによる養育バフ・個別空間生成後の最低包摂コスト
  C_erase            : Int  -- スクリーニングコスト
  L_varCollapse      : Int  -- 多様性消滅による非定常ショック (\Delta \theta^* \gg 0) 時の崩壊損失
  L_preemptiveTerror : Int  -- 基準インフレに伴う中間層の予防的テロ損失
  deriving Repr

/-- 長期期待社会価値: AIによる包摂・多様性保全戦略 -/
def welfareAIInclude (a : AILongRunParams) : Int :=
  a.y_homo + a.B_breakthrough + a.V_diversityOption - a.T_min_AI

/-- 長期期待社会価値: AIによる早期スクリーニング・均質化戦略 -/
def welfareAICull (a : AILongRunParams) : Int :=
  -a.C_erase - a.L_varCollapse - a.L_preemptiveTerror

/--
  【定理 3.4】非定常環境ショック下における「AI包摂戦略」の厳密優位性:
  AIを人間の選別・切り捨てに使うと、予防的テロと多様性分散消滅（Var(\omega_t) \to 0）による
  ショック崩壊損失 L_{varCollapse} > 0 が発生する。
  一方、AIを養育バフ・個別環境生成に使って T_{min}^{AI} を多様性＋革新価値以下に抑え込めば、
  長期社会価値は AI包摂戦略が厳密に上回る。
-/
theorem ai_inclusion_dominates_culling_under_shocks
    (a : AILongRunParams)
    (h_homo : a.y_homo ≥ 0)
    (h_erase : a.C_erase ≥ 0)
    (h_shock_collapse : a.L_varCollapse > 0)
    (h_rebel : a.L_preemptiveTerror ≥ 0)
    (h_ai_bound : a.T_min_AI ≤ a.V_diversityOption + a.B_breakthrough) :
    welfareAIInclude a > welfareAICull a := by
  unfold welfareAIInclude welfareAICull
  omega

-- ============================================================================
-- セクション 4: 3つの評価移転チャネル (w_g, w_p, w_e) と3大性能 (A, S, U)
-- ============================================================================

/-- 評価移転チャネルに基づく社会体制の性能・コスト指標 -/
structure TransferChannelRegime where
  A_accuracy             : Int  -- ① 評価の正しさ A
  S_coverage             : Int  -- ② 評価の範囲の広さ S
  U_updatability         : Int  -- ③ 評価の更新性 U
  V_sys                  : Int  -- 3大性能が生むマクロ協調余剰 V_{sys}(A, S, U)
  C_inst                 : Int  -- いじめ苦痛・公開・塀の維持コスト C_{inst}
  L_conflict             : Int  -- テロおよび土地収奪紛争の期待損失
  s_bullying             : Int  -- 社会的に正当化されるいじめ・同調圧力 s^*
  alpha_tag              : Int  -- 評価タグ公開度 \alpha_{tag}^*
  kin_or_wall_deterrence : Int  -- 血縁連座制 \Omega_{kin} または物理的塀 b_\ell の抑止力
  next_gen_hope          : Int  -- 1世代待ちの階級上昇希望 \eta_p
  deriving Repr

/-- 評価体制の総合マクロ純厚生 -/
def regimeWelfare (r : TransferChannelRegime) : Int :=
  r.V_sys - r.C_inst - r.L_conflict

/--
  【定理 4.1】強制的正しさ（血統・塀社会） vs 観測的正しさ（親ガチャ・希望社会）:
  血縁連座制や高い塀によりテロ被害が抑え込まれる体制では、いじめ s^* を強めて正しさ A を
  確保することが合理的になり得る一方、連座や塀がない親ガチャ社会では強い同調圧力が
  テロ損失を爆発させるため、低いじめ＋1世代上昇希望 (\eta_p > 0)＋タグ公開が合理的となる。
-/
theorem coercive_vs_observational_accuracy
    (r_coercive_low_s r_coercive_high_s : TransferChannelRegime)
    (r_parental_low_s r_parental_high_s : TransferChannelRegime)
    (_h_coercive_s : r_coercive_high_s.s_bullying > r_coercive_low_s.s_bullying)
    (_h_deterred : r_coercive_high_s.kin_or_wall_deterrence > 0)
    (h_coercive_net :
      r_coercive_high_s.V_sys - r_coercive_low_s.V_sys >
        (r_coercive_high_s.C_inst - r_coercive_low_s.C_inst) +
        (r_coercive_high_s.L_conflict - r_coercive_low_s.L_conflict))
    (_h_parental_hope : r_parental_low_s.next_gen_hope > 0)
    (_h_no_wall : r_parental_low_s.kin_or_wall_deterrence = 0)
    (_h_parental_s : r_parental_high_s.s_bullying > r_parental_low_s.s_bullying)
    (h_parental_terror_blowup :
      r_parental_high_s.L_conflict - r_parental_low_s.L_conflict >
        (r_parental_high_s.V_sys - r_parental_low_s.V_sys) -
        (r_parental_high_s.C_inst - r_parental_low_s.C_inst)) :
    regimeWelfare r_coercive_high_s > regimeWelfare r_coercive_low_s ∧
    regimeWelfare r_parental_low_s > regimeWelfare r_parental_high_s := by
  unfold regimeWelfare
  omega

/--
  【定理 4.2】分離定理に基づくハイブリッド評価設計の優位性:
  最低限の衛生ルールを環境基準で担保しつつ、範囲 S と更新性 U を親の努力反映と
  新空間開拓（集団移転）で確保するハイブリッド体制は、単一チャネル体制を厳密に凌駕する。
-/
theorem hybrid_channel_separation_dominates
    (hybrid single : TransferChannelRegime)
    (h_scale_update : hybrid.V_sys > single.V_sys)
    (h_cost : hybrid.C_inst ≤ single.C_inst)
    (h_conflict : hybrid.L_conflict ≤ single.L_conflict) :
    regimeWelfare hybrid > regimeWelfare single := by
  unfold regimeWelfare
  omega

-- ============================================================================
-- セクション 5: 土地収奪 → 新天地開拓 → 枯渇相転移と評価軸の多次元開拓
-- ============================================================================

/-- ① 既存の土地の奪い合い（定住・収奪モード: Pred）の利得 -/
def payoffPred (V_share C_war C_wall : Int) : Int :=
  V_share - C_war - C_wall

/-- ② 新天地への集団移転・開拓（フロンティア拡大モード: Front）の利得 -/
def payoffFront (V_0 P_pioneer C_mig : Int) : Int :=
  V_0 + P_pioneer - C_mig

/-- ③ 評価軸の多層化・仮想開拓（内包的フロンティアモード: Int）の利得 -/
def payoffInt (V_niche C_coord : Int) : Int :=
  V_niche - C_coord

/-- 式 ②-a より決まる管理者が奪取可能な権限価格の上限 p_{max}(F_t) -/
def admMaxPrice (V_gt C_raw_j alt_cur : Int) : Int :=
  V_gt - C_raw_j - alt_cur

/-- 式 ②-b（キュレーター精度維持・不正抑止条件） -/
def cond2b_curator (deltaP V_next p_renew alt_cur C_raw_j b_bribe : Int) : Prop :=
  deltaP * (V_next - p_renew - alt_cur) > C_raw_j + b_bribe

/--
  【定理 5.1】第1の切り替わり（土地の奪い合い → 新天地への集団移転・開拓）:
  文書化によって集団移転コスト C_{mig} が下がり、既存地の混雑によって闘争・塀コスト
  C_{war} + C_{wall} が上昇するとき、集団移転・開拓モードが土地収奪モードを上回る。
-/
theorem phase_transition_predation_to_frontier
    (V_share C_war C_wall V_0 P_pioneer C_mig : Int)
    (h_trans : P_pioneer + C_war + C_wall ≥ C_mig + (V_share - V_0)) :
    payoffFront V_0 P_pioneer C_mig ≥ payoffPred V_share C_war C_wall := by
  unfold payoffFront payoffPred
  omega

/--
  【定理 5.2】新天地枯渇 (F_t → 0) による評価管理者 (adm) のレントシーキング化:
  フロンティアが消滅してキュレーターの外部オプション \Pi^{alt(-cur)} が低下すると
  （alt_low < alt_high）、管理者が請求できる権限価格の上限 p_{max} が厳密に上昇する。
-/
theorem frontier_exhaustion_causes_adm_rent_seeking
    (V_gt C_raw_j alt_high alt_low : Int)
    (h_exit_drops : alt_low < alt_high) :
    admMaxPrice V_gt C_raw_j alt_low > admMaxPrice V_gt C_raw_j alt_high := by
  unfold admMaxPrice
  omega

/--
  【定理 5.3】新天地枯渇 (F_t → 0) によるキュレーター (cur) の腐敗と減点主義への変質:
  フロンティアが存在した期 (F_{high}) には式 ②-b が成立していたにもかかわらず、
  新天地枯渇によって管理者が更新料を吊り上げ（p_{renew\_low} - p_{renew\_high} \ge alt_{high} - alt_{low}）、
  かつ逃げ場を失った被評価者からの買収圧力 b_{low} が急騰すると、
  式 ②-b の不等号が逆転し、客観審査の放棄・縁故腐敗が発生する。
-/
theorem frontier_exhaustion_corrupts_curators
    (deltaP V_next p_renew_high p_renew_low alt_high alt_low C_raw_j b_high b_low : Int)
    (h_deltaP_pos : deltaP > 0)
    (_h_alt_drops : alt_low < alt_high)
    (_h_renew_hike : p_renew_low > p_renew_high)
    (h_rent_squeeze : p_renew_low - p_renew_high ≥ alt_high - alt_low)
    (_h_bribe_surge : b_low > b_high)
    (h_high_ok : cond2b_curator deltaP V_next p_renew_high alt_high C_raw_j b_high)
    (h_bribe_breaks : C_raw_j + b_low ≥ deltaP * (V_next - p_renew_high - alt_high)) :
    cond2b_curator deltaP V_next p_renew_high alt_high C_raw_j b_high ∧
    ¬ cond2b_curator deltaP V_next p_renew_low alt_low C_raw_j b_low := by
  refine ⟨h_high_ok, ?_⟩
  unfold cond2b_curator
  have h_margin_le : V_next - p_renew_low - alt_low ≤ V_next - p_renew_high - alt_high := by
    omega
  have h_delta_nonneg : 0 ≤ deltaP := by omega
  have h_mul_le :
      deltaP * (V_next - p_renew_low - alt_low) ≤
      deltaP * (V_next - p_renew_high - alt_high) :=
    Int.mul_le_mul_of_nonneg_left h_margin_le h_delta_nonneg
  omega

/--
  【定理 5.4】新天地枯渇後の崩壊を防ぐ「評価空間の多次元開拓」条件（経路Bへの軟着陸）:
  物理的フロンティアの喪失による外部オプション低下 L_{physExhaust} を、
  新しい直交評価空間の創出による利得 gainFromNewEvalSpaces で補填できれば、
  (1) 外部オプション \Pi^{Exit} が維持され、
  (2) 管理者による権限価格の暴騰が抑止され、
  (3) 競争圧力による更新料抑制を通じてキュレーターの条件 ②-b が保たれ、
  (4) 社会全体が再収奪 (Pred) ではなく内包的フロンティア (Int) を選択する。
-/
theorem evaluation_frontier_expansion_prevents_collapse
    (alt_0 L_physExhaust gainFromNewEvalSpaces V_gt C_raw_j : Int)
    (deltaP V_next p_renew_0 p_renew_int b_0 b_int : Int)
    (V_niche C_coord V_share C_war C_wall : Int)
    (h_deltaP_pos : deltaP > 0)
    (_h_exhaust_nonneg : L_physExhaust ≥ 0)
    (h_eval_compensates : gainFromNewEvalSpaces ≥ L_physExhaust)
    (h_adm_comp_caps_renew :
      p_renew_int + (alt_0 - L_physExhaust + gainFromNewEvalSpaces) ≤ p_renew_0 + alt_0)
    (h_bribe_contained : b_int ≤ b_0)
    (h_high_ok : cond2b_curator deltaP V_next p_renew_0 alt_0 C_raw_j b_0)
    (h_int_beats_pred : V_niche - C_coord ≥ V_share - C_war - C_wall) :
    let alt_preserved := alt_0 - L_physExhaust + gainFromNewEvalSpaces
    alt_preserved ≥ alt_0 ∧
    admMaxPrice V_gt C_raw_j alt_preserved ≤ admMaxPrice V_gt C_raw_j alt_0 ∧
    cond2b_curator deltaP V_next p_renew_int alt_preserved C_raw_j b_int ∧
    payoffInt V_niche C_coord ≥ payoffPred V_share C_war C_wall := by
  intro alt_preserved
  have h_alt : alt_preserved ≥ alt_0 := by
    dsimp [alt_preserved]
    omega
  have h_price : admMaxPrice V_gt C_raw_j alt_preserved ≤ admMaxPrice V_gt C_raw_j alt_0 := by
    unfold admMaxPrice
    omega
  have h_cond2b : cond2b_curator deltaP V_next p_renew_int alt_preserved C_raw_j b_int := by
    unfold cond2b_curator at *
    have h_margin_ge : V_next - p_renew_0 - alt_0 ≤ V_next - p_renew_int - alt_preserved := by
      dsimp [alt_preserved]
      omega
    have h_delta_nonneg : 0 ≤ deltaP := by omega
    have h_mul_le :
        deltaP * (V_next - p_renew_0 - alt_0) ≤
        deltaP * (V_next - p_renew_int - alt_preserved) :=
      Int.mul_le_mul_of_nonneg_left h_margin_ge h_delta_nonneg
    omega
  have h_route_b : payoffInt V_niche C_coord ≥ payoffPred V_share C_war C_wall := by
    unfold payoffInt payoffPred
    omega
  exact ⟨h_alt, h_price, h_cond2b, h_route_b⟩

-- ============================================================================
-- セクション 6: 制度進化の段階的解禁と認知限界・物語圧縮・アルゴリズム統治モデル
-- ============================================================================

/-- 主体の認知・推論・時間選好の限界を表すパラメータ -/
structure CognitiveCapacityParams where
  baseVal          : Int  -- |S_t^{base}| c_{raw,i}
  inferenceLoss    : Int  -- \mathcal{O}(\rho_{i,t}(g)) |S_t^{base}| c_{raw,i}（ボトルネック①）
  sigCost          : Int  -- M_{\mathcal{G}_i} c_{sig}（記号読解コスト）
  deltaDiscount    : Int  -- \delta \cdot \Delta P(\omega_{g,t+1})（ボトルネック②：時間割引・確実性）
  futureCurSurplus : Int  -- V_{g,t+1}(\rho_t^*) - p_{g,t+1}^{renew} - \Pi_{j,t+1}^{alt(-cur)}
  curRawCost       : Int  -- |S'_{j,t}| c_{raw,j}
  b_bribe          : Int  -- 買収工作コスト b_t
  deriving Repr

/-- 利用者の有効認知純利得 \Delta C_i(g) -/
def deltaC (c : CognitiveCapacityParams) : Int :=
  (c.baseVal - c.inferenceLoss) - c.sigCost

/-- 認知限界下における条件 ①（利用者の有効認知条件 \Delta C_i > 0） -/
def cogCond1 (c : CognitiveCapacityParams) : Prop :=
  deltaC c > 0

/-- 認知限界下における条件 ②-b（将来利得に基づく不正抑止条件） -/
def cogCond2b (c : CognitiveCapacityParams) : Prop :=
  c.deltaDiscount * c.futureCurSurplus > c.curRawCost + c.b_bribe

/--
  【定理 6.1】サル（原始段階）の認知ボトルネックによる高度制度の不成立:
  シグナル推論損失 \mathcal{O}(\rho) が過大で、かつ近視眼的時間割引（\delta = 0）のもとでは、
  条件 ① と条件 ②-b が同時に破綻し、いきなり高度な法・金融・メタ制度へ移行できない。
-/
theorem primate_cognitive_bottleneck_blocks_advanced_institutions
    (c : CognitiveCapacityParams)
    (h_inf_excess : c.inferenceLoss ≥ c.baseVal - c.sigCost)
    (h_myopic : c.deltaDiscount = 0)
    (h_cost_nonneg : c.curRawCost + c.b_bribe ≥ 0) :
    ¬ cogCond1 c ∧ ¬ cogCond2b c := by
  unfold cogCond1 deltaC cogCond2b
  rw [h_myopic, Int.zero_mul]
  omega

/--
  【定理 6.2】物語による共通事前確率圧縮と文字・法律による記号コスト削減:
  物語・神話による推論損失の一括圧縮 (\Delta O_{narrative}) と、
  文字・成文法による記号コスト削減 (\Delta c_{sig\_law}) が組み合わさることで、
  初めて条件 ① (\Delta C > 0) が解禁される。物語の圧縮を欠いたままでは条件 ① は成立しない。
-/
theorem narrative_and_law_unlock_cognition
    (c : CognitiveCapacityParams)
    (deltaO_narrative deltaCsig_law : Int)
    (_h_prim_fail : ¬ cogCond1 c)
    (_h_narr_nonneg : deltaO_narrative ≥ 0)
    (_h_law_nonneg : deltaCsig_law ≥ 0)
    (h_combined_unlocks : deltaO_narrative + deltaCsig_law > c.inferenceLoss + c.sigCost - c.baseVal)
    (h_law_alone_insufficient : deltaCsig_law ≤ c.inferenceLoss + c.sigCost - c.baseVal) :
    let c_unlocked : CognitiveCapacityParams :=
      { c with
        inferenceLoss := c.inferenceLoss - deltaO_narrative
        sigCost := c.sigCost - deltaCsig_law }
    let c_law_only : CognitiveCapacityParams :=
      { c with sigCost := c.sigCost - deltaCsig_law }
    cogCond1 c_unlocked ∧ ¬ cogCond1 c_law_only := by
  intro c_unlocked c_law_only
  unfold cogCond1 deltaC at *
  dsimp [c_unlocked, c_law_only]
  omega

/-- 段階移行における総余剰と認知・インフラコストの比較パラメータ -/
structure StageTransitionParams where
  V_simple          : Int  -- 現在の単純段階が生む余剰
  C_simple          : Int  -- 現在の単純段階の認知・維持コスト
  V_advanced        : Int  -- 高度段階の潜在総余剰 (V_advanced > V_simple)
  C_advanced_raw    : Int  -- 認知・外部記憶進化前の高度段階の生コスト
  cogCapabilityGain : Int  -- 認知能力・外部記憶・計算インフラ進化によるコスト削減幅
  deriving Repr

/-- 制度段階の純余剰 -/
def netStageSurplus (V C : Int) : Int := V - C

/--
  【定理 6.3】制度の段階的進化定理（一足飛びの不能性と能力獲得後の逆転）:
  認知・外部記憶能力の獲得前は高度制度の生コストが過大で単純段階に劣るため移行できず、
  段階的に能力を獲得してコスト削減幅が臨界を超えた後に初めて高度段階が優位となる。
-/
theorem stepwise_institutional_evolution
    (s : StageTransitionParams)
    (_h_adv_potential : s.V_advanced > s.V_simple)
    (h_premature_costly : s.C_advanced_raw - s.C_simple > s.V_advanced - s.V_simple)
    (h_capability_evolved :
      s.cogCapabilityGain > (s.C_advanced_raw - s.C_simple) - (s.V_advanced - s.V_simple)) :
    netStageSurplus s.V_advanced s.C_advanced_raw < netStageSurplus s.V_simple s.C_simple ∧
    netStageSurplus s.V_advanced (s.C_advanced_raw - s.cogCapabilityGain) >
      netStageSurplus s.V_simple s.C_simple := by
  unfold netStageSurplus
  omega

def maxInstitutionalPayoff (rp : RolePayoffs) : Int :=
  max rp.cons (max rp.cur rp.adm)

def applyCognitiveLoad (rp : RolePayoffs) (cogPenalty : Int) : RolePayoffs :=
  { cons := rp.cons - cogPenalty
    cur := rp.cur - cogPenalty
    adm := rp.adm - cogPenalty }


theorem cognitive_overload_triggers_regression_to_violence
    (rp : RolePayoffs)
    (cogPenalty payoffViolence : Int)
    (h_overload : cogPenalty > maxInstitutionalPayoff rp - payoffViolence) :
    let rp_loaded := applyCognitiveLoad rp cogPenalty
    payoffViolence > rp_loaded.cons ∧
    payoffViolence > rp_loaded.cur ∧
    payoffViolence > rp_loaded.adm ∧
    payoffViolence > maxInstitutionalPayoff rp_loaded := by
  intro rp_loaded
  dsimp [rp_loaded, maxInstitutionalPayoff, applyCognitiveLoad] at *
  omega

/-- 第8段階（アルゴリズム自律調停＋パーソナライズドガバナンス）による負荷軽減・摩擦低減後の利得 -/
def applyAlgorithmicRecovery
    (rp : RolePayoffs) (cogPenalty deltaCog_personal deltaFee_algo : Int) : RolePayoffs :=
  let rp_loaded := applyCognitiveLoad rp cogPenalty
  { cons := rp_loaded.cons + deltaCog_personal + deltaFee_algo
    cur  := rp_loaded.cur + deltaCog_personal + deltaFee_algo
    adm  := rp_loaded.adm + deltaCog_personal + deltaFee_algo }

theorem algorithmic_governance_dominates_and_eliminates_betrayal
    (d : DisclosureGovernanceParams)
    (rp : RolePayoffs)
    (cogPenalty payoffViolence deltaCog_personal deltaFee_algo : Int)
    (h_algo_surplus : d.openContinuationSurplus ≥ d.C_store)
    (_h_personal_pos : deltaCog_personal > 0)
    (_h_fee_nonneg : deltaFee_algo ≥ 0)
    (h_recovery_sufficient :
      deltaCog_personal + deltaFee_algo ≥
        payoffViolence - maxInstitutionalPayoff (applyCognitiveLoad rp cogPenalty)) :
    let d_algo : DisclosureGovernanceParams :=
      { d with alphaMech := 100, B_adm := 0, predatoryGain := 0 }
    let rp_stage8 := applyAlgorithmicRecovery rp cogPenalty deltaCog_personal deltaFee_algo
    cond3a_incumbent_no_hit_and_run d_algo ∧
    maxInstitutionalPayoff rp_stage8 ≥ payoffViolence := by
  intro d_algo rp_stage8
  dsimp [d_algo, rp_stage8, cond3a_incumbent_no_hit_and_run, applyAlgorithmicRecovery,
    maxInstitutionalPayoff, applyCognitiveLoad] at *
  omega

-- ============================================================================
-- セクション 2〜6 の数値検証インスタンス
-- ============================================================================

def sampleBullyingClosed : BullyingTerrorParams where
  pi_in := 60
  C_copy := 45
  S_harm := 35
  pi_altSys := 50
  C_exit := 80
  pi_ruin := 10
  R_ressentiment := 40
  c_atk := 15

def sampleGachaAI : GachaAIPolicyParams where
  pi_terror := 35
  pi_copy := -10
  L_terror := 200
  y_homo := 0
  B_breakthrough := 0
  C_erase := 5

def sampleAILongRun : AILongRunParams where
  y_homo := 5
  B_breakthrough := 10
  V_diversityOption := 40
  T_min_AI := 8
  C_erase := 5
  L_varCollapse := 150
  L_preemptiveTerror := 80

def samplePrimateCognitive : CognitiveCapacityParams where
  baseVal := 50
  inferenceLoss := 45
  sigCost := 25
  deltaDiscount := 0
  futureCurSurplus := 100
  curRawCost := 15
  b_bribe := 10

def sampleStageTransition : StageTransitionParams where
  V_simple := 40
  C_simple := 10
  V_advanced := 120
  C_advanced_raw := 100
  cogCapabilityGain := 65

def sampleStage8RolePayoffs : RolePayoffs where
  cons := 45
  cur := 50
  adm := 40
-- ============================================================================
-- セクション 7: 評価保存能力・情報劣化率による動的ガバナンス相転移と資本主義超克定理
-- ============================================================================

/-- 高度ガバナンス進化パラメータ（アーカイブ長・劣化率・検証可能性・包摂性） -/
structure AdvancedGovernanceParams where
  L                  : Nat  -- アーカイブ長 L
  degRate            : Int  -- 情報劣化率 \lambda_{deg}(L) \in [0, 100]
  verifiability      : Int  -- 暗号学的検証可能性 \nu \in [0, 100]
  inclusivity        : Int  -- 包摂的透明性 \alpha_{trans} \in [0, 100]
  capitalistRent     : Int  -- 資本主義的評価・市場独占による歪みコスト（レント搾取）
  algorithmicSurplus : Int  -- アルゴリズム統治による摩擦軽減と公正な分配余剰
  -- パラメータの定義域不変条件（0〜100スケールおよび非負制約）
  h_bounds :
    (0 ≤ degRate ∧ degRate ≤ 100) ∧
    (0 ≤ verifiability ∧ verifiability ≤ 100) ∧
    (0 ≤ inclusivity ∧ inclusivity ≤ 100) ∧
    capitalistRent ≥ 0 ∧ algorithmicSurplus ≥ 0
  deriving Repr

-- ----------------------------------------------------------------------------
-- 各ガバナンス形態の独立成立条件述語（固定ステージを排した不等式条件）
-- ----------------------------------------------------------------------------

/-- ① 物理・暴力支配の成立述語: 外部記録 L=0 でも常に成立する基底状態 -/
def isViolenceFeasible (_p : AdvancedGovernanceParams) : Prop := True

/-- ② 理念・物語（口伝）統治の成立述語: 記憶の反復 L > 0 を要するが、高い劣化率 (≤ 60) を許容 -/
def isNarrativeFeasible (p : AdvancedGovernanceParams) : Prop :=
  p.L > 0 ∧ p.degRate ≤ 60

/-- ③ 規範・成文法（法治国家）統治の成立述語: 成文アーカイブ L ≥ 10 と一定の低劣化 (degRate ≤ 30) を要求 -/
def isRuleOfLawFeasible (p : AdvancedGovernanceParams) : Prop :=
  p.L ≥ 10 ∧ p.degRate ≤ 30

/-- ④ 評価・市場投票（資本主義）統治の成立述語: 信用履歴 L ≥ 50 と低劣化 (degRate ≤ 15) を要求 -/
def isMarketFeasible (p : AdvancedGovernanceParams) : Prop :=
  p.L ≥ 50 ∧ p.degRate ≤ 15

/-- ⑤ 自律調停・暗号学的検証可能アルゴリズム統治の成立述語:
    長期不変ログ L ≥ 100, 超低劣化 degRate ≤ 5, 高検証性 ν ≥ 80, 高包摂性 α_trans ≥ 80 を要求 -/
def isAlgorithmicGovernanceFeasible (p : AdvancedGovernanceParams) : Prop :=
  p.L ≥ 100 ∧ p.degRate ≤ 5 ∧ p.verifiability ≥ 80 ∧ p.inclusivity ≥ 80

-- ----------------------------------------------------------------------------
-- パラメータの関数として表現された各ガバナンス形態の社会純厚生関数
-- ----------------------------------------------------------------------------

/-- 暴力・物理支配の社会純厚生（基礎秩序値） -/
def welfareViolence (_p : AdvancedGovernanceParams) : Int := 20

/-- 口伝・物語統治の社会純厚生（共有神話による協調 45 から情報風化損失を控除） -/
def welfareNarrative (p : AdvancedGovernanceParams) : Int :=
  45 - p.degRate / 2

/-- 成文法・法治統治の社会純厚生（法秩序による協調余剰 65 から条文形骸化損失を控除） -/
def welfareRuleOfLaw (p : AdvancedGovernanceParams) : Int :=
  65 - p.degRate

/-- 資本主義・市場評価統治の社会純厚生（市場余剰 100 から独占レント搾取と劣化損失を控除） -/
def welfareMarket (p : AdvancedGovernanceParams) : Int :=
  100 - p.capitalistRent - p.degRate

/-- アルゴリズム統治の社会純厚生（分配余剰＋検証性・包摂性信頼ボーナスから不整合ペナルティを控除） -/
def welfareAlgorithmic (p : AdvancedGovernanceParams) : Int :=
  100 + p.algorithmicSurplus + (p.verifiability + p.inclusivity) / 2 - 2 * p.degRate

-- 後方互換性エイリアス
def netPayoffCapitalism (p : AdvancedGovernanceParams) : Int := welfareMarket p
def netPayoffAlgorithmic (p : AdvancedGovernanceParams) : Int := welfareAlgorithmic p

-- ----------------------------------------------------------------------------
-- 連続的パラメータ変動による動的相転移定理群
-- ----------------------------------------------------------------------------

/--
  【定理 7.1】情報劣化率 \lambda_{deg} の連続的上昇による段階的崩壊・原始退行の連鎖定理:
  アーカイブ長 L が十分であっても、情報劣化率 degRate が 30 を超えると、
  成文法・法治（Rule of Law）、市場・資本主義（Market）、アルゴリズム統治（Algorithmic）は
  すべて実現不可能となる。
-/
theorem degradation_cascade_collapse
    (p : AdvancedGovernanceParams)
    (h_deg : p.degRate > 30) :
    ¬ isRuleOfLawFeasible p ∧
    ¬ isMarketFeasible p ∧
    ¬ isAlgorithmicGovernanceFeasible p := by
  unfold isRuleOfLawFeasible isMarketFeasible isAlgorithmicGovernanceFeasible
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, h⟩; omega
  · rintro ⟨_, h⟩; omega
  · rintro ⟨_, h, _, _⟩; omega

/--
  【定理 7.2】極限劣化（degRate > 60）における完全な暴力支配への退行定理:
  情報劣化率が口伝の許容限界（60）すら突破すると、物語統治すら崩壊し、
  一切の記録や制度に依存しない暴力均衡のみが成立可能な状態となる。
-/
theorem extreme_degradation_regresses_to_violence_only
    (p : AdvancedGovernanceParams)
    (h_extreme : p.degRate > 60) :
    ¬ isNarrativeFeasible p ∧
    ¬ isRuleOfLawFeasible p ∧
    ¬ isMarketFeasible p ∧
    ¬ isAlgorithmicGovernanceFeasible p ∧
    isViolenceFeasible p := by
  unfold isNarrativeFeasible isRuleOfLawFeasible isMarketFeasible isAlgorithmicGovernanceFeasible isViolenceFeasible
  refine ⟨?_, ?_, ?_, ?_, trivial⟩
  · rintro ⟨_, h⟩; omega
  · rintro ⟨_, h⟩; omega
  · rintro ⟨_, h⟩; omega
  · rintro ⟨_, h, _, _⟩; omega

/--
  【定理 7.3】アーカイブ長 L の伸長に伴う動的ガバナンス様式の連続解禁定理:
  情報劣化が低く検証性が担保された環境下で、記録蓄積量 L が閾値（10, 50, 100）を突破するごとに
  法治、市場、アルゴリズム統治が自発的に解禁されていく動的相転移のプロセス。
-/
theorem archive_growth_enables_higher_governance
    (p : AdvancedGovernanceParams)
    (h_low_deg : p.degRate ≤ 5)
    (h_high_verif : p.verifiability ≥ 80)
    (h_high_incl : p.inclusivity ≥ 80) :
    (p.L < 10 → ¬ isRuleOfLawFeasible p ∧ ¬ isMarketFeasible p ∧ ¬ isAlgorithmicGovernanceFeasible p) ∧
    (p.L ≥ 10 → isRuleOfLawFeasible p) ∧
    (p.L ≥ 50 → isMarketFeasible p) ∧
    (p.L ≥ 100 → isAlgorithmicGovernanceFeasible p) := by
  unfold isRuleOfLawFeasible isMarketFeasible isAlgorithmicGovernanceFeasible
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hL
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨h, _⟩; omega
    · rintro ⟨h, _⟩; omega
    · rintro ⟨h, _, _, _⟩; omega
  · intro hL; exact ⟨hL, by omega⟩
  · intro hL; exact ⟨hL, by omega⟩
  · intro hL; exact ⟨hL, h_low_deg, h_high_verif, h_high_incl⟩

/--
  【定理 7.4】検証可能アルゴリズム統治による資本主義的評価（市場）の厳密超克定理:
  暗号学的検証可能性 \nu と包摂的透明性 \alpha_{trans} が十分に高く（\nu ≥ 80, \alpha_{trans} ≥ 80）、
  低劣化（degRate ≤ 5）ならば、アルゴリズム統治の社会純厚生は資本主義的評価を厳密に凌駕する。
-/
theorem algorithmic_governance_surpasses_capitalism
    (p : AdvancedGovernanceParams)
    (h_verif_high : p.verifiability ≥ 80)
    (h_incl_high  : p.inclusivity ≥ 80)
    (h_low_deg    : p.degRate ≤ 5) :
    welfareAlgorithmic p > welfareMarket p := by
  unfold welfareAlgorithmic welfareMarket
  have ⟨⟨h_deg_nonneg, _⟩, _, _, h_rent_nonneg, h_surplus_nonneg⟩ := p.h_bounds
  omega

/--
  【定理 7.5】資本主義のレント搾取ゼロ（完全競争極限）であってもなお成立する優位性:
  仮に資本主義的評価がレント搾取を完全に排除した理想状態（capitalistRent = 0）であっても、
  信頼ボーナスと協調分配余剰によりアルゴリズム統治は依然として市場評価を厳密に凌駕する。
-/
theorem algorithmic_surpasses_even_ideal_zero_rent_capitalism
    (p : AdvancedGovernanceParams)
    (_h_zero_rent : p.capitalistRent = 0)
    (h_trust_sum  : p.verifiability + p.inclusivity ≥ 20)
    (h_low_deg    : p.degRate ≤ 5) :
    welfareAlgorithmic p > welfareMarket p := by
  unfold welfareAlgorithmic welfareMarket
  have ⟨_, _, _, _, h_surplus_nonneg⟩ := p.h_bounds
  omega

/--
  【定理 7.6】全ガバナンス体制に対するアルゴリズム統治の最適性（Max Welfare）定理:
  保存能力と検証性が整った環境において、アルゴリズム統治は市場・法治・物語・暴力の
  すべてのガバナンス形態の社会純厚生を同時にかつ厳密に凌駕する。
-/
theorem algorithmic_surpasses_all_modes
    (p : AdvancedGovernanceParams)
    (h_verif_high : p.verifiability ≥ 80)
    (h_incl_high  : p.inclusivity ≥ 80)
    (h_low_deg    : p.degRate ≤ 5) :
    welfareAlgorithmic p > welfareMarket p ∧
    welfareAlgorithmic p > welfareRuleOfLaw p ∧
    welfareAlgorithmic p > welfareNarrative p ∧
    welfareAlgorithmic p > welfareViolence p := by
  unfold welfareAlgorithmic welfareMarket welfareRuleOfLaw welfareNarrative welfareViolence
  have ⟨⟨h_deg_nonneg, _⟩, _, _, h_rent_nonneg, h_surplus_nonneg⟩ := p.h_bounds
  omega

/--
  【定理 7.7】情報劣化・改ざんの激化に伴う厚生の自発的逆転（Phase Inversion）定理:
  情報劣化率 degRate が臨界値（アルゴリズム余剰＋信頼ボーナス＋35）を超えて悪化すると、
  暗号不整合ペナルティの膨張により、アルゴリズム統治の純厚生はより単純な成文法治を下回る。
-/
theorem degradation_inverts_algorithmic_vs_law
    (p : AdvancedGovernanceParams)
    (h_deg_rise : p.degRate > p.algorithmicSurplus + (p.verifiability + p.inclusivity) / 2 + 35) :
    welfareRuleOfLaw p > welfareAlgorithmic p := by
  unfold welfareRuleOfLaw welfareAlgorithmic
  omega

-- ----------------------------------------------------------------------------
-- 具象パラメータ系列による動的相転移シナリオと自動証明 (decide)
-- ----------------------------------------------------------------------------

/-- ① 原始・高劣化環境: 暴力支配のみが成立し最大厚生 -/
def sampleEnvPrimitive : AdvancedGovernanceParams where
  L := 0
  degRate := 85
  verifiability := 0
  inclusivity := 0
  capitalistRent := 0
  algorithmicSurplus := 0
  h_bounds := by decide

/-- ② 成文法治環境: 記録の蓄積により法治が解禁され、暴力を上回る -/
def sampleEnvRuleOfLaw : AdvancedGovernanceParams where
  L := 25
  degRate := 20
  verifiability := 20
  inclusivity := 30
  capitalistRent := 15
  algorithmicSurplus := 10
  h_bounds := by decide

/-- ③ 市場・資本主義環境: 信用履歴の蓄積と市場取引により市場が解禁され、法治を上回る -/
def sampleEnvMarket : AdvancedGovernanceParams where
  L := 60
  degRate := 12
  verifiability := 50
  inclusivity := 50
  capitalistRent := 20
  algorithmicSurplus := 20
  h_bounds := by decide

/-- ④ アルゴリズム統治環境: 不変アーカイブと暗号検証によりアルゴリズム統治が解禁され全体制を圧倒 -/
def sampleEnvAlgorithmic : AdvancedGovernanceParams where
  L := 1000
  degRate := 2
  verifiability := 95
  inclusivity := 90
  capitalistRent := 35
  algorithmicSurplus := 40
  h_bounds := by decide

/-- 後方互換用インスタンス -/
def sampleStage8Advanced : AdvancedGovernanceParams := sampleEnvAlgorithmic

/-- 具象証明 ①: 原始環境における暴力単独成立と厚生最大性の自動証明 -/
theorem sample_primitive_phase :
    isViolenceFeasible sampleEnvPrimitive ∧
    ¬ isNarrativeFeasible sampleEnvPrimitive ∧
    ¬ isRuleOfLawFeasible sampleEnvPrimitive ∧
    ¬ isMarketFeasible sampleEnvPrimitive ∧
    ¬ isAlgorithmicGovernanceFeasible sampleEnvPrimitive ∧
    welfareViolence sampleEnvPrimitive > welfareRuleOfLaw sampleEnvPrimitive ∧
    welfareViolence sampleEnvPrimitive > welfareMarket sampleEnvPrimitive := by
  unfold isViolenceFeasible isNarrativeFeasible isRuleOfLawFeasible isMarketFeasible isAlgorithmicGovernanceFeasible
  unfold welfareViolence welfareRuleOfLaw welfareMarket
  decide

/-- 具象証明 ②: 法治環境における法治解禁と暴力超克の自動証明 -/
theorem sample_rule_of_law_phase :
    isRuleOfLawFeasible sampleEnvRuleOfLaw ∧
    ¬ isMarketFeasible sampleEnvRuleOfLaw ∧
    ¬ isAlgorithmicGovernanceFeasible sampleEnvRuleOfLaw ∧
    welfareRuleOfLaw sampleEnvRuleOfLaw > welfareViolence sampleEnvRuleOfLaw := by
  unfold isRuleOfLawFeasible isMarketFeasible isAlgorithmicGovernanceFeasible welfareRuleOfLaw welfareViolence
  decide

/-- 具象証明 ③: 市場環境における市場解禁と法治超克の自動証明 -/
theorem sample_market_phase :
    isMarketFeasible sampleEnvMarket ∧
    ¬ isAlgorithmicGovernanceFeasible sampleEnvMarket ∧
    welfareMarket sampleEnvMarket > welfareRuleOfLaw sampleEnvMarket ∧
    welfareMarket sampleEnvMarket > welfareViolence sampleEnvMarket := by
  unfold isMarketFeasible isAlgorithmicGovernanceFeasible welfareMarket welfareRuleOfLaw welfareViolence
  decide

/-- 具象証明 ④: アルゴリズム統治環境における解禁と全体制圧倒の自動証明 -/
theorem sample_algorithmic_phase :
    isAlgorithmicGovernanceFeasible sampleEnvAlgorithmic ∧
    welfareAlgorithmic sampleEnvAlgorithmic > welfareMarket sampleEnvAlgorithmic ∧
    welfareAlgorithmic sampleEnvAlgorithmic > welfareRuleOfLaw sampleEnvAlgorithmic ∧
    welfareAlgorithmic sampleEnvAlgorithmic > welfareViolence sampleEnvAlgorithmic := by
  unfold isAlgorithmicGovernanceFeasible welfareAlgorithmic welfareMarket welfareRuleOfLaw welfareViolence
  decide

/-- 後方互換用証明 -/
theorem sample_stage8_feasible_and_dominant :
    isAlgorithmicGovernanceFeasible sampleStage8Advanced ∧
    welfareAlgorithmic sampleStage8Advanced > welfareMarket sampleStage8Advanced := by
  unfold isAlgorithmicGovernanceFeasible welfareAlgorithmic welfareMarket
  decide

-- ============================================================================
-- セクション 8: 結果の平等操作（Outcome Equality）と体制間競争（Regime Competition）の動学モデル
-- ============================================================================

/-- 結果の平等操作および体制間競争（Regime Competition）の統合パラメータ -/
structure RegimeCompetitionParams where
  -- 共通基礎パラメータ
  V_base             : Int  -- 基礎付加価値 V_{base}
  p_fee              : Int  -- 制度利用料・参加費
  c_cost             : Int  -- 基礎活動・検証コスト
  C_switch           : Int  -- 体制間移動コスト C_{regime_switch}
  -- 体制 A（再分配・結果の平等操作型体制）のパラメータ
  eqOutcome          : Int  -- 結果の平等度（再分配強度） \in [0, 100]
  k_redist           : Int  -- 独占レント・収奪利得およびテロ脅威の削滅係数
  k_incentive        : Int  -- 高貢献層の努力誘因・付加価値減衰係数
  base_pred_A        : Int  -- 体制 A の初期収奪利得（eqOutcome = 0 時）
  stay_surplus_A     : Int  -- 体制 A のルール内制度維持余剰
  base_terror_A      : Int  -- 体制 A の初期格差不満・テロ脅威利得
  -- 体制 B（機会均等・自由競争／アルゴリズム検証体制）のパラメータ
  V_bonus_B          : Int  -- 検証性・イノベーションによる追加付加価値
  capitalistRent_B   : Int  -- 体制 B の市場独占・不公平レント
  base_terror_B      : Int  -- 体制 B の格差放置による潜在的不満利得
  -- パラメータの定義域不変条件
  h_bounds :
    (0 ≤ eqOutcome ∧ eqOutcome ≤ 100) ∧
    k_redist > 0 ∧ k_incentive > 0 ∧
    C_switch ≥ 0 ∧
    V_base > 0 ∧ V_bonus_B ≥ 0
  deriving Repr

-- ----------------------------------------------------------------------------
-- 各体制における利得関数および社会純厚生関数
-- ----------------------------------------------------------------------------

/-- 平等化に伴う高貢献層のインセンティブ減衰コスト C_{incentive}(eqOutcome) -/
def costIncentive (p : RegimeCompetitionParams) : Int :=
  p.k_incentive * p.eqOutcome

/-- 体制 A の実効収奪利得（再分配による独占レントの圧縮） -/
def effectivePredGainA (p : RegimeCompetitionParams) : Int :=
  p.base_pred_A - p.k_redist * p.eqOutcome

/-- 体制 A の実効格差不満・テロ脅威利得（再分配によるルサンチマン解消） -/
def effectiveTerrorPayoffA (p : RegimeCompetitionParams) : Int :=
  p.base_terror_A - p.k_redist * p.eqOutcome

/-- 体制 A のキュレーター（高貢献・革新層）純利得 -/
def curPayoffA (p : RegimeCompetitionParams) : Int :=
  p.V_base - p.p_fee - p.c_cost - costIncentive p

/-- 体制 A の一般利用者（大衆層）純利得（再分配給付余剰を含む） -/
def consPayoffA (p : RegimeCompetitionParams) : Int :=
  p.V_base - p.p_fee + (p.k_redist * p.eqOutcome) / 2

/-- 体制 B のキュレーター（高貢献・革新層）純利得（イノベーションボーナスを最大享受） -/
def curPayoffB (p : RegimeCompetitionParams) : Int :=
  p.V_base + p.V_bonus_B - p.p_fee - p.c_cost

/-- 体制 B の一般利用者（大衆層）純利得（市場独占レントの負担） -/
def consPayoffB (p : RegimeCompetitionParams) : Int :=
  p.V_base + p.V_bonus_B - p.p_fee - p.capitalistRent_B

/-- 体制 A の社会純厚生: 基礎余剰からインセンティブ損失およびテロ脅威損失を控除 -/
def welfareRegimeA (p : RegimeCompetitionParams) : Int :=
  p.V_base - p.c_cost - costIncentive p - max 0 (effectiveTerrorPayoffA p)

/-- 体制 B の社会純厚生: イノベーション余剰から独占レント歪みコストを控除 -/
def welfareRegimeB (p : RegimeCompetitionParams) : Int :=
  p.V_base + p.V_bonus_B - p.c_cost - p.capitalistRent_B

/-- 並立共存社会の合算社会純厚生 -/
def welfareJointSystem (p : RegimeCompetitionParams) : Int :=
  welfareRegimeA p + welfareRegimeB p

-- ----------------------------------------------------------------------------
-- 体制間の移動・選択述語および共存安定条件
-- ----------------------------------------------------------------------------

/-- キュレーターの体制 A 滞在条件（人材流出の抑止） -/
def curStaysInA (p : RegimeCompetitionParams) : Prop :=
  curPayoffA p ≥ curPayoffB p - p.C_switch

/-- キュレーターの体制 B 流出条件（Brain Drain） -/
def curFleesToB (p : RegimeCompetitionParams) : Prop :=
  curPayoffA p < curPayoffB p - p.C_switch

/-- 利用者の体制 B 滞在条件（大衆離脱の抑止） -/
def consStaysInB (p : RegimeCompetitionParams) : Prop :=
  consPayoffB p ≥ consPayoffA p - p.C_switch

/-- 利用者の体制 A 離脱条件（大衆流出） -/
def consFleesToA (p : RegimeCompetitionParams) : Prop :=
  consPayoffB p < consPayoffA p - p.C_switch

/-- 体制間共存の安定条件（体制 A で独占抑止＆人材維持、かつ体制 B で大衆維持） -/
def isRegimeCoexistenceStable (p : RegimeCompetitionParams) : Prop :=
  effectivePredGainA p ≤ p.stay_surplus_A ∧
  curStaysInA p ∧
  consStaysInB p

-- ----------------------------------------------------------------------------
-- 体制間競争・平等操作の動学定理群
-- ----------------------------------------------------------------------------

/--
  【定理 8.1】適正な平等操作による破壊的独占の抑止定理:
  初期状態（eqOutcome = 0）では破壊的収奪が優位（base_pred_A > stay_surplus_A）な環境であっても、
  再分配強度 eqOutcome を適正範囲（インセンティブ維持上限以下、かつ独占抑止下限以上）に
  設定することで、収奪を完全に抑止しつつキュレーターの滞在条件を両立できる。
-/
theorem moderate_equality_deters_monopoly
    (p : RegimeCompetitionParams)
    (h_cur_ok : costIncentive p ≤ p.C_switch - p.V_bonus_B)
    (h_pred_deterred : p.k_redist * p.eqOutcome ≥ p.base_pred_A - p.stay_surplus_A) :
    effectivePredGainA p ≤ p.stay_surplus_A ∧ curStaysInA p := by
  unfold effectivePredGainA curStaysInA curPayoffA curPayoffB costIncentive at *
  omega

/--
  【定理 8.2】過度な平等操作による人材流出・停滞定理:
  体制 A が平等度を過度に引き上げ（costIncentive > C_switch - V_bonus_B）、
  高貢献層の努力が報われない悪平等に達すると、キュレーターの純利得が体制 B の
  転向利得を下回り、高貢献層の体制 B への人材流出（Brain Drain）が不可避となる。
-/
theorem excessive_equality_causes_brain_drain
    (p : RegimeCompetitionParams)
    (h_excessive : costIncentive p > p.C_switch - p.V_bonus_B) :
    curFleesToB p := by
  unfold curFleesToB curPayoffA curPayoffB costIncentive at *
  omega

/--
  【定理 8.3】体制間競争による最適均衡（相互牽制）定理:
  移動コスト C_switch が有限な開放環境において両体制が共存安定（curStaysInA ∧ consStaysInB）しているとき、
  (1) 体制 A はキュレーター流出を防ぐため過度な悪平等を自制せざるを得ず、
  (2) 体制 B は利用者の離脱を防ぐため過度な市場独占レントを自制せざるを得ない。
-/
theorem regime_competition_enforces_balanced_equilibrium
    (p : RegimeCompetitionParams)
    (h_cur_stay : curStaysInA p)
    (h_cons_stay : consStaysInB p) :
    costIncentive p ≤ p.C_switch - p.V_bonus_B ∧
    p.capitalistRent_B ≤ p.V_bonus_B + p.C_switch - (p.k_redist * p.eqOutcome) / 2 := by
  unfold curStaysInA curPayoffA curPayoffB costIncentive at *
  unfold consStaysInB consPayoffA consPayoffB at *
  omega

/--
  【定理 8.4】体制間競争による独占レント暴騰の抑止と社会純厚生の防衛定理:
  体制間競争による移動の脅威（足による投票）が存在する場合、体制 B の独占レントが
  上限以内に抑え込まれるため、競争のない閉鎖独占体制よりも体制 B の社会純厚生が厳密に高くなる。
-/
theorem regime_competition_caps_rent_and_improves_welfare
    (p_coex p_monopoly : RegimeCompetitionParams)
    (h_same_tech : p_coex.V_base = p_monopoly.V_base ∧ p_coex.V_bonus_B = p_monopoly.V_bonus_B ∧ p_coex.c_cost = p_monopoly.c_cost)
    (h_unconstrained_higher_rent : p_monopoly.capitalistRent_B > p_coex.capitalistRent_B) :
    welfareRegimeB p_coex > welfareRegimeB p_monopoly := by
  unfold welfareRegimeB
  omega

-- ----------------------------------------------------------------------------
-- 数値検証インスタンスと自動証明 (decide)
-- ----------------------------------------------------------------------------

/-- 共存均衡を満たす基準パラメータ -/
def sampleRegimeCompetition : RegimeCompetitionParams where
  V_base := 100
  p_fee := 20
  c_cost := 10
  C_switch := 50
  eqOutcome := 25
  k_redist := 3
  k_incentive := 1
  base_pred_A := 90
  stay_surplus_A := 30
  base_terror_A := 60
  V_bonus_B := 15
  capitalistRent_B := 20
  base_terror_B := 40
  h_bounds := by decide

/-- 過度な平等化（eqOutcome = 60）によりキュレーターが流出する反例シナリオ -/
def sampleExcessiveEquality : RegimeCompetitionParams where
  V_base := 100
  p_fee := 20
  c_cost := 10
  C_switch := 50
  eqOutcome := 60
  k_redist := 3
  k_incentive := 1
  base_pred_A := 90
  stay_surplus_A := 30
  base_terror_A := 60
  V_bonus_B := 15
  capitalistRent_B := 20
  base_terror_B := 40
  h_bounds := by decide

/-- 体制 B が独占レント（capitalistRent_B = 65）を貪り大衆が流出する反例シナリオ -/
def sampleExtremeRentB : RegimeCompetitionParams where
  V_base := 100
  p_fee := 20
  c_cost := 10
  C_switch := 50
  eqOutcome := 25
  k_redist := 3
  k_incentive := 1
  base_pred_A := 90
  stay_surplus_A := 30
  base_terror_A := 60
  V_bonus_B := 15
  capitalistRent_B := 65
  base_terror_B := 40
  h_bounds := by decide

/-- 具象検証 ①: 基準パラメータにおける体制間共存安定性の自動証明 -/
theorem sample_regime_competition_valid :
    isRegimeCoexistenceStable sampleRegimeCompetition := by
  unfold isRegimeCoexistenceStable effectivePredGainA curStaysInA consStaysInB
  unfold curPayoffA curPayoffB consPayoffA consPayoffB costIncentive
  decide

/-- 具象検証 ②: 過度な平等化（eqOutcome = 60）による人材流出（Brain Drain）の自動証明 -/
theorem sample_excessive_equality_triggers_drain :
    curFleesToB sampleExcessiveEquality := by
  unfold curFleesToB curPayoffA curPayoffB costIncentive
  decide

/-- 具象検証 ③: 体制 B の過度な独占レント（capitalistRent_B = 65）による大衆流出の自動証明 -/
theorem sample_excessive_rent_triggers_exodus :
    consFleesToA sampleExtremeRentB := by
  unfold consFleesToA consPayoffA consPayoffB
  decide

-- ============================================================================
-- セクション 9: アルゴリズム自律統治（体制 A）vs 評価文字化・信用取引体制（体制 T）の連続競争動学
-- ============================================================================

/-- アルゴリズム統治（体制 A）vs 文字・評判取引統治（体制 T）の連続競争パラメータ -/
structure TextTradeVsAlgoParams where
  V_base          : Int  -- 共通基礎付加価値
  nu_verif        : Int  -- 暗号学的検証可能性 \nu \in [0, 100]
  C_rigid         : Int  -- アルゴリズム統治の硬直性・非流動性コスト
  alpha_text      : Int  -- 文字情報公開・明示度 \alpha_{text} \in [0, 100]
  mu_trade        : Int  -- 評価取引流動性 \mu_{trade} \in [0, 100]
  R_trade         : Int  -- 文字化評価の取引手数料・独占レント
  C_signal        : Int  -- 見せかけの評判作り・シグナリング歪みコスト
  degRate         : Int  -- 環境情報劣化率 \lambda_{deg} \in [0, 100]
  h_bounds :
    (0 ≤ degRate ∧ degRate ≤ 100) ∧
    (0 ≤ nu_verif ∧ nu_verif ≤ 100) ∧
    (0 ≤ alpha_text ∧ alpha_text ≤ 100) ∧
    (0 ≤ mu_trade ∧ mu_trade ≤ 100) ∧
    C_rigid ≥ 0 ∧ R_trade ≥ 0 ∧ C_signal ≥ 0
  deriving Repr

-- ----------------------------------------------------------------------------
-- 各体制の単位効用および連続的ポートフォリオ配分関数
-- ----------------------------------------------------------------------------

/-- 体制 A（アルゴリズム自律統治）の単位効用:
    基礎価値 ＋ 検証性ボーナス － 低度劣化ペナルティ (degRate) － 硬直性コスト -/
def unitPayoffA (p : TextTradeVsAlgoParams) : Int :=
  p.V_base + p.nu_verif - p.degRate - p.C_rigid

/-- 体制 T（評価文字表示・市場取引体制）の単位効用:
    基礎価値 ＋ 取引流動性ボーナス － 高度劣化ペナルティ (3 * degRate) － 取引レント － シグナリング歪み -/
def unitPayoffT (p : TextTradeVsAlgoParams) : Int :=
  p.V_base + (p.alpha_text + p.mu_trade) / 2 - 3 * p.degRate - p.R_trade - p.C_signal

/-- 体制 A と体制 T の単位効用格差 \Delta u = u_A - u_T -/
def payoffDiff (p : TextTradeVsAlgoParams) : Int :=
  unitPayoffA p - unitPayoffT p

/-- 連続的リソース配分 w \in [0, 100] に対する限界効用均衡条件:
    体制 A への限界利得 (u_A - w) と体制 T への限界利得 (u_T - (100 - w)) が一致する -/
def isEquilibriumWeight (p : TextTradeVsAlgoParams) (w : Int) : Prop :=
  unitPayoffA p - w = unitPayoffT p - (100 - w)

/-- 内点均衡（0 < w < 100 で限界効用が一致し、両体制が連続的にシェアを分け合う共存状態） -/
def isInteriorEquilibrium (p : TextTradeVsAlgoParams) (w : Int) : Prop :=
  0 < w ∧ w < 100 ∧ isEquilibriumWeight p w

-- ----------------------------------------------------------------------------
-- 連続競争・相転移定理群（セクション 9）
-- ----------------------------------------------------------------------------

/--
  【定理 9.1】文字情報の劣化・改ざんによる取引体制の自壊（連続的優位性逆転）:
  情報劣化率 \lambda_{deg} が連続的に上昇し、臨界代数関係式
  2 * degRate > (alpha_text + mu_trade)/2 - nu_verif + C_rigid - R_trade - C_signal
  を超過した瞬間、文字情報の風化・文脈喪失のペナルティが取引流動性ボーナスを完全に相殺し、
  アルゴリズム統治（体制 A）の純効用が評価取引体制（体制 T）を厳密に上回る。
-/
theorem degradation_inverts_text_trade_to_algorithmic
    (p : TextTradeVsAlgoParams)
    (h_crit : 2 * p.degRate > (p.alpha_text + p.mu_trade) / 2 - p.nu_verif + p.C_rigid - p.R_trade - p.C_signal) :
    unitPayoffA p > unitPayoffT p := by
  unfold unitPayoffA unitPayoffT
  omega

/--
  【定理 9.2】高流動性・低劣化環境における「評価取引体制」の局所優位:
  情報の劣化が極めて小さく、かつ文字情報公開度 \alpha_{text} と取引流動性 \mu_{trade} が
  十分に高い場合、アルゴリズム統治の硬直性ペナルティを打ち破り、
  評価取引体制（体制 T）が体制 A を厳密に上回る。
-/
theorem high_liquidity_enables_trade_regime_dominance
    (p : TextTradeVsAlgoParams)
    (h_trade_beats : (p.alpha_text + p.mu_trade) / 2 > p.nu_verif + 2 * p.degRate - p.C_rigid + p.R_trade + p.C_signal) :
    unitPayoffT p > unitPayoffA p := by
  unfold unitPayoffT unitPayoffA
  omega

/--
  【定理 9.3】連続的リソース配分 w における内点均衡（二体制の共存と相互牽制）:
  体制間の効用格差 \Delta u が分散投資による許容幅（-100 < \Delta u < 100）に収まっているとき、
  限界効用を等しくする配分比率 w は必ず 0 < w < 100 の範囲に収まり、
  どちらか一方への完全な片寄り（0 or 100）を排除した連続的共存状態が成立する。
-/
theorem continuous_portfolio_interior_equilibrium
    (p : TextTradeVsAlgoParams)
    (w : Int)
    (h_eq : isEquilibriumWeight p w)
    (h_lower : payoffDiff p > -100)
    (h_upper : payoffDiff p < 100) :
    isInteriorEquilibrium p w := by
  unfold isInteriorEquilibrium isEquilibriumWeight payoffDiff at *
  refine ⟨?_, ?_, h_eq⟩
  · omega
  · omega

/--
  【定理 9.4】体制間競争による「評価取引の独占レント」抑制効果:
  体制 A（アルゴリズム統治）という逃げ場（外部オプション）が存在するため、
  体制 T の支配層が取引手数料・独占レント R_trade を引き上げると、
  エージェントの最適配分比率は体制 A 側へ連続的かつ単調にシフト（w_2 > w_1）し、
  結果として体制 T のレント搾取が自己抑制される。
-/
theorem regime_competition_disciplines_trade_rent
    (p1 p2 : TextTradeVsAlgoParams)
    (w1 w2 : Int)
    (h_eq1 : isEquilibriumWeight p1 w1)
    (h_eq2 : isEquilibriumWeight p2 w2)
    (h_same : p1.V_base = p2.V_base ∧ p1.nu_verif = p2.nu_verif ∧
              p1.C_rigid = p2.C_rigid ∧ p1.alpha_text = p2.alpha_text ∧
              p1.mu_trade = p2.mu_trade ∧ p1.C_signal = p2.C_signal ∧
              p1.degRate = p2.degRate)
    (h_rent_hike : p2.R_trade > p1.R_trade) :
    w2 > w1 := by
  unfold isEquilibriumWeight unitPayoffA unitPayoffT at *
  omega

-- ----------------------------------------------------------------------------
-- 数値検証インスタンスと自動証明 (decide)
-- ----------------------------------------------------------------------------

/-- 基準共存シナリオ: 両体制が均衡し、エージェントが約58%を体制 A、42%を体制 T に配分 -/
def sampleTextTradeVsAlgo : TextTradeVsAlgoParams where
  V_base := 100
  nu_verif := 60
  C_rigid := 14
  alpha_text := 70
  mu_trade := 70
  R_trade := 10
  C_signal := 10
  degRate := 10
  h_bounds := by decide

/-- 劣化危機シナリオ (degRate = 30): 文字情報が風化し、体制 A が体制 T を圧倒 -/
def sampleHighDegCrisis : TextTradeVsAlgoParams where
  V_base := 100
  nu_verif := 60
  C_rigid := 14
  alpha_text := 70
  mu_trade := 70
  R_trade := 10
  C_signal := 10
  degRate := 30
  h_bounds := by decide

/-- 流動性好況シナリオ (degRate = 2, 可視性・流動性 = 90): 体制 T が体制 A を局所凌駕 -/
def sampleHighLiquidityBoom : TextTradeVsAlgoParams where
  V_base := 100
  nu_verif := 60
  C_rigid := 14
  alpha_text := 90
  mu_trade := 90
  R_trade := 10
  C_signal := 10
  degRate := 2
  h_bounds := by decide

/-- 具象検証 ①: 基準シナリオにおける内点均衡 (w = 58%) の自動証明 -/
theorem sample_interior_equilibrium_valid :
    isInteriorEquilibrium sampleTextTradeVsAlgo 58 := by
  unfold isInteriorEquilibrium isEquilibriumWeight unitPayoffA unitPayoffT
  decide

/-- 具象検証 ②: 劣化急増時における体制 A の優位性逆転の自動証明 -/
theorem sample_high_deg_inversion_valid :
    unitPayoffA sampleHighDegCrisis > unitPayoffT sampleHighDegCrisis := by
  unfold unitPayoffA unitPayoffT
  decide

/-- 具象検証 ③: 高流動性・低劣化環境における体制 T の局所優位の自動証明 -/
theorem sample_high_liquidity_boom_valid :
    unitPayoffT sampleHighLiquidityBoom > unitPayoffA sampleHighLiquidityBoom := by
  unfold unitPayoffT unitPayoffA
  decide

-- ============================================================================
-- セクション 10: 汎用政治体制の動的競争モデル（個別相定義の統合と一般化）
-- ============================================================================

/-- 任意の政治体制が持つ汎用的な特性・コストパラメータ構造体 -/
structure GenericRegime where
  id             : Nat  -- 体制識別番号
  archiveLen     : Int  -- 記録保持・アーカイブ長 L
  degRate        : Int  -- 情報劣化率 \lambda_{deg} \in [0, 100]
  verifiability  : Int  -- 検証可能性 \nu \in [0, 100]
  inclusivity    : Int  -- 包摂性・透明性 \alpha_{trans} \in [0, 100]
  rentCost       : Int  -- 独占レント・維持コスト歪み
  coordination   : Int  -- 協調・イノベーション余剰ボーナス
  h_bounds       : 
    (0 ≤ degRate ∧ degRate ≤ 100) ∧
    (0 ≤ verifiability ∧ verifiability ≤ 100) ∧
    (0 ≤ inclusivity ∧ inclusivity ≤ 100) ∧
    archiveLen ≥ 0 ∧ rentCost ≥ 0 ∧ coordination ≥ 0
  deriving Repr

/-- 任意の政治体制における統一的な社会純厚生関数 -/
def genericRegimeWelfare (r : GenericRegime) : Int :=
  100 + r.coordination + (r.verifiability + r.inclusivity) / 2 - r.rentCost - 2 * r.degRate

/--
  【定理 10.1】情報劣化率と検証可能性のトレードオフによる体制間競争優位性定理（一般化定理）:
  アーカイブ長が十分に長く、情報劣化率が低く抑えられ、かつ検証性と包摂性が高い体制 A は、
  劣化耐性が低くレント歪みが大きい体制 B を社会純厚生において厳密に凌駕する。
-/
theorem generic_regime_competition_dominance
    (regimeA regimeB : GenericRegime)
    (h_better_deg : regimeA.degRate ≤ regimeB.degRate)
    (h_better_verif : regimeA.verifiability ≥ regimeB.verifiability)
    (h_better_incl : regimeA.inclusivity ≥ regimeB.inclusivity)
    (h_lower_rent : regimeA.rentCost ≤ regimeB.rentCost)
    (h_higher_coord : regimeA.coordination ≥ regimeB.coordination)
    (h_strict : regimeA.degRate < regimeB.degRate ∨ 
                regimeA.verifiability + regimeA.inclusivity ≥ regimeB.verifiability + regimeB.inclusivity + 2 ∨ 
                regimeA.rentCost < regimeB.rentCost ∨ 
                regimeA.coordination > regimeB.coordination) :
    genericRegimeWelfare regimeA > genericRegimeWelfare regimeB := by
  unfold genericRegimeWelfare
  have ⟨⟨ha_deg, _⟩, _, _, ha_L, ha_rent, ha_coord⟩ := regimeA.h_bounds
  have ⟨⟨hb_deg, _⟩, _, _, hb_L, hb_rent, hb_coord⟩ := regimeB.h_bounds
  omega

/-- 体制間での人材・リソースの選択・滞在判定関数（ブール値） -/
def regimeChoiceShare (welfareA welfareB C_switch : Int) : Bool :=
  welfareA ≥ welfareB - C_switch

/-- 体制間での人材・リソースの選択・滞在条件（命題） -/
def regimeChoiceCondition (welfareA welfareB C_switch : Int) : Prop :=
  welfareA ≥ welfareB - C_switch

/-- 連続的リソースシェア配分比率（ポートフォリオ選択） -/
def continuousRegimeShareA (welfareA welfareB C_switch : Int) : Int :=
  50 + (welfareA - welfareB) / (2 * (max 1 C_switch))

/--
  【定理 10.2】スイッチングコスト C_switch による劣位体制の固定化（Lock-in）定理:
  たとえ体制 B の潜在厚生が体制 A より高くても、体制間の移動コスト C_switch が
  厚生格差以上である限り、エージェントは体制 A に留まり続け、ロックインが発生する。
-/
theorem switching_cost_enables_lockin
    (welfareA welfareB C_switch : Int)
    (h_lockin : C_switch ≥ welfareB - welfareA) :
    regimeChoiceCondition welfareA welfareB C_switch := by
  unfold regimeChoiceCondition
  omega

/--
  【定理 10.3】開放系における移動の自由によるロックイン解消と優位体制移行定理:
  移動コスト C_switch が厚生格差を下回る開放環境では、劣位体制へのロックインが打破され、
  エージェントは優位体制 B への移動を選択する。
-/
theorem open_mobility_eliminates_lockin
    (welfareA welfareB C_switch : Int)
    (h_open : C_switch < welfareB - welfareA) :
    ¬ regimeChoiceCondition welfareA welfareB C_switch := by
  unfold regimeChoiceCondition
  omega

-- ----------------------------------------------------------------------------
-- 各歴史的・先進的ガバナンス形態の GenericRegime 統一インスタンス
-- ----------------------------------------------------------------------------

/-- ① 汎用アルゴリズム自律統治（超低劣化・高検証性・ゼロレント） -/
def genericAlgorithmic : GenericRegime where
  id := 1
  archiveLen := 1000
  degRate := 2
  verifiability := 95
  inclusivity := 90
  rentCost := 0
  coordination := 40
  h_bounds := by decide

/-- ② 汎用評価文字化・信用取引体制（高流動性・中劣化・取引レント） -/
def genericTextTrade : GenericRegime where
  id := 2
  archiveLen := 200
  degRate := 10
  verifiability := 70
  inclusivity := 80
  rentCost := 15
  coordination := 35
  h_bounds := by decide

/-- ③ 汎用市場・資本主義体制（中検証性・独占レント搾取） -/
def genericCapitalism : GenericRegime where
  id := 3
  archiveLen := 60
  degRate := 12
  verifiability := 50
  inclusivity := 50
  rentCost := 25
  coordination := 20
  h_bounds := by decide

/-- ④ 汎用成文法治国家（成文アーカイブ・法治解釈劣化） -/
def genericRuleOfLaw : GenericRegime where
  id := 4
  archiveLen := 25
  degRate := 20
  verifiability := 30
  inclusivity := 30
  rentCost := 10
  coordination := 10
  h_bounds := by decide

/-- 具象検証 ①: 統一厚生評価における全体制の自然な階層序列の自動証明 -/
theorem sample_generic_hierarchy :
    genericRegimeWelfare genericAlgorithmic > genericRegimeWelfare genericTextTrade ∧
    genericRegimeWelfare genericTextTrade > genericRegimeWelfare genericCapitalism ∧
    genericRegimeWelfare genericCapitalism > genericRegimeWelfare genericRuleOfLaw := by
  unfold genericRegimeWelfare
  decide

/-- 具象検証 ②: アルゴリズム統治が資本主義を凌駕し移動条件を満たすことの自動証明 -/
theorem sample_generic_algo_dominates_capitalism :
    genericRegimeWelfare genericAlgorithmic > genericRegimeWelfare genericCapitalism ∧
    regimeChoiceShare (genericRegimeWelfare genericAlgorithmic) (genericRegimeWelfare genericCapitalism) 10 = true := by
  unfold genericRegimeWelfare regimeChoiceShare
  decide

-- ============================================================================
-- セクション 11: 生命発生から資本主義・民主主義・タグ通貨への大統一進化動学
-- （個別相の定義を排除し、物理法則の利用と記録共有の連続ダイナミクスとして再現）
-- ============================================================================

/--
  生命発生から現代・未来に至る汎用進化環境パラメータ構造体:
  - 物理法則（熱力学・力学・エネルギー）の利用能力と集団内分布
  - 知識を保存・共有する記録メディア特性（世代長 L, 劣化率 λ, 検証性 ν, 包摂性 α）
  - 社会的機能・インセンティブ特性（資本蓄積, タグ流動性, 独占レント）
-/
structure LifeEvolutionParams where
  physBase            : Int  -- 物理法則を利用したエネルギー・資源獲得ポテンシャル
  physPioneerRatio    : Int  -- 自力で物理法則を利用できる先駆個体率 \in [0, 100]
  archiveLen          : Int  -- 世代間記録保持長 L \ge 0 (DNA/文字/デジタル台帳)
  degRate             : Int  -- 情報劣化・変異散逸率 \lambda_{deg} \in [0, 100]
  verifiability       : Int  -- 記録の検証可能性・再現忠実度 \nu \in [0, 100]
  inclusivity         : Int  -- 知識の共有・大衆包摂度 \alpha \in [0, 100]
  capitalAccumulation : Int  -- 物理利用装置（道具・機械・資本財）の基底蓄積力 \ge 0
  tagLiquidity        : Int  -- 信用・評価タグの取引流動性 \mu_{tag} \in [0, 100]
  monopolyRent        : Int  -- 物理知識の囲い込み・独占レント \ge 0
  h_bounds :
    (0 ≤ physPioneerRatio ∧ physPioneerRatio ≤ 100) ∧
    (0 ≤ degRate ∧ degRate ≤ 100) ∧
    (0 ≤ verifiability ∧ verifiability ≤ 100) ∧
    (0 ≤ inclusivity ∧ inclusivity ≤ 100) ∧
    (0 ≤ tagLiquidity ∧ tagLiquidity ≤ 100) ∧
    physBase ≥ 0 ∧ archiveLen ≥ 0 ∧ capitalAccumulation ≥ 0 ∧ monopolyRent ≥ 0
  deriving Repr

/--
  実効的物理法則利用余剰 S_phys:
  先駆個体の自力獲得に加え、記録の共有包摂（α）と検証性（ν）によって集団全体に物理法則の利用法が伝播し、
  情報劣化（λ_deg）によって減衰する。
-/
def physicsSurplus (p : LifeEvolutionParams) : Int :=
  p.physBase + 2 * p.physPioneerRatio + (p.inclusivity + p.verifiability) / 2 - 2 * p.degRate

/--
  資本主義の創発余剰 S_cap（道具・機械・資本財の蓄積余剰）:
  物理法則を利用する手段が記録され（L）、劣化散逸（λ_deg）を上回るとき、
  現在消費を犠牲にして資本蓄積を行うインセンティブが自発的に正となる。
-/
def capitalSurplus (p : LifeEvolutionParams) : Int :=
  p.capitalAccumulation + p.archiveLen / 10 - 2 * p.degRate

/--
  民主主義の創発余剰 S_dem（知識包摂と分散検証による合意形成余剰）:
  物理法則の利用法が一部のエリートに独占されず全員に共有（α）され、
  相互検証（ν）されるとき、独占レント搾取を打破して民主的合意が正の余剰を生む。
-/
def democraticSurplus (p : LifeEvolutionParams) : Int :=
  (p.inclusivity + p.verifiability) / 2 - p.monopolyRent

/--
  タグ通貨の創発余剰 S_tag（評価・信用の記号化と低摩擦流動性余剰）:
  物理的貢献や信用を「明示的な文字・デジタルタグ」として取引・決済する余剰。
  低劣化（λ_deg）と高検証性（ν）、高流動性（μ_tag）の元で実物交換を超克する。
-/
def tagCurrencySurplus (p : LifeEvolutionParams) : Int :=
  (p.tagLiquidity + p.verifiability) / 2 - 2 * p.degRate

/--
  生命・社会集団の大統一進化適応度関数 W_evo:
  離散的な相の区分を一切行わず、基礎物理利用余剰と各制度的創発余剰の総和として定義される。
-/
def evolutionaryFitness (p : LifeEvolutionParams) : Int :=
  50 + physicsSurplus p + capitalSurplus p + democraticSurplus p + tagCurrencySurplus p

/-- 資本主義の自発的創発条件（資本蓄積余剰が正） -/
def isCapitalismEmerged (p : LifeEvolutionParams) : Prop :=
  capitalSurplus p > 0

/-- 民主主義の自発的創発条件（民主的合意余剰が正） -/
def isDemocracyEmerged (p : LifeEvolutionParams) : Prop :=
  democraticSurplus p > 0

/-- タグ通貨の自発的創発条件（タグ信用取引余剰が正） -/
def isTagCurrencyEmerged (p : LifeEvolutionParams) : Prop :=
  tagCurrencySurplus p > 0

/--
  【定理 11.1】初期生命の局所生存・共有不全定理（Abiogenesis Isolation Theorem）:
  生命発生初期（記録なし L=0、共有なし α=0、検証なし ν=0、高劣化 λ_deg ≫ 0）では、
  資本蓄積・民主的合意・タグ通貨余剰のすべてが厳密に非正となり、
  物理法則を利用できる極少数の先駆個体のみが局所的に自活する。
-/
theorem abiogenesis_isolation_theorem
    (p : LifeEvolutionParams)
    (h_no_archive : p.archiveLen = 0)
    (h_no_incl : p.inclusivity = 0)
    (h_no_verif : p.verifiability = 0)
    (h_high_deg : p.degRate ≥ 50)
    (h_low_cap : p.capitalAccumulation ≤ 50)
    (h_low_tag : p.tagLiquidity ≤ 50) :
    capitalSurplus p ≤ 0 ∧ democraticSurplus p ≤ 0 ∧ tagCurrencySurplus p ≤ 0 := by
  unfold capitalSurplus democraticSurplus tagCurrencySurplus
  have ⟨_, _, _, _, _, _, _, _, hb_rent⟩ := p.h_bounds
  omega

/--
  【定理 11.2】知識蓄積による資本主義の自発的創発定理（Emergence of Capitalism Theorem）:
  アーカイブ長 L の伸長と情報劣化率 λ_deg の低下により、
  道具・機械などの資本財を記録・蓄積する余剰が厳密に正（S_cap > 0）となる。
-/
theorem emergence_of_capitalism_theorem
    (p : LifeEvolutionParams)
    (h_acc : p.capitalAccumulation + p.archiveLen / 10 > 2 * p.degRate) :
    isCapitalismEmerged p := by
  unfold isCapitalismEmerged capitalSurplus
  omega

/--
  【定理 11.3】知識包摂による民主主義の自発的創発定理（Emergence of Democracy Theorem）:
  物理利用知識の大衆包摂度 α と検証忠実度 ν の向上が独占レントを上回るとき、
  専制支配を打破して民主的合意形成が自発的に創発（S_dem > 0）する。
-/
theorem emergence_of_democracy_theorem
    (p : LifeEvolutionParams)
    (h_dem : (p.inclusivity + p.verifiability) / 2 > p.monopolyRent) :
    isDemocracyEmerged p := by
  unfold isDemocracyEmerged democraticSurplus
  omega

/--
  【定理 11.4】低劣化・高検証性によるタグ通貨の自発的創発定理（Emergence of Tag Currency Theorem）:
  情報劣化率 λ_deg が十分に低減され、検証性 ν と流動性 μ_tag が高まることで、
  実物交換に依存しない信用タグ決済・評価取引が自発的に創発（S_tag > 0）する。
-/
theorem emergence_of_tag_currency_theorem
    (p : LifeEvolutionParams)
    (h_tag : (p.tagLiquidity + p.verifiability) / 2 > 2 * p.degRate) :
    isTagCurrencyEmerged p := by
  unfold isTagCurrencyEmerged tagCurrencySurplus
  omega

/--
  【定理 11.5】生命・社会大統一適応度単調性定理（Grand Unified Monotonicity Theorem）:
  物理利用ポテンシャルおよび記録・共有パラメータが改善し、情報劣化と独占レントが抑制されるとき、
  いかなる個別相の遷移フラグも経ることなく、大統一適応度 W_evo は厳密に単調増加する。
-/
theorem evolutionary_fitness_strictly_monotonic
    (p1 p2 : LifeEvolutionParams)
    (h_physBase : p1.physBase ≤ p2.physBase)
    (h_pioneer  : p1.physPioneerRatio ≤ p2.physPioneerRatio)
    (h_archive  : p1.archiveLen ≤ p2.archiveLen)
    (h_deg      : p1.degRate ≥ p2.degRate)
    (h_verif    : p1.verifiability ≤ p2.verifiability)
    (h_incl     : p1.inclusivity ≤ p2.inclusivity)
    (h_cap      : p1.capitalAccumulation ≤ p2.capitalAccumulation)
    (h_tag      : p1.tagLiquidity ≤ p2.tagLiquidity)
    (h_rent     : p1.monopolyRent ≥ p2.monopolyRent)
    (h_strict   : p1.physBase < p2.physBase ∨
                  p1.physPioneerRatio < p2.physPioneerRatio ∨
                  p1.archiveLen + 10 ≤ p2.archiveLen ∨
                  p1.degRate > p2.degRate ∨
                  p1.verifiability + p1.inclusivity + 2 ≤ p2.verifiability + p2.inclusivity ∨
                  p1.capitalAccumulation < p2.capitalAccumulation ∨
                  p1.tagLiquidity + p1.verifiability + 2 ≤ p2.tagLiquidity + p2.verifiability ∨
                  p1.monopolyRent > p2.monopolyRent) :
    evolutionaryFitness p1 < evolutionaryFitness p2 := by
  unfold evolutionaryFitness physicsSurplus capitalSurplus democraticSurplus tagCurrencySurplus
  have ⟨_, _, _, _, _, _, _, _, _⟩ := p1.h_bounds
  have ⟨_, _, _, _, _, _, _, _, _⟩ := p2.h_bounds
  omega

-- ----------------------------------------------------------------------------
-- 進化史における具象環境インスタンスと自動証明 (decide)
-- ----------------------------------------------------------------------------

/-- ① 生命発生初期 (Abiogenesis): 物理法則利用者は極一部、共有ゼロ、超高劣化 -/
def envAbiogenesis : LifeEvolutionParams where
  physBase := 20
  physPioneerRatio := 2
  archiveLen := 0
  degRate := 90
  verifiability := 0
  inclusivity := 0
  capitalAccumulation := 0
  tagLiquidity := 0
  monopolyRent := 20
  h_bounds := by decide

/-- ② 原始遺伝・代謝固定化 (Genetic Evolution): DNA/RNAによる世代間記録の獲得 -/
def envGeneticEvolution : LifeEvolutionParams where
  physBase := 40
  physPioneerRatio := 15
  archiveLen := 50
  degRate := 40
  verifiability := 30
  inclusivity := 20
  capitalAccumulation := 10
  tagLiquidity := 0
  monopolyRent := 15
  h_bounds := by decide

/-- ③ 近代産業・資本主義 (Capitalist Industrial): 印刷・図面・複式簿記による資本蓄積 -/
def envCapitalistIndustrial : LifeEvolutionParams where
  physBase := 80
  physPioneerRatio := 30
  archiveLen := 800
  degRate := 15
  verifiability := 60
  inclusivity := 40
  capitalAccumulation := 50
  tagLiquidity := 20
  monopolyRent := 35
  h_bounds := by decide

/-- ④ 知識社会・大衆民主主義 (Democratic Knowledge): 義務教育・情報共有による分散合意 -/
def envDemocraticKnowledge : LifeEvolutionParams where
  physBase := 90
  physPioneerRatio := 50
  archiveLen := 1200
  degRate := 10
  verifiability := 80
  inclusivity := 85
  capitalAccumulation := 60
  tagLiquidity := 50
  monopolyRent := 15
  h_bounds := by decide

/-- ⑤ 暗号・アルゴリズム・タグ通貨経済 (Tag Currency Network): 分散台帳による高解像度信用取引 -/
def envTagCurrencyNetwork : LifeEvolutionParams where
  physBase := 100
  physPioneerRatio := 70
  archiveLen := 5000
  degRate := 2
  verifiability := 95
  inclusivity := 95
  capitalAccumulation := 70
  tagLiquidity := 95
  monopolyRent := 5
  h_bounds := by decide

/--
  具象検証 ①: 各時代の制度自発的創発（Emergence）フラグの自動証明
  - 初期生命: 資本・民主・タグのすべてが不成立
  - 資本主義時代: 資本蓄積が自発的に成立 (isCapitalismEmerged)
  - 民主主義時代: 民主的合意が自発的に成立 (isDemocracyEmerged)
  - タグ通貨時代: タグ信用取引が自発的に成立 (isTagCurrencyEmerged)
-/
theorem sample_evolution_emergence_valid :
    ¬ isCapitalismEmerged envAbiogenesis ∧
    ¬ isDemocracyEmerged envAbiogenesis ∧
    ¬ isTagCurrencyEmerged envAbiogenesis ∧
    isCapitalismEmerged envCapitalistIndustrial ∧
    isDemocracyEmerged envDemocraticKnowledge ∧
    isTagCurrencyEmerged envTagCurrencyNetwork := by
  unfold isCapitalismEmerged isDemocracyEmerged isTagCurrencyEmerged
  unfold capitalSurplus democraticSurplus tagCurrencySurplus
  decide

/--
  具象検証 ②: 生命発生からタグ経済に至る大統一適応度の厳密な単調階層序列の自動証明
  W(Abiogenesis) < W(Genetic) < W(Capitalist) < W(Democratic) < W(TagCurrency)
-/
theorem sample_evolution_grand_hierarchy :
    evolutionaryFitness envAbiogenesis < evolutionaryFitness envGeneticEvolution ∧
    evolutionaryFitness envGeneticEvolution < evolutionaryFitness envCapitalistIndustrial ∧
    evolutionaryFitness envCapitalistIndustrial < evolutionaryFitness envDemocraticKnowledge ∧
    evolutionaryFitness envDemocraticKnowledge < evolutionaryFitness envTagCurrencyNetwork := by
  unfold evolutionaryFitness physicsSurplus capitalSurplus democraticSurplus tagCurrencySurplus
  decide

-- ============================================================================
-- 実行用エントリポイントと数値検証シナリオ
-- ============================================================================

def main : IO Unit := do
  IO.println "======================================================================"
  IO.println " 評価システムの動的ガバナンス・公開条件・相転移モデル (Lean 4 形式検証)"
  IO.println "======================================================================"
  -- Section 0
  let p := sampleParams
  let pi_C := netPayoffC p
  let pi_D := netPayoffD p
  IO.println s!"[Sec 0] 記録継承純利得 Π_C={pi_C}, 破壊リセット純利得 Π_D={pi_D}"
  -- Section 1
  let d := sampleOpenGovernance
  IO.println s!"[Sec 1] 状態分離公開ガバナンス (α_log={d.alphaLog}, α_mech={d.alphaMech}, B_adm={d.B_adm}):"
  IO.println s!"        状態引継純余剰={d.V_H_next - d.C_mig - d.C_store} vs リセット={d.V_empty_next} (FullOpenStability 証明済)"
  -- Section 2
  let b := sampleBullyingClosed
  IO.println s!"[Sec 2] 閉鎖空間過剰いじめ: Π^Copy={payoffCopy b}, Π^Exit={payoffExit b}, Π^Terror={payoffTerror b}"
  let b_exit := { b with C_exit := 10 }
  IO.println s!"        処方箋①(多層離脱 C_exit=10): Π^Exit={payoffExit b_exit} >= Π^Terror={payoffTerror b_exit}"
  -- Section 3
  let g := sampleGachaAI
  IO.println s!"[Sec 3] 近視眼的AI切り捨て誘惑: uErase={uErase g} > uSupport={uSupport g} (T_min={T_min g})"
  let alr := sampleAILongRun
  IO.println s!"        非定常ショック下長期厚生: AI包摂={welfareAIInclude alr} > 早期切り捨て={welfareAICull alr}"
  -- Section 4 & 5
  let pred := payoffPred 80 35 20
  let front := payoffFront 50 45 10
  let int_f := payoffInt 90 15
  IO.println s!"[Sec 5] 相転移比較: 土地収奪 Π^Pred={pred} -> 新天地開拓 Π^Front={front} -> 多次元開拓 Π^Int={int_f}"
  IO.println s!"        枯渇時管理者上限価格: F_high(alt=40)={admMaxPrice 120 15 40} -> F_low(alt=5)={admMaxPrice 120 15 5}"
  -- Section 6
  let cog := samplePrimateCognitive
  let cog_unlocked := { cog with inferenceLoss := cog.inferenceLoss - 30, sigCost := cog.sigCost - 15 }
  let st := sampleStageTransition
  let rp_loaded := applyCognitiveLoad sampleStage8RolePayoffs 40
  let rp_stage8 := applyAlgorithmicRecovery sampleStage8RolePayoffs 40 25 10
  IO.println s!"[Sec 6] 認知限界ΔC: 原始段階={deltaC cog} -> 物語+法律解禁={deltaC cog_unlocked}"
  IO.println s!"        段階進化純余剰: 単純={netStageSurplus st.V_simple st.C_simple} vs 能力不足時={netStageSurplus st.V_advanced st.C_advanced_raw} -> 獲得後={netStageSurplus st.V_advanced (st.C_advanced_raw - st.cogCapabilityGain)}"
  IO.println s!"        認知過負荷時最大利得={maxInstitutionalPayoff rp_loaded} (< 暴力=20) -> 第8段階回復後={maxInstitutionalPayoff rp_stage8} (>= 20)"
  -- Section 7
  IO.println "[Sec 7] 保存能力・情報劣化率による動的ガバナンス相転移シミュレーション:"
  let p_prim := sampleEnvPrimitive
  IO.println s!"        ① 原始・高劣化相 (deg={p_prim.degRate}, L={p_prim.L}): W(暴力)={welfareViolence p_prim} > W(法治)={welfareRuleOfLaw p_prim}, W(市場)={welfareMarket p_prim} [暴力単独成立]"
  let p_law := sampleEnvRuleOfLaw
  IO.println s!"        ② 成文法治相 (deg={p_law.degRate}, L={p_law.L}): W(法治)={welfareRuleOfLaw p_law} > W(暴力)={welfareViolence p_law} [法治解禁・最適]"
  let p_mkt := sampleEnvMarket
  IO.println s!"        ③ 市場・資本主義相 (deg={p_mkt.degRate}, L={p_mkt.L}): W(市場)={welfareMarket p_mkt} > W(法治)={welfareRuleOfLaw p_mkt} [市場解禁・最適]"
  let p_algo := sampleEnvAlgorithmic
  IO.println s!"        ④ アルゴリズム統治相 (deg={p_algo.degRate}, L={p_algo.L}, ν={p_algo.verifiability}): W(アルゴリズム)={welfareAlgorithmic p_algo} > W(市場)={welfareMarket p_algo} [全ガバナンス圧倒・超克]"
  -- Section 8
  IO.println "[Sec 8] 結果の平等操作 (Outcome Equality) と体制間競争 (Regime Competition):"
  let rc := sampleRegimeCompetition
  IO.println s!"        共存均衡時 (eq={rc.eqOutcome}, C_switch={rc.C_switch}):"
  IO.println s!"          体制A(再分配): 収奪利得={effectivePredGainA rc} (<=30: 独占抑止成功), キュレーター利得={curPayoffA rc}, 大衆利得={consPayoffA rc}"
  IO.println s!"          体制B(自由競争): キュレーター利得={curPayoffB rc}, 大衆利得={consPayoffB rc} (独占レント={rc.capitalistRent_B})"
  IO.println s!"          判定: isRegimeCoexistenceStable = True (キュレーター流出なし・大衆離脱なし)"
  let rc_drain := sampleExcessiveEquality
  IO.println s!"        過度な平等化相 (eq={rc_drain.eqOutcome}): 体制Aキュレーター={curPayoffA rc_drain} < 体制B転向={curPayoffB rc_drain - rc_drain.C_switch} -> 体制Bへ人材流出 (Brain Drain)"
  let rc_rent := sampleExtremeRentB
  IO.println s!"        過度な市場独占相 (Rent_B={rc_rent.capitalistRent_B}): 体制B大衆={consPayoffB rc_rent} < 体制A転向={consPayoffA rc_rent - rc_rent.C_switch} -> 体制Aへ大衆流出 (Exodus)"
  -- Section 9
  IO.println "[Sec 9] アルゴリズム統治 (体制A) vs 評価文字化・信用取引 (体制T) の連続競争動学:"
  let p9 := sampleTextTradeVsAlgo
  IO.println s!"        ① 基準共存均衡 (deg={p9.degRate}, α={p9.alpha_text}, μ={p9.mu_trade}):"
  IO.println s!"          単位効用: u_A={unitPayoffA p9}, u_T={unitPayoffT p9} (Δu={payoffDiff p9})"
  IO.println s!"          連続的リソース最適配分: 体制Aシェア w*=58%, 体制Tシェア (100-w*)=42% [内点均衡成立]"
  let p9_deg := sampleHighDegCrisis
  IO.println s!"        ② 情報劣化危機相 (deg={p9_deg.degRate}): u_A={unitPayoffA p9_deg} > u_T={unitPayoffT p9_deg} [文字情報風化・体制Aへ大シフト]"
  let p9_boom := sampleHighLiquidityBoom
  IO.println s!"        ③ 高流動性好況相 (deg={p9_boom.degRate}, α={p9_boom.alpha_text}, μ={p9_boom.mu_trade}): u_T={unitPayoffT p9_boom} > u_A={unitPayoffA p9_boom} [流動性プレミアム・体制T局所優位]"
  -- Section 10
  IO.println "[Sec 10] 汎用政治体制の動的競争モデル (Generic Regime Competition):"
  let w_algo := genericRegimeWelfare genericAlgorithmic
  let w_txt := genericRegimeWelfare genericTextTrade
  let w_cap := genericRegimeWelfare genericCapitalism
  let w_law := genericRegimeWelfare genericRuleOfLaw
  IO.println s!"        統一社会純厚生: W(Algo)={w_algo} > W(TextTrade)={w_txt} > W(Market)={w_cap} > W(Law)={w_law}"
  IO.println s!"        体制選択判定 (C_switch=20): Choice(Algo vs Market)={regimeChoiceShare w_algo w_cap 20} (Algo優位)"
  IO.println s!"        ロックイン判定: Choice(Market vs Algo, C_switch=150)={regimeChoiceShare w_cap w_algo 150} (高移動コストによるロックイン)"
  -- Section 11
  IO.println "[Sec 11] 生命発生から資本主義・民主主義・タグ通貨への大統一進化動学:"
  let w_abio := evolutionaryFitness envAbiogenesis
  let w_gene := evolutionaryFitness envGeneticEvolution
  let w_capi := evolutionaryFitness envCapitalistIndustrial
  let w_demo := evolutionaryFitness envDemocraticKnowledge
  let w_tagc := evolutionaryFitness envTagCurrencyNetwork
  IO.println s!"        ① 生命初期(Abiogenesis): 物理先駆者=2%, 共有なし, W={w_abio} (資本={capitalSurplus envAbiogenesis}, 民主={democraticSurplus envAbiogenesis}, タグ={tagCurrencySurplus envAbiogenesis} [全制度未成立])"
  IO.println s!"        ② 遺伝代謝(Genetic): 物理先駆者=15%, DNA記録, W={w_gene} (遺伝的代謝固定化)"
  IO.println s!"        ③ 近代資本主義(Capitalism): 物理先駆者=30%, 印刷/簿記, W={w_capi} (S_cap={capitalSurplus envCapitalistIndustrial} > 0 [資本主義自発的創発])"
  IO.println s!"        ④ 大衆民主主義(Democracy): 物理先駆者=50%, 教育/包摂85%, W={w_demo} (S_dem={democraticSurplus envDemocraticKnowledge} > 0 [民主主義自発的創発])"
  IO.println s!"        ⑤ タグ通貨経済(Tag Currency): 物理先駆者=70%, 暗号台帳, W={w_tagc} (S_tag={tagCurrencySurplus envTagCurrencyNetwork} > 0 [タグ通貨自発的創発・最大余剰])"
  IO.println s!"        統一適応度序列: W(Abiogenesis)={w_abio} < W(Genetic)={w_gene} < W(Capitalism)={w_capi} < W(Democracy)={w_demo} < W(TagCurrency)={w_tagc}"
  IO.println "======================================================================"
  IO.println " 全セクション (Sec 0〜11) の定理群が Lean 4 型検査により検証されました。"
