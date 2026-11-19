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
  IO.println "======================================================================"
  IO.println " 全セクション (Sec 0〜7) の定理群が Lean 4 型検査により検証されました。"
