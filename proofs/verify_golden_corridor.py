from z3 import *


def verify_extended_phase_transitions():
  print("=" * 75)
  print(
      " 拡張評価システム：ギルド継承 vs 自由競争 vs 廃墟化均衡の Z3 自動検証"
  )
  print("=" * 75)

  # Z3 Real変数の定義
  lam_inst = Real("lambda_inst")  # 計画的減衰率 (0, 1)
  nu_dep = Real("nu_depart")  # 検索離れ・不可逆離脱率 [0, 1)
  alpha_log = Real("alpha_log")  # 記録の公開度 [0, 1]
  alpha_mech = Real("alpha_mech")  # 管理手段の公開度 [0, 1]
  gamma_guild = Real("gamma_guild")  # ギルド的閉鎖性・相互監視度 [0, 1]
  c_destroy = Real("c_destroy")  # 記録抹消・解体コスト >= 0

  # 基本的な公理（定義域の制約）
  domain_axioms = [
      lam_inst > 0.02,
      lam_inst < 0.98,
      nu_dep >= 0.0,
      nu_dep < 0.98,
      alpha_log >= 0.0,
      alpha_log <= 1.0,
      alpha_mech >= 0.0,
      alpha_mech <= 1.0,
      gamma_guild >= 0.0,
      gamma_guild <= 1.0,
      c_destroy >= 0.1,
  ]

  # -------------------------------------------------------------------------
  # 各体制の成立・不成立を規定する数理制約の定義
  # -------------------------------------------------------------------------

  # ① 自由競争・黄金の回廊（Constitutional Turnover: C）の成立条件
  # - 検索離れが許容範囲内、公開度が高く検証可能、減衰率が適切な帯域にある
  cond_constitutional_turnover = And(
      nu_dep < 0.55,
      alpha_log >= 0.4,
      alpha_mech >= 0.4,
      lam_inst >= 0.15 + 0.3 * nu_dep,
      lam_inst <= 0.80 - 0.25 * alpha_log,
  )

  # ② ギルド的継承モデル（Guild Succession: S_guild）の成立条件
  # - 公開度や検証技術が低くても（alpha_log が低くても）、閉鎖的相互監視(gamma_guild)が高ければ
  #   外部からのゲーミングを防ぎ、ローカルな信頼と安定を維持できる。ただし広域流通価値は限定的。
  cond_guild_succession = And(
      gamma_guild >= 0.65,  # 高いギルド的閉鎖性・相互監視
      alpha_log <= 0.5,  # グローバルな検証インフラは未熟でもよい
      nu_dep < 0.60,  # ローカルな検索者が維持されている
  )

  # ③ 破壊的リセット（Destructive Reset: D）が優位になる条件
  # - 既得権と古い記録が硬直して新陳代謝が止まり、かつ破壊コストが低く（c_destroy が安い）、
  #   独占レントを狙う勢力Dにとって攻撃の採算が合う状態。
  cond_destructive_reset = And(
      nu_dep >= 0.30,
      nu_dep < 0.75,
      alpha_log < 0.35,  # 記録が分散せず特定箇所にあるため破壊しやすい
      c_destroy <= 2.5,  # 破壊コストが比較的低い
      Or(lam_inst < 0.15, lam_inst > 0.85),  # 減衰率の不全（硬直または崩壊）
  )

  # ④ 完全放置・廃墟化均衡（Abandonment & Ruin: A / Ghost Archive）の成立条件
  # - 不可逆な検索離れが極限まで進み（nu_dep >= 0.75）、かつ公開度が高いために
  #   過去ログの解体・消去コスト c_destroy が高止まりし、誰のインセンティブも満たさず死滅する状態。
  cond_abandonment_ruin = And(
      nu_dep >= 0.75,  # 検索者の永久離脱・不可逆離脱
      c_destroy >= 3.0,  # 分散ログの消去コストの下限硬直
      alpha_log >= 0.5,  # 記録が強固に分散公開されているため更地にしにくい
  )

  # -------------------------------------------------------------------------
  # 検証シナリオ 1: 「ギルド的継承」が最適な防壁として機能する領域の探索 (SAT)
  # -------------------------------------------------------------------------
  s1 = Solver()
  s1.add(domain_axioms + [cond_guild_succession, Not(cond_constitutional_turnover)])

  print(
      "\n[検証 1] 「ギルド的継承モデル」が自由競争の不可能な環境で成立する条件の探索:"
  )
  if s1.check() == sat:
    m = s1.model()
    print("  -> 【判定: SAT】 ギルド的継承が最適防壁となるパラメータの具体例:")
    print(f"     - ギルド閉鎖性 (gamma_guild) = {m[gamma_guild]}")
    print(f"     - 記録の公開度 (alpha_log)   = {m[alpha_log]}")
    print(f"     - 検索離れ率   (nu_depart)   = {m[nu_dep]}")
  else:
    print("  -> 【判定: UNSAT】")

  # -------------------------------------------------------------------------
  # 検証シナリオ 2: 「廃墟化均衡 (Ghost Archive)」の不可避性の証明 (SAT)
  # -------------------------------------------------------------------------
  s2 = Solver()
  s2.add(
      domain_axioms
      + [
          cond_abandonment_ruin,
          Not(cond_constitutional_turnover),
          Not(cond_destructive_reset),
      ]
  )

  print(
      "\n[検証 2] 「強固な公開性(alpha_log)が仇となり、破壊すらできず廃墟化する均衡(A)」の証明:"
  )
  if s2.check() == sat:
    m = s2.model()
    print("  -> 【判定: SAT (廃墟化均衡の存在証明)】")
    print(f"     - 検索離れ率 (nu_depart)  = {m[nu_dep]}")
    print(f"     - 記録の公開度 (alpha_log) = {m[alpha_log]}")
    print(f"     - 解体コスト   (c_destroy) = {m[c_destroy]}")
    print(
        "     -> 考察: 記録が分散公開されすぎて消去コスト c_destroy が高く、"
    )
    print(
        "        かつ検索者が去った結果、誰も直さず誰も壊せない『亡霊アーカイブ』が数学的に確定します。"
    )
  else:
    print("  -> 【判定: UNSAT】")

  # -------------------------------------------------------------------------
  # 検証シナリオ 3: 5つの相（憲法体制C・ギルド体制・破壊的リセットD・廃墟化A）の排他性・網羅性チェック
  # -------------------------------------------------------------------------
  s3 = Solver()
  # 全ての相のいずれにも属さない「定義の抜け穴（バグ）」が存在するかどうかを検証
  s3.add(domain_axioms)
  s3.add(
      Not(
          Or(
              cond_constitutional_turnover,
              cond_guild_succession,
              cond_destructive_reset,
              cond_abandonment_ruin,
          )
      )
  )

  print("\n[検証 3] 理論モデルの抜け穴（どの相にも分類されない異常領域）の網羅的探索:")
  if s3.check() == sat:
    m = s3.model()
    print(
        "  -> 【警告: 抜け穴発見】どの相にも属さない特異なパラメータ領域が存在します:"
    )
    print(f"     {m}")