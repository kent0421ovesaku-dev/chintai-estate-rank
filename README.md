# 賃貸等不動産 含み益ランキング

東証上場企業（不動産業除く）の「賃貸等不動産の時価等に関する事項」を自動取得し、含み益ランキングを生成するシステム。

## 機能

- EDINETから有価証券報告書を自動取得
- iXBRL形式の財務諸表から賃貸等不動産の帳簿価額・時価を抽出
- 業種分類、単位統一（百万円）、バリデーション処理
- インタラクティブなHTMLレポート生成（検索・ソート・フィルタ機能付き）

## 必要環境

- Python 3.8+
- EDINET APIキー

## インストール

```bash
pip install -r requirements.txt
```

## 環境変数の設定

EDINET APIキーを環境変数として設定してください：

```bash
# Bash/Zsh の場合
export EDINET_API_KEY="your_api_key_here"

# または .env ファイルに記載して source で読み込み
echo 'export EDINET_API_KEY="your_api_key_here"' >> ~/.bashrc
source ~/.bashrc
```

**重要**: APIキーはコード内に直接書かず、環境変数で管理してください。

## 使用方法

```bash
# 1. 企業リスト取得（初回・年次更新時）
python main.py --fetch-companies

# 2. 有報解析・ランキング生成
python main.py --run

# 3. 中断時の再開
python main.py --resume
```

## 出力

- `output/index.html` - インタラクティブなランキング表
- `output/results.csv` - 生データ（CSV形式）
- `data/target_companies_dynamic.json` - 対象企業マスター

## データソース

- EDINET API v2
- 対象：東証上場企業（不動産業を除く）
- 期間：過去14ヶ月分の有価証券報告書
