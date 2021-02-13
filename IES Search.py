# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# 配光データの類似度計算

# 処理を速くするため、なるべくNumpyを使用
# Pandasは、csvの読み込みと書き出しが必要な場合や
# データの処理が複雑で、整理したい場合に限る
# 特に、Pandasデータフレームを1行ずつ、付け足す処理は避ける
# リストへのアクセスやappendは、Pythonの方が、Numpyより速い
# ravelの方がfalttenより速い、コピーなし

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# Pythonの開始

# cd /Users/takeosugamata/python_env
# source py3env/bin/activate

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# ライブラリーのインポート
import codecs                                                                   # codecsは、UnicodeDecodeErrorを避けるため
import copy                                                                     # 複合オブジェクトの深いコピーのため
import glob
import itertools
import json
import math
import matplotlib.pyplot as plt
import numpy   as np
import pandas  as pd
import os
import pandas  as pd
from   pathlib import Path
import quaternion
import re                                                                       # 正規表現
import requests
import seaborn as sns                                                           # ヒートマップ用
import shutil
import sqlite3
from   statistics import median, mean
import string
import sys
import time                                                                     # 処理速度の計測
import traceback                                                                # 例外処理
import types
import urllib as ul

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# 環境変数の設定

pd.options.display.float_format = '{:.5f}'.format                               # データフレームの数値を小数点第５位まで表記
np.set_printoptions(suppress=True)                                              # 少数点表記

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# データベース・フォルダの構成

# Funnel/                       DATABASE PATH
#   |__ Database.sqlite         SQLITE_PATH
#   |__ 1 Manufacturer/         MANUFACTURER_PATH
#   |   |__ Manufacturer.csv
#   |   |__ IES/                * 古いものはzipする
#   |   |__ Photos/
#   |__ ...
#   |__ 2 Cluster/              CLUSTER_PATH
#   |   |__ Cluster Seeds/      CLUSTER_SEED_PATH
#   |   |__ Graph/              CLUSTER_GRAPH_PATH
#   |__ 3 Query/                QUERY_PATH
#   |   |__ Query.ies
#   |__ 4 Plot/                 PLOT_PATH
#   |   |__ Plot.ies
#   |__ 5 Error Log/            ERROR_PATH

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# グローバル変数の設定

# パスの設定
DATABASE_PATH      = '/Users/takeosugamata/Downloads/Funnel/'
SQLITE_PATH        = '/Users/takeosugamata/Downloads/Funnel/Database.sqlite'
MANUFACTURER_PATH  = '/Users/takeosugamata/Downloads/Funnel/1 Manufacturer/'
CLUSTER_PATH       = '/Users/takeosugamata/Downloads/Funnel/2 Cluster/'
CLUSTER_SEED_PATH  = '/Users/takeosugamata/Downloads/Funnel/2 Cluster/Seed/'
CLUSTER_GRAPH_PATH = '/Users/takeosugamata/Downloads/Funnel/2 Cluster/Graph/'
QUERY_PATH         = '/Users/takeosugamata/Downloads/Funnel/3 Query/'
PLOT_PATH          = '/Users/takeosugamata/Downloads/Funnel/4 Plot/'
ERROR_PATH         = '/Users/takeosugamata/Downloads/Funnel/5 Error Log/'

# SQliteへの接続
con                = sqlite3.connect(SQLITE_PATH)
cur                = con.cursor()

# データベースの列のインデックス番号                                                  # 列の追加や削除に伴い、カンマの有無を確認
COLUMNS      = [
                'Cluster No',                                                   # 列1
                'IES',                                                          # 列2
                'Diff',                                                         # 列3
                'Photo Filepath',                                               # 列4
                'Type',                                                         # 列5
                'Ceiling Mounted',                                              # 列6
                'Wall Mounted',                                                 # 列7
                'Floor Mounted',                                                # 列8
                'FFE Mounted',                                                  # 列9
                'Other Mounted',                                                # 列10
                'Fixing',                                                       # 列11
                'Manufacturer',                                                 # 列12
                'Model Name',                                                   # 列13
                'Model Code',                                                   # 列14
                'Light Source',                                                 # 列15
                'Socket',                                                       # 列16
                'Min Voltage',                                                  # 列17
                'Max Voltage',                                                  # 列18
                'Wattage',                                                      # 列19
                'Luminous Flux',                                                # 列20
                'Beam Angles',                                                  # 列21
                'Max Luminous Intensity',                                       # 列22
                'Lowerst Color Temperature',                                    # 列23
                'Highest Color Temperature',                                    # 列24
                'IES Color Temperature IES',                                    # 列25
                'Color',                                                        # 列26
                'Color Rendering',                                              # 列27
                'Lamp Life',                                                    # 列28
                'IP Rate',                                                      # 列29
                'Dimming',                                                      # 列30
                'Download URL',                                                 # 列31、ダウンロードURLのある親のページのURL
               ]

IES_COLUMNS        = [str(i) +'-'+ str(j) 
                      for i in list(range(0,361,10))                            # 列26-列1394の1369列
                      for j in list(range(0,181,5))]
DIFF_THETA_COLUMNS = ['theta_' + str(i) +'-'+ str(j)                            # 列1395-列2762の1368列
                      for i in list(range(0,351,10)) 
                      for j in list(range(0,186,5))]
DIFF_PHI_COLUMNS   = ['phi_'   + str(i) +'-'+ str(j)                            # 列2763-列4057の1295列
                       for i in list(range(0,361,10)) 
                       for j in list(range(5,176,5))]

DIFF_COLUMNS       = DIFF_THETA_COLUMNS + DIFF_PHI_COLUMNS

FILE_NAME         = 0
CLUSTER_NO        = 1
IES               = 2
DIFF              = 3
MANUFACTURER      = 12
MODEL_NAME        = 13
MODEL_CODE        = 14
LUMEN             = 20
DOWNLOAD_URL      = 31

# 色のリスト
COLOR_LIST = ['gold', 'orange', 'red', 'green', 'blue', 'purple', 'hotpink',
              'yellowgreen', 'cyan', 'darkviolet', 'magenta', 'chartreuse',
              'chocolate','olive','grey']

# 極座標のグリッドのラベル
THETA_GRIDS        = np.linspace(0,360,8,endpoint=False)
THETA_GRIDS_LABELS = ["0", "45°", "90°>", "135°", "180°", "135°", "90°", "45°"]
PHI_GRIDS_LABELS   = ["0", "45°", "90°", "135°", "180°", "225°", "270°", "315°"]

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# 変数のサイズを表示

def show_variable_size():
    
    print('--------------------'*4)
    print('{:<30}{:<10}'.format('Variable Name','Size'))
    print('')
    
    variable_names = []
    for variable_name, v in globals().items():
        
        if  (hasattr(v, 'size')                                                 # アンダースコアで始まらない、かつ
             and not variable_name.startswith('_')                              # アンダースコアで始まらない、かつ
             and not isinstance(v,types.ModuleType)                             # モデュールでないなら
            ):
             print('{:<30}{:<10}'.format(variable_name, str(v.size)))
             
        elif (hasattr(v, '__sizeof__')                                          # サイズ属性を持ち、かつ
             and hasattr(v, '__len__')                                          # 長さ属性を持ち、かつ
             and not variable_name.startswith('_')                              # アンダースコアで始まらない、かつ
             and not isinstance(v,types.ModuleType)):                           # モデュールでないなら
             
             print('{:<30}{:<10}'.format(variable_name, 
                                           str(sys.getsizeof(v))))

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# 拡張子iesを小文字に統一

def ies_to_lowercase(folder_path):
    for f in Path(folder_path).rglob('*.IES'):                                  # rglobは再起的な検索、拡張子が大文字の場合
        if  os.path.isfile(f):
            shutil.move(f, f.with_name(f.stem+'.ies'))                          # shutil.move使用、os.renameは失敗の可能性あり
            print('change ' + f.name)                                           # PosixPath型なので、nameプロパティでファイル名取得

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# 白熱電球のIES

def make_bulb():
    theta_label = list(range(0,181,1))
    phi_label   = list(range(0,361,1))
    cd = 1500 / (4 * np.pi)                                                     # 1500lmを全方位の立体角4πで割る
    bulb = pd.DataFrame(np.ones((361,181))*cd, 
                        index=phi_label,columns=theta_label)
    return bulb
    
# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# 配光データの読み込み

def read_ies_raw(file_path):
    
    # CSVの読み込み
    csv = []
    with codecs.open(file_path,'r','utf-8','ignore') as f:
        for line in f:                                                          # 一行ずつ読み込み
            csv.append(line)                                                    # リストに追加する
    csv = [c.strip() for c in csv]                                              # 文字列前後の空白を除く
    csv = [c for c in csv if c!='']                                             # 最後に空白行があると、データフレーム作成時、行ラベルと行数が合わない
    
    # 基本情報の取得
    manufac   = [c[9: ].strip()  for c in csv if c.startswith('[MANUFAC]')]     # [MANUFAC]で始まるなら、10文字目以降がメーカー名
    lumcat    = [c[8: ].strip()  for c in csv if c.startswith('[LUMCAT]')]      # [LUMCAT]で始まるなら、9文字目以降が照明器具カタログ情報
    luminaire = [c[11:].strip()  for c in csv if c.startswith('[LUMINAIRE]')]   # [LUMINAIRE]で始まるなら、12文字目以降が照明器具情報
    lamp      = [c[6: ].strip()  for c in csv if c.startswith('[LAMP]')]        # [LAMP]で始まるなら、7文字目以降が光源情報
    # [KEYWORD]の直後に空白がある場合とない場合がある
    # [KEYWORD]の後の文字列を全部取得して、前後の空白を除く
    
    manufac   = ['-' if ((manufac   ==[]) or (manufac   ==[''])) else manufac   [0]] [0] # 空あるいは空文字なら、ハイフン、あるなら、そのまま、文字列を抽出
    lumcat    = ['-' if ((lumcat    ==[]) or (lumcat    ==[''])) else lumcat    [0]] [0]
    luminaire = ['-' if ((luminaire ==[]) or (luminaire ==[''])) else luminaire [0]] [0]
    lamp      = ['-' if ((lamp      ==[]) or (lamp      ==[''])) else lamp      [0]] [0]
    
    tilt      = [c for c in csv if c.startswith('TILT=')][0]                    # TILT=で始まるなら
    i         = csv.index(tilt)                                                 # TILT=が記載されている行、以後iはcsvの行を表す
    
    # TILT行に続く10項目
    # ランプの数、ランプ当たりの光束、掛け値、鉛直角度数、水平角度数などは
    # 同じ行に書いてある場合がほとんどだが、改行している場合もある
    
    i += 1                                                                      # TILTの次の行
    line_after_tilt  = csv[i].split()                                           # TILT行の次の行の文を、空白区切りでリスト化
    # 定義によると、区切り文字は、カンマ、空白（複数可）、改行文字が可
    # 但し、今の所、空白のみ
    
    while len(line_after_tilt) < 10:                                            # 10個の要素が集まるまで
        i += 1                                                                  # 次の行に移動し
        line_after_tilt += csv[i].split()                                       # 要素を追加していく
    
    # メーカー側の誤入力の例
    # ランプの数、鉛直角度数、水平角度数、配光型、単位型は整数のはずが小数
    # 文字列>整数ではなく、文字列>小数>整数とする  （Koizumi)
    # 掛け値が0で、配光が0になる、本来は1と思われる (Toshiba)
    
    no_of_lamps      = int(float(line_after_tilt[0]))                           # ランプの数、0番目の要素、整数化
    lumens_per_lamp  =     float(line_after_tilt[1])                            # ランプ当たりのルーメン、1番目の要素、小数化
    multiplier       =     float(line_after_tilt[2])                            # 掛け値、2番目の要素、小数化
    no_of_theta      = int(float(line_after_tilt[3]))                           # 鉛直角度の数、3番目の要素、整数化
    no_of_phi        = int(float(line_after_tilt[4]))                           # 水平角度の数、4番目の要素、整数化
    photometric_type = int(float(line_after_tilt[5]))                           # 測光型、1=TypeC、2=TypeB、3=TypeA
    
    # 器具消費電力
    i += 1
    line_for_watts   = csv[i].split()
    wattage = float(line_for_watts[2])                                          # 器具消費電力、2番目の要素、整数化
    if wattage == 0:                                                            # 器具消費電力が0の場合
        wattage = '?'                                                           # 不正確だと思われるので、?を代入
    
    # 鉛直角度ラベルの読み込み
    i += 1                                                                      # 鉛直角度ラベルの開始行
    theta_label = []                                                            # 鉛直角度ラベルの空のリストを作成
    while len(theta_label) < no_of_theta:                                       # 要素数が鉛直角度数の未満の間、角度数が不正確な場合がある
        theta_label += csv[i].split()                                           # 各行の文字列をリスト化し追加していく
        i += 1
    theta_label = list(map (float, theta_label))                                # リストなので、MAP関数により、小数化
    
    # 水平角度ラベルの読み込み
    phi_label = []                                                              # 水平角度ラベルの空のリストを作成
    while len(phi_label) < no_of_phi:                                           # 要素数が水平角度数の未満の間、角度数が不正確な場合がある
        phi_label  += csv[i].split()                                            # 各行の文字列をリスト化し追加していく
        i += 1
    phi_label   = list(map (float, phi_label))                                  # リストなので、MAP関数により、小数化
    
    # 配光データの読み込み
    ies_values_array = []                                                       # 配光データの空のリストを作成
    for j in range(no_of_phi):                                                  # 水平角度数だけ繰り返す
        ies_values_list = []                                                    # 各水平角度の配光データの空のリストを作成
        while len(ies_values_list) != no_of_theta:                              # 要素数が鉛直角度数と一致するまで
            ies_values_list += csv[i].split()                                   # 各行の文字列をリスト化し追加していく
            i += 1
        ies_values_list = list(map(float, ies_values_list))                     # リストなので、MAP関数により、小数化
        ies_values_array.append(ies_values_list)                                # 各水平角度の配光データを追加
    
    ies_values = np.array(ies_values_array)                                     # 次のブロードキャスト計算のため配列化
    ies_values = ies_values * multiplier                                        # 光度*掛け値、lm当たりの光度になってる場合があるため
    # データフレーム後の計算より４倍速い
    
    ies_raw = pd.DataFrame(ies_values,index=phi_label,columns=theta_label)
    
    # TILTの次の行の角度数や角度ラベルの数が間違ってても
    # SQliteに読み込まれ、後の計算でエラーを起こすことがある
    if not (no_of_theta == len(theta_label)
       and  no_of_phi   == len(phi_label)
       and  theta_label[0 ] in [-90, 0              ]
       and  theta_label[-1] in [     0, 90, 180     ]
       and  phi_label  [0 ] in [-90, 0              ]
       and  phi_label  [-1] in [     0, 90, 180, 360]):
       ies_raw = None                                                           # Noneを代入し、次の標準化でエラーを起こす
    
    return manufac, lumcat, luminaire, lamp, wattage, ies_raw

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# 配光データの読み込み(LDT)

def read_ldt_raw(file_path):
    
    # CSVの読み込み
    csv = []
    with codecs.open(file_path,'r','utf-8','ignore') as f:
        for line in f:                                                          # 一行ずつ読み込み
            csv.append(line)                                                    # リストに追加する
    csv = [c.strip() for c in csv]                                              # 文字列前後の空白を除く、iesと異なり空白行は除かない
    
    # 照明器具メーカー、型名、型番
    manufac         = csv[0]                                                    # 1行目、メーカー名
    luminaire       = csv[8]                                                    # 8行目、型名
    lumcat          = csv[9]                                                    # 9行目、型番
    
    # 鉛直と水平角度の数
    no_of_theta     = int(csv[5])                                               # 5行目、鉛直角度の数、整数化
    no_of_phi       = int(csv[3])                                               # 3行目、水平角度の数、整数化、360度を含まない
    
    n = int(csv[25])                                                            # 25行目、標準時のランプの数、整数化
    if n == 1:                                                                  # n値が1ならば
        absolute_photometry = True                                              # 絶対測光
    
    lamp            = csv[26 + n]                                               # 26行目 + n行、複数の場合もあるが、ひとつ目のみ
    
    wattage = csv[26 + (n*5) : 26 + (n*6)]                                      # 各光源の消費電力(文字列)のリスト、['100.0', '50.0'...]
    wattage = list(map(float, wattage))                                         # 各光源の消費電力(小数)のリスト、[100.0, 50.0...]
    wattage = sum(wattage)                                                      # 各光源の消費電力の合計値
    
    # 行ラベル（水平角度）の読み込み
    lumens     = list(map(float, (csv[26 + (n*2) : 26 + (n*3)])))               # 各ランプごとの光束
    lumen      = sum(lumens)                                                    # 光束の合計値
    multiplier = lumen / 1000                                                   # klmに変換
    
    # 行ラベル（水平角度）の読み込み
    i = 25 + (n*6) + 10 + 1                                                     # 25行目 + n*6行 + 10行(DR)の次の行
    phi_label = list(map(float, csv[i : i+no_of_phi]))                          # リストなので、MAP関数により、小数化
    phi_label += [360]                                                          # iesに合わせ、360度を追加
    
    # 列ラベル(鉛直角度)の読み込み
    i = i + no_of_phi                                                           # 鉛直角度の開始行
    theta_label = list(map(float, csv[i : i+no_of_theta]))                      # リストなので、MAP関数により、小数化
    
    # 配光データの読み込み
    ies_values_array = []                                                       # 配光データの空のリストを作成
    for j in range(no_of_phi):                                                  # 水平角度数だけ繰り返す、水平角度分ない場合がある
        i = i + no_of_theta
        ies_values_list = list(map(float, csv[i : i+no_of_theta]))              # リストなので、MAP関数により、小数化
        if ies_values_list != []:                                               # 値がある場合
            ies_values_array.append(ies_values_list)                            # 値を追加
        else:                                                                   # 値がない場合
            ies_values_array.append(ies_values_array[0])                        # 各水平角度の配光データを追加
    ies_values_array.append(ies_values_array[0])                                # φ=0度の配光データをφ=360度の配光データとして追加
    
    ies_values = np.array(ies_values_array)                                     # 次のブロードキャスト計算のため配列化
    ies_values = ies_values * multiplier                                        # 光度*掛け値、klm当たりの光度になってる
    # データフレーム後の計算より４倍速い
    
    ies_raw = pd.DataFrame(ies_values,index=phi_label,columns=theta_label)
    
    return manufac, lumcat, luminaire, lamp, wattage, ies_raw

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# 配光データの読み込み・標準化(IESとLDT)

def read_ies(file_path):                                                        # read_ies_raw関数を使用
    
    # ファイルの種類で場合分け
    file_extention = file_path[-4:]                                             # ファイルの拡張子を取得
    
    if   file_extention == '.ies' or file_extention =='.IES':                   # ies ファイルなら
         manufac, lumcat, luminaire, lamp, wattage, ies_raw = \
         read_ies_raw(file_path)    # iesを読み込み、データフレーム化
    elif file_extention == '.ldt' or file_extention =='.LDT':                   # ldt ファイルなら
         manufac, lumcat, luminaire, lamp, wattage, ies_raw = \
         read_ldt_raw(file_path)    # ldtを読み込み、データフレーム化
        
    else:                                                                       # 配光データでないなら
         print('file is neither ies nor ldt')
    
    '''
    # 稀に最後の値が0でない場合がある
    # 0でないと、欠損値の補完が正しく行われない
    for row in ies_raw.iterrows():                                              # 行ごとに繰り返す、返り値はタプル
        if  row[1].values[-1]!=0:                                               # ２つ目の要素がシリーズ、稀に最後の値が0でない場合がある
            ies_raw.loc[:,ies_raw.columns[-1]+0.5]=0                            # 0.5度次の列を作成し、0を入力
            break
    '''
    
    # 鉛直角度
    # TypeA 0度から90度 or -90度から90度
    # TypeB 0度から90度 or -90度から90度
    # TypeC 0度から90度 or  90度から180度 or 0度から180度
    # TypeCが一番多い
    
    if  ies_raw.columns.min() == -90:                                           # 鉛直角度が-90度で始まる場合
        ies_raw.columns = ies_raw.columns + 90                                  # 0度始まりにする
    
    # 水平角度
    # TypeA 0度から90度 or -90度から90度
    # TypeB 0度から90度 or -90度から90度
    # TypeC 0度のみ or 0度から90度 or 0度から180度 or 0度から360度 
    # TypeCが一番多い
    
    if  ies_raw.index.min() == -90:                                             # 水平角度が-90度で始まる場合
        ies_raw.index = ies_raw.index + 90                                      # 0度始まりにする
    
    # 水平角が0度で省略、1度から360度を補完
    if  ies_raw.index.max() == 0: 
        pass
    
    # 水平角が90度で省略、91度から180度を補完
    if  ies_raw.index.max() == 90:                                              # 最大水平角度が90度の場合
        ies_mirrored = ies_raw.iloc[:-1,:]                                      # 90度の行を除く        例: 0,1,,,89,90 >> 0,1,,,89
        ies_mirrored = ies_mirrored[::-1]                                       # 行の順番を逆にする     例: 0,1,,,89 >> 89,,,1,0
        ies_mirrored_index = 180 - ies_mirrored.index                           # 反転した行ラベルを作成、例: 180-89,,,180-0 >> 91,,,180
        ies_mirrored.index = ies_mirrored_index                                 # 行ラベルを変更
        ies_raw = ies_raw.append(ies_mirrored)
    
    # 水平角が180度で省略、181度から360度を補完
    if  ies_raw.index.max() == 180:                                             # 最大水平角度が180度の場合
        ies_mirrored = ies_raw.iloc[:-1,:]                                      # 180度の行を除く       例: 0,1,,,179,180 >> 0,1,,,179
        ies_mirrored = ies_mirrored[::-1]                                       # 行の順番を逆にする     例: 0,1,,,179 >> 179,,,1,0
        ies_mirrored_index = 360 - ies_mirrored.index                           # 反転した行ラベルを作成、例: 360-179,,,360-0 >> 181,,,360
        ies_mirrored.index = ies_mirrored_index                                 # 行ラベルを変更
        ies_raw = ies_raw.append(ies_mirrored)
        
    # iesを代入する標準データフレームを作成
    theta_label = np.arange(0,180.5,0.5)                                        # 列ラベルの作成、0.5度刻み、値は小数
    phi_label   = np.arange(0,360.5,0.5)                                        # 行ラベルの作成、0.5度刻み、値は小数
    ies = pd.DataFrame(0, columns=theta_label, index=phi_label)                 # 空のデータフレーム
    
    # θ方向は、2.5度刻みで測定したiesがある
    # φ方向は、22.5度刻みで測定したiesがある
    # 標準形式の角度を1度刻みにすると
    # 0度、5度...
    
    # θ方向は、0.1度刻みで測定したiesがある(例：カラーキネティクス)
    # 標準形の0.5度刻みにない角度があると
    # データフレームを合成時、721行 x 361列より大きくなり、エラー発生
    # 標準形の角度と重複するもののみ抽出する
    # 例えば、0.1度刻みなら、0度、0.5度、1度...
    # 例えば、0.2度刻みなら、0度、1度...
    # 0.2度はまだないが、0.4度と0.6度の情報は失われ、0.5度を再計算
    
    ies_raw = ies_raw.loc[np.intersect1d(ies_raw.index, phi_label),
                          np.intersect1d(ies_raw.columns, theta_label)]         # 標準形にある列と行のみ抽出、intersect1dは重複要素の抽出
    
    # iesを代入し、欠損値処理
    ies = ies + ies_raw                                                         # 配光データを標準化。データのある部分は数字、ない部分はNan
    
    # 721行 x 361列 のデータフレーム
    #       0.0   0.5   1.0   ... 179.5 180.0
    #   0.0   -     -     -     -     -     -
    #   0.5   -     -     -     -     -     -
    #   1.0   -     -     -     -     -     -
    #   .     -     -     -     -     -     -
    #   .     -     -     -     -     -     -
    # 359.5   -     -     -     -     -     -
    # 360.0   -     -     -     -     -     -
    
    ies = ies.interpolate(method='linear',axis=1)                               # θ方向の欠損地を埋める、inplaceも試すが、速度変わらず
    ies = ies.iloc[:,range(0,361,2)]                                            # θ方向の次元の削減、0.5度から、1度刻みに
    
    # θ方向の次元削減してから、
    # φ方向の欠損値処理
    # 約2割速い
    
    ies = ies.interpolate(method='linear',axis=0)                               # φ方向の欠損地を埋める、inplaceも試すが、速度変わらず
    ies = ies.iloc[range(0,721,2),:]                                            # φ方向の次元の削減、0.5度から、1度刻みに
    
    # φ方向の次元削減してから、
    # 欠損値処理
    
    ies.fillna(0, inplace=True)                                                 # Nanを0に変換、fillnaは、再代入より、inplaceの方が速い
    
    # 361行 x 181列 のデータフレーム
    #       0.0   1.0   ... 180.0
    #   0.0   -     -     -     -
    #   1.0   -     -     -     -
    #   .     -     -     -     -
    #   .     -     -     -     -
    # 360.0   -     -     -     -
    
    ies.index   = [int(i) for i in ies.index  ]                                 # 水平角ラベルを整数化
    ies.columns = [int(c) for c in ies.columns]                                 # 鉛直角ラベルを整数化
    
    # 361行 x 181列 のデータフレーム
    #       0   1 ... 180
    #   0   -   -   -   -
    #   1   -   -   -   -
    #   .   -   -   -   -
    #   .   -   -   -   -
    # 360   -   -   -   -
    
    # 次元を標準化した後でないと、エラー
    rotation_angle = cal_direction(ies) * -1                                    # 照射方向を0度にするので、-1を掛ける
    ies = rotate_ies(ies, rotation_angle)                                       # 水平照射方向の回転
    
    return manufac, lumcat, luminaire, lamp, wattage, ies

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# 天頂と天底の重複を削除

def remove_duplicates(ies):
    
    # 次元の削減に対応
    # θとφの間隔を取得し
    # 代入には、ilocではなく、locを使用
    
    theta_interval, phi_interval = theta_phi_interval(ies) 
    ies.loc[phi_interval:,[0,180]] = 0                                          # θ=0度と180度の重複する値を0に

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# 天頂と天底の重複を復元

def restore_duplicates(ies):
    
    # 次元の削減に対応
    # θとφの間隔を取得し
    # 代入には、ilocではなく、locを使用
    
    theta_interval, phi_interval = theta_phi_interval(ies)
    ies.loc[phi_interval:,0  ] = ies.loc[0,0  ]                                 # θ=0度の0にした値を元に戻す
    ies.loc[phi_interval:,180] = ies.loc[0,180]                                 # θ=180度の0にした値を元に戻す

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# 配光データの一次元配列化(データフレームからシリーズ、次元削減に対応済み)

def two_to_one(ies):
    angle_label = [str(i)+'-'+str(j) for i in ies.index for j in ies.columns]   # 水平角度-鉛直角度を組み合わせたラベル、例: 270-90
    ies_flat = ies.values.ravel()                                               # データフレームを配列化、一次元化
    ies_1D   = pd.Series(ies_flat, index = angle_label)                         # シリーズ化
    return ies_1D

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# 配光データの二次元配列化(シリーズからデータフレーム、次元削減に対応済み)

def one_to_two(ies_1D):
    
    phi_max        = int(float(re.split('-',ies_1D.index[-1])[0]))              # 最後の行ラベルの-より前が最大水平角度、小数化し整数化
    theta_max      = int(float(re.split('-',ies_1D.index[-1])[1]))              # 最後の行ラベルの-より後が最大鉛直角度、小数化し整数化
    theta_interval = int(float(re.split('-',ies_1D.index[1])[1]))               # 2番目の行ラベルの-より後が鉛直角度間隔、小数化し整数化
    n = int(theta_max / theta_interval+1)                                       # 列の数、整数化、次元削減してなければ、n=181
    phi_interval   = int(float(re.split('-',ies_1D.index[(n+1)])[0]))           # 次の水平角度の行ラベルの-より前が間隔、小数化し整数化
    
    # 例:
    # 鉛直角度最大値が90度で、鉛直角度間隔が10度の場合
    # [0-10,0-20,0-30,0,40,0-50,0-60,0-70,0-80,0-90,10-0,...]
    # nは9で、次の水平角度は10番目から
    
    phi_label   = list(range(0, phi_max+1,   phi_interval))                     # 次元削減してなければ、[0,1,,,360]
    theta_label = list(range(0, theta_max+1, theta_interval))                   # 次元削減してなければ、[0,1,,,180]
    m = len(phi_label)                                                          # 行の数、次元削減してなければ、n=361
    ies = ies_1D.values.reshape(m,n)                                            # m x n の配列化
    ies = pd.DataFrame(ies, index=phi_label, columns=theta_label)               # データフレーム化
    
    return ies

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# 次元の削減（1度刻みの361x181データフレーム用）

# 引数のiesは、361行x181列、鉛直角度は0-180度まで1度刻み、水平角度は0-360度まで1度刻み
def reduce_dimensions(ies, theta_interval=1, phi_interval=1,                    # 引数のiesは、361行x181列
                           theta_max=180,    phi_max=360   ):                   # 鉛直角度0-180度まで1度刻み、水平角度0-360度まで1度刻み
    theta_label = range(0, theta_max + 1 , theta_interval)                      # 抽出する水平角度のインデックスのリスト
    phi_label   = range(0, phi_max + 1 , phi_interval)                          # 抽出する鉛直角度のインデックスのリスト
    ies_small = ies.iloc[phi_label, theta_label]                                # データの抽出
    return ies_small

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# 次元の削減（1度刻みの1x65341シリーズ用）
    
def reduce_dimensions_series(ies_1D, theta_interval=1, phi_interval=1,
                                     theta_max=180,    phi_max=360   ):
    # 一次元の値の列から何番目を抽出するか
    index_to_extract = []                                                       # 抽出するindexを格納するための空のリスト
    i = 0
    while i <= phi_max:                                                         # 水平角度の最大値まで繰り返す、これ以降iは水平角度
        index_each_phi = list(range(181*i, 181*i+theta_max+1, theta_interval))  # 各水平角度ごとの抽出するindex、stopの値は含まれない
        # 計算例:
        # 0-0,  0-45,   0-90,  0-135、  0-180、 1-0,    1-45,...
        # と鉛直角度45度、水平角度1度ごとに抽出する場合
        # 0番目, 45番目, 90番目, 135番目, 180番目, 181番目, 226番目,...
        # のindexを抽出することになる
        # 一定間隔ではないことに注意
        index_to_extract += index_each_phi
        i += phi_interval                                                       # 次の水平角度へ
    
    ies_small = ies_1D[index_to_extract]                                        # 抽出するインデックスのリストを与える
    
    return ies_small

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# 次元の削減（1度刻みの1(複数行）x65341データフレーム用）

def reduce_dimensions_df(ies_1D, theta_interval=1, phi_interval=1,
                                 theta_max=180,    phi_max=360):
    index_to_extract = np.array([])                                             # 抽出するindexを格納するための空のリスト
    i = 0
    while i <= phi_max:                                                         # 水平角度の最大値まで繰り返す、これ以降iは水平角度
        index_each_phi = list(range(181*i,181*i+theta_max+1,theta_interval))    # 各水平角度ごとの抽出するindex、stopの値は含まれない
        index_to_extract += index_each_phi
        i += phi_interval                                                       # 次の水平角度へ
    ies_small = ies_1D.iloc[:,index_to_extract]                                 # # 抽出するインデックスのリストを与える
    return ies_small

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# 配光データのθとφの間隔を取得

def theta_phi_interval(ies):
    theta_interval = ies.columns[1] - ies.columns[0]                            # 2番目の列名から1番目の列名の差がθの間隔
    phi_interval   = ies.index[1] - ies.index[0]                                # 2番目の行名から1番目の列名の差がφの間隔
    # iesのみなら、2番目の列名と行名を取得すればいいが
    # iesの差分データの場合、差の形式にする必要がある
    return theta_interval, phi_interval

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# 配光データのθとφの最大値取得

def theta_phi_maxl(ies):
    theta_max      = ies.columns[-1]                                            # 最後の列名がθの最大値
    phi_max        = ies.index[-1]                                              # 最後の行名がφの最大値
    return theta_max, phi_max

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# 最大光度の算出

def cal_cd_max(ies):
    
    # ピークが複数ある場合
    # そのうちの一つしか抽出できない
    # 測定誤差の影響を受ける可能性がある
    
    remove_duplicates(ies)                                                      # 最大光度が、天頂と天底の場合、φが重複するため
    
    ies_small = reduce_dimensions(ies, 5, 5, 180, 360)                          # 誤差の影響を減らすため、θ・φともに5度刻みに
    ies_small = ies_small[:-1]                                                  # φ=0度と重複するφ=360度を削除
    
    cd_max = ies_small.values.max()                                             # 配列化し、最大値を取得
    cd_max = int(round(cd_max, 0))                                              # 四捨五入し、整数化
    
    cd_max_id  = np.where(ies_small==cd_max)                                    # 最大光度のindex、φとθの２次元配列
    # 例: (array([0,36]), array([0,0]))
    cd_max_angles = list(map(lambda x: x*5, cd_max_id))                         # indexに、5度刻みを掛け、角度に
    # 例: (array([0,180]), array([0,0]))
    cd_max_id  = list(zip(*cd_max_angles))                                      # 引数に*を付けると、展開して引数に渡せる
    # 例: [(0,0),(0,180)]
    restore_duplicates(ies)                                                     # 天頂と天底の値を戻す
    
    return cd_max, cd_max_id

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# 配光データの水平照射方向の推定（1度刻みのデータフレーム)

def cal_direction(ies):
    
    # 局所的な誤差の影響を防ぐため
    # φ方向1/4区間を合計して比較
    # φ方向1/2区間の合計だと、
    # スプレッドの時に方向を特定できない
    
    # 照射方向の算出では
    # 0度と重複するため
    # 360度を削除
    
    # φ方向1/4の合計を算出
    ies_quarter_sums = []
    for i in range(0,360):                                                      # 0-359度まで繰り返す、360度は0度と重複
        ies_quarter_id = list(range(i-45, i+46))                                # [i,...,i+90]の91度分、奇数:-45度分+照射角度+45度分
        ies_quarter_id = [i % 360 for i in ies_quarter_id]                      # 360度以上で0から、例:i=300 [300..359,0,1...30]
        ies_quarter_sum = ies.iloc[ies_quarter_id, :].values.sum()              # i度から91度分を合計
        ies_quarter_sums.append(ies_quarter_sum)
    
    # φ方向1/4の合計の最大値を算出
    ies_quarter_sums = np.array(ies_quarter_sums)                               # 配列化、np.whereを使用するため
    directions = np.where(ies_quarter_sums == ies_quarter_sums.max())[0]        # 最大値の角度のリスト
    
    # 最大値の数で場合分け
    if   len(directions) >= 3:                                                  # 最大値が３つ以上の場合
            direction = 0                                                       # 方向性がないとし、照射方向を変えない
    
    elif len(directions) == 2:                                                  # 最大値が２つの場合
    
        # 角度がほぼ同じ側の場合
        # 差が170度以下
        if         directions[1]-directions[0] <= 170:
            direction = int(directions.mean())                                  # ２つの最大値の中間を照射方向
        # 差が190度以上
        if  190 <= directions[1]-directions[0]:
            direction = (int(directions.mean()) + 180) % 360                    # ２つの最大値の中間の反対側を照射方向
        
        # 角度がほぼ反対側の場合
        # 差が170度より上、190度より下
        if (170 < directions[1]-directions[0]
        and       directions[1]-directions[0] < 190):                           # 2つが反対向きの場合（スプレッドなど）
            direction = directions[0]                                           # 広い方の向き
    
    else:
            direction = directions[0]                                           # 最大値の方向を照射方向
    
    return direction

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# 照射方向の描画

def plot_direction(ies):
    
    # φ方向1/4の合計を算出
    ies_quarter_sums = []
    for i in range(0,360):                                                      # 0-359度まで繰り返す、360度は0度と重複
        ies_quarter_id = list(range(i-45, i+46))                                # [i,...,i+90]の91度分、奇数:-45度分+照射角度+45度分
        ies_quarter_id = [i % 360 for i in ies_quarter_id]                      # 360度以上で0から、例:i=300 [300..359,0,1...30]
        ies_quarter_sum = ies.iloc[ies_quarter_id, :].values.sum()              # i度から91度分を合計
        ies_quarter_sums.append(ies_quarter_sum)
    
    # φ方向1/4の合計の最大値を算出
    ies_quarter_sums = np.array(ies_quarter_sums)                               # 配列化、np.whereを使用するため
    directions = np.where(ies_quarter_sums == ies_quarter_sums.max())[0]        # 最大値の角度のリスト
    
    # 描画用の角度と半径などの算出
    theta = ies.index.values[0:-1] / 180 * np.pi                                # シリーズを配列にし、弧度法からラジアンに変換
    # 照射方向の算出では
    # 0度と重複するため
    # 360度を削除していることに注意
    r = ies_quarter_sums                                                        # ２分割した光度の合計値を抽出
    
    # 描画設定
    fig = plt.figure(figsize=(10,10))
    ax = fig.add_subplot(111, polar=True)                                       # 図の配置を１行１列の１番目にし、極座標に設定
    
    # 描画設定
    ax.set_theta_zero_location('E')                                             # 0度を東にする
    ax.set_title('AIMING DIRECTION', fontsize=13)                               # タイトルの書式設定
    ax.set_thetagrids(THETA_GRIDS, labels=PHI_GRIDS_LABELS)
    ax.plot(theta, r, label='Quarter Total of Luminous Intensity', color='gold')# 鉛直方向の総和、黄色
    
    plt.show()

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# 配光データの水平照射方向の回転（1度刻みのデータフレーム用、負の回転角度に対応）

def rotate_ies(ies, rotation_angle):
    
    # 回転角度は、0未満、360度以上に対応
    
    # 回転角度の正負で場合分け
    if rotation_angle >= 0:
        rotation_angle = rotation_angle % 360                                   # 例:362度は2度に
    if rotation_angle < 0:
        rotation_angle = rotation_angle % 360 + 1                               # 例:-362度は359度に    
        # φは0と360度が重複し、361行あるため、
        # 単に360で割った余り分移動するだけでは、
        # ひとつ足りない
    
    ies1 = ies.shift(rotation_angle).fillna(0)                                  # 行方向に回転角度分だけ半時計回りにずらし、欠損値に0代入
    ies2 = ies.shift(rotation_angle - 361).fillna(0)                            # 上記の操作で失われた行を埋めるようにずらす、欠損値に0代入   
    # 正の場合と負の場合で、ies1とies2が入れ替わる
    # 回転角度 362度の場合、ies1は2度ずらし、ies2は-359度ずらす
    # 回転角度-362度の場合、ies1は359度ずらし、ies2は-2度ずらす
    
    ies = ies1 + ies2
    
    return ies

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# ピーク範囲の分類

def cal_peak_zone(ies):
    
    peak_angle  = cal_peak_angle(ies)                                           # 光度のピークの座標のリスト
    peak_values = cal_peak_value(ies)                                           # 光度のピークの値のリスト
    
    if peak_angle.size == 0:                                                    # ピークがない場合
        peak_zone = 'Diffuse'                                                   # 一様な配光であると判断
    else:
        peak_phi_angle, peak_theta_angle = \
        del_small_peak(peak_angle, peak_values)                                 # 小さなピークを除く
    
        # ピークの極座標値の精度は
        # 差分時にどの程度次元を削減するかによる
        # 現状では、φ=10度間隔、θ=5度間隔
        
        if   ([p for p in peak_theta_angle if p <  20] != []                    # ピークが天底から±20度未満にあり、かつ
        and   [p for p in peak_theta_angle if p >= 20] == []):                  # それ以外にピークがないなら
               peak_zone = 'Down'
               # Soraa 36d 四角配光は、ピークが15度にもある
        
        elif ([p for p in peak_theta_angle if     20 <= p <  50] != []          # ピークが天底から±20度以上かつ45度未満にあり、かつ
        and   [p for p in peak_theta_angle if p < 20 or p >= 50] == []):        # それ以外にピークがないなら
               peak_zone = 'Semi Down'
        
        elif ([p for p in peak_theta_angle if     50 <= p <  80] != []          # ピークが天底から±45度以上かつ80度未満にあり、かつ
        and   [p for p in peak_theta_angle if p < 50 or p >= 80] == []):        # それ以外にピークがないなら
               peak_zone = 'Side Down'
        
        elif ([p for p in peak_theta_angle if     80 <= p <  105] != []         # ピークが天底から±80度以上かつ105度未満にあり、かつ
        and   [p for p in peak_theta_angle if p < 80 or p >= 105] == []):       # それ以外にピークがないなら
               peak_zone = 'Side'
        
        elif ([p for p in peak_theta_angle if     105 <= p <  135] != []        # ピークが天底から±105度以上かつ165度未満にあり、かつ
        and   [p for p in peak_theta_angle if p < 105 or p >= 135] == []):      # それ以外にピークがないなら
               peak_zone = 'Side Up'
        
        elif ([p for p in peak_theta_angle if     135 <= p <  165] != []        # ピークが天底から±105度以上かつ165度未満にあり、かつ
        and   [p for p in peak_theta_angle if p < 135 or p >= 165] == []):      # それ以外にピークがないなら
               peak_zone = 'Semi Up'
        
        elif ([p for p in peak_theta_angle if p >= 165] != []                   # ピークが天底から±165度以上、かつ
        and   [p for p in peak_theta_angle if p <  165] == []):                 # それ以外にピークがないなら
               peak_zone = 'Up'
        
        elif ([p for p in peak_theta_angle if p <   20] != []                   # ピークが天底から±5度未満にあり、かつ
        and   [p for p in peak_theta_angle if p >= 165] != []                   # ピークが天頂から±5度以内にあり、かつ
        and   [p for p in peak_theta_angle if 20 <= p < 165] == []):            # それ以外にピークがないなら
               peak_zone = 'Up & Down'
        else:
               peak_zone = 'Others'
                
    return peak_zone

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# ピークの分類(データベースには入れないが、ビーム角の算出で利用)

def cal_peaks(ies):
            
    peak_phi_angle, peak_theta_angle = cal_peak_angle(ies)                      # 光度のピークの座標のリスト
    
    no_of_peaks_up   = len([p for p in peak_theta_angle if 120 <= p])           # 天頂から±60度以内にあるピークの数
    no_of_peaks_side = len([p for p in peak_theta_angle if 60 < p < 120])       # 水平方向±30度にあるピークの数
    no_of_peaks_down = len([p for p in peak_theta_angle if p <= 60])            # 天底から±60度以内にあるピークの数
    
    return no_of_peaks_up, no_of_peaks_down, no_of_peaks_side

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# 設置面の判定

def cal_mounting_surface(ies):
    
    # 誤差の影響が大きいので
    # 1カンデラ以下を0にする
    ies = ies[ies>=1]
    ies = ies.fillna(0)
    
    # 光度から光束に変換
    ies_lm = cd_to_lm(ies)                                                      # 光度から光束に変換、データフレーム
    
    # m行 x n列 の配列
    # array([[-, - ... -],
    #        [-, - ... -],
    #        ...
    #        [-, - ... -]])
    
    # 上下横で分割
    upper_ies_lm = ies_lm[:,91:]                                                # 上方光束、φ=90度除く
    lower_ies_lm = ies_lm[:,:90]                                                # 下方光束、φ=90度除く、WWは、φ=90度も0ではない
    side_ies_lm  = ies_lm[120:241,10:171]                                       # 照射方向と反対側の約半分
    
    # 天頂と天底は漏れ光がある(Flos My Wayなど)
    # 境界をより狭くする
    
    # 上下横半球での光束の合計値
    upper_lumen = upper_ies_lm.sum()                                            # 上方光束の合計値
    lower_lumen = lower_ies_lm.sum()                                            # 下方光束の合計値
    side_lumen  = side_ies_lm.sum()
    
    # 光束が0の半球の有無による設置面の推定
    
    if   side_lumen  == 0.0:                                                    # 横半分の光束がないなら
         mounting_surface = 'Wall Recessed'                                     # 壁付け照明器具の可能性が高い
         
         # 上下配光は、吊りか壁表面
    
    elif upper_lumen == 0.0:                                                    # 上方光束がないなら
         mounting_surface = 'Ceiling'                                           # 天井付け照明器具の可能性が高い
         
         # スポットライトで、ライトアップにも使える？
         
    elif lower_lumen == 0.0:                                                    # 上方光束がないなら
         mounting_surface = 'Floor'                                             # 床付け照明器具の可能性が高い
         
    else:
        mounting_surface = 'Unknown'
    
    return mounting_surface

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# 上方光束比の算出

def cal_upper_light_ratio(ies):
    
    # 光度から光束に変換
    ies_lm = cd_to_lm(ies)                                                      # 光度から光束に変換、データフレーム
    
    # m行 x n列 の配列
    # array([[-, - ... -],
    #        [-, - ... -],
    #        ...
    #        [-, - ... -]])
    
    # 上方光束比の算出
    upper_ies_lm      = ies_lm[:,91:]                                           # 上方光束、φ=90度除く
    lower_ies_lm      = ies_lm[:,:90]                                           # 下方光束、φ=90度除く、WWは、φ=90度も0ではない
    upper_lumen       = upper_ies_lm.sum()                                      # 上方光束の合計値
    lower_lumen       = lower_ies_lm.sum()                                      # 下方光束の合計値
    lumen_sum         = upper_lumen + lower_lumen                               # 全光束からφ=90度を除く
    upper_light_ratio = upper_lumen / lumen_sum
    
    return upper_light_ratio

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# 上方光束比による分類
    
def cal_upper_light_ratio_type(ies):
    
    upper_light_ratio = cal_upper_light_ratio(ies)
    
    # 上方光束比による分類分け
    
    if            upper_light_ratio < 0.01:                                     # 上方光束比が1%割未満
                  upper_or_lower  = 'Only Lower'
    
    # 測定誤差のため、小さな値で、0にならない場合がある
    # そのため、1lm以下に設定、係数は要調整
    
    elif (0.01 <= upper_light_ratio                                             # 上方光束比が1%以上
    and           upper_light_ratio < 0.1):                                     # 上方光束比が10%未満
                  upper_or_lower  = 'Lower'
                  # 例: 下方配光のボラードでも、発光面があると、上方へ光が漏れる
    
    elif (0.1 <= upper_light_ratio                                              # 上方光束比が10%以上
    and           upper_light_ratio < 0.4):                                     # 上方光束比が30%未満
                  upper_or_lower  = 'Semi Lower'
                  # 例: 下方配光のボラードでも、発光面があると、上方へ光が漏れる
                
    elif (0.4 <= upper_light_ratio                                              # 上方光束比が30%割以上
    and          upper_light_ratio < 0.6):                                      # 上方光束比が70%未満
                 upper_or_lower  = 'Middle'                                     # 上下配光か、拡散配光 Up/Down、Diffuse、Uniform
                
    elif (0.6 <= upper_light_ratio                                              # 上方光束比が70%以上
    and          upper_light_ratio <0.9):                                       # 上方光束比が90%未満
                 upper_or_lower  = 'Semi Upper'
    
    elif (0.9 <= upper_light_ratio                                              # 上方光束比が90%以上
    and          upper_light_ratio <0.99):                                      # 上方光束比が99%未満
                 upper_or_lower  = 'Upper'
    
    elif  0.99 <= upper_light_ratio:                                            # 上方光束比が99%以上
                 upper_or_lower  = 'Only Upper'
                
    return upper_or_lower

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# 配光の対称性の分類

def cal_symmetry(ies):
    
    ies_np = ies.values                                                         # 計算速度を速めるため、配列化
    ies_theta_sum = ies_np.sum(axis=1)                                          # θ方向の合計値
    ies_theta_sum_average = ies_theta_sum.mean()                                # θ方向の合計値の平均
    ies_theta_sum_std = np.std(ies_theta_sum)                                   # θ方向の合計値の標準偏差
    
    # 4つの軸に対称な値の差
    differences_x_axis = []                                                     # φ0-180軸
    differences_y_axis = []                                                     # φ90-270軸
    differences_v_axis = []                                                     # φ45-225軸、vは斜め軸
    differences_w_axis = []                                                     # φ135-315軸、wは斜め軸
    
    for i in range(181):                                                        #181度分繰り返す
        # X軸 - 水平角度0-180度軸で対称な値どうしの差
        differences_x_axis.append(ies_theta_sum[i]                              #   0,  1,  2,...178,179,180度と
                                - ies_theta_sum[360 - i])                       # 360,359,358,...182,181,180度の比較
                              
        # Y軸 - 水平角度90-270度軸で対称な値どうしの差
        differences_y_axis.append(ies_theta_sum[(90 - i) % 360]                 # 90, 89, 88,...   1,  0,359,...272,271,270度と
                                - ies_theta_sum[ 90 + i])                       # 90, 91, 92,...,179,180,181,...268,269,270度の比較
        
        # V軸 - 水平角度45-225度軸で対称な値どうしの差
        differences_v_axis.append(ies_theta_sum[(45 - i) % 360]                 #  45, 44, 43,...  1,  0,359,...227,226,225度と
                                - ies_theta_sum[ 45 + i])                       # 135,136,137,... 89, 90, 91,...223,224,225度の比較
        
        # W軸 - 水平角度135-315度軸で対称な値どうしの差
        differences_w_axis.append(ies_theta_sum[(135 - i) % 360]                # 135,134,133,...  1,  0,359,...317,316,315度と
                                - ies_theta_sum[ 135 + i])                      # 135,136,137,...269,270,271,...313,314,315度の比較
    
    std_dev_x_axis = np.std(differences_x_axis)                                 # 水平角度  0-180度軸に対称な値の差の標準偏差
    std_dev_y_axis = np.std(differences_y_axis)                                 # 水平角度 90-270度軸に対称な値の差の標準偏差
    std_dev_v_axis = np.std(differences_v_axis)                                 # 水平角度 45-225度軸に対称な値の差の標準偏差
    std_dev_w_axis = np.std(differences_w_axis)                                 # 水平角度135-315度軸に対称な値の差の標準偏差
    
    # 変動係数＝標準偏差/平均の大小で、
    # バラツキの程度を判断
    # 変動係数 < 閾値
    # 標準偏差 < 平均 * 閾値
    flag_p = ies_theta_sum_std < ies_theta_sum_average * 0.03                   # 点周りで、 標準偏差が、平均の3%未満なら、対称
    # 5%だと、Flosのウォールウォッシャーも点対称
    flag_x = std_dev_x_axis < ies_theta_sum_average * 0.1                       # X軸に対し、標準偏差が、平均の10%未満なら、対称
    flag_y = std_dev_y_axis < ies_theta_sum_average * 0.1                       # Y軸に対し、標準偏差が、平均の10%未満なら、対称
    flag_v = std_dev_v_axis < ies_theta_sum_average * 0.1                       # 斜め軸に対し、標準偏差が、平均の10%未満なら、対称
    flag_w = std_dev_w_axis < ies_theta_sum_average * 0.1                       # 斜め軸に対し、標準偏差が、平均の10%未満なら、対称
    # 5%だと、Soraaの10−60度がXY軸対称にならない
        
    # 対称性の判断
    if   flag_p:
         symmetry = 'Point Symmetry'                                            # 点対称、例:普通のビーム
    elif flag_x and not flag_y and not (flag_v or  flag_w):
         symmetry = 'X Axis Symmetry'                                           # 1軸対称、例:ウォールウォッシャー
    elif flag_x and     flag_y and not (flag_v or  flag_w):
         symmetry = 'XY Axis Symmetry'                                          # 2軸対称、例:スプレッド
    elif flag_x and     flag_y and      flag_v and flag_w:
         symmetry = 'XYVW Axis Symmetry'                                        # 4軸対称、例:スクエア
    else:
         symmetry = 'Others'                                                    # その他、例:フロスのウォールウォッシャー、XVW軸のみ対称
         
    return symmetry

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# 対称性の描画

def plot_symmetry(ies):
    
    # 合計の算出
    ies_np = ies.values  
    ies_theta_sum = ies_np.sum(axis=1)                                          # θ方向の合計値
    
    # 平均の算出
    ies_theta_sum_average = ies_theta_sum.mean()                                # θ方向のの合計値の平均
    ies_theta_sum_average = np.tile(ies_theta_sum_average, 361)                 # 平均線を描くため、各φ用の平均を用意
    
    # 標準偏差の算出
    ies_theta_sum_std = np.std(ies_theta_sum)                                   # φごとの合計値の標準偏差
    ies_theta_sum_std = np.tile(ies_theta_sum_std, 361)                         # 標準偏差線を描くため、各φ用の標準偏差を用意
    ies_theta_sum_std_plus  = ies_theta_sum_average + ies_theta_sum_std         # 平均+標準偏差
    ies_theta_sum_std_minus = ies_theta_sum_average - ies_theta_sum_std         # 平均-標準偏差
    
    # 描画用の角度と半径などの算出
    theta = ies.index.values / 180 * np.pi                                      # シリーズを配列にし、弧度法からラジアンに変換
    r = ies_theta_sum.values.ravel()                                            # シリーズを配列化し、一次元化
    symmetry = cal_symmetry(ies)                                                # 対称性の算出
    
    # 描画設定
    fig = plt.figure(figsize=(10,10))
    ax = fig.add_subplot(111, polar=True)                                       # 図の配置を１行１列の１番目にし、極座標に設定
    
    # 描画設定
    ax.set_theta_zero_location('E')                                             # 0度を東にする
    ax.set_title('LIGHT DISTRIBUTION OF THETA TOTAL', fontsize=13)              # タイトルの書式設定
    ax.set_thetagrids(THETA_GRIDS, labels=PHI_GRIDS_LABELS)
    ax.plot(theta, r, label='Theta Total of Luminous Intensity', color='gold')  # θ方向の合計値を描画、黄色
    ax.plot(theta, ies_theta_sum_average,   color='grey')                       # 平均を描画、灰色実線
    ax.plot(theta, ies_theta_sum_std_plus,  color='grey', linestyle='dashed')   # 平均+標準偏差を描画、灰色点線
    ax.plot(theta, ies_theta_sum_std_minus, color='grey', linestyle='dashed')   # 平均-標準偏差を描画、灰色点線
    fig.text(0.5, 0.05, 'SYMMETRY TYPE: ' + symmetry, 
             color='black', horizontalalignment='center')                       # 対称性の分類を表示
    # 描画
    plt.show()

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# 1/2ビーム角の算出

def cal_beam(ies):
    
    symmetry     = cal_symmetry(ies)                                            # 対称性の確認
    up_down_side = cal_peaks(ies)                                               # 上下横の確認
    
    if  symmetry == 'Symmetry' or symmetry == 'XY Axis Symmetry':               # 配光が点対称(ビーム)か2軸対称(スプレッド)なら
        cd_max   = cal_cd_max(ies)[0]
        cd_half  = cd_max/2
        ies_half = ies[ies <= cd_half]                                          # 最大光度の半分以下になるデータを抽出、半分以上はNaN
        
        # 上方配光の場合
        if  up_down_side == 'Up':
            
            # 上方
            # φ=0度
            theta_n_0          = ies_half.iloc[0].dropna().index[-1]            # φ=0度で、Nan削除し、最後の角度
            cd_n_plus_1_0      = ies.iloc[0, theta_n_0 + 1]                     # n+1番目の光度
            cd_n_0             = ies.iloc[0, theta_n_0]                         # n番目の光度
            cd_half_theta_0  = (                                                # 1/2光度の時のθ
                               (cd_half       - cd_n_0)                         # (Ih - In) / (In1 - In) + θn
                             / (cd_n_plus_1_0 - cd_n_0)
                             + theta_n_0
                               )
            # (Ih - In) / (In1 - In) + θn
            half_beam_0_up     = (180 - cd_half_theta_0) * 2                    # 1/2ビーム角
            half_beam_0_up     = int(round(half_beam_0_up, 0))
            
            # φ=90度
            theta_n_90         = ies_half.iloc[90].dropna().index[-1]           # φ=90度で、Nan削除し、最後の角度
            cd_n_plus_1_90     = ies.iloc[90, theta_n_90 + 1]                   # n+1番目の光度
            cd_n_90            = ies.iloc[90, theta_n_90]                       # n番目の光度
            cd_half_theta_90 = (
                               (cd_half        - cd_n_90)
                             / (cd_n_plus_1_90 - cd_n_90)
                             + theta_n_90
                               )
            half_beam_90_up    = (180 - cd_half_theta_90) * 2                   # 1/2ビーム角
            half_beam_90_up    = int(round(half_beam_90_up, 0))
            
            # 下方
            # φ=0度
            half_beam_0_dn  = 'Nan'                                             # 上方配光の場合、下方のビームなし    
            # φ=90度
            half_beam_90_dn = 'Nan'                                             # 上方配光の場合、下方のビームなし
        
        # 下方配光の場合
        if  up_down_side == 'Down':
            
            # 上方
            # φ=0度
            half_beam_0_up  = 'Nan'                                             # 下方配光の場合、上方のビームなし
            # φ=90度
            half_beam_90_up = 'Nan'                                             # 下方配光の場合、上方のビームなし
            
            # 下方
            # φ=0度
            theta_n_0          = ies_half.iloc[0].dropna().index[0]             # φ=0度で、Nan削除し、最初の角度
            cd_n_0             = ies.iloc[0, theta_n_0]
            cd_n_minus_1_0     = ies.iloc[0, theta_n_0 - 1]
            cd_half_theta_0  = (
                               (cd_half - cd_n_minus_1_0)
                             / (cd_n_0  - cd_n_minus_1_0)                       # (Ih - In-1) / (In - In-1) + θn -1
                               + theta_n_0 - 1
                               )
            half_beam_0_dn     = cd_half_theta_0 * 2
            half_beam_0_dn     = int(round(half_beam_0_dn, 0))
            
            # φ=90度
            theta_n_90         = ies_half.iloc[90].dropna().index[0]            # φ=90度で、Nan削除し、最初の角度
            cd_n_90            = ies.iloc[90, theta_n_90]
            cd_n_minus_1_90    = ies.iloc[90, theta_n_90 - 1]
            cd_half_theta_90 = (
                               (cd_half - cd_n_minus_1_90)
                             / (cd_n_90 - cd_n_minus_1_90)
                             + theta_n_90 - 1
                               )
            half_beam_90_dn    = cd_half_theta_90 * 2
            half_beam_90_dn    = int(round(half_beam_90_dn, 0))
            
        # 上下配光の場合
        if  up_down_side == 'Up & Down':
            peak_theta = cal_peak_theta(ies)                                    # ピークの鉛直角度
            peak_theta = [p for p in peak_theta if p<10 or (170<p and p<=180)]  # ピークの鉛直角度が10度以下あるいは170度以上
            
            # 上方
            cd_max_up = ies.iloc[0, peak_theta[1]]                              # ほとんどの場合、180度
            cd_half_up = cd_max_up/2
            ies_up = ies.iloc[:, 90:]                                           # 鉛直角度90度以上の成分を抽出
            ies_up_half = ies_up[ies_up <= cd_half_up]                          # 最大光度の半分以下になるデータを抽出
            
            # φ=0度
            theta_n_0          = ies_half.iloc[0].dropna().index[-1]            # φ=0度で、Nan削除し、最後の角度
            cd_n_plus_1_0      = ies.iloc[phi, theta_n_0 + 1]
            cd_n_0             = ies.iloc[phi, theta_n_0]
            cd_half_theta_0  = (
                               (cd_half_up    - cd_n_0)
                             / (cd_n_plus_1_0 - cd_n_0)
                             + theta_n_0
                               )
            half_beam_0_up     = (180 - cd_half_theta_0) * 2
            half_beam_0_up     = int(round(half_beam_0_up, 0))
            
            # φ=90度
            theta_n_90         = ies_half.iloc[90].dropna().index[-1]           # φ=90度で、Nan削除し、最後の角度
            cd_n_plus_1_90     = ies.iloc[phi, theta_n_90 + 1]
            cd_n_90            = ies.iloc[phi, theta_n_90]
            cd_half_theta_90 = (
                               (cd_half_up     - cd_n_90)
                             / (cd_n_plus_1_90 - cd_n_90)
                             + theta_n_90
                               )
            half_beam_90_up    = (180 - cd_half_theta_90) * 2
            half_beam_90_up    = int(round(half_beam_90_up, 0))
            
            # 下方
            cd_max_dn = ies.iloc[0, peak_theta[0]]                              # ほとんどの場合、0度
            cd_half_dn = cd_max_dn/2
            ies_dn = ies.iloc[:, :91]                                           # 鉛直角度90度以下の成分を抽出
            ies_dn_half = ies_dn[ies_dn <= cd_half_dn]                          # 最大光度の半分以下になるデータを抽出
            
            # φ=0度
            theta_n_0          = ies_dn_half.iloc[0].dropna().index[0]          # φ=0度で、Nan削除し、最初の角度
            cd_n_0             = ies.iloc[0, theta_n_0]
            cd_n_minus_1_0     = ies.iloc[0, theta_n_0 - 1]
            cd_half_theta_0  = (
                               (cd_half_dn - cd_n_minus_1_0)
                             / (cd_n_0     - cd_n_minus_1_0)
                             + theta_n_0 - 1
                               )
            half_beam_0_dn     = cd_half_theta_0 * 2
            half_beam_0_dn     = int(round(half_beam_0_dn, 0))
            
            # φ=90度
            theta_n_90         = ies_dn_half.iloc[90].dropna().index[0]         # φ=90度で、Nan削除し、最初の角度
            cd_n_90            = ies.iloc[90, theta_n_0]
            cd_n_minus_1_90    = ies.iloc[90, theta_n_0 - 1]
            cd_half_theta_90 = (
                               (cd_half_dn - cd_n_minus_1_90)
                             / (cd_n_90    - cd_n_minus_1_90)
                             + theta_n_90 - 1
                               )
            half_beam_90_dn    = cd_half_theta_90 * 2
            half_beam_90_dn    = int(round(half_beam_90_dn, 0))
        
        # 横配光の場合
        if  up_down_side == 'Side' or up_down_side == 'Others':
            half_beam_0_dn  = 'Nan'
            half_beam_90_dn = 'Nan'
            half_beam_0_up  = 'Nan'
            half_beam_90_up = 'Nan'
    else:
        half_beam_0_dn  = 'Nan'
        half_beam_90_dn = 'Nan'
        half_beam_0_up  = 'Nan'
        half_beam_90_up = 'Nan'
        
    return half_beam_0_up, half_beam_90_up, half_beam_0_dn, half_beam_90_dn

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# 極座標を直行座標への写像（未完成！！！）

def mapping(ies,tilt_theta):
    map_array = []
    for i in ies.index:                                                         # 行名ごとに繰り返す
        map_list = []
        for c in ies.columns:                                                   # 列名ごとに繰り返す
            x, y, z = pole_to_rec(1, c, i)                                      # 極座標を直交座標に変換
            x, y, z = rotate(x,y,z, tilt_theta)                                 # 座標を回転
            r, theta, phi = rec_to_pole(x,y,z)                                  # 直交座標を極座標に変換
            theta, phi = round(theta), round(phi)                               # 整数化
            map_list.append((theta,phi))
        map_array.append(columns_list)
    map_matrix = pd.DataFrame(map_array, index=ies.index, columns=ies.columns)
    return map_matrix

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# 極座標を直行座標に変換

def pole_to_rec(r, theta, phi):
    phi = phi * np.pi / 180                                                     # 弧度法からラジアンへ
    theta = theta * np.pi / 180                                                 # 弧度法からラジアンへ
    x = r * np.sin(theta) * np.cos(phi)
    y = r * np.sin(theta) * np.sin(phi)
    z = r * np.cos(theta) * -1                                                  # 天底側を正とする
    return x, y, z

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# 直行座標を極座標に変換（未完成！！！）

def rec_to_pole(x, y, z):
    r = (x**2 + y**2 + z**2) ** 0.5                                             # 半径を計算
    theta = np.arccos(z * -1)                                                   # θを計算
    if theta != 0 and theta != np.pi:
    # θ≠0度かつ180度(sinθ≠0)なら
            phi = np.arccos(min(1, max(-1, x / np.sin(theta))))                 # φを計算、-1以下あるいは1以上
            if round(y,10) != round(np.sin(theta) * np.sin(phi),10):            # arccosでは、一意に定まらない、yの値で確認、誤差が大きいので、値を丸める
                phi = 2 * np.pi - phi
    else:
        phi = 0                                                                 # 天頂が天底の場合、φは定義できないが、phi0以外は、値を0にしてあるので、ここでは0
    theta = theta / np.pi * 180                                                 # ラジアンから弧度法へ
    phi = (phi / np.pi * 180) % 360                                             # ラジアンから弧度法へ、負を避けるため、360の余とする
    return r, theta, phi

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# 回転の四元数計算(y軸回り)（未完成！！！）

def tilt(x, y, z, phi):
    point = np.quaternion(0, x, y, z)                                           # 座標を四元数に
    phi = (phi * np.pi / 180) * -1                                              # 弧度法からラジアンへ、時計回りから反時計回りに変換
    q = np.quaternion(np.cos(phi/2), 0, np.sin(phi/2), 0)                       # phi回転の四元数
    new_point = q * point * q.inverse()                                         # 新しい座標の四元数
    x, y, z = new_point.vec                                                     # 座標を取得
    return x, y, z

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# 光度から光束への変換フィルター

def cd_to_lm(ies):                                                              # 引数はデータフレーム、次元の削減に対応済み
    
    # θとφの間隔を取得
    theta_interval, phi_interval = theta_phi_interval(ies)
    theta_label = ies.columns                                                   # 0から180までのθの配列
    phi_label   = ies.index[0:-1]                                               # 0から359までのφの配列、360度を除く
    
    # ΔθとΔφの区画の立体角を算出
    solid_angle_list = []                                                       # 空の立体角のリストの作成
    solid_angle_array = []                                                      # 空の立体角のリストのリストの作成
    for i in range(int(180 / theta_interval + 1)):                              # θごとに繰り返す
        theta1 = max(0,  (theta_label[i] - theta_interval / 2)) * np.pi / 180   # 積分開始θ、弧度法からラジアンに、最初の値は0度
        theta2 = min(180,(theta_label[i] + theta_interval / 2)) * np.pi / 180   # 積分終了θ、弧度法からラジアンに、最後の値は180度
        phi1 =  phi_label[0]                 * np.pi / 180                      # 積分開始φ、弧度法からラジアンに
        phi2 = (phi_label[0] + phi_interval) * np.pi / 180                      # 積分終了φ、弧度法からラジアンに、0.5度ごとの場合
        solid_angle = (np.cos(theta1)-np.cos(theta2)) * (phi2-phi1)             # 立体角、dw = sinθdθdφ の積分
        # 一応計算しているが、Δφ = φ2-φ1は常に一定で、φ間隔に等しい
        solid_angle_list.append(solid_angle)
    for j in range(int(360 / phi_interval)):                                    # φごとに繰り返す
        solid_angle_array.append(solid_angle_list)
    solid_angle_array = np.array(solid_angle_array)                             # 配列化
    
    # 光束を算出
    ies_np   = ies.values                                                       # 配列化
    ies_lm = ies_np[0:-1,:] * solid_angle_array                                 # 光束 = 光度 * 立体角、0度と重複するため、最後のφを除く
    
    # 返り値は配列
    # array([[-, - ... -],
    #        [-, - ... -],
    #        ...
    #        [-, - ... -]])
    
    # 行と列の意味は下記の通り
    
    # 次元削減してない場合
    # 360行 x 181列
    #       0   1 ... 179 360
    #   0   -   -   -   -   -
    #   1   -   -   -   -   -
    #   .   -   -   -   -   -
    #   .   -   -   -   -   -
    # 358   -   -   -   -   -
    # 359   -   -   -   -   -
    
    # 次元削減(θ=5度刻み,φ=10度刻み)している場合
    # 36行 x 37列
    #       0   5 ... 175 360
    #   0   -   -   -   -   -
    #   1   -   -   -   -   -
    #   .   -   -   -   -   -
    #   .   -   -   -   -   -
    # 340   -   -   -   -   -
    # 350   -   -   -   -   -
    
    # 光度から光束に変換すると、行数がひとつ減る
    
    return ies_lm                                                               # 返り値は配列

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# 光束の算出

def cal_lm(ies):
    ies_lm = cd_to_lm(ies)                                                      # 光度を光束に変更
    lumen  = ies_lm.ravel().sum()
    lumen  = int(round(lumen,0))
    return lumen

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# 差分用のies (ピークを検証する元データとしても必要)

def for_diff(ies):
    
    # iesの次元は
    # データベースを作成する時: φ=1度、θ=1度
    # クラスター平均を更新する時: φ=5度、θ=10度
    
    if ies.shape == (361, 181):
        ies_for_diff = reduce_dimensions(ies, 5, 10, 180, 360)                  # 誤差の影響を減らすため、θ=5度・φ=10度刻みに
    else:
        ies_for_diff = ies.copy()                                               # copyにしないと、SettingWithCopyWarning警告
    theta_interval, phi_interval = theta_phi_interval(ies_for_diff)             # θ=5度・φ=10度刻みだが、今後の変更のため、変数で
    
    # 何度刻みがいいのかは要検討
    # ピークの数は問題ないが、
    # ピークの方向と、大きさずれる可能性
    # 特になだらかなピークで
    
    # 37行 x 37列
    #       0   5 ... 175 180
    #   0   -   -   -   -   -
    #  10   -   -   -   -   -
    #   .   -   -   -   -   -
    #   .   -   -   -   -   -
    # 350   -   -   -   -   -
    # 360   -   -   -   -   -
    
    ies_for_diff = ies_for_diff.iloc[:-1]                                       # φ=0度と重複するφ=360度は削除、後に追加
    
    # 36行 x 37列
    #       0   5 ... 175 180
    #   0   -   -   -   -   -
    #  10   -   -   -   -   -
    #   .   -   -   -   -   -
    #   .   -   -   -   -   -
    # 340   -   -   -   -   -
    # 350   -   -   -   -   -
    
    # θ方向の処理
    # 天頂と天底で差分を取るため
    # 先頭と末尾に列を加える
    # その際、上半分と下半分を入れ替える
    # 先頭は差分後に削除
    
    # 入れ替えのためのインデックス作成
    no_of_phi      =  len(ies_for_diff)                                         # 行を上下二分割するため、行数を取得
    half_no_of_phi =  int(no_of_phi/2)                                          # 半分の行数をrange関数のため整数化
    id_to_extract =  list(range(half_no_of_phi, no_of_phi))                     # 下半分のインデックスが先
    id_to_extract += list(range(half_no_of_phi))                                # 上半分のインデックスが後
    
    ies_left  = ies_for_diff.iloc[:, 1]                                         # 最後の次の列を抽出、シリーズ、5度を抽出
    ies_right = ies_for_diff.iloc[:,-2]                                         # 最初の次の列を抽出、シリーズ、175度を抽出
    
    ies_left  = ies_left.iloc[id_to_extract]                                    # 上下半分を入れ替え
    ies_right = ies_right.iloc[id_to_extract]                                   # 上下半分を入れ替え
    
    ies_left.index  = [i * phi_interval for i in range(no_of_phi)]              # 該当indexに追加されるよう変更、[0,10...340,350]
    ies_right.index = [i * phi_interval for i in range(no_of_phi)]              # 該当indexに追加されるよう変更、[0,10...340,350]
    
    ies_left_column  = theta_interval * -1                                      # 列名はθ間隔を負にしたもの、-5度
    ies_right_column = theta_interval + 180                                     # 列名はθ間隔に180を加えたもの、185度
    
    ies_for_diff[ies_left_column]  = ies_left                                   # 先頭列前にies_leftを追加
    ies_for_diff[ies_right_column] = ies_right                                  # 末尾列後にies_rightを追加
    ies_for_diff = ies_for_diff.sort_index(axis=1, ascending=True)              # 列名で並び替え
    
    # 36行 x 39列
    #      -5   0   5 ... 175 180 185
    #   0   x   -   y   -   w   -   v
    #  10   x   -   y   -   w   -   v
    #   .   x   -   y   -   w   -   v
    # 175   x   -   y   -   w   -   v
    # 180   y   -   x   -   v   -   w
    #   .   y   -   x   -   v   -   w
    # 340   y   -   x   -   v   -   w
    # 350   y   -   x   -   v   -   w
    # 対応関係を、x,y,v,w で示す
    
    # φ方向の処理
    # 差分を取るため
    # 先頭に行を加える
    
    ies_above = ies_for_diff.iloc[-1]                                           # 最後から２番目の行を抽出、シリーズ、350度を抽出
    ies_below = ies_for_diff.iloc[0]                                            # 最初の行を抽出、シリーズ、0度を抽出
    
    ies_above.name = phi_interval * -1                                          # 行名はφ間隔を負にしたもの、-10度
    ies_below.name = phi_interval + 350                                         # 行名はφ間隔を350を加えたもの、360度
    
    ies_for_diff = ies_for_diff.append(ies_above)                               # 先頭行を末尾に追加
    ies_for_diff = ies_for_diff.append(ies_below)                               # 末尾行を末尾に追加
    ies_for_diff = ies_for_diff.sort_index(ascending=True)                      # 行名で並び替え
    
    # 38行 x 39列
    #      -5   0   5 ... 180 185
    # -10   -   -   -   -   -   -
    #   0   -   -   -   -   -   -
    #  10   -   -   -   -   -   -
    #   .   -   -   -   -   -   -
    #   .   -   -   -   -   -   -
    # 350   -   -   -   -   -   -
    # 360   -   -   -   -   -   -
    
    return ies_for_diff
    

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# θ方向の差分

def diff_theta(ies):
    
    ies_for_diff = for_diff(ies)                                                # 差分用のiesを用意、38行 x 39列
    
    ies_diff_theta = ies_for_diff.diff(axis=1)                                  # θ方向に差分を取る
    
    # 38行 x 39列
    #      -5   0   5 ... 180 185
    # -10 NaN   -   -   -   -   -
    #   0 NaN   -   -   -   -   -
    #  10 NaN   -   -   -   -   -
    #   . NaN   -   -   -   -   -
    #   . NaN   -   -   -   -   -
    # 350 NaN   -   -   -   -   -
    # 360 NaN   -   -   -   -   -
    # -10行は350行、360行は0行と重複
    # 185列は重複してるが、極大の検出のために必要
    
    ies_diff_theta = ies_diff_theta.dropna(axis=1)                              # 欠損値を削除
    ies_diff_theta = ies_diff_theta.iloc[1:-1]                                  # 最初と最後の行を削除
    
    # 36行 x 38列
    #       0   5 ... 180 185
    #   0   -   -   -   -   -
    #  10   -   -   -   -   -
    #   .   -   -   -   -   -
    #   .   -   -   -   -   -
    # 350   -   -   -   -   -
    # 360   -   -   -   -   -
    
    return ies_diff_theta

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# φ方向の差分

def diff_phi(ies):
    
    ies_for_diff = for_diff(ies)                                                # 差分用のiesを用意、38行 x 39列
    
    ies_diff_phi = ies_for_diff.diff(axis=0)                                    # φ方向に差分を取る
    
    # 38行 x 39列
    #      -5   0   5 ... 180 185
    # -10 NaN NaN NaN NaN NaN NaN
    #   0   -   -   -   -   -   -
    #  10   -   -   -   -   -   -
    #   .   -   -   -   -   -   -
    #   .   -   -   -   -   -   -
    # 350   -   -   -   -   -   -
    # 360   -   -   -   -   -   -
    # 0列、180列は定義不可
    # -5列は5列、185列は175列（入れ替えあり）と重複
    # 360行は0行と重複してるが、極大の検出のために必要
     
    ies_diff_phi = ies_diff_phi.dropna(axis=0)                                  # φ方向に差分を取り、欠損値を削除
    ies_diff_phi = ies_diff_phi.iloc[:, 2:-2]                                   # 最初の2列と最後の2列を削除
    
    # 37行 x 35列
    #       5  10 ... 170 175
    #   0   -   -   -   -   -
    #  10   -   -   -   -   -
    #   .   -   -   -   -   -
    #   .   -   -   -   -   -
    # 350   -   -   -   -   -
    # 360   -   -   -   -   -
    
    return ies_diff_phi

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# θ方向の光度のピーク判定の真偽値の算出

def cal_peak_theta_mask(ies):
    
    ies_diff_theta = diff_theta(ies)                                            # θ方向の差分を取る、36行 x 38列
    theta_interval, phi_interval = theta_phi_interval(ies_diff_theta)           # θ=5度・φ=10度刻みだが、今後の変更のため、変数で
    
    # 36行 x 38列 のデータフレーム
    #       0   5 ... 180 185
    #   0   -   -   -   -   -
    #  10   -   -   -   -   -
    #   .   -   -   -   -   -
    #   .   -   -   -   -   -
    # 340   -   -   -   -   -
    # 350   -   -   -   -   -
    
    # データフレームの繰り返し処理は遅いので、配列化
    # 計算速度に約13倍差が出る
    
    ies_diff_theta_ndarray = ies_diff_theta.values
    
    # 36行 x 38列 の配列
    # array([[-, - ... -],
    #        [-, - ... -],
    #        ...
    #        [-, - ... -]])
    # 行名と列名を失う
    
    # 配列の場合、空の配列を用意しても、
    # 要素数が合わず、繰り返し処理の時に追加できない
    # 36行あるので、要素数36の配列を作成する
    # 対応関係が分かりやすいよう、行名にする
    
    peak_theta_mask = np.array(range(0, 351, 10))                               # array([0,10...340,350])、36要素の配列
    
    for i in range(37):                                                         # θは[0,5...185]の38列
        
        # θは38列ある 
        # iの時、iは37まで、range(38)まで可
        # i+1の時、iは36まで、range(37)まで可
        
        peak_flag = (
                    
                    # 単純に正の後が負という条件ではうまくいかない
                    # 差分=0のピークも存在、0を含める必要も
                    # 光度が、ほぼ0の時
                    # 誤差と思われる僅かなピークがある
                    # このピークを除くため
                    # 二つの条件式の一方に0を含めた場合
                    # もう一方は絶対値1以上にする
                    
                    (
                    (ies_diff_theta_ndarray[:, i]   >= 0)                       # i列が0か正
                  * (ies_diff_theta_ndarray[:, i+1] < -1)                       # i+1列が-1より下
                    )
                    
                    # i列を抽出するが、36要素の配列になる
                    # array([-, - ... -])
                    
                    # i番目が0で、
                    # i+1番目が負でも、
                    # i-1番目が負である可能性も
                    
                  + (
                    (ies_diff_theta_ndarray[:, i]   >  1)                       # i列が1より上
                  * (ies_diff_theta_ndarray[:, i+1] <= 0)                       # i+1列が0か負
                    )
                    
                    # i番目が正で
                    # i+1番目が0でも、
                    # i+2番目が正である可能性も
                    
                    )
        peak_theta_mask = np.vstack((peak_theta_mask, peak_flag))               # 列ごと(計算中は行)の真偽値を追加、引数はタプル
        
    # 38行 x 36列 の配列
    # array([[-, - ... -],
    #        [-, - ... -],
    #        ...
    #        [-, - ... -]])
    # 先頭にダミー行があるので、38行
    # データフレームと行と列が入れ替わっているので、
    # 転置する必要がある
    
    peak_theta_mask = peak_theta_mask[1:]                                       # ダミー行の削除
    peak_theta_mask = peak_theta_mask.T                                         # 配列の転置
    
    # 36行 x 37列 の配列
    # array([[-, - ... -],
    #        [-, - ... -],
    #        ...
    #        [-, - ... -]])
    
    peak_theta_mask = pd.DataFrame(peak_theta_mask,                             # 繰り返し処理が終わったので、データフレーム化
                         index   = list(range(0, 351, phi_interval)),
                         columns = list(range(0, 181, theta_interval)))
                         
                         # 変更時は、-5から始まるか、0から始まるか、要確認
                         # 現状は、0から始まる式
    
    # 36行 x 37列
    #       0   5 ... 175 180
    #   0   F   F   F   F   F
    #  10   F   F   F   F   F
    #   .   F   F   F   F   F
    #   .   F   F   F   F   F
    # 340   F   F   F   F   F
    # 350   F   F   F   F   F
        
    return peak_theta_mask
    
# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# φ方向の光度のピーク判定の真偽値の算出

def cal_peak_phi_mask(ies):
    
    ies_diff_phi = diff_phi(ies)                                                # φ方向の差分を取る、37行 x 35列
    theta_interval, phi_interval = theta_phi_interval(ies_diff_phi)             # θ=5度・φ=10度刻みだが、今後の変更のため、変数で
    
    # 37行 x 35列
    #       5  10 ... 170 175
    #   0   -   -   -   -   -
    #  10   -   -   -   -   -
    #   .   -   -   -   -   -
    #   .   -   -   -   -   -
    # 350   -   -   -   -   -
    # 360   -   -   -   -   -
    
    # データフレームの繰り返し処理は遅いので、配列化
    # 計算速度に約6倍差が出る
    
    ies_diff_phi_np = ies_diff_phi.values
    
    # 37行 x 35列 の配列
    # array([[-, - ... -],
    #        [-, - ... -],
    #        ...
    #        [-, - ... -]])
    # 行名と列名を失う
    
    # 配列の場合、空の配列を用意しても、
    # 要素数が合わず、繰り返し処理の時に追加できない
    # 35列あるので、要素数35の配列を作成する
    # 対応関係が分かりやすいよう、列名にする
    
    peak_phi_mask = np.array(range(5, 176, 5))                                  # array([5,10...175])、35要素の配列
    
    for i in range(36):                                                         # φは[0,10...340,360]の37行
        
        # この処理は時間がかかる
        # φは37行ある 
        # iの時、iは36まで、range(37)まで可
        # i+1の時、iは35まで、range(36)まで可
        
        peak_flag = (
                    
                    # 単純に正の後が負という条件ではうまくいかない
                    # 差分=0のピークも存在、0を含める必要も
                    # 光度が、ほぼ0の時
                    # 誤差と思われる僅かなピークがある
                    # このピークを除くため
                    # 二つの条件式の一方に0を含めた場合
                    # もう一方は絶対値1以上にする
                    
                    (
                    (ies_diff_phi_np[i]   >= 0)                                 # i行が0か正
                  * (ies_diff_phi_np[i+1] < -1)                                 # i+1行が-1より下
                    )
                    
                    # i行を抽出する、35要素の配列になる
                    # θ方向のような、列と行の入れ替わりはない
                    # array([-, - ... -])
                    
                    # i番目が0で、
                    # i+1番目が負でも、
                    # i-1番目が負である可能性も
                    
                  + (
                    (ies_diff_phi_np[i]   >  1)                                 # i行が1より上
                  * (ies_diff_phi_np[i+1] <= 0)                                 # i+1行が0か負
                    )
                  
                    # i番目が正で
                    # i+1番目が0でも、
                    # i+2番目が正である可能性も
                    
                  )
                  
        peak_phi_mask = np.vstack((peak_phi_mask, peak_flag))                   # 行ごとの真偽値を追加、引数はタプル
    
    # 37行 x 35列 の配列
    # array([[-, - ... -],
    #        [-, - ... -],
    #        ...
    #        [-, - ... -]])
    # 先頭にダミー行があるので、37行
    
    peak_phi_mask = peak_phi_mask[1:]                                           # ダミー行の削除
    
    # 36行 x 35列 の配列
    # array([[-, - ... -],
    #        [-, - ... -],
    #        ...
    #        [-, - ... -]])
    
    if  peak_phi_mask.sum() == 0:
        
        # 全てが0はφ方向の変化が緩やかな場合
        # 差分が全て0は全く変化がない場合
        # 後者だと条件が厳し過ぎる
        # θ方向でのみ、ピークの検出を行うため、
        # φ方向の真偽値を全て1にする
        
        peak_phi_mask = pd.DataFrame(1,                                         # 繰り返し処理終了後、データフレーム化、値を全て１に
                           index   = list(range(0, 351, phi_interval)),
                           columns = list(range(5, 176, theta_interval)))
    
        # 36行 x 35列
        #       5  10 ... 170 175
        #   0   1   1   1   1   1
        #  10   1   1   1   1   1
        #   .   1   1   1   1   1
        #   .   1   1   1   1   1
        # 340   1   1   1   1   1
        # 350   1   1   1   1   1
    
    else:
        
        peak_phi_mask = pd.DataFrame(peak_phi_mask,                             # 繰り返し処理終了後、データフレーム化
                           index   = list(range(0, 351, phi_interval)),
                           columns = list(range(5, 176, theta_interval)))
                         
                           # 変更時は、-5から始まるか、0から始まるか、要確認
                           # 現状は、0から始まる式
     
        # 36行 x 35列
        #       5  10 ... 170 175
        #   0   F   F   F   F   F
        #  10   F   F   F   F   F
        #   .   F   F   F   F   F
        #   .   F   F   F   F   F
        # 340   F   F   F   F   F
        # 350   F   F   F   F   F
        
    return peak_phi_mask


# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# 光度のピーク判定の真偽値の算出

def cal_peak_mask(ies):
    
    peak_mask = pd.DataFrame(True, index=range(-10,361,10), 
                                      columns=range(-5,186,5))                  # 代入用に、38行 x 39列のデータフレームを用意
    
    peak_theta_mask = cal_peak_theta_mask(ies)                                  # θ方向のピークの真偽値
    peak_phi_mask   = cal_peak_phi_mask(ies)                                    # φ方向のピークの真偽値
    
    # φ方向の差分の特異点の処理
    peak_phi_mask.insert(0, 0, False)                                           # 0番目のindexに、列名で0、Falseを代入
    peak_phi_mask[180] = False                                                  # 列名180で、Falseを代入
    peak_phi_mask.iloc[0, [0,-1]] = True                                        # φ=0度を、Trueに
    
    # θ・φ方向共にピークかの真偽値
    peak_mask = peak_mask & peak_theta_mask & peak_phi_mask                     # θ・φ方向共にピークの真偽値、38行 x 39列
    peak_mask = peak_mask.fillna(False)
    
    # 小さいピークもピークなため
    # 必ずしも最大値と一致しない
    
    # 38行 x 39列
    #      -5   0   5 ... 180 185
    # -10   -   -   -   -   -   -
    #   0   -   -   -   -   -   -
    #  10   -   -   -   -   -   -
    #   .   -   -   -   -   -   -
    #   .   -   -   -   -   -   -
    # 350   -   -   -   -   -   -
    # 360   -   -   -   -   -   -
    
    return peak_mask
    
# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# 光度のピーク座標の算出

def cal_peak_angle(ies):
    
    peak_mask = cal_peak_mask(ies)
    theta_interval, phi_interval = theta_phi_interval(peak_mask)                # θ=5度・φ=10度刻みだが、今後の変更のため、変数で
    
    # ピークのインデックスを取得
    peak_phi_id   = np.where(peak_mask)[0]                                      # ピークのφのインデックス
    peak_theta_id = np.where(peak_mask)[1]                                      # ピークのθのインデックス
    
    # インデックスを角度に変換
    peak_phi_angle   = peak_phi_id   * phi_interval   - phi_interval            # インデックスを角度に変換、-10度始まりに注意
    peak_theta_angle = peak_theta_id * theta_interval - theta_interval          # インデックスを角度に変換、-5度始まりに注意
    
    peak_angle = np.vstack([peak_phi_angle, peak_theta_angle])
    
    # 2行 x n列 の配列
    # array([[-, - ... -],
    #        [-, - ... -]])
    #
    # 単にタプルにすると、
    # 1行 x n列 の配列が 2行になる
    # (array([-, - ... -],
    #  array([-, - ... -])
    
    return peak_angle

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# 光度のピーク値を算出

def cal_peak_value(ies):
    
    peak_phi_angle, peak_theta_angle = cal_peak_angle(ies)
    
    peak_values = []
    for i in range(len(peak_phi_angle)):
        phi   = peak_phi_angle[i]
        theta = peak_theta_angle[i]
        peak_value = ies.loc[phi, theta]                                        # 行と列名を参照、配列化できない
        peak_values.append(peak_value)
    
    peak_values = np.array(peak_values)                                         # 配列化、速くなるか分からない
    
    return peak_values

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# 光度の小さいピークを除く

def del_small_peak(peak_angle, peak_values):
    
    peak_values_max   = peak_values.max()                                       # ピークの最大値
    bool_of_main_peak = peak_values > peak_values_max / 2                       # ピークの最大値の半分より大きいピークの真偽値
    
    peak_phi_angle   = peak_angle[0][bool_of_main_peak]
    peak_theta_angle = peak_angle[1][bool_of_main_peak]
    
    return peak_phi_angle, peak_theta_angle
    
# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# 光度のピーク左右前後の光度の抽出

def get_ies_around_peak(ies):
    
    peak_mask = cal_peak_mask(ies)
    
    # Trueの前後左右もTrueに
    # この真偽値で元の光度の値を抽出し
    # どういう状況でピークが発生しているか確認
    
    bool_of_peak_for_search = peak_mask.copy()
    
    # 検索用のデータフレームを別に用意
    # 元データフレームの前後左右を
    # 随時Trueにしていくので
    # 後右の後右の後右...もTrueに
    
    # φ方向
    for i in range(37):                                                         # i+1があるので、行数は38だが、1を引く
        for j in range(39):                                                     # jのみなので、列数は39で、そのまま
            if  bool_of_peak_for_search.iloc[i, j]  == True:                    # i行目がTrueなら、i=0の時False、i-1はエラーではない
                peak_mask.iloc[i-1, j] = True                                   # i-1行目もTrue
                peak_mask.iloc[i+1, j] = True                                   # i+1行目もTrue、二行連続でTrueはない
                
    # θ方向
    for m in range(38):                                                         # m+1があるので、列数は39だが、1を引く
        for n in range(38):                                                     # nのみなので、行数は38で、そのまま
            if  bool_of_peak_for_search.iloc[n, m]  == True:                    # m列目がTrueなら、m=0の時False、m-1はエラーではない
                peak_mask.iloc[n, m-1] = True                                   # m-1列目もTrue
                peak_mask.iloc[n, m+1] = True                                   # m+1列目もTrue、二列連続でTrueはない
    
    ies_for_diff = for_diff(ies)                                                # 差分用の元データを取得
    ies_around_peak = ies_for_diff[peak_mask]                                   # ピークの前後左右のデータを抽出
    
    ies_around_peak = ies_around_peak.dropna(axis=0, how='all')                 # 全て欠損値の行を削除
    ies_around_peak = ies_around_peak.dropna(axis=1, how='all')                 # 全て欠損値の列を削除
    
    return ies_around_peak

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# 配光データの差分の差分（θ方向）

def ies_diff_theta2(ies):
    ies_diff_theta = diff_theta(ies)
    ies_diff_theta2 = ies_diff_theta.diff(axis=1).fillna(0)                     # θ方向の差分、欠損値に0代入
    ies_diff_theta2[0] = ies_diff_theta2[360]                                   # θ=0度にθ=360度の値を代入
    ies_diff_theta2 = ies_diff_theta2[range(0,361,5)]
    return ies_diff_theta2

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# テーブルの作成

def make_table(table):                                                          # 引数は、'light_table', 'cluster_table'
    
    # 一度作成したら
    # 繰り返すことはない
    
    # テーブルは最大列数=2000
    # 光度とその差分だけで数千列ある
    # 数値の配列をjsonの文字列化する
    # テーブルの分割も試したが
    # 列数が多いと検索に時間がかかる
    
    # 命名規則で、
    # 最初の文字に数字使用不可
    # ハイフンも使用不可
    
    # テーブルの作成
    cur.execute( 
                'CREATE TABLE ' + table +
                '''
                (                                                               -- 各列の最後のカンマ忘れに注意、最後は要らない
                file_name               TEXT    PRIMARY KEY,                    -- 列0、 主キーに設定
                cluster_no              INTEGER DEFAULT 0,                      -- 列1、 インデックス
                ies                     TEXT,                                   -- 列2、 json文字列
                ies_diff                TEXT,                                   -- 列3、 json文字列
                photo_filepath          TEXT,                                   -- 列4
                type                    INTEGER,                                -- 列5、 照明器具タイプ番号
                ceiling_mounted         INTEGER,                                -- 列6、 1(真)or0(偽)
                wall_mounted            INTEGER,                                -- 列7、 1(真)or0(偽)
                floor_mounted           INTEGER,                                -- 列8、 1(真)or0(偽)
                furniture_mounted       INTEGER,                                -- 列9、 1(真)or0(偽)
                other_mounted           INTEGER,                                -- 列10、1(真)or0(偽)
                fixing                  INTEGER,                                -- 列11、取付けタイプ番号
                manufacturer            TEXT,                                   -- 列12、インデックス
                model_name              TEXT,                                   -- 列13
                model_code              TEXT,                                   -- 列14
                light_source            INTEGER,                                -- 列15、光源タイプ番号
                socket                  TEXT,                                   -- 列16
                min_voltage             INTEGER,                                -- 列17、100Vの場合、100
                max_voltage             INTEGER,                                -- 列18、240Vの場合、240
                wattage                 INTEGER,                                -- 列19、100Wの場合、100、四捨五入
                luminous_flux           INTEGER,                                -- 列20、1500lmの場合、1500、インデックス
                beam_angles             TEXT,                                   -- 列21、非対称や上下配光の場合は、数字以外記号もある
                max_luminous_intensity  INTEGER,                                -- 列22、100cdの場合、100
                lowest_cct              INTEGER,                                -- 列23、2700Kの場合、2700
                highest_cct             INTEGER,                                -- 列24、4200Kの場合、4200
                ies_cct                 INTEGER,                                -- 列25、3000Kの場合、3000
                color                   INTEGER,                                -- 列26、カラータイプ番号
                cri                     INTEGER,                                -- 列27、Ra90の場合、90
                lamp_life               INTEGER,                                -- 列28、50000hの場合、50000
                ip_rate                 INTEGER,                                -- 列29、IP20の場合、20
                dimming                 INTEGER,                                -- 列30、調光タイプ番号
                download_url            TEXT                                    -- 列31
                )
                '''
               )
    
    con.commit()

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# テーブルの削除

def del_table(table):
    
    cur.execute('DROP TABLE ' + table )
    
    con.commit()
    
# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# テーブル情報の取得

def get_table_info():
    
    cur.execute(' SELECT name           ' 
                ' FROM   sqlite_master  '
                ' WHERE  type = "table" '
               #' ORDER BY name'
               )                                                                # 予約語の前後の空白が大事
    
    tables = cur.fetchall()                                                     # [('table_1',), ... , ('table_n',)]
    tables = [t[0] for t in tables]                                             # ['table_1', ... , 'table_n']
    
    nos_of_columns  = []
    nos_of_rows     = []
    list_of_columns = []
    
    for t in tables:
        
        # 行数の取得
        cur.execute('SELECT COUNT (file_name) FROM ' + t)
        no_of_rows = cur.fetchone()[0]                                          # [(0,)] の最初の要素、>0
        nos_of_rows.append(no_of_rows)
        
        # 列数の取得
        cur.execute('SELECT * FROM ' + t)
        no_of_columns = len(cur.description)                                    # (('列1',None,None,None,None,None,None),(('列2'
        nos_of_columns.append(no_of_columns)
        
        #列名を取得
        columnn = get_columns(t)
        list_of_columns.append(columnn)
        
    return tables, nos_of_columns, nos_of_rows, list_of_columns

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# テーブル情報を表示

def show_table_info():
    
    # テーブル情報を取得
    tables, nos_of_columns, nos_of_rows, list_of_columns = get_table_info()
    
    # テーブル情報を表示
    for i in range(len(tables)):
        print('--------------------'*4)
        print('table name:      ', tables[i])
        print('no of rows:      ', nos_of_rows[i])
        print('no of columns:   ', nos_of_columns[i])
        print('list of columns: ')
        for j, k in enumerate(list_of_columns[i]):
            print('                 ', j, k)

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# テーブルの列名を取得

def get_columns(table):                                                         # 引数は、文字列で与える
    
    # 直前に選んだテーブルの列を表示
    
    cur.execute('SELECT * FROM ' + table)
    
    columnn = []
    for c in cur.description:
        columnn.append(c[0])
    
    return columnn

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# テーブルの指定した列の項目一覧取得

def get_items(table, column_name):                                              # 引数は、文字列で与える
    
    # メーカー名やクラスター番号の一覧を取得
    
    cur.execute( ' SELECT DISTINCT ' + column_name +
                 ' FROM            ' + table +
                 ' ORDER BY        ' + column_name 
               )                                                                # 予約語の前後の空白が大事
    
    item_names = cur.fetchall()                                                 # [('Item',), ... ,('Item',)]
    item_names = [i[0] for i in item_names]                                     # ['Item', ... , 'Item']
    
    return item_names

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# メーカー名ー覧取得

def get_manufacturers_from_sql():
    
    manufacturers = get_items('light_table', 'manufacturer')
    
    return manufacturers

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# クラスター番号ー覧取得

def get_cluster_nos(clusters):
    
    # 照明器具テーブルから抽出する方法
    cluster_nos = get_items('light_table', 'cluster_no')
    
    # クラスターテーブルから抽出する方法
    # cluster_nos = get_items('cluster_table', 'cluster_no')
    
    # クラスター変数から抽出する方法
    # cluster_nos = [c[CLUSTER_NO] for c in clusters]
    
    return cluster_nos

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# クラスターの要素数の取得

def count_cluster_members(clusters):
    
    # 照明器具テーブルのクラスター番号更新後でないと不正確
    
    print('{:<15}{:<15}'.format(
           'cluster no',
           'no of members')) 
    
    nos_of_cluster_members = []
    for i in range(len(clusters)):
        
        cur.execute( ' SELECT COUNT (*) '
                     ' FROM   light_table '
                     ' WHERE  cluster_no = ' + str(i)
                   )                                                            # 予約語の前後の空白が大事
        
        no_of_cluster_members = cur.fetchall()
        no_of_cluster_members = no_of_cluster_members[0][0]
            
        print('{:<15}{:<15}'.format(
               'cluster ' + str(i),
               no_of_cluster_members))
               
        nos_of_cluster_members.append(no_of_cluster_members)
        
    return nos_of_cluster_members

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# 空クラスターの取得

def get_empty_clusters(clusters):
    
    # 照明器具テーブルのクラスター番号更新後でないと不正確
    
    nos_of_cluster_members = count_cluster_members(clusters)
        
    empty_clusters = \
    [i for i, n in enumerate(nos_of_cluster_members) if n == 0]
    
    return empty_clusters

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# 空クラスターの削除

def del_empty_clusters(clusters):
    
    # 空クラスターがあっても、検索には問題ない
    
    empty_clusters = get_empty_clusters(clusters)                               # 空のクラスター番号のリストを取得
    
    if empty_clusters != []:                                                    # 空のクラスターがある場合
        clusters = [c for c in clusters if c[CLUSTER_NO] not in empty_clusters] # 空のクラスターを除く
    
    for i in range(len(clusters)):
        clusters[i][CLUSTER_NO] = i                                             # クラスターの通し番号を振り直す
    
    return clusters

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# 指定した列を削除

def del_column(table, column_name):                                             # 引数は、テーブル名のイニシャル、文字列で与える
    
    # SQliteでは、列の削除はできない
    # 下記のプロセスが必要
    
    # 仮のテーブルを作成
    make_table('tmp_table')
    
    # 既存のテーブルから削除したい列を除いた列名一覧を取得
    columnn = get_columns(table)
    columnn = [c for c in columnn if c!=column_name]
    columnn = ','.join(columnn)
    
    # 既存のテーブルに複製するデータを取得
    cur.execute( ' SELECT ' + columnn +
                 ' FROM   ' + table
               )
    data_to_copy = cur.fetchall()
                  
    # 仮のテーブルに複製するデータを追加
    cur.executemany( ' INSERT INTO tmp_table'
                     ' VALUES      (' + ('?,'*32)[:-1] + ')'                    # ?はプレースホルダー、最後のカンマを削除
                   # '(?,?,...?)'という?が32個の文字列
                     , data_to_copy
                   )
    
    # 元のテーブルを削除
    cur.execute( ' DROP TABLE ' + table)
    
    # 仮のテーブルを元のテーブルの名前に変更
    cur.execute( ' ALTER  TABLE   tmp_table'
                 ' RENAME TO  ' + table
               )
    
    con.commit()

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# データ型の確認
'''
cur.execute(' SELECT typeof(min_voltage), '
            '        typeof(min_voltage), '
            '        typeof(min_voltage), '
            '        typeof(min_voltage), '
            '        typeof(min_voltage), '
            '        typeof(min_voltage), '
            '        typeof(min_voltage), '
            '        typeof(min_voltage), '
            '        typeof(min_voltage), '
            '        typeof(min_voltage), '
            '        typeof(min_voltage), '
            '        typeof(min_voltage), '
            '        typeof(min_voltage), '
            '        typeof(min_voltage), '
            '        typeof(min_voltage), '
            ' FROM   light_table '
            ' WHERE manufacturer = "Endo"') 
                (text, integer, text, text, text, integer, interger, interger, interger, interger, interger, interger, text, text, text, interger, text, interger, interger, interger, interger,
                text, interger, interger, interger, interger, interger, interger, interger, interger, interger, text)
'''

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# テーブルの複製
# これはメモリが足りない
# cur.execute('INSERT INTO new SELECT * FROM light_table')


# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# 照明器具レコードの作成

def make_light(file_path):                                                      # 引数は、iesへのパス
    
    file_name = os.path.basename(file_path)[0:-4]                               # ファイル名を取得、拡張子iesを除く
    
    manufac, lumcat, luminaire, lamp, wattage, ies = read_ies(file_path)        # iesの読み込み
    ies_small      = reduce_dimensions(ies,5,10,180,360)                        # 次元の削減
    ies_diff_theta = diff_theta(ies)                                            # θ方向の差分
    ies_diff_phi   = diff_phi(ies)                                              # φ方向の差分
    
    ies_list       = ies_small.values.ravel().tolist()                          # 配列化、一元化、リスト化、1369要素のリスト
    diff_list      = ies_diff_theta.values.ravel().tolist()                     # 配列化、一元化、リスト化、1368要素のリスト
    diff_list     += ies_diff_phi.values.ravel().tolist()                       # 配列化、一元化、リスト化、1295要素のリストを追加
    
    # 照明器具のデータフレームに列を追加し、値を代入する
    # 要高速化
    light          = [
                     file_name,                                                 # 列0:  ファイル名
                     0,                                                         # 列1:  クラスター番号
                     ies_list,                                                  # 列2:  光度、リスト、後にSQlite用にjson文字列化
                     diff_list,                                                 # 列3:  光度の差分、リスト、後にSQlite用にjson文字列化
                     None,                                                      # 列4:  写真のファイルパス
                     None,                                                      # 列5:  照明器具タイプ
                     None,                                                      # 列6:  天井設置
                     None,                                                      # 列7:  壁設置
                     None,                                                      # 列8:  床設置
                     None,                                                      # 列9:  家具設置
                     None,                                                      # 列10: その他設置
                     None,                                                      # 列11: 設置方法
                     manufac,                                                   # 列12: メーカー名、後でフォルダ名で置換
                     luminaire,                                                 # 列13: 型名
                     lumcat,                                                    # 列14: 型番
                     lamp,                                                      # 列15: 光源
                     None,                                                      # 列16: ソケット
                     None,                                                      # 列17: 最小電圧
                     None,                                                      # 列18: 最大電圧
                     wattage,                                                   # 列19: 消費電力
                     cal_lm(ies),                                               # 列20: 器具光束
                     None,                                                      # 列21: ビーム角
                     cal_cd_max(ies)[0],                                        # 列22: 器具最大光度
                     None,                                                      # 列23: 最低色温度
                     None,                                                      # 列24: 最高色温度
                     None,                                                      # 列25: 測定色温度
                     None,                                                      # 列26: 色
                     None,                                                      # 列27: 演色性
                     None,                                                      # 列28: 光源寿命
                     None,                                                      # 列29: 調光
                     None,                                                      # 列30: 防塵防水
                     None                                                       # 列31: ダウンロードURL
                     ]
    
    return light                                                                # 返り値はリスト、リストの方が後の繰り返し追加処理が速い

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# 照明器具レコーズの作成

def make_lights_basic(folder_path):                                             # 引数は、クラスタリング、クエリのフォルダ
    
    start_time = time.time()
    
    file_paths  = glob.glob(folder_path+'/**/*.ies', recursive=True)            # フォルダ内のiesファイルを取得、/**/で直下以外も
    no_of_files = len(file_paths)
    
    lights   = []
    unreadable_files = []
    for i in range(0, no_of_files):                                             # フォルダ内の全ファイルで繰り返す
        
        # n番目が中断した場合、i=n-1が中断
        # 0をn-1として、再開 
        
        # メーカーにより数千個の照明器具データがある
        # 繰り返しの途中でエラーが発生することも想定
        
        try:
            print(i+1, '/', no_of_files, ' ', file_paths[i])
            
            file_path = file_paths[i]
            file_name = os.path.basename(file_path)
            
            # データベースの作成
            light = make_light(file_path)                                       # 照明器具レコードの作成
            lights.append(light)
            
        except:                                                                 # iesの読み込みに失敗する可能性も
            print('--------------------'*4)
            print('error: ')
            print(traceback.format_exc())
            unreadable_files.append(file_name)
            
            continue
    
    end_time = time.time()
    elapse_time = round((end_time - start_time), 5)
    print('make light fixtures:   ', elapse_time, ' sec')
    print('')
    
    return lights                                                               # 返り値はリストのリスト

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# 照明器具レコーズの作成

def make_lights(folder_path):                                                   # 引数は、メーカー
    
    start_time = time.time()
    
    folder_name = os.path.basename(folder_path)                                 # フォルダ名は、メーカー名
    file_paths  = glob.glob(folder_path+'/**/*.ies', recursive=True)            # フォルダ内のiesファイルを取得、/**/で再起的に取得
    no_of_files = len(file_paths)
    
    links_df = read_links_df(folder_path)                                       # フォルダ内のcsvファイルの読み込み
    
    lights           = []
    unreadable_files = []
    for i in range(0, no_of_files):                                             # フォルダ内の全ファイルで繰り返す
        
        # n番目が中断した場合、i=n-1が中断
        # 0をn-1として、再開 
        
        # メーカーにより数千個の照明器具データがある
        # 繰り返しの途中でエラーが発生することも想定
        
        try:
            print(i+1, '/', no_of_files, ' ', file_paths[i])
            
            file_path = file_paths[i]
            file_name = os.path.basename(file_path)
            link_df = links_df[links_df['IES File Name']==file_name]            # 読み込むファイルに該当するデータ
            parent_page_url = link_df['Parent Page'][0]                         # iesファイルのダウンロードリンク
            
            # データベースの作成
            light = make_light(file_path)                                       # 照明器具レコードの作成
            light[MANUFACTURER] = folder_name                                   # メーカー名に、フォルダ名を代入
            light[DOWNLOAD_URL] = parent_page_url
            lights.append(light)
            
        except:                                                                 # iesの読み込みに失敗する可能性も
            print('--------------------'*4)
            print('error: ')
            print(traceback.format_exc())
            unreadable_files.append(file_name)
            
            continue
    
    # エラーファイルを書き出す
    error_file_path  = ERROR_PATH + 'Error - make_lights.txt'                   # エラーファイルを書き出すファイルパス
    no_of_unreadable_files = len(unreadable_files)
    unreadable_files = '\n'.join(unreadable_files)                              # ['a.ies', 'b.ies']を改行表示のため、'a.ies\nb.ies'に変換
    with open(error_file_path, 'a') as f:
        f.write('--------------------'*2)
        f.write('\n')
        f.write(folder_path)
        f.write('\n')
        f.write('number of unreadable files: ' + str(no_of_unreadable_files))
        f.write('\n')
        f.write(unreadable_files)
        f.write('\n')
    
    end_time = time.time()
    elapse_time = round((end_time - start_time), 5)
    print('make light fixtures:   ', elapse_time, ' sec')
    print('')
    
    return lights                                                               # 返り値はリストのリスト

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# 照明器具レコーズの追加

def add_lights(lights):
    
    start_time = time.time()
    
    lights = to_json(lights)
    
    tables, nos_of_columns, nos_of_rows_before = get_table_info()               # レコーズ追加前にテーブル情報を取得
    
    # 繰り返し処理
    # no_of_data = len(lights)
    # for i in range(no_of_data):
    # 
    #     print(str(i+1) +'/'+ str(no_of_data) +' '+ lights[i][0])              # 何番目/全体 ファイル名を表示
    # 
    #     cur.execute(  ' INSERT INTO light_table '                             # 予約語の前後の空白が大事
    #                   ' VALUES ' + str(tuple(lights[i]))
    #                   )
    
    # バッチ処理、
    # 繰り返し処理より約５倍速いが、メモリ不足の可能性
    cur.executemany( ' INSERT INTO light_table '
                     ' VALUES      (' + ('?,'*32)[:-1] + ')'                    # ?はプレースホルダー、最後はカンマを削除
                   # '(?,?,...32個...?)'の文字列
                     , lights
                   )
    
    tables, nos_of_columns, nos_of_rows_after = get_table_info()                # レコーズ追加後にテーブル情報を取得
    
    id = tables.index('light_table')                                            # テーブル情報の返り値がリストのため要インデックス
    
    # データ追加前後の行数を表示
    print('--------------------'*4)
    print('add light fixtures')
    print('before:     ', nos_of_rows_before[id], ' rows')
    print('after:      ', nos_of_rows_after[id],  ' rows')
    print('added:      ', nos_of_rows_after[id]
                        - nos_of_rows_before[id], ' rows')
    
    con.commit()
    
    end_time = time.time()
    elapsed_time = round((end_time - start_time), 5)
    print('')
    print(elapsed_time, ' sec')

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# 全メーカーで照明器具レコーズの作成・追加

def make_add_lights():
    
    manufacturers_in_folder = get_manufacturers_from_folder()
    manufacturers_in_sql    = get_manufacturers_from_sql()
    
    manufacturers = set(manufacturers_in_folder) - set(manufacturers_in_sql)    # フォルダにあるが、データベースにないものを選ぶ
    
    for m in manufacturers:                                                     # 各メーカーのフォルダで繰り返す
        print('--------------------'*4)
        print('start: ' + m)
        
        cur.execute( ' SELECT manufacturer'
                     ' FROM   light_table ')
        
        folder_path = MANUFACTURER_PATH + m                                     # メーカーフォルダへのパスを作成
        
        lights = make_lights(folder_path)                                       # 照明器具レコーズの作成
        add_lights(lights)                                                      # 照明器具レコーズの追加

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# リンクの読み込み

def read_links_df(folder_path):
    
    folder_name = os.path.basename(folder_path)                                 # フォルダ名は、メーカー名
    file_path   = folder_path +'/'+ folder_name + '.csv'                        # リンクのcsvファイル
    links_df    = pd.read_csv(file_path, header=0, index_col=0)
    
    # フォルダ内のファイルの拡張子を小文字化しているため
    # リスト内のファイル名の拡張子も小文字化する必要あり
    # SQlite登録時、ファイルのダウンロードリンクが見つからず、エラーになる
    # 拡張子の変更により、完全一致検索に影響があるか要確認
    
    links_df = links_df.replace('\.IES$', {'IES File Name': '.ies'},regex=True) # IESファイルの拡張子、.IESを.iesに変換
    
    return links_df

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# 照明器具レコーズの光度とその差分のjson文字列化

def to_json(lights):
    
    for l in lights:
        l[IES]  = json.dumps(l[IES])
        l[DIFF] = json.dumps(l[DIFF])
    
    return lights

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# データベース内のメーカー名を取得

def get_manufacturers_from_folder():
    
    # スクレイピングの際に
    # メーカー・フォルダ内に 
    # メーカーごとのフォルダが
    # 作成されてることが前提
    
    folders_files = os.listdir(MANUFACTURER_PATH)                               # データベースフォルダ内のフォルダとファイルを取得
    
    folders = [f for f in folders_files 
               if os.path.isdir(os.path.join(MANUFACTURER_PATH, f))]            # データベースフォルダ内のフォルダのみ、ファイルを除く
    
    manufacturers = folders
    
    manufacturers.sort()
    
    return manufacturers

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# インデックスの作成

def make_indices():
    cur.execute(
    'CREATE INDEX file_name_id     ON light_table (file_name)    ')
    cur.execute(
    'CREATE INDEX cluster_no_id    ON light_table (cluster_no)   ')
    cur.execute(
    'CREATE INDEX manufacturer_id  ON light_table (manufacturer) ')
    cur.execute(
    'CREATE INDEX luminous_flux_id ON light_table (luminous_flux)')
    con.commit()
    
# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# インデックスの削除

def del_indices():
    cur.execute('DROP INDEX file_name_id    ')
    cur.execute('DROP INDEX cluster_no_id   ')
    cur.execute('DROP INDEX manufacturer_id ')
    cur.execute('DROP INDEX luminous_flux_id')
    con.commit()

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# 照明器具レコーズの抽出

def get_lights(search_condition, record_limit=100000):                          # 条件式は文字列で与える、レコード数上限の初期値は10万
    
    start_time = time.time()
    
    # 条件式は文字列で与える
    # 照明器具テーブルは
    # メーカーごと、クラスターごとで
    # 検索することが多い
    # 例: 'manufacturer = "ABC"'、文字列内の文字列は""で囲む
    # 例: 'cluster_no = 7'
    
    cur.execute( ' SELECT * '                                                   # 照明器具レコーズを選択、予約語の前後の空白が大事
                 ' FROM      light_table '
                 ' WHERE ' + search_condition +
                 ' LIMIT ' + str(record_limit)
               )
    
    lights = cur.fetchall()                                                     # 照明器具レコーズを取得
    
    # [(ファイル名, ... 配光文字列, 差分文字列, ...),
    #  (ファイル名, ... 配光文字列, 差分文字列, ...),
    #   ...
    #  (ファイル名, ... 配光文字列, 差分文字列, ...)]
    
    lights = [list(l) for l in lights]                                          # タプルのリストをリストのリストに変換
    
    # [[ファイル名, ... 配光文字列, 差分文字列, ...],
    #  [ファイル名, ... 配光文字列, 差分文字列, ...],
    #   ...
    #  [ファイル名, ... 配光文字列, 差分文字列, ...]]
    # データ型は、文字と数字が混ざる
    # 光度とその差分は、json文字列
    # 文字があると、時間がかかるので、配列化しない
    
    no_of_lights = len(lights)                                                  # 照明器具レコーズの数を取得
    
    # json文字列をリストに変換
    # ls:lights
    # l: light
    # 下記の繰り返しで、上記のように略す
    
    ls = []
    for l in lights:
        l1 = l[:IES]                                                            # 配光より前の部分
        l2 = json.loads(l[IES])                                                 # 配光のjson文字列をリスト化
        l3 = json.loads(l[DIFF])                                                # 差分のjson文字列をリスト化
        l4 = l[DIFF+1:]                                                         # 差分より後の部分
        l1.append(l2)                                                           # リストを要素として追加なので、append
        l1.append(l3)                                                           # リストを要素として追加なので、append
        l1  = l1 + l4
        ls.append(l1)
        
    lights = ls
    
    # [[ファイル名, ... [配光リスト], [差分リスト], ...],
    #  [ファイル名, ... [配光リスト], [差分リスト], ...],
    #   ...
    #  [ファイル名, ... [配光リスト], [差分リスト], ...]]
    
    # 配光とその差分のリストは配列化しない
    # この段階で配列化しても、配列のリストになるだけ
    # [array、... array]
    # 全体の配列化のため、再度配列化が必要
    # 配列化は、光度とその差分を抽出する際に実行
        
    end_time = time.time()
    elapsed_time = round((end_time - start_time), 5)
    
    print('get light fixtures')
    print('search by:    ', search_condition       )
    print('found:        ', no_of_lights,   ' lights')
    print('elapsed time: ', elapsed_time, ' sec'   )
    print('')
    
    return lights                                                               # 返り値は、リストのリスト

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# 照明器具レコーズの削除

def del_lights(search_condition):                                       # 条件式は文字列で与える
    
    cur.execute( ' DELETE'                                                      # 予約語の前後の空白が大事
                 ' FROM      light_table '
                 ' WHERE ' + search_condition
               )
    
    con.commit()

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# クラスターレコーズの抽出

def get_clusters():                                                             # 条件式は文字列で与える
    
    start_time = time.time()
    
    # コードは、get_lightsとほぼ同じ
    # テーブルと選択条件が異なるだけ
    # 使い回すため,変数にはlightsを使用し
    # 最後でclustersに変換する
    
    # クラスターテーブルは
    # 全てを取得することが多い
    
    cur.execute( ' SELECT * '                                                   # 照明器具レコーズを選択、予約語の前後の空白が大事
                 ' FROM   cluster_table '
               )
    
    lights = cur.fetchall()                                                     # 照明器具レコーズを取得
    
    # [(ファイル名, ... 配光文字列, 差分文字列, ...),
    #  (ファイル名, ... 配光文字列, 差分文字列, ...),
    #   ...
    #  (ファイル名, ... 配光文字列, 差分文字列, ...)]
    
    lights = [list(l) for l in lights]                                          # タプルのリストをリストのリストに変換
    
    # [[ファイル名, ... 配光文字列, 差分文字列, ...],
    #  [ファイル名, ... 配光文字列, 差分文字列, ...],
    #   ...
    #  [ファイル名, ... 配光文字列, 差分文字列, ...]]
    # データ型は、文字と数字が混ざる
    # 光度とその差分は、json文字列
    # 文字があると、時間がかかるので、配列化しない
    
    no_of_lights = len(lights)                                                  # 照明器具レコーズの数を取得
    
    # json文字列をリストに変換
    # ls:lights
    # l: light
    # 下記の繰り返しで、上記のように略す
    
    ls = []
    for l in lights:
        l1 = l[:IES]                                                           # 配光より前の部分
        l2 = json.loads(l[IES])                                                # 配光のjson文字列をリスト化
        l3 = json.loads(l[DIFF])                                               # 差分のjson文字列をリスト化
        l4 = l[DIFF+1:]                                                        # 差分より後の部分
        l1.append(l2)                                                         # リストを要素として追加なので、append
        l1.append(l3)                                                         # リストを要素として追加なので、append
        l1  = l1 + l4
        ls.append(l1)
        
    lights = ls
    
    # [[ファイル名, ... [配光リスト], [差分リスト], ...],
    #  [ファイル名, ... [配光リスト], [差分リスト], ...],
    #   ...
    #  [ファイル名, ... [配光リスト], [差分リスト], ...]]
    
    # 配光とその差分のリストは配列化しない
    # この段階で配列化しても、配列のリストになるだけ
    # [array、... array]
    # 全体の配列化のため、再度配列化が必要
    # 配列化は、光度とその差分を抽出する際に実行
    
    end_time = time.time()
    elapsed_time = round((end_time - start_time), 5)
    
    #print('--------------------'*4)
    print('search by:    ', 'clusters'     )
    print('found:        ', no_of_lights,   ' lights')
    print('elapsed time: ', elapsed_time, ' sec\n'   )
    
    clusters = lights
    
    return clusters                                                             # 返り値は、リストのリスト

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# 照明器具レコーズのデータフレーム化

def to_df(lights):                                                              # 引数は、lightsとclusters
    
    file_names = [l[FILE_NAME]    for l in lights]
    data       = [l[FILE_NAME+1:] for l in lights]
    
    lights_df = pd.DataFrame(data, index=file_names, columns=COLUMNS)
    
    return lights_df

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# 照明器具レコーズのデータフレーム化(光度)

def to_df_ies(lights):                                                          # 引数は、lightsとclusters
    
    file_names = [l[FILE_NAME] for l in lights]
    data       = [l[IES]       for l in lights]
    
    lights_ies_df = pd.DataFrame(data, index=file_names, columns=IES_COLUMNS)   # θ=5度、φ=10度刻みである前提
    
    return lights_ies_df

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# 照明器具レコーズのデータフレーム化(差分)

def to_df_diff(lights):                                                         # 引数は、lightsとclusters
    
    file_names = [l[FILE_NAME] for l in lights]
    data       = [l[DIFF]      for l in lights]
    
    lights_diff_df = pd.DataFrame(data, index=file_names, columns=DIFF_COLUMNS) # θ=5度、φ=10度刻みである前提
    
    return lights_diff_df

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# 照明器具レコーズの光度部分の抽出

def only_ies(lights):                                                           # 引数は、リスト
    
    lights_ies = [l[IES] for l in lights]                                       # n行 x 1369列のリスト
    # [[配光リスト], ... , [配光リスト]]
        
    lights_ies = np.array(lights_ies)                                           # n行 x 1369列 の配列、データ型は小数
    # n行 x 1369列 の配列
    # array([[-, - ... -],
    #        [-, - ... -],
    #        ...
    #        [-, - ... -]])
    
    return lights_ies                                                           # 返り値は配列

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# 照明器具レコーズの差分部分の抽出

def only_diff(lights):                                                          # 引数は、リスト
    
    lights_diff = [l[DIFF] for l in lights]                                     # n行 x 2663列のリスト
    # [[差分リスト], ... , [差分リスト]]
    
    lights_diff = np.array(lights_diff)                                         # n行 x 2663列 の配列、データ型は小数
    # n行 x 2663列 の配列
    # array([[-, - ... -],
    #        [-, - ... -],
    #        ...
    #        [-, - ... -]])
    
    return lights_diff                                                          # 返り値は配列

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
#  配光ベクトルの正規化

def norm_ies(ies):                                                              # 引数は、ies、ies_1D、lights_ies(単数）
    
    # データフレームとシリーズに
    # 対応できるように、まず一元化
    
    ies_flat   = ies.values.ravel()
    ies_length = (ies_flat ** 2).sum() ** 0.5                                   # 配光ベクトルの大きさ、シリーズ
    ies_normd  = ies / ies_length                                               # 配光ベクトルの単位化
    
    return ies_normd

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
#  配光行列の正規化

def norm_lights_ies(lights_ies):                                                # 引数は、照明器具レコーズからiesかdiffを抽出し配列化
    
    ies_length = (lights_ies ** 2).sum(axis=1) ** 0.5                           # 配光行列の大きさ
    
    # n個の要素の配列
    # array([-, - ... -])
    
    ies_length = ies_length.reshape(-1,1)                                       # ブロードキャストのため転置
    
    # n行の配列
    # array([[-],
    #        [-],
    #        ...
    #        [-]])
    
    lights_ies_normd = lights_ies / ies_length
        
    return lights_ies_normd

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
#  照明レコーズの正規化

def norm_lights(lights):                                                        # 引数は、照明器具レコーズ
    
    lights_ies        = only_ies(lights)                                        # 照明器具レコーズからiesを抽出
    lights_ies_normd  = norm_lights_ies(lights_ies)                             # 配光行列の正規化
    lights_ies_normd  = lights_ies_normd.tolist()                               # リスト化
    
    lights_diff       = only_diff(lights)                                       # 照明器具レコーズからdiffを抽出
    lights_diff_normd = norm_lights_ies(lights_diff)                            # 配光差分行列の正規化
    lights_diff_normd = lights_diff_normd.tolist()                              # リスト化
    
    # ls:lights
    # l: light
    # 下記の繰り返しで、上記のように略す
    
    ls = []
    for l, lin, ldn in zip(
                          lights, 
                          lights_ies_normd, 
                          lights_diff_normd):
        l1 = l[:IES]                                                           # 配光より前の部分
        l1.append(lin)                                                         # リストを要素として追加なので、append
        l1.append(ldn)                                                         # リストを要素として追加なので、append
        l2 = l[DIFF+1:]                                                        # 差分より後の部分
        l1  = l1 + l2
        ls.append(l1)
        
    lights_normd = ls
    
    return lights_normd                                                         # 返り値はリスト

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# 配光ベクトル間の距離の算出(単数)

def cal_distance(ies1, ies2):                                                   # 引数は、ies、ies_1D、lights_ies(単数）
    
    # データフレームとシリーズに
    # 対応できるように、まず一元化
    
    ies1 = ies1.values.ravel()                                                  # 配列化、一次元化
    ies2 = ies2.values.ravel()                                                  # 配列化、一次元化
      
    difference_squared = (ies1 - ies2) ** 2                                     # 各要素の差の２乗
    distance = difference_squared.sum() ** 0.5                                  # 各要素を合計し、平方根を取る
    
    return distance

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# 配光行列間の距離の算出(複数)

def cal_distances(lights_ies1, lights_ies2):                                    # 引数は、照明器具レコーズからiesかdiffを抽出し配列化
    
    # 配列の方がデータフレームより数十倍速い
    
    # m個の照明器具
    # m行 x 1369列の配列
    # array([[-,-...-],
    #        [-,-...-],
    #        ...
    #        [-,-...-],)
    
    # n個の照明器具
    # n行 x 1369列の配列
    # array([[-,-...-],
    #        [-,-...-],
    #        ...
    #        [-,-...-],)
    
    distances = []
    for i in lights_ies1:
        differences = lights_ies2 - i
        
        # n行 x 1369列の配列
        # array([[-,-...-],
        #        [-,-...-],
        #        ...
        #        [-,-...-],)
        
        distance = ((differences ** 2).max(axis=1)) ** 0.5                      # 差の二乗和の平方根
        
        # n個の要素の配列
        # array([-,-...-])
        # 次元が2から1になる
        # 2次元のaxis=0方向が、1次元の0方向になる
        
        distances.append(distance)
        
        # n個の要素を持った配列が、m個あるリスト
        # [array([-,-...-]), array([-,-...-]) ... array([-,-...-])]
    
    distances = np.array(distances)
        
    # m行 x n列の距離行列
    # array([[-,-...-],
    #        [-,-...-],
    #        ...
    #        [-,-...-],)
    
    return distances

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# 配光行列間のコサイン距離のヒートマップ

def plot_heatmap_distances(lights1, lights2, annotation=True):                  # 引数は、照明器具レコーズ
    
    # 距離行列の算出
    distances = cal_distances(only_ies(lights1), 
                              only_ies(lights2))                                # 距離の算出
    
    # ヒートマップの描画
    fig = plt.subplots(figsize=(10, 8))
    sns.heatmap(distances, 
                square=True, 
                center=0.7, annot=annotation, cmap='Reds',                      # annotで数値を表示の有無 
                xticklabels=0, yticklabels=0,                                   # 0で軸ラベルなし
                vmax=1000, vmin=0,                                              # vmax, vmin: カラーバーの最大・最小値
                cbar_kws={"shrink":1,"aspect":20,"label": "Cos Similarity"})    # shringk: カラーバーの長さをヒートマップと揃える
    plt.show()

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# 配光ベクトル間のコサイン類似度の算出

def cal_cos_similarity(ies1, ies2):                                             # 引数は、ies、ies_1D、lights_ies(単数）
    
    # ２次元と１次元の両方に
    # 対応できるように、まず一元化
    
    ies1 = ies1.values.ravel()                                                  # 配列化、一次元化、内積計算のため
    ies2 = ies2.values.ravel()                                                  # 配列化、一次元化、内積計算のため
    
    inner_product  = np.dot(ies1,ies2)                                          # 配光ベクトルの内積
    ies1_norm      = np.dot(ies1,ies1) ** 0.5                                   # 配光ベクトル１のノルム
    ies2_norm      = np.dot(ies2,ies2) ** 0.5                                   # 配光ベクトル２のノルム
    cos_similarity = inner_product / ies1_norm / ies2_norm                      # コサイン類似度
    
    return cos_similarity

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# 配光行列間のコサイン類似度行列の算出

def cal_cos_similarities(lights_ies1, lights_ies2):                             # 引数は、照明器具レコーズからiesかdiffを抽出し配列化
    
    # 配列の方がデータフレームより十数倍速い
    
    # 光度とその差分に対応させる
    # 引数をlightsにせず
    # only_ies()かonly_diff()で
    # 関数の外で計算
    
    inner_product = np.dot(lights_ies1, lights_ies2.T)                          # 配光ベクトルの内積、ies2は計算のために転置
    
    # m個の照明器具: L1, L2 ... Lm
    # n個の照明器具: l1, l2 ... ln
    # m行 x n列のコサイン類似度行列
    # array([[-,-...-],
    #        [-,-...-],
    #        ...
    #        [-,-...-],)
    
    lights_ies1_norm = (lights_ies1 ** 2).sum(axis=1) ** 0.5                    # 配光ベクトル１のノルム、配列化
    lights_ies2_norm = (lights_ies2 ** 2).sum(axis=1) ** 0.5                    # 配光ベクトル２のノルム、配列化
    
    # ies1は、m個の配列: array([-,-...-])
    # ies2は、n個の配列: array([-,-...-])
    
    cos_similarities = (inner_product 
                     / lights_ies1_norm.reshape(1,-1).T
                     / lights_ies2_norm)
    
    # 配列なので
    # ブロードキャストを利用
    # ies1は、m行にするため、転置
    # ies2は、n列のまま
    
    cos_similarities = np.round(cos_similarities, 10)
    
    # 値を丸める
    # 計算誤差のため
    # 一致するはずのものが一致しなくなる
    # 順位付けには、誤差は問題ないと思われる
    
    return cos_similarities

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# 配光行列間のコサイン類似度行列のヒートマップ

def plot_heatmap_cos_similarities(lights1, lights2, annotation):                # 引数は、照明器具レコーズ
    
    # 光度とその差分の両方を掛け合わせたコサイン類似度
    # そのため、引数は照明器具レコーズで
    # この関数内で光度とその差分を抽出
    
    # コサイン類似度行列の算出
    cos_similarities_ies = \
    cal_cos_similarities(only_ies(lights1),
                         only_ies(lights2))                                     # 光度のコサイン類似度
    
    cos_similarities_diff = \
    cal_cos_similarities(only_diff(lights1),
                         only_diff(lights2))                                    # 差分のコサイン類似度
    
    cos_similarities = cos_similarities_ies * cos_similarities_diff
    
    # ヒートマップの描画
    fig = plt.subplots(figsize=(10, 8))
    sns.heatmap(cos_similarities, 
                square=True, 
                center=0.7, annot=annotation, cmap='Reds',                      # annotで数値を表示の有無 
                xticklabels=0, yticklabels=0,                                   # 0で軸ラベルなし
                vmax=1, vmin=0,                                                 # vmax, vmin: カラーバーの最大・最小値
                cbar_kws={"shrink":1,"aspect":20,"label": "Cos Similarity"})    # shringk: カラーバーの長さをヒートマップと揃える
    plt.show()

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# 配光行列間のコサイン類似度行列のヒートマップの繰り返し保存

def plot_heatmap_clusters(clusters):
    
    for c in range(len(clusters)):
        print('--------------------'*4)
        print('Cluster ', c)
        
        cluster_k = get_lights('cluster_no = ' + str(c))
        
        if cluster_k != []:
        
            cos_similarities_ies = \
            cal_cos_similarities(only_ies(cluster_k),
                                 only_ies(cluster_k))                           # コサイン類似度
            
            cos_similarities_diff = \
            cal_cos_similarities(only_diff(cluster_k),
                                 only_diff(cluster_k))                          # 差分のコサイン類似度
            
            cos_similarities = cos_similarities_ies * cos_similarities_diff
            
            # ヒートマップの描画
            fig = plt.subplots(figsize=(10, 8))
            sns.heatmap(cos_similarities, 
                        square=True, 
                        center=0.7, annot=False, cmap='seismic',                # annotで数値を表示の有無 
                        xticklabels=0, yticklabels=0,                           # 0で軸ラベルなし
                        vmax=1, vmin=0,                                         # vmax, vmin: カラーバーの最大・最小値
                        cbar_kws={"shrink":1,"aspect":20,"label":"Cos Similarity"}) # shringk: カラーバーの長さをヒートマップと揃える
            
            plt.title('Cluster ' + str(c))
            #plt.colorbar()
            plt.savefig(CLUSTER_GRAPH_PATH + 'Heatmap/Heatmap ' + str(c))
            plt.clf()                                                           # 現在のfigをクリア
            plt.close()

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# 配光行列間のコサイン類似度行列のヒストグラムの繰り返し保存

def plot_histgram_clusters(clusters):
    
    for c in range(len(clusters)):
        print('--------------------'*4)
        print('Cluster ', c)
        
        cluster_k = get_lights('cluster_no = ' + str(c))
        
        if cluster_k != []:
        
            cos_similarities_ies = \
            cal_cos_similarities(only_ies(cluster_k),
                                 only_ies(cluster_k))                           # コサイン類似度
            
            cos_similarities_diff = \
            cal_cos_similarities(only_diff(cluster_k),
                                 only_diff(cluster_k))                          # 差分のコサイン類似度
            
            cos_similarities = cos_similarities_ies * cos_similarities_diff
            
            if  len(cluster_k)!=1:
                cos_similarities_mean = \
                (cos_similarities.sum(axis=0) - 1) / (len(cluster_k)-1)
            else:
                cos_similarities_mean = cos_similarities.sum(axis=0)
            
            # ヒストグラムの描画
            fig = plt.subplots(figsize=(10, 8))
            plt.hist(cos_similarities_mean, 
                     range=(0,1),                                               # 横軸の範囲を0-1に設定
                     bins=20,                                                   # 階級の数を20に設定、0-1までの0.5刻み
                     color='y')
            
            plt.title('Cluster ' + str(c))
            plt.savefig(CLUSTER_GRAPH_PATH + 'Histgram/Histgram ' + str(c))
            plt.clf()                                                           # 現在のfigをクリア
            plt.close()

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# 配光ベクトル間の相関係数の算出

def cal_corrcoef(ies1, ies2):                                                   # 引数は、ies、ies_1D、lights_ies(単数）
    
    # ２次元と１次元の両方に
    # 対応できるように、まず一元化
    
    ies1 = ies1.values.ravel()                                                  # 配列化、一次元化
    ies2 = ies2.values.ravel()                                                  # 配列化、一次元化
    
    correlation_coefficient = np.corrcoef(ies1,ies2)[0][1]                      # 相関係数の算出、0行1列目の値を抽出
    
    return correlation_coefficient

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# 配光ベクトル散布図の描画

def plot_scatter(ies1, ies2):
    
    # φ=10度、θ=5度刻みだと
    # 判例が全部表示される
    
    no_of_phi = len(ies1.index)
    corrcoef = round(cal_corrcoef(ies1, ies2), 4)                               # 相関係数を算出、小数点第４位まで
    
    # 横軸にies1, 縦軸にies2
    # φごとに異なる色を使用
    # 対称な配光だと、点が重なる
    # 上下横のタイプが同じだと
    # 0の近くにデータが集まる
    
    fig, ax = plt.subplots(1,1,figsize=(10,10))
    for i in range(no_of_phi):                                                  # φごとに繰り返す
        x = ies1.iloc[i]
        y = ies2.iloc[i]
        color_scale = (i/no_of_phi, 0.0, 1-i/no_of_phi)                         # rgbを指定、φ=0度で(0,0,1)、φ=360度で(1,0,0)、青>赤
        ax.scatter(x, y, label=str(ies1.index[i])+'d', 
                   color=color_scale, alpha=0.01)
    ax.set_title('Scatter Plot')
    ax.set_xlabel('ies1')
    ax.set_ylabel('ies2')
    ax.legend(bbox_to_anchor=(1.13,1.02))
    fig.text(0.5,0.05, 'Correlation Coefficient: ' + str(corrcoef), 
             horizontalalignment='center')
    plt.show()

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# 配光行列間の類似度行列の算出

def cal_similarities(lights1, lights2):                                         # 引数は、lightsとそのjson文字列を展開したもの
    
    # 類似度の比較に使用するデータベースの列
    # コサイン類似度: 光度とその差分 
    # 配光分類:      設置面
    # 測光量:        光束
    
    cos_similarities = \
    cal_cos_similarities(only_ies(lights1),only_ies(lights2))                   # コサイン類似度
    
    cos_similarities_diff = \
    cal_cos_similarities(only_diff(lights1),only_diff(lights2))                 # 差分のコサイン類似度
    
    # 点対称な場合
    # φ方向の差分は全て0になり
    # コサイン類似度も0になってしまう
    # そのため、常にφとθ方向の差分をまとめて
    # コサイン類似度を計算する
    # θ方向の差分が0になる可能性もあるが
    # 全方位に均一な配光でない限り
    # φとθの両方向の差分が同時に0にはならない
    
    # upper_light_ratio_filter = \
    # make_constraint_mask(lights1, lights2, UPPER_LIGHT_RATIO) # 上方光束比の制約
    
    # m個の照明器具: L1, L2 ... Lm
    # n個の照明器具: l1, l2 ... ln
    # m行 x n列のコサイン類似度行列
    #     l1  l2 ...  ln
    #  L1  -   -   -   -
    #  L2  -   -   -   -
    # ...  -   -   -   -
    #  Lm  -   -   -   -
    
    similarities = (                                                            # 類似度 =
                      cos_similarities                                          #   コサイン類似度
                    * cos_similarities_diff                                     # * コサイン類似度(差分)
                    #* upper_light_ratio_filter                                 # * 上方光束比マスク
                   ) 
    
    return similarities                                                         # 返り値は配列

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# クラスター制約マスクの作成

def make_constraint_mask(lights1, lights2, column_no):                          # 引数は二次元のリストと列のインデックス
    
    # 同じ分類かどうか
    # 判定した真偽値の配列を作成
    # column_name:
    # 'Peak Zone'         ピークの範囲
    # 'Upper Light Ratio' 上方光束比
    # 'Symmetry'          対称性
    
    lights1_type = [d[column_no] for d in lights1]                              # 指定した列を抽出、リスト
    lights1_type = np.array(lights1_type)                                       # 配列化
     
    # 要素数nの配列
    # array ([x1, x2 ... xn])
    
    lights1_type  = lights1_type.reshape(-1,1)                                  # 計算上、転置する、n行１列
    
    # n行 x 1列の配列
    # array([[x1],
    #        [x2],
    #        ...
    #        [xn]])
    
    lights2_type = [d[column_no] for d in lights2]                              # 指定した列を抽出、リスト
    lights2_type = np.array(lights2_type)                                       # 配列化
    
    # 要素数kの配列
    # array ([y1, y2 ... yk])
    
    # タイル状に並べて、配列の大きさを揃えるより
    # ブロードキャストの方が１割ほど速い
    
    constraint_mask = (lights1_type == lights2_type)                            # 同じ分類であればTrue、でなければFalse
    # n行 x k列の配列
    # array([[x1==y1, x1==y2 ... x1==yk],
    #        [x2==y1, x2==y2 ... x2==yk],
    #        ...
    #        [xn==y1, xn==y2 ... xn==yk]])  
    
    return constraint_mask                                                      # 返り値は配列

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# 光束比マスクの作成

def make_lumen_ratio_mask(lights1,lights2, minus_tol,plus_tol):                 # 引数は二次元のリスト
    
    # 負の許容比の範囲は、0 <= minus_tol < 1
    # 正の許容比の範囲は、0 <= plus_tol
    # 負の許容比は、若干暗くても許容する時に設定、値は0.2までが現実的
    # 正の許容比は、若干明るくても許容する時に設定、
    # あるいは、調光できる時に設定、値は0.5までが現実的
    
    lumen1 = [l1[LUMEN] for l1 in lights1]                                      # 光束の列をテーブルから抽出、リスト
    lumen1 = np.array(lumen1)                                                   # 配列化
    
    # m個の照明器具: L1, L2 ... Lm
    # m個の要素の配列
    # array([-, - ... -])
    
    lumen1 = lumen1.reshape(-1,1)                                               # 計算上、転置する、n行１列
    
    # m行 x 1列の配列
    # array([-],
    #       [-],
    #       ... 
    #       [-])
    # テストデータ、lumen1 = np.array([10,25,50,75,100]).reshape(-1,1)
    
    lumen2 = [l2[LUMEN] for l2 in lights2]                                      # 指定した列のリスト
    lumen2 = np.array(lumen2)                                                   # 配列化
    
    # n個の照明器具: L1, L2 ... Ln
    # n個の要素の配列
    # array([-, - ... -])
    # テストデータ、lumen2 = np.array([10,25,50,75,100])
    
    # タイル状に並べて、配列の大きさを揃えるより
    # ブロードキャストの方が１割ほど速い
    
    # 次の処理で
    # 負の許容比=1だと、分母=0なので
    # 0.99999で近似する
    if  minus_tol == 1:
        minus_tol = 0.99999
    
    # 比較対象が、負の許容比で補正した光束未満の場合
    lights1_mask = (1-minus_tol) * lumen1 > lumen2                              # Φ2がa%減したΦ1未満なら
    lumen_ratio1 = lights1_mask * (lumen2 / ((1-minus_tol) * lumen1))           # Φ2/(1-a)Φ1、a=0でΦ2/Φ1
    
    #lights1_mask * 
    # 光束1=100lm 光束2=90lm で
    # 光束1 >= 光束2 の場合
    # 光束比は90/100 = 0.900
    # 光束2に比例
    
    # 比較対象が、正の許容比で補正した光束以上の場合
    lights2_mask = (1+plus_tol) * lumen1 <= lumen2                              # Φ2がa%増したΦ1以上なら
    lumen_ratio2 = lights2_mask * ((1+plus_tol) * lumen1 / lumen2)              # (1+a)Φ1/Φ2、a=0でΦ1/Φ2
    
    # 光束1=100lm 光束2=110lm で
    # 光束1 < 光束2 の場合
    # 光束比は100/110 = 0.909
    # 光束2に反比例
    
    # 対数の採用も検討したが
    # 距離感が違うと判断
    
    # 比較対象が、
    # 負の許容比で補正した光束以上、かつ
    # 正の許容比で補正した光束未満の場合
    
    lights3_mask = lumen1 * (1-minus_tol) <= lumen2
    lights4_mask = lumen1 * (1+plus_tol)  >  lumen2
    lumen_ratio3 = lights3_mask * lights4_mask                                  # 許容範囲内なら、光束比=1
    
    lumen_ratio_mask = lumen_ratio1 + lumen_ratio2 + lumen_ratio3
    # テストデータ
    # pd.DataFrame(lumen_ratio_mask, 
    #              index=[10,25,50,75,100], columns=[10,25,50,75,100])
    
    return lumen_ratio_mask                                                     # 返り値は配列

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# 光束範囲の算出

def cal_lumen_range(lumen, minus_tol, plus_tol, lumen_percentage=0.85):
    
    # 総合類似度 = 類似度 x 光束比
    # 類似度の最大値=1であるから
    # 総合類似度>=0.8であるためには
    # 光束比>=0.8
    
    # 下限光束 <= クエリの光束 < 上限光束
    
    # 下限光束 / ((1-負の許容比) * クエリの光束) = 0.8
    # Φmin / (1-a)Φq = 0.8
    # Φmin = (1-a)Φq x 0.8
    
    lower_lumen_limit = (1-minus_tol) * lumen * lumen_percentage
    lower_lumen_limit = round(lower_lumen_limit)
     
    # ((1+正の許容比) * クエリの光束) / 上限光束 = 0.8
    # (1+a)Φq / Φmax = 0.8
    # Φmax = (1+a)Φq / 0.8
    
    upper_lumen_limit = (1+plus_tol) * lumen / lumen_percentage
    upper_lumen_limit = round(upper_lumen_limit)
    
    return lower_lumen_limit, upper_lumen_limit

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# 配光データの検索と比較の場合分け

def search_compare_ies(clusters):
    
    file_paths = glob.glob(QUERY_PATH + '*')                                    # 全てのファイルパスを取得
    
    # ファイルの種類が配光データか確認
    file_type_flag = True
    for f in file_paths:
        
        if (f.endswith('ies') or                                                # 拡張子がies
            f.endswith('IES') or                                                # 拡張子がIES
            f.endswith('ldt') or                                                # 拡張子がldt
            f.endswith('LDT')):                                                 # 拡張子がLDT、の配光ファイルの場合
            
            file_type_flag = file_type_flag * True                              # これ以前に配光以外のファイルがあった場合、0*1＝0で偽
        
        else:                                                                   # 配光以外のファイルの場合
            file_type_flag = False
            print('to be ies or ldt files')
    
    # ファイルの数が１つか２つか確認
    if file_type_flag == True:
        
        # ファイルパスが1つの場合は検索
        if  len(file_paths) == 1:
            result = search_ies(clusters, file_paths[0])
            
        # ファイルパスが2つの場合は比較
        if  len(file_paths) == 2:
            similarity = compare_ies(file_paths)
            result = search_ies(clusters, file_paths)
            
        # ファイルパスが３つ以上の場合は処理なし
        if  len(file_paths) >= 3:
            print('number of files to be one or two')

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# 配光データの検索初期条件

'''
ウェブサイトに合わせて、要設計
'''

manufacturer = 'Bega'                                                           # 文字列、リストの方が良い
cct          = 3000                                                             # 整数、範囲指定？
cri          = 90                                                               # 整数、範囲指定？
dimming      = 'non dim'                                                        # 'non dimmable'、'dimmable'、'unknown'
ip_rate      = 20                                                               # 整数
minus_tol    = 0                                                                # 負の許容比の範囲は、0 <= minus_tol < 1
plus_tol     = 0                                                                # 正の許容比の範囲は、0 <= plus_tol

search_condition   = ''
search_condition  += ' manufacturer = "' + manufacturer + '"'
#search_condition += ' AND  cct = '           + str(0)
#search_condition += ' AND  cri > '           + str(0)
#search_condition += ' AND  dimming = '       + str("*")
#search_condition += ' AND  ip_rate = '       + str(0)

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# 配光データの検索

def search_ies(clusters, file_path):
    
    # 事前にクラスターのレコーズを読み込んでおく
    
    # 引数はファイルパス
    # フォルダパスのファイル数で検索か比較かを事前に場合分けしてるため
    
    start_time = time.time()
    
    # クエリの取得
    print('--------------------'*4)
    query = [make_light(file_path)]                                             # 照明器具レコードの作成、配列
    file_name = query[0][0]
    print('search query  ', file_name)
    
    # 類似するクラスターの特定
    # 光束比は考慮しない
    # 各クラスターの配光が
    # 明るさの異なる照明器具の平均値であるため
    
    time1 = time.time()
    print('time1', time1 - start_time)
    
    print('--------------------'*4)                                             # 秒数が表示される類似度計算の前に区切りを入れ
    print('find similar clusters')                                              # 何との類似度かを表示
    print('')
    
    similarities_cluster = cal_similarities(clusters, query)                    # 類似度行列の算、引数は、クラスターが先、クエリが後
    similarities_cluster = similarities_cluster.ravel()                         # 一元化、クエリがひとつなので、データを単純化
    
    # 1個のクエリー: Q
    # k個のクラスター: C1, C2 ... Ck
    # k個の要素の配列
    # array([-,- ... -])
    
    # 上位いくつのクラスターを選ぶか判断
    # 類似した照明器具が多いと
    # クラスター間の類似度は僅差になる
    # この差は、光束を考慮した場合、容易に逆転し得る。
    # 事前にいくつと決めるのではなく
    # クラスター間類似度0.8以上にする
    # 多めに選び、漏れを少なくする
    
    time2 = time.time()
    print('time2', time2 - time1)
    
    similar_clusters = np.sort(similarities_cluster)[::-1]                      # 類似度を昇順に並べ、逆順、array([1,0.9,...])
    no_of_similar_clusters = len(np.where(similar_clusters>0.85)[0])            # 類似度0.85以上の数
    no_of_similar_clusters = max(5,  no_of_similar_clusters)                    # 最少5クラスター
    no_of_similar_clusters = min(20, no_of_similar_clusters)                    # 最多20クラスター
    
    similar_clusters = similarities_cluster.argsort()[::-1]                     # 類似度を昇順に並べ、逆順、array([i,j...])
    similar_clusters = similar_clusters[:no_of_similar_clusters]                # 最も似ている5つを選ぶ、array([i,j])
    
    # インデックス番号はクラスター番号と一致
    
    # 類似度順に並べ
    # 上位のクラスターから照明器具を抽出するが
    # 1) 照明器具が数個しかないクラスターが上位を占める
    # 2) 下位のクラスターのより類似した照明器具が漏れる
    # という問題がある
    
    time3 = time.time()
    print('time3', time3 - time2)
    
    print('similar 5 clusters')
    print('{:<13}{:<13}'.format(
          'sim', 'cluster no'))
    for s in similar_clusters:
        print('{:<13.5f}{:<13}'.format(
              similarities_cluster[s], 
              str(s)))
    print('')
    
    
    # 類似するクラスターの照明器具レコーズの取得
    search_condition  = ['cluster_no='+str(o) for o in similar_clusters]        # 番号前に'cluster_no='を追加、[cluster_no=i, cluster_no=j]
    search_condition  = ' OR '.join(search_condition)                           # リストを文字列化、間に' OR 'を挟む、'cluster_no=i OR cluster_no=j'
    search_condition  = ' (' + search_condition + ')'
    
    lumen = query[0][LUMEN]
    lower_lumen_limit, upper_lumen_limit = \
    cal_lumen_range(lumen, minus_tol, plus_tol, 0.85)
    search_condition += ' AND (luminous_flux > ' + str(lower_lumen_limit)
    search_condition += ' AND  luminous_flux < ' + str(upper_lumen_limit) + ')'
    
    time31 = time.time()
    print('time3.5', time31 - time3)
    
    search_result = get_lights(search_condition)
    
    if search_result == []:                                                     # 絞り込み検索で、該当する照明器具がない場合
        print('no lights found')
    
    else:                                                                       # 該当する照明器具がある場合
        
        # 類似する照明器具の検索
        # 個別の照明器具との比較のため
        # 光束比を考慮する
        # そのため、クラスターとの類似度よりも
        # かなり低くなる可能性もある
        # 非類似クラスターに属する
        # 照明器具の類似度の方が高くなってしまう
        # 逆転現象の主な要因と考えられる
        
        print('--------------------'*4)                                         # 秒数が表示される類似度計算の前に区切り
        print('find similar light fixtures \n')                                 # 何との類似度の計算かを表示
        similarities = cal_similarities(search_result, query)                   # 類似度行列の算出、引数は、クラスターが先、クエリが後
        lumen_ratio_mask = \
        make_lumen_ratio_mask(search_result, query, minus_tol, plus_tol)
        overall_similarities = similarities * lumen_ratio_mask
        
        time4 = time.time()
        print('time4', time4 - time3)
        
        # 1個のクエリー: Q
        # j+k+l+m+n個の照明器具: L1, L2 ... Ljklmn
        # j+k+l+m+n個の配列
        # array([[-],
        #        [-],
        #        ...
        #        [-]])
        
        
        # 下記の処理は
        # 要素にリストがあるので
        # numpyでは推奨されておらず
        # 処理も遅い
        
        search_result_temp=[]
        for i in range(len(search_result)):
            search_result_temp.append(overall_similarities[i].tolist()
                                    + similarities[i].tolist()
                                    + lumen_ratio_mask[i].tolist()
                                    + search_result[i])                         # 検索結果の先頭列に類似度を追加
        search_result = search_result_temp
        search_result.sort(key=lambda x: x[0], reverse=True)                    # 検索結果を類似度の降順で並べ替え
        
        time5 = time.time()
        print('time5', time5 - time4)
        
        # 最大類似度が複数ある場合も
        # 例: 塗装色が異なるだけで配光が同じ
        # ファイル名も一致するものがあれば、同じ照明器具と判断
        # ファイル名が変更されてないことが前提
        # メーカーと型番名での比較は難しい
        # ファイル名も同じデータを先頭へ移動
        
        match_flag = 0
        file_names = [s[FILE_NAME + 3] for s in search_result]                  # ファイル名のリストを取得、類似度を先頭に追加してるため、+3
        if file_name in file_names:                                             # クエリのファイル名がリストにないと、次の処理でエラー
            match_flag = 1
            match_id   = file_names.index(file_name)                            # クエリのファイル名と一致するインデックス、初めの方にある
            tmp1 = search_result[0]                                             # 先頭の行
            tmp2 = search_result[match_id]                                      # 一致する行
            search_result[0] = tmp2                                             # 先頭を一致する行の値を代入
            search_result[match_id] = tmp1                                      # 一致する行に先頭の値を代入
            print('exact match')
            print('{:<13}{:<13}{:<13}{:<13}{:<13}{:<13}{:<13}'.format(
                  'sim','cos sim','lumen ratio','cluster no','cluster rank','manufacturer','file name'))
            print('{:<13.5f}{:<13.5f}{:<13.5f}{:<13}{:<13}{:<13}{:<13}'.format(
                   search_result[match_id][0], 
                   search_result[match_id][1],
                   search_result[match_id][2],  
                   str(search_result[match_id][CLUSTER_NO + 3]),                # クラスター番号を表示、類似度を先頭に追加してるため、+3
                   np.where(similar_clusters
                          ==search_result[match_id][CLUSTER_NO + 3])[0][0]+1,   # クラスターの類似度順位を表示、類似度を先頭に追加してるため、+3
                   search_result[match_id][MANUFACTURER + 3],                   # メーカー名を表示、類似度を先頭に追加してるため、+3
                   search_result[match_id][FILE_NAME + 3]))                     # 行名に文字と数が混在すると、数値と判定されることも
            print('')
        
        time6 = time.time()
        print('time6', time6 - time5)
        
        print('order of similarities')
        print('{:<13}{:<13}{:<13}{:<13}{:<13}{:<13}{:<13}'.format(
              'sim','cos sim','lumen ratio','cluster no','cluster rank','manufacturer','file name'))
        for s in search_result:                                                 # 類似している順に表示する
            print('{:<13.5f}{:<13.5f}{:<13.5f}{:<13}{:<13}{:<13}{:<13}'.format( # ファイル名は長いこともあるので、最後
                   s[0],                                                        # 類似度を表示
                   s[1],
                   s[2],
                   str(s[CLUSTER_NO + 3]),                                      # クラスター番号を表示、類似度を先頭に追加してるため、+3
                   np.where(similar_clusters==s[CLUSTER_NO + 3])[0][0]+1,       # クラスターの類似度順位を表示、類似度を先頭に追加してるため、+3
                   s[MANUFACTURER + 3],                                         # メーカー名を表示、類似度を先頭に追加してるため、+3
                   s[FILE_NAME + 3]))                                           # 行名に文字と数が混在すると、数値と判定されることも
    
    time7 = time.time()
    print('time7', time7 - time6)
    
    print('--------------------'*4)
    end_time = time.time()
    elapsed_time_total = round((end_time - start_time), 5)
    print('search total: ', elapsed_time_total, ' sec')
    
    return search_result
    #return search_result[0][FILE_NAME + 3]                                     # 自己一致正答率の確認では、返り値はファイル名

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# 配光データの全検索

def search_ies_full(clusters):
    
    start_time = time.time()                                                    # 開始時刻
    
    # クエリのデータの取得
    query     = make_lights_basic(QUERY_PATH)                                   # クエリ照明器具のレコーズを作成、器具数=1なので1行のみ
    file_name = query[0][0]
    print('query: ' + file_name)
    
    # 全てのクラスター順に繰り返す
    pre_max_similarity = 0
    for i in range(len(clusters)):
        
        print('--------------------'*4)
        print('cluster ', i)
        
        cluster_k = get_lights('cluster_no = ' + str(i))
        
        if cluster_k != []:
        
            # クラスター内での類似度を計算
            similarities        = cal_similarities(cluster_k, query)
            similarities        = similarities.ravel()
            max_similarity      = similarities.max()
            max_similarity_id   = similarities.argmax()
            max_similarity_name = cluster_k[max_similarity_id][0]
            
            # 各クラスターごとに最類似照明器具を表示
            print('max similarity:     ', round(max_similarity, 5), '/ ',
                                                max_similarity_name)
            
            if max_similarity >= pre_max_similarity: 
                pre_max_similarity      = max_similarity
                pre_max_similarity_id   = max_similarity_id
                pre_max_similarity_name = max_similarity_name
                print('max similarity update: ', pre_max_similarity)
            
    end_time = time.time()                                                      # 終了時刻
    elapsed_time = round((end_time - start_time), 5)                            # 経過時間
    
    # 検索結果の表示
    print('--------------------'*4)
    print('max similarity:     ', round(pre_max_similarity, 5))
    print('max similarity:     ', pre_max_similarity_id)
    print('max similarity:     ', pre_max_similarity_name)
    print('total:              ', elapsed_time, ' sec')
    

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# 配光データ検索の自己一致正答率

def cal_search_accuracy():
    
    manufacturers = get_manufacturers_from_folder()
    for i in range(7, len(manufacturers)):
        print('--------------------'*4)
        print(i)
        
        manufacturer_path = MANUFACTURER_PATH + manufacturers[i] + '/'          # メーカーを選ぶ
        
        h, i, j = 0, 0, 0
        paths = glob.glob(manufacturer_path + '*')
        for p in paths:
            
            ies_query = os.path.basename(p)                                     # ファイル名を取得
            ies_result = search_ies(clusters, p) + '.ies'                       # 検証用は、返り値を完全一致のファイル名に変更
            if ies_query == ies_result:                                         # 検索クエリと検索結果が一致するなら
                print('correct')
                i += 1
            else:
                print('wrong')
                print(ies_query +':'+ ies_result)
            j += 1
            h += 1
            print('accuracy: ' + str(i) +'/'+str(j))
    
    print(i/j)

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# 配光データの比較

def compare_ies(file_paths):
    
    # 引数はファイルパス
    # フォルダパスのファイル数で検索か比較かを事前に場合分けしてるため
    
    '''
    まとめて取得して、2x2の類似度行列？
    '''
    
    start_time = time.time()
    
    file_name1 = os.path.basename(file_paths[0])[:-4]                           # クエリ1のファイル名、拡張子を除く
    file_name2 = os.path.basename(file_paths[1])[:-4]                           # クエリ2のファイル名、拡張子を除く
    print('compare query ', file_name1, ' & ', file_name2)
    
    # クエリ・ファイルが2つある場合
    query1  = [make_light(file_paths[0])]                                       # 引数がファイルパス、照明器具レコードの作成でリスト化
    query2  = [make_light(file_paths[1])]                                       # 引数がファイルパス、照明器具レコードの作成でリスト化
    similarities     = cal_similarities(query1, query2)
    lumen_ratio_mask = make_lumen_ratio_mask(query1,query2, 0, 0)               # 明るさの許容度は、0にする
    similarities     = similarities * lumen_ratio_mask
    
    print('similarity:   ', round(similarities[0][0], 5))
    
    end_time = time.time()
    elapsed_time_total = round((end_time - start_time), 5)
    print('compare total:', elapsed_time_total, ' sec')
    
    return similarities

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# 初期クラスターの作成

def make_initial_clusters():
    
    clusters = make_lights_basic(CLUSTER_SEED_PATH)                             # クラスター種のレコーズ作成
    
    # k個のクラスター: C1, C2 ... Ck
    # k行 x 31列のリスト
    # [[ファイル名, ... 配光リスト,差分リスト,...],
    #  [ファイル名, ... 配光リスト,差分リスト,...],
    #  ...
    #  [ファイル名, ... 配光リスト,差分リスト,...]]
    
    cluster_nos = len(clusters)
    
    # クラスター種の特定のため
    # 型番にファイル名を入力
    # 型番がないことがあるため
    
    i = 0
    for c in clusters:
        c[CLUSTER_NO] = i                                                       # クラスター番号を入力
        i += 1
    
    return clusters

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# クラスタリング（クラスターとの最小類似度を上げる）

def clustering1(clusters):
    
    # クラスター番号が割り振られた後に
    # 追加されたクラスターの方が類似している可能性があるため
    # 2回繰り返す必要がある
    
    for i in range(2):                                                          # 最大2回繰り返す
        print('--------------------'*4)
        print('Iterration     ', i )
        print('')
        
        # データが多いので
        # 各メーカーに分けて処理
        
        manufacturers = get_manufacturers_from_folder()
        for m in manufacturers:                                                 # メーカーごとに繰り返す
            print('--------------------'*4)
            print('manufacturer:  ', m )
            print('')
            
            lights = get_lights('manufacturer="'+ m +'"')                       # メーカーの照明器具レコーズの取得、検索条件は文字列なため、引用符に注意
            
            # n個の照明器具: L1, L2 ... Ln
            # n行 x 32列のリスト
            # [[ファイル名, ... 配光文字列,差分文字列],
            #  [ファイル名, ... 配光文字列,差分文字列],
            #  ...
            #  [ファイル名, ... 配光文字列,差分文字列]]
            
            # 類似度が係数を超えるまで、クラスターを追加
            clusters = add_clusters(lights, clusters)                           # 引数は、データベースが先、クラスターが後
            
            # k+j個のクラスター: C1, C2 ... Ck ... Ck+j
            # k+j行 x 32列のリスト
            # [[ファイル名, ... 配光文字列,差分文字列],
            #  [ファイル名, ... 配光文字列,差分文字列],
            #  ...
            #  [ファイル名, ... 配光文字列,差分文字列]]
            
            update_cluster_no(lights, clusters)                                 # 照明器具テーブルのクラスター番号の列を更新
    
    return clusters

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# クラスタリング（大規模クラスターの分割）

def clustering2(clusters):
    
    # クラスター番号の割り当て後
    # 各クラスターの要素数を算出
    # クラスターの要素数が500以上なら
    # そのクラスターの最小類似度を算出
    # その照明器具を新たなクラスター種にし
    # クラスターを分割
    
    # 繰り返し処理でクラスターが追加される
    # 決められた回数だけ繰り返すforではなく
    # 条件で繰り返すwhile
    
    i = 0
    while i < len(clusters):
    #while i < temp+100:
        
        print('--------------------'*4)
        print('Cluster ', i)
        print('')
        
        # 照明器具レコーズ数が多いと
        # 類似度計算中に、メモリ不足
        # 2万レコーズまで可だが、余裕をみて1万レコーズに設定
        # 繰り返し処理の最後で、照明器具レコーズを再取得し
        # 他のクラスターに移った分を補填
        # 照明器具レコーズ数は、徐々に減るので
        # 繰り返す内に全て網羅
        
        cluster_k = get_lights('cluster_no = ' + str(i), 10000)                 # クラスターkに属する照明器具レコーズの取得
        no_of_cluster_members = len(cluster_k)                                  # クラスターkの要素数
        
        # 要素数が500であれば、検索にかかる時間は許容範囲と判断
        
        while no_of_cluster_members >= 500:                                     # 要素数が500以上の場合
            
            similarities = cal_similarities(cluster_k, clusters)                # クラスターkに属する照明器具と全クラスターとの類似度行列
            
            # n個の照明器具: L1, L2 ... Ln
            # n行 x k列の類似度行列
            # array([[-, - ... -],
            #        [-, - ... -],
            #              ...
            #        [-, - ... -]])
            
            # 最大要素数10000の制限があるため
            # 前回の繰り返しに含まれていないと
            # クラスターの再割り当てが行われていない
            # そのため、現段階でクラスターkに属していても
            # 新たに追加されたクラスターに属すべきものがある
            # これらは、後の類似度再計算により、割り当て直される
            # しかし、これらの中から新たなクラスター種が選ばれ
            # それが追加されたクラスターと同一配光である場合
            # そのクラスターが空になる
            # クラスター種候補が、クラスターkに属するか再確認
            
            not_cluster_k_id = np.where(similarities.argmax(axis=1) != i)[0]    # 再計算すれば、クラスターk以外に属する照明器具のインデックス
            # array([-, - ... -])
            
            similarities          = similarities[:, i]                          # クラスターkに属する照明器具と現クラスターとの類似度行列
            sorted_similarity_id = similarities.argsort()                       # 類似度を昇順に並び替えたインデックス
            
            j=0                                                                 # j=0で、類似度の最小値
            condition = True
            while condition:
                if sorted_similarity_id[j] in not_cluster_k_id:                 # インデックスが、クラスターk以外に属するインデックスの場合
                    j += 1
                else:                                                           # インデックスが、クラスターkに属するインデックスの場合
                    
                    min_similarity     = similarities[sorted_similarity_id[j]]  # 類似度の最小値
                    min_similarity_id = sorted_similarity_id[j]                 # 類似度の最小値のインデックス
                    condition = False
            
            print('--------------------'*4)
            print('min similarity')
            print('{:<15.5f}{:15}'.format(                                      # 表示フォーマット
                   min_similarity,
                   cluster_k[min_similarity_id][FILE_NAME]))
            print('')
            
            if  min_similarity != 1:                                            # クラスター種 or 同一配光でない場合
                
                clusters  = \
                add_cluster_seed(cluster_k, clusters, min_similarity_id)        # インデックスで指定した照明器具を新たなクラスターに追加
                
                update_cluster_no(cluster_k, clusters)
                
                cluster_k = get_lights('cluster_no='+str(i),10000)              # クラスターkに属する照明器具レコーズの取得
                no_of_cluster_members = len(cluster_k)                          # クラスターkの要素数
                
            else:                                                               # 全てがクラスター種と同一配光の場合
                
                print('all the light fixtures are the same')
                no_of_cluster_members = 0                                       # 要素数>=500でも、要素数を0に設定し、繰り返しを抜ける、
                
        i += 1
    
    # クラスター分割後
    # 最初のクラスターから、クラスター番号を割り当て直す
    # 繰り返しの際も
    # クラスター番号を割り当て直すが、分割中のクラスターのみ
    # 最後にまとめて再割り当てをするのは
    # クラスター種が移動しないことが前提
    # そうでなければ、繰り返しの際に、このプロセスを含む必要がある
    # しかし、時間がかかる
    
    for i in range(len(clusters)):
        cluster_k = get_lights('cluster_no = ' + str(i))                        # 原則、要素数は500を超えない
        update_cluster_no(cluster_k, clusters) 
    
    return clusters

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# クラスタリング（クラスター内の純度を高める）

def clustering3(clusters):
    
    # クラスター番号の割り当て後
    # 各クラスター内類似度行列を算出
    # 各照明器具の類似度の平均を算出
    # 各クラスターの最小類似度を算出
    # 全クラスターで最小の最小類似度を計算し
    # (そのため繰り返し処理に時間がかかる)
    # それがある係数より小さい場合
    # その照明器具を新たなクラスター種とする
    
    condition = True
    while condition:
        
        no_of_clusters = len(clusters)
        
        # クラスター番号に欠番がないという前提
        # id=クラスター番号になる
        
        # この関数内では、以下
        # similaritiesに当たる語をsimと略す
        
        sim_mean_min_list = []
        sim_mean_min_id_list = []
        
        for i in range(no_of_clusters):
            print('--------------------'*4)
            print('Cluster ', i)
            
            cluster_k = get_lights('cluster_no = ' + str(i))                    # クラスターkに属する照明器具レコーズの取得
            
            similarities = cal_similarities(cluster_k, cluster_k)               # クラスターkに属する照明器具どうしの類似度行列
            
            # n個の照明器具: L1, L2 ... Ln
            # n行 x n列の類似度行列
            # array([[1, - ... -],
            #        [-, 1 ... -],
            #              ...
            #        [-, - ... 1]])
            # 正方対称行列、対角成分=1
            
            # クラスターkの要素がひとつだけの場合
            # array([[1]])
            
            if  len(cluster_k) > 1:                                             # クラスターkに属する照明器具が一つより多い場合
                sim_mean = (similarities.sum(axis=0)-1) / (len(cluster_k)-1)    # 自身を除く他の照明器具との類似度の平均値
                # n個の要素の配列
                # array([-, - ... -])
                
                sim_mean_min     = sim_mean.min()                               # 類似度平均の最小値
                sim_mean_min_id  = sim_mean.argmin()                            # 類似度平均の最小値のインデックス
                sim_mean_min_list.append(sim_mean_min)
                sim_mean_min_id_list.append(sim_mean_min_id)
            
            else:                                                               # クラスターkに属する照明器具が一つの場合
                # array([[1]])
                sim_mean_min_list.append(1)                                     # 自身との比較なので、類似度平均の最小値は1
                sim_mean_min_id_list.append(0)                                  # 一つしかないので、そのインデックスは0
        
        sim_mean_min_list = np.array(sim_mean_min_list)
        # k個の要素の配列
        # array([-, - ... -])
        
        # クラスター種が、クラスターの外れにある場合
        # 類似度平均の最小値の最小値が、クラスター種の可能性がある
        # クラスター種かどうか確認し
        # クラスター種の場合、次の最小値を選択する必要がある
        
        sim = cal_similarities(cluster_k, clusters)
        sorted_sim_mean_min_list_id = sim_mean_min_list.argsort()               # 類似度を昇順に並び替えたインデックス
        
        j=0                                                                     # j=0で、類似度の最小値
        condition = True
        while condition:
            sim_mean_min_min = sim_mean_min_list[sorted_sim_mean_min_list_id[j]]# 類似度平均のの最小値の最小値
            cluster_no  = sorted_sim_mean_min_list_id[j]                        # 類似度平均の最小値の最小値インデックス
            light_id = sim_mean_min_id_list[cluster_no]
            
            if  sim[light_id, cluster_no] != 1:                                 # 該当する照明器具がクラスター種でない場合
                condition = False
            else:
                j += 1
        
        print('--------------------'*4)
        print('min min similarity mean')
        print('{:<15.5f}{:<15}'.format(                                         # 表示フォーマット
               sim_mean_min_min,                                                # 類似度平均の最小値の最小値
              'cluster ' + str(cluster_no)))                                    # そのクラスター番号
        print('')
        
        if sim_mean_min_min < 0.6:                                              # 係数は要調整
            
            cluster_k = get_lights('cluster_no = ' + str(cluster_no))
            clusters  = \
            add_cluster_seed(cluster_k, clusters, light_id)                     # インデックスで指定した照明器具を新たなクラスターに追加
            
            for j in range(no_of_clusters):
                print('--------------------'*4)
                print('Cluster ', j)
                
                cluster_k = get_lights('cluster_no = ' + str(j))                # クラスターkに属する照明器具レコーズの取得
                update_cluster_no(cluster_k, clusters)                          # 照明器具テーブルのクラスター番号の列を更新
            
        else:
            condition = False
            
    return clusters


# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# クラスタリング（クラスター平均によるクラスタリング）

def clustering4(clusters):
    
    i = 0
    condition = True
    while (condition and (i < 20)):
    #for i in range(10):                                                        # テストでは14回で収束
        print('--------------------'*4)
        print('Iterration     ', i )
        print('')
    
        # 更新前のクラスター数と平均
        old_no_of_clusters = len(clusters)
        old_cluster_mean   = only_ies(clusters)
        
        # クラスター番号の再割り当て
        for j in range(len(clusters)):
            
            print('--------------------'*4)
            
            cluster_k = get_lights('cluster_no = ' + str(j))
            
            if cluster_k != []:
                update_cluster_no(cluster_k, clusters)
        
        # クラスター平均の再計算は
        # 照明器具テーブルのクラスター番号再割り当て後
        # 空のクラスター削除前
        # クラスター平均の再計算では
        # clustersの回数だけ繰り返し、照明器具テーブルを参照する
        # clustersのクラスター数と
        # 照明器具テーブルのクラスター数が同じである必要
        
        # クラスター平均の再計算
        # 照明器具テーブルの空クラスター対応済み
        clusters = cal_cluster_mean(clusters)
        
        # 更新後のクラスター数と平均
        new_no_of_clusters = len(clusters)
        new_cluster_mean   = only_ies(clusters)
        
        if old_no_of_clusters == new_no_of_clusters:
            no_change_flag = np.all(old_cluster_mean == new_cluster_mean)
            if no_change_flag:
                condition = False
                print('no cluster change')
        
        i += 1
        
    return clusters

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# クラスターの追加

def add_clusters(lights, clusters):
    
    # 類似度最小値を一定以上にするため
    
    # クラスターとの類似度を計算
    # 最も類似したクラスターでも
    # 類似度がある係数を超えない場合
    # その照明器具を新たなクラスター種とする
    
    condition = True
    while condition:
        
        similarities = cal_similarities(lights, clusters)                       # 類似度、引数は、照明器具が先、クラスターが後
        
        # n個の照明器具: L1, L2 ... Ln
        # k個のクラスター: C1, C2 ... Ck
        # n行 x k列の類似度行列
        # array([[-, - ... -],
        #        [-, - ... -],
        #              ...
        #        [-, - ... -]])
        
        # この関数内では、以下
        # similaritiesに当たる語をsimと略す
        
        sim_max          = similarities.max(axis=1)                             # 各照明器具の類似度の最大値
        # n個の要素の配列
        # array([-, - ... -])
        
        sim_max_min     = sim_max.min()                                         # 各照明器具の類似度の最大値の最小値
        sim_max_min_id  = sim_max.argmin()                                      # 各照明器具の類似度の最大値の最小値のインデックス
        sim_max_min5_id = sim_max.argsort()[0:5]                                # 各照明器具の類似度の最大値を昇順に並べたインデックス
        
        print('--------------------'*4)
        print('min5 of max similarities')
        for min5 in sim_max_min5_id:                                            # 類似度の最大値が最も小さい５つのインデックス
            min5_file_names   = lights[min5][0]
            min5_similarities = sim_max[min5]
            
            print('{:<15.5f}{:<15}'.format(                                     # 表示フォーマット
                   min5_similarities,                                           # 類似度の最大値が最も小さい５つの類似度
                   min5_file_names))                                            # 類似度の最大値が最も小さい５つのファイル名
        print('')
        
        # 類似度0.6: やや大雑把
        # 類似度0.7: 使えなくはない
        # 類似度0.8: 適正
        # 類似度0.9: より精確だが、クラスター数が増加
        # 試行結果によると
        # 0.6だと、要素数が多い
        # 0.8だと、クラスター数が多い
        # 類似度の最大値の最小値が0.7より小さいなら
        
        # 新たなクラスターはひとつずつ追加
        # 現段階で類似度の最大値の最小値が0.7以下でも
        # 新クラスターとの類似度がそれ以上かもしれないため
        
        if  sim_max_min < 0.7:                                                  # 係数は要調整
            
            clusters  = add_cluster_seed(lights, clusters, sim_max_min_id)      # インデックスで指定した照明器具を新たなクラスターに追加
            
        else:
            
            condition = False
        
    return clusters

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# クラスターの追加

def add_cluster_seed(lights, clusters, light_id):
    
    new_cluster = lights[light_id].copy()                                       # 新クラスター種の照明器具のレコード
    new_cluster[CLUSTER_NO] = len(clusters)                                     # 新クラスターの番号、0始まりのため、数=次の番号
    clusters.append(new_cluster)
    
    print('add')
    print('{:<15}{:<15}'.format(
           'cluster ' + str(new_cluster[CLUSTER_NO]),                           # 追加クラスター番号を表示、ファイル名がクラスター番号
           new_cluster[FILE_NAME]))                                             # 追加ファイル名を表示、型番がファイル名
    print('')
    
    return clusters

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# クラスター番号の更新

def update_cluster_no(lights, clusters):
    
    # 照明器具テーブルのクラスター番号の列を更新
    # クラスターテーブルは更新されない
    
    # 類似度を計算
    similarities = cal_similarities(lights, clusters)                           # 類似度、引数は、各クラスターの照明器具が先、クラスターが後
    
    # n個の照明器具: L1, L2 ... Ln
    # k個のクラスター: C1, C2 ... Ck
    # n行 x k列の類似度行列
    # array([[-, - ... -],
    #        [-, - ... -],
    #              ...
    #        [-, - ... -]])
    
    old_cluster_nos = [l[CLUSTER_NO] for l in lights]                           # 旧クラスター番号、リスト
    new_cluster_nos = similarities.argmax(axis=1)                               # 新クラスター番号、配列
    
    # クラスター番号が変わった照明器具のみ更新
    # 新旧のクラスター番号を比較
    id_to_update = np.where(old_cluster_nos != new_cluster_nos)                 # 新旧のクラスター番号が一致しない照明器具のインデックス
    # (array([-, - ... -]),)
    id_to_update = id_to_update[0]                                              # タプルから初めの要素だけ抽出
    # array([-, - ... -])
    
    print('--------------------'*4)
    print('update cluster nos - ', len(id_to_update), ' lights')
    print('')
    
    file_names = [l[FILE_NAME] for l in lights]                                 # 照明器具レコーズのファイル名を取得
    cluster_no_update_info = (                                                  # クラスター番号の更新情報の作成
    [[c,f] for c, f in zip(new_cluster_nos, file_names)])                       # [[cluster_no, file_name], ...]
    cluster_no_update_info = np.array(cluster_no_update_info)                   # インデックスを使用するため配列化
    cluster_no_update_info = cluster_no_update_info[id_to_update]               # 変わったもののみ抽出
    
    # 照明器具テーブルのクラスター番号を更新
    cur.executemany( ' UPDATE light_table '
                     ' SET    cluster_no = ?      '
                     ' WHERE  file_name  = ?      '
                     , cluster_no_update_info 
                   )
    
    con.commit()
    
    # 更新されたクラスター番号を表示
    print('{:<15}{:<15}{:<15}'.format(
           'old', 'new', 'file name'))
    for i in id_to_update:                                                      # 新旧で一致しない行だけ表示
        old_cluster_no = old_cluster_nos[i]
        new_cluster_no = new_cluster_nos[i]
        file_name      = lights[i][FILE_NAME]
        print('{:<15}{:<15}{:<15}'.format(
                'cluster ' + str(old_cluster_no), 
                'cluster ' + str(new_cluster_no), 
                file_name))
    print('')

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# クラスター平均の計算

def cal_cluster_mean(clusters):
    
    print('--------------------'*4)
    print('update cluster mean')
    print('')
    
    for k in range(len(clusters)):                                              # 各クラスターごとに繰り返す
        
        print('--------------------'*4)
        print('cluster ', k,)
        print('')
        
        start_time = time.time()
        
        cluster_k = get_lights('cluster_no=' + str(k))                          # クラスター番号=kの照明器具レコーズを取得
        
        # クラスターkに分類されている
        # n個の照明器具: L1, L2 ... Ln
        # n行 x 32列のリスト
        # [[ファイル名, ...配光リスト,差分リスト...],
        #  [ファイル名, ...配光リスト,差分リスト...],
        #   ...
        #  [ファイル名, ...配光リスト,差分リスト...]]
        
        if cluster_k == []:                                                     # 空クラスターの場合、再計算なし
            
            print('cluster is empty')
        
        else:
            
            # クラスター内の全照明器具の配光を平均する
            # クラスター種の照明器具の配光からずれる
            
            # クラスターは
            # ベクトルの向き(コサイン類似度)による分類
            # ベクトルの大きいものと小さいものが混在
            # そのまま平均を計算すると
            # 極端に大きいベクトルのレコードの影響が強い
            # 問題ないかもしれないが，ここではまず正規化し平均を計算
            # 平均の計算後は、クラスターとの距離計算はさらに意味を持たない
            
            cluster_k_normd = norm_lights(cluster_k)
            cluster_k_normd_ies = only_ies(cluster_k_normd)
            to_df(cluster_k_normd)
            # n行 x 1369列 の配列
            # array([[-, - ... -],
            #        [-, - ... -],
            #        ...
            #        [-, - ... -]])
            
            # 光度
            cluster_k_normd_ies_mean = cluster_k_normd_ies.mean(axis=0).tolist()# クラスターkの配光データの平均を計算し、リスト化
            cluster_k_normd_ies_mean_ser = \
            pd.Series(cluster_k_normd_ies_mean, index=IES_COLUMNS)              # 差分や光束の再計算のため、シリーズ化
            # このベクトルの大きさは、1ではない可能性も
            
            # 光度の差分
            cluster_k_diff_theta = \
            two_to_one(diff_theta(one_to_two(
            cluster_k_normd_ies_mean_ser))).values.ravel()                      # θ方向の差分の再計算、配列化、一元化、1368要素の配列
            
            cluster_k_diff_phi   = \
            two_to_one(diff_phi(one_to_two(
            cluster_k_normd_ies_mean_ser))).values.ravel()                      # φ方向の差分の再計算、配列化、一元化、1295要素の配列
            
            cluster_k_diff = \
            np.hstack([cluster_k_diff_theta, cluster_k_diff_phi])               # θとφ方向の差分を横に連結、2663要素の配列
            
            cluster_k_diff = cluster_k_diff.tolist()
            
            # 光束
            cluster_k_lumen = cal_lm(one_to_two(cluster_k_normd_ies_mean_ser)) 
            
            # 更新
            clusters[k][IES]   = cluster_k_normd_ies_mean                       # 光度の更新
            clusters[k][DIFF]  = cluster_k_diff                                 # 差分の更新
            clusters[k][LUMEN] = cluster_k_lumen                                # 光束の更新
            # ベクトルの大きさに意味はないので、最大光度は更新しない
            
        end_time = time.time()
        elapsed_time = end_time - start_time
        print(round(elapsed_time, 5), ' sec')
    
    return clusters
    
# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# クラスターテーブルの更新

def update_cluster_table(clusters):
    
    clusters_for_sql = copy.deepcopy(clusters)                                  # 複合オブジェクトのコピーのため
    
    # 更新用は、json文字列にする必要がある
    
    clusters_for_sql = to_json(clusters_for_sql)
    
    # 全削除し全追加している
    # SQliteにTRUNCATE文はない
    
    cur.execute('DELETE FROM cluster_table')
    
    cur.executemany( ' INSERT INTO cluster_table '
                     ' VALUES      (' + ('?,'*32)[:-1] + ')'                    # ?はプレースホルダー、最後のカンマを削除
                   # '(?,?,...32個...?)'の文字列
                     , clusters_for_sql
                   )
    
    con.commit()

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# 各クラスターの配光分布図の描画

(((x-x.mean(axis=0))**2).sum(axis=0)/len(x))[1][1]
x_cov = np.cov(x, rowvar=False, bias=True)
x_vals, x_vecs = np.linalg.eig(x_cov)
sort_index = x_vals.argsort()[::-1].tolist()
ies_column_names = np.array(IES_COLUMNS)
ies_column_names[sort_index]
# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# 各クラスターの配光分布図の描画

def plot_clusters(clusters):
    
    # 正規化しないと、
    # 値の大小にバラツキが大きい場合、
    # 値の大きいものに合わせて座標軸の縮尺が設定されるため
    # 値の小さいものがすごく小さくしか表示されない
    
    clusters_normd        = norm_lights(clusters)                               # クラスターレコーズの正規化
    clusters_normd_ies_df = to_df_ies(clusters_normd)                           # データフレーム化
    
    # 極座標の角度は、
    # 全照明器具で共通のため
    # 最初の照明器具を基に算出
    
    theta, phi = cal_theta_phi(clusters_normd_ies_df.iloc[0])                   # 極座標の角度を計算、引数はies_1D
    
    # 1ページに10個(2行5列)のグラフを配置
    # 各グラフが各クラスターを表す
    # クラスターごとの特徴把握やクラスター間比較に適する
    # 一方、クラスター内の異なる照明器具の配光分布が同じ色で描かれるため、
    # どの線がどの照明器具に対応するか特定できない
    
    no_of_clusters = len(clusters)                                              # クラスターの数
    no_of_pages    = (no_of_clusters-1)//10+1                                   # 1ページに10個のグラフを配置した時に必要なページ数
    
    # クラスター数=kの時、(k-1)//10+1 ページ必要
    # 例: クラスター数=10の時、 9//10+1 = 1ページ
    # 例: クラスター=11の時、10//10+1 = 2ページ
    #for j in range(2):
    for j in range(no_of_pages):                                                # 各ページで繰り返す、jはクラスターの十の位
        print('--------------------'*4)
        print('Page ', j)  
        
        fig, ax = \
        plt.subplots(2,5,figsize=(25,13), subplot_kw=dict(projection='polar'))  # 極座標を２行５列配置 
        
        ax1 = ax.ravel()                                                        # 繰り返しのため一次元化
        for k in range(0,min(10,(no_of_clusters-(j*10)))):                      # 各クラスターで繰り返す、kはクラスターの一の位
            
            # 10個のグラフで一区切り
            # 例: クラスター数12の時 
            # 1ページ目(j=0の時)、k=0,1,2,3,4,5,6,7,8,9
            # 2ページ目(j=1の時)、k=0,1
            # 最大でrange(10)なので、kは9を超えない
            # 以後、クラスター番号は、j*10+k になる
            
            ies_1D = clusters_normd_ies_df.iloc[j*10+k]                         # クラスターkの配光ベクトル
            r_0_180, r_90_270, r_30, r_150 = cal_r(ies_1D)                      # 極座標の半径を計算
            symmetry = clusters[j*10+k][SYMMETRY]                               # 対称性のタイプ
            
            # グラフの設定
            ax1[k].set_theta_zero_location('S')                                 # 0度を南にする
            ax1[k].set_title('Cluster '+str(j*10+k), fontsize=13)               # タイトルの書式設定
            ax1[k].set_thetagrids(THETA_GRIDS, labels=THETA_GRIDS_LABELS)
            
            # クラスターkの平均値を描画
            ax1[k].plot(theta, r_0_180,label='0-180', color='black', alpha=0.5) # k番目のグラフに平均配光分布を描出、φ=0-180度
            ax1[k].plot(theta,r_90_270,label='90-270',color='black', alpha=0.5, 
                                       linestyle='dashed')                      # k番目のグラフに平均配光分布を描出、φ=90-270度
            
            # クラスターkの各照明器具を描画
            lights = get_lights('cluster_no = ' + str(j*10+k))                  # クラスターkの照明器具レコーズを取得
            n = len(lights)
            
            if lights != []:                                                    # クラスターが空でない場合
                
                lights_normd = norm_lights(lights)                              # 照明器具レコーズの正規化
                lights_normd_ies_df = to_df_ies(lights_normd)                   # データフレーム化
                
                similarities = cal_similarities(lights, lights)
                similarities_mean = (similarities.sum()-n) / max((n**2 - n), 1) # 要素=1で分母0ではなく1にする
                
                for i in range(len(lights)):                                    # 各照明器具で繰り返す
                        
                        ies_1D = lights_normd_ies_df.iloc[i]                    # i番目のiesデータを抽出
                        
                        r_0_180, r_90_270, r_30, r_150 = cal_r(ies_1D)          # 極座標の半径を計算
                        
                        ax1[k].plot(theta, r_0_180, label='0-180', 
                                                    color=COLOR_LIST[k],
                                                    alpha=0.5)                  # k番目のグラフに配光分布を描出、水平角度0-180度
                        
                        ax1[k].plot(theta, r_90_270,label='90-270',
                                                    color=COLOR_LIST[k],
                                                    alpha=0.5,
                                                    linestyle='dashed')         # k番目のグラフに描出、水平角度90-270度
                
                ax_position = ax1[k].get_position()                             # クラスターkの位置を取得
                fig.text((ax_position.x0+ax_position.x1)/2,
                          ax_position.y0-0.04,
                          str(len(lights)) +' lights' + 
                          '/ similarity: '+ str(round(similarities_mean, 5)), 
                          color='black',horizontalalignment='center')
        
        fig.savefig(CLUSTER_GRAPH_PATH + 'Light Distribution/Light Distribution ' + str(j))
        plt.cla()                                                               # 現在のax1[k]をクリア
        plt.clf()                                                               # 現在のfigをクリア
        plt.close()

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# 各照明器具の配光分布図の描画

def plot_lights(search_condition):                                              # 引数は、文字列
    
    lights = get_lights(search_condition)
    
    # 正規化しないと、
    # 値の大小にバラツキが大きい場合、
    # 値の大きいものに合わせて座標軸の縮尺が設定されるため
    # 値の小さいものがすごく小さくしか表示されない
    
    lights_normd        = norm_lights(lights)                                   # クラスター照明レコーズの正規化
    lights_normd_ies_df = to_df_ies(lights_ies_normd)                           # データフレーム化
    
    # 極座標の角度は、
    # 全照明器具で共通のため
    # 最初の照明器具を基に算出
    
    theta, phi = cal_theta_phi(lights_normd_ies_df.iloc[0])                     # 極座標の角度を計算、引数はies_1D
    
    # 1ページに10個(2行5列)のグラフを配置
    # 各グラフに5つの配光分布を表示
    # ５つは異なる色で描かれ、凡例に器具名を表示するため、
    # どの線がどの照明器具に対応するか分かる
    
    no_of_lights = len(lights)                                                  # 照明器具レコーズの数
    no_of_graphs = (no_of_lights-1) // 5 + 1                                    # 各グラフに5個のiesを描画した時に必要なグラフ数
    no_of_pages  = (no_of_lights-1) // 50 + 1                                   # 各ページに5x10個のiesを描画した時に必要なページ数
    
    # 例: 照明器具数=72の時、 15グラフ、2ページ必要
    # 各グラフに5つずつ配光分布が描かれるが、
    # 最後のグラフだけ2つしかない
    
    for h in range(no_of_pages):                                                # 各ページで繰り返す
        fig, ax = plt.subplots(2, 5, figsize = (25, 13), 
                               subplot_kw = dict(projection='polar'))           # 極座標を２行５列配置
        ax1 = ax.ravel()                                                        # 繰り返しのために一次元化
        for i in range(min(10, no_of_graphs - h*10)):                           # 各グラフで繰り返す、
            
            # 例: グラフ数が12の時
            # 1ページ目(h=0)の時、i=0,1,2,3,4,5,6,7,8,9
            # 2ページ目(h=1)の時、i=0,1
            # 最大でrange(10)なので、kは9を超えない
            
            # グラフの設定
            ax1[i].set_theta_zero_location('S')                                 # 0度を南にする
            ax1[i].set_title(str(i*5)+'-', fontsize=13)                         # タイトルの書式設定
            ax1[i].set_thetagrids(THETA_GRIDS, labels=THETA_GRIDS_LABELS)
            
            if  i == (no_of_graphs - h*10) - 1:                                 # 最後のグラフを描画する時
                k = no_of_lights % 5                                            # kは5で割った余りだけ
                
                # 例: グラフ数が12で、グラフが12番目の時
                # h=1, i=1, (12-1*10)-1=1
                # 条件が真
                # 照明器具数は56,57,58,59,60の４通り
                # それぞれに、グラフに1つ,2つ,3つ,4つ,5つしか描かれない
                
            else:
                k = 5                                                           # kは5
                
                # 上記以外は
                # 各グラフに5つの配光分布が描かれる
            
            for j in range(k):                                                  # 各グラフごとにk回繰り返す、基本５回だが、最後のグラフの描画の時だけ要変更
                
                ies_1D = lights_normd_ies_df.iloc[h*50 + i*5 + j]
                r_0_180, r_90_270, r_30, r_150 = cal_r(ies_1D)                  # 極座標の半径を計算
                file_name = lights[h*50 + i*5 + j][0]                           # ファイル名を取得、拡張子.iesを除く
                ax1[i].plot(theta,r_0_180, 
                            label=file_name + ' 0-180', 
                            color=COLOR_LIST[j], 
                            alpha=0.5)                                          # φ=0-180度
                
                ax1[i].plot(theta,r_90_270, 
                            color=COLOR_LIST[j], 
                            alpha=0.5, 
                            linestyle='dashed')                                 # φ=90-270度、重複するので凡例なし
            
            ax1[i].legend(bbox_to_anchor=(0.5,-0.25),loc='center')              # 凡例はグラフの外側の左上
        
        fig.savefig(CLUSTER_GRAPH_PATH + 'Selected Light Fixtures ' + str(h))
            
    plt.cla()                                                                   # 現在のax1[k]をクリア
    plt.clf()                                                                   # 現在のfigをクリア
    plt.close()

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
# 配光分布図の描画（２次元）

def plot_ies():
    
    file_paths = [f for f in Path(PLOT_PATH).rglob('*.ies')]                    # iesの読み込み、データフレームのリスト
    file_name1 = os.path.basename(file_paths[0])[:-4]
    file_name2 = os.path.basename(file_paths[1])[:-4]
    ies1   = read_ies(str(file_paths[0]))[5]
    ies2   = read_ies(str(file_paths[1]))[5]
    
    # 配光分布図用のデータ作成
    ies_1D = two_to_one(ies1)                                                   # 各照明器具に共通、最初のデータを抽出
    theta, phi = cal_theta_phi(ies_1D)                                          # 極座標の角度を計算
    
    r1 = cal_r(two_to_one(ies1))                                                # ies1の極座標の半径を計算
    r2 = cal_r(two_to_one(ies2))                                                # ies2の極座標の半径を計算
    
    # 類似度の計算
    distance = int(cal_distance(ies1, ies2))                                    # 配光ベクトル間の距離の算出
    cos_similarity = round(cal_cos_similarity(ies1, ies2),5)                    # 配光ベクトル間のコサイン類似度の算出
    correlation_coefficient = round(cal_corrcoef(ies1, ies2),5)                 # 配光ベクトル間の相関係数の算出
    
    # 最大光度の算出
    cd_max1   = cal_cd_max(ies1)[0]                                             # ies1の最大光度を算出
    cd_max2   = cal_cd_max(ies2)[0]                                             # ies2の最大光度を算出
    cd_max    = max(cd_max1, cd_max2)                                           # 最大光度を算出
    
    # 光束の算出
    lumen_sum1 = cal_lm(ies1)                                                   # 光束を算出、小数第２位で四捨五入
    lumen_sum2 = cal_lm(ies2)                                                   # 光束を算出、小数第２位で四捨五入
    
    similarity = round(cos_similarity * 
                       min(lumen_sum1, lumen_sum2) / 
                       max(lumen_sum1, lumen_sum2) * 100, 1)
    
    text =  ' Distance:' + str(distance)
    text += ' Cos Similarity:' + str(cos_similarity)
    text += ' Correlation Coeffient:' + str(correlation_coefficient)
    text1 = ' file name: ' + file_name1 + '/ ' + file_name2
    text2 = ' Max. Luminous Intensity: '+str(cd_max1)+'cd/ '+str(cd_max2)+'cd'
    text3 = ' Luminous Flux: '+str(lumen_sum1)+'lm/ '+ str(lumen_sum2)+'lm'
    text4 = ' Similarity: ' + str(similarity) + '%'
    
    # 配光分布図の描画開始
    fig,ax = plt.subplots(2,1,figsize=(10,10),subplot_kw=dict(projection='polar')) # 極座標を２行２列配置
    ax1 = ax.ravel()                                                            # 繰り返しのために一次元化
    
    # 鉛直配光分布図の出力（光度）
    ax1[0].set_theta_zero_location('S')                                         # 0度を南にする
    ax1[0].set_thetagrids(THETA_GRIDS, labels=THETA_GRIDS_LABELS)
    ax1[0].set_title('LUMINOUS INTENSITY', fontsize=13)                         # タイトルの書式設定
    ax1[0].set_rlim([0, cd_max*1.1])                                            # 半径の最大値を設定
    ax1[0].plot(theta,r1[0], label='ies1 H 0-180d', color=COLOR_LIST[0])        # 水平角度0-180度
    ax1[0].plot(theta,r1[1], label='ies1 H 90-270d',color=COLOR_LIST[0],linestyle='dashed')  # 水平角度90-270度
    ax1[0].plot(theta,r2[0], label='ies2 H 0-180d', color=COLOR_LIST[1])        # 水平角度0-180度
    ax1[0].plot(theta,r2[1], label='ies2 H 90-270d',color=COLOR_LIST[1],linestyle='dashed')  # 水平角度90-270度
    ax1[0].legend(bbox_to_anchor=(1.15,1),loc='upper left')                     # 凡例はグラフの外側の左上
    
    # 水平配光分布図の出力（光度）
    ax1[1].set_theta_zero_location('E')                                         # 0度を東にする
    ax1[1].set_thetagrids(THETA_GRIDS, labels=PHI_GRIDS_LABELS)
    ax1[1].set_rlim([0, cd_max*1.1])                                            # 半径の最大値を設定
    ax1[1].plot(phi,r1[2], label='ies1 V 30d', color=COLOR_LIST[0])             # 水平面より下
    ax1[1].plot(phi,r1[3], label='ies1 V 150d',color=COLOR_LIST[0],linestyle='dashed')  # 水平面より上
    ax1[1].plot(phi,r2[2], label='ies2 V 30d', color=COLOR_LIST[1])             # 水平面より下
    ax1[1].plot(phi,r2[3], label='ies2 V 150d',color=COLOR_LIST[1],linestyle='dashed')  # 水平面より上
    ax1[1].legend(bbox_to_anchor=(1.15,1),loc='upper left')                     # 凡例はグラフの外側の左上
    
    fig.text(0.5,0.01, text4, color='black', horizontalalignment='center')      # 配光ベクトル間の類似度の表示
    fig.text(0.5,0.07, text1, color='black', horizontalalignment='center')
    fig.text(0.5,0.05, text2, color='black', horizontalalignment='center')
    fig.text(0.5,0.03, text3, color='black', horizontalalignment='center')
    
    plt.show()
    
# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
#  配光分布描画用の角度の算出

def cal_theta_phi(ies_1D):                                                      # 引数は、iesのシリーズ
    
    ies = one_to_two(ies_1D)                                                    # 二次元化
    theta_interval, phi_interval = theta_phi_interval(ies)
    
    # θ方向
    theta = np.append(np.arange(  0,181,theta_interval),
                      np.arange(180,361,theta_interval))                        # 362要素の配列、[0,1,2,...180,180,...360]
    theta = theta / 180 * np.pi                                                 # 弧度法からラジアンに変更
    
    # φ方向
    phi = np.arange(0,361,phi_interval)                                         # 361要素の配列、[0,1,2,...180,...360]
    phi = phi / 180 * np.pi                                                     # 弧度法からラジアンに変更
    
    return theta, phi

# """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
#  配光分布描画用の半径の算出

def cal_r(ies_1D):                                                              # 引数は、iesのシリーズ
    
    ies = one_to_two(ies_1D)                                                    # 二次元化
    
    # θ方向
    r_list = []                                                                 # 空のリストを作成
    for i, j in [[0,180],[90,270]]:                                             # 水平角度0度と180度のペア、90度と270度のペアで、繰り返す
        r_i  = ies.loc[i,:]                                                     # 光度のシリーズ、1回目は水平角度0度、2回目は水平角度90度
        r_j  = ies.loc[j,:]                                                     # 光度のシリーズ、1回目は水平角度180度、2回目は水平角度270度
        r_j  = r_j[::-1]                                                        # グラフの線をつなげるため、逆順
        r    = r_i.append(r_j).values                                           # 一つの光度シリーズにし、配列化
        r_list.append(r)                                                        # 半径の配列をリストに追加
    r_0_180  = r_list[0]                                                        # 362要素の配列、[0,1,2,...180,180,...360]
    r_90_270 = r_list[1]                                                        # 362要素の配列、[0,1,2,...180,180,...360]
    
    # φ方向
    r_list = []                                                                 # 空のリストを作成
    for i in [30,150]:                                                          # 抽出する鉛直角度をリストで指定し、繰り返す
        r = (ies.loc[:,i] * np.sin(i /180 * np.pi)).values                      # 鉛直角度i度方向を抽出し、水平方向成分を計算し、配列化
        r_list.append(r)                                                        # 半径の配列をリストに追加
    r_30  = r_list[0]                                                           # 361要素の配列、[0,1,2,...180,...360]
    r_150 = r_list[1]                                                           # 361要素の配列、[0,1,2,...180,...360]
    
    return r_0_180, r_90_270, r_30, r_150
