#!/usr/bin/env python3
"""Rewrite the embedded PDF outlines for reference textbooks.

The source files are scans.  Some of them unfortunately ship with one outline
entry per page, which makes both Preview and the in-app reader unusable.  This
tool deliberately rebuilds an outline from verified table-of-contents data and
never changes page content.  It writes a full backup before replacing a file.
"""

from __future__ import annotations

import argparse
import os
import re
import shutil
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path

from pypdf import PdfReader, PdfWriter


MATH_ROOT = Path("/Users/chuan/高中数学/中学教材/高中/数学")

# Page numbers below are PDF page numbers (one-based), checked against each
# book's printed contents page.  Keeping this explicit is safer than guessing
# from unreliable OCR in the scanned files.
@dataclass(frozen=True)
class OutlineEntry:
    level: int
    title: str
    printed_page: int
    page_offset: int = 8

    @property
    def pdf_page(self) -> int:
        return self.printed_page + self.page_offset


# This first volume is transcribed from its four printed contents pages.  The
# lowest visible layer (1.1, 1.2 …) becomes a real nested PDF bookmark rather
# than a synthetic page label.  The remaining three volumes are temporarily
# chapter-level below and are progressively replaced in the same format.
BDS_OUTLINES: dict[str, list[OutlineEntry]] = {
    "北师大-必修1.pdf": [
        OutlineEntry(0, "第一章 预备知识", 1),
        OutlineEntry(1, "§ 1 集合", 2),
        OutlineEntry(2, "1.1 集合的概念与表示", 2),
        OutlineEntry(2, "1.2 集合的基本关系", 5),
        OutlineEntry(2, "1.3 集合的基本运算", 8),
        OutlineEntry(1, "§ 2 常用逻辑用语", 14),
        OutlineEntry(2, "2.1 必要条件与充分条件", 14),
        OutlineEntry(2, "2.2 全称量词与存在量词", 18),
        OutlineEntry(1, "§ 3 不等式", 24),
        OutlineEntry(2, "3.1 不等式的性质", 24),
        OutlineEntry(2, "3.2 基本不等式", 27),
        OutlineEntry(1, "§ 4 一元二次函数与一元二次不等式", 33),
        OutlineEntry(2, "4.1 一元二次函数", 33),
        OutlineEntry(2, "4.2 一元二次不等式及其解法", 35),
        OutlineEntry(2, "4.3 一元二次不等式的应用", 39),
        OutlineEntry(0, "第二章 函数", 49),
        OutlineEntry(1, "§ 1 生活中的变量关系", 50),
        OutlineEntry(1, "§ 2 函数", 54),
        OutlineEntry(2, "2.1 函数概念", 54),
        OutlineEntry(2, "2.2 函数的表示法", 56),
        OutlineEntry(1, "§ 3 函数的单调性和最值", 61),
        OutlineEntry(1, "§ 4 函数的奇偶性与简单的幂函数", 66),
        OutlineEntry(2, "4.1 函数的奇偶性", 66),
        OutlineEntry(2, "4.2 简单幂函数的图象和性质", 67),
        OutlineEntry(0, "第三章 指数运算与指数函数", 75),
        OutlineEntry(1, "§ 1 指数幂的拓展", 76),
        OutlineEntry(1, "§ 2 指数幂的运算性质", 80),
        OutlineEntry(1, "§ 3 指数函数", 84),
        OutlineEntry(2, "3.1 指数函数的概念", 84),
        OutlineEntry(2, "3.2 指数函数的图象和性质", 84),
        OutlineEntry(0, "第四章 对数运算与对数函数", 97),
        OutlineEntry(1, "§ 1 对数的概念", 98),
        OutlineEntry(1, "§ 2 对数的运算", 102),
        OutlineEntry(2, "2.1 对数的运算性质", 102),
        OutlineEntry(2, "2.2 换底公式", 104),
        OutlineEntry(1, "§ 3 对数函数", 110),
        OutlineEntry(2, "3.1 对数函数的概念", 110),
        OutlineEntry(2, "3.2 对数函数 y=log₂x 的图象和性质", 111),
        OutlineEntry(2, "3.3 对数函数 y=logₐx 的图象和性质", 114),
        OutlineEntry(1, "§ 4 指数函数、幂函数、对数函数增长的比较", 119),
        OutlineEntry(1, "§ 5 信息技术支持的函数研究", 121),
        OutlineEntry(0, "第五章 函数应用", 129),
        OutlineEntry(1, "§ 1 方程解的存在性及方程的近似解", 130),
        OutlineEntry(2, "1.1 利用函数性质判定方程解的存在性", 130),
        OutlineEntry(2, "1.2 利用二分法求方程的近似解", 132),
        OutlineEntry(1, "§ 2 实际问题中的函数模型", 136),
        OutlineEntry(2, "2.1 实际问题的函数刻画", 136),
        OutlineEntry(2, "2.2 用函数模型解决实际问题", 139),
        OutlineEntry(0, "第六章 统计", 145),
        OutlineEntry(1, "§ 1 获取数据的途径", 146),
        OutlineEntry(2, "1.1 直接获取与间接获取数据", 146),
        OutlineEntry(2, "1.2 普查和抽查", 147),
        OutlineEntry(2, "1.3 总体和样本", 149),
        OutlineEntry(1, "§ 2 抽样的基本方法", 153),
        OutlineEntry(2, "2.1 简单随机抽样", 153),
        OutlineEntry(2, "2.2 分层随机抽样", 157),
        OutlineEntry(1, "§ 3 用样本估计总体的分布", 161),
        OutlineEntry(2, "3.1 从频数到频率", 161),
        OutlineEntry(2, "3.2 频率分布直方图", 163),
        OutlineEntry(1, "§ 4 用样本估计总体的数字特征", 168),
        OutlineEntry(2, "4.1 样本的数字特征", 168),
        OutlineEntry(2, "4.2 分层随机抽样的均值与方差", 171),
        OutlineEntry(2, "4.3 百分位数", 175),
        OutlineEntry(0, "第七章 概率", 183),
        OutlineEntry(1, "§ 1 随机现象与随机事件", 184),
        OutlineEntry(2, "1.1 随机现象", 184),
        OutlineEntry(2, "1.2 样本空间", 184),
        OutlineEntry(2, "1.3 随机事件", 188),
        OutlineEntry(2, "1.4 随机事件的运算", 190),
        OutlineEntry(1, "§ 2 古典概型", 196),
        OutlineEntry(2, "2.1 古典概型的概率计算公式", 196),
        OutlineEntry(2, "2.2 古典概型的应用", 198),
        OutlineEntry(1, "§ 3 频率与概率", 208),
        OutlineEntry(1, "§ 4 事件的独立性", 214),
        OutlineEntry(0, "第八章 数学建模活动（一）", 223),
        OutlineEntry(1, "§ 1 走近数学建模", 224),
        OutlineEntry(1, "§ 2 数学建模的主要步骤", 227),
        OutlineEntry(1, "§ 3 数学建模活动的主要过程", 230),
    ],
    "北师大-必修2.pdf": [
        OutlineEntry(0, "第一章 三角函数", 1),
        OutlineEntry(1, "1 周期变化", 2),
        OutlineEntry(1, "2.1 角的概念推广", 5),
        OutlineEntry(1, "2.2 象限角及其表示", 6),
        OutlineEntry(1, "3.1 弧度概念", 9),
        OutlineEntry(1, "3.2 弧度与角度的换算", 10),
        OutlineEntry(1, "4.1 单位圆与任意角的正弦函数、余弦函数定义", 14),
        OutlineEntry(1, "4.2 单位圆与正弦函数、余弦函数的基本性质", 17),
        OutlineEntry(1, "4.3 诱导公式与对称", 20),
        OutlineEntry(1, "4.4 诱导公式与旋转", 22),
        OutlineEntry(1, "5.1 正弦函数的图象与性质再认识", 28),
        OutlineEntry(1, "5.2 余弦函数的图象与性质再认识", 34),
        OutlineEntry(1, "6.1 探究 ω 对 y=sin(ωx) 图象的影响", 42),
        OutlineEntry(1, "6.2 探究 φ 对 y=sin(x+φ) 图象的影响", 45),
        OutlineEntry(1, "6.3 探究 A 对 y=A sin(ωx+φ) 图象的影响", 48),
        OutlineEntry(1, "7.1 正切函数的定义", 58),
        OutlineEntry(1, "7.2 正切函数的诱导公式", 59),
        OutlineEntry(1, "7.3 正切函数的图象与性质", 60),
        OutlineEntry(1, "8 三角函数的简单应用", 66),
        OutlineEntry(0, "第二章 平面向量及其应用", 77),
        OutlineEntry(1, "1.1 位移、速度、力与向量的概念", 78),
        OutlineEntry(1, "1.2 向量的基本关系", 80),
        OutlineEntry(1, "2.1 向量的加法", 84),
        OutlineEntry(1, "2.2 向量的减法", 88),
        OutlineEntry(1, "3.1 向量的数乘运算", 92),
        OutlineEntry(1, "3.2 向量的数乘与向量共线的关系", 95),
        OutlineEntry(1, "4.1 平面向量基本定理", 99),
        OutlineEntry(1, "4.2 平面向量及运算的坐标表示", 101),
        OutlineEntry(1, "5.1 向量的数量积", 107),
        OutlineEntry(1, "5.2 向量数量积的坐标表示", 110),
        OutlineEntry(1, "5.3 利用数量积计算长度与角度", 111),
        OutlineEntry(1, "6.1 余弦定理与正弦定理", 114),
        OutlineEntry(1, "6.2 平面向量在几何、物理中的应用举例", 125),
        OutlineEntry(0, "第三章 数学建模活动（二）", 139),
        OutlineEntry(1, "1.1 回顾：数学建模活动的过程", 140),
        OutlineEntry(1, "1.2 数学建模活动的设计与实施——测量建筑物的高度", 141),
        OutlineEntry(1, "1.3 尝试数学建模选题", 143),
        OutlineEntry(1, "2 自主数学建模的开题交流", 144),
        OutlineEntry(0, "第四章 三角恒等变换", 145),
        OutlineEntry(1, "1.1 基本关系式", 146),
        OutlineEntry(1, "1.2 由一个三角函数值求其他三角函数值", 146),
        OutlineEntry(1, "1.3 综合应用", 148),
        OutlineEntry(1, "2.1 两角和与差的余弦公式及其应用", 152),
        OutlineEntry(1, "2.2 两角和与差的正弦、正切公式及其应用", 154),
        OutlineEntry(1, "2.3 三角函数的叠加及其应用", 157),
        OutlineEntry(1, "2.4 积化和差与和差化积公式", 159),
        OutlineEntry(1, "3.1 二倍角公式", 164),
        OutlineEntry(1, "3.2 半角公式", 165),
        OutlineEntry(0, "第五章 复数", 175),
        OutlineEntry(1, "1.1 复数的概念", 176),
        OutlineEntry(1, "1.2 复数的几何意义", 177),
        OutlineEntry(1, "2.1 复数的加法与减法", 181),
        OutlineEntry(1, "2.2 复数的乘法与除法", 183),
        OutlineEntry(1, "2.3 复数乘法几何意义初探", 187),
        OutlineEntry(1, "3.1 复数的三角表示式", 191),
        OutlineEntry(1, "3.2 复数乘除运算的几何意义", 192),
        OutlineEntry(0, "第六章 立体几何初步", 203),
        OutlineEntry(1, "1.1 构成空间几何体的基本元素", 204),
        OutlineEntry(1, "1.2 简单多面体——棱柱、棱锥和棱台", 205),
        OutlineEntry(1, "1.3 简单旋转体——球、圆柱、圆锥和圆台", 208),
        OutlineEntry(1, "2 直观图", 213),
        OutlineEntry(1, "3.1 空间图形基本位置关系的认识", 219),
        OutlineEntry(1, "3.2 刻画空间点、线、面位置关系的公理", 220),
        OutlineEntry(1, "4.1 直线与平面平行", 228),
        OutlineEntry(1, "4.2 平面与平面平行", 231),
        OutlineEntry(1, "5.1 直线与平面垂直", 238),
        OutlineEntry(1, "5.2 平面与平面垂直", 243),
        OutlineEntry(1, "6.1 柱、锥、台的侧面展开与面积", 250),
        OutlineEntry(1, "6.2 柱、锥、台的体积", 252),
        OutlineEntry(1, "6.3 球的表面积和体积", 254),
    ],
    "北师大-选择性必修1.pdf": [
        OutlineEntry(0, "第一章 直线与圆", 1),
        OutlineEntry(1, "1.1 一次函数的图象与直线的方程", 2),
        OutlineEntry(1, "1.2 直线的倾斜角、斜率及其关系", 2),
        OutlineEntry(1, "1.3 直线的方程", 8),
        OutlineEntry(1, "1.4 两条直线的平行与垂直", 16),
        OutlineEntry(1, "1.5 两条直线的交点坐标", 19),
        OutlineEntry(1, "1.6 平面直角坐标系中的距离公式", 21),
        OutlineEntry(1, "2.1 圆的标准方程", 28),
        OutlineEntry(1, "2.2 圆的一般方程", 31),
        OutlineEntry(1, "2.3 直线与圆的位置关系", 34),
        OutlineEntry(1, "2.4 圆与圆的位置关系", 37),
        OutlineEntry(0, "第二章 圆锥曲线", 47),
        OutlineEntry(1, "1.1 椭圆及其标准方程", 48),
        OutlineEntry(1, "1.2 椭圆的简单几何性质", 53),
        OutlineEntry(1, "2.1 双曲线及其标准方程", 61),
        OutlineEntry(1, "2.2 双曲线的简单几何性质", 63),
        OutlineEntry(1, "3.1 抛物线及其标准方程", 69),
        OutlineEntry(1, "3.2 抛物线的简单几何性质", 72),
        OutlineEntry(1, "4.1 直线与圆锥曲线的交点", 78),
        OutlineEntry(1, "4.2 直线与圆锥曲线的综合问题", 81),
        OutlineEntry(0, "第三章 空间向量与立体几何", 91),
        OutlineEntry(1, "1.1 点在空间直角坐标系中的坐标", 92),
        OutlineEntry(1, "1.2 空间两点间的距离公式", 94),
        OutlineEntry(1, "2.1 从平面向量到空间向量", 98),
        OutlineEntry(1, "2.2 空间向量的运算", 99),
        OutlineEntry(1, "3.1 空间向量基本定理", 110),
        OutlineEntry(1, "3.2 空间向量运算的坐标表示及应用", 112),
        OutlineEntry(1, "4.1 直线的方向向量与平面的法向量", 120),
        OutlineEntry(1, "4.2 用向量方法研究立体几何中的位置关系", 124),
        OutlineEntry(1, "4.3 用向量方法研究立体几何中的度量关系", 129),
        OutlineEntry(1, "5 数学探究活动（一）：正方体截面探究", 144),
        OutlineEntry(0, "第四章 数学建模活动（三）", 151),
        OutlineEntry(1, "1 自主数学建模的结题报告", 152),
        OutlineEntry(1, "2 自主数学建模的结题交流", 153),
        OutlineEntry(0, "第五章 计数原理", 157),
        OutlineEntry(1, "1.1 分类加法计数原理", 158),
        OutlineEntry(1, "1.2 分步乘法计数原理", 158),
        OutlineEntry(1, "1.3 基本计数原理的简单应用", 160),
        OutlineEntry(1, "2.1 排列与排列数", 163),
        OutlineEntry(1, "2.2 排列数公式", 166),
        OutlineEntry(1, "3.1 组合", 170),
        OutlineEntry(1, "3.2 组合数及其性质", 171),
        OutlineEntry(1, "4.1 二项式定理的推导", 175),
        OutlineEntry(1, "4.2 二项式系数的性质", 176),
        OutlineEntry(0, "第六章 概率", 183),
        OutlineEntry(1, "1.1 条件概率的概念", 184),
        OutlineEntry(1, "1.2 乘法公式与事件的独立性", 187),
        OutlineEntry(1, "1.3 全概率公式", 190),
        OutlineEntry(1, "2.1 随机变量", 196),
        OutlineEntry(1, "2.2 离散型随机变量的分布列", 197),
        OutlineEntry(1, "3.1 离散型随机变量的均值", 203),
        OutlineEntry(1, "3.2 离散型随机变量的方差", 206),
        OutlineEntry(1, "4.1 二项分布", 211),
        OutlineEntry(1, "4.2 超几何分布", 216),
        OutlineEntry(1, "5 正态分布", 221),
        OutlineEntry(0, "第七章 统计案例", 233),
        OutlineEntry(1, "1.1 直线拟合", 234),
        OutlineEntry(1, "1.2 一元线性回归方程", 235),
        OutlineEntry(1, "2.1 相关系数", 242),
        OutlineEntry(1, "2.2 成对数据的线性相关性分析", 246),
        OutlineEntry(1, "3.1 独立性检验", 251),
        OutlineEntry(1, "3.2 独立性检验的基本思想", 254),
        OutlineEntry(1, "3.3 独立性检验的应用", 255),
    ],
    "北师大-选择性必修2.pdf": [
        OutlineEntry(0, "第一章 数列", 1),
        OutlineEntry(1, "1.1 数列的概念", 2),
        OutlineEntry(1, "1.2 数列的函数特性", 5),
        OutlineEntry(1, "2.1 等差数列的概念及其通项公式", 11),
        OutlineEntry(1, "2.2 等差数列的前 n 项和", 15),
        OutlineEntry(1, "3.1 等比数列的概念及其通项公式", 22),
        OutlineEntry(1, "3.2 等比数列的前 n 项和", 27),
        OutlineEntry(1, "4 数列在日常经济生活中的应用", 34),
        OutlineEntry(1, "5 数学归纳法", 39),
        OutlineEntry(0, "第二章 导数及其应用", 49),
        OutlineEntry(1, "1.1 平均变化率", 50),
        OutlineEntry(1, "1.2 瞬时变化率", 52),
        OutlineEntry(1, "2.1 导数的概念", 57),
        OutlineEntry(1, "2.2 导数的几何意义", 58),
        OutlineEntry(1, "3 导数的计算", 63),
        OutlineEntry(1, "4.1 导数的加法与减法法则", 67),
        OutlineEntry(1, "4.2 导数的乘法与除法法则", 69),
        OutlineEntry(1, "5 简单复合函数的求导法则", 74),
        OutlineEntry(1, "6.1 函数的单调性", 77),
        OutlineEntry(1, "6.2 函数的极值", 79),
        OutlineEntry(1, "6.3 函数的最值", 82),
        OutlineEntry(1, "7.1 实际问题中导数的意义", 85),
        OutlineEntry(1, "7.2 实际问题中的最值问题", 88),
        OutlineEntry(1, "8 数学探究活动（二）：探究函数性质", 92),
    ],
}


def sectionize(entries: list[OutlineEntry], section_names: dict[str, dict[int, str]]) -> list[OutlineEntry]:
    """Turn a chapter's flat 1.1-style leaves into chapter → § → leaf.

    The section titles are copied from the printed contents pages.  Each
    generated § bookmark uses the same printed page as its first child (or the
    standalone § row), so no page positions are guessed here.
    """
    result: list[OutlineEntry] = []
    chapter = ""
    seen: set[int] = set()
    for entry in entries:
        if entry.level == 0:
            chapter = entry.title
            seen = set()
            result.append(entry)
            continue
        match = re.match(r"^(\d+)(?:\.(\d+))?\s+", entry.title)
        sections = section_names.get(chapter, {})
        if not match or int(match.group(1)) not in sections:
            result.append(entry)
            continue
        number = int(match.group(1))
        if number not in seen:
            seen.add(number)
            result.append(OutlineEntry(1, f"§ {number} {sections[number]}", entry.printed_page))
        # A title such as "1 周期变化" is the § row itself; it must not become
        # another child.  A title such as "1.1 …" is an actual lowest level.
        if match.group(2) is not None:
            result.append(OutlineEntry(2, entry.title, entry.printed_page))
    return result


SECTION_NAMES: dict[str, dict[str, dict[int, str]]] = {
    "北师大-必修2.pdf": {
        "第一章 三角函数": {1: "周期变化", 2: "任意角", 3: "弧度制", 4: "正弦函数和余弦函数的概念及其性质", 5: "正弦函数、余弦函数的图象与性质再认识", 6: "函数 y=A sin(ωx+φ) 的性质与图象", 7: "正切函数", 8: "三角函数的简单应用"},
        "第二章 平面向量及其应用": {1: "从位移、速度、力到向量", 2: "从位移的合成到向量的加减法", 3: "从速度的倍数到向量的数乘", 4: "平面向量基本定理及坐标表示", 5: "从力的做功到向量的数量积", 6: "平面向量的应用"},
        "第三章 数学建模活动（二）": {1: "数学建模活动的准备", 2: "自主数学建模的开题交流"},
        "第四章 三角恒等变换": {1: "同角三角函数的基本关系", 2: "两角和与差的三角函数公式", 3: "二倍角的三角函数公式"},
        "第五章 复数": {1: "复数的概念及其几何意义", 2: "复数的四则运算", 3: "复数的三角表示"},
        "第六章 立体几何初步": {1: "基本立体图形", 2: "直观图", 3: "空间点、直线、平面之间的位置关系", 4: "平行关系", 5: "垂直关系", 6: "简单几何体的再认识"},
    },
    "北师大-选择性必修1.pdf": {
        "第一章 直线与圆": {1: "直线与直线的方程", 2: "圆与圆的方程"},
        "第二章 圆锥曲线": {1: "椭圆", 2: "双曲线", 3: "抛物线", 4: "直线与圆锥曲线的位置关系"},
        "第三章 空间向量与立体几何": {1: "空间直角坐标系", 2: "空间向量与向量运算", 3: "空间向量基本定理及空间向量运算的坐标表示", 4: "向量在立体几何中的应用", 5: "数学探究活动（一）：正方体截面探究"},
        "第四章 数学建模活动（三）": {1: "自主数学建模的结题报告", 2: "自主数学建模的结题交流"},
        "第五章 计数原理": {1: "基本计数原理", 2: "排列问题", 3: "组合问题", 4: "二项式定理"},
        "第六章 概率": {1: "随机事件的条件概率", 2: "离散型随机变量及其分布列", 3: "离散型随机变量的均值与方差", 4: "二项分布与超几何分布", 5: "正态分布"},
        "第七章 统计案例": {1: "一元线性回归", 2: "成对数据的线性相关性", 3: "独立性检验问题"},
    },
    "北师大-选择性必修2.pdf": {
        "第一章 数列": {1: "数列的概念及其函数特性", 2: "等差数列", 3: "等比数列", 4: "数列在日常经济生活中的应用", 5: "数学归纳法"},
        "第二章 导数及其应用": {1: "平均变化率与瞬时变化率", 2: "导数的概念及其几何意义", 3: "导数的计算", 4: "导数的四则运算法则", 5: "简单复合函数的求导法则", 6: "用导数研究函数的性质", 7: "导数的应用", 8: "数学探究活动（二）：探究函数性质"},
    },
}

for _book, _sections in SECTION_NAMES.items():
    BDS_OUTLINES[_book] = sectionize(BDS_OUTLINES[_book], _sections)


def outline(rows: list[tuple[int, str, int]]) -> list[OutlineEntry]:
    """Keep the manually verified contents transcription compact and legible."""
    # Xiangjiao and People’s Education B both have seven unnumbered pages
    # before book page 1.  This was checked against their first body section.
    return [OutlineEntry(*row, page_offset=7) for row in rows]


# Transcribed directly from the two printed contents pages in each Xiangjiao
# volume.  Its printed contents has two levels only: chapter → section.
XJ_OUTLINES: dict[str, list[OutlineEntry]] = {
    "湘教-必修1.pdf": outline([
        (0, "第1章 集合与逻辑", 1),
        (1, "1.1 集合", 2), (1, "1.2 常用逻辑用语", 14),
        (0, "第2章 一元二次函数、方程和不等式", 31),
        (1, "2.1 相等关系与不等关系", 32), (1, "2.2 从函数观点看一元二次方程", 45), (1, "2.3 一元二次不等式", 50),
        (0, "第3章 函数的概念与性质", 64),
        (1, "3.1 函数", 65), (1, "3.2 函数的基本性质", 79),
        (0, "第4章 幂函数、指数函数和对数函数", 93),
        (1, "4.1 实数指数幂和幂函数", 94), (1, "4.2 指数函数", 106), (1, "4.3 对数函数", 115), (1, "4.4 函数与方程", 130), (1, "4.5 函数模型及其应用", 139),
        (0, "第5章 三角函数", 155),
        (1, "5.1 任意角与弧度制", 156), (1, "5.2 任意角的三角函数", 163), (1, "5.3 三角函数的图像与性质", 177), (1, "5.4 函数 y=A sin(ωx+φ) 的图像与性质", 188), (1, "5.5 三角函数模型的简单应用", 199),
        (0, "第6章 统计学初步", 210),
        (1, "6.1 获取数据的途径及统计概念", 211), (1, "6.2 抽样", 215), (1, "6.3 统计图表", 224), (1, "6.4 用样本估计总体", 235),
    ]),
    "湘教-必修2.pdf": outline([
        (0, "第1章 平面向量及其应用", 1),
        (1, "1.1 向量", 2), (1, "1.2 向量的加法", 6), (1, "1.3 向量的数乘", 14), (1, "1.4 向量的分解与坐标表示", 22), (1, "1.5 向量的数量积", 31), (1, "1.6 解三角形", 41), (1, "1.7 平面向量的应用举例", 54),
        (0, "第2章 三角恒等变换", 66),
        (1, "2.1 两角和与差的三角函数", 67), (1, "2.2 二倍角的三角函数", 78), (1, "2.3 简单的三角恒等变换", 83),
        (0, "第3章 复数", 100),
        (1, "3.1 复数的概念", 101), (1, "3.2 复数的四则运算", 105), (1, "3.3 复数的几何表示", 110), (1, "3.4 复数的三角表示", 116),
        (0, "第4章 立体几何初步", 131),
        (1, "4.1 空间的几何体", 132), (1, "4.2 平面", 146), (1, "4.3 直线与直线、直线与平面的位置关系", 151), (1, "4.4 平面与平面的位置关系", 172), (1, "4.5 几种简单几何体的表面积和体积", 186),
        (0, "第5章 概率", 209),
        (1, "5.1 随机事件与样本空间", 210), (1, "5.2 概率及运算", 217), (1, "5.3 用频率估计概率", 229), (1, "5.4 随机事件的独立性", 235),
        (0, "第6章 数学建模", 247),
        (1, "6.1 走进异彩纷呈的数学建模世界", 248), (1, "6.2 数学建模——从自然走向理性之路", 254), (1, "6.3 数学建模案例（一）：最佳视角", 258), (1, "6.4 数学建模案例（二）：曼哈顿距离", 261), (1, "6.5 数学建模案例（三）：人数估计", 266),
    ]),
    "湘教-选择性必修1.pdf": outline([
        (0, "第1章 数列", 1),
        (1, "1.1 数列的概念", 2), (1, "1.2 等差数列", 12), (1, "1.3 等比数列", 24), (1, "1.4 数学归纳法", 39),
        (0, "第2章 平面解析几何初步", 59),
        (1, "2.1 直线的斜率", 60), (1, "2.2 直线的方程", 65), (1, "2.3 两条直线的位置关系", 76), (1, "2.4 点到直线的距离", 83), (1, "2.5 圆的方程", 89), (1, "2.6 直线与圆、圆与圆的位置关系", 95), (1, "2.7 用坐标方法解决几何问题", 103),
        (0, "第3章 圆锥曲线与方程", 115),
        (1, "3.1 椭圆", 119), (1, "3.2 双曲线", 129), (1, "3.3 抛物线", 140), (1, "3.4 曲线与方程", 150), (1, "3.5 圆锥曲线的应用", 157),
        (0, "第4章 计数原理", 177),
        (1, "4.1 两个计数原理", 178), (1, "4.2 排列", 184), (1, "4.3 组合", 190), (1, "4.4 二项式定理", 196),
    ]),
    "湘教-选择性必修2.pdf": outline([
        (0, "第1章 导数及其应用", 1),
        (1, "1.1 导数概念及其意义", 2), (1, "1.2 导数的运算", 16), (1, "1.3 导数在研究函数中的应用", 29),
        (0, "第2章 空间向量与立体几何", 56),
        (1, "2.1 空间直角坐标系", 57), (1, "2.2 空间向量及其运算", 64), (1, "2.3 空间向量基本定理及坐标表示", 72), (1, "2.4 空间向量在立体几何中的应用", 85),
        (0, "第3章 概率", 114),
        (1, "3.1 条件概率与事件的独立性", 115), (1, "3.2 离散型随机变量及其分布列", 131), (1, "3.3 正态分布", 151),
        (0, "第4章 统计", 168),
        (1, "4.1 成对数据的统计相关性", 169), (1, "4.2 一元线性回归模型", 180), (1, "4.3 独立性检验", 191),
    ]),
}


# People’s Education B uses the full three-level printed hierarchy:
# chapter → blue major heading → numbered lowest-level item.  Do not flatten it.
PEPB_OUTLINES: dict[str, list[OutlineEntry]] = {
    "人教B2019-必修1.pdf": outline([
        (0, "第一章 集合与常用逻辑用语", 1), (1, "1.1 集合", 3),
        (2, "1.1.1 集合及其表示方法", 3), (2, "1.1.2 集合的基本关系", 10), (2, "1.1.3 集合的基本运算", 15),
        (1, "1.2 常用逻辑用语", 23), (2, "1.2.1 命题与量词", 23), (2, "1.2.2 全称量词命题与存在量词命题的否定", 28), (2, "1.2.3 充分条件、必要条件", 31),
        (0, "第二章 等式与不等式", 43), (1, "2.1 等式", 45),
        (2, "2.1.1 等式的性质与方程的解集", 45), (2, "2.1.2 一元二次方程的解集及其根与系数的关系", 49), (2, "2.1.3 方程组的解集", 54),
        (1, "2.2 不等式", 61), (2, "2.2.1 不等式及其性质", 61), (2, "2.2.2 不等式的解集", 67), (2, "2.2.3 一元二次不等式的解法", 71), (2, "2.2.4 均值不等式及其应用", 76),
        (0, "第三章 函数", 87), (1, "3.1 函数的概念与性质", 89),
        (2, "3.1.1 函数及其表示方法", 89), (2, "3.1.2 函数的单调性", 99), (2, "3.1.3 函数的奇偶性", 109),
        (1, "3.2 函数与方程、不等式之间的关系", 118), (1, "3.3 函数的应用（一）", 128), (1, "3.4 数学建模活动：决定苹果的最佳出售时间点", 132),
    ]),
    "人教B2019-必修2.pdf": outline([
        (0, "第四章 指数函数、对数函数与幂函数", 1), (1, "4.1 指数与指数函数", 3),
        (2, "4.1.1 实数指数幂及其运算", 3), (2, "4.1.2 指数函数的性质与图象", 9),
        (1, "4.2 对数与对数函数", 15), (2, "4.2.1 对数运算", 15), (2, "4.2.2 对数运算法则", 20), (2, "4.2.3 对数函数的性质与图象", 24),
        (1, "4.3 指数函数与对数函数的关系", 31), (1, "4.4 幂函数", 34), (1, "4.5 增长速度的比较", 39), (1, "4.6 函数的应用（二）", 43), (1, "4.7 数学建模活动：生长规律的描述", 47),
        (0, "第五章 统计与概率", 55), (1, "5.1 统计", 57),
        (2, "5.1.1 数据的收集", 57), (2, "5.1.2 数据的数字特征", 63), (2, "5.1.3 数据的直观表示", 71), (2, "5.1.4 用样本估计总体", 80),
        (1, "5.2 数学探究活动：由编号样本估计总数及其模拟", 93), (1, "5.3 概率", 96),
        (2, "5.3.1 样本空间与事件", 96), (2, "5.3.2 事件之间的关系与运算", 101), (2, "5.3.3 古典概型", 106), (2, "5.3.4 频率与概率", 112), (2, "5.3.5 随机事件的独立性", 118),
        (1, "5.4 统计与概率的应用", 123),
        (0, "第六章 平面向量初步", 135), (1, "6.1 平面向量及其线性运算", 137),
        (2, "6.1.1 向量的概念", 137), (2, "6.1.2 向量的加法", 141), (2, "6.1.3 向量的减法", 146), (2, "6.1.4 数乘向量", 149), (2, "6.1.5 向量的线性运算", 152),
        (1, "6.2 向量基本定理与向量的坐标", 157), (2, "6.2.1 向量基本定理", 157), (2, "6.2.2 直线上向量的坐标及其运算", 162), (2, "6.2.3 平面向量的坐标及其运算", 166),
        (1, "6.3 平面向量线性运算的应用", 174),
    ]),
    "人教B2019-必修3.pdf": outline([
        (0, "第七章 三角函数", 1), (1, "7.1 任意角的概念与弧度制", 3), (2, "7.1.1 角的推广", 3), (2, "7.1.2 弧度制及其与角度制的换算", 8),
        (1, "7.2 任意角的三角函数", 14), (2, "7.2.1 三角函数的定义", 14), (2, "7.2.2 单位圆与三角函数线", 18), (2, "7.2.3 同角三角函数的基本关系式", 22), (2, "7.2.4 诱导公式", 27),
        (1, "7.3 三角函数的性质与图象", 37), (2, "7.3.1 正弦函数的性质与图象", 37), (2, "7.3.2 正弦型函数的性质与图象", 44), (2, "7.3.3 余弦函数的性质与图象", 52), (2, "7.3.4 正切函数的性质与图象", 56), (2, "7.3.5 已知三角函数值求角", 60),
        (1, "7.4 数学建模活动：周期现象的描述", 67),
        (0, "第八章 向量的数量积与三角恒等变换", 73), (1, "8.1 向量的数量积", 75),
        (2, "8.1.1 向量数量积的概念", 75), (2, "8.1.2 向量数量积的运算律", 80), (2, "8.1.3 向量数量积的坐标运算", 85),
        (1, "8.2 三角恒等变换", 91), (2, "8.2.1 两角和与差的余弦", 91), (2, "8.2.2 两角和与差的正弦、正切", 94), (2, "8.2.3 倍角公式", 100), (2, "8.2.4 三角恒等变换的应用", 103),
    ]),
    "人教B2019-必修4.pdf": outline([
        (0, "第九章 解三角形", 1), (1, "9.1 正弦定理与余弦定理", 3), (2, "9.1.1 正弦定理", 3), (2, "9.1.2 余弦定理", 8), (1, "9.2 正弦定理与余弦定理的应用", 13), (1, "9.3 数学探究活动：得到不可达两点之间的距离", 17),
        (0, "第十章 复数", 23), (1, "10.1 复数及其几何意义", 25), (2, "10.1.1 复数的概念", 25), (2, "10.1.2 复数的几何意义", 29), (1, "10.2 复数的运算", 33), (2, "10.2.1 复数的加法与减法", 33), (2, "10.2.2 复数的乘法与除法", 36), (1, "10.3 复数的三角形式及其运算", 43),
        (0, "第十一章 立体几何初步", 53), (1, "11.1 空间几何体", 55),
        (2, "11.1.1 空间几何体与斜二测画法", 55), (2, "11.1.2 构成空间几何体的基本元素", 60), (2, "11.1.3 多面体与棱柱", 66), (2, "11.1.4 棱锥与棱台", 72), (2, "11.1.5 旋转体", 77), (2, "11.1.6 祖暅原理与几何体的体积", 83),
        (1, "11.2 平面的基本事实与推论", 92), (1, "11.3 空间中的平行关系", 97), (2, "11.3.1 平行直线与异面直线", 97), (2, "11.3.2 直线与平面平行", 101), (2, "11.3.3 平面与平面平行", 105),
        (1, "11.4 空间中的垂直关系", 112), (2, "11.4.1 直线与平面垂直", 112), (2, "11.4.2 平面与平面垂直", 118),
    ]),
    "人教B2019-选择性必修1.pdf": outline([
        (0, "第一章 空间向量与立体几何", 1), (1, "1.1 空间向量及其运算", 3),
        (2, "1.1.1 空间向量及其运算", 3), (2, "1.1.2 空间向量基本定理", 13), (2, "1.1.3 空间向量的坐标与空间直角坐标系", 18),
        (1, "1.2 空间向量在立体几何中的应用", 30), (2, "1.2.1 空间中的点、直线与空间向量", 30), (2, "1.2.2 空间中的平面与空间向量", 38), (2, "1.2.3 直线与平面的夹角", 44), (2, "1.2.4 二面角", 49), (2, "1.2.5 空间中的距离", 54),
        (0, "第二章 平面解析几何", 69), (1, "2.1 坐标法", 71), (1, "2.2 直线及其方程", 75),
        (2, "2.2.1 直线的倾斜角与斜率", 75), (2, "2.2.2 直线的方程", 83), (2, "2.2.3 两条直线的位置关系", 91), (2, "2.2.4 点到直线的距离", 97),
        (1, "2.3 圆及其方程", 103), (2, "2.3.1 圆的标准方程", 103), (2, "2.3.2 圆的一般方程", 107), (2, "2.3.3 直线与圆的位置关系", 110), (2, "2.3.4 圆与圆的位置关系", 116),
        (1, "2.4 曲线与方程", 123), (1, "2.5 椭圆及其方程", 129), (2, "2.5.1 椭圆的标准方程", 129), (2, "2.5.2 椭圆的几何性质", 135),
        (1, "2.6 双曲线及其方程", 144), (2, "2.6.1 双曲线的标准方程", 144), (2, "2.6.2 双曲线的几何性质", 149),
        (1, "2.7 抛物线及其方程", 158), (2, "2.7.1 抛物线的标准方程", 158), (2, "2.7.2 抛物线的几何性质", 162), (1, "2.8 直线与圆锥曲线的位置关系", 168),
    ]),
    "人教B2019-选择性必修2.pdf": outline([
        (0, "第三章 排列、组合与二项式定理", 1), (1, "3.1 排列与组合", 3), (2, "3.1.1 基本计数原理", 3), (2, "3.1.2 排列与排列数", 9), (2, "3.1.3 组合与组合数", 16), (1, "3.2 数学探究活动：生日悖论的解释与模拟", 26), (1, "3.3 二项式定理与杨辉三角", 30),
        (0, "第四章 概率与统计", 41), (1, "4.1 条件概率与事件的独立性", 43), (2, "4.1.1 条件概率", 43), (2, "4.1.2 乘法公式与全概率公式", 48), (2, "4.1.3 独立性与条件概率的关系", 58),
        (1, "4.2 随机变量", 64), (2, "4.2.1 随机变量及其与事件的联系", 64), (2, "4.2.2 离散型随机变量的分布列", 69), (2, "4.2.3 二项分布与超几何分布", 74), (2, "4.2.4 随机变量的数字特征", 83), (2, "4.2.5 正态分布", 90),
        (1, "4.3 统计模型", 100), (2, "4.3.1 一元线性回归模型", 100), (2, "4.3.2 独立性检验", 116), (1, "4.4 数学探究活动：了解高考选考科目的确定是否与性别有关", 123),
    ]),
    "人教B2019-选择性必修3.pdf": outline([
        (0, "第五章 数列", 1), (1, "5.1 数列基础", 3), (2, "5.1.1 数列的概念", 3), (2, "5.1.2 数列中的递推", 9),
        (1, "5.2 等差数列", 16), (2, "5.2.1 等差数列", 16), (2, "5.2.2 等差数列的前 n 项和", 23),
        (1, "5.3 等比数列", 29), (2, "5.3.1 等比数列", 29), (2, "5.3.2 等比数列的前 n 项和", 37), (1, "5.4 数列的应用", 45), (1, "5.5 数学归纳法", 52),
        (0, "第六章 导数及其应用", 61), (1, "6.1 导数", 63), (2, "6.1.1 函数的平均变化率", 63), (2, "6.1.2 导数及其几何意义", 68), (2, "6.1.3 基本初等函数的导数", 75), (2, "6.1.4 求导法则及其应用", 81),
        (1, "6.2 利用导数研究函数的性质", 92), (2, "6.2.1 导数与函数的单调性", 92), (2, "6.2.2 导数与函数的极值、最值", 96), (1, "6.3 利用导数解决实际问题", 103), (1, "6.4 数学建模活动：描述体重与脉搏率的关系", 109),
    ]),
}


def sh_outline(rows: list[tuple[int, str, int]]) -> list[OutlineEntry]:
    """Shanghai textbooks: printed book page 1 is PDF page 8."""
    return [OutlineEntry(*row, page_offset=7) for row in rows]


def e_outline(rows: list[tuple[int, str, int]]) -> list[OutlineEntry]:
    """E-Jiao textbooks: printed book page 4 is PDF page 8."""
    return [OutlineEntry(*row, page_offset=4) for row in rows]


# The following two sets are transcribed from the printed contents pages.  The
# page offset is deliberately kept per edition, rather than inferred from an
# unreliable legacy outline.  Only the contents hierarchy is written back.
SH_OUTLINES: dict[str, list[OutlineEntry]] = {
    "沪教-必修1.pdf": sh_outline([
        (0, "第1章 集合与逻辑", 1), (1, "1.1 集合初步", 2), (1, "1.2 常用逻辑用语", 14),
        (0, "第2章 等式与不等式", 25), (1, "2.1 等式与不等式的性质", 26), (1, "2.2 不等式的求解", 37), (1, "2.3 基本不等式及其应用", 50),
        (0, "第3章 幂、指数与对数", 63), (1, "3.1 幂与指数", 64), (1, "3.2 对数", 70),
        (0, "第4章 幂函数、指数函数与对数函数", 83), (1, "4.1 幂函数", 84), (1, "4.2 指数函数", 91), (1, "4.3 对数函数", 99),
        (0, "第5章 函数的概念、性质及应用", 113), (1, "5.1 函数", 114), (1, "5.2 函数的基本性质", 124), (1, "5.3 函数的应用", 137), (1, "5.4 反函数", 146),
    ]),
    "沪教-必修2.pdf": sh_outline([
        (0, "第6章 三角", 1), (1, "6.1 正弦、余弦、正切、余切", 2), (1, "6.2 常用三角公式", 27), (1, "6.3 解三角形", 43),
        (0, "第7章 三角函数", 61), (1, "7.1 正弦函数的图像与性质", 62), (1, "7.2 余弦函数的图像与性质", 78), (1, "7.3 函数 y=A sin(ωx+φ) 的图像", 82), (1, "7.4 正切函数的图像与性质", 89),
        (0, "第8章 平面向量", 97), (1, "8.1 向量的概念和线性运算", 98), (1, "8.2 向量的数量积", 110), (1, "8.3 向量的坐标表示", 117), (1, "8.4 向量的应用", 127),
        (0, "第9章 复数", 139), (1, "9.1 复数及其四则运算", 140), (1, "9.2 复数的几何意义", 150), (1, "9.3 实系数一元二次方程", 158), (1, "9.4 复数的三角形式", 162),
    ]),
    "沪教-必修3.pdf": sh_outline([
        (0, "第10章 空间直线与平面", 1), (1, "10.1 平面及其基本性质", 2), (1, "10.2 直线与直线的位置关系", 13), (1, "10.3 直线与平面的位置关系", 25), (1, "10.4 平面与平面的位置关系", 38), (1, "10.5 异面直线间的距离", 45),
        (0, "第11章 简单几何体", 57), (1, "11.1 柱体", 58), (1, "11.2 锥体", 67), (1, "11.3 多面体与旋转体", 77), (1, "11.4 球", 83),
        (0, "第12章 概率初步", 95), (1, "12.1 随机现象与样本空间", 96), (1, "12.2 古典概率", 103), (1, "12.3 频率与概率", 115), (1, "12.4 随机事件的独立性", 120),
        (0, "第13章 统计", 131), (1, "13.1 总体与样本", 132), (1, "13.2 数据的获取", 135), (1, "13.3 抽样方法", 139), (1, "13.4 统计图表", 147), (1, "13.5 统计估计", 159), (1, "13.6 统计活动", 177),
    ]),
    "沪教-必修4.pdf": sh_outline([
        (0, "引论", 1), (0, "第1部分 数学建模活动案例", 5), (1, "1 红绿灯管理", 6), (1, "2 “诱人”的优惠券", 10), (1, "3 车辆转弯时的安全隐患", 15), (1, "4 雨中行", 22),
        (0, "第2部分 数学建模活动A", 29), (1, "5 出租车运价", 30), (1, "6 家具搬运", 32), (1, "7 登山行程设计", 34),
        (0, "第3部分 数学建模活动B", 37), (1, "8 包装彩带", 38), (1, "9 削菠萝", 39), (1, "10 高度测量", 40), (1, "11 外卖与环保", 42),
        (0, "附录", 43),
    ]),
    "沪教-选择性必修1.pdf": sh_outline([
        (0, "第1章 平面直角坐标系中的直线", 1), (1, "1.1 直线的倾斜角与斜率", 2), (1, "1.2 直线的方程", 6), (1, "1.3 两条直线的位置关系", 16), (1, "1.4 点到直线的距离", 25),
        (0, "第2章 圆锥曲线", 33), (1, "2.1 圆", 34), (1, "2.2 椭圆", 48), (1, "2.3 双曲线", 56), (1, "2.4 抛物线", 66), (1, "2.5 曲线与方程", 74),
        (0, "第3章 空间向量及其应用", 95), (1, "3.1 空间向量及其运算", 96), (1, "3.2 空间向量基本定理", 103), (1, "3.3 空间向量的坐标表示", 108), (1, "3.4 空间向量在立体几何中的应用", 114),
        (0, "第4章 数列", 131), (1, "4.1 等差数列", 132), (1, "4.2 等比数列", 140), (1, "4.3 数列", 151), (1, "4.4 数学归纳法", 161), (1, "4.5 用迭代序列求根号2的近似值", 169),
    ]),
    "沪教-选择性必修2.pdf": sh_outline([
        (0, "第5章 导数及其运用", 1), (1, "5.1 导数的概念及意义", 2), (1, "5.2 导数的运算", 12), (1, "5.3 导数的应用", 21),
        (0, "第6章 计数原理", 39), (1, "6.1 乘法原理与加法原理", 40), (1, "6.2 排列", 46), (1, "6.3 组合", 57), (1, "6.4 计数原理在古典概率中的应用", 66), (1, "6.5 二项式定理", 69),
        (0, "第7章 概率初步（续）", 79), (1, "7.1 条件概率与相关公式", 80), (1, "7.2 随机变量的分布与特征", 89), (1, "7.3 常用分布", 101),
        (0, "第8章 成对数据的统计分析", 115), (1, "8.1 成对数据的相关分析", 116), (1, "8.2 一元线性回归分析", 125), (1, "8.3 2×2列联表", 138),
    ]),
    "沪教-选择性必修3.pdf": sh_outline([
        (0, "引论", 1), (0, "第1部分 数学建模活动案例", 3), (1, "1 刹车距离", 4), (1, "2 易拉罐的设计", 8), (1, "3 珠穆朗玛峰顶上有多少氧气", 12), (1, "4 水葫芦的生长", 20),
        (0, "第2部分 数学建模活动A", 27), (1, "5 铅球投掷", 28), (1, "6 电梯调度", 31),
        (0, "第3部分 数学建模活动B", 33), (1, "7 存款计划", 34), (1, "8 民生巨变40年", 35), (1, "9 教室里的照明", 37),
        (0, "附录", 38),
    ]),
}


E_OUTLINES: dict[str, list[OutlineEntry]] = {
    "鄂教-必修1.pdf": e_outline([
        (0, "第1章 集合", 3), (1, "1.1 集合的概念与表示", 4), (1, "1.2 集合的基本关系", 8), (1, "1.3 集合的基本运算", 12),
        (0, "第2章 常用逻辑用语", 19), (1, "2.1 充分条件与必要条件", 20), (1, "2.2 全称量词与存在量词", 23),
        (0, "第3章 不等式初步", 29), (1, "3.1 相等关系与不等关系", 30), (1, "3.2 等式与不等式的性质", 32), (1, "3.3 从函数观点看一元二次方程和一元二次不等式", 34), (1, "3.4 基本不等式", 40),
    ]),
    "鄂教-必修2.pdf": e_outline([
        (0, "第1章 函数的概念与性质", 3), (1, "1.1 函数", 4), (1, "1.2 函数的基本性质", 14),
        (0, "第2章 幂函数、指数函数、对数函数", 27), (1, "2.1 幂函数", 28), (1, "2.2 指数函数", 34), (1, "2.3 对数函数", 42), (1, "2.4 几类函数的增长差异", 51),
        (0, "第3章 三角函数", 59), (1, "3.1 任意角与弧度制", 60), (1, "3.2 任意角的三角函数", 66), (1, "3.3 三角函数的图象与性质", 79), (1, "3.4 函数 y=Asin(ωx+φ) 的图象", 93), (1, "3.5 三角函数模型的简单应用", 99), (1, "3.6 三角恒等变换", 102),
        (0, "第4章 函数的应用", 123), (1, "4.1 二分法与求方程的近似解", 124), (1, "4.2 函数与数学模型", 130),
    ]),
    "鄂教-必修3.pdf": e_outline([
        (0, "第1章 平面向量及其应用", 3), (1, "1.1 向量的概念", 4), (1, "1.2 向量的运算", 7), (1, "1.3 向量基本定理及坐标表示", 18), (1, "1.4 向量的应用与解三角形", 28),
        (0, "第2章 复数", 43), (1, "2.1 复数的概念", 44), (1, "2.2 复数的运算", 49), (1, "2.3 复数的三角表示", 55),
        (0, "第3章 立体几何初步", 63), (1, "3.1 空间几何体", 64), (1, "3.2 平面的基本性质", 72), (1, "3.3 空间两条直线的位置关系", 77), (1, "3.4 直线与平面的位置关系", 81), (1, "3.5 平面与平面的位置关系", 88),
    ]),
    "鄂教-必修4.pdf": e_outline([
        (0, "第1章 概率", 3), (1, "1.1 随机事件及其概率", 4), (1, "1.2 古典概型", 15), (1, "1.3 概率的加法公式", 21), (1, "1.4 随机事件的独立性", 26),
        (0, "第2章 统计", 35), (1, "2.1 数据获取", 36), (1, "2.2 数据整理", 49), (1, "2.3 用样本估计总体", 56),
    ]),
    "鄂教-选择性必修1.pdf": e_outline([
        (0, "第1章 空间向量与立体几何", 3), (1, "1.1 空间直角坐标系", 4), (1, "1.2 空间向量及其运算", 7), (1, "1.3 空间向量基本定理及坐标表示", 12), (1, "1.4 空间向量的应用", 22),
        (0, "第2章 平面解析几何初步", 39), (1, "2.1 直线与直线的方程", 40), (1, "2.2 圆与圆的方程", 61),
        (0, "第3章 圆锥曲线的方程", 81), (1, "3.1 椭圆", 82), (1, "3.2 双曲线", 99), (1, "3.3 抛物线", 111), (1, "3.4 圆锥曲线的简单应用", 119),
    ]),
    "鄂教-选择性必修2.pdf": e_outline([
        (0, "第1章 数列", 3), (1, "1.1 数列的概念", 4), (1, "1.2 等差数列", 9), (1, "1.3 等差数列的前 n 项和", 12), (1, "1.4 等比数列", 19), (1, "1.5 等比数列的前 n 项和", 23), (1, "1.6 数学归纳法", 27),
        (0, "第2章 一元函数导数及其应用", 37), (1, "2.1 导数的概念及其意义", 38), (1, "2.2 导数的运算", 49), (1, "2.3 导数在研究函数中的应用", 60),
    ]),
    "鄂教-选择性必修3.pdf": e_outline([
        (0, "第1章 计数原理", 3), (1, "1.1 基本计数原理", 4), (1, "1.2 排列", 8), (1, "1.3 组合", 14), (1, "1.4 二项式定理", 18),
        (0, "第2章 概率", 29), (1, "2.1 随机事件的条件概率", 30), (1, "2.2 离散型随机变量及其分布列", 42), (1, "2.3 离散型随机变量的数字特征", 51), (1, "2.4 正态分布", 62),
        (0, "第3章 统计", 73), (1, "3.1 成对数据的统计相关性", 74), (1, "3.2 一元线性回归", 79), (1, "3.3 2×2列联表", 88),
    ]),
}


EDITION_OUTLINES = {
    "北师大版": BDS_OUTLINES,
    "湘教版": XJ_OUTLINES,
    "人教B版": PEPB_OUTLINES,
    "沪教版": SH_OUTLINES,
    "鄂教版": E_OUTLINES,
}


def metadata_for(reader: PdfReader) -> dict[str, str]:
    result: dict[str, str] = {}
    for key, value in (reader.metadata or {}).items():
        if isinstance(key, str) and isinstance(value, str):
            result[key] = value
    return result


def flatten_outline(items) -> list[str]:
    labels: list[str] = []
    for item in items:
        if isinstance(item, list):
            labels.extend(flatten_outline(item))
        elif hasattr(item, "title"):
            labels.append(item.title)
    return labels


def rewrite(source: Path, backup: Path, entries: list[OutlineEntry], dry_run: bool) -> None:
    reader = PdfReader(str(source))
    total = len(reader.pages)
    for entry in entries:
        if not 1 <= entry.pdf_page <= total:
            raise ValueError(f"{source.name}: {entry.title} points outside the document ({entry.pdf_page}/{total})")

    print(f"{source.name}: {total} pages -> {len(entries)} chapter bookmarks")
    if dry_run:
        return

    backup.parent.mkdir(parents=True, exist_ok=True)
    if backup.exists():
        raise FileExistsError(f"Backup already exists: {backup}")
    shutil.copy2(source, backup)

    writer = PdfWriter()
    # Do not import the original outline: its per-page entries are the defect
    # being repaired.  Page contents/links/annotations are copied as-is.
    writer.append(reader, import_outline=False)
    metadata = metadata_for(reader)
    if metadata:
        writer.add_metadata(metadata)
    parents: dict[int, object] = {}
    for entry in entries:
        parent = parents.get(entry.level - 1)
        parents[entry.level] = writer.add_outline_item(entry.title, entry.pdf_page - 1, parent=parent)
        for deeper in tuple(parents):
            if deeper > entry.level:
                del parents[deeper]

    descriptor, temporary_name = tempfile.mkstemp(
        prefix=f".{source.stem}.bookmarks-", suffix=".pdf", dir=source.parent
    )
    os.close(descriptor)
    temporary = Path(temporary_name)
    try:
        with temporary.open("wb") as stream:
            writer.write(stream)
        # Ensure the replacement is readable and has precisely the requested
        # semantic labels before it can replace the user's original file.
        check = PdfReader(str(temporary))
        labels = flatten_outline(check.outline)
        expected = [entry.title for entry in entries]
        if len(check.pages) != total or labels != expected:
            raise RuntimeError(f"Verification failed for {source.name}: {labels!r}")
        os.replace(temporary, source)
    except Exception:
        temporary.unlink(missing_ok=True)
        raise


def main() -> int:
    parser = argparse.ArgumentParser(description="Repair reference textbook PDF bookmarks")
    parser.add_argument("--edition", default="北师大版", choices=sorted(EDITION_OUTLINES))
    parser.add_argument("--backup-root", required=True, type=Path)
    parser.add_argument("--dry-run", action="store_true")
    parser.add_argument("--books", nargs="*", help="Only rewrite the named PDF files")
    args = parser.parse_args()

    outlines = EDITION_OUTLINES[args.edition]
    books = args.books or list(outlines)
    unknown = set(books) - set(outlines)
    if unknown:
        raise ValueError(f"Unknown book(s): {', '.join(sorted(unknown))}")
    for filename in books:
        entries = outlines[filename]
        source = MATH_ROOT / args.edition / filename
        if not source.is_file():
            raise FileNotFoundError(source)
        rewrite(source, args.backup_root / args.edition / filename, entries, args.dry_run)
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        raise SystemExit(1)
