"""高中数学教材笔记本：按教材小节沉淀备课与解题资料。"""
from __future__ import annotations

import base64
import hashlib
import html
import json
import re
import shutil
import sys
import uuid
from functools import lru_cache
from io import BytesIO
from collections import defaultdict
from datetime import datetime
from pathlib import Path

from PySide6.QtCore import QEvent, QFileSystemWatcher, QModelIndex, QIODevice, QRect, QSaveFile, QSettings, QSize, QTimer, Qt, QUrl, Signal
from PySide6.QtGui import QAction, QColor, QDesktopServices, QImage, QPainter, QPen, QPixmap, QTextCursor
from PySide6.QtPdf import QPdfBookmarkModel, QPdfDocument
from PySide6.QtWebEngineCore import QWebEnginePage, QWebEngineSettings
from PySide6.QtWebEngineWidgets import QWebEngineView
from PySide6.QtWidgets import (
    QApplication, QAbstractItemView, QComboBox, QDialog, QFileDialog, QFrame,
    QHBoxLayout, QLabel, QLineEdit, QListWidget, QListWidgetItem, QMainWindow,
    QMessageBox, QPushButton, QScrollArea, QSizePolicy, QSplitter, QStatusBar,
    QSpinBox, QStackedWidget, QTextEdit, QTreeWidget, QTreeWidgetItem, QVBoxLayout, QWidget,
)


APP_TITLE = "高中数学教材笔记本"
ROOT = Path(__file__).resolve().parent
# 依赖安装在工作区根目录，应用脚本位于“教学设计工作台”子目录。
KATEX_DIST = ROOT.parent / "node_modules" / "katex" / "dist"
LEGACY_DATA_PATH = ROOT / "我的教学卡数据.json"
SOURCE_ROOT_CANDIDATES = (
    ROOT.parent / "节引言资料包",
    ROOT.parent / "中学教材" / "高中" / "数学" / "论文" / "节引言资料包",
    Path("/Users/chuan/高中数学/中学教材/高中/数学/论文/节引言资料包"),
)
DATA_SOURCES = {"人教A版": "pep_sections_verified.json", "苏教版": "sj_sections_verified.json"}
PDF_ROOTS = {
    "人教A版": Path("/Users/chuan/高中数学/中学教材/高中/数学/人教A版"),
    "苏教版": Path("/Users/chuan/高中数学/中学教材/高中/数学/苏教版"),
}
LOCAL_SCREENSHOT_DIR = ROOT / "教材截图"
# 为兼容既有的截图调用保留这个名称；启用同步后会指向同步资料夹。
SCREENSHOT_DIR = LOCAL_SCREENSHOT_DIR
SCREENSHOT_TOKEN = re.compile(r"\[\[教材截图:([0-9a-f]{32})\]\]")

SECTION_META = {
    "knowledge": ("知识点列表", ""),
    "patterns": ("基本例习题类型", ""),
    "examples": ("有价值的例习题", ""),
    "questions": ("问题串设计", ""),
    "pitfalls": ("易错与辨析", ""),
}


def bookmark_key(text: str) -> str:
    return re.sub(r"[\s·．.、,，:：;；（）()【】\[\]－—-]", "", str(text)).lower()


_FULLWIDTH_DIGITS = str.maketrans("０１２３４５６７８９", "0123456789")


def catalog_chapter_titles(book: dict) -> dict[str, str]:
    """从资料包目录页补出“第 N 章 + 名称”。

    苏教版资料原先只给了小节，未写章名；目录页本身是教材核对过的
    原始资料，优先用它而不是依据小节名称猜测。
    """
    titles: dict[str, str] = {}
    for entry in book.get("entries", []):
        text = str(entry.get("page_text", "")).translate(_FULLWIDTH_DIGITS).replace("\n", "")
        for match in re.finditer(
            r"第\s*(\d+)\s*章\s*([^\d]{1,80}?)(?=\s*\d+\s*[．.]\s*\d+|第\s*\d+\s*章|$)",
            text,
        ):
            number = match.group(1)
            name = re.sub(r"\s+", "", match.group(2)).strip("·、，,：:－—- ")
            if name:
                titles[number] = f"第{number}章 {name}"
    return titles


class PdfReferenceIndex:
    """从 PDF 书签生成“小节 → 起止页”的可重复映射。页码对用户始终按 1 开始显示。"""
    def __init__(self):
        self._outlines: dict[Path, tuple[int, list[dict]]] = {}

    def pdf_path_for(self, lesson: dict) -> Path:
        return PDF_ROOTS.get(lesson.get("edition"), Path()) / lesson.get("file", "")

    def reference_for(self, lesson: dict) -> dict:
        pdf_path = self.pdf_path_for(lesson)
        page_count, outline = self._outline_for(pdf_path)
        fallback = max(1, int(lesson.get("corrected_pdf_page") or lesson.get("pdf_page") or 1))
        if not outline:
            return {"path": pdf_path, "start": fallback, "end": min(page_count or fallback, fallback + 3), "source": "catalog"}

        section_no = bookmark_key(lesson.get("section_no", ""))
        section_title = bookmark_key(lesson.get("section_title", ""))
        scored = []
        for index, item in enumerate(outline):
            title = bookmark_key(item["title"])
            score = 0
            if section_no and section_no in title:
                score += 80
            if section_title and section_title in title:
                score += 120
            score += min(20, len(set(section_title) & set(title)))
            if score:
                scored.append((score, -abs(item["page"] + 1 - fallback), index, item))
        if not scored:
            return {"path": pdf_path, "start": fallback, "end": min(page_count or fallback, fallback + 3), "source": "catalog"}

        _, _, index, match = max(scored)
        start = match["page"] + 1
        end = page_count or start
        for next_item in outline[index + 1:]:
            if next_item["level"] <= match["level"] and next_item["page"] >= match["page"]:
                end = max(start, next_item["page"])
                break
        return {"path": pdf_path, "start": start, "end": end, "source": "bookmark", "bookmark": match["title"]}

    def _outline_for(self, pdf_path: Path) -> tuple[int, list[dict]]:
        if pdf_path in self._outlines:
            return self._outlines[pdf_path]
        if not pdf_path.exists():
            result = (0, [])
            self._outlines[pdf_path] = result
            return result
        document = QPdfDocument()
        if document.load(str(pdf_path)) != QPdfDocument.Error.None_:
            result = (0, [])
            self._outlines[pdf_path] = result
            return result
        model = QPdfBookmarkModel()
        model.setDocument(document)
        outline: list[dict] = []

        def visit(parent: QModelIndex = QModelIndex()) -> None:
            for row in range(model.rowCount(parent)):
                index = model.index(row, 0, parent)
                outline.append({
                    "title": str(model.data(index, QPdfBookmarkModel.Role.Title) or ""),
                    "page": int(model.data(index, QPdfBookmarkModel.Role.Page) or 0),
                    "level": int(model.data(index, QPdfBookmarkModel.Role.Level) or 0),
                })
                visit(index)

        visit()
        result = (document.pageCount(), outline)
        self._outlines[pdf_path] = result
        return result

class PdfCropLabel(QLabel):
    """显示已渲染 PDF 页并让用户拖拽框选截图区域。"""
    def __init__(self, parent=None):
        super().__init__(parent)
        self._start = None
        self._selection = QRect()
        self._highlight = QRect()
        self._capture_enabled = False
        self._pixel_ratio = 1.0
        self.setAlignment(Qt.AlignmentFlag.AlignLeft | Qt.AlignmentFlag.AlignTop)
        self.setCursor(Qt.CursorShape.ArrowCursor)

    def set_page_image(self, image, pixel_ratio: float = 1.0) -> None:
        pixmap = QPixmap.fromImage(image)
        self._pixel_ratio = max(1.0, float(pixel_ratio))
        pixmap.setDevicePixelRatio(self._pixel_ratio)
        self.setPixmap(pixmap)
        self.setFixedSize(pixmap.deviceIndependentSize().toSize())
        self._start = None
        self._selection = QRect()
        self._highlight = QRect()
        self.update()

    def set_capture_enabled(self, enabled: bool) -> None:
        self._capture_enabled = enabled
        self._start = None
        self._selection = QRect()
        self.setCursor(Qt.CursorShape.CrossCursor if enabled else Qt.CursorShape.ArrowCursor)
        self.update()

    def set_highlight_normalized(self, rect: dict | None) -> None:
        if self.pixmap() is None or not rect:
            self._highlight = QRect()
        else:
            width, height = self.width(), self.height()
            self._highlight = QRect(
                round(float(rect.get("x", 0)) * width),
                round(float(rect.get("y", 0)) * height),
                round(float(rect.get("width", 0)) * width),
                round(float(rect.get("height", 0)) * height),
            ).intersected(self.rect())
        self.update()

    def selected_image(self):
        pixmap = self.pixmap()
        if pixmap is None or self._selection.width() < 8 or self._selection.height() < 8:
            return None
        rect = self._selection.intersected(self.rect())
        source_rect = QRect(
            round(rect.x() * self._pixel_ratio), round(rect.y() * self._pixel_ratio),
            round(rect.width() * self._pixel_ratio), round(rect.height() * self._pixel_ratio),
        )
        return pixmap.copy(source_rect.intersected(pixmap.rect())).toImage()

    def selected_rect_normalized(self) -> dict | None:
        if self.pixmap() is None or self._selection.width() < 8 or self._selection.height() < 8:
            return None
        rect = self._selection.intersected(self.rect())
        return {
            "x": round(rect.x() / self.width(), 6),
            "y": round(rect.y() / self.height(), 6),
            "width": round(rect.width() / self.width(), 6),
            "height": round(rect.height() / self.height(), 6),
        }

    def mousePressEvent(self, event) -> None:
        if self._capture_enabled and event.button() == Qt.MouseButton.LeftButton:
            self._start = event.position().toPoint()
            self._selection = QRect(self._start, self._start)
            self.update()

    def mouseMoveEvent(self, event) -> None:
        if self._capture_enabled and self._start is not None:
            self._selection = QRect(self._start, event.position().toPoint()).normalized()
            self.update()

    def mouseReleaseEvent(self, event) -> None:
        if self._capture_enabled and event.button() == Qt.MouseButton.LeftButton and self._start is not None:
            self._selection = QRect(self._start, event.position().toPoint()).normalized()
            self._start = None
            self.update()

    def paintEvent(self, event) -> None:
        super().paintEvent(event)
        if not self._selection.isNull():
            painter = QPainter(self)
            painter.fillRect(self._selection, QColor(43, 116, 89, 48))
            painter.setPen(QPen(QColor("#2d8cff"), 2, Qt.PenStyle.DashLine))
            painter.drawRect(self._selection)
        if not self._highlight.isNull():
            painter = QPainter(self)
            painter.fillRect(self._highlight, QColor(33, 150, 243, 38))
            painter.setPen(QPen(QColor("#1680c4"), 3, Qt.PenStyle.SolidLine))
            painter.drawRect(self._highlight)


class PdfCaptureDialog(QDialog):
    """在当前小节对应的 PDF 页码范围内框选并返回图片。"""
    def __init__(self, lesson: dict, reference: dict, parent=None):
        super().__init__(parent)
        self.lesson = lesson
        self.reference = reference
        self.captured_image = None
        self.document = QPdfDocument(self)
        self.setWindowTitle("从教材页面插入截图")
        self.resize(1080, 820)
        layout = QVBoxLayout(self)
        layout.setContentsMargins(14, 12, 14, 14)
        header = QLabel(f"{lesson['edition']} · {clean_name(lesson['file'])} · {lesson['section_no']} {lesson['section_title']}")
        header.setObjectName("pdfHeading")
        layout.addWidget(header)
        controls = QHBoxLayout()
        source = "书签定位" if reference.get("source") == "bookmark" else "目录页码定位"
        controls.addWidget(QLabel(f"本节教材范围：第 {reference['start']}–{reference['end']} 页（{source}）"))
        controls.addStretch()
        previous = QPushButton("上一页")
        previous.setObjectName("smallAction")
        previous.clicked.connect(lambda: self.set_page(self.page_box.value() - 1))
        controls.addWidget(previous)
        controls.addWidget(QLabel("页码"))
        self.page_box = QSpinBox()
        self.page_box.setRange(reference["start"], reference["end"])
        self.page_box.setValue(reference["start"])
        self.page_box.valueChanged.connect(self.set_page)
        controls.addWidget(self.page_box)
        following = QPushButton("下一页")
        following.setObjectName("smallAction")
        following.clicked.connect(lambda: self.set_page(self.page_box.value() + 1))
        controls.addWidget(following)
        controls.addWidget(QLabel("缩放"))
        self.zoom_box = QSpinBox()
        self.zoom_box.setRange(50, 250)
        self.zoom_box.setSingleStep(25)
        self.zoom_box.setValue(100)
        self.zoom_box.setSuffix("%")
        self.zoom_box.setToolTip("缩放页面；框选截图会按当前清晰度保存")
        self.zoom_box.valueChanged.connect(lambda _value: self.render_page(self.page_box.value()))
        controls.addWidget(self.zoom_box)
        layout.addLayout(controls)
        guide = QLabel("在页面上拖拽框选需要引用的区域；可切换本节范围内的页面后重新框选。")
        guide.setObjectName("sectionHint")
        layout.addWidget(guide)
        self.crop_label = PdfCropLabel()
        scroll = QScrollArea()
        scroll.setWidgetResizable(False)
        scroll.setAlignment(Qt.AlignmentFlag.AlignHCenter | Qt.AlignmentFlag.AlignTop)
        scroll.setWidget(self.crop_label)
        layout.addWidget(scroll, 1)
        actions = QHBoxLayout()
        reset = QPushButton("清除框选")
        reset.setObjectName("smallAction")
        reset.clicked.connect(lambda: self.render_page(self.page_box.value()))
        actions.addWidget(reset)
        actions.addStretch()
        cancel = QPushButton("取消")
        cancel.setObjectName("smallAction")
        cancel.clicked.connect(self.reject)
        actions.addWidget(cancel)
        confirm = QPushButton("插入框选截图")
        confirm.clicked.connect(self.accept_capture)
        actions.addWidget(confirm)
        layout.addLayout(actions)
        if self.document.load(str(reference["path"])) != QPdfDocument.Error.None_:
            QMessageBox.warning(self, "无法打开教材", f"无法读取 PDF：\n{reference['path']}")
            self.reject()
            return
        self.render_page(reference["start"])

    def set_page(self, page: int) -> None:
        page = max(self.reference["start"], min(self.reference["end"], page))
        if page != self.page_box.value():
            self.page_box.setValue(page)
            return
        self.render_page(page)

    def render_page(self, page: int) -> None:
        page_index = page - 1
        point_size = self.document.pagePointSize(page_index)
        width = round(1440 * self.zoom_box.value() / 100)
        height = max(1, round(width * point_size.height() / point_size.width()))
        image = self.document.render(page_index, QSize(width, height))
        self.crop_label.set_page_image(image)

    def accept_capture(self) -> None:
        image = self.crop_label.selected_image()
        if image is None:
            QMessageBox.information(self, "请先框选", "请在教材页面上拖拽框选需要插入的区域。")
            return
        self.captured_image = image
        self.accept()


class ChapterIntroPageDialog(QDialog):
    """为章引言选择一个准确的教材页，并在确认前直接预览。"""
    def __init__(self, pdf_path: Path, initial_page: int, parent=None):
        super().__init__(parent)
        self.setWindowTitle("修正章引言页")
        self.resize(760, 760)
        self.pdf_path = pdf_path
        self.document = QPdfDocument(self)
        self.selected_page = 0
        if self.document.load(str(pdf_path)) != QPdfDocument.Error.None_ or not self.document.pageCount():
            self.reject()
            return
        layout = QVBoxLayout(self)
        layout.setContentsMargins(14, 12, 14, 14)
        layout.setSpacing(8)
        controls = QHBoxLayout()
        controls.addWidget(QLabel("选择章引言所在页"))
        previous = QPushButton("‹")
        previous.setObjectName("pdfControl")
        previous.clicked.connect(lambda: self.set_page(self.page_box.value() - 1))
        controls.addWidget(previous)
        self.page_box = QSpinBox()
        self.page_box.setRange(1, self.document.pageCount())
        self.page_box.setValue(max(1, min(initial_page, self.document.pageCount())))
        self.page_box.valueChanged.connect(self.set_page)
        controls.addWidget(self.page_box)
        controls.addWidget(QLabel(f"/ {self.document.pageCount()}"))
        following = QPushButton("›")
        following.setObjectName("pdfControl")
        following.clicked.connect(lambda: self.set_page(self.page_box.value() + 1))
        controls.addWidget(following)
        controls.addStretch()
        layout.addLayout(controls)
        self.preview = SourceImagePreview()
        scroll = QScrollArea()
        scroll.setWidgetResizable(True)
        scroll.setWidget(self.preview)
        layout.addWidget(scroll, 1)
        actions = QHBoxLayout()
        actions.addStretch()
        cancel = QPushButton("取消")
        cancel.setObjectName("smallAction")
        cancel.clicked.connect(self.reject)
        actions.addWidget(cancel)
        confirm = QPushButton("使用此页")
        confirm.setObjectName("primaryCompact")
        confirm.clicked.connect(self.accept_page)
        actions.addWidget(confirm)
        layout.addLayout(actions)
        self.set_page(self.page_box.value())

    def set_page(self, page: int) -> None:
        page = max(1, min(page, self.document.pageCount()))
        if page != self.page_box.value():
            self.page_box.setValue(page)
            return
        self.preview.set_pdf_page(self.pdf_path, page)

    def accept_page(self) -> None:
        self.selected_page = self.page_box.value()
        self.accept()


class PdfReaderPanel(QFrame):
    """常驻右栏教材阅读器：单页渲染、整书翻阅、框选截图与来源高亮。"""
    capture_confirmed = Signal(object, int, object)
    capture_cancelled = Signal()
    locate_requested = Signal()

    def __init__(self, parent=None):
        super().__init__(parent)
        self.setObjectName("pdfReader")
        self.document = QPdfDocument(self)
        self.pdf_path = Path()
        self.current_page = 0
        self.highlight_rect: dict | None = None
        self.capture_mode = False
        self.fit_width_enabled = False

        layout = QVBoxLayout(self)
        layout.setContentsMargins(10, 10, 10, 10)
        layout.setSpacing(6)
        navigation = QHBoxLayout()
        navigation.setSpacing(5)
        self.previous = QPushButton("‹")
        self.previous.setObjectName("pdfControl")
        self.previous.setToolTip("上一页")
        self.previous.clicked.connect(lambda: self.set_page(self.current_page - 1))
        navigation.addWidget(self.previous)
        self.page_box = QSpinBox()
        self.page_box.setObjectName("pdfPageBox")
        self.page_box.setRange(1, 1)
        self.page_box.valueChanged.connect(self.set_page)
        navigation.addWidget(self.page_box)
        self.total_pages = QLabel("/ —")
        self.total_pages.setObjectName("pdfPageTotal")
        navigation.addWidget(self.total_pages)
        self.next = QPushButton("›")
        self.next.setObjectName("pdfControl")
        self.next.setToolTip("下一页")
        self.next.clicked.connect(lambda: self.set_page(self.current_page + 1))
        navigation.addWidget(self.next)
        navigation.addStretch()
        self.locate_button = QPushButton("定位本节")
        self.locate_button.setObjectName("smallAction")
        self.locate_button.clicked.connect(self.locate_requested.emit)
        navigation.addWidget(self.locate_button)
        layout.addLayout(navigation)

        zoom_controls = QHBoxLayout()
        zoom_controls.setSpacing(5)
        self.zoom_out = QPushButton("−")
        self.zoom_out.setObjectName("pdfControl")
        self.zoom_out.setToolTip("缩小")
        self.zoom_out.clicked.connect(lambda: self.zoom_box.setValue(self.zoom_box.value() - 10))
        zoom_controls.addWidget(self.zoom_out)
        self.zoom_box = QSpinBox()
        self.zoom_box.setObjectName("pdfZoomBox")
        self.zoom_box.setRange(20, 260)
        self.zoom_box.setSingleStep(10)
        self.zoom_box.setValue(85)
        self.zoom_box.setSuffix("%")
        self.zoom_box.valueChanged.connect(self.on_zoom_changed)
        zoom_controls.addWidget(self.zoom_box)
        self.zoom_in = QPushButton("+")
        self.zoom_in.setObjectName("pdfControl")
        self.zoom_in.setToolTip("放大")
        self.zoom_in.clicked.connect(lambda: self.zoom_box.setValue(self.zoom_box.value() + 10))
        zoom_controls.addWidget(self.zoom_in)
        self.fit_width = QPushButton("适合宽度")
        self.fit_width.setObjectName("smallAction")
        self.fit_width.clicked.connect(self.fit_to_width)
        zoom_controls.addWidget(self.fit_width)
        zoom_controls.addStretch()
        layout.addLayout(zoom_controls)

        self.bookmarks = QComboBox()
        self.bookmarks.setObjectName("bookmarkBox")
        self.bookmarks.addItem("书签与章节跳转", None)
        self.bookmarks.currentIndexChanged.connect(self.jump_to_bookmark)
        layout.addWidget(self.bookmarks)

        self.capture_bar = QFrame()
        self.capture_bar.setObjectName("captureBar")
        capture_layout = QHBoxLayout(self.capture_bar)
        capture_layout.setContentsMargins(8, 6, 8, 6)
        self.capture_hint = QLabel("在页面上拖拽框选教材内容")
        capture_layout.addWidget(self.capture_hint, 1)
        cancel = QPushButton("取消")
        cancel.setObjectName("smallAction")
        cancel.clicked.connect(self.cancel_capture)
        capture_layout.addWidget(cancel)
        confirm = QPushButton("插入框选")
        confirm.setObjectName("primaryCompact")
        confirm.clicked.connect(self.confirm_capture)
        capture_layout.addWidget(confirm)
        self.capture_bar.setVisible(False)
        layout.addWidget(self.capture_bar)

        self.crop_label = PdfCropLabel()
        self.scroll = QScrollArea()
        self.scroll.setObjectName("pdfScroll")
        self.scroll.setWidgetResizable(False)
        self.scroll.setAlignment(Qt.AlignmentFlag.AlignHCenter | Qt.AlignmentFlag.AlignTop)
        self.scroll.viewport().installEventFilter(self)
        self.empty_label = QLabel("选择一个教材小节以载入 PDF")
        self.empty_label.setObjectName("pdfEmpty")
        self.empty_label.setAlignment(Qt.AlignmentFlag.AlignCenter)
        self.empty_label.setMinimumSize(280, 180)
        self.scroll.setWidget(self.empty_label)
        layout.addWidget(self.scroll, 1)

    def set_message(self, message: str) -> None:
        self.empty_label.setText(message)
        self.scroll.setWidget(self.empty_label)
        self.capture_mode = False
        self.capture_bar.setVisible(False)
        self.crop_label.set_capture_enabled(False)

    def open_document(self, path: Path, page: int, heading: str, highlight: dict | None = None) -> bool:
        if not path.exists():
            self.set_message("本机尚未配置这本教材 PDF")
            return False
        if path != self.pdf_path:
            if self.document.load(str(path)) != QPdfDocument.Error.None_:
                self.set_message("无法读取这本教材 PDF")
                return False
            self.pdf_path = path
            self.populate_bookmarks()
        page_count = self.document.pageCount()
        if not page_count:
            self.set_message("该 PDF 没有可阅读页面")
            return False
        self.setToolTip(f"{clean_name(path.name)} · {heading}")
        self.total_pages.setText(f"/ {page_count}")
        self.page_box.blockSignals(True)
        self.page_box.setRange(1, page_count)
        self.page_box.blockSignals(False)
        self.highlight_rect = highlight
        self.set_page(max(1, min(page, page_count)), force=True)
        return True

    def populate_bookmarks(self) -> None:
        self.bookmarks.blockSignals(True)
        self.bookmarks.clear()
        self.bookmarks.addItem("书签与章节跳转", None)
        model = QPdfBookmarkModel()
        model.setDocument(self.document)

        def append_children(parent: QModelIndex = QModelIndex()) -> None:
            for row in range(model.rowCount(parent)):
                index = model.index(row, 0, parent)
                title = str(model.data(index, QPdfBookmarkModel.Role.Title) or "未命名书签")
                page = int(model.data(index, QPdfBookmarkModel.Role.Page) or 0) + 1
                level = int(model.data(index, QPdfBookmarkModel.Role.Level) or 0)
                self.bookmarks.addItem(f"{'　' * min(level, 3)}{title}", page)
                append_children(index)

        append_children()
        self.bookmarks.blockSignals(False)

    def jump_to_bookmark(self, index: int) -> None:
        page = self.bookmarks.itemData(index)
        if isinstance(page, int) and page > 0:
            self.highlight_rect = None
            self.set_page(page)

    def set_page(self, page: int, force: bool = False) -> None:
        if not self.document.pageCount():
            return
        page = max(1, min(int(page), self.document.pageCount()))
        if not force and page == self.current_page:
            return
        self.current_page = page
        if self.page_box.value() != page:
            self.page_box.blockSignals(True)
            self.page_box.setValue(page)
            self.page_box.blockSignals(False)
        self.render_page()

    def on_zoom_changed(self, _value: int) -> None:
        self.fit_width_enabled = False
        self.render_page()

    def fit_to_width(self) -> None:
        if not self.document.pageCount() or self.current_page < 1:
            return
        point_size = self.document.pagePointSize(self.current_page - 1)
        if point_size.width() <= 0:
            return
        available = max(220, self.scroll.viewport().width() - 18)
        zoom = round(available * 100 / 1280)
        self.fit_width_enabled = True
        self.zoom_box.blockSignals(True)
        self.zoom_box.setValue(max(self.zoom_box.minimum(), min(self.zoom_box.maximum(), zoom)))
        self.zoom_box.blockSignals(False)
        self.render_page()

    def render_page(self) -> None:
        if not self.document.pageCount() or self.current_page < 1:
            return
        point_size = self.document.pagePointSize(self.current_page - 1)
        logical_width = max(220, round(1280 * self.zoom_box.value() / 100))
        pixel_ratio = max(1.0, self.devicePixelRatioF())
        render_width = round(logical_width * pixel_ratio)
        render_height = max(1, round(render_width * point_size.height() / point_size.width()))
        image = self.document.render(self.current_page - 1, QSize(render_width, render_height))
        self.crop_label.set_page_image(image, pixel_ratio)
        self.crop_label.set_capture_enabled(self.capture_mode)
        self.crop_label.set_highlight_normalized(self.highlight_rect)
        self.scroll.setWidget(self.crop_label)

    def _adjust_zoom(self, amount: int) -> None:
        if not amount:
            return
        self.zoom_box.setValue(max(self.zoom_box.minimum(), min(self.zoom_box.maximum(), self.zoom_box.value() + amount)))

    def eventFilter(self, watched, event) -> bool:  # type: ignore[override]
        if watched is self.scroll.viewport():
            if event.type() == QEvent.Type.Wheel and event.modifiers() & Qt.KeyboardModifier.ControlModifier:
                delta = event.angleDelta().y() or event.pixelDelta().y()
                if delta:
                    self._adjust_zoom(10 if delta > 0 else -10)
                    event.accept()
                    return True
            if event.type() == QEvent.Type.NativeGesture and hasattr(event, "gestureType"):
                native_type = getattr(getattr(Qt, "NativeGestureType", object), "ZoomNativeGesture", None)
                if native_type is not None and event.gestureType() == native_type:
                    value = float(event.value())
                    if value:
                        self._adjust_zoom(max(4, round(abs(value) * 100)) * (1 if value > 0 else -1))
                        event.accept()
                        return True
        return super().eventFilter(watched, event)

    def begin_capture(self) -> bool:
        if not self.document.pageCount():
            return False
        self.capture_mode = True
        self.highlight_rect = None
        self.crop_label.set_capture_enabled(True)
        self.capture_bar.setVisible(True)
        self.capture_hint.setText(f"在第 {self.current_page} 页拖拽框选，确认后插入笔记")
        return True

    def cancel_capture(self) -> None:
        if not self.capture_mode:
            return
        self.capture_mode = False
        self.capture_bar.setVisible(False)
        self.crop_label.set_capture_enabled(False)
        self.capture_cancelled.emit()

    def confirm_capture(self) -> None:
        image = self.crop_label.selected_image()
        rect = self.crop_label.selected_rect_normalized()
        if image is None or rect is None:
            self.capture_hint.setText("请先拖拽框选一个有效区域")
            return
        page = self.current_page
        self.capture_mode = False
        self.capture_bar.setVisible(False)
        self.crop_label.set_capture_enabled(False)
        self.capture_confirmed.emit(image, page, rect)


def clean_name(filename: str) -> str:
    return filename.removesuffix(".pdf").replace("人教A2019-", "人教A ").replace("苏教-", "苏教 ")


def resolve_source_image(image_path: str | Path | None) -> Path | None:
    """资料 JSON 内的绝对路径在另一台电脑上可能不同，按文件名回查资料包。"""
    if not image_path:
        return None
    candidate = Path(image_path)
    if candidate.exists():
        return candidate
    for root in SOURCE_ROOT_CANDIDATES:
        if not root.exists():
            continue
        for folder in (root / "节引言截图", root / "原书页图"):
            if not folder.exists():
                continue
            matches = list(folder.rglob(candidate.name))
            if matches:
                return matches[0]
    return None


@lru_cache(maxsize=256)
def source_intro_crop_rect(page_image_path: str, intro_image_path: str) -> tuple[float, float, float, float] | None:
    """求资料包“引言截图”在对应原书页图中的相对裁剪区域。

    资料包保留的是低分辨率裁图，但它与原书页图逐像素对应。定位出该条带
    后即可从 PDF 的高清渲染结果裁同一块，而无需在页面里展示整页。
    """
    page_image = QImage(page_image_path)
    intro_image = QImage(intro_image_path)
    if page_image.isNull() or intro_image.isNull():
        return None
    if page_image.width() != intro_image.width() or not (0 < intro_image.height() < page_image.height()):
        return None
    # 取分散的深浅像素行寻找原图中的精确起点；避开只比较一片白底造成误判。
    sample_x = tuple(round((page_image.width() - 1) * fraction) for fraction in (0.06, 0.19, 0.37, 0.53, 0.71, 0.89))
    sample_y = tuple(round((intro_image.height() - 1) * fraction) for fraction in (0.04, 0.17, 0.31, 0.47, 0.63, 0.79, 0.94))
    samples = [(x, y, intro_image.pixel(x, y)) for y in sample_y for x in sample_x]
    max_top = page_image.height() - intro_image.height()
    for top in range(max_top + 1):
        if all(page_image.pixel(x, top + y) == pixel for x, y, pixel in samples):
            return (0.0, top / page_image.height(), 1.0, intro_image.height() / page_image.height())
    return None


class NotebookStorage:
    """本机设置 + 可被坚果云同步的笔记资料目录。"""
    FOLDER_NAME = "教材笔记本数据"
    LOCK_TTL_SECONDS = 150

    def __init__(self):
        self.settings = QSettings("Chuan", "高中数学教材笔记本")
        self.device_id = str(self.settings.value("sync/device_id", "")) or uuid.uuid4().hex
        self.settings.setValue("sync/device_id", self.device_id)
        self.device_name = str(self.settings.value("sync/device_name", "")) or f"本机-{self.device_id[:6]}"
        self.settings.setValue("sync/device_name", self.device_name)
        configured = str(self.settings.value("sync/folder", "") or "").strip()
        self.sync_parent = Path(configured).expanduser() if configured else None

    @property
    def enabled(self) -> bool:
        return self.sync_parent is not None

    @property
    def root(self) -> Path:
        return (self.sync_parent / self.FOLDER_NAME) if self.sync_parent else ROOT

    @property
    def notes_path(self) -> Path:
        return self.root / "我的教材笔记.json"

    @property
    def screenshot_dir(self) -> Path:
        return self.root / "教材截图"

    @property
    def locks_dir(self) -> Path:
        return self.root / "locks"

    @property
    def backups_dir(self) -> Path:
        return self.root / "backups"

    def ensure_directories(self) -> None:
        self.root.mkdir(parents=True, exist_ok=True)
        self.screenshot_dir.mkdir(parents=True, exist_ok=True)
        self.locks_dir.mkdir(parents=True, exist_ok=True)
        self.backups_dir.mkdir(parents=True, exist_ok=True)

    @staticmethod
    def atomic_write(path: Path, data: bytes) -> None:
        path.parent.mkdir(parents=True, exist_ok=True)
        target = QSaveFile(str(path))
        if not target.open(QIODevice.OpenModeFlag.WriteOnly):
            raise OSError(f"无法写入：{path}")
        if target.write(data) != len(data) or not target.commit():
            raise OSError(f"无法完成保存：{path}")

    @staticmethod
    def fingerprint(path: Path) -> str:
        try:
            return hashlib.sha256(path.read_bytes()).hexdigest()
        except OSError:
            return ""

    @staticmethod
    def read_json(path: Path) -> dict:
        try:
            value = json.loads(path.read_text(encoding="utf-8"))
            return value if isinstance(value, dict) else {}
        except (OSError, json.JSONDecodeError):
            return {}

    def write_json(self, path: Path, value: dict) -> None:
        self.atomic_write(path, json.dumps(value, ensure_ascii=False, indent=2).encode("utf-8"))

    def configure(self, parent: Path | None) -> None:
        self.sync_parent = parent
        self.settings.setValue("sync/folder", str(parent) if parent else "")
        if parent:
            self.ensure_directories()

    def lock_path(self, lesson_id: str) -> Path:
        return self.locks_dir / f"{hashlib.sha256(lesson_id.encode('utf-8')).hexdigest()}.json"

    def read_lock(self, lesson_id: str) -> dict | None:
        path = self.lock_path(lesson_id)
        lock = self.read_json(path)
        if not lock:
            return None
        try:
            expires = datetime.fromisoformat(str(lock.get("expires_at", "")))
        except ValueError:
            expires = datetime.min
        if expires <= datetime.now():
            try:
                path.unlink()
            except OSError:
                pass
            return None
        return lock

    def acquire_lock(self, lesson_id: str) -> tuple[bool, dict | None]:
        if not self.enabled:
            return True, None
        self.ensure_directories()
        current = self.read_lock(lesson_id)
        if current and current.get("device_id") != self.device_id:
            return False, current
        self.refresh_lock(lesson_id)
        return True, None

    def refresh_lock(self, lesson_id: str) -> None:
        if not self.enabled:
            return
        expires = datetime.now().timestamp() + self.LOCK_TTL_SECONDS
        self.write_json(self.lock_path(lesson_id), {
            "lesson_id": lesson_id,
            "device_id": self.device_id,
            "device_name": self.device_name,
            "updated_at": now(),
            "expires_at": datetime.fromtimestamp(expires).isoformat(timespec="seconds"),
        })

    def release_lock(self, lesson_id: str | None) -> None:
        if not lesson_id or not self.enabled:
            return
        lock = self.read_lock(lesson_id)
        path = self.lock_path(lesson_id)
        if lock and lock.get("device_id") == self.device_id:
            try:
                path.unlink()
            except OSError:
                pass

    def backup_payload(self, label: str, payload: dict) -> Path:
        self.backups_dir.mkdir(parents=True, exist_ok=True)
        safe_label = re.sub(r"[^\w\-]+", "_", label)
        target = self.backups_dir / f"{datetime.now():%Y%m%d_%H%M%S}_{safe_label}.json"
        self.write_json(target, payload)
        return target


ACTIVE_STORAGE: NotebookStorage | None = None


def set_active_storage(storage: NotebookStorage) -> None:
    global ACTIVE_STORAGE, SCREENSHOT_DIR
    ACTIVE_STORAGE = storage
    SCREENSHOT_DIR = storage.screenshot_dir


def data_path() -> Path:
    return ACTIVE_STORAGE.notes_path if ACTIVE_STORAGE else ROOT / "我的教材笔记.json"


def katex_base_url() -> QUrl:
    """让 QWebEngine 从项目内的 KaTeX 资源加载字体、CSS 与脚本，不依赖网络。"""
    return QUrl.fromLocalFile(f"{KATEX_DIST.resolve()}/")


def referenced_screenshot_ids(notes: dict) -> set[str]:
    return set(SCREENSHOT_TOKEN.findall(json.dumps(notes, ensure_ascii=False)))


def find_source_root() -> Path:
    for candidate in SOURCE_ROOT_CANDIDATES:
        if (candidate / "pep_sections_verified.json").exists() or (candidate / "sj_sections_verified.json").exists():
            return candidate
    return SOURCE_ROOT_CANDIDATES[0]


def now() -> str:
    return datetime.now().isoformat(timespec="seconds")


def empty_note() -> dict:
    return {
        "intro_note": "",
        "knowledge": [],
        "patterns": [],
        "examples": [],
        "questions": [],
        "pitfalls": [],
        "lesson_note": "",
    }


def join_legacy_items(items: list[dict]) -> str:
    """把旧的标题/正文卡保存在一个轻量文本字段中。"""
    blocks = []
    for item in items or []:
        title = str(item.get("title", "")).strip()
        content = str(item.get("content", "")).strip()
        if title and content:
            blocks.append(f"{title}\n{content}")
        elif title or content:
            blocks.append(title or content)
    return "\n\n".join(blocks)


def normalize_note(note: dict) -> dict:
    """迁移旧教学卡及 v2 通用项目卡，确保填写内容不会消失。"""
    if not isinstance(note, dict):
        return empty_note()
    # 原教学设计卡里的 examples/questions 与新版字段同名，必须优先识别。
    if any(key in note for key in ("content_line", "goal", "lesson_flow", "micro_teaching")):
        return normalize_legacy_teaching_card(note)
    if any(key in note for key in ("intro_note", "lesson_note", "knowledge", "patterns", "pitfalls")):
        normalized = empty_note()
        for key in normalized:
            value = note.get(key, normalized[key])
            normalized[key] = value if isinstance(value, list if key not in {"intro_note", "lesson_note"} else str) else normalized[key]
        return normalized

    if "items" in note:
        items = note.get("items", {})
        result = empty_note()
        result["intro_note"] = join_legacy_items(items.get("introduction", []))
        result["knowledge"] = [
            {"title": str(item.get("title", "")), "content": str(item.get("content", ""))}
            for item in items.get("knowledge", [])
        ]
        result["patterns"] = [
            {"title": str(item.get("title", "")), "example": "", "note": str(item.get("content", ""))}
            for item in items.get("basic_patterns", [])
        ]
        result["examples"] = [
            {"title": str(item.get("title", "")), "source": "", "problem": "", "note": str(item.get("content", ""))}
            for item in items.get("valuable_examples", [])
        ]
        for item in items.get("question_chain", []):
            title = str(item.get("title", "")).strip()
            content = str(item.get("content", "")).strip()
            if title or content:
                result["questions"].append({
                    "question": title or content,
                    "followups": [{"text": content}] if title and content else [],
                })
        result["pitfalls"] = [
            {"title": str(item.get("title", "")), "content": str(item.get("content", ""))}
            for item in items.get("pitfalls", [])
        ]
        return result

    return normalize_legacy_teaching_card(note)


def normalize_legacy_teaching_card(note: dict) -> dict:
    """原教学设计卡。所有旧字段均保存到最相近的新版位置。"""
    result = empty_note()
    result["intro_note"] = str(note.get("content_line", ""))
    if note.get("goal"):
        result["knowledge"].append({"title": "目标与重点", "content": str(note["goal"])})
    if note.get("examples"):
        result["patterns"].append({"title": "例题与习题组", "example": "", "note": str(note["examples"])})
    if note.get("questions"):
        result["questions"].append({"question": str(note["questions"]), "followups": []})
    if note.get("micro_teaching"):
        result["lesson_note"] = f"【原试讲 / 复盘】\n{note['micro_teaching']}"
    if note.get("lesson_flow"):
        extra = f"【原教学流程】\n{note['lesson_flow']}"
        result["lesson_note"] = f"{result['lesson_note']}\n\n{extra}".strip()
    return result


FORMULA_PATTERN = re.compile(r"(?<!\\)\$(?!\$)(.*?)(?<!\\)\$", re.DOTALL)


def normalize_preview_math(expression: str) -> str:
    """KaTeX 原样接收用户输入；不再为了 MathText 的限制改写公式含义或样式。"""
    return expression.strip()


@lru_cache(maxsize=512)
def render_formula_html(source: str) -> str:
    """输出待 KaTeX 排版的行内节点；不再把每段公式做成孤立 SVG 图片。"""
    match = FORMULA_PATTERN.fullmatch(source)
    if not match:
        return ""
    expression = match.group(1)
    normalized_expression = normalize_preview_math(expression)
    escaped = html.escape(normalized_expression, quote=True)
    return f"<span class='latex-source' data-tex='{escaped}'>${html.escape(expression)}$</span>"


def katex_runtime() -> str:
    """所有预览共用的本地 KaTeX 运行时。脚本加载失败时仍保留原始源码。"""
    return """<link rel='stylesheet' href='katex.min.css'>
<style>body .katex { font-size: 1em !important; }</style>
<script src='katex.min.js'></script>
<script>
window.addEventListener('load', () => {
  document.querySelectorAll('.latex-source').forEach((node) => {
    const source = node.dataset.tex || '';
    try {
      katex.render(source, node, {displayMode: false, throwOnError: false, strict: 'ignore', output: 'htmlAndMathml'});
    } catch (_error) {
      node.textContent = '$' + source + '$';
      node.classList.add('math-fallback');
    }
  });
});
</script>"""


def render_text_fragment(text: str) -> str:
    """转义普通文本，同时把持久化的教材截图标记替换为本地图片。"""
    parts = []
    cursor = 0
    for match in SCREENSHOT_TOKEN.finditer(text):
        parts.append(html.escape(text[cursor:match.start()]))
        image_path = SCREENSHOT_DIR / f"{match.group(1)}.png"
        if image_path.exists():
            # QWebEngine 对 file:// 的跨目录读取会受平台策略影响；嵌入数据可稳定显示并便于预览缓存。
            encoded = base64.b64encode(image_path.read_bytes()).decode("ascii")
            parts.append(f"<img class='textbook-shot' src='data:image/png;base64,{encoded}' alt='教材截图'>")
        else:
            parts.append("<span class='missing-shot'>[教材截图文件缺失]</span>")
        cursor = match.end()
    parts.append(html.escape(text[cursor:]))
    return "".join(parts)


def render_mixed_math_html(text: str, placeholder: str) -> str:
    """与题目管理器一致地将正文分成自然段，再嵌入行内公式。"""
    if not text.strip():
        # 空字段保持真正的留白。字段用途由栏目标题、卡片结构和按钮表达，
        # 不在内容区反复堆放“请填写 / 支持公式”一类的说明文字。
        return ""
    parts = []
    cursor = 0
    for match in FORMULA_PATTERN.finditer(text):
        parts.append(render_text_fragment(text[cursor:match.start()]))
        parts.append(render_formula_html(match.group(0)))
        cursor = match.end()
    parts.append(render_text_fragment(text[cursor:]))
    body = "".join(parts)
    return "".join(f"<p>{paragraph.replace(chr(10), '<br>')}</p>" for paragraph in body.split("\n\n"))


def render_math_field_document(text: str, placeholder: str, compact: bool = False) -> str:
    """与题目管理器一致地交给 Chromium 渲染 HTML + SVG。"""
    typography = (
        "body { padding: 5px 8px; font-size: 16px; line-height: 1.45; } "
        "p { margin: 0; line-height: 1.45; white-space: nowrap; overflow: hidden; }"
        if compact else
        "body { padding: 7px 10px; font-size: 17px; line-height: 1.82; } "
        "p { margin: 8px 0; line-height: 1.82; font-size: 17px; word-break: break-word; }"
    )
    return f"""<!doctype html>
<html lang='zh-CN'><head><meta charset='utf-8'><style>
* {{ box-sizing: border-box; }}
html, body {{ margin: 0; overflow: hidden; background: transparent; }}
body {{ color: #e4eef3; font-family: \"Times New Roman\", \"Songti SC\", \"STSong\", serif; cursor: text; }}
{typography}
.latex-source {{ white-space: nowrap; margin: 0 .18em; }}
.katex {{ font-size: 1em; }}
#content {{ display: flow-root; padding-bottom: 4px; }}
.textbook-shot {{ display: block; max-width: min(100%, 760px); max-height: 460px; object-fit: contain; margin: 10px 0; border: 1px solid #d6cdbb; border-radius: 6px; }}
.missing-shot {{ color: #ff9a9f; font-family: \"PingFang SC\", sans-serif; }}
.math-fallback {{ color: #ff9a9f; font-family: \"Menlo\", monospace; font-size: .9em; }}
.empty-math-field {{ color: #8da4b2; font-family: \"PingFang SC\", sans-serif; }}
</style>{katex_runtime()}</head><body onclick=\"window.location.href='textbook://edit'\"><div id='content'>{render_mixed_math_html(text, placeholder)}</div></body></html>"""


def render_list_detail_document(key: str, entries: list[dict]) -> str:
    title = SECTION_META[key][0]
    cards = []
    for index, entry in enumerate(entries, 1):
        if key == "knowledge":
            body = f"<h3>{index}. {render_mixed_math_html(entry.get('title', ''), '未命名知识点')}</h3><div>{render_mixed_math_html(entry.get('content', ''), '暂无内容')}</div>"
        elif key == "patterns":
            body = (
                f"<h3>{index}. {render_mixed_math_html(entry.get('title', ''), '未命名题型')}</h3>"
                f"<h4>示例</h4><div>{render_mixed_math_html(entry.get('example', ''), '暂无示例')}</div>"
                f"<h4>备注</h4><div>{render_mixed_math_html(entry.get('note', ''), '暂无备注')}</div>"
            )
        elif key == "examples":
            body = (
                f"<h3>{index}. {render_mixed_math_html(entry.get('title', ''), '未命名例题')}</h3>"
                f"<h4>来源</h4><div>{render_mixed_math_html(entry.get('source', ''), '未标注')}</div>"
                f"<h4>原题</h4><div>{render_mixed_math_html(entry.get('problem', ''), '暂无原题')}</div>"
                f"<h4>备注</h4><div>{render_mixed_math_html(entry.get('note', ''), '暂无备注')}</div>"
            )
        elif key == "questions":
            followups = "".join(
                f"<div class='question-followup'><span>【追问{followup_index}】</span>{render_mixed_math_html(item.get('text', ''), '')}</div>"
                for followup_index, item in enumerate(entry.get("followups", []), 1)
            )
            body = f"<div class='question-line'><strong>【问题{index}】</strong>{render_mixed_math_html(entry.get('question', ''), '')}</div>{followups}"
        else:
            body = f"<h3>{index}. {render_mixed_math_html(entry.get('title', ''), '未命名项目')}</h3><div>{render_mixed_math_html(entry.get('content', ''), '暂无内容')}</div>"
        cards.append(f"<article>{body}</article>")
    content = "".join(cards) or "<p class='empty'>暂未添加项目。</p>"
    return f"""<!doctype html><html lang='zh-CN'><head><meta charset='utf-8'><style>
* {{ box-sizing:border-box; }} body {{ margin:0; padding:22px 24px 36px; background:#18232e; color:#e4eef3; font-family:\"Times New Roman\",\"Songti SC\",\"STSong\",serif; font-size:16px; line-height:1.75; }}
article {{ background:#23313d; border:1px solid #3b5260; border-left:4px solid #4b9fff; border-radius:8px; padding:13px 16px; margin:0 0 12px; }} h3 {{ margin:0 0 8px; color:#a4ceff; font-size:18px; }} h4 {{ margin:11px 0 2px; color:#9db8d8; font-family:\"PingFang SC\",sans-serif; font-size:13px; }} p {{ margin:8px 0; line-height:1.82; font-size:17px; word-break:break-word; }} .question-line {{ display:flex; gap:10px; align-items:baseline; }} .question-line strong, .question-followup span {{ color:#a8c8dd; font-family:\"PingFang SC\",sans-serif; font-size:13px; white-space:nowrap; }} .question-line p, .question-followup p {{ margin:0; }} .question-followup {{ display:flex; gap:10px; align-items:baseline; margin:7px 0 0 22px; }} .latex-source {{ white-space:nowrap; margin:0 .18em; }} .katex {{ font-size:1em; }} .textbook-shot {{ display:block; max-width:min(100%,760px); max-height:460px; object-fit:contain; margin:10px 0; border:1px solid #587287; border-radius:6px; }} .missing-shot {{ color:#ff9a9f; }} .math-fallback {{ color:#ff9a9f; font-family:Menlo,monospace; }} .empty {{ color:#9bb0be; font-style:italic; }}
</style>{katex_runtime()}</head><body><h2>{title}</h2>{content}</body></html>"""


class MathPreviewPage(QWebEnginePage):
    edit_requested = Signal()

    def acceptNavigationRequest(self, url, navigation_type, is_main_frame):  # type: ignore[override]
        if url.scheme() == "textbook":
            self.edit_requested.emit()
            return False
        return super().acceptNavigationRequest(url, navigation_type, is_main_frame)


class ClickableMathView(QWebEngineView):
    clicked = Signal()
    content_height_changed = Signal(int)

    def __init__(self, parent=None):
        super().__init__(parent)
        self.setObjectName("renderedMath")
        page = MathPreviewPage(self)
        page.edit_requested.connect(lambda: self.clicked.emit())
        page.setBackgroundColor(QColor("#273743"))
        self.setPage(page)
        self.settings().setAttribute(QWebEngineSettings.WebAttribute.LocalContentCanAccessFileUrls, True)
        self._auto_height = True
        self._last_height = 0
        self.setSizePolicy(QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Fixed)
        self.loadFinished.connect(self.page_loaded)

    def page_loaded(self, _ok: bool) -> None:
        # KaTeX 与字体均从本地资源加载；再校准一次，避免首次排版后裁掉分式上下部分。
        self.measure_content_height()
        QTimer.singleShot(80, self.measure_content_height)

    def set_auto_height(self, enabled: bool) -> None:
        self._auto_height = enabled

    def resizeEvent(self, event) -> None:
        super().resizeEvent(event)
        if self._auto_height:
            QTimer.singleShot(0, self.measure_content_height)

    def set_content(self, text: str, placeholder: str, compact: bool = False) -> None:
        self._last_height = 0
        self.setHtml(render_math_field_document(text, placeholder, compact), katex_base_url())

    def measure_content_height(self) -> None:
        if not self._auto_height:
            return
        script = """
            (() => {
                const node = document.getElementById('content');
                if (!node) return 32;
                const style = getComputedStyle(document.body);
                const contentHeight = Math.max(node.getBoundingClientRect().height, node.scrollHeight);
                return Math.ceil(contentHeight + parseFloat(style.paddingTop) + parseFloat(style.paddingBottom) + 2);
            })();
        """
        self.page().runJavaScript(script, self.apply_content_height)

    def apply_content_height(self, value) -> None:
        try:
            # 普通文字仍会自然收缩；带教材截图时允许完整显示一张中等高度的框选图。
            height = max(34, min(760, int(float(value))))
        except (TypeError, ValueError):
            return
        if height == self._last_height:
            return
        self._last_height = height
        self.setFixedHeight(height)
        self.content_height_changed.emit(height)


class ScreenshotPreview(QLabel):
    """截图用原生 QLabel 缩放显示，避免单行 Web 预览截断位图。"""
    source_requested = Signal(str)

    def __init__(self, screenshot_id: str, image_path: Path, parent=None):
        super().__init__(parent)
        self.screenshot_id = screenshot_id
        self._original = QPixmap(str(image_path))
        self.setObjectName("textbookAttachment")
        self.setAlignment(Qt.AlignmentFlag.AlignLeft | Qt.AlignmentFlag.AlignTop)
        self.setSizePolicy(QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Preferred)
        self.setMinimumWidth(0)
        self.setToolTip(f"教材截图：{image_path.name}")
        self.refresh_scaled_pixmap()

    def hasHeightForWidth(self) -> bool:  # type: ignore[override]
        return not self._original.isNull()

    def heightForWidth(self, width: int) -> int:  # type: ignore[override]
        if self._original.isNull():
            return 24
        target_width = max(120, min(width, 680, self._original.width()))
        return round(self._original.height() * target_width / self._original.width())

    def sizeHint(self) -> QSize:  # type: ignore[override]
        width = min(560, self._original.width()) if not self._original.isNull() else 160
        return QSize(width, self.heightForWidth(width))

    def resizeEvent(self, event) -> None:
        super().resizeEvent(event)
        self.refresh_scaled_pixmap()

    def refresh_scaled_pixmap(self) -> None:
        if self._original.isNull():
            self.setText("教材截图无法读取")
            return
        available = self.width() if self.width() > 20 else min(560, self._original.width())
        target_width = max(120, min(available, 680, self._original.width()))
        self.setPixmap(self._original.scaledToWidth(target_width, Qt.TransformationMode.SmoothTransformation))

    def mouseReleaseEvent(self, event) -> None:  # type: ignore[override]
        if event.button() == Qt.MouseButton.LeftButton and not self._original.isNull():
            self.source_requested.emit(self.screenshot_id)
            event.accept()
            return
        super().mouseReleaseEvent(event)


class SourceImagePreview(QLabel):
    """教材资料包中的原书截图，按容器宽度等比例显示。"""
    def __init__(self, parent=None):
        super().__init__(parent)
        self._original = QPixmap()
        self.setObjectName("sourceImage")
        self.setAlignment(Qt.AlignmentFlag.AlignLeft | Qt.AlignmentFlag.AlignTop)
        self.setSizePolicy(QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Preferred)
        self.setMinimumWidth(0)

    def set_source(self, image_path: str | Path | None) -> None:
        self._original = QPixmap(str(image_path)) if image_path and Path(image_path).exists() else QPixmap()
        if self._original.isNull():
            self.clear()
            self.setText("未找到对应的教材引言截图")
            self.setMinimumHeight(34)
        else:
            self.setText("")
            self.refresh_pixmap()

    def set_pdf_page(self, pdf_path: str | Path | None, page: int, crop_rect: tuple[float, float, float, float] | None = None) -> bool:
        """按 PDF 物理页渲染；可只取资料包引言所对应的页面区域。"""
        path = Path(pdf_path) if pdf_path else Path()
        if not path.exists() or page < 1:
            return False
        document = QPdfDocument(self)
        if document.load(str(path)) != QPdfDocument.Error.None_ or page > document.pageCount():
            return False
        point_size = document.pagePointSize(page - 1)
        # 引言图会在中间工作区放大显示；直接以较高分辨率从 PDF 重绘，
        # 不放大资料包里较小的预先截屏，避免文字发糊。
        width = 2600
        height = max(1, round(width * point_size.height() / point_size.width()))
        rendered = document.render(page - 1, QSize(width, height))
        # PDF 渲染结果可能带透明底；在深色界面中必须先落到白纸上。
        paper = QImage(rendered.size(), QImage.Format.Format_ARGB32_Premultiplied)
        paper.fill(Qt.GlobalColor.white)
        painter = QPainter(paper)
        painter.drawImage(0, 0, rendered)
        painter.end()
        if crop_rect:
            left, top, width_ratio, height_ratio = crop_rect
            x = max(0, min(paper.width() - 1, round(paper.width() * left)))
            y = max(0, min(paper.height() - 1, round(paper.height() * top)))
            width = max(1, min(paper.width() - x, round(paper.width() * width_ratio)))
            height = max(1, min(paper.height() - y, round(paper.height() * height_ratio)))
            paper = paper.copy(x, y, width, height)
        self._original = QPixmap.fromImage(paper)
        if self._original.isNull():
            return False
        self.setText("")
        self.refresh_pixmap()
        return True

    def hasHeightForWidth(self) -> bool:  # type: ignore[override]
        return not self._original.isNull()

    def heightForWidth(self, width: int) -> int:  # type: ignore[override]
        if self._original.isNull():
            return 34
        target_width = max(120, min(width, 980, self._original.width()))
        return round(self._original.height() * target_width / self._original.width())

    def sizeHint(self) -> QSize:  # type: ignore[override]
        width = min(760, self._original.width()) if not self._original.isNull() else 240
        return QSize(width, self.heightForWidth(width))

    def resizeEvent(self, event) -> None:
        super().resizeEvent(event)
        self.refresh_pixmap()

    def refresh_pixmap(self) -> None:
        if not self._original.isNull():
            available = self.width() if self.width() > 20 else min(760, self._original.width())
            width = max(120, min(available, 980, self._original.width()))
            self.setPixmap(self._original.scaledToWidth(width, Qt.TransformationMode.SmoothTransformation))


class FormulaTextEdit(QWidget):
    """静态时只展示排版结果；编辑时并排保留源码输入与实时 KaTeX 预览。"""
    textChanged = Signal()
    screenshot_request_handler = None
    screenshot_open_handler = None
    image_request_handler = None
    edit_request_handler = None

    def __init__(self, parent=None, single_line: bool = False):
        super().__init__(parent)
        self._raw_text = ""
        self._single_line = single_line
        self._placeholder = ""
        self._media_mode = False
        self.preview_timer = QTimer(self)
        self.preview_timer.setSingleShot(True)
        self.preview_timer.setInterval(140)
        self.preview_timer.timeout.connect(self.refresh_view)
        self.setObjectName("mathField")
        # QWebEngineView 会给出很大的首选宽度；单行表格中必须允许布局把它压缩。
        self.setMinimumWidth(0)
        layout = QVBoxLayout(self)
        layout.setContentsMargins(0, 0, 0, 0)
        layout.setSpacing(0)
        self.view = ClickableMathView()
        self.view.setMinimumWidth(0)
        self.view.setFocusPolicy(Qt.FocusPolicy.NoFocus)
        self.view.clicked.connect(self.start_editing)
        self.view.content_height_changed.connect(self._display_height_changed)
        self.attachments = QWidget()
        self.attachments.setObjectName("textbookAttachments")
        self.attachments_layout = QVBoxLayout(self.attachments)
        self.attachments_layout.setContentsMargins(0, 8, 0, 0)
        self.attachments_layout.setSpacing(6)
        self.attachments.setVisible(False)
        self.edit_holder = QWidget()
        self.edit_holder.setMinimumWidth(0)
        edit_layout = QVBoxLayout(self.edit_holder)
        edit_layout.setContentsMargins(0, 0, 0, 0)
        edit_layout.setSpacing(6)
        self.editor = QTextEdit()
        self.editor.setObjectName("latexSource")
        self.editor.setMinimumWidth(0)
        self.editor.textChanged.connect(self._source_changed)
        self.editor.installEventFilter(self)
        self.done = QPushButton("完成编辑")
        self.done.setObjectName("finishEdit")
        self.done.clicked.connect(self.finish_editing)
        self.insert_screenshot = QPushButton("插入教材截图")
        self.insert_screenshot.setObjectName("smallAction")
        self.insert_screenshot.clicked.connect(self.request_screenshot)
        self.insert_image = QPushButton("插入本机图片")
        self.insert_image.setObjectName("smallAction")
        self.insert_image.clicked.connect(self.request_local_image)
        self._capture_in_progress = False
        if single_line:
            self._single_display_height = 40
            # 源码编辑和阅读态保持同高，紧凑列表编辑时不会反复推挤页面。
            self._single_edit_height = self._single_display_height
            self.editor.setFixedHeight(self._single_display_height)
            self.editor.setLineWrapMode(QTextEdit.LineWrapMode.NoWrap)
            self.editor.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
            line = QHBoxLayout()
            line.setContentsMargins(0, 0, 0, 0)
            line.addWidget(self.editor, 1)
            self.insert_screenshot.setText("▣")
            self.insert_screenshot.setToolTip("从当前小节教材页面框选并插入截图")
            self.insert_screenshot.setFixedWidth(30)
            # 单行内容的编辑空间优先留给源码；图片可在需要多行内容的字段中插入。
            self.insert_image.setVisible(False)
            self.done.setVisible(False)
            line.addWidget(self.insert_screenshot)
            edit_layout.addLayout(line)
            self.view.setFixedHeight(self._single_display_height)
            self.view.set_auto_height(False)
            self.setFixedHeight(self._single_display_height)
        else:
            edit_layout.addWidget(self.editor)
            actions = QHBoxLayout()
            actions.addStretch()
            actions.addWidget(self.insert_screenshot)
            actions.addWidget(self.insert_image)
            actions.addWidget(self.done)
            edit_layout.addLayout(actions)
        layout.addWidget(self.edit_holder)
        layout.addWidget(self.view)
        layout.addWidget(self.attachments)
        self.edit_holder.setVisible(False)

    def toPlainText(self) -> str:  # type: ignore[override]
        return self._raw_text

    def text(self) -> str:
        return self._raw_text

    def setText(self, text: str) -> None:
        self.setPlainText(text)

    def setPlainText(self, text: str) -> None:  # type: ignore[override]
        self._raw_text = text or ""
        self.editor.blockSignals(True)
        self.editor.setPlainText(self._raw_text)
        self.editor.blockSignals(False)
        self.refresh_view()

    def setPlaceholderText(self, text: str) -> None:
        # 交互字段不使用说明性占位符；空白就是空白，避免笔记页面显得嘈杂。
        self._placeholder = ""
        self.editor.setPlaceholderText("")
        self.refresh_view()

    def setMinimumHeight(self, height: int) -> None:  # type: ignore[override]
        # 内容展示态必须随文本收缩；最小高度只用于真正的编辑器。
        if not self._single_line:
            self.editor.setMinimumHeight(height)

    def _display_height_changed(self, _height: int) -> None:
        self.updateGeometry()
        self.textChanged.emit()

    def _configure_single_line_media_mode(self, enabled: bool) -> None:
        """紧凑表格默认单行；插入教材截图后自动展开，不能用单行高度裁掉图片。"""
        if not self._single_line:
            return
        self._media_mode = enabled
        if enabled:
            self.view.set_auto_height(True)
            self.view.setMinimumHeight(self._single_display_height)
            self.view.setMaximumHeight(760)
            QWidget.setMinimumHeight(self, self._single_edit_height if self.edit_holder.isVisible() else self._single_display_height)
            self.setMaximumHeight(16777215)
            self.setSizePolicy(QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Preferred)
        else:
            self.view.set_auto_height(False)
            self.view.setFixedHeight(self._single_display_height)
            self.setFixedHeight(self._single_edit_height if self.edit_holder.isVisible() else self._single_display_height)

    def start_editing(self) -> None:
        if self.edit_holder.isVisible():
            self.editor.setFocus()
            return
        guard = type(self).edit_request_handler
        if callable(guard) and not guard(self):
            return
        self.editor.blockSignals(True)
        self.editor.setPlainText(self._raw_text)
        self.editor.blockSignals(False)
        # 编辑时只显示源码框；预览与源码同时占位会让单行卡片变高并导致滚动区抖动。
        self.view.setVisible(False)
        self.edit_holder.setVisible(True)
        if self._single_line:
            self._configure_single_line_media_mode(bool(SCREENSHOT_TOKEN.search(self._raw_text)))
        self.editor.setFocus()
        self.editor.moveCursor(QTextCursor.MoveOperation.End)
        # 通知外层可排序卡片重新计算高度，防止编辑器被列表裁切。
        self.textChanged.emit()

    def eventFilter(self, watched, event) -> bool:
        if watched is self.editor and event.type() == QEvent.Type.FocusOut:
            # 让“完成编辑”成为可选操作：离开源码框即收起并渲染。
            QTimer.singleShot(0, self.finish_if_needed)
        return super().eventFilter(watched, event)

    def finish_if_needed(self) -> None:
        if self.edit_holder.isVisible() and not self.editor.hasFocus() and not self._capture_in_progress:
            self.finish_editing()

    def finish_editing(self) -> None:
        self.preview_timer.stop()
        self._raw_text = self.editor.toPlainText()
        self.edit_holder.setVisible(False)
        self.view.setVisible(True)
        if self._single_line:
            self._configure_single_line_media_mode(bool(SCREENSHOT_TOKEN.search(self._raw_text)))
        self.refresh_view()
        self.textChanged.emit()

    def _source_changed(self) -> None:
        self._raw_text = self.editor.toPlainText()
        if self.edit_holder.isVisible() and self.view.isVisible():
            self.preview_timer.start()
        self.textChanged.emit()

    def request_screenshot(self) -> None:
        guard = type(self).edit_request_handler
        if callable(guard) and not guard(self):
            return
        handler = type(self).screenshot_request_handler
        if not callable(handler):
            QMessageBox.information(self, "尚未选择教材", "请先从左侧选择一个教材小节，再插入教材截图。")
            return
        self._capture_in_progress = True
        try:
            screenshot_id = handler(self)
        except Exception:
            self._capture_in_progress = False
            raise
        if screenshot_id:
            self.insert_external_screenshot(screenshot_id)
        elif not self._capture_in_progress:
            self.finish_if_needed()

    def insert_external_screenshot(self, screenshot_id: str) -> None:
        """供右侧阅读器框选完成后回插，保持原字段和原光标位置。"""
        if not self.edit_holder.isVisible():
            self.start_editing()
        self.editor.insertPlainText(f"[[教材截图:{screenshot_id}]]")
        self._capture_in_progress = False
        self.preview_timer.stop()
        self._raw_text = self.editor.toPlainText()
        self.refresh_view()
        self.textChanged.emit()
        self.editor.setFocus()

    def cancel_external_capture(self) -> None:
        self._capture_in_progress = False
        self.finish_if_needed()

    def request_local_image(self) -> None:
        guard = type(self).edit_request_handler
        if callable(guard) and not guard(self):
            return
        handler = type(self).image_request_handler
        if not callable(handler):
            return
        image_id = handler(self)
        if image_id:
            self.editor.insertPlainText(f"[[教材截图:{image_id}]]")
            self.preview_timer.stop()
            self._raw_text = self.editor.toPlainText()
            self.refresh_view()
            self.textChanged.emit()
            self.editor.setFocus()

    def refresh_view(self) -> None:
        has_screenshot = bool(SCREENSHOT_TOKEN.search(self._raw_text))
        self._configure_single_line_media_mode(has_screenshot)
        self.refresh_attachments()
        # 位图由原生附件区显示；网页预览中直接移除内部标记，不向用户暴露实现细节。
        preview_text = SCREENSHOT_TOKEN.sub("", self._raw_text)
        self.view.set_content(preview_text, self._placeholder, self._single_line)

    def refresh_attachments(self) -> None:
        while self.attachments_layout.count():
            item = self.attachments_layout.takeAt(0)
            if item.widget():
                item.widget().deleteLater()
        screenshot_ids = SCREENSHOT_TOKEN.findall(self._raw_text)
        for screenshot_id in screenshot_ids:
            image_path = SCREENSHOT_DIR / f"{screenshot_id}.png"
            if image_path.exists():
                attachment = QFrame()
                attachment.setObjectName("textbookAttachment")
                attachment_layout = QVBoxLayout(attachment)
                attachment_layout.setContentsMargins(6, 6, 6, 5)
                attachment_layout.setSpacing(4)
                preview = ScreenshotPreview(screenshot_id, image_path)
                preview.source_requested.connect(self.open_screenshot_source)
                attachment_layout.addWidget(preview)
                metadata_path = SCREENSHOT_DIR / f"{screenshot_id}.json"
                try:
                    metadata = json.loads(metadata_path.read_text(encoding="utf-8")) if metadata_path.exists() else {}
                except (OSError, json.JSONDecodeError):
                    metadata = {}
                page = metadata.get("page")
                if isinstance(page, int) and page > 0:
                    source = QPushButton(f"教材第 {page} 页 · 回到原书")
                    source.setObjectName("attachmentSource")
                    source.clicked.connect(lambda _checked=False, shot=screenshot_id: self.open_screenshot_source(shot))
                    attachment_layout.addWidget(source, 0, Qt.AlignmentFlag.AlignLeft)
                self.attachments_layout.addWidget(attachment)
            else:
                missing = QLabel("教材截图文件缺失")
                missing.setObjectName("missingAttachment")
                self.attachments_layout.addWidget(missing)
        self.attachments.setVisible(bool(screenshot_ids))
        self.updateGeometry()
        QTimer.singleShot(0, self.textChanged.emit)

    def open_screenshot_source(self, screenshot_id: str) -> None:
        handler = type(self).screenshot_open_handler
        if callable(handler):
            handler(screenshot_id)


class DragGrip(QLabel):
    """把卡片内的抓手事件交给外层 QListWidget 发起真实拖拽。"""
    def __init__(self, card, parent=None):
        super().__init__("⠿", parent)
        self.card = card
        self.setObjectName("dragGrip")
        self.setToolTip("按住并拖动整张卡片即可排序")

    def mousePressEvent(self, event) -> None:
        if event.button() == Qt.MouseButton.LeftButton:
            self.card.request_drag()
            event.accept()
            return
        super().mousePressEvent(event)


class BaseCard(QFrame):
    """所有可排序项目卡的基础外观和 LaTeX 即时预览。"""
    mutation_request_handler = None
    def __init__(self, remove_callback, changed_callback, parent=None):
        super().__init__(parent)
        self.remove_callback = remove_callback
        self.changed_callback = changed_callback
        self.setObjectName("noteItem")
        self.setSizePolicy(QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Preferred)
        self.layout_box = QVBoxLayout(self)
        self.layout_box.setContentsMargins(12, 10, 12, 11)
        self.layout_box.setSpacing(7)
        self._drag_handler = None

    def add_remove_row(self, _label: str = "") -> QHBoxLayout:
        row = QHBoxLayout()
        grip = DragGrip(self)
        row.addWidget(grip)
        # 保留紧凑卡片原有的插入位置（字段会插到第 2 个位置），但不显示旧标题。
        hidden_caption_slot = QWidget()
        hidden_caption_slot.setFixedSize(0, 0)
        row.addWidget(hidden_caption_slot)
        row.addStretch()
        remove = QPushButton("删除")
        remove.setObjectName("removeAction")
        remove.setSizePolicy(QSizePolicy.Policy.Fixed, QSizePolicy.Policy.Fixed)
        remove.clicked.connect(self.request_remove)
        row.addWidget(remove)
        self.layout_box.addLayout(row)
        return row

    def track(self, widget) -> None:
        signal = widget.textChanged
        signal.connect(self.changed)

    def set_drag_handler(self, handler) -> None:
        self._drag_handler = handler

    def request_drag(self) -> None:
        guard = type(self).mutation_request_handler
        if callable(guard) and not guard():
            return
        if self._drag_handler:
            self._drag_handler()

    def request_remove(self) -> None:
        guard = type(self).mutation_request_handler
        if not callable(guard) or guard():
            self.remove_callback()

    def changed(self, *_args) -> None:
        self.changed_callback()

    def preview_text(self) -> str:
        return ""

    def is_empty(self) -> bool:
        return False

    def data(self) -> dict:
        return {}


class TitleContentCard(BaseCard):
    def __init__(self, item: dict, remove_callback, changed_callback, parent=None):
        super().__init__(remove_callback, changed_callback, parent)
        self.add_remove_row("拖动排序")
        self.title = FormulaTextEdit(single_line=True)
        self.title.setPlainText(str(item.get("title", "")))
        self.title.setPlaceholderText("标题（支持 LaTeX）")
        self.content = FormulaTextEdit()
        self.content.setPlainText(str(item.get("content", "")))
        self.content.setPlaceholderText("内容（支持 $...$ 公式）")
        self.content.setMinimumHeight(72)
        self.layout_box.addWidget(self.title)
        self.layout_box.addWidget(self.content)
        self.track(self.title)
        self.track(self.content)

    def preview_text(self) -> str:
        return "\n".join(part for part in [self.title.toPlainText().strip(), self.content.toPlainText().strip()] if part)

    def is_empty(self) -> bool:
        return not self.title.toPlainText().strip() and not self.content.toPlainText().strip()

    def data(self) -> dict:
        return {"title": self.title.toPlainText().strip(), "content": self.content.toPlainText().strip()}


def configure_compact_cell(field: FormulaTextEdit, minimum_width: int) -> None:
    """让紧凑列表的每一列既有可读下限，也能从 WebEngine 的首选宽度收缩。"""
    field.setMinimumWidth(minimum_width)
    field.setSizePolicy(QSizePolicy.Policy.Ignored, QSizePolicy.Policy.Fixed)
    field.view.setMinimumWidth(0)
    field.view.setSizePolicy(QSizePolicy.Policy.Ignored, QSizePolicy.Policy.Fixed)
    field.edit_holder.setMinimumWidth(0)
    field.editor.setMinimumWidth(0)
    field.editor.setSizePolicy(QSizePolicy.Policy.Ignored, QSizePolicy.Policy.Fixed)


class CompactKnowledgeCard(BaseCard):
    """知识点主界面的紧凑行：完整内容交给栏目级“查看全部”。"""
    def __init__(self, item: dict, remove_callback, changed_callback, parent=None):
        super().__init__(remove_callback, changed_callback, parent)
        row = self.add_remove_row("拖动排序")
        self.title = FormulaTextEdit(single_line=True)
        self.title.setPlainText(str(item.get("title", "")))
        self.title.setPlaceholderText("知识点标题")
        self.content = FormulaTextEdit(single_line=True)
        self.content.setPlainText(str(item.get("content", "")))
        self.content.setPlaceholderText("知识点内容")
        configure_compact_cell(self.title, 180)
        configure_compact_cell(self.content, 240)
        row.insertWidget(2, self.title, 2)
        row.insertWidget(3, self.content, 4)
        self.track(self.title)
        self.track(self.content)

    def is_empty(self) -> bool:
        return not self.title.toPlainText().strip() and not self.content.toPlainText().strip()

    def data(self) -> dict:
        return {"title": self.title.toPlainText().strip(), "content": self.content.toPlainText().strip()}


class PatternCard(BaseCard):
    def __init__(self, item: dict, remove_callback, changed_callback, parent=None):
        super().__init__(remove_callback, changed_callback, parent)
        self.add_remove_row("题型卡 · 拖动排序")
        self.title = FormulaTextEdit(single_line=True)
        self.title.setPlainText(str(item.get("title", "")))
        self.title.setPlaceholderText("题型名称（支持 LaTeX）")
        self.example = FormulaTextEdit()
        self.example.setPlainText(str(item.get("example", "")))
        self.example.setPlaceholderText("示例（可写题目、条件或代表式）")
        self.example.setMinimumHeight(62)
        self.note = FormulaTextEdit()
        self.note.setPlainText(str(item.get("note", "")))
        self.note.setPlaceholderText("备注：识别信号、通法、变式或提醒")
        self.note.setMinimumHeight(62)
        self.layout_box.addWidget(self.title)
        self.layout_box.addWidget(field_label("示例"))
        self.layout_box.addWidget(self.example)
        self.layout_box.addWidget(field_label("备注"))
        self.layout_box.addWidget(self.note)
        for widget in (self.title, self.example, self.note):
            self.track(widget)

    def preview_text(self) -> str:
        return "\n".join(part for part in [self.title.toPlainText().strip(), self.example.toPlainText().strip(), self.note.toPlainText().strip()] if part)

    def is_empty(self) -> bool:
        return not any((self.title.toPlainText().strip(), self.example.toPlainText().strip(), self.note.toPlainText().strip()))

    def data(self) -> dict:
        return {"title": self.title.toPlainText().strip(), "example": self.example.toPlainText().strip(), "note": self.note.toPlainText().strip()}


class CompactPatternCard(BaseCard):
    """题型主界面的紧凑行：题型、示例、备注三列并排。"""
    def __init__(self, item: dict, remove_callback, changed_callback, parent=None):
        super().__init__(remove_callback, changed_callback, parent)
        row = self.add_remove_row("拖动排序")
        self.title = FormulaTextEdit(single_line=True)
        self.title.setPlainText(str(item.get("title", "")))
        self.title.setPlaceholderText("题型")
        self.example = FormulaTextEdit(single_line=True)
        self.example.setPlainText(str(item.get("example", "")))
        self.example.setPlaceholderText("示例")
        self.note = FormulaTextEdit(single_line=True)
        self.note.setPlainText(str(item.get("note", "")))
        self.note.setPlaceholderText("备注")
        configure_compact_cell(self.title, 150)
        configure_compact_cell(self.example, 170)
        configure_compact_cell(self.note, 170)
        row.insertWidget(2, self.title, 2)
        row.insertWidget(3, self.example, 3)
        row.insertWidget(4, self.note, 3)
        self.track(self.title)
        self.track(self.example)
        self.track(self.note)

    def is_empty(self) -> bool:
        return not any((self.title.toPlainText().strip(), self.example.toPlainText().strip(), self.note.toPlainText().strip()))

    def data(self) -> dict:
        return {"title": self.title.toPlainText().strip(), "example": self.example.toPlainText().strip(), "note": self.note.toPlainText().strip()}


class ExampleCard(BaseCard):
    def __init__(self, item: dict, remove_callback, changed_callback, parent=None):
        super().__init__(remove_callback, changed_callback, parent)
        self.add_remove_row("例题卡 · 拖动排序")
        self.title = FormulaTextEdit(single_line=True)
        self.title.setPlainText(str(item.get("title", "")))
        self.title.setPlaceholderText("例题标题（支持 LaTeX）")
        self.source = FormulaTextEdit(single_line=True)
        self.source.setPlainText(str(item.get("source", "")))
        self.source.setPlaceholderText("来源（教材页码、试卷或资料；支持 LaTeX）")
        self.problem = FormulaTextEdit()
        self.problem.setPlainText(str(item.get("problem", "")))
        self.problem.setPlaceholderText("原题（支持 $...$ 公式）")
        self.problem.setMinimumHeight(104)
        self.note = FormulaTextEdit()
        self.note.setPlainText(str(item.get("note", "")))
        self.note.setPlaceholderText("备注：关键处理、为何保留或课堂使用提示")
        self.note.setMinimumHeight(66)
        self.layout_box.addWidget(self.title)
        self.layout_box.addWidget(self.source)
        self.layout_box.addWidget(field_label("原题"))
        self.layout_box.addWidget(self.problem)
        self.layout_box.addWidget(field_label("备注"))
        self.layout_box.addWidget(self.note)
        for widget in (self.title, self.source, self.problem, self.note):
            self.track(widget)

    def preview_text(self) -> str:
        return "\n".join(part for part in [self.title.toPlainText().strip(), self.source.toPlainText().strip(), self.problem.toPlainText().strip(), self.note.toPlainText().strip()] if part)

    def is_empty(self) -> bool:
        return not any((self.title.toPlainText().strip(), self.source.toPlainText().strip(), self.problem.toPlainText().strip(), self.note.toPlainText().strip()))

    def data(self) -> dict:
        return {"title": self.title.toPlainText().strip(), "source": self.source.toPlainText().strip(), "problem": self.problem.toPlainText().strip(), "note": self.note.toPlainText().strip()}


class ReorderTag(QLabel):
    """编号本身就是拖拽抓手，不为排序另占一行。"""
    def __init__(self, card, parent=None):
        super().__init__(parent)
        self.card = card
        self.setObjectName("followupTag")
        self.setCursor(Qt.CursorShape.OpenHandCursor)
        self.setToolTip("拖动调整追问顺序")

    def mousePressEvent(self, event) -> None:  # type: ignore[override]
        if event.button() == Qt.MouseButton.LeftButton:
            self.card.request_drag()
            event.accept()
            return
        super().mousePressEvent(event)


class FollowupCard(BaseCard):
    def __init__(self, item: dict, remove_callback, changed_callback, parent=None):
        super().__init__(remove_callback, changed_callback, parent)
        self.setObjectName("followupItem")
        self.layout_box.setContentsMargins(8, 4, 8, 4)
        self.layout_box.setSpacing(0)
        row = QHBoxLayout()
        row.setContentsMargins(0, 0, 0, 0)
        row.setSpacing(8)
        self.tag = ReorderTag(self)
        self.tag.setMinimumWidth(58)
        row.addWidget(self.tag)
        self.text = FormulaTextEdit(single_line=True)
        self.text.setPlainText(str(item.get("text", "")))
        self.text.setPlaceholderText("追问")
        configure_compact_cell(self.text, 160)
        row.addWidget(self.text, 1)
        remove = QPushButton("删除")
        remove.setObjectName("removeAction")
        remove.setSizePolicy(QSizePolicy.Policy.Fixed, QSizePolicy.Policy.Fixed)
        remove.clicked.connect(self.request_remove)
        row.addWidget(remove)
        self.layout_box.addLayout(row)
        self.track(self.text)

    def set_position(self, position: int) -> None:
        self.tag.setText(f"【追问{position}】")

    def preview_text(self) -> str:
        return self.text.toPlainText().strip()

    def is_empty(self) -> bool:
        return not self.text.toPlainText().strip()

    def data(self) -> dict:
        return {"text": self.text.toPlainText().strip()}


class ReorderList(QListWidget):
    """以 QListWidget 的 InternalMove 提供可靠的卡片拖拽排序。"""
    def __init__(self, card_type, on_change, parent=None):
        super().__init__(parent)
        self.card_type = card_type
        self.on_change = on_change
        self._cards: dict[int, BaseCard] = {}
        self.setObjectName("cardList")
        self.setDragDropMode(QAbstractItemView.DragDropMode.InternalMove)
        self.setDefaultDropAction(Qt.DropAction.MoveAction)
        self.setDragEnabled(True)
        self.setAcceptDrops(True)
        self.setDropIndicatorShown(True)
        self.setSelectionMode(QAbstractItemView.SelectionMode.SingleSelection)
        self.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.setSpacing(8)
        self.setSizePolicy(QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Fixed)
        self.model().rowsMoved.connect(self.reordered)

    def add_data(self, data: dict | None = None, notify: bool = True) -> None:
        item = QListWidgetItem()
        card = self.card_type(data or {}, lambda: self.remove_card(item), lambda: self.card_changed(item))
        card.set_drag_handler(lambda: self.start_card_drag(item))
        self._cards[id(item)] = card
        item.setSizeHint(card.sizeHint())
        self.addItem(item)
        self.setItemWidget(item, card)
        self.refresh_height()
        if notify:
            self.on_change()

    def start_card_drag(self, item: QListWidgetItem) -> None:
        if self.row(item) >= 0:
            self.setCurrentItem(item)
            self.startDrag(Qt.DropAction.MoveAction)

    def remove_card(self, item: QListWidgetItem) -> None:
        row = self.row(item)
        if row >= 0:
            self.takeItem(row)
            self._cards.pop(id(item), None)
            self.refresh_height()
            self.on_change()

    def card_changed(self, item: QListWidgetItem) -> None:
        QTimer.singleShot(0, lambda: self.sync_item_size(item))
        self.on_change()

    def sync_item_size(self, item: QListWidgetItem) -> None:
        if self.row(item) < 0:
            return
        card = self.itemWidget(item) or self._cards.get(id(item))
        if card:
            item.setSizeHint(card.sizeHint())
        self.refresh_height()

    def reordered(self, *_args) -> None:
        self.restore_cards()
        self.refresh_height()
        self.on_change()

    def dropEvent(self, event) -> None:
        super().dropEvent(event)
        QTimer.singleShot(0, self.restore_cards)

    def restore_cards(self) -> None:
        """内部移动后重新绑定卡片，避免 Qt 丢失 itemWidget 引用。"""
        for row in range(self.count()):
            item = self.item(row)
            if self.itemWidget(item) is None and id(item) in self._cards:
                self.setItemWidget(item, self._cards[id(item)])

    def set_data(self, entries: list[dict]) -> None:
        self.clear()
        self._cards.clear()
        for entry in entries or []:
            self.add_data(entry, notify=False)
        self.refresh_height()

    def values(self) -> list[dict]:
        values = []
        for row in range(self.count()):
            item = self.item(row)
            card = self.itemWidget(item) or self._cards.get(id(item))
            if card and not card.is_empty():
                values.append(card.data())
        return values

    def refresh_height(self) -> None:
        # 先给隐藏状态或初次创建一个保守高度；真正高度随后由已绘制行的位置校准。
        total = self.frameWidth() * 2 + 12
        for row in range(self.count()):
            item = self.item(row)
            card = self.itemWidget(item) or self._cards.get(id(item))
            if card and hasattr(card, "set_position"):
                card.set_position(row + 1)
            card_height = max(item.sizeHint().height(), card.sizeHint().height() if card else 0, card.minimumSizeHint().height() if card else 0)
            item.setSizeHint(item.sizeHint().expandedTo(card.sizeHint() if card else item.sizeHint()))
            total += card_height
        total += max(0, self.count() - 1) * self.spacing()
        self.setFixedHeight(max(2, total))
        QTimer.singleShot(0, self.fit_height_to_rows)

    def fit_height_to_rows(self) -> None:
        """按 QListWidget 实际绘制的最后一行校准高度，避免多项时出现微小内滚动。"""
        if not self.isVisible() or not self.count():
            return
        self.verticalScrollBar().setValue(0)
        last_rect = self.visualItemRect(self.item(self.count() - 1))
        if not last_rect.isValid():
            return
        # rect 坐标相对 viewport；再加框线和少量下沿余量，确保最后一行完整露出。
        target_height = last_rect.bottom() + 1 + self.frameWidth() * 2 + 6
        if self.height() != target_height:
            self.setFixedHeight(max(2, target_height))

    def showEvent(self, event) -> None:  # type: ignore[override]
        super().showEvent(event)
        QTimer.singleShot(0, self.fit_height_to_rows)


class QuestionCard(BaseCard):
    def __init__(self, item: dict, remove_callback, changed_callback, parent=None):
        super().__init__(remove_callback, changed_callback, parent)
        self.setObjectName("questionItem")
        self.layout_box.setContentsMargins(8, 5, 8, 5)
        self.layout_box.setSpacing(4)
        question_row = QHBoxLayout()
        question_row.setContentsMargins(0, 0, 0, 0)
        question_row.setSpacing(8)
        self.tag = ReorderTag(self)
        self.tag.setMinimumWidth(58)
        question_row.addWidget(self.tag)
        self.question = FormulaTextEdit(single_line=True)
        self.question.setPlainText(str(item.get("question", "")))
        self.question.setPlaceholderText("问题")
        configure_compact_cell(self.question, 220)
        question_row.addWidget(self.question, 1)
        remove = QPushButton("删除")
        remove.setObjectName("removeAction")
        remove.setSizePolicy(QSizePolicy.Policy.Fixed, QSizePolicy.Policy.Fixed)
        remove.clicked.connect(self.request_remove)
        question_row.addWidget(remove)
        add = QPushButton("＋ 添加追问")
        add.setObjectName("smallAction")
        add.clicked.connect(self.add_followup)
        question_row.addWidget(add)
        self.layout_box.addLayout(question_row)
        self.followups = ReorderList(FollowupCard, self.changed)
        self.followups.setObjectName("followupList")
        self.followups.setSpacing(4)
        followup_holder = QWidget()
        followup_layout = QVBoxLayout(followup_holder)
        followup_layout.setContentsMargins(22, 0, 0, 0)
        followup_layout.setSpacing(0)
        followup_layout.addWidget(self.followups)
        self.layout_box.addWidget(followup_holder)
        self.track(self.question)
        self.followups.set_data(item.get("followups", []))

    def add_followup(self) -> None:
        guard = BaseCard.mutation_request_handler
        if callable(guard) and not guard():
            return
        self.followups.add_data()
        self.changed()

    def preview_text(self) -> str:
        parts = [self.question.toPlainText().strip()]
        parts.extend(entry.get("text", "") for entry in self.followups.values())
        return "\n".join(part for part in parts if part)

    def is_empty(self) -> bool:
        return not self.question.toPlainText().strip() and not self.followups.values()

    def data(self) -> dict:
        return {"question": self.question.toPlainText().strip(), "followups": self.followups.values()}

    def set_position(self, position: int) -> None:
        self.tag.setText(f"【问题{position}】")


def field_label(text: str) -> QLabel:
    label = QLabel(text)
    label.setObjectName("fieldLabel")
    return label


class NotebookSection(QFrame):
    mutation_request_handler = None
    def __init__(self, key: str, card_type, on_change, parent=None):
        super().__init__(parent)
        self.key = key
        self.on_change = on_change
        self.setObjectName("notebookSection")
        # 折叠区只按内容高度占位；滚动页剩余高度交给末尾弹簧，不能把空栏目拉厚。
        self.setSizePolicy(QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Maximum)
        title, hint = SECTION_META[key]
        layout = QVBoxLayout(self)
        layout.setContentsMargins(14, 11, 14, 13)
        layout.setSpacing(8)
        heading = QHBoxLayout()
        self.toggle = QPushButton(f"▾  {title}")
        self.toggle.setObjectName("sectionToggle")
        self.toggle.setCheckable(True)
        self.toggle.setChecked(True)
        self.toggle.clicked.connect(self.set_expanded)
        heading.addWidget(self.toggle)
        heading.addStretch()
        self.view_all = QPushButton("查看全部")
        self.view_all.setObjectName("smallAction")
        self.view_all.clicked.connect(self.open_full_view)
        heading.addWidget(self.view_all)
        self.add = QPushButton("＋ 添加项目")
        self.add.setObjectName("smallAction")
        self.add.clicked.connect(self.add_item)
        heading.addWidget(self.add)
        layout.addLayout(heading)
        self.body = QWidget()
        body_layout = QVBoxLayout(self.body)
        body_layout.setContentsMargins(0, 0, 0, 0)
        body_layout.setSpacing(8)
        if hint:
            description = QLabel(hint)
            description.setObjectName("sectionHint")
            description.setWordWrap(True)
            body_layout.addWidget(description)
        self.entries = ReorderList(card_type, on_change)
        body_layout.addWidget(self.entries)
        layout.addWidget(self.body)

    def set_expanded(self, expanded: bool) -> None:
        self.body.setVisible(expanded)
        title = SECTION_META[self.key][0]
        self.toggle.setText(f"{'▾' if expanded else '▸'}  {title}")

    def add_item(self) -> None:
        guard = type(self).mutation_request_handler
        if not callable(guard) or guard():
            self.entries.add_data()

    def set_data(self, entries: list[dict]) -> None:
        self.entries.set_data(entries)

    def values(self) -> list[dict]:
        return self.entries.values()

    def open_full_view(self) -> None:
        """紧凑列表只作快速浏览；完整的多行内容在独立窗口中阅读。"""
        dialog = QDialog(self)
        dialog.setWindowTitle(f"{SECTION_META[self.key][0]} · 完整查看")
        dialog.setMinimumSize(620, 420)
        dialog.resize(840, 680)
        layout = QVBoxLayout(dialog)
        layout.setContentsMargins(0, 0, 0, 10)
        preview = QWebEngineView(dialog)
        page = QWebEnginePage(preview)
        page.setBackgroundColor(QColor("#18232e"))
        preview.setPage(page)
        preview.settings().setAttribute(QWebEngineSettings.WebAttribute.LocalContentCanAccessFileUrls, True)
        preview.setHtml(render_list_detail_document(self.key, self.values()), katex_base_url())
        layout.addWidget(preview)
        actions = QHBoxLayout()
        actions.addStretch()
        close = QPushButton("关闭")
        close.setObjectName("smallAction")
        close.clicked.connect(dialog.accept)
        actions.addWidget(close)
        layout.addLayout(actions)
        dialog.exec()


class FixedTextSection(QFrame):
    def __init__(self, title: str, placeholder: str, on_change, parent=None):
        super().__init__(parent)
        self.setObjectName("notebookSection")
        self.setSizePolicy(QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Maximum)
        layout = QVBoxLayout(self)
        layout.setContentsMargins(14, 11, 14, 13)
        layout.setSpacing(8)
        layout.addWidget(section_heading(title))
        self.editor = FormulaTextEdit()
        self.editor.setPlaceholderText(placeholder)
        self.editor.setMinimumHeight(74)
        self.editor.textChanged.connect(on_change)
        layout.addWidget(self.editor)

    def set_text(self, text: str) -> None:
        self.editor.setPlainText(text)

    def text(self) -> str:
        return self.editor.toPlainText().strip()


def section_heading(text: str) -> QLabel:
    label = QLabel(text)
    label.setObjectName("sectionLabel")
    return label


class LessonNotebook(QWidget):
    open_pdf_requested = Signal()

    def __init__(self, on_change):
        super().__init__()
        self.on_change = on_change
        self.scroll_area: QScrollArea | None = None
        self.sections = {
            "knowledge": NotebookSection("knowledge", CompactKnowledgeCard, on_change),
            "patterns": NotebookSection("patterns", CompactPatternCard, on_change),
            "examples": NotebookSection("examples", ExampleCard, on_change),
            "questions": NotebookSection("questions", QuestionCard, on_change),
            "pitfalls": NotebookSection("pitfalls", TitleContentCard, on_change),
        }
        layout = QVBoxLayout(self)
        layout.setContentsMargins(0, 0, 0, 18)
        layout.setSpacing(12)
        self.title = QLabel("请选择左侧教材小节")
        self.title.setObjectName("lessonTitle")
        self.meta = QLabel("")
        self.meta.setObjectName("meta")
        meta_row = QHBoxLayout()
        meta_row.setContentsMargins(0, 0, 0, 0)
        meta_row.addWidget(self.meta, 1)
        self.open_pdf_button = QPushButton("教材")
        self.open_pdf_button.setObjectName("smallAction")
        self.open_pdf_button.setToolTip("在右侧阅读器定位当前教材内容")
        self.open_pdf_button.clicked.connect(self.open_pdf_requested.emit)
        self.open_pdf_button.setEnabled(False)
        meta_row.addWidget(self.open_pdf_button)
        self.anchor_bar = QFrame()
        self.anchor_bar.setObjectName("anchorBar")
        anchor_layout = QHBoxLayout(self.anchor_bar)
        anchor_layout.setContentsMargins(4, 2, 4, 0)
        anchor_layout.setSpacing(0)
        self.anchors: dict[str, QPushButton] = {}
        anchors = [("intro", "引言"), ("knowledge", "知识点"), ("patterns", "题型"), ("examples", "例题"), ("questions", "问题串"), ("pitfalls", "易错"), ("lesson", "课后备注")]
        for key, text in anchors:
            button = QPushButton(text)
            button.setObjectName("anchorButton")
            button.setCheckable(True)
            button.clicked.connect(lambda _checked=False, section=key: self.open_section(section))
            self.anchors[key] = button
            anchor_layout.addWidget(button)
        anchor_layout.addStretch()
        source_box = QFrame()
        source_box.setObjectName("sourceIntro")
        source_box.setSizePolicy(QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Maximum)
        source_layout = QVBoxLayout(source_box)
        source_layout.setContentsMargins(14, 11, 14, 12)
        source_layout.addWidget(section_heading("教材引言"))
        self.intro_source = SourceImagePreview()
        source_layout.addWidget(self.intro_source)
        layout.addWidget(source_box)
        self.intro_note = FixedTextSection("引入备注", "补充自己的引入思路、情境或过渡（支持 $...$ 公式）", on_change)
        layout.addWidget(self.intro_note)
        for section in self.sections.values():
            layout.addWidget(section)
        self.lesson_note = FixedTextSection("课后备注", "记录本节课堂调整点或待补材料（支持 $...$ 公式）", on_change)
        layout.addWidget(self.lesson_note)
        # 页面被滚动容器拉高时，把剩余空间留在最底部，不能均摊进每个空分区。
        layout.addStretch(1)

    def attach_scroll_area(self, scroll_area: QScrollArea) -> None:
        self.scroll_area = scroll_area

    def open_section(self, key: str) -> None:
        for section_key, section in self.sections.items():
            section.set_expanded(section_key == key)
            section.toggle.setChecked(section_key == key)
        for anchor_key, button in self.anchors.items():
            button.setChecked(anchor_key == key)
        target = self.intro_note if key == "intro" else self.lesson_note if key == "lesson" else self.sections[key]
        if self.scroll_area:
            QTimer.singleShot(0, lambda: self.scroll_area.ensureWidgetVisible(target, 0, 10))

    def set_lesson(self, lesson: dict, note: dict) -> None:
        self.title.setText(f"{lesson['section_no']}  {lesson['section_title']}")
        reference = lesson.get("pdf_reference", {})
        page_text = f"第 {reference.get('start', '—')}–{reference.get('end', '—')} 页"
        self.meta.setText(f"{lesson['edition']}  /  {clean_name(lesson['file'])}  /  {lesson['chapter']}    ·    {page_text}")
        self.open_pdf_button.setEnabled(bool(reference.get("path") and Path(reference["path"]).exists()))
        # 资料包中的引言 PNG 用作离线兜底；本机 PDF 可用时按同一裁剪区域高清重绘。
        pdf_path = Path(reference.get("path", ""))
        intro_page = int(lesson.get("corrected_pdf_page") or reference.get("start") or lesson.get("pdf_page") or 1)
        page_image = resolve_source_image(lesson.get("image_path"))
        intro_image = resolve_source_image(lesson.get("intro_image_path"))
        crop_rect = source_intro_crop_rect(str(page_image), str(intro_image)) if page_image and intro_image else None
        if not (crop_rect and pdf_path.exists() and self.intro_source.set_pdf_page(pdf_path, intro_page, crop_rect)):
            self.intro_source.set_source(intro_image)
        normalized = normalize_note(note)
        self.intro_note.set_text(normalized["intro_note"])
        for key, section in self.sections.items():
            section.set_data(normalized[key])
        self.lesson_note.set_text(normalized["lesson_note"])
        # 初次进入小节从顶部开始阅读；只展开知识点，不复用会滚动定位的锚点动作。
        for key, section in self.sections.items():
            expanded = key == "knowledge"
            section.set_expanded(expanded)
            section.toggle.setChecked(expanded)
        for key, button in self.anchors.items():
            button.setChecked(key == "knowledge")
        if self.scroll_area:
            QTimer.singleShot(0, lambda: self.scroll_area.verticalScrollBar().setValue(0))

    def note(self) -> dict:
        return {
            "intro_note": self.intro_note.text(),
            "knowledge": self.sections["knowledge"].values(),
            "patterns": self.sections["patterns"].values(),
            "examples": self.sections["examples"].values(),
            "questions": self.sections["questions"].values(),
            "pitfalls": self.sections["pitfalls"].values(),
            "lesson_note": self.lesson_note.text(),
        }


class ChapterNotebook(QWidget):
    """章页与“章节总复习”共享的轻量编辑器。"""
    intro_page_correction_requested = Signal()
    def __init__(self, on_change):
        super().__init__()
        self.on_change = on_change
        layout = QVBoxLayout(self)
        layout.setContentsMargins(0, 0, 0, 18)
        layout.setSpacing(12)
        self.title = QLabel()
        self.title.setObjectName("lessonTitle")
        layout.addWidget(self.title)
        self.chapter_intro = QFrame()
        self.chapter_intro.setObjectName("sourceIntro")
        self.chapter_intro.setSizePolicy(QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Maximum)
        intro_layout = QVBoxLayout(self.chapter_intro)
        intro_layout.setContentsMargins(14, 11, 14, 12)
        intro_heading = QHBoxLayout()
        intro_heading.addWidget(section_heading("章引言"))
        intro_heading.addStretch()
        correct_intro = QPushButton("修正页码")
        correct_intro.setObjectName("smallAction")
        correct_intro.setToolTip("手动选择这一章真正的引言页")
        correct_intro.clicked.connect(self.intro_page_correction_requested.emit)
        intro_heading.addWidget(correct_intro)
        intro_layout.addLayout(intro_heading)
        self.intro = SourceImagePreview()
        intro_layout.addWidget(self.intro)
        layout.addWidget(self.chapter_intro)
        self.chapter_note = FixedTextSection("本章总备注", "", on_change)
        layout.addWidget(self.chapter_note)
        self.review = QFrame()
        self.review.setObjectName("notebookSection")
        self.review.setSizePolicy(QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Maximum)
        review_layout = QVBoxLayout(self.review)
        review_layout.setContentsMargins(14, 11, 14, 13)
        review_layout.setSpacing(8)
        review_layout.addWidget(section_heading("章节总复习"))
        review_layout.addWidget(field_label("知识结构图"))
        self.map = FormulaTextEdit()
        self.map.setMinimumHeight(60)
        self.map.textChanged.connect(on_change)
        review_layout.addWidget(self.map)
        heading = QHBoxLayout()
        heading.addWidget(field_label("有价值的复习题"))
        heading.addStretch()
        add = QPushButton("＋ 添加复习题")
        add.setObjectName("smallAction")
        add.clicked.connect(self.add_example)
        heading.addWidget(add)
        review_layout.addLayout(heading)
        self.examples = ReorderList(ExampleCard, on_change)
        review_layout.addWidget(self.examples)
        self.review_note = FixedTextSection("复习备注", "", on_change)
        review_layout.addWidget(self.review_note)
        layout.addWidget(self.review)
        layout.addStretch(1)

    def add_example(self) -> None:
        guard = BaseCard.mutation_request_handler
        if not callable(guard) or guard():
            self.examples.add_data()

    def set_chapter(self, chapter: dict, data: dict, review_mode: bool = False) -> None:
        self.title.setText(f"{chapter['chapter']} · {'章节总复习' if review_mode else '章引言'}")
        self.chapter_intro.setVisible(not review_mode)
        self.chapter_note.setVisible(not review_mode)
        self.review.setVisible(review_mode)
        if not review_mode:
            reference = chapter.get("pdf_reference", {})
            self.intro_page = int(data.get("intro_page") or chapter.get("chapter_intro_page", 0) or 0)
            # 章引言固定为本章第一节起始页的前一页。
            if not self.intro.set_pdf_page(reference.get("path"), self.intro_page):
                self.intro.set_source(resolve_source_image(chapter.get("image_path") or chapter.get("intro_image_path")))
            self.chapter_note.set_text(str(data.get("note", "")))
        else:
            review = data.get("review", {}) if isinstance(data.get("review", {}), dict) else {}
            self.map.setPlainText(str(review.get("map", "")))
            self.examples.set_data(review.get("examples", []))
            self.review_note.set_text(str(review.get("note", "")))

    def chapter_data(self) -> dict:
        data = {"note": self.chapter_note.text()}
        if getattr(self, "intro_page", 0):
            data["intro_page"] = self.intro_page
        return data

    def review_data(self) -> dict:
        return {"map": self.map.toPlainText().strip(), "examples": self.examples.values(), "note": self.review_note.text()}


class SidebarTree(QTreeWidget):
    """自绘浅色展开箭头，避免深色目录沿用系统黑色分支图标。"""
    def drawBranches(self, painter: QPainter, rect: QRect, index: QModelIndex) -> None:  # type: ignore[override]
        if not self.model().hasChildren(index):
            return
        painter.save()
        painter.setRenderHint(QPainter.RenderHint.Antialiasing)
        painter.setPen(QPen(QColor("#a9c4d8"), 2, Qt.PenStyle.SolidLine, Qt.PenCapStyle.RoundCap, Qt.PenJoinStyle.RoundJoin))
        x = rect.left() + max(8, rect.width() // 2)
        y = rect.center().y()
        if self.isExpanded(index):
            painter.drawLine(x - 4, y - 2, x, y + 2)
            painter.drawLine(x, y + 2, x + 4, y - 2)
        else:
            painter.drawLine(x - 2, y - 4, x + 2, y)
            painter.drawLine(x + 2, y, x - 2, y + 4)
        painter.restore()


class SidebarComboBox(QComboBox):
    """深色侧栏中的筛选框使用浅色自绘箭头。"""
    def paintEvent(self, event) -> None:  # type: ignore[override]
        super().paintEvent(event)
        painter = QPainter(self)
        painter.setRenderHint(QPainter.RenderHint.Antialiasing)
        painter.setPen(QPen(QColor("#c3d5e2"), 2, Qt.PenStyle.SolidLine, Qt.PenCapStyle.RoundCap, Qt.PenJoinStyle.RoundJoin))
        x, y = self.width() - 17, self.height() // 2 - 2
        painter.drawLine(x - 5, y, x, y + 5)
        painter.drawLine(x, y + 5, x + 5, y)
        painter.end()


class MainWindow(QMainWindow):
    def __init__(self):
        super().__init__()
        self.setWindowTitle(APP_TITLE)
        self.resize(1360, 880)
        self.setMinimumSize(960, 640)
        self.storage = NotebookStorage()
        set_active_storage(self.storage)
        for edition, default_root in tuple(PDF_ROOTS.items()):
            configured_root = str(self.storage.settings.value(f"pdf_roots/{edition}", "") or "").strip()
            if configured_root:
                PDF_ROOTS[edition] = Path(configured_root).expanduser()
        self.notes_revision = 0
        self.notes_fingerprint = ""
        self.held_lock_id: str | None = None
        self.external_change_pending = False
        self.handled_conflict_files: set[str] = set()
        self.sync_watcher = QFileSystemWatcher(self)
        self.sync_reload_timer = QTimer(self)
        self.sync_reload_timer.setSingleShot(True)
        self.sync_reload_timer.setInterval(900)
        self.sync_reload_timer.timeout.connect(self.reload_from_sync)
        self.sync_watcher.fileChanged.connect(self.on_sync_path_changed)
        self.sync_watcher.directoryChanged.connect(self.on_sync_path_changed)
        self.lock_timer = QTimer(self)
        self.lock_timer.setInterval(45000)
        self.lock_timer.timeout.connect(self.refresh_current_lock)
        self.source_root = find_source_root()
        self.pdf_index = PdfReferenceIndex()
        self.lessons = self.load_catalog()
        self.chapter_notes: dict[str, dict] = {}
        self.section_notes: dict[str, dict] = {}
        self.custom_subsections: dict[str, list[dict]] = {}
        self.notes = self.load_notes()
        self.current_id: str | None = None
        self.current_lesson: dict | None = None
        self.current_node_type = "lesson"
        self.current_chapter: dict | None = None
        self.pending_screenshot_field: FormulaTextEdit | None = None
        self.pending_screenshot_context: dict | None = None
        self.loading = False
        self.build_ui()
        FormulaTextEdit.screenshot_request_handler = self.capture_textbook_screenshot
        FormulaTextEdit.screenshot_open_handler = self.open_screenshot_source
        FormulaTextEdit.image_request_handler = self.import_local_image
        FormulaTextEdit.edit_request_handler = self.ensure_edit_lock
        BaseCard.mutation_request_handler = self.ensure_edit_lock
        NotebookSection.mutation_request_handler = self.ensure_edit_lock
        self.configure_sync_watcher()
        self.populate_tree()
        self.update_progress()
        self.update_sync_indicator()

    def load_catalog(self) -> list[dict]:
        lessons = []
        for edition, filename in DATA_SOURCES.items():
            path = self.source_root / filename
            if not path.exists():
                continue
            for book in json.loads(path.read_text(encoding="utf-8")):
                chapter_titles = catalog_chapter_titles(book)
                book_entries = []
                for entry in book.get("entries", []):
                    entry = dict(entry)
                    chapter_number = entry["section_no"].split(".")[0]
                    legacy_chapter = entry.get("chapter") or f"第{chapter_number}章"
                    entry.update(
                        edition=edition,
                        file=book["file"],
                        chapter=entry.get("chapter") or chapter_titles.get(chapter_number) or legacy_chapter,
                        legacy_chapter=legacy_chapter,
                    )
                    entry["id"] = f"{edition}|{book['file']}|{entry['section_no']}|{entry['section_title']}"
                    entry["pdf_reference"] = self.pdf_index.reference_for(entry)
                    book_entries.append(entry)
                # 无标准 PDF 书签时，使用目录资料中相邻小节的首页计算完整范围，而非固定猜测页数。
                ordered = sorted(book_entries, key=lambda item: int(item.get("corrected_pdf_page") or item.get("pdf_page") or 1))
                page_count, _ = self.pdf_index._outline_for(self.pdf_index.pdf_path_for(ordered[0])) if ordered else (0, [])
                for index, entry in enumerate(ordered):
                    reference = entry["pdf_reference"]
                    if reference.get("source") != "bookmark":
                        next_start = int(ordered[index + 1].get("corrected_pdf_page") or ordered[index + 1].get("pdf_page") or reference["start"]) if index + 1 < len(ordered) else page_count
                        reference["end"] = max(reference["start"], next_start - 1 if index + 1 < len(ordered) else next_start)
                lessons.extend(book_entries)
        return lessons

    def migrate_chapter_note_keys(self) -> None:
        """章名由“第 N 章”补全后，保留旧章引言和章节总复习的数据。"""
        migrations: dict[str, str] = {}
        for lesson in self.lessons:
            chapter = lesson.get("chapter", "")
            legacy = lesson.get("legacy_chapter", chapter)
            if chapter == legacy:
                continue
            old_id = f"chapter|{lesson['edition']}|{lesson['file']}|{legacy}"
            new_id = f"chapter|{lesson['edition']}|{lesson['file']}|{chapter}"
            migrations[old_id] = new_id
        for old_id, new_id in migrations.items():
            if old_id in self.chapter_notes and new_id not in self.chapter_notes:
                self.chapter_notes[new_id] = self.chapter_notes.pop(old_id)

    def load_notes(self) -> dict:
        source = data_path() if data_path().exists() else LEGACY_DATA_PATH
        if not source.exists():
            self.notes_revision = 0
            self.notes_fingerprint = ""
            self.chapter_notes = {}
            self.section_notes = {}
            self.custom_subsections = {}
            return {}
        try:
            payload = json.loads(source.read_text(encoding="utf-8"))
            raw = payload.get("notes", {})
            self.notes_revision = int(payload.get("revision", 0) or 0)
            self.chapter_notes = payload.get("chapter_notes", {}) if isinstance(payload.get("chapter_notes", {}), dict) else {}
            self.section_notes = payload.get("section_notes", {}) if isinstance(payload.get("section_notes", {}), dict) else {}
            self.custom_subsections = payload.get("custom_subsections", {}) if isinstance(payload.get("custom_subsections", {}), dict) else {}
        except (OSError, json.JSONDecodeError):
            self.notes_revision = 0
            self.notes_fingerprint = ""
            self.chapter_notes = {}
            self.section_notes = {}
            self.custom_subsections = {}
            return {}
        self.notes_fingerprint = self.storage.fingerprint(source)
        self.migrate_chapter_note_keys()
        return {key: normalize_note(value) for key, value in raw.items()}

    def build_ui(self) -> None:
        bar = self.menuBar()
        file_menu = bar.addMenu("文件")
        file_menu.addAction(QAction("同步设置…", self, triggered=self.configure_sync))
        file_menu.addAction(QAction("导出教材笔记备份…", self, triggered=self.export_notes))
        file_menu.addAction(QAction("导入教材笔记备份…", self, triggered=self.import_notes))
        sync_menu = bar.addMenu("同步")
        sync_menu.addAction(QAction("立即重新载入", self, triggered=lambda: self.reload_from_sync(force=True)))
        sync_menu.addAction(QAction("打开同步文件夹", self, triggered=self.open_sync_folder))
        sync_menu.addAction(QAction("解除过期锁", self, triggered=self.clear_expired_locks))
        tools_menu = bar.addMenu("工具")
        tools_menu.addAction(QAction("用系统工具打开当前教材", self, triggered=self.open_current_pdf))
        tools_menu.addAction(QAction("跨版本定位", self, triggered=self.show_comparison))
        tools_menu.addAction(QAction("导出当前小节笔记…", self, triggered=self.export_current_note))
        help_menu = bar.addMenu("说明")
        help_menu.addAction(QAction("LaTeX 输入说明", self, triggered=self.show_latex_help))

        splitter = QSplitter(Qt.Orientation.Horizontal)
        splitter.setChildrenCollapsible(False)
        splitter.setHandleWidth(8)
        sidebar = self.make_sidebar()
        sidebar.setMinimumWidth(250)
        self.sidebar = sidebar
        self.sidebar_holder = QFrame()
        self.sidebar_holder.setObjectName("sidebarHolder")
        sidebar_holder_layout = QVBoxLayout(self.sidebar_holder)
        sidebar_holder_layout.setContentsMargins(0, 0, 0, 0)
        sidebar_holder_layout.addWidget(sidebar)
        self.sidebar_expand_button = QPushButton("›")
        self.sidebar_expand_button.setObjectName("sidebarRailToggle")
        self.sidebar_expand_button.setToolTip("展开教材目录")
        self.sidebar_expand_button.clicked.connect(lambda: self.set_sidebar_visible(True))
        self.sidebar_expand_button.setVisible(False)
        sidebar_holder_layout.addWidget(self.sidebar_expand_button, 0, Qt.AlignmentFlag.AlignTop | Qt.AlignmentFlag.AlignHCenter)
        splitter.addWidget(self.sidebar_holder)
        splitter.addWidget(self.make_editor_area())
        splitter.setStretchFactor(0, 0)
        splitter.setStretchFactor(1, 1)
        splitter.setSizes([330, 1030])
        splitter.splitterMoved.connect(self.save_workspace_layout)
        self.main_splitter = splitter
        self.setCentralWidget(splitter)
        status = QStatusBar()
        self.status_label = QLabel("就绪")
        status.addWidget(self.status_label)
        self.sync_label = QLabel("本机保存")
        self.sync_label.setObjectName("syncStatus")
        status.addPermanentWidget(self.sync_label)
        self.setStatusBar(status)
        QTimer.singleShot(0, self.restore_workspace_layout)

    def update_sync_indicator(self) -> None:
        if not self.storage.enabled:
            text = "本机保存"
        elif self.external_change_pending:
            text = "同步冲突待处理"
        elif self.held_lock_id:
            text = "正在编辑 · 已锁定"
        else:
            text = "已同步"
        if hasattr(self, "sync_label"):
            self.sync_label.setText(text)

    def make_sidebar(self) -> QWidget:
        panel = QWidget()
        panel.setObjectName("sidebar")
        layout = QVBoxLayout(panel)
        layout.setContentsMargins(16, 18, 16, 16)
        heading_row = QHBoxLayout()
        heading = QLabel("教材目录")
        heading.setObjectName("sidebarTitle")
        heading_row.addWidget(heading)
        heading_row.addStretch()
        self.sidebar_toggle_button = QPushButton("‹")
        self.sidebar_toggle_button.setObjectName("sidebarHeaderToggle")
        self.sidebar_toggle_button.setToolTip("收起教材目录")
        self.sidebar_toggle_button.clicked.connect(self.toggle_sidebar)
        heading_row.addWidget(self.sidebar_toggle_button)
        layout.addLayout(heading_row)
        self.progress = QLabel()
        self.progress.setObjectName("progress")
        layout.addWidget(self.progress)
        self.search = QLineEdit()
        self.search.setPlaceholderText("搜索小节或笔记内容…")
        self.search.textChanged.connect(self.populate_tree)
        layout.addWidget(self.search)
        self.edition = SidebarComboBox()
        self.edition.addItems(["全部教材", "人教A版", "苏教版", "仅已有笔记"])
        self.edition.currentTextChanged.connect(self.populate_tree)
        layout.addWidget(self.edition)
        self.tree = SidebarTree()
        self.tree.setHeaderHidden(True)
        self.tree.itemClicked.connect(self.on_tree_click)
        layout.addWidget(self.tree)
        return panel

    def make_editor_area(self) -> QWidget:
        holder = QWidget()
        holder.setObjectName("workspace")
        layout = QVBoxLayout(holder)
        layout.setContentsMargins(18, 14, 18, 16)
        layout.setSpacing(10)
        self.editor = LessonNotebook(self.save_current)
        self.editor.open_pdf_requested.connect(self.open_current_in_reader)
        self.context_bar = QFrame()
        self.context_bar.setObjectName("contextBar")
        context = QHBoxLayout(self.context_bar)
        context.setContentsMargins(12, 8, 10, 8)
        context.setSpacing(7)
        path_box = QVBoxLayout()
        path_box.setSpacing(1)
        self.context_label = QLabel("请选择左侧教材小节")
        self.context_label.setObjectName("contextPath")
        self.context_detail = QLabel("笔记与教材将在这里联动")
        self.context_detail.setObjectName("contextDetail")
        path_box.addWidget(self.context_label)
        path_box.addWidget(self.context_detail)
        context.addLayout(path_box)
        context.addWidget(self.editor.anchor_bar, 1)
        self.reader_toggle_button = QPushButton("收起教材")
        self.reader_toggle_button.setObjectName("primaryCompact")
        self.reader_toggle_button.clicked.connect(self.toggle_pdf_reader)
        context.addWidget(self.reader_toggle_button)
        layout.addWidget(self.context_bar)

        self.chapter_editor = ChapterNotebook(self.save_current)
        self.chapter_editor.intro_page_correction_requested.connect(self.correct_chapter_intro_page)
        self.editor_stack = QStackedWidget()
        self.editor_stack.setObjectName("editorStack")
        self.editor_stack.addWidget(self.editor)
        self.editor_stack.addWidget(self.chapter_editor)
        self.editor_scroll = QScrollArea()
        self.editor_scroll.setObjectName("editorScroll")
        self.editor_scroll.setWidgetResizable(True)
        self.editor_scroll.setFrameShape(QFrame.Shape.NoFrame)
        self.editor_scroll.setWidget(self.editor_stack)
        self.editor.attach_scroll_area(self.editor_scroll)
        self.pdf_reader = PdfReaderPanel()
        self.pdf_reader.setMinimumWidth(330)
        self.pdf_reader.locate_requested.connect(self.open_current_in_reader)
        self.pdf_reader.capture_confirmed.connect(self.complete_reader_capture)
        self.pdf_reader.capture_cancelled.connect(self.cancel_reader_capture)
        self.content_splitter = QSplitter(Qt.Orientation.Horizontal)
        self.content_splitter.setChildrenCollapsible(False)
        self.content_splitter.setHandleWidth(7)
        self.content_splitter.addWidget(self.editor_scroll)
        self.content_splitter.addWidget(self.pdf_reader)
        self.content_splitter.setStretchFactor(0, 1)
        self.content_splitter.setStretchFactor(1, 0)
        self.content_splitter.setSizes([760, 470])
        self.content_splitter.splitterMoved.connect(self.save_workspace_layout)
        layout.addWidget(self.content_splitter, 1)
        return holder

    def restore_workspace_layout(self) -> None:
        settings = self.storage.settings
        main_sizes = settings.value("ui/main_splitter_sizes", [])
        content_sizes = settings.value("ui/content_splitter_sizes", [])
        if isinstance(main_sizes, list) and len(main_sizes) == 2:
            self.main_splitter.setSizes([int(value) for value in main_sizes])
        if isinstance(content_sizes, list) and len(content_sizes) == 2:
            self.content_splitter.setSizes([int(value) for value in content_sizes])
        visible = str(settings.value("ui/pdf_reader_visible", "true")).lower() not in {"false", "0"}
        self.set_pdf_reader_visible(visible, locate=visible)
        sidebar_visible = str(settings.value("ui/sidebar_visible", "true")).lower() not in {"false", "0"}
        self.set_sidebar_visible(sidebar_visible)

    def save_workspace_layout(self, *_args) -> None:
        if not hasattr(self, "content_splitter"):
            return
        self.storage.settings.setValue("ui/main_splitter_sizes", self.main_splitter.sizes())
        self.storage.settings.setValue("ui/content_splitter_sizes", self.content_splitter.sizes())
        self.storage.settings.setValue("ui/pdf_reader_visible", self.pdf_reader.isVisible())
        self.storage.settings.setValue("ui/sidebar_visible", self.sidebar.isVisible())

    def set_sidebar_visible(self, visible: bool) -> None:
        self.sidebar.setVisible(visible)
        self.sidebar_expand_button.setVisible(not visible)
        if visible:
            self.sidebar_holder.setMinimumWidth(250)
            self.sidebar_holder.setMaximumWidth(16777215)
            if hasattr(self, "_sidebar_last_width"):
                self.main_splitter.setSizes([self._sidebar_last_width, max(1, self.main_splitter.width() - self._sidebar_last_width)])
        else:
            self._sidebar_last_width = max(250, self.main_splitter.sizes()[0])
            self.sidebar_holder.setMinimumWidth(38)
            self.sidebar_holder.setMaximumWidth(38)
            self.main_splitter.setSizes([38, max(1, self.main_splitter.width() - 38)])
        self.storage.settings.setValue("ui/sidebar_visible", visible)

    def toggle_sidebar(self) -> None:
        self.set_sidebar_visible(not self.sidebar.isVisible())

    def set_pdf_reader_visible(self, visible: bool, locate: bool = False) -> None:
        self.pdf_reader.setVisible(visible)
        self.reader_toggle_button.setText("收起教材" if visible else "展开教材")
        self.storage.settings.setValue("ui/pdf_reader_visible", visible)
        if visible and locate:
            self.locate_current_in_reader()

    def toggle_pdf_reader(self) -> None:
        self.set_pdf_reader_visible(not self.pdf_reader.isVisible(), locate=True)

    def current_pdf_target(self) -> tuple[dict, int, str] | None:
        if not self.current_lesson:
            return None
        reference = self.current_lesson.get("pdf_reference", {})
        if not reference:
            return None
        if self.current_node_type == "chapter":
            page = int(self.current_lesson.get("chapter_intro_page") or reference.get("start") or 1)
            detail = f"{self.current_lesson['chapter']} · 章引言"
        elif self.current_node_type == "review":
            matching = [
                entry for entry in self.lessons
                if entry["edition"] == self.current_lesson["edition"]
                and entry["file"] == self.current_lesson["file"]
                and entry["chapter"] == self.current_lesson["chapter"]
            ]
            page = max((int(entry.get("pdf_reference", {}).get("end") or entry.get("pdf_reference", {}).get("start") or 1) for entry in matching), default=int(reference.get("start") or 1))
            detail = f"{self.current_lesson['chapter']} · 章节总复习"
        else:
            page = int(reference.get("start") or 1)
            detail = f"{self.current_lesson['section_no']} {self.current_lesson['section_title']}"
        return reference, page, detail

    def update_context_bar(self) -> None:
        if not self.current_lesson:
            self.context_label.setText("请选择左侧教材小节")
            self.context_detail.setText("笔记与教材将在这里联动")
            return
        if self.current_node_type == "lesson":
            title = f"{self.current_lesson['section_no']}  {self.current_lesson['section_title']}"
        elif self.current_node_type == "review":
            title = f"{self.current_lesson['chapter']} · 章节总复习"
        else:
            title = f"{self.current_lesson['chapter']} · 章引言"
        self.context_label.setText(title)
        self.context_detail.setText(f"{self.current_lesson['edition']} · {clean_name(self.current_lesson['file'])} · {self.current_lesson['chapter']}")

    def locate_current_in_reader(self) -> bool:
        target = self.current_pdf_target()
        if not target:
            self.pdf_reader.set_message("当前页面没有关联教材 PDF")
            return False
        reference, page, detail = target
        path = Path(reference.get("path", ""))
        return self.pdf_reader.open_document(path, page, detail)

    def open_current_in_reader(self) -> None:
        if not self.current_lesson:
            QMessageBox.information(self, "尚未选择教材", "请先从目录中选择一个具体教材小节。")
            return
        if not self.ensure_local_pdf_root():
            return
        self.set_pdf_reader_visible(True)
        if self.locate_current_in_reader():
            self.status_label.setText("已在右侧教材栏定位当前内容")

    def correct_chapter_intro_page(self) -> None:
        if self.current_node_type != "chapter" or not self.current_lesson or not self.current_id:
            return
        chapter = self.current_lesson
        path = self.ensure_pdf_for_metadata({"edition": chapter["edition"], "book": chapter["file"]})
        if path is None or not path.exists():
            QMessageBox.information(self, "找不到教材 PDF", "请先为该版本选择本机教材目录，再修正章引言页。")
            return
        current = self.chapter_notes.get(self.current_id, {})
        initial_page = int(current.get("intro_page") or chapter.get("chapter_intro_page") or 1)
        dialog = ChapterIntroPageDialog(path, initial_page, self)
        if dialog.exec() != QDialog.DialogCode.Accepted or not dialog.selected_page:
            return
        data = dict(current)
        data["intro_page"] = dialog.selected_page
        self.chapter_notes[self.current_id] = data
        self.current_lesson = {**chapter, "pdf_reference": {**chapter.get("pdf_reference", {}), "path": path}}
        self.loading = True
        self.show_current_node()
        self.loading = False
        self.write_notes()
        self.status_label.setText(f"已将章引言修正为教材第 {dialog.selected_page} 页")

    def ensure_pdf_for_metadata(self, metadata: dict) -> Path | None:
        edition = str(metadata.get("edition") or "")
        book = str(metadata.get("book") or "")
        path = PDF_ROOTS.get(edition, Path()) / book
        if path.exists():
            return path
        if not edition or not book:
            return None
        choice = QMessageBox.question(
            self, "需要本机教材目录",
            f"本机未找到 {edition} 的《{clean_name(book)}》。\n是否选择该版本教材所在文件夹？",
            QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No,
            QMessageBox.StandardButton.Yes,
        )
        if choice != QMessageBox.StandardButton.Yes:
            return None
        folder = QFileDialog.getExistingDirectory(self, f"选择 {edition} 教材文件夹", str(PDF_ROOTS.get(edition, Path.home())))
        if not folder:
            return None
        PDF_ROOTS[edition] = Path(folder)
        self.storage.settings.setValue(f"pdf_roots/{edition}", folder)
        self.pdf_index = PdfReferenceIndex()
        return PDF_ROOTS[edition] / book

    def open_screenshot_source(self, screenshot_id: str) -> None:
        metadata_path = SCREENSHOT_DIR / f"{screenshot_id}.json"
        try:
            metadata = json.loads(metadata_path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            QMessageBox.information(self, "没有教材来源", "这张图片没有可用的教材页码信息。")
            return
        path = self.ensure_pdf_for_metadata(metadata)
        page = int(metadata.get("page") or 0)
        if path is None or not path.exists() or page < 1:
            QMessageBox.information(self, "无法定位教材来源", "这张图片不是教材框选截图，或本机尚未配置对应 PDF。")
            return
        self.set_pdf_reader_visible(True)
        title = f"截图来源 · 教材第 {page} 页"
        if self.pdf_reader.open_document(path, page, title, metadata.get("crop_rect")):
            self.status_label.setText(f"已定位截图来源：教材第 {page} 页")

    @staticmethod
    def has_content(note: dict) -> bool:
        normalized = normalize_note(note)
        if normalized["intro_note"] or normalized["lesson_note"]:
            return True
        return any(normalized[key] for key in ("knowledge", "patterns", "examples", "questions", "pitfalls"))

    @staticmethod
    def note_text(note: dict) -> str:
        return json.dumps(normalize_note(note), ensure_ascii=False).lower()

    def configure_sync_watcher(self) -> None:
        """坚果云写入本地目录后会触发这里；QSaveFile 替换文件后需重新登记路径。"""
        paths = self.sync_watcher.files() + self.sync_watcher.directories()
        if paths:
            self.sync_watcher.removePaths(paths)
        if not self.storage.enabled:
            return
        self.storage.ensure_directories()
        self.sync_watcher.addPath(str(self.storage.root))
        if data_path().exists():
            self.sync_watcher.addPath(str(data_path()))

    def on_sync_path_changed(self, _path: str) -> None:
        if self.storage.enabled:
            self.sync_reload_timer.start()

    def copy_screenshots(self, source: Path, target: Path) -> None:
        if not source.exists() or source.resolve() == target.resolve():
            return
        target.mkdir(parents=True, exist_ok=True)
        for item in source.iterdir():
            if item.is_file() and item.suffix in {".png", ".json"}:
                shutil.copy2(item, target / item.name)

    def configure_sync(self) -> None:
        self.save_current()
        folder = QFileDialog.getExistingDirectory(self, "选择坚果云中的同步文件夹", str(self.storage.sync_parent or Path.home()))
        if not folder:
            return
        parent = Path(folder)
        target_root = parent / NotebookStorage.FOLDER_NAME
        source_notes = data_path()
        source_shots = SCREENSHOT_DIR
        target_notes = target_root / "我的教材笔记.json"
        local_payload = self.storage.read_json(source_notes)
        target_payload = self.storage.read_json(target_notes)
        local_has_content = bool(local_payload.get("notes"))
        target_has_content = bool(target_payload.get("notes"))
        use_local = not target_has_content
        if target_has_content and local_has_content and self.storage.fingerprint(source_notes) != self.storage.fingerprint(target_notes):
            decision = QMessageBox(self)
            decision.setWindowTitle("发现两份教材笔记")
            decision.setText("所选坚果云文件夹中已有教材笔记，本机也有不同内容。")
            decision.setInformativeText("请选择首次同步使用哪一份；另一份会保存在同步目录的 backups 中，不会丢失。")
            remote = decision.addButton("使用同步副本", QMessageBox.ButtonRole.AcceptRole)
            local = decision.addButton("使用本机副本", QMessageBox.ButtonRole.DestructiveRole)
            cancel = decision.addButton("取消", QMessageBox.ButtonRole.RejectRole)
            decision.exec()
            if decision.clickedButton() is cancel:
                return
            use_local = decision.clickedButton() is local
            if use_local:
                target_root.mkdir(parents=True, exist_ok=True)
                (target_root / "backups").mkdir(exist_ok=True)
                backup = target_root / "backups" / f"首次同步前_同步副本_{datetime.now():%Y%m%d_%H%M%S}.json"
                NotebookStorage.atomic_write(backup, json.dumps(target_payload, ensure_ascii=False, indent=2).encode("utf-8"))
        if use_local:
            target_root.mkdir(parents=True, exist_ok=True)
            if source_notes.exists():
                NotebookStorage.atomic_write(target_notes, source_notes.read_bytes())
            self.copy_screenshots(source_shots, target_root / "教材截图")
        self.release_current_lock()
        self.storage.configure(parent)
        set_active_storage(self.storage)
        self.notes = self.load_notes()
        self.configure_sync_watcher()
        self.populate_tree()
        self.update_progress()
        if self.current_lesson:
            self.loading = True
            self.show_current_node()
            self.loading = False
        self.status_label.setText(f"已启用同步：{self.storage.root}")
        self.update_sync_indicator()

    def reload_from_sync(self, force: bool = False) -> None:
        if not self.storage.enabled:
            return
        conflict_files = self.detect_sync_conflict_copies()
        current_fingerprint = self.storage.fingerprint(data_path())
        self.configure_sync_watcher()
        if current_fingerprint == self.notes_fingerprint:
            if force:
                self.status_label.setText("发现同步冲突副本，已备份" if conflict_files else "本机已是同步目录中的最新版本")
            return
        if self.held_lock_id:
            self.external_change_pending = True
            remote = self.storage.read_json(data_path())
            if remote:
                self.storage.backup_payload("远端冲突待处理", remote)
            self.status_label.setText("检测到另一台电脑的更新；本节仍由本机编辑，保存时将要求确认。")
            self.update_sync_indicator()
            return
        self.notes = self.load_notes()
        self.loading = True
        if self.current_lesson:
            self.show_current_node()
        self.loading = False
        self.populate_tree()
        self.update_progress()
        self.status_label.setText("已载入另一台电脑的更新")
        self.update_sync_indicator()

    def detect_sync_conflict_copies(self) -> list[Path]:
        """坚果云/系统产生的“冲突副本”绝不参与自动覆盖，先留档供人工判断。"""
        if not self.storage.enabled or not self.storage.root.exists():
            return []
        found = []
        for candidate in self.storage.root.glob("*.json"):
            name = candidate.name.lower()
            if candidate == data_path() or ("冲突" not in candidate.name and "conflict" not in name):
                continue
            key = f"{candidate}:{candidate.stat().st_mtime_ns}"
            if key in self.handled_conflict_files:
                continue
            self.storage.backups_dir.mkdir(parents=True, exist_ok=True)
            target = self.storage.backups_dir / f"同步冲突副本_{datetime.now():%Y%m%d_%H%M%S}_{candidate.name}"
            try:
                shutil.copy2(candidate, target)
                self.handled_conflict_files.add(key)
                found.append(target)
            except OSError:
                continue
        return found

    def ensure_edit_lock(self, *_args) -> bool:
        if not self.current_id:
            QMessageBox.information(self, "尚未选择小节", "请先从左侧选择一个教材小节。")
            return False
        if not self.storage.enabled:
            return True
        if self.held_lock_id == self.current_id:
            return True
        # 开始编辑前总是先读取坚果云已经落地的最新版本。
        if self.storage.fingerprint(data_path()) != self.notes_fingerprint:
            self.reload_from_sync()
        ok, lock = self.storage.acquire_lock(self.current_id)
        if not ok:
            owner = str((lock or {}).get("device_name") or "另一台电脑")
            expires = str((lock or {}).get("expires_at") or "稍后")
            self.status_label.setText(f"{owner} 正在编辑本节")
            QMessageBox.information(self, "本节正在编辑", f"{owner} 正在编辑这一节。\n锁会在对方切换小节、关闭应用或 {expires} 到期后释放。")
            return False
        self.held_lock_id = self.current_id
        self.external_change_pending = False
        self.lock_timer.start()
        self.status_label.setText("正在编辑本节（已同步锁定）")
        self.update_sync_indicator()
        return True

    def refresh_current_lock(self) -> None:
        if self.held_lock_id:
            self.storage.refresh_lock(self.held_lock_id)

    def release_current_lock(self) -> None:
        if self.held_lock_id:
            self.storage.release_lock(self.held_lock_id)
        self.held_lock_id = None
        self.external_change_pending = False
        self.lock_timer.stop()
        self.update_sync_indicator()

    def open_sync_folder(self) -> None:
        if not self.storage.enabled:
            QMessageBox.information(self, "尚未启用同步", "请先在“文件 → 同步设置”中选择坚果云同步文件夹。")
            return
        QDesktopServices.openUrl(QUrl.fromLocalFile(str(self.storage.root)))

    def clear_expired_locks(self) -> None:
        if not self.storage.enabled:
            return
        removed = 0
        self.storage.ensure_directories()
        for path in self.storage.locks_dir.glob("*.json"):
            lock = self.storage.read_json(path)
            try:
                expired = datetime.fromisoformat(str(lock.get("expires_at", ""))) <= datetime.now()
            except ValueError:
                expired = True
            if expired:
                try:
                    path.unlink()
                    removed += 1
                except OSError:
                    pass
        self.status_label.setText(f"已清理 {removed} 个过期编辑锁")

    def resolve_write_conflict(self) -> bool:
        remote = self.storage.read_json(data_path())
        if not remote:
            return True
        backup = self.storage.backup_payload("远端冲突副本", remote)
        choice = QMessageBox.question(
            self, "发现同步冲突",
            f"另一台电脑在本机编辑期间更新了这份笔记。远端版本已备份到：\n{backup.name}\n\n选择“是”用本机内容继续保存；选择“否”载入远端版本。",
            QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No,
            QMessageBox.StandardButton.No,
        )
        if choice == QMessageBox.StandardButton.No:
            self.release_current_lock()
            self.notes = self.load_notes()
            self.loading = True
            self.show_current_node()
            self.loading = False
            self.populate_tree()
            self.update_progress()
            return False
        return True

    def populate_tree(self) -> None:
        if not hasattr(self, "tree"):
            return
        self.tree.clear()
        self.node_index: dict[str, dict] = {}
        selected_edition = self.edition.currentText()
        query = self.search.text().strip().lower()

        def matches(lesson: dict) -> bool:
            note = self.notes.get(lesson["id"], {})
            chapter_id = f"chapter|{lesson['edition']}|{lesson['file']}|{lesson['chapter']}"
            chapter_data = self.chapter_notes.get(chapter_id, {})
            chapter_has_content = bool(chapter_data.get("note") or chapter_data.get("review"))
            if selected_edition in {"人教A版", "苏教版"} and lesson["edition"] != selected_edition:
                return False
            if selected_edition == "仅已有笔记" and not (self.has_content(note) or chapter_has_content):
                return False
            haystack = f"{lesson['section_no']} {lesson['section_title']} {lesson['chapter']} {lesson['file']} {self.note_text(note)} {json.dumps(chapter_data, ensure_ascii=False)}".lower()
            return query in haystack

        groups: dict[tuple[str, str], list[dict]] = defaultdict(list)
        for lesson in filter(matches, self.lessons):
            groups[(lesson["edition"], lesson["file"])].append(lesson)
        for (edition, book), items in groups.items():
            book_item = QTreeWidgetItem([f"{edition} · {clean_name(book)}"])
            book_item.setExpanded(True)
            self.tree.addTopLevelItem(book_item)
            chapters: dict[str, list[dict]] = defaultdict(list)
            for lesson in items:
                chapters[lesson["chapter"]].append(lesson)
            for chapter, entries in chapters.items():
                chapter_item = QTreeWidgetItem([chapter])
                chapter_item.setExpanded(True)
                book_item.addChild(chapter_item)
                first = min(entries, key=lambda entry: tuple(int(part) for part in re.findall(r"\d+", entry["section_no"])))
                chapter_id = f"chapter|{edition}|{book}|{chapter}"
                first_reference = first.get("pdf_reference", {})
                chapter_node = {
                    "id": chapter_id, "node_type": "chapter", "chapter": chapter, "edition": edition, "file": book,
                    "image_path": first.get("image_path"), "intro_image_path": first.get("intro_image_path"),
                    "pdf_reference": first_reference, "chapter_intro_page": max(1, int(first_reference.get("start", 1)) - 1),
                }
                self.node_index[chapter_id] = chapter_node
                chapter_item.setData(0, Qt.ItemDataRole.UserRole, chapter_id)
                # 每一节均直接承载完整笔记；不再拆出三级“小小节”，目录保持清爽。
                for lesson in sorted(entries, key=lambda entry: tuple(int(part) for part in re.findall(r"\d+", entry["section_no"]))):
                    self.node_index[lesson["id"]] = {**lesson, "node_type": "lesson"}
                    prefix = "● " if self.has_content(self.notes.get(lesson["id"], {})) else ""
                    section_item = QTreeWidgetItem([prefix + f"{lesson['section_no']}  {lesson['section_title']}"])
                    section_item.setData(0, Qt.ItemDataRole.UserRole, lesson["id"])
                    if prefix:
                        section_item.setForeground(0, QColor("#63acff"))
                    chapter_item.addChild(section_item)
                # 复习页固定放在本章所有小节之后，便于按教材顺序整理。
                review_id = f"review|{chapter_id}"
                self.node_index[review_id] = {**chapter_node, "id": review_id, "node_type": "review", "chapter_id": chapter_id}
                review = QTreeWidgetItem(["章节总复习"])
                review.setData(0, Qt.ItemDataRole.UserRole, review_id)
                chapter_item.addChild(review)

    def on_tree_click(self, item: QTreeWidgetItem) -> None:
        node_id = item.data(0, Qt.ItemDataRole.UserRole)
        node = getattr(self, "node_index", {}).get(node_id)
        if not node:
            return
        self.save_current()
        self.release_current_lock()
        self.current_id = node_id
        self.current_lesson = node
        self.current_node_type = node.get("node_type", "lesson")
        self.current_chapter = node if self.current_node_type in {"chapter", "review"} else None
        self.loading = True
        self.show_current_node()
        self.loading = False
        self.status_label.setText(f"正在整理：{item.text(0).lstrip('● ').strip()}")

    def show_current_node(self) -> None:
        if not self.current_lesson or not self.current_id:
            return
        self.editor.anchor_bar.setVisible(self.current_node_type == "lesson")
        if self.current_node_type == "chapter":
            self.chapter_editor.set_chapter(self.current_lesson, self.chapter_notes.get(self.current_id, {}), review_mode=False)
            self.editor_stack.setCurrentWidget(self.chapter_editor)
        elif self.current_node_type == "review":
            chapter_id = self.current_lesson["chapter_id"]
            self.chapter_editor.set_chapter(self.current_lesson, self.chapter_notes.get(chapter_id, {}), review_mode=True)
            self.editor_stack.setCurrentWidget(self.chapter_editor)
        else:
            self.editor.set_lesson(self.current_lesson, self.notes.get(self.current_id, {}))
            self.editor_stack.setCurrentWidget(self.editor)
        self.update_context_bar()
        if self.pdf_reader.isVisible() and not self.pdf_reader.capture_mode:
            self.locate_current_in_reader()

    def save_current(self) -> None:
        if self.loading or not self.current_id:
            return
        if self.current_node_type == "chapter":
            data = self.chapter_editor.chapter_data()
            if data.get("note"):
                self.chapter_notes[self.current_id] = data
            else:
                self.chapter_notes.pop(self.current_id, None)
        elif self.current_node_type == "review":
            chapter_id = self.current_lesson["chapter_id"]
            chapter_data = dict(self.chapter_notes.get(chapter_id, {}))
            chapter_data["review"] = self.chapter_editor.review_data()
            self.chapter_notes[chapter_id] = chapter_data
        else:
            note = self.editor.note()
            if self.has_content(note):
                note["updated_at"] = now()
                self.notes[self.current_id] = note
            else:
                self.notes.pop(self.current_id, None)
        self.write_notes()
        self.update_progress()

    def write_notes(self) -> None:
        path = data_path()
        disk_fingerprint = self.storage.fingerprint(path)
        if self.storage.enabled and self.notes_fingerprint and disk_fingerprint and disk_fingerprint != self.notes_fingerprint:
            if not self.resolve_write_conflict():
                return
        disk_payload = self.storage.read_json(path)
        disk_revision = int(disk_payload.get("revision", 0) or 0)
        payload = {
            "version": 5,
            "revision": max(self.notes_revision, disk_revision) + 1,
            "updated_at": now(),
            "updated_by": self.storage.device_name if self.storage.enabled else "本机",
            "notes": self.notes,
            "chapter_notes": self.chapter_notes,
            "section_notes": self.section_notes,
            "custom_subsections": self.custom_subsections,
        }
        try:
            self.storage.write_json(path, payload)
        except OSError as error:
            QMessageBox.warning(self, "保存失败", str(error))
            return
        self.notes_revision = payload["revision"]
        self.notes_fingerprint = self.storage.fingerprint(path)
        self.configure_sync_watcher()

    def ensure_local_pdf_root(self) -> bool:
        """同步只带笔记和截图；找不到 PDF 时在本机单独选择一次教材目录。"""
        if not self.current_lesson:
            return False
        reference = self.current_lesson.get("pdf_reference", {})
        if Path(reference.get("path", "")).exists():
            return True
        edition = self.current_lesson["edition"]
        choice = QMessageBox.question(
            self, "需要本机教材目录",
            f"本机未找到 {edition} 对应的教材 PDF。\n是否选择该版本教材所在的文件夹？",
            QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No,
            QMessageBox.StandardButton.Yes,
        )
        if choice != QMessageBox.StandardButton.Yes:
            return False
        folder = QFileDialog.getExistingDirectory(self, f"选择 {edition} 教材文件夹", str(PDF_ROOTS.get(edition, Path.home())))
        if not folder:
            return False
        PDF_ROOTS[edition] = Path(folder)
        self.storage.settings.setValue(f"pdf_roots/{edition}", folder)
        self.pdf_index = PdfReferenceIndex()
        refreshed = self.load_catalog()
        refreshed_lesson = next((entry for entry in refreshed if entry["id"] == self.current_id), None)
        if refreshed_lesson:
            self.current_lesson = refreshed_lesson
            self.lessons = refreshed
            self.show_current_node()
        return bool(self.current_lesson and Path(self.current_lesson.get("pdf_reference", {}).get("path", "")).exists())

    def capture_textbook_screenshot(self, field: FormulaTextEdit) -> str | None:
        if not self.current_lesson:
            QMessageBox.information(self, "尚未选择教材", "请先从左侧选择一个教材小节。")
            field.cancel_external_capture()
            return None
        if not self.current_lesson.get("pdf_reference"):
            QMessageBox.information(self, "当前没有对应教材页", "章页与章节总复习请使用“插入本机图片”；教材框选截图请在具体小节中使用。")
            field.cancel_external_capture()
            return None
        if not self.ensure_local_pdf_root():
            field.cancel_external_capture()
            return None
        reference = self.current_lesson.get("pdf_reference", {})
        if not reference.get("path") or not Path(reference["path"]).exists():
            QMessageBox.warning(self, "找不到教材 PDF", f"未找到本节关联的教材文件：\n{reference.get('path', '—')}")
            field.cancel_external_capture()
            return None
        if self.pending_screenshot_field and self.pending_screenshot_field is not field:
            self.pending_screenshot_field.cancel_external_capture()
        self.pending_screenshot_field = field
        self.pending_screenshot_context = dict(self.current_lesson)
        self.set_pdf_reader_visible(True)
        detail = f"{self.current_lesson['section_no']} {self.current_lesson['section_title']} · 框选教材截图"
        if not self.pdf_reader.open_document(Path(reference["path"]), int(reference.get("start") or 1), detail):
            self.pending_screenshot_field = None
            self.pending_screenshot_context = None
            field.cancel_external_capture()
            return None
        if not self.pdf_reader.begin_capture():
            self.pending_screenshot_field = None
            self.pending_screenshot_context = None
            field.cancel_external_capture()
            return None
        self.status_label.setText("请在右侧教材栏框选内容，再点击“插入框选”")
        # 截图将在右侧确认后异步回插到当前字段。
        return None

    def complete_reader_capture(self, image: QImage, page: int, crop_rect: dict) -> None:
        field = self.pending_screenshot_field
        context = self.pending_screenshot_context
        if field is None or context is None:
            return
        SCREENSHOT_DIR.mkdir(parents=True, exist_ok=True)
        screenshot_id = uuid.uuid4().hex
        image_path = SCREENSHOT_DIR / f"{screenshot_id}.png"
        if not image.save(str(image_path), "PNG"):
            QMessageBox.warning(self, "截图保存失败", "无法把框选图片保存到笔记资料目录。")
            field.cancel_external_capture()
            self.pending_screenshot_field = None
            self.pending_screenshot_context = None
            return
        reference = context.get("pdf_reference", {})
        metadata = {
            # 同步数据不保存本机绝对路径；另一台电脑只需各自配置教材目录即可继续引用。
            "edition": context["edition"],
            "book": context["file"],
            "page": page,
            "section_range": [reference["start"], reference["end"]],
            "lesson_id": context["id"],
            "crop_rect": crop_rect,
            "created_at": now(),
        }
        (SCREENSHOT_DIR / f"{screenshot_id}.json").write_text(json.dumps(metadata, ensure_ascii=False, indent=2), encoding="utf-8")
        self.pending_screenshot_field = None
        self.pending_screenshot_context = None
        field.insert_external_screenshot(screenshot_id)
        self.status_label.setText(f"已插入教材第 {metadata['page']} 页截图")

    def cancel_reader_capture(self) -> None:
        field = self.pending_screenshot_field
        self.pending_screenshot_field = None
        self.pending_screenshot_context = None
        if field:
            field.cancel_external_capture()
        self.status_label.setText("已取消教材截图框选")

    def import_local_image(self, _field) -> str | None:
        source, _ = QFileDialog.getOpenFileName(self, "选择要插入并同步的图片", "", "图片文件 (*.png *.jpg *.jpeg *.webp *.bmp)")
        if not source:
            return None
        image = QImage(source)
        if image.isNull():
            QMessageBox.warning(self, "无法读取图片", "请选择有效的 PNG、JPG、WEBP 或 BMP 图片。")
            return None
        SCREENSHOT_DIR.mkdir(parents=True, exist_ok=True)
        image_id = uuid.uuid4().hex
        target = SCREENSHOT_DIR / f"{image_id}.png"
        if not image.save(str(target), "PNG"):
            QMessageBox.warning(self, "图片保存失败", "无法将图片复制到笔记资料目录。")
            return None
        metadata = {"kind": "local_image", "lesson_id": self.current_id, "created_at": now()}
        (SCREENSHOT_DIR / f"{image_id}.json").write_text(json.dumps(metadata, ensure_ascii=False, indent=2), encoding="utf-8")
        self.status_label.setText("已插入图片；将随教材笔记同步")
        return image_id

    def open_current_pdf(self) -> None:
        if not self.current_lesson:
            return
        if not self.ensure_local_pdf_root():
            return
        reference = self.current_lesson.get("pdf_reference", {})
        pdf_path = Path(reference.get("path", ""))
        if not pdf_path.exists():
            QMessageBox.warning(self, "找不到教材 PDF", f"未找到本节关联的教材文件：\n{pdf_path or '—'}")
            return
        url = QUrl.fromLocalFile(str(pdf_path))
        url.setFragment(f"page={reference.get('start', 1)}")
        if not QDesktopServices.openUrl(url):
            QMessageBox.warning(self, "无法打开 PDF", "系统未能调用默认 PDF 工具，请检查该 PDF 的打开方式。")
            return
        self.status_label.setText(f"已调用系统 PDF 工具：第 {reference.get('start', 1)} 页")

    def update_progress(self) -> None:
        count = sum(self.has_content(note) for note in self.notes.values())
        self.progress.setText(f"已整理 {count} 节\n教材目录共 {len(self.lessons)} 节")

    def clear_note(self) -> None:
        if not self.current_id:
            return
        answer = QMessageBox.question(self, "清空本节笔记", "确定清空本节的所有笔记吗？", QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No)
        if answer != QMessageBox.StandardButton.Yes:
            return
        if self.current_node_type == "chapter":
            self.chapter_notes.pop(self.current_id, None)
        elif self.current_node_type == "review":
            chapter_id = self.current_lesson["chapter_id"]
            chapter_data = dict(self.chapter_notes.get(chapter_id, {}))
            chapter_data.pop("review", None)
            self.chapter_notes[chapter_id] = chapter_data
        else:
            self.notes.pop(self.current_id, None)
        self.loading = True
        self.show_current_node()
        self.loading = False
        self.write_notes()
        self.populate_tree()
        self.update_progress()
        self.status_label.setText("已清空本节笔记")

    def export_notes(self) -> None:
        self.save_current()
        target, _ = QFileDialog.getSaveFileName(self, "导出教材笔记", str(Path.home() / "Desktop" / f"教材笔记备份_{datetime.now():%Y%m%d}.json"), "JSON 文件 (*.json)")
        if target:
            payload = {
                "version": 5, "exported_at": now(), "notes": self.notes,
                "chapter_notes": self.chapter_notes, "section_notes": self.section_notes,
                "custom_subsections": self.custom_subsections, "screenshots": self.backup_screenshots(),
            }
            Path(target).write_text(json.dumps(payload, ensure_ascii=False, indent=2), encoding="utf-8")
            self.status_label.setText(f"已导出到：{target}")

    def import_notes(self) -> None:
        source, _ = QFileDialog.getOpenFileName(self, "导入教材笔记", "", "JSON 文件 (*.json)")
        if not source:
            return
        try:
            payload = json.loads(Path(source).read_text(encoding="utf-8"))
            raw = payload["notes"]
            if not isinstance(raw, dict):
                raise ValueError
        except (OSError, KeyError, ValueError, json.JSONDecodeError):
            QMessageBox.warning(self, "导入失败", "请选择本工具导出的有效 JSON 备份文件。")
            return
        self.restore_screenshots(payload.get("screenshots", {}))
        self.notes.update({key: normalize_note(value) for key, value in raw.items()})
        if isinstance(payload.get("chapter_notes"), dict):
            self.chapter_notes.update(payload["chapter_notes"])
        if isinstance(payload.get("section_notes"), dict):
            self.section_notes.update(payload["section_notes"])
        if isinstance(payload.get("custom_subsections"), dict):
            self.custom_subsections.update(payload["custom_subsections"])
        self.write_notes()
        self.populate_tree()
        self.update_progress()
        if self.current_lesson:
            self.loading = True
            self.show_current_node()
            self.loading = False
        self.status_label.setText("导入完成")

    def backup_screenshots(self) -> dict:
        assets = {}
        all_note_data = {
            "notes": self.notes,
            "chapter_notes": self.chapter_notes,
            "section_notes": self.section_notes,
        }
        for screenshot_id in referenced_screenshot_ids(all_note_data):
            image_path = SCREENSHOT_DIR / f"{screenshot_id}.png"
            if not image_path.exists():
                continue
            metadata_path = SCREENSHOT_DIR / f"{screenshot_id}.json"
            assets[screenshot_id] = {
                "png": base64.b64encode(image_path.read_bytes()).decode("ascii"),
                "metadata": json.loads(metadata_path.read_text(encoding="utf-8")) if metadata_path.exists() else {},
            }
        return assets

    def restore_screenshots(self, assets: dict) -> None:
        if not isinstance(assets, dict):
            return
        SCREENSHOT_DIR.mkdir(parents=True, exist_ok=True)
        for screenshot_id, item in assets.items():
            if not re.fullmatch(r"[0-9a-f]{32}", str(screenshot_id)) or not isinstance(item, dict):
                continue
            encoded = item.get("png")
            if not isinstance(encoded, str):
                continue
            try:
                (SCREENSHOT_DIR / f"{screenshot_id}.png").write_bytes(base64.b64decode(encoded, validate=True))
                (SCREENSHOT_DIR / f"{screenshot_id}.json").write_text(json.dumps(item.get("metadata", {}), ensure_ascii=False, indent=2), encoding="utf-8")
            except (OSError, ValueError):
                continue

    def export_current_note(self) -> None:
        if not self.current_lesson or self.current_node_type != "lesson":
            QMessageBox.information(self, "请选择具体小节", "单节 Markdown 导出仅用于具体教学小节；章页与章节总复习会随完整备份同步。")
            return
        self.save_current()
        note = normalize_note(self.notes.get(self.current_id, {}))
        lesson = self.current_lesson
        parts = [f"# {lesson['section_no']} {lesson['section_title']}", "", "## 教材引言", "", lesson.get("intro_text") or "暂未提取到节引言。", ""]
        if note["intro_note"]:
            parts.extend(["## 引入备注", "", note["intro_note"], ""])
        self.append_title_content_markdown(parts, "知识点列表", note["knowledge"])
        if note["patterns"]:
            parts.extend(["## 基本例习题类型", ""])
            for entry in note["patterns"]:
                parts.extend([f"### {entry.get('title') or '未命名题型'}", ""])
                if entry.get("example"):
                    parts.extend(["**示例**", "", entry["example"], ""])
                if entry.get("note"):
                    parts.extend(["**备注**", "", entry["note"], ""])
        if note["examples"]:
            parts.extend(["## 有价值的例习题", ""])
            for entry in note["examples"]:
                parts.extend([f"### {entry.get('title') or '未命名例题'}", ""])
                if entry.get("source"):
                    parts.extend([f"来源：{entry['source']}", ""])
                if entry.get("problem"):
                    parts.extend(["**原题**", "", entry["problem"], ""])
                if entry.get("note"):
                    parts.extend(["**备注**", "", entry["note"], ""])
        if note["questions"]:
            parts.extend(["## 问题串设计", ""])
            for index, entry in enumerate(note["questions"], 1):
                parts.extend([f"### 大问题 {index}", "", entry.get("question", ""), ""])
                for followup in entry.get("followups", []):
                    if followup.get("text"):
                        parts.append(f"- 追问：{followup['text']}")
                parts.append("")
        self.append_title_content_markdown(parts, "易错与辨析", note["pitfalls"])
        if note["lesson_note"]:
            parts.extend(["## 课后备注", "", note["lesson_note"], ""])
        target, _ = QFileDialog.getSaveFileName(self, "导出当前小节笔记", str(Path.home() / "Desktop" / f"{lesson['section_no']}_{lesson['section_title']}_教材笔记.md"), "Markdown 文件 (*.md)")
        if target:
            Path(target).write_text("\n".join(parts), encoding="utf-8")
            self.status_label.setText(f"已导出：{target}")

    @staticmethod
    def append_title_content_markdown(parts: list[str], heading: str, entries: list[dict]) -> None:
        if not entries:
            return
        parts.extend([f"## {heading}", ""])
        for entry in entries:
            parts.extend([f"### {entry.get('title') or '未命名项目'}", "", entry.get("content", ""), ""])

    def show_comparison(self) -> None:
        if not self.current_lesson or self.current_node_type != "lesson":
            QMessageBox.information(self, "尚未选择小节", "请先选择一个小节，再定位另一版本中的相近内容。")
            return
        current = self.current_lesson
        candidates = [entry for entry in self.lessons if entry["edition"] != current["edition"]]
        tokens = set(current["section_title"])
        candidates.sort(key=lambda entry: len(tokens & set(entry["section_title"])) + (3 if entry["section_no"] == current["section_no"] else 0), reverse=True)
        dialog = QDialog(self)
        dialog.setWindowTitle("跨版本定位")
        dialog.resize(720, 500)
        layout = QVBoxLayout(dialog)
        layout.addWidget(QLabel(f"当前：{current['edition']} · {current['section_no']} {current['section_title']}"))
        output = QTextEdit()
        output.setReadOnly(True)
        output.setPlainText("\n\n".join(
            f"{entry['edition']} · {clean_name(entry['file'])}\n{entry['chapter']}  {entry['section_no']} {entry['section_title']}\n{entry.get('intro_text', '')[:160]}"
            for entry in candidates[:8]
        ))
        layout.addWidget(output)
        close = QPushButton("关闭")
        close.clicked.connect(dialog.accept)
        layout.addWidget(close)
        dialog.exec()

    def show_latex_help(self) -> None:
        QMessageBox.information(self, "LaTeX 输入说明", "所有文本字段都支持 LaTeX。公式用单个美元符号包裹，例如：\n\n$f(x)=x^2+1$\n\n分式：$\\frac{a+b}{2}$\n根式：$\\sqrt{x^2+y^2}$\n\n平时字段只显示排版结果。点击字段后进入源码编辑；光标离开编辑框时会自动收起并重新渲染，“完成编辑”只是可选快捷操作。")

    def closeEvent(self, event) -> None:  # type: ignore[override]
        self.save_current()
        self.release_current_lock()
        super().closeEvent(event)


def main() -> None:
    app = QApplication(sys.argv)
    app.setApplicationName(APP_TITLE)
    app.setOrganizationName("个人教材笔记本")
    app.setStyleSheet("""
        QMainWindow { background: #18232e; color: #dce7ee; }
        #sidebar { background: #1b2732; border-right: 1px solid #324452; }
        #sidebarHolder { background: #1b2732; }
        #workspace { background: #18232e; }
        #sidebarTitle { font-size: 17px; font-weight: 700; color: #f3f7fa; letter-spacing: 1px; }
        #progress { background: #223541; border: 1px solid #385366; border-radius: 6px; padding: 8px 9px; color: #c7d8e3; }
        #sidebar QLineEdit, #sidebar QComboBox { background: #23333f; border: 1px solid #385366; color: #e9f2f7; border-radius: 5px; padding: 7px; }
        #sidebar QLineEdit:focus, #sidebar QComboBox:focus { border: 1px solid #5caeff; }
        #sidebar QComboBox::drop-down { border: 0; width: 28px; } #sidebar QComboBox::down-arrow { image: none; width: 0; height: 0; }
        #sidebar QTreeWidget { background: transparent; color: #dce8ef; border: 0; outline: 0; }
        #sidebar QTreeWidget::item { padding: 6px 5px; border-radius: 4px; }
        #sidebar QTreeWidget::item:selected { background: #1f6fbf; color: #ffffff; }
        #sidebar QTreeWidget::item:hover { background: #2c3e4d; }
        #lessonTitle { color: #e7f0f5; font-size: 23px; font-weight: 650; padding: 7px 0 0; }
        #meta { color: #9cb0c0; font-size: 13px; padding: 0 0 7px; }
        #contextBar { background: #202d38; border: 0; border-bottom: 1px solid #344956; border-radius: 0; }
        #contextPath { color: #edf4f7; font-size: 14px; font-weight: 700; }
        #contextDetail, #pdfSubheading { color: #9bb0be; font-size: 12px; }
        #anchorBar { background: transparent; border: 0; border-left: 1px solid #344956; border-radius: 0; }
        #anchorButton { background: transparent; color: #9fb1bd; border: 0; border-bottom: 2px solid transparent; border-radius: 0; padding: 9px 11px 8px; font-weight: 600; }
        #anchorButton:hover { background: #293b47; color: #dcecff; }
        #anchorButton:checked { color: #76baff; border-bottom-color: #3f98f5; background: transparent; }
        #notebookSection, #sourceIntro { background: #23313d; border: 1px solid #364b59; border-radius: 8px; }
        #sectionLabel { color: #69afff; font-size: 16px; font-weight: 700; }
        #sectionToggle { background: transparent; color: #69afff; border: 0; padding: 0; font-size: 16px; font-weight: 700; text-align: left; }
        #sectionToggle:hover { color: #a4ceff; }
        #sectionHint { color: #9aafbc; padding-bottom: 1px; }
        #fieldLabel, #cardCaption { color: #9db1be; font-size: 12px; font-weight: 600; }
        #dragGrip { color: #728a98; font-size: 18px; padding-right: 2px; }
        #intro { background: #1d3449; border: 1px solid #345c7c; border-left: 4px solid #3f98f5; border-radius: 7px; padding: 7px; color: #d5e7fb; }
        #sourceImage { background: transparent; border: 0; border-radius: 5px; padding: 0; color: #718096; }
        #noteItem, #questionItem { background: #273743; border: 1px solid #3b5260; border-radius: 6px; }
        #followupItem { background: #1f2c36; border: 1px solid #334b5b; border-radius: 5px; }
        #followupTag { color: #a8c8dd; font-size: 12px; font-weight: 650; }
        #textbookAttachment { background: #1f2c36; border: 1px solid #3b5260; border-radius: 7px; }
        #attachmentSource { background: transparent; color: #78baff; border: 0; padding: 3px 4px; font-size: 12px; font-weight: 600; }
        #attachmentSource:hover { color: #afd4ff; text-decoration: underline; }
        #missingAttachment { color: #ff9a9f; padding: 5px 7px; }
        #cardList, #followupList { background: transparent; border: 0; outline: 0; }
        QListWidget::item { border: 0; } QListWidget::item:selected { background: transparent; }
        QListWidget::item:drop { border: 2px solid #3f98f5; }
        QTextEdit, QLineEdit, QComboBox, QSpinBox { background: #1d2a34; border: 1px solid #3b5260; color: #e5eef3; border-radius: 6px; padding: 7px; selection-background-color: #246eae; }
        QTextEdit:focus, QLineEdit:focus, QComboBox:focus, QSpinBox:focus { border: 2px solid #4b9fff; }
        QPushButton { background: #236eaf; color: white; border: 0; border-radius: 6px; padding: 7px 11px; font-weight: 600; }
        QPushButton:hover { background: #195b94; } QPushButton:disabled { background: #526a7b; color: #c9d8e2; }
        QPushButton#smallAction { background: #2a3b47; color: #d5e5ed; border: 1px solid #486170; padding: 5px 9px; }
        QPushButton#smallAction:hover { background: #345061; border-color: #6aaeff; color: #eaf4ff; }
        QPushButton#primaryCompact { background: #236eaf; color: white; padding: 5px 9px; }
        QPushButton#removeAction { background: transparent; color: #ffadb0; border: 1px solid #a75a61; padding: 4px 8px; }
        QTreeWidget { background: transparent; border: 0; outline: 0; } QTreeWidget::item { padding: 6px 4px; border-radius: 5px; }
        QTreeWidget::item:selected { background: #254e75; color: #eef6ff; } QTreeWidget::item:hover { background: #2c3e4d; }
        #pdfReader { background: #202d38; border: 1px solid #364b59; border-radius: 8px; }
        #pdfHeading { color: #e5eef3; font-size: 16px; font-weight: 700; }
        #pdfControl { background: #2a3b47; color: #d7e5ed; border: 1px solid #486170; border-radius: 5px; min-width: 26px; padding: 4px 6px; font-size: 17px; }
        #pdfControl:hover { background: #345061; color: #9ccbff; }
        #pdfPageBox, #pdfZoomBox { min-width: 62px; padding: 4px 5px; }
        #pdfPageTotal { color: #a9bdc9; min-width: 42px; }
        #bookmarkBox { padding: 5px 7px; }
        #captureBar { background: #1e3c59; border: 1px solid #3b719e; border-radius: 7px; color: #d8eaff; }
        #pdfScroll { background: #141e27; border: 1px solid #354a59; border-radius: 7px; }
        #pdfEmpty { color: #9eb3c0; }
        #sidebarHeaderToggle, #sidebarRailToggle { background: transparent; color: #a9c0ce; border: 0; border-radius: 5px; font-size: 24px; padding: 0 6px; min-width: 28px; }
        #sidebarHeaderToggle:hover, #sidebarRailToggle:hover { background: #2a3b47; color: #ffffff; }
        #editorScroll, #editorScroll::viewport, #editorStack { background: #18232e; border: 0; }
        QComboBox QAbstractItemView { background: #253541; color: #e5eef3; border: 1px solid #486170; selection-background-color: #246eae; }
        QSplitter::handle { background: #22313c; } QSplitter::handle:hover { background: #3f98f5; }
        QStatusBar { background: #202d38; border-top: 1px solid #344956; color: #a9bdc9; }
        QMenuBar { background: #202b36; color: #d9e4ec; border-bottom: 1px solid #344452; } QMenuBar::item:selected { background: #2d3e4d; } QMenu { background: #263542; color: #e4eef3; border: 1px solid #3d5262; } QMenu::item:selected { background: #1f6fbf; }
    """)
    window = MainWindow()
    if not window.lessons:
        QMessageBox.critical(window, "找不到教材资料", f"未能读取教材目录。请确认资料目录存在：\n{window.source_root}")
    window.show()
    sys.exit(app.exec())


if __name__ == "__main__":
    main()
