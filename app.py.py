# -*- coding: utf-8 -*-
"""
ระบบเว็บไซต์ธุรกิจอลูมิเนียมลายไม้ — ประตู หน้าต่าง ระแนงปรับองศา มุ้งกันยุง มุ้งจีบ
มุ้งลวดบานเลื่อน/บานเปิด มุ้งจีบนิรภัยอลูมิเนียม มุ้งลวดนิรภัยสแตนเลส

Single-file Flask app + Tailwind (CDN) + SQLite (มากับ Python)

หน้าร้าน (ลูกค้า)
  /                    หน้าแรก + รายการสินค้า + ราคาเริ่มต้น
  /calculator          เลือกสินค้า ปรับรูปแบบ (จำนวนบาน ลูกฟัก ทิศทางเปิด องศาระแนง สีลายไม้ กระจก)
                       ใส่ขนาด กว้าง×สูง → ราคาทันที พร้อมภาพตัวอย่าง
  /cart                ตะกร้า แก้ไข/ลบ/ปรับจำนวน แล้วส่งคำสั่งซื้อ
  /track               ติดตามสถานะงานด้วยเลขที่คำสั่งซื้อ + เบอร์โทร

หลังบ้าน (ผู้ดูแล)    /admin   (ค่าเริ่มต้น admin / admin1234 — เปลี่ยนด้วย env ADMIN_USER, ADMIN_PASSWORD)
  - แดชบอร์ด ยอดขาย ต้นทุน กำไร
  - คำสั่งซื้อ + ใบแตกวัสดุ (BOM) ต้นทุนรายชิ้น + เปลี่ยนสถานะ + พิมพ์
  - สินค้า & สูตรวัสดุ (BOM) แก้สูตรได้เอง เช่น  L, P*2*(W/P+H), ceil(H/0.1)*W
  - ราคาวัสดุ (แก้ราคาแล้วต้นทุน/ราคาขายคำนวณใหม่อัตโนมัติ)
  - สีลายไม้ / ชนิดกระจก / ตั้งค่า (% เผื่อเศษ, การปัดราคา, ข้อมูลร้าน)

รัน:
  pip install flask
  python app.py          → http://127.0.0.1:5000
"""
import ast
import datetime
import hmac
import json
import math
import operator
import os
import re
import secrets
import sqlite3
import string
from functools import wraps

from flask import (Flask, abort, flash, g, jsonify, redirect, render_template,
                   request, session, url_for)
from jinja2 import DictLoader
from markupsafe import Markup

BASE_DIR = os.path.dirname(os.path.abspath(__file__))
DB_PATH = os.environ.get("DB_PATH", os.path.join(BASE_DIR, "alu_shop.db"))
ADMIN_USER = os.environ.get("ADMIN_USER", "admin")
ADMIN_PASSWORD = os.environ.get("ADMIN_PASSWORD", "admin1234")

app = Flask(__name__)
app.secret_key = os.environ.get("SECRET_KEY") or secrets.token_hex(32)

DEFAULT_SETTINGS = {
    "company_name": "ไม้ทองอลูมิเนียม",
    "tagline": "ประตู หน้าต่าง ระแนง มุ้งลวด อลูมิเนียมลายไม้ ผลิตตามขนาดจริง",
    "phone": "081-234-5678",
    "line_id": "@maithong-alu",
    "address": "99/9 ถ.ตัวอย่าง ต.ตัวอย่าง อ.เมือง จ.นนทบุรี 11000",
    "waste_pct": "5",
    "round_to": "10",
}

STATUS = {
    "new": ("ใหม่", "bg-sky-100 text-sky-700"),
    "confirmed": ("ยืนยัน/นัดวัดหน้างาน", "bg-indigo-100 text-indigo-700"),
    "producing": ("กำลังผลิต", "bg-amber-100 text-amber-800"),
    "ready": ("พร้อมติดตั้ง", "bg-teal-100 text-teal-700"),
    "done": ("ติดตั้งเสร็จสิ้น", "bg-emerald-100 text-emerald-700"),
    "cancelled": ("ยกเลิก", "bg-stone-200 text-stone-600"),
}
STATUS_FLOW = ["new", "confirmed", "producing", "ready", "done"]

MATERIAL_CATEGORIES = {
    "aluminum": "อลูมิเนียม (คิดส่วนเพิ่มตามสี)",
    "mesh": "มุ้ง / ตะแกรง",
    "accessory": "อุปกรณ์",
    "labor": "ค่าแรง",
}
PREVIEW_TYPES = {"sliding": "บานเลื่อน", "swing": "บานเปิด", "louver": "ระแนงปรับองศา", "pleated": "มุ้งจีบ"}
INFILL_TYPES = {"glass": "กระจก", "mesh": "มุ้งไฟเบอร์", "ss": "ตะแกรงสแตนเลส",
                "pleat": "มุ้งจีบ", "pleat_safe": "มุ้งจีบนิรภัย", "louver": "ใบระแนง"}
CATEGORY_ORDER = ["ประตู", "หน้าต่าง", "ระแนง", "มุ้งกันยุง", "มุ้งนิรภัย"]

# ---------------------------------------------------------------------------
# Safe formula evaluation (สูตร BOM ที่หลังบ้านแก้ได้)
# ---------------------------------------------------------------------------
_BIN_OPS = {ast.Add: operator.add, ast.Sub: operator.sub, ast.Mult: operator.mul,
            ast.Div: operator.truediv, ast.FloorDiv: operator.floordiv,
            ast.Mod: operator.mod, ast.Pow: operator.pow}
_UNARY_OPS = {ast.UAdd: operator.pos, ast.USub: operator.neg}
_FUNCS = {"ceil": math.ceil, "floor": math.floor, "min": min, "max": max,
          "round": round, "abs": abs, "sqrt": math.sqrt}
FORMULA_VARS = {
    "W": "ความกว้าง (เมตร)", "H": "ความสูง (เมตร)", "A": "พื้นที่ W×H (ตร.ม.)",
    "L": "เส้นรอบรูป 2×(W+H) (เมตร)", "P": "จำนวนบาน", "D": "จำนวนลูกฟักแนวนอนต่อบาน",
}
SAMPLE_VARS = {"W": 1.2, "H": 2.0, "A": 2.4, "L": 6.4, "P": 2, "D": 1}


def safe_eval(expr, variables):
    tree = ast.parse(str(expr), mode="eval")

    def ev(n):
        if isinstance(n, ast.Expression):
            return ev(n.body)
        if isinstance(n, ast.Constant) and isinstance(n.value, (int, float)) and not isinstance(n.value, bool):
            return n.value
        if isinstance(n, ast.Name):
            if n.id in variables:
                return variables[n.id]
            raise ValueError(f"ไม่รู้จักตัวแปร {n.id}")
        if isinstance(n, ast.BinOp) and type(n.op) in _BIN_OPS:
            left, right = ev(n.left), ev(n.right)
            if isinstance(n.op, ast.Pow) and abs(right) > 4:
                raise ValueError("เลขยกกำลังเกิน 4")
            return _BIN_OPS[type(n.op)](left, right)
        if isinstance(n, ast.UnaryOp) and type(n.op) in _UNARY_OPS:
            return _UNARY_OPS[type(n.op)](ev(n.operand))
        if (isinstance(n, ast.Call) and isinstance(n.func, ast.Name)
                and n.func.id in _FUNCS and not n.keywords):
            return _FUNCS[n.func.id](*[ev(a) for a in n.args])
        raise ValueError("สูตรมีรูปแบบที่ไม่อนุญาต")

    return ev(tree)


def validate_formula(expr):
    try:
        v = safe_eval(expr, SAMPLE_VARS)
        float(v)
        return None
    except Exception as e:  # noqa: BLE001
        return str(e) or "สูตรไม่ถูกต้อง"


# ---------------------------------------------------------------------------
# Database
# ---------------------------------------------------------------------------
SCHEMA = """
CREATE TABLE IF NOT EXISTS settings (key TEXT PRIMARY KEY, value TEXT);
CREATE TABLE IF NOT EXISTS materials (
  id INTEGER PRIMARY KEY, code TEXT UNIQUE NOT NULL, name TEXT NOT NULL, unit TEXT NOT NULL,
  unit_cost REAL NOT NULL DEFAULT 0, category TEXT NOT NULL DEFAULT 'accessory');
CREATE TABLE IF NOT EXISTS products (
  id INTEGER PRIMARY KEY, slug TEXT UNIQUE NOT NULL, name TEXT NOT NULL, category TEXT NOT NULL,
  description TEXT DEFAULT '', preview TEXT NOT NULL DEFAULT 'sliding', infill TEXT NOT NULL DEFAULT 'glass',
  panel_options TEXT NOT NULL DEFAULT '2', uses_glass INTEGER DEFAULT 0, has_divider INTEGER DEFAULT 0,
  markup_pct REAL DEFAULT 40, min_price REAL DEFAULT 0,
  min_w REAL DEFAULT 50, max_w REAL DEFAULT 300, min_h REAL DEFAULT 50, max_h REAL DEFAULT 250,
  def_w REAL DEFAULT 100, def_h REAL DEFAULT 100, sort INTEGER DEFAULT 0, active INTEGER DEFAULT 1);
CREATE TABLE IF NOT EXISTS bom (
  id INTEGER PRIMARY KEY, product_id INTEGER NOT NULL REFERENCES products(id) ON DELETE CASCADE,
  material_code TEXT NOT NULL, formula TEXT NOT NULL, note TEXT DEFAULT '', sort INTEGER DEFAULT 0);
CREATE TABLE IF NOT EXISTS finishes (
  id INTEGER PRIMARY KEY, name TEXT NOT NULL, hex TEXT NOT NULL, is_wood INTEGER DEFAULT 1,
  surcharge_pct REAL DEFAULT 0, sort INTEGER DEFAULT 0, active INTEGER DEFAULT 1);
CREATE TABLE IF NOT EXISTS glass_types (
  id INTEGER PRIMARY KEY, name TEXT NOT NULL, hex TEXT NOT NULL DEFAULT '#bfdbfe',
  cost_per_sqm REAL DEFAULT 0, sort INTEGER DEFAULT 0, active INTEGER DEFAULT 1);
CREATE TABLE IF NOT EXISTS orders (
  id INTEGER PRIMARY KEY, code TEXT UNIQUE NOT NULL, created_at TEXT NOT NULL,
  customer_name TEXT, phone TEXT, email TEXT, address TEXT, note TEXT,
  items_json TEXT NOT NULL, total_price REAL DEFAULT 0, total_cost REAL DEFAULT 0,
  status TEXT DEFAULT 'new', admin_note TEXT DEFAULT '');
"""

SEED_MATERIALS = [
    # code, name, unit, unit_cost, category
    ("AL-FRAME", "อลูมิเนียมวงกบ ลายไม้ 4\"", "ม.", 180, "aluminum"),
    ("AL-SASH", "อลูมิเนียมกรอบบาน ลายไม้", "ม.", 150, "aluminum"),
    ("AL-TRACK", "รางบานเลื่อน อลูมิเนียม", "ม.", 120, "aluminum"),
    ("AL-LOUVER", "ใบระแนงอลูมิเนียมลายไม้ 4\"", "ม.", 220, "aluminum"),
    ("AL-PLEAT", "เฟรมอลูมิเนียมมุ้งจีบ", "ม.", 160, "aluminum"),
    ("AL-HEAVY", "อลูมิเนียมเฟรมนิรภัย (หนาพิเศษ)", "ม.", 260, "aluminum"),
    ("MESH-FIBER", "มุ้งไฟเบอร์กลาส", "ตร.ม.", 60, "mesh"),
    ("MESH-PLEAT", "มุ้งจีบโพลีเอสเตอร์", "ตร.ม.", 180, "mesh"),
    ("MESH-ALSAFE", "ตะแกรงอลูมิเนียมนิรภัย (จีบ)", "ตร.ม.", 650, "mesh"),
    ("MESH-SS", "ตะแกรงสแตนเลส 304 นิรภัย", "ตร.ม.", 950, "mesh"),
    ("ROLLER", "ลูกล้อบานเลื่อน", "ชิ้น", 45, "accessory"),
    ("LOCK", "ชุดกุญแจ/ล็อค", "ชุด", 180, "accessory"),
    ("HANDLE", "มือจับ", "ชิ้น", 90, "accessory"),
    ("HINGE", "บานพับสแตนเลส", "ชิ้น", 60, "accessory"),
    ("LOUVER-GEAR", "ชุดกลไกปรับองศาระแนง", "ชุด", 350, "accessory"),
    ("PLEAT-CORD", "สลิง/เชือกมุ้งจีบ", "ม.", 15, "accessory"),
    ("MAGNET", "แม่เหล็กล็อคบาน", "ชุด", 80, "accessory"),
    ("GASKET", "ยางอัดกระจก/ขอบบาน", "ม.", 12, "accessory"),
    ("SCREW", "น็อต สกรู ซิลิโคน", "ชุด", 60, "accessory"),
    ("LABOR", "ค่าแรงผลิต + ติดตั้ง", "ตร.ม.", 350, "labor"),
]

SASH = "P*2*(W/P+H)"
SEED_PRODUCTS = [
    dict(slug="door-sliding", name="ประตูอลูมิเนียมลายไม้ บานเลื่อน", category="ประตู",
         description="ประตูบานเลื่อนกรอบอลูมิเนียมลายไม้ ไม่ผุ ไม่บวม ไม่มีปลวก เลือกกระจกได้",
         preview="sliding", infill="glass", panel_options="2,3,4", uses_glass=1, has_divider=1,
         markup_pct=45, min_price=6500, min_w=120, max_w=400, min_h=180, max_h=260, def_w=200, def_h=220,
         bom=[("AL-FRAME", "L", "วงกบรอบนอก"), ("AL-SASH", SASH + " + D*W", "กรอบบาน + ลูกฟัก"),
              ("AL-TRACK", "2*W", "รางบน-ล่าง"), ("ROLLER", "P*2", "2 ลูก/บาน"), ("LOCK", "1", ""),
              ("HANDLE", "P", ""), ("GASKET", SASH, "ยางรอบบาน"), ("SCREW", "1", ""),
              ("LABOR", "max(A,1.5)", "ขั้นต่ำ 1.5 ตร.ม.")]),
    dict(slug="door-swing", name="ประตูอลูมิเนียมลายไม้ บานเปิด", category="ประตู",
         description="ประตูบานเปิดเดี่ยว/คู่ ลายไม้เสมือนจริง แข็งแรง ทนแดดทนฝน",
         preview="swing", infill="glass", panel_options="1,2", uses_glass=1, has_divider=1,
         markup_pct=45, min_price=5500, min_w=70, max_w=200, min_h=180, max_h=260, def_w=90, def_h=210,
         bom=[("AL-FRAME", "L", "วงกบ"), ("AL-SASH", SASH + " + D*W", "กรอบบาน + ลูกฟัก"),
              ("HINGE", "P*3", "3 ตัว/บาน"), ("LOCK", "1", ""), ("HANDLE", "P", ""),
              ("GASKET", SASH, ""), ("SCREW", "1", ""), ("LABOR", "max(A,1.5)*1.2", "")]),
    dict(slug="window-sliding", name="หน้าต่างอลูมิเนียมลายไม้ บานเลื่อน", category="หน้าต่าง",
         description="หน้าต่างบานเลื่อน 2–4 บาน ประหยัดพื้นที่ เปิดรับลมได้กว้าง",
         preview="sliding", infill="glass", panel_options="2,3,4", uses_glass=1, has_divider=1,
         markup_pct=45, min_price=2800, min_w=60, max_w=300, min_h=40, max_h=200, def_w=160, def_h=120,
         bom=[("AL-FRAME", "L", ""), ("AL-SASH", SASH + " + D*W", ""), ("AL-TRACK", "2*W", ""),
              ("ROLLER", "P*2", ""), ("LOCK", "1", ""), ("HANDLE", "P", ""), ("GASKET", SASH, ""),
              ("SCREW", "1", ""), ("LABOR", "max(A,0.8)", "ขั้นต่ำ 0.8 ตร.ม.")]),
    dict(slug="window-swing", name="หน้าต่างอลูมิเนียมลายไม้ บานเปิด", category="หน้าต่าง",
         description="หน้าต่างบานเปิดออก ปิดสนิท กันฝนสาดได้ดี",
         preview="swing", infill="glass", panel_options="1,2", uses_glass=1, has_divider=1,
         markup_pct=45, min_price=2500, min_w=40, max_w=160, min_h=40, max_h=180, def_w=100, def_h=110,
         bom=[("AL-FRAME", "L", ""), ("AL-SASH", SASH + " + D*W", ""), ("HINGE", "P*2", ""),
              ("LOCK", "P", ""), ("HANDLE", "P", ""), ("GASKET", SASH, ""), ("SCREW", "1", ""),
              ("LABOR", "max(A,0.8)", "")]),
    dict(slug="louver", name="ระแนงอลูมิเนียมลายไม้ ปรับองศาได้", category="ระแนง",
         description="ระแนงบังแดด/บังสายตา ปรับมุมใบได้ 0–90° ใช้เป็นฉากกั้น ผนังหน้าบ้าน หรือบานหน้าต่าง",
         preview="louver", infill="louver", panel_options="1", uses_glass=0, has_divider=0,
         markup_pct=40, min_price=3500, min_w=50, max_w=300, min_h=50, max_h=300, def_w=150, def_h=200,
         bom=[("AL-FRAME", "L", "เฟรมรอบ"), ("AL-LOUVER", "ceil(H/0.1)*W", "ใบระแนงทุก 10 ซม."),
              ("LOUVER-GEAR", "ceil(W/1.2)", "1 ชุด/ช่วง 1.2 ม."), ("SCREW", "ceil(A)", ""),
              ("LABOR", "max(A,1)", "")]),
    dict(slug="screen-sliding", name="มุ้งลวดบานเลื่อน", category="มุ้งกันยุง",
         description="มุ้งลวดไฟเบอร์กลาส กรอบอลูมิเนียมลายไม้ ติดคู่กับหน้าต่าง/ประตูบานเลื่อน",
         preview="sliding", infill="mesh", panel_options="1,2", uses_glass=0, has_divider=0,
         markup_pct=50, min_price=1200, min_w=50, max_w=300, min_h=50, max_h=250, def_w=80, def_h=120,
         bom=[("AL-SASH", SASH, "กรอบบานมุ้ง"), ("AL-TRACK", "W", "รางมุ้ง"), ("MESH-FIBER", "A*1.1", "เผื่อขอบ 10%"),
              ("ROLLER", "P*2", ""), ("HANDLE", "P", ""), ("SCREW", "1", ""),
              ("LABOR", "max(A,0.8)*0.5", "")]),
    dict(slug="screen-swing", name="มุ้งลวดบานเปิด", category="มุ้งกันยุง",
         description="มุ้งลวดบานเปิด พร้อมแม่เหล็กล็อค ใช้กับประตู/หน้าต่างบานเปิด",
         preview="swing", infill="mesh", panel_options="1,2", uses_glass=0, has_divider=0,
         markup_pct=50, min_price=1300, min_w=50, max_w=180, min_h=50, max_h=250, def_w=90, def_h=200,
         bom=[("AL-FRAME", "L", "วงกบมุ้ง"), ("AL-SASH", SASH, ""), ("HINGE", "P*2", ""), ("MAGNET", "P", ""),
              ("MESH-FIBER", "A*1.1", ""), ("HANDLE", "P", ""), ("SCREW", "1", ""),
              ("LABOR", "max(A,0.8)*0.5", "")]),
    dict(slug="pleated", name="มุ้งจีบ", category="มุ้งกันยุง",
         description="มุ้งจีบพับเก็บได้ ไม่เกะกะ ไม่ต้องถอดล้าง เหมาะกับประตูทางเข้า-ออกบ่อย",
         preview="pleated", infill="pleat", panel_options="1,2", uses_glass=0, has_divider=0,
         markup_pct=50, min_price=1800, min_w=50, max_w=300, min_h=50, max_h=260, def_w=90, def_h=210,
         bom=[("AL-PLEAT", "L", "เฟรม + รางมุ้งจีบ"), ("MESH-PLEAT", "A*1.6", "ผ้าจีบ (เผื่อพับ)"),
              ("PLEAT-CORD", "ceil(H/0.25)*W*1.2", "สลิงทุก 25 ซม."), ("HANDLE", "P", ""),
              ("MAGNET", "P", ""), ("SCREW", "1", ""), ("LABOR", "max(A,0.8)*0.5", "")]),
    dict(slug="pleated-safety", name="มุ้งจีบนิรภัยอลูมิเนียม", category="มุ้งนิรภัย",
         description="มุ้งจีบตะแกรงอลูมิเนียม กันยุง กันขโมย กันสัตว์เลี้ยงข่วน พับเก็บได้",
         preview="pleated", infill="pleat_safe", panel_options="1,2", uses_glass=0, has_divider=0,
         markup_pct=45, min_price=4500, min_w=60, max_w=300, min_h=80, max_h=260, def_w=90, def_h=210,
         bom=[("AL-HEAVY", "L", "เฟรมนิรภัย"), ("MESH-ALSAFE", "A*1.5", ""),
              ("PLEAT-CORD", "ceil(H/0.25)*W*1.2", ""), ("LOCK", "1", ""), ("HANDLE", "P", ""),
              ("SCREW", "1", ""), ("LABOR", "max(A,1)*0.7", "")]),
    dict(slug="ss-sliding", name="มุ้งลวดนิรภัยสแตนเลส บานเลื่อน", category="มุ้งนิรภัย",
         description="ตะแกรงสแตนเลส 304 ทนแรงกระแทก กันขโมย กันยุง มองเห็นวิวชัด",
         preview="sliding", infill="ss", panel_options="2,3,4", uses_glass=0, has_divider=0,
         markup_pct=45, min_price=5500, min_w=80, max_w=400, min_h=80, max_h=260, def_w=180, def_h=210,
         bom=[("AL-HEAVY", "L + " + SASH, "วงกบ + กรอบบานนิรภัย"), ("AL-TRACK", "2*W", ""),
              ("MESH-SS", "A*1.05", ""), ("ROLLER", "P*2", ""), ("LOCK", "P", "ล็อคทุกบาน"),
              ("HANDLE", "P", ""), ("SCREW", "1", ""), ("LABOR", "max(A,1)*0.8", "")]),
    dict(slug="ss-swing", name="มุ้งลวดนิรภัยสแตนเลส บานเปิด", category="มุ้งนิรภัย",
         description="ประตูมุ้งนิรภัยสแตนเลสบานเปิด ล็อคแน่นหนา เปิดรับลมได้ปลอดภัย",
         preview="swing", infill="ss", panel_options="1,2", uses_glass=0, has_divider=0,
         markup_pct=45, min_price=5000, min_w=60, max_w=200, min_h=80, max_h=260, def_w=90, def_h=210,
         bom=[("AL-HEAVY", "L + " + SASH, ""), ("HINGE", "P*3", ""), ("LOCK", "1", ""),
              ("MESH-SS", "A*1.05", ""), ("HANDLE", "P", ""), ("SCREW", "1", ""),
              ("LABOR", "max(A,1)*0.8", "")]),
]

SEED_FINISHES = [
    ("ลายไม้สักทอง", "#b8803f", 1, 0), ("ลายไม้โอ๊ค", "#c9a27a", 1, 0),
    ("ลายไม้วอลนัท", "#5c3a21", 1, 5), ("ลายไม้มะฮอกกานี", "#7b2e1e", 1, 5),
    ("ลายไม้เทาวินเทจ", "#8a8580", 1, 8), ("สีขาวอบ", "#f1f1ef", 0, -10),
    ("สีดำด้าน", "#2b2b2b", 0, -5), ("สีชาเข้ม (อะโนไดซ์)", "#4a3b2f", 0, 0),
]
SEED_GLASS = [
    ("กระจกใส 5 มม.", "#cfe8f7", 450), ("กระจกชาดำ 5 มม.", "#6b6458", 550),
    ("กระจกเขียวตัดแสง 5 มม.", "#a7d7c5", 600), ("กระจกฝ้า 5 มม.", "#e8eef2", 650),
    ("กระจกลามิเนต 6.38 มม.", "#bfdbea", 1300), ("กระจกเทมเปอร์ 8 มม.", "#b9d6e6", 1500),
]


def get_db():
    if "db" not in g:
        g.db = sqlite3.connect(DB_PATH)
        g.db.row_factory = sqlite3.Row
        g.db.execute("PRAGMA foreign_keys = ON")
    return g.db


@app.teardown_appcontext
def close_db(_exc):
    db = g.pop("db", None)
    if db is not None:
        db.close()


def init_db():
    con = sqlite3.connect(DB_PATH)
    con.executescript(SCHEMA)
    for k, v in DEFAULT_SETTINGS.items():
        con.execute("INSERT OR IGNORE INTO settings(key,value) VALUES(?,?)", (k, v))
    if not con.execute("SELECT 1 FROM materials LIMIT 1").fetchone():
        con.executemany("INSERT INTO materials(code,name,unit,unit_cost,category) VALUES(?,?,?,?,?)", SEED_MATERIALS)
    if not con.execute("SELECT 1 FROM products LIMIT 1").fetchone():
        for i, p in enumerate(SEED_PRODUCTS):
            p = dict(p)
            bom = p.pop("bom")
            cols = list(p.keys()) + ["sort"]
            cur = con.execute(f"INSERT INTO products({','.join(cols)}) VALUES({','.join('?' * len(cols))})",
                              list(p.values()) + [i])
            con.executemany("INSERT INTO bom(product_id,material_code,formula,note,sort) VALUES(?,?,?,?,?)",
                            [(cur.lastrowid, c, f, n, j) for j, (c, f, n) in enumerate(bom)])
    if not con.execute("SELECT 1 FROM finishes LIMIT 1").fetchone():
        con.executemany("INSERT INTO finishes(name,hex,is_wood,surcharge_pct,sort) VALUES(?,?,?,?,?)",
                        [(n, h, w, s, i) for i, (n, h, w, s) in enumerate(SEED_FINISHES)])
    if not con.execute("SELECT 1 FROM glass_types LIMIT 1").fetchone():
        con.executemany("INSERT INTO glass_types(name,hex,cost_per_sqm,sort) VALUES(?,?,?,?)",
                        [(n, h, c, i) for i, (n, h, c) in enumerate(SEED_GLASS)])
    con.commit()
    con.close()


def get_settings():
    s = dict(DEFAULT_SETTINGS)
    s.update({r["key"]: r["value"] for r in get_db().execute("SELECT key,value FROM settings")})
    return s


def parse_panels(s):
    vals = sorted({int(x) for x in str(s).split(",") if x.strip().isdigit() and 1 <= int(x) <= 8})
    return vals or [1]


def to_float(v, default=0.0):
    try:
        return float(v)
    except (TypeError, ValueError):
        return default


def to_int(v, default=0):
    try:
        return int(float(v))
    except (TypeError, ValueError):
        return default


# ---------------------------------------------------------------------------
# Pricing engine — คำนวณวัสดุ ต้นทุน ราคาขาย อัตโนมัติจาก BOM
# ---------------------------------------------------------------------------
class QuoteError(Exception):
    pass


def calc_quote(cfg, admin=False):
    db = get_db()
    S = get_settings()
    sql = "SELECT * FROM products WHERE slug=?" + ("" if admin else " AND active=1")
    p = db.execute(sql, (str(cfg.get("slug", "")),)).fetchone()
    if not p:
        raise QuoteError("ไม่พบสินค้าที่เลือก")

    w_cm, h_cm = to_float(cfg.get("width"), None), to_float(cfg.get("height"), None)
    if w_cm is None or h_cm is None:
        raise QuoteError("กรุณาระบุความกว้างและความสูงเป็นตัวเลข")
    if not p["min_w"] <= w_cm <= p["max_w"]:
        raise QuoteError(f"ความกว้างต้องอยู่ระหว่าง {p['min_w']:g}–{p['max_w']:g} ซม.")
    if not p["min_h"] <= h_cm <= p["max_h"]:
        raise QuoteError(f"ความสูงต้องอยู่ระหว่าง {p['min_h']:g}–{p['max_h']:g} ซม.")

    panel_opts = parse_panels(p["panel_options"])
    panels = to_int(cfg.get("panels"), panel_opts[0])
    if panels not in panel_opts:
        raise QuoteError("จำนวนบานไม่ถูกต้องสำหรับสินค้านี้")
    divider = max(0, min(3, to_int(cfg.get("divider"), 0))) if p["has_divider"] else 0
    qty = max(1, min(999, to_int(cfg.get("qty"), 1)))
    direction = "right" if cfg.get("direction") == "right" else "left"
    angle = max(0, min(90, to_int(cfg.get("angle"), 45)))

    finish = db.execute("SELECT * FROM finishes WHERE id=? AND active=1", (to_int(cfg.get("finish_id")),)).fetchone() \
        or db.execute("SELECT * FROM finishes WHERE active=1 ORDER BY sort,id LIMIT 1").fetchone()
    glass = None
    if p["uses_glass"]:
        glass = db.execute("SELECT * FROM glass_types WHERE id=? AND active=1", (to_int(cfg.get("glass_id")),)).fetchone() \
            or db.execute("SELECT * FROM glass_types WHERE active=1 ORDER BY sort,id LIMIT 1").fetchone()

    W, H = w_cm / 100, h_cm / 100
    var = {"W": W, "H": H, "A": W * H, "L": 2 * (W + H), "P": panels, "D": divider}
    surcharge = 1 + (finish["surcharge_pct"] / 100 if finish else 0)

    lines = []
    rows = db.execute("""SELECT b.*, m.name AS m_name, m.unit, m.unit_cost, m.category
                         FROM bom b JOIN materials m ON m.code=b.material_code
                         WHERE b.product_id=? ORDER BY b.sort, b.id""", (p["id"],)).fetchall()
    for b in rows:
        try:
            q = max(0.0, float(safe_eval(b["formula"], var)))
        except Exception:  # noqa: BLE001
            raise QuoteError(f"สูตรวัสดุ {b['material_code']} ผิดพลาด กรุณาติดต่อร้าน")
        uc = b["unit_cost"] * (surcharge if b["category"] == "aluminum" else 1)
        lines.append(dict(code=b["material_code"], name=b["m_name"], unit=b["unit"], category=b["category"],
                          formula=b["formula"], note=b["note"], qty=round(q, 3), unit_cost=round(uc, 2),
                          amount=round(q * uc, 2)))
    if glass and glass["cost_per_sqm"] > 0:
        q = var["A"] * 0.9
        lines.append(dict(code="GLASS", name=glass["name"], unit="ตร.ม.", category="glass", formula="A*0.9",
                          note="พื้นที่กระจกโดยประมาณ (หักกรอบ)", qty=round(q, 3),
                          unit_cost=glass["cost_per_sqm"], amount=round(q * glass["cost_per_sqm"], 2)))

    material_cost = sum(l["amount"] for l in lines if l["category"] != "labor")
    labor_cost = sum(l["amount"] for l in lines if l["category"] == "labor")
    waste_pct = to_float(S["waste_pct"], 0)
    waste_cost = sum(l["amount"] for l in lines if l["category"] in ("aluminum", "mesh", "glass")) * waste_pct / 100
    unit_cost = material_cost + waste_cost + labor_cost
    raw_price = unit_cost * (1 + p["markup_pct"] / 100)
    unit_price = max(raw_price, p["min_price"])
    rt = to_float(S["round_to"], 1) or 1
    unit_price = math.ceil(round(unit_price / rt, 6)) * rt

    parts = [f"{w_cm:g}×{h_cm:g} ซม."]
    if len(panel_opts) > 1 or panels > 1:
        parts.append(f"{panels} บาน")
    if divider:
        parts.append(f"ลูกฟัก {divider} เส้น")
    if p["preview"] in ("swing", "pleated") and panels == 1:
        parts.append("เปิดซ้าย" if direction == "left" else "เปิดขวา")
    if p["preview"] == "louver":
        parts.append(f"ใบระแนง {angle}°")
    if finish:
        parts.append(finish["name"])
    if glass:
        parts.append(glass["name"])

    return dict(
        product_slug=p["slug"], product_name=p["name"], category=p["category"],
        preview=p["preview"], infill=p["infill"],
        config=dict(slug=p["slug"], width=w_cm, height=h_cm, panels=panels, divider=divider,
                    direction=direction, angle=angle, finish_id=finish["id"] if finish else None,
                    glass_id=glass["id"] if glass else None, qty=qty),
        summary=" · ".join(parts), area=round(var["A"], 3), qty=qty,
        finish_name=finish["name"] if finish else "", finish_hex=finish["hex"] if finish else "#b8803f",
        finish_is_wood=finish["is_wood"] if finish else 1,
        glass_name=glass["name"] if glass else "", glass_hex=glass["hex"] if glass else "",
        lines=lines, material_cost=round(material_cost, 2), waste_pct=waste_pct, waste_cost=round(waste_cost, 2),
        labor_cost=round(labor_cost, 2), unit_cost=round(unit_cost, 2), markup_pct=p["markup_pct"],
        min_price=p["min_price"], raw_price=round(raw_price, 2), unit_price=unit_price,
        total_price=unit_price * qty, total_cost=round(unit_cost * qty, 2),
    )


PUBLIC_KEYS = ("product_slug", "product_name", "category", "preview", "infill", "config", "summary", "area",
               "qty", "finish_name", "finish_hex", "finish_is_wood", "glass_name", "glass_hex",
               "unit_price", "total_price")


def public_quote(q):
    return {k: q[k] for k in PUBLIC_KEYS}


def public_catalog():
    db = get_db()
    prods = db.execute("SELECT * FROM products WHERE active=1 ORDER BY sort, id").fetchall()
    order = {c: i for i, c in enumerate(CATEGORY_ORDER)}
    prods = sorted(prods, key=lambda p: (order.get(p["category"], 99), p["sort"], p["id"]))
    return dict(
        products=[dict(slug=p["slug"], name=p["name"], category=p["category"], description=p["description"],
                       preview=p["preview"], infill=p["infill"], panels=parse_panels(p["panel_options"]),
                       uses_glass=bool(p["uses_glass"]), has_divider=bool(p["has_divider"]),
                       min_w=p["min_w"], max_w=p["max_w"], min_h=p["min_h"], max_h=p["max_h"],
                       def_w=p["def_w"], def_h=p["def_h"]) for p in prods],
        finishes=[dict(id=f["id"], name=f["name"], hex=f["hex"], is_wood=f["is_wood"]) for f in
                  db.execute("SELECT * FROM finishes WHERE active=1 ORDER BY sort, id")],
        glass=[dict(id=x["id"], name=x["name"], hex=x["hex"]) for x in
               db.execute("SELECT * FROM glass_types WHERE active=1 ORDER BY sort, id")],
    )


def gen_order_code():
    db = get_db()
    while True:
        code = "AL" + datetime.datetime.now().strftime("%y%m%d") + "".join(
            secrets.choice(string.ascii_uppercase + string.digits) for _ in range(4))
        if not db.execute("SELECT 1 FROM orders WHERE code=?", (code,)).fetchone():
            return code


def digits(s):
    return re.sub(r"\D", "", s or "")


# ---------------------------------------------------------------------------
# Security helpers: CSRF + admin login
# ---------------------------------------------------------------------------
def csrf_token():
    if "_csrf" not in session:
        session["_csrf"] = secrets.token_hex(16)
    return session["_csrf"]


def csrf_field():
    return Markup(f'<input type="hidden" name="_csrf" value="{csrf_token()}">')


CSRF_EXEMPT = {"api_quote"}


@app.before_request
def csrf_protect():
    if request.method == "POST" and request.endpoint not in CSRF_EXEMPT:
        tok = request.form.get("_csrf") or request.headers.get("X-CSRF-Token") or ""
        if not hmac.compare_digest(tok, session.get("_csrf", "")):
            if request.is_json:
                return jsonify(ok=False, error="เซสชันหมดอายุ กรุณารีเฟรชหน้าเว็บ"), 400
            flash("เซสชันหมดอายุ กรุณาลองอีกครั้ง", "error")
            return redirect(request.url)


def admin_required(fn):
    @wraps(fn)
    def wrapper(*a, **kw):
        if not session.get("admin"):
            return redirect(url_for("admin_login", next=request.path))
        return fn(*a, **kw)
    return wrapper


@app.template_filter("money")
def money_filter(v):
    try:
        return f"{float(v):,.0f}"
    except (TypeError, ValueError):
        return "0"


@app.template_filter("num")
def num_filter(v, d=3):
    try:
        s = f"{float(v):,.{d}f}"
        return s.rstrip("0").rstrip(".") if "." in s else s
    except (TypeError, ValueError):
        return "0"


@app.context_processor
def inject_globals():
    return dict(S=get_settings(), STATUS=STATUS, csrf_field=csrf_field, csrf_token=csrf_token,
                is_admin=bool(session.get("admin")))


# ---------------------------------------------------------------------------
# Public routes
# ---------------------------------------------------------------------------
@app.get("/")
def home():
    catalog = public_catalog()
    from_price = {}
    for p in catalog["products"]:
        try:
            from_price[p["slug"]] = calc_quote({"slug": p["slug"], "width": p["min_w"], "height": p["min_h"]})["unit_price"]
        except QuoteError:
            pass
    return render_template("home.html", catalog=catalog, from_price=from_price, categories=CATEGORY_ORDER)


@app.get("/calculator")
def calculator():
    catalog = public_catalog()
    if not catalog["products"]:
        flash("ยังไม่มีสินค้าเปิดขาย", "error")
        return redirect(url_for("home"))
    return render_template("calculator.html", catalog=catalog)


@app.get("/cart")
def cart():
    return render_template("cart.html", catalog=public_catalog())


@app.post("/api/quote")
def api_quote():
    cfg = request.get_json(silent=True)
    if not isinstance(cfg, dict):
        return jsonify(ok=False, error="ข้อมูลไม่ถูกต้อง"), 400
    try:
        return jsonify(ok=True, quote=public_quote(calc_quote(cfg)))
    except QuoteError as e:
        return jsonify(ok=False, error=str(e)), 400


@app.post("/api/order")
def api_order():
    data = request.get_json(silent=True) or {}
    c = data.get("customer") if isinstance(data.get("customer"), dict) else {}
    name = str(c.get("name", "")).strip()[:120]
    phone = str(c.get("phone", "")).strip()[:30]
    if not name or len(digits(phone)) < 9:
        return jsonify(ok=False, error="กรุณากรอกชื่อและเบอร์โทรศัพท์ให้ถูกต้อง"), 400
    items = data.get("items")
    if not isinstance(items, list) or not 1 <= len(items) <= 50:
        return jsonify(ok=False, error="ไม่มีรายการสินค้าในตะกร้า"), 400
    quotes = []
    for i, cfg in enumerate(items, 1):
        if not isinstance(cfg, dict):
            return jsonify(ok=False, error=f"รายการที่ {i} ไม่ถูกต้อง"), 400
        try:
            quotes.append(calc_quote(cfg))
        except QuoteError as e:
            return jsonify(ok=False, error=f"รายการที่ {i}: {e}"), 400
    code = gen_order_code()
    db = get_db()
    db.execute("""INSERT INTO orders(code,created_at,customer_name,phone,email,address,note,items_json,
                  total_price,total_cost,status) VALUES(?,?,?,?,?,?,?,?,?,?, 'new')""",
               (code, datetime.datetime.now().strftime("%Y-%m-%d %H:%M"), name, phone,
                str(c.get("email", "")).strip()[:120], str(c.get("address", "")).strip()[:500],
                str(c.get("note", "")).strip()[:1000], json.dumps(quotes, ensure_ascii=False),
                sum(q["total_price"] for q in quotes), sum(q["total_cost"] for q in quotes)))
    db.commit()
    session["my_orders"] = (session.get("my_orders") or [])[-9:] + [code]
    return jsonify(ok=True, code=code, url=url_for("order_view", code=code))


def load_order_public(code):
    o = get_db().execute("SELECT * FROM orders WHERE code=?", (code,)).fetchone()
    if not o:
        return None, None
    return o, [public_quote(q) for q in json.loads(o["items_json"])]


@app.get("/order/<code>")
def order_view(code):
    if code not in (session.get("my_orders") or []):
        return redirect(url_for("track", code=code))
    o, items = load_order_public(code)
    if not o:
        abort(404)
    return render_template("order.html", o=o, items=items, flow=STATUS_FLOW, just_ordered=True)


@app.get("/track")
def track():
    code = request.args.get("code", "").strip().upper()
    phone = request.args.get("phone", "").strip()
    o = items = None
    error = None
    if code and phone:
        o, items = load_order_public(code)
        if not o or digits(o["phone"])[-9:] != digits(phone)[-9:]:
            o, items, error = None, None, "ไม่พบคำสั่งซื้อ กรุณาตรวจสอบเลขที่และเบอร์โทร"
    return render_template("track.html", code=code, phone=phone, o=o, items=items, error=error, flow=STATUS_FLOW)


# ---------------------------------------------------------------------------
# Admin routes
# ---------------------------------------------------------------------------
@app.route("/admin/login", methods=["GET", "POST"])
def admin_login():
    if request.method == "POST":
        u = request.form.get("username", "")
        pw = request.form.get("password", "")
        if hmac.compare_digest(u, ADMIN_USER) and hmac.compare_digest(pw, ADMIN_PASSWORD):
            session["admin"] = True
            nxt = request.args.get("next", "")
            return redirect(nxt if nxt.startswith("/admin") else url_for("admin_dashboard"))
        flash("ชื่อผู้ใช้หรือรหัสผ่านไม่ถูกต้อง", "error")
    return render_template("admin_login.html")


@app.get("/admin/logout")
def admin_logout():
    session.pop("admin", None)
    return redirect(url_for("home"))


@app.get("/admin")
@admin_required
def admin_dashboard():
    db = get_db()
    orders = db.execute("SELECT * FROM orders ORDER BY id DESC").fetchall()
    valid = [o for o in orders if o["status"] != "cancelled"]
    revenue = sum(o["total_price"] for o in valid)
    cost = sum(o["total_cost"] for o in valid)
    counts = {k: 0 for k in STATUS}
    for o in orders:
        counts[o["status"]] = counts.get(o["status"], 0) + 1
    top = {}
    for o in valid:
        for q in json.loads(o["items_json"]):
            t = top.setdefault(q["product_name"], {"qty": 0, "revenue": 0, "profit": 0})
            t["qty"] += q["qty"]
            t["revenue"] += q["total_price"]
            t["profit"] += q["total_price"] - q["total_cost"]
    top = sorted(top.items(), key=lambda kv: -kv[1]["revenue"])[:6]
    return render_template("admin_dashboard.html", orders=orders[:8], n_orders=len(orders), revenue=revenue,
                           cost=cost, counts=counts, top=top)


@app.get("/admin/orders")
@admin_required
def admin_orders():
    status = request.args.get("status", "")
    q = request.args.get("q", "").strip()
    sql, args = "SELECT * FROM orders WHERE 1=1", []
    if status in STATUS:
        sql += " AND status=?"
        args.append(status)
    if q:
        sql += " AND (code LIKE ? OR customer_name LIKE ? OR phone LIKE ?)"
        args += [f"%{q}%"] * 3
    rows = get_db().execute(sql + " ORDER BY id DESC", args).fetchall()
    orders = [dict(o, n_items=len(json.loads(o["items_json"]))) for o in rows]
    return render_template("admin_orders.html", orders=orders, status=status, q=q)


@app.route("/admin/orders/<int:oid>", methods=["GET", "POST"])
@admin_required
def admin_order(oid):
    db = get_db()
    o = db.execute("SELECT * FROM orders WHERE id=?", (oid,)).fetchone()
    if not o:
        abort(404)
    if request.method == "POST":
        if request.form.get("action") == "delete":
            db.execute("DELETE FROM orders WHERE id=?", (oid,))
            db.commit()
            flash(f"ลบคำสั่งซื้อ {o['code']} แล้ว", "ok")
            return redirect(url_for("admin_orders"))
        st = request.form.get("status")
        if st in STATUS:
            db.execute("UPDATE orders SET status=?, admin_note=? WHERE id=?",
                       (st, request.form.get("admin_note", "")[:2000], oid))
            db.commit()
            flash("บันทึกสถานะแล้ว", "ok")
        return redirect(url_for("admin_order", oid=oid))
    items = json.loads(o["items_json"])
    summary = {}
    for q in items:
        for l in q["lines"]:
            s = summary.setdefault(l["code"], {"name": l["name"], "unit": l["unit"], "qty": 0, "amount": 0})
            s["qty"] += l["qty"] * q["qty"]
            s["amount"] += l["amount"] * q["qty"]
    return render_template("admin_order.html", o=o, items=items, summary=summary)


@app.route("/admin/materials", methods=["GET", "POST"])
@admin_required
def admin_materials():
    db = get_db()
    if request.method == "POST":
        action = request.form.get("action")
        if action == "save":
            for m in db.execute("SELECT * FROM materials").fetchall():
                i = m["id"]
                if request.form.get(f"del_{i}"):
                    used = db.execute("SELECT COUNT(*) FROM bom WHERE material_code=?", (m["code"],)).fetchone()[0]
                    if used:
                        flash(f"ลบ {m['code']} ไม่ได้ เพราะยังถูกใช้ใน BOM {used} รายการ", "error")
                    else:
                        db.execute("DELETE FROM materials WHERE id=?", (i,))
                    continue
                cat = request.form.get(f"category_{i}", m["category"])
                db.execute("UPDATE materials SET name=?, unit=?, unit_cost=?, category=? WHERE id=?",
                           (request.form.get(f"name_{i}", m["name"]).strip() or m["name"],
                            request.form.get(f"unit_{i}", m["unit"]).strip() or m["unit"],
                            max(0.0, to_float(request.form.get(f"cost_{i}"), m["unit_cost"])),
                            cat if cat in MATERIAL_CATEGORIES else m["category"], i))
            db.commit()
            flash("บันทึกราคาวัสดุแล้ว — ราคาสินค้าทั้งหมดคำนวณใหม่อัตโนมัติ", "ok")
        elif action == "add":
            code = re.sub(r"[^A-Z0-9\-]", "", request.form.get("code", "").upper())
            name = request.form.get("name", "").strip()
            cat = request.form.get("category", "accessory")
            if not code or not name:
                flash("กรุณากรอกรหัสและชื่อวัสดุ", "error")
            elif db.execute("SELECT 1 FROM materials WHERE code=?", (code,)).fetchone():
                flash("รหัสวัสดุนี้มีอยู่แล้ว", "error")
            else:
                db.execute("INSERT INTO materials(code,name,unit,unit_cost,category) VALUES(?,?,?,?,?)",
                           (code, name, request.form.get("unit", "ชิ้น").strip() or "ชิ้น",
                            max(0.0, to_float(request.form.get("unit_cost"))),
                            cat if cat in MATERIAL_CATEGORIES else "accessory"))
                db.commit()
                flash(f"เพิ่มวัสดุ {code} แล้ว", "ok")
        return redirect(url_for("admin_materials"))
    mats = db.execute("""SELECT m.*, (SELECT COUNT(*) FROM bom b WHERE b.material_code=m.code) AS used
                         FROM materials m ORDER BY m.category, m.code""").fetchall()
    return render_template("admin_materials.html", mats=mats, cats=MATERIAL_CATEGORIES)


@app.route("/admin/products", methods=["GET", "POST"])
@admin_required
def admin_products():
    db = get_db()
    if request.method == "POST":
        slug = re.sub(r"[^a-z0-9\-]", "", request.form.get("slug", "").lower())
        name = request.form.get("name", "").strip()
        if not slug or not name:
            flash("กรุณากรอก slug และชื่อสินค้า", "error")
        elif db.execute("SELECT 1 FROM products WHERE slug=?", (slug,)).fetchone():
            flash("slug นี้ถูกใช้แล้ว", "error")
        else:
            cur = db.execute("INSERT INTO products(slug,name,category,active,sort) VALUES(?,?,?,0,99)",
                             (slug, name, request.form.get("category", "ประตู")))
            db.commit()
            flash("สร้างสินค้าแล้ว (ปิดการขายไว้ก่อน) — กรุณาเพิ่มสูตรวัสดุ", "ok")
            return redirect(url_for("admin_product", pid=cur.lastrowid))
        return redirect(url_for("admin_products"))
    prods = db.execute("""SELECT p.*, (SELECT COUNT(*) FROM bom b WHERE b.product_id=p.id) AS n_bom
                          FROM products p ORDER BY p.sort, p.id""").fetchall()
    rows = []
    for p in prods:
        r = dict(p)
        try:
            q = calc_quote({"slug": p["slug"], "width": p["def_w"], "height": p["def_h"]}, admin=True)
            r.update(sample_price=q["unit_price"], sample_cost=q["unit_cost"])
        except QuoteError as e:
            r.update(sample_error=str(e))
        rows.append(r)
    return render_template("admin_products.html", prods=rows, categories=CATEGORY_ORDER, previews=PREVIEW_TYPES)


@app.route("/admin/products/<int:pid>", methods=["GET", "POST"])
@admin_required
def admin_product(pid):
    db = get_db()
    p = db.execute("SELECT * FROM products WHERE id=?", (pid,)).fetchone()
    if not p:
        abort(404)
    codes = {m["code"] for m in db.execute("SELECT code FROM materials")}
    if request.method == "POST":
        if request.form.get("action") == "delete":
            db.execute("DELETE FROM products WHERE id=?", (pid,))
            db.commit()
            flash("ลบสินค้าแล้ว", "ok")
            return redirect(url_for("admin_products"))
        f = request.form
        errors = []
        min_w, max_w = to_float(f.get("min_w"), p["min_w"]), to_float(f.get("max_w"), p["max_w"])
        min_h, max_h = to_float(f.get("min_h"), p["min_h"]), to_float(f.get("max_h"), p["max_h"])
        if min_w <= 0 or min_h <= 0 or min_w > max_w or min_h > max_h:
            errors.append("ช่วงขนาดไม่ถูกต้อง")
        preview = f.get("preview") if f.get("preview") in PREVIEW_TYPES else p["preview"]
        infill = f.get("infill") if f.get("infill") in INFILL_TYPES else p["infill"]
        panel_options = ",".join(map(str, parse_panels(f.get("panel_options", ""))))
        bom_updates, bom_deletes, bom_new = [], [], []
        for b in db.execute("SELECT * FROM bom WHERE product_id=?", (pid,)).fetchall():
            i = b["id"]
            if f.get(f"b_del_{i}"):
                bom_deletes.append(i)
                continue
            code, formula = f.get(f"b_code_{i}", ""), f.get(f"b_formula_{i}", "").strip()
            err = validate_formula(formula)
            if code not in codes or err:
                errors.append(f"สูตรแถว {b['material_code']}: {err or 'ไม่พบรหัสวัสดุ'}")
            bom_updates.append((code, formula, f.get(f"b_note_{i}", "").strip(), to_int(f.get(f"b_sort_{i}")), i))
        for n in range(5):
            code, formula = f.get(f"n_code_{n}", ""), f.get(f"n_formula_{n}", "").strip()
            if not code and not formula:
                continue
            err = validate_formula(formula)
            if code not in codes or err:
                errors.append(f"แถวใหม่ {code or '-'}: {err or 'กรุณาเลือกวัสดุ'}")
            bom_new.append((pid, code, formula, f.get(f"n_note_{n}", "").strip(), to_int(f.get(f"n_sort_{n}"), 50)))
        if errors:
            for e in errors:
                flash(e, "error")
            return redirect(url_for("admin_product", pid=pid))
        db.execute("""UPDATE products SET name=?, category=?, description=?, preview=?, infill=?, panel_options=?,
                      uses_glass=?, has_divider=?, markup_pct=?, min_price=?, min_w=?, max_w=?, min_h=?, max_h=?,
                      def_w=?, def_h=?, sort=?, active=? WHERE id=?""",
                   (f.get("name", p["name"]).strip() or p["name"], f.get("category", p["category"]).strip() or p["category"],
                    f.get("description", "").strip(), preview, infill, panel_options,
                    1 if f.get("uses_glass") else 0, 1 if f.get("has_divider") else 0,
                    to_float(f.get("markup_pct"), p["markup_pct"]), max(0.0, to_float(f.get("min_price"), p["min_price"])),
                    min_w, max_w, min_h, max_h,
                    min(max(to_float(f.get("def_w"), min_w), min_w), max_w),
                    min(max(to_float(f.get("def_h"), min_h), min_h), max_h),
                    to_int(f.get("sort"), p["sort"]), 1 if f.get("active") else 0, pid))
        db.executemany("UPDATE bom SET material_code=?, formula=?, note=?, sort=? WHERE id=?", bom_updates)
        db.executemany("DELETE FROM bom WHERE id=?", [(i,) for i in bom_deletes])
        db.executemany("INSERT INTO bom(product_id,material_code,formula,note,sort) VALUES(?,?,?,?,?)", bom_new)
        db.commit()
        flash("บันทึกสินค้าและสูตรวัสดุแล้ว", "ok")
        return redirect(url_for("admin_product", pid=pid))

    bom = db.execute("SELECT * FROM bom WHERE product_id=? ORDER BY sort, id", (pid,)).fetchall()
    mats = db.execute("SELECT * FROM materials ORDER BY category, code").fetchall()
    finishes = db.execute("SELECT * FROM finishes ORDER BY sort, id").fetchall()
    glass = db.execute("SELECT * FROM glass_types ORDER BY sort, id").fetchall()
    a = request.args
    tcfg = dict(slug=p["slug"], width=a.get("t_w", p["def_w"]), height=a.get("t_h", p["def_h"]),
                panels=a.get("t_p", parse_panels(p["panel_options"])[0]), divider=a.get("t_d", 0),
                finish_id=a.get("t_f"), glass_id=a.get("t_g"), qty=1)
    test, test_error = None, None
    try:
        test = calc_quote(tcfg, admin=True)
    except QuoteError as e:
        test_error = str(e)
    return render_template("admin_product.html", p=p, bom=bom, mats=mats, finishes=finishes, glass=glass,
                           panels=parse_panels(p["panel_options"]), tcfg=tcfg, test=test, test_error=test_error,
                           previews=PREVIEW_TYPES, infills=INFILL_TYPES, fvars=FORMULA_VARS,
                           categories=CATEGORY_ORDER, cats=MATERIAL_CATEGORIES)


@app.route("/admin/options", methods=["GET", "POST"])
@admin_required
def admin_options():
    db = get_db()
    if request.method == "POST":
        f = request.form
        action = f.get("action")
        hexok = lambda h, d: h if re.fullmatch(r"#[0-9a-fA-F]{6}", h or "") else d  # noqa: E731
        if action == "save_finishes":
            for r in db.execute("SELECT * FROM finishes").fetchall():
                i = r["id"]
                db.execute("UPDATE finishes SET name=?, hex=?, is_wood=?, surcharge_pct=?, sort=?, active=? WHERE id=?",
                           (f.get(f"name_{i}", r["name"]).strip() or r["name"], hexok(f.get(f"hex_{i}"), r["hex"]),
                            1 if f.get(f"wood_{i}") else 0, to_float(f.get(f"sur_{i}"), r["surcharge_pct"]),
                            to_int(f.get(f"sort_{i}"), r["sort"]), 1 if f.get(f"active_{i}") else 0, i))
        elif action == "add_finish" and f.get("name", "").strip():
            db.execute("INSERT INTO finishes(name,hex,is_wood,surcharge_pct,sort) VALUES(?,?,?,?,99)",
                       (f["name"].strip(), hexok(f.get("hex"), "#b8803f"), 1 if f.get("is_wood") else 0,
                        to_float(f.get("surcharge_pct"))))
        elif action == "save_glass":
            for r in db.execute("SELECT * FROM glass_types").fetchall():
                i = r["id"]
                db.execute("UPDATE glass_types SET name=?, hex=?, cost_per_sqm=?, sort=?, active=? WHERE id=?",
                           (f.get(f"name_{i}", r["name"]).strip() or r["name"], hexok(f.get(f"hex_{i}"), r["hex"]),
                            max(0.0, to_float(f.get(f"cost_{i}"), r["cost_per_sqm"])),
                            to_int(f.get(f"sort_{i}"), r["sort"]), 1 if f.get(f"active_{i}") else 0, i))
        elif action == "add_glass" and f.get("name", "").strip():
            db.execute("INSERT INTO glass_types(name,hex,cost_per_sqm,sort) VALUES(?,?,?,99)",
                       (f["name"].strip(), hexok(f.get("hex"), "#cfe8f7"), max(0.0, to_float(f.get("cost_per_sqm")))))
        db.commit()
        flash("บันทึกแล้ว", "ok")
        return redirect(url_for("admin_options"))
    return render_template("admin_options.html",
                           finishes=db.execute("SELECT * FROM finishes ORDER BY sort, id").fetchall(),
                           glass=db.execute("SELECT * FROM glass_types ORDER BY sort, id").fetchall())


@app.route("/admin/settings", methods=["GET", "POST"])
@admin_required
def admin_settings():
    db = get_db()
    if request.method == "POST":
        for k in DEFAULT_SETTINGS:
            v = request.form.get(k, "").strip()
            if k in ("waste_pct", "round_to"):
                v = str(max(0.0, to_float(v, float(DEFAULT_SETTINGS[k])))).rstrip("0").rstrip(".") or "0"
            db.execute("INSERT INTO settings(key,value) VALUES(?,?) ON CONFLICT(key) DO UPDATE SET value=excluded.value",
                       (k, v))
        db.commit()
        flash("บันทึกการตั้งค่าแล้ว", "ok")
        return redirect(url_for("admin_settings"))
    return render_template("admin_settings.html")


# ---------------------------------------------------------------------------
# Templates (Tailwind CDN)
# ---------------------------------------------------------------------------
TEMPLATES = {}

TEMPLATES["base.html"] = r"""<!doctype html>
<html lang="th">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<meta name="csrf-token" content="{{ csrf_token() }}">
<title>{% block title %}{{ S.company_name }}{% endblock %}</title>
<link rel="preconnect" href="https://fonts.googleapis.com">
<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
<link href="https://fonts.googleapis.com/css2?family=Prompt:wght@300;400;500;600;700&display=swap" rel="stylesheet">
<script src="https://cdn.tailwindcss.com"></script>
<script>
  tailwind.config = { theme: { extend: {
    fontFamily: { sans: ['Prompt', 'ui-sans-serif', 'system-ui', 'sans-serif'] },
    colors: { wood: { 50: '#fbf7f1', 100: '#f4e9d8', 200: '#e8d0ad', 300: '#d9b07b', 400: '#c98f4f',
                      500: '#b07434', 600: '#8f5b28', 700: '#704623', 800: '#53341d', 900: '#3b2516' } }
  } } };
</script>
<style>
  .wood-tex { background-image: repeating-linear-gradient(176deg, rgba(0,0,0,.13) 0 2px, transparent 2px 9px),
                                repeating-linear-gradient(184deg, rgba(255,255,255,.10) 0 1px, transparent 1px 14px); }
  @media print { .no-print { display: none !important; } body { background: #fff !important; } .print-full { box-shadow: none !important; border: 0 !important; } }
</style>
{% block head %}{% endblock %}
</head>
<body class="bg-stone-50 text-stone-800 font-sans antialiased min-h-screen flex flex-col">
{% block nav %}
<header class="no-print sticky top-0 z-40 bg-white/90 backdrop-blur border-b border-stone-200">
  <div class="max-w-7xl mx-auto px-4 h-16 flex items-center justify-between gap-3">
    <a href="{{ url_for('home') }}" class="flex items-center gap-2 font-semibold text-lg shrink-0">
      <span class="w-9 h-9 rounded-lg bg-wood-500 wood-tex grid place-items-center text-white text-sm font-bold shadow-inner">AL</span>
      <span class="hidden sm:inline">{{ S.company_name }}</span>
    </a>
    <nav class="flex items-center gap-1 text-sm">
      <a href="{{ url_for('home') }}#products" class="hidden md:inline-flex px-3 py-2 rounded-lg hover:bg-stone-100">สินค้า</a>
      <a href="{{ url_for('calculator') }}" class="px-3 py-2 rounded-lg hover:bg-stone-100 font-medium text-wood-700">คำนวณราคา</a>
      <a href="{{ url_for('track') }}" class="hidden md:inline-flex px-3 py-2 rounded-lg hover:bg-stone-100">ติดตามงาน</a>
      {% if is_admin %}<a href="{{ url_for('admin_dashboard') }}" class="hidden md:inline-flex px-3 py-2 rounded-lg hover:bg-stone-100">หลังบ้าน</a>{% endif %}
      <a href="{{ url_for('cart') }}" class="relative ml-1 inline-flex items-center gap-2 px-3 py-2 rounded-lg bg-wood-600 text-white hover:bg-wood-700">
        <svg class="w-4 h-4" fill="none" stroke="currentColor" stroke-width="2" viewBox="0 0 24 24"><path d="M3 3h2l2.4 12.2a1 1 0 0 0 1 .8h9.7a1 1 0 0 0 1-.8L21 7H6"/><circle cx="9" cy="20" r="1.4"/><circle cx="18" cy="20" r="1.4"/></svg>
        ตะกร้า
        <span id="cartCount" class="hidden absolute -top-1.5 -right-1.5 min-w-[20px] h-5 px-1 rounded-full bg-red-500 text-[11px] grid place-items-center">0</span>
      </a>
    </nav>
  </div>
</header>
{% endblock %}

{% with msgs = get_flashed_messages(with_categories=true) %}{% if msgs %}
<div class="no-print max-w-7xl mx-auto w-full px-4 mt-4 space-y-2">
  {% for cat, m in msgs %}
  <div class="rounded-lg px-4 py-3 text-sm border {{ 'bg-red-50 border-red-200 text-red-700' if cat == 'error' else 'bg-emerald-50 border-emerald-200 text-emerald-800' }}">{{ m }}</div>
  {% endfor %}
</div>
{% endif %}{% endwith %}

<main class="flex-1">{% block content %}{% endblock %}</main>

{% block footer %}
<footer class="no-print mt-16 bg-stone-900 text-stone-300">
  <div class="max-w-7xl mx-auto px-4 py-10 grid md:grid-cols-3 gap-8 text-sm">
    <div>
      <div class="flex items-center gap-2 text-white font-semibold text-lg mb-2">
        <span class="w-8 h-8 rounded-lg bg-wood-500 wood-tex grid place-items-center text-xs">AL</span>{{ S.company_name }}
      </div>
      <p class="text-stone-400">{{ S.tagline }}</p>
    </div>
    <div>
      <div class="text-white font-medium mb-2">ติดต่อเรา</div>
      <p>โทร {{ S.phone }}</p><p>LINE {{ S.line_id }}</p><p class="text-stone-400 mt-1">{{ S.address }}</p>
    </div>
    <div>
      <div class="text-white font-medium mb-2">เมนู</div>
      <p><a class="hover:text-white" href="{{ url_for('calculator') }}">คำนวณราคาด้วยตัวเอง</a></p>
      <p><a class="hover:text-white" href="{{ url_for('track') }}">ติดตามสถานะงาน</a></p>
      <p><a class="hover:text-white" href="{{ url_for('admin_dashboard') }}">สำหรับเจ้าหน้าที่</a></p>
    </div>
  </div>
</footer>
{% endblock %}

<script>
const CSRF = document.querySelector('meta[name=csrf-token]').content;
const fmt = n => '฿' + Number(n || 0).toLocaleString('th-TH', { maximumFractionDigits: 0 });
const esc = s => String(s == null ? '' : s).replace(/[&<>"']/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' })[c]);
async function api(url, data) {
  const r = await fetch(url, { method: 'POST', headers: { 'Content-Type': 'application/json', 'X-CSRF-Token': CSRF }, body: JSON.stringify(data) });
  try { return await r.json(); } catch (e) { return { ok: false, error: 'เกิดข้อผิดพลาด (' + r.status + ')' }; }
}
const Cart = {
  key: 'alu_cart_v1',
  get() { try { return JSON.parse(localStorage.getItem(this.key)) || []; } catch (e) { return []; } },
  set(v) { try { localStorage.setItem(this.key, JSON.stringify(v)); } catch (e) {} updateBadge(); },
};
function updateBadge() {
  const el = document.getElementById('cartCount'); if (!el) return;
  const n = Cart.get().length; el.textContent = n; el.classList.toggle('hidden', n === 0); el.classList.toggle('grid', n > 0);
}
updateBadge();

/* ---------- ภาพตัวอย่างสินค้า (SVG) ---------- */
const ALU = (() => {
  let uid = 0;
  function shade(hex, amt) {
    let c = String(hex || '#b8803f').replace('#', '');
    if (c.length === 3) c = c.split('').map(x => x + x).join('');
    const n = parseInt(c, 16) || 0, rgb = [n >> 16, (n >> 8) & 255, n & 255];
    return '#' + rgb.map(v => Math.max(0, Math.min(255, Math.round(amt < 0 ? v * (1 + amt) : v + (255 - v) * amt))))
      .map(v => v.toString(16).padStart(2, '0')).join('');
  }
  function woodPattern(id, f, vertical) {
    const base = f.hex, tr = vertical ? ' patternTransform="rotate(90)"' : '';
    if (!f.is_wood) return `<pattern id="${id}" width="10" height="10" patternUnits="userSpaceOnUse"><rect width="10" height="10" fill="${base}"/></pattern>`;
    const d1 = shade(base, -0.3), d2 = shade(base, 0.2);
    let p = '';
    [4, 11, 17, 25, 31, 39, 46, 53].forEach((y, i) => {
      const a = i % 2 ? 2.5 : -2.5;
      p += `<path d="M0 ${y} Q20 ${y + a} 40 ${y} T80 ${y}" stroke="${i % 3 ? d1 : d2}" stroke-width="${i % 2 ? 0.7 : 1.3}" fill="none" opacity=".55"/>`;
    });
    return `<pattern id="${id}" width="80" height="58" patternUnits="userSpaceOnUse"${tr}><rect width="80" height="58" fill="${base}"/>${p}</pattern>`;
  }
  function draw(svg, o) {
    if (!svg || !o || !o.product) return;
    const pr = o.product, W = +o.W || 100, H = +o.H || 100, Pn = Math.max(1, +o.P || 1), D = +o.D || 0;
    const f = o.finish || { hex: '#b8803f', is_wood: 1 };
    const tint = (o.glass && o.glass.hex) || '#cfe8f7';
    const k = ++uid, I = { h: 'wh' + k, v: 'wv' + k, g: 'gl' + k, m: 'me' + k, s: 'ss' + k, p: 'pl' + k, q: 'pq' + k, edge: shade(f.hex, -0.5) };
    const S = 260 / Math.max(W, H), w = W * S, h = H * S, pad = 34, x0 = pad, y0 = pad;
    const ft = Math.max(5, Math.min(w, h) * 0.05);
    const defs = woodPattern(I.h, f, false) + woodPattern(I.v, f, true)
      + `<linearGradient id="${I.g}" x1="0" y1="0" x2="1" y2="1"><stop offset="0" stop-color="${shade(tint, 0.55)}" stop-opacity=".9"/><stop offset="1" stop-color="${tint}" stop-opacity=".95"/></linearGradient>`
      + `<pattern id="${I.m}" width="4" height="4" patternUnits="userSpaceOnUse"><rect width="4" height="4" fill="#eef2f6"/><path d="M0 0H4M0 0V4" stroke="#64748b" stroke-width=".5" opacity=".6"/></pattern>`
      + `<pattern id="${I.s}" width="3.5" height="3.5" patternUnits="userSpaceOnUse"><rect width="3.5" height="3.5" fill="#cbd5e1"/><path d="M0 0H3.5M0 0V3.5" stroke="#334155" stroke-width=".8"/></pattern>`
      + `<pattern id="${I.p}" width="6" height="10" patternUnits="userSpaceOnUse"><rect width="6" height="10" fill="#f1f5f9"/><path d="M0 0V10" stroke="#94a3b8" stroke-width=".8"/><path d="M3 0V10" stroke="#e2e8f0" stroke-width="1.2"/></pattern>`
      + `<pattern id="${I.q}" width="6" height="6" patternUnits="userSpaceOnUse"><rect width="6" height="6" fill="#cbd5e1"/><path d="M0 0V6" stroke="#475569" stroke-width="1"/><path d="M0 3H6" stroke="#64748b" stroke-width=".5"/></pattern>`;
    const E = `stroke="${I.edge}" stroke-width=".6"`;
    const frame = (x, y, fw, fh, t) =>
      `<rect x="${x}" y="${y}" width="${fw}" height="${t}" fill="url(#${I.h})" ${E}/>` +
      `<rect x="${x}" y="${y + fh - t}" width="${fw}" height="${t}" fill="url(#${I.h})" ${E}/>` +
      `<rect x="${x}" y="${y + t}" width="${t}" height="${fh - 2 * t}" fill="url(#${I.v})" ${E}/>` +
      `<rect x="${x + fw - t}" y="${y + t}" width="${t}" height="${fh - 2 * t}" fill="url(#${I.v})" ${E}/>`;
    const infill = (x, y, iw, ih) => {
      if (iw <= 0 || ih <= 0) return '';
      if (pr.infill === 'glass') return `<rect x="${x}" y="${y}" width="${iw}" height="${ih}" fill="url(#${I.g})"/>`
        + `<path d="M${x + iw * .18} ${y + ih * .82} L${x + iw * .55} ${y + ih * .18}" stroke="#fff" stroke-opacity=".55" stroke-width="2"/>`
        + `<path d="M${x + iw * .34} ${y + ih * .86} L${x + iw * .7} ${y + ih * .26}" stroke="#fff" stroke-opacity=".3" stroke-width="1"/>`;
      const pat = { mesh: I.m, ss: I.s, pleat: I.p, pleat_safe: I.q }[pr.infill] || I.m;
      return `<rect x="${x}" y="${y}" width="${iw}" height="${ih}" fill="url(#${pat})"/>`;
    };
    let b = `<rect x="${x0 + 3}" y="${y0 + 4}" width="${w}" height="${h}" fill="#000" opacity=".08" rx="2"/>`;
    const ix = x0 + ft, iy = y0 + ft, iw = w - 2 * ft, ih = h - 2 * ft;
    if (pr.preview === 'louver') {
      b += `<rect x="${ix}" y="${iy}" width="${iw}" height="${ih}" fill="#dbeafe"/>`;
      const n = Math.max(1, Math.round(ih / (10 * S))), step = ih / n;
      const ang = (o.angle == null ? 45 : +o.angle) * Math.PI / 180;
      const th = Math.max(1.2, step * 0.98 * Math.cos(ang));
      for (let i = 0; i < n; i++) {
        const cy = iy + step * (i + 0.5);
        b += `<rect x="${ix}" y="${cy - th / 2}" width="${iw}" height="${th}" fill="url(#${I.h})" stroke="${I.edge}" stroke-width=".4"/>`;
        b += `<rect x="${ix}" y="${cy + th / 2 - Math.min(1, th / 3)}" width="${iw}" height="${Math.min(1, th / 3)}" fill="#000" opacity=".18"/>`;
      }
      b += frame(x0, y0, w, h, ft);
    } else if (pr.preview === 'pleated') {
      b += infill(ix, iy, iw, ih);
      const bar = Math.max(3, ft * 0.8);
      if (Pn >= 2) {
        b += `<rect x="${ix + iw / 2 - bar / 2}" y="${iy}" width="${bar}" height="${ih}" fill="url(#${I.v})" ${E}/>`;
        b += `<rect x="${ix}" y="${iy}" width="${bar * 1.3}" height="${ih}" fill="url(#${I.v})" ${E}/><rect x="${ix + iw - bar * 1.3}" y="${iy}" width="${bar * 1.3}" height="${ih}" fill="url(#${I.v})" ${E}/>`;
      } else {
        const right = o.dir === 'right';
        b += `<rect x="${right ? ix + iw - bar * 1.3 : ix}" y="${iy}" width="${bar * 1.3}" height="${ih}" fill="url(#${I.v})" ${E}/>`;
        b += `<rect x="${right ? ix : ix + iw - bar}" y="${iy}" width="${bar}" height="${ih}" fill="url(#${I.v})" ${E}/>`;
        b += `<rect x="${(right ? ix + bar / 2 : ix + iw - bar / 2) - 1.2}" y="${iy + ih / 2 - 8}" width="2.4" height="16" rx="1" fill="#1f2937"/>`;
      }
      b += frame(x0, y0, w, h, ft);
    } else {
      b += frame(x0, y0, w, h, ft);
      const pw = iw / Pn, st = Math.max(3.5, ft * 0.75);
      for (let i = 0; i < Pn; i++) {
        const px = ix + i * pw, py = iy, ph = ih;
        b += infill(px + st, py + st, pw - 2 * st, ph - 2 * st);
        for (let d = 1; d <= D; d++) {
          const dy = py + ph * d / (D + 1);
          b += `<rect x="${px + st}" y="${dy - st * 0.35}" width="${pw - 2 * st}" height="${st * 0.7}" fill="url(#${I.h})" ${E}/>`;
        }
        b += frame(px, py, pw, ph, st);
        if (pr.preview === 'sliding') {
          const cx = px + pw / 2, ay = py + ph - st - 12, r = i % 2 === 0;
          const tip = r ? cx + 10 : cx - 10, back = r ? -4 : 4;
          b += `<path d="M${cx - 10} ${ay}H${cx + 10}M${tip} ${ay}l${back} -3M${tip} ${ay}l${back} 3" stroke="#1e293b" stroke-opacity=".55" stroke-width="1.5" stroke-linecap="round" fill="none"/>`;
          const hx = r ? px + pw - st / 2 : px + st / 2;
          b += `<rect x="${hx - 1.2}" y="${py + ph / 2 - 9}" width="2.4" height="18" rx="1" fill="#1f2937"/>`;
        } else {
          const hingeLeft = Pn === 1 ? o.dir !== 'right' : i < Pn / 2;
          const hx = hingeLeft ? px + st : px + pw - st, ox = hingeLeft ? px + pw - st : px + st;
          b += `<path d="M${ox} ${py + st}L${hx} ${py + ph / 2}L${ox} ${py + ph - st}" fill="none" stroke="${I.edge}" stroke-dasharray="4 3" stroke-width="1" opacity=".7"/>`;
          const hdx = hingeLeft ? px + pw - st / 2 : px + st / 2;
          b += `<rect x="${hdx - 1.2}" y="${py + ph / 2 - 8}" width="2.4" height="16" rx="1" fill="#1f2937"/>`;
        }
      }
    }
    const dy = y0 + h + 16, dx = x0 + w + 16;
    b += `<g stroke="#94a3b8" stroke-width=".8"><path d="M${x0} ${dy}H${x0 + w}M${x0} ${dy - 4}V${dy + 4}M${x0 + w} ${dy - 4}V${dy + 4}"/>`
      + `<path d="M${dx} ${y0}V${y0 + h}M${dx - 4} ${y0}H${dx + 4}M${dx - 4} ${y0 + h}H${dx + 4}"/></g>`
      + `<text x="${x0 + w / 2}" y="${dy + 14}" text-anchor="middle" font-size="11" fill="#64748b" font-family="Prompt,sans-serif">${W} ซม.</text>`
      + `<text x="${dx + 12}" y="${y0 + h / 2}" text-anchor="middle" font-size="11" fill="#64748b" font-family="Prompt,sans-serif" transform="rotate(90 ${dx + 12} ${y0 + h / 2})">${H} ซม.</text>`;
    svg.setAttribute('viewBox', `0 0 ${w + pad * 2} ${h + pad * 2}`);
    svg.setAttribute('preserveAspectRatio', 'xMidYMid meet');
    svg.innerHTML = `<defs>${defs}</defs>${b}`;
  }
  /* วาดจากข้อมูลใบเสนอราคา (quote) ที่เก็บในคำสั่งซื้อ */
  function drawQuote(svg, q) {
    const c = q.config || {};
    draw(svg, { product: { preview: q.preview, infill: q.infill }, W: c.width, H: c.height, P: c.panels, D: c.divider,
      dir: c.direction, angle: c.angle, finish: { hex: q.finish_hex, is_wood: q.finish_is_wood }, glass: q.glass_hex ? { hex: q.glass_hex } : null });
  }
  return { draw, drawQuote, shade };
})();
</script>
{% block scripts %}{% endblock %}
</body>
</html>
"""

TEMPLATES["home.html"] = r"""{% extends "base.html" %}
{% block content %}
<section class="relative overflow-hidden bg-gradient-to-br from-wood-800 via-wood-700 to-wood-900 text-white">
  <div class="absolute inset-0 wood-tex opacity-40"></div>
  <div class="relative max-w-7xl mx-auto px-4 py-16 md:py-24 grid md:grid-cols-2 gap-10 items-center">
    <div>
      <span class="inline-block px-3 py-1 rounded-full bg-white/10 text-wood-100 text-sm mb-4">ผลิตตามขนาดจริง · ติดตั้งโดยทีมช่างของร้าน</span>
      <h1 class="text-3xl md:text-5xl font-semibold leading-tight">อลูมิเนียมลายไม้<br>สวยเหมือนไม้จริง <span class="text-wood-200">ทนกว่าไม้จริง</span></h1>
      <p class="mt-5 text-wood-100/90 text-lg">{{ S.tagline }} — คำนวณราคาได้เองออนไลน์ เลือกรูปแบบ สี และขนาด รู้ราคาทันทีไม่ต้องรอช่าง</p>
      <div class="mt-8 flex flex-wrap gap-3">
        <a href="{{ url_for('calculator') }}" class="px-6 py-3 rounded-xl bg-white text-wood-800 font-semibold hover:bg-wood-50 shadow-lg">คำนวณราคาเลย →</a>
        <a href="#products" class="px-6 py-3 rounded-xl border border-white/30 hover:bg-white/10">ดูสินค้าทั้งหมด</a>
      </div>
    </div>
    <div class="bg-white/10 rounded-3xl p-6 backdrop-blur border border-white/10">
      <svg id="heroPreview" class="w-full h-72"></svg>
    </div>
  </div>
</section>

<section class="max-w-7xl mx-auto px-4 -mt-8 relative z-10">
  <div class="grid grid-cols-2 md:grid-cols-4 gap-3">
    {% for t, d in [('ไม่ผุ ไม่บวม', 'ไม่มีปัญหาปลวก ทนความชื้น'), ('ผลิตตามขนาด', 'วัดหน้างานจริงก่อนผลิต'), ('ราคาโปร่งใส', 'คำนวณเองได้ทุกรายการ'), ('รับประกันงาน', 'อุปกรณ์และการติดตั้ง')] %}
    <div class="bg-white rounded-2xl border border-stone-200 p-4 shadow-sm"><div class="font-semibold text-wood-700">{{ t }}</div><div class="text-sm text-stone-500">{{ d }}</div></div>
    {% endfor %}
  </div>
</section>

<section id="products" class="max-w-7xl mx-auto px-4 pt-16">
  <div class="flex items-end justify-between mb-6 gap-4">
    <div><h2 class="text-2xl md:text-3xl font-semibold">สินค้าของเรา</h2><p class="text-stone-500 mt-1">คลิกที่สินค้าเพื่อปรับแบบและคำนวณราคา</p></div>
  </div>
  {% for cat in categories %}{% set items = catalog.products | selectattr('category', 'equalto', cat) | list %}{% if items %}
  <h3 class="mt-8 mb-3 font-semibold text-lg flex items-center gap-2"><span class="w-1.5 h-5 rounded bg-wood-500"></span>{{ cat }}</h3>
  <div class="grid sm:grid-cols-2 lg:grid-cols-3 xl:grid-cols-4 gap-4">
    {% for p in items %}
    <a href="{{ url_for('calculator', product=p.slug) }}" class="group bg-white rounded-2xl border border-stone-200 overflow-hidden hover:shadow-lg hover:border-wood-300 transition">
      <div class="bg-gradient-to-b from-sky-50 to-stone-100 p-3"><svg data-preview="{{ p.slug }}" class="w-full h-44"></svg></div>
      <div class="p-4">
        <div class="font-medium group-hover:text-wood-700">{{ p.name }}</div>
        <p class="text-sm text-stone-500 mt-1 line-clamp-2">{{ p.description }}</p>
        <div class="mt-3 flex items-center justify-between">
          {% if from_price.get(p.slug) %}<span class="text-sm">เริ่มต้น <b class="text-wood-700 text-base">฿{{ from_price[p.slug]|money }}</b></span>{% else %}<span></span>{% endif %}
          <span class="text-sm text-wood-700">คำนวณราคา →</span>
        </div>
      </div>
    </a>
    {% endfor %}
  </div>
  {% endif %}{% endfor %}
</section>

<section class="max-w-7xl mx-auto px-4 pt-16">
  <h2 class="text-2xl md:text-3xl font-semibold mb-6">สั่งง่าย 4 ขั้นตอน</h2>
  <div class="grid md:grid-cols-4 gap-4">
    {% for t, d in [('เลือกสินค้า', 'ประตู หน้าต่าง ระแนง หรือมุ้งแบบที่ต้องการ'), ('ใส่ขนาดและปรับแบบ', 'กว้าง × สูง จำนวนบาน สีลายไม้ กระจก'), ('ส่งคำสั่งซื้อ', 'รู้ราคาทันที เพิ่มหลายรายการในตะกร้าได้'), ('วัดหน้างานและติดตั้ง', 'ช่างยืนยันขนาดจริงก่อนผลิตทุกครั้ง')] %}
    <div class="bg-white rounded-2xl border border-stone-200 p-5">
      <div class="w-10 h-10 rounded-full bg-wood-600 text-white grid place-items-center font-semibold">{{ loop.index }}</div>
      <div class="mt-3 font-semibold">{{ t }}</div><div class="text-sm text-stone-500 mt-1">{{ d }}</div>
    </div>
    {% endfor %}
  </div>
</section>
{% endblock %}
{% block scripts %}
<script>
const CAT = {{ catalog|tojson }};
const F0 = CAT.finishes[0], G0 = CAT.glass[0];
CAT.products.forEach(p => {
  document.querySelectorAll(`[data-preview="${p.slug}"]`).forEach(svg =>
    ALU.draw(svg, { product: p, W: p.def_w, H: p.def_h, P: p.panels[p.panels.length > 1 ? 1 : 0], D: 0, angle: 35, finish: F0, glass: G0 }));
});
const hero = CAT.products.find(p => p.preview === 'sliding' && p.uses_glass) || CAT.products[0];
if (hero) ALU.draw(document.getElementById('heroPreview'), { product: hero, W: 240, H: 220, P: 3, D: 1, finish: CAT.finishes[0], glass: G0 });
</script>
{% endblock %}
"""

TEMPLATES["calculator.html"] = r"""{% extends "base.html" %}
{% block title %}คำนวณราคา · {{ S.company_name }}{% endblock %}
{% block content %}
<div class="max-w-7xl mx-auto px-4 py-8">
  <div class="mb-6">
    <h1 class="text-2xl md:text-3xl font-semibold">คำนวณราคาด้วยตัวเอง</h1>
    <p class="text-stone-500 mt-1">เลือกสินค้า ใส่ขนาด และปรับแต่งรูปแบบ ระบบจะคำนวณราคาให้ทันที</p>
  </div>
  <div id="editBanner" class="hidden mb-4 rounded-xl bg-amber-50 border border-amber-200 text-amber-800 px-4 py-3 text-sm">
    กำลังแก้ไขรายการในตะกร้า — ปรับแบบแล้วกด <b>บันทึกการแก้ไข</b> · <a href="{{ url_for('cart') }}" class="underline">กลับไปตะกร้า</a>
  </div>
  <div class="grid lg:grid-cols-5 gap-6">
    <div class="lg:col-span-3 space-y-5">
      <section class="bg-white rounded-2xl border border-stone-200 p-5">
        <h2 class="font-semibold mb-4 flex items-center gap-2"><span class="w-7 h-7 rounded-full bg-wood-600 text-white grid place-items-center text-sm">1</span>เลือกสินค้า</h2>
        <div id="productPicker" class="space-y-4"></div>
        <p id="prodDesc" class="text-sm text-stone-500 mt-4"></p>
      </section>

      <section class="bg-white rounded-2xl border border-stone-200 p-5">
        <h2 class="font-semibold mb-4 flex items-center gap-2"><span class="w-7 h-7 rounded-full bg-wood-600 text-white grid place-items-center text-sm">2</span>ขนาด (เซนติเมตร)</h2>
        <div class="grid sm:grid-cols-2 gap-5">
          <div>
            <label class="text-sm font-medium">ความกว้าง</label>
            <div class="flex items-center gap-2 mt-1">
              <input id="inW" type="number" step="1" class="w-full rounded-lg border border-stone-300 px-3 py-2 focus:ring-2 focus:ring-wood-300 focus:border-wood-500 outline-none">
              <span class="text-sm text-stone-500">ซม.</span>
            </div>
            <input id="rgW" type="range" class="w-full mt-3 accent-amber-700">
            <div class="flex justify-between text-xs text-stone-400"><span id="minW"></span><span id="maxW"></span></div>
          </div>
          <div>
            <label class="text-sm font-medium">ความสูง</label>
            <div class="flex items-center gap-2 mt-1">
              <input id="inH" type="number" step="1" class="w-full rounded-lg border border-stone-300 px-3 py-2 focus:ring-2 focus:ring-wood-300 focus:border-wood-500 outline-none">
              <span class="text-sm text-stone-500">ซม.</span>
            </div>
            <input id="rgH" type="range" class="w-full mt-3 accent-amber-700">
            <div class="flex justify-between text-xs text-stone-400"><span id="minH"></span><span id="maxH"></span></div>
          </div>
        </div>
        <p class="text-xs text-stone-500 mt-3">💡 วัดขนาดช่องเปิดจริง (กว้าง × สูง) ช่างจะวัดยืนยันอีกครั้งก่อนผลิต</p>
      </section>

      <section class="bg-white rounded-2xl border border-stone-200 p-5 space-y-5">
        <h2 class="font-semibold flex items-center gap-2"><span class="w-7 h-7 rounded-full bg-wood-600 text-white grid place-items-center text-sm">3</span>รูปแบบ</h2>
        <div id="panelsBox"><div class="text-sm font-medium mb-2">จำนวนบาน</div><div id="panelsBtns" class="flex flex-wrap gap-2"></div></div>
        <div id="dividerBox"><div class="text-sm font-medium mb-2">ลูกฟักแนวนอน (เส้นแบ่งต่อบาน)</div><div id="dividerBtns" class="flex flex-wrap gap-2"></div></div>
        <div id="directionBox"><div class="text-sm font-medium mb-2">ทิศทางการเปิด</div><div id="directionBtns" class="flex flex-wrap gap-2"></div></div>
        <div id="angleBox">
          <div class="text-sm font-medium mb-2">องศาใบระแนง <span id="angleVal" class="text-wood-700"></span> <span class="text-stone-400 font-normal">(ดูตัวอย่าง — ปรับได้จริงหลังติดตั้ง)</span></div>
          <input id="rgAngle" type="range" min="0" max="90" step="5" class="w-full accent-amber-700">
          <div class="flex justify-between text-xs text-stone-400"><span>0° ปิดทึบ</span><span>90° เปิดสุด</span></div>
        </div>
      </section>

      <section class="bg-white rounded-2xl border border-stone-200 p-5 space-y-5">
        <h2 class="font-semibold flex items-center gap-2"><span class="w-7 h-7 rounded-full bg-wood-600 text-white grid place-items-center text-sm">4</span>สี / ลายไม้ และวัสดุ</h2>
        <div id="finishBtns" class="grid grid-cols-2 sm:grid-cols-4 gap-2"></div>
        <div id="glassBox"><div class="text-sm font-medium mb-2">ชนิดกระจก</div><div id="glassBtns" class="grid sm:grid-cols-2 gap-2"></div></div>
      </section>
    </div>

    <div class="lg:col-span-2">
      <div class="lg:sticky lg:top-20 space-y-4">
        <div class="bg-white rounded-2xl border border-stone-200 p-5">
          <div class="flex items-start justify-between gap-2">
            <h3 id="pvName" class="font-semibold"></h3><span id="pvCat" class="text-xs px-2 py-1 rounded-full bg-wood-50 text-wood-700 shrink-0"></span>
          </div>
          <div class="mt-3 rounded-xl bg-gradient-to-b from-sky-50 to-stone-100 p-2"><svg id="preview" class="w-full h-72"></svg></div>
          <p id="pvSummary" class="text-sm text-stone-500 mt-3"></p>
        </div>
        <div class="bg-stone-900 text-white rounded-2xl p-5">
          <div class="flex items-center justify-between">
            <span class="text-stone-300 text-sm">จำนวน (ชุด)</span>
            <div class="flex items-center rounded-lg bg-white/10">
              <button id="qtyMinus" type="button" class="w-9 h-9 hover:bg-white/10 rounded-l-lg">−</button>
              <input id="inQty" type="number" min="1" max="999" class="w-14 bg-transparent text-center outline-none">
              <button id="qtyPlus" type="button" class="w-9 h-9 hover:bg-white/10 rounded-r-lg">+</button>
            </div>
          </div>
          <div class="mt-4 flex justify-between text-sm text-stone-300"><span>ราคาต่อชุด</span><span id="unitPrice">—</span></div>
          <div class="mt-1 flex items-end justify-between">
            <span class="text-stone-300 text-sm">ราคารวม</span>
            <span id="totalPrice" class="text-3xl font-semibold transition-opacity">—</span>
          </div>
          <p id="quoteErr" class="hidden mt-3 text-sm text-red-300"></p>
          <button id="addBtn" type="button" class="mt-5 w-full py-3 rounded-xl bg-wood-500 hover:bg-wood-400 font-semibold disabled:opacity-40 disabled:cursor-not-allowed">เพิ่มลงตะกร้า</button>
          <p class="text-xs text-stone-400 mt-3">* ราคาประเมินเบื้องต้น รวมค่าวัสดุ ค่าผลิต และค่าติดตั้งในพื้นที่บริการ ราคาจริงยืนยันหลังวัดหน้างาน</p>
        </div>
      </div>
    </div>
  </div>
</div>
<div id="toast" class="hidden fixed bottom-6 left-1/2 -translate-x-1/2 z-50 bg-stone-900 text-white rounded-xl shadow-xl px-5 py-3 text-sm flex items-center gap-4">
  <span>✓ เพิ่มลงตะกร้าแล้ว</span><a href="{{ url_for('cart') }}" class="font-semibold text-wood-200 underline">ดูตะกร้า</a>
</div>
{% endblock %}
{% block scripts %}
<script>
const CAT = {{ catalog|tojson }};
const CART_URL = {{ url_for('cart')|tojson }};
const $ = id => document.getElementById(id);
const P_BY = Object.fromEntries(CAT.products.map(p => [p.slug, p]));
const clamp = (v, a, b) => Math.min(b, Math.max(a, v));
const qs = new URLSearchParams(location.search);
let editIdx = qs.has('edit') ? parseInt(qs.get('edit'), 10) : null;
const first = P_BY[qs.get('product')] || CAT.products[0];
let st = { slug: first.slug, width: first.def_w, height: first.def_h, panels: first.panels[0], divider: 0, direction: 'left',
  angle: 45, finish_id: CAT.finishes[0] ? CAT.finishes[0].id : null, glass_id: CAT.glass[0] ? CAT.glass[0].id : null, qty: 1 };
if (editIdx !== null) {
  const it = Cart.get()[editIdx];
  if (it && it.cfg && P_BY[it.cfg.slug]) {
    Object.assign(st, it.cfg);
    $('editBanner').classList.remove('hidden');
    $('addBtn').textContent = 'บันทึกการแก้ไข';
  } else editIdx = null;
}
if (!CAT.finishes.some(f => f.id === st.finish_id) && CAT.finishes[0]) st.finish_id = CAT.finishes[0].id;
if (!CAT.glass.some(g => g.id === st.glass_id) && CAT.glass[0]) st.glass_id = CAT.glass[0].id;

const prod = () => P_BY[st.slug];
const btnCls = on => 'px-3 py-2 rounded-lg border text-sm transition text-left ' +
  (on ? 'border-wood-600 bg-wood-50 text-wood-800 ring-2 ring-wood-200' : 'border-stone-200 hover:border-wood-300 bg-white');
function buttons(el, opts, cur, onPick) {
  el.innerHTML = opts.map(([v, label]) => `<button type="button" data-v="${esc(v)}" class="${btnCls(String(v) === String(cur))}">${label}</button>`).join('');
  el.querySelectorAll('button').forEach(b => b.onclick = () => onPick(b.dataset.v));
}

function renderPicker() {
  const cats = [...new Set(CAT.products.map(p => p.category))];
  $('productPicker').innerHTML = cats.map(c => `<div><div class="text-xs font-medium text-stone-500 mb-2">${esc(c)}</div><div class="flex flex-wrap gap-2">` +
    CAT.products.filter(p => p.category === c).map(p => `<button type="button" data-slug="${p.slug}" class="${btnCls(p.slug === st.slug)}">${esc(p.name)}</button>`).join('') +
    `</div></div>`).join('');
  $('productPicker').querySelectorAll('button').forEach(b => b.onclick = () => selectProduct(b.dataset.slug));
  $('prodDesc').textContent = prod().description || '';
}
function selectProduct(slug) {
  const p = P_BY[slug]; if (!p) return;
  st.slug = slug;
  st.width = clamp(+st.width || p.def_w, p.min_w, p.max_w);
  st.height = clamp(+st.height || p.def_h, p.min_h, p.max_h);
  if (!p.panels.includes(+st.panels)) st.panels = p.panels[0];
  if (!p.has_divider) st.divider = 0;
  if (editIdx === null) history.replaceState(null, '', '?product=' + slug);
  renderAll();
}
function renderDims() {
  const p = prod();
  [['W', 'width', 'min_w', 'max_w'], ['H', 'height', 'min_h', 'max_h']].forEach(([k, key, mn, mx]) => {
    $('in' + k).min = $('rg' + k).min = p[mn]; $('in' + k).max = $('rg' + k).max = p[mx];
    $('in' + k).value = st[key]; $('rg' + k).value = st[key];
    $('min' + k).textContent = p[mn] + ' ซม.'; $('max' + k).textContent = p[mx] + ' ซม.';
  });
}
function renderOptions() {
  const p = prod();
  $('panelsBox').classList.toggle('hidden', p.panels.length < 2);
  buttons($('panelsBtns'), p.panels.map(n => [n, n + ' บาน']), st.panels, v => { st.panels = +v; renderOptions(); update(); });
  $('dividerBox').classList.toggle('hidden', !p.has_divider);
  buttons($('dividerBtns'), [[0, 'ไม่มี'], [1, '1 เส้น'], [2, '2 เส้น'], [3, '3 เส้น']], st.divider, v => { st.divider = +v; renderOptions(); update(); });
  const showDir = (p.preview === 'swing' || p.preview === 'pleated') && +st.panels === 1;
  $('directionBox').classList.toggle('hidden', !showDir);
  const dl = p.preview === 'pleated' ? [['left', 'เก็บมุ้งฝั่งซ้าย'], ['right', 'เก็บมุ้งฝั่งขวา']] : [['left', 'บานพับซ้าย'], ['right', 'บานพับขวา']];
  buttons($('directionBtns'), dl, st.direction, v => { st.direction = v; renderOptions(); update(); });
  $('angleBox').classList.toggle('hidden', p.preview !== 'louver');
  $('rgAngle').value = st.angle; $('angleVal').textContent = st.angle + '°';
  $('glassBox').classList.toggle('hidden', !p.uses_glass);
  buttons($('glassBtns'), CAT.glass.map(g => [g.id, `<span class="inline-flex items-center gap-2"><span class="w-5 h-5 rounded border border-stone-300" style="background:${g.hex}"></span>${esc(g.name)}</span>`]),
    st.glass_id, v => { st.glass_id = +v; renderOptions(); update(); });
}
function renderFinishes() {
  $('finishBtns').innerHTML = CAT.finishes.map(f => `<button type="button" data-id="${f.id}" class="${btnCls(f.id === st.finish_id)} flex items-center gap-2">
    <span class="w-8 h-8 rounded-md border border-black/10 shrink-0 ${f.is_wood ? 'wood-tex' : ''}" style="background-color:${f.hex}"></span>
    <span class="leading-tight">${esc(f.name)}</span></button>`).join('');
  $('finishBtns').querySelectorAll('button').forEach(b => b.onclick = () => { st.finish_id = +b.dataset.id; renderFinishes(); update(); });
}
function renderAll() { renderPicker(); renderDims(); renderOptions(); renderFinishes(); update(); }

function drawPreview() {
  const p = prod();
  ALU.draw($('preview'), { product: p, W: st.width, H: st.height, P: st.panels, D: st.divider, dir: st.direction, angle: st.angle,
    finish: CAT.finishes.find(f => f.id === st.finish_id), glass: p.uses_glass ? CAT.glass.find(g => g.id === st.glass_id) : null });
  $('pvName').textContent = p.name; $('pvCat').textContent = p.category;
}
let qTimer = null, qSeq = 0, lastQuote = null;
function update() {
  drawPreview();
  $('inQty').value = st.qty;
  $('totalPrice').classList.add('opacity-40');
  $('addBtn').disabled = true;
  clearTimeout(qTimer); qTimer = setTimeout(doQuote, 220);
}
async function doQuote() {
  const seq = ++qSeq;
  let r;
  try { r = await api('/api/quote', st); } catch (e) { r = { ok: false, error: 'เชื่อมต่อไม่ได้ กรุณาลองใหม่' }; }
  if (seq !== qSeq) return;
  $('totalPrice').classList.remove('opacity-40');
  if (r.ok) {
    lastQuote = r.quote;
    $('unitPrice').textContent = fmt(r.quote.unit_price);
    $('totalPrice').textContent = fmt(r.quote.total_price);
    $('pvSummary').textContent = r.quote.summary + ` · พื้นที่ ${r.quote.area.toFixed(2)} ตร.ม.`;
    $('quoteErr').classList.add('hidden'); $('addBtn').disabled = false;
  } else {
    lastQuote = null;
    $('unitPrice').textContent = '—'; $('totalPrice').textContent = '—';
    $('quoteErr').textContent = r.error; $('quoteErr').classList.remove('hidden');
  }
}
['W', 'H'].forEach(k => {
  const key = k === 'W' ? 'width' : 'height';
  $('in' + k).addEventListener('input', e => { st[key] = e.target.value; $('rg' + k).value = e.target.value; update(); });
  $('rg' + k).addEventListener('input', e => { st[key] = +e.target.value; $('in' + k).value = e.target.value; update(); });
});
$('rgAngle').addEventListener('input', e => { st.angle = +e.target.value; $('angleVal').textContent = st.angle + '°'; update(); });
$('inQty').addEventListener('input', e => { st.qty = clamp(parseInt(e.target.value, 10) || 1, 1, 999); update(); });
$('qtyMinus').onclick = () => { st.qty = Math.max(1, st.qty - 1); update(); };
$('qtyPlus').onclick = () => { st.qty = Math.min(999, st.qty + 1); update(); };
$('addBtn').onclick = () => {
  if (!lastQuote) return;
  const item = { cfg: lastQuote.config, name: lastQuote.product_name, summary: lastQuote.summary,
    unit_price: lastQuote.unit_price, total: lastQuote.total_price, quote: lastQuote };
  const cart = Cart.get();
  if (editIdx !== null && cart[editIdx]) { cart[editIdx] = item; Cart.set(cart); location.href = CART_URL; return; }
  cart.push(item); Cart.set(cart);
  const t = $('toast'); t.classList.remove('hidden'); clearTimeout(t._h); t._h = setTimeout(() => t.classList.add('hidden'), 3500);
};
renderAll();
</script>
{% endblock %}
"""

TEMPLATES["cart.html"] = r"""{% extends "base.html" %}
{% block title %}ตะกร้าสินค้า · {{ S.company_name }}{% endblock %}
{% block content %}
<div class="max-w-7xl mx-auto px-4 py-8">
  <h1 class="text-2xl md:text-3xl font-semibold mb-6">ตะกร้าสินค้า</h1>
  <div id="cartEmpty" class="hidden bg-white rounded-2xl border border-stone-200 p-10 text-center">
    <p class="text-stone-500">ยังไม่มีสินค้าในตะกร้า</p>
    <a href="{{ url_for('calculator') }}" class="inline-block mt-4 px-5 py-2.5 rounded-xl bg-wood-600 text-white hover:bg-wood-700">ไปคำนวณราคา</a>
  </div>
  <div id="cartWrap" class="hidden grid lg:grid-cols-3 gap-6">
    <div class="lg:col-span-2 space-y-3">
      <div id="items" class="space-y-3"></div>
      <a href="{{ url_for('calculator') }}" class="inline-flex items-center gap-1 text-sm text-wood-700 hover:underline">+ เพิ่มสินค้าอื่น</a>
    </div>
    <aside class="space-y-4">
      <div class="bg-white rounded-2xl border border-stone-200 p-5">
        <div class="flex justify-between text-sm text-stone-500"><span>จำนวนรายการ</span><span id="sumCount"></span></div>
        <div class="flex justify-between items-end mt-2"><span class="font-medium">ราคารวมประเมิน</span><span id="sumTotal" class="text-2xl font-semibold text-wood-700"></span></div>
        <p class="text-xs text-stone-500 mt-2">ราคานี้รวมติดตั้งในพื้นที่บริการ ช่างจะวัดหน้างานและยืนยันราคาก่อนผลิต</p>
      </div>
      <form id="orderForm" class="bg-white rounded-2xl border border-stone-200 p-5 space-y-3">
        <h2 class="font-semibold">ข้อมูลผู้สั่ง</h2>
        <input name="name" required placeholder="ชื่อ-นามสกุล *" class="w-full rounded-lg border border-stone-300 px-3 py-2">
        <input name="phone" required placeholder="เบอร์โทรศัพท์ *" inputmode="tel" class="w-full rounded-lg border border-stone-300 px-3 py-2">
        <input name="email" type="email" placeholder="อีเมล (ถ้ามี)" class="w-full rounded-lg border border-stone-300 px-3 py-2">
        <textarea name="address" rows="2" placeholder="ที่อยู่หน้างาน" class="w-full rounded-lg border border-stone-300 px-3 py-2"></textarea>
        <textarea name="note" rows="2" placeholder="หมายเหตุ เช่น วันที่สะดวกให้ช่างเข้าวัด" class="w-full rounded-lg border border-stone-300 px-3 py-2"></textarea>
        <p id="formErr" class="hidden text-sm text-red-600"></p>
        <button id="submitBtn" class="w-full py-3 rounded-xl bg-wood-600 hover:bg-wood-700 text-white font-semibold disabled:opacity-50">ส่งคำสั่งซื้อ / ขอนัดวัดหน้างาน</button>
      </form>
    </aside>
  </div>
</div>
{% endblock %}
{% block scripts %}
<script>
const CALC_URL = {{ url_for('calculator')|tojson }};
const $ = id => document.getElementById(id);
let items = Cart.get().filter(it => it && it.cfg);

function render() {
  const empty = items.length === 0;
  $('cartEmpty').classList.toggle('hidden', !empty); $('cartWrap').classList.toggle('hidden', empty);
  if (empty) return;
  $('items').innerHTML = items.map((it, i) => `
    <div class="bg-white rounded-2xl border ${it.error ? 'border-red-300' : 'border-stone-200'} p-4 flex gap-4">
      <div class="w-24 h-24 sm:w-32 sm:h-32 shrink-0 rounded-xl bg-gradient-to-b from-sky-50 to-stone-100"><svg data-i="${i}" class="w-full h-full"></svg></div>
      <div class="flex-1 min-w-0">
        <div class="flex justify-between gap-2"><h3 class="font-medium">${esc(it.name)}</h3>
          <button data-del="${i}" class="text-sm text-stone-400 hover:text-red-600 shrink-0">ลบ</button></div>
        <p class="text-sm text-stone-500 mt-0.5">${esc(it.summary)}</p>
        ${it.error ? `<p class="text-sm text-red-600 mt-1">${esc(it.error)} — กรุณาแก้ไข</p>` : ''}
        <div class="flex items-center justify-between gap-3 mt-3 flex-wrap">
          <div class="flex items-center rounded-lg border border-stone-300">
            <button data-q="${i}" data-d="-1" class="w-8 h-8 hover:bg-stone-100 rounded-l-lg">−</button>
            <span class="w-10 text-center text-sm">${it.cfg.qty}</span>
            <button data-q="${i}" data-d="1" class="w-8 h-8 hover:bg-stone-100 rounded-r-lg">+</button>
          </div>
          <a href="${CALC_URL}?edit=${i}" class="text-sm text-wood-700 hover:underline">✎ แก้ไขรูปแบบ/ขนาด</a>
          <div class="text-right"><div class="text-xs text-stone-500">${fmt(it.unit_price)} / ชุด</div><div class="font-semibold">${fmt(it.total)}</div></div>
        </div>
      </div>
    </div>`).join('');
  $('items').querySelectorAll('svg[data-i]').forEach(svg => { const it = items[+svg.dataset.i]; if (it.quote) ALU.drawQuote(svg, it.quote); });
  $('items').querySelectorAll('[data-del]').forEach(b => b.onclick = () => { items.splice(+b.dataset.del, 1); Cart.set(items); render(); });
  $('items').querySelectorAll('[data-q]').forEach(b => b.onclick = async () => {
    const it = items[+b.dataset.q]; it.cfg.qty = Math.max(1, Math.min(999, it.cfg.qty + (+b.dataset.d)));
    await requote(it); Cart.set(items); render();
  });
  $('sumCount').textContent = items.reduce((s, it) => s + it.cfg.qty, 0) + ' ชุด (' + items.length + ' รายการ)';
  $('sumTotal').textContent = fmt(items.reduce((s, it) => s + (it.error ? 0 : it.total), 0));
}
async function requote(it) {
  const r = await api('/api/quote', it.cfg);
  if (r.ok) Object.assign(it, { cfg: r.quote.config, name: r.quote.product_name, summary: r.quote.summary,
    unit_price: r.quote.unit_price, total: r.quote.total_price, quote: r.quote, error: null });
  else it.error = r.error;
}
render();
Promise.all(items.map(requote)).then(() => { Cart.set(items); render(); });

$('orderForm').addEventListener('submit', async e => {
  e.preventDefault();
  const fd = Object.fromEntries(new FormData(e.target).entries());
  const err = m => { $('formErr').textContent = m; $('formErr').classList.remove('hidden'); };
  if (items.some(it => it.error)) return err('มีรายการที่ต้องแก้ไขก่อนส่งคำสั่งซื้อ');
  if ((fd.phone || '').replace(/\D/g, '').length < 9) return err('กรุณากรอกเบอร์โทรศัพท์ให้ถูกต้อง');
  $('submitBtn').disabled = true; $('formErr').classList.add('hidden');
  const r = await api('/api/order', { customer: fd, items: items.map(it => it.cfg) });
  if (r.ok) { Cart.set([]); location.href = r.url; }
  else { err(r.error || 'ส่งคำสั่งซื้อไม่สำเร็จ'); $('submitBtn').disabled = false; }
});
</script>
{% endblock %}
"""

TEMPLATES["_order_body.html"] = r"""
<div class="bg-white rounded-2xl border border-stone-200 p-5 print-full">
  <div class="flex flex-wrap justify-between gap-4">
    <div>
      <div class="text-sm text-stone-500">เลขที่คำสั่งซื้อ</div>
      <div class="text-2xl font-semibold tracking-wide">{{ o.code }}</div>
      <div class="text-sm text-stone-500 mt-1">วันที่ {{ o.created_at }} · {{ o.customer_name }}</div>
    </div>
    <div class="text-right">
      <span class="inline-block px-3 py-1 rounded-full text-sm {{ STATUS[o.status][1] }}">{{ STATUS[o.status][0] }}</span>
      <div class="text-sm text-stone-500 mt-2">ราคารวมประเมิน</div>
      <div class="text-2xl font-semibold text-wood-700">฿{{ o.total_price|money }}</div>
    </div>
  </div>
  {% if o.status != 'cancelled' %}
  <ol class="mt-6 grid grid-cols-5 gap-1 text-[11px] sm:text-xs text-center">
    {% set cur = flow.index(o.status) if o.status in flow else 0 %}
    {% for s in flow %}
    <li><div class="h-1.5 rounded-full {{ 'bg-wood-600' if loop.index0 <= cur else 'bg-stone-200' }}"></div>
      <div class="mt-1 {{ 'text-wood-700 font-medium' if loop.index0 == cur else 'text-stone-400' }}">{{ STATUS[s][0] }}</div></li>
    {% endfor %}
  </ol>
  {% endif %}
  <div class="mt-6 divide-y divide-stone-100">
    {% for q in items %}
    <div class="py-3 flex gap-4 items-center">
      <div class="w-20 h-20 shrink-0 rounded-lg bg-stone-50"><svg class="w-full h-full" data-q="{{ loop.index0 }}"></svg></div>
      <div class="flex-1 min-w-0"><div class="font-medium">{{ q.product_name }}</div><div class="text-sm text-stone-500">{{ q.summary }}</div></div>
      <div class="text-right text-sm"><div class="text-stone-500">{{ q.qty }} × ฿{{ q.unit_price|money }}</div><div class="font-semibold">฿{{ q.total_price|money }}</div></div>
    </div>
    {% endfor %}
  </div>
</div>
<script>
(() => { const Q = {{ items|tojson }}; document.querySelectorAll('svg[data-q]').forEach(s => ALU.drawQuote(s, Q[+s.dataset.q])); })();
</script>
"""

TEMPLATES["order.html"] = r"""{% extends "base.html" %}
{% block title %}คำสั่งซื้อ {{ o.code }}{% endblock %}
{% block content %}
<div class="max-w-3xl mx-auto px-4 py-10">
  <div class="text-center mb-8 no-print">
    <div class="w-14 h-14 mx-auto rounded-full bg-emerald-100 text-emerald-600 grid place-items-center text-2xl">✓</div>
    <h1 class="text-2xl font-semibold mt-3">ได้รับคำสั่งซื้อแล้ว ขอบคุณค่ะ</h1>
    <p class="text-stone-500 mt-1">เจ้าหน้าที่จะติดต่อกลับเพื่อนัดวัดหน้างานภายใน 1 วันทำการ · โทร {{ S.phone }} · LINE {{ S.line_id }}</p>
    <p class="text-sm text-stone-500 mt-2">เก็บเลขที่คำสั่งซื้อไว้เพื่อ <a class="text-wood-700 underline" href="{{ url_for('track', code=o.code) }}">ติดตามสถานะงาน</a></p>
  </div>
  {% include "_order_body.html" %}
  <div class="mt-4 flex gap-2 justify-end no-print">
    <button onclick="window.print()" class="px-4 py-2 rounded-lg border border-stone-300 hover:bg-white text-sm">พิมพ์ / บันทึก PDF</button>
    <a href="{{ url_for('home') }}" class="px-4 py-2 rounded-lg bg-wood-600 text-white text-sm hover:bg-wood-700">กลับหน้าแรก</a>
  </div>
</div>
{% endblock %}
"""

TEMPLATES["track.html"] = r"""{% extends "base.html" %}
{% block title %}ติดตามงาน · {{ S.company_name }}{% endblock %}
{% block content %}
<div class="max-w-3xl mx-auto px-4 py-10">
  <h1 class="text-2xl md:text-3xl font-semibold">ติดตามสถานะงาน</h1>
  <form method="get" class="mt-5 bg-white rounded-2xl border border-stone-200 p-5 grid sm:grid-cols-3 gap-3 no-print">
    <input name="code" value="{{ code }}" required placeholder="เลขที่คำสั่งซื้อ เช่น AL2610..." class="rounded-lg border border-stone-300 px-3 py-2 uppercase">
    <input name="phone" value="{{ phone }}" required placeholder="เบอร์โทรที่ใช้สั่ง" class="rounded-lg border border-stone-300 px-3 py-2">
    <button class="rounded-lg bg-wood-600 hover:bg-wood-700 text-white font-medium py-2">ค้นหา</button>
  </form>
  {% if error %}<p class="mt-4 text-red-600 text-sm">{{ error }}</p>{% endif %}
  {% if o %}<div class="mt-6">{% include "_order_body.html" %}</div>{% endif %}
</div>
{% endblock %}
"""

TEMPLATES["admin_base.html"] = r"""{% extends "base.html" %}
{% block title %}หลังบ้าน · {{ S.company_name }}{% endblock %}
{% block nav %}
<header class="no-print sticky top-0 z-40 bg-stone-900 text-stone-200">
  <div class="max-w-7xl mx-auto px-4 h-14 flex items-center gap-1 overflow-x-auto text-sm whitespace-nowrap">
    <a href="{{ url_for('admin_dashboard') }}" class="font-semibold text-white mr-3 flex items-center gap-2">
      <span class="w-7 h-7 rounded-md bg-wood-500 wood-tex grid place-items-center text-[11px]">AL</span>หลังบ้าน</a>
    {% for ep, label in [('admin_dashboard','แดชบอร์ด'), ('admin_orders','คำสั่งซื้อ'), ('admin_products','สินค้า & สูตร BOM'), ('admin_materials','ราคาวัสดุ'), ('admin_options','สี / กระจก'), ('admin_settings','ตั้งค่า')] %}
    <a href="{{ url_for(ep) }}" class="px-3 py-1.5 rounded-lg {{ 'bg-white/15 text-white' if request.endpoint == ep or (ep == 'admin_orders' and request.endpoint == 'admin_order') or (ep == 'admin_products' and request.endpoint == 'admin_product') else 'hover:bg-white/10' }}">{{ label }}</a>
    {% endfor %}
    <span class="flex-1"></span>
    <a href="{{ url_for('home') }}" target="_blank" class="px-3 py-1.5 rounded-lg hover:bg-white/10">ดูหน้าร้าน ↗</a>
    <a href="{{ url_for('admin_logout') }}" class="px-3 py-1.5 rounded-lg hover:bg-white/10">ออกจากระบบ</a>
  </div>
</header>
{% endblock %}
{% block content %}<div class="max-w-7xl mx-auto px-4 py-6">{% block admin %}{% endblock %}</div>{% endblock %}
{% block footer %}{% endblock %}
"""

TEMPLATES["admin_login.html"] = r"""{% extends "base.html" %}
{% block title %}เข้าสู่ระบบหลังบ้าน{% endblock %}
{% block nav %}{% endblock %}{% block footer %}{% endblock %}
{% block content %}
<div class="min-h-[80vh] grid place-items-center px-4">
  <form method="post" class="w-full max-w-sm bg-white rounded-2xl border border-stone-200 shadow-sm p-6 space-y-4">
    {{ csrf_field() }}
    <div class="text-center">
      <div class="w-12 h-12 mx-auto rounded-xl bg-wood-500 wood-tex grid place-items-center text-white font-bold">AL</div>
      <h1 class="text-xl font-semibold mt-3">เข้าสู่ระบบหลังบ้าน</h1>
      <p class="text-sm text-stone-500">{{ S.company_name }}</p>
    </div>
    <input name="username" required placeholder="ชื่อผู้ใช้" class="w-full rounded-lg border border-stone-300 px-3 py-2">
    <input name="password" type="password" required placeholder="รหัสผ่าน" class="w-full rounded-lg border border-stone-300 px-3 py-2">
    <button class="w-full py-2.5 rounded-lg bg-stone-900 text-white hover:bg-stone-800 font-medium">เข้าสู่ระบบ</button>
    <a href="{{ url_for('home') }}" class="block text-center text-sm text-stone-500 hover:underline">← กลับหน้าร้าน</a>
  </form>
</div>
{% endblock %}
"""

TEMPLATES["admin_dashboard.html"] = r"""{% extends "admin_base.html" %}
{% block admin %}
<h1 class="text-2xl font-semibold mb-5">แดชบอร์ด</h1>
{% set profit = revenue - cost %}
<div class="grid grid-cols-2 lg:grid-cols-5 gap-3">
  {% for label, val, cls in [('คำสั่งซื้อทั้งหมด', n_orders|string + ' รายการ', ''), ('รอดำเนินการ (ใหม่)', counts['new']|string + ' รายการ', 'text-sky-700'),
      ('ยอดขาย (ไม่รวมยกเลิก)', '฿' + revenue|money, 'text-wood-700'), ('ต้นทุนรวม', '฿' + cost|money, 'text-stone-700'),
      ('กำไรขั้นต้น', '฿' + profit|money + (' (' + '%.1f'|format(profit / revenue * 100) + '%)' if revenue else ''), 'text-emerald-700')] %}
  <div class="bg-white rounded-2xl border border-stone-200 p-4"><div class="text-xs text-stone-500">{{ label }}</div><div class="text-xl font-semibold mt-1 {{ cls }}">{{ val }}</div></div>
  {% endfor %}
</div>
<div class="grid lg:grid-cols-3 gap-5 mt-5">
  <div class="lg:col-span-2 bg-white rounded-2xl border border-stone-200 overflow-hidden">
    <div class="px-5 py-3 border-b flex justify-between items-center"><h2 class="font-semibold">คำสั่งซื้อล่าสุด</h2><a href="{{ url_for('admin_orders') }}" class="text-sm text-wood-700 hover:underline">ดูทั้งหมด</a></div>
    <table class="w-full text-sm">
      <thead class="bg-stone-50 text-stone-500 text-left"><tr><th class="px-4 py-2">เลขที่</th><th class="px-4 py-2">ลูกค้า</th><th class="px-4 py-2 text-right">ราคาขาย</th><th class="px-4 py-2 text-right">กำไร</th><th class="px-4 py-2">สถานะ</th></tr></thead>
      <tbody class="divide-y divide-stone-100">
      {% for o in orders %}
        <tr class="hover:bg-stone-50"><td class="px-4 py-2"><a class="text-wood-700 font-medium hover:underline" href="{{ url_for('admin_order', oid=o.id) }}">{{ o.code }}</a><div class="text-xs text-stone-400">{{ o.created_at }}</div></td>
          <td class="px-4 py-2">{{ o.customer_name }}<div class="text-xs text-stone-400">{{ o.phone }}</div></td>
          <td class="px-4 py-2 text-right">฿{{ o.total_price|money }}</td><td class="px-4 py-2 text-right text-emerald-700">฿{{ (o.total_price - o.total_cost)|money }}</td>
          <td class="px-4 py-2"><span class="px-2 py-0.5 rounded-full text-xs {{ STATUS[o.status][1] }}">{{ STATUS[o.status][0] }}</span></td></tr>
      {% else %}<tr><td colspan="5" class="px-4 py-8 text-center text-stone-400">ยังไม่มีคำสั่งซื้อ</td></tr>{% endfor %}
      </tbody>
    </table>
  </div>
  <div class="space-y-5">
    <div class="bg-white rounded-2xl border border-stone-200 p-5">
      <h2 class="font-semibold mb-3">สถานะงาน</h2>
      {% for k, v in STATUS.items() %}
      <a href="{{ url_for('admin_orders', status=k) }}" class="flex justify-between py-1.5 text-sm hover:text-wood-700"><span class="flex items-center gap-2"><span class="w-2 h-2 rounded-full {{ v[1].split()[0] }}"></span>{{ v[0] }}</span><b>{{ counts.get(k, 0) }}</b></a>
      {% endfor %}
    </div>
    <div class="bg-white rounded-2xl border border-stone-200 p-5">
      <h2 class="font-semibold mb-3">สินค้าขายดี</h2>
      {% for name, t in top %}
      <div class="py-1.5 text-sm"><div class="flex justify-between"><span class="truncate pr-2">{{ name }}</span><b>฿{{ t.revenue|money }}</b></div>
        <div class="text-xs text-stone-500">{{ t.qty }} ชุด · กำไร ฿{{ t.profit|money }}</div></div>
      {% else %}<p class="text-sm text-stone-400">ยังไม่มีข้อมูล</p>{% endfor %}
    </div>
  </div>
</div>
{% endblock %}
"""

TEMPLATES["admin_orders.html"] = r"""{% extends "admin_base.html" %}
{% block admin %}
<div class="flex flex-wrap items-center justify-between gap-3 mb-4">
  <h1 class="text-2xl font-semibold">คำสั่งซื้อ</h1>
  <form method="get" class="flex gap-2">
    <input type="hidden" name="status" value="{{ status }}">
    <input name="q" value="{{ q }}" placeholder="ค้นหาเลขที่ / ชื่อ / เบอร์" class="rounded-lg border border-stone-300 px-3 py-1.5 text-sm">
    <button class="px-3 py-1.5 rounded-lg bg-stone-900 text-white text-sm">ค้นหา</button>
  </form>
</div>
<div class="flex flex-wrap gap-2 mb-4 text-sm">
  <a href="{{ url_for('admin_orders', q=q) }}" class="px-3 py-1 rounded-full border {{ 'bg-stone-900 text-white border-stone-900' if not status else 'bg-white border-stone-300' }}">ทั้งหมด</a>
  {% for k, v in STATUS.items() %}
  <a href="{{ url_for('admin_orders', status=k, q=q) }}" class="px-3 py-1 rounded-full border {{ 'bg-stone-900 text-white border-stone-900' if status == k else 'bg-white border-stone-300' }}">{{ v[0] }}</a>
  {% endfor %}
</div>
<div class="bg-white rounded-2xl border border-stone-200 overflow-x-auto">
  <table class="w-full text-sm min-w-[760px]">
    <thead class="bg-stone-50 text-stone-500 text-left"><tr>
      <th class="px-4 py-2">เลขที่ / วันที่</th><th class="px-4 py-2">ลูกค้า</th><th class="px-4 py-2 text-center">รายการ</th>
      <th class="px-4 py-2 text-right">ราคาขาย</th><th class="px-4 py-2 text-right">ต้นทุน</th><th class="px-4 py-2 text-right">กำไร</th><th class="px-4 py-2">สถานะ</th></tr></thead>
    <tbody class="divide-y divide-stone-100">
    {% for o in orders %}{% set pf = o.total_price - o.total_cost %}
      <tr class="hover:bg-stone-50">
        <td class="px-4 py-2"><a href="{{ url_for('admin_order', oid=o.id) }}" class="font-medium text-wood-700 hover:underline">{{ o.code }}</a><div class="text-xs text-stone-400">{{ o.created_at }}</div></td>
        <td class="px-4 py-2">{{ o.customer_name }}<div class="text-xs text-stone-400">{{ o.phone }}</div></td>
        <td class="px-4 py-2 text-center">{{ o.n_items }}</td>
        <td class="px-4 py-2 text-right">฿{{ o.total_price|money }}</td>
        <td class="px-4 py-2 text-right text-stone-500">฿{{ o.total_cost|money }}</td>
        <td class="px-4 py-2 text-right text-emerald-700">฿{{ pf|money }} <span class="text-xs text-stone-400">{{ '%.0f'|format(pf / o.total_price * 100) if o.total_price else 0 }}%</span></td>
        <td class="px-4 py-2"><span class="px-2 py-0.5 rounded-full text-xs {{ STATUS[o.status][1] }}">{{ STATUS[o.status][0] }}</span></td>
      </tr>
    {% else %}<tr><td colspan="7" class="px-4 py-10 text-center text-stone-400">ไม่พบคำสั่งซื้อ</td></tr>{% endfor %}
    </tbody>
  </table>
</div>
{% endblock %}
"""

TEMPLATES["admin_order.html"] = r"""{% extends "admin_base.html" %}
{% block admin %}
{% set profit = o.total_price - o.total_cost %}
<div class="flex flex-wrap items-center justify-between gap-3 mb-4">
  <div><a href="{{ url_for('admin_orders') }}" class="text-sm text-stone-500 hover:underline no-print">← คำสั่งซื้อ</a>
    <h1 class="text-2xl font-semibold">ใบสรุปต้นทุน / ใบสั่งผลิต {{ o.code }}</h1></div>
  <button onclick="window.print()" class="no-print px-4 py-2 rounded-lg border border-stone-300 bg-white text-sm hover:bg-stone-50">พิมพ์</button>
</div>
<div class="grid lg:grid-cols-3 gap-5">
  <div class="bg-white rounded-2xl border border-stone-200 p-5 text-sm space-y-1">
    <h2 class="font-semibold mb-2">ลูกค้า</h2>
    <div><b>{{ o.customer_name }}</b></div><div>โทร {{ o.phone }}</div>{% if o.email %}<div>{{ o.email }}</div>{% endif %}
    {% if o.address %}<div class="text-stone-600">{{ o.address }}</div>{% endif %}
    {% if o.note %}<div class="mt-2 p-2 rounded bg-amber-50 text-amber-900">หมายเหตุลูกค้า: {{ o.note }}</div>{% endif %}
    <div class="text-stone-400 pt-1">สั่งเมื่อ {{ o.created_at }}</div>
  </div>
  <div class="bg-white rounded-2xl border border-stone-200 p-5 text-sm">
    <h2 class="font-semibold mb-2">สรุปเงิน</h2>
    <div class="flex justify-between py-1"><span>ราคาขายรวม</span><b>฿{{ o.total_price|money }}</b></div>
    <div class="flex justify-between py-1"><span>ต้นทุนรวม</span><span>฿{{ o.total_cost|money }}</span></div>
    <div class="flex justify-between py-1 border-t mt-1 pt-2 text-emerald-700"><span>กำไรขั้นต้น</span><b>฿{{ profit|money }} ({{ '%.1f'|format(profit / o.total_price * 100) if o.total_price else 0 }}%)</b></div>
  </div>
  <form method="post" class="bg-white rounded-2xl border border-stone-200 p-5 text-sm space-y-3 no-print">
    {{ csrf_field() }}
    <h2 class="font-semibold">สถานะงาน</h2>
    <select name="status" class="w-full rounded-lg border border-stone-300 px-3 py-2">
      {% for k, v in STATUS.items() %}<option value="{{ k }}" {{ 'selected' if o.status == k }}>{{ v[0] }}</option>{% endfor %}
    </select>
    <textarea name="admin_note" rows="2" placeholder="บันทึกภายใน (ลูกค้าไม่เห็น)" class="w-full rounded-lg border border-stone-300 px-3 py-2">{{ o.admin_note or '' }}</textarea>
    <div class="flex gap-2">
      <button name="action" value="status" class="flex-1 py-2 rounded-lg bg-stone-900 text-white">บันทึก</button>
      <button name="action" value="delete" onclick="return confirm('ลบคำสั่งซื้อนี้ถาวร?')" class="px-3 py-2 rounded-lg border border-red-200 text-red-600 hover:bg-red-50">ลบ</button>
    </div>
  </form>
</div>

{% for q in items %}
<div class="bg-white rounded-2xl border border-stone-200 mt-5 overflow-hidden" style="break-inside: avoid">
  <div class="p-5 flex flex-wrap gap-5 items-center border-b">
    <div class="w-28 h-28 rounded-xl bg-stone-50 shrink-0"><svg class="w-full h-full" data-q="{{ loop.index0 }}"></svg></div>
    <div class="flex-1 min-w-[220px]">
      <div class="text-xs text-stone-400">รายการที่ {{ loop.index }}</div>
      <div class="font-semibold text-lg">{{ q.product_name }}</div>
      <div class="text-sm text-stone-500">{{ q.summary }} · พื้นที่ {{ q.area|num(2) }} ตร.ม.</div>
      <div class="text-sm mt-1">จำนวน <b>{{ q.qty }}</b> ชุด</div>
    </div>
    <div class="grid grid-cols-3 gap-4 text-sm text-right">
      <div><div class="text-stone-500">ต้นทุน/ชุด</div><div class="font-semibold">฿{{ q.unit_cost|money }}</div></div>
      <div><div class="text-stone-500">ราคาขาย/ชุด</div><div class="font-semibold text-wood-700">฿{{ q.unit_price|money }}</div></div>
      <div><div class="text-stone-500">กำไร/ชุด</div><div class="font-semibold text-emerald-700">฿{{ (q.unit_price - q.unit_cost)|money }}</div></div>
    </div>
  </div>
  <div class="overflow-x-auto">
  <table class="w-full text-sm min-w-[720px]">
    <thead class="bg-stone-50 text-stone-500 text-left"><tr><th class="px-4 py-2">รหัส</th><th class="px-4 py-2">วัสดุ</th><th class="px-4 py-2">สูตร</th>
      <th class="px-4 py-2 text-right">ปริมาณ/ชุด</th><th class="px-4 py-2 text-right">รวม {{ q.qty }} ชุด</th><th class="px-4 py-2 text-right">ราคา/หน่วย</th><th class="px-4 py-2 text-right">ต้นทุน/ชุด</th></tr></thead>
    <tbody class="divide-y divide-stone-100">
      {% for l in q.lines %}
      <tr><td class="px-4 py-1.5 font-mono text-xs">{{ l.code }}</td><td class="px-4 py-1.5">{{ l.name }}{% if l.note %} <span class="text-xs text-stone-400">({{ l.note }})</span>{% endif %}</td>
        <td class="px-4 py-1.5 font-mono text-xs text-stone-500">{{ l.formula }}</td>
        <td class="px-4 py-1.5 text-right">{{ l.qty|num }} {{ l.unit }}</td><td class="px-4 py-1.5 text-right">{{ (l.qty * q.qty)|num }} {{ l.unit }}</td>
        <td class="px-4 py-1.5 text-right">{{ l.unit_cost|num(2) }}</td><td class="px-4 py-1.5 text-right">{{ l.amount|num(2) }}</td></tr>
      {% endfor %}
    </tbody>
    <tfoot class="text-right">
      <tr class="border-t"><td colspan="6" class="px-4 py-1.5">ค่าวัสดุ</td><td class="px-4 py-1.5">{{ q.material_cost|num(2) }}</td></tr>
      <tr><td colspan="6" class="px-4 py-1.5">เผื่อเศษวัสดุ {{ q.waste_pct|num }}%</td><td class="px-4 py-1.5">{{ q.waste_cost|num(2) }}</td></tr>
      <tr><td colspan="6" class="px-4 py-1.5">ค่าแรง</td><td class="px-4 py-1.5">{{ q.labor_cost|num(2) }}</td></tr>
      <tr class="font-semibold"><td colspan="6" class="px-4 py-1.5">ต้นทุนรวม/ชุด → บวกกำไร {{ q.markup_pct|num }}% (ขั้นต่ำ ฿{{ q.min_price|money }})</td><td class="px-4 py-1.5">฿{{ q.unit_cost|money }} → ฿{{ q.unit_price|money }}</td></tr>
    </tfoot>
  </table>
  </div>
</div>
{% endfor %}

<div class="bg-white rounded-2xl border border-stone-200 mt-5 overflow-hidden" style="break-inside: avoid">
  <div class="px-5 py-3 border-b font-semibold">สรุปวัสดุที่ต้องเบิก / สั่งซื้อ (ทั้งคำสั่งซื้อ)</div>
  <table class="w-full text-sm">
    <thead class="bg-stone-50 text-stone-500 text-left"><tr><th class="px-4 py-2">รหัส</th><th class="px-4 py-2">วัสดุ</th><th class="px-4 py-2 text-right">ปริมาณรวม</th><th class="px-4 py-2 text-right">ต้นทุนรวม</th></tr></thead>
    <tbody class="divide-y divide-stone-100">
      {% for code, s in summary.items() %}
      <tr><td class="px-4 py-1.5 font-mono text-xs">{{ code }}</td><td class="px-4 py-1.5">{{ s.name }}</td><td class="px-4 py-1.5 text-right">{{ s.qty|num(2) }} {{ s.unit }}</td><td class="px-4 py-1.5 text-right">฿{{ s.amount|money }}</td></tr>
      {% endfor %}
    </tbody>
  </table>
</div>
{% endblock %}
{% block scripts %}
<script>
(() => { const Q = {{ items|tojson }}; document.querySelectorAll('svg[data-q]').forEach(s => ALU.drawQuote(s, Q[+s.dataset.q])); })();
</script>
{% endblock %}
"""

TEMPLATES["admin_materials.html"] = r"""{% extends "admin_base.html" %}
{% block admin %}
<div class="flex flex-wrap items-end justify-between gap-3 mb-4">
  <div><h1 class="text-2xl font-semibold">ราคาวัสดุ (ต้นทุน)</h1>
    <p class="text-sm text-stone-500">แก้ราคาแล้วกดบันทึก — ต้นทุนและราคาขายของทุกสินค้าคำนวณใหม่อัตโนมัติ (คำสั่งซื้อเก่าเก็บราคา ณ วันที่สั่ง)</p></div>
</div>
<form method="post" class="bg-white rounded-2xl border border-stone-200 overflow-x-auto">
  {{ csrf_field() }}<input type="hidden" name="action" value="save">
  <table class="w-full text-sm min-w-[800px]">
    <thead class="bg-stone-50 text-stone-500 text-left"><tr><th class="px-3 py-2">รหัส</th><th class="px-3 py-2">ชื่อวัสดุ</th><th class="px-3 py-2">หมวด</th>
      <th class="px-3 py-2">หน่วย</th><th class="px-3 py-2 text-right">ราคาต้นทุน/หน่วย (฿)</th><th class="px-3 py-2 text-center">ใช้ใน BOM</th><th class="px-3 py-2 text-center">ลบ</th></tr></thead>
    <tbody class="divide-y divide-stone-100">
    {% for m in mats %}
      <tr>
        <td class="px-3 py-1.5 font-mono text-xs">{{ m.code }}</td>
        <td class="px-3 py-1.5"><input name="name_{{ m.id }}" value="{{ m.name }}" class="w-full rounded border border-stone-200 px-2 py-1"></td>
        <td class="px-3 py-1.5"><select name="category_{{ m.id }}" class="rounded border border-stone-200 px-2 py-1">{% for k, v in cats.items() %}<option value="{{ k }}" {{ 'selected' if m.category == k }}>{{ v }}</option>{% endfor %}</select></td>
        <td class="px-3 py-1.5"><input name="unit_{{ m.id }}" value="{{ m.unit }}" class="w-20 rounded border border-stone-200 px-2 py-1"></td>
        <td class="px-3 py-1.5 text-right"><input name="cost_{{ m.id }}" type="number" step="0.01" min="0" value="{{ m.unit_cost }}" class="w-32 text-right rounded border border-stone-200 px-2 py-1 font-medium"></td>
        <td class="px-3 py-1.5 text-center text-stone-500">{{ m.used }}</td>
        <td class="px-3 py-1.5 text-center"><input type="checkbox" name="del_{{ m.id }}" {{ 'disabled' if m.used }} title="{{ 'ใช้งานอยู่ ลบไม่ได้' if m.used else 'ลบ' }}"></td>
      </tr>
    {% endfor %}
    </tbody>
  </table>
  <div class="p-4 border-t flex justify-end"><button class="px-5 py-2 rounded-lg bg-stone-900 text-white">บันทึกราคาวัสดุ</button></div>
</form>
<form method="post" class="mt-5 bg-white rounded-2xl border border-stone-200 p-5 grid sm:grid-cols-6 gap-2 text-sm items-end">
  {{ csrf_field() }}<input type="hidden" name="action" value="add">
  <div class="sm:col-span-6 font-semibold">เพิ่มวัสดุใหม่</div>
  <input name="code" placeholder="รหัส เช่น AL-NEW" required class="rounded border border-stone-300 px-2 py-1.5 uppercase">
  <input name="name" placeholder="ชื่อวัสดุ" required class="sm:col-span-2 rounded border border-stone-300 px-2 py-1.5">
  <select name="category" class="rounded border border-stone-300 px-2 py-1.5">{% for k, v in cats.items() %}<option value="{{ k }}">{{ v }}</option>{% endfor %}</select>
  <div class="flex gap-2"><input name="unit" placeholder="หน่วย" class="w-20 rounded border border-stone-300 px-2 py-1.5"><input name="unit_cost" type="number" step="0.01" min="0" placeholder="ราคา" class="w-full rounded border border-stone-300 px-2 py-1.5"></div>
  <button class="rounded-lg bg-wood-600 text-white py-1.5">เพิ่ม</button>
</form>
{% endblock %}
"""

TEMPLATES["admin_products.html"] = r"""{% extends "admin_base.html" %}
{% block admin %}
<h1 class="text-2xl font-semibold mb-1">สินค้า & สูตรวัสดุ (BOM)</h1>
<p class="text-sm text-stone-500 mb-4">ราคาตัวอย่างคำนวณที่ขนาดเริ่มต้นของแต่ละสินค้า ด้วยราคาวัสดุปัจจุบัน</p>
<div class="bg-white rounded-2xl border border-stone-200 overflow-x-auto">
  <table class="w-full text-sm min-w-[900px]">
    <thead class="bg-stone-50 text-stone-500 text-left"><tr><th class="px-4 py-2">สินค้า</th><th class="px-4 py-2">หมวด / แบบ</th><th class="px-4 py-2 text-center">BOM</th>
      <th class="px-4 py-2 text-right">บวกกำไร</th><th class="px-4 py-2 text-right">ขนาดตัวอย่าง</th><th class="px-4 py-2 text-right">ต้นทุน</th><th class="px-4 py-2 text-right">ราคาขาย</th><th class="px-4 py-2 text-center">สถานะ</th></tr></thead>
    <tbody class="divide-y divide-stone-100">
    {% for p in prods %}
      <tr class="hover:bg-stone-50">
        <td class="px-4 py-2"><a href="{{ url_for('admin_product', pid=p.id) }}" class="font-medium text-wood-700 hover:underline">{{ p.name }}</a><div class="text-xs text-stone-400 font-mono">{{ p.slug }}</div></td>
        <td class="px-4 py-2">{{ p.category }}<div class="text-xs text-stone-400">{{ previews.get(p.preview, p.preview) }} · {{ p.panel_options }} บาน</div></td>
        <td class="px-4 py-2 text-center">{{ p.n_bom }}</td>
        <td class="px-4 py-2 text-right">{{ p.markup_pct|num }}%</td>
        <td class="px-4 py-2 text-right text-stone-500">{{ p.def_w|num }}×{{ p.def_h|num }}</td>
        {% if p.sample_error %}<td colspan="2" class="px-4 py-2 text-right text-red-600 text-xs">{{ p.sample_error }}</td>
        {% else %}<td class="px-4 py-2 text-right text-stone-500">฿{{ p.sample_cost|money }}</td><td class="px-4 py-2 text-right font-medium">฿{{ p.sample_price|money }}</td>{% endif %}
        <td class="px-4 py-2 text-center"><span class="px-2 py-0.5 rounded-full text-xs {{ 'bg-emerald-100 text-emerald-700' if p.active else 'bg-stone-200 text-stone-500' }}">{{ 'เปิดขาย' if p.active else 'ปิด' }}</span></td>
      </tr>
    {% endfor %}
    </tbody>
  </table>
</div>
<form method="post" class="mt-5 bg-white rounded-2xl border border-stone-200 p-5 grid sm:grid-cols-4 gap-2 text-sm items-end">
  {{ csrf_field() }}
  <div class="sm:col-span-4 font-semibold">เพิ่มสินค้าใหม่</div>
  <input name="slug" placeholder="slug (a-z, 0-9, -) เช่น door-folding" required class="rounded border border-stone-300 px-2 py-1.5">
  <input name="name" placeholder="ชื่อสินค้า" required class="rounded border border-stone-300 px-2 py-1.5">
  <input name="category" list="cats" placeholder="หมวด" value="ประตู" class="rounded border border-stone-300 px-2 py-1.5">
  <datalist id="cats">{% for c in categories %}<option value="{{ c }}">{% endfor %}</datalist>
  <button class="rounded-lg bg-wood-600 text-white py-1.5">สร้างแล้วไปตั้งค่าสูตร →</button>
</form>
{% endblock %}
"""

TEMPLATES["admin_product.html"] = r"""{% extends "admin_base.html" %}
{% block admin %}
<a href="{{ url_for('admin_products') }}" class="text-sm text-stone-500 hover:underline">← สินค้าทั้งหมด</a>
<div class="flex flex-wrap items-center justify-between gap-3 mb-4">
  <h1 class="text-2xl font-semibold">{{ p.name }}</h1>
  {% if p.active %}<a href="{{ url_for('calculator', product=p.slug) }}" target="_blank" class="text-sm text-wood-700 hover:underline">เปิดในหน้าคำนวณราคา ↗</a>{% endif %}
</div>
<datalist id="matlist">{% for m in mats %}<option value="{{ m.code }}">{{ m.name }} ({{ m.unit_cost|num(2) }}/{{ m.unit }})</option>{% endfor %}</datalist>
<div class="grid xl:grid-cols-5 gap-5">
<form method="post" class="xl:col-span-3 space-y-5">
  {{ csrf_field() }}
  <div class="bg-white rounded-2xl border border-stone-200 p-5 grid sm:grid-cols-2 gap-3 text-sm">
    <div class="sm:col-span-2 font-semibold text-base">ข้อมูลสินค้า</div>
    <label class="block">ชื่อสินค้า<input name="name" value="{{ p.name }}" class="mt-1 w-full rounded border border-stone-300 px-2 py-1.5"></label>
    <label class="block">หมวด<input name="category" list="pcats" value="{{ p.category }}" class="mt-1 w-full rounded border border-stone-300 px-2 py-1.5">
      <datalist id="pcats">{% for c in categories %}<option value="{{ c }}">{% endfor %}</datalist></label>
    <label class="block sm:col-span-2">คำอธิบาย<textarea name="description" rows="2" class="mt-1 w-full rounded border border-stone-300 px-2 py-1.5">{{ p.description }}</textarea></label>
    <label class="block">ภาพตัวอย่าง (รูปแบบ)<select name="preview" class="mt-1 w-full rounded border border-stone-300 px-2 py-1.5">{% for k, v in previews.items() %}<option value="{{ k }}" {{ 'selected' if p.preview == k }}>{{ v }}</option>{% endfor %}</select></label>
    <label class="block">ไส้บาน<select name="infill" class="mt-1 w-full rounded border border-stone-300 px-2 py-1.5">{% for k, v in infills.items() %}<option value="{{ k }}" {{ 'selected' if p.infill == k }}>{{ v }}</option>{% endfor %}</select></label>
    <label class="block">จำนวนบานที่เลือกได้ (คั่นด้วย ,)<input name="panel_options" value="{{ p.panel_options }}" class="mt-1 w-full rounded border border-stone-300 px-2 py-1.5"></label>
    <div class="flex items-end gap-4 pb-1.5">
      <label class="flex items-center gap-2"><input type="checkbox" name="uses_glass" {{ 'checked' if p.uses_glass }}> ใช้กระจก</label>
      <label class="flex items-center gap-2"><input type="checkbox" name="has_divider" {{ 'checked' if p.has_divider }}> มีลูกฟัก</label>
      <label class="flex items-center gap-2"><input type="checkbox" name="active" {{ 'checked' if p.active }}> เปิดขาย</label>
    </div>
    <div class="sm:col-span-2 grid grid-cols-3 gap-3">
      <label class="block">กว้างต่ำสุด–สูงสุด (ซม.)<div class="flex gap-1 mt-1"><input name="min_w" type="number" value="{{ p.min_w|num }}" class="w-full rounded border border-stone-300 px-2 py-1.5"><input name="max_w" type="number" value="{{ p.max_w|num }}" class="w-full rounded border border-stone-300 px-2 py-1.5"></div></label>
      <label class="block">สูงต่ำสุด–สูงสุด (ซม.)<div class="flex gap-1 mt-1"><input name="min_h" type="number" value="{{ p.min_h|num }}" class="w-full rounded border border-stone-300 px-2 py-1.5"><input name="max_h" type="number" value="{{ p.max_h|num }}" class="w-full rounded border border-stone-300 px-2 py-1.5"></div></label>
      <label class="block">ขนาดเริ่มต้น กว้าง×สูง<div class="flex gap-1 mt-1"><input name="def_w" type="number" value="{{ p.def_w|num }}" class="w-full rounded border border-stone-300 px-2 py-1.5"><input name="def_h" type="number" value="{{ p.def_h|num }}" class="w-full rounded border border-stone-300 px-2 py-1.5"></div></label>
    </div>
    <label class="block">บวกกำไร (Markup %)<input name="markup_pct" type="number" step="0.1" value="{{ p.markup_pct|num }}" class="mt-1 w-full rounded border border-stone-300 px-2 py-1.5"></label>
    <label class="block">ราคาขายขั้นต่ำ/ชุด (฿)<input name="min_price" type="number" step="1" value="{{ p.min_price|num }}" class="mt-1 w-full rounded border border-stone-300 px-2 py-1.5"></label>
    <label class="block">ลำดับการแสดง<input name="sort" type="number" value="{{ p.sort }}" class="mt-1 w-full rounded border border-stone-300 px-2 py-1.5"></label>
  </div>

  <div class="bg-white rounded-2xl border border-stone-200 overflow-x-auto">
    <div class="px-5 py-3 border-b"><div class="font-semibold">สูตรวัสดุ (BOM) ต่อ 1 ชุด</div>
      <div class="text-xs text-stone-500 mt-1">ตัวแปร: {% for k, v in fvars.items() %}<code class="bg-stone-100 px-1 rounded">{{ k }}</code> {{ v }}{{ ', ' if not loop.last }}{% endfor %}
        · ฟังก์ชัน <code class="bg-stone-100 px-1 rounded">ceil floor min max round abs sqrt</code> · ตัวอย่าง <code class="bg-stone-100 px-1 rounded">P*2*(W/P+H) + D*W</code></div></div>
    <table class="w-full text-sm min-w-[640px]">
      <thead class="bg-stone-50 text-stone-500 text-left"><tr><th class="px-3 py-2 w-16">ลำดับ</th><th class="px-3 py-2">รหัสวัสดุ</th><th class="px-3 py-2">สูตรปริมาณ</th><th class="px-3 py-2">หมายเหตุ</th><th class="px-3 py-2 text-center">ลบ</th></tr></thead>
      <tbody class="divide-y divide-stone-100">
      {% for b in bom %}
        <tr><td class="px-3 py-1.5"><input name="b_sort_{{ b.id }}" type="number" value="{{ b.sort }}" class="w-14 rounded border border-stone-200 px-1 py-1"></td>
          <td class="px-3 py-1.5"><input name="b_code_{{ b.id }}" list="matlist" value="{{ b.material_code }}" class="w-36 rounded border border-stone-200 px-2 py-1 font-mono text-xs"></td>
          <td class="px-3 py-1.5"><input name="b_formula_{{ b.id }}" value="{{ b.formula }}" class="w-full rounded border border-stone-200 px-2 py-1 font-mono text-xs"></td>
          <td class="px-3 py-1.5"><input name="b_note_{{ b.id }}" value="{{ b.note }}" class="w-full rounded border border-stone-200 px-2 py-1"></td>
          <td class="px-3 py-1.5 text-center"><input type="checkbox" name="b_del_{{ b.id }}"></td></tr>
      {% endfor %}
      {% for n in range(5) %}
        <tr class="bg-wood-50/40"><td class="px-3 py-1.5"><input name="n_sort_{{ n }}" type="number" value="{{ 50 + n }}" class="w-14 rounded border border-stone-200 px-1 py-1"></td>
          <td class="px-3 py-1.5"><input name="n_code_{{ n }}" list="matlist" placeholder="+ เพิ่มวัสดุ" class="w-36 rounded border border-stone-200 px-2 py-1 font-mono text-xs"></td>
          <td class="px-3 py-1.5"><input name="n_formula_{{ n }}" placeholder="เช่น W*2" class="w-full rounded border border-stone-200 px-2 py-1 font-mono text-xs"></td>
          <td class="px-3 py-1.5"><input name="n_note_{{ n }}" class="w-full rounded border border-stone-200 px-2 py-1"></td><td></td></tr>
      {% endfor %}
      </tbody>
    </table>
    <p class="px-5 py-2 text-xs text-stone-500 border-t">ถ้าสินค้าใช้กระจก ระบบเพิ่มค่ากระจก = A×0.9 × ราคากระจกที่ลูกค้าเลือก ให้อัตโนมัติ · ราคาวัสดุหมวดอลูมิเนียมปรับตาม % ส่วนเพิ่มของสีที่เลือก</p>
  </div>
  <div class="flex justify-between">
    <button name="action" value="delete" onclick="return confirm('ลบสินค้านี้และสูตรทั้งหมด?')" class="px-4 py-2 rounded-lg border border-red-200 text-red-600 hover:bg-red-50 text-sm">ลบสินค้า</button>
    <button name="action" value="save" class="px-6 py-2 rounded-lg bg-stone-900 text-white">บันทึก</button>
  </div>
</form>

<div class="xl:col-span-2">
  <div class="xl:sticky xl:top-20 bg-white rounded-2xl border border-stone-200 overflow-hidden">
    <form method="get" class="p-5 border-b grid grid-cols-2 gap-2 text-sm">
      <div class="col-span-2 font-semibold text-base">ทดลองคำนวณต้นทุน</div>
      <label>กว้าง (ซม.)<input name="t_w" type="number" value="{{ tcfg.width }}" class="mt-1 w-full rounded border border-stone-300 px-2 py-1"></label>
      <label>สูง (ซม.)<input name="t_h" type="number" value="{{ tcfg.height }}" class="mt-1 w-full rounded border border-stone-300 px-2 py-1"></label>
      <label>จำนวนบาน<select name="t_p" class="mt-1 w-full rounded border border-stone-300 px-2 py-1">{% for n in panels %}<option {{ 'selected' if n|string == tcfg.panels|string }}>{{ n }}</option>{% endfor %}</select></label>
      <label>ลูกฟัก<select name="t_d" class="mt-1 w-full rounded border border-stone-300 px-2 py-1">{% for n in range(4) %}<option {{ 'selected' if n|string == tcfg.divider|string }}>{{ n }}</option>{% endfor %}</select></label>
      <label>สี<select name="t_f" class="mt-1 w-full rounded border border-stone-300 px-2 py-1">{% for f in finishes if f.active %}<option value="{{ f.id }}" {{ 'selected' if f.id|string == tcfg.finish_id|string }}>{{ f.name }} ({{ '%+g'|format(f.surcharge_pct) }}%)</option>{% endfor %}</select></label>
      <label>กระจก<select name="t_g" class="mt-1 w-full rounded border border-stone-300 px-2 py-1" {{ 'disabled' if not p.uses_glass }}>{% for x in glass if x.active %}<option value="{{ x.id }}" {{ 'selected' if x.id|string == tcfg.glass_id|string }}>{{ x.name }}</option>{% endfor %}</select></label>
      <button class="col-span-2 mt-1 py-1.5 rounded-lg bg-wood-600 text-white">คำนวณ</button>
    </form>
    {% if test_error %}<p class="p-5 text-sm text-red-600">{{ test_error }}</p>{% endif %}
    {% if test %}
    <table class="w-full text-xs">
      <thead class="bg-stone-50 text-stone-500 text-left"><tr><th class="px-3 py-1.5">วัสดุ</th><th class="px-3 py-1.5 text-right">ปริมาณ</th><th class="px-3 py-1.5 text-right">@</th><th class="px-3 py-1.5 text-right">รวม</th></tr></thead>
      <tbody class="divide-y divide-stone-100">
        {% for l in test.lines %}<tr><td class="px-3 py-1"><span class="font-mono">{{ l.code }}</span><div class="text-stone-400">{{ l.formula }}</div></td><td class="px-3 py-1 text-right">{{ l.qty|num }} {{ l.unit }}</td><td class="px-3 py-1 text-right">{{ l.unit_cost|num(2) }}</td><td class="px-3 py-1 text-right">{{ l.amount|num(2) }}</td></tr>{% endfor %}
      </tbody>
    </table>
    <div class="p-5 border-t text-sm space-y-1">
      <div class="flex justify-between"><span>ค่าวัสดุ</span><span>{{ test.material_cost|num(2) }}</span></div>
      <div class="flex justify-between"><span>เผื่อเศษ {{ test.waste_pct|num }}%</span><span>{{ test.waste_cost|num(2) }}</span></div>
      <div class="flex justify-between"><span>ค่าแรง</span><span>{{ test.labor_cost|num(2) }}</span></div>
      <div class="flex justify-between font-semibold border-t pt-1"><span>ต้นทุนรวม</span><span>฿{{ test.unit_cost|money }}</span></div>
      <div class="flex justify-between text-stone-500"><span>× (1 + {{ test.markup_pct|num }}%)</span><span>฿{{ test.raw_price|money }}</span></div>
      <div class="flex justify-between font-semibold text-wood-700 text-base"><span>ราคาขาย (ปัด/ขั้นต่ำ)</span><span>฿{{ test.unit_price|money }}</span></div>
      <div class="flex justify-between text-emerald-700"><span>กำไร</span><span>฿{{ (test.unit_price - test.unit_cost)|money }} ({{ '%.1f'|format((test.unit_price - test.unit_cost) / test.unit_price * 100) }}%)</span></div>
    </div>
    {% endif %}
  </div>
</div>
</div>
{% endblock %}
"""

TEMPLATES["admin_options.html"] = r"""{% extends "admin_base.html" %}
{% block admin %}
<h1 class="text-2xl font-semibold mb-4">สีลายไม้ & ชนิดกระจก</h1>
<div class="grid xl:grid-cols-2 gap-5">
  <div>
    <form method="post" class="bg-white rounded-2xl border border-stone-200 overflow-x-auto">
      {{ csrf_field() }}<input type="hidden" name="action" value="save_finishes">
      <div class="px-5 py-3 border-b"><div class="font-semibold">สี / ลายไม้</div><div class="text-xs text-stone-500">% ส่วนเพิ่ม คิดกับราคาวัสดุหมวดอลูมิเนียม (ติดลบ = ถูกลง)</div></div>
      <table class="w-full text-sm min-w-[560px]">
        <thead class="bg-stone-50 text-stone-500 text-left"><tr><th class="px-3 py-2">สี</th><th class="px-3 py-2">ชื่อ</th><th class="px-3 py-2 text-center">ลายไม้</th><th class="px-3 py-2">% เพิ่ม</th><th class="px-3 py-2">ลำดับ</th><th class="px-3 py-2 text-center">ใช้งาน</th></tr></thead>
        <tbody class="divide-y divide-stone-100">
        {% for f in finishes %}
          <tr><td class="px-3 py-1.5"><input type="color" name="hex_{{ f.id }}" value="{{ f.hex }}" class="w-10 h-8 rounded"></td>
            <td class="px-3 py-1.5"><input name="name_{{ f.id }}" value="{{ f.name }}" class="w-full rounded border border-stone-200 px-2 py-1"></td>
            <td class="px-3 py-1.5 text-center"><input type="checkbox" name="wood_{{ f.id }}" {{ 'checked' if f.is_wood }}></td>
            <td class="px-3 py-1.5"><input name="sur_{{ f.id }}" type="number" step="0.1" value="{{ f.surcharge_pct|num }}" class="w-20 rounded border border-stone-200 px-2 py-1"></td>
            <td class="px-3 py-1.5"><input name="sort_{{ f.id }}" type="number" value="{{ f.sort }}" class="w-14 rounded border border-stone-200 px-2 py-1"></td>
            <td class="px-3 py-1.5 text-center"><input type="checkbox" name="active_{{ f.id }}" {{ 'checked' if f.active }}></td></tr>
        {% endfor %}
        </tbody>
      </table>
      <div class="p-4 border-t flex justify-end"><button class="px-5 py-2 rounded-lg bg-stone-900 text-white text-sm">บันทึกสี</button></div>
    </form>
    <form method="post" class="mt-3 bg-white rounded-2xl border border-stone-200 p-4 flex flex-wrap gap-2 items-center text-sm">
      {{ csrf_field() }}<input type="hidden" name="action" value="add_finish">
      <input type="color" name="hex" value="#b8803f" class="w-10 h-8 rounded">
      <input name="name" required placeholder="ชื่อสีใหม่" class="flex-1 min-w-[140px] rounded border border-stone-300 px-2 py-1.5">
      <input name="surcharge_pct" type="number" step="0.1" placeholder="% เพิ่ม" class="w-24 rounded border border-stone-300 px-2 py-1.5">
      <label class="flex items-center gap-1"><input type="checkbox" name="is_wood" checked> ลายไม้</label>
      <button class="px-4 py-1.5 rounded-lg bg-wood-600 text-white">เพิ่ม</button>
    </form>
  </div>
  <div>
    <form method="post" class="bg-white rounded-2xl border border-stone-200 overflow-x-auto">
      {{ csrf_field() }}<input type="hidden" name="action" value="save_glass">
      <div class="px-5 py-3 border-b"><div class="font-semibold">ชนิดกระจก</div><div class="text-xs text-stone-500">ราคาต้นทุนต่อ ตร.ม. — คิดพื้นที่กระจก = A × 0.9</div></div>
      <table class="w-full text-sm min-w-[520px]">
        <thead class="bg-stone-50 text-stone-500 text-left"><tr><th class="px-3 py-2">สี</th><th class="px-3 py-2">ชื่อ</th><th class="px-3 py-2">฿/ตร.ม.</th><th class="px-3 py-2">ลำดับ</th><th class="px-3 py-2 text-center">ใช้งาน</th></tr></thead>
        <tbody class="divide-y divide-stone-100">
        {% for x in glass %}
          <tr><td class="px-3 py-1.5"><input type="color" name="hex_{{ x.id }}" value="{{ x.hex }}" class="w-10 h-8 rounded"></td>
            <td class="px-3 py-1.5"><input name="name_{{ x.id }}" value="{{ x.name }}" class="w-full rounded border border-stone-200 px-2 py-1"></td>
            <td class="px-3 py-1.5"><input name="cost_{{ x.id }}" type="number" step="0.01" min="0" value="{{ x.cost_per_sqm }}" class="w-24 rounded border border-stone-200 px-2 py-1"></td>
            <td class="px-3 py-1.5"><input name="sort_{{ x.id }}" type="number" value="{{ x.sort }}" class="w-14 rounded border border-stone-200 px-2 py-1"></td>
            <td class="px-3 py-1.5 text-center"><input type="checkbox" name="active_{{ x.id }}" {{ 'checked' if x.active }}></td></tr>
        {% endfor %}
        </tbody>
      </table>
      <div class="p-4 border-t flex justify-end"><button class="px-5 py-2 rounded-lg bg-stone-900 text-white text-sm">บันทึกกระจก</button></div>
    </form>
    <form method="post" class="mt-3 bg-white rounded-2xl border border-stone-200 p-4 flex flex-wrap gap-2 items-center text-sm">
      {{ csrf_field() }}<input type="hidden" name="action" value="add_glass">
      <input type="color" name="hex" value="#cfe8f7" class="w-10 h-8 rounded">
      <input name="name" required placeholder="ชื่อกระจกใหม่" class="flex-1 min-w-[140px] rounded border border-stone-300 px-2 py-1.5">
      <input name="cost_per_sqm" type="number" step="0.01" min="0" placeholder="฿/ตร.ม." class="w-28 rounded border border-stone-300 px-2 py-1.5">
      <button class="px-4 py-1.5 rounded-lg bg-wood-600 text-white">เพิ่ม</button>
    </form>
  </div>
</div>
{% endblock %}
"""

TEMPLATES["admin_settings.html"] = r"""{% extends "admin_base.html" %}
{% block admin %}
<h1 class="text-2xl font-semibold mb-4">ตั้งค่า</h1>
<form method="post" class="max-w-2xl bg-white rounded-2xl border border-stone-200 p-5 grid sm:grid-cols-2 gap-4 text-sm">
  {{ csrf_field() }}
  <label class="block sm:col-span-2">ชื่อร้าน<input name="company_name" value="{{ S.company_name }}" class="mt-1 w-full rounded border border-stone-300 px-2 py-1.5"></label>
  <label class="block sm:col-span-2">สโลแกน<input name="tagline" value="{{ S.tagline }}" class="mt-1 w-full rounded border border-stone-300 px-2 py-1.5"></label>
  <label class="block">เบอร์โทร<input name="phone" value="{{ S.phone }}" class="mt-1 w-full rounded border border-stone-300 px-2 py-1.5"></label>
  <label class="block">LINE ID<input name="line_id" value="{{ S.line_id }}" class="mt-1 w-full rounded border border-stone-300 px-2 py-1.5"></label>
  <label class="block sm:col-span-2">ที่อยู่<textarea name="address" rows="2" class="mt-1 w-full rounded border border-stone-300 px-2 py-1.5">{{ S.address }}</textarea></label>
  <div class="sm:col-span-2 border-t pt-4 font-semibold">การคำนวณต้นทุน / ราคา</div>
  <label class="block">% เผื่อเศษวัสดุ (อลูมิเนียม มุ้ง กระจก)<input name="waste_pct" type="number" step="0.1" min="0" value="{{ S.waste_pct }}" class="mt-1 w-full rounded border border-stone-300 px-2 py-1.5"></label>
  <label class="block">ปัดราคาขายขึ้นทีละ (บาท)<input name="round_to" type="number" step="1" min="0" value="{{ S.round_to }}" class="mt-1 w-full rounded border border-stone-300 px-2 py-1.5"></label>
  <div class="sm:col-span-2 flex justify-end"><button class="px-6 py-2 rounded-lg bg-stone-900 text-white">บันทึก</button></div>
</form>
<p class="text-xs text-stone-500 mt-4">รหัสผ่านผู้ดูแลตั้งผ่าน environment variable <code>ADMIN_USER</code> / <code>ADMIN_PASSWORD</code> และ <code>SECRET_KEY</code></p>
{% endblock %}
"""

app.jinja_loader = DictLoader(TEMPLATES)
init_db()

if __name__ == "__main__":
    print(f" * ร้าน: http://127.0.0.1:5000   หลังบ้าน: http://127.0.0.1:5000/admin  (DB: {DB_PATH})")
    app.run(debug=os.environ.get("FLASK_DEBUG", "1") == "1", host="127.0.0.1", port=int(os.environ.get("PORT", 5000)))
