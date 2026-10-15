import bpy
import bmesh
import math
import os
import random
import socket
import struct
import tempfile
import threading
import time
import traceback
import json
import wave
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import urlparse, parse_qs
from mathutils import Matrix, Vector
 
# =============================================================================
# CONFIG
# =============================================================================
PORT = 8000
MAX_SPEED = 2.0          # scene units per second at full joystick
TURN_SPEED = 2.2         # radians per second at full joystick
FOLLOW_CAM = True        # camera follows the creeper (set False to orbit freely)
CAM_DIST, CAM_H = 3.4, 1.9
ADD_SOUND = True         # hiss sound played by Blender while in a gas zone
GAS_WARN, GAS_ALARM = 150, 300
SENSOR_RANGE = 5.0       # ultrasonic range in scene units
UNIT_CM = 16.0           # 1 scene unit = 16 cm  (creeper is about 28 cm tall)
PX = 1.0 / 16.0          # one Minecraft "pixel" in scene units
START = (0.0, -2.2)
 
scene = bpy.context.scene
ns = bpy.app.driver_namespace
 
# =============================================================================
# STOP ANYTHING FROM A PREVIOUS RUN
# =============================================================================
try:
    old = ns.get('creeper_srv')
    if old:
        old.shutdown()
        old.server_close()
except Exception:
    pass
try:
    old_tick = ns.get('creeper_tick')
    if old_tick and bpy.app.timers.is_registered(old_tick):
        bpy.app.timers.unregister(old_tick)
except Exception:
    pass
 
# =============================================================================
# SHARED STATE (the web server thread writes CTL, Blender's timer reads it)
# =============================================================================
CTL = {'f': 0.0, 't': 0.0, 'stamp': 0.0, 'reset': False}
STATUS = {'gas': 20, 'dist': None, 'state': 'SAFE', 'alarm': False}
 
# =============================================================================
# SCENE HELPERS
# =============================================================================
def clean_scene():
    for o in list(bpy.data.objects):
        bpy.data.objects.remove(o, do_unlink=True)
    for coll in (bpy.data.meshes, bpy.data.curves, bpy.data.materials,
                 bpy.data.cameras, bpy.data.lights):
        for d in list(coll):
            coll.remove(d)
 
 
_mats, _sock, _cur = {}, {}, {}
 
 
def material(name, rgb):
    if name in _mats:
        return _mats[name]
    m = bpy.data.materials.new(name)
    try:
        m.use_nodes = True
    except Exception:
        pass
    m.diffuse_color = (rgb[0], rgb[1], rgb[2], 1.0)
    b = m.node_tree.nodes.get('Principled BSDF') if m.node_tree else None
    if b:
        b.inputs['Base Color'].default_value = (rgb[0], rgb[1], rgb[2], 1.0)
        b.inputs['Roughness'].default_value = 0.85
        _sock[m] = b.inputs['Base Color']
    _mats[name] = m
    _cur[m] = rgb
    return m
 
 
def set_color(m, rgb):
    """Live colour change (only touches Blender when the colour really changes)."""
    if _cur.get(m) == rgb:
        return
    _cur[m] = rgb
    m.diffuse_color = (rgb[0], rgb[1], rgb[2], 1.0)
    s = _sock.get(m)
    if s:
        s.default_value = (rgb[0], rgb[1], rgb[2], 1.0)
 
 
def mesh_object(name, bm, mat, parent=None, loc=(0, 0, 0)):
    me = bpy.data.meshes.new(name)
    bm.to_mesh(me)
    bm.free()
    me.materials.append(mat)
    ob = bpy.data.objects.new(name, me)
    scene.collection.objects.link(ob)
    if parent is not None:
        ob.parent = parent
    ob.location = loc
    return ob
 
 
def box(name, size, loc, mat, parent=None, u=PX):
    bm = bmesh.new()
    bmesh.ops.create_cube(bm, size=1.0)
    for v in bm.verts:
        v.co.x *= size[0] * u
        v.co.y *= size[1] * u
        v.co.z *= size[2] * u
    return mesh_object(name, bm, mat, parent, (loc[0] * u, loc[1] * u, loc[2] * u))
 
 
def cyl(name, radius_px, depth_px, loc_px, mat, parent=None, axis='Y'):
    bm = bmesh.new()
    bmesh.ops.create_cone(bm, cap_ends=True, cap_tris=False, segments=20,
                          radius1=radius_px * PX, radius2=radius_px * PX,
                          depth=depth_px * PX)
    if axis == 'Y':
        bmesh.ops.rotate(bm, cent=(0, 0, 0),
                         matrix=Matrix.Rotation(math.pi / 2, 3, 'X'), verts=bm.verts)
    return mesh_object(name, bm, mat, parent,
                       (loc_px[0] * PX, loc_px[1] * PX, loc_px[2] * PX))
 
 
def disc(name, radius, loc, mat):
    bm = bmesh.new()
    bmesh.ops.create_circle(bm, cap_ends=True, radius=radius, segments=48)
    return mesh_object(name, bm, mat, None, loc)
 
 
def empty(name, parent=None, loc=(0, 0, 0)):
    e = bpy.data.objects.new(name, None)
    e.empty_display_type = 'PLAIN_AXES'
    e.empty_display_size = 0.15
    scene.collection.objects.link(e)
    if parent is not None:
        e.parent = parent
    e.location = loc
    return e
 
 
# =============================================================================
# BUILD THE WORLD + CREEPER
# =============================================================================
clean_scene()
 
BODY_RGB = (0.20, 0.58, 0.16)
HEAD_RGB = (0.27, 0.68, 0.22)
LEG_RGB = (0.15, 0.46, 0.12)
LCD_GREEN = (0.55, 0.95, 0.45)
LCD_RED = (1.00, 0.20, 0.12)
LED_OFF = (0.25, 0.25, 0.25)
LED_ON = (0.10, 1.00, 0.20)
WHITE = (1.0, 1.0, 1.0)
 
M_BODY = material('Creeper_Body', BODY_RGB)
M_HEAD = material('Creeper_Head', HEAD_RGB)
M_LEG = material('Creeper_Legs', LEG_RGB)
M_LCD = material('LCD_Screen', LCD_GREEN)
M_PIXEL = material('LCD_Pixel', (0.02, 0.05, 0.02))
M_DARK = material('Dark_Plastic', (0.05, 0.05, 0.06))
M_LENS = material('Camera_Lens', (0.02, 0.05, 0.25))
M_LED = material('Status_LED', LED_OFF)
M_PCB = material('PCB_Blue', (0.04, 0.18, 0.55))
M_METAL = material('Sensor_Metal', (0.75, 0.76, 0.80))
M_BATT = material('AA_Battery_Pack', (0.95, 0.75, 0.10))
M_SERVO = material('Servo_Blue', (0.10, 0.25, 0.80))
M_ARM = material('Arm_Grey', (0.55, 0.57, 0.60))
 
root = empty('Pet_Root')
swell = empty('Pet_Swell', root)
 
legs = {}
for nm, lx, ly in (('FL', -2, 2), ('FR', 2, 2), ('BL', -2, -2), ('BR', 2, -2)):
    piv = empty('Leg_' + nm, swell, (lx * PX, ly * PX, 6 * PX))
    box('Leg_' + nm + '_mesh', (4, 4, 6), (0, 0, -3), M_LEG, piv)
    legs[nm] = piv
 
box('Body', (8, 4, 12), (0, 0, 12), M_BODY, swell)
box('Head', (8, 8, 8), (0, 0, 22), M_HEAD, swell)
box('LCD_Screen', (6, 0.6, 6), (0, 4.3, 22), M_LCD, swell)
FACE = ["........", "........", ".XX..XX.", ".XX..XX.",
        "...XX...", "..XXXX..", "..XXXX..", "..X..X.."]
for r, row in enumerate(FACE):
    for c, ch in enumerate(row):
        if ch == 'X':
            box('LCD_px_%d_%d' % (r, c), (0.75, 0.4, 0.75),
                ((c - 3.5) * 0.75, 4.7, 22 + (3.5 - r) * 0.75), M_PIXEL, swell)
 
box('ESP32S3_CAM', (3, 2, 2.4), (0, 3.2, 27.2), M_DARK, swell)
cyl('Camera_Lens', 0.8, 1.0, (0, 4.7, 27.2), M_LENS, swell)
box('Status_LED', (1.5, 1.5, 1.5), (-3, 0, 26.75), M_LED, swell)
box('Ultrasonic_Board', (8, 0.8, 3.6), (0, 2.4, 9.5), M_PCB, swell)
cyl('Ultrasonic_TX', 1.45, 1.8, (-2.3, 3.7, 9.5), M_METAL, swell)
cyl('Ultrasonic_RX', 1.45, 1.8, (2.3, 3.7, 9.5), M_METAL, swell)
box('AA_Battery_Pack', (6, 2.5, 7), (0, -3.5, 12), M_BATT, swell)
box('ESP32_Board', (5, 1, 3), (0, -2.6, 16), M_PCB, swell)
 
# servo arm, held in a raised "tucked" pose while driving
L1 = L2 = 11 * PX
 
 
def ik(r, z):
    c = (r * r + z * z - L1 * L1 - L2 * L2) / (2 * L1 * L2)
    c = max(-1.0, min(1.0, c))
    q2 = -math.acos(c)
    q1 = math.atan2(z, r) - math.atan2(L2 * math.sin(q2), L1 + L2 * math.cos(q2))
    return q1, q2
 
 
box('Shoulder_Servo', (5, 5, 5), (0, 2, 15), M_SERVO, root)
arm = empty('Arm_Shoulder', root, (0, 2 * PX, 15 * PX))
box('Upper_Arm', (3, 11, 3), (0, 5.5, 0), M_ARM, arm)
elbow = empty('Arm_Elbow', arm, (0, 11 * PX, 0))
box('Elbow_Servo', (4, 4, 4), (0, 0, 0), M_SERVO, elbow)
box('Forearm', (3, 7, 3), (0, 3.5, 0), M_ARM, elbow)
box('Palm', (13, 1, 3), (0, 7.5, 0), M_ARM, elbow)
for sgn, nm in ((-1, 'Finger_L'), (1, 'Finger_R')):
    f = box(nm, (1.5, 6, 3), (0, 0, 0), M_ARM, elbow)
    f.location = (sgn * 6.2 * PX, 11 * PX, 0)
q1, q2 = ik(9 * PX, 8 * PX)
arm.rotation_euler = (q1, 0, 0)
elbow.rotation_euler = (q2, 0, 0)
 
# desk + grass
box('Grass_Top', (40, 40, 0.4), (0, 0, -3.4), material('Grass', (0.25, 0.60, 0.20)), u=1.0)
box('Dirt', (40, 40, 1.0), (0, 0, -3.9), material('Dirt', (0.38, 0.25, 0.14)), u=1.0)
PLANK_A = material('Oak_A', (0.62, 0.45, 0.25))
PLANK_B = material('Oak_B', (0.55, 0.39, 0.21))
for i, x in enumerate((-4, -2, 0, 2, 4)):
    box('Desk_Plank_%d' % i, (1.99, 6.5, 0.3), (x, 0, -0.15),
        PLANK_A if i % 2 == 0 else PLANK_B, u=1.0)
M_LEGWOOD = material('Desk_Leg', (0.40, 0.28, 0.15))
for sx in (-4.6, 4.6):
    for sy in (-2.9, 2.9):
        box('Desk_Leg', (0.4, 0.4, 2.9), (sx, sy, -1.75), M_LEGWOOD, u=1.0)
 
# obstacles: (cx, cy, width, depth) are also used for collision + ultrasonic
M_RED = material('Obj_Red', (0.90, 0.12, 0.10))
M_BLUE = material('Obj_Blue', (0.12, 0.30, 0.95))
M_STONE = material('Obj_Stone', (0.50, 0.50, 0.53))
OBST = []
box('Red_Cube', (0.4, 0.4, 0.4), (-3.2, 1.6, 0.2), M_RED, u=1.0)
OBST.append((-3.2, 1.6, 0.4, 0.4))
box('Blue_Cube', (0.4, 0.4, 0.4), (2.2, 1.5, 0.2), M_BLUE, u=1.0)
OBST.append((2.2, 1.5, 0.4, 0.4))
cyl('Red_Can', 0.2 / PX, 0.4 / PX, (-0.8 / PX, 0.4 / PX, 0.2 / PX), M_RED, axis='Z')
OBST.append((-0.8, 0.4, 0.4, 0.4))
box('Stone_Block', (0.9, 0.9, 0.9), (-0.3, 2.2, 0.45), M_STONE, u=1.0)
OBST.append((-0.3, 2.2, 0.9, 0.9))
box('Stone_Block_2', (0.7, 1.4, 0.7), (3.6, -0.2, 0.35), M_STONE, u=1.0)
OBST.append((3.6, -0.2, 0.7, 1.4))
 
# toxic gas zones (reading rises as the creeper gets closer to the centre)
M_GAS = material('Gas_Zone', (0.95, 0.15, 0.08))
try:
    M_GAS.blend_method = 'BLEND'
except Exception:
    pass
try:
    M_GAS.node_tree.nodes.get('Principled BSDF').inputs['Alpha'].default_value = 0.55
    M_GAS.diffuse_color = (0.95, 0.15, 0.08, 0.55)
except Exception:
    pass
ZONES = [(2.4, -1.2, 1.4), (-2.9, -0.9, 1.3)]
for i, (zx, zy, zr) in enumerate(ZONES):
    disc('Gas_Zone_%d' % i, zr, (zx, zy, 0.02), M_GAS)
 
# camera, light, sky
cam_data = bpy.data.cameras.new('Camera')
cam_data.lens = 35
cam = bpy.data.objects.new('Camera', cam_data)
scene.collection.objects.link(cam)
cam.location = (START[0], START[1] - CAM_DIST, CAM_H)
look = empty('Camera_Target', None, (START[0], START[1], 0.9))
trk = cam.constraints.new('TRACK_TO')
trk.target = look
trk.track_axis = 'TRACK_NEGATIVE_Z'
trk.up_axis = 'UP_Y'
scene.camera = cam
 
sun_data = bpy.data.lights.new('Sun', 'SUN')
sun_data.energy = 3.5
sun = bpy.data.objects.new('Sun', sun_data)
scene.collection.objects.link(sun)
sun.rotation_euler = (math.radians(50), math.radians(10), math.radians(30))
 
world = bpy.data.worlds.new('MC_Sky')
try:
    world.use_nodes = True
except Exception:
    pass
if world.node_tree:
    bg = world.node_tree.nodes.get('Background')
    if bg:
        bg.inputs[0].default_value = (0.53, 0.81, 0.92, 1.0)
        bg.inputs[1].default_value = 1.0
scene.world = world
try:
    scene.view_settings.view_transform = 'Standard'
except Exception:
    pass
 
# show the camera view in the first 3D viewport
try:
    for w in bpy.context.window_manager.windows:
        for a in w.screen.areas:
            if a.type == 'VIEW_3D':
                a.spaces.active.region_3d.view_perspective = 'CAMERA'
                raise StopIteration
except StopIteration:
    pass
except Exception:
    pass
 
# =============================================================================
# HISS SOUND (played by Blender through the aud module)
# =============================================================================
HISS = {'dev': None, 'snd': None, 'h': None, 'on': False, 'failed': False}
 
 
def make_hiss_wav():
    d = bpy.app.tempdir or tempfile.gettempdir()
    path = os.path.join(d, 'creeper_hiss_loop.wav')
    rate, n = 22050, 22050
    rr = random.Random(3)
    prev, data = 0.0, bytearray()
    for i in range(n):
        x = rr.uniform(-1, 1)
        y = x - 0.9 * prev
        prev = x
        env = 0.8 + 0.2 * math.sin(2 * math.pi * 8 * i / rate)
        data += struct.pack('<h', int(max(-1.0, min(1.0, y * 0.55 * env)) * 32767))
    with wave.open(path, 'wb') as w:
        w.setnchannels(1)
        w.setsampwidth(2)
        w.setframerate(rate)
        w.writeframes(bytes(data))
    return path
 
 
def hiss(on):
    if not ADD_SOUND or HISS['failed'] or on == HISS['on']:
        return
    HISS['on'] = on
    try:
        import aud
        if on:
            if HISS['dev'] is None:
                HISS['dev'] = aud.Device()
                HISS['snd'] = aud.Sound.file(make_hiss_wav())
            HISS['h'] = HISS['dev'].play(HISS['snd'])
            HISS['h'].loop_count = -1
            HISS['h'].volume = 0.7
        elif HISS['h'] is not None:
            HISS['h'].stop()
            HISS['h'] = None
    except Exception:
        HISS['failed'] = True
        print('Creeper: could not play hiss sound (aud unavailable).')
 
 
# =============================================================================
# PHONE PAGE + WEB SERVER
# =============================================================================
PAGE = """<!DOCTYPE html>
<html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1,maximum-scale=1,user-scalable=no,viewport-fit=cover">
<title>Creeper Remote</title>
<style>
html,body{height:100%;margin:0;background:#0f1e2a;color:#e6f0f6;font-family:system-ui,sans-serif;
touch-action:none;-webkit-user-select:none;user-select:none;overflow:hidden}
body{display:flex;flex-direction:column;align-items:center;justify-content:space-between;
padding:calc(10px + env(safe-area-inset-top)) 16px calc(24px + env(safe-area-inset-bottom));box-sizing:border-box;transition:background .2s}
body.alarm{background:#5a0f0a}
#top{text-align:center;width:100%;max-width:420px}
h1{font-size:20px;margin:6px 0}
#stat{font-size:24px;font-weight:700;color:#4ade80}
#stat.WARNING{color:#fbbf24}#stat.DANGER{color:#ff7b6b}
.row{display:flex;justify-content:space-around;margin-top:8px;font-size:17px}
#net{font-size:12px;opacity:.7;margin-top:8px}
#stick{position:relative;width:250px;height:250px;border-radius:50%;border:4px solid #e6f0f6;background:#16293a}
#knob{position:absolute;left:50%;top:50%;width:100px;height:100px;margin:-50px;border-radius:50%;background:#4ade80;opacity:.85}
button{font-size:15px;padding:10px 18px;border-radius:10px;border:2px solid #e6f0f6;background:transparent;color:#e6f0f6}
</style></head><body>
<div id="top"><h1>Creeper Scout</h1>
<div id="stat">SAFE</div>
<div class="row"><div>Gas <b id="gas">0</b> ppm</div><div>Front <b id="dist">-</b></div></div>
<div id="net">connecting...</div></div>
<div id="stick"><div id="knob"></div></div>
<button id="rst">Reset position</button>
<script>
var $=function(i){return document.getElementById(i)};
var st=$('stick'),kn=$('knob'),jx=0,jy=0,pid=null,busy=false,lastVib=0;
function mv(e){var r=st.getBoundingClientRect(),dx=e.clientX-(r.left+r.width/2),dy=e.clientY-(r.top+r.height/2),
m=Math.hypot(dx,dy),R=r.width/2-12;if(m>R){dx*=R/m;dy*=R/m}jx=dx/R;jy=dy/R;
kn.style.transform='translate('+dx+'px,'+dy+'px)'}
st.addEventListener('pointerdown',function(e){pid=e.pointerId;st.setPointerCapture(pid);mv(e)});
st.addEventListener('pointermove',function(e){if(e.pointerId===pid)mv(e)});
function end(e){if(e.pointerId===pid){pid=null;jx=jy=0;kn.style.transform=''}}
st.addEventListener('pointerup',end);st.addEventListener('pointercancel',end);
$('rst').addEventListener('click',function(){fetch('/reset',{cache:'no-store'})});
function ui(s){
  $('gas').textContent=s.gas;
  $('dist').textContent=s.dist==null?'clear':s.dist+' cm';
  $('stat').textContent=s.alarm?'DANGER: TOXIC GAS':s.state;
  $('stat').className=s.state;
  document.body.className=s.alarm?'alarm':'';
  if(s.alarm&&Date.now()-lastVib>800){lastVib=Date.now();if(navigator.vibrate)navigator.vibrate(200)}
}
setInterval(function(){
  if(busy)return;busy=true;
  fetch('/ctl?f='+(-jy).toFixed(2)+'&t='+jx.toFixed(2),{cache:'no-store'})
  .then(function(r){return r.json()})
  .then(function(s){ui(s);$('net').textContent='connected to Blender'})
  .catch(function(){$('net').textContent='connection lost - check WiFi'})
  .then(function(){busy=false});
},60);
</script></body></html>"""
 
 
def _num(q, key):
    try:
        return max(-1.0, min(1.0, float(q.get(key, ['0'])[0])))
    except Exception:
        return 0.0
 
 
class Handler(BaseHTTPRequestHandler):
    def log_message(self, *a):
        pass
 
    def _send(self, code, ctype, body):
        b = body.encode('utf-8')
        self.send_response(code)
        self.send_header('Content-Type', ctype)
        self.send_header('Content-Length', str(len(b)))
        self.send_header('Cache-Control', 'no-store')
        self.end_headers()
        self.wfile.write(b)
 
    def do_GET(self):
        u = urlparse(self.path)
        if u.path == '/ctl':
            q = parse_qs(u.query)
            CTL['f'] = _num(q, 'f')
            CTL['t'] = _num(q, 't')
            CTL['stamp'] = time.time()
            self._send(200, 'application/json', json.dumps(STATUS))
        elif u.path == '/reset':
            CTL['reset'] = True
            self._send(200, 'application/json', '{}')
        elif u.path == '/favicon.ico':
            self._send(204, 'text/plain', '')
        else:
            self._send(200, 'text/html; charset=utf-8', PAGE)
 
 
def lan_ip():
    s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    try:
        s.connect(('8.8.8.8', 80))
        return s.getsockname()[0]
    except Exception:
        try:
            return socket.gethostbyname(socket.gethostname())
        except Exception:
            return '127.0.0.1'
    finally:
        s.close()
 
 
srv, port = None, PORT
for port in range(PORT, PORT + 10):
    try:
        srv = ThreadingHTTPServer(('0.0.0.0', port), Handler)
        break
    except OSError:
        continue
if srv is None:
    raise RuntimeError('Creeper: no free port between %d and %d' % (PORT, PORT + 9))
threading.Thread(target=srv.serve_forever, daemon=True).start()
ns['creeper_srv'] = srv
 
# =============================================================================
# REAL-TIME LOOP (runs inside Blender ~30 times per second)
# =============================================================================
S = dict(x=START[0], y=START[1], th=0.0, ph=0.0, sw=1.0, last=time.time(), alarm=False)
CR = 0.45                          # creeper collision radius
BOUND_X, BOUND_Y = 4.55, 3.0       # keep the creeper on the desk
LEG_SIGN = (('FL', 1), ('BR', 1), ('FR', -1), ('BL', -1))
 
 
def ray_aabb(ox, oy, dx, dy, b):
    tmin, tmax = 0.0, 1e9
    for o, d, lo, hi in ((ox, dx, b[0] - b[2] / 2, b[0] + b[2] / 2),
                         (oy, dy, b[1] - b[3] / 2, b[1] + b[3] / 2)):
        if abs(d) < 1e-9:
            if o < lo or o > hi:
                return None
        else:
            t1, t2 = (lo - o) / d, (hi - o) / d
            if t1 > t2:
                t1, t2 = t2, t1
            tmin, tmax = max(tmin, t1), min(tmax, t2)
            if tmin > tmax:
                return None
    return tmin
 
 
def redraw():
    try:
        for w in bpy.context.window_manager.windows:
            for a in w.screen.areas:
                if a.type == 'VIEW_3D':
                    a.tag_redraw()
    except Exception:
        pass
 
 
def step():
    now = time.time()
    dt = min(0.1, max(0.0, now - S['last']))
    S['last'] = now
 
    if CTL['reset']:
        CTL['reset'] = False
        S['x'], S['y'], S['th'] = START[0], START[1], 0.0
 
    f, t = CTL['f'], CTL['t']
    if now - CTL['stamp'] > 0.6:      # fail-safe: phone stopped talking -> stop
        f = t = 0.0
    connected = (now - CTL['stamp']) < 1.5
 
    # --- drive ---
    S['th'] -= t * TURN_SPEED * dt
    sp = f * MAX_SPEED * dt
    S['x'] += -math.sin(S['th']) * sp
    S['y'] += math.cos(S['th']) * sp
    for (cx, cy, w, d) in OBST:        # collision with objects
        nx = max(cx - w / 2, min(S['x'], cx + w / 2))
        ny = max(cy - d / 2, min(S['y'], cy + d / 2))
        dx, dy = S['x'] - nx, S['y'] - ny
        dist = math.hypot(dx, dy)
        if dist < CR:
            if dist < 1e-4:
                dx, dy, dist = 0.0, 1.0, 1.0
            S['x'] += dx / dist * (CR - dist)
            S['y'] += dy / dist * (CR - dist)
    S['x'] = max(-BOUND_X, min(BOUND_X, S['x']))
    S['y'] = max(-BOUND_Y, min(BOUND_Y, S['y']))
 
    # --- walk animation ---
    mag = max(abs(f), abs(t) * 0.6)
    S['ph'] += mag * dt * 10.0
    amp = mag * 0.55
    for nm, sg in LEG_SIGN:
        legs[nm].rotation_euler = (math.sin(S['ph']) * amp * sg, 0, 0)
    root.location = (S['x'], S['y'], 0.0)
    root.rotation_euler = (0, 0, S['th'])
 
    # --- gas sensor (simulated) ---
    gas = 20.0
    for zx, zy, zr in ZONES:
        gas += max(0.0, 1.0 - math.hypot(S['x'] - zx, S['y'] - zy) / zr) * 700.0
    gas = int(gas)
    alarm = gas > GAS_ALARM
    state = 'DANGER' if alarm else ('WARNING' if gas > GAS_WARN else 'SAFE')
 
    # --- hiss effects ---
    target = 1.14 + 0.06 * math.sin(now * 14.0) if alarm else 1.0
    S['sw'] += (target - S['sw']) * 0.3
    swell.scale = (S['sw'], S['sw'], S['sw'])
    flash = alarm and int(now * 7.5) % 2 == 0
    set_color(M_BODY, WHITE if flash else BODY_RGB)
    set_color(M_HEAD, WHITE if flash else HEAD_RGB)
    set_color(M_LEG, WHITE if flash else LEG_RGB)
    set_color(M_LCD, LCD_RED if alarm else LCD_GREEN)
    set_color(M_LED, LED_ON if connected else LED_OFF)
    hiss(alarm)
 
    # --- ultrasonic sensor ---
    fx, fy = -math.sin(S['th']), math.cos(S['th'])
    ox, oy = S['x'] + fx * 0.25, S['y'] + fy * 0.25
    best = None
    for b in OBST:
        h = ray_aabb(ox, oy, fx, fy, b)
        if h is not None and h <= SENSOR_RANGE and (best is None or h < best):
            best = h
    STATUS['gas'] = gas
    STATUS['dist'] = None if best is None else int(round(best * UNIT_CM))
    STATUS['state'] = state
    STATUS['alarm'] = alarm
 
    # --- follow camera ---
    look.location = (S['x'], S['y'], 0.9)
    if FOLLOW_CAM:
        goal = Vector((S['x'] - fx * CAM_DIST, S['y'] - fy * CAM_DIST, CAM_H))
        cam.location = cam.location.lerp(goal, min(1.0, dt * 5.0))
    redraw()
 
 
def tick():
    try:
        step()
    except Exception:
        traceback.print_exc()
    return 1.0 / 30.0
 
 
ns['creeper_tick'] = tick
bpy.app.timers.register(tick, persistent=False)
scene.frame_set(1)
 
ip = lan_ip()
print('=' * 60)
print(' Creeper phone control is running.')
print(' On your phone (same WiFi) open:  http://%s:%d' % (ip, port))
print('=' * 60)
 
