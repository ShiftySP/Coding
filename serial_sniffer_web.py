import threading
import time
import json
from queue import Queue

from flask import Flask, Response, request, jsonify

# Try to import pyserial's Serial and list_ports
try:
    import serial
    from serial import Serial as _Serial
    from serial import SerialException
    import serial.tools.list_ports
    SerialClass = _Serial
except ImportError:
    serial = None
    SerialClass = None
    class SerialException(Exception):
        """Fallback SerialException if pyserial is missing."""

app = Flask(__name__)

ser_a = None
ser_b = None
running = False
data_queue = Queue()
bytes_a_to_b = 0
bytes_b_to_a = 0


def list_ports():
    if serial is None:
        return []
    return [p.device for p in serial.tools.list_ports.comports()]


def reader(src, dst, direction):
    global bytes_a_to_b, bytes_b_to_a, running
    while running:
        try:
            if src and src.in_waiting:
                data = src.read(src.in_waiting)
                if dst:
                    dst.write(data)
                ts = time.time()
                if direction == 'A->B':
                    bytes_a_to_b += len(data)
                else:
                    bytes_b_to_a += len(data)
                data_queue.put({
                    'dir': direction,
                    'data': data.hex(),
                    'timestamp': ts,
                    'bytes_a_to_b': bytes_a_to_b,
                    'bytes_b_to_a': bytes_b_to_a,
                })
            else:
                time.sleep(0.01)
        except SerialException:
            data_queue.put({'dir': direction, 'error': 'serial error'})
            break


@app.route('/ports')
def ports():
    return jsonify(list_ports())


@app.post('/configure')
def configure():
    global ser_a, ser_b, running, bytes_a_to_b, bytes_b_to_a
    cfg = request.get_json()
    port_a = cfg.get('port_a')
    port_b = cfg.get('port_b')
    baudrate = int(cfg.get('baudrate', 9600))
    databits = int(cfg.get('databits', 8))
    parity = cfg.get('parity', 'N')
    stopbits = int(cfg.get('stopbits', 1))
    enable_a = cfg.get('enable_a', True)
    enable_b = cfg.get('enable_b', True)

    if running:
        return jsonify({'status': 'already running'}), 400

    if SerialClass is None:
        return jsonify({'error': 'pyserial not installed'}), 500

    try:
        if enable_a:
            ser_a = SerialClass(port_a, baudrate=baudrate, bytesize=databits,
                                parity=parity, stopbits=stopbits, timeout=0)
        if enable_b:
            ser_b = SerialClass(port_b, baudrate=baudrate, bytesize=databits,
                                parity=parity, stopbits=stopbits, timeout=0)
    except SerialException as e:
        return jsonify({'error': str(e)}), 500

    running = True
    bytes_a_to_b = 0
    bytes_b_to_a = 0
    if enable_a:
        threading.Thread(target=reader, args=(ser_a, ser_b if enable_b else None, 'A->B'), daemon=True).start()
    if enable_b:
        threading.Thread(target=reader, args=(ser_b, ser_a if enable_a else None, 'B->A'), daemon=True).start()

    return jsonify({'status': 'ok'})


@app.post('/stop')
def stop():
    global running, ser_a, ser_b
    running = False
    time.sleep(0.1)
    if ser_a:
        ser_a.close()
        ser_a = None
    if ser_b:
        ser_b.close()
        ser_b = None
    return jsonify({'status': 'stopped'})


@app.post('/send')
def send():
    port = request.json.get('port', 'A')
    data = request.json.get('data', '')
    mode = request.json.get('mode', 'ascii').lower()
    target = ser_a if port == 'A' else ser_b
    if not target:
        return jsonify({'error': 'port not open'}), 400
    try:
        if mode == 'hex':
            to_send = bytes.fromhex(data)
        elif mode == 'bin':
            to_send = int(data, 2).to_bytes((len(data)+7)//8, 'big')
        else:
            to_send = data.encode('utf-8')
        target.write(to_send)
        return jsonify({'status': 'sent', 'bytes': len(to_send)})
    except ValueError as e:
        return jsonify({'error': str(e)}), 400


def event_stream():
    while True:
        item = data_queue.get()
        yield f"data: {json.dumps(item)}\n\n"


@app.route('/stream')
def stream():
    return Response(event_stream(), mimetype='text/event-stream')


INDEX_HTML = """
<!DOCTYPE html>
<html>
<head>
    <meta charset="utf-8" />
    <title>Serial Sniffer Web</title>
    <style>
        body { font-family: sans-serif; margin: 20px; }
        #log { border: 1px solid #ccc; height: 300px; overflow: auto; white-space: pre; }
    </style>
</head>
<body>
<h1>Serial Sniffer Web</h1>
<div>
    <label>Port A: <select id="portA"></select></label>
    <label>Port B: <select id="portB"></select></label>
    <label>Baud: <input id="baud" value="9600" size="6"/></label>
    <button onclick="start()">Start</button>
    <button onclick="stop()">Stop</button>
</div>
<div>
    <label>Display: <select id="display"><option>ascii</option><option>hex</option><option>bin</option></select></label>
</div>
<div id="log"></div>
<div>
    <label>Send Port: <select id="sendPort"><option>A</option><option>B</option></select></label>
    <input id="cmd" placeholder="command"/>
    <select id="cmdMode"><option value="ascii">ASCII</option><option value="hex">HEX</option><option value="bin">BIN</option></select>
    <button onclick="sendCmd()">Send</button>
</div>
<div>
    <label>Auto-send every <input id="interval" value="" size="4"/>s</label>
    <button onclick="toggleAuto()" id="autoBtn">Start Auto</button>
</div>
<div>Bytes A→B: <span id="cntAB">0</span> | Bytes B→A: <span id="cntBA">0</span></div>
<script>
let evt;
let autoTimer=null;
function loadPorts(){
 fetch('/ports').then(r=>r.json()).then(list=>{
  const selA=document.getElementById('portA');
  const selB=document.getElementById('portB');
  selA.innerHTML=''; selB.innerHTML='';
  list.forEach(p=>{ selA.innerHTML += `<option>${p}</option>`; selB.innerHTML += `<option>${p}</option>`; });
 });
}
function start(){
 const cfg={
  port_a:document.getElementById('portA').value,
  port_b:document.getElementById('portB').value,
  baudrate:document.getElementById('baud').value
 };
 fetch('/configure',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify(cfg)});
 evt=new EventSource('/stream');
 evt.onmessage=e=>{
  const obj=JSON.parse(e.data);
  if(obj.error){ console.log(obj.error); return; }
  const mode=document.getElementById('display').value;
  let text='';
  const bytes=hexToBytes(obj.data);
  if(mode==='hex') text=obj.data;
  else if(mode==='bin') text=bytesToBin(bytes);
  else text=bytesToAscii(bytes);
  const log=document.getElementById('log');
  log.textContent += `${obj.dir} ${text}\n`;
  log.scrollTop=log.scrollHeight;
  document.getElementById('cntAB').textContent=obj.bytes_a_to_b;
  document.getElementById('cntBA').textContent=obj.bytes_b_to_a;
 };
}
function stop(){
 fetch('/stop',{method:'POST'});
 if(evt){evt.close();}
}
function sendCmd(){
 const data=document.getElementById('cmd').value;
 const port=document.getElementById('sendPort').value;
 const mode=document.getElementById('cmdMode').value;
 fetch('/send',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({port:port,data:data,mode:mode})});
}
function toggleAuto(){
 if(autoTimer){ clearInterval(autoTimer); autoTimer=null; document.getElementById('autoBtn').textContent='Start Auto'; return; }
 const interval=parseFloat(document.getElementById('interval').value);
 if(!interval){return;}
 autoTimer=setInterval(sendCmd,interval*1000);
 document.getElementById('autoBtn').textContent='Stop Auto';
}
function hexToBytes(hex){
 const bytes=[]; for(let c=0;c<hex.length;c+=2) bytes.push(parseInt(hex.substr(c,2),16));
 return bytes;
}
function bytesToAscii(arr){ return String.fromCharCode(...arr); }
function bytesToBin(arr){ return arr.map(b=>b.toString(2).padStart(8,'0')).join(' '); }
loadPorts();
</script>
</body>
</html>
"""


@app.route('/')
def index():
    return INDEX_HTML


if __name__ == '__main__':
    app.run(debug=True, port=5000)
