package com.example.myapp

import android.app.Activity
import android.content.Context
import android.content.Intent
import android.content.SharedPreferences
import android.graphics.Color
import android.graphics.Typeface
import android.net.Uri
import android.os.Bundle
import android.os.ParcelFileDescriptor
import android.provider.DocumentsContract
import android.provider.OpenableColumns
import android.view.KeyEvent
import android.view.View
import android.view.ViewGroup
import android.view.WindowManager
import android.widget.Button
import android.widget.LinearLayout
import android.widget.ProgressBar
import android.widget.ScrollView
import android.widget.TextView
import android.widget.Toast
import java.io.BufferedWriter
import java.io.File
import java.io.FileInputStream
import java.io.FileOutputStream
import java.io.IOException
import java.io.InputStream
import java.io.OutputStream
import java.io.OutputStreamWriter
import java.io.RandomAccessFile
import java.nio.ByteBuffer
import java.nio.channels.FileChannel
import java.text.SimpleDateFormat
import java.util.ArrayList
import java.util.BitSet
import java.util.Date
import java.util.HashMap
import java.util.Locale
import java.util.concurrent.atomic.AtomicLong

// ===============================================================
// Small helpers / data holders (primitive growable arrays = fast, low memory)
// ===============================================================
private const val MASK = 0xFFFFFFFFL

class CancelEx : Exception("Cancelled")

class IntList {
    var a = IntArray(1024)
    var n = 0
    fun add(v: Int) {
        if (n == a.size) a = a.copyOf(n * 2)
        a[n] = v
        n++
    }
    operator fun get(i: Int): Int = a[i]
}

class LongList {
    var a = LongArray(1024)
    var n = 0
    fun add(v: Long) {
        if (n == a.size) a = a.copyOf(n * 2)
        a[n] = v
        n++
    }
    operator fun get(i: Int): Long = a[i]
}

class FR(val f1: String, val f2: String, val errors: ArrayList<String>)

class Scan(val lines: Int, val idx: LongList, val k: Int)

class Holder {
    @Volatile var v: Scan? = null
    @Volatile var err: Throwable? = null
}

class Stats {
    var processed = 0
    var inserted = 0L
    var outLines = 0L
}

fun rangeStr(a: Long, b: Long): String {
    return if (a != b) "$a-$b" else a.toString()
}

fun clampI(v: Long): Int {
    return if (v > Int.MAX_VALUE) Int.MAX_VALUE else if (v < Int.MIN_VALUE) Int.MIN_VALUE else v.toInt()
}

interface Env {
    fun openIn(which: Int): InputStream          // 1 = file1, 2 = file2, 3 = map
    fun size(which: Int): Long
    fun openChannel(): FileChannel               // random access to file2
    fun openOut(name: String): OutputStream
    fun discard(name: String)
    fun release()
}

// Buffered output (1 MB)
class OutBuf(private val os: OutputStream) {
    private val b = ByteArray(1 shl 20)
    private var n = 0
    var total = 0L

    fun put(v: Int) {
        if (n == b.size) flush()
        b[n] = v.toByte()
        n++
    }

    fun flush() {
        if (n > 0) {
            os.write(b, 0, n)
            total += n
            n = 0
        }
    }
}

// Random-access reader for file2: sparse line index + sliding window
class RR(
    private val ch: FileChannel,
    private val size: Long,
    private val idx: LongList,
    private val kk: Int,
    private val onLoad: () -> Unit
) {
    private val win = ByteArray(1 shl 20)
    private var wStart = 0L
    private var wLen = 0
    private var nextLoad = 32768

    private fun load(pos: Long) {
        nextLoad = if (wLen > 0 && pos == wStart + wLen) minOf(1 shl 20, nextLoad * 2) else 32768
        val want = minOf(nextLoad.toLong(), size - pos).toInt()
        val bb = ByteBuffer.wrap(win, 0, want)
        var got = 0
        while (got < want) {
            val r = ch.read(bb, pos + got)
            if (r < 0) break
            got += r
        }
        wStart = pos
        wLen = got
        onLoad()
    }

    // copies file2 lines s..e (1-based, inclusive) to ob, line endings normalised to \n
    fun copy(s: Int, e: Int, ob: OutBuf) {
        val m = (s - 1) / kk
        var pos = idx[m]
        var line = 1 + m * kk
        var prevCR = false
        var fin = false
        while (!fin && pos < size) {
            if (pos < wStart || pos >= wStart + wLen) {
                load(pos)
                if (wLen == 0) break
            }
            var j = (pos - wStart).toInt()
            while (j < wLen) {
                val b = win[j].toInt()
                j++
                if (prevCR) {
                    prevCR = false
                    if (b == 10) continue
                }
                if (b == 10 || b == 13) {
                    if (line >= s) ob.put(10)
                    if (line == e) {
                        fin = true
                        break
                    }
                    line++
                    if (b == 13) prevCR = true
                } else if (line >= s) {
                    ob.put(b)
                }
            }
            pos = wStart + j
        }
    }
}

// ===============================================================
// The engine: streaming port of the Python script
// ===============================================================
class Engine(
    private val env: Env,
    private val tmp: File,
    private val say: (String) -> Unit,
    private val prog: (String, Int) -> Unit
) {
    @Volatile var cancel = false

    private val eq = "=".repeat(60)
    private val dash = "-".repeat(60)
    private val sb = StringBuilder()
    private var cnt = 0
    private var lastTick = 0L
    private val scanDone = AtomicLong()

    // per-mapping compact storage
    private val mSt = IntList()
    private val mEn = IntList()
    private val mLine = IntList()
    private val mRs = IntList()
    private val r2s = IntList()
    private val r2e = IntList()
    private val fails = HashMap<Int, FR>()
    private val failedBits = BitSet()
    private var failedCount = 0
    private var totalMappings = 0
    private var l1 = 0
    private var l2 = 0
    private var tokOk = true
    private var tmpT = LongArray(1024)
    private var tmpN = 0
    private var procDone = 0L
    private var procTotal = 0L

    private fun chk() {
        if (cancel) throw CancelEx()
    }

    private fun fl() {
        if (sb.isNotEmpty()) {
            val t = sb.toString()
            sb.setLength(0)
            say(t)
        }
    }

    private fun p(s: String) {
        sb.append(s).append("\n")
        cnt++
        if (cnt % 25 == 0) fl()
    }

    private fun tick(stage: String, done: Long, total: Long) {
        val now = System.nanoTime()
        if (now - lastTick < 120000000L) return
        lastTick = now
        val pm = if (total > 0) ((done * 1000L) / total).toInt().coerceIn(0, 1000) else -1
        prog(stage, pm)
    }

    private fun tmpWriter(f: File): BufferedWriter {
        return BufferedWriter(OutputStreamWriter(FileOutputStream(f), Charsets.UTF_8), 1 shl 18)
    }

    private fun wr(os: OutputStream, s: String) {
        os.write(s.toByteArray(Charsets.UTF_8))
    }

    private fun copyFile(f: File, os: OutputStream) {
        val buf = ByteArray(1 shl 18)
        FileInputStream(f).use { ins ->
            while (true) {
                val r = ins.read(buf)
                if (r < 0) break
                os.write(buf, 0, r)
                chk()
            }
        }
    }

    // ---------- pass 1: count lines (and build sparse index for file2) ----------
    private fun scan(which: Int, wantIdx: Boolean, total: Long): Scan {
        val buf = ByteArray(1 shl 20)
        var lines = 0L
        var atStart = true
        var prevCR = false
        var pos = 0L
        var k = 1
        val idx = LongList()
        env.openIn(which).use { ins ->
            while (true) {
                val n = ins.read(buf)
                if (n < 0) break
                chk()
                var i = 0
                while (i < n) {
                    val b = buf[i].toInt()
                    if (prevCR) {
                        prevCR = false
                        if (b == 10) {
                            i++
                            continue
                        }
                    }
                    if (atStart) {
                        lines++
                        if (wantIdx && (lines - 1) % k == 0L) {
                            idx.add(pos + i)
                            if (idx.n >= 2000000) {
                                val h = (idx.n + 1) / 2
                                var q = 0
                                while (q < h) {
                                    idx.a[q] = idx.a[2 * q]
                                    q++
                                }
                                idx.n = h
                                k *= 2
                            }
                        }
                        atStart = false
                    }
                    if (b == 10) {
                        atStart = true
                    } else if (b == 13) {
                        atStart = true
                        prevCR = true
                    }
                    i++
                }
                pos += n
                val d = scanDone.addAndGet(n.toLong())
                tick("Scanning input files", d, total)
            }
        }
        if (lines > Int.MAX_VALUE) throw IOException("File has more than 2,147,483,647 lines (not supported)")
        return Scan(lines.toInt(), idx, k)
    }

    // ---------- pass 2: parse the map file (streaming, no per-line objects) ----------
    private fun tok(lb: ByteArray, a: Int, b: Int): Long {
        var s = a
        var e = b
        while (s < e && (lb[s].toInt() and 0xFF) <= 32) s++
        while (e > s && (lb[e - 1].toInt() and 0xFF) <= 32) e--
        var neg = false
        if (s < e) {
            val c = lb[s].toInt()
            if (c == 45 || c == 43) {
                neg = (c == 45)
                s++
            }
        }
        if (s >= e) {
            tokOk = false
            return 0L
        }
        var v = 0L
        var i = s
        while (i < e) {
            val d = lb[i].toInt() - 48
            if (d < 0 || d > 9) {
                tokOk = false
                return 0L
            }
            if (v < 100000000000000000L) v = v * 10 + d else v = 1000000000000000000L
            i++
        }
        tokOk = true
        return if (neg) -v else v
    }

    private fun badMsg(lb: ByteArray, a: Int, b: Int): String {
        return "invalid literal for int() with base 10: '" + String(lb, a, b - a, Charsets.UTF_8) + "'"
    }

    private fun addParseFail(k: Int, errors: ArrayList<String>, msg: String) {
        errors.add("Parse error: $msg")
        mSt.add(0)
        mEn.add(-1)
        failedBits.set(k)
        failedCount++
        if (fails.size < 100000) fails[k] = FR("N/A", "N/A", errors)
    }

    private fun handleLine(lb: ByteArray, len: Int, lineNum: Int) {
        var s = 0
        var e = len
        while (s < e && (lb[s].toInt() and 0xFF) <= 32) s++
        while (e > s && (lb[e - 1].toInt() and 0xFF) <= 32) e--
        if (s >= e) return
        var eqPos = -1
        var eqCount = 0
        var i = s
        while (i < e) {
            if (lb[i].toInt() == 61) {
                eqCount++
                if (eqPos < 0) eqPos = i
            }
            i++
        }
        if (eqCount == 0) return

        totalMappings++
        val k = mSt.n
        mLine.add(lineNum)
        mRs.add(r2s.n)
        val errors = ArrayList<String>()

        if (eqCount > 1) {
            addParseFail(k, errors, "too many values to unpack (expected 2)")
            return
        }

        // ----- left side -----
        var comma = -1
        var j = s
        while (j < eqPos) {
            if (lb[j].toInt() == 44) {
                comma = j
                break
            }
            j++
        }
        var start1 = 0L
        var end1 = 0L
        var bad: String? = null
        if (comma >= 0) {
            start1 = tok(lb, s, comma)
            if (!tokOk) {
                bad = badMsg(lb, s, comma)
            } else {
                var c2 = comma + 1
                while (c2 < eqPos && lb[c2].toInt() != 44) c2++
                end1 = tok(lb, comma + 1, c2)
                if (!tokOk) bad = badMsg(lb, comma + 1, c2)
            }
        } else {
            start1 = tok(lb, s, eqPos)
            if (!tokOk) bad = badMsg(lb, s, eqPos)
            end1 = start1
        }
        if (bad != null) {
            addParseFail(k, errors, bad)
            return
        }

        if (start1 < 1 || end1 > l1) {
            errors.add("File1 range $start1-$end1 is out of bounds (1-$l1)")
        }
        if (start1 > end1) {
            errors.add("File1 range $start1-$end1 is invalid (start > end)")
        }

        // ----- right side -----
        tmpN = 0
        var a = eqPos + 1
        while (true) {
            var c = a
            while (c < e && lb[c].toInt() != 44) c++
            val v = tok(lb, a, c)
            if (!tokOk) {
                bad = badMsg(lb, a, c)
                break
            }
            if (tmpN == tmpT.size) tmpT = tmpT.copyOf(tmpN * 2)
            tmpT[tmpN] = v
            tmpN++
            if (c >= e) break
            a = c + 1
        }
        if (bad != null) {
            addParseFail(k, errors, bad)
            return
        }

        val save = r2s.n
        var pi = 0
        var rn = 1
        while (pi < tmpN) {
            val x = tmpT[pi]
            val y = if (pi + 1 < tmpN) tmpT[pi + 1] else x
            if (x < 1 || y > l2) errors.add("File2 range #$rn ($x-$y) is out of bounds (1-$l2)")
            if (x > y) errors.add("File2 range #$rn ($x-$y) is invalid (start > end)")
            r2s.add(x.toInt())
            r2e.add(y.toInt())
            pi += 2
            rn++
        }

        mSt.add(clampI(start1))
        mEn.add(clampI(end1))

        if (errors.isNotEmpty()) {
            r2s.n = save
            r2e.n = save
            failedBits.set(k)
            failedCount++
            if (fails.size < 100000) {
                val rb = StringBuilder()
                var q = 0
                while (q < tmpN) {
                    val x = tmpT[q]
                    val y = if (q + 1 < tmpN) tmpT[q + 1] else x
                    if (rb.isNotEmpty()) rb.append(", ")
                    rb.append(rangeStr(x, y))
                    q += 2
                }
                fails[k] = FR(rangeStr(start1, end1), rb.toString(), errors)
            }
        }
    }

    private fun parseMap(size: Long) {
        val buf = ByteArray(1 shl 20)
        var lb = ByteArray(1 shl 16)
        var ln = 0
        var lineNum = 0
        var prevCR = false
        var done = 0L
        env.openIn(3).use { ins ->
            while (true) {
                val n = ins.read(buf)
                if (n < 0) break
                chk()
                var i = 0
                while (i < n) {
                    val b = buf[i].toInt()
                    i++
                    if (prevCR) {
                        prevCR = false
                        if (b == 10) continue
                    }
                    if (b == 10 || b == 13) {
                        lineNum++
                        handleLine(lb, ln, lineNum)
                        ln = 0
                        if (b == 13) prevCR = true
                    } else {
                        if (ln == lb.size) lb = lb.copyOf(ln * 2)
                        lb[ln] = b.toByte()
                        ln++
                    }
                }
                done += n
                tick("Reading map file", done, size)
            }
        }
        if (ln > 0) {
            lineNum++
            handleLine(lb, ln, lineNum)
        }
        mRs.add(r2s.n)
    }

    // ---------- sorting + overlap detection (no O(n^2)) ----------
    private fun buildSorted(): LongArray {
        val n = mSt.n
        val keys = LongList()
        var mono = true
        var lastS = -1
        var k = 0
        while (k < n) {
            val s = mSt[k]
            if (s >= 1 && s <= mEn[k]) {
                if (s < lastS) mono = false
                lastS = s
                keys.add((s.toLong() shl 32) or k.toLong())
            }
            k++
        }
        val sorted = keys.a.copyOf(keys.n)
        if (!mono) java.util.Arrays.sort(sorted)
        return sorted
    }

    private fun findOverlaps(sorted: LongArray): LongArray {
        val act = IntList()
        val pairs = LongList()
        var q = 0
        while (q < sorted.size) {
            val k = (sorted[q] and MASK).toInt()
            val s = mSt[k]
            var w = 0
            var r = 0
            while (r < act.n) {
                val i = act.a[r]
                if (mEn[i] >= s) {
                    act.a[w] = i
                    w++
                    if (pairs.n < 3000000) {
                        val hi = if (i > k) i else k
                        val lo = if (i > k) k else i
                        pairs.add((hi.toLong() shl 32) or lo.toLong())
                    }
                }
                r++
            }
            act.n = w
            act.add(k)
            if ((q and 0xFFFF) == 0) chk()
            q++
        }
        val out = pairs.a.copyOf(pairs.n)
        java.util.Arrays.sort(out)
        return out
    }

    // ---------- validation report: log temp files + short on-screen view ----------
    private fun writeValidation(pairs: LongArray, vFile: File, dFile: File) {
        val n = mSt.n
        val vw = tmpWriter(vFile)
        val dw = tmpWriter(dFile)
        val showAll = n <= 200
        var shown = 0
        var hidden = 0
        var pp = 0
        val b = StringBuilder()
        val rb = StringBuilder()
        p("\n[3/5] Validation Results:")
        p(dash)
        if (!showAll) p("  (large map: only failed / warned entries are shown here; full results are in the log file)")
        try {
            var k = 0
            while (k < n) {
                val failed = failedBits.get(k)
                val fr: FR? = if (failed) fails[k] else null
                val f1: String
                val f2: String
                if (fr != null) {
                    f1 = fr.f1
                    f2 = fr.f2
                } else if (failed) {
                    f1 = "N/A"
                    f2 = "N/A"
                } else {
                    f1 = rangeStr(mSt[k].toLong(), mEn[k].toLong())
                    rb.setLength(0)
                    var q = mRs[k]
                    val qe = mRs[k + 1]
                    while (q < qe) {
                        if (rb.isNotEmpty()) rb.append(", ")
                        rb.append(rangeStr(r2s[q].toLong(), r2e[q].toLong()))
                        q++
                    }
                    f2 = rb.toString()
                }
                val hasWarn = pp < pairs.size && (pairs[pp] shr 32).toInt() == k

                b.setLength(0)
                b.append("Map #").append(k + 1).append(" (line ").append(mLine[k]).append("): ")
                b.append(if (failed) "✗ FAILED" else "✓ SUCCESS").append("\n")
                b.append("  File1: ").append(f1).append(" → File2: [").append(f2).append("]\n")
                if (fr != null) {
                    for (er in fr.errors) b.append("  ✗ ERROR: ").append(er).append("\n")
                } else if (failed) {
                    b.append("  ✗ ERROR: (details omitted - more than 100000 failed mappings)\n")
                }
                while (pp < pairs.size && (pairs[pp] shr 32).toInt() == k) {
                    val lo = (pairs[pp] and MASK).toInt()
                    b.append("  ⚠ WARNING: Overlaps with previous mapping at file1 lines ")
                    b.append(mSt[lo]).append("-").append(mEn[lo]).append("\n")
                    pp++
                }
                b.append("\n")
                vw.append(b)

                if (fr == null) {
                    if (!failed) {
                        dw.append("Map #").append((k + 1).toString()).append(": File1 lines ").append(f1)
                        dw.append(" → File2 lines [").append(f2).append("]\n")
                    }
                } else if (fr.f1 != "N/A") {
                    dw.append("Map #").append((k + 1).toString()).append(": File1 lines ").append(f1)
                    dw.append(" → File2 lines [").append(f2).append("]\n")
                }

                if (showAll || failed || hasWarn) {
                    if (showAll || shown < 100) {
                        shown++
                        val txt = b.toString().trimEnd('\n')
                        for (ln in txt.split("\n")) p("  $ln")
                        p("")
                    } else {
                        hidden++
                    }
                }
                if ((k and 0xFFF) == 0) {
                    chk()
                    tick("Checking map entries", k.toLong(), n.toLong())
                }
                k++
            }
        } finally {
            vw.close()
            dw.close()
        }
        if (hidden > 0) p("  ... $hidden more failed / warned entries not shown (see log file)")
    }

    // ---------- pass 3: stream file1 -> output, applying replacements ----------
    private fun doProcess(sorted: LongArray, os: OutputStream, s2: Scan, size1: Long, pFile: File, st: Stats) {
        val nrep = sorted.size
        val ob = OutBuf(os)
        var chn: FileChannel? = null
        var rr: RR? = null
        procTotal = size1
        procDone = 0L
        val pw = tmpWriter(pFile)
        try {
            if (r2s.n > 0) {
                val c = env.openChannel()
                chn = c
                rr = RR(c, c.size(), s2.idx, s2.k) { }
            }
            val buf = ByteArray(1 shl 20)
            var line = 0
            var atStart = true
            var prevCR = false
            var skipUntil = 0
            var skipping = false
            var ri = 0
            var nextStart = if (nrep > 0) mSt[(sorted[0] and MASK).toInt()] else Int.MAX_VALUE
            env.openIn(1).use { strm ->
                while (true) {
                    val n = strm.read(buf)
                    if (n < 0) break
                    chk()
                    var i = 0
                    while (i < n) {
                        val b = buf[i].toInt()
                        i++
                        if (prevCR) {
                            prevCR = false
                            if (b == 10) continue
                        }
                        if (atStart) {
                            line++
                            atStart = false
                            if (line > skipUntil && line == nextStart) {
                                val kk = (sorted[ri] and MASK).toInt()
                                var inserted = 0L
                                var q = mRs[kk]
                                val qe = mRs[kk + 1]
                                val reader = rr ?: throw IllegalStateException("file2 reader missing")
                                while (q < qe) {
                                    val a2 = r2s[q]
                                    val e2 = r2e[q]
                                    reader.copy(a2, e2, ob)
                                    inserted += (e2 - a2 + 1).toLong()
                                    q++
                                    chk()
                                }
                                st.inserted += inserted
                                st.outLines += inserted
                                st.processed++
                                val f1s = rangeStr(mSt[kk].toLong(), mEn[kk].toLong())
                                if (nrep <= 100 || st.processed <= 50) {
                                    p("  [${st.processed}/$nrep] ✓ Replaced file1 lines $f1s with $inserted lines from file2")
                                }
                                pw.write("Map #${st.processed}: ✓ SUCCESS\n  File1 range: $f1s\n  Lines inserted: $inserted\n\n")
                                skipUntil = mEn[kk]
                                ri++
                                nextStart = if (ri < nrep) mSt[(sorted[ri] and MASK).toInt()] else Int.MAX_VALUE
                            }
                            skipping = line <= skipUntil
                            if (!skipping) st.outLines++
                        }
                        if (b == 10) {
                            if (!skipping) ob.put(10)
                            atStart = true
                        } else if (b == 13) {
                            if (!skipping) ob.put(10)
                            atStart = true
                            prevCR = true
                        } else if (!skipping) {
                            ob.put(b)
                        }
                    }
                    procDone += n
                    tick("Processing replacements", procDone, procTotal)
                }
            }
            ob.flush()
        } finally {
            pw.close()
            try {
                chn?.close()
            } catch (e: Exception) {
            }
        }
        if (nrep > 100 && st.processed > 50) {
            p("  ... ${st.processed - 50} more replacements not shown (see log file)")
        }
    }

    // ---------- main flow ----------
    fun run(file1Name: String, file2Name: String, mapName: String, outName: String, logName: String) {
        val t0 = System.currentTimeMillis()
        val ts = SimpleDateFormat("yyyy-MM-dd HH:mm:ss", Locale.US).format(Date())
        val vFile = File(tmp, "lr_v.tmp")
        val pFile = File(tmp, "lr_p.tmp")
        val dFile = File(tmp, "lr_d.tmp")
        try {
            p(eq)
            p("LINE REPLACEMENT TOOL")
            p(eq)

            p("\n[1/5] Reading input files...")
            val size1 = env.size(1)
            val size2 = env.size(2)
            val sizeM = env.size(3)
            val tot = if (size1 > 0 && size2 > 0) size1 + size2 else -1L
            scanDone.set(0L)
            val h = Holder()
            val th = Thread {
                try {
                    h.v = scan(2, true, tot)
                } catch (e: Throwable) {
                    h.err = e
                }
            }
            th.start()
            val s1 = try {
                scan(1, false, tot)
            } catch (e: Throwable) {
                cancel = true
                th.join()
                throw e
            }
            th.join()
            val he = h.err
            if (he != null) throw he
            val s2 = h.v ?: throw IllegalStateException("Scan of file 2 failed")
            l1 = s1.lines
            l2 = s2.lines
            p("  ✓ File1: $l1 lines loaded")
            p("  ✓ File2: $l2 lines loaded")

            p("\n[2/5] Parsing and validating map file...")
            parseMap(sizeM)
            p("  ✓ Found $totalMappings mapping(s) to process")

            val sorted = buildSorted()
            val pairs = findOverlaps(sorted)
            writeValidation(pairs, vFile, dFile)
            val successCount = totalMappings - failedCount
            p("  Validation Summary: $successCount succeeded, $failedCount failed")

            if (failedCount > 0) {
                p("\n✗ Cannot proceed due to validation errors. Please fix the map file.")
                p("  Check log file for details: $logName")
                val lo = env.openOut(logName)
                try {
                    wr(lo, eq + "\nLINE REPLACEMENT LOG - VALIDATION FAILED\n" + eq + "\nTimestamp: $ts\n\n")
                    copyFile(vFile, lo)
                } finally {
                    lo.close()
                }
                return
            }

            p("\n[4/5] Processing replacements...")
            val st = Stats()
            val os = env.openOut(outName)
            var okOut = false
            try {
                doProcess(sorted, os, s2, size1, pFile, st)
                okOut = true
            } finally {
                try {
                    os.close()
                } catch (e: Exception) {
                }
                if (!okOut) {
                    try {
                        env.discard(outName)
                    } catch (e: Exception) {
                    }
                }
            }
            p("  ✓ All ${st.processed} replacement(s) completed successfully")

            p("\n[5/5] Writing output file...")
            p("  ✓ Output saved to: $outName")
            p("  ✓ Total lines in output: ${st.outLines}")

            p("\n[6/6] Generating log file...")
            tick("Writing log file", 0L, 0L)
            val lo = env.openOut(logName)
            try {
                val hd = StringBuilder()
                hd.append(eq).append("\nLINE REPLACEMENT LOG - SUCCESS\n").append(eq).append("\n")
                hd.append("Timestamp: $ts\n\n")
                hd.append("INPUT FILES:\n")
                hd.append("  File1: $file1Name ($l1 lines)\n")
                hd.append("  File2: $file2Name ($l2 lines)\n")
                hd.append("  Map:   $mapName ($totalMappings mappings)\n\n")
                hd.append("OUTPUT:\n")
                hd.append("  Result: $outName (${st.outLines} lines)\n\n")
                hd.append("VALIDATION RESULTS:\n").append(dash).append("\n")
                wr(lo, hd.toString())
                copyFile(vFile, lo)
                wr(lo, "Summary: $successCount succeeded, $failedCount failed\n" + dash + "\n\n")
                wr(lo, "PROCESSING RESULTS:\n" + dash + "\n")
                copyFile(pFile, lo)
                wr(lo, dash + "\n\n")
                wr(lo, "REPLACEMENT SUMMARY:\n")
                wr(lo, "  Total mappings processed: ${st.processed}\n")
                wr(lo, "  Total lines inserted from file2: ${st.inserted}\n\n")
                wr(lo, "DETAILED MAPPINGS:\n" + dash + "\n")
                copyFile(dFile, lo)
                wr(lo, dash + "\n")
            } finally {
                lo.close()
            }
            p("  ✓ Log saved to: $logName")

            p("\n" + eq)
            p("SUMMARY")
            p(eq)
            p("✓ Validated $successCount/$totalMappings mappings successfully")
            p("✓ Processed ${st.processed}/$totalMappings mappings")
            p("✓ Inserted ${st.inserted} lines from file2")
            p("✓ Output file: ${st.outLines} total lines")
            p("✓ Log file: $logName")
            p(eq)
            val secs = (System.currentTimeMillis() - t0) / 1000.0
            p("  Time taken: " + String.format(Locale.US, "%.1f", secs) + " s")
            p("\n✓ Replacement complete!")
        } finally {
            fl()
            vFile.delete()
            pFile.delete()
            dFile.delete()
        }
    }
}

// ===============================================================
// Activity (UI built in code, framework Views only)
// ===============================================================
@Suppress("DEPRECATION")
class MainActivity : Activity() {

    private val REQ_F1 = 101
    private val REQ_F2 = 102
    private val REQ_MAP = 103
    private val REQ_OUT = 104

    private lateinit var prefs: SharedPreferences
    private lateinit var statusTv: TextView
    private lateinit var logTv: TextView
    private lateinit var logScroll: ScrollView
    private lateinit var runBtn: Button
    private lateinit var progBar: ProgressBar
    private lateinit var progTv: TextView

    private var uri1: Uri? = null
    private var uri2: Uri? = null
    private var uriMap: Uri? = null
    private var uriOut: Uri? = null
    private var running: Boolean = false
    private var curEngine: Engine? = null
    private var pfdKeep: ParcelFileDescriptor? = null

    private fun dp(v: Int): Int = (v * resources.displayMetrics.density).toInt()

    override fun onCreate(savedInstanceState: Bundle?) {
        super.onCreate(savedInstanceState)
        prefs = getSharedPreferences("linereplace", Context.MODE_PRIVATE)

        val root = LinearLayout(this)
        root.orientation = LinearLayout.VERTICAL
        root.setBackgroundColor(Color.parseColor("#1B1F24"))
        root.setPadding(dp(8), dp(8), dp(8), dp(8))

        val title = TextView(this)
        title.text = "LINE REPLACEMENT TOOL"
        title.setTextColor(Color.WHITE)
        title.textSize = 18f
        title.typeface = Typeface.DEFAULT_BOLD
        title.setPadding(dp(4), dp(4), dp(4), dp(8))
        root.addView(title)

        val row1 = LinearLayout(this)
        row1.orientation = LinearLayout.HORIZONTAL
        row1.addView(mkBtn("File 1") { pickFile(REQ_F1) })
        row1.addView(mkBtn("File 2") { pickFile(REQ_F2) })
        root.addView(row1)

        val row2 = LinearLayout(this)
        row2.orientation = LinearLayout.HORIZONTAL
        row2.addView(mkBtn("Map file") { pickFile(REQ_MAP) })
        row2.addView(mkBtn("Output folder") { pickFolder() })
        root.addView(row2)

        statusTv = TextView(this)
        statusTv.setTextColor(Color.parseColor("#CFD8DC"))
        statusTv.textSize = 12f
        statusTv.setPadding(dp(4), dp(6), dp(4), dp(6))
        root.addView(statusTv)

        val row3 = LinearLayout(this)
        row3.orientation = LinearLayout.HORIZONTAL
        runBtn = mkBtn("RUN") { startRun() }
        row3.addView(runBtn)
        row3.addView(mkBtn("Stop") { curEngine?.cancel = true })
        row3.addView(mkBtn("Clear log") { logTv.text = "" })
        root.addView(row3)

        progBar = ProgressBar(this, null, android.R.attr.progressBarStyleHorizontal)
        progBar.max = 1000
        root.addView(
            progBar,
            LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT)
        )
        progTv = TextView(this)
        progTv.setTextColor(Color.parseColor("#FFE082"))
        progTv.textSize = 12f
        progTv.setPadding(dp(4), 0, dp(4), dp(4))
        root.addView(progTv)

        logScroll = ScrollView(this)
        logScroll.setBackgroundColor(Color.BLACK)
        logTv = TextView(this)
        logTv.setTextColor(Color.parseColor("#B9F6CA"))
        logTv.typeface = Typeface.MONOSPACE
        logTv.textSize = 11f
        logTv.setPadding(dp(6), dp(6), dp(6), dp(6))
        logScroll.addView(
            logTv,
            ViewGroup.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT)
        )
        val lp = LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, 0, 1f)
        lp.topMargin = dp(6)
        root.addView(logScroll, lp)

        setContentView(root)

        restoreState()
        refreshStatus()
    }

    private fun mkBtn(text: String, action: () -> Unit): Button {
        val b = Button(this)
        b.text = text
        b.isFocusable = false
        b.isFocusableInTouchMode = false
        b.setOnClickListener { action() }
        b.layoutParams = LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.WRAP_CONTENT, 1f)
        return b
    }

    // ---------------- state ----------------
    private fun restoreState() {
        uri1 = loadUri("f1")
        uri2 = loadUri("f2")
        uriMap = loadUri("map")
        uriOut = loadUri("out")
    }

    private fun loadUri(key: String): Uri? {
        val s = prefs.getString(key, null) ?: return null
        val u = Uri.parse(s)
        var ok = false
        try {
            for (perm in contentResolver.persistedUriPermissions) {
                if (perm.uri == u) ok = true
            }
        } catch (e: Exception) {
            ok = false
        }
        return if (ok) u else null
    }

    private fun saveUri(key: String, u: Uri) {
        prefs.edit().putString(key, u.toString()).apply()
    }

    override fun onPause() {
        super.onPause()
        val e = prefs.edit()
        uri1?.let { e.putString("f1", it.toString()) }
        uri2?.let { e.putString("f2", it.toString()) }
        uriMap?.let { e.putString("map", it.toString()) }
        uriOut?.let { e.putString("out", it.toString()) }
        e.apply()
    }

    private fun nameOf(x: Uri?): String {
        val u: Uri = x ?: return "(not selected)"
        try {
            if (DocumentsContract.isTreeUri(u)) {
                return DocumentsContract.getTreeDocumentId(u)
            }
            val c = contentResolver.query(u, arrayOf(OpenableColumns.DISPLAY_NAME), null, null, null)
            if (c != null) {
                c.use {
                    if (it.moveToFirst()) {
                        val n = it.getString(0)
                        if (n != null) return n
                    }
                }
            }
        } catch (e: Exception) {
            // fall through
        }
        return u.lastPathSegment ?: u.toString()
    }

    private fun sizeOf(u: Uri): Long {
        try {
            val c = contentResolver.query(u, arrayOf(OpenableColumns.SIZE), null, null, null)
            if (c != null) {
                c.use {
                    if (it.moveToFirst() && !it.isNull(0)) return it.getLong(0)
                }
            }
        } catch (e: Exception) {
            // ignore
        }
        return -1L
    }

    private fun refreshStatus() {
        statusTv.text = "File 1:   " + nameOf(uri1) + "\n" +
            "File 2:   " + nameOf(uri2) + "\n" +
            "Map file: " + nameOf(uriMap) + "\n" +
            "Output:   " + nameOf(uriOut)
    }

    // ---------------- pickers ----------------
    private fun pickFile(req: Int) {
        val i = Intent(Intent.ACTION_OPEN_DOCUMENT)
        i.addCategory(Intent.CATEGORY_OPENABLE)
        i.type = "*/*"
        i.addFlags(Intent.FLAG_GRANT_READ_URI_PERMISSION or Intent.FLAG_GRANT_PERSISTABLE_URI_PERMISSION)
        startActivityForResult(i, req)
    }

    private fun pickFolder() {
        val i = Intent(Intent.ACTION_OPEN_DOCUMENT_TREE)
        i.addFlags(
            Intent.FLAG_GRANT_READ_URI_PERMISSION or
                Intent.FLAG_GRANT_WRITE_URI_PERMISSION or
                Intent.FLAG_GRANT_PERSISTABLE_URI_PERMISSION
        )
        startActivityForResult(i, REQ_OUT)
    }

    override fun onActivityResult(requestCode: Int, resultCode: Int, data: Intent?) {
        super.onActivityResult(requestCode, resultCode, data)
        if (resultCode != RESULT_OK) return
        val u: Uri = data?.data ?: return
        try {
            if (requestCode == REQ_OUT) {
                contentResolver.takePersistableUriPermission(
                    u,
                    Intent.FLAG_GRANT_READ_URI_PERMISSION or Intent.FLAG_GRANT_WRITE_URI_PERMISSION
                )
            } else {
                contentResolver.takePersistableUriPermission(u, Intent.FLAG_GRANT_READ_URI_PERMISSION)
            }
        } catch (e: Exception) {
            // ignore
        }
        when (requestCode) {
            REQ_F1 -> { uri1 = u; saveUri("f1", u) }
            REQ_F2 -> { uri2 = u; saveUri("f2", u) }
            REQ_MAP -> { uriMap = u; saveUri("map", u) }
            REQ_OUT -> { uriOut = u; saveUri("out", u) }
        }
        refreshStatus()
    }

    // ---------------- keyboard shortcuts ----------------
    override fun dispatchKeyEvent(event: KeyEvent): Boolean {
        if (event.action == KeyEvent.ACTION_DOWN && event.isCtrlPressed) {
            when (event.keyCode) {
                KeyEvent.KEYCODE_1 -> { pickFile(REQ_F1); return true }
                KeyEvent.KEYCODE_2 -> { pickFile(REQ_F2); return true }
                KeyEvent.KEYCODE_3 -> { pickFile(REQ_MAP); return true }
                KeyEvent.KEYCODE_O -> { pickFolder(); return true }
                KeyEvent.KEYCODE_R, KeyEvent.KEYCODE_ENTER -> { startRun(); return true }
                KeyEvent.KEYCODE_PERIOD -> { curEngine?.cancel = true; return true }
            }
        }
        return super.dispatchKeyEvent(event)
    }

    // ---------------- UI callbacks from the worker thread ----------------
    private fun appendLog(t: String) {
        runOnUiThread {
            if (logTv.length() > 200000) {
                logTv.text = logTv.text.toString().takeLast(100000)
            }
            logTv.append(t)
            logScroll.post { logScroll.fullScroll(View.FOCUS_DOWN) }
        }
    }

    private fun setProgress(stage: String, pm: Int) {
        runOnUiThread {
            if (pm < 0) {
                progBar.isIndeterminate = true
                progTv.text = "$stage..."
            } else {
                progBar.isIndeterminate = false
                progBar.progress = pm
                progTv.text = stage + "... " + (pm / 10) + "." + (pm % 10) + "%"
            }
        }
    }

    // ---------------- SAF output helpers ----------------
    private fun findDocIds(tree: Uri, name: String): ArrayList<String> {
        val docId = DocumentsContract.getTreeDocumentId(tree)
        val kids = DocumentsContract.buildChildDocumentsUriUsingTree(tree, docId)
        val res = ArrayList<String>()
        val c = contentResolver.query(
            kids,
            arrayOf(
                DocumentsContract.Document.COLUMN_DOCUMENT_ID,
                DocumentsContract.Document.COLUMN_DISPLAY_NAME
            ),
            null, null, null
        )
        if (c != null) {
            c.use {
                while (it.moveToNext()) {
                    if (it.getString(1) == name) res.add(it.getString(0))
                }
            }
        }
        return res
    }

    private fun deleteDocs(tree: Uri, name: String) {
        for (id in findDocIds(tree, name)) {
            try {
                DocumentsContract.deleteDocument(
                    contentResolver,
                    DocumentsContract.buildDocumentUriUsingTree(tree, id)
                )
            } catch (e: Exception) {
                // ignore
            }
        }
    }

    private fun openDocOut(tree: Uri, name: String): OutputStream {
        deleteDocs(tree, name)
        val docId = DocumentsContract.getTreeDocumentId(tree)
        val parent = DocumentsContract.buildDocumentUriUsingTree(tree, docId)
        val doc = DocumentsContract.createDocument(contentResolver, parent, "text/plain", name)
            ?: throw IOException("Could not create $name")
        return contentResolver.openOutputStream(doc, "wt")
            ?: throw IOException("Could not write $name")
    }

    private fun makeEnv(a: Uri, b: Uri, m: Uri, o: Uri): Env {
        return object : Env {
            override fun openIn(which: Int): InputStream {
                val u: Uri = if (which == 1) a else if (which == 2) b else m
                return contentResolver.openInputStream(u) ?: throw IOException("Cannot open " + nameOf(u))
            }

            override fun size(which: Int): Long {
                val u: Uri = if (which == 1) a else if (which == 2) b else m
                return sizeOf(u)
            }

            override fun openChannel(): FileChannel {
                try {
                    val pfd = contentResolver.openFileDescriptor(b, "r")
                    if (pfd != null) {
                        val ch = FileInputStream(pfd.fileDescriptor).channel
                        ch.read(ByteBuffer.allocate(1), 0L)
                        pfdKeep = pfd
                        return ch
                    }
                } catch (e: Exception) {
                    // fall back to a cached copy below
                }
                val f = File(cacheDir, "file2.cache")
                val ins = contentResolver.openInputStream(b) ?: throw IOException("Cannot open file 2")
                ins.use { src ->
                    FileOutputStream(f).use { dst -> src.copyTo(dst, 1 shl 20) }
                }
                return RandomAccessFile(f, "r").channel
            }

            override fun openOut(name: String): OutputStream = openDocOut(o, name)

            override fun discard(name: String) {
                deleteDocs(o, name)
            }

            override fun release() {
                try {
                    pfdKeep?.close()
                } catch (e: Exception) {
                    // ignore
                }
                pfdKeep = null
                File(cacheDir, "file2.cache").delete()
            }
        }
    }

    // ---------------- running ----------------
    private fun startRun() {
        if (running) return
        val a = uri1
        val b = uri2
        val m = uriMap
        val o = uriOut
        if (a == null || b == null || m == null || o == null) {
            Toast.makeText(this, "Select File 1, File 2, Map file and Output folder first", Toast.LENGTH_LONG).show()
            return
        }
        running = true
        runBtn.isEnabled = false
        logTv.text = ""
        window.addFlags(WindowManager.LayoutParams.FLAG_KEEP_SCREEN_ON)
        val n1 = nameOf(a)
        val n2 = nameOf(b)
        val nm = nameOf(m)

        Thread {
            val env = makeEnv(a, b, m, o)
            val eng = Engine(env, cacheDir, { t -> appendLog(t) }, { st, pm -> setProgress(st, pm) })
            curEngine = eng
            try {
                eng.run(n1, n2, nm, "result.txt", "replacement_log.txt")
            } catch (e: CancelEx) {
                appendLog("\n✗ Stopped by user. Partial output was removed.\n")
            } catch (e: OutOfMemoryError) {
                appendLog("\n✗ ERROR: Out of memory (map file is extremely large).\n")
            } catch (e: Throwable) {
                appendLog("\n✗ ERROR: " + (e.message ?: e.toString()) + "\n")
            } finally {
                env.release()
                curEngine = null
            }
            runOnUiThread {
                running = false
                runBtn.isEnabled = true
                progBar.isIndeterminate = false
                progBar.progress = 0
                progTv.text = ""
                window.clearFlags(WindowManager.LayoutParams.FLAG_KEEP_SCREEN_ON)
            }
        }.start()
    }
}
