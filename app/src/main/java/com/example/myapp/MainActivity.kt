package com.example.myapp

import android.app.Activity
import android.content.Context
import android.content.Intent
import android.content.SharedPreferences
import android.graphics.Color
import android.graphics.Typeface
import android.net.Uri
import android.os.Bundle
import android.provider.DocumentsContract
import android.provider.OpenableColumns
import android.view.KeyEvent
import android.view.ViewGroup
import android.widget.Button
import android.widget.LinearLayout
import android.widget.ScrollView
import android.widget.TextView
import android.widget.Toast
import java.io.IOException
import java.text.SimpleDateFormat
import java.util.ArrayList
import java.util.Date
import java.util.Locale

// ---------------------------------------------------------------
// Data holders
// ---------------------------------------------------------------
class PyEx(msg: String) : Exception(msg)

class Rep(val start1: Int, val end1: Int, val ranges: List<Pair<Int, Int>>)

class VR(
    val num: Int,
    val lineNum: Int,
    val file1Range: String,
    val file2Ranges: String,
    val status: String,
    val errors: List<String>,
    val warnings: List<String>
)

class PR(val num: Int, val file1Range: String, val inserted: Int, val status: String)

fun pyInt(s: String): Int {
    val t = s.trim()
    val v = t.toIntOrNull()
    if (v == null) throw PyEx("invalid literal for int() with base 10: '" + s + "'")
    return v
}

fun splitLines(text: String): List<String> {
    val t = text.replace("\r\n", "\n").replace("\r", "\n")
    val r = ArrayList<String>()
    var s = 0
    var i = 0
    while (i < t.length) {
        if (t[i] == '\n') {
            r.add(t.substring(s, i + 1))
            s = i + 1
        }
        i++
    }
    if (s < t.length) r.add(t.substring(s))
    return r
}

fun rangeStr(a: Int, b: Int): String {
    return if (a != b) "$a-$b" else a.toString()
}

// ---------------------------------------------------------------
// The engine: exact port of the Python script
// ---------------------------------------------------------------
class Engine(
    private val flushCb: (String) -> Unit,
    private val writer: (String, String) -> Unit
) {
    private val sb = StringBuilder()
    private var cnt = 0

    private fun fl() {
        if (sb.isNotEmpty()) {
            val t = sb.toString()
            sb.setLength(0)
            flushCb(t)
        }
    }

    private fun p(s: String) {
        sb.append(s).append("\n")
        cnt++
        if (cnt % 25 == 0) fl()
    }

    fun finish() {
        fl()
    }

    fun run(
        file1Name: String,
        file2Name: String,
        mapName: String,
        file1Lines: List<String>,
        file2Lines: List<String>,
        mapLines: List<String>,
        outName: String,
        logName: String
    ) {
        val eq = "=".repeat(60)
        val dash = "-".repeat(60)
        val ts = SimpleDateFormat("yyyy-MM-dd HH:mm:ss", Locale.US).format(Date())

        p(eq)
        p("LINE REPLACEMENT TOOL")
        p(eq)

        p("\n[1/5] Reading input files...")
        p("  ✓ File1: ${file1Lines.size} lines loaded")
        p("  ✓ File2: ${file2Lines.size} lines loaded")

        p("\n[2/5] Parsing and validating map file...")
        val replacements = ArrayList<Rep>()
        val logEntries = ArrayList<String>()
        val vrs = ArrayList<VR>()

        var totalMappings = 0
        for (l in mapLines) {
            if (l.trim().isNotEmpty() && l.contains("=")) totalMappings++
        }
        p("  ✓ Found $totalMappings mapping(s) to process")

        var mappingNum = 0
        var idx = 0
        while (idx < mapLines.size) {
            val lineNum = idx + 1
            val line = mapLines[idx].trim()
            idx++
            if (line.isEmpty() || !line.contains("=")) continue

            mappingNum++
            val errors = ArrayList<String>()
            val warnings = ArrayList<String>()

            try {
                val parts = line.split("=")
                if (parts.size != 2) throw PyEx("too many values to unpack (expected 2)")
                val left = parts[0]
                val right = parts[1]

                val leftPair: Pair<Int, Int> = if (left.contains(",")) {
                    val lp = left.split(",")
                    val a = pyInt(lp[0])
                    val b = pyInt(lp[1])
                    Pair(a, b)
                } else {
                    val x = pyInt(left)
                    Pair(x, x)
                }
                val start1 = leftPair.first
                val end1 = leftPair.second

                if (start1 < 1 || end1 > file1Lines.size) {
                    errors.add("File1 range $start1-$end1 is out of bounds (1-${file1Lines.size})")
                }
                if (start1 > end1) {
                    errors.add("File1 range $start1-$end1 is invalid (start > end)")
                }

                val rightParts = ArrayList<Int>()
                for (x in right.split(",")) rightParts.add(pyInt(x))

                val file2Ranges = ArrayList<Pair<Int, Int>>()
                var i = 0
                while (i < rightParts.size) {
                    if (i + 1 < rightParts.size) {
                        file2Ranges.add(Pair(rightParts[i], rightParts[i + 1]))
                        i += 2
                    } else {
                        file2Ranges.add(Pair(rightParts[i], rightParts[i]))
                        i += 1
                    }
                }

                var ri = 0
                while (ri < file2Ranges.size) {
                    val s2 = file2Ranges[ri].first
                    val e2 = file2Ranges[ri].second
                    if (s2 < 1 || e2 > file2Lines.size) {
                        errors.add("File2 range #${ri + 1} ($s2-$e2) is out of bounds (1-${file2Lines.size})")
                    }
                    if (s2 > e2) {
                        errors.add("File2 range #${ri + 1} ($s2-$e2) is invalid (start > end)")
                    }
                    ri++
                }

                for (prev in replacements) {
                    if (!(end1 < prev.start1 || start1 > prev.end1)) {
                        warnings.add("Overlaps with previous mapping at file1 lines ${prev.start1}-${prev.end1}")
                    }
                }

                val status = if (errors.isEmpty()) "✓ SUCCESS" else "✗ FAILED"

                replacements.add(Rep(start1, end1, file2Ranges))

                val file1Str = rangeStr(start1, end1)
                val rangesList = ArrayList<String>()
                for (pr in file2Ranges) rangesList.add(rangeStr(pr.first, pr.second))
                val rangesStr = rangesList.joinToString(", ")

                vrs.add(VR(mappingNum, lineNum, file1Str, rangesStr, status, errors, warnings))
                logEntries.add("Map #$mappingNum: File1 lines $file1Str → File2 lines [$rangesStr]")
            } catch (e: PyEx) {
                errors.add("Parse error: ${e.message}")
                vrs.add(VR(mappingNum, lineNum, "N/A", "N/A", "✗ FAILED", errors, ArrayList<String>()))
            }
        }

        // Validation results
        p("\n[3/5] Validation Results:")
        p(dash)
        var successCount = 0
        var failedCount = 0
        for (r in vrs) {
            p("  Map #${r.num} (line ${r.lineNum}): ${r.status}")
            p("    File1: ${r.file1Range} → File2: [${r.file2Ranges}]")
            if (r.errors.isNotEmpty()) {
                failedCount++
                for (er in r.errors) p("    ✗ ERROR: $er")
            } else {
                successCount++
            }
            for (w in r.warnings) p("    ⚠ WARNING: $w")
            p("")
        }
        p("  Validation Summary: $successCount succeeded, $failedCount failed")

        if (failedCount > 0) {
            p("\n✗ Cannot proceed due to validation errors. Please fix the map file.")
            p("  Check log file for details: $logName")
            val lg = StringBuilder()
            lg.append(eq).append("\n")
            lg.append("LINE REPLACEMENT LOG - VALIDATION FAILED\n")
            lg.append(eq).append("\n")
            lg.append("Timestamp: $ts\n\n")
            for (r in vrs) {
                lg.append("Map #${r.num} (line ${r.lineNum}): ${r.status}\n")
                lg.append("  File1: ${r.file1Range} → File2: [${r.file2Ranges}]\n")
                for (er in r.errors) lg.append("  ✗ ERROR: $er\n")
                for (w in r.warnings) lg.append("  ⚠ WARNING: $w\n")
                lg.append("\n")
            }
            writer(logName, lg.toString())
            finish()
            return
        }

        val sorted = replacements.sortedBy { it.start1 }

        p("\n[4/5] Processing replacements...")
        val outputLines = ArrayList<String>()
        var current = 1
        var repIndex = 0
        val numFile1 = file1Lines.size
        var processedCount = 0
        var totalInserted = 0
        val processing = ArrayList<PR>()

        while (current <= numFile1) {
            if (repIndex < sorted.size && current == sorted[repIndex].start1) {
                val r = sorted[repIndex]
                var inserted = 0
                for (rg in r.ranges) {
                    val chunk = file2Lines.subList(rg.first - 1, rg.second)
                    outputLines.addAll(chunk)
                    inserted += chunk.size
                }
                totalInserted += inserted
                processedCount++
                val file1Str = rangeStr(r.start1, r.end1)
                p("  [$processedCount/${sorted.size}] ✓ Replaced file1 lines $file1Str with $inserted lines from file2")
                processing.add(PR(processedCount, file1Str, inserted, "✓ SUCCESS"))
                current = r.end1 + 1
                repIndex++
            } else {
                outputLines.add(file1Lines[current - 1])
                current++
            }
        }
        p("  ✓ All $processedCount replacement(s) completed successfully")

        p("\n[5/5] Writing output file...")
        writer(outName, outputLines.joinToString(""))
        p("  ✓ Output saved to: $outName")
        p("  ✓ Total lines in output: ${outputLines.size}")

        p("\n[6/6] Generating log file...")
        val lg = StringBuilder()
        lg.append(eq).append("\n")
        lg.append("LINE REPLACEMENT LOG - SUCCESS\n")
        lg.append(eq).append("\n")
        lg.append("Timestamp: $ts\n\n")

        lg.append("INPUT FILES:\n")
        lg.append("  File1: $file1Name (${file1Lines.size} lines)\n")
        lg.append("  File2: $file2Name (${file2Lines.size} lines)\n")
        lg.append("  Map:   $mapName ($totalMappings mappings)\n\n")

        lg.append("OUTPUT:\n")
        lg.append("  Result: $outName (${outputLines.size} lines)\n\n")

        lg.append("VALIDATION RESULTS:\n")
        lg.append(dash).append("\n")
        for (r in vrs) {
            lg.append("Map #${r.num} (line ${r.lineNum}): ${r.status}\n")
            lg.append("  File1: ${r.file1Range} → File2: [${r.file2Ranges}]\n")
            for (er in r.errors) lg.append("  ✗ ERROR: $er\n")
            for (w in r.warnings) lg.append("  ⚠ WARNING: $w\n")
            lg.append("\n")
        }
        lg.append("Summary: $successCount succeeded, $failedCount failed\n")
        lg.append(dash).append("\n\n")

        lg.append("PROCESSING RESULTS:\n")
        lg.append(dash).append("\n")
        for (r in processing) {
            lg.append("Map #${r.num}: ${r.status}\n")
            lg.append("  File1 range: ${r.file1Range}\n")
            lg.append("  Lines inserted: ${r.inserted}\n\n")
        }
        lg.append(dash).append("\n\n")

        lg.append("REPLACEMENT SUMMARY:\n")
        lg.append("  Total mappings processed: $processedCount\n")
        lg.append("  Total lines inserted from file2: $totalInserted\n\n")

        lg.append("DETAILED MAPPINGS:\n")
        lg.append(dash).append("\n")
        for (en in logEntries) lg.append(en).append("\n")
        lg.append(dash).append("\n")

        writer(logName, lg.toString())
        p("  ✓ Log saved to: $logName")

        p("\n" + eq)
        p("SUMMARY")
        p(eq)
        p("✓ Validated $successCount/$totalMappings mappings successfully")
        p("✓ Processed $processedCount/$totalMappings mappings")
        p("✓ Inserted $totalInserted lines from file2")
        p("✓ Output file: ${outputLines.size} total lines")
        p("✓ Log file: $logName")
        p(eq)
        p("\n✓ Replacement complete!")
        finish()
    }
}

// ---------------------------------------------------------------
// Activity (UI built in code, framework Views only)
// ---------------------------------------------------------------
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

    private var uri1: Uri? = null
    private var uri2: Uri? = null
    private var uriMap: Uri? = null
    private var uriOut: Uri? = null
    private var running: Boolean = false

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
        row3.addView(mkBtn("Clear log") { logTv.text = "" })
        root.addView(row3)

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
            }
        }
        return super.dispatchKeyEvent(event)
    }

    // ---------------- running ----------------
    private fun appendLog(t: String) {
        runOnUiThread {
            logTv.append(t)
            logScroll.post { logScroll.fullScroll(android.view.View.FOCUS_DOWN) }
        }
    }

    private fun readText(u: Uri): String {
        val ins = contentResolver.openInputStream(u) ?: throw IOException("Cannot open " + nameOf(u))
        val bytes = ins.use { it.readBytes() }
        return String(bytes, Charsets.UTF_8)
    }

    private fun writeDoc(tree: Uri, name: String, content: String) {
        val docId = DocumentsContract.getTreeDocumentId(tree)
        val parent = DocumentsContract.buildDocumentUriUsingTree(tree, docId)
        val kids = DocumentsContract.buildChildDocumentsUriUsingTree(tree, docId)
        val toDelete = ArrayList<String>()
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
                    if (it.getString(1) == name) toDelete.add(it.getString(0))
                }
            }
        }
        for (id in toDelete) {
            try {
                DocumentsContract.deleteDocument(
                    contentResolver,
                    DocumentsContract.buildDocumentUriUsingTree(tree, id)
                )
            } catch (e: Exception) {
                // ignore
            }
        }
        val doc = DocumentsContract.createDocument(contentResolver, parent, "text/plain", name)
            ?: throw IOException("Could not create $name")
        val os = contentResolver.openOutputStream(doc, "wt")
            ?: throw IOException("Could not write $name")
        os.use { it.write(content.toByteArray(Charsets.UTF_8)) }
    }

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
        val n1 = nameOf(a)
        val n2 = nameOf(b)
        val nm = nameOf(m)

        Thread {
            try {
                val l1 = splitLines(readText(a))
                val l2 = splitLines(readText(b))
                val lm = splitLines(readText(m))
                val engine = Engine(
                    { t -> appendLog(t) },
                    { name, content -> writeDoc(o, name, content) }
                )
                engine.run(n1, n2, nm, l1, l2, lm, "result.txt", "replacement_log.txt")
            } catch (e: Exception) {
                appendLog("\n✗ ERROR: " + (e.message ?: e.toString()) + "\n")
            }
            runOnUiThread {
                running = false
                runBtn.isEnabled = true
            }
        }.start()
    }
}
