import Foundation
import SwiftUI
import Observation

enum PipelinePhase: String, CaseIterable, Identifiable, Sendable {
    case idle
    case fetchingPapers
    case extractingTheorems
    case formalizingProofs
    case refiningProofs
    case updatingDashboard
    case complete
    case failed

    var id: String { rawValue }

    var displayName: String {
        switch self {
        case .idle: "Idle"
        case .fetchingPapers: "Fetching Papers"
        case .extractingTheorems: "Extracting Theorems"
        case .formalizingProofs: "Formalizing Proofs"
        case .refiningProofs: "Refining Proofs"
        case .updatingDashboard: "Updating Dashboard"
        case .complete: "Complete"
        case .failed: "Failed"
        }
    }

    var icon: String {
        switch self {
        case .idle: "moon.zzz"
        case .fetchingPapers: "arrow.down.doc"
        case .extractingTheorems: "magnifyingglass"
        case .formalizingProofs: "hammer"
        case .refiningProofs: "arrow.triangle.2.circlepath"
        case .updatingDashboard: "chart.bar"
        case .complete: "checkmark.circle"
        case .failed: "xmark.circle"
        }
    }

    var color: SwiftUI.Color {
        switch self {
        case .idle: AppTheme.textSecondary
        case .fetchingPapers, .extractingTheorems: AppTheme.textAccent
        case .formalizingProofs, .refiningProofs: AppTheme.formalized
        case .updatingDashboard: AppTheme.proven
        case .complete: AppTheme.proven
        case .failed: AppTheme.failed
        }
    }
}

@Observable
@MainActor
final class PipelineService {
    var phase: PipelinePhase = .idle
    var isRunning: Bool = false
    var logOutput: [String] = []
    var lastRunDate: Date?
    var errorMessage: String?

    // Per-phase progress
    var paperCount: Int = 0
    var candidateCount: Int = 0
    var processedCount: Int = 0
    var provenCount: Int = 0
    var formalizedCount: Int = 0

    // Auto-run
    var nextRunDate: Date?
    private var autoRunTimer: Timer?

    private var currentProcess: Process?
    private var baseDirectory: URL?
    private var configService: ConfigService?

    func configure(baseDirectory: URL, configService: ConfigService? = nil) {
        self.baseDirectory = baseDirectory
        self.configService = configService
    }

    // MARK: - Auto-Run Timer

    func startAutoRunTimer() {
        stopAutoRunTimer()
        guard let config = configService?.config, config.schedule.autoRun else { return }

        let interval = TimeInterval(config.schedule.runIntervalMinutes * 60)
        nextRunDate = Date().addingTimeInterval(interval)

        autoRunTimer = Timer.scheduledTimer(withTimeInterval: interval, repeats: true) { [weak self] _ in
            Task { @MainActor in
                guard let self, !self.isRunning else { return }
                self.runFullPipeline()
                self.nextRunDate = Date().addingTimeInterval(interval)
            }
        }
    }

    func stopAutoRunTimer() {
        autoRunTimer?.invalidate()
        autoRunTimer = nil
        nextRunDate = nil
    }

    // MARK: - Run Full Pipeline

    func runFullPipeline() {
        guard !isRunning, let baseDir = baseDirectory else { return }
        isRunning = true
        errorMessage = nil
        logOutput = []
        resetCounts()

        let scriptPath = baseDir.appendingPathComponent("scripts/hourly-math-loop.sh").path
        let configPath = baseDir.appendingPathComponent("config.json").path

        appendLog("Starting full pipeline run...")
        phase = .fetchingPapers

        Task.detached { [weak self] in
            await self?.executeScript(at: scriptPath, in: baseDir, configPath: configPath)
        }
    }

    // MARK: - Run Individual Phases

    func fetchPapers() {
        guard !isRunning, let baseDir = baseDirectory else { return }
        let config = configService?.config ?? .default
        isRunning = true
        errorMessage = nil
        logOutput = []
        phase = .fetchingPapers
        appendLog("Fetching papers from arXiv...")

        let date = Self.todayString()
        let script = baseDir.appendingPathComponent("scripts/fetch-arxiv-papers.py").path
        let output = baseDir.appendingPathComponent("papers/papers-\(date).json").path

        var args: [String] = []
        for cat in config.arxiv.categories {
            args += ["--category", cat]
        }
        args += ["--days", "\(config.arxiv.daysBack)", "--max-results", "\(config.arxiv.maxResults)", "--output", output]

        Task.detached { [weak self] in
            await self?.executePython(
                script: script,
                args: args,
                in: baseDir,
                nextPhase: .idle
            )
        }
    }

    func extractTheorems() {
        guard !isRunning, let baseDir = baseDirectory else { return }
        let config = configService?.config ?? .default
        isRunning = true
        errorMessage = nil
        logOutput = []
        phase = .extractingTheorems
        appendLog("Extracting theorem candidates...")

        let date = Self.todayString()
        let script = baseDir.appendingPathComponent("scripts/extract-theorems.py").path
        let input = baseDir.appendingPathComponent("papers/papers-\(date).json").path
        let output = baseDir.appendingPathComponent("target-theorems/candidates-\(date).json").path

        Task.detached { [weak self] in
            await self?.executePython(
                script: script,
                args: [
                    "--input", input,
                    "--output", output,
                    "--max-candidates", "\(config.extraction.maxCandidates)",
                    "--model", config.extraction.model
                ],
                in: baseDir,
                nextPhase: .idle
            )
        }
    }

    func stop() {
        currentProcess?.terminate()
        currentProcess = nil
        isRunning = false
        phase = .idle
        appendLog("Pipeline stopped by user.")
    }

    // MARK: - Execution

    private func executeScript(at path: String, in workDir: URL, configPath: String? = nil) async {
        let process = Process()
        process.executableURL = URL(fileURLWithPath: "/bin/bash")
        process.arguments = [path]
        process.currentDirectoryURL = workDir

        var env = ProcessInfo.processInfo.environment.merging([
            "PATH": "\(NSHomeDirectory())/.elan/bin:/opt/homebrew/bin:/usr/local/bin:/usr/bin:/bin",
            "HOME": NSHomeDirectory()
        ]) { _, new in new }

        // Source API keys file if it exists
        if let configPath {
            env["PIPELINE_CONFIG"] = configPath
        }
        let keysFile = FileManager.default.homeDirectoryForCurrentUser.appendingPathComponent(".lean-math-ai-keys")
        if let keysContent = try? String(contentsOf: keysFile) {
            for line in keysContent.components(separatedBy: "\n") {
                let stripped = line.trimmingCharacters(in: .whitespaces)
                if stripped.hasPrefix("export "), let eqRange = stripped.range(of: "=") {
                    let key = String(stripped[stripped.index(stripped.startIndex, offsetBy: 7)..<eqRange.lowerBound])
                    var value = String(stripped[eqRange.upperBound...])
                    value = value.trimmingCharacters(in: CharacterSet(charactersIn: "\""))
                    env[key] = value
                }
            }
        }
        process.environment = env

        let pipe = Pipe()
        process.standardOutput = pipe
        process.standardError = pipe

        await MainActor.run {
            self.currentProcess = process
        }

        do {
            try process.run()

            let handle = pipe.fileHandleForReading
            Task.detached { [weak self] in
                while true {
                    let data = handle.availableData
                    if data.isEmpty { break }
                    if let line = String(data: data, encoding: .utf8) {
                        let lines = line.split(separator: "\n", omittingEmptySubsequences: false)
                        for l in lines where !l.isEmpty {
                            let cleaned = Self.stripAnsi(String(l))
                            await self?.appendLog(cleaned)
                            await self?.parsePhaseFromLog(cleaned)
                        }
                    }
                }
            }

            process.waitUntilExit()

            let status = process.terminationStatus
            await MainActor.run {
                self.currentProcess = nil
                self.isRunning = false
                self.lastRunDate = Date()

                if status == 0 {
                    self.phase = .complete
                    self.appendLog("Pipeline completed successfully.")
                } else {
                    self.phase = .failed
                    self.errorMessage = "Pipeline exited with code \(status)"
                    self.appendLog("Pipeline failed with exit code \(status)")
                }
            }
        } catch {
            await MainActor.run {
                self.isRunning = false
                self.phase = .failed
                self.errorMessage = error.localizedDescription
                self.appendLog("Error: \(error.localizedDescription)")
            }
        }
    }

    private func executePython(script: String, args: [String], in workDir: URL, nextPhase: PipelinePhase) async {
        let process = Process()
        process.executableURL = URL(fileURLWithPath: "/opt/homebrew/bin/python3")
        process.arguments = [script] + args
        process.currentDirectoryURL = workDir

        var env = ProcessInfo.processInfo.environment.merging([
            "PATH": "\(NSHomeDirectory())/.elan/bin:/opt/homebrew/bin:/usr/local/bin:/usr/bin:/bin",
            "HOME": NSHomeDirectory()
        ]) { _, new in new }

        // Source API keys
        let keysFile = FileManager.default.homeDirectoryForCurrentUser.appendingPathComponent(".lean-math-ai-keys")
        if let keysContent = try? String(contentsOf: keysFile) {
            for line in keysContent.components(separatedBy: "\n") {
                let stripped = line.trimmingCharacters(in: .whitespaces)
                if stripped.hasPrefix("export "), let eqRange = stripped.range(of: "=") {
                    let key = String(stripped[stripped.index(stripped.startIndex, offsetBy: 7)..<eqRange.lowerBound])
                    var value = String(stripped[eqRange.upperBound...])
                    value = value.trimmingCharacters(in: CharacterSet(charactersIn: "\""))
                    env[key] = value
                }
            }
        }
        process.environment = env

        let pipe = Pipe()
        process.standardOutput = pipe
        process.standardError = pipe

        await MainActor.run {
            self.currentProcess = process
        }

        do {
            try process.run()

            let handle = pipe.fileHandleForReading
            Task.detached { [weak self] in
                while true {
                    let data = handle.availableData
                    if data.isEmpty { break }
                    if let line = String(data: data, encoding: .utf8) {
                        for l in line.split(separator: "\n", omittingEmptySubsequences: false) where !l.isEmpty {
                            await self?.appendLog(Self.stripAnsi(String(l)))
                        }
                    }
                }
            }

            process.waitUntilExit()
            let status = process.terminationStatus

            await MainActor.run {
                self.currentProcess = nil
                self.isRunning = false
                self.lastRunDate = Date()

                if status == 0 {
                    self.phase = nextPhase == .idle ? .complete : nextPhase
                    self.appendLog("Phase completed.")
                } else {
                    self.phase = .failed
                    self.errorMessage = "Exited with code \(status)"
                    self.appendLog("Failed with exit code \(status)")
                }
            }
        } catch {
            await MainActor.run {
                self.isRunning = false
                self.phase = .failed
                self.errorMessage = error.localizedDescription
                self.appendLog("Error: \(error.localizedDescription)")
            }
        }
    }

    // MARK: - Log Parsing

    private func parsePhaseFromLog(_ line: String) async {
        await MainActor.run {
            if line.contains("PHASE 1") { self.phase = .fetchingPapers }
            else if line.contains("PHASE 2") { self.phase = .extractingTheorems }
            else if line.contains("PHASE 3:") && !line.contains("3.5") { self.phase = .formalizingProofs }
            else if line.contains("PHASE 3.5") { self.phase = .refiningProofs }
            else if line.contains("PHASE 4") { self.phase = .updatingDashboard }

            if line.contains("PROVEN:") { self.provenCount += 1; self.processedCount += 1 }
            else if line.contains("FORMALIZED:") { self.formalizedCount += 1; self.processedCount += 1 }
            else if line.contains("FAILED:") { self.processedCount += 1 }
            else if line.contains("TEMPLATE:") { self.processedCount += 1 }
            else if line.contains("TRIVIAL:") { self.processedCount += 1 }

            if line.contains("Downloaded") && line.contains("papers") {
                if let match = line.range(of: #"\d+"#, options: .regularExpression) {
                    self.paperCount = Int(line[match]) ?? 0
                }
            }
            if line.contains("candidates available") || line.contains("candidates_found") {
                if let match = line.range(of: #"\d+"#, options: .regularExpression) {
                    self.candidateCount = Int(line[match]) ?? 0
                }
            }
        }
    }

    @MainActor
    private func appendLog(_ line: String) {
        logOutput.append(line)
        if logOutput.count > 500 {
            logOutput.removeFirst(logOutput.count - 500)
        }
    }

    private func resetCounts() {
        paperCount = 0
        candidateCount = 0
        processedCount = 0
        provenCount = 0
        formalizedCount = 0
    }

    nonisolated private static func todayString() -> String {
        let formatter = DateFormatter()
        formatter.dateFormat = "yyyy-MM-dd"
        return formatter.string(from: Date())
    }

    nonisolated private static func stripAnsi(_ string: String) -> String {
        string.replacingOccurrences(
            of: #"\x1B\[[0-9;]*[a-zA-Z]"#,
            with: "",
            options: .regularExpression
        )
    }
}
