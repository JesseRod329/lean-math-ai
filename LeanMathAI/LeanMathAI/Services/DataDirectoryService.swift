import Foundation
import SwiftUI
import Observation

@Observable
final class DataDirectoryService {
    var baseDirectory: URL?
    var isValid: Bool = false
    var validationErrors: [String] = []
    var availableDates: [String] = []

    private static let bookmarkKey = "LeanMathAI_DirectoryBookmark"
    private static let pathKey = "LeanMathAI_DirectoryPath"

    // MARK: - Computed Subdirectories

    var papersDirectory: URL? { baseDirectory?.appendingPathComponent("papers") }
    var candidatesDirectory: URL? { baseDirectory?.appendingPathComponent("target-theorems") }
    var completedProofsDirectory: URL? { baseDirectory?.appendingPathComponent("completed-proofs") }
    var failedAttemptsDirectory: URL? { baseDirectory?.appendingPathComponent("failed-attempts") }
    var proofsDirectory: URL? { baseDirectory?.appendingPathComponent("proofs") }
    var dashboardDataDirectory: URL? { baseDirectory?.appendingPathComponent("dashboard").appendingPathComponent("data") }
    var dailyReportsDirectory: URL? { baseDirectory?.appendingPathComponent("daily-reports") }

    // MARK: - Init

    init() {
        restoreDirectory()
    }

    // MARK: - Directory Management

    func setDirectory(_ url: URL) {
        baseDirectory = url
        if validate() {
            saveBookmark(for: url)
            scanAvailableDates()
        }
    }

    @discardableResult
    func validate() -> Bool {
        validationErrors = []

        guard let base = baseDirectory else {
            validationErrors.append("No directory selected")
            isValid = false
            return false
        }

        let fm = FileManager.default
        let requiredDirs = [
            "papers", "target-theorems", "scripts"
        ]

        for dir in requiredDirs {
            let path = base.appendingPathComponent(dir).path
            if !fm.fileExists(atPath: path) {
                validationErrors.append("Missing directory: \(dir)")
            }
        }

        isValid = validationErrors.isEmpty
        return isValid
    }

    func scanAvailableDates() {
        guard let papersDir = papersDirectory else { return }
        let fm = FileManager.default

        do {
            let files = try fm.contentsOfDirectory(at: papersDir, includingPropertiesForKeys: [.contentModificationDateKey])
            availableDates = files
                .filter { $0.pathExtension == "json" }
                .compactMap { url -> String? in
                    let name = url.deletingPathExtension().lastPathComponent
                    guard name.hasPrefix("papers-") else { return nil }
                    return String(name.dropFirst("papers-".count))
                }
                .sorted(by: >)
        } catch {
            availableDates = []
        }
    }

    // MARK: - File Paths

    func papersFile(for date: String) -> URL? {
        papersDirectory?.appendingPathComponent("papers-\(date).json")
    }

    func candidatesFile(for date: String) -> URL? {
        candidatesDirectory?.appendingPathComponent("candidates-\(date).json")
    }

    func provenFile(for date: String) -> URL? {
        completedProofsDirectory?.appendingPathComponent("proven-\(date).jsonl")
    }

    func formalizedFile(for date: String) -> URL? {
        completedProofsDirectory?.appendingPathComponent("formalized-\(date).jsonl")
    }

    func failedFile(for date: String) -> URL? {
        failedAttemptsDirectory?.appendingPathComponent("failed-\(date).jsonl")
    }

    func templatesFile(for date: String) -> URL? {
        failedAttemptsDirectory?.appendingPathComponent("templates-\(date).jsonl")
    }

    func trivialFile(for date: String) -> URL? {
        failedAttemptsDirectory?.appendingPathComponent("trivial-\(date).jsonl")
    }

    func latestDashboard() -> URL? {
        dashboardDataDirectory?.appendingPathComponent("latest.json")
    }

    func proofsListing() -> URL? {
        dashboardDataDirectory?.appendingPathComponent("proofs.json")
    }

    // MARK: - Find Lean Source Files

    func leanFiles(for date: String) -> [URL] {
        guard let proofsDir = proofsDirectory?.appendingPathComponent(date) else { return [] }
        let fm = FileManager.default
        guard let enumerator = fm.enumerator(at: proofsDir, includingPropertiesForKeys: nil) else { return [] }

        var files: [URL] = []
        while let url = enumerator.nextObject() as? URL {
            if url.pathExtension == "lean" {
                files.append(url)
            }
        }
        return files.sorted { $0.lastPathComponent < $1.lastPathComponent }
    }

    // MARK: - Bookmark Persistence

    private func saveBookmark(for url: URL) {
        do {
            let bookmark = try url.bookmarkData(
                options: .withSecurityScope,
                includingResourceValuesForKeys: nil,
                relativeTo: nil
            )
            UserDefaults.standard.set(bookmark, forKey: Self.bookmarkKey)
            UserDefaults.standard.set(url.path, forKey: Self.pathKey)
        } catch {
            // Fallback: just save path
            UserDefaults.standard.set(url.path, forKey: Self.pathKey)
        }
    }

    private func restoreDirectory() {
        // Try bookmark first
        if let data = UserDefaults.standard.data(forKey: Self.bookmarkKey) {
            var isStale = false
            if let url = try? URL(
                resolvingBookmarkData: data,
                options: .withSecurityScope,
                relativeTo: nil,
                bookmarkDataIsStale: &isStale
            ) {
                _ = url.startAccessingSecurityScopedResource()
                if isStale {
                    saveBookmark(for: url)
                }
                baseDirectory = url
                if validate() {
                    scanAvailableDates()
                    return
                }
            }
        }

        // Fallback: try raw path
        if let path = UserDefaults.standard.string(forKey: Self.pathKey) {
            let url = URL(fileURLWithPath: path)
            if FileManager.default.fileExists(atPath: path) {
                baseDirectory = url
                if validate() {
                    scanAvailableDates()
                    return
                }
            }
        }

        // Auto-detect: try the known project path
        let knownPath = NSHomeDirectory() + "/clawd/lean-math-ai"
        if FileManager.default.fileExists(atPath: knownPath) {
            let url = URL(fileURLWithPath: knownPath)
            baseDirectory = url
            if validate() {
                saveBookmark(for: url)
                scanAvailableDates()
                return
            }
        }

        // Nothing worked — clear stale state so onboarding shows clean
        baseDirectory = nil
        isValid = false
        validationErrors = []
    }
}
