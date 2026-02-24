import Foundation
import Observation

@Observable
@MainActor
final class ConfigService {
    var config: PipelineConfig = .default
    var isDirty: Bool = false

    private var configURL: URL?
    private var saveTask: Task<Void, Never>?

    func configure(baseDirectory: URL) {
        configURL = baseDirectory.appendingPathComponent("config.json")
        load()
    }

    func load() {
        guard let url = configURL else { return }
        do {
            let data = try Data(contentsOf: url)
            let decoder = JSONDecoder()
            config = try decoder.decode(PipelineConfig.self, from: data)
            isDirty = false
        } catch {
            // Config doesn't exist or is malformed — write defaults
            config = .default
            save()
        }
    }

    func save() {
        guard let url = configURL else { return }
        do {
            let encoder = JSONEncoder()
            encoder.outputFormatting = [.prettyPrinted, .sortedKeys]
            let data = try encoder.encode(config)
            try data.write(to: url, options: .atomic)
            isDirty = false
        } catch {
            print("Failed to save config: \(error)")
        }
    }

    /// Debounced save — waits 0.5s after last change before writing
    func scheduleSave() {
        isDirty = true
        saveTask?.cancel()
        saveTask = Task { @MainActor in
            try? await Task.sleep(for: .milliseconds(500))
            guard !Task.isCancelled else { return }
            save()
        }
    }

    // MARK: - Environment Keys

    func hasAnthropicKey() -> Bool {
        ProcessInfo.processInfo.environment["ANTHROPIC_API_KEY"] != nil
    }

    func hasOpenAIKey() -> Bool {
        ProcessInfo.processInfo.environment["OPENAI_API_KEY"] != nil
    }

    func setEnvironmentKey(_ key: String, value: String) {
        // Write to ~/.lean-math-ai-keys for the scripts to source
        let keysFile = FileManager.default.homeDirectoryForCurrentUser
            .appendingPathComponent(".lean-math-ai-keys")
        var existing = (try? String(contentsOf: keysFile)) ?? ""

        // Replace or append
        let pattern = "export \(key)="
        if existing.contains(pattern) {
            let lines = existing.components(separatedBy: "\n").map { line in
                line.hasPrefix(pattern) ? "export \(key)=\"\(value)\"" : line
            }
            existing = lines.joined(separator: "\n")
        } else {
            existing += "\nexport \(key)=\"\(value)\""
        }

        try? existing.trimmingCharacters(in: .whitespacesAndNewlines)
            .write(to: keysFile, atomically: true, encoding: .utf8)
    }
}
