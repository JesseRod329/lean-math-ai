import Foundation

struct ProofDataService {
    /// Load proof results from a JSONL file.
    /// Handles both single-line JSONL and multi-line pretty-printed JSON objects.
    static func loadJSONL(from url: URL) -> [ProofResult] {
        guard let content = try? String(contentsOf: url, encoding: .utf8),
              !content.isEmpty else { return [] }

        let decoder = JSONDecoder()

        // First try: single-line JSONL (one JSON object per line)
        let lines = content.split(separator: "\n", omittingEmptySubsequences: true)
        let singleLineResults = lines.compactMap { line -> ProofResult? in
            let trimmed = line.trimmingCharacters(in: .whitespaces)
            guard trimmed.hasPrefix("{") else { return nil }
            return try? decoder.decode(ProofResult.self, from: Data(trimmed.utf8))
        }
        if !singleLineResults.isEmpty {
            return singleLineResults
        }

        // Fallback: multi-line JSON objects (from jq pretty-print)
        // Use JSONSerialization.jsonObject to incrementally parse
        var results: [ProofResult] = []
        let data = Data(content.utf8)
        var offset = 0

        while offset < data.count {
            // Skip whitespace
            while offset < data.count {
                let byte = data[offset]
                if byte == UInt8(ascii: " ") || byte == UInt8(ascii: "\n") ||
                   byte == UInt8(ascii: "\r") || byte == UInt8(ascii: "\t") {
                    offset += 1
                } else {
                    break
                }
            }
            guard offset < data.count else { break }

            // Find matching closing brace for this JSON object
            guard data[offset] == UInt8(ascii: "{") else { offset += 1; continue }

            var depth = 0
            var inString = false
            var escaped = false
            var end = offset

            for i in offset..<data.count {
                let byte = data[i]
                if escaped {
                    escaped = false
                    continue
                }
                if byte == UInt8(ascii: "\\") && inString {
                    escaped = true
                    continue
                }
                if byte == UInt8(ascii: "\"") {
                    inString = !inString
                    continue
                }
                if inString { continue }
                if byte == UInt8(ascii: "{") { depth += 1 }
                if byte == UInt8(ascii: "}") {
                    depth -= 1
                    if depth == 0 { end = i + 1; break }
                }
            }

            guard depth == 0, end > offset else { break }

            let objectData = data[offset..<end]
            if let result = try? decoder.decode(ProofResult.self, from: Data(objectData)) {
                results.append(result)
            }
            offset = end
        }

        return results
    }

    static func loadAllResults(for date: String, from ds: DataDirectoryService) -> [ProofResult] {
        var results: [ProofResult] = []

        if let url = ds.provenFile(for: date) {
            results.append(contentsOf: loadJSONL(from: url))
        }
        if let url = ds.formalizedFile(for: date) {
            results.append(contentsOf: loadJSONL(from: url))
        }
        if let url = ds.failedFile(for: date) {
            results.append(contentsOf: loadJSONL(from: url))
        }
        if let url = ds.templatesFile(for: date) {
            results.append(contentsOf: loadJSONL(from: url))
        }
        if let url = ds.trivialFile(for: date) {
            results.append(contentsOf: loadJSONL(from: url))
        }

        return results
    }

    static func loadAllResultsAllDates(from ds: DataDirectoryService) -> [ProofResult] {
        var all: [ProofResult] = []
        for date in ds.availableDates {
            all.append(contentsOf: loadAllResults(for: date, from: ds))
        }
        return all
    }

    static func loadLeanSource(at url: URL) -> String? {
        try? String(contentsOf: url, encoding: .utf8)
    }
}
