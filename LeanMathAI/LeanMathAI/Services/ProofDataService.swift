import Foundation

struct ProofDataService {
    static func loadJSONL(from url: URL) -> [ProofResult] {
        guard let content = try? String(contentsOf: url, encoding: .utf8) else { return [] }
        return content
            .split(separator: "\n")
            .compactMap { line -> ProofResult? in
                guard !line.trimmingCharacters(in: .whitespaces).isEmpty else { return nil }
                return try? JSONDecoder().decode(ProofResult.self, from: Data(line.utf8))
            }
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
