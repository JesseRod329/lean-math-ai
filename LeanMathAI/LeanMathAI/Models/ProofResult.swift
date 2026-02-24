import Foundation

struct ProofResult: Codable, Identifiable, Hashable, Sendable {
    let name: String
    let statement: String
    let objects: [String]
    let difficulty: String
    let value: String
    let formalization_hints: String
    let source_paper: SourcePaper
    let id: String
    let status: ProofStatus
    let date: String
    let hour: String?
    let abstract_excerpt: String?
    let extraction_method: String?

    var resultDate: Date? {
        let formatter = DateFormatter()
        formatter.dateFormat = "yyyy-MM-dd"
        return formatter.date(from: date)
    }

    var hasLaTeX: Bool {
        statement.contains("$") || statement.contains("\\(")
    }
}
