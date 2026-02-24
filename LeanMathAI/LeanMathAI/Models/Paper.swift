import Foundation

struct Paper: Codable, Identifiable, Hashable, Sendable {
    let id: String
    let title: String
    let summary: String
    let published: String
    let authors: [String]
    let categories: [String]
    let pdf_link: String
    let doi: String

    var publishedDate: Date? {
        let formatter = ISO8601DateFormatter()
        formatter.formatOptions = [.withInternetDateTime, .withFractionalSeconds]
        return formatter.date(from: published) ?? ISO8601DateFormatter().date(from: published)
    }

    var pdfURL: URL? { URL(string: pdf_link) }
    var arxivURL: URL? { URL(string: "https://arxiv.org/abs/\(id)") }
    var primaryCategory: String { categories.first ?? "math" }
    var hasLaTeX: Bool { summary.contains("$") || summary.contains("\\(") }
}

struct PaperFeed: Codable, Sendable {
    let fetch_date: String
    let categories: [String]
    let days_back: Int
    let count: Int
    let papers: [Paper]
}
