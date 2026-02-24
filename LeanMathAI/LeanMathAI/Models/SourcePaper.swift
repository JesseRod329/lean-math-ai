import Foundation

struct SourcePaper: Codable, Hashable, Sendable {
    let id: String
    let title: String
    let authors: [String]
    let categories: [String]

    var arxivURL: URL? {
        URL(string: "https://arxiv.org/abs/\(id)")
    }

    var pdfURL: URL? {
        URL(string: "https://arxiv.org/pdf/\(id)")
    }
}
