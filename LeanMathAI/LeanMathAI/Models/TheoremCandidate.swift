import Foundation
import SwiftUI

struct TheoremCandidate: Codable, Identifiable, Hashable, Sendable {
    let name: String
    let statement: String
    let objects: [String]
    let difficulty: String
    let value: String
    let formalization_hints: String
    let source_paper: SourcePaper
    let abstract_excerpt: String?
    let extraction_method: String?
    let id: String

    var hasLaTeX: Bool {
        statement.contains("$") || statement.contains("\\(") || statement.contains("\\[")
    }

    var difficultyLevel: DifficultyLevel {
        DifficultyLevel(rawValue: difficulty.lowercased()) ?? .medium
    }
}

enum DifficultyLevel: String, CaseIterable, Identifiable, Sendable {
    case easy
    case medium
    case hard

    var id: String { rawValue }

    var displayName: String {
        switch self {
        case .easy: "Easy"
        case .medium: "Medium"
        case .hard: "Hard"
        }
    }

    var color: SwiftUI.Color {
        switch self {
        case .easy: AppTheme.proven
        case .medium: AppTheme.formalized
        case .hard: AppTheme.failed
        }
    }
}

struct CandidateFeed: Codable, Sendable {
    let extraction_date: String
    let total_papers: Int
    let candidates_found: Int
    let candidates: [TheoremCandidate]
}
