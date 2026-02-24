import SwiftUI

enum ProofStatus: String, Codable, CaseIterable, Identifiable, Sendable {
    case proven
    case formalized
    case failed
    case template
    case trivial

    var id: String { rawValue }

    var displayName: String {
        switch self {
        case .proven: "Proven"
        case .formalized: "Formalized"
        case .failed: "Failed"
        case .template: "Template"
        case .trivial: "Trivial"
        }
    }

    var explanation: String {
        switch self {
        case .proven: "Compiles with no sorry — fully verified"
        case .formalized: "Compiles with sorry — statement correct, proof incomplete"
        case .failed: "Does not compile — needs syntax fixes"
        case .template: "LLM fallback — not real AI output"
        case .trivial: "True := by — meaningless proof"
        }
    }

    var icon: String {
        switch self {
        case .proven: "checkmark.seal.fill"
        case .formalized: "doc.badge.gearshape"
        case .failed: "xmark.octagon.fill"
        case .template: "exclamationmark.triangle.fill"
        case .trivial: "minus.circle.fill"
        }
    }

    var color: Color {
        switch self {
        case .proven: AppTheme.proven
        case .formalized: AppTheme.formalized
        case .failed: AppTheme.failed
        case .template: AppTheme.template
        case .trivial: AppTheme.trivial
        }
    }

    var sortOrder: Int {
        switch self {
        case .proven: 0
        case .formalized: 1
        case .failed: 2
        case .template: 3
        case .trivial: 4
        }
    }
}
