import Foundation

struct DailySnapshot: Identifiable, Sendable {
    let id: String
    let date: Date
    let dateString: String
    let paperCount: Int
    let candidateCount: Int
    let provenCount: Int
    let formalizedCount: Int
    let failedCount: Int
    let templateCount: Int
    let trivialCount: Int

    var totalProcessed: Int {
        provenCount + formalizedCount + failedCount + templateCount + trivialCount
    }

    var successCount: Int {
        provenCount + formalizedCount
    }

    var successRate: Double {
        guard totalProcessed > 0 else { return 0 }
        return Double(successCount) / Double(totalProcessed) * 100
    }
}
