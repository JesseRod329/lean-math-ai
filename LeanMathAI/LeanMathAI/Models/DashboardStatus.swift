import Foundation

struct DashboardStatus: Codable, Sendable {
    let last_update: String
    let date: String
    let hour: String
    let papers: Int
    let candidates: Int
    let processed_this_hour: Int
    let proven_today: Int
    let formalized_today: Int
    let status: String

    var isRunning: Bool { status == "running" }

    var lastUpdateDate: Date? {
        let formatter = ISO8601DateFormatter()
        formatter.formatOptions = [.withInternetDateTime, .withFractionalSeconds]
        return formatter.date(from: last_update) ?? ISO8601DateFormatter().date(from: last_update)
    }

    var totalProcessedToday: Int {
        proven_today + formalized_today
    }

    var successRate: Double {
        guard totalProcessedToday > 0 else { return 0 }
        return Double(proven_today + formalized_today) / Double(candidates) * 100
    }
}
