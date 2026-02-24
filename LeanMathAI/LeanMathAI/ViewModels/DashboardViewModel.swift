import Foundation
import Observation

@Observable
final class DashboardViewModel {
    var dashboardStatus: DashboardStatus?
    var recentProofs: [ProofResult] = []
    var todaySnapshot: DailySnapshot?
    var weeklySnapshots: [DailySnapshot] = []
    var isLoading = true
    var lastRefresh: Date?

    // Pipeline funnel
    var pipelinePapers: Int = 0
    var pipelineCandidates: Int = 0
    var pipelineProcessed: Int = 0
    var pipelineProven: Int = 0

    // All-time stats
    var totalProven: Int = 0
    var totalFormalized: Int = 0
    var totalFailed: Int = 0

    func refresh(from ds: DataDirectoryService) {
        isLoading = true

        // Load dashboard status
        dashboardStatus = DashboardDataService.loadLatest(from: ds)

        // Build snapshots
        weeklySnapshots = DashboardDataService.buildSnapshots(from: ds)
        todaySnapshot = weeklySnapshots.first

        // Pipeline funnel from today
        if let today = todaySnapshot {
            pipelinePapers = today.paperCount
            pipelineCandidates = today.candidateCount
            pipelineProcessed = today.totalProcessed
            pipelineProven = today.provenCount
        }

        // All-time totals
        totalProven = weeklySnapshots.reduce(0) { $0 + $1.provenCount }
        totalFormalized = weeklySnapshots.reduce(0) { $0 + $1.formalizedCount }
        totalFailed = weeklySnapshots.reduce(0) { $0 + $1.failedCount }

        // Recent proofs (last 10 across all dates)
        let allResults = ProofDataService.loadAllResultsAllDates(from: ds)
        recentProofs = Array(allResults.sorted { ($0.date, $0.hour ?? "") > ($1.date, $1.hour ?? "") }.prefix(10))

        lastRefresh = Date()
        isLoading = false
    }
}
