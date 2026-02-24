import Foundation

struct DashboardDataService {
    static func loadLatest(from url: URL) throws -> DashboardStatus {
        let data = try Data(contentsOf: url)
        return try JSONDecoder().decode(DashboardStatus.self, from: data)
    }

    static func loadLatest(from ds: DataDirectoryService) -> DashboardStatus? {
        guard let url = ds.latestDashboard() else { return nil }
        return try? loadLatest(from: url)
    }

    static func buildSnapshots(from ds: DataDirectoryService) -> [DailySnapshot] {
        let formatter = DateFormatter()
        formatter.dateFormat = "yyyy-MM-dd"

        return ds.availableDates.compactMap { dateString -> DailySnapshot? in
            guard let date = formatter.date(from: dateString) else { return nil }

            // Paper count
            let paperCount: Int
            if let url = ds.papersFile(for: dateString),
               let feed = try? PaperDataService.loadPapers(from: url) {
                paperCount = feed.count
            } else {
                paperCount = 0
            }

            // Candidate count
            let candidateCount: Int
            if let feed = CandidateDataService.loadCandidates(for: dateString, from: ds) {
                candidateCount = feed.candidates_found
            } else {
                candidateCount = 0
            }

            // Proof results
            let results = ProofDataService.loadAllResults(for: dateString, from: ds)
            let grouped = Dictionary(grouping: results, by: \.status)

            return DailySnapshot(
                id: dateString,
                date: date,
                dateString: dateString,
                paperCount: paperCount,
                candidateCount: candidateCount,
                provenCount: grouped[.proven]?.count ?? 0,
                formalizedCount: grouped[.formalized]?.count ?? 0,
                failedCount: grouped[.failed]?.count ?? 0,
                templateCount: grouped[.template]?.count ?? 0,
                trivialCount: grouped[.trivial]?.count ?? 0
            )
        }
        .sorted { $0.dateString > $1.dateString }
    }
}
