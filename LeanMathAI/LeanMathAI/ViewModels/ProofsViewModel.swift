import Foundation
import Observation

@Observable
final class ProofsViewModel {
    var allResults: [ProofResult] = []
    var filteredResults: [ProofResult] = []
    var selectedStatus: ProofStatus? { didSet { applyFilter() } }
    var selectedDate: String? { didSet { loadCurrentDate() } }
    var availableDates: [String] = []
    var isLoading = true

    // Lean source files for the selected date
    var leanFiles: [URL] = []

    var statusCounts: [ProofStatus: Int] {
        Dictionary(grouping: allResults, by: \.status).mapValues(\.count)
    }

    var totalCount: Int { allResults.count }

    private var directoryService: DataDirectoryService?

    func setup(from ds: DataDirectoryService) {
        directoryService = ds
        availableDates = ds.availableDates
        selectedDate = ds.availableDates.first
    }

    func loadCurrentDate() {
        guard let ds = directoryService, let date = selectedDate else { return }
        isLoading = true

        allResults = ProofDataService.loadAllResults(for: date, from: ds)
            .sorted { $0.status.sortOrder < $1.status.sortOrder }

        leanFiles = ds.leanFiles(for: date)

        applyFilter()
        isLoading = false
    }

    func applyFilter() {
        if let status = selectedStatus {
            filteredResults = allResults.filter { $0.status == status }
        } else {
            filteredResults = allResults
        }
    }

    func leanSource(for result: ProofResult) -> String? {
        // Try to find a matching .lean file by ID
        let matchingFile = leanFiles.first { url in
            url.deletingPathExtension().lastPathComponent.contains(
                result.id.replacingOccurrences(of: "/", with: "_")
            )
        }
        guard let file = matchingFile else { return nil }
        return ProofDataService.loadLeanSource(at: file)
    }
}
