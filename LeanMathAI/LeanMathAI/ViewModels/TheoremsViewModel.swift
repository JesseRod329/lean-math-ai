import Foundation
import Observation

@Observable
final class TheoremsViewModel {
    var allCandidates: [TheoremCandidate] = []
    var filteredCandidates: [TheoremCandidate] = []
    var searchText = "" { didSet { applyFilters() } }
    var selectedDifficulty: DifficultyLevel? { didSet { applyFilters() } }
    var selectedDate: String? { didSet { loadCurrentDate() } }
    var availableDates: [String] = []
    var isLoading = true

    // Status cross-reference
    var candidateStatuses: [String: ProofStatus] = [:]

    private var directoryService: DataDirectoryService?

    func setup(from ds: DataDirectoryService) {
        directoryService = ds
        availableDates = ds.availableDates
        selectedDate = ds.availableDates.first
    }

    func loadCurrentDate() {
        guard let ds = directoryService, let date = selectedDate else { return }
        isLoading = true

        // Load candidates
        if let feed = CandidateDataService.loadCandidates(for: date, from: ds) {
            allCandidates = feed.candidates
        } else {
            allCandidates = []
        }

        // Cross-reference with proof results
        let results = ProofDataService.loadAllResults(for: date, from: ds)
        candidateStatuses = Dictionary(uniqueKeysWithValues: results.map { ($0.id, $0.status) })

        applyFilters()
        isLoading = false
    }

    func applyFilters() {
        var candidates = allCandidates

        if !searchText.isEmpty {
            let query = searchText.lowercased()
            candidates = candidates.filter {
                $0.name.lowercased().contains(query) ||
                $0.statement.lowercased().contains(query) ||
                $0.objects.joined(separator: " ").lowercased().contains(query)
            }
        }

        if let difficulty = selectedDifficulty {
            candidates = candidates.filter { $0.difficultyLevel == difficulty }
        }

        filteredCandidates = candidates
    }

    func status(for candidate: TheoremCandidate) -> ProofStatus? {
        candidateStatuses[candidate.id]
    }
}
