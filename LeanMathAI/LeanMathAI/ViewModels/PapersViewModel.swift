import Foundation
import Observation

@Observable
final class PapersViewModel {
    var allPapers: [Paper] = []
    var filteredPapers: [Paper] = []
    var searchText = "" { didSet { applyFilters() } }
    var selectedCategories: Set<String> = [] { didSet { applyFilters() } }
    var allCategories: [String] = []
    var selectedDate: String? { didSet { loadCurrentDate() } }
    var availableDates: [String] = []
    var isLoading = true
    var paperCount: Int = 0

    private var directoryService: DataDirectoryService?

    func setup(from ds: DataDirectoryService) {
        directoryService = ds
        availableDates = ds.availableDates
        selectedDate = ds.availableDates.first
    }

    func loadCurrentDate() {
        guard let ds = directoryService, let date = selectedDate else { return }
        isLoading = true

        guard let url = ds.papersFile(for: date),
              let feed = try? PaperDataService.loadPapers(from: url) else {
            allPapers = []
            filteredPapers = []
            paperCount = 0
            isLoading = false
            return
        }

        allPapers = feed.papers
        paperCount = feed.count

        // Collect all categories
        let categories = Set(feed.papers.flatMap(\.categories))
        allCategories = categories.sorted()

        applyFilters()
        isLoading = false
    }

    func applyFilters() {
        var papers = allPapers

        if !searchText.isEmpty {
            let query = searchText.lowercased()
            papers = papers.filter {
                $0.title.lowercased().contains(query) ||
                $0.authors.joined(separator: " ").lowercased().contains(query) ||
                $0.summary.lowercased().contains(query)
            }
        }

        if !selectedCategories.isEmpty {
            papers = papers.filter { paper in
                !selectedCategories.isDisjoint(with: paper.categories)
            }
        }

        filteredPapers = papers
    }
}
