import Foundation
import SwiftUI
import Observation

@Observable
final class SettingsViewModel {
    var directoryPath: String = ""
    var isValid: Bool = false
    var autoRefresh: Bool = true
    var dateCount: Int = 0
    var totalProofs: Int = 0
    var totalPapers: Int = 0

    func refresh(from ds: DataDirectoryService) {
        directoryPath = ds.baseDirectory?.path ?? "Not set"
        isValid = ds.isValid
        dateCount = ds.availableDates.count

        // Count totals
        var proofs = 0
        var papers = 0
        for date in ds.availableDates {
            let results = ProofDataService.loadAllResults(for: date, from: ds)
            proofs += results.count
            if let url = ds.papersFile(for: date),
               let feed = try? PaperDataService.loadPapers(from: url) {
                papers += feed.count
            }
        }
        totalProofs = proofs
        totalPapers = papers
    }
}
