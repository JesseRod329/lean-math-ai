import Foundation

struct PaperDataService {
    static func loadPapers(from url: URL) throws -> PaperFeed {
        let data = try Data(contentsOf: url)
        return try JSONDecoder().decode(PaperFeed.self, from: data)
    }

    static func loadAllPapers(from directoryService: DataDirectoryService) -> [(String, PaperFeed)] {
        var results: [(String, PaperFeed)] = []
        for date in directoryService.availableDates {
            guard let url = directoryService.papersFile(for: date) else { continue }
            if let feed = try? loadPapers(from: url) {
                results.append((date, feed))
            }
        }
        return results
    }
}
