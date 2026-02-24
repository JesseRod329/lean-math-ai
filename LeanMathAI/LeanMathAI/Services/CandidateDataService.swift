import Foundation

struct CandidateDataService {
    static func loadCandidates(from url: URL) throws -> CandidateFeed {
        let data = try Data(contentsOf: url)
        return try JSONDecoder().decode(CandidateFeed.self, from: data)
    }

    static func loadCandidates(for date: String, from directoryService: DataDirectoryService) -> CandidateFeed? {
        guard let url = directoryService.candidatesFile(for: date) else { return nil }
        return try? loadCandidates(from: url)
    }
}
