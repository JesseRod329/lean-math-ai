import Foundation
import Observation

@Observable
final class TimelineViewModel {
    var snapshots: [DailySnapshot] = []
    var isLoading = true

    func refresh(from ds: DataDirectoryService) {
        isLoading = true
        snapshots = DashboardDataService.buildSnapshots(from: ds)
        isLoading = false
    }
}
