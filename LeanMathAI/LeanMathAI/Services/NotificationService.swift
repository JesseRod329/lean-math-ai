import Foundation
import UserNotifications

@MainActor
final class NotificationService {
    static let shared = NotificationService()

    private var isAuthorized = false

    func requestAuthorization() {
        UNUserNotificationCenter.current().requestAuthorization(options: [.alert, .sound, .badge]) { granted, _ in
            Task { @MainActor in
                self.isAuthorized = granted
            }
        }
    }

    func notifyProofResult(name: String, status: String, paperTitle: String) {
        guard isAuthorized else { return }

        let content = UNMutableNotificationContent()
        content.title = status == "proven"
            ? "Theorem Proven!"
            : "Proof \(status.capitalized)"
        content.body = "\(name)\nFrom: \(paperTitle)"
        content.sound = status == "proven" ? .default : nil

        let request = UNNotificationRequest(
            identifier: UUID().uuidString,
            content: content,
            trigger: nil
        )
        UNUserNotificationCenter.current().add(request)
    }

    func notifyPipelineComplete(proven: Int, formalized: Int, failed: Int) {
        guard isAuthorized else { return }

        let content = UNMutableNotificationContent()
        content.title = "Pipeline Complete"
        content.body = "Results: \(proven) proven, \(formalized) formalized, \(failed) failed"
        content.sound = proven > 0 ? .default : nil

        let request = UNNotificationRequest(
            identifier: UUID().uuidString,
            content: content,
            trigger: nil
        )
        UNUserNotificationCenter.current().add(request)
    }
}
