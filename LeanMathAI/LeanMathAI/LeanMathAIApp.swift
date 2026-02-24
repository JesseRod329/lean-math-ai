import SwiftUI

@main
struct LeanMathAIApp: App {
    @State private var directoryService = DataDirectoryService()
    @State private var configService = ConfigService()

    var body: some Scene {
        WindowGroup {
            ContentView()
                .environment(directoryService)
                .environment(configService)
                .preferredColorScheme(.dark)
                .frame(minWidth: 1000, minHeight: 650)
                .onAppear {
                    if let baseDir = directoryService.baseDirectory {
                        configService.configure(baseDirectory: baseDir)
                    }
                    NotificationService.shared.requestAuthorization()
                }
        }
        .windowStyle(.titleBar)
        .defaultSize(width: 1200, height: 800)
        .commands {
            CommandMenu("Navigate") {
                Button("Dashboard") {
                    NotificationCenter.default.post(name: .navigateTo, object: SidebarItem.dashboard)
                }
                .keyboardShortcut("1")

                Button("Papers") {
                    NotificationCenter.default.post(name: .navigateTo, object: SidebarItem.papers)
                }
                .keyboardShortcut("2")

                Button("Theorems") {
                    NotificationCenter.default.post(name: .navigateTo, object: SidebarItem.theorems)
                }
                .keyboardShortcut("3")

                Button("Proofs") {
                    NotificationCenter.default.post(name: .navigateTo, object: SidebarItem.proofs)
                }
                .keyboardShortcut("4")

                Button("Timeline") {
                    NotificationCenter.default.post(name: .navigateTo, object: SidebarItem.timeline)
                }
                .keyboardShortcut("5")

                Button("Settings") {
                    NotificationCenter.default.post(name: .navigateTo, object: SidebarItem.settings)
                }
                .keyboardShortcut("6")
            }
        }

        MenuBarExtra {
            VStack(alignment: .leading, spacing: 8) {
                Text("LeanMath AI")
                    .font(.headline)

                Divider()

                Button("Open Dashboard") {
                    NSApp.activate(ignoringOtherApps: true)
                }

                Button("Quit") {
                    NSApp.terminate(nil)
                }
            }
            .padding(12)
            .frame(width: 200)
        } label: {
            Image(systemName: "function")
        }
        .menuBarExtraStyle(.window)
    }
}

extension Notification.Name {
    static let navigateTo = Notification.Name("navigateTo")
}
