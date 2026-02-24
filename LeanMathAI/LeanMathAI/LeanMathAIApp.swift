import SwiftUI

@main
struct LeanMathAIApp: App {
    @State private var directoryService = DataDirectoryService()

    var body: some Scene {
        WindowGroup {
            ContentView()
                .environment(directoryService)
                .preferredColorScheme(.dark)
                .frame(minWidth: 1000, minHeight: 650)
        }
        .windowStyle(.titleBar)
        .defaultSize(width: 1200, height: 800)
    }
}
