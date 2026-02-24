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
                }
        }
        .windowStyle(.titleBar)
        .defaultSize(width: 1200, height: 800)
    }
}
