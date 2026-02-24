import SwiftUI

struct ContentView: View {
    @Environment(DataDirectoryService.self) var directoryService

    var body: some View {
        Group {
            if directoryService.isValid {
                MainView()
            } else {
                OnboardingView()
            }
        }
        .animation(.easeInOut(duration: 0.3), value: directoryService.isValid)
    }
}

struct OnboardingView: View {
    @Environment(DataDirectoryService.self) var directoryService
    @State private var isHovering = false

    var body: some View {
        ZStack {
            GradientBackground()

            VStack(spacing: 32) {
                Image(systemName: "function")
                    .font(.system(size: 64, weight: .light))
                    .foregroundStyle(AppTheme.textAccent)
                    .shadow(color: AppTheme.textAccent.opacity(0.4), radius: 20)

                VStack(spacing: 12) {
                    Text("LeanMath AI")
                        .font(.system(size: 36, weight: .bold, design: .rounded))
                        .foregroundStyle(AppTheme.textPrimary)

                    Text("Autonomous Formal Mathematics Dashboard")
                        .font(.title3)
                        .foregroundStyle(AppTheme.textSecondary)
                }

                VStack(spacing: 16) {
                    Text("Select your lean-math-ai data directory to get started")
                        .font(.body)
                        .foregroundStyle(AppTheme.textSecondary)

                    Button(action: selectDirectory) {
                        HStack(spacing: 10) {
                            Image(systemName: "folder.badge.plus")
                            Text("Choose Directory")
                        }
                        .font(.headline)
                        .foregroundStyle(AppTheme.backgroundPrimary)
                        .padding(.horizontal, 28)
                        .padding(.vertical, 14)
                        .background(AppTheme.textAccent)
                        .clipShape(RoundedRectangle(cornerRadius: 12))
                        .shadow(color: AppTheme.textAccent.opacity(isHovering ? 0.5 : 0.2), radius: isHovering ? 16 : 8)
                    }
                    .buttonStyle(.plain)
                    .onHover { isHovering = $0 }

                    if !directoryService.validationErrors.isEmpty {
                        VStack(alignment: .leading, spacing: 4) {
                            ForEach(directoryService.validationErrors, id: \.self) { error in
                                Text(error)
                                    .font(.caption)
                                    .foregroundStyle(AppTheme.failed)
                            }
                        }
                    }
                }
            }
        }
    }

    private func selectDirectory() {
        let panel = NSOpenPanel()
        panel.canChooseDirectories = true
        panel.canChooseFiles = false
        panel.allowsMultipleSelection = false
        panel.message = "Select the lean-math-ai project directory"
        panel.prompt = "Select"

        if panel.runModal() == .OK, let url = panel.url {
            directoryService.setDirectory(url)
        }
    }
}
