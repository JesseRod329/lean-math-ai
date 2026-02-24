import SwiftUI

struct SettingsView: View {
    @Bindable var viewModel: SettingsViewModel
    @Environment(DataDirectoryService.self) var directoryService

    var body: some View {
        ScrollView {
            VStack(spacing: AppTheme.sectionSpacing) {
                // Directory settings
                GlowingCardView {
                    VStack(alignment: .leading, spacing: 16) {
                        Text("Data Directory")
                            .font(AppTheme.headlineFont)
                            .foregroundStyle(AppTheme.textAccent)

                        HStack {
                            Image(systemName: viewModel.isValid ? "checkmark.circle.fill" : "xmark.circle.fill")
                                .foregroundStyle(viewModel.isValid ? AppTheme.proven : AppTheme.failed)

                            Text(viewModel.directoryPath)
                                .font(.system(.body, design: .monospaced))
                                .foregroundStyle(AppTheme.textPrimary)
                                .lineLimit(1)
                                .truncationMode(.middle)

                            Spacer()

                            Button("Change...") {
                                selectDirectory()
                            }
                            .buttonStyle(.bordered)
                            .tint(AppTheme.textAccent)
                        }
                    }
                }

                // Data stats
                GlowingCardView {
                    VStack(alignment: .leading, spacing: 16) {
                        Text("Data Overview")
                            .font(AppTheme.headlineFont)
                            .foregroundStyle(AppTheme.textAccent)

                        LazyVGrid(columns: [
                            GridItem(.flexible()),
                            GridItem(.flexible()),
                            GridItem(.flexible())
                        ], spacing: 16) {
                            statBox("Dates Available", value: "\(viewModel.dateCount)")
                            statBox("Total Papers", value: "\(viewModel.totalPapers)")
                            statBox("Total Proofs", value: "\(viewModel.totalProofs)")
                        }
                    }
                }

                // About
                GlowingCardView {
                    VStack(alignment: .leading, spacing: 12) {
                        Text("About")
                            .font(AppTheme.headlineFont)
                            .foregroundStyle(AppTheme.textAccent)

                        VStack(alignment: .leading, spacing: 6) {
                            aboutRow("App", value: "LeanMath AI Dashboard")
                            aboutRow("Platform", value: "macOS 14+")
                            aboutRow("Pipeline", value: "arXiv → LLM → Lean 4 → Verify")
                            aboutRow("Proof Tiers", value: "Proven / Formalized / Failed / Template / Trivial")
                        }
                    }
                }
            }
            .padding(24)
        }
        .navigationTitle("Settings")
        .frame(maxWidth: .infinity, maxHeight: .infinity)
    }

    private func statBox(_ label: String, value: String) -> some View {
        VStack(spacing: 4) {
            Text(value)
                .font(AppTheme.smallMetricFont)
                .foregroundStyle(AppTheme.textPrimary)
            Text(label)
                .font(AppTheme.captionFont)
                .foregroundStyle(AppTheme.textSecondary)
        }
        .frame(maxWidth: .infinity)
        .padding(.vertical, 12)
        .background(Color.white.opacity(0.03))
        .clipShape(RoundedRectangle(cornerRadius: 10))
    }

    private func aboutRow(_ label: String, value: String) -> some View {
        HStack {
            Text(label)
                .font(.callout)
                .foregroundStyle(AppTheme.textSecondary)
            Spacer()
            Text(value)
                .font(.callout)
                .foregroundStyle(AppTheme.textPrimary)
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
            viewModel.refresh(from: directoryService)
        }
    }
}
