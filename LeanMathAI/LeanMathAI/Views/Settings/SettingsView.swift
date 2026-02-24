import SwiftUI

struct SettingsView: View {
    @Bindable var viewModel: SettingsViewModel
    @Environment(DataDirectoryService.self) var directoryService
    @Environment(ConfigService.self) var configService

    var body: some View {
        ScrollView {
            VStack(spacing: AppTheme.sectionSpacing) {
                directorySection
                arxivSection
                modelSection
                pipelineSection
                refinementSection
                scheduleSection
                dataOverviewSection
                aboutSection
            }
            .padding(24)
        }
        .navigationTitle("Settings")
        .frame(maxWidth: .infinity, maxHeight: .infinity)
    }

    // MARK: - Directory

    private var directorySection: some View {
        GlowingCardView {
            VStack(alignment: .leading, spacing: 16) {
                sectionHeader("Data Directory", icon: "folder")

                HStack {
                    Image(systemName: viewModel.isValid ? "checkmark.circle.fill" : "xmark.circle.fill")
                        .foregroundStyle(viewModel.isValid ? AppTheme.proven : AppTheme.failed)

                    Text(viewModel.directoryPath)
                        .font(.system(.body, design: .monospaced))
                        .foregroundStyle(AppTheme.textPrimary)
                        .lineLimit(1)
                        .truncationMode(.middle)

                    Spacer()

                    Button("Change...") { selectDirectory() }
                        .buttonStyle(.bordered)
                        .tint(AppTheme.textAccent)
                }
            }
        }
    }

    // MARK: - arXiv Paper Fetching

    private var arxivSection: some View {
        GlowingCardView {
            VStack(alignment: .leading, spacing: 16) {
                sectionHeader("arXiv Paper Fetching", icon: "arrow.down.doc")

                VStack(alignment: .leading, spacing: 12) {
                    Text("Categories")
                        .font(.callout.weight(.medium))
                        .foregroundStyle(AppTheme.textSecondary)

                    let allCategories = [
                        "math.NT", "math.CO", "math.AG", "math.AT", "math.CT",
                        "math.GR", "math.LO", "math.RA", "math.AC", "math.GN",
                        "cs.LO", "cs.AI"
                    ]

                    FlowLayout(spacing: 8) {
                        ForEach(allCategories, id: \.self) { cat in
                            categoryChip(cat)
                        }
                    }
                }

                Divider().overlay(AppTheme.cardBorder)

                configRow("Days back") {
                    Stepper(
                        "\(configService.config.arxiv.daysBack)",
                        value: Bindable(configService).config.arxiv.daysBack,
                        in: 1...7
                    )
                    .frame(width: 140)
                }

                configRow("Max papers") {
                    Picker("", selection: Bindable(configService).config.arxiv.maxResults) {
                        Text("10").tag(10)
                        Text("25").tag(25)
                        Text("50").tag(50)
                        Text("100").tag(100)
                    }
                    .frame(width: 100)
                }
            }
            .onChange(of: configService.config.arxiv) { configService.scheduleSave() }
        }
    }

    // MARK: - Model Selection

    private var modelSection: some View {
        GlowingCardView {
            VStack(alignment: .leading, spacing: 16) {
                sectionHeader("Model Selection", icon: "cpu")

                configRow("Backend") {
                    Picker("", selection: Bindable(configService).config.formalization.backend) {
                        Label("Local MLX", systemImage: "desktopcomputer").tag("mlx")
                        Label("Anthropic API", systemImage: "cloud").tag("anthropic")
                        Label("OpenAI API", systemImage: "cloud").tag("openai")
                    }
                    .frame(width: 180)
                }

                // Show relevant model picker based on backend
                switch configService.config.formalization.backend {
                case "mlx":
                    configRow("Local model") {
                        Picker("", selection: Bindable(configService).config.formalization.model) {
                            Text("DeepSeek-Coder-V2-Lite-4bit (16B)").tag("mlx-community/DeepSeek-Coder-V2-Lite-Instruct-4bit")
                            Text("DeepSeek-Coder-6.7B").tag("mlx-community/deepseek-coder-6.7b-instruct")
                        }
                        .frame(width: 280)
                    }

                case "anthropic":
                    configRow("Anthropic model") {
                        HStack(spacing: 8) {
                            Picker("", selection: Bindable(configService).config.formalization.anthropicModel) {
                                HStack {
                                    Text("Claude Sonnet 4")
                                }.tag("claude-sonnet-4-20250514")
                                Text("Claude 3.5 Haiku").tag("claude-3-5-haiku-20241022")
                            }
                            .frame(width: 200)

                            Text("Recommended")
                                .font(.caption2.weight(.bold))
                                .foregroundStyle(.black)
                                .padding(.horizontal, 6)
                                .padding(.vertical, 2)
                                .background(AppTheme.proven)
                                .clipShape(Capsule())
                        }
                    }

                    apiKeyRow("ANTHROPIC_API_KEY", isSet: configService.hasAnthropicKey())

                case "openai":
                    configRow("OpenAI model") {
                        Picker("", selection: Bindable(configService).config.formalization.openaiModel) {
                            Text("GPT-4o").tag("gpt-4o")
                            Text("GPT-4o mini").tag("gpt-4o-mini")
                        }
                        .frame(width: 160)
                    }

                    apiKeyRow("OPENAI_API_KEY", isSet: configService.hasOpenAIKey())

                default:
                    EmptyView()
                }

                // Quality note
                if configService.config.formalization.backend == "anthropic" {
                    HStack(spacing: 8) {
                        Image(systemName: "sparkles")
                            .foregroundStyle(AppTheme.proven)
                        Text("Claude produces ~70% valid statements and ~30% real proofs vs ~15% with local models")
                            .font(.caption)
                            .foregroundStyle(AppTheme.textSecondary)
                    }
                    .padding(10)
                    .background(AppTheme.proven.opacity(0.08))
                    .clipShape(RoundedRectangle(cornerRadius: 8))
                }
            }
            .onChange(of: configService.config.formalization) { configService.scheduleSave() }
        }
    }

    // MARK: - Pipeline Parameters

    private var pipelineSection: some View {
        GlowingCardView {
            VStack(alignment: .leading, spacing: 16) {
                sectionHeader("Pipeline Parameters", icon: "gearshape.2")

                configRow("Max candidates per run") {
                    Stepper(
                        "\(configService.config.extraction.maxCandidates)",
                        value: Bindable(configService).config.extraction.maxCandidates,
                        in: 1...20
                    )
                    .frame(width: 140)
                }

                configRow("Formalization attempts") {
                    Stepper(
                        "\(configService.config.formalization.attempts)",
                        value: Bindable(configService).config.formalization.attempts,
                        in: 1...5
                    )
                    .frame(width: 140)
                }

                configRow("Max proofs per hour") {
                    Stepper(
                        "\(configService.config.formalization.maxPerHour)",
                        value: Bindable(configService).config.formalization.maxPerHour,
                        in: 1...10
                    )
                    .frame(width: 140)
                }

                configRow("Max tokens") {
                    Picker("", selection: Bindable(configService).config.formalization.maxTokens) {
                        Text("2048").tag(2048)
                        Text("4096").tag(4096)
                        Text("8192").tag(8192)
                    }
                    .frame(width: 100)
                }

                configRow("Temperature") {
                    HStack(spacing: 8) {
                        Slider(
                            value: Bindable(configService).config.formalization.temperature,
                            in: 0.0...1.0,
                            step: 0.05
                        )
                        .frame(width: 160)

                        Text(String(format: "%.2f", configService.config.formalization.temperature))
                            .font(.system(.body, design: .monospaced))
                            .foregroundStyle(AppTheme.textPrimary)
                            .frame(width: 40)
                    }
                }
            }
            .onChange(of: configService.config.extraction) { configService.scheduleSave() }
            .onChange(of: configService.config.formalization) { configService.scheduleSave() }
        }
    }

    // MARK: - Refinement

    private var refinementSection: some View {
        GlowingCardView {
            VStack(alignment: .leading, spacing: 16) {
                sectionHeader("Refinement Pass", icon: "arrow.triangle.2.circlepath")

                configRow("Enable refinement") {
                    Toggle("", isOn: Bindable(configService).config.refinement.enabled)
                        .toggleStyle(.switch)
                        .tint(AppTheme.proven)
                }

                if configService.config.refinement.enabled {
                    configRow("Max refinement attempts") {
                        Stepper(
                            "\(configService.config.refinement.maxAttempts)",
                            value: Bindable(configService).config.refinement.maxAttempts,
                            in: 1...5
                        )
                        .frame(width: 140)
                    }
                }
            }
            .onChange(of: configService.config.refinement) { configService.scheduleSave() }
        }
    }

    // MARK: - Schedule

    private var scheduleSection: some View {
        GlowingCardView {
            VStack(alignment: .leading, spacing: 16) {
                sectionHeader("Schedule", icon: "clock")

                configRow("Auto-run pipeline") {
                    Toggle("", isOn: Bindable(configService).config.schedule.autoRun)
                        .toggleStyle(.switch)
                        .tint(AppTheme.proven)
                }

                if configService.config.schedule.autoRun {
                    configRow("Run interval") {
                        Picker("", selection: Bindable(configService).config.schedule.runIntervalMinutes) {
                            Text("15 min").tag(15)
                            Text("30 min").tag(30)
                            Text("1 hour").tag(60)
                            Text("2 hours").tag(120)
                            Text("4 hours").tag(240)
                        }
                        .frame(width: 120)
                    }
                }
            }
            .onChange(of: configService.config.schedule) { configService.scheduleSave() }
        }
    }

    // MARK: - Data Overview

    private var dataOverviewSection: some View {
        GlowingCardView {
            VStack(alignment: .leading, spacing: 16) {
                sectionHeader("Data Overview", icon: "chart.bar")

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
    }

    // MARK: - About

    private var aboutSection: some View {
        GlowingCardView {
            VStack(alignment: .leading, spacing: 12) {
                sectionHeader("About", icon: "info.circle")

                VStack(alignment: .leading, spacing: 6) {
                    aboutRow("App", value: "LeanMath AI Dashboard")
                    aboutRow("Platform", value: "macOS 14+")
                    aboutRow("Pipeline", value: "arXiv \u{2192} LLM \u{2192} Lean 4 \u{2192} Verify")
                    aboutRow("Proof Tiers", value: "Proven / Formalized / Failed / Template / Trivial")
                }
            }
        }
    }

    // MARK: - Helpers

    private func sectionHeader(_ title: String, icon: String) -> some View {
        HStack(spacing: 8) {
            Image(systemName: icon)
                .foregroundStyle(AppTheme.textAccent)
            Text(title)
                .font(AppTheme.headlineFont)
                .foregroundStyle(AppTheme.textAccent)
        }
    }

    private func configRow<Content: View>(_ label: String, @ViewBuilder content: () -> Content) -> some View {
        HStack {
            Text(label)
                .font(.callout)
                .foregroundStyle(AppTheme.textPrimary)
            Spacer()
            content()
        }
    }

    private func categoryChip(_ category: String) -> some View {
        let isSelected = configService.config.arxiv.categories.contains(category)
        return Button {
            if isSelected {
                configService.config.arxiv.categories.removeAll { $0 == category }
            } else {
                configService.config.arxiv.categories.append(category)
            }
            configService.scheduleSave()
        } label: {
            Text(category)
                .font(.caption.weight(.medium))
                .foregroundStyle(isSelected ? .black : AppTheme.textSecondary)
                .padding(.horizontal, 10)
                .padding(.vertical, 5)
                .background(isSelected ? AppTheme.textAccent : Color.white.opacity(0.05))
                .clipShape(Capsule())
                .overlay(
                    Capsule().stroke(isSelected ? Color.clear : AppTheme.cardBorder, lineWidth: 1)
                )
        }
        .buttonStyle(.plain)
    }

    @State private var showingKeyEntry = false
    @State private var keyEntryName = ""
    @State private var keyEntryValue = ""

    private func apiKeyRow(_ keyName: String, isSet: Bool) -> some View {
        configRow(keyName) {
            HStack(spacing: 8) {
                Circle()
                    .fill(isSet ? AppTheme.proven : AppTheme.failed)
                    .frame(width: 8, height: 8)
                Text(isSet ? "Set" : "Not set")
                    .font(.caption)
                    .foregroundStyle(isSet ? AppTheme.proven : AppTheme.textSecondary)

                Button("Set Key...") {
                    keyEntryName = keyName
                    keyEntryValue = ""
                    showingKeyEntry = true
                }
                .buttonStyle(.bordered)
                .controlSize(.small)
            }
        }
        .sheet(isPresented: $showingKeyEntry) {
            VStack(spacing: 16) {
                Text("Enter \(keyEntryName)")
                    .font(.headline)
                SecureField("API Key", text: $keyEntryValue)
                    .textFieldStyle(.roundedBorder)
                    .frame(width: 400)
                HStack {
                    Button("Cancel") { showingKeyEntry = false }
                        .buttonStyle(.bordered)
                    Button("Save") {
                        configService.setEnvironmentKey(keyEntryName, value: keyEntryValue)
                        showingKeyEntry = false
                    }
                    .buttonStyle(.borderedProminent)
                    .tint(AppTheme.textAccent)
                    .disabled(keyEntryValue.isEmpty)
                }
            }
            .padding(24)
        }
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
            configService.configure(baseDirectory: url)
        }
    }
}

// MARK: - Flow Layout for category chips

struct FlowLayout: Layout {
    var spacing: CGFloat = 8

    func sizeThatFits(proposal: ProposedViewSize, subviews: Subviews, cache: inout ()) -> CGSize {
        let result = layout(proposal: proposal, subviews: subviews)
        return result.size
    }

    func placeSubviews(in bounds: CGRect, proposal: ProposedViewSize, subviews: Subviews, cache: inout ()) {
        let result = layout(proposal: proposal, subviews: subviews)
        for (index, position) in result.positions.enumerated() {
            subviews[index].place(
                at: CGPoint(x: bounds.minX + position.x, y: bounds.minY + position.y),
                proposal: .unspecified
            )
        }
    }

    private func layout(proposal: ProposedViewSize, subviews: Subviews) -> (size: CGSize, positions: [CGPoint]) {
        let maxWidth = proposal.width ?? .infinity
        var positions: [CGPoint] = []
        var x: CGFloat = 0
        var y: CGFloat = 0
        var rowHeight: CGFloat = 0

        for subview in subviews {
            let size = subview.sizeThatFits(.unspecified)
            if x + size.width > maxWidth, x > 0 {
                x = 0
                y += rowHeight + spacing
                rowHeight = 0
            }
            positions.append(CGPoint(x: x, y: y))
            rowHeight = max(rowHeight, size.height)
            x += size.width + spacing
        }

        return (CGSize(width: maxWidth, height: y + rowHeight), positions)
    }
}
