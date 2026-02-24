import SwiftUI

struct PipelineControlView: View {
    @Bindable var pipeline: PipelineService
    @State private var showLog = false

    var body: some View {
        VStack(alignment: .leading, spacing: 16) {
            // Header
            HStack {
                Text("Pipeline Control")
                    .font(AppTheme.headlineFont)
                    .foregroundStyle(AppTheme.textAccent)

                Spacer()

                // Phase indicator
                HStack(spacing: 6) {
                    Image(systemName: pipeline.phase.icon)
                        .foregroundStyle(pipeline.phase.color)
                        .symbolEffect(.pulse, isActive: pipeline.isRunning)
                    Text(pipeline.phase.displayName)
                        .font(.callout.weight(.medium))
                        .foregroundStyle(pipeline.phase.color)
                }
                .padding(.horizontal, 12)
                .padding(.vertical, 6)
                .background(pipeline.phase.color.opacity(0.1))
                .clipShape(Capsule())
            }

            // Live counters when running
            if pipeline.isRunning || pipeline.phase == .complete {
                HStack(spacing: 20) {
                    liveCounter("Papers", value: pipeline.paperCount, color: AppTheme.textAccent)
                    liveCounter("Candidates", value: pipeline.candidateCount, color: AppTheme.formalized)
                    liveCounter("Processed", value: pipeline.processedCount, color: .orange)
                    liveCounter("Proven", value: pipeline.provenCount, color: AppTheme.proven)
                    liveCounter("Formalized", value: pipeline.formalizedCount, color: AppTheme.formalized)
                }
            }

            // Error message
            if let error = pipeline.errorMessage {
                HStack(spacing: 8) {
                    Image(systemName: "exclamationmark.triangle.fill")
                        .foregroundStyle(AppTheme.failed)
                    Text(error)
                        .font(.callout)
                        .foregroundStyle(AppTheme.failed)
                }
            }

            // Action buttons
            HStack(spacing: 12) {
                if pipeline.isRunning {
                    Button(action: pipeline.stop) {
                        HStack(spacing: 6) {
                            Image(systemName: "stop.fill")
                            Text("Stop")
                        }
                        .font(.callout.weight(.semibold))
                        .foregroundStyle(.white)
                        .padding(.horizontal, 20)
                        .padding(.vertical, 10)
                        .background(AppTheme.failed)
                        .clipShape(RoundedRectangle(cornerRadius: 10))
                    }
                    .buttonStyle(.plain)
                } else {
                    // Full pipeline run
                    Button(action: pipeline.runFullPipeline) {
                        HStack(spacing: 6) {
                            Image(systemName: "play.fill")
                            Text("Run Full Pipeline")
                        }
                        .font(.callout.weight(.semibold))
                        .foregroundStyle(AppTheme.backgroundPrimary)
                        .padding(.horizontal, 20)
                        .padding(.vertical, 10)
                        .background(AppTheme.proven)
                        .clipShape(RoundedRectangle(cornerRadius: 10))
                    }
                    .buttonStyle(.plain)

                    // Individual phases
                    Button(action: pipeline.fetchPapers) {
                        HStack(spacing: 4) {
                            Image(systemName: "arrow.down.doc")
                            Text("Fetch Papers")
                        }
                        .font(.caption.weight(.medium))
                        .foregroundStyle(AppTheme.textAccent)
                        .padding(.horizontal, 14)
                        .padding(.vertical, 8)
                        .background(AppTheme.textAccent.opacity(0.1))
                        .clipShape(RoundedRectangle(cornerRadius: 8))
                        .overlay(
                            RoundedRectangle(cornerRadius: 8)
                                .stroke(AppTheme.textAccent.opacity(0.3), lineWidth: 1)
                        )
                    }
                    .buttonStyle(.plain)

                    Button(action: pipeline.extractTheorems) {
                        HStack(spacing: 4) {
                            Image(systemName: "magnifyingglass")
                            Text("Extract Theorems")
                        }
                        .font(.caption.weight(.medium))
                        .foregroundStyle(AppTheme.formalized)
                        .padding(.horizontal, 14)
                        .padding(.vertical, 8)
                        .background(AppTheme.formalized.opacity(0.1))
                        .clipShape(RoundedRectangle(cornerRadius: 8))
                        .overlay(
                            RoundedRectangle(cornerRadius: 8)
                                .stroke(AppTheme.formalized.opacity(0.3), lineWidth: 1)
                        )
                    }
                    .buttonStyle(.plain)
                }

                Spacer()

                // Toggle log
                Button(action: { withAnimation { showLog.toggle() } }) {
                    HStack(spacing: 4) {
                        Image(systemName: "terminal")
                        Text(showLog ? "Hide Log" : "Show Log")
                    }
                    .font(.caption.weight(.medium))
                    .foregroundStyle(AppTheme.textSecondary)
                    .padding(.horizontal, 12)
                    .padding(.vertical, 6)
                    .background(Color.white.opacity(0.05))
                    .clipShape(RoundedRectangle(cornerRadius: 8))
                }
                .buttonStyle(.plain)

                if let lastRun = pipeline.lastRunDate {
                    Text("Last: \(lastRun, style: .relative) ago")
                        .font(.caption2)
                        .foregroundStyle(AppTheme.textSecondary)
                }
            }

            // Log output
            if showLog && !pipeline.logOutput.isEmpty {
                logView
            }
        }
    }

    private func liveCounter(_ label: String, value: Int, color: Color) -> some View {
        VStack(spacing: 2) {
            Text("\(value)")
                .font(.title3.weight(.bold).monospacedDigit())
                .foregroundStyle(color)
                .contentTransition(.numericText())
            Text(label)
                .font(.caption2)
                .foregroundStyle(AppTheme.textSecondary)
        }
    }

    private var logView: some View {
        ScrollViewReader { proxy in
            ScrollView {
                LazyVStack(alignment: .leading, spacing: 2) {
                    ForEach(Array(pipeline.logOutput.enumerated()), id: \.offset) { idx, line in
                        Text(line)
                            .font(.system(size: 11, design: .monospaced))
                            .foregroundStyle(logColor(for: line))
                            .id(idx)
                    }
                }
                .padding(10)
            }
            .frame(maxHeight: 250)
            .background(Color.black.opacity(0.5))
            .clipShape(RoundedRectangle(cornerRadius: 8))
            .overlay(
                RoundedRectangle(cornerRadius: 8)
                    .stroke(AppTheme.cardBorder, lineWidth: 1)
            )
            .onChange(of: pipeline.logOutput.count) { _, _ in
                if let last = pipeline.logOutput.indices.last {
                    proxy.scrollTo(last, anchor: .bottom)
                }
            }
        }
    }

    private func logColor(for line: String) -> Color {
        if line.contains("[SUCCESS]") || line.contains("PROVEN") { return AppTheme.proven }
        if line.contains("[ERROR]") || line.contains("FAILED") { return AppTheme.failed }
        if line.contains("[WARNING]") || line.contains("TEMPLATE") || line.contains("TRIVIAL") { return AppTheme.formalized }
        if line.contains("PHASE") { return AppTheme.textAccent }
        return AppTheme.textSecondary
    }
}
