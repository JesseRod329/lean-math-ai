import SwiftUI

struct MenuBarStatusView: View {
    let pipeline: PipelineService
    let dashboard: DashboardViewModel

    var body: some View {
        VStack(alignment: .leading, spacing: 12) {
            // Header
            HStack {
                Text("LeanMath AI")
                    .font(.headline)
                Spacer()
                StatusIndicatorView(isActive: pipeline.isRunning)
            }
            .padding(.bottom, 4)

            Divider()

            // Today's stats
            VStack(spacing: 8) {
                statRow("Papers", value: dashboard.pipelinePapers, icon: "doc.text", color: .blue)
                statRow("Candidates", value: dashboard.pipelineCandidates, icon: "function", color: .orange)
                statRow("Proven", value: dashboard.totalProven, icon: "checkmark.seal.fill", color: .green)
                statRow("Formalized", value: dashboard.totalFormalized, icon: "doc.badge.gearshape", color: .yellow)
                statRow("Failed", value: dashboard.totalFailed, icon: "xmark.circle", color: .red)
            }

            Divider()

            // Phase
            if pipeline.isRunning {
                HStack(spacing: 6) {
                    Image(systemName: pipeline.phase.icon)
                        .foregroundStyle(pipeline.phase.color)
                    Text(pipeline.phase.displayName)
                        .font(.callout)
                }

                ProgressView(value: pipeline.progressFraction)
                    .tint(pipeline.phase.color)
            }

            if let lastRun = pipeline.lastRunDate {
                Text("Last run: \(lastRun, style: .relative) ago")
                    .font(.caption2)
                    .foregroundStyle(.secondary)
            }

            Divider()

            // Actions
            HStack(spacing: 12) {
                Button("Open Dashboard") {
                    NSApp.activate(ignoringOtherApps: true)
                }
                .buttonStyle(.borderedProminent)
                .controlSize(.small)

                if !pipeline.isRunning {
                    Button("Run Pipeline") {
                        pipeline.runFullPipeline()
                    }
                    .buttonStyle(.bordered)
                    .controlSize(.small)
                }
            }

            Button("Quit") {
                NSApp.terminate(nil)
            }
            .buttonStyle(.plain)
            .font(.caption)
            .foregroundStyle(.secondary)
        }
        .padding(16)
        .frame(width: 280)
    }

    private func statRow(_ label: String, value: Int, icon: String, color: Color) -> some View {
        HStack {
            Image(systemName: icon)
                .font(.caption)
                .foregroundStyle(color)
                .frame(width: 16)
            Text(label)
                .font(.callout)
            Spacer()
            Text("\(value)")
                .font(.callout.weight(.bold).monospacedDigit())
                .foregroundStyle(color)
        }
    }
}
