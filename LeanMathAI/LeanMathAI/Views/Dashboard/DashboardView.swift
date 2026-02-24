import SwiftUI
import Charts

struct DashboardView: View {
    @Bindable var viewModel: DashboardViewModel
    @Bindable var pipeline: PipelineService

    var body: some View {
        ScrollView {
            VStack(spacing: AppTheme.sectionSpacing) {
                // Header with status
                statusHeader

                // Pipeline control
                GlowingCardView(accentColor: pipeline.isRunning ? AppTheme.proven : nil) {
                    PipelineControlView(pipeline: pipeline)
                }

                // Metric cards
                metricsGrid

                // Pipeline funnel
                GlowingCardView {
                    PipelineFunnelView(
                        papers: viewModel.pipelinePapers,
                        candidates: viewModel.pipelineCandidates,
                        processed: viewModel.pipelineProcessed,
                        proven: viewModel.pipelineProven
                    )
                }

                // Success chart
                if !viewModel.weeklySnapshots.isEmpty {
                    GlowingCardView {
                        SuccessChartView(snapshots: viewModel.weeklySnapshots)
                    }
                }

                // Recent activity
                if !viewModel.recentProofs.isEmpty {
                    GlowingCardView {
                        ActivityFeedView(results: viewModel.recentProofs)
                    }
                }
            }
            .padding(24)
        }
        .frame(maxWidth: .infinity, maxHeight: .infinity)
    }

    private var statusHeader: some View {
        HStack(spacing: 16) {
            StatusIndicatorView(
                isActive: viewModel.dashboardStatus?.isRunning ?? false
            )

            VStack(alignment: .leading, spacing: 4) {
                Text("Pipeline Status")
                    .font(AppTheme.headlineFont)
                    .foregroundStyle(AppTheme.textPrimary)

                if let status = viewModel.dashboardStatus {
                    Text("Last update: \(status.hour) on \(status.date)")
                        .font(AppTheme.captionFont)
                        .foregroundStyle(AppTheme.textSecondary)
                } else {
                    Text("No status data available")
                        .font(AppTheme.captionFont)
                        .foregroundStyle(AppTheme.textSecondary)
                }
            }

            Spacer()

            if let refresh = viewModel.lastRefresh {
                Text("Refreshed \(refresh, style: .relative) ago")
                    .font(.caption2)
                    .foregroundStyle(AppTheme.textSecondary)
            }
        }
        .padding(AppTheme.cardPadding)
        .background(AppTheme.cardBackground)
        .clipShape(RoundedRectangle(cornerRadius: AppTheme.cardCornerRadius))
        .overlay(
            RoundedRectangle(cornerRadius: AppTheme.cardCornerRadius)
                .stroke(AppTheme.cardBorder, lineWidth: 1)
        )
    }

    private var metricsGrid: some View {
        LazyVGrid(columns: [
            GridItem(.flexible()),
            GridItem(.flexible()),
            GridItem(.flexible()),
            GridItem(.flexible())
        ], spacing: AppTheme.itemSpacing) {
            MetricCardView(
                title: "Papers Today",
                value: viewModel.pipelinePapers,
                icon: "doc.text",
                color: AppTheme.textAccent
            )
            MetricCardView(
                title: "Candidates",
                value: viewModel.pipelineCandidates,
                icon: "function",
                color: AppTheme.formalized
            )
            MetricCardView(
                title: "Proven",
                value: viewModel.totalProven,
                icon: "checkmark.seal.fill",
                color: AppTheme.proven
            )
            MetricCardView(
                title: "Formalized",
                value: viewModel.totalFormalized,
                icon: "doc.badge.gearshape",
                color: AppTheme.formalized
            )
        }
    }
}
