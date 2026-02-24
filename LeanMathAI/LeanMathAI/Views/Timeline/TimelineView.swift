import SwiftUI
import Charts

struct TimelineView: View {
    @Bindable var viewModel: TimelineViewModel

    var body: some View {
        ScrollView {
            VStack(spacing: AppTheme.sectionSpacing) {
                // Trend chart
                if !viewModel.snapshots.isEmpty {
                    GlowingCardView {
                        trendChart
                    }
                }

                // Day cards
                ForEach(viewModel.snapshots) { snapshot in
                    DayCardView(snapshot: snapshot)
                }
            }
            .padding(24)
        }
        .navigationTitle("Timeline")
        .frame(maxWidth: .infinity, maxHeight: .infinity)
    }

    private var trendChart: some View {
        VStack(alignment: .leading, spacing: 12) {
            Text("Success Rate Trend")
                .font(AppTheme.headlineFont)
                .foregroundStyle(AppTheme.textAccent)

            Chart(viewModel.snapshots.reversed()) { snapshot in
                LineMark(
                    x: .value("Date", snapshot.date, unit: .day),
                    y: .value("Rate", snapshot.successRate)
                )
                .foregroundStyle(AppTheme.proven)
                .interpolationMethod(.catmullRom)
                .lineStyle(StrokeStyle(lineWidth: 2))

                AreaMark(
                    x: .value("Date", snapshot.date, unit: .day),
                    y: .value("Rate", snapshot.successRate)
                )
                .foregroundStyle(
                    LinearGradient(
                        colors: [AppTheme.proven.opacity(0.3), AppTheme.proven.opacity(0.0)],
                        startPoint: .top,
                        endPoint: .bottom
                    )
                )

                PointMark(
                    x: .value("Date", snapshot.date, unit: .day),
                    y: .value("Rate", snapshot.successRate)
                )
                .foregroundStyle(AppTheme.proven)
                .symbolSize(30)
            }
            .chartYAxis {
                AxisMarks(values: .stride(by: 25)) { value in
                    AxisGridLine(stroke: StrokeStyle(lineWidth: 0.5))
                        .foregroundStyle(Color.white.opacity(0.1))
                    AxisValueLabel {
                        if let v = value.as(Double.self) {
                            Text("\(Int(v))%")
                                .foregroundStyle(AppTheme.textSecondary)
                        }
                    }
                }
            }
            .chartXAxis {
                AxisMarks { _ in
                    AxisValueLabel(format: .dateTime.day().month(.abbreviated))
                        .foregroundStyle(AppTheme.textSecondary)
                }
            }
            .chartYScale(domain: 0...100)
            .frame(height: 200)
        }
    }
}

struct DayCardView: View {
    let snapshot: DailySnapshot

    var body: some View {
        GlowingCardView(accentColor: snapshot.successRate > 50 ? AppTheme.proven : AppTheme.formalized) {
            VStack(alignment: .leading, spacing: 12) {
                // Date header
                HStack {
                    Text(snapshot.date, style: .date)
                        .font(AppTheme.headlineFont)
                        .foregroundStyle(AppTheme.textPrimary)

                    Spacer()

                    Text(String(format: "%.0f%%", snapshot.successRate))
                        .font(AppTheme.smallMetricFont)
                        .foregroundStyle(snapshot.successRate > 50 ? AppTheme.proven : AppTheme.formalized)
                }

                // Stats row
                HStack(spacing: 20) {
                    statItem("Papers", count: snapshot.paperCount, color: AppTheme.textAccent)
                    statItem("Candidates", count: snapshot.candidateCount, color: AppTheme.formalized)
                    statItem("Proven", count: snapshot.provenCount, color: AppTheme.proven)
                    statItem("Formalized", count: snapshot.formalizedCount, color: AppTheme.formalized)
                    statItem("Failed", count: snapshot.failedCount, color: AppTheme.failed)

                    if snapshot.templateCount > 0 {
                        statItem("Template", count: snapshot.templateCount, color: AppTheme.template)
                    }
                    if snapshot.trivialCount > 0 {
                        statItem("Trivial", count: snapshot.trivialCount, color: AppTheme.trivial)
                    }
                }

                // Mini funnel bar
                GeometryReader { geo in
                    HStack(spacing: 2) {
                        if snapshot.provenCount > 0 {
                            Rectangle()
                                .fill(AppTheme.proven)
                                .frame(width: barWidth(geo, count: snapshot.provenCount))
                        }
                        if snapshot.formalizedCount > 0 {
                            Rectangle()
                                .fill(AppTheme.formalized)
                                .frame(width: barWidth(geo, count: snapshot.formalizedCount))
                        }
                        if snapshot.failedCount > 0 {
                            Rectangle()
                                .fill(AppTheme.failed)
                                .frame(width: barWidth(geo, count: snapshot.failedCount))
                        }
                        if snapshot.templateCount > 0 {
                            Rectangle()
                                .fill(AppTheme.template)
                                .frame(width: barWidth(geo, count: snapshot.templateCount))
                        }
                        if snapshot.trivialCount > 0 {
                            Rectangle()
                                .fill(AppTheme.trivial)
                                .frame(width: barWidth(geo, count: snapshot.trivialCount))
                        }
                        Spacer(minLength: 0)
                    }
                    .clipShape(RoundedRectangle(cornerRadius: 3))
                }
                .frame(height: 6)
            }
        }
    }

    private func statItem(_ label: String, count: Int, color: Color) -> some View {
        VStack(spacing: 2) {
            Text("\(count)")
                .font(.callout.weight(.bold).monospacedDigit())
                .foregroundStyle(color)
            Text(label)
                .font(.caption2)
                .foregroundStyle(AppTheme.textSecondary)
        }
    }

    private func barWidth(_ geo: GeometryProxy, count: Int) -> CGFloat {
        guard snapshot.totalProcessed > 0 else { return 0 }
        return geo.size.width * CGFloat(count) / CGFloat(snapshot.totalProcessed)
    }
}
