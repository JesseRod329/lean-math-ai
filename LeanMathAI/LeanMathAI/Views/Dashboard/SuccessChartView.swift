import SwiftUI
import Charts

struct SuccessChartView: View {
    let snapshots: [DailySnapshot]

    var body: some View {
        VStack(alignment: .leading, spacing: 12) {
            Text("Daily Results")
                .font(AppTheme.headlineFont)
                .foregroundStyle(AppTheme.textAccent)

            Chart {
                ForEach(snapshots.reversed()) { snapshot in
                    BarMark(
                        x: .value("Date", snapshot.date, unit: .day),
                        y: .value("Count", snapshot.provenCount)
                    )
                    .foregroundStyle(AppTheme.proven)
                    .position(by: .value("Status", "Proven"))

                    BarMark(
                        x: .value("Date", snapshot.date, unit: .day),
                        y: .value("Count", snapshot.formalizedCount)
                    )
                    .foregroundStyle(AppTheme.formalized)
                    .position(by: .value("Status", "Formalized"))

                    BarMark(
                        x: .value("Date", snapshot.date, unit: .day),
                        y: .value("Count", snapshot.failedCount)
                    )
                    .foregroundStyle(AppTheme.failed)
                    .position(by: .value("Status", "Failed"))
                }
            }
            .chartForegroundStyleScale([
                "Proven": AppTheme.proven,
                "Formalized": AppTheme.formalized,
                "Failed": AppTheme.failed
            ])
            .chartYAxis {
                AxisMarks { _ in
                    AxisGridLine(stroke: StrokeStyle(lineWidth: 0.5))
                        .foregroundStyle(Color.white.opacity(0.1))
                    AxisValueLabel()
                        .foregroundStyle(AppTheme.textSecondary)
                }
            }
            .chartXAxis {
                AxisMarks { _ in
                    AxisValueLabel(format: .dateTime.day().month(.abbreviated))
                        .foregroundStyle(AppTheme.textSecondary)
                }
            }
            .chartLegend(position: .bottom, spacing: 16)
            .frame(height: 220)
        }
    }
}
