import SwiftUI

struct PipelineFunnelView: View {
    let papers: Int
    let candidates: Int
    let processed: Int
    let proven: Int
    let formalized: Int

    var body: some View {
        VStack(alignment: .leading, spacing: 14) {
            Text("Pipeline Funnel -- Today")
                .font(AppTheme.headlineFont)
                .foregroundStyle(AppTheme.textAccent)

            funnelRow(label: "Papers Fetched", count: papers, maxCount: papers, color: AppTheme.textAccent, icon: "doc.text", delay: 0)

            chevron

            funnelRow(label: "Candidates Extracted", count: candidates, maxCount: papers, color: AppTheme.formalized, icon: "function", delay: 0.1)

            chevron

            funnelRow(label: "Processed", count: processed, maxCount: max(candidates, 1), color: .orange, icon: "gearshape", delay: 0.2)

            chevron

            funnelRow(label: "Formalized", count: formalized, maxCount: max(processed, 1), color: AppTheme.formalized, icon: "doc.badge.gearshape", delay: 0.3)

            chevron

            funnelRow(label: "Proven", count: proven, maxCount: max(processed, 1), color: AppTheme.proven, icon: "checkmark.seal.fill", delay: 0.4)
        }
    }

    private var chevron: some View {
        HStack {
            Spacer()
            Image(systemName: "chevron.down")
                .font(.caption)
                .foregroundStyle(AppTheme.textSecondary.opacity(0.5))
            Spacer()
        }
    }

    private func funnelRow(label: String, count: Int, maxCount: Int, color: Color, icon: String, delay: Double) -> some View {
        VStack(spacing: 6) {
            HStack {
                Image(systemName: icon)
                    .font(.caption)
                    .foregroundStyle(color)
                Text(label)
                    .font(.callout)
                    .foregroundStyle(AppTheme.textSecondary)
                Spacer()
                Text("\(count)")
                    .font(.callout.weight(.bold).monospacedDigit())
                    .foregroundStyle(color)
                    .contentTransition(.numericText())
            }

            GeometryReader { geo in
                ZStack(alignment: .leading) {
                    RoundedRectangle(cornerRadius: 4)
                        .fill(Color.white.opacity(0.05))

                    RoundedRectangle(cornerRadius: 4)
                        .fill(color.opacity(0.6))
                        .frame(width: maxCount > 0
                               ? geo.size.width * CGFloat(min(count, maxCount)) / CGFloat(max(maxCount, 1))
                               : 0)
                        .animation(.spring(duration: 0.6, bounce: 0.2).delay(delay), value: count)
                }
            }
            .frame(height: 8)
        }
    }
}
