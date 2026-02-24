import SwiftUI

struct PipelineFunnelView: View {
    let papers: Int
    let candidates: Int
    let processed: Int
    let proven: Int

    var body: some View {
        VStack(alignment: .leading, spacing: 14) {
            Text("Pipeline Funnel — Today")
                .font(AppTheme.headlineFont)
                .foregroundStyle(AppTheme.textAccent)

            funnelRow(label: "Papers Fetched", count: papers, maxCount: papers, color: AppTheme.textAccent, icon: "doc.text")

            chevron

            funnelRow(label: "Candidates Extracted", count: candidates, maxCount: papers, color: AppTheme.formalized, icon: "function")

            chevron

            funnelRow(label: "Processed", count: processed, maxCount: papers, color: .orange, icon: "gearshape")

            chevron

            funnelRow(label: "Proven", count: proven, maxCount: papers, color: AppTheme.proven, icon: "checkmark.seal.fill")
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

    private func funnelRow(label: String, count: Int, maxCount: Int, color: Color, icon: String) -> some View {
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
            }

            GeometryReader { geo in
                ZStack(alignment: .leading) {
                    RoundedRectangle(cornerRadius: 4)
                        .fill(Color.white.opacity(0.05))

                    RoundedRectangle(cornerRadius: 4)
                        .fill(color.opacity(0.6))
                        .frame(width: maxCount > 0
                               ? geo.size.width * CGFloat(count) / CGFloat(max(maxCount, 1))
                               : 0)
                }
            }
            .frame(height: 8)
        }
    }
}
