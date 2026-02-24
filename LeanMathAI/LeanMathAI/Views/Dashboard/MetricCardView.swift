import SwiftUI

struct MetricCardView: View {
    let title: String
    let value: Int
    let icon: String
    let color: Color

    @State private var isHovering = false

    var body: some View {
        VStack(alignment: .leading, spacing: 10) {
            HStack {
                Image(systemName: icon)
                    .font(.title3)
                    .foregroundStyle(color)
                Spacer()
            }

            Text("\(value)")
                .font(AppTheme.metricFont)
                .foregroundStyle(color)
                .contentTransition(.numericText())

            Text(title)
                .font(AppTheme.captionFont)
                .foregroundStyle(AppTheme.textSecondary)
        }
        .padding(AppTheme.cardPadding)
        .background(isHovering ? AppTheme.cardBackgroundHover : AppTheme.cardBackground)
        .clipShape(RoundedRectangle(cornerRadius: AppTheme.cardCornerRadius))
        .overlay(
            RoundedRectangle(cornerRadius: AppTheme.cardCornerRadius)
                .stroke(color.opacity(isHovering ? 0.3 : 0.1), lineWidth: 1)
        )
        .shadow(color: color.opacity(isHovering ? 0.15 : 0), radius: 12)
        .onHover { isHovering = $0 }
        .animation(.easeOut(duration: 0.2), value: isHovering)
    }
}
