import SwiftUI

struct ActivityFeedView: View {
    let results: [ProofResult]

    var body: some View {
        VStack(alignment: .leading, spacing: 12) {
            Text("Recent Activity")
                .font(AppTheme.headlineFont)
                .foregroundStyle(AppTheme.textAccent)

            ForEach(results) { result in
                HStack(spacing: 12) {
                    ProofStatusDot(status: result.status)

                    VStack(alignment: .leading, spacing: 2) {
                        Text(result.name)
                            .font(.callout.weight(.medium))
                            .foregroundStyle(AppTheme.textPrimary)
                            .lineLimit(1)

                        HStack(spacing: 8) {
                            Text(result.date)
                                .font(.caption2)
                                .foregroundStyle(AppTheme.textSecondary)
                            if let hour = result.hour {
                                Text(hour)
                                    .font(.caption2)
                                    .foregroundStyle(AppTheme.textSecondary)
                            }
                            Text(result.difficulty)
                                .font(.caption2)
                                .foregroundStyle(AppTheme.difficultyColor(result.difficulty))
                        }
                    }

                    Spacer()

                    ProofStatusBadge(status: result.status)
                }
                .padding(.vertical, 4)

                if result.id != results.last?.id {
                    Divider()
                        .background(AppTheme.cardBorder)
                }
            }
        }
    }
}
