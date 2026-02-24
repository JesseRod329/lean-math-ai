import SwiftUI

struct EmptyStateView: View {
    let icon: String
    let title: String
    let message: String

    var body: some View {
        VStack(spacing: 16) {
            Image(systemName: icon)
                .font(.system(size: 48, weight: .light))
                .foregroundStyle(AppTheme.textSecondary.opacity(0.5))

            Text(title)
                .font(AppTheme.headlineFont)
                .foregroundStyle(AppTheme.textSecondary)

            Text(message)
                .font(AppTheme.captionFont)
                .foregroundStyle(AppTheme.textSecondary.opacity(0.7))
                .multilineTextAlignment(.center)
        }
        .frame(maxWidth: .infinity, maxHeight: .infinity)
        .padding(40)
    }
}
