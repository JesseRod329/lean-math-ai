import SwiftUI

struct DifficultyBadge: View {
    let difficulty: String

    var body: some View {
        Text(difficulty)
            .font(.caption2.weight(.bold))
            .padding(.horizontal, 8)
            .padding(.vertical, 3)
            .background(AppTheme.difficultyColor(difficulty).opacity(0.15))
            .foregroundStyle(AppTheme.difficultyColor(difficulty))
            .clipShape(Capsule())
    }
}
