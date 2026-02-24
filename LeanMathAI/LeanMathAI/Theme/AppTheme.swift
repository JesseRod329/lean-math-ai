import SwiftUI

enum AppTheme {
    // MARK: - Backgrounds
    static let backgroundPrimary = Color(red: 0.04, green: 0.04, blue: 0.06)
    static let backgroundSecondary = Color(red: 0.10, green: 0.10, blue: 0.18)
    static let backgroundTertiary = Color(red: 0.086, green: 0.13, blue: 0.24)
    static let cardBackground = Color.white.opacity(0.04)
    static let cardBackgroundHover = Color.white.opacity(0.07)

    // MARK: - Status Colors
    static let proven = Color(red: 0.39, green: 1.0, blue: 0.85)
    static let formalized = Color(red: 0.996, green: 0.792, blue: 0.341)
    static let failed = Color(red: 1.0, green: 0.42, blue: 0.42)
    static let template = Color(red: 1.0, green: 0.67, blue: 0.47)
    static let trivial = Color(red: 0.6, green: 0.6, blue: 0.6)

    // MARK: - Text
    static let textPrimary = Color.white
    static let textSecondary = Color(red: 0.533, green: 0.573, blue: 0.69)
    static let textAccent = Color(red: 0.39, green: 1.0, blue: 0.85)

    // MARK: - Accent Gradient
    static let accentGradient = LinearGradient(
        colors: [
            Color(red: 1.0, green: 0.42, blue: 0.42),
            Color(red: 0.996, green: 0.792, blue: 0.341),
            Color(red: 0.282, green: 0.859, blue: 0.984),
            Color(red: 1.0, green: 0.624, blue: 0.953)
        ],
        startPoint: .leading,
        endPoint: .trailing
    )

    // MARK: - Card
    static let cardBorder = Color(red: 0.39, green: 0.59, blue: 1.0).opacity(0.1)
    static let cardBorderGlow = Color(red: 0.39, green: 0.59, blue: 1.0).opacity(0.25)

    // MARK: - Typography
    static let titleFont = Font.system(.largeTitle, design: .rounded, weight: .bold)
    static let headlineFont = Font.system(.headline, design: .rounded, weight: .semibold)
    static let bodyFont = Font.system(.body, design: .default)
    static let captionFont = Font.system(.caption, design: .default)
    static let codeFont = Font.system(.body, design: .monospaced)
    static let metricFont = Font.system(size: 36, weight: .bold, design: .rounded)
    static let smallMetricFont = Font.system(size: 24, weight: .bold, design: .rounded)

    // MARK: - Spacing
    static let cardPadding: CGFloat = 20
    static let cardCornerRadius: CGFloat = 16
    static let sectionSpacing: CGFloat = 24
    static let itemSpacing: CGFloat = 12

    // MARK: - Helpers
    static func difficultyColor(_ difficulty: String) -> Color {
        switch difficulty.lowercased() {
        case "easy": proven
        case "medium": formalized
        case "hard": failed
        default: textSecondary
        }
    }
}
