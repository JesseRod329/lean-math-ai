import SwiftUI

struct GlowingCardView<Content: View>: View {
    var accentColor: Color?
    @ViewBuilder let content: () -> Content

    var body: some View {
        content()
            .padding(AppTheme.cardPadding)
            .background(AppTheme.cardBackground)
            .clipShape(RoundedRectangle(cornerRadius: AppTheme.cardCornerRadius))
            .overlay(
                RoundedRectangle(cornerRadius: AppTheme.cardCornerRadius)
                    .stroke(AppTheme.cardBorder, lineWidth: 1)
            )
            .overlay(alignment: .top) {
                if let accentColor {
                    accentColor
                        .frame(height: 2)
                        .clipShape(UnevenRoundedRectangle(
                            topLeadingRadius: AppTheme.cardCornerRadius,
                            bottomLeadingRadius: 0,
                            bottomTrailingRadius: 0,
                            topTrailingRadius: AppTheme.cardCornerRadius
                        ))
                } else {
                    AppTheme.accentGradient
                        .frame(height: 2)
                        .clipShape(UnevenRoundedRectangle(
                            topLeadingRadius: AppTheme.cardCornerRadius,
                            bottomLeadingRadius: 0,
                            bottomTrailingRadius: 0,
                            topTrailingRadius: AppTheme.cardCornerRadius
                        ))
                }
            }
    }
}
