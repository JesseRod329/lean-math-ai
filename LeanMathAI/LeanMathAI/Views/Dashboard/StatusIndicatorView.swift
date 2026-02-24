import SwiftUI

struct StatusIndicatorView: View {
    let isActive: Bool
    @State private var isPulsing = false

    var body: some View {
        HStack(spacing: 8) {
            Circle()
                .fill(isActive ? AppTheme.proven : AppTheme.textSecondary)
                .frame(width: 10, height: 10)
                .shadow(
                    color: (isActive ? AppTheme.proven : AppTheme.textSecondary).opacity(isPulsing ? 0.7 : 0.3),
                    radius: isPulsing ? 8 : 4
                )

            Text(isActive ? "Running" : "Idle")
                .font(.caption.weight(.semibold))
                .foregroundStyle(isActive ? AppTheme.proven : AppTheme.textSecondary)
        }
        .padding(.horizontal, 12)
        .padding(.vertical, 6)
        .background((isActive ? AppTheme.proven : AppTheme.textSecondary).opacity(0.1))
        .clipShape(Capsule())
        .onAppear {
            if isActive {
                withAnimation(.easeInOut(duration: 1.5).repeatForever(autoreverses: true)) {
                    isPulsing = true
                }
            }
        }
        .onChange(of: isActive) { _, newValue in
            if newValue {
                withAnimation(.easeInOut(duration: 1.5).repeatForever(autoreverses: true)) {
                    isPulsing = true
                }
            } else {
                withAnimation(.easeInOut(duration: 0.3)) {
                    isPulsing = false
                }
            }
        }
    }
}
