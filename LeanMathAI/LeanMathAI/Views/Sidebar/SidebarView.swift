import SwiftUI

enum SidebarItem: String, CaseIterable, Identifiable {
    case dashboard
    case papers
    case theorems
    case proofs
    case timeline
    case settings

    var id: String { rawValue }

    var label: String {
        switch self {
        case .dashboard: "Dashboard"
        case .papers: "Papers"
        case .theorems: "Theorems"
        case .proofs: "Proofs"
        case .timeline: "Timeline"
        case .settings: "Settings"
        }
    }

    var icon: String {
        switch self {
        case .dashboard: "gauge.open.with.lines.needle.33percent"
        case .papers: "doc.text.magnifyingglass"
        case .theorems: "function"
        case .proofs: "checkmark.seal"
        case .timeline: "calendar.badge.clock"
        case .settings: "gearshape"
        }
    }

    var shortcut: KeyEquivalent {
        switch self {
        case .dashboard: "1"
        case .papers: "2"
        case .theorems: "3"
        case .proofs: "4"
        case .timeline: "5"
        case .settings: "6"
        }
    }

    /// Navigation items (excludes settings)
    static var navigationItems: [SidebarItem] {
        [.dashboard, .papers, .theorems, .proofs, .timeline]
    }
}

struct SidebarView: View {
    @Binding var selection: SidebarItem
    var proofCount: Int = 0
    var paperCount: Int = 0
    var provenCount: Int = 0
    var isRunning: Bool = false

    var body: some View {
        List(selection: $selection) {
            Section {
                ForEach(SidebarItem.navigationItems) { item in
                    HStack {
                        Label(item.label, systemImage: item.icon)
                        Spacer()
                        badgeFor(item)
                    }
                    .tag(item)
                }
            }

            Section {
                Label(SidebarItem.settings.label, systemImage: SidebarItem.settings.icon)
                    .tag(SidebarItem.settings)
            }
        }
        .listStyle(.sidebar)
        .frame(minWidth: 200)
    }

    @ViewBuilder
    private func badgeFor(_ item: SidebarItem) -> some View {
        switch item {
        case .dashboard:
            if isRunning {
                Circle()
                    .fill(AppTheme.proven)
                    .frame(width: 8, height: 8)
                    .shadow(color: AppTheme.proven.opacity(0.5), radius: 4)
            }
        case .proofs:
            if proofCount > 0 {
                badgePill("\(proofCount)", color: provenCount > 0 ? AppTheme.proven : AppTheme.formalized)
            }
        case .papers:
            if paperCount > 0 {
                badgePill("\(paperCount)", color: AppTheme.textAccent)
            }
        default:
            EmptyView()
        }
    }

    private func badgePill(_ text: String, color: Color) -> some View {
        Text(text)
            .font(.caption2.weight(.semibold).monospacedDigit())
            .padding(.horizontal, 6)
            .padding(.vertical, 2)
            .background(color.opacity(0.2))
            .foregroundStyle(color)
            .clipShape(Capsule())
    }
}
