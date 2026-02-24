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
}

struct SidebarView: View {
    @Binding var selection: SidebarItem

    var body: some View {
        List(SidebarItem.allCases, selection: $selection) { item in
            Label(item.label, systemImage: item.icon)
                .tag(item)
        }
        .listStyle(.sidebar)
        .frame(minWidth: 180)
    }
}
