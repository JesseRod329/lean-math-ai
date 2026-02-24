import SwiftUI

struct ProofRowView: View {
    let result: ProofResult
    var leanSource: String? = nil
    @State private var isExpanded = false
    @State private var isHovering = false

    var body: some View {
        VStack(alignment: .leading, spacing: 8) {
            // Header
            HStack(spacing: 10) {
                ProofStatusDot(status: result.status)

                VStack(alignment: .leading, spacing: 2) {
                    Text(result.name)
                        .font(.headline)
                        .foregroundStyle(AppTheme.textPrimary)
                        .lineLimit(isExpanded ? nil : 1)

                    HStack(spacing: 8) {
                        Text(result.date)
                            .font(.caption2)
                        if let hour = result.hour {
                            Text(hour)
                                .font(.caption2)
                        }
                        Text(result.source_paper.categories.joined(separator: ", "))
                            .font(.caption2)
                    }
                    .foregroundStyle(AppTheme.textSecondary)
                }

                Spacer()

                DifficultyBadge(difficulty: result.difficulty)
                ProofStatusBadge(status: result.status)
                Image(systemName: isExpanded ? "chevron.up" : "chevron.down")
                    .font(.caption2)
                    .foregroundStyle(AppTheme.textSecondary)
            }

            // Statement preview
            Text(result.statement)
                .font(.callout)
                .foregroundStyle(AppTheme.textSecondary)
                .lineLimit(isExpanded ? nil : 2)

            // Expanded: full details
            if isExpanded {
                Divider().background(AppTheme.cardBorder)

                // Status explanation
                HStack(spacing: 8) {
                    Image(systemName: result.status.icon)
                        .foregroundStyle(result.status.color)
                    Text(result.status.explanation)
                        .font(.caption)
                        .foregroundStyle(AppTheme.textSecondary)
                }

                // Mathematical objects
                if !result.objects.isEmpty {
                    VStack(alignment: .leading, spacing: 4) {
                        Text("Mathematical Objects")
                            .font(.caption.weight(.bold))
                            .foregroundStyle(AppTheme.textAccent)

                        FlowLayoutView(items: result.objects) { obj in
                            Text(obj)
                                .font(.caption2)
                                .padding(.horizontal, 6)
                                .padding(.vertical, 2)
                                .background(AppTheme.formalized.opacity(0.1))
                                .foregroundStyle(AppTheme.formalized)
                                .clipShape(Capsule())
                        }
                    }
                }

                // Formalization hints
                VStack(alignment: .leading, spacing: 4) {
                    Text("Formalization Hints")
                        .font(.caption.weight(.bold))
                        .foregroundStyle(AppTheme.textAccent)
                    Text(result.formalization_hints)
                        .font(.callout)
                        .foregroundStyle(AppTheme.textSecondary)
                }

                // Source paper
                if let url = result.source_paper.arxivURL {
                    Link(destination: url) {
                        HStack(spacing: 4) {
                            Image(systemName: "link")
                            Text(result.source_paper.title)
                                .lineLimit(1)
                        }
                        .font(.caption)
                        .foregroundStyle(AppTheme.textAccent)
                    }
                }

                // Lean 4 source code
                if let source = leanSource, !source.isEmpty {
                    VStack(alignment: .leading, spacing: 6) {
                        HStack {
                            Text("Lean 4 Code")
                                .font(.caption.weight(.bold))
                                .foregroundStyle(AppTheme.textAccent)
                            Spacer()
                            Button {
                                NSPasteboard.general.clearContents()
                                NSPasteboard.general.setString(source, forType: .string)
                            } label: {
                                HStack(spacing: 4) {
                                    Image(systemName: "doc.on.doc")
                                    Text("Copy")
                                }
                                .font(.caption2)
                                .foregroundStyle(AppTheme.textAccent)
                            }
                            .buttonStyle(.plain)
                        }
                        LeanCodeView(source: source)
                            .frame(maxHeight: 300)
                    }
                }
            }
        }
        .padding(.vertical, 6)
        .padding(8)
        .background(
            RoundedRectangle(cornerRadius: 10)
                .fill(isHovering ? Color.white.opacity(0.04) : Color.clear)
        )
        .onHover { isHovering = $0 }
        .animation(.easeOut(duration: 0.15), value: isHovering)
        .contentShape(Rectangle())
        .onTapGesture {
            withAnimation(.easeInOut(duration: 0.2)) {
                isExpanded.toggle()
            }
        }
    }
}

// Simple flow layout for tags
struct FlowLayoutView<Data: RandomAccessCollection, Content: View>: View where Data.Element: Hashable {
    let items: Data
    let content: (Data.Element) -> Content

    init(items: Data, @ViewBuilder content: @escaping (Data.Element) -> Content) {
        self.items = items
        self.content = content
    }

    var body: some View {
        HStack(spacing: 4) {
            ForEach(Array(items.prefix(6)), id: \.self) { item in
                content(item)
            }
            if items.count > 6 {
                Text("+\(items.count - 6)")
                    .font(.caption2)
                    .foregroundStyle(AppTheme.textSecondary)
            }
        }
    }
}
