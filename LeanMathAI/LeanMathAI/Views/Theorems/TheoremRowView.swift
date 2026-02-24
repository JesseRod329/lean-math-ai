import SwiftUI

struct TheoremRowView: View {
    let candidate: TheoremCandidate
    let status: ProofStatus?
    @State private var isExpanded = false
    @State private var isHovering = false

    var body: some View {
        VStack(alignment: .leading, spacing: 8) {
            // Header: name + badges
            HStack(spacing: 8) {
                if let status {
                    ProofStatusDot(status: status)
                }

                Text(candidate.name)
                    .font(.headline)
                    .foregroundStyle(AppTheme.textPrimary)
                    .lineLimit(isExpanded ? nil : 1)

                Spacer()

                DifficultyBadge(difficulty: candidate.difficulty)

                if let status {
                    ProofStatusBadge(status: status)
                }
                Image(systemName: isExpanded ? "chevron.up" : "chevron.down")
                    .font(.caption2)
                    .foregroundStyle(AppTheme.textSecondary)
            }

            // Statement preview
            Text(candidate.statement)
                .font(.callout)
                .foregroundStyle(AppTheme.textSecondary)
                .lineLimit(isExpanded ? nil : 2)

            // Object tags
            HStack(spacing: 4) {
                ForEach(candidate.objects.prefix(4), id: \.self) { obj in
                    Text(obj)
                        .font(.caption2)
                        .padding(.horizontal, 6)
                        .padding(.vertical, 2)
                        .background(AppTheme.formalized.opacity(0.1))
                        .foregroundStyle(AppTheme.formalized)
                        .clipShape(Capsule())
                }
                if candidate.objects.count > 4 {
                    Text("+\(candidate.objects.count - 4)")
                        .font(.caption2)
                        .foregroundStyle(AppTheme.textSecondary)
                }

                Spacer()

                Text(candidate.source_paper.title)
                    .font(.caption2)
                    .foregroundStyle(AppTheme.textSecondary)
                    .lineLimit(1)
            }

            // Expanded details
            if isExpanded {
                Divider().background(AppTheme.cardBorder)

                VStack(alignment: .leading, spacing: 12) {
                    // Formalization hints
                    VStack(alignment: .leading, spacing: 4) {
                        Text("Formalization Hints")
                            .font(.caption.weight(.bold))
                            .foregroundStyle(AppTheme.textAccent)
                        Text(candidate.formalization_hints)
                            .font(.callout)
                            .foregroundStyle(AppTheme.textSecondary)
                    }

                    // Value
                    VStack(alignment: .leading, spacing: 4) {
                        Text("Value")
                            .font(.caption.weight(.bold))
                            .foregroundStyle(AppTheme.textAccent)
                        Text(candidate.value)
                            .font(.callout)
                            .foregroundStyle(AppTheme.textSecondary)
                    }

                    // Source paper link
                    if let url = candidate.source_paper.arxivURL {
                        Link(destination: url) {
                            HStack(spacing: 4) {
                                Image(systemName: "link")
                                Text("View paper on arXiv")
                            }
                            .font(.caption)
                            .foregroundStyle(AppTheme.textAccent)
                        }
                    }

                    // Extraction method
                    if let method = candidate.extraction_method {
                        HStack {
                            Text("Extracted via:")
                                .font(.caption2)
                                .foregroundStyle(AppTheme.textSecondary)
                            Text(method.uppercased())
                                .font(.caption2.weight(.bold))
                                .foregroundStyle(method == "llm" ? AppTheme.proven : AppTheme.formalized)
                        }
                    }

                    // LaTeX rendered statement
                    if candidate.hasLaTeX {
                        VStack(alignment: .leading, spacing: 4) {
                            Text("Rendered Statement")
                                .font(.caption.weight(.bold))
                                .foregroundStyle(AppTheme.textAccent)
                            LaTeXView(latex: candidate.statement, fontSize: 14)
                                .frame(height: 80)
                        }
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
