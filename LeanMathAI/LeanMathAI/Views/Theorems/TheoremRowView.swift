import SwiftUI

struct TheoremRowView: View {
    let candidate: TheoremCandidate
    let status: ProofStatus?
    @State private var isExpanded = false

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
                }
            }
        }
        .padding(.vertical, 6)
        .contentShape(Rectangle())
        .onTapGesture {
            withAnimation(.easeInOut(duration: 0.2)) {
                isExpanded.toggle()
            }
        }
    }
}
