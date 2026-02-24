import SwiftUI

struct PaperRowView: View {
    let paper: Paper
    @State private var isExpanded = false

    var body: some View {
        VStack(alignment: .leading, spacing: 8) {
            // Title
            Text(paper.title)
                .font(.headline)
                .foregroundStyle(AppTheme.textPrimary)
                .lineLimit(isExpanded ? nil : 2)

            // Authors
            Text(paper.authors.prefix(3).joined(separator: ", ") + (paper.authors.count > 3 ? " et al." : ""))
                .font(.caption)
                .foregroundStyle(AppTheme.textSecondary)
                .lineLimit(1)

            // Category badges + date
            HStack(spacing: 6) {
                ForEach(paper.categories, id: \.self) { category in
                    Text(category)
                        .font(.caption2.weight(.medium))
                        .padding(.horizontal, 6)
                        .padding(.vertical, 2)
                        .background(AppTheme.textAccent.opacity(0.12))
                        .foregroundStyle(AppTheme.textAccent)
                        .clipShape(Capsule())
                }

                Spacer()

                if let date = paper.publishedDate {
                    Text(date, style: .date)
                        .font(.caption2)
                        .foregroundStyle(AppTheme.textSecondary)
                }
            }

            // Expandable abstract
            if isExpanded {
                Divider().background(AppTheme.cardBorder)

                Text(paper.summary)
                    .font(.callout)
                    .foregroundStyle(AppTheme.textSecondary)
                    .lineLimit(10)

                HStack(spacing: 12) {
                    if let url = paper.arxivURL {
                        Link("arXiv", destination: url)
                            .font(.caption.weight(.medium))
                            .foregroundStyle(AppTheme.textAccent)
                    }
                    if let url = paper.pdfURL {
                        Link("PDF", destination: url)
                            .font(.caption.weight(.medium))
                            .foregroundStyle(AppTheme.textAccent)
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
