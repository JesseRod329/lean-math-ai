import SwiftUI

struct PapersListView: View {
    @Bindable var viewModel: PapersViewModel

    var body: some View {
        VStack(spacing: 0) {
            // Date picker ribbon
            dateRibbon

            // Category filter
            if !viewModel.allCategories.isEmpty {
                categoryFilter
            }

            // Papers list
            if viewModel.filteredPapers.isEmpty && !viewModel.isLoading {
                EmptyStateView(
                    icon: "doc.text.magnifyingglass",
                    title: "No Papers Found",
                    message: viewModel.searchText.isEmpty
                        ? "No papers available for this date."
                        : "No papers match your search."
                )
            } else {
                List(viewModel.filteredPapers) { paper in
                    PaperRowView(paper: paper)
                        .listRowBackground(Color.clear)
                        .listRowSeparatorTint(AppTheme.cardBorder)
                }
                .listStyle(.plain)
                .scrollContentBackground(.hidden)
            }
        }
        .searchable(text: $viewModel.searchText, prompt: "Search papers...")
        .navigationTitle("Papers")
        .toolbar {
            ToolbarItem {
                Text("\(viewModel.filteredPapers.count) papers")
                    .font(.caption)
                    .foregroundStyle(AppTheme.textSecondary)
            }
        }
    }

    private var dateRibbon: some View {
        ScrollView(.horizontal, showsIndicators: false) {
            HStack(spacing: 8) {
                ForEach(viewModel.availableDates, id: \.self) { date in
                    Button(action: { viewModel.selectedDate = date }) {
                        Text(formatDateChip(date))
                            .font(.caption.weight(.medium))
                            .padding(.horizontal, 12)
                            .padding(.vertical, 6)
                            .background(
                                viewModel.selectedDate == date
                                    ? AppTheme.textAccent.opacity(0.2)
                                    : AppTheme.cardBackground
                            )
                            .foregroundStyle(
                                viewModel.selectedDate == date
                                    ? AppTheme.textAccent
                                    : AppTheme.textSecondary
                            )
                            .clipShape(Capsule())
                            .overlay(
                                Capsule()
                                    .stroke(
                                        viewModel.selectedDate == date
                                            ? AppTheme.textAccent.opacity(0.5)
                                            : AppTheme.cardBorder,
                                        lineWidth: 1
                                    )
                            )
                    }
                    .buttonStyle(.plain)
                }
            }
            .padding(.horizontal, 16)
            .padding(.vertical, 10)
        }
        .background(AppTheme.backgroundPrimary.opacity(0.5))
    }

    private var categoryFilter: some View {
        ScrollView(.horizontal, showsIndicators: false) {
            HStack(spacing: 6) {
                ForEach(viewModel.allCategories, id: \.self) { category in
                    Button(action: {
                        if viewModel.selectedCategories.contains(category) {
                            viewModel.selectedCategories.remove(category)
                        } else {
                            viewModel.selectedCategories.insert(category)
                        }
                    }) {
                        Text(category)
                            .font(.caption2.weight(.medium))
                            .padding(.horizontal, 10)
                            .padding(.vertical, 4)
                            .background(
                                viewModel.selectedCategories.contains(category)
                                    ? AppTheme.formalized.opacity(0.2)
                                    : Color.clear
                            )
                            .foregroundStyle(
                                viewModel.selectedCategories.contains(category)
                                    ? AppTheme.formalized
                                    : AppTheme.textSecondary
                            )
                            .clipShape(Capsule())
                            .overlay(
                                Capsule().stroke(AppTheme.cardBorder, lineWidth: 1)
                            )
                    }
                    .buttonStyle(.plain)
                }
            }
            .padding(.horizontal, 16)
            .padding(.vertical, 6)
        }
    }

    private func formatDateChip(_ date: String) -> String {
        let formatter = DateFormatter()
        formatter.dateFormat = "yyyy-MM-dd"
        guard let d = formatter.date(from: date) else { return date }
        formatter.dateFormat = "MMM d"
        return formatter.string(from: d)
    }
}
