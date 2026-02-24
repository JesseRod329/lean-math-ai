import SwiftUI

struct TheoremsListView: View {
    @Bindable var viewModel: TheoremsViewModel

    var body: some View {
        VStack(spacing: 0) {
            // Date + difficulty filter bar
            filterBar

            if viewModel.filteredCandidates.isEmpty && !viewModel.isLoading {
                EmptyStateView(
                    icon: "function",
                    title: "No Theorems Found",
                    message: "No theorem candidates for this date or filter."
                )
            } else {
                List(viewModel.filteredCandidates) { candidate in
                    TheoremRowView(
                        candidate: candidate,
                        status: viewModel.status(for: candidate)
                    )
                    .listRowBackground(Color.clear)
                    .listRowSeparatorTint(AppTheme.cardBorder)
                }
                .listStyle(.plain)
                .scrollContentBackground(.hidden)
            }
        }
        .searchable(text: $viewModel.searchText, prompt: "Search theorems...")
        .navigationTitle("Theorems")
        .toolbar {
            ToolbarItem {
                Text("\(viewModel.filteredCandidates.count) theorems")
                    .font(.caption)
                    .foregroundStyle(AppTheme.textSecondary)
            }
        }
    }

    private var filterBar: some View {
        HStack(spacing: 12) {
            // Date picker
            ScrollView(.horizontal, showsIndicators: false) {
                HStack(spacing: 8) {
                    ForEach(viewModel.availableDates, id: \.self) { date in
                        Button(action: { viewModel.selectedDate = date }) {
                            Text(formatDate(date))
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
                        }
                        .buttonStyle(.plain)
                    }
                }
            }

            Divider().frame(height: 20)

            // Difficulty filters
            HStack(spacing: 6) {
                Button(action: { viewModel.selectedDifficulty = nil }) {
                    Text("All")
                        .font(.caption.weight(.medium))
                        .padding(.horizontal, 10)
                        .padding(.vertical, 5)
                        .background(viewModel.selectedDifficulty == nil ? AppTheme.textAccent.opacity(0.2) : Color.clear)
                        .foregroundStyle(viewModel.selectedDifficulty == nil ? AppTheme.textAccent : AppTheme.textSecondary)
                        .clipShape(Capsule())
                }
                .buttonStyle(.plain)

                ForEach(DifficultyLevel.allCases) { level in
                    Button(action: { viewModel.selectedDifficulty = level }) {
                        Text(level.displayName)
                            .font(.caption.weight(.medium))
                            .padding(.horizontal, 10)
                            .padding(.vertical, 5)
                            .background(
                                viewModel.selectedDifficulty == level
                                    ? level.color.opacity(0.2)
                                    : Color.clear
                            )
                            .foregroundStyle(
                                viewModel.selectedDifficulty == level
                                    ? level.color
                                    : AppTheme.textSecondary
                            )
                            .clipShape(Capsule())
                    }
                    .buttonStyle(.plain)
                }
            }
        }
        .padding(.horizontal, 16)
        .padding(.vertical, 10)
        .background(AppTheme.backgroundPrimary.opacity(0.5))
    }

    private func formatDate(_ date: String) -> String {
        let formatter = DateFormatter()
        formatter.dateFormat = "yyyy-MM-dd"
        guard let d = formatter.date(from: date) else { return date }
        formatter.dateFormat = "MMM d"
        return formatter.string(from: d)
    }
}
