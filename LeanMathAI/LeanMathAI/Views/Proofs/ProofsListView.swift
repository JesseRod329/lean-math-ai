import SwiftUI

struct ProofsListView: View {
    @Bindable var viewModel: ProofsViewModel

    var body: some View {
        VStack(spacing: 0) {
            // Status filter bar
            statusFilterBar

            if viewModel.filteredResults.isEmpty && !viewModel.isLoading {
                EmptyStateView(
                    icon: "checkmark.seal",
                    title: "No Proofs Found",
                    message: "No proof results for this date or filter."
                )
            } else {
                List(viewModel.filteredResults) { result in
                    ProofRowView(result: result, leanSource: viewModel.leanSource(for: result))
                        .listRowBackground(Color.clear)
                        .listRowSeparatorTint(AppTheme.cardBorder)
                }
                .listStyle(.plain)
                .scrollContentBackground(.hidden)
            }
        }
        .navigationTitle("Proofs")
        .toolbar {
            ToolbarItem {
                Text("\(viewModel.filteredResults.count) results")
                    .font(.caption)
                    .foregroundStyle(AppTheme.textSecondary)
            }
        }
    }

    private var statusFilterBar: some View {
        VStack(spacing: 8) {
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

            // Status tier filter
            HStack(spacing: 6) {
                statusFilterChip(nil, label: "All", count: viewModel.totalCount)

                ForEach(ProofStatus.allCases) { status in
                    statusFilterChip(status, label: status.displayName, count: viewModel.statusCounts[status] ?? 0)
                }
            }
        }
        .padding(.horizontal, 16)
        .padding(.vertical, 10)
        .background(AppTheme.backgroundPrimary.opacity(0.5))
    }

    private func statusFilterChip(_ status: ProofStatus?, label: String, count: Int) -> some View {
        Button(action: { viewModel.selectedStatus = status }) {
            HStack(spacing: 4) {
                if let status {
                    Image(systemName: status.icon)
                        .font(.caption2)
                }
                Text(label)
                    .font(.caption.weight(.medium))
                Text("\(count)")
                    .font(.caption2.monospacedDigit())
                    .padding(.horizontal, 5)
                    .padding(.vertical, 1)
                    .background(Color.white.opacity(0.1))
                    .clipShape(Capsule())
            }
            .padding(.horizontal, 10)
            .padding(.vertical, 5)
            .background(
                viewModel.selectedStatus == status
                    ? (status?.color ?? AppTheme.textAccent).opacity(0.2)
                    : Color.clear
            )
            .foregroundStyle(
                viewModel.selectedStatus == status
                    ? (status?.color ?? AppTheme.textAccent)
                    : AppTheme.textSecondary
            )
            .clipShape(Capsule())
            .overlay(
                Capsule().stroke(AppTheme.cardBorder, lineWidth: 1)
            )
        }
        .buttonStyle(.plain)
    }

    private func formatDate(_ date: String) -> String {
        let formatter = DateFormatter()
        formatter.dateFormat = "yyyy-MM-dd"
        guard let d = formatter.date(from: date) else { return date }
        formatter.dateFormat = "MMM d"
        return formatter.string(from: d)
    }
}
