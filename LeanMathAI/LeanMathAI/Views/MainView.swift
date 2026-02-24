import SwiftUI

struct MainView: View {
    @Environment(DataDirectoryService.self) var directoryService
    @Environment(ConfigService.self) var configService
    @State private var selectedItem: SidebarItem = .dashboard
    @State private var fileWatcher = FileWatcherService()

    // ViewModels
    @State private var dashboardVM = DashboardViewModel()
    @State private var papersVM = PapersViewModel()
    @State private var theoremsVM = TheoremsViewModel()
    @State private var proofsVM = ProofsViewModel()
    @State private var timelineVM = TimelineViewModel()
    @State private var settingsVM = SettingsViewModel()
    @State private var pipelineService = PipelineService()
    @State private var refreshTask: Task<Void, Never>?

    var body: some View {
        NavigationSplitView {
            SidebarView(
                selection: $selectedItem,
                proofCount: dashboardVM.totalFormalized + dashboardVM.totalProven,
                paperCount: dashboardVM.pipelinePapers,
                provenCount: dashboardVM.totalProven,
                isRunning: pipelineService.isRunning
            )
        } detail: {
            ZStack {
                GradientBackground()
                detailView
            }
        }
        .navigationSplitViewStyle(.balanced)
        .onAppear(perform: initialLoad)
        .onAppear(perform: setupFileWatcher)
        .onReceive(NotificationCenter.default.publisher(for: .navigateTo)) { notification in
            if let item = notification.object as? SidebarItem {
                selectedItem = item
            }
        }
    }

    @ViewBuilder
    private var detailView: some View {
        switch selectedItem {
        case .dashboard:
            DashboardView(viewModel: dashboardVM, pipeline: pipelineService)
        case .papers:
            PapersListView(viewModel: papersVM)
        case .theorems:
            TheoremsListView(viewModel: theoremsVM)
        case .proofs:
            ProofsListView(viewModel: proofsVM)
        case .timeline:
            TimelineView(viewModel: timelineVM)
        case .settings:
            SettingsView(viewModel: settingsVM)
        }
    }

    private func initialLoad() {
        dashboardVM.refresh(from: directoryService)
        papersVM.setup(from: directoryService)
        theoremsVM.setup(from: directoryService)
        proofsVM.setup(from: directoryService)
        timelineVM.refresh(from: directoryService)
        settingsVM.refresh(from: directoryService)
        if let baseDir = directoryService.baseDirectory {
            configService.configure(baseDirectory: baseDir)
            pipelineService.configure(baseDirectory: baseDir, configService: configService)
            if configService.config.schedule.autoRun {
                pipelineService.startAutoRunTimer()
            }
        }
    }

    private func setupFileWatcher() {
        // Watch key directories for changes
        if let completedDir = directoryService.completedProofsDirectory {
            fileWatcher.watch(directory: completedDir)
        }
        if let failedDir = directoryService.failedAttemptsDirectory {
            fileWatcher.watch(directory: failedDir)
        }
        if let dashboardDir = directoryService.dashboardDataDirectory {
            fileWatcher.watch(directory: dashboardDir)
        }

        fileWatcher.onChange = {
            refreshTask?.cancel()
            refreshTask = Task { @MainActor in
                try? await Task.sleep(for: .seconds(1))
                guard !Task.isCancelled else { return }
                directoryService.scanAvailableDates()
                dashboardVM.refresh(from: directoryService)
                timelineVM.refresh(from: directoryService)
                papersVM.loadCurrentDate()
                theoremsVM.loadCurrentDate()
                proofsVM.loadCurrentDate()
            }
        }
    }
}
