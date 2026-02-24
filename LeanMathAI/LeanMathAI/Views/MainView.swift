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

    var body: some View {
        NavigationSplitView {
            SidebarView(selection: $selectedItem)
        } detail: {
            ZStack {
                GradientBackground()
                detailView
            }
        }
        .navigationSplitViewStyle(.balanced)
        .onAppear(perform: initialLoad)
        .onAppear(perform: setupFileWatcher)
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

        fileWatcher.onChange = { [self] in
            // Debounced refresh
            DispatchQueue.main.asyncAfter(deadline: .now() + 1.0) {
                self.directoryService.scanAvailableDates()
                self.dashboardVM.refresh(from: self.directoryService)
                self.timelineVM.refresh(from: self.directoryService)
                // Reload current date for detail views
                self.papersVM.loadCurrentDate()
                self.theoremsVM.loadCurrentDate()
                self.proofsVM.loadCurrentDate()
            }
        }
    }
}
