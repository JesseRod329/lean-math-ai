import Foundation

struct PipelineConfig: Codable, Equatable {
    var arxiv: ArxivConfig
    var extraction: ExtractionConfig
    var formalization: FormalizationConfig
    var refinement: RefinementConfig
    var schedule: ScheduleConfig

    struct ArxivConfig: Codable, Equatable {
        var categories: [String]
        var daysBack: Int
        var maxResults: Int

        enum CodingKeys: String, CodingKey {
            case categories
            case daysBack = "days_back"
            case maxResults = "max_results"
        }
    }

    struct ExtractionConfig: Codable, Equatable {
        var model: String
        var maxCandidates: Int
        var maxPerPaper: Int

        enum CodingKeys: String, CodingKey {
            case model
            case maxCandidates = "max_candidates"
            case maxPerPaper = "max_per_paper"
        }
    }

    struct FormalizationConfig: Codable, Equatable {
        var backend: String
        var model: String
        var anthropicModel: String
        var openaiModel: String
        var attempts: Int
        var maxTokens: Int
        var temperature: Double
        var maxPerHour: Int

        enum CodingKeys: String, CodingKey {
            case backend, model, attempts, temperature
            case anthropicModel = "anthropic_model"
            case openaiModel = "openai_model"
            case maxTokens = "max_tokens"
            case maxPerHour = "max_per_hour"
        }
    }

    struct RefinementConfig: Codable, Equatable {
        var enabled: Bool
        var maxAttempts: Int
        var model: String

        enum CodingKeys: String, CodingKey {
            case enabled, model
            case maxAttempts = "max_attempts"
        }
    }

    struct ScheduleConfig: Codable, Equatable {
        var runIntervalMinutes: Int
        var autoRun: Bool

        enum CodingKeys: String, CodingKey {
            case runIntervalMinutes = "run_interval_minutes"
            case autoRun = "auto_run"
        }
    }

    static let `default` = PipelineConfig(
        arxiv: ArxivConfig(categories: ["math.NT", "math.CO"], daysBack: 1, maxResults: 50),
        extraction: ExtractionConfig(model: "mlx-community/DeepSeek-Coder-V2-Lite-Instruct-4bit", maxCandidates: 10, maxPerPaper: 3),
        formalization: FormalizationConfig(
            backend: "mlx",
            model: "mlx-community/DeepSeek-Coder-V2-Lite-Instruct-4bit",
            anthropicModel: "claude-sonnet-4-20250514",
            openaiModel: "gpt-4o",
            attempts: 3,
            maxTokens: 4096,
            temperature: 0.1,
            maxPerHour: 3
        ),
        refinement: RefinementConfig(enabled: true, maxAttempts: 3, model: "mlx-community/DeepSeek-Coder-V2-Lite-Instruct-4bit"),
        schedule: ScheduleConfig(runIntervalMinutes: 60, autoRun: false)
    )
}
