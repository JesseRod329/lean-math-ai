import SwiftUI

struct LeanCodeView: View {
    let source: String

    var body: some View {
        ScrollView([.horizontal, .vertical]) {
            Text(highlightedSource)
                .font(.system(.body, design: .monospaced))
                .textSelection(.enabled)
                .padding(16)
        }
        .background(Color.black.opacity(0.4))
        .clipShape(RoundedRectangle(cornerRadius: 12))
        .overlay(
            RoundedRectangle(cornerRadius: 12)
                .stroke(AppTheme.cardBorder, lineWidth: 1)
        )
    }

    private var highlightedSource: AttributedString {
        var result = AttributedString(source)

        let keywords = [
            "import", "theorem", "lemma", "example", "def", "where",
            "by", "sorry", "trivial", "simp", "exact", "apply",
            "intro", "have", "let", "in", "if", "then", "else",
            "match", "with", "fun", "do", "return", "open", "namespace",
            "section", "end", "variable", "instance", "class", "structure",
            "inductive", "noncomputable", "private", "protected"
        ]

        let types = [
            "Prop", "Type", "Nat", "Int", "Bool", "True", "False",
            "Finset", "Set", "List", "Option", "String", "Float", "Unit"
        ]

        // Highlight keywords
        for keyword in keywords {
            var searchRange = result.startIndex..<result.endIndex
            while let range = result[searchRange].range(of: keyword, options: .init()) {
                let globalRange = range
                // Check word boundary
                let beforeOk = globalRange.lowerBound == result.startIndex ||
                    !result.characters[result.characters.index(before: globalRange.lowerBound)].isLetter
                let afterOk = globalRange.upperBound == result.endIndex ||
                    !result.characters[globalRange.upperBound].isLetter

                if beforeOk && afterOk {
                    if keyword == "sorry" {
                        result[globalRange].foregroundColor = NSColor(AppTheme.failed)
                        result[globalRange].font = .monospacedSystemFont(ofSize: 13, weight: .bold)
                    } else {
                        result[globalRange].foregroundColor = NSColor(red: 0.78, green: 0.56, blue: 1.0, alpha: 1.0)
                    }
                }

                if globalRange.upperBound < result.endIndex {
                    searchRange = globalRange.upperBound..<result.endIndex
                } else {
                    break
                }
            }
        }

        // Highlight types
        for typeName in types {
            var searchRange = result.startIndex..<result.endIndex
            while let range = result[searchRange].range(of: typeName, options: .init()) {
                let beforeOk = range.lowerBound == result.startIndex ||
                    !result.characters[result.characters.index(before: range.lowerBound)].isLetter
                let afterOk = range.upperBound == result.endIndex ||
                    !result.characters[range.upperBound].isLetter

                if beforeOk && afterOk {
                    result[range].foregroundColor = NSColor(AppTheme.textAccent)
                }

                if range.upperBound < result.endIndex {
                    searchRange = range.upperBound..<result.endIndex
                } else {
                    break
                }
            }
        }

        // Highlight line comments (--)
        let lines = source.split(separator: "\n", omittingEmptySubsequences: false)
        var offset = result.startIndex
        for line in lines {
            let lineStr = String(line)
            if let commentIdx = lineStr.range(of: "--") {
                let charOffset = lineStr.distance(from: lineStr.startIndex, to: commentIdx.lowerBound)
                let commentStart = result.index(offset, offsetByCharacters: charOffset)
                let lineEnd = result.index(offset, offsetByCharacters: lineStr.count)
                if commentStart < lineEnd {
                    result[commentStart..<lineEnd].foregroundColor = NSColor(
                        red: 0.5, green: 0.5, blue: 0.5, alpha: 0.8
                    )
                }
            }
            // Move offset past the line + newline
            let advance = lineStr.count + 1
            if let newOffset = Optional(result.index(offset, offsetByCharacters: advance)),
               newOffset <= result.endIndex {
                offset = newOffset
            } else {
                offset = result.endIndex
            }
        }

        return result
    }
}
