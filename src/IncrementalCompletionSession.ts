/*
 * Copyright (c) Mike Lischke. All rights reserved.
 * Licensed under the MIT License. See License.txt in the project root for license information.
 */

import {
    CommonToken, Interval, Parser, ParserRuleContext, Token, TokenSource,
} from "antlr4ng";

import {
    CandidatesCollection, CodeCompletionCore, FollowSetsPerState,
    IIncrementalCompletionDiagnostics, IIncrementalCompletionRunStats,
    IIncrementalCompletionSessionOptions, ITokenEdit, IncrementalInvalidationReason,
    PersistentRuleCache,
} from "./CodeCompletionCore.js";

class SessionTokenStream {
    private position = 0;

    public constructor(private readonly streamTokens: Token[], private readonly source: TokenSource) { }

    public get index(): number {
        return this.position;
    }

    public get size(): number {
        return this.streamTokens.length;
    }

    public get tokenSource(): TokenSource {
        return this.source;
    }

    public consume(): void {
        if (this.position < this.streamTokens.length - 1) {
            ++this.position;
        }
    }

    public LA(offset: number): number {
        return this.LT(offset)?.type ?? Token.EOF;
    }

    public LT(offset: number): Token | null {
        const index = this.position + offset - 1;

        return index >= 0 && index < this.streamTokens.length ? this.streamTokens[index]! : null;
    }

    public get(index: number): Token {
        return this.streamTokens[index]!;
    }

    public mark(): number {
        return this.position;
    }

    public release(_marker: number): void { }

    public seek(index: number): void {
        this.position = Math.max(0, Math.min(index, this.streamTokens.length - 1));
    }

    public reset(): void {
        this.position = 0;
    }

    public getSourceName(): string {
        return this.source.sourceName;
    }

    public getText(interval?: Interval): string {
        const start = interval?.start ?? 0;
        const stop = interval?.stop ?? this.streamTokens.length - 1;

        return this.streamTokens.slice(start, stop + 1).map((token) => { return token.text ?? ""; }).join("");
    }

    public getTextFromInterval(interval: Interval): string {
        return this.getText(interval);
    }

    public getTextFromContext(context: ParserRuleContext): string {
        if (!context.start) {
            return this.getText();
        }

        const stop = context.stop?.tokenIndex ?? context.start.tokenIndex;

        return this.getText(new Interval(context.start.tokenIndex, stop));
    }

    public getTextFromRange(start: Token | null, stop: Token | null): string {
        if (!start) {
            return this.getText();
        }

        return this.getText(new Interval(start.tokenIndex, stop?.tokenIndex ?? start.tokenIndex));
    }

    public setLine(_line: number): void { }
    public setColumn(_column: number): void { }
}

export class IncrementalCompletionSession {
    private readonly core: CodeCompletionCore;
    private readonly cachesByContext = new Map<string, PersistentRuleCache>();
    private readonly followSets: FollowSetsPerState = new Map();
    private tokens: Token[];
    private parser: Parser;
    private preferredRules: Set<number>;
    private ignoredTokens: Set<number>;
    private translateRulesTopDown: boolean;
    private predicateResultVersion: number | string;
    private maxCachedRuleInvocations: number;
    private tick = 0;
    private configurationSignature: string;

    private diagnosticsData: IIncrementalCompletionDiagnostics = {
        requests: 0,
        cachedRuleInvocations: 0,
        persistentPrefixHits: 0,
        shortcutHits: 0,
        recomputedStates: 0,
        evictedRuleInvocations: 0,
        invalidationEvents: this.emptyEventCounts(),
        invalidatedRuleInvocations: this.emptyEventCounts(),
        lastRun: {
            persistentPrefixHits: 0,
            shortcutHits: 0,
            recomputedStates: 0,
        },
    };

    public constructor(parser: Parser, initialTokens: Token[], options: IIncrementalCompletionSessionOptions = {}) {
        this.parser = parser;
        this.core = new CodeCompletionCore(parser);
        this.preferredRules = options.preferredRules ?? new Set();
        this.ignoredTokens = options.ignoredTokens ?? new Set();
        this.translateRulesTopDown = options.translateRulesTopDown ?? false;
        this.predicateResultVersion = options.predicateResultVersion ?? 0;
        this.maxCachedRuleInvocations = Math.max(0, options.maxCachedRuleInvocations ?? 4096);
        this.tokens = this.normalizeTokens(initialTokens);
        this.core.preferredRules = this.preferredRules;
        this.core.ignoredTokens = this.ignoredTokens;
        this.core.translateRulesTopDown = this.translateRulesTopDown;
        this.configurationSignature = this.currentConfigurationSignature();
    }

    public get currentTokens(): Token[] {
        return this.tokens.map((token) => { return CommonToken.fromToken(token); });
    }

    public get diagnostics(): IIncrementalCompletionDiagnostics {
        return {
            ...this.diagnosticsData,
            invalidationEvents: { ...this.diagnosticsData.invalidationEvents },
            invalidatedRuleInvocations: { ...this.diagnosticsData.invalidatedRuleInvocations },
            lastRun: { ...this.diagnosticsData.lastRun },
        };
    }

    public setParser(parser: Parser): void {
        if (parser === this.parser) {
            return;
        }

        const grammarChanged = parser.atn !== this.core.parserATN;
        this.parser = parser;
        this.core.setParserInstance(parser);
        this.invalidateAll(grammarChanged ? "grammar-changed" : "parser-replaced");
        if (grammarChanged) {
            this.followSets.clear();
        }
    }

    public setPredicateResultVersion(version: number | string): void {
        if (version !== this.predicateResultVersion) {
            this.predicateResultVersion = version;
            this.followSets.clear();
            this.invalidateAll("predicate-version-changed");
        }
    }

    public dispose(): void {
        this.invalidateAll("cleared");
        this.followSets.clear();
        this.tokens = [];
    }

    public collectCandidates(caretTokenIndex: number, context?: ParserRuleContext): CandidatesCollection {
        if (this.tokens.some((token, index) => { return token.tokenIndex !== index; })) {
            this.invalidateAll("token-index-renumbered");
            this.tokens = this.normalizeTokens(this.tokens);
        }

        if (this.parser !== this.core.parserInstance) {
            this.core.setParserInstance(this.parser);
        }

        const nextConfiguration = this.currentConfigurationSignature();
        if (nextConfiguration !== this.configurationSignature) {
            this.invalidateAll("configuration-changed");
            this.configurationSignature = nextConfiguration;
        }

        this.core.preferredRules = this.preferredRules;
        this.core.ignoredTokens = this.ignoredTokens;
        this.core.translateRulesTopDown = this.translateRulesTopDown;

        const contextKey = `${context?.ruleIndex ?? 0}:${context?.start?.tokenIndex ?? -1}`;
        let cache = this.cachesByContext.get(contextKey);
        if (!cache) {
            cache = new Map();
            this.cachesByContext.set(contextKey, cache);
        }

        const runStats: IIncrementalCompletionRunStats = {
            persistentPrefixHits: 0,
            shortcutHits: 0,
            recomputedStates: 0,
        };
        ++this.tick;
        const originalStream = this.parser.tokenStream;
        const stream = new SessionTokenStream(this.tokens, originalStream.tokenSource);
        this.parser.tokenStream = stream as unknown as typeof originalStream;

        let result: CandidatesCollection;
        try {
            result = this.core.collectCandidatesForSession(caretTokenIndex, context, {
                inputTokens: this.tokens,
                persistentCache: cache,
                followSets: this.followSets,
                predicateResultVersion: this.predicateResultVersion,
                accessTick: this.tick,
                stats: runStats,
            });
        } finally {
            this.parser.tokenStream = originalStream;
        }

        runStats.recomputedStates = this.core.processedStates;
        this.evict(cache);
        this.recordRun(runStats);

        return result;
    }

    public insertTokens(start: number, tokens: Token[]): IIncrementalCompletionDiagnostics {
        return this.applyEdit({ start, deleteCount: 0, tokens });
    }

    public deleteTokens(start: number, deleteCount: number): IIncrementalCompletionDiagnostics {
        return this.applyEdit({ start, deleteCount });
    }

    public replaceTokens(start: number, deleteCount: number, tokens: Token[]): IIncrementalCompletionDiagnostics {
        return this.applyEdit({ start, deleteCount, tokens });
    }

    public applyEdit(edit: ITokenEdit): IIncrementalCompletionDiagnostics {
        if (edit.start < 0 || edit.start > this.tokens.length) {
            throw new RangeError("Token edit start must be within the current token sequence.");
        }
        if (edit.deleteCount < 0 || edit.start + edit.deleteCount > this.tokens.length) {
            throw new RangeError("Token edit deletion must be within the current token sequence.");
        }

        const insertion = (edit.tokens ?? []).map((token) => { return CommonToken.fromToken(token); });
        const oldEnd = edit.start + edit.deleteCount;
        const touchesEof = this.tokens.slice(edit.start, oldEnd).some((token) => { return token.type === Token.EOF; })
            || insertion.some((token) => { return token.type === Token.EOF; });
        const before = this.tokens.slice(0, edit.start);
        const after = this.tokens.slice(oldEnd);
        const nextTokens = this.normalizeTokens([...before, ...insertion, ...after]);

        if (touchesEof) {
            this.invalidateAll("eof-changed");
        } else {
            this.invalidateInterval(nextTokens, edit.start, oldEnd);
        }

        this.tokens = nextTokens;

        return this.diagnostics;
    }

    private emptyEventCounts(): Record<IncrementalInvalidationReason, number> {
        return {
            "parser-replaced": 0,
            "grammar-changed": 0,
            "configuration-changed": 0,
            "context-changed": 0,
            "predicate-version-changed": 0,
            "token-sequence-changed": 0,
            "token-index-renumbered": 0,
            "edit-overlap": 0,
            "eof-changed": 0,
            "cache-limit": 0,
            "cleared": 0,
        };
    }

    private allCaches(): PersistentRuleCache[] {
        return [...this.cachesByContext.values()];
    }

    private invalidateAll(reason: IncrementalInvalidationReason): void {
        let count = 0;
        for (const cache of this.allCaches()) {
            for (const ruleCache of cache.values()) {
                count += ruleCache.size;
                ruleCache.clear();
            }
        }
        this.diagnosticsData.invalidationEvents[reason]++;
        this.diagnosticsData.invalidatedRuleInvocations[reason] += count;
    }

    private evict(activeCache: PersistentRuleCache): void {
        type EvictionEntry = {
            cache: PersistentRuleCache;
            ruleIndex: number;
            key: string;
            lastUsed: number;
        };

        let total = 0;
        const entries: EvictionEntry[] = [];
        for (const cache of this.allCaches()) {
            for (const [ruleIndex, ruleCache] of cache) {
                total += ruleCache.size;
                for (const [key, entry] of ruleCache) {
                    entries.push({ cache, ruleIndex, key, lastUsed: entry.lastUsed });
                }
            }
        }

        let evicted = 0;
        if (total > this.maxCachedRuleInvocations) {
            entries.sort((a, b) => { return a.lastUsed - b.lastUsed; });
            const removalCount = total - this.maxCachedRuleInvocations;
            for (const entry of entries.slice(0, removalCount)) {
                if (entry.cache.get(entry.ruleIndex)?.delete(entry.key)) {
                    ++evicted;
                }
            }
            this.diagnosticsData.invalidationEvents["cache-limit"]++;
            this.diagnosticsData.invalidatedRuleInvocations["cache-limit"] += evicted;
        }

        this.diagnosticsData.evictedRuleInvocations += evicted;
        this.diagnosticsData.cachedRuleInvocations = Math.max(0, total - evicted);
    }

    private recordRun(stats: IIncrementalCompletionRunStats): void {
        ++this.diagnosticsData.requests;
        this.diagnosticsData.persistentPrefixHits += stats.persistentPrefixHits;
        this.diagnosticsData.shortcutHits += stats.shortcutHits;
        this.diagnosticsData.recomputedStates += stats.recomputedStates;
        this.diagnosticsData.lastRun = { ...stats };
    }

    private normalizeTokens(input: Token[]): Token[] {
        const result = input
            .filter((token) => { return token.type !== Token.EOF; })
            .map((token) => { return CommonToken.fromToken(token); });
        const eof = CommonToken.fromType(Token.EOF, "");
        eof.channel = Token.DEFAULT_CHANNEL;
        result.push(eof);
        result.forEach((token, index) => { token.setTokenIndex(index); });

        return result;
    }

    private currentConfigurationSignature(): string {
        const preferred = [...this.preferredRules].sort((a, b) => { return a - b; }).join(",");
        const ignored = [...this.ignoredTokens].sort((a, b) => { return a - b; }).join(",");

        return `${preferred}|${ignored}|${this.translateRulesTopDown}`;
    }

    private invalidateInterval(nextTokens: Token[], oldStartRaw: number, oldEndRaw: number): void {
        const oldDefaults = this.defaultTokens(this.tokens);
        const newDefaults = this.defaultTokens(nextTokens);
        let oldStart = oldDefaults.findIndex((token) => { return token.rawIndex >= oldStartRaw; });
        let oldEnd = oldDefaults.findIndex((token) => { return token.rawIndex >= oldEndRaw; });
        if (oldEnd < 0) {
            oldEnd = oldDefaults.length;
        }
        if (oldStart < 0) {
            oldStart = oldEnd;
        }
        let newStart = newDefaults.findIndex((token) => { return token.rawIndex >= oldStartRaw; });
        if (newStart < 0) {
            newStart = newDefaults.length;
        }
        const newEnd = newStart;

        let prefix = 0;
        const prefixLimit = Math.min(oldStart, newStart);
        while (prefix < prefixLimit && oldDefaults[prefix]?.type === newDefaults[prefix]?.type) {
            ++prefix;
        }

        let suffix = 0;
        while (oldEnd + suffix < oldDefaults.length && newEnd + suffix < newDefaults.length &&
            oldDefaults[oldEnd + suffix]?.type === newDefaults[newEnd + suffix]?.type) {
            ++suffix;
        }

        const oldChangedStart = prefix;
        const oldChangedEnd = oldDefaults.length - suffix - 1;
        const hasChangedOldRange = oldChangedStart <= oldChangedEnd;
        const rawByNewOrdinal = new Map<number, number>();
        newDefaults.forEach((token, ordinal) => { rawByNewOrdinal.set(ordinal, token.rawIndex); });
        const oldRawToOrdinal = new Map<number, number>();
        oldDefaults.forEach((token, ordinal) => { oldRawToOrdinal.set(token.rawIndex, ordinal); });

        const mapOrdinal = (ordinal: number): number | undefined => {
            if (ordinal < prefix) {
                return rawByNewOrdinal.get(ordinal);
            }
            if (ordinal >= oldEnd + suffix) {
                return rawByNewOrdinal.get(ordinal - oldEnd + newEnd);
            }

            return undefined;
        };

        for (const cache of this.allCaches()) {
            for (const [ruleIndex, ruleCache] of cache) {
                for (const [key, entry] of ruleCache) {
                    const minOrdinal = oldRawToOrdinal.get(entry.dependencyMinAbsoluteIndex) ?? -1;
                    const maxOrdinal = oldRawToOrdinal.get(entry.dependencyMaxAbsoluteIndex) ?? -1;
                    const overlapsChangedDefault = hasChangedOldRange && minOrdinal <= oldChangedEnd &&
                        maxOrdinal >= oldChangedStart;
                    const predicateOverlapsEdit = entry.usesPredicate &&
                        minOrdinal <= oldEnd + suffix - 1 && maxOrdinal >= prefix;
                    if (overlapsChangedDefault || predicateOverlapsEdit) {
                        ruleCache.delete(key);
                        this.diagnosticsData.invalidationEvents.editOverlap++;
                        this.diagnosticsData.invalidatedRuleInvocations.editOverlap++;
                        continue;
                    }

                    const startOrdinal = oldRawToOrdinal.get(entry.startAbsoluteIndex);
                    const mappedStart = startOrdinal === undefined ? undefined : mapOrdinal(startOrdinal);
                    if (mappedStart === undefined) {
                        ruleCache.delete(key);
                        this.diagnosticsData.invalidationEvents.editOverlap++;
                        this.diagnosticsData.invalidatedRuleInvocations.editOverlap++;
                        continue;
                    }

                    entry.startAbsoluteIndex = mappedStart;
                    entry.dependencyMinAbsoluteIndex = mapOrdinal(minOrdinal) ?? mappedStart;
                    entry.dependencyMaxAbsoluteIndex = mapOrdinal(maxOrdinal) ?? mappedStart;
                    entry.endAbsoluteIndexes = new Set([...entry.endAbsoluteIndexes].map((rawIndex) => {
                        const ordinal = oldRawToOrdinal.get(rawIndex);

                        return ordinal === undefined ? undefined : mapOrdinal(ordinal);
                    }).filter((rawIndex): rawIndex is number => rawIndex !== undefined));
                    if (entry.endAbsoluteIndexes.size === 0) {
                        ruleCache.delete(key);
                        this.diagnosticsData.invalidationEvents.editOverlap++;
                        this.diagnosticsData.invalidatedRuleInvocations.editOverlap++;
                    }
                }

                if (ruleCache.size === 0) {
                    cache.delete(ruleIndex);
                }
            }
        }
    }

    private defaultTokens(tokens: Token[]): Array<{ rawIndex: number; type: number }> {
        return tokens
            .filter((token) => { return token.channel === Token.DEFAULT_CHANNEL; })
            .map((token) => {
                return { rawIndex: token.tokenIndex, type: token.type };
            });
    }

    private countDefaults(tokens: Token[]): number {
        return tokens.filter((token) => { return token.channel === Token.DEFAULT_CHANNEL; }).length;
    }
}
