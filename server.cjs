const express = require('express');
const http = require('http');
const socketIo = require('socket.io');
const fs = require('fs').promises;
const fsSync = require('fs');
const path = require('path');
const axios = require('axios');
const WebSocket = require('ws');

// Configuration du serveur
const app = express();
const server = http.createServer(app);
const io = socketIo(server, {
    cors: {
        origin: "*",
        methods: ["GET", "POST"]
    }
});

// Middleware
app.use(express.json());
app.use(express.static('.'));

// Paramètres par défaut
const DEFAULT_AUTH_TOKEN = '70eb6339151ce50386c914434b5d0679a3ecc3689f54f5146891dae7a83814f6cc661e4127af348615d5dde04f297a31446359e96c4c8de817ec37ecb737953090659cc69f00e0fd9badacd28c8a67e15422e30dfb558da3fd78f4d9ff44b7fbc20d15bb185a8667b5636adef9c4273b70d542c4a69d0019a91915e050451e928f86d02132787a9827f309436b8916a5ed418de1691f070475babbbf.1c071e6410d9d5628a0157cd70b4eff4.077dee8d-c923-4c02-9bee-757573662e69';
const MAX_CACHE_SIZE = 1000;
const CONFIG_FILE = path.join(__dirname, 'server-config.json');

// Variables globales
let config = {
    "isPolling": false,
    "pollingFrequency": 10,
    "historySize": 10000,
    "customSizes": {
        "median": 50,
        "mean": 100
    },
    "users": {
        "admin": "password"
    },
    "ranges": [
        { "name": "Bas (<1.5)", "min": 1, "max": 1.5, "color": "#e74c3c", "limit": 500 },
        { "name": "Moyen (1.5-2.0)", "min": 1.5, "max": 2, "color": "#f39c12", "limit": 300 },
        { "name": "Élevé (≥2.0)", "min": 2, "max": null, "color": "#2ecc71", "limit": 200 }
    ],
    "medianHistory": [],
    "meanHistory": [],
    "authToken": DEFAULT_AUTH_TOKEN
};

let isPolling = false;
let pollingFrequency = 1000;
let historySize = 10000;
let customSizes = { median: 50, mean: 100 };
let crashHistory = [];
let users = { 'admin': 'password' };
let authToken = DEFAULT_AUTH_TOKEN;

// Historiques des médianes et moyennes
let medianHistory = [];
let meanHistory = [];

// Variables WebSocket
let wsConnection = null;
let pingInterval = null;
let dataSenderInterval = null;
let currentToken = null;
let tokenExpireTime = null;
let tokenRefreshInterval = null;
const WEBSOCKET_BASE_URL = "wss://crash-gateway-grm-cr.100hp.app/websocket/lifecycle";
const TOKEN_REFRESH_URL = "https://crash-gateway-grm-cr.100hp.app/user/token";
const USER_AUTH_URL = "https://crash-gateway-grm-cr.100hp.app/user/auth";
const BALANCE_URL = "https://crash-gateway-grm-cr.100hp.app/user/balance";
const BET_PLACE_URL = "https://crash-gateway-grm-cr.100hp.app/bets/place";

// Informations utilisateur
let userInfo = {
    userId: null,
    userName: "Utilisateur",
    sessionId: "194dd3f3-b267-4f1b-9856-15bb0db1e9b2",
    customerId: "077dee8d-c923-4c02-9bee-757573662e69",
    balance: 0
};

// Coefficient en cours
let currentCoefficient = null;

let currentRanges = [
    { "name": "Bas (<1.5)", "min": 1, "max": 1.5, "color": "#e74c3c", "limit": 500 },
    { "name": "Moyen (1.5-2.0)", "min": 1.5, "max": 2, "color": "#f39c12", "limit": 300 },
    { "name": "Élevé (≥2.0)", "min": 2, "max": null, "color": "#2ecc71", "limit": 200 }
];

// Variables pour le calcul des pourcentages par plage
let rangePercentageHistory = new Map();

// 🆕 NOUVEAU SYSTÈME DE CLASSEMENT DES POURCENTAGES
let percentageRankingHistory = new Map(); // Stockage du classement par range
let percentageFrequencyAnalysis = new Map(); // Analyse des fréquences par range

// 🎯 NOUVEAU SYSTÈME PRÉDICTIF COMPLET
let rankingEvolutionHistory = new Map();      // Historique des évolutions de classement
let rankTransitionMatrices = new Map();       // Matrices de transition entre rangs
let momentumAnalysis = new Map();             // Analyse du momentum des rangs
let competitiveZonesAnalysis = new Map();     // Zones de bataille concurrentielle
let predictionModels = new Map();             // Modèles prédictifs par range
let temporalPatterns = new Map();             // Patterns temporels et cycles
let chainReactionTracking = new Map();        // Suivi des effets domino

// Variables pour l'envoi de données
let pendingValues = [];
let dataSendActive = false;

// Contrôle de redémarrage automatique
let autoRestartEnabled = true;
let restartTimeout = null;

// Variables pour l'analyse des pics et creux
let picsCreuxAnalysis = new Map(); // Stockage par range
let globalTrendAnalysis = {};

// Variables pour l'analyse des chutes et montées progressives
let chutesMonteeAnalysis = new Map(); // Stockage par range
let globalChuteMonteeTrendAnalysis = {};

// Variables pour l'analyse des pics et creux légers
let picsCreuxLegersAnalysis = new Map(); // Stockage par range
let globalPicsCreuxLegersTrendAnalysis = {};

// Variables pour l'analyse des plateaux
let plateauxAnalysis = new Map(); // Stockage par range
let globalPlateauxTrendAnalysis = {};

// 🌡️ SYSTÈME DE THERMOMÈTRE CORRIGÉ AVEC STABILITÉ : Variables pour le thermomètre de situation
let thermometrePointsHistory = new Map(); // Stockage des points par range avec identifiants

// 🎯 SYSTÈME PRÉDICTIF PRINCIPAL

/**
 * 📊 Initialise le système prédictif pour une range
 */
function initializePredictiveSystem(rangeName) {
    if (!rankingEvolutionHistory.has(rangeName)) {
        rankingEvolutionHistory.set(rangeName, {
            rounds: [],                    // Historique des rounds avec classements
            currentRound: 0,
            rankHistory: new Map(),        // Historique par pourcentage
            lastRankingSnapshot: null
        });
    }
    
    if (!rankTransitionMatrices.has(rangeName)) {
        rankTransitionMatrices.set(rangeName, {
            transitions: new Map(),        // rank_from -> rank_to -> count
            probabilities: new Map(),      // rank_from -> rank_to -> probability
            stabilityScores: new Map(),    // rank -> stability_score
            lastUpdate: Date.now()
        });
    }
    
    if (!momentumAnalysis.has(rangeName)) {
        momentumAnalysis.set(rangeName, {
            currentMomentum: new Map(),    // percentage -> momentum_data
            velocities: new Map(),         // percentage -> velocity
            accelerations: new Map(),      // percentage -> acceleration
            projections: new Map(),        // percentage -> projected_rank
            lastUpdate: Date.now()
        });
    }
    
    if (!competitiveZonesAnalysis.has(rangeName)) {
        competitiveZonesAnalysis.set(rangeName, {
            battleClusters: [],           // Groupes en compétition
            noMansLand: [],              // Zones peu disputées
            bottlenecks: [],             // Rangs difficiles à franchir
            dominanceIndex: 0,           // Index de domination
            lastUpdate: Date.now()
        });
    }
    
    if (!temporalPatterns.has(rangeName)) {
        temporalPatterns.set(rangeName, {
            cycles: [],                   // Cycles détectés
            currentPhase: "unknown",      // Phase actuelle
            leadershipRotation: [],       // Rotation des leaders
            activityLevel: "normal",      // Niveau d'activité
            nextPhaseProjection: null,    // Projection prochaine phase
            lastUpdate: Date.now()
        });
    }
    
    if (!predictionModels.has(rangeName)) {
        predictionModels.set(rangeName, {
            nextCrashProbability: 0,      // Probabilité pour le prochain crash
            confidence: "unknown",        // Niveau de confiance
            reasoning: [],                // Raisons de la prédiction
            modelReliability: 0,          // Fiabilité du modèle
            historicalAccuracy: 0,        // Précision historique
            lastPrediction: null,
            lastUpdate: Date.now()
        });
    }
}

/**
 * 🎯 Capture et analyse l'évolution du classement
 */
function captureRankingEvolution(rangeName) {
    const frequencyData = percentageFrequencyAnalysis.get(rangeName);
    if (!frequencyData || !frequencyData.classementDetaille) return;
    
    initializePredictiveSystem(rangeName);
    
    const evolutionData = rankingEvolutionHistory.get(rangeName);
    const currentClassement = frequencyData.classementDetaille.slice(0, 20); // Top 20
    
    // Créer snapshot du round actuel
    const roundSnapshot = {
        round: evolutionData.currentRound,
        timestamp: Date.now(),
        ranking: currentClassement.map(item => ({
            percentage: item.percentage,
            rank: item.rank,
            frequency: item.frequency,
            occurrencePercentage: item.occurrencePercentage
        }))
    };
    
    // Analyser les changements si on a un snapshot précédent
    if (evolutionData.lastRankingSnapshot) {
        analyzeRankingChanges(rangeName, evolutionData.lastRankingSnapshot, roundSnapshot);
    }
    
    // Sauvegarder le snapshot
    evolutionData.rounds.push(roundSnapshot);
    evolutionData.lastRankingSnapshot = roundSnapshot;
    evolutionData.currentRound++;
    
    // Maintenir historique limité
    if (evolutionData.rounds.length > 20) {
        evolutionData.rounds = evolutionData.rounds.slice(-20);
    }
    
    // Mettre à jour les analyses
    updateRankTransitionAnalysis(rangeName);
    updateMomentumAnalysis(rangeName);
    updateCompetitiveZonesAnalysis(rangeName);
    updateTemporalPatterns(rangeName);
    
    // Générer prédiction finale
    generateRangePrediction(rangeName);
}

/**
 * 🔍 Analyse les changements entre deux snapshots de classement
 */
function analyzeRankingChanges(rangeName, previousSnapshot, currentSnapshot) {
    const evolutionData = rankingEvolutionHistory.get(rangeName);
    
    // Créer maps pour faciliter les comparaisons
    const prevMap = new Map();
    const currentMap = new Map();
    
    previousSnapshot.ranking.forEach(item => {
        prevMap.set(item.percentage, item.rank);
    });
    
    currentSnapshot.ranking.forEach(item => {
        currentMap.set(item.percentage, item.rank);
    });
    
    // Analyser chaque pourcentage
    currentMap.forEach((currentRank, percentage) => {
        const previousRank = prevMap.get(percentage);
        
        if (previousRank !== undefined) {
            const rankChange = previousRank - currentRank; // Positif = montée
            
            // Mettre à jour l'historique de ce pourcentage
            if (!evolutionData.rankHistory.has(percentage)) {
                evolutionData.rankHistory.set(percentage, []);
            }
            
            const history = evolutionData.rankHistory.get(percentage);
            history.push({
                round: currentSnapshot.round,
                rank: currentRank,
                previousRank: previousRank,
                change: rankChange,
                timestamp: currentSnapshot.timestamp
            });
            
            // Maintenir historique limité
            if (history.length > 20) {
                evolutionData.rankHistory.set(percentage, history.slice(-20));
            }
        }
    });
}

/**
 * 📈 Met à jour l'analyse des transitions de rangs
 */
function updateRankTransitionAnalysis(rangeName) {
    const evolutionData = rankingEvolutionHistory.get(rangeName);
    const transitionData = rankTransitionMatrices.get(rangeName);
    
    if (evolutionData.rounds.length < 2) return;
    
    const currentRound = evolutionData.rounds[evolutionData.rounds.length - 1];
    const previousRound = evolutionData.rounds[evolutionData.rounds.length - 2];
    
    // Construire matrice de transitions
    const prevMap = new Map(previousRound.ranking.map(item => [item.percentage, item.rank]));
    const currentMap = new Map(currentRound.ranking.map(item => [item.percentage, item.rank]));
    
    currentMap.forEach((currentRank, percentage) => {
        const previousRank = prevMap.get(percentage);
        if (previousRank !== undefined) {
            const transitionKey = `${previousRank}_to_${currentRank}`;
            
            if (!transitionData.transitions.has(transitionKey)) {
                transitionData.transitions.set(transitionKey, 0);
            }
            
            transitionData.transitions.set(transitionKey, 
                transitionData.transitions.get(transitionKey) + 1);
        }
    });
    
    // Calculer probabilités de transition
    calculateTransitionProbabilities(rangeName);
    
    // Calculer scores de stabilité par rang
    calculateRankStabilityScores(rangeName);
}

/**
 * 📊 Calcule les probabilités de transition entre rangs
 */
function calculateTransitionProbabilities(rangeName) {
    const transitionData = rankTransitionMatrices.get(rangeName);
    const transitions = transitionData.transitions;
    
    // Grouper par rang d'origine
    const fromRankTotals = new Map();
    
    transitions.forEach((count, transitionKey) => {
        const fromRank = parseInt(transitionKey.split('_to_')[0]);
        
        if (!fromRankTotals.has(fromRank)) {
            fromRankTotals.set(fromRank, 0);
        }
        
        fromRankTotals.set(fromRank, fromRankTotals.get(fromRank) + count);
    });
    
    // Calculer probabilités
    transitions.forEach((count, transitionKey) => {
        const fromRank = parseInt(transitionKey.split('_to_')[0]);
        const total = fromRankTotals.get(fromRank);
        
        if (total > 0) {
            const probability = count / total;
            transitionData.probabilities.set(transitionKey, probability);
        }
    });
}

/**
 * 🎯 Calcule les scores de stabilité par rang
 */
function calculateRankStabilityScores(rangeName) {
    const transitionData = rankTransitionMatrices.get(rangeName);
    const probabilities = transitionData.probabilities;
    
    // Pour chaque rang, calculer la probabilité de rester au même rang
    for (let rank = 1; rank <= 20; rank++) {
        const stayKey = `${rank}_to_${rank}`;
        const stayProbability = probabilities.get(stayKey) || 0;
        
        transitionData.stabilityScores.set(rank, stayProbability);
    }
}

/**
 * ⚡ Met à jour l'analyse du momentum
 */
function updateMomentumAnalysis(rangeName) {
    const evolutionData = rankingEvolutionHistory.get(rangeName);
    const momentumData = momentumAnalysis.get(rangeName);
    
    if (evolutionData.rounds.length < 3) return;
    
    const recentRounds = evolutionData.rounds.slice(-5); // 5 derniers rounds
    
    // Analyser chaque pourcentage actif
    const currentRanking = recentRounds[recentRounds.length - 1].ranking;
    
    currentRanking.forEach(currentItem => {
        const percentage = currentItem.percentage;
        const rankHistoryForPercentage = [];
        
        // Collecter l'historique des rangs pour ce pourcentage
        recentRounds.forEach(round => {
            const item = round.ranking.find(r => r.percentage === percentage);
            if (item) {
                rankHistoryForPercentage.push({
                    round: round.round,
                    rank: item.rank,
                    timestamp: round.timestamp
                });
            }
        });
        
        if (rankHistoryForPercentage.length >= 3) {
            // Calculer vélocité (changement moyen par round)
            const rankChanges = [];
            for (let i = 1; i < rankHistoryForPercentage.length; i++) {
                const change = rankHistoryForPercentage[i-1].rank - rankHistoryForPercentage[i].rank; // Positif = montée
                rankChanges.push(change);
            }
            
            const velocity = rankChanges.reduce((sum, change) => sum + change, 0) / rankChanges.length;
            
            // Calculer accélération (changement de vélocité)
            let acceleration = 0;
            if (rankChanges.length >= 2) {
                const recentVelocity = (rankChanges[rankChanges.length - 1] + rankChanges[rankChanges.length - 2]) / 2;
                const olderVelocity = rankChanges.length >= 4 ? 
                    (rankChanges[0] + rankChanges[1]) / 2 : rankChanges[0];
                acceleration = recentVelocity - olderVelocity;
            }
            
            // Projeter rang futur
            const currentRank = currentItem.rank;
            const projectedRank = Math.max(1, Math.min(20, currentRank - (velocity * 3))); // Projection 3 rounds
            
            // Déterminer type de momentum
            let momentumType = "stable";
            if (velocity > 1) momentumType = "forte_montée";
            else if (velocity > 0.3) momentumType = "montée";
            else if (velocity < -1) momentumType = "forte_chute";
            else if (velocity < -0.3) momentumType = "chute";
            
            // Sauvegarder données
            momentumData.currentMomentum.set(percentage, {
                velocity: parseFloat(velocity.toFixed(2)),
                acceleration: parseFloat(acceleration.toFixed(2)),
                momentumType: momentumType,
                projectedRank: Math.round(projectedRank),
                confidence: Math.min(1, rankHistoryForPercentage.length / 5),
                timeAtCurrentRank: calculateTimeAtRank(rankHistoryForPercentage, currentRank)
            });
            
            momentumData.velocities.set(percentage, velocity);
            momentumData.accelerations.set(percentage, acceleration);
            momentumData.projections.set(percentage, projectedRank);
        }
    });
    
    momentumData.lastUpdate = Date.now();
}

/**
 * 🕐 Calcule le temps passé au rang actuel
 */
function calculateTimeAtRank(rankHistory, currentRank) {
    let timeAtRank = 0;
    
    for (let i = rankHistory.length - 1; i >= 0; i--) {
        if (rankHistory[i].rank === currentRank) {
            timeAtRank++;
        } else {
            break;
        }
    }
    
    return timeAtRank;
}

/**
 * ⚔️ Met à jour l'analyse des zones concurrentielles
 */
function updateCompetitiveZonesAnalysis(rangeName) {
    const momentumData = momentumAnalysis.get(rangeName);
    const competitiveData = competitiveZonesAnalysis.get(rangeName);
    const evolutionData = rankingEvolutionHistory.get(rangeName);
    
    if (evolutionData.rounds.length === 0) return;
    
    const currentRanking = evolutionData.rounds[evolutionData.rounds.length - 1].ranking;
    
    // Identifier les clusters de bataille (groupes de rangs serrés)
    const battleClusters = [];
    const rankGroups = new Map();
    
    currentRanking.forEach(item => {
        const rank = item.rank;
        const group = Math.floor((rank - 1) / 3) + 1; // Groupes de 3 rangs
        
        if (!rankGroups.has(group)) {
            rankGroups.set(group, []);
        }
        
        rankGroups.get(group).push({
            percentage: item.percentage,
            rank: rank,
            frequency: item.frequency,
            momentum: momentumData.currentMomentum.get(item.percentage)
        });
    });
    
    // Analyser chaque groupe pour détecter les batailles
    rankGroups.forEach((items, groupId) => {
        if (items.length >= 2) {
            const frequencies = items.map(i => i.frequency);
            const maxFreq = Math.max(...frequencies);
            const minFreq = Math.min(...frequencies);
            const frequencyGap = maxFreq - minFreq;
            
            // C'est une zone de bataille si l'écart est faible
            if (frequencyGap <= 5) {
                const rankRange = `${Math.min(...items.map(i => i.rank))}-${Math.max(...items.map(i => i.rank))}`;
                
                // Calculer intensité de bataille
                let battleIntensity = "faible";
                if (frequencyGap <= 2) battleIntensity = "très_élevée";
                else if (frequencyGap <= 3) battleIntensity = "élevée";
                else if (frequencyGap <= 4) battleIntensity = "moyenne";
                
                battleClusters.push({
                    rankRange: rankRange,
                    competitors: items.map(i => `${i.percentage}%`),
                    frequencyGap: frequencyGap,
                    battleIntensity: battleIntensity,
                    dominanceIndex: minFreq / maxFreq,
                    nextShakeupProbability: calculateShakeupProbability(items)
                });
            }
        }
    });
    
    // Identifier les zones "no man's land" (peu disputées)
    const noMansLand = [];
    for (let rank = 1; rank <= 20; rank++) {
        const inBattle = battleClusters.some(cluster => {
            const [start, end] = cluster.rankRange.split('-').map(Number);
            return rank >= start && rank <= end;
        });
        
        if (!inBattle) {
            noMansLand.push({
                rank: rank,
                stability: "haute",
                explanation: "Zone peu disputée, changements rares"
            });
        }
    }
    
    // Identifier les goulots d'étranglement
    const bottlenecks = identifyBottlenecks(rangeName);
    
    // Calculer index de domination global
    const dominanceIndex = calculateDominanceIndex(currentRanking);
    
    // Sauvegarder
    competitiveData.battleClusters = battleClusters;
    competitiveData.noMansLand = noMansLand;
    competitiveData.bottlenecks = bottlenecks;
    competitiveData.dominanceIndex = dominanceIndex;
    competitiveData.lastUpdate = Date.now();
}

/**
 * 🎲 Calcule la probabilité de bouleversement d'un cluster
 */
function calculateShakeupProbability(items) {
    let totalMomentum = 0;
    let momentumCount = 0;
    
    items.forEach(item => {
        if (item.momentum && item.momentum.velocity !== undefined) {
            totalMomentum += Math.abs(item.momentum.velocity);
            momentumCount++;
        }
    });
    
    if (momentumCount === 0) return 0.1;
    
    const averageMomentum = totalMomentum / momentumCount;
    return Math.min(0.95, Math.max(0.05, averageMomentum / 2));
}

/**
 * 🚧 Identifie les goulots d'étranglement
 */
function identifyBottlenecks(rangeName) {
    const transitionData = rankTransitionMatrices.get(rangeName);
    const bottlenecks = [];
    
    // Analyser les rangs difficiles à franchir
    for (let rank = 2; rank <= 10; rank++) {
        const upwardKey = `${rank}_to_${rank-1}`;
        const downwardKey = `${rank-1}_to_${rank}`;
        
        const upwardProb = transitionData.probabilities.get(upwardKey) || 0;
        const downwardProb = transitionData.probabilities.get(downwardKey) || 0;
        
        // C'est un goulot si très difficile de monter
        if (upwardProb < 0.15 && downwardProb > 0.3) {
            bottlenecks.push({
                rank: rank - 1,
                explanation: "Rang difficile à franchir - seuil critique",
                crossingProbability: upwardProb
            });
        }
    }
    
    return bottlenecks;
}

/**
 * 👑 Calcule l'index de domination global
 */
function calculateDominanceIndex(ranking) {
    if (ranking.length < 2) return 0;
    
    const first = ranking[0];
    const second = ranking[1];
    
    return second.frequency / first.frequency;
}

/**
 * 🔄 Met à jour les patterns temporels
 */
function updateTemporalPatterns(rangeName) {
    const evolutionData = rankingEvolutionHistory.get(rangeName);
    const temporalData = temporalPatterns.get(rangeName);
    
    if (evolutionData.rounds.length < 5) return;
    
    const recentRounds = evolutionData.rounds.slice(-10);
    
    // Analyser la rotation du leadership
    const leaders = recentRounds.map(round => 
        round.ranking.length > 0 ? round.ranking[0].percentage : null
    ).filter(leader => leader !== null);
    
    // Détecter cycles de leadership
    const leadershipCycles = detectLeadershipCycles(leaders);
    
    // Analyser niveau d'activité
    const activityLevel = calculateActivityLevel(recentRounds);
    
    // Déterminer phase actuelle
    const currentPhase = determineCurrentPhase(recentRounds, activityLevel);
    
    // Projeter prochaine phase
    const nextPhaseProjection = projectNextPhase(currentPhase, leadershipCycles);
    
    // Sauvegarder
    temporalData.leadershipRotation = leadershipCycles;
    temporalData.activityLevel = activityLevel;
    temporalData.currentPhase = currentPhase;
    temporalData.nextPhaseProjection = nextPhaseProjection;
    temporalData.lastUpdate = Date.now();
}

/**
 * 👑 Détecte les cycles de leadership
 */
function detectLeadershipCycles(leaders) {
    const cycles = [];
    const leaderCounts = new Map();
    
    leaders.forEach(leader => {
        leaderCounts.set(leader, (leaderCounts.get(leader) || 0) + 1);
    });
    
    const sortedLeaders = Array.from(leaderCounts.entries())
        .sort((a, b) => b[1] - a[1]);
    
    if (sortedLeaders.length > 0) {
        cycles.push({
            pattern: sortedLeaders.map(([leader, count]) => leader).join('→'),
            dominantLeader: sortedLeaders[0][0],
            leadershipDuration: sortedLeaders[0][1],
            rotationFrequency: leaders.length / leaderCounts.size
        });
    }
    
    return cycles;
}

/**
 * 📊 Calcule le niveau d'activité
 */
function calculateActivityLevel(rounds) {
    if (rounds.length < 2) return "unknown";
    
    let totalChanges = 0;
    let comparisonCount = 0;
    
    for (let i = 1; i < rounds.length; i++) {
        const prevRanking = rounds[i-1].ranking;
        const currentRanking = rounds[i].ranking;
        
        const prevMap = new Map(prevRanking.map(item => [item.percentage, item.rank]));
        
        currentRanking.forEach(item => {
            const prevRank = prevMap.get(item.percentage);
            if (prevRank !== undefined && prevRank !== item.rank) {
                totalChanges++;
            }
            comparisonCount++;
        });
    }
    
    if (comparisonCount === 0) return "unknown";
    
    const changeRate = totalChanges / comparisonCount;
    
    if (changeRate > 0.3) return "très_agité";
    else if (changeRate > 0.2) return "agité";
    else if (changeRate > 0.1) return "modéré";
    else return "calme";
}

/**
 * 🎭 Détermine la phase actuelle
 */
function determineCurrentPhase(rounds, activityLevel) {
    const recentActivity = rounds.slice(-3);
    
    if (activityLevel === "très_agité" || activityLevel === "agité") {
        return "période_agitée";
    } else if (activityLevel === "calme") {
        return "période_calme";
    } else {
        return "période_transitoire";
    }
}

/**
 * 🔮 Projette la prochaine phase
 */
function projectNextPhase(currentPhase, cycles) {
    const projections = {
        "période_agitée": {
            next: "période_transitoire",
            timeframe: "dans_2-4_rounds",
            probability: 0.7
        },
        "période_calme": {
            next: "période_transitoire",
            timeframe: "dans_3-5_rounds",
            probability: 0.6
        },
        "période_transitoire": {
            next: "période_agitée",
            timeframe: "dans_1-3_rounds",
            probability: 0.8
        }
    };
    
    return projections[currentPhase] || {
        next: "unknown",
        timeframe: "incertain",
        probability: 0.5
    };
}

/**
 * 🎯 FONCTION PRINCIPALE - Génère la prédiction finale pour une range
 */
function generateRangePrediction(rangeName) {
    const predictionData = predictionModels.get(rangeName);
    const momentumData = momentumAnalysis.get(rangeName);
    const competitiveData = competitiveZonesAnalysis.get(rangeName);
    const temporalData = temporalPatterns.get(rangeName);
    const evolutionData = rankingEvolutionHistory.get(rangeName);
    
    if (!predictionData || !evolutionData.rounds.length) return;
    
    const currentRanking = evolutionData.rounds[evolutionData.rounds.length - 1].ranking;
    if (currentRanking.length === 0) return;
    
    // Facteurs pour calculer la probabilité
    const factors = {
        currentDominance: 0,      // Position actuelle dans le classement
        momentum: 0,              // Momentum positif/négatif
        stability: 0,             // Stabilité du leader
        competition: 0,           // Niveau de compétition
        temporalCycle: 0,         // Phase du cycle temporel
        historicalPattern: 0      // Patterns historiques
    };
    
    // 1. Facteur de dominance actuelle (40% du poids)
    const leader = currentRanking[0];
    const totalOccurrences = currentRanking.reduce((sum, item) => sum + item.frequency, 0);
    factors.currentDominance = totalOccurrences > 0 ? (leader.frequency / totalOccurrences) * 0.4 : 0;
    
    // 2. Facteur momentum (25% du poids)
    const leaderMomentum = momentumData.currentMomentum.get(leader.percentage);
    if (leaderMomentum) {
        let momentumScore = 0;
        if (leaderMomentum.momentumType === "forte_montée") momentumScore = 1;
        else if (leaderMomentum.momentumType === "montée") momentumScore = 0.7;
        else if (leaderMomentum.momentumType === "stable") momentumScore = 0.5;
        else if (leaderMomentum.momentumType === "chute") momentumScore = 0.3;
        else if (leaderMomentum.momentumType === "forte_chute") momentumScore = 0.1;
        
        factors.momentum = momentumScore * 0.25;
    }
    
    // 3. Facteur stabilité (15% du poids)
    const transitionData = rankTransitionMatrices.get(rangeName);
    const stabilityScore = transitionData.stabilityScores.get(1) || 0.5; // Stabilité du rang #1
    factors.stability = stabilityScore * 0.15;
    
    // 4. Facteur compétition (10% du poids)
    const topBattleClusters = competitiveData.battleClusters.filter(cluster => 
        cluster.rankRange.includes('1') || cluster.rankRange.includes('2') || cluster.rankRange.includes('3')
    );
    const competitionLevel = topBattleClusters.length > 0 ? 
        (1 - topBattleClusters[0].dominanceIndex) * 0.1 : 0.05;
    factors.competition = competitionLevel;
    
    // 5. Facteur cycle temporel (5% du poids)
    let temporalScore = 0.5;
    if (temporalData.currentPhase === "période_calme") temporalScore = 0.7;
    else if (temporalData.currentPhase === "période_agitée") temporalScore = 0.3;
    factors.temporalCycle = temporalScore * 0.05;
    
    // 6. Facteur pattern historique (5% du poids)
    factors.historicalPattern = calculateHistoricalPatternScore(rangeName) * 0.05;
    
    // Calculer probabilité finale
    const totalProbability = Object.values(factors).reduce((sum, factor) => sum + factor, 0);
    const finalProbability = Math.min(95, Math.max(5, totalProbability * 100));
    
    // Déterminer niveau de confiance
    let confidence = "faible";
    const dataQuality = Math.min(1, evolutionData.rounds.length / 10);
    if (finalProbability > 70 && dataQuality > 0.8) confidence = "élevée";
    else if (finalProbability > 50 && dataQuality > 0.6) confidence = "moyenne";
    
    // Générer raisons
    const reasoning = generateReasoningForPrediction(factors, leaderMomentum, competitiveData, temporalData);
    
    // Calculer fiabilité du modèle
    const modelReliability = calculateModelReliability(evolutionData, dataQuality);
    
    // Sauvegarder prédiction
    predictionData.nextCrashProbability = parseFloat(finalProbability.toFixed(1));
    predictionData.confidence = confidence;
    predictionData.reasoning = reasoning;
    predictionData.modelReliability = parseFloat(modelReliability.toFixed(2));
    predictionData.lastPrediction = {
        timestamp: Date.now(),
        factors: factors,
        leader: leader
    };
    predictionData.lastUpdate = Date.now();
}

/**
 * 📈 Calcule le score des patterns historiques
 */
function calculateHistoricalPatternScore(rangeName) {
    const evolutionData = rankingEvolutionHistory.get(rangeName);
    
    if (evolutionData.rounds.length < 5) return 0.5;
    
    // Analyser la consistance du leader sur les derniers rounds
    const recentLeaders = evolutionData.rounds.slice(-5).map(round => 
        round.ranking.length > 0 ? round.ranking[0].percentage : null
    );
    
    const currentLeader = recentLeaders[recentLeaders.length - 1];
    const leaderConsistency = recentLeaders.filter(leader => leader === currentLeader).length / recentLeaders.length;
    
    return leaderConsistency;
}

/**
 * 💭 Génère les raisons de la prédiction
 */
function generateReasoningForPrediction(factors, leaderMomentum, competitiveData, temporalData) {
    const reasoning = [];
    
    // Dominance actuelle
    if (factors.currentDominance > 0.25) {
        reasoning.push("Position dominante dans le classement");
    } else if (factors.currentDominance < 0.15) {
        reasoning.push("Position faible dans le classement");
    }
    
    // Momentum
    if (leaderMomentum) {
        if (leaderMomentum.momentumType.includes("montée")) {
            reasoning.push(`Momentum ${leaderMomentum.momentumType.replace('_', ' ')} (+${Math.abs(leaderMomentum.velocity)} rangs/round)`);
        } else if (leaderMomentum.momentumType.includes("chute")) {
            reasoning.push(`Momentum ${leaderMomentum.momentumType.replace('_', ' ')} (${leaderMomentum.velocity} rangs/round)`);
        } else {
            reasoning.push("Momentum stable");
        }
    }
    
    // Compétition
    const topBattles = competitiveData.battleClusters.filter(cluster => 
        cluster.rankRange.includes('1') || cluster.rankRange.includes('2')
    );
    if (topBattles.length > 0) {
        reasoning.push(`Concurrence ${topBattles[0].battleIntensity.replace('_', ' ')} en tête de classement`);
    }
    
    // Phase temporelle
    if (temporalData.currentPhase) {
        reasoning.push(`Phase actuelle: ${temporalData.currentPhase.replace('_', ' ')}`);
    }
    
    return reasoning;
}

/**
 * 🎯 Calcule la fiabilité du modèle
 */
function calculateModelReliability(evolutionData, dataQuality) {
    // Fiabilité basée sur la quantité de données et la consistance
    const roundsCount = evolutionData.rounds.length;
    
    let reliability = dataQuality; // Base sur la qualité des données
    
    // Bonus pour historique long
    if (roundsCount >= 20) reliability += 0.1;
    else if (roundsCount >= 10) reliability += 0.05;
    
    // Malus si très peu de données
    if (roundsCount < 5) reliability *= 0.5;
    
    return Math.min(1, Math.max(0, reliability));
}

/**
 * 🎯 FONCTION PRINCIPALE - Génère la prédiction globale pour toutes les ranges
 */
function generateGlobalPrediction() {
    const predictions = [];
    let totalProbability = 0;
    
    currentRanges.forEach(range => {
        const predictionData = predictionModels.get(range.name);
        
        if (predictionData && predictionData.nextCrashProbability > 0) {
            predictions.push({
                rangeName: range.name,
                rangeColor: range.color,
                probability: predictionData.nextCrashProbability,
                confidence: predictionData.confidence,
                reasoning: predictionData.reasoning,
                modelReliability: predictionData.modelReliability
            });
            
            totalProbability += predictionData.nextCrashProbability;
        }
    });
    
    // Normaliser les probabilités pour qu'elles totalisent 100%
    if (totalProbability > 0) {
        predictions.forEach(pred => {
            pred.probability = parseFloat(((pred.probability / totalProbability) * 100).toFixed(1));
        });
    }
    
    // Trier par probabilité décroissante
    predictions.sort((a, b) => b.probability - a.probability);
    
    // Générer recommandation
    const mostLikely = predictions.length > 0 ? predictions[0] : null;
    
    const recommendation = mostLikely ? {
        mostLikely: mostLikely.rangeName,
        probability: mostLikely.probability,
        action: `MISER SUR PLAGE ${mostLikely.rangeName.toUpperCase()}`,
        riskLevel: mostLikely.probability > 60 ? "faible" : 
                   mostLikely.probability > 40 ? "moyen" : "élevé"
    } : null;
    
    // Calculer métriques globales
    const dominanceIndex = mostLikely ? mostLikely.probability / 100 : 0;
    const uncertainty = mostLikely ? 100 - mostLikely.probability : 100;
    
    // Évaluer fiabilité du modèle global
    const averageReliability = predictions.length > 0 ? 
        predictions.reduce((sum, p) => sum + p.modelReliability, 0) / predictions.length : 0;
    
    let modelReliability = "faible";
    if (averageReliability > 0.8) modelReliability = "haute";
    else if (averageReliability > 0.6) modelReliability = "moyenne";
    
    return {
        predictions: predictions,
        recommendation: recommendation,
        predictionMetrics: {
            totalCertainty: 100.0,
            dominanceIndex: parseFloat(dominanceIndex.toFixed(2)),
            uncertainty: parseFloat(uncertainty.toFixed(1)),
            modelReliability: modelReliability,
            averageReliability: parseFloat(averageReliability.toFixed(2))
        },
        timestamp: Date.now()
    };
}

// 🆕 NOUVEAU SYSTÈME DE CLASSEMENT ET ANALYSE DES FRÉQUENCES DES POURCENTAGES

/**
 * 📊 Initialise le système de classement pour une range
 */
function initializePercentageRanking(rangeName) {
    if (!percentageRankingHistory.has(rangeName)) {
        percentageRankingHistory.set(rangeName, {
            percentageGroups: new Map(), // Groupes de pourcentages similaires
            topPercentages: [], // Top des pourcentages les plus fréquents
            rarePecentages: [], // Pourcentages rares
            averageFrequency: 0,
            totalOccurrences: 0,
            lastUpdate: Date.now()
        });
    }
    
    if (!percentageFrequencyAnalysis.has(rangeName)) {
        percentageFrequencyAnalysis.set(rangeName, {
            frequencyDistribution: new Map(), // Distribution des fréquences
            percentileRanks: {}, // Classements en percentiles
            statistiques: {
                modePercentage: 0, // Pourcentage le plus fréquent
                medianFrequency: 0, // Fréquence médiane
                varianceFrequency: 0, // Variance des fréquences
                coefficientVariation: 0 // Coefficient de variation
            },
            classementDetaille: [], // Classement détaillé avec toutes les métriques
            tendanceFrequence: "stable", // Tendance des fréquences
            indexStabilite: 0 // Index de stabilité des pourcentages
        });
    }
}

/**
 * 📈 Groupe les pourcentages similaires avec une tolérance
 */
function groupSimilarPercentages(percentages, tolerance = 0.1) {
    const groups = new Map();
    
    percentages.forEach(percentage => {
        let foundGroup = false;
        
        for (const [groupKey, groupData] of groups.entries()) {
            if (Math.abs(percentage - groupKey) <= tolerance) {
                groupData.values.push(percentage);
                groupData.count++;
                groupData.average = groupData.values.reduce((sum, val) => sum + val, 0) / groupData.values.length;
                foundGroup = true;
                break;
            }
        }
        
        if (!foundGroup) {
            groups.set(percentage, {
                values: [percentage],
                count: 1,
                average: percentage,
                range: { min: percentage, max: percentage }
            });
        }
    });
    
    // Mettre à jour les ranges pour chaque groupe
    groups.forEach((groupData, key) => {
        groupData.range.min = Math.min(...groupData.values);
        groupData.range.max = Math.max(...groupData.values);
    });
    
    return groups;
}

/**
 * 📊 Calcule les fréquences exactes des pourcentages
 */
function calculatePercentageFrequencies(percentages) {
    const frequencyMap = new Map();
    
    percentages.forEach(percentage => {
        // Arrondir à 1 décimale pour regrouper les valeurs similaires
        const roundedPercentage = Math.round(percentage * 10) / 10;
        
        if (frequencyMap.has(roundedPercentage)) {
            frequencyMap.set(roundedPercentage, frequencyMap.get(roundedPercentage) + 1);
        } else {
            frequencyMap.set(roundedPercentage, 1);
        }
    });
    
    return frequencyMap;
}

/**
 * 🏆 Met à jour le classement des pourcentages pour une range
 */
function updatePercentageRanking(rangeName) {
    const percentageHistory = rangePercentageHistory.get(rangeName) || [];
    
    if (percentageHistory.length < 5) return; // Pas assez de données
    
    initializePercentageRanking(rangeName);
    
    const rankingData = percentageRankingHistory.get(rangeName);
    const frequencyData = percentageFrequencyAnalysis.get(rangeName);
    
    // 1️⃣ Calcul des fréquences exactes
    const frequencyMap = calculatePercentageFrequencies(percentageHistory);
    
    // 2️⃣ Groupement des pourcentages similaires
    const percentageGroups = groupSimilarPercentages(percentageHistory, 0.2);
    
    // 3️⃣ Création du classement détaillé
    const classementDetaille = [];
    
    frequencyMap.forEach((frequency, percentage) => {
        const occurrencePercentage = (frequency / percentageHistory.length) * 100;
        
        classementDetaille.push({
            percentage: percentage,
            frequency: frequency,
            occurrencePercentage: parseFloat(occurrencePercentage.toFixed(2)),
            rank: 0, // Sera calculé après tri
            category: "", // Sera déterminée après analyse
            rarity: "", // Rare, Common, Frequent, Very Frequent
            lastSeen: getLastOccurrenceIndex(percentageHistory, percentage),
            firstSeen: getFirstOccurrenceIndex(percentageHistory, percentage),
            consecutiveCount: getMaxConsecutiveCount(percentageHistory, percentage),
            averageGap: calculateAverageGap(percentageHistory, percentage)
        });
    });
    
    // 4️⃣ Tri par fréquence décroissante et attribution des rangs
    classementDetaille.sort((a, b) => b.frequency - a.frequency);
    classementDetaille.forEach((item, index) => {
        item.rank = index + 1;
    });
    
    // 5️⃣ Catégorisation et détermination de la rareté
    const totalItems = classementDetaille.length;
    classementDetaille.forEach((item, index) => {
        // Catégories basées sur le rang relatif
        const percentileRank = ((totalItems - index) / totalItems) * 100;
        
        if (percentileRank >= 90) {
            item.category = "Ultra-Fréquent";
            item.rarity = "Very Frequent";
        } else if (percentileRank >= 70) {
            item.category = "Très-Fréquent";
            item.rarity = "Frequent";
        } else if (percentileRank >= 50) {
            item.category = "Fréquent";
            item.rarity = "Common";
        } else if (percentileRank >= 30) {
            item.category = "Modéré";
            item.rarity = "Uncommon";
        } else if (percentileRank >= 10) {
            item.category = "Rare";
            item.rarity = "Rare";
        } else {
            item.category = "Ultra-Rare";
            item.rarity = "Very Rare";
        }
        
        item.percentileRank = parseFloat(percentileRank.toFixed(1));
    });
    
    // 6️⃣ Calcul des statistiques globales
    const frequencies = classementDetaille.map(item => item.frequency);
    const meanFrequency = frequencies.reduce((sum, freq) => sum + freq, 0) / frequencies.length;
    const medianFrequency = calculateMedian(frequencies);
    const varianceFrequency = frequencies.reduce((sum, freq) => sum + Math.pow(freq - meanFrequency, 2), 0) / frequencies.length;
    const coefficientVariation = meanFrequency > 0 ? (Math.sqrt(varianceFrequency) / meanFrequency) * 100 : 0;
    
    // 7️⃣ Détermination du mode (pourcentage le plus fréquent)
    const modePercentage = classementDetaille.length > 0 ? classementDetaille[0].percentage : 0;
    
    // 8️⃣ Analyse de la tendance des fréquences
    const tendanceFrequence = analyzeFrequencyTrend(classementDetaille);
    
    // 9️⃣ Calcul de l'index de stabilité
    const indexStabilite = calculateStabilityIndex(classementDetaille, percentageHistory);
    
    // 🔟 Top et rare pourcentages
    const topPercentages = classementDetaille.slice(0, Math.min(10, Math.ceil(totalItems * 0.2)));
    const rarePercentages = classementDetaille.slice(-Math.min(5, Math.ceil(totalItems * 0.1)));
    
    // Mise à jour des données
    rankingData.percentageGroups = percentageGroups;
    rankingData.topPercentages = topPercentages;
    rankingData.rarePercentages = rarePercentages;
    rankingData.averageFrequency = parseFloat(meanFrequency.toFixed(2));
    rankingData.totalOccurrences = percentageHistory.length;
    rankingData.lastUpdate = Date.now();
    
    frequencyData.frequencyDistribution = frequencyMap;
    frequencyData.statistiques = {
        modePercentage: modePercentage,
        medianFrequency: parseFloat(medianFrequency.toFixed(2)),
        varianceFrequency: parseFloat(varianceFrequency.toFixed(4)),
        coefficientVariation: parseFloat(coefficientVariation.toFixed(2))
    };
    frequencyData.classementDetaille = classementDetaille;
    frequencyData.tendanceFrequence = tendanceFrequence;
    frequencyData.indexStabilite = parseFloat(indexStabilite.toFixed(2));
    
    // Calcul des percentiles
    frequencyData.percentileRanks = calculatePercentileRanks(classementDetaille);
    
    console.log(`📊 Classement mis à jour pour ${rangeName}: ${totalItems} pourcentages uniques, Mode: ${modePercentage}%, Top fréquence: ${topPercentages[0]?.frequency || 0}`);
    
    // 🎯 NOUVEAU: Capturer l'évolution du classement pour les prédictions
    captureRankingEvolution(rangeName);
}

/**
 * 🔍 Fonctions utilitaires pour l'analyse des pourcentages
 */
function getLastOccurrenceIndex(percentages, targetPercentage) {
    const tolerance = 0.05;
    for (let i = 0; i < percentages.length; i++) {
        if (Math.abs(percentages[i] - targetPercentage) <= tolerance) {
            return i;
        }
    }
    return -1;
}

function getFirstOccurrenceIndex(percentages, targetPercentage) {
    const tolerance = 0.05;
    for (let i = percentages.length - 1; i >= 0; i--) {
        if (Math.abs(percentages[i] - targetPercentage) <= tolerance) {
            return percentages.length - 1 - i;
        }
    }
    return -1;
}

function getMaxConsecutiveCount(percentages, targetPercentage) {
    const tolerance = 0.05;
    let maxConsecutive = 0;
    let currentConsecutive = 0;
    
    percentages.forEach(percentage => {
        if (Math.abs(percentage - targetPercentage) <= tolerance) {
            currentConsecutive++;
            maxConsecutive = Math.max(maxConsecutive, currentConsecutive);
        } else {
            currentConsecutive = 0;
        }
    });
    
    return maxConsecutive;
}

function calculateAverageGap(percentages, targetPercentage) {
    const tolerance = 0.05;
    const occurrences = [];
    
    percentages.forEach((percentage, index) => {
        if (Math.abs(percentage - targetPercentage) <= tolerance) {
            occurrences.push(index);
        }
    });
    
    if (occurrences.length < 2) return 0;
    
    const gaps = [];
    for (let i = 1; i < occurrences.length; i++) {
        gaps.push(occurrences[i] - occurrences[i - 1]);
    }
    
    return gaps.length > 0 ? parseFloat((gaps.reduce((sum, gap) => sum + gap, 0) / gaps.length).toFixed(1)) : 0;
}

function analyzeFrequencyTrend(classement) {
    if (classement.length < 3) return "insufficient-data";
    
    const topFrequencies = classement.slice(0, Math.min(5, classement.length)).map(item => item.frequency);
    const bottomFrequencies = classement.slice(-Math.min(5, classement.length)).map(item => item.frequency);
    
    const topAverage = topFrequencies.reduce((sum, freq) => sum + freq, 0) / topFrequencies.length;
    const bottomAverage = bottomFrequencies.reduce((sum, freq) => sum + freq, 0) / bottomFrequencies.length;
    
    const ratio = bottomAverage > 0 ? topAverage / bottomAverage : topAverage;
    
    if (ratio > 5) return "très-concentré";
    else if (ratio > 3) return "concentré";
    else if (ratio > 2) return "modérément-concentré";
    else if (ratio > 1.5) return "légèrement-concentré";
    else return "équilibré";
}

function calculateStabilityIndex(classement, percentageHistory) {
    if (classement.length === 0 || percentageHistory.length === 0) return 0;
    
    // L'index de stabilité est basé sur la régularité des pourcentages les plus fréquents
    const topItems = classement.slice(0, Math.min(3, classement.length));
    const totalTopFrequency = topItems.reduce((sum, item) => sum + item.frequency, 0);
    const stabilityRatio = (totalTopFrequency / percentageHistory.length) * 100;
    
    // Plus le ratio est élevé, plus c'est stable
    return Math.min(100, stabilityRatio);
}

function calculatePercentileRanks(classement) {
    const percentiles = {};
    const total = classement.length;
    
    [10, 25, 50, 75, 90, 95, 99].forEach(percentile => {
        const index = Math.ceil((percentile / 100) * total) - 1;
        if (index >= 0 && index < total) {
            percentiles[`p${percentile}`] = classement[total - 1 - index]; // Inverser car le classement est décroissant
        }
    });
    
    return percentiles;
}

/**
 * 🏆 Obtient le résumé global du classement pour toutes les ranges
 */
function getGlobalPercentageRankingSummary() {
    const allRanges = Array.from(percentageRankingHistory.keys());
    
    if (allRanges.length === 0) {
        return {
            totalRanges: 0,
            globalTopPercentages: [],
            rangeMostStable: null,
            rangeMostDiverse: null,
            averageUniquePercentages: 0,
            totalUniquePercentages: 0,
            globalTrendFrequency: "unknown",
            stabilityComparison: {},
            diversityMetrics: {},
            recommendationDominance: "balanced"
        };
    }
    
    let totalUniquePercentages = 0;
    let mostStableRange = null;
    let mostDiverseRange = null;
    let maxStability = 0;
    let maxDiversity = 0;
    const globalTopPercentages = [];
    const stabilityComparison = {};
    const diversityMetrics = {};
    
    allRanges.forEach(rangeName => {
        const rankingData = percentageRankingHistory.get(rangeName);
        const frequencyData = percentageFrequencyAnalysis.get(rangeName);
        
        if (rankingData && frequencyData) {
            const uniqueCount = frequencyData.classementDetaille.length;
            totalUniquePercentages += uniqueCount;
            
            const stability = frequencyData.indexStabilite;
            const diversity = uniqueCount;
            
            // Collecte des tops pour le global
            rankingData.topPercentages.slice(0, 3).forEach(item => {
                globalTopPercentages.push({
                    ...item,
                    rangeName: rangeName
                });
            });
            
            // Range la plus stable
            if (stability > maxStability) {
                maxStability = stability;
                mostStableRange = {
                    name: rangeName,
                    stability: stability,
                    topPercentage: frequencyData.statistiques.modePercentage,
                    trend: frequencyData.tendanceFrequence
                };
            }
            
            // Range la plus diverse
            if (diversity > maxDiversity) {
                maxDiversity = diversity;
                mostDiverseRange = {
                    name: rangeName,
                    uniquePercentages: diversity,
                    coefficientVariation: frequencyData.statistiques.coefficientVariation,
                    trend: frequencyData.tendanceFrequence
                };
            }
            
            stabilityComparison[rangeName] = {
                indexStabilite: stability,
                tendance: frequencyData.tendanceFrequence,
                modePercentage: frequencyData.statistiques.modePercentage
            };
            
            diversityMetrics[rangeName] = {
                uniquePercentages: uniqueCount,
                coefficientVariation: frequencyData.statistiques.coefficientVariation,
                medianFrequency: frequencyData.statistiques.medianFrequency
            };
        }
    });
    
    // Tri des tops globaux
    globalTopPercentages.sort((a, b) => b.frequency - a.frequency);
    const topGlobalPercentages = globalTopPercentages.slice(0, 15);
    
    const averageUniquePercentages = allRanges.length > 0 ? totalUniquePercentages / allRanges.length : 0;
    
    // Détermination de la tendance globale
    const allTrends = allRanges.map(rangeName => {
        const frequencyData = percentageFrequencyAnalysis.get(rangeName);
        return frequencyData ? frequencyData.tendanceFrequence : 'unknown';
    });
    
    const trendCounts = {};
    allTrends.forEach(trend => {
        trendCounts[trend] = (trendCounts[trend] || 0) + 1;
    });
    
    const globalTrendFrequency = Object.keys(trendCounts).reduce((a, b) => 
        trendCounts[a] > trendCounts[b] ? a : b, 'unknown');
    
    // Recommandation de dominance
    let recommendationDominance = "balanced";
    const avgStability = Object.values(stabilityComparison).reduce((sum, item) => sum + item.indexStabilite, 0) / allRanges.length;
    
    if (avgStability > 70) recommendationDominance = "stability-focused";
    else if (avgStability < 30) recommendationDominance = "diversity-focused";
    else recommendationDominance = "balanced";
    
    return {
        totalRanges: allRanges.length,
        globalTopPercentages: topGlobalPercentages,
        rangeMostStable: mostStableRange,
        rangeMostDiverse: mostDiverseRange,
        averageUniquePercentages: parseFloat(averageUniquePercentages.toFixed(1)),
        totalUniquePercentages: totalUniquePercentages,
        globalTrendFrequency: globalTrendFrequency,
        stabilityComparison: stabilityComparison,
        diversityMetrics: diversityMetrics,
        recommendationDominance: recommendationDominance,
        averageStability: parseFloat(avgStability.toFixed(1))
    };
}

// 🌡️ SYSTÈME DE THERMOMÈTRE CORRIGÉ AVEC STABILITÉ

/**
 * Initialise le stockage des points pour le thermomètre
 */
function initializeThermometreForRange(rangeName, limit) {
    if (!thermometrePointsHistory.has(rangeName)) {
        thermometrePointsHistory.set(rangeName, {
            points: [], // Tableau des points avec identifiants
            limit: limit || 1000,
            counters: {
                p: 0,    // pics
                c: 0,    // creux
                pl: 0,   // pics légers
                cl: 0,   // creux légers
                mp: 0,   // montées progressives
                cp: 0,   // chutes progressives
                st: 0    // stabilité (plateaux)
            }
        });
    }
}

/**
 * 🔧 FONCTION CORRIGÉE : Met à jour le thermomètre avec les nouvelles analyses (avec zone de stabilité)
 */
function updateThermometreForRange(rangeName, picsCreuxEvents, chutesMonteeEvents, picsCreuxLegersEvents, plateauxEvents) {
    const range = currentRanges.find(r => r.name === rangeName);
    if (!range) return;
    
    // 🔧 CORRECTION MAJEURE : Réinitialiser complètement le thermomètre à chaque mise à jour
    thermometrePointsHistory.set(rangeName, {
        points: [],
        limit: range.limit || 1000,
        counters: {
            p: 0,    // pics
            c: 0,    // creux
            pl: 0,   // pics légers
            cl: 0,   // creux légers
            mp: 0,   // montées progressives
            cp: 0,   // chutes progressives
            st: 0    // stabilité (plateaux)
        }
    });
    
    const thermometreData = thermometrePointsHistory.get(rangeName);
    let totalPointsAdded = 0;
    
    // ✅ Traiter les pics et creux classiques - 1 POINT PAR ÉVÉNEMENT EXACTEMENT
    if (picsCreuxEvents && Array.isArray(picsCreuxEvents)) {
        picsCreuxEvents.forEach(event => {
            const pointType = event.type === 'pic' ? 'p' : 'c';
            thermometreData.points.push({
                type: pointType,
                timestamp: event.timestamp || Date.now(),
                value: event.value,
                source: 'pics-creux',
                eventId: `pc_${event.index}`
            });
            thermometreData.counters[pointType]++;
            totalPointsAdded++;
        });
    }
    
    // ✅ Traiter les pics et creux légers - 1 POINT PAR ÉVÉNEMENT EXACTEMENT
    if (picsCreuxLegersEvents && Array.isArray(picsCreuxLegersEvents)) {
        picsCreuxLegersEvents.forEach(event => {
            const pointType = event.type === 'pic-leger' ? 'pl' : 'cl';
            thermometreData.points.push({
                type: pointType,
                timestamp: event.timestamp || Date.now(),
                value: event.value || event.plateauMean_Value,
                source: 'pics-creux-legers',
                eventId: `pcl_${event.plateauStart_Index || event.index}`
            });
            thermometreData.counters[pointType]++;
            totalPointsAdded++;
        });
    }
    
    // ✅ Traiter les chutes et montées progressives - POINTS = LONGUEUR DU MOUVEMENT
    if (chutesMonteeEvents && Array.isArray(chutesMonteeEvents)) {
        chutesMonteeEvents.forEach(movement => {
            const pointType = movement.type === 'montee' ? 'mp' : 'cp';
            // Ajouter exactement movement.length points
            for (let i = 0; i < movement.length; i++) {
                thermometreData.points.push({
                    type: pointType,
                    timestamp: movement.timestamp || Date.now(),
                    value: movement.startValue + (i * (movement.slope || 0)),
                    source: 'chutes-montees',
                    eventId: `cm_${movement.startIndex}_${i}`
                });
                thermometreData.counters[pointType]++;
                totalPointsAdded++;
            }
        });
    }
    
    // 🆕 NOUVEAU : Traiter les plateaux (stabilité) - POINTS = LONGUEUR DU PLATEAU
    if (plateauxEvents && Array.isArray(plateauxEvents)) {
        plateauxEvents.forEach(plateau => {
            // Ajouter exactement plateau.pointsCount ou plateau.length points de stabilité
            const plateauPoints = plateau.pointsCount || plateau.length || 1;
            for (let i = 0; i < plateauPoints; i++) {
                thermometreData.points.push({
                    type: 'st', // stabilité
                    timestamp: plateau.timestamp || Date.now(),
                    value: plateau.avgValue || plateau.plateauMean || 0,
                    source: 'plateaux',
                    eventId: `pl_${plateau.startIndex}_${i}`
                });
                thermometreData.counters.st++;
                totalPointsAdded++;
            }
        });
    }
    
    // ✅ Maintenir la limite du thermomètre
    if (thermometreData.points.length > thermometreData.limit) {
        const excessPoints = thermometreData.points.length - thermometreData.limit;
        const removedPoints = thermometreData.points.splice(0, excessPoints);
        
        // Ajuster les compteurs pour les points supprimés
        removedPoints.forEach(point => {
            if (thermometreData.counters.hasOwnProperty(point.type)) {
                thermometreData.counters[point.type] = Math.max(0, thermometreData.counters[point.type] - 1);
            }
        });
    }
    
    console.log(`🌡️ THERMOMÈTRE ${rangeName}: ${totalPointsAdded} points ajoutés - Pics: ${thermometreData.counters.p}, Creux: ${thermometreData.counters.c}, Pics légers: ${thermometreData.counters.pl}, Creux légers: ${thermometreData.counters.cl}, Montées: ${thermometreData.counters.mp}, Chutes: ${thermometreData.counters.cp}, Stabilité: ${thermometreData.counters.st}`);
    
    return calculateZonePercentages(rangeName);
}

/**
 * Calcule les pourcentages de zone négative, stabilité et positive
 */
function calculateZonePercentages(rangeName) {
    const thermometreData = thermometrePointsHistory.get(rangeName);
    if (!thermometreData || thermometreData.points.length === 0) {
        return {
            zoneNegative: 0,
            zoneStabilite: 0,
            zonePositive: 0,
            totalPoints: 0,
            repartition: {
                pics: 0,
                creux: 0,
                picsLegers: 0,
                creuxLegers: 0,
                monteesProgressives: 0,
                chutesProgressives: 0,
                stabilite: 0
            }
        };
    }
    
    const counters = thermometreData.counters;
    const totalPoints = thermometreData.points.length;
    
    // Zone négative : chutes progressives + creux + creux légers
    const pointsNegatifs = counters.cp + counters.c + counters.cl;
    
    // Zone de stabilité : plateaux
    const pointsStabilite = counters.st || 0;
    
    // Zone positive : montées progressives + pics + pics légers
    const pointsPositifs = counters.mp + counters.p + counters.pl;
    
    const totalPatternsPoints = pointsNegatifs + pointsStabilite + pointsPositifs;
    
    const zoneNegative = totalPatternsPoints > 0 ? (pointsNegatifs / totalPatternsPoints) * 100 : 0;
    const zoneStabilite = totalPatternsPoints > 0 ? (pointsStabilite / totalPatternsPoints) * 100 : 0;
    const zonePositive = totalPatternsPoints > 0 ? (pointsPositifs / totalPatternsPoints) * 100 : 0;
    
    return {
        zoneNegative: parseFloat(zoneNegative.toFixed(2)),
        zoneStabilite: parseFloat(zoneStabilite.toFixed(2)),
        zonePositive: parseFloat(zonePositive.toFixed(2)),
        totalPoints: totalPoints,
        totalPatternsPoints: totalPatternsPoints,
        repartition: {
            pics: counters.p,
            creux: counters.c,
            picsLegers: counters.pl,
            creuxLegers: counters.cl,
            monteesProgressives: counters.mp,
            chutesProgressives: counters.cp,
            stabilite: counters.st || 0
        },
        pourcentageRepartition: totalPatternsPoints > 0 ? {
            pics: parseFloat(((counters.p / totalPatternsPoints) * 100).toFixed(1)),
            creux: parseFloat(((counters.c / totalPatternsPoints) * 100).toFixed(1)),
            picsLegers: parseFloat(((counters.pl / totalPatternsPoints) * 100).toFixed(1)),
            creuxLegers: parseFloat(((counters.cl / totalPatternsPoints) * 100).toFixed(1)),
            monteesProgressives: parseFloat(((counters.mp / totalPatternsPoints) * 100).toFixed(1)),
            chutesProgressives: parseFloat(((counters.cp / totalPatternsPoints) * 100).toFixed(1)),
            stabilite: parseFloat(((counters.st / totalPatternsPoints) * 100).toFixed(1))
        } : {
            pics: 0, creux: 0, picsLegers: 0, creuxLegers: 0, monteesProgressives: 0, chutesProgressives: 0, stabilite: 0
        }
    };
}

/**
 * Calcule le résumé global du thermomètre avec stabilité
 */
function getGlobalThermometreSummary() {
    const allRanges = Array.from(thermometrePointsHistory.keys());
    
    if (allRanges.length === 0) {
        return {
            totalRanges: 0,
            zoneNegativeGlobale: 0,
            zoneStabiliteGlobale: 0,
            zonePositiveGlobale: 0,
            rangeMostNegative: null,
            rangeMostStable: null,
            rangeMostPositive: null,
            repartitionGlobale: {
                pics: 0, creux: 0, picsLegers: 0, creuxLegers: 0, 
                monteesProgressives: 0, chutesProgressives: 0, stabilite: 0
            },
            tendanceGlobale: "neutre",
            equilibreGlobal: 0,
            stabiliteGlobale: 0
        };
    }
    
    let totalNegatif = 0;
    let totalStabilite = 0;
    let totalPositif = 0;
    let totalPatterns = 0;
    let mostNegativeRange = null;
    let mostStableRange = null;
    let mostPositiveRange = null;
    let maxNegative = 0;
    let maxStable = 0;
    let maxPositive = 0;
    
    const repartitionGlobale = {
        pics: 0, creux: 0, picsLegers: 0, creuxLegers: 0, 
        monteesProgressives: 0, chutesProgressives: 0, stabilite: 0
    };
    
    allRanges.forEach(rangeName => {
        const zoneData = calculateZonePercentages(rangeName);
        const thermometreData = thermometrePointsHistory.get(rangeName);
        
        if (thermometreData && zoneData.totalPatternsPoints > 0) {
            const counters = thermometreData.counters;
            
            // Accumulation des totaux
            totalNegatif += counters.cp + counters.c + counters.cl;
            totalStabilite += counters.st || 0;
            totalPositif += counters.mp + counters.p + counters.pl;
            totalPatterns += zoneData.totalPatternsPoints;
            
            // Accumulation de la répartition
            repartitionGlobale.pics += counters.p;
            repartitionGlobale.creux += counters.c;
            repartitionGlobale.picsLegers += counters.pl;
            repartitionGlobale.creuxLegers += counters.cl;
            repartitionGlobale.monteesProgressives += counters.mp;
            repartitionGlobale.chutesProgressives += counters.cp;
            repartitionGlobale.stabilite += counters.st || 0;
            
            // Recherche des ranges les plus négatives/stables/positives
            if (zoneData.zoneNegative > maxNegative) {
                maxNegative = zoneData.zoneNegative;
                mostNegativeRange = {
                    name: rangeName,
                    pourcentage: zoneData.zoneNegative
                };
            }
            
            if (zoneData.zoneStabilite > maxStable) {
                maxStable = zoneData.zoneStabilite;
                mostStableRange = {
                    name: rangeName,
                    pourcentage: zoneData.zoneStabilite
                };
            }
            
            if (zoneData.zonePositive > maxPositive) {
                maxPositive = zoneData.zonePositive;
                mostPositiveRange = {
                    name: rangeName,
                    pourcentage: zoneData.zonePositive
                };
            }
        }
    });
    
    const zoneNegativeGlobale = totalPatterns > 0 ? (totalNegatif / totalPatterns) * 100 : 0;
    const zoneStabiliteGlobale = totalPatterns > 0 ? (totalStabilite / totalPatterns) * 100 : 0;
    const zonePositiveGlobale = totalPatterns > 0 ? (totalPositif / totalPatterns) * 100 : 0;
    
    // Déterminer la tendance globale selon les trois zones
    let tendanceGlobale = "neutre";
    const zones = [
        { nom: "négative", valeur: zoneNegativeGlobale },
        { nom: "stabilité", valeur: zoneStabiliteGlobale },
        { nom: "positive", valeur: zonePositiveGlobale }
    ];
    
    const zoneDominante = zones.reduce((max, zone) => zone.valeur > max.valeur ? zone : max);
    
    if (zoneDominante.valeur > 40) {
        if (zoneDominante.nom === "négative") tendanceGlobale = "très-négative";
        else if (zoneDominante.nom === "stabilité") tendanceGlobale = "très-stable";
        else tendanceGlobale = "très-positive";
    } else if (zoneDominante.valeur > 35) {
        if (zoneDominante.nom === "négative") tendanceGlobale = "négative";
        else if (zoneDominante.nom === "stabilité") tendanceGlobale = "stable";
        else tendanceGlobale = "positive";
    } else {
        tendanceGlobale = "équilibrée";
    }
    
    const equilibreGlobal = zonePositiveGlobale - zoneNegativeGlobale;
    const stabiliteGlobale = zoneStabiliteGlobale;
    
    return {
        totalRanges: allRanges.length,
        zoneNegativeGlobale: parseFloat(zoneNegativeGlobale.toFixed(2)),
        zoneStabiliteGlobale: parseFloat(zoneStabiliteGlobale.toFixed(2)),
        zonePositiveGlobale: parseFloat(zonePositiveGlobale.toFixed(2)),
        rangeMostNegative: mostNegativeRange,
        rangeMostStable: mostStableRange,
        rangeMostPositive: mostPositiveRange,
        repartitionGlobale,
        pourcentageRepartitionGlobale: totalPatterns > 0 ? {
            pics: parseFloat(((repartitionGlobale.pics / totalPatterns) * 100).toFixed(1)),
            creux: parseFloat(((repartitionGlobale.creux / totalPatterns) * 100).toFixed(1)),
            picsLegers: parseFloat(((repartitionGlobale.picsLegers / totalPatterns) * 100).toFixed(1)),
            creuxLegers: parseFloat(((repartitionGlobale.creuxLegers / totalPatterns) * 100).toFixed(1)),
            monteesProgressives: parseFloat(((repartitionGlobale.monteesProgressives / totalPatterns) * 100).toFixed(1)),
            chutesProgressives: parseFloat(((repartitionGlobale.chutesProgressives / totalPatterns) * 100).toFixed(1)),
            stabilite: parseFloat(((repartitionGlobale.stabilite / totalPatterns) * 100).toFixed(1))
        } : {
            pics: 0, creux: 0, picsLegers: 0, creuxLegers: 0, monteesProgressives: 0, chutesProgressives: 0, stabilite: 0
        },
        tendanceGlobale,
        equilibreGlobal: parseFloat(equilibreGlobal.toFixed(2)),
        stabiliteGlobale: parseFloat(stabiliteGlobale.toFixed(2)),
        totalPatterns
    };
}

// 🔥 FONCTIONS D'ANALYSE DES PLATEAUX AVEC SYSTÈME DE POINTS

/**
 * Détecte les zones de plateau dans une série de données
 */
function detectPlateaux(data, minPlateauLength = 1, maxVariation = 1.5, minStabilityDuration = 1) {
    if (!data || data.length < minPlateauLength) return [];
    
    const plateaux = [];
    let currentPlateau = null;
    
    for (let i = 0; i < data.length - minPlateauLength + 1; i++) {
        const window = data.slice(i, i + minPlateauLength);
        const windowMean = window.reduce((sum, val) => sum + val, 0) / window.length;
        
        const windowVariations = window.map(val => Math.abs((val - windowMean) / windowMean) * 100);
        const maxWindowVariation = Math.max(...windowVariations);
        
        if (maxWindowVariation <= maxVariation) {
            if (!currentPlateau) {
                currentPlateau = {
                    startIndex: i,
                    endIndex: i + minPlateauLength - 1,
                    values: [...window],
                    stabilityPoints: 1
                };
            } else {
                currentPlateau.endIndex = i + minPlateauLength - 1;
                currentPlateau.values.push(data[i + minPlateauLength - 1]);
                currentPlateau.stabilityPoints++;
            }
        } else {
            if (currentPlateau && currentPlateau.stabilityPoints >= minStabilityDuration) {
                const plateauData = finalizePlateau(currentPlateau, data);
                if (plateauData.length >= minPlateauLength) {
                    plateaux.push(plateauData);
                }
            }
            currentPlateau = null;
        }
    }
    
    if (currentPlateau && currentPlateau.stabilityPoints >= minStabilityDuration) {
        const plateauData = finalizePlateau(currentPlateau, data);
        if (plateauData.length >= minPlateauLength) {
            plateaux.push(plateauData);
        }
    }
    
    return plateaux;
}

/**
 * Finalise un plateau détecté avec toutes ses métriques et comptage de points
 */
function finalizePlateau(plateau, data) {
    const startIndex = plateau.startIndex;
    const endIndex = Math.min(plateau.endIndex, data.length - 1);
    const plateauValues = data.slice(startIndex, endIndex + 1);
    
    const length = plateauValues.length;
    const avgValue = plateauValues.reduce((sum, val) => sum + val, 0) / length;
    const minValue = Math.min(...plateauValues);
    const maxValue = Math.max(...plateauValues);
    
    // 🆕 NOUVEAUTÉ : Comptage de points pour le plateau
    const pointsCount = length; // Chaque point du plateau compte
    
    const variation = avgValue > 0 ? ((maxValue - minValue) / avgValue) * 100 : maxValue - minValue;
    
    const variance = plateauValues.reduce((sum, val) => sum + Math.pow(val - avgValue, 2), 0) / length;
    const stability = avgValue > 0 ? Math.max(0, 100 - (Math.sqrt(variance) / avgValue) * 100) : 100 - Math.sqrt(variance);
    
    const density = length / (endIndex - startIndex + 1);
    
    let internalTrend = "stable";
    if (plateauValues.length >= 3) {
        const firstThird = plateauValues.slice(0, Math.floor(length / 3));
        const lastThird = plateauValues.slice(-Math.floor(length / 3));
        const firstAvg = firstThird.reduce((sum, val) => sum + val, 0) / firstThird.length;
        const lastAvg = lastThird.reduce((sum, val) => sum + val, 0) / lastThird.length;
        
        const trendChange = ((lastAvg - firstAvg) / firstAvg) * 100;
        if (trendChange > 0.5) internalTrend = "légèrement-croissant";
        else if (trendChange < -0.5) internalTrend = "légèrement-décroissant";
    }
    
    return {
        startIndex,
        endIndex,
        length,
        pointsCount,
        avgValue: parseFloat(avgValue.toFixed(3)),
        minValue: parseFloat(minValue.toFixed(3)),
        maxValue: parseFloat(maxValue.toFixed(3)),
        variation: parseFloat(variation.toFixed(2)),
        stability: parseFloat(stability.toFixed(2)),
        density: parseFloat(density.toFixed(2)),
        internalTrend,
        stabilityPoints: plateau.stabilityPoints,
        timestamp: Date.now() - (data.length - endIndex) * 100,
        plateauValues: plateauValues
    };
}

/**
 * Calcule l'analyse globale des plateaux avec pourcentages de présence
 */
function calculatePlateauxGlobalTrend(plateaux, picsCreux = [], chutesMontees = [], picsCreuxLegers = [], dataSize = 0) {
    if (!plateaux || plateaux.length === 0) {
        return {
            totalPlateaux: 0,
            totalPointsPlateaux: 0,
            pourcentagePresencePlateaux: 0,
            moyenneLongueurPlateaux: 0,
            moyenneStabilitePlateaux: 0,
            moyenneVariationPlateaux: 0,
            pourcentageTempsEnPlateau: 0,
            ratioPlateauxVsEvenements: 0,
            tendanceGlobale: "inconnue",
            stabiliteGlobale: 0,
            dernierPlateau: null,
            frequencePlateaux: 0,
            densiteMoyennePlateaux: 0,
            repartitionTendancesInternes: {},
            comparaisonAvecAutresEvenements: {},
            typeActiviteDominante: "inconnue"
        };
    }
    
    const totalPlateaux = plateaux.length;
    
    const totalPointsPlateaux = plateaux.reduce((sum, p) => sum + p.pointsCount, 0);
    const pourcentagePresencePlateaux = dataSize > 0 ? (totalPointsPlateaux / dataSize) * 100 : 0;
    
    const moyenneLongueurPlateaux = totalPlateaux > 0 ? 
        plateaux.reduce((sum, p) => sum + p.length, 0) / totalPlateaux : 0;
    
    const moyenneStabilitePlateaux = totalPlateaux > 0 ? 
        plateaux.reduce((sum, p) => sum + p.stability, 0) / totalPlateaux : 0;
    
    const moyenneVariationPlateaux = totalPlateaux > 0 ? 
        plateaux.reduce((sum, p) => sum + p.variation, 0) / totalPlateaux : 0;
    
    const densiteMoyennePlateaux = totalPlateaux > 0 ? 
        plateaux.reduce((sum, p) => sum + p.density, 0) / totalPlateaux : 0;
    
    const tempsEnPlateau = plateaux.reduce((sum, p) => sum + p.length, 0);
    const pourcentageTempsEnPlateau = dataSize > 0 ? (tempsEnPlateau / dataSize) * 100 : 0;
    
    const totalAutresEvenements = picsCreux.length + chutesMontees.length + picsCreuxLegers.length;
    const ratioPlateauxVsEvenements = totalAutresEvenements > 0 ? totalPlateaux / totalAutresEvenements : totalPlateaux;
    
    const repartitionTendancesInternes = {
        stable: plateaux.filter(p => p.internalTrend === "stable").length,
        croissant: plateaux.filter(p => p.internalTrend === "légèrement-croissant").length,
        decroissant: plateaux.filter(p => p.internalTrend === "légèrement-décroissant").length
    };
    
    let tendanceGlobale = "équilibrée";
    if (pourcentagePresencePlateaux >= 60) tendanceGlobale = "très-stable";
    else if (pourcentagePresencePlateaux >= 40) tendanceGlobale = "plutôt-stable";
    else if (pourcentagePresencePlateaux >= 20) tendanceGlobale = "modérément-stable";
    else tendanceGlobale = "très-dynamique";
    
    let typeActiviteDominante = "inconnue";
    const totalEvenements = totalPlateaux + totalAutresEvenements;
    
    if (totalEvenements > 0) {
        const pourcentagePlateaux = (totalPlateaux / totalEvenements) * 100;
        
        if (pourcentagePlateaux >= 50) {
            typeActiviteDominante = "stabilité-dominante";
        } else {
            const maxEventType = Math.max(picsCreux.length, chutesMontees.length, picsCreuxLegers.length);
            
            if (picsCreux.length === maxEventType) typeActiviteDominante = "pics-creux-dominants";
            else if (chutesMontees.length === maxEventType) typeActiviteDominante = "tendances-progressives-dominantes";
            else if (picsCreuxLegers.length === maxEventType) typeActiviteDominante = "fluctuations-legeres-dominantes";
            else typeActiviteDominante = "dynamique-mixte";
        }
    }
    
    const comparaisonAvecAutresEvenements = {
        pics_creux: {
            count: picsCreux.length,
            ratio: picsCreux.length > 0 ? totalPlateaux / picsCreux.length : totalPlateaux,
            pourcentage: totalEvenements > 0 ? (picsCreux.length / totalEvenements) * 100 : 0
        },
        chutes_montees: {
            count: chutesMontees.length,
            ratio: chutesMontees.length > 0 ? totalPlateaux / chutesMontees.length : totalPlateaux,
            pourcentage: totalEvenements > 0 ? (chutesMontees.length / totalEvenements) * 100 : 0
        },
        pics_creux_legers: {
            count: picsCreuxLegers.length,
            ratio: picsCreuxLegers.length > 0 ? totalPlateaux / picsCreuxLegers.length : totalPlateaux,
            pourcentage: totalEvenements > 0 ? (picsCreuxLegers.length / totalEvenements) * 100 : 0
        },
        plateaux: {
            count: totalPlateaux,
            pourcentage: totalEvenements > 0 ? (totalPlateaux / totalEvenements) * 100 : 0
        }
    };
    
    const stabiliteGlobale = moyenneStabilitePlateaux;
    const dernierPlateau = plateaux.length > 0 ? plateaux[plateaux.length - 1] : null;
    const frequencePlateaux = dataSize > 0 ? (totalPlateaux / dataSize) * 100 : 0;
    
    return {
        totalPlateaux,
        totalPointsPlateaux,
        pourcentagePresencePlateaux: parseFloat(pourcentagePresencePlateaux.toFixed(2)),
        moyenneLongueurPlateaux: parseFloat(moyenneLongueurPlateaux.toFixed(2)),
        moyenneStabilitePlateaux: parseFloat(moyenneStabilitePlateaux.toFixed(2)),
        moyenneVariationPlateaux: parseFloat(moyenneVariationPlateaux.toFixed(2)),
        pourcentageTempsEnPlateau: parseFloat(pourcentageTempsEnPlateau.toFixed(2)),
        ratioPlateauxVsEvenements: parseFloat(ratioPlateauxVsEvenements.toFixed(2)),
        tendanceGlobale,
        stabiliteGlobale: parseFloat(stabiliteGlobale.toFixed(2)),
        dernierPlateau,
        frequencePlateaux: parseFloat(frequencePlateaux.toFixed(2)),
        densiteMoyennePlateaux: parseFloat(densiteMoyennePlateaux.toFixed(2)),
        repartitionTendancesInternes,
        comparaisonAvecAutresEvenements,
        typeActiviteDominante
    };
}

// 🔍 FONCTION AVEC LOGIQUE INVERSÉE D'ANALYSE DES PICS ET CREUX LÉGERS

/**
 * Détecte les pics et creux légers avec comptage de points - LOGIQUE INVERSÉE
 */
function detectPicsCreuxLegers(data, minPlateauLength = 2, maxPlateauVariation = 2.0, minInitialChange = 1.0) {
    if (!data || data.length < 3) return [];
    
    const events = [];
   
    for (let i = 0; i < data.length - minPlateauLength - 1; i++) {
        let plateauValues = [];
        let plateauEnd = i;
        let isValidPlateau = false;
        
        for (let plateauLen = minPlateauLength; plateauLen <= Math.min(10, data.length - i - 1); plateauLen++) {
            const candidatePlateau = data.slice(i, i + plateauLen);
            const plateauMean = candidatePlateau.reduce((sum, val) => sum + val, 0) / candidatePlateau.length;
            
            let maxVariationInPlateau = 0;
            for (const value of candidatePlateau) {
                const variation = plateauMean > 0 ? Math.abs((value - plateauMean) / plateauMean) * 100 : Math.abs(value - plateauMean);
                maxVariationInPlateau = Math.max(maxVariationInPlateau, variation);
            }
            
            if (maxVariationInPlateau <= maxPlateauVariation) {
                plateauValues = candidatePlateau;
                plateauEnd = i + plateauLen - 1;
                isValidPlateau = true;
            } else {
                break;
            }
        }
        
        if (isValidPlateau && plateauEnd + 1 < data.length) {
            const plateauMean = plateauValues.reduce((sum, val) => sum + val, 0) / plateauValues.length;
            const pointAfterPlateau = data[plateauEnd + 1];
            
            const changePlateauToNext = plateauMean > 0 ? ((pointAfterPlateau - plateauMean) / plateauMean) * 100 : 0;
            
            if (Math.abs(changePlateauToNext) >= minInitialChange) {
                const plateauVariance = plateauValues.reduce((sum, val) => sum + Math.pow(val - plateauMean, 2), 0) / plateauValues.length;
                const stability = plateauMean > 0 ? Math.max(0, 100 - (Math.sqrt(plateauVariance) / plateauMean) * 100) : 100 - Math.sqrt(plateauVariance);
                
                let type = "";
                if (changePlateauToNext > 0) {
                    type = "creux-leger";
                } else {
                    type = "pic-leger";
                }
                
                const intensite = Math.abs(changePlateauToNext);
                
                const plateauMin = Math.min(...plateauValues);
                const plateauMax = Math.max(...plateauValues);
                const plateauVariationRange = plateauMax > 0 ? ((plateauMax - plateauMin) / plateauMax) * 100 : plateauMax - plateauMin;
                
                events.push({
                    plateauStart_Index: i,
                    plateauEnd_Index: plateauEnd,
                    plateauMean_Value: parseFloat(plateauMean.toFixed(3)),
                    changePoint_Index: plateauEnd + 1,
                    changePoint_Value: parseFloat(pointAfterPlateau.toFixed(3)),
                    
                    type: type,
                    changePlateauToNext: parseFloat(changePlateauToNext.toFixed(2)),
                    intensite: parseFloat(intensite.toFixed(2)),
                    
                    // ✅ CORRECTION : Chaque détection = 1 point EXACTEMENT
                    pointsCount: 1,
                    
                    plateauLength: plateauValues.length,
                    plateauStart: i,
                    plateauEnd: plateauEnd,
                    plateauMean: parseFloat(plateauMean.toFixed(3)),
                    plateauVariationRange: parseFloat(plateauVariationRange.toFixed(2)),
                    stability: parseFloat(stability.toFixed(2)),
                    plateauValues: plateauValues,
                    
                    timestamp: Date.now() - (data.length - (plateauEnd + 1)) * 100,
                    
                    index: plateauEnd + 1,
                    value: parseFloat(pointAfterPlateau.toFixed(3)),
                    initialChange: parseFloat(changePlateauToNext.toFixed(2)),
                    previousValue: parseFloat(plateauMean.toFixed(3)),
                    
                    pointA_Index: plateauEnd + 1,
                    pointA_Value: parseFloat(pointAfterPlateau.toFixed(3)),
                    pointB_Index: plateauEnd,
                    pointB_Value: parseFloat(plateauMean.toFixed(3)),
                    changeAtoB: parseFloat((-changePlateauToNext).toFixed(2))
                });
                
                i = plateauEnd;
            }
        }
    }
    
    return events.sort((a, b) => a.plateauStart_Index - b.plateauStart_Index);
}

/**
 * Calcule l'analyse globale des pics et creux légers avec pourcentages de présence
 */
function calculateGlobalPicsCreuxLegersTrend(events, dataSize = 0) {
    if (!events || events.length === 0) {
        return {
            totalPicsLegers: 0,
            totalCreuxLegers: 0,
            totalPointsPicsLegers: 0,
            totalPointsCreuxLegers: 0,
            pourcentagePresencePicsLegers: 0,
            pourcentagePresenceCreuxLegers: 0,
            pourcentagePresenceGlobale: 0,
            moyennePlateauLengthPics: 0,
            moyennePlateauLengthCreux: 0,
            moyenneStabilitePics: 0,
            moyenneStabiliteCreux: 0,
            moyenneIntensitePics: 0,
            moyenneIntensiteCreux: 0,
            tendance: "neutre",
            ratioPicsCreuxLegers: 0,
            stabiliteGlobale: 0,
            dernierEvenement: null,
            frequencePicsLegers: 0,
            frequenceCreuxLegers: 0,
            pourcentagePicsLegers: 0,
            pourcentageCreuxLegers: 0,
            moyenneDureePlateaux: 0,
            moyenneChangeAtoB: 0
        };
    }
    
    const picsLegers = events.filter(e => e.type === "pic-leger");
    const creuxLegers = events.filter(e => e.type === "creux-leger");
    
    const totalPicsLegers = picsLegers.length;
    const totalCreuxLegers = creuxLegers.length;
    
    // ✅ CORRECTION : Chaque événement = 1 point exactement
    const totalPointsPicsLegers = totalPicsLegers; // Chaque pic léger = 1 point
    const totalPointsCreuxLegers = totalCreuxLegers; // Chaque creux léger = 1 point
    const totalPointsGlobaux = totalPointsPicsLegers + totalPointsCreuxLegers;
    
    const pourcentagePresencePicsLegers = dataSize > 0 ? (totalPointsPicsLegers / dataSize) * 100 : 0;
    const pourcentagePresenceCreuxLegers = dataSize > 0 ? (totalPointsCreuxLegers / dataSize) * 100 : 0;
    const pourcentagePresenceGlobale = dataSize > 0 ? (totalPointsGlobaux / dataSize) * 100 : 0;
    
    const moyennePlateauLengthPics = totalPicsLegers > 0 ? 
        picsLegers.reduce((sum, p) => sum + p.plateauLength, 0) / totalPicsLegers : 0;
    
    const moyenneStabilitePics = totalPicsLegers > 0 ? 
        picsLegers.reduce((sum, p) => sum + p.stability, 0) / totalPicsLegers : 0;
    
    const moyenneIntensitePics = totalPicsLegers > 0 ? 
        picsLegers.reduce((sum, p) => sum + p.intensite, 0) / totalPicsLegers : 0;
    
    const moyennePlateauLengthCreux = totalCreuxLegers > 0 ? 
        creuxLegers.reduce((sum, c) => sum + c.plateauLength, 0) / totalCreuxLegers : 0;
    
    const moyenneStabiliteCreux = totalCreuxLegers > 0 ? 
        creuxLegers.reduce((sum, c) => sum + c.stability, 0) / totalCreuxLegers : 0;
    
    const moyenneIntensiteCreux = totalCreuxLegers > 0 ? 
        creuxLegers.reduce((sum, c) => sum + c.intensite, 0) / totalCreuxLegers : 0;
    
    const totalEvents = totalPicsLegers + totalCreuxLegers;
    const pourcentagePicsLegers = totalEvents > 0 ? (totalPicsLegers / totalEvents) * 100 : 0;
    const pourcentageCreuxLegers = totalEvents > 0 ? (totalCreuxLegers / totalEvents) * 100 : 0;
    
    let tendance = "neutre";
    if (pourcentagePresencePicsLegers > pourcentagePresenceCreuxLegers * 1.2) tendance = "pics-legers-dominants";
    else if (pourcentagePresenceCreuxLegers > pourcentagePresencePicsLegers * 1.2) tendance = "creux-legers-dominants";
    else if (pourcentagePicsLegers >= 55) tendance = "pics-legers-dominants";
    else if (pourcentageCreuxLegers >= 55) tendance = "creux-legers-dominants";
    
    const ratioPicsCreuxLegers = totalCreuxLegers > 0 ? totalPicsLegers / totalCreuxLegers : totalPicsLegers;
    const stabiliteGlobale = totalEvents > 0 ? 
        (moyenneStabilitePics * totalPicsLegers + moyenneStabiliteCreux * totalCreuxLegers) / totalEvents : 0;
    
    const dernierEvenement = events.length > 0 ? events[events.length - 1] : null;
    
    const dernierePosition = events.length > 0 ? Math.max(...events.map(e => e.changePoint_Index || e.index)) : 0;
    const frequencePicsLegers = dernierePosition > 0 ? (totalPicsLegers / dernierePosition) * 100 : 0;
    const frequenceCreuxLegers = dernierePosition > 0 ? (totalCreuxLegers / dernierePosition) * 100 : 0;
    
    const moyenneDureePlateaux = totalEvents > 0 ? 
        (moyennePlateauLengthPics * totalPicsLegers + moyennePlateauLengthCreux * totalCreuxLegers) / totalEvents : 0;
    
    const moyenneChangeAtoB = totalEvents > 0 ? 
        events.reduce((sum, e) => sum + Math.abs(e.changePlateauToNext || e.initialChange || 0), 0) / totalEvents : 0;
    
    return {
        totalPicsLegers,
        totalCreuxLegers,
        totalPointsPicsLegers,
        totalPointsCreuxLegers,
        pourcentagePresencePicsLegers: parseFloat(pourcentagePresencePicsLegers.toFixed(2)),
        pourcentagePresenceCreuxLegers: parseFloat(pourcentagePresenceCreuxLegers.toFixed(2)),
        pourcentagePresenceGlobale: parseFloat(pourcentagePresenceGlobale.toFixed(2)),
        moyennePlateauLengthPics: parseFloat(moyennePlateauLengthPics.toFixed(2)),
        moyennePlateauLengthCreux: parseFloat(moyennePlateauLengthCreux.toFixed(2)),
        moyenneStabilitePics: parseFloat(moyenneStabilitePics.toFixed(2)),
        moyenneStabiliteCreux: parseFloat(moyenneStabiliteCreux.toFixed(2)),
        moyenneIntensitePics: parseFloat(moyenneIntensitePics.toFixed(2)),
        moyenneIntensiteCreux: parseFloat(moyenneIntensiteCreux.toFixed(2)),
        tendance,
        ratioPicsCreuxLegers: parseFloat(ratioPicsCreuxLegers.toFixed(2)),
        stabiliteGlobale: parseFloat(stabiliteGlobale.toFixed(2)),
        dernierEvenement,
        frequencePicsLegers: parseFloat(frequencePicsLegers.toFixed(2)),
        frequenceCreuxLegers: parseFloat(frequenceCreuxLegers.toFixed(2)),
        pourcentagePicsLegers: parseFloat(pourcentagePicsLegers.toFixed(1)),
        pourcentageCreuxLegers: parseFloat(pourcentageCreuxLegers.toFixed(1)),
        moyenneDureePlateaux: parseFloat(moyenneDureePlateaux.toFixed(2)),
        moyenneChangeAtoB: parseFloat(moyenneChangeAtoB.toFixed(2))
    };
}

// 🔍 FONCTIONS D'ANALYSE DES PICS ET CREUX CLASSIQUES AVEC SYSTÈME DE POINTS

/**
 * Détecte les pics et creux classiques avec comptage de points
 */
function detectPicsCreux(data, minSensitivity = 0.5) {
    if (!data || data.length < 3) return [];
    
    const events = [];
    
    for (let i = 1; i < data.length - 1; i++) {
        const prev = data[i - 1];
        const current = data[i];
        const next = data[i + 1];
        
        // Détection de pic (valeur plus haute que ses voisins)
        if (current > prev && current > next) {
            const intensiteGauche = Math.abs(current - prev);
            const intensiteDroite = Math.abs(current - next);
            const intensiteMoyenne = (intensiteGauche + intensiteDroite) / 2;
            const profondeurPourcentage = (intensiteMoyenne / current) * 100;
            
            if (profondeurPourcentage >= minSensitivity) {
                events.push({
                    index: i,
                    value: current,
                    type: "pic",
                    pointsCount: 1, // ✅ CORRECTION : Chaque détection = 1 point EXACTEMENT
                    intensite: intensiteMoyenne,
                    profondeur: profondeurPourcentage,
                    intensiteGauche,
                    intensiteDroite,
                    timestamp: Date.now() - (data.length - i) * 100
                });
            }
        }
        
        // Détection de creux (valeur plus basse que ses voisins)
        if (current < prev && current < next) {
            const intensiteGauche = Math.abs(prev - current);
            const intensiteDroite = Math.abs(next - current);
            const intensiteMoyenne = (intensiteGauche + intensiteDroite) / 2;
            const profondeurPourcentage = current > 0 ? (intensiteMoyenne / current) * 100 : intensiteMoyenne;
            
            if (profondeurPourcentage >= minSensitivity) {
                events.push({
                    index: i,
                    value: current,
                    type: "creux",
                    pointsCount: 1, // ✅ CORRECTION : Chaque détection = 1 point EXACTEMENT
                    intensite: intensiteMoyenne,
                    profondeur: profondeurPourcentage,
                    intensiteGauche,
                    intensiteDroite,
                    timestamp: Date.now() - (data.length - i) * 100
                });
            }
        }
    }
    
    return events.sort((a, b) => a.index - b.index);
}

/**
 * Calcule l'analyse globale des pics et creux classiques avec pourcentages de présence
 */
function calculateGlobalTrend(events, dataSize = 0) {
    if (!events || events.length === 0) {
        return {
            totalPics: 0,
            totalCreux: 0,
            totalPointsPics: 0,
            totalPointsCreux: 0,
            pourcentagePresencePics: 0,
            pourcentagePresenceCreux: 0,
            pourcentagePresenceGlobale: 0,
            moyenneHauteurPics: 0,
            moyenneProfondeurCreux: 0,
            moyenneIntensitePics: 0,
            moyenneIntensiteCreux: 0,
            tendance: "neutre",
            intensiteGlobale: "0% piquant vs 0% creux",
            ratioPicsCreux: 0,
            variabiliteGlobale: 0,
            dernierEvenement: null,
            frequencePics: 0,
            frequenceCreux: 0
        };
    }
    
    const pics = events.filter(e => e.type === "pic");
    const creux = events.filter(e => e.type === "creux");
    
    const totalPics = pics.length;
    const totalCreux = creux.length;
    
    // ✅ CORRECTION : Chaque événement = 1 point exactement
    const totalPointsPics = totalPics; // Chaque pic = 1 point
    const totalPointsCreux = totalCreux; // Chaque creux = 1 point
    const totalPointsGlobaux = totalPointsPics + totalPointsCreux;
    
    const pourcentagePresencePics = dataSize > 0 ? (totalPointsPics / dataSize) * 100 : 0;
    const pourcentagePresenceCreux = dataSize > 0 ? (totalPointsCreux / dataSize) * 100 : 0;
    const pourcentagePresenceGlobale = dataSize > 0 ? (totalPointsGlobaux / dataSize) * 100 : 0;
    
    const moyenneHauteurPics = totalPics > 0 ? 
        pics.reduce((sum, p) => sum + p.profondeur, 0) / totalPics : 0;
    
    const moyenneProfondeurCreux = totalCreux > 0 ? 
        creux.reduce((sum, c) => sum + c.profondeur, 0) / totalCreux : 0;
    
    const moyenneIntensitePics = totalPics > 0 ? 
        pics.reduce((sum, p) => sum + p.intensite, 0) / totalPics : 0;
    
    const moyenneIntensiteCreux = totalCreux > 0 ? 
        creux.reduce((sum, c) => sum + c.intensite, 0) / totalCreux : 0;
    
    let tendance = "neutre";
    if (pourcentagePresencePics > pourcentagePresenceCreux * 1.2) tendance = "piquante";
    else if (pourcentagePresenceCreux > pourcentagePresencePics * 1.2) tendance = "creusante";
    else {
        const totalEvents = totalPics + totalCreux;
        const pourcentagePics = totalEvents > 0 ? (totalPics / totalEvents) * 100 : 0;
        const pourcentageCreux = totalEvents > 0 ? (totalCreux / totalEvents) * 100 : 0;
        
        if (pourcentagePics >= 55) tendance = "piquante";
        else if (pourcentageCreux >= 55) tendance = "creusante";
    }
    
    const intensiteGlobale = `${pourcentagePresencePics.toFixed(1)}% piquant vs ${pourcentagePresenceCreux.toFixed(1)}% creux`;
    
    const ratioPicsCreux = totalCreux > 0 ? totalPics / totalCreux : totalPics;
    const variabiliteGlobale = totalPics + totalCreux > 0 ? 
        (moyenneHauteurPics + moyenneProfondeurCreux) / 2 : 0;
    
    const dernierEvenement = events.length > 0 ? events[events.length - 1] : null;
    
    const dernierePosition = events.length > 0 ? Math.max(...events.map(e => e.index)) : 0;
    const frequencePics = dernierePosition > 0 ? (totalPics / dernierePosition) * 100 : 0;
    const frequenceCreux = dernierePosition > 0 ? (totalCreux / dernierePosition) * 100 : 0;
    
    return {
        totalPics,
        totalCreux,
        totalPointsPics,
        totalPointsCreux,
        pourcentagePresencePics: parseFloat(pourcentagePresencePics.toFixed(2)),
        pourcentagePresenceCreux: parseFloat(pourcentagePresenceCreux.toFixed(2)),
        pourcentagePresenceGlobale: parseFloat(pourcentagePresenceGlobale.toFixed(2)),
        moyenneHauteurPics: parseFloat(moyenneHauteurPics.toFixed(2)),
        moyenneProfondeurCreux: parseFloat(moyenneProfondeurCreux.toFixed(2)),
        moyenneIntensitePics: parseFloat(moyenneIntensitePics.toFixed(2)),
        moyenneIntensiteCreux: parseFloat(moyenneIntensiteCreux.toFixed(2)),
        tendance,
        intensiteGlobale,
        ratioPicsCreux: parseFloat(ratioPicsCreux.toFixed(2)),
        variabiliteGlobale: parseFloat(variabiliteGlobale.toFixed(2)),
        dernierEvenement,
        frequencePics: parseFloat(frequencePics.toFixed(2)),
        frequenceCreux: parseFloat(frequenceCreux.toFixed(2)),
        pourcentagePics: parseFloat(pourcentagePresencePics.toFixed(1)),
        pourcentageCreux: parseFloat(pourcentagePresenceCreux.toFixed(1))
    };
}

// 🔥 FONCTIONS D'ANALYSE DES CHUTES ET MONTÉES AVEC SYSTÈME DE POINTS

/**
 * Détecte les chutes et montées progressives avec comptage de points cumulés
 */
function detectChutesMonteeProgressives(data, minLength = 3, minVariation = 1.0) {
    if (!data || data.length < minLength) return [];
    
    const events = [];
    let currentTrend = null;
    
    for (let i = 1; i < data.length; i++) {
        const prev = data[i - 1];
        const current = data[i];
        const direction = current < prev ? 'montee' : (current > prev ? 'chute' : 'stable');
        
        if (direction === 'stable') {
            if (currentTrend && currentTrend.length >= minLength) {
                const variation = calculateTrendVariation(data, currentTrend.startIndex, i - 1);
                if (Math.abs(variation) >= minVariation) {
                    events.push(finalizeTrend(data, currentTrend, i - 1, variation));
                }
            }
            currentTrend = null;
            continue;
        }
        
        if (!currentTrend) {
            currentTrend = {
                type: direction,
                startIndex: i - 1,
                length: 2,
                startValue: prev,
                currentValue: current
            };
        } else if (currentTrend.type === direction) {
            currentTrend.length++;
            currentTrend.currentValue = current;
        } else {
            if (currentTrend.length >= minLength) {
                const variation = calculateTrendVariation(data, currentTrend.startIndex, i - 1);
                if (Math.abs(variation) >= minVariation) {
                    events.push(finalizeTrend(data, currentTrend, i - 1, variation));
                }
            }
            
            currentTrend = {
                type: direction,
                startIndex: i - 1,
                length: 2,
                startValue: prev,
                currentValue: current
            };
        }
    }
    
    if (currentTrend && currentTrend.length >= minLength) {
        const variation = calculateTrendVariation(data, currentTrend.startIndex, data.length - 1);
        if (Math.abs(variation) >= minVariation) {
            events.push(finalizeTrend(data, currentTrend, data.length - 1, variation));
        }
    }
    
    return events;
}

/**
 * Calcule la variation d'une tendance en pourcentage
 */
function calculateTrendVariation(data, startIndex, endIndex) {
    const startValue = data[startIndex];
    const endValue = data[endIndex];
    
    if (startValue === 0) return 0;
    return ((endValue - startValue) / startValue) * 100;
}

/**
 * Finalise une tendance détectée avec comptage de points
 */
function finalizeTrend(data, trend, endIndex, variation) {
    const startValue = data[trend.startIndex];
    const endValue = data[endIndex];
    const length = endIndex - trend.startIndex + 1;
    
    // ✅ CORRECTION : Points cumulés = longueur de la tendance EXACTEMENT
    const pointsCount = length;
    
    const slope = (endValue - startValue) / length;
    const intensity = Math.abs(slope);
    
    let regularity = 0;
    if (length > 2) {
        let consistentDirections = 0;
        for (let i = trend.startIndex + 1; i <= endIndex; i++) {
            const currentDirection = data[i] > data[i - 1];
            const expectedDirection = trend.type === 'montee';
            if (currentDirection === expectedDirection) {
                consistentDirections++;
            }
        }
        regularity = (consistentDirections / (length - 1)) * 100;
    }
    
    return {
        type: trend.type,
        startIndex: trend.startIndex,
        endIndex: endIndex,
        startValue: startValue,
        endValue: endValue,
        length: length,
        pointsCount, // ✅ CORRECTION : Points cumulés de la tendance
        variation: parseFloat(variation.toFixed(2)),
        slope: parseFloat(slope.toFixed(4)),
        intensity: parseFloat(intensity.toFixed(4)),
        regularity: parseFloat(regularity.toFixed(2)),
        timestamp: Date.now() - (data.length - endIndex) * 100
    };
}

/**
 * Calcule l'analyse globale des chutes et montées avec pourcentages de présence
 */
function calculateChuteMonteeTrend(events, dataSize = 0) {
    if (!events || events.length === 0) {
        return {
            totalChutes: 0,
            totalMontees: 0,
            totalPointsChutes: 0,
            totalPointsMontees: 0,
            pourcentagePresenceChutes: 0,
            pourcentagePresenceMontees: 0,
            pourcentagePresenceGlobale: 0,
            moyenneLongueurChutes: 0,
            moyenneLongueurMontees: 0,
            moyenneVariationChutes: 0,
            moyenneVariationMontees: 0,
            moyenneIntensiteChutes: 0,
            moyenneIntensiteMontees: 0,
            moyenneRegulariteChutes: 0,
            moyenneRegulariteMontees: 0,
            tendanceGlobale: "neutre",
            ratioChutesVsMontees: 0,
            dureeMovementMoyenne: 0,
            dernierEvenement: null,
            pourcentageChutes: 0,
            pourcentageMontees: 0
        };
    }
    
    const chutes = events.filter(e => e.type === "chute");
    const montees = events.filter(e => e.type === "montee");
    
    const totalChutes = chutes.length;
    const totalMontees = montees.length;
    
    // ✅ CORRECTION : Points cumulés = somme des longueurs EXACTEMENT
    const totalPointsChutes = chutes.reduce((sum, c) => sum + (c.pointsCount || c.length), 0);
    const totalPointsMontees = montees.reduce((sum, m) => sum + (m.pointsCount || m.length), 0);
    const totalPointsGlobaux = totalPointsChutes + totalPointsMontees;
    
    const pourcentagePresenceChutes = dataSize > 0 ? (totalPointsChutes / dataSize) * 100 : 0;
    const pourcentagePresenceMontees = dataSize > 0 ? (totalPointsMontees / dataSize) * 100 : 0;
    const pourcentagePresenceGlobale = dataSize > 0 ? (totalPointsGlobaux / dataSize) * 100 : 0;
    
    const moyenneLongueurChutes = totalChutes > 0 ? 
        chutes.reduce((sum, c) => sum + c.length, 0) / totalChutes : 0;
    
    const moyenneVariationChutes = totalChutes > 0 ? 
        chutes.reduce((sum, c) => sum + Math.abs(c.variation), 0) / totalChutes : 0;
    
    const moyenneIntensiteChutes = totalChutes > 0 ? 
        chutes.reduce((sum, c) => sum + c.intensity, 0) / totalChutes : 0;
        
    const moyenneRegulariteChutes = totalChutes > 0 ? 
        chutes.reduce((sum, c) => sum + c.regularity, 0) / totalChutes : 0;
    
    const moyenneLongueurMontees = totalMontees > 0 ? 
        montees.reduce((sum, m) => sum + m.length, 0) / totalMontees : 0;
    
    const moyenneVariationMontees = totalMontees > 0 ? 
        montees.reduce((sum, m) => sum + Math.abs(m.variation), 0) / totalMontees : 0;
    
    const moyenneIntensiteMontees = totalMontees > 0 ? 
        montees.reduce((sum, m) => sum + m.intensity, 0) / totalMontees : 0;
        
    const moyenneRegulariteMontees = totalMontees > 0 ? 
        montees.reduce((sum, m) => sum + m.regularity, 0) / totalMontees : 0;
    
    let tendanceGlobale = "neutre";
    if (pourcentagePresenceChutes > pourcentagePresenceMontees * 1.2) tendanceGlobale = "baissière";
    else if (pourcentagePresenceMontees > pourcentagePresenceChutes * 1.2) tendanceGlobale = "haussière";
    else {
        const totalEvents = totalChutes + totalMontees;
        const pourcentageChutes = totalEvents > 0 ? (totalChutes / totalEvents) * 100 : 0;
        const pourcentageMontees = totalEvents > 0 ? (totalMontees / totalEvents) * 100 : 0;
        
        if (pourcentageChutes >= 55) tendanceGlobale = "baissière";
        else if (pourcentageMontees >= 55) tendanceGlobale = "haussière";
    }
    
    const ratioChutesVsMontees = totalMontees > 0 ? totalChutes / totalMontees : totalChutes;
    const dureeMovementMoyenne = totalChutes + totalMontees > 0 ? 
        (moyenneLongueurChutes * totalChutes + moyenneLongueurMontees * totalMontees) / (totalChutes + totalMontees) : 0;
    
    const dernierEvenement = events.length > 0 ? events[events.length - 1] : null;
    
    return {
        totalChutes,
        totalMontees,
        totalPointsChutes,
        totalPointsMontees,
        pourcentagePresenceChutes: parseFloat(pourcentagePresenceChutes.toFixed(2)),
        pourcentagePresenceMontees: parseFloat(pourcentagePresenceMontees.toFixed(2)),
        pourcentagePresenceGlobale: parseFloat(pourcentagePresenceGlobale.toFixed(2)),
        moyenneLongueurChutes: parseFloat(moyenneLongueurChutes.toFixed(2)),
        moyenneLongueurMontees: parseFloat(moyenneLongueurMontees.toFixed(2)),
        moyenneVariationChutes: parseFloat(moyenneVariationChutes.toFixed(2)),
        moyenneVariationMontees: parseFloat(moyenneVariationMontees.toFixed(2)),
        moyenneIntensiteChutes: parseFloat(moyenneIntensiteChutes.toFixed(4)),
        moyenneIntensiteMontees: parseFloat(moyenneIntensiteMontees.toFixed(4)),
        moyenneRegulariteChutes: parseFloat(moyenneRegulariteChutes.toFixed(2)),
        moyenneRegulariteMontees: parseFloat(moyenneRegulariteMontees.toFixed(2)),
        tendanceGlobale,
        ratioChutesVsMontees: parseFloat(ratioChutesVsMontees.toFixed(2)),
        dureeMovementMoyenne: parseFloat(dureeMovementMoyenne.toFixed(2)),
        dernierEvenement,
        pourcentageChutes: parseFloat(pourcentagePresenceChutes.toFixed(1)),
        pourcentageMontees: parseFloat(pourcentagePresenceMontees.toFixed(1))
    };
}

// FONCTIONS D'ANALYSE COMPLÈTES MISES À JOUR

/**
 * Analyse complète des plateaux pour toutes les ranges
 */
function analyzePlateauxForAllRanges(minPlateauLength = 1, maxVariation = 1.5, minStabilityDuration = 1) {
    const analysis = {};
    
    currentRanges.forEach(range => {
        const percentageHistory = rangePercentageHistory.get(range.name) || [];
        
        if (percentageHistory.length >= minPlateauLength) {
            const plateaux = detectPlateaux(percentageHistory, minPlateauLength, maxVariation, minStabilityDuration);
            
            const picsCreuxData = picsCreuxAnalysis.get(range.name);
            const chutesMonteeData = chutesMonteeAnalysis.get(range.name);
            const picsCreuxLegersData = picsCreuxLegersAnalysis.get(range.name);
            
            const picsCreux = picsCreuxData ? picsCreuxData.events || [] : [];
            const chutesMontees = chutesMonteeData ? chutesMonteeData.events || [] : [];
            const picsCreuxLegers = picsCreuxLegersData ? picsCreuxLegersData.events || [] : [];
            
            const globalTrend = calculatePlateauxGlobalTrend(plateaux, picsCreux, chutesMontees, picsCreuxLegers, percentageHistory.length);
            
            analysis[range.name] = {
                rangeName: range.name,
                rangeColor: range.color,
                rangeLimit: range.limit,
                plateaux: plateaux,
                globalTrend: globalTrend,
                dataSize: percentageHistory.length,
                lastUpdate: Date.now(),
                parameters: { minPlateauLength, maxVariation, minStabilityDuration }
            };
            
            plateauxAnalysis.set(range.name, analysis[range.name]);
        }
    });
    
    return analysis;
}

/**
 * Analyse complète des pics et creux légers pour toutes les ranges
 */
function analyzePicsCreuxLegersForAllRanges(minPlateauLength = 2, maxPlateauVariation = 2.0, minInitialChange = 1.0) {
    const analysis = {};
    
    currentRanges.forEach(range => {
        const percentageHistory = rangePercentageHistory.get(range.name) || [];
        
        if (percentageHistory.length >= 3) {
            const events = detectPicsCreuxLegers(percentageHistory, minPlateauLength, maxPlateauVariation, minInitialChange);
            const globalTrend = calculateGlobalPicsCreuxLegersTrend(events, percentageHistory.length);
            
            analysis[range.name] = {
                rangeName: range.name,
                rangeColor: range.color,
                rangeLimit: range.limit,
                events: events,
                globalTrend: globalTrend,
                dataSize: percentageHistory.length,
                lastUpdate: Date.now(),
                parameters: { minPlateauLength, maxPlateauVariation, minInitialChange }
            };
            
            picsCreuxLegersAnalysis.set(range.name, analysis[range.name]);
        }
    });
    
    return analysis;
}

/**
 * Analyse complète des chutes et montées pour toutes les ranges
 */
function analyzeChutesMonteeForAllRanges(minLength = 3, minVariation = 1.0) {
    const analysis = {};
    
    currentRanges.forEach(range => {
        const percentageHistory = rangePercentageHistory.get(range.name) || [];
        
        if (percentageHistory.length >= minLength) {
            const events = detectChutesMonteeProgressives(percentageHistory, minLength, minVariation);
            const globalTrend = calculateChuteMonteeTrend(events, percentageHistory.length);
            
            analysis[range.name] = {
                rangeName: range.name,
                rangeColor: range.color,
                rangeLimit: range.limit,
                events: events,
                globalTrend: globalTrend,
                dataSize: percentageHistory.length,
                lastUpdate: Date.now(),
                parameters: { minLength, minVariation }
            };
            
            chutesMonteeAnalysis.set(range.name, analysis[range.name]);
        }
    });
    
    return analysis;
}

/**
 * Analyse complète des pics et creux pour toutes les ranges
 */
function analyzePicsCreuxForAllRanges(minSensitivity = 0.5) {
    const analysis = {};
    
    currentRanges.forEach(range => {
        const percentageHistory = rangePercentageHistory.get(range.name) || [];
        
        if (percentageHistory.length >= 3) {
            const events = detectPicsCreux(percentageHistory, minSensitivity);
            const globalTrend = calculateGlobalTrend(events, percentageHistory.length);
            
            analysis[range.name] = {
                rangeName: range.name,
                rangeColor: range.color,
                rangeLimit: range.limit,
                events: events,
                globalTrend: globalTrend,
                dataSize: percentageHistory.length,
                lastUpdate: Date.now()
            };
            
            picsCreuxAnalysis.set(range.name, analysis[range.name]);
        }
    });
    
    return analysis;
}

// 🌡️ FONCTION MISE À JOUR POUR LE THERMOMÈTRE DE SITUATION AVEC STABILITÉ

/**
 * 🔧 FONCTION CORRIGÉE : Analyse complète du thermomètre de situation pour toutes les ranges avec stabilité
 */
function analyzeThermometreForAllRanges() {
    const analysis = {};
    
    currentRanges.forEach(range => {
        // Récupérer les analyses existantes
        const picsCreuxData = picsCreuxAnalysis.get(range.name);
        const chutesMonteeData = chutesMonteeAnalysis.get(range.name);
        const picsCreuxLegersData = picsCreuxLegersAnalysis.get(range.name);
        const plateauxData = plateauxAnalysis.get(range.name);
        
        const picsCreuxEvents = picsCreuxData ? picsCreuxData.events || [] : [];
        const chutesMonteeEvents = chutesMonteeData ? chutesMonteeData.events || [] : [];
        const picsCreuxLegersEvents = picsCreuxLegersData ? picsCreuxLegersData.events || [] : [];
        const plateauxEvents = plateauxData ? plateauxData.plateaux || [] : [];
        
        // ✅ CORRECTION : Mettre à jour le thermomètre avec toutes les analyses incluant la stabilité
        const zoneData = updateThermometreForRange(
            range.name, 
            picsCreuxEvents, 
            chutesMonteeEvents, 
            picsCreuxLegersEvents, 
            plateauxEvents
        );
        
        if (zoneData) {
            analysis[range.name] = {
                rangeName: range.name,
                rangeColor: range.color,
                rangeLimit: range.limit,
                zoneData: zoneData,
                lastUpdate: Date.now()
            };
        }
    });
    
    return analysis;
}

// FONCTIONS DE RÉSUMÉ GLOBAL MISES À JOUR

/**
 * Obtient un résumé global de toutes les analyses de plateaux
 */
function getGlobalPlateauxSummary() {
    const allAnalyses = Array.from(plateauxAnalysis.values());
    
    if (allAnalyses.length === 0) {
        return {
            totalRanges: 0,
            rangeMostStable: null,
            tendanceGlobaleGenerale: "inconnue",
            moyenneStabiliteGlobale: 0,
            totalPlateaux: 0,
            totalPointsPlateauxGlobal: 0,
            pourcentagePresenceGlobale: 0,
            ratioStabiliteVsDynamisme: 0,
            typeActiviteDominanteGlobale: "inconnue",
            pourcentageTempsEnPlateauGlobal: 0,
            repartitionTendancesGlobales: {}
        };
    }
    
    const totalPlateaux = allAnalyses.reduce((sum, analysis) => sum + analysis.globalTrend.totalPlateaux, 0);
    const totalPointsPlateauxGlobal = allAnalyses.reduce((sum, analysis) => sum + analysis.globalTrend.totalPointsPlateaux, 0);
    const totalDataSize = allAnalyses.reduce((sum, a) => sum + a.dataSize, 0);
    const pourcentagePresenceGlobale = totalDataSize > 0 ? (totalPointsPlateauxGlobal / totalDataSize) * 100 : 0;
    
    const rangeMostStable = allAnalyses.reduce((most, current) => {
        const currentStability = current.globalTrend.pourcentagePresencePlateaux;
        const mostStability = most ? most.globalTrend.pourcentagePresencePlateaux : 0;
        return currentStability > mostStability ? current : most;
    }, null);
    
    const moyenneStabiliteGlobale = allAnalyses.length > 0 ? 
        allAnalyses.reduce((sum, a) => sum + a.globalTrend.stabiliteGlobale, 0) / allAnalyses.length : 0;
    
    const typesActivite = allAnalyses.map(a => a.globalTrend.typeActiviteDominante);
    const stabiliteCount = typesActivite.filter(t => t === "stabilité-dominante").length;
    const dynamiqueCount = allAnalyses.length - stabiliteCount;
    
    const ratioStabiliteVsDynamisme = dynamiqueCount > 0 ? stabiliteCount / dynamiqueCount : stabiliteCount;
    
    let tendanceGlobaleGenerale = "équilibrée";
    if (pourcentagePresenceGlobale >= 60) tendanceGlobaleGenerale = "globalement-stable";
    else if (pourcentagePresenceGlobale >= 40) tendanceGlobaleGenerale = "plutôt-stable";
    else if (pourcentagePresenceGlobale >= 20) tendanceGlobaleGenerale = "modérément-dynamique";
    else tendanceGlobaleGenerale = "très-dynamique";
    
    let typeActiviteDominanteGlobale = "équilibrée";
    if (stabiliteCount > dynamiqueCount) typeActiviteDominanteGlobale = "stabilité-dominante";
    else if (dynamiqueCount > stabiliteCount) typeActiviteDominanteGlobale = "dynamisme-dominant";
    
    const repartitionTendancesGlobales = {
        stabilite_dominante: stabiliteCount,
        dynamisme_dominant: dynamiqueCount,
        pourcentage_stabilite: allAnalyses.length > 0 ? (stabiliteCount / allAnalyses.length) * 100 : 0,
        pourcentage_dynamisme: allAnalyses.length > 0 ? (dynamiqueCount / allAnalyses.length) * 100 : 0
    };
    
    const totalTempsEnPlateau = allAnalyses.reduce((sum, a) => 
        sum + (a.globalTrend.pourcentageTempsEnPlateau * a.dataSize / 100), 0);
    const pourcentageTempsEnPlateauGlobal = totalDataSize > 0 ? (totalTempsEnPlateau / totalDataSize) * 100 : 0;
    
    return {
        totalRanges: allAnalyses.length,
        rangeMostStable: rangeMostStable ? {
            name: rangeMostStable.rangeName,
            stabilite: rangeMostStable.globalTrend.pourcentagePresencePlateaux,
            typeActivite: rangeMostStable.globalTrend.typeActiviteDominante
        } : null,
        tendanceGlobaleGenerale,
        moyenneStabiliteGlobale: parseFloat(moyenneStabiliteGlobale.toFixed(2)),
        totalPlateaux,
        totalPointsPlateauxGlobal,
        pourcentagePresenceGlobale: parseFloat(pourcentagePresenceGlobale.toFixed(2)),
        ratioStabiliteVsDynamisme: parseFloat(ratioStabiliteVsDynamisme.toFixed(2)),
        typeActiviteDominanteGlobale,
        pourcentageTempsEnPlateauGlobal: parseFloat(pourcentageTempsEnPlateauGlobal.toFixed(2)),
        repartitionTendancesGlobales
    };
}

/**
 * Obtient un résumé global de toutes les analyses de pics et creux légers
 */
function getGlobalPicsCreuxLegersSummary() {
    const allAnalyses = Array.from(picsCreuxLegersAnalysis.values());
    
    if (allAnalyses.length === 0) {
        return {
            totalRanges: 0,
            rangeMostActive: null,
            tendanceGlobale: "neutre",
            moyenneStabilite: 0,
            totalEvents: 0,
            totalPointsGlobal: 0,
            pourcentagePresenceGlobale: 0,
            ratioGlobalPicsCreuxLegers: 0,
            moyenneDureePlateauxGlobale: 0,
            moyenneChangeAtoBGlobale: 0
        };
    }
    
    const totalEvents = allAnalyses.reduce((sum, analysis) => 
        sum + analysis.globalTrend.totalPicsLegers + analysis.globalTrend.totalCreuxLegers, 0);
    
    const totalPointsGlobal = allAnalyses.reduce((sum, analysis) => 
        sum + analysis.globalTrend.totalPointsPicsLegers + analysis.globalTrend.totalPointsCreuxLegers, 0);
    
    const totalDataSize = allAnalyses.reduce((sum, a) => sum + a.dataSize, 0);
    const pourcentagePresenceGlobale = totalDataSize > 0 ? (totalPointsGlobal / totalDataSize) * 100 : 0;
    
    const rangeMostActive = allAnalyses.reduce((most, current) => {
        const currentPresence = current.globalTrend.pourcentagePresenceGlobale;
        const mostPresence = most ? most.globalTrend.pourcentagePresenceGlobale : 0;
        return currentPresence > mostPresence ? current : most;
    }, null);
    
    const moyenneStabilite = allAnalyses.length > 0 ? 
        allAnalyses.reduce((sum, a) => sum + a.globalTrend.stabiliteGlobale, 0) / allAnalyses.length : 0;
    
    const totalPicsLegers = allAnalyses.reduce((sum, a) => sum + a.globalTrend.totalPicsLegers, 0);
    const totalCreuxLegers = allAnalyses.reduce((sum, a) => sum + a.globalTrend.totalCreuxLegers, 0);
    const ratioGlobalPicsCreuxLegers = totalCreuxLegers > 0 ? totalPicsLegers / totalCreuxLegers : totalPicsLegers;
    
    const moyenneDureePlateauxGlobale = allAnalyses.length > 0 ? 
        allAnalyses.reduce((sum, a) => sum + a.globalTrend.moyenneDureePlateaux, 0) / allAnalyses.length : 0;
    
    const moyenneChangeAtoBGlobale = allAnalyses.length > 0 ? 
        allAnalyses.reduce((sum, a) => sum + a.globalTrend.moyenneChangeAtoB, 0) / allAnalyses.length : 0;
    
    const tendances = allAnalyses.map(a => a.globalTrend.tendance);
    const picsLegersCount = tendances.filter(t => t === "pics-legers-dominants").length;
    const creuxLegersCount = tendances.filter(t => t === "creux-legers-dominants").length;
    
    let tendanceGlobale = "neutre";
    if (picsLegersCount > creuxLegersCount) tendanceGlobale = "pics-legers-dominants";
    else if (creuxLegersCount > picsLegersCount) tendanceGlobale = "creux-legers-dominants";
    
    return {
        totalRanges: allAnalyses.length,
        rangeMostActive: rangeMostActive ? {
            name: rangeMostActive.rangeName,
            events: rangeMostActive.globalTrend.totalPicsLegers + rangeMostActive.globalTrend.totalCreuxLegers,
            tendance: rangeMostActive.globalTrend.tendance,
            presencePercentage: rangeMostActive.globalTrend.pourcentagePresenceGlobale
        } : null,
        tendanceGlobale,
        moyenneStabilite: parseFloat(moyenneStabilite.toFixed(2)),
        totalEvents,
        totalPointsGlobal,
        pourcentagePresenceGlobale: parseFloat(pourcentagePresenceGlobale.toFixed(2)),
        ratioGlobalPicsCreuxLegers: parseFloat(ratioGlobalPicsCreuxLegers.toFixed(2)),
        moyenneDureePlateauxGlobale: parseFloat(moyenneDureePlateauxGlobale.toFixed(2)),
        moyenneChangeAtoBGlobale: parseFloat(moyenneChangeAtoBGlobale.toFixed(2)),
        repartitionTendances: {
            picsLegersDomine: picsLegersCount,
            creuxLegersDomine: creuxLegersCount,
            neutre: allAnalyses.length - picsLegersCount - creuxLegersCount
        },
        totalPicsLegers,
        totalCreuxLegers
    };
}

/**
 * Obtient un résumé global de toutes les analyses de chutes/montées
 */
function getGlobalChuteMonteeSummary() {
    const allAnalyses = Array.from(chutesMonteeAnalysis.values());
    
    if (allAnalyses.length === 0) {
        return {
            totalRanges: 0,
            rangeMostActive: null,
            tendanceGlobale: "neutre",
            moyenneDureeMovement: 0,
            totalEvents: 0,
            totalPointsGlobal: 0,
            pourcentagePresenceGlobale: 0,
            ratioGlobalChutesVsMontees: 0
        };
    }
    
    const totalEvents = allAnalyses.reduce((sum, analysis) => 
        sum + analysis.globalTrend.totalChutes + analysis.globalTrend.totalMontees, 0);
    
    const totalPointsGlobal = allAnalyses.reduce((sum, analysis) => 
        sum + analysis.globalTrend.totalPointsChutes + analysis.globalTrend.totalPointsMontees, 0);
    
    const totalDataSize = allAnalyses.reduce((sum, a) => sum + a.dataSize, 0);
    const pourcentagePresenceGlobale = totalDataSize > 0 ? (totalPointsGlobal / totalDataSize) * 100 : 0;
    
    const rangeMostActive = allAnalyses.reduce((most, current) => {
        const currentPresence = current.globalTrend.pourcentagePresenceGlobale;
        const mostPresence = most ? most.globalTrend.pourcentagePresenceGlobale : 0;
        return currentPresence > mostPresence ? current : most;
    }, null);
    
    const moyenneDureeMovement = allAnalyses.length > 0 ? 
        allAnalyses.reduce((sum, a) => sum + a.globalTrend.dureeMovementMoyenne, 0) / allAnalyses.length : 0;
    
    const totalChutes = allAnalyses.reduce((sum, a) => sum + a.globalTrend.totalChutes, 0);
    const totalMontees = allAnalyses.reduce((sum, a) => sum + a.globalTrend.totalMontees, 0);
    const ratioGlobalChutesVsMontees = totalMontees > 0 ? totalChutes / totalMontees : totalChutes;
    
    const tendances = allAnalyses.map(a => a.globalTrend.tendanceGlobale);
    const baissiereCount = tendances.filter(t => t === "baissière").length;
    const haussiereCount = tendances.filter(t => t === "haussière").length;
    
    let tendanceGlobale = "neutre";
    if (baissiereCount > haussiereCount) tendanceGlobale = "baissière";
    else if (haussiereCount > baissiereCount) tendanceGlobale = "haussière";
    
    return {
        totalRanges: allAnalyses.length,
        rangeMostActive: rangeMostActive ? {
            name: rangeMostActive.rangeName,
            events: rangeMostActive.globalTrend.totalChutes + rangeMostActive.globalTrend.totalMontees,
            tendance: rangeMostActive.globalTrend.tendanceGlobale,
            presencePercentage: rangeMostActive.globalTrend.pourcentagePresenceGlobale
        } : null,
        tendanceGlobale,
        moyenneDureeMovement: parseFloat(moyenneDureeMovement.toFixed(2)),
        totalEvents,
        totalPointsGlobal,
        pourcentagePresenceGlobale: parseFloat(pourcentagePresenceGlobale.toFixed(2)),
        ratioGlobalChutesVsMontees: parseFloat(ratioGlobalChutesVsMontees.toFixed(2)),
        repartitionTendances: {
            baissiere: baissiereCount,
            haussiere: haussiereCount,
            neutre: allAnalyses.length - baissiereCount - haussiereCount
        },
        totalChutes,
        totalMontees
    };
}

/**
 * Obtient un résumé global de toutes les analyses pics et creux classiques
 */
function getGlobalPicsCreuxSummary() {
    const allAnalyses = Array.from(picsCreuxAnalysis.values());
    
    if (allAnalyses.length === 0) {
        return {
            totalRanges: 0,
            rangeMostActive: null,
            tendanceGlobale: "neutre",
            moyenneVariabilite: 0,
            totalEvents: 0,
            totalPointsGlobal: 0,
            pourcentagePresenceGlobale: 0
        };
    }
    
    const totalEvents = allAnalyses.reduce((sum, analysis) => 
        sum + analysis.globalTrend.totalPics + analysis.globalTrend.totalCreux, 0);
    
    const totalPointsGlobal = allAnalyses.reduce((sum, analysis) => 
        sum + analysis.globalTrend.totalPointsPics + analysis.globalTrend.totalPointsCreux, 0);
    
    const totalDataSize = allAnalyses.reduce((sum, a) => sum + a.dataSize, 0);
    const pourcentagePresenceGlobale = totalDataSize > 0 ? (totalPointsGlobal / totalDataSize) * 100 : 0;
    
    const rangeMostActive = allAnalyses.reduce((most, current) => {
        const currentPresence = current.globalTrend.pourcentagePresenceGlobale;
        const mostPresence = most ? most.globalTrend.pourcentagePresenceGlobale : 0;
        return currentPresence > mostPresence ? current : most;
    }, null);
    
    const moyenneVariabilite = allAnalyses.length > 0 ? 
        allAnalyses.reduce((sum, a) => sum + a.globalTrend.variabiliteGlobale, 0) / allAnalyses.length : 0;
    
    const tendances = allAnalyses.map(a => a.globalTrend.tendance);
    const piquanteCount = tendances.filter(t => t === "piquante").length;
    const creusanteCount = tendances.filter(t => t === "creusante").length;
    
    let tendanceGlobale = "neutre";
    if (piquanteCount > creusanteCount) tendanceGlobale = "piquante";
    else if (creusanteCount > piquanteCount) tendanceGlobale = "creusante";
    
    return {
        totalRanges: allAnalyses.length,
        rangeMostActive: rangeMostActive ? {
            name: rangeMostActive.rangeName,
            events: rangeMostActive.globalTrend.totalPics + rangeMostActive.globalTrend.totalCreux,
            tendance: rangeMostActive.globalTrend.tendance,
            presencePercentage: rangeMostActive.globalTrend.pourcentagePresenceGlobale
        } : null,
        tendanceGlobale,
        moyenneVariabilite: parseFloat(moyenneVariabilite.toFixed(2)),
        totalEvents,
        totalPointsGlobal,
        pourcentagePresenceGlobale: parseFloat(pourcentagePresenceGlobale.toFixed(2)),
        repartitionTendances: {
            piquante: piquanteCount,
            creusante: creusanteCount,
            neutre: allAnalyses.length - piquanteCount - creusanteCount
        }
    };
}

// FONCTION POUR REDÉMARRER AUTOMATIQUEMENT LE CŒUR DU SERVEUR
function restartServerCore() {
    try {
        console.log('🔄 REDÉMARRAGE AUTOMATIQUE DU CŒUR SERVEUR...');
        
        stopPolling();
        
        wsConnection = null;
        currentToken = null;
        tokenExpireTime = null;
        currentCoefficient = null;
        
        pendingValues = [];
        crashHistory = [];
        
        if (tokenRefreshInterval) {
            clearTimeout(tokenRefreshInterval);
            tokenRefreshInterval = null;
        }
        
        if (restartTimeout) {
            clearTimeout(restartTimeout);
            restartTimeout = null;
        }
        
        console.log('🧹 Nettoyage terminé, redémarrage des connexions...');
        
        setTimeout(async () => {
            try {
                console.log('🔐 Récupération des informations utilisateur...');
                await fetchUserAuth();
                
                console.log('🔑 Récupération d\'un nouveau token...');
                const tokenSuccess = await refreshToken();
                
                if (tokenSuccess && isPolling) {
                    console.log('✅ Token récupéré, redémarrage des connexions...');
                    startWebSocketConnection();
                    startDataSender();
                } else if (!tokenSuccess) {
                    console.log('❌ Échec de récupération du token, nouvelle tentative dans 10 secondes...');
                    restartTimeout = setTimeout(restartServerCore, 10000);
                }
                
                console.log('✅ REDÉMARRAGE AUTOMATIQUE TERMINÉ');
            } catch (error) {
                console.error('❌ Erreur lors du redémarrage automatique:', error);
                restartTimeout = setTimeout(restartServerCore, 15000);
            }
        }, 2000);
        
    } catch (error) {
        console.error('❌ Erreur critique lors du redémarrage:', error);
        restartTimeout = setTimeout(restartServerCore, 20000);
    }
}

// Récupérer les informations utilisateur
async function fetchUserAuth() {
    try {
        console.log('🔐 Récupération des informations utilisateur...');
        
        const response = await axios.post(USER_AUTH_URL, null, {
            headers: {
                "accept": "application/json, text/plain, */*",
                "accept-language": "en-US,en;q=0.9,fr-CI;q=0.8,fr;q=0.7",
                "auth-token": authToken,
                "sec-ch-ua": "\"Not-A.Brand\";v=\"99\", \"Chromium\";v=\"124\"",
                "sec-ch-ua-mobile": "?1",
                "sec-ch-ua-platform": "\"Android\"",
                "sec-fetch-dest": "empty",
                "sec-fetch-mode": "cors",
                "sec-fetch-site": "cross-site",
                "Referer": "https://1play.gamedev-tech.cc/",
                "Referrer-Policy": "strict-origin-when-cross-origin"
            }
        });

        if (response.data) {
            userInfo = {
                userId: response.data.userId || userInfo.userId,
                userName: response.data.userName || userInfo.userName,
                sessionId: response.data.sessionId || userInfo.sessionId,
                customerId: response.data.customerId || userInfo.customerId,
                balance: response.data.balance || 0
            };
            
            console.log('✅ Informations utilisateur récupérées:');
            console.log(`   - Nom: ${userInfo.userName}`);
            console.log(`   - ID: ${userInfo.userId}`);
            console.log(`   - Session: ${userInfo.sessionId}`);
            console.log(`   - Customer: ${userInfo.customerId}`);
            console.log(`   - Solde: ${userInfo.balance}`);
            
            return true;
        } else {
            throw new Error('Réponse invalide de l\'API d\'authentification');
        }
    } catch (error) {
        console.error('❌ Erreur lors de la récupération des informations utilisateur:', error.message);
        return false;
    }
}

// Fonction pour sauvegarder la configuration
async function saveConfig() {
    try {
        config.isPolling = isPolling;
        config.pollingFrequency = pollingFrequency;
        config.historySize = historySize;
        config.customSizes = customSizes;
        config.users = users;
        config.ranges = currentRanges;
        config.medianHistory = medianHistory;
        config.meanHistory = meanHistory;
        config.authToken = authToken;
        
        await fs.writeFile(CONFIG_FILE, JSON.stringify(config, null, 2), 'utf8');
        console.log('Configuration sauvegardée avec customSizes:', customSizes);
        console.log('Historiques sauvegardés - Médiane:', medianHistory.length, 'Moyenne:', meanHistory.length);
    } catch (error) {
        console.error('Erreur lors de la sauvegarde:', error);
    }
}

// Fonction pour charger la configuration
async function loadConfig() {
    try {
        if (fsSync.existsSync(CONFIG_FILE)) {
            const data = await fs.readFile(CONFIG_FILE, 'utf8');
            const loadedConfig = JSON.parse(data);
            
            isPolling = loadedConfig.isPolling || false;
            pollingFrequency = loadedConfig.pollingFrequency || 1000;
            historySize = loadedConfig.historySize || 100;
            customSizes = loadedConfig.customSizes || { median: 50, mean: 100 };
            users = loadedConfig.users || {"admin": "password"};
            currentRanges = loadedConfig.ranges || currentRanges;
            medianHistory = loadedConfig.medianHistory || [];
            meanHistory = loadedConfig.meanHistory || [];
            authToken = loadedConfig.authToken || DEFAULT_AUTH_TOKEN;
            
            config = loadedConfig;
            console.log('Configuration chargée avec customSizes:', customSizes);
            console.log('Historiques chargés - Médiane:', medianHistory.length, 'Moyenne:', meanHistory.length);
            
            if (isPolling) {
                startPolling();
            }
        }
    } catch (error) {
        console.error('Erreur lors du chargement de la configuration:', error);
    }
}

// Fonction pour récupérer un nouveau token
async function refreshToken() {
    try {
        console.log('🔄 Récupération d\'un nouveau token...');
        
        const response = await axios.post(TOKEN_REFRESH_URL, null, {
            headers: {
                "accept": "application/json, text/plain, */*",
                "accept-language": "en-US,en;q=0.9,fr-CI;q=0.8,fr;q=0.7",
                "customer-id": userInfo.customerId,
                "sec-ch-ua": "\"Not-A.Brand\";v=\"99\", \"Chromium\";v=\"124\"",
                "sec-ch-ua-mobile": "?1",
                "sec-ch-ua-platform": "\"Android\"",
                "sec-fetch-dest": "empty",
                "sec-fetch-mode": "cors",
                "sec-fetch-site": "cross-site",
                "session-id": userInfo.sessionId,
                "Referer": "https://1play.gamedev-tech.cc/",
                "Referrer-Policy": "strict-origin-when-cross-origin"
            }
        });

        if (response.data && response.data.centrifugo && response.data.centrifugo.mainToken) {
            currentToken = response.data.centrifugo.mainToken;
            
            try {
                const payload = JSON.parse(atob(currentToken.split('.')[1]));
                tokenExpireTime = payload.exp * 1000;
                
                console.log('✅ Nouveau mainToken récupéré avec succès');
                console.log(`📅 Token expire le: ${new Date(tokenExpireTime).toLocaleString()}`);
                
                console.log('🔍 Informations du token:');
                console.log(`   - Sujet: ${payload.sub}`);
                console.log(`   - Channels: ${JSON.stringify(payload.channels)}`);
                console.log(`   - Émis le: ${new Date(payload.iat * 1000).toLocaleString()}`);
                
            } catch (e) {
                tokenExpireTime = Date.now() + (60 * 60 * 1000);
                console.log('⚠️  Impossible de décoder le token, utilisation d\'une expiration par défaut');
            }
            
            const refreshTime = tokenExpireTime - Date.now() - (30 * 60 * 1000);
            if (tokenRefreshInterval) clearTimeout(tokenRefreshInterval);
            
            tokenRefreshInterval = setTimeout(() => {
                refreshToken();
            }, Math.max(refreshTime, 60000));
            
            console.log(`⏰ Prochain rafraîchissement dans: ${Math.round(refreshTime / (60 * 1000))} minutes`);
            
            return true;
        } else {
            throw new Error('Structure de réponse invalide - mainToken non trouvé dans centrifugo');
        }
    } catch (error) {
        console.error('❌ Erreur lors de la récupération du token:', error.message);
        
        if (tokenRefreshInterval) clearTimeout(tokenRefreshInterval);
        tokenRefreshInterval = setTimeout(() => {
            refreshToken();
        }, 5 * 60 * 1000);
        
        return false;
    }
}

// Fonction pour traiter les messages WebSocket
function onWebSocketMessage(data) {
    try {
        if (!data || data.toString().trim() === '' || data.toString().trim() === '{}') {
            if (wsConnection && wsConnection.readyState === WebSocket.OPEN) {
                wsConnection.send('{}');
                console.log('🔄 Réponse envoyée au message vide');
            }
            return;
        }
        
        const cleanMessage = data.toString().replace(/[\x1e\n\r]/g, '').trim();
        if (!cleanMessage) return;
        
        let parsedData;
        try {
            parsedData = JSON.parse(cleanMessage);
        } catch (e) {
            return;
        }
        
        const coefficientData = findCoefficientChange(parsedData);
        if (coefficientData && coefficientData.current && Array.isArray(coefficientData.current) && coefficientData.current.length > 0) {
            currentCoefficient = coefficientData.current[0];
            
            io.emit('coefficientUpdate', {
                type: 'coefficientUpdate',
                coefficient: currentCoefficient,
                timestamp: Date.now()
            });
        }
        
        const finalCoeffValues = findFinalCoefficientValues(parsedData);
        
        if (finalCoeffValues && Array.isArray(finalCoeffValues) && finalCoeffValues.length > 0) {
            const fValue = finalCoeffValues[0];
            if (typeof fValue === 'number' && fValue > 0) {
                console.log(`🎯 finalCoefficientValues trouvé: ${fValue} ✅ CAPTURÉE`);
                bufferDataForSending(fValue, "finalCoefficientValues");
            }
        }
        
    } catch (error) {
        console.error('❌ Erreur lors du traitement du message:', error);
    }
}

// Rechercher les changements de coefficient
function findCoefficientChange(obj) {
    if (typeof obj === 'object' && obj !== null) {
        if (Array.isArray(obj)) {
            for (const item of obj) {
                const result = findCoefficientChange(item);
                if (result !== null) return result;
            }
        } else {
            if (obj.eventType === "changeCoefficient" && obj.current) {
                return obj;
            }
            
            for (const key of ['push', 'pub', 'data', 'payload', 'result', 'content']) {
                if (key in obj) {
                    const result = findCoefficientChange(obj[key]);
                    if (result !== null) return result;
                }
            }
            
            for (const value of Object.values(obj)) {
                const result = findCoefficientChange(value);
                if (result !== null) return result;
            }
        }
    }
    return null;
}

// Rechercher finalCoefficientValues
function findFinalCoefficientValues(obj) {
    if (typeof obj === 'object' && obj !== null) {
        if (Array.isArray(obj)) {
            for (const item of obj) {
                const result = findFinalCoefficientValues(item);
                if (result !== null) return result;
            }
        } else {
            if ('finalCoefficientValues' in obj) {
                return obj.finalCoefficientValues;
            }
            
            for (const key of ['push', 'pub', 'data', 'payload', 'result', 'content']) {
                if (key in obj) {
                    const result = findFinalCoefficientValues(obj[key]);
                    if (result !== null) return result;
                }
            }
            
            for (const value of Object.values(obj)) {
                const result = findFinalCoefficientValues(value);
                if (result !== null) return result;
            }
        }
    }
    return null;
}

function initializeRangePercentageHistory(rangeName, limit) {
    if (!rangePercentageHistory.has(rangeName)) {
        rangePercentageHistory.set(rangeName, []);
    }
    
    // 🎯 Initialiser le système prédictif
    initializePredictiveSystem(rangeName);
}

// FONCTION CORRIGÉE - Utilise maintenant les limites spécifiques de chaque range ET met à jour le classement et prédictions
function updateRangePercentages() {
    try {
        if (crashHistory.length === 0) return;

        currentRanges.forEach(range => {
            initializeRangePercentageHistory(range.name, range.limit);

            const limit = range.limit || 1000;
            const rangeHistory = crashHistory.slice(0, Math.min(limit, crashHistory.length));
            const totalCount = rangeHistory.length;

            let count = 0;
            for (const value of rangeHistory) {
                if (range.min !== null && value < range.min) continue;
                if (range.max !== null && value > range.max) continue;
                count++;
            }

            const percentage = totalCount > 0 ? (count / totalCount) * 100 : 0;
            let percentageHistory = rangePercentageHistory.get(range.name);
            
            percentageHistory.unshift(percentage);

            if (percentageHistory.length > limit) {
                percentageHistory = percentageHistory.slice(0, limit);
                rangePercentageHistory.set(range.name, percentageHistory);
            }

            const averagePercentage = calculateMean(percentageHistory);
            
            const difference = percentage - averagePercentage;

            console.log(`📈 ${range.name}: ${percentage.toFixed(2)}% (Moy: ${averagePercentage.toFixed(2)}%, Diff: ${difference >= 0 ? '+' : ''}${difference.toFixed(2)}%) [Limite: ${limit}, Taille échantillon: ${totalCount}]`);
            
            // 🆕 NOUVEAU : Mise à jour du classement des pourcentages et prédictions
            updatePercentageRanking(range.name);
        });

        // 🔍 ANALYSES AUTOMATIQUES AVEC SYSTÈME DE POINTS CORRIGÉ
        analyzePicsCreuxForAllRanges(0.5);
        analyzeChutesMonteeForAllRanges(3, 1.0);
        analyzePicsCreuxLegersForAllRanges(2, 2.0, 1.0);
        analyzePlateauxForAllRanges(2, 1.5, 2);
        
        // 🌡️ NOUVEAU : Analyse du thermomètre de situation CORRIGÉE AVEC STABILITÉ
        analyzeThermometreForAllRanges();
        
    } catch (error) {
        console.error('❌ Erreur calcul pourcentages:', error);
    }
}

// Mise à jour des historiques de médiane et moyenne
function updateMedianMeanHistories() {
    try {
        if (crashHistory.length === 0) return;

        const currentMedian = calculateMedian(crashHistory.slice(0, customSizes.median));
        medianHistory.unshift(currentMedian);
        
        if (medianHistory.length > customSizes.median) {
            medianHistory = medianHistory.slice(0, customSizes.median);
        }

        const currentMean = calculateMean(crashHistory.slice(0, customSizes.mean));
        meanHistory.unshift(currentMean);
        
        if (meanHistory.length > customSizes.mean) {
            meanHistory = meanHistory.slice(0, customSizes.mean);
        }

        console.log(`📊 Médiane actuelle: ${currentMedian.toFixed(3)} (historique: ${medianHistory.length})`);
        console.log(`📊 Moyenne actuelle: ${currentMean.toFixed(3)} (historique: ${meanHistory.length})`);
        
        const medianOfMedians = calculateMean(medianHistory);
        const meanOfMeans = calculateMean(meanHistory);
        
        console.log(`🔢 Moyenne des médianes: ${medianOfMedians.toFixed(3)}`);
        console.log(`🔢 Moyenne des moyennes: ${meanOfMeans.toFixed(3)}`);
        
    } catch (error) {
        console.error('❌ Erreur mise à jour historiques médiane/moyenne:', error);
    }
}

function bufferDataForSending(fValue, target = null) {
    try {
        pendingValues.push({
            value: fValue,
            target: target,
            timestamp: Date.now()
        });
        
        crashHistory.unshift(fValue);
        crashHistory = crashHistory.slice(0, historySize);
        
        updateRangePercentages();
        
        updateMedianMeanHistories();
        
        console.log(`📊 Valeur f=${fValue} ajoutée au buffer (Total: ${pendingValues.length})`);
    } catch (error) {
        console.error('❌ Erreur buffer:', error);
    }
}

function startDataSender() {
    if (dataSendActive) return;
    
    dataSendActive = true;
    dataSenderInterval = setInterval(() => {
        if (!dataSendActive) return;
        
        if (pendingValues.length > 0) {
            const valuesToSend = [...pendingValues];
            pendingValues = [];
            
            const newValues = valuesToSend.map(item => item.value);
            
            const rangePercentageData = {};
            currentRanges.forEach(range => {
                const percentageHistory = rangePercentageHistory.get(range.name) || [];
                const averagePercentage = calculateMean(percentageHistory);
                const currentPercentage = percentageHistory[0] || 0;
                const difference = currentPercentage - averagePercentage;
                
                rangePercentageData[range.name] = {
                    currentPercentage: currentPercentage,
                    history: percentageHistory.slice(0, 10),
                    averagePercentage: averagePercentage,
                    difference: difference,
                    percentageHistory: percentageHistory.slice(0, 50),
                    historySize: percentageHistory.length,
                    rangeLimit: range.limit || 1000
                };
            });

            // 🔍 ANALYSES AVEC SYSTÈME DE POINTS CORRIGÉ
            const picsCreuxData = analyzePicsCreuxForAllRanges(0.5);
            const globalSummary = getGlobalPicsCreuxSummary();

            const chutesMonteeData = analyzeChutesMonteeForAllRanges(3, 1.0);
            const globalChuteMonteeSummary = getGlobalChuteMonteeSummary();

            const picsCreuxLegersData = analyzePicsCreuxLegersForAllRanges(2, 2.0, 1.0);
            const globalPicsCreuxLegersSummary = getGlobalPicsCreuxLegersSummary();

            const plateauxData = analyzePlateauxForAllRanges(2, 1.5, 2);
            const globalPlateauxSummary = getGlobalPlateauxSummary();

            // 🌡️ NOUVEAU : Analyse du thermomètre de situation CORRIGÉE AVEC STABILITÉ
            const thermometreData = analyzeThermometreForAllRanges();
            const globalThermometreSummary = getGlobalThermometreSummary();
            
            // 🆕 NOUVEAU : Données de classement des pourcentages
            const percentageRankingData = getGlobalPercentageRankingSummary();
            
            // 🎯 NOUVEAU : Prédictions de crash
            const nextCrashPrediction = generateGlobalPrediction();

            const payload = {
                type: 'update',
                data: {
                    newValues: newValues,
                    history: crashHistory,
                    timestamp: Date.now(),
                    count: newValues.length,
                    rangePercentages: rangePercentageData,
                    medianHistory: medianHistory.slice(0, 20),
                    meanHistory: meanHistory.slice(0, 20),
                    medianOfMedians: calculateMean(medianHistory),
                    meanOfMeans: calculateMean(meanHistory),
                    currentMedian: medianHistory[0] || 0,
                    currentMean: meanHistory[0] || 0,
                    // 🔍 DONNÉES AVEC SYSTÈME DE POINTS CORRIGÉ
                    picsCreuxAnalysis: picsCreuxData,
                    picsCreuxGlobalSummary: globalSummary,
                    chutesMonteeAnalysis: chutesMonteeData,
                    chutesMonteeGlobalSummary: globalChuteMonteeSummary,
                    picsCreuxLegersAnalysis: picsCreuxLegersData,
                    picsCreuxLegersGlobalSummary: globalPicsCreuxLegersSummary,
                    plateauxAnalysis: plateauxData,
                    plateauxGlobalSummary: globalPlateauxSummary,
                    // 🌡️ NOUVEAU : Données du thermomètre de situation CORRIGÉES AVEC STABILITÉ
                    thermometreAnalysis: thermometreData,
                    thermometreGlobalSummary: globalThermometreSummary,
                    // 🆕 NOUVEAU : Données de classement des pourcentages
                    percentageRankingData: percentageRankingData,
                    // 🎯 NOUVEAU : PRÉDICTIONS DE CRASH
                    nextCrashPrediction: nextCrashPrediction,
                    autoRefreshChart: true,
                    playNotificationSound: true
                }
            };
            
            io.emit('update', payload);
            console.log(`📤 Envoyé ${newValues.length} valeurs vers les clients avec toutes les analyses + 🎯 PRÉDICTIONS DE CRASH`);
            
            // Affichage console de la prédiction principale
            if (nextCrashPrediction.recommendation) {
                const rec = nextCrashPrediction.recommendation;
                console.log(`🎯 PRÉDICTION: ${rec.mostLikely} - ${rec.probability}% (${rec.riskLevel})`);
            }
        }
    }, 100);
    
    console.log('🚀 Thread d\'envoi de données + PRÉDICTIONS démarré');
}

function stopDataSender() {
    if (!dataSendActive) return;
    
    dataSendActive = false;
    if (dataSenderInterval) {
        clearInterval(dataSenderInterval);
        dataSenderInterval = null;
    }
    console.log('⏹️ Thread d\'envoi de données arrêté');
}

// Fonction WebSocket mise à jour avec redémarrage automatique
function startWebSocketConnection() {
    try {
        console.log('🔌 Tentative de connexion WebSocket...');
        
        if (!currentToken) {
            console.log('❌ Aucun token disponible, impossible de se connecter');
            return;
        }
        
        wsConnection = new WebSocket(WEBSOCKET_BASE_URL);
        
        wsConnection.on('open', () => {
            console.log('✅ Connexion WebSocket établie');
            
            const authMessage = {
                "connect": {
                    "token": currentToken,
                    "name": "js"
                },
                "id": 1
            };
            
            wsConnection.send(JSON.stringify(authMessage));
            console.log('📤 Message d\'authentification envoyé:', JSON.stringify(authMessage));
        });
        
        wsConnection.on('message', onWebSocketMessage);
        
        wsConnection.on('error', (error) => {
            console.error('❌ Erreur WebSocket:', error);
        });
        
        wsConnection.on('close', (code, reason) => {
            console.log(`🔌 Connexion WebSocket fermée: ${code} - ${reason}`);
            
            if (autoRestartEnabled && isPolling) {
                console.log('🔄 Déclenchement du redémarrage automatique du cœur serveur...');
                restartServerCore();
            } else if (isPolling) {
                console.log('🔄 Tentative de reconnexion dans 5 secondes...');
                setTimeout(() => {
                    if (isPolling) {
                        startWebSocketConnection();
                    }
                }, 5000);
            }
        });
        
    } catch (error) {
        console.error('❌ Erreur de connexion WebSocket:', error);
        
        if (autoRestartEnabled && isPolling) {
            console.log('🔄 Erreur critique, déclenchement du redémarrage automatique...');
            setTimeout(restartServerCore, 3000);
        }
    }
}

// Récupérer le solde
async function getUserBalance() {
    try {
        console.log('💰 Récupération du solde utilisateur...');
        
        const response = await axios.get(BALANCE_URL, {
            headers: {
                "accept": "application/json, text/plain, */*",
                "accept-language": "en-US,en;q=0.9,fr-CI;q=0.8,fr;q=0.7",
                "customer-id": userInfo.customerId,
                "sec-ch-ua": "\"Not-A.Brand\";v=\"99\", \"Chromium\";v=\"124\"",
                "sec-ch-ua-mobile": "?1",
                "sec-ch-ua-platform": "\"Android\"",
                "sec-fetch-site": "cross-site",
                "session-id": userInfo.sessionId,
                "Referer": "https://1play.gamedev-tech.cc/",
                "Referrer-Policy": "strict-origin-when-cross-origin"
            }
        });
        
        if (response.data && response.data.balance !== undefined) {
            userInfo.balance = response.data.balance;
            console.log(`💰 Solde récupéré: ${userInfo.balance} FCFA`);
            return response.data.balance;
        } else {
            console.log('❌ Réponse de solde invalide:', response.data);
            return null;
        }
    } catch (error) {
        console.error('❌ Erreur de récupération du solde:', error.message);
        return null;
    }
}

// Placer un pari
async function placeBet(amount, autoCash) {
    try {
        console.log(`🎲 Placement d'un pari: ${amount} FCFA avec auto-cashout à ${autoCash}x`);
        
        const betData = {
            details: {
                slotIndex: 1,
                coefficientIndex: 0,
                type: "base",
                autoCashOutTarget: autoCash
            },
            wager: {
                type: "money",
                size: amount
            }
        };
        
        const response = await axios.post(BET_PLACE_URL, betData, {
            headers: {
                "accept": "application/json, text/plain, */*",
                "accept-language": "en-US,en;q=0.9,fr-CI;q=0.8,fr;q=0.7",
                "authorization": `Bearer ${userInfo.sessionId}`,
                "content-type": "application/json",
                "customer-id": userInfo.customerId,
                "sec-ch-ua": "\"Not-A.Brand\";v=\"99\", \"Chromium\";v=\"124\"",
                "sec-ch-ua-mobile": "?1",
                "sec-ch-ua-platform": "\"Android\"",
                "sec-fetch-dest": "empty",
                "sec-fetch-mode": "cors",
                "sec-fetch-site": "cross-site",
                "session-id": userInfo.sessionId,
                "Referer": "https://1play.gamedev-tech.cc/",
                "Referrer-Policy": "strict-origin-when-cross-origin"
            }
        });

        console.log('🎲 Réponse du pari:', response.data);

        if (response.data && response.data.code) {
            return {
                status: "error",
                error: response.data.description || "Erreur de pari",
                code: response.data.code
            };
        } else if (response.data && response.data.data) {
            return {
                status: "success",
                bet: response.data.data
            };
        } else if (response.data && !response.data.code) {
            return {
                status: "success",
                bet: response.data
            };
        } else {
            return {
                status: "error",
                error: "Format de réponse inattendu"
            };
        }

    } catch (error) {
        console.error('❌ Erreur lors du placement du pari:', error.message);
        
        if (error.response && error.response.data) {
            const errorData = error.response.data;
            return {
                status: "error",
                error: errorData.description || errorData.message || "Erreur de connexion",
                code: errorData.code
            };
        }
        
        return {
            status: "error",
            error: "Erreur de connexion"
        };
    }
}

// FONCTION CORRIGÉE - Utilise maintenant les limites spécifiques dans l'analyse
function analyzeData(history, ranges, customSizes = {}) {
    if (!history || history.length === 0) {
        return {
            total: 0,
            ranges: {},
            median: 0,
            mean: 0,
            medianOfMedians: 0,
            meanOfMeans: 0,
            medianHistory: [],
            meanHistory: []
        };
    }
    
    const medianSize = customSizes.median;
    const meanSize = customSizes.mean;
    const medianHistory = medianSize && medianSize < history.length ? history.slice(0, medianSize) : history;
    const meanHistory = meanSize && meanSize < history.length ? history.slice(0, meanSize) : history;
    
    const results = {
        total: history.length,
        ranges: {},
        median: calculateMedian(medianHistory),
        mean: calculateMean(meanHistory),
        medianOfMedians: calculateMean(medianHistory),
        meanOfMeans: calculateMean(meanHistory),
        medianHistory: medianHistory.slice(0, 20),
        meanHistory: meanHistory.slice(0, 20)
    };
    
    for (const rangeDef of ranges) {
        const name = rangeDef.name;
        const minVal = rangeDef.min;
        const maxVal = rangeDef.max;
        const color = rangeDef.color;
        const limit = rangeDef.limit;
        
        const rangeHistory = limit && limit < history.length ? history.slice(0, limit) : history;
        const valuesInRange = [];
        
        for (const value of rangeHistory) {
            if (minVal !== null && maxVal !== null) {
                if (minVal <= value && value < maxVal) {
                    valuesInRange.push(value);
                }
            } else if (minVal !== null) {
                if (value >= minVal) {
                    valuesInRange.push(value);
                }
            } else if (maxVal !== null) {
                if (value < maxVal) {
                    valuesInRange.push(value);
                }
            }
        }
        
        const percentageHistory = rangePercentageHistory.get(name) || [];
        const currentPercentage = rangeHistory.length > 0 ? (valuesInRange.length / rangeHistory.length) * 100 : 0;
        const averagePercentage = calculateMean(percentageHistory);

        results.ranges[name] = {
            count: valuesInRange.length,
            percentage: currentPercentage,
            mean: calculateMean(valuesInRange),
            color: color,
            percentageHistory: percentageHistory.slice(0, limit || 100),
            percentageHistorySize: percentageHistory.length,
            averagePercentage: averagePercentage,
            difference: currentPercentage - averagePercentage
        };
    }
    
    return results;
}

function calculateMedian(values) {
    if (!values || values.length === 0) return 0;
    
    const sorted = [...values].sort((a, b) => a - b);
    const mid = Math.floor(sorted.length / 2);
    
    if (sorted.length % 2 === 0) {
        return (sorted[mid - 1] + sorted[mid]) / 2;
    } else {
        return sorted[mid];
    }
}

function calculateMean(values) {
    if (!values || values.length === 0) return 0;
    return values.reduce((sum, val) => sum + val, 0) / values.length;
}

function startPolling() {
    if (isPolling) return;
    
    isPolling = true;
    
    if (wsConnection) {
        wsConnection.close();
    }
    
    startDataSender();
    
    if (currentToken) {
        startWebSocketConnection();
    } else {
        console.log('⚠️  Aucun token disponible, récupération en cours...');
        refreshToken().then(success => {
            if (success) {
                startWebSocketConnection();
            }
        });
    }
    
    console.log('🚀 Système PRÉDICTIF + Polling WebSocket démarré');
    saveConfig();
}

function stopPolling() {
    if (!isPolling) return;
    
    isPolling = false;
    
    stopDataSender();
    
    if (wsConnection) {
        wsConnection.close();
        wsConnection = null;
    }
    
    if (pingInterval) {
        clearInterval(pingInterval);
        pingInterval = null;
    }
    
    console.log('⏹️ Système PRÉDICTIF + Polling WebSocket arrêté');
    saveConfig();
}

// Routes
app.get('/', (req, res) => {
    res.sendFile(path.join(__dirname, 'index.html'));
});

app.post('/api/login', (req, res) => {
    const { username, password } = req.body;
    
    if (users[username] === password) {
        res.json({ 
            success: true, 
            userInfo: userInfo
        });
    } else {
        res.status(401).json({ success: false, message: "Identifiants incorrects" });
    }
});

app.get('/api/range-percentages', (req, res) => {
    try {
        const rangeData = {};
        
        currentRanges.forEach(range => {
            const percentageHistory = rangePercentageHistory.get(range.name) || [];
            const averagePercentage = calculateMean(percentageHistory);
            const currentPercentage = percentageHistory[0] || 0;
            const difference = currentPercentage - averagePercentage;
            
            rangeData[range.name] = {
                name: range.name,
                color: range.color,
                limit: range.limit,
                currentPercentage: currentPercentage,
                percentageHistory: percentageHistory,
                averagePercentage: averagePercentage,
                difference: difference,
                historySize: percentageHistory.length,
                min: range.min,
                max: range.max
            };
        });
        
        res.json({
            success: true,
            data: rangeData,
            totalHistorySize: crashHistory.length
        });
    } catch (error) {
        res.status(500).json({ success: false, message: `Erreur: ${error.message}` });
    }
});

// API pour récupérer les statistiques de médiane et moyenne
app.get('/api/median-mean-stats', (req, res) => {
    try {
        const medianOfMedians = calculateMean(medianHistory);
        const meanOfMeans = calculateMean(meanHistory);
        
        res.json({
            success: true,
            data: {
                medianHistory: medianHistory,
                meanHistory: meanHistory,
                medianOfMedians: medianOfMedians,
                meanOfMeans: meanOfMeans,
                currentMedian: medianHistory[0] || 0,
                currentMean: meanHistory[0] || 0,
                medianHistorySize: medianHistory.length,
                meanHistorySize: meanHistory.length,
                customSizes: customSizes
            }
        });
    } catch (error) {
        res.status(500).json({ success: false, message: `Erreur: ${error.message}` });
    }
});

// 🎯 NOUVELLES ROUTES API PRÉDICTIVES

app.get('/api/crash-prediction', (req, res) => {
    try {
        const globalPrediction = generateGlobalPrediction();
        
        res.json({
            success: true,
            data: globalPrediction
        });
    } catch (error) {
        res.status(500).json({ success: false, message: `Erreur: ${error.message}` });
    }
});

app.get('/api/crash-prediction/:rangeName', (req, res) => {
    try {
        const rangeName = req.params.rangeName;
        const predictionData = predictionModels.get(rangeName);
        
        if (!predictionData) {
            return res.status(404).json({ 
                success: false, 
                message: `Range "${rangeName}" non trouvée` 
            });
        }
        
        res.json({
            success: true,
            data: {
                rangeName: rangeName,
                prediction: predictionData,
                timestamp: Date.now()
            }
        });
    } catch (error) {
        res.status(500).json({ success: false, message: `Erreur: ${error.message}` });
    }
});

app.get('/api/ranking-evolution/:rangeName', (req, res) => {
    try {
        const rangeName = req.params.rangeName;
        const evolutionData = rankingEvolutionHistory.get(rangeName);
        const momentumData = momentumAnalysis.get(rangeName);
        const competitiveData = competitiveZonesAnalysis.get(rangeName);
        const temporalData = temporalPatterns.get(rangeName);
        
        if (!evolutionData) {
            return res.status(404).json({ 
                success: false, 
                message: `Range "${rangeName}" non trouvée` 
            });
        }
        
        res.json({
            success: true,
            data: {
                rangeName: rangeName,
                evolution: evolutionData,
                momentum: momentumData,
                competitive: competitiveData,
                temporal: temporalData,
                timestamp: Date.now()
            }
        });
    } catch (error) {
        res.status(500).json({ success: false, message: `Erreur: ${error.message}` });
    }
});

app.get('/api/transition-analysis/:rangeName', (req, res) => {
    try {
        const rangeName = req.params.rangeName;
        const transitionData = rankTransitionMatrices.get(rangeName);
        
        if (!transitionData) {
            return res.status(404).json({ 
                success: false, 
                message: `Range "${rangeName}" non trouvée` 
            });
        }
        
        res.json({
            success: true,
            data: {
                rangeName: rangeName,
                transitions: transitionData,
                timestamp: Date.now()
            }
        });
    } catch (error) {
        res.status(500).json({ success: false, message: `Erreur: ${error.message}` });
    }
});

// 🆕 NOUVELLES ROUTES API POUR LE CLASSEMENT DES POURCENTAGES

// API pour récupérer le classement global des pourcentages
app.get('/api/percentage-ranking', (req, res) => {
    try {
        const globalRanking = getGlobalPercentageRankingSummary();
        
        res.json({
            success: true,
            data: {
                globalRanking: globalRanking,
                timestamp: Date.now()
            }
        });
    } catch (error) {
        res.status(500).json({ success: false, message: `Erreur: ${error.message}` });
    }
});

// API pour récupérer le classement d'une range spécifique
app.get('/api/percentage-ranking/:rangeName', (req, res) => {
    try {
        const rangeName = req.params.rangeName;
        const tolerance = parseFloat(req.query.tolerance) || 0.2;
        
        const rankingData = percentageRankingHistory.get(rangeName);
        const frequencyData = percentageFrequencyAnalysis.get(rangeName);
        
        if (!rankingData || !frequencyData) {
            return res.status(404).json({ 
                success: false, 
                message: `Range "${rangeName}" non trouvée ou pas encore analysée` 
            });
        }
        
        res.json({
            success: true,
            data: {
                rangeName: rangeName,
                ranking: rankingData,
                frequency: frequencyData,
                parameters: { tolerance },
                timestamp: Date.now()
            }
        });
    } catch (error) {
        res.status(500).json({ success: false, message: `Erreur: ${error.message}` });
    }
});

// API pour récupérer le top des pourcentages par range
app.get('/api/percentage-ranking/:rangeName/top', (req, res) => {
    try {
        const rangeName = req.params.rangeName;
        const limit = parseInt(req.query.limit) || 10;
        
        const frequencyData = percentageFrequencyAnalysis.get(rangeName);
        
        if (!frequencyData) {
            return res.status(404).json({ 
                success: false, 
                message: `Range "${rangeName}" non trouvée` 
            });
        }
        
        const topPercentages = frequencyData.classementDetaille.slice(0, limit);
        
        res.json({
            success: true,
            data: {
                rangeName: rangeName,
                topPercentages: topPercentages,
                totalUniquePercentages: frequencyData.classementDetaille.length,
                modePercentage: frequencyData.statistiques.modePercentage,
                stabilityIndex: frequencyData.indexStabilite,
                timestamp: Date.now()
            }
        });
    } catch (error) {
        res.status(500).json({ success: false, message: `Erreur: ${error.message}` });
    }
});

// API pour rechercher un pourcentage spécifique
app.get('/api/percentage-ranking/:rangeName/search', (req, res) => {
    try {
        const rangeName = req.params.rangeName;
        const targetPercentage = parseFloat(req.query.percentage);
        const tolerance = parseFloat(req.query.tolerance) || 0.1;
        
        if (isNaN(targetPercentage)) {
            return res.status(400).json({ 
                success: false, 
                message: 'Paramètre "percentage" requis et doit être un nombre' 
            });
        }
        
        const frequencyData = percentageFrequencyAnalysis.get(rangeName);
        
        if (!frequencyData) {
            return res.status(404).json({ 
                success: false, 
                message: `Range "${rangeName}" non trouvée` 
            });
        }
        
        const matches = frequencyData.classementDetaille.filter(item => 
            Math.abs(item.percentage - targetPercentage) <= tolerance
        );
        
        res.json({
            success: true,
            data: {
                rangeName: rangeName,
                searchedPercentage: targetPercentage,
                tolerance: tolerance,
                matches: matches,
                totalMatches: matches.length,
                timestamp: Date.now()
            }
        });
    } catch (error) {
        res.status(500).json({ success: false, message: `Erreur: ${error.message}` });
    }
});

// API pour récupérer les statistiques détaillées d'une range
app.get('/api/percentage-ranking/:rangeName/stats', (req, res) => {
    try {
        const rangeName = req.params.rangeName;
        
        const rankingData = percentageRankingHistory.get(rangeName);
        const frequencyData = percentageFrequencyAnalysis.get(rangeName);
        const percentageHistory = rangePercentageHistory.get(rangeName) || [];
        
        if (!rankingData || !frequencyData) {
            return res.status(404).json({ 
                success: false, 
                message: `Range "${rangeName}" non trouvée` 
            });
        }
        
        const range = currentRanges.find(r => r.name === rangeName);
        
        res.json({
            success: true,
            data: {
                rangeName: rangeName,
                rangeConfig: range,
                totalDataPoints: percentageHistory.length,
                uniquePercentages: frequencyData.classementDetaille.length,
                averageFrequency: rankingData.averageFrequency,
                statistics: frequencyData.statistiques,
                stabilityIndex: frequencyData.indexStabilite,
                trendFrequency: frequencyData.tendanceFrequence,
                percentileRanks: frequencyData.percentileRanks,
                topCategories: {
                    ultraFrequent: frequencyData.classementDetaille.filter(item => item.category === "Ultra-Fréquent").length,
                    tresFrequent: frequencyData.classementDetaille.filter(item => item.category === "Très-Fréquent").length,
                    frequent: frequencyData.classementDetaille.filter(item => item.category === "Fréquent").length,
                    modere: frequencyData.classementDetaille.filter(item => item.category === "Modéré").length,
                    rare: frequencyData.classementDetaille.filter(item => item.category === "Rare").length,
                    ultraRare: frequencyData.classementDetaille.filter(item => item.category === "Ultra-Rare").length
                },
                timestamp: Date.now()
            }
        });
    } catch (error) {
        res.status(500).json({ success: false, message: `Erreur: ${error.message}` });
    }
});

// 🌡️ NOUVELLE ROUTE API POUR LE THERMOMÈTRE DE SITUATION CORRIGÉE AVEC STABILITÉ

// API pour récupérer l'analyse du thermomètre de situation
app.get('/api/thermometre-analysis', (req, res) => {
    try {
        const analysis = analyzeThermometreForAllRanges();
        const globalSummary = getGlobalThermometreSummary();
        
        res.json({
            success: true,
            data: {
                analysis: analysis,
                globalSummary: globalSummary,
                timestamp: Date.now()
            }
        });
    } catch (error) {
        res.status(500).json({ success: false, message: `Erreur: ${error.message}` });
    }
});

// API pour récupérer l'analyse d'une range spécifique pour le thermomètre
app.get('/api/thermometre-analysis/:rangeName', (req, res) => {
    try {
        const rangeName = req.params.rangeName;
        
        const zoneData = calculateZonePercentages(rangeName);
        
        if (!zoneData) {
            return res.status(404).json({ 
                success: false, 
                message: `Range "${rangeName}" non trouvée` 
            });
        }
        
        res.json({
            success: true,
            data: {
                rangeName: rangeName,
                zoneData: zoneData,
                timestamp: Date.now()
            }
        });
    } catch (error) {
        res.status(500).json({ success: false, message: `Erreur: ${error.message}` });
    }
});

// 🔍 ROUTES API POUR L'ANALYSE DES PICS ET CREUX AVEC SYSTÈME DE POINTS CORRIGÉ

// API pour récupérer l'analyse des pics et creux
app.get('/api/pics-creux-analysis', (req, res) => {
    try {
        const sensitivity = parseFloat(req.query.sensitivity) || 0.5;
        const analysis = analyzePicsCreuxForAllRanges(sensitivity);
        const globalSummary = getGlobalPicsCreuxSummary();
        
        res.json({
            success: true,
            data: {
                analysis: analysis,
                globalSummary: globalSummary,
                sensitivity: sensitivity,
                timestamp: Date.now()
            }
        });
    } catch (error) {
        res.status(500).json({ success: false, message: `Erreur: ${error.message}` });
    }
});

// API pour récupérer l'analyse d'une range spécifique
app.get('/api/pics-creux-analysis/:rangeName', (req, res) => {
    try {
        const rangeName = req.params.rangeName;
        const sensitivity = parseFloat(req.query.sensitivity) || 0.5;
        
        const analysis = picsCreuxAnalysis.get(rangeName);
        if (!analysis) {
            return res.status(404).json({ 
                success: false, 
                message: `Range "${rangeName}" non trouvée` 
            });
        }
        
        const percentageHistory = rangePercentageHistory.get(rangeName) || [];
        const events = detectPicsCreux(percentageHistory, sensitivity);
        const globalTrend = calculateGlobalTrend(events, percentageHistory.length);
        
        res.json({
            success: true,
            data: {
                rangeName: rangeName,
                events: events,
                globalTrend: globalTrend,
                sensitivity: sensitivity,
                dataSize: percentageHistory.length,
                timestamp: Date.now()
            }
        });
    } catch (error) {
        res.status(500).json({ success: false, message: `Erreur: ${error.message}` });
    }
});

// 🔥 ROUTES API POUR L'ANALYSE DES CHUTES ET MONTÉES AVEC SYSTÈME DE POINTS CORRIGÉ

// API pour récupérer l'analyse des chutes et montées
app.get('/api/chutes-montee-analysis', (req, res) => {
    try {
        const minLength = parseInt(req.query.minLength) || 3;
        const minVariation = parseFloat(req.query.minVariation) || 1.0;
        const analysis = analyzeChutesMonteeForAllRanges(minLength, minVariation);
        const globalSummary = getGlobalChuteMonteeSummary();
        
        res.json({
            success: true,
            data: {
                analysis: analysis,
                globalSummary: globalSummary,
                parameters: { minLength, minVariation },
                timestamp: Date.now()
            }
        });
    } catch (error) {
        res.status(500).json({ success: false, message: `Erreur: ${error.message}` });
    }
});

// API pour récupérer l'analyse d'une range spécifique pour chutes/montées
app.get('/api/chutes-montee-analysis/:rangeName', (req, res) => {
    try {
        const rangeName = req.params.rangeName;
        const minLength = parseInt(req.query.minLength) || 3;
        const minVariation = parseFloat(req.query.minVariation) || 1.0;
        
        const analysis = chutesMonteeAnalysis.get(rangeName);
        if (!analysis) {
            return res.status(404).json({ 
                success: false, 
                message: `Range "${rangeName}" non trouvée` 
            });
        }
        
        const percentageHistory = rangePercentageHistory.get(rangeName) || [];
        const events = detectChutesMonteeProgressives(percentageHistory, minLength, minVariation);
        const globalTrend = calculateChuteMonteeTrend(events, percentageHistory.length);
        
        res.json({
            success: true,
            data: {
                rangeName: rangeName,
                events: events,
                globalTrend: globalTrend,
                parameters: { minLength, minVariation },
                dataSize: percentageHistory.length,
                timestamp: Date.now()
            }
        });
    } catch (error) {
        res.status(500).json({ success: false, message: `Erreur: ${error.message}` });
    }
});

// 🆕 ROUTES API POUR L'ANALYSE DES PICS ET CREUX LÉGERS AVEC SYSTÈME DE POINTS CORRIGÉ

// API pour récupérer l'analyse des pics et creux légers
app.get('/api/pics-creux-legers-analysis', (req, res) => {
    try {
        const minPlateauLength = parseInt(req.query.minPlateauLength) || 1;
        const maxPlateauVariation = parseFloat(req.query.maxPlateauVariation) || 2.0;
        const minInitialChange = parseFloat(req.query.minInitialChange) || 1.0;
        const analysis = analyzePicsCreuxLegersForAllRanges(minPlateauLength, maxPlateauVariation, minInitialChange);
        const globalSummary = getGlobalPicsCreuxLegersSummary();
        
        res.json({
            success: true,
            data: {
                analysis: analysis,
                globalSummary: globalSummary,
                parameters: { minPlateauLength, maxPlateauVariation, minInitialChange },
                timestamp: Date.now()
            }
        });
    } catch (error) {
        res.status(500).json({ success: false, message: `Erreur: ${error.message}` });
    }
});

// API pour récupérer l'analyse d'une range spécifique pour pics/creux légers
app.get('/api/pics-creux-legers-analysis/:rangeName', (req, res) => {
    try {
        const rangeName = req.params.rangeName;
        const minPlateauLength = parseInt(req.query.minPlateauLength) || 2;
        const maxPlateauVariation = parseFloat(req.query.maxPlateauVariation) || 2.0;
        const minInitialChange = parseFloat(req.query.minInitialChange) || 1.0;
        
        const analysis = picsCreuxLegersAnalysis.get(rangeName);
        if (!analysis) {
            return res.status(404).json({ 
                success: false, 
                message: `Range "${rangeName}" non trouvée` 
            });
        }
        
        const percentageHistory = rangePercentageHistory.get(rangeName) || [];
        const events = detectPicsCreuxLegers(percentageHistory, minPlateauLength, maxPlateauVariation, minInitialChange);
        const globalTrend = calculateGlobalPicsCreuxLegersTrend(events, percentageHistory.length);
        
        res.json({
            success: true,
            data: {
                rangeName: rangeName,
                events: events,
                globalTrend: globalTrend,
                parameters: { minPlateauLength, maxPlateauVariation, minInitialChange },
                dataSize: percentageHistory.length,
                timestamp: Date.now()
            }
        });
    } catch (error) {
        res.status(500).json({ success: false, message: `Erreur: ${error.message}` });
    }
});

// 🔥 ROUTES API POUR L'ANALYSE DES PLATEAUX AVEC SYSTÈME DE POINTS CORRIGÉ

// API pour récupérer l'analyse des plateaux
app.get('/api/plateaux-analysis', (req, res) => {
    try {
        const minPlateauLength = parseInt(req.query.minPlateauLength) || 1;
        const maxVariation = parseFloat(req.query.maxVariation) || 1.5;
        const minStabilityDuration = parseInt(req.query.minStabilityDuration) || 2;
        const analysis = analyzePlateauxForAllRanges(minPlateauLength, maxVariation, minStabilityDuration);
        const globalSummary = getGlobalPlateauxSummary();
        
        res.json({
            success: true,
            data: {
                analysis: analysis,
                globalSummary: globalSummary,
                parameters: { minPlateauLength, maxVariation, minStabilityDuration },
                timestamp: Date.now()
            }
        });
    } catch (error) {
        res.status(500).json({ success: false, message: `Erreur: ${error.message}` });
    }
});

// API pour récupérer l'analyse d'une range spécifique pour plateaux
app.get('/api/plateaux-analysis/:rangeName', (req, res) => {
    try {
        const rangeName = req.params.rangeName;
        const minPlateauLength = parseInt(req.query.minPlateauLength) || 1;
        const maxVariation = parseFloat(req.query.maxVariation) || 1.5;
        const minStabilityDuration = parseInt(req.query.minStabilityDuration) || 2;
        
        const analysis = plateauxAnalysis.get(rangeName);
        if (!analysis) {
            return res.status(404).json({ 
                success: false, 
                message: `Range "${rangeName}" non trouvée` 
            });
        }
        
        const percentageHistory = rangePercentageHistory.get(rangeName) || [];
        
        const picsCreuxData = picsCreuxAnalysis.get(rangeName);
        const chutesMonteeData = chutesMonteeAnalysis.get(rangeName);
        const picsCreuxLegersData = picsCreuxLegersAnalysis.get(rangeName);
        
        const picsCreux = picsCreuxData ? picsCreuxData.events || [] : [];
        const chutesMontees = chutesMonteeData ? chutesMonteeData.events || [] : [];
        const picsCreuxLegers = picsCreuxLegersData ? picsCreuxLegersData.events || [] : [];
        
        const plateaux = detectPlateaux(percentageHistory, minPlateauLength, maxVariation, minStabilityDuration);
        const globalTrend = calculatePlateauxGlobalTrend(plateaux, picsCreux, chutesMontees, picsCreuxLegers, percentageHistory.length);
        
        res.json({
            success: true,
            data: {
                rangeName: rangeName,
                plateaux: plateaux,
                globalTrend: globalTrend,
                parameters: { minPlateauLength, maxVariation, minStabilityDuration },
                dataSize: percentageHistory.length,
                timestamp: Date.now()
            }
        });
    } catch (error) {
        res.status(500).json({ success: false, message: `Erreur: ${error.message}` });
    }
});

// Gestionnaires Socket.IO AVEC SYSTÈME DE POINTS CORRIGÉ ET STABILITÉ + CLASSEMENT DES POURCENTAGES + PRÉDICTIONS
io.on('connection', (socket) => {
    console.log('Client connecté');
    
    const globalPrediction = generateGlobalPrediction();
    
    socket.emit('init', {
        type: 'init',
        data: {
            history: crashHistory,
            historySize: historySize,
            isPolling: isPolling,
            ranges: currentRanges,
            customSizes: customSizes,
            medianHistory: medianHistory.slice(0, 20),
            meanHistory: meanHistory.slice(0, 20),
            medianOfMedians: calculateMean(medianHistory),
            meanOfMeans: calculateMean(meanHistory),
            userInfo: userInfo,
            currentCoefficient: currentCoefficient,
            // 🔍 DONNÉES AVEC SYSTÈME DE POINTS CORRIGÉ à l'initialisation
            picsCreuxAnalysis: analyzePicsCreuxForAllRanges(0.5),
            picsCreuxGlobalSummary: getGlobalPicsCreuxSummary(),
            chutesMonteeAnalysis: analyzeChutesMonteeForAllRanges(3, 1.0),
            chutesMonteeGlobalSummary: getGlobalChuteMonteeSummary(),
            picsCreuxLegersAnalysis: analyzePicsCreuxLegersForAllRanges(2, 2.0, 1.0),
            picsCreuxLegersGlobalSummary: getGlobalPicsCreuxLegersSummary(),
            plateauxAnalysis: analyzePlateauxForAllRanges(2, 1.5, 2),
            plateauxGlobalSummary: getGlobalPlateauxSummary(),
            // 🌡️ NOUVEAU : Données du thermomètre de situation CORRIGÉES AVEC STABILITÉ à l'initialisation
            thermometreAnalysis: analyzeThermometreForAllRanges(),
            thermometreGlobalSummary: getGlobalThermometreSummary(),
            // 🆕 NOUVEAU : Données de classement des pourcentages à l'initialisation
            percentageRankingData: getGlobalPercentageRankingSummary(),
            // 🎯 NOUVEAU : PRÉDICTIONS DE CRASH à l'initialisation
            nextCrashPrediction: globalPrediction
        }
    });
    
    socket.on('message', async (message) => {
        try {
            const data = typeof message === 'string' ? JSON.parse(message) : message;
            const messageType = data.type;
            
            switch (messageType) {
                case 'startPolling':
                    startPolling();
                    socket.emit('pollingStatus', { type: 'pollingStatus', isPolling: true });
                    break;
                    
                case 'stopPolling':
                    stopPolling();
                    socket.emit('pollingStatus', { type: 'pollingStatus', isPolling: false });
                    break;
                    
                case 'setHistorySize':
                    historySize = parseInt(data.size) || 100;
                    crashHistory = crashHistory.slice(0, historySize);
                    socket.emit('historyUpdated', {
                        type: 'historyUpdated',
                        history: crashHistory,
                        historySize: historySize
                    });
                    await saveConfig();
                    break;
                    
                case 'setPollingFrequency':
                    pollingFrequency = parseInt(data.frequency) || 1000;
                    socket.emit('frequencyUpdated', { type: 'frequencyUpdated', frequency: pollingFrequency });
                    await saveConfig();
                    break;
                    
                case 'updateCustomSizes':
                    if (data.customSizes && typeof data.customSizes === 'object') {
                        if (data.customSizes.median && !isNaN(data.customSizes.median)) {
                            customSizes.median = parseInt(data.customSizes.median);
                            if (medianHistory.length > customSizes.median) {
                                medianHistory = medianHistory.slice(0, customSizes.median);
                            }
                        }
                        if (data.customSizes.mean && !isNaN(data.customSizes.mean)) {
                            customSizes.mean = parseInt(data.customSizes.mean);
                            if (meanHistory.length > customSizes.mean) {
                                meanHistory = meanHistory.slice(0, customSizes.mean);
                            }
                        }
                        console.log('CustomSizes mis à jour:', customSizes);
                        socket.emit('customSizesUpdated', { 
                            type: 'customSizesUpdated', 
                            success: true, 
                            customSizes: customSizes 
                        });
                        await saveConfig();
                    } else {
                        socket.emit('customSizesUpdated', { 
                            type: 'customSizesUpdated', 
                            success: false, 
                            message: 'Format customSizes invalide' 
                        });
                    }
                    break;

                case 'updateAuthToken':
                    if (data.authToken && typeof data.authToken === 'string') {
                        authToken = data.authToken;
                        socket.emit('authTokenUpdated', { 
                            type: 'authTokenUpdated', 
                            success: true,
                            message: 'Auth token mis à jour avec succès'
                        });
                        await saveConfig();
                    } else {
                        socket.emit('authTokenUpdated', { 
                            type: 'authTokenUpdated', 
                            success: false, 
                            message: 'Format auth token invalide' 
                        });
                    }
                    break;
                    
                case 'updateUsers':
                    if (data.users && typeof data.users === 'object') {
                        users = data.users;
                        socket.emit('usersUpdated', { type: 'usersUpdated', success: true });
                        await saveConfig();
                    } else {
                        socket.emit('usersUpdated', { type: 'usersUpdated', success: false, message: 'Format utilisateurs invalide' });
                    }
                    break;
                    
                case 'getBalance':
                    const balance = userInfo.balance;
                    socket.emit('balance', { type: 'balance', data: balance });
                    break;
                    
                case 'placeBet':
                    const betResult = await placeBet(data.amount, data.autoCash);
                    socket.emit('betResult', { type: 'betResult', data: betResult });
                    break;
                    
                case 'analyze':
                    const customHistory = data.customHistory || crashHistory.slice(0, data.limit || historySize);
                    const ranges = data.ranges || currentRanges;
                    const customSizesForAnalysis = data.customSizes || customSizes;
                    const analysis = analyzeData(customHistory, ranges, customSizesForAnalysis);
                    
                    analysis.medianOfMedians = calculateMean(medianHistory);
                    analysis.meanOfMeans = calculateMean(meanHistory);
                    analysis.medianHistory = medianHistory.slice(0, 20);
                    analysis.meanHistory = meanHistory.slice(0, 20);
                    
                    socket.emit('analysis', { type: 'analysis', data: analysis });
                    break;
                    
                case 'saveRanges':
                    if (data.ranges && Array.isArray(data.ranges)) {
                        currentRanges = data.ranges;
                        
                        // Réinitialiser les systèmes prédictifs pour les nouvelles ranges
                        currentRanges.forEach(range => {
                            initializeRangePercentageHistory(range.name, range.limit);
                        });
                        
                        socket.emit('rangesSaved', { type: 'rangesSaved', success: true, ranges: currentRanges });
                        await saveConfig();
                    } else {
                        socket.emit('rangesSaved', { type: 'rangesSaved', success: false, message: 'Format de plages invalide' });
                    }
                    break;
                    
                case 'getRanges':
                    socket.emit('rangesData', { type: 'rangesData', ranges: currentRanges });
                    break;
                    
                case 'fetchNow':
                    socket.emit('message', { type: 'info', message: 'WebSocket actif - les données sont envoyées toutes les secondes' });
                    break;
                    
                case 'getRangePercentages':
                    const rangePercentageData = {};
                    currentRanges.forEach(range => {
                        const percentageHistory = rangePercentageHistory.get(range.name) || [];
                        const averagePercentage = calculateMean(percentageHistory);
                        const currentPercentage = percentageHistory[0] || 0;
                        const difference = currentPercentage - averagePercentage;
                        
                        rangePercentageData[range.name] = {
                            name: range.name,
                            color: range.color,
                            limit: range.limit,
                            currentPercentage: currentPercentage,
                            percentageHistory: percentageHistory.slice(0, data.limit || 100),
                            averagePercentage: averagePercentage,
                            difference: difference,
                            historySize: percentageHistory.length,
                            min: range.min,
                            max: range.max
                        };
                    });
                    socket.emit('rangePercentagesData', { 
                        type: 'rangePercentagesData', 
                        data: rangePercentageData,
                        totalHistorySize: crashHistory.length 
                    });
                    break;

                case 'getMedianMeanStats':
                    socket.emit('medianMeanStats', {
                        type: 'medianMeanStats',
                        data: {
                            medianHistory: medianHistory.slice(0, data.limit || 20),
                            meanHistory: meanHistory.slice(0, data.limit || 20),
                            medianOfMedians: calculateMean(medianHistory),
                            meanOfMeans: calculateMean(meanHistory),
                            currentMedian: medianHistory[0] || 0,
                            currentMean: meanHistory[0] || 0,
                            medianHistorySize: medianHistory.length,
                            meanHistorySize: meanHistory.length,
                            customSizes: customSizes
                        }
                    });
                    break;

                case 'clearMedianMeanHistory':
                    medianHistory = [];
                    meanHistory = [];
                    socket.emit('medianMeanHistoryCleared', {
                        type: 'medianMeanHistoryCleared',
                        success: true,
                        message: 'Historiques de médiane et moyenne réinitialisés'
                    });
                    await saveConfig();
                    break;
                    
                case 'toggleAutoRestart':
                    autoRestartEnabled = data.enabled !== undefined ? data.enabled : !autoRestartEnabled;
                    socket.emit('autoRestartToggled', {
                        type: 'autoRestartToggled',
                        enabled: autoRestartEnabled,
                        message: autoRestartEnabled ? 'Redémarrage automatique activé' : 'Redémarrage automatique désactivé'
                    });
                    break;
                    
                case 'restartServerCore':
                    socket.emit('message', { 
                        type: 'info', 
                        message: 'Redémarrage manuel du cœur serveur en cours...' 
                    });
                    setTimeout(restartServerCore, 1000);
                    break;

                // 🎯 NOUVEAUX HANDLERS SOCKET POUR LES PRÉDICTIONS
                case 'getCrashPrediction':
                    const prediction = generateGlobalPrediction();
                    socket.emit('crashPredictionData', {
                        type: 'crashPredictionData',
                        data: prediction
                    });
                    break;
                    
                case 'getRankingEvolution':
                    const rangeName = data.rangeName;
                    if (rangeName) {
                        const evolutionData = rankingEvolutionHistory.get(rangeName);
                        const momentumData = momentumAnalysis.get(rangeName);
                        const competitiveData = competitiveZonesAnalysis.get(rangeName);
                        const temporalData = temporalPatterns.get(rangeName);
                        
                        socket.emit('rankingEvolutionData', {
                            type: 'rankingEvolutionData',
                            data: {
                                rangeName: rangeName,
                                evolution: evolutionData,
                                momentum: momentumData,
                                competitive: competitiveData,
                                temporal: temporalData,
                                timestamp: Date.now()
                            }
                        });
                    }
                    break;
                    
                case 'clearPredictionHistory':
                    // Réinitialiser toutes les données prédictives
                    currentRanges.forEach(range => {
                        rankingEvolutionHistory.delete(range.name);
                        rankTransitionMatrices.delete(range.name);
                        momentumAnalysis.delete(range.name);
                        competitiveZonesAnalysis.delete(range.name);
                        temporalPatterns.delete(range.name);
                        predictionModels.delete(range.name);
                    });
                    
                    socket.emit('predictionHistoryCleared', {
                        type: 'predictionHistoryCleared',
                        success: true,
                        message: 'Historique prédictif réinitialisé'
                    });
                    break;

                // 🔍 HANDLERS SOCKET POUR LES PICS ET CREUX AVEC SYSTÈME DE POINTS CORRIGÉ
                case 'getPicsCreuxAnalysis':
                    const sensitivity = parseFloat(data.sensitivity) || 0.5;
                    const picsCreuxAnalysisData = analyzePicsCreuxForAllRanges(sensitivity);
                    const globalSummaryData = getGlobalPicsCreuxSummary();
                    
                    socket.emit('picsCreuxAnalysisData', {
                        type: 'picsCreuxAnalysisData',
                        data: {
                            analysis: picsCreuxAnalysisData,
                            globalSummary: globalSummaryData,
                            sensitivity: sensitivity,
                            timestamp: Date.now()
                        }
                    });
                    break;

                case 'getPicsCreuxForRange':
                    const targetRange = data.rangeName;
                    const rangeSensitivity = parseFloat(data.sensitivity) || 0.5;
                    
                    if (!targetRange) {
                        socket.emit('error', { 
                            type: 'error', 
                            message: 'Nom de range requis' 
                        });
                        break;
                    }
                    
                    const percentageHistory = rangePercentageHistory.get(targetRange) || [];
                    if (percentageHistory.length < 3) {
                        socket.emit('picsCreuxRangeData', {
                            type: 'picsCreuxRangeData',
                            data: {
                                rangeName: targetRange,
                                events: [],
                                globalTrend: calculateGlobalTrend([], percentageHistory.length),
                                sensitivity: rangeSensitivity,
                                dataSize: percentageHistory.length,
                                message: 'Pas assez de données pour cette range'
                            }
                        });
                        break;
                    }
                    
                    const rangeEvents = detectPicsCreux(percentageHistory, rangeSensitivity);
                    const rangeGlobalTrend = calculateGlobalTrend(rangeEvents, percentageHistory.length);
                    
                    socket.emit('picsCreuxRangeData', {
                        type: 'picsCreuxRangeData',
                        data: {
                            rangeName: targetRange,
                            events: rangeEvents,
                            globalTrend: rangeGlobalTrend,
                            sensitivity: rangeSensitivity,
                            dataSize: percentageHistory.length,
                            timestamp: Date.now()
                        }
                    });
                    break;

                case 'clearPicsCreuxAnalysis':
                    picsCreuxAnalysis.clear();
                    globalTrendAnalysis = {};
                    socket.emit('picsCreuxAnalysisCleared', {
                        type: 'picsCreuxAnalysisCleared',
                        success: true,
                        message: 'Analyse des pics et creux réinitialisée'
                    });
                    break;

                // 🔥 HANDLERS SOCKET POUR LES CHUTES ET MONTÉES AVEC SYSTÈME DE POINTS CORRIGÉ
                case 'getChutesMonteeAnalysis':
                    const minLength = parseInt(data.minLength) || 3;
                    const minVariation = parseFloat(data.minVariation) || 1.0;
                    const chutesMonteeAnalysisData = analyzeChutesMonteeForAllRanges(minLength, minVariation);
                    const globalChuteMonteeSummaryData = getGlobalChuteMonteeSummary();
                    
                    socket.emit('chutesMonteeAnalysisData', {
                        type: 'chutesMonteeAnalysisData',
                        data: {
                            analysis: chutesMonteeAnalysisData,
                            globalSummary: globalChuteMonteeSummaryData,
                            parameters: { minLength, minVariation },
                            timestamp: Date.now()
                        }
                    });
                    break;

                case 'getChutesMonteeForRange':
                    const targetCMRange = data.rangeName;
                    const rangeMinLength = parseInt(data.minLength) || 3;
                    const rangeMinVariation = parseFloat(data.minVariation) || 1.0;
                    
                    if (!targetCMRange) {
                        socket.emit('error', { 
                            type: 'error', 
                            message: 'Nom de range requis' 
                        });
                        break;
                    }
                    
                    const cmPercentageHistory = rangePercentageHistory.get(targetCMRange) || [];
                    if (cmPercentageHistory.length < rangeMinLength) {
                        socket.emit('chutesMonteeRangeData', {
                            type: 'chutesMonteeRangeData',
                            data: {
                                rangeName: targetCMRange,
                                events: [],
                                globalTrend: calculateChuteMonteeTrend([], cmPercentageHistory.length),
                                parameters: { minLength: rangeMinLength, minVariation: rangeMinVariation },
                                dataSize: cmPercentageHistory.length,
                                message: 'Pas assez de données pour cette range'
                            }
                        });
                        break;
                    }
                    
                    const rangeCMEvents = detectChutesMonteeProgressives(cmPercentageHistory, rangeMinLength, rangeMinVariation);
                    const rangeCMGlobalTrend = calculateChuteMonteeTrend(rangeCMEvents, cmPercentageHistory.length);
                    
                    socket.emit('chutesMonteeRangeData', {
                        type: 'chutesMonteeRangeData',
                        data: {
                            rangeName: targetCMRange,
                            events: rangeCMEvents,
                            globalTrend: rangeCMGlobalTrend,
                            parameters: { minLength: rangeMinLength, minVariation: rangeMinVariation },
                            dataSize: cmPercentageHistory.length,
                            timestamp: Date.now()
                        }
                    });
                    break;

                case 'clearChutesMonteeAnalysis':
                    chutesMonteeAnalysis.clear();
                    globalChuteMonteeTrendAnalysis = {};
                    socket.emit('chutesMonteeAnalysisCleared', {
                        type: 'chutesMonteeAnalysisCleared',
                        success: true,
                        message: 'Analyse des chutes et montées réinitialisée'
                    });
                    break;

                // 🆕 HANDLERS SOCKET POUR LES PICS ET CREUX LÉGERS AVEC SYSTÈME DE POINTS CORRIGÉ
                case 'getPicsCreuxLegersAnalysis':
                    const minPlateauLength = parseInt(data.minPlateauLength) || 1;
                    const maxPlateauVariation = parseFloat(data.maxPlateauVariation) || 2.0;
                    const minInitialChange = parseFloat(data.minInitialChange) || 1.0;
                    const picsCreuxLegersAnalysisData = analyzePicsCreuxLegersForAllRanges(minPlateauLength, maxPlateauVariation, minInitialChange);
                    const globalPicsCreuxLegersSummaryData = getGlobalPicsCreuxLegersSummary();
                    
                    socket.emit('picsCreuxLegersAnalysisData', {
                        type: 'picsCreuxLegersAnalysisData',
                        data: {
                            analysis: picsCreuxLegersAnalysisData,
                            globalSummary: globalPicsCreuxLegersSummaryData,
                            parameters: { minPlateauLength, maxPlateauVariation, minInitialChange },
                            timestamp: Date.now()
                        }
                    });
                    break;

                case 'getPicsCreuxLegersForRange':
                    const targetPCLRange = data.rangeName;
                    const rangePlateauLength = parseInt(data.minPlateauLength) || 2;
                    const rangePlateauVariation = parseFloat(data.maxPlateauVariation) || 2.0;
                    const rangeInitialChange = parseFloat(data.minInitialChange) || 1.0;
                    
                    if (!targetPCLRange) {
                        socket.emit('error', { 
                            type: 'error', 
                            message: 'Nom de range requis' 
                        });
                        break;
                    }
                    
                    const pclPercentageHistory = rangePercentageHistory.get(targetPCLRange) || [];
                    if (pclPercentageHistory.length < rangePlateauLength + 2) {
                        socket.emit('picsCreuxLegersRangeData', {
                            type: 'picsCreuxLegersRangeData',
                            data: {
                                rangeName: targetPCLRange,
                                events: [],
                                globalTrend: calculateGlobalPicsCreuxLegersTrend([], pclPercentageHistory.length),
                                parameters: { minPlateauLength: rangePlateauLength, maxPlateauVariation: rangePlateauVariation, minInitialChange: rangeInitialChange },
                                dataSize: pclPercentageHistory.length,
                                message: 'Pas assez de données pour cette range'
                            }
                        });
                        break;
                    }
                    
                    const rangePCLEvents = detectPicsCreuxLegers(pclPercentageHistory, rangePlateauLength, rangePlateauVariation, rangeInitialChange);
                    const rangePCLGlobalTrend = calculateGlobalPicsCreuxLegersTrend(rangePCLEvents, pclPercentageHistory.length);
                    
                    socket.emit('picsCreuxLegersRangeData', {
                        type: 'picsCreuxLegersRangeData',
                        data: {
                            rangeName: targetPCLRange,
                            events: rangePCLEvents,
                            globalTrend: rangePCLGlobalTrend,
                            parameters: { minPlateauLength: rangePlateauLength, maxPlateauVariation: rangePlateauVariation, minInitialChange: rangeInitialChange },
                            dataSize: pclPercentageHistory.length,
                            timestamp: Date.now()
                        }
                    });
                    break;

                case 'clearPicsCreuxLegersAnalysis':
                    picsCreuxLegersAnalysis.clear();
                    globalPicsCreuxLegersTrendAnalysis = {};
                    socket.emit('picsCreuxLegersAnalysisCleared', {
                        type: 'picsCreuxLegersAnalysisCleared',
                        success: true,
                        message: 'Analyse des pics et creux légers réinitialisée'
                    });
                    break;

                // 🔥 HANDLERS SOCKET POUR LES PLATEAUX AVEC SYSTÈME DE POINTS CORRIGÉ
                case 'getPlateauxAnalysis':
                    const plateauMinLength = parseInt(data.minPlateauLength) || 1;
                    const plateauMaxVariation = parseFloat(data.maxVariation) || 1.5;
                    const plateauMinStability = parseInt(data.minStabilityDuration) || 1;
                    const plateauxAnalysisData = analyzePlateauxForAllRanges(plateauMinLength, plateauMaxVariation, plateauMinStability);
                    const globalPlateauxSummaryData = getGlobalPlateauxSummary();
                    
                    socket.emit('plateauxAnalysisData', {
                        type: 'plateauxAnalysisData',
                        data: {
                            analysis: plateauxAnalysisData,
                            globalSummary: globalPlateauxSummaryData,
                            parameters: { minPlateauLength: plateauMinLength, maxVariation: plateauMaxVariation, minStabilityDuration: plateauMinStability },
                            timestamp: Date.now()
                        }
                    });
                    break;

                case 'getPlateauxForRange':
                    const targetPlateauRange = data.rangeName;
                    const rangePlateauMinLength = parseInt(data.minPlateauLength) || 1;
                    const rangePlateauMaxVariation = parseFloat(data.maxVariation) || 1.5;
                    const rangePlateauMinStability = parseInt(data.minStabilityDuration) || 1;
                    
                    if (!targetPlateauRange) {
                        socket.emit('error', { 
                            type: 'error', 
                            message: 'Nom de range requis' 
                        });
                        break;
                    }
                    
                    const plateauPercentageHistory = rangePercentageHistory.get(targetPlateauRange) || [];
                    if (plateauPercentageHistory.length < rangePlateauMinLength) {
                        socket.emit('plateauxRangeData', {
                            type: 'plateauxRangeData',
                            data: {
                                rangeName: targetPlateauRange,
                                plateaux: [],
                                globalTrend: calculatePlateauxGlobalTrend([], [], [], [], plateauPercentageHistory.length),
                                parameters: { minPlateauLength: rangePlateauMinLength, maxVariation: rangePlateauMaxVariation, minStabilityDuration: rangePlateauMinStability },
                                dataSize: plateauPercentageHistory.length,
                                message: 'Pas assez de données pour cette range'
                            }
                        });
                        break;
                    }
                    
                    const picsCreuxData = picsCreuxAnalysis.get(targetPlateauRange);
                    const chutesMonteeData = chutesMonteeAnalysis.get(targetPlateauRange);
                    const picsCreuxLegersData = picsCreuxLegersAnalysis.get(targetPlateauRange);
                    
                    const picsCreux = picsCreuxData ? picsCreuxData.events || [] : [];
                    const chutesMontees = chutesMonteeData ? chutesMonteeData.events || [] : [];
                    const picsCreuxLegers = picsCreuxLegersData ? picsCreuxLegersData.events || [] : [];
                    
                    const rangePlateaux = detectPlateaux(plateauPercentageHistory, rangePlateauMinLength, rangePlateauMaxVariation, rangePlateauMinStability);
                    const rangePlateauGlobalTrend = calculatePlateauxGlobalTrend(rangePlateaux, picsCreux, chutesMontees, picsCreuxLegers, plateauPercentageHistory.length);
                    
                    socket.emit('plateauxRangeData', {
                        type: 'plateauxRangeData',
                        data: {
                            rangeName: targetPlateauRange,
                            plateaux: rangePlateaux,
                            globalTrend: rangePlateauGlobalTrend,
                            parameters: { minPlateauLength: rangePlateauMinLength, maxVariation: rangePlateauMaxVariation, minStabilityDuration: rangePlateauMinStability },
                            dataSize: plateauPercentageHistory.length,
                            timestamp: Date.now()
                        }
                    });
                    break;

                case 'clearPlateauxAnalysis':
                    plateauxAnalysis.clear();
                    globalPlateauxTrendAnalysis = {};
                    socket.emit('plateauxAnalysisCleared', {
                        type: 'plateauxAnalysisCleared',
                        success: true,
                        message: 'Analyse des plateaux réinitialisée'
                    });
                    break;

                // 🌡️ HANDLERS SOCKET POUR LE THERMOMÈTRE DE SITUATION CORRIGÉ AVEC STABILITÉ
                case 'getThermometreAnalysis':
                    const thermometreAnalysisData = analyzeThermometreForAllRanges();
                    const globalThermometreSummaryData = getGlobalThermometreSummary();
                    
                    socket.emit('thermometreAnalysisData', {
                        type: 'thermometreAnalysisData',
                        data: {
                            analysis: thermometreAnalysisData,
                            globalSummary: globalThermometreSummaryData,
                            timestamp: Date.now()
                        }
                    });
                    break;

                case 'getThermometreForRange':
                    const targetThermRange = data.rangeName;
                    
                    if (!targetThermRange) {
                        socket.emit('error', { 
                            type: 'error', 
                            message: 'Nom de range requis' 
                        });
                        break;
                    }
                    
                    const thermZoneData = calculateZonePercentages(targetThermRange);
                    
                    socket.emit('thermometreRangeData', {
                        type: 'thermometreRangeData',
                        data: {
                            rangeName: targetThermRange,
                            zoneData: thermZoneData,
                            timestamp: Date.now()
                        }
                    });
                    break;

                case 'clearThermometreAnalysis':
                    thermometrePointsHistory.clear();
                    socket.emit('thermometreAnalysisCleared', {
                        type: 'thermometreAnalysisCleared',
                        success: true,
                        message: 'Analyse du thermomètre de situation réinitialisée'
                    });
                    break;

                // 🆕 HANDLERS SOCKET POUR LE CLASSEMENT DES POURCENTAGES
                case 'getPercentageRanking':
                    const globalRankingData = getGlobalPercentageRankingSummary();
                    
                    socket.emit('percentageRankingData', {
                        type: 'percentageRankingData',
                        data: {
                            globalRanking: globalRankingData,
                            timestamp: Date.now()
                        }
                    });
                    break;

                case 'getPercentageRankingForRange':
                    const targetRankingRange = data.rangeName;
                    const tolerance = parseFloat(data.tolerance) || 0.2;
                    
                    if (!targetRankingRange) {
                        socket.emit('error', { 
                            type: 'error', 
                            message: 'Nom de range requis' 
                        });
                        break;
                    }
                    
                    const rankingData = percentageRankingHistory.get(targetRankingRange);
                    const frequencyData = percentageFrequencyAnalysis.get(targetRankingRange);
                    
                    if (!rankingData || !frequencyData) {
                        socket.emit('percentageRankingRangeData', {
                            type: 'percentageRankingRangeData',
                            data: {
                                rangeName: targetRankingRange,
                                error: 'Range non trouvée ou pas encore analysée',
                                timestamp: Date.now()
                            }
                        });
                        break;
                    }
                    
                    socket.emit('percentageRankingRangeData', {
                        type: 'percentageRankingRangeData',
                        data: {
                            rangeName: targetRankingRange,
                            ranking: rankingData,
                            frequency: frequencyData,
                            parameters: { tolerance },
                            timestamp: Date.now()
                        }
                    });
                    break;

                case 'searchPercentageInRange':
                    const searchRange = data.rangeName;
                    const targetPercentage = parseFloat(data.percentage);
                    const searchTolerance = parseFloat(data.tolerance) || 0.1;
                    
                    if (!searchRange || isNaN(targetPercentage)) {
                        socket.emit('error', { 
                            type: 'error', 
                            message: 'Nom de range et pourcentage requis' 
                        });
                        break;
                    }
                    
                    const searchFrequencyData = percentageFrequencyAnalysis.get(searchRange);
                    
                    if (!searchFrequencyData) {
                        socket.emit('percentageSearchResult', {
                            type: 'percentageSearchResult',
                            data: {
                                rangeName: searchRange,
                                searchedPercentage: targetPercentage,
                                tolerance: searchTolerance,
                                matches: [],
                                totalMatches: 0,
                                error: 'Range non trouvée',
                                timestamp: Date.now()
                            }
                        });
                        break;
                    }
                    
                    const matches = searchFrequencyData.classementDetaille.filter(item => 
                        Math.abs(item.percentage - targetPercentage) <= searchTolerance
                    );
                    
                    socket.emit('percentageSearchResult', {
                        type: 'percentageSearchResult',
                        data: {
                            rangeName: searchRange,
                            searchedPercentage: targetPercentage,
                            tolerance: searchTolerance,
                            matches: matches,
                            totalMatches: matches.length,
                            timestamp: Date.now()
                        }
                    });
                    break;

                case 'getTopPercentagesForRange':
                    const topRange = data.rangeName;
                    const limit = parseInt(data.limit) || 10;
                    
                    if (!topRange) {
                        socket.emit('error', { 
                            type: 'error', 
                            message: 'Nom de range requis' 
                        });
                        break;
                    }
                    
                    const topFrequencyData = percentageFrequencyAnalysis.get(topRange);
                    
                    if (!topFrequencyData) {
                        socket.emit('topPercentagesData', {
                            type: 'topPercentagesData',
                            data: {
                                rangeName: topRange,
                                topPercentages: [],
                                totalUniquePercentages: 0,
                                error: 'Range non trouvée',
                                timestamp: Date.now()
                            }
                        });
                        break;
                    }
                    
                    const topPercentages = topFrequencyData.classementDetaille.slice(0, limit);
                    
                    socket.emit('topPercentagesData', {
                        type: 'topPercentagesData',
                        data: {
                            rangeName: topRange,
                            topPercentages: topPercentages,
                            totalUniquePercentages: topFrequencyData.classementDetaille.length,
                            modePercentage: topFrequencyData.statistiques.modePercentage,
                            stabilityIndex: topFrequencyData.indexStabilite,
                            timestamp: Date.now()
                        }
                    });
                    break;

                case 'clearPercentageRanking':
                    percentageRankingHistory.clear();
                    percentageFrequencyAnalysis.clear();
                    socket.emit('percentageRankingCleared', {
                        type: 'percentageRankingCleared',
                        success: true,
                        message: 'Classement des pourcentages réinitialisé'
                    });
                    break;

                default:
                    socket.emit('error', { type: 'error', message: `Type de message non reconnu: ${messageType}` });
                    break;
            }
        } catch (error) {
            console.error('Erreur lors du traitement du message:', error);
            socket.emit('error', { type: 'error', message: `Erreur: ${error.message}` });
        }
    });
    
    socket.on('disconnect', () => {
        console.log('Client déconnecté');
    });
});

const port = process.env.PORT || 5000;

async function startServer() {
    try {
        await loadConfig();
        
        console.log('🔐 Récupération des informations utilisateur...');
        await fetchUserAuth();
        
        console.log('🔑 Récupération du token...');
        const tokenSuccess = await refreshToken();
        
        if (tokenSuccess) {
            console.log('✅ Token récupéré');
            
            if (isPolling) {
                startWebSocketConnection();
                startDataSender();
            }
        }
        
        server.listen(port, '0.0.0.0', () => {
            console.log(`🚀 Serveur PRÉDICTIF + ANALYSE COMPLÈTE démarré sur le port ${port}`);
            console.log(`🎯 SYSTÈME DE PRÉDICTION DE CRASH ACTIVÉ:`);
            console.log(`   📊 Analyse dynamique du classement`);
            console.log(`   ⚡ Calcul de momentum et accélération`);
            console.log(`   ⚔️ Zones de bataille concurrentielle`);
            console.log(`   🔄 Patterns temporels et cycles`);
            console.log(`   🎲 Matrices de transition entre rangs`);
            console.log(`   🎯 PRÉDICTION PROBABILISTE FINALE`);
            console.log(`🔍 ANALYSES AVANCÉES ACTIVÉES:`);
            console.log(`   📈 Détection des pics et creux classiques`);
            console.log(`   🔥 Analyse des chutes et montées progressives`);
            console.log(`   🆕 Détection des pics et creux légers`);
            console.log(`   🔥 Analyse des plateaux de stabilité`);
            console.log(`   🌡️ Thermomètre de situation avec zones`);
            console.log(`   🆕 Classement intelligent des pourcentages`);
            console.log(`🎯 FONCTIONNALITÉS PRINCIPALES:`);
            
            currentRanges.forEach(range => {
                console.log(`   - ${range.name}: Limite ${range.limit || 1000} entrées`);
            });
            
            console.log(`   - Historique total: ${historySize} valeurs`);
            console.log(`   - CustomSizes: Médiane=${customSizes.median}, Moyenne=${customSizes.mean}`);
            console.log(`   - Redémarrage automatique: ${autoRestartEnabled ? 'ACTIVÉ' : 'DÉSACTIVÉ'}`);
        });
    } catch (error) {
        console.error('Erreur lors du démarrage:', error);
        setTimeout(startServer, 5000);
    }
}

startServer();

process.on('SIGINT', () => {
    console.log('Arrêt du serveur...');
    stopPolling();
    process.exit(0);
});

process.on('SIGTERM', () => {
    console.log('Arrêt du serveur...');
    stopPolling();
    process.exit(0);
});

