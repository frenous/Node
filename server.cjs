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
const CRASH_HISTORY_FILE = path.join(__dirname, 'crash-history.txt');
const CRASH_HISTORY_BACKUP_FILE = path.join(__dirname, 'crash-history-backup.txt');

// Variables globales pour la configuration
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
    "medianHistory": [],
    "meanHistory": [],
    "authToken": DEFAULT_AUTH_TOKEN,
    "rankingMethod": "current",
    "autoStartPolling": false
};

// Variables d'état du serveur
let isPolling = false;
let pollingFrequency = 1000;
let historySize = 10000;
let customSizes = { median: 50, mean: 100 };
let crashHistory = [];
let users = { 'admin': 'password' };
let authToken = DEFAULT_AUTH_TOKEN;
let rankingMethod = "current";
let autoStartPolling = false;

// Historiques des médianes et moyennes
let medianHistory = [];
let meanHistory = [];

// Variables WebSocket et monitoring
let wsConnection = null;
let pingInterval = null;
let dataSenderInterval = null;
let currentToken = null;
let tokenExpireTime = null;
let tokenRefreshInterval = null;

// Variables pour le monitoring
let lastCoefficientUpdate = Date.now();
let connectionMonitorTimer = null;
let syncCheckInterval = null;
let connectionState = 'DISCONNECTED';

// Variables pour éviter la pollution par coefficients en progression
let isReconnecting = false;
let blockCoefficientCapture = false;
let reconnectionSyncDone = false;

const WEBSOCKET_BASE_URL = "wss://crash-gateway-grm-cr.100hp.app/websocket/lifecycle";
const TOKEN_REFRESH_URL = "https://crash-gateway-grm-cr.100hp.app/user/token";
const USER_AUTH_URL = "https://crash-gateway-grm-cr.100hp.app/user/auth";
const BALANCE_URL = "https://crash-gateway-grm-cr.100hp.app/user/balance";
const BET_PLACE_URL = "https://crash-gateway-grm-cr.100hp.app/bets/place";
const HISTORY_URL = "https://crash-gateway-grm-cr.100hp.app/history";

// Informations utilisateur
let userInfo = {
    userId: null,
    userName: "Utilisateur-Inconnu",
    sessionId: "194dd3f3-b267-4f1b-9856-15bb0db1e9b2",
    customerId: "077dee8d-c923-4c02-9bee-757573662e69",
    balance: 0
};

// Coefficient en cours
let currentCoefficient = null;

let currentRanges = [
  {  
    "name": "1.00 - 1.10",  
    "min": 1.0,  
    "max": 1.1,  
    "color": "#3498db",  
    "limit": 20  
  },  
  {  
    "name": "1.10 - 1.35",  
    "min": 1.1,  
    "max": 1.35,  
    "color": "#b05695",  
    "limit": 20  
  },  
  {  
    "name": "1.35 - 1.75",  
    "min": 1.35,  
    "max": 1.75,  
    "color": "#c2c480",  
    "limit": 20  
  },  
  {  
    "name": "1.75 - 2.50",  
    "min": 1.75,  
    "max": 2.5,  
    "color": "#4b3de3",  
    "limit": 20  
  },  
  {  
    "name": "2.50 - 4.50",  
    "min": 2.5,  
    "max": 4.5,  
    "color": "#1a8509",  
    "limit": 20  
  },  
  {  
    "name": "4.50 - 35.00",  
    "min": 4.5,  
    "max": 35.0,  
    "color": "#8a2b2b",  
    "limit": 20  
  }  
];

// Variables pour les pourcentages par plage
let rangePercentageHistory = new Map();

// Variables pour l'envoi de données
let pendingValues = [];
let dataSendActive = false;

// Variables pour le classement des plages
let rangeRankings = [];
let previousRankings = [];

// Variables pour l'équilibre des pourcentages
let balanceEquilibriumHistory = [];
let currentBalanceEquilibrium = 0;

// Contrôle de redémarrage automatique
let autoRestartEnabled = true;
let restartTimeout = null;

// ========== NOUVELLES FONCTIONS D'ATTENTE DE CONNECTIVITÉ ==========

// NOUVELLE FONCTION: Attendre la connectivité internet avec retry intelligent
async function waitForInternetConnectivity(maxAttempts = 30, retryInterval = 2000) {
    console.log('🌐 Attente de la connectivité internet...');
    
    for (let attempt = 1; attempt <= maxAttempts; attempt++) {
        try {
            console.log(`🔄 Tentative ${attempt}/${maxAttempts} de vérification de connectivité...`);
            
            // Tester plusieurs endpoints pour plus de fiabilité
            const testUrls = [
                'https://httpbin.org/status/200',
                'https://www.google.com',
                'https://cloudflare.com',
                'https://8.8.8.8'
            ];
            
            for (const url of testUrls) {
                try {
                    const response = await axios.get(url, { 
                        timeout: 5000,
                        headers: {
                            'User-Agent': 'Mozilla/5.0 (compatible; ConnectivityCheck/1.0)'
                        }
                    });
                    
                    if (response.status === 200 || response.status === 204) {
                        console.log(`✅ Connectivité internet confirmée via ${url}`);
                        return true;
                    }
                } catch (urlError) {
                    // Continuer avec l'URL suivante
                    continue;
                }
            }
            
            console.log(`❌ Tentative ${attempt} échouée - Nouvelle tentative dans ${retryInterval/1000}s...`);
            
            // Notifier les clients de l'état d'attente
            io.emit('connectionWaiting', {
                type: 'connectionWaiting',
                attempt: attempt,
                maxAttempts: maxAttempts,
                nextRetryIn: retryInterval / 1000,
                message: `Attente de connexion internet (${attempt}/${maxAttempts})`
            });
            
            // Attendre avant la prochaine tentative avec backoff exponentiel
            const delay = Math.min(retryInterval * Math.pow(1.2, attempt - 1), 10000);
            await new Promise(resolve => setTimeout(resolve, delay));
            
        } catch (error) {
            console.log(`❌ Erreur tentative ${attempt}: ${error.message}`);
        }
    }
    
    console.log('❌ Impossible d\'établir une connexion internet après toutes les tentatives');
    return false;
}

// NOUVELLE FONCTION: Attendre le token avec retry
async function waitForValidToken(maxAttempts = 10, retryInterval = 3000) {
    console.log('🔑 Attente d\'un token valide...');
    
    for (let attempt = 1; attempt <= maxAttempts; attempt++) {
        try {
            console.log(`🔄 Tentative ${attempt}/${maxAttempts} de récupération du token...`);
            
            const tokenSuccess = await refreshToken();
            if (tokenSuccess && currentToken) {
                console.log('✅ Token valide obtenu');
                return true;
            }
            
            console.log(`❌ Échec tentative ${attempt} - Nouvelle tentative dans ${retryInterval/1000}s...`);
            
            // Notifier les clients
            io.emit('tokenWaiting', {
                type: 'tokenWaiting',
                attempt: attempt,
                maxAttempts: maxAttempts,
                nextRetryIn: retryInterval / 1000,
                message: `Récupération du token (${attempt}/${maxAttempts})`
            });
            
            await new Promise(resolve => setTimeout(resolve, retryInterval));
            
        } catch (error) {
            console.log(`❌ Erreur token tentative ${attempt}: ${error.message}`);
        }
    }
    
    console.log('❌ Impossible d\'obtenir un token valide après toutes les tentatives');
    return false;
}

// ========== FONCTIONS DE SÉCURITÉ AMÉLIORÉES ==========

// FONCTION DE SAUVEGARDE DE SÉCURITÉ
async function createBackupBeforeOperation(operationName) {
    try {
        console.log(`🛡️  Création d'une sauvegarde de sécurité avant: ${operationName}`);
        
        const backupData = {
            timestamp: new Date().toISOString(),
            operation: operationName,
            historySize: crashHistory.length,
            crashHistory: crashHistory
        };
        
        const jsonData = JSON.stringify(backupData, null, 2);
        await fs.writeFile(CRASH_HISTORY_BACKUP_FILE, jsonData, 'utf8');
        
        console.log(`✅ Sauvegarde de sécurité créée: ${crashHistory.length} entrées`);
        return true;
    } catch (error) {
        console.error('❌ ERREUR lors de la sauvegarde de sécurité:', error);
        return false;
    }
}

// FONCTION DE RESTAURATION DEPUIS LA SAUVEGARDE
async function restoreFromBackup() {
    try {
        if (fsSync.existsSync(CRASH_HISTORY_BACKUP_FILE)) {
            console.log('🔄 Restauration depuis la sauvegarde de sécurité...');
            
            const data = await fs.readFile(CRASH_HISTORY_BACKUP_FILE, 'utf8');
            const backupData = JSON.parse(data);
            
            if (backupData.crashHistory && Array.isArray(backupData.crashHistory)) {
                crashHistory = backupData.crashHistory;
                console.log(`✅ Restauration réussie: ${crashHistory.length} entrées restaurées`);
                console.log(`📅 Sauvegarde datée du: ${backupData.timestamp}`);
                return true;
            }
        }
        return false;
    } catch (error) {
        console.error('❌ Erreur lors de la restauration:', error);
        return false;
    }
}

// FONCTION DE VALIDATION DE CONNECTIVITÉ (SIMPLIFIÉE)
async function checkInternetConnectivity() {
    try {
        const response = await axios.get('https://httpbin.org/status/200', { timeout: 5000 });
        return true;
    } catch (error) {
        return false;
    }
}

// FONCTION DE VALIDATION DES DONNÉES API
function validateApiData(apiData) {
    if (!apiData || !Array.isArray(apiData)) {
        console.log('❌ Données API invalides: pas un tableau');
        return false;
    }
    
    if (apiData.length === 0) {
        console.log('❌ Données API vides');
        return false;
    }
    
    const sampleItem = apiData[0];
    if (!sampleItem.finalValues || !Array.isArray(sampleItem.finalValues)) {
        console.log('❌ Structure API invalide: finalValues manquant');
        return false;
    }
    
    console.log(`✅ Données API valides: ${apiData.length} entrées`);
    return true;
}

// FONCTION POUR SAUVEGARDER L'HISTORIQUE DES CRASH
async function saveCrashHistoryToFile() {
    try {
        console.log('💾 Sauvegarde de l\'historique des crash...');
        
        if (fsSync.existsSync(CRASH_HISTORY_FILE)) {
            const oldData = await fs.readFile(CRASH_HISTORY_FILE, 'utf8');
            await fs.writeFile(CRASH_HISTORY_FILE + '.old', oldData, 'utf8');
        }
        
        const dataToSave = {
            timestamp: new Date().toISOString(),
            historySize: crashHistory.length,
            crashHistory: crashHistory
        };
        
        const jsonData = JSON.stringify(dataToSave, null, 2);
        await fs.writeFile(CRASH_HISTORY_FILE, jsonData, 'utf8');
        
        console.log(`✅ Historique sauvegardé: ${crashHistory.length} entrées dans ${CRASH_HISTORY_FILE}`);
    } catch (error) {
        console.error('❌ Erreur lors de la sauvegarde de l\'historique:', error);
    }
}

// FONCTION POUR CHARGER L'HISTORIQUE DES CRASH
async function loadCrashHistoryFromFile() {
    try {
        if (fsSync.existsSync(CRASH_HISTORY_FILE)) {
            console.log('📂 Chargement de l\'historique des crash depuis le fichier...');
            
            const data = await fs.readFile(CRASH_HISTORY_FILE, 'utf8');
            const savedData = JSON.parse(data);
            
            if (savedData.crashHistory && Array.isArray(savedData.crashHistory)) {
                crashHistory = savedData.crashHistory;
                
                console.log(`✅ Historique chargé: ${crashHistory.length} entrées`);
                console.log(`📅 Dernière sauvegarde: ${savedData.timestamp}`);
                console.log(`🔢 Échantillon des 5 dernières côtes: ${crashHistory.slice(0, 5).map(entry => typeof entry === 'object' ? entry.value : entry)}`);
                
                return true;
            } else {
                console.log('⚠️  Format de fichier invalide, historique ignoré');
                return false;
            }
        } else {
            console.log('📝 Aucun fichier d\'historique trouvé, démarrage avec historique vide');
            return false;
        }
    } catch (error) {
        console.error('❌ Erreur lors du chargement de l\'historique:', error);
        return false;
    }
}

// SYNCHRONISATION INTELLIGENTE AU DÉMARRAGE (AVEC ATTENTE)
async function performStartupIntelligentSync() {
    try {
        console.log('🚀 SYNCHRONISATION INTELLIGENTE AU DÉMARRAGE AVEC ATTENTE...');
        
        // Attendre la connectivité internet
        const hasInternet = await waitForInternetConnectivity();
        if (!hasInternet) {
            console.log('🛡️  Impossible d\'obtenir une connexion internet - Préservation des données locales');
            return { success: false, action: 'no_internet_after_wait', count: 0 };
        }
        
        // Attendre un token valide
        if (!currentToken) {
            console.log('🔑 Token manquant - Attente d\'un token valide...');
            const hasToken = await waitForValidToken();
            if (!hasToken) {
                console.log('🛡️  Impossible d\'obtenir un token - Synchronisation annulée');
                return { success: false, action: 'no_token_after_wait', count: 0 };
            }
        }
        
        if (crashHistory.length === 0) {
            console.log('📥 Historique local vide - Chargement depuis l\'API autorisé');
        } else {
            const backupCreated = await createBackupBeforeOperation('startup_sync');
            if (!backupCreated) {
                console.log('❌ Impossible de créer une sauvegarde - Synchronisation annulée');
                return { success: false, action: 'backup_failed', count: 0 };
            }
        }
        
        console.log('🚀 SYNCHRONISATION INTELLIGENTE AU DÉMARRAGE...');
        connectionState = 'SYNCING_DATA';
        
        const response = await axios.get(HISTORY_URL, {
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
            },
            timeout: 10000
        });

        if (!validateApiData(response.data)) {
            console.log('🛡️  Données API invalides - Synchronisation annulée');
            return { success: false, action: 'invalid_api_data', count: 0 };
        }

        const apiLastTwenty = response.data.slice(0, 20).map(item => ({
            value: item.finalValues[0],
            hash: item.hash,
            id: item.id
        }));
        
        console.log('🎯 COMPARAISON AU DÉMARRAGE (AVEC HASHES):');
        console.log('   API (20 dernières):', apiLastTwenty.map(x => `${x.value}(${x.hash ? x.hash.substring(0, 8) : 'NO_HASH'})`));
        
        if (crashHistory.length === 0) {
            console.log('📥 Historique local vide - Chargement complet depuis l\'API');
            await loadFullHistoryFromAPI(response.data);
            return { success: true, action: 'loaded_full', count: response.data.length };
        } else {
            const ourLastTwenty = crashHistory.slice(0, 20).map(item => ({
                value: typeof item === 'object' ? item.value : item,
                hash: typeof item === 'object' ? item.hash : null
            }));
            
            console.log('   Local (20 dernières):', ourLastTwenty.map(x => `${x.value}(${x.hash ? x.hash.substring(0, 8) : 'NO_HASH'})`));
            
            const syncPoint = findBestSyncPointByHash(apiLastTwenty, ourLastTwenty);
            
            if (syncPoint.found) {
                console.log(`🎯 Point de synchronisation HASH trouvé: hash ${syncPoint.hash.substring(0, 12)}... (valeur: ${syncPoint.value}) à l'index API ${syncPoint.apiIndex}, index local ${syncPoint.ourIndex}`);
                
                if (syncPoint.apiIndex > 0) {
                    const missingData = response.data.slice(0, syncPoint.apiIndex);
                    console.log(`📥 Ajout de ${missingData.length} côtes manquantes au démarrage`);
                    
                    missingData.reverse().forEach(item => {
                        const dataEntry = {
                            value: item.finalValues[0],
                            hash: item.hash,
                            id: item.id,
                            timestamp: Date.now()
                        };
                        crashHistory.unshift(dataEntry);
                        console.log(`➕ Ajout: ${item.finalValues[0]} (hash: ${item.hash ? item.hash.substring(0, 8) + '...' : 'N/A'})`);
                    });
                    
                    crashHistory = crashHistory.slice(0, historySize);
                    
                    return { success: true, action: 'synced', count: missingData.length };
                } else {
                    console.log('✅ Déjà synchronisé - Aucune action nécessaire');
                    return { success: true, action: 'already_synced', count: 0 };
                }
            } else {
                console.log('⚠️  Aucun point de synchronisation trouvé par hash - Conservation des données locales');
                return { success: true, action: 'kept_local', count: 0 };
            }
        }
        
    } catch (error) {
        console.error('❌ Erreur lors de la synchronisation de démarrage:', error.message);
        
        if (crashHistory.length === 0) {
            console.log('🔄 Tentative de restauration depuis la sauvegarde...');
            await restoreFromBackup();
        }
        
        return { success: false, action: 'error', count: 0, error: error.message };
    }
}

// NOUVELLE FONCTION: SYNCHRONISATION INTELLIGENTE LORS DU DÉMARRAGE MANUEL DU POLLING (AVEC ATTENTE)
async function performPollingStartIntelligentSync() {
    try {
        console.log('🎯 SYNCHRONISATION INTELLIGENTE - DÉMARRAGE MANUEL DU POLLING AVEC ATTENTE ET HASHES');
        
        // Attendre la connectivité internet avec notification des clients
        io.emit('syncStatus', {
            type: 'syncStatus',
            success: false,
            message: 'Vérification de la connectivité internet...',
            waiting: true
        });
        
        const hasInternet = await waitForInternetConnectivity();
        if (!hasInternet) {
            console.log('🛡️  Impossible d\'obtenir une connexion internet après attente');
            io.emit('syncStatus', {
                type: 'syncStatus',
                success: false,
                message: 'Impossible d\'établir une connexion internet après plusieurs tentatives'
            });
            return { success: false, action: 'no_internet_after_wait', count: 0 };
        }
        
        // Attendre un token valide
        if (!currentToken) {
            console.log('🛡️  Pas de token disponible - Attente de récupération...');
            io.emit('syncStatus', {
                type: 'syncStatus',
                success: false,
                message: 'Récupération du token d\'authentification...',
                waiting: true
            });
            
            const hasToken = await waitForValidToken();
            if (!hasToken) {
                console.log('❌ Impossible de récupérer le token pour la synchronisation');
                io.emit('syncStatus', {
                    type: 'syncStatus',
                    success: false,
                    message: 'Impossible de récupérer le token d\'authentification après plusieurs tentatives'
                });
                return { success: false, action: 'no_token_after_wait', count: 0 };
            }
        }
        
        // Créer une sauvegarde de sécurité avant la synchronisation
        if (crashHistory.length > 0) {
            const backupCreated = await createBackupBeforeOperation('polling_start_sync');
            if (!backupCreated) {
                console.log('❌ Impossible de créer une sauvegarde - Synchronisation annulée');
                io.emit('syncStatus', {
                    type: 'syncStatus',
                    success: false,
                    message: 'Impossible de créer une sauvegarde de sécurité'
                });
                return { success: false, action: 'backup_failed', count: 0 };
            }
        }
        
        connectionState = 'SYNCING_DATA';
        io.emit('connectionStatus', {
            type: 'connectionStatus',
            state: connectionState,
            message: 'Synchronisation intelligente par hash en cours...'
        });
        
        const response = await axios.get(HISTORY_URL, {
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
            },
            timeout: 15000
        });

        if (!validateApiData(response.data)) {
            console.log('🛡️  Données API invalides - Synchronisation du polling annulée');
            io.emit('syncStatus', {
                type: 'syncStatus',
                success: false,
                message: 'Données API invalides reçues'
            });
            return { success: false, action: 'invalid_api_data', count: 0 };
        }

        const apiLastTwenty = response.data.slice(0, 20).map(item => ({
            value: item.finalValues[0],
            hash: item.hash,
            id: item.id
        }));
        
        console.log('🎯 COMPARAISON POLLING MANUEL (AVEC HASHES):');
        console.log('   API (20 dernières):', apiLastTwenty.map(x => `${x.value}(${x.hash ? x.hash.substring(0, 8) : 'NO_HASH'})`));
        
        if (crashHistory.length === 0) {
            console.log('📥 Historique local vide - Chargement complet depuis l\'API');
            await loadFullHistoryFromAPI(response.data);
            
            io.emit('syncStatus', {
                type: 'syncStatus',
                success: true,
                message: `Historique chargé avec succès: ${response.data.length} entrées`,
                count: response.data.length,
                action: 'loaded_full'
            });
            
            return { success: true, action: 'loaded_full', count: response.data.length };
        } else {
            const ourLastTwenty = crashHistory.slice(0, 20).map(item => ({
                value: typeof item === 'object' ? item.value : item,
                hash: typeof item === 'object' ? item.hash : null
            }));
            
            console.log('   Local (20 dernières):', ourLastTwenty.map(x => `${x.value}(${x.hash ? x.hash.substring(0, 8) : 'NO_HASH'})`));
            
            const syncPoint = findBestSyncPointByHash(apiLastTwenty, ourLastTwenty);
            
            if (syncPoint.found) {
                console.log(`🎯 Point de synchronisation HASH trouvé: hash ${syncPoint.hash.substring(0, 12)}... (valeur: ${syncPoint.value}) à l'index API ${syncPoint.apiIndex}, index local ${syncPoint.ourIndex}`);
                
                if (syncPoint.apiIndex > 0) {
                    const missingData = response.data.slice(0, syncPoint.apiIndex);
                    console.log(`📥 Ajout de ${missingData.length} côtes manquantes lors du démarrage du polling`);
                    
                    missingData.reverse().forEach(item => {
                        const dataEntry = {
                            value: item.finalValues[0],
                            hash: item.hash,
                            id: item.id,
                            timestamp: Date.now()
                        };
                        crashHistory.unshift(dataEntry);
                        console.log(`➕ Ajout: ${item.finalValues[0]} (hash: ${item.hash ? item.hash.substring(0, 8) + '...' : 'N/A'})`);
                    });
                    
                    crashHistory = crashHistory.slice(0, historySize);
                    
                    // Recalculer les statistiques après synchronisation
                    calculateAndRankRanges();
                    updateMedianMeanHistories();
                    
                    io.emit('syncStatus', {
                        type: 'syncStatus',
                        success: true,
                        message: `Synchronisation par hash réussie: ${missingData.length} nouvelles côtes récupérées`,
                        count: missingData.length,
                        action: 'synced'
                    });
                    
                    // Envoyer les données mises à jour aux clients
                    io.emit('dataSynced', {
                        type: 'dataSynced',
                        message: `Polling démarré avec synchronisation par hash: ${missingData.length} côtes récupérées`,
                        count: missingData.length,
                        newHistory: crashHistory.map(entry => typeof entry === 'object' ? entry.value : entry)
                    });
                    
                    return { success: true, action: 'synced', count: missingData.length };
                } else {
                    console.log('✅ Déjà synchronisé - Aucune action nécessaire pour le polling');
                    io.emit('syncStatus', {
                        type: 'syncStatus',
                        success: true,
                        message: 'Déjà synchronisé avec l\'API - Polling démarré',
                        count: 0,
                        action: 'already_synced'
                    });
                    return { success: true, action: 'already_synced', count: 0 };
                }
            } else {
                console.log('⚠️  Aucun point de synchronisation trouvé par hash - Conservation des données locales pour le polling');
                io.emit('syncStatus', {
                    type: 'syncStatus',
                    success: true,
                    message: 'Polling démarré avec les données locales (pas de point de synchronisation trouvé)',
                    count: 0,
                    action: 'kept_local'
                });
                return { success: true, action: 'kept_local', count: 0 };
            }
        }
        
    } catch (error) {
        console.error('❌ Erreur lors de la synchronisation du polling:', error.message);
        
        io.emit('syncStatus', {
            type: 'syncStatus',
            success: false,
            message: `Erreur de synchronisation: ${error.message}`,
            action: 'error'
        });
        
        if (crashHistory.length === 0) {
            console.log('🔄 Tentative de restauration depuis la sauvegarde...');
            await restoreFromBackup();
        }
        
        return { success: false, action: 'error', count: 0, error: error.message };
    }
}

// SYSTÈME DE MONITORING DES COEFFICIENTS
function resetConnectionMonitor() {
    if (connectionMonitorTimer) {
        clearTimeout(connectionMonitorTimer);
    }
    
    connectionMonitorTimer = setTimeout(() => {
        console.log('❌ Aucun coefficient reçu depuis 20 secondes - Connexion probablement perdue');
        handleConnectionLoss();
    }, 20000);
}

function onCoefficientUpdate() {
    lastCoefficientUpdate = Date.now();
    connectionState = 'CONNECTED';
    resetConnectionMonitor();
    
    io.emit('connectionStatus', {
        type: 'connectionStatus',
        state: connectionState,
        lastUpdate: lastCoefficientUpdate
    });
}

// GESTION DE PERTE DE CONNEXION
async function handleConnectionLoss() {
    console.log('🚨 Gestion de la perte de connexion...');
    connectionState = 'CHECKING_SYNC';
    smartReconnectWebSocket();
}

// SYNCHRONISATION IMMÉDIATE APRÈS RECONNEXION (AVEC ATTENTE)
async function performImmediateReconnectionSync() {
    try {
        console.log('🚀 SYNCHRONISATION IMMÉDIATE APRÈS RECONNEXION AVEC ATTENTE ET HASHES');
        
        // Attendre la connectivité internet sans timeout trop strict
        const hasInternet = await waitForInternetConnectivity(10, 1000);
        if (!hasInternet) {
            console.log('🛡️  Pas de connectivité après reconnexion - Synchronisation annulée');
            blockCoefficientCapture = false;
            reconnectionSyncDone = true;
            return;
        }
        
        await createBackupBeforeOperation('reconnection_sync');
        
        connectionState = 'SYNCING_DATA';
        
        const response = await axios.get(HISTORY_URL, {
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
            },
            timeout: 10000
        });

        if (!validateApiData(response.data)) {
            console.log('🛡️  Données API invalides - Synchronisation de reconnexion annulée');
            blockCoefficientCapture = false;
            reconnectionSyncDone = true;
            return;
        }

        console.log(`📊 API retourne ${response.data.length} entrées pour sync immédiate`);
        
        const apiLastTwenty = response.data.slice(0, 20).map(item => ({
            value: item.finalValues[0],
            hash: item.hash,
            id: item.id
        }));
        
        const ourLastTwenty = crashHistory.slice(0, 20).map(item => ({
            value: typeof item === 'object' ? item.value : item,
            hash: typeof item === 'object' ? item.hash : null
        }));
        
        console.log('🎯 COMPARAISON IMMÉDIATE (AVEC HASHES):');
        console.log('   API:', apiLastTwenty.map(x => `${x.value}(${x.hash ? x.hash.substring(0, 8) : 'NO_HASH'})`));
        console.log('   Nous:', ourLastTwenty.map(x => `${x.value}(${x.hash ? x.hash.substring(0, 8) : 'NO_HASH'})`));
        
        const syncPoint = findBestSyncPointByHash(apiLastTwenty, ourLastTwenty);
        
        if (syncPoint.found) {
            console.log(`🎯 Point de synchronisation HASH: hash ${syncPoint.hash.substring(0, 12)}... (valeur: ${syncPoint.value}) à l'index API ${syncPoint.apiIndex}, index local ${syncPoint.ourIndex}`);
            
            if (syncPoint.apiIndex > 0) {
                const missingData = response.data.slice(0, syncPoint.apiIndex);
                console.log(`📥 Ajout de ${missingData.length} côtes manquantes`);
                
                missingData.reverse().forEach(item => {
                    const dataEntry = {
                        value: item.finalValues[0],
                        hash: item.hash,
                        id: item.id,
                        timestamp: Date.now()
                    };
                    crashHistory.unshift(dataEntry);
                    console.log(`➕ Ajout: ${item.finalValues[0]} (hash: ${item.hash ? item.hash.substring(0, 8) + '...' : 'N/A'})`);
                });
                
                crashHistory = crashHistory.slice(0, historySize);
                
                calculateAndRankRanges();
                updateMedianMeanHistories();
                
                io.emit('dataSynced', {
                    type: 'dataSynced',
                    message: `Synchronisation immédiate par hash: ${missingData.length} côtes récupérées`,
                    count: missingData.length
                });
                
                console.log(`✅ Synchronisation immédiate par hash terminée - ${missingData.length} côtes ajoutées`);
            }
        } else {
            console.log('⚠️  Aucun point de synchronisation trouvé par hash en mode immédiat');
        }
        
        reconnectionSyncDone = true;
        
        setTimeout(() => {
            blockCoefficientCapture = false;
            console.log('🔓 Capture des coefficients débloquée');
        }, 5000);
        
    } catch (error) {
        console.error('❌ Erreur lors de la synchronisation immédiate:', error.message);
        blockCoefficientCapture = false;
        reconnectionSyncDone = true;
    }
}

// VÉRIFICATION DE SYNCHRONISATION PÉRIODIQUE (AVEC ATTENTE COURTE)
async function checkSynchronizationWithAPI() {
    try {
        console.log('🔍 Vérification périodique de synchronisation par hash...');
        
        // Vérification rapide de connectivité (seulement 3 tentatives)
        const hasInternet = await waitForInternetConnectivity(3, 1000);
        if (!hasInternet) {
            console.log('🛡️  Pas de connectivité pour la vérification périodique');
            return false;
        }
        
        connectionState = 'CHECKING_SYNC';
        
        const response = await axios.get(HISTORY_URL, {
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
            },
            timeout: 10000
        });

        if (!validateApiData(response.data)) {
            console.log('🛡️  Données API invalides pour la vérification périodique');
            return false;
        }

        const apiLastTwenty = response.data.slice(0, 20).map(item => ({
            value: item.finalValues[0],
            hash: item.hash,
            id: item.id
        }));
        
        const ourLastTwenty = crashHistory.slice(0, 20).map(item => ({
            value: typeof item === 'object' ? item.value : item,
            hash: typeof item === 'object' ? item.hash : null
        }));
        
        // Vérifier la synchronisation par hash en priorité
        const isInSyncByHash = checkHashSync(apiLastTwenty, ourLastTwenty);
        
        if (isInSyncByHash) {
            console.log('✅ Vérification périodique: Serveur synchronisé par hash');
            return true;
        } else {
            console.log('⚠️  Vérification périodique: Désynchronisation détectée par hash');
            const syncResult = await performIntelligentSyncByHash(apiLastTwenty, ourLastTwenty, response.data);
            return !syncResult.isInSync;
        }
        
    } catch (error) {
        console.error('❌ Erreur lors de la vérification périodique:', error.message);
        return false;
    }
}

// SYNCHRONISATION INTELLIGENTE PAR HASH
async function performIntelligentSyncByHash(apiData, ourData, fullApiHistory) {
    try {
        console.log('🧠 Synchronisation intelligente par hash en cours...');
        
        await createBackupBeforeOperation('intelligent_sync_hash');
        
        connectionState = 'SYNCING_DATA';
        
        if (ourData.length === 0) {
            await loadFullHistoryFromAPI(fullApiHistory);
            return { isInSync: false, addedCount: fullApiHistory.length };
        }
        
        const syncPoint = findBestSyncPointByHash(apiData, ourData);
        
        if (syncPoint.found) {
            console.log(`🎯 Point de synchronisation HASH trouvé: hash ${syncPoint.hash.substring(0, 12)}... (valeur: ${syncPoint.value}) à l'index API ${syncPoint.apiIndex}, index local ${syncPoint.ourIndex}`);
            
            if (syncPoint.apiIndex > 0) {
                const missingData = fullApiHistory.slice(0, syncPoint.apiIndex);
                await addMissingData(missingData);
                return { isInSync: false, addedCount: missingData.length };
            } else {
                return { isInSync: true, addedCount: 0 };
            }
        } else {
            console.log('⚠️  Aucun point de synchronisation trouvé par hash - Conservation des données locales');
            return { isInSync: true, addedCount: 0 };
        }
        
    } catch (error) {
        console.error('❌ Erreur lors de la synchronisation intelligente par hash:', error);
        return { isInSync: false, addedCount: 0 };
    }
}

// NOUVELLE FONCTION: ALGORITHME DE SYNCHRONISATION PAR HASH
function findBestSyncPointByHash(apiData, ourData) {
    if (!apiData || !ourData || apiData.length === 0 || ourData.length === 0) {
        return { found: false };
    }
    
    console.log('🔑 Recherche de synchronisation par HASH...');
    
    // Priorité 1: Correspondance exacte par hash
    for (let ourIndex = 0; ourIndex < ourData.length; ourIndex++) {
        const ourHash = ourData[ourIndex].hash;
        
        if (!ourHash) {
            continue; // Passer si pas de hash local
        }
        
        for (let apiIndex = 0; apiIndex < apiData.length; apiIndex++) {
            const apiHash = apiData[apiIndex].hash;
            
            if (apiHash && apiHash === ourHash) {
                console.log(`✅ CORRESPONDANCE HASH EXACTE trouvée!`);
                console.log(`   Hash: ${ourHash.substring(0, 16)}...`);
                console.log(`   Valeur: ${ourData[ourIndex].value} = ${apiData[apiIndex].value}`);
                console.log(`   Position: API index ${apiIndex}, Local index ${ourIndex}`);
                
                return {
                    found: true,
                    value: ourData[ourIndex].value,
                    hash: ourHash,
                    ourIndex: ourIndex,
                    apiIndex: apiIndex,
                    method: 'hash_exact'
                };
            }
        }
    }
    

    
    console.log('⚠️  Aucune correspondance de hash trouvée - ÉCHEC DE SYNCHRONISATION');

}

// NOUVELLE FONCTION: Vérifier la synchronisation par hash
function checkHashSync(apiData, ourData) {
    if (!apiData || !ourData || apiData.length === 0 || ourData.length === 0) {
        return false;
    }
    
    // Vérifier les 5 premiers éléments
    const checkCount = Math.min(5, Math.min(apiData.length, ourData.length));
    
    for (let i = 0; i < checkCount; i++) {
        const apiHash = apiData[i].hash;
        const ourHash = ourData[i].hash;
        
        // Si les deux ont des hashes, les comparer
        if (apiHash && ourHash) {
            if (apiHash !== ourHash) {
                console.log(`❌ Désynchronisation détectée à l'index ${i}: hash API ${apiHash.substring(0, 8)} ≠ hash local ${ourHash.substring(0, 8)}`);
                return false;
            }
        } else {
            // Fallback sur la comparaison de valeurs si pas de hash
            const apiValue = parseFloat(apiData[i].value);
            const ourValue = parseFloat(ourData[i].value);
            
            if (Math.abs(apiValue - ourValue) > 0.01) {
                console.log(`❌ Désynchronisation détectée à l'index ${i}: valeur API ${apiValue} ≠ valeur locale ${ourValue}`);
                return false;
            }
        }
    }
    
    return true;
}

// CHARGER TOUT L'HISTORIQUE DEPUIS L'API
async function loadFullHistoryFromAPI(apiHistory) {
    console.log('📥 Chargement complet de l\'historique depuis l\'API...');
    
    if (!apiHistory || apiHistory.length === 0) {
        console.log('❌ Tentative de chargement d\'un historique API vide - ANNULÉE');
        return;
    }
    
    crashHistory = [];
    apiHistory.forEach(item => {
        const dataEntry = {
            value: item.finalValues[0],
            hash: item.hash,
            id: item.id,
            timestamp: Date.now()
        };
        crashHistory.push(dataEntry);
    });
    
    calculateAndRankRanges();
    updateMedianMeanHistories();
    
    console.log(`✅ Historique chargé: ${crashHistory.length} entrées`);
}

// AJOUTER LES DONNÉES MANQUANTES
async function addMissingData(missingDataArray) {
    console.log(`📥 Ajout de ${missingDataArray.length} côtes manquantes...`);
    
    missingDataArray.reverse().forEach(item => {
        const dataEntry = {
            value: item.finalValues[0],
            hash: item.hash,
            id: item.id,
            timestamp: Date.now()
        };
        
        crashHistory.unshift(dataEntry);
        console.log(`➕ Ajout côte: ${item.finalValues[0]} (hash: ${item.hash ? item.hash.substring(0, 8) + '...' : 'N/A'})`);
    });
    
    crashHistory = crashHistory.slice(0, historySize);
    
    calculateAndRankRanges();
    updateMedianMeanHistories();
    
    io.emit('dataSynced', {
        type: 'dataSynced',
        message: `${missingDataArray.length} côtes synchronisées par hash depuis l'API`,
        count: missingDataArray.length
    });
    
    console.log(`✅ ${missingDataArray.length} côtes ajoutées avec succès`);
}

// RECONNEXION INTELLIGENTE (AVEC ATTENTE)
function smartReconnectWebSocket() {
    console.log('🔄 Reconnexion WebSocket intelligente avec attente...');
    connectionState = 'RECONNECTING';
    isReconnecting = true;
    blockCoefficientCapture = true;
    reconnectionSyncDone = false;
    
    if (wsConnection) {
        wsConnection.removeAllListeners();
        if (wsConnection.readyState === WebSocket.OPEN) {
            wsConnection.close();
        }
        wsConnection = null;
    }
    
    if (connectionMonitorTimer) {
        clearTimeout(connectionMonitorTimer);
        connectionMonitorTimer = null;
    }
    
    setTimeout(async () => {
        if (currentToken && isPolling) {
            console.log('🔌 Démarrage de la nouvelle connexion WebSocket...');
            startWebSocketConnection();
        } else {
            console.log('⚠️  Token manquant, attente de récupération avant reconnexion...');
            const hasToken = await waitForValidToken(5, 2000);
            if (hasToken && isPolling) {
                startWebSocketConnection();
            }
        }
    }, 2000);
}

// COMPARAISON DE TABLEAUX
function arraysEqual(a, b) {
    if (a.length !== b.length) return false;
    for (let i = 0; i < a.length; i++) {
        if (a[i] !== b[i]) return false;
    }
    return true;
}

// CALCULER L'ÉQUILIBRE DES POURCENTAGES
function calculateRangePercentageBalance() {
    try {
        if (crashHistory.length === 0 || rangeRankings.length === 0) {
            return { balance: 0, status: "insuffisant" };
        }

        const rangeCurrentPercentages = rangeRankings.map(range => range.currentPercentage).filter(percentage => !isNaN(percentage) && percentage >= 0);
        
        if (rangeCurrentPercentages.length < 2) {
            return { balance: 0, status: "insuffisant" };
        }

        const globalAverage = rangeCurrentPercentages.reduce((sum, percentage) => sum + percentage, 0) / rangeCurrentPercentages.length;
        
        const variance = rangeCurrentPercentages.reduce((sum, percentage) => sum + Math.pow(percentage - globalAverage, 2), 0) / rangeCurrentPercentages.length;
        const standardDeviation = Math.sqrt(variance);
        
        const coefficientOfVariation = globalAverage > 0 ? (standardDeviation / globalAverage) : 0;
        
        const balancePercentage = Math.max(0, Math.min(100, 100 - (coefficientOfVariation * 100)));
        
        let status;
        if (balancePercentage >= 80) {
            status = "très équilibré";
        } else if (balancePercentage >= 60) {
            status = "équilibré";
        } else if (balancePercentage >= 40) {
            status = "modérément équilibré";
        } else if (balancePercentage >= 20) {
            status = "déséquilibré";
        } else {
            status = "très déséquilibré";
        }

        const result = {
            balance: balancePercentage,
            status: status,
            globalAverage: globalAverage,
            standardDeviation: standardDeviation,
            coefficientOfVariation: coefficientOfVariation,
            rangeCount: rangeCurrentPercentages.length,
            rangePercentages: rangeCurrentPercentages,
            details: rangeRankings.map(range => ({
                name: range.name,
                currentPercentage: range.currentPercentage,
                deviation: Math.abs(range.currentPercentage - globalAverage)
            }))
        };

        balanceEquilibriumHistory.unshift(balancePercentage);
        if (balanceEquilibriumHistory.length > 20) {
            balanceEquilibriumHistory = balanceEquilibriumHistory.slice(0, 20);
        }
        
        currentBalanceEquilibrium = balancePercentage;

        return result;
    } catch (error) {
        console.error('❌ Erreur calcul équilibre pourcentages:', error);
        return { balance: 0, status: "erreur" };
    }
}

// RÉCUPÉRER LES INFORMATIONS UTILISATEUR
async function fetchUserAuth() {
    try {
        console.log('🔐 Récupération des informations utilisateur...');
        console.log(`🔑 Utilisation du token: ${authToken.substring(0, 50)}...`);
        
        const response = await axios.post(USER_AUTH_URL, null, {
            headers: {
                "accept": "application/json, text/plain, */*",
                "accept-language": "en-US,en;q=0.9,fr-CI;q=0.8,fr;q=0.7",
                "auth-token": authToken,
                "content-type": "application/json",
                "sec-ch-ua": "\"Not-A.Brand\";v=\"99\", \"Chromium\";v=\"124\"",
                "sec-ch-ua-mobile": "?1",
                "sec-ch-ua-platform": "\"Android\"",
                "sec-fetch-dest": "empty",
                "sec-fetch-mode": "cors",
                "sec-fetch-site": "cross-site",
                "Referer": "https://1play.gamedev-tech.cc/",
                "Referrer-Policy": "strict-origin-when-cross-origin"
            },
            timeout: 15000
        });

        console.log('🔍 Réponse de l\'API d\'authentification:', response.status, response.statusText);
        console.log('📄 Données reçues:', JSON.stringify(response.data, null, 2));

        if (response.data) {
            if (response.data.userId) {
                userInfo.userId = response.data.userId;
                console.log(`✅ User ID récupéré: ${userInfo.userId}`);
            }
            
            if (response.data.userName) {
                userInfo.userName = response.data.userName;
                console.log(`✅ User Name récupéré: ${userInfo.userName}`);
            }
            
            if (response.data.sessionId) {
                userInfo.sessionId = response.data.sessionId;
                console.log(`✅ Session ID récupéré: ${userInfo.sessionId}`);
            }
            
            if (response.data.customerId) {
                userInfo.customerId = response.data.customerId;
                console.log(`✅ Customer ID récupéré: ${userInfo.customerId}`);
            }
            
            if (response.data.balance !== undefined) {
                userInfo.balance = response.data.balance;
                console.log(`✅ Solde récupéré: ${userInfo.balance}`);
            }
            
            console.log('✅ Informations utilisateur mises à jour:');
            console.log(`   - Nom: ${userInfo.userName}`);
            console.log(`   - ID: ${userInfo.userId}`);
            console.log(`   - Session: ${userInfo.sessionId}`);
            console.log(`   - Customer: ${userInfo.customerId}`);
            console.log(`   - Solde: ${userInfo.balance}`);
            
            return true;
        } else {
            console.log('⚠️  Réponse vide de l\'API d\'authentification, conservation des valeurs par défaut');
            return false;
        }
    } catch (error) {
        console.error('❌ Erreur lors de la récupération des informations utilisateur:', error.message);
        if (error.response) {
            console.error('📋 Status:', error.response.status);
            console.error('📋 Data:', error.response.data);
            console.error('📋 Headers:', error.response.headers);
        }
        console.log('💡 Conservation des informations utilisateur par défaut');
        return false;
    }
}

// FONCTION POUR SAUVEGARDER LA CONFIGURATION
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
        config.rankingMethod = rankingMethod;
        config.balanceEquilibriumHistory = balanceEquilibriumHistory;
        config.autoStartPolling = autoStartPolling;
        
        await fs.writeFile(CONFIG_FILE, JSON.stringify(config, null, 2), 'utf8');
        console.log(`💾 Configuration sauvegardée (isPolling: ${isPolling}, autoStartPolling: ${autoStartPolling})`);
    } catch (error) {
        console.error('❌ Erreur lors de la sauvegarde:', error);
    }
}

// FONCTION POUR CHARGER LA CONFIGURATION
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
            rankingMethod = loadedConfig.rankingMethod || "current";
            balanceEquilibriumHistory = loadedConfig.balanceEquilibriumHistory || [];
            autoStartPolling = loadedConfig.autoStartPolling || loadedConfig.isPolling || false;
            
            config = loadedConfig;
            console.log(`📋 Configuration chargée:`);
            console.log(`   - isPolling: ${isPolling}`);
            console.log(`   - autoStartPolling: ${autoStartPolling}`);
            console.log(`   - pollingFrequency: ${pollingFrequency}`);
            console.log(`   - historySize: ${historySize}`);
            console.log(`   - rankingMethod: ${rankingMethod}`);
            
            if (autoStartPolling) {
                console.log('🚀 Démarrage automatique du polling configuré');
                isPolling = true;
            }
        } else {
            console.log('📝 Aucun fichier de configuration trouvé, utilisation des valeurs par défaut');
        }
    } catch (error) {
        console.error('❌ Erreur lors du chargement de la configuration:', error);
    }
}

// RÉCUPÉRER UN NOUVEAU TOKEN
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
            },
            timeout: 10000
        });

        if (response.data && response.data.centrifugo && response.data.centrifugo.mainToken) {
            currentToken = response.data.centrifugo.mainToken;
            
            try {
                const payload = JSON.parse(atob(currentToken.split('.')[1]));
                tokenExpireTime = payload.exp * 1000;
                
                console.log('✅ Nouveau mainToken récupéré avec succès');
                console.log(`📅 Token expire le: ${new Date(tokenExpireTime).toLocaleString()}`);
                
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

// TRAITER LES MESSAGES WEBSOCKET
function onWebSocketMessage(data) {
    try {
        if (!data || data.toString().trim() === '' || data.toString().trim() === '{}') {
            if (wsConnection && wsConnection.readyState === WebSocket.OPEN) {
                wsConnection.send('{}');
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
            
            onCoefficientUpdate();
            
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
                
                if (blockCoefficientCapture) {
                    console.log(`🚫 Coefficient ${fValue} ignoré (synchronisation en cours)`);
                    return;
                }
                
                const hashInfo = extractHashFromMessage(parsedData);
                console.log(`🎯 finalCoefficientValues trouvé: ${fValue} ✅ CAPTURÉE${hashInfo ? ` (hash: ${hashInfo.substring(0, 8)}...)` : ''}`);
                bufferDataForSending(fValue, hashInfo, "finalCoefficientValues");
            }
        }
        
    } catch (error) {
        console.error('❌ Erreur lors du traitement du message:', error);
    }
}

// EXTRAIRE LE HASH DES MESSAGES
function extractHashFromMessage(obj) {
    if (typeof obj === 'object' && obj !== null) {
        if (Array.isArray(obj)) {
            for (const item of obj) {
                const result = extractHashFromMessage(item);
                if (result !== null) return result;
            }
        } else {
            if (obj.provablyFair && obj.provablyFair.hash) {
                return obj.provablyFair.hash;
            }
            
            if (obj.hash) {
                return obj.hash;
            }
            
            for (const key of ['push', 'pub', 'data', 'payload', 'result', 'content']) {
                if (key in obj) {
                    const result = extractHashFromMessage(obj[key]);
                    if (result !== null) return result;
                }
            }
            
            for (const value of Object.values(obj)) {
                const result = extractHashFromMessage(value);
                if (result !== null) return result;
            }
        }
    }
    return null;
}

// RECHERCHER LES CHANGEMENTS DE COEFFICIENT
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

// RECHERCHER FINALCOEFFICIENTVALUES
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
}

// CALCULER ET CLASSER LES PLAGES
function calculateAndRankRanges() {
    try {
        if (crashHistory.length === 0) return;

        previousRankings = [...rangeRankings];
        
        const newRankings = [];
        
        currentRanges.forEach(range => {
            initializeRangePercentageHistory(range.name, range.limit);

            const limit = range.limit || 1000;
            const rangeHistory = crashHistory.slice(0, Math.min(limit, crashHistory.length));
            const totalCount = rangeHistory.length;

            let count = 0;
            for (const entry of rangeHistory) {
                const value = typeof entry === 'object' ? entry.value : entry;
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

            newRankings.push({
                name: range.name,
                color: range.color,
                min: range.min,
                max: range.max,
                limit: limit,
                currentPercentage: percentage,
                averagePercentage: averagePercentage,
                difference: difference,
                count: count,
                totalCount: totalCount,
                percentageHistory: percentageHistory.slice(0, 50),
                historySize: percentageHistory.length
            });
        });
        
        if (rankingMethod === "average") {
            newRankings.sort((a, b) => {
                return b.averagePercentage - a.averagePercentage;
            });
        } else {
            newRankings.sort((a, b) => {
                if (Math.abs(a.currentPercentage - b.currentPercentage) < 0.01) {
                    return b.averagePercentage - a.averagePercentage;
                }
                return b.currentPercentage - a.currentPercentage;
            });
        }
        
        newRankings.forEach((range, index) => {
            range.position = index + 1;
            range.previousPosition = getPreviousPosition(range.name);
        });
        
        rangeRankings = newRankings;
        
        calculateRangePercentageBalance();
        
    } catch (error) {
        console.error('❌ Erreur calcul classement:', error);
    }
}

function getPreviousPosition(rangeName) {
    const previousRange = previousRankings.find(r => r.name === rangeName);
    return previousRange ? previousRange.position : null;
}

// MISE À JOUR DES HISTORIQUES DE MÉDIANE ET MOYENNE
function updateMedianMeanHistories() {
    try {
        if (crashHistory.length === 0) return;

        const values = crashHistory.map(entry => typeof entry === 'object' ? entry.value : entry);

        const currentMedian = calculateMedian(values.slice(0, customSizes.median));
        medianHistory.unshift(currentMedian);
        
        if (medianHistory.length > customSizes.median) {
            medianHistory = medianHistory.slice(0, customSizes.median);
        }

        const currentMean = calculateMean(values.slice(0, customSizes.mean));
        meanHistory.unshift(currentMean);
        
        if (meanHistory.length > customSizes.mean) {
            meanHistory = meanHistory.slice(0, customSizes.mean);
        }
        
    } catch (error) {
        console.error('❌ Erreur mise à jour historiques médiane/moyenne:', error);
    }
}

// BUFFER DATA FOR SENDING
function bufferDataForSending(fValue, hash = null, target = null) {
    try {
        pendingValues.push({
            value: fValue,
            hash: hash,
            target: target,
            timestamp: Date.now()
        });
        
        const dataEntry = {
            value: fValue,
            hash: hash,
            timestamp: Date.now()
        };
        
        crashHistory.unshift(dataEntry);
        crashHistory = crashHistory.slice(0, historySize);
        
        calculateAndRankRanges();
        updateMedianMeanHistories();
        
        console.log(`📊 Valeur f=${fValue} ajoutée au buffer (Total: ${pendingValues.length})${hash ? ` [Hash: ${hash.substring(0, 8)}...]` : ''}`);
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
            
            const rangeRankingData = rangeRankings.map(range => ({
                name: range.name,
                color: range.color,
                position: range.position,
                previousPosition: range.previousPosition,
                currentPercentage: range.currentPercentage,
                averagePercentage: range.averagePercentage,
                difference: range.difference,
                count: range.count,
                totalCount: range.totalCount,
                percentageHistory: range.percentageHistory,
                historySize: range.historySize,
                limit: range.limit,
                min: range.min,
                max: range.max
            }));

            const balanceEquilibrium = calculateRangePercentageBalance();

            const payload = {
                type: 'update',
                data: {
                    newValues: newValues,
                    history: crashHistory.map(entry => typeof entry === 'object' ? entry.value : entry),
                    timestamp: Date.now(),
                    count: newValues.length,
                    rangeRankings: rangeRankingData,
                    medianHistory: medianHistory.slice(0, 20),
                    meanHistory: meanHistory.slice(0, 20),
                    medianOfMedians: calculateMean(medianHistory),
                    meanOfMeans: calculateMean(meanHistory),
                    currentMedian: medianHistory[0] || 0,
                    currentMean: meanHistory[0] || 0,
                    autoRefreshChart: true,
                    playNotificationSound: true,
                    rankingMethod: rankingMethod,
                    balanceEquilibrium: balanceEquilibrium,
                    balanceEquilibriumHistory: balanceEquilibriumHistory.slice(0, 50),
                    connectionState: connectionState
                }
            };
            
            io.emit('update', payload);
            console.log(`📤 Envoyé ${newValues.length} valeurs vers les clients [État: ${connectionState}]`);
        }
    }, 100);
    
    console.log('🚀 Thread d\'envoi de données démarré');
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

// WEBSOCKET CONNECTION
function startWebSocketConnection() {
    try {
        console.log('🔌 Tentative de connexion WebSocket...');
        
        if (!currentToken) {
            console.log('❌ Aucun token disponible, impossible de se connecter');
            return;
        }
        
        wsConnection = new WebSocket(WEBSOCKET_BASE_URL);
        
        wsConnection.on('open', async () => {
            console.log('✅ Connexion WebSocket établie');
            connectionState = 'CONNECTED';
            
            const authMessage = {
                "connect": {
                    "token": currentToken,
                    "name": "js"
                },
                "id": 1
            };
            
            wsConnection.send(JSON.stringify(authMessage));
            console.log('📤 Message d\'authentification envoyé');
            
            if (isReconnecting) {
                console.log('🚀 DÉBUT DE SYNCHRONISATION IMMÉDIATE...');
                await performImmediateReconnectionSync();
                isReconnecting = false;
                console.log('✅ SYNCHRONISATION IMMÉDIATE TERMINÉE');
            }
            
            resetConnectionMonitor();
            
            io.emit('connectionStatus', {
                type: 'connectionStatus',
                state: connectionState,
                message: 'Connexion WebSocket établie et synchronisée'
            });
        });
        
        wsConnection.on('message', onWebSocketMessage);
        
        wsConnection.on('error', (error) => {
            console.error('❌ Erreur WebSocket:', error);
            connectionState = 'ERROR';
        });
        
        wsConnection.on('close', (code, reason) => {
            console.log(`🔌 Connexion WebSocket fermée: ${code} - ${reason}`);
            connectionState = 'DISCONNECTED';
            
            if (connectionMonitorTimer) {
                clearTimeout(connectionMonitorTimer);
                connectionMonitorTimer = null;
            }
            
            if (isPolling) {
                console.log('🔄 Reconnexion automatique dans 5 secondes...');
                setTimeout(() => {
                    if (isPolling) {
                        smartReconnectWebSocket();
                    }
                }, 5000);
            }
        });
        
    } catch (error) {
        console.error('❌ Erreur de connexion WebSocket:', error);
        connectionState = 'ERROR';
        
        if (isPolling) {
            console.log('🔄 Nouvelle tentative dans 10 secondes...');
            setTimeout(() => {
                if (isPolling) {
                    startWebSocketConnection();
                }
            }, 10000);
        }
    }
}

// VÉRIFICATION PÉRIODIQUE
function startPeriodicSyncCheck() {
    if (syncCheckInterval) {
        clearInterval(syncCheckInterval);
    }
    
    syncCheckInterval = setInterval(async () => {
        if (connectionState === 'CONNECTED' && crashHistory.length > 0) {
            console.log('🔍 Vérification périodique de synchronisation par hash...');
            await checkSynchronizationWithAPI();
        }
    }, 60000);
    
    console.log('⏰ Vérification périodique de synchronisation par hash activée (60s)');
}

function stopPeriodicSyncCheck() {
    if (syncCheckInterval) {
        clearInterval(syncCheckInterval);
        syncCheckInterval = null;
    }
    console.log('⏰ Vérification périodique de synchronisation désactivée');
}

// RÉCUPÉRER LE SOLDE
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
            },
            timeout: 10000
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

// PLACER UN PARI
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
            },
            timeout: 10000
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
            meanHistory: [],
            balanceEquilibrium: { balance: 0, status: "insuffisant" },
            balanceEquilibriumHistory: []
        };
    }
    
    const values = history.map(entry => typeof entry === 'object' ? entry.value : entry);
    
    const medianSize = customSizes.median;
    const meanSize = customSizes.mean;
    const medianHistory = medianSize && medianSize < values.length ? values.slice(0, medianSize) : values;
    const meanHistory = meanSize && meanSize < values.length ? values.slice(0, meanSize) : values;
    
    const results = {
        total: values.length,
        ranges: {},
        median: calculateMedian(medianHistory),
        mean: calculateMean(meanHistory),
        medianOfMedians: calculateMean(medianHistory),
        meanOfMeans: calculateMean(meanHistory),
        medianHistory: medianHistory.slice(0, 20),
        meanHistory: meanHistory.slice(0, 20),
        balanceEquilibrium: calculateRangePercentageBalance(),
        balanceEquilibriumHistory: balanceEquilibriumHistory.slice(0, 50)
    };
    
    for (const rangeDef of ranges) {
        const name = rangeDef.name;
        const minVal = rangeDef.min;
        const maxVal = rangeDef.max;
        const color = rangeDef.color;
        const limit = rangeDef.limit;
        
        const rangeHistory = limit && limit < values.length ? values.slice(0, limit) : values;
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

// FONCTION MODIFIÉE POUR LE DÉMARRAGE DU POLLING AVEC SYNCHRONISATION INTELLIGENTE
function startPolling() {
    if (isPolling) return;
    
    console.log('🚀 DÉMARRAGE DU POLLING AVEC SYNCHRONISATION PAR HASH...');
    
    isPolling = true;
    autoStartPolling = true;
    connectionState = 'CONNECTING';
    
    if (wsConnection) {
        wsConnection.close();
    }
    
    startDataSender();
    startPeriodicSyncCheck();
    
    // LANCER LA SYNCHRONISATION INTELLIGENTE PAR HASH
    performPollingStartIntelligentSync().then(syncResult => {
        console.log('✅ Synchronisation intelligente par hash du polling terminée:', syncResult);
        
        // Après la synchronisation, démarrer la connexion WebSocket
        if (currentToken) {
            startWebSocketConnection();
        } else {
            console.log('⚠️  Aucun token disponible, attente de récupération...');
            waitForValidToken().then(hasToken => {
                if (hasToken) {
                    startWebSocketConnection();
                }
            });
        }
    }).catch(error => {
        console.error('❌ Erreur lors de la synchronisation intelligente du polling:', error);
        
        // Même en cas d'erreur de synchronisation, continuer avec la connexion WebSocket
        if (currentToken) {
            startWebSocketConnection();
        } else {
            console.log('⚠️  Aucun token disponible, attente de récupération...');
            waitForValidToken().then(hasToken => {
                if (hasToken) {
                    startWebSocketConnection();
                }
            });
        }
    });
    
    console.log('🚀 Polling WebSocket démarré avec persistance et démarrage automatique activé');
    saveConfig();
}

// FONCTION MODIFIÉE POUR L'ARRÊT DU POLLING
function stopPolling() {
    if (!isPolling) return;
    
    isPolling = false;
    autoStartPolling = false;
    connectionState = 'DISCONNECTED';
    
    stopDataSender();
    stopPeriodicSyncCheck();
    
    if (wsConnection) {
        wsConnection.close();
        wsConnection = null;
    }
    
    if (connectionMonitorTimer) {
        clearTimeout(connectionMonitorTimer);
        connectionMonitorTimer = null;
    }
    
    if (pingInterval) {
        clearInterval(pingInterval);
        pingInterval = null;
    }
    
    console.log('⏹️ Polling WebSocket arrêté et démarrage automatique désactivé');
    saveConfig();
}

// FONCTION DE NETTOYAGE ET SAUVEGARDE
async function gracefulShutdown(signal) {
    console.log(`\n🛑 Signal ${signal} reçu - Arrêt propre du serveur...`);
    
    try {
        if (crashHistory.length > 0) {
            await saveCrashHistoryToFile();
            console.log(`💾 Sauvegarde finale: ${crashHistory.length} entrées`);
        } else {
            console.log('⚠️  Historique vide - Pas de sauvegarde effectuée');
        }
        
        await saveConfig();
        
        server.close(() => {
            console.log('✅ Serveur HTTP fermé');
        });
        
        console.log('✅ Arrêt propre terminé avec protection des données');
        process.exit(0);
        
    } catch (error) {
        console.error('❌ Erreur lors de l\'arrêt propre:', error);
        process.exit(1);
    }
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

app.get('/api/range-rankings', (req, res) => {
    try {
        res.json({
            success: true,
            data: rangeRankings,
            totalHistorySize: crashHistory.length,
            rankingMethod: rankingMethod,
            balanceEquilibrium: calculateRangePercentageBalance(),
            balanceEquilibriumHistory: balanceEquilibriumHistory.slice(0, 50),
            connectionState: connectionState
        });
    } catch (error) {
        res.status(500).json({ success: false, message: `Erreur: ${error.message}` });
    }
});

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
                customSizes: customSizes,
                balanceEquilibrium: calculateRangePercentageBalance(),
                balanceEquilibriumHistory: balanceEquilibriumHistory.slice(0, 50),
                connectionState: connectionState
            }
        });
    } catch (error) {
        res.status(500).json({ success: false, message: `Erreur: ${error.message}` });
    }
});

app.get('/api/balance-equilibrium', (req, res) => {
    try {
        const balanceData = calculateRangePercentageBalance();
        res.json({
            success: true,
            data: {
                current: balanceData,
                history: balanceEquilibriumHistory.slice(0, 100),
                historySize: balanceEquilibriumHistory.length,
                connectionState: connectionState
            }
        });
    } catch (error) {
        res.status(500).json({ success: false, message: `Erreur: ${error.message}` });
    }
});

app.post('/api/check-sync', async (req, res) => {
    try {
        console.log('🔍 Vérification manuelle de synchronisation par hash demandée');
        const isInSync = await checkSynchronizationWithAPI();
        res.json({
            success: true,
            isInSync: isInSync,
            historySize: crashHistory.length,
            connectionState: connectionState,
            message: isInSync ? 'Serveur synchronisé par hash' : 'Synchronisation par hash effectuée'
        });
    } catch (error) {
        res.status(500).json({ 
            success: false, 
            message: `Erreur lors de la vérification: ${error.message}` 
        });
    }
});

// Gestionnaires Socket.IO (reste identique)
io.on('connection', (socket) => {
    console.log('Client connecté');
    
    socket.emit('init', {
        type: 'init',
        data: {
            history: crashHistory.map(entry => typeof entry === 'object' ? entry.value : entry),
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
            rangeRankings: rangeRankings,
            rankingMethod: rankingMethod,
            balanceEquilibrium: calculateRangePercentageBalance(),
            balanceEquilibriumHistory: balanceEquilibriumHistory.slice(0, 50),
            connectionState: connectionState
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
                        history: crashHistory.map(entry => typeof entry === 'object' ? entry.value : entry),
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
                    
                case 'setRankingMethod':
                    if (data.method === 'current' || data.method === 'average') {
                        const oldMethod = rankingMethod;
                        rankingMethod = data.method;
                        
                        calculateAndRankRanges();
                        
                        const methodName = rankingMethod === 'average' ? 'moyenne' : 'pourcentage actuel';
                        socket.emit('rankingMethodUpdated', {
                            type: 'rankingMethodUpdated',
                            success: true,
                            method: rankingMethod,
                            message: `Méthode de classement changée vers: ${methodName}`
                        });
                        
                        const rangeRankingData = rangeRankings.map(range => ({
                            name: range.name,
                            color: range.color,
                            position: range.position,
                            previousPosition: range.previousPosition,
                            currentPercentage: range.currentPercentage,
                            averagePercentage: range.averagePercentage,
                            difference: range.difference,
                            count: range.count,
                            totalCount: range.totalCount,
                            percentageHistory: range.percentageHistory,
                            historySize: range.historySize,
                            limit: range.limit,
                            min: range.min,
                            max: range.max
                        }));
                        
                        io.emit('rankingMethodChanged', {
                            type: 'rankingMethodChanged',
                            rankingMethod: rankingMethod,
                            rangeRankings: rangeRankingData,
                            balanceEquilibrium: calculateRangePercentageBalance()
                        });
                        
                        await saveConfig();
                        console.log(`🔄 Méthode de classement changée de "${oldMethod}" vers "${rankingMethod}"`);
                    } else {
                        socket.emit('rankingMethodUpdated', {
                            type: 'rankingMethodUpdated',
                            success: false,
                            message: 'Méthode de classement invalide'
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
                    analysis.balanceEquilibrium = calculateRangePercentageBalance();
                    analysis.balanceEquilibriumHistory = balanceEquilibriumHistory.slice(0, 50);
                    
                    socket.emit('analysis', { type: 'analysis', data: analysis });
                    break;
                    
                case 'saveRanges':
                    if (data.ranges && Array.isArray(data.ranges)) {
                        currentRanges = data.ranges;
                        
                        currentRanges.forEach(range => {
                            initializeRangePercentageHistory(range.name, range.limit);
                        });
                        
                        calculateAndRankRanges();
                        
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
                    socket.emit('message', { type: 'info', message: 'WebSocket actif - les données sont envoyées automatiquement' });
                    break;
                    
                case 'getRangeRankings':
                    socket.emit('rangeRankingsData', { 
                        type: 'rangeRankingsData', 
                        data: rangeRankings,
                        totalHistorySize: crashHistory.length,
                        rankingMethod: rankingMethod,
                        balanceEquilibrium: calculateRangePercentageBalance(),
                        balanceEquilibriumHistory: balanceEquilibriumHistory.slice(0, 50),
                        connectionState: connectionState
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
                            customSizes: customSizes,
                            balanceEquilibrium: calculateRangePercentageBalance(),
                            balanceEquilibriumHistory: balanceEquilibriumHistory.slice(0, 50),
                            connectionState: connectionState
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

                case 'getBalanceEquilibrium':
                    const balanceData = calculateRangePercentageBalance();
                    socket.emit('balanceEquilibriumData', {
                        type: 'balanceEquilibriumData',
                        data: {
                            current: balanceData,
                            history: balanceEquilibriumHistory.slice(0, data.limit || 50),
                            historySize: balanceEquilibriumHistory.length,
                            connectionState: connectionState
                        }
                    });
                    break;

                case 'clearBalanceEquilibriumHistory':
                    balanceEquilibriumHistory = [];
                    currentBalanceEquilibrium = 0;
                    socket.emit('balanceEquilibriumHistoryCleared', {
                        type: 'balanceEquilibriumHistoryCleared',
                        success: true,
                        message: 'Historique d\'équilibre des pourcentages réinitialisé'
                    });
                    await saveConfig();
                    break;
                    
                case 'checkSync':
                    socket.emit('message', { 
                        type: 'info', 
                        message: 'Vérification de synchronisation par hash en cours...' 
                    });
                    const syncResult = await checkSynchronizationWithAPI();
                    socket.emit('syncResult', {
                        type: 'syncResult',
                        isInSync: syncResult,
                        message: syncResult ? 'Synchronisé par hash avec l\'API' : 'Données synchronisées par hash'
                    });
                    break;
                    
                case 'forceReconnect':
                    socket.emit('message', { 
                        type: 'info', 
                        message: 'Reconnexion forcée en cours...' 
                    });
                    smartReconnectWebSocket();
                    break;
                    
                case 'getConnectionStatus':
                    socket.emit('connectionStatus', {
                        type: 'connectionStatus',
                        state: connectionState,
                        lastUpdate: lastCoefficientUpdate,
                        historySize: crashHistory.length
                    });
                    break;

                case 'saveHistoryFile':
                    socket.emit('message', { 
                        type: 'info', 
                        message: 'Sauvegarde manuelle de l\'historique en cours...' 
                    });
                    await saveCrashHistoryToFile();
                    socket.emit('historyFileSaved', {
                        type: 'historyFileSaved',
                        success: true,
                        message: `Historique sauvegardé: ${crashHistory.length} entrées`
                    });
                    break;

                case 'restoreFromBackup':
                    socket.emit('message', { 
                        type: 'info', 
                        message: 'Restauration depuis la sauvegarde en cours...' 
                    });
                    const restored = await restoreFromBackup();
                    if (restored) {
                        calculateAndRankRanges();
                        updateMedianMeanHistories();
                        socket.emit('historyRestored', {
                            type: 'historyRestored',
                            success: true,
                            message: `Historique restauré: ${crashHistory.length} entrées`
                        });
                    } else {
                        socket.emit('historyRestored', {
                            type: 'historyRestored',
                            success: false,
                            message: 'Aucune sauvegarde trouvée ou erreur de restauration'
                        });
                    }
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

// FONCTION MODIFIÉE POUR LE DÉMARRAGE DU SERVEUR AVEC ATTENTE ET SYNCHRONISATION PAR HASH
async function startServer() {
    try {
        // 1. Charger la configuration en premier
        await loadConfig();
        
        // 2. Charger l'historique depuis le fichier
        console.log('📂 Chargement de l\'historique depuis le fichier...');
        const historyLoaded = await loadCrashHistoryFromFile();
        
        // 3. Récupérer les informations utilisateur avec gestion d'erreur améliorée
        console.log('🔐 Récupération des informations utilisateur...');
        const authSuccess = await fetchUserAuth();
        if (authSuccess) {
            console.log('✅ Informations utilisateur récupérées avec succès');
        } else {
            console.log('⚠️  Échec de récupération des informations utilisateur - Utilisation des valeurs par défaut');
        }
        
        // 4. Récupérer le token avec attente si nécessaire
        console.log('🔑 Récupération du token...');
        let tokenSuccess = await refreshToken();
        if (!tokenSuccess) {
            console.log('⚠️  Échec initial de récupération du token - Attente de connectivité...');
            const hasInternet = await waitForInternetConnectivity(10, 2000);
            if (hasInternet) {
                tokenSuccess = await waitForValidToken(5, 3000);
            }
        }
        
        if (tokenSuccess) {
            console.log('✅ Token récupéré avec succès');
            
            // 5. DÉCLENCHER AUTOMATIQUEMENT LA SYNCHRONISATION INTELLIGENTE PAR HASH APRÈS RÉCUPÉRATION DU TOKEN
            console.log('🚀 DÉMARRAGE AUTOMATIQUE DE LA SYNCHRONISATION PAR HASH APRÈS RÉCUPÉRATION DU TOKEN...');
            const syncResult = await performStartupIntelligentSync();
            console.log(`✅ Synchronisation intelligente par hash automatique terminée:`, syncResult);
            
            // Recalculer les statistiques après synchronisation
            calculateAndRankRanges();
            updateMedianMeanHistories();
        } else {
            console.log('⚠️  Impossible de récupérer le token après tentatives');
            if (historyLoaded) {
                console.log(`📊 Historique local disponible: ${crashHistory.length} entrées`);
                calculateAndRankRanges();
                updateMedianMeanHistories();
            }
        }
        
        // 6. DÉMARRAGE AUTOMATIQUE DU POLLING si configuré (AVEC ATTENTE)
        if (autoStartPolling) {
            console.log('🚀 DÉMARRAGE AUTOMATIQUE DU POLLING CONFIGURÉ...');
            
            if (!tokenSuccess) {
                console.log('🔑 Token manquant pour démarrage auto - Attente de connectivité...');
                const hasInternet = await waitForInternetConnectivity(15, 2000);
                if (hasInternet) {
                    const hasToken = await waitForValidToken(10, 3000);
                    if (hasToken) {
                        console.log('✅ Token récupéré - Démarrage automatique du polling');
                        isPolling = true;
                        startWebSocketConnection();
                        startDataSender();
                        startPeriodicSyncCheck();
                    } else {
                        console.log('❌ Impossible de récupérer le token - Démarrage automatique annulé');
                        autoStartPolling = false;
                        isPolling = false;
                    }
                } else {
                    console.log('❌ Pas de connectivité - Démarrage automatique annulé');
                    autoStartPolling = false;
                    isPolling = false;
                }
            } else {
                console.log('✅ Token disponible - Démarrage automatique du polling');
                isPolling = true;
                startWebSocketConnection();
                startDataSender();
                startPeriodicSyncCheck();
            }
        } else {
            console.log('💤 Démarrage automatique désactivé - Serveur en attente');
        }
        
        // 7. Démarrer le serveur HTTP
        server.listen(port, '0.0.0.0', () => {
            console.log(`🚀 Serveur démarré sur le port ${port}`);
            console.log(`📊 ÉTAT DU SERVEUR AVEC SYNCHRONISATION PAR HASH:`);
            console.log(`   - 🛡️  Protection des données: ACTIVÉE`);
            console.log(`   - 🔑 Synchronisation par HASH cryptographique: ACTIVÉE`);
            console.log(`   - 🔄 Démarrage automatique du polling: ${autoStartPolling ? 'ACTIVÉ' : 'DÉSACTIVÉ'}`);
            console.log(`   - 📡 Polling actuel: ${isPolling ? 'ACTIF' : 'INACTIF'}`);
            console.log(`   - 🌐 État de connexion: ${connectionState}`);
            console.log(`   - 📊 Historique actuel: ${crashHistory.length} entrées`);
            console.log(`   - 👤 Utilisateur: ${userInfo.userName} (ID: ${userInfo.userId || 'N/A'})`);
            console.log(`   - 💰 Solde: ${userInfo.balance} FCFA`);
            console.log(`   - 📋 Méthode de classement: ${rankingMethod === 'average' ? 'MOYENNE' : 'POURCENTAGE ACTUEL'}`);
            console.log(`   - 🌐 Attente intelligente de connectivité: ACTIVÉE`);
            console.log(`   - 🔑 Correspondance par hash cryptographique: ACTIVÉE`);
            console.log(`   - 💾 Fichiers de sauvegarde:`);
            console.log(`     • Principal: ${CRASH_HISTORY_FILE}`);
            console.log(`     • Sécurité: ${CRASH_HISTORY_BACKUP_FILE}`);
            console.log(`     • Configuration: ${CONFIG_FILE}`);
            
            console.log(`   - 🎯 Plages configurées:`);
            currentRanges.forEach(range => {
                console.log(`     • ${range.name}: Limite ${range.limit || 1000} entrées`);
            });
            
            console.log(`   - 📈 Tailles personnalisées: Médiane=${customSizes.median}, Moyenne=${customSizes.mean}`);
            
            if (autoStartPolling) {
                console.log(`\n🔥 POLLING AUTOMATIQUE ACTIVÉ - Le serveur attend la connectivité et se reconnecte automatiquement!`);
            } else {
                console.log(`\n💡 Pour activer le démarrage automatique, démarrez le polling depuis l'interface web.`);
            }
            
            console.log(`\n🚀 NOUVELLES FONCTIONNALITÉS - SYNCHRONISATION PAR HASH:`);
            console.log(`   • Correspondance exacte par hash cryptographique`);
            console.log(`   • Élimination des faux positifs avec valeurs identiques`);
            console.log(`   • Fallback intelligent vers comparaison par valeur`);
            console.log(`   • Fiabilité maximale de synchronisation`);
            console.log(`   • Logs détaillés pour debug des correspondances`);
        });
    } catch (error) {
        console.error('❌ Erreur lors du démarrage:', error);
        
        console.log('🔄 Tentative de restauration d\'urgence...');
        await restoreFromBackup();
        
        setTimeout(startServer, 5000);
    }
}

// Démarrer le serveur
startServer();

// GESTIONNAIRES DE SIGNAUX POUR SAUVEGARDE
process.on('SIGINT', gracefulShutdown);
process.on('SIGTERM', gracefulShutdown);
process.on('SIGUSR1', gracefulShutdown);
process.on('SIGUSR2', gracefulShutdown);

// Gestionnaire d'erreurs non capturées
process.on('uncaughtException', async (error) => {
    console.error('❌ Erreur non capturée:', error);
    if (crashHistory.length > 0) {
        await saveCrashHistoryToFile();
        console.log('💾 Sauvegarde d\'urgence effectuée');
    }
    process.exit(1);
});

process.on('unhandledRejection', async (reason, promise) => {
    console.error('❌ Promesse rejetée non gérée:', reason);
    if (crashHistory.length > 0) {
        await saveCrashHistoryToFile();
        console.log('💾 Sauvegarde d\'urgence effectuée');
    }
    process.exit(1);
});
