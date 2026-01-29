#define SDL_MAIN_HANDLED
#include <SDL2/SDL.h>
#include <SDL2/SDL_image.h>
#include <SDL2/SDL_ttf.h>
#include <SDL2/SDL_mixer.h>
#include <vector>
#include <queue>
#include <cmath>
#include <algorithm>
#include <string>
#include <cstdlib>
#include <ctime>
#include <fstream>
#include <iostream>


// ================= CONFIG =================
const int TILE = 40;
const int ROWS = 17;
const int COLS = 17;
const int WIDTH = COLS * TILE;
const int HEIGHT = ROWS * TILE + 100;
const int ENTITY = 32;
const int TUNNEL_ROW = 7;

const float PAC_SPEED = 2.0f;
const float GHOST_SPEED = 1.2f;
const Uint32 FRIGHT_TIME = 6000;
const int NUM_GHOSTS = 2;  // Réduit à 2 fantômes

// ================= ENUM =================
enum GameState { MENU, PLAYING, PAUSED, WIN, GAME_OVER };
enum GhostState {
    NORMAL,
    FRIGHTENED,
    EATEN
};

// ================= STRUCT =================
struct Entity {
    float x, y;
    int row, col;
    float dx, dy;
};

struct Ghost {
    Entity e;
    GhostState state;
    SDL_Texture* tex;
    int targetR, targetC;

    bool visible;
    Uint32 respawnTime;
    Uint32 respawnSafeTime;
    Uint32 stuckTimer;
    int id;
};

// ================= SDL =================
SDL_Window* window;
SDL_Renderer* renderer;
TTF_Font* font;
TTF_Font* fontLarge;
TTF_Font* fontSmall;

SDL_Texture* texPac;
SDL_Texture* ghostTex[2];

// ================= AUDIO =================
Mix_Chunk* soundChomp = nullptr;
Mix_Chunk* soundEatGhost = nullptr;
Mix_Chunk* soundDeath = nullptr;
Mix_Chunk* soundPowerUp = nullptr;
Mix_Music* musicBg = nullptr;

// ================= GAME =================
GameState gameState = MENU;
std::vector<Ghost> ghosts;
Entity pacman;

Uint32 frightenedEnd = 0;
Uint32 lastBFS = 0;
Uint32 animTimer = 0;
Uint32 powerPelletBlink = 0;

int score = 0;
int highScore = 0;
int pelletsLeft = 0;
int totalPellets = 0;
int lives = 1;
int level = 1;
int comboMultiplier = 1;
Uint32 comboTimer = 0;

// ================= MAP =================
int maze[ROWS][COLS];
int baseMaze[ROWS][COLS] = {
 {1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1},
 {1,3,2,2,2,2,2,2,1,2,2,2,2,2,2,3,1},
 {1,2,1,1,2,1,1,2,1,2,1,1,2,1,1,2,1},
 {1,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,1},
 {1,2,1,2,1,2,1,1,1,1,1,2,1,2,1,2,1},
 {1,2,2,2,1,2,2,2,1,2,2,2,1,2,2,2,1},
 {1,1,1,2,1,1,1,0,0,0,1,1,1,2,1,1,1},
 {0,0,0,2,0,0,1,0,0,0,1,0,0,2,0,0,0},
 {1,1,1,2,1,1,1,1,1,1,1,1,1,2,1,1,1},
 {1,2,2,2,2,2,2,2,1,2,2,2,2,2,2,2,1},
 {1,2,1,1,2,1,1,2,1,2,1,1,2,1,1,2,1},
 {1,2,2,1,2,2,2,2,0,2,2,2,2,1,2,2,1},
 {1,1,2,1,2,1,2,1,1,1,2,1,2,1,2,1,1},
 {1,2,2,2,2,1,2,2,1,2,2,1,2,2,2,2,1},
 {1,2,1,1,1,1,1,2,1,2,1,1,1,1,1,2,1},
 {1,3,2,2,2,2,2,2,2,2,2,2,2,2,2,3,1},
 {1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1}
};

int ghostStartPos[2][2] = {
    {8, 8},  // Fantôme 1 : Chasseur direct
    {7, 7}   // Fantôme 2 : Prédicteur
};

// ================= UTILS =================
bool canMove(int r, int c) {
    return r >= 0 && c >= 0 && r < ROWS && c < COLS && maze[r][c] != 1;
}

const std::string HIGHSCORE_FILE = "highscore.txt";

// Charger le high score depuis le fichier
int loadHighScore() {
    std::ifstream file(HIGHSCORE_FILE);
    int hs = 0;

    if (file.is_open()) {
        file >> hs;
        file.close();
    }

    return hs;
}

// Sauvegarder le high score dans le fichier
void saveHighScore(int hs) {
    std::ofstream file(HIGHSCORE_FILE, std::ios::trunc);

    if (file.is_open()) {
        file << hs;
        file.close();
    }
}


void snap(Entity& e) {
    e.col = int((e.x + ENTITY / 2) / TILE);
    e.row = int((e.y + ENTITY / 2) / TILE);
    e.x = e.col * TILE + 4;
    e.y = e.row * TILE + 4;
}

bool checkGhostCollision(const Ghost& g1, const Ghost& g2) {
    if(!g1.visible || !g2.visible) return false;
    if(g1.state == EATEN || g2.state == EATEN) return false;
    float dx = g1.e.x - g2.e.x;
    float dy = g1.e.y - g2.e.y;
    return (dx*dx + dy*dy) < 250;
}

// ================= BFS =================
std::pair<int,int> bfs(int sr,int sc,int tr,int tc) {
    if(sr == tr && sc == tc) return {sr, sc};

    bool vis[ROWS][COLS]={0};
    std::pair<int,int> par[ROWS][COLS];
    int dr[4]={-1,1,0,0}, dc[4]={0,0,-1,1};

    std::queue<std::pair<int,int>> q;
    q.push({sr,sc});
    vis[sr][sc]=true;

    while(!q.empty()){
        auto [r,c]=q.front(); q.pop();
        if(r==tr && c==tc) break;

        for(int i=0;i<4;i++){
            int nr=r+dr[i], nc=c+dc[i];

            if(nr==TUNNEL_ROW){
                if(nc<0) nc=COLS-1;
                if(nc>=COLS) nc=0;
            }

            if(!canMove(nr,nc) || vis[nr][nc]) continue;
            vis[nr][nc]=true;
            par[nr][nc]={r,c};
            q.push({nr,nc});
        }
    }

    if(!vis[tr][tc]) return {sr,sc};

    int r=tr,c=tc;
    while(par[r][c] != std::make_pair(sr,sc)){
        auto p=par[r][c];
        r=p.first; c=p.second;
    }
    return {r,c};
}

// ================= RESET =================
void resetGame() {
    pelletsLeft = 0;
    totalPellets = 0;
    for(int r=0;r<ROWS;r++)
        for(int c=0;c<COLS;c++){
            maze[r][c] = baseMaze[r][c];
            if(maze[r][c]==2 || maze[r][c]==3) {
                pelletsLeft++;
                totalPellets++;
            }
        }

    pacman = {1*TILE+4,14*TILE+4,14,1,0,0};

    ghosts.clear();
    for(int i=0;i<NUM_GHOSTS;i++){
        Ghost g;
        g.id = i;
        g.e.row=ghostStartPos[i][0];
        g.e.col=ghostStartPos[i][1];
        g.e.x=g.e.col*TILE+4;
        g.e.y=g.e.row*TILE+4;
        g.e.dx = 0;
        g.e.dy = 0;
        g.state=NORMAL;
        g.tex=ghostTex[i];
        g.visible = true;
        g.respawnTime = 0;
        g.respawnSafeTime = 0;
        g.stuckTimer = 0;
        g.targetR = g.e.row;
        g.targetC = g.e.col;
        ghosts.push_back(g);
    }

    score=0;
    lives=1;
    level=1;
    comboMultiplier = 1;
    gameState=PLAYING;
}

// ================= DRAW FUNCTIONS =================
void drawTextCentered(const std::string& t, int y, SDL_Color c, TTF_Font* f) {
    if(!f) return;
    SDL_Surface* s=TTF_RenderText_Blended(f,t.c_str(),c);
    if(!s) return;
    SDL_Texture* tx=SDL_CreateTextureFromSurface(renderer,s);
    SDL_Rect r={(WIDTH-s->w)/2,y,s->w,s->h};
    SDL_RenderCopy(renderer,tx,nullptr,&r);
    SDL_FreeSurface(s);
    SDL_DestroyTexture(tx);
}

void drawText(const std::string& t,int x,int y,SDL_Color c,TTF_Font* f) {
    if(!f) return;
    SDL_Surface* s=TTF_RenderText_Blended(f,t.c_str(),c);
    if(!s) return;
    SDL_Texture* tx=SDL_CreateTextureFromSurface(renderer,s);
    SDL_Rect r={x,y,s->w,s->h};
    SDL_RenderCopy(renderer,tx,nullptr,&r);
    SDL_FreeSurface(s);
    SDL_DestroyTexture(tx);
}

void drawRoundedRect(int x, int y, int w, int h, SDL_Color color, int alpha=255) {
    SDL_SetRenderDrawBlendMode(renderer, SDL_BLENDMODE_BLEND);
    SDL_SetRenderDrawColor(renderer, color.r, color.g, color.b, alpha);
    SDL_Rect r = {x, y, w, h};
    SDL_RenderFillRect(renderer, &r);
}

void drawGradient(int x, int y, int w, int h, SDL_Color top, SDL_Color bottom) {
    for(int i=0; i<h; i++) {
        float ratio = (float)i / h;
        int r = top.r + (bottom.r - top.r) * ratio;
        int g = top.g + (bottom.g - top.g) * ratio;
        int b = top.b + (bottom.b - top.b) * ratio;
        SDL_SetRenderDrawColor(renderer, r, g, b, 255);
        SDL_RenderDrawLine(renderer, x, y+i, x+w, y+i);
    }
}

std::pair<int,int> getFleeTarget(const Ghost& g) {
    std::pair<int,int> corners[4] = {
        {1,1}, {1,COLS-2}, {ROWS-2,1}, {ROWS-2,COLS-2}
    };

    int best = 0;
    float maxDist = -1;

    for(int i=0;i<4;i++){
        float dx = corners[i].first  - pacman.row;
        float dy = corners[i].second - pacman.col;
        float d = dx*dx + dy*dy;
        if(d > maxDist){
            maxDist = d;
            best = i;
        }
    }
    return corners[best];
}

// ================= MAIN =================
int main(){
    Mix_OpenAudio(44100, MIX_DEFAULT_FORMAT, 2, 2048);
    Mix_Chunk* test = Mix_LoadWAV("assets/chomp.wav");
    Mix_PlayChannel(-1, test, 0);
    SDL_Delay(1000);


    SDL_Init(SDL_INIT_VIDEO | SDL_INIT_AUDIO);
    if (Mix_OpenAudio(44100, MIX_DEFAULT_FORMAT, 2, 2048) < 0) {
        printf("Mix_OpenAudio ERROR: %s\n", Mix_GetError());
    } else {
        printf("Mix_OpenAudio OK\n");
    }
    IMG_Init(IMG_INIT_PNG);
    TTF_Init();
    highScore = loadHighScore();


    // ================= INITIALISATION AUDIO =================
    if(Mix_OpenAudio(44100, MIX_DEFAULT_FORMAT, 2, 2048) < 0) {
        printf("Erreur SDL_mixer: %s\n", Mix_GetError());
    }

    // Charger les sons (optionnel - le jeu fonctionnera sans)
    soundChomp = Mix_LoadWAV("assets/chomp.wav");
    soundEatGhost = Mix_LoadWAV("assets/eat_ghost.wav");
    soundDeath = Mix_LoadWAV("assets/death.wav");
    soundPowerUp = Mix_LoadWAV("assets/powerup.wav");
    musicBg = Mix_LoadMUS("assets/background.mp3");

    // Si la musique existe, la jouer
    if(musicBg) {
        Mix_PlayMusic(musicBg, -1); // -1 = boucle infinie
        Mix_VolumeMusic(32); // Volume à 25%
    }

    window = SDL_CreateWindow("PAC-MAN - SDL2",
        SDL_WINDOWPOS_CENTERED,SDL_WINDOWPOS_CENTERED,
        WIDTH,HEIGHT,0);
    renderer = SDL_CreateRenderer(window,-1,SDL_RENDERER_ACCELERATED);

    font = TTF_OpenFont("arial.ttf",20);
    fontLarge = TTF_OpenFont("arial.ttf",48);
    fontSmall = TTF_OpenFont("arial.ttf",16);

    texPac = IMG_LoadTexture(renderer,"assets/pacman.png");
    ghostTex[0]=IMG_LoadTexture(renderer,"assets/ghost.png");
    ghostTex[1]=IMG_LoadTexture(renderer,"assets/ghost_1.png");

    bool run=true;
    SDL_Event e;

    while(run){
        Uint32 currentTime = SDL_GetTicks();

        while(SDL_PollEvent(&e)){
            if(e.type==SDL_QUIT) run=false;

            if(e.type==SDL_KEYDOWN){
                if(e.key.keysym.sym==SDLK_SPACE &&
                   (gameState==MENU||gameState==GAME_OVER||gameState==WIN))
                    resetGame();

                if(e.key.keysym.sym==SDLK_ESCAPE) run=false;
                if(e.key.keysym.sym==SDLK_p && gameState==PLAYING) gameState=PAUSED;
                else if(e.key.keysym.sym==SDLK_p && gameState==PAUSED) gameState=PLAYING;

                if(gameState==PLAYING){
                    if(e.key.keysym.sym==SDLK_UP || e.key.keysym.sym==SDLK_z)
                        pacman.dy=-PAC_SPEED, pacman.dx=0;
                    if(e.key.keysym.sym==SDLK_DOWN || e.key.keysym.sym==SDLK_s)
                        pacman.dy= PAC_SPEED, pacman.dx=0;
                    if(e.key.keysym.sym==SDLK_LEFT || e.key.keysym.sym==SDLK_q)
                        pacman.dx=-PAC_SPEED, pacman.dy=0;
                    if(e.key.keysym.sym==SDLK_RIGHT || e.key.keysym.sym==SDLK_d)
                        pacman.dx= PAC_SPEED, pacman.dy=0;
                }
            }
        }

        if(gameState==PLAYING){
            bool frightEnded = (frightenedEnd != 0 && currentTime > frightenedEnd);

            // Reset combo si temps écoulé
            if(comboTimer > 0 && currentTime > comboTimer) {
                comboMultiplier = 1;
                comboTimer = 0;
            }

            float nx=pacman.x+pacman.dx;
            float ny=pacman.y+pacman.dy;
            int nr=int((ny+ENTITY/2)/TILE);
            int nc=int((nx+ENTITY/2)/TILE);

            if(nr==TUNNEL_ROW){
                if(nc<0){ nc=COLS-1; nx=nc*TILE+4; }
                if(nc>=COLS){ nc=0; nx=nc*TILE+4; }
            }

            if(canMove(nr,nc)){
                pacman.x=nx; pacman.y=ny;
                pacman.row=nr; pacman.col=nc;
            }

            if(maze[pacman.row][pacman.col]==2){
                maze[pacman.row][pacman.col]=0;
                score+=10 * comboMultiplier;
                pelletsLeft--;
                if(soundChomp) Mix_PlayChannel(-1, soundChomp, 0);
            }

            if(maze[pacman.row][pacman.col]==3){
                maze[pacman.row][pacman.col]=0;
                score+=50 * comboMultiplier;
                pelletsLeft--;
                frightenedEnd=currentTime+FRIGHT_TIME;
                comboMultiplier = 1;
                if(soundPowerUp) Mix_PlayChannel(-1, soundPowerUp, 0);
                for(auto& g:ghosts) {
                    if(g.state != EATEN && g.visible) {
                        g.state=FRIGHTENED;
                    }
                }
            }

            if(pelletsLeft<=0) {
                level++;
                gameState=WIN;
            }

            if(currentTime-lastBFS>200){
                for(auto& g:ghosts){
                    if(!g.visible) continue;

                    std::pair<int,int> target;

                    if(g.state == FRIGHTENED){
                        auto flee = getFleeTarget(g);
                        target = bfs(g.e.row, g.e.col, flee.first, flee.second);
                    } else if(g.state == NORMAL){
                        // Fantôme 0 : Chasseur direct (suit Pac-Man)
                        if(g.id == 0) {
                            target = bfs(g.e.row, g.e.col, pacman.row, pacman.col);
                        }
                        // Fantôme 1 : Prédicteur (anticipe la position de Pac-Man)
                        else if(g.id == 1) {
                            int predict = 4; // Prédit 4 cases à l'avance
                            int pr = pacman.row + (int)(pacman.dy * predict / PAC_SPEED);
                            int pc = pacman.col + (int)(pacman.dx * predict / PAC_SPEED);
                            // S'assurer que la prédiction est valide
                            if(canMove(pr, pc)) {
                                target = bfs(g.e.row, g.e.col, pr, pc);
                            } else {
                                target = bfs(g.e.row, g.e.col, pacman.row, pacman.col);
                            }
                        }
                    } else if(g.state == EATEN){
                        target = bfs(g.e.row, g.e.col, ghostStartPos[g.id][0], ghostStartPos[g.id][1]);
                    }

                    g.targetR = target.first;
                    g.targetC = target.second;
                }
                lastBFS = currentTime;
            }

            for(auto& g:ghosts){
                if(!g.visible) {
                    if(currentTime > g.respawnTime){
                        g.visible = true;
                        g.state = NORMAL;
                        g.respawnSafeTime = currentTime + 1000;
                        g.e.row = ghostStartPos[g.id][0];
                        g.e.col = ghostStartPos[g.id][1];
                        snap(g.e);
                        g.stuckTimer = 0;
                    }
                    continue;
                }

                float tx=g.targetC*TILE+4, ty=g.targetR*TILE+4;
                float vx=tx-g.e.x, vy=ty-g.e.y;
                float d=sqrt(vx*vx+vy*vy);

                float speed = (g.state == FRIGHTENED) ? GHOST_SPEED * 0.5f :
                             (g.state == EATEN) ? GHOST_SPEED * 1.5f : GHOST_SPEED;

                if(d<=speed) {
                    snap(g.e);
                    g.stuckTimer = 0;
                } else {
                    float newX = g.e.x + (vx/d)*speed;
                    float newY = g.e.y + (vy/d)*speed;

                    bool collision = false;
                    Ghost tempGhost = g;
                    tempGhost.e.x = newX;
                    tempGhost.e.y = newY;

                    for(auto& other : ghosts) {
                        if(other.id != g.id && checkGhostCollision(tempGhost, other)) {
                            collision = true;
                            break;
                        }
                    }

                    if(!collision) {
                        g.e.x = newX;
                        g.e.y = newY;
                        g.stuckTimer = 0;
                    } else {
                        g.stuckTimer++;
                        // Si bloqué trop longtemps, forcer un nouveau chemin
                        if(g.stuckTimer > 30) {
                            int dr[4]={-1,1,0,0}, dc[4]={0,0,-1,1};
                            int randomDir = rand() % 4;
                            g.targetR = g.e.row + dr[randomDir];
                            g.targetC = g.e.col + dc[randomDir];
                            g.stuckTimer = 0;
                        }
                    }
                }

                g.e.row = int((g.e.y + ENTITY/2) / TILE);
                g.e.col = int((g.e.x + ENTITY/2) / TILE);

                float dx = pacman.x - g.e.x;
                float dy = pacman.y - g.e.y;
                float distSq = dx*dx + dy*dy;

                if(distSq < 400){
                    if(g.state == FRIGHTENED){
                        score += 200 * comboMultiplier;
                        comboMultiplier++;
                        comboTimer = currentTime + 3000;
                        g.state = EATEN;
                        g.visible = false;
                        g.respawnTime = currentTime + 3000;
                        if(soundEatGhost) Mix_PlayChannel(-1, soundEatGhost, 0);
                    }
                    else if(g.state == NORMAL){
                        if(currentTime > g.respawnSafeTime){
                            lives--;
                            if(soundDeath) Mix_PlayChannel(-1, soundDeath, 0);
                            if (lives <= 0) {
                                if (score > highScore) {
                                    highScore = score;
                                    saveHighScore(highScore); //Sauvegarde HighScore
                                }
                                gameState = GAME_OVER;
                            }
                            else {
                                pacman.x = 1*TILE+4;
                                pacman.y = 14*TILE+4;
                                pacman.row = 14;
                                pacman.col = 1;
                                pacman.dx = 0;
                                pacman.dy = 0;

                                for(auto& gh : ghosts){
                                    gh.e.row = ghostStartPos[gh.id][0];
                                    gh.e.col = ghostStartPos[gh.id][1];
                                    snap(gh.e);
                                    gh.state = NORMAL;
                                    gh.visible = true;
                                    gh.respawnSafeTime = currentTime + 2000;
                                    gh.stuckTimer = 0;
                                }

                                SDL_Delay(1000);
                            }
                        }
                    }
                }
            }

            if(frightEnded){
                frightenedEnd = 0;
                for(auto& g:ghosts){
                    if(g.state == FRIGHTENED){
                        g.state = NORMAL;
                    }
                }
            }
        }

        // ================= RENDU =================
        drawGradient(0, 0, WIDTH, HEIGHT, {10,10,30}, {5,5,15});

        for(int r=0;r<ROWS;r++) {
            for(int c=0;c<COLS;c++){
                if(maze[r][c]==1){
                    SDL_Rect t={c*TILE,r*TILE,TILE,TILE};
                    SDL_SetRenderDrawColor(renderer,0,0,150,255);
                    SDL_RenderFillRect(renderer,&t);
                    SDL_SetRenderDrawColor(renderer,50,50,200,255);
                    SDL_Rect inner={c*TILE+2,r*TILE+2,TILE-4,TILE-4};
                    SDL_RenderFillRect(renderer,&inner);
                }
                if(maze[r][c]==2){
                    int pulse = (currentTime / 100) % 20;
                    int size = 4 + pulse / 10;
                    SDL_SetRenderDrawColor(renderer,255,255,100,255);
                    SDL_Rect d={c*TILE+(TILE-size)/2,r*TILE+(TILE-size)/2,size,size};
                    SDL_RenderFillRect(renderer,&d);
                }
                if(maze[r][c]==3){
                    int glow = abs((int)(currentTime / 50) % 40 - 20);
                    SDL_SetRenderDrawBlendMode(renderer, SDL_BLENDMODE_BLEND);
                    SDL_SetRenderDrawColor(renderer,255,255,255,200+glow);
                    SDL_Rect outer={c*TILE+8,r*TILE+8,24,24};
                    SDL_RenderFillRect(renderer,&outer);
                    SDL_SetRenderDrawColor(renderer,255,255,255,255);
                    SDL_Rect d={c*TILE+12,r*TILE+12,16,16};
                    SDL_RenderFillRect(renderer,&d);
                }
            }
        }

        if(gameState==MENU){
            drawRoundedRect(WIDTH/2-250, HEIGHT/2-200, 500, 400, {0,0,0}, 200);

            drawTextCentered("PAC-MAN", HEIGHT/2-150, {255,255,0}, fontLarge);
            drawTextCentered("Appuyez sur ESPACE pour jouer", HEIGHT/2-50, {200,200,255}, font);
            drawTextCentered("Fleches ou ZQSD pour bouger", HEIGHT/2, {150,150,200}, fontSmall);
            drawTextCentered("P = Pause  |  ESC = Quitter", HEIGHT/2+30, {150,150,200}, fontSmall);
            drawTextCentered("Mangez toutes les pastilles !", HEIGHT/2+80, {100,255,100}, fontSmall);
        }

        if(gameState==PLAYING||gameState==PAUSED){
            SDL_Rect p={(int)pacman.x,(int)pacman.y,ENTITY,ENTITY};
            double angle = 0;
            if(pacman.dx > 0) angle = 0;
            else if(pacman.dx < 0) angle = 180;
            else if(pacman.dy < 0) angle = 270;
            else if(pacman.dy > 0) angle = 90;
            SDL_RenderCopyEx(renderer,texPac,nullptr,&p,angle,nullptr,SDL_FLIP_NONE);

            for(auto& g:ghosts){
                if(!g.visible) continue;

                if(g.state == FRIGHTENED) {
                    if(frightenedEnd - currentTime < 2000) {
                        if((currentTime / 200) % 2 == 0)
                            SDL_SetTextureColorMod(g.tex,255,255,255);
                        else
                            SDL_SetTextureColorMod(g.tex,50,50,255);
                    } else {
                        SDL_SetTextureColorMod(g.tex,50,50,255);
                    }
                    SDL_SetTextureAlphaMod(g.tex, 200);
                }
                else if(g.state == EATEN) {
                    SDL_SetTextureColorMod(g.tex,100,100,100);
                    SDL_SetTextureAlphaMod(g.tex, 128);
                }
                else {
                    SDL_SetTextureColorMod(g.tex,255,255,255);
                    SDL_SetTextureAlphaMod(g.tex, 255);

                    if(currentTime < g.respawnSafeTime) {
                        if((currentTime / 150) % 2 == 0)
                            SDL_SetTextureAlphaMod(g.tex, 100);
                    }
                }

                SDL_Rect r={(int)g.e.x,(int)g.e.y,ENTITY,ENTITY};
                SDL_RenderCopy(renderer,g.tex,nullptr,&r);
            }

            drawRoundedRect(0, HEIGHT-100, WIDTH, 100, {20,20,40}, 230);
            SDL_SetRenderDrawColor(renderer,100,100,150,255);
            SDL_RenderDrawLine(renderer, 0, HEIGHT-100, WIDTH, HEIGHT-100);

            drawText("SCORE",20,HEIGHT-80,{150,150,200},fontSmall);
            drawText(std::to_string(score),20,HEIGHT-55,{255,255,100},font);

            drawText("RECORD",200,HEIGHT-80,{150,150,200},fontSmall);
            drawText(std::to_string(highScore),200,HEIGHT-55,{255,100,100},font);

            drawText("NIVEAU",400,HEIGHT-80,{150,150,200},fontSmall);
            drawText(std::to_string(level),400,HEIGHT-55,{100,255,100},font);

            drawText("VIES",550,HEIGHT-80,{150,150,200},fontSmall);
            for(int i=0;i<lives;i++){
                SDL_Rect heart={550+i*25,HEIGHT-50,20,20};
                SDL_SetRenderDrawColor(renderer,255,50,50,255);
                SDL_RenderFillRect(renderer,&heart);
            }

            if(comboMultiplier > 1) {
                std::string comboText = "COMBO x" + std::to_string(comboMultiplier);
                drawText(comboText, WIDTH-120, HEIGHT-55, {255,200,0}, font);
            }

            if(gameState==PAUSED) {
                drawRoundedRect(WIDTH/2-150, HEIGHT/2-100, 300, 200, {0,0,0}, 230);
                drawTextCentered("PAUSE",HEIGHT/2-40,{255,255,0},fontLarge);
                drawTextCentered("Appuyez sur P pour continuer",HEIGHT/2+40,{200,200,200},fontSmall);
            }
        }

        if(gameState==WIN){
            drawRoundedRect(WIDTH/2-200, HEIGHT/2-150, 400, 300, {0,50,0}, 230);
            drawTextCentered("NIVEAU TERMINE !",HEIGHT/2-80,{100,255,100},fontLarge);
            drawTextCentered("Score: "+std::to_string(score),HEIGHT/2,{255,255,100},font);
            drawTextCentered("Niveau suivant: "+std::to_string(level),HEIGHT/2+40,{200,200,255},font);
            drawTextCentered("ESPACE pour continuer",HEIGHT/2+90,{150,255,150},fontSmall);
        }

        if(gameState==GAME_OVER){
            drawRoundedRect(WIDTH/2-200, HEIGHT/2-150, 400, 300, {50,0,0}, 230);
            drawTextCentered("GAME OVER",HEIGHT/2-80,{255,50,50},fontLarge);
            drawTextCentered("Score final: "+std::to_string(score),HEIGHT/2,{255,255,100},font);
            drawTextCentered("Record: "+std::to_string(highScore),HEIGHT/2+40,{255,200,100},font);
            drawTextCentered("ESPACE pour recommencer",HEIGHT/2+90,{255,150,150},fontSmall);
        }

        SDL_RenderPresent(renderer);
        SDL_Delay(16);
    }

    SDL_DestroyTexture(texPac);
    for(int i=0;i<NUM_GHOSTS;i++) if(ghostTex[i]) SDL_DestroyTexture(ghostTex[i]);
    if(font) TTF_CloseFont(font);
    if(fontLarge) TTF_CloseFont(fontLarge);
    if(fontSmall) TTF_CloseFont(fontSmall);
    SDL_DestroyRenderer(renderer);
    SDL_DestroyWindow(window);

    // ================= NETTOYAGE AUDIO =================
    if(soundChomp) Mix_FreeChunk(soundChomp);
    if(soundEatGhost) Mix_FreeChunk(soundEatGhost);
    if(soundDeath) Mix_FreeChunk(soundDeath);
    if(soundPowerUp) Mix_FreeChunk(soundPowerUp);
    if(musicBg) Mix_FreeMusic(musicBg);
    Mix_CloseAudio();

    TTF_Quit();
    IMG_Quit();
    SDL_Quit();
    return 0;
}
