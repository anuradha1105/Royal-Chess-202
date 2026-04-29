#include <QApplication>
#include <QMainWindow>
#include <QWidget>
#include <QPainter>
#include <QMouseEvent>
#include <QVBoxLayout>
#include <QHBoxLayout>
#include <QLabel>
#include <QPushButton>
#include <QLineEdit>
#include <QMessageBox>
#include <QTimer>
#include <QStackedWidget>
#include <QScrollArea>
#include <QScrollBar>
#include <QFileInfo>
#include <QFont>
#include <QJsonObject>
#include <QJsonArray>
#include <QJsonDocument>
#include <QFile>
#include <QDir>
#include <QStandardPaths>
#include <QDateTime>
#include <vector>
#include <array>
#include <memory>
#include <algorithm>
#include <climits>
#include <cmath>
#include <functional>

// ─── Types ────────────────────────────────────────────────────────────────────
enum class Color { White, Black, None };
inline Color opp(Color c){ return c==Color::White?Color::Black:Color::White; }

enum class PType { King,Queen,Rook,Bishop,Knight,Pawn,None };

struct Pos {
    int r=-1,c=-1;
    bool ok() const { return r>=0&&r<8&&c>=0&&c<8; }
    bool operator==(const Pos& o) const { return r==o.r&&c==o.c; }
    bool operator!=(const Pos& o) const { return !(*this==o); }
};

struct Move {
    Pos from,to;
    PType piece=PType::None, cap=PType::None;
    Color pCol=Color::None, cCol=Color::None;
    Pos capPos;
    bool castle=false,enPassant=false,promotion=false;
    bool kSide=false;
};

// ─── Piece values ─────────────────────────────────────────────────────────────
static int pieceVal(PType t){
    switch(t){
        case PType::Pawn:   return 100;
        case PType::Knight: return 320;
        case PType::Bishop: return 330;
        case PType::Rook:   return 500;
        case PType::Queen:  return 900;
        case PType::King:   return 20000;
        default: return 0;
    }
}

// ─── Board ────────────────────────────────────────────────────────────────────
struct Square { PType type=PType::None; Color col=Color::None; bool moved=false; };

class Board {
public:
    std::array<std::array<Square,8>,8> g;
    Color turn=Color::White;
    Pos ep;
    std::vector<Move> history;

    void reset(){
        for(auto& row:g) for(auto& s:row) s={PType::None,Color::None,false};
        turn=Color::White; ep={}; history.clear();
        // White
        auto place=[&](int r,int c,PType t,Color col){ g[r][c]={t,col,false}; };
        place(0,0,PType::Rook,Color::White); place(0,1,PType::Knight,Color::White);
        place(0,2,PType::Bishop,Color::White); place(0,3,PType::Queen,Color::White);
        place(0,4,PType::King,Color::White); place(0,5,PType::Bishop,Color::White);
        place(0,6,PType::Knight,Color::White); place(0,7,PType::Rook,Color::White);
        for(int c=0;c<8;c++) place(1,c,PType::Pawn,Color::White);
        // Black
        place(7,0,PType::Rook,Color::Black); place(7,1,PType::Knight,Color::Black);
        place(7,2,PType::Bishop,Color::Black); place(7,3,PType::Queen,Color::Black);
        place(7,4,PType::King,Color::Black); place(7,5,PType::Bishop,Color::Black);
        place(7,6,PType::Knight,Color::Black); place(7,7,PType::Rook,Color::Black);
        for(int c=0;c<8;c++) place(6,c,PType::Pawn,Color::Black);
    }

    Square& at(Pos p){ return g[p.r][p.c]; }
    const Square& at(Pos p) const { return g[p.r][p.c]; }

    Pos findKing(Color col) const {
        for(int r=0;r<8;r++) for(int c=0;c<8;c++)
            if(g[r][c].type==PType::King&&g[r][c].col==col) return {r,c};
        return {};
    }

    bool attacked(Pos pos, Color by) const;
    bool inCheck(Color col) const { return attacked(findKing(col),by(col)); }
    Color by(Color c) const { return opp(c); }

    std::vector<Move> pseudoMoves(Color col) const;
    std::vector<Move> legalMoves(Color col);
    void make(const Move& m);
    void undo(const Move& m);

    int evaluate() const {
        int score=0;
        for(int r=0;r<8;r++) for(int c=0;c<8;c++){
            auto& s=g[r][c];
            if(s.type==PType::None) continue;
            int v=pieceVal(s.type);
            score += (s.col==Color::White)?v:-v;
        }
        return score;
    }
};

// ── Attack detection ──────────────────────────────────────────────────────────
bool Board::attacked(Pos pos, Color by) const {
    // Check knight attacks
    int kj[][2]={{2,1},{2,-1},{-2,1},{-2,-1},{1,2},{1,-2},{-1,2},{-1,-2}};
    for(auto& j:kj){
        Pos p{pos.r+j[0],pos.c+j[1]};
        if(p.ok()&&g[p.r][p.c].type==PType::Knight&&g[p.r][p.c].col==by) return true;
    }
    // Check sliding (rook/queen horizontal/vertical)
    int sd[][2]={{1,0},{-1,0},{0,1},{0,-1}};
    for(auto& d:sd){
        Pos p=pos;
        while(true){
            p={p.r+d[0],p.c+d[1]};
            if(!p.ok()) break;
            auto& s=g[p.r][p.c];
            if(s.type!=PType::None){
                if(s.col==by&&(s.type==PType::Rook||s.type==PType::Queen)) return true;
                break;
            }
        }
    }
    // Check sliding diagonal (bishop/queen)
    int bd[][2]={{1,1},{1,-1},{-1,1},{-1,-1}};
    for(auto& d:bd){
        Pos p=pos;
        while(true){
            p={p.r+d[0],p.c+d[1]};
            if(!p.ok()) break;
            auto& s=g[p.r][p.c];
            if(s.type!=PType::None){
                if(s.col==by&&(s.type==PType::Bishop||s.type==PType::Queen)) return true;
                break;
            }
        }
    }
    // King
    int kd[][2]={{1,0},{-1,0},{0,1},{0,-1},{1,1},{1,-1},{-1,1},{-1,-1}};
    for(auto& d:kd){
        Pos p{pos.r+d[0],pos.c+d[1]};
        if(p.ok()&&g[p.r][p.c].type==PType::King&&g[p.r][p.c].col==by) return true;
    }
    // Pawn
    int pDir=(by==Color::White)?1:-1;
    for(int dc:{-1,1}){
        Pos p{pos.r-pDir,pos.c+dc};
        if(p.ok()&&g[p.r][p.c].type==PType::Pawn&&g[p.r][p.c].col==by) return true;
    }
    return false;
}

// ── Pseudo-legal moves ────────────────────────────────────────────────────────
std::vector<Move> Board::pseudoMoves(Color col) const {
    std::vector<Move> moves;
    for(int r=0;r<8;r++) for(int c=0;c<8;c++){
        auto& s=g[r][c];
        if(s.type==PType::None||s.col!=col) continue;
        Pos from{r,c};

        auto addMove=[&](Pos to){
            Move m; m.from=from; m.to=to; m.piece=s.type; m.pCol=col;
            auto& t=g[to.r][to.c];
            if(t.type!=PType::None){ m.cap=t.type; m.cCol=t.col; m.capPos=to; }
            if(s.type==PType::Pawn){
                int promRow=(col==Color::White)?7:0;
                if(to.r==promRow) m.promotion=true;
            }
            moves.push_back(m);
        };

        auto slide=[&](int dr,int dc){
            Pos p{r+dr,c+dc};
            while(p.ok()){
                auto& t=g[p.r][p.c];
                if(t.type!=PType::None){
                    if(t.col!=col){ Move m; m.from=from; m.to=p; m.piece=s.type; m.pCol=col; m.cap=t.type; m.cCol=t.col; m.capPos=p; moves.push_back(m); }
                    break;
                }
                addMove(p);
                p={p.r+dr,p.c+dc};
            }
        };

        switch(s.type){
        case PType::Knight:{
            int j[][2]={{2,1},{2,-1},{-2,1},{-2,-1},{1,2},{1,-2},{-1,2},{-1,-2}};
            for(auto& jj:j){ Pos p{r+jj[0],c+jj[1]}; if(p.ok()&&g[p.r][p.c].col!=col) addMove(p); }
        } break;
        case PType::Bishop: slide(1,1);slide(1,-1);slide(-1,1);slide(-1,-1); break;
        case PType::Rook:   slide(1,0);slide(-1,0);slide(0,1);slide(0,-1); break;
        case PType::Queen:  slide(1,0);slide(-1,0);slide(0,1);slide(0,-1);slide(1,1);slide(1,-1);slide(-1,1);slide(-1,-1); break;
        case PType::King:{
            int d[][2]={{1,0},{-1,0},{0,1},{0,-1},{1,1},{1,-1},{-1,1},{-1,-1}};
            for(auto& dd:d){ Pos p{r+dd[0],c+dd[1]}; if(p.ok()&&g[p.r][p.c].col!=col) addMove(p); }
            // Castling
            if(!s.moved&&!inCheck(col)){
                auto trycastle=[&](bool ks){
                    int rc=ks?7:0; int steps=ks?2:-2;
                    if(g[r][rc].type==PType::Rook&&!g[r][rc].moved){
                        int s1=ks?5:3,s2=ks?6:1;
                        bool clear=true;
                        for(int cc=std::min(c+steps,c);cc<=std::max(c+steps,c);cc++) if(cc!=c&&g[r][cc].type!=PType::None) clear=false;
                        if(clear){
                            bool safe=true;
                            for(int cc=c;cc!=(c+steps+1*(steps>0?1:-1));cc+=(steps>0?1:-1)) if(attacked({r,cc},opp(col))) safe=false;
                            if(safe){ Move m; m.from=from; m.to={r,c+(ks?2:-2)}; m.piece=PType::King; m.pCol=col; m.castle=true; m.kSide=ks; moves.push_back(m); }
                        }
                    }
                };
                trycastle(true); trycastle(false);
            }
        } break;
        case PType::Pawn:{
            int dir=(col==Color::White)?1:-1;
            Pos fwd{r+dir,c};
            if(fwd.ok()&&g[fwd.r][fwd.c].type==PType::None){
                addMove(fwd);
                int startR=(col==Color::White)?1:6;
                Pos fwd2{r+2*dir,c};
                if(r==startR&&g[fwd2.r][fwd2.c].type==PType::None) addMove(fwd2);
            }
            for(int dc:{-1,1}){
                Pos diag{r+dir,c+dc};
                if(!diag.ok()) continue;
                if(g[diag.r][diag.c].type!=PType::None&&g[diag.r][diag.c].col!=col) addMove(diag);
                if(diag==ep){ Move m; m.from=from; m.to=diag; m.piece=PType::Pawn; m.pCol=col; m.enPassant=true; m.cap=PType::Pawn; m.cCol=opp(col); m.capPos={r,c+dc}; moves.push_back(m); }
            }
        } break;
        default: break;
        }
    }
    return moves;
}

// ── Make / Undo ───────────────────────────────────────────────────────────────
void Board::make(const Move& m){
    auto& from=g[m.from.r][m.from.c];
    auto& to=g[m.to.r][m.to.c];
    // En passant capture
    if(m.enPassant) g[m.capPos.r][m.capPos.c]={PType::None,Color::None,false};
    // Castling rook
    if(m.castle){
        int rFrom=m.kSide?7:0, rTo=m.kSide?5:3;
        g[m.from.r][rTo]=g[m.from.r][rFrom]; g[m.from.r][rTo].moved=true;
        g[m.from.r][rFrom]={PType::None,Color::None,false};
    }
    to=from; to.moved=true;
    if(m.promotion) to.type=PType::Queen;
    from={PType::None,Color::None,false};
    // EP target
    ep={};
    if(m.piece==PType::Pawn&&std::abs(m.to.r-m.from.r)==2)
        ep={(m.from.r+m.to.r)/2,m.from.c};
    turn=opp(turn);
    history.push_back(m);
}

void Board::undo(const Move& m){
    history.pop_back();
    auto& from=g[m.from.r][m.from.c];
    auto& to=g[m.to.r][m.to.c];
    from=to;
    from.type=m.piece;
    from.moved=!history.empty(); // approximate
    to={PType::None,Color::None,false};
    if(m.cap!=PType::None&&!m.enPassant) g[m.capPos.r][m.capPos.c]={m.cap,m.cCol,true};
    if(m.enPassant) g[m.capPos.r][m.capPos.c]={PType::Pawn,m.cCol,true};
    if(m.castle){
        int rTo=m.kSide?7:0, rFrom=m.kSide?5:3;
        g[m.from.r][rTo]=g[m.from.r][rFrom]; g[m.from.r][rTo].moved=false;
        g[m.from.r][rFrom]={PType::None,Color::None,false};
    }
    // Restore ep from history
    if(!history.empty()){
        auto& last=history.back();
        if(last.piece==PType::Pawn&&std::abs(last.to.r-last.from.r)==2)
            ep={(last.from.r+last.to.r)/2,last.from.c};
        else ep={};
    } else ep={};
    turn=opp(turn);
}

std::vector<Move> Board::legalMoves(Color col){
    std::vector<Move> legal;
    for(auto& m:pseudoMoves(col)){
        make(m);
        if(!inCheck(col)) legal.push_back(m);
        undo(m);
    }
    return legal;
}

// ─── AI ───────────────────────────────────────────────────────────────────────
int alphaBeta(Board& b, int depth, int alpha, int beta, bool maxing){
    if(depth==0) return b.evaluate();
    Color col=maxing?Color::White:Color::Black;
    auto moves=b.legalMoves(col);
    if(moves.empty()) return b.inCheck(col)?(maxing?-15000:15000):0;
    if(maxing){
        int best=INT_MIN;
        for(auto& m:moves){ b.make(m); best=std::max(best,alphaBeta(b,depth-1,alpha,beta,false)); b.undo(m); alpha=std::max(alpha,best); if(beta<=alpha) break; }
        return best;
    } else {
        int best=INT_MAX;
        for(auto& m:moves){ b.make(m); best=std::min(best,alphaBeta(b,depth-1,alpha,beta,true)); b.undo(m); beta=std::min(beta,best); if(beta<=alpha) break; }
        return best;
    }
}

Move bestMove(Board& b, Color col, int depth){
    auto moves=b.legalMoves(col);
    if(moves.empty()) return {};
    Move best=moves[0];
    int bestVal=(col==Color::White)?INT_MIN:INT_MAX;
    bool maxing=(col==Color::White);
    for(auto& m:moves){
        b.make(m);
        int val=alphaBeta(b,depth-1,INT_MIN,INT_MAX,!maxing);
        b.undo(m);
        if(maxing?val>bestVal:val<bestVal){ bestVal=val; best=m; }
    }
    return best;
}

// ─── Board Widget ─────────────────────────────────────────────────────────────
class BoardWidget : public QWidget {
    Q_OBJECT
public:
    Board board;
    Color playerColor=Color::White;
    int aiDepth=3;
    bool gameActive=false;
    Pos selected;
    std::vector<Pos> hints;
    std::vector<Move> cachedLegalMoves;
    std::function<void(const QString&)> onEvent;

    explicit BoardWidget(QWidget* p=nullptr):QWidget(p){
        setMinimumSize(480,480);
        setSizePolicy(QSizePolicy::Expanding,QSizePolicy::Expanding);
    }

    void startGame(Color pc, int depth){
        playerColor=pc; aiDepth=depth;
        board.reset(); gameActive=true;
        selected={}; hints.clear();
        update();
        if(playerColor==Color::Black) QTimer::singleShot(300,this,&BoardWidget::doAI);
    }

    void stopGame(){ gameActive=false; selected={}; hints.clear(); update(); }

protected:
    void paintEvent(QPaintEvent*) override {
        QPainter p(this);
        p.setRenderHint(QPainter::Antialiasing);
        int sz=squareSize();

        // Board squares
        for(int r=0;r<8;r++) for(int c=0;c<8;c++){
            bool light=(r+c)%2==0;
            p.fillRect(c*sz,(7-r)*sz,sz,sz,light?QColor("#D4A96A"):QColor("#8B5E1A"));
        }

        if(!gameActive){ drawCoords(p,sz); return; }

        // Last move highlight
        if(!board.history.empty()){
            auto& lm=board.history.back();
            auto hl=[&](Pos pos){ QPoint tl=toScreen(pos,sz); p.fillRect(tl.x(),tl.y(),sz,sz,QColor(255,255,0,80)); };
            hl(lm.from); hl(lm.to);
        }

        // Selected + hints
        if(selected.ok()){
            QPoint tl=toScreen(selected,sz);
            p.fillRect(tl.x(),tl.y(),sz,sz,QColor(255,255,0,140));
        }
        p.setPen(Qt::NoPen);
        for(auto& h:hints){
            QPoint tl=toScreen(h,sz);
            bool cap=board.g[h.r][h.c].type!=PType::None;
            p.setBrush(QColor(0,0,0,cap?0:65));
            if(cap){ p.setBrush(Qt::NoBrush); p.setPen(QPen(QColor(0,0,0,100),sz*0.08)); p.drawEllipse(tl.x()+2,tl.y()+2,sz-4,sz-4); p.setPen(Qt::NoPen); }
            else p.drawEllipse(tl.x()+sz/2-sz/6,tl.y()+sz/2-sz/6,sz/3,sz/3);
        }

        // Check highlight
        if(board.inCheck(board.turn)){
            Pos kp=board.findKing(board.turn);
            QPoint tl=toScreen(kp,sz);
            p.fillRect(tl.x(),tl.y(),sz,sz,QColor(200,30,30,160));
        }

        // Pieces
        drawPieces(p,sz);
        drawCoords(p,sz);
    }

    void drawPieces(QPainter& p, int sz){
        // Unicode chess pieces - using system font
        static const QString wp[]={"♔","♕","♖","♗","♘","♙"};
        static const QString bp[]={"♚","♛","♜","♝","♞","♟"};
        static const PType order[]={PType::King,PType::Queen,PType::Rook,PType::Bishop,PType::Knight,PType::Pawn};

        QFont font=p.font();
        font.setPixelSize(sz*0.72);
        p.setFont(font);

        for(int r=0;r<8;r++) for(int c=0;c<8;c++){
            auto& sq=board.g[r][c];
            if(sq.type==PType::None) continue;
            QString sym="?";
            for(int i=0;i<6;i++) if(order[i]==sq.type){ sym=(sq.col==Color::White?wp[i]:bp[i]); break; }
            QPoint tl=toScreen({r,c},sz);
            // Shadow
            p.setPen(QColor(0,0,0,100));
            p.drawText(QRect(tl.x()+2,tl.y()+2,sz,sz),Qt::AlignCenter,sym);
            // Piece
            p.setPen(sq.col==Color::White?QColor(255,250,230):QColor(10,5,0));
            p.drawText(QRect(tl.x(),tl.y(),sz,sz),Qt::AlignCenter,sym);
        }
    }

    void drawCoords(QPainter& p, int sz){
        QFont f("Georgia",sz/7); p.setFont(f);
        for(int i=0;i<8;i++){
            bool flip=(playerColor==Color::Black);
            int rank=flip?i+1:8-i;
            bool rLight=(i%2==(flip?1:0));
            p.setPen(rLight?QColor("#8B5E1A"):QColor("#D4A96A"));
            p.drawText(3,i*sz+14,QString::number(rank));
            int file=flip?7-i:i;
            bool fLight=(file%2==(flip?1:0));
            p.setPen(fLight?QColor("#8B5E1A"):QColor("#D4A96A"));
            QFontMetrics fm(f);
            QString letter=QString(QChar('a'+file));
            p.drawText(i*sz+sz-fm.horizontalAdvance(letter)-3,8*sz-3,letter);
        }
    }

    void mousePressEvent(QMouseEvent* e) override {
        if(!gameActive||e->button()!=Qt::LeftButton) return;
        if(board.turn!=playerColor) return;
        Pos pos=toBoard(e->pos());
        if(!pos.ok()) return;

        auto& sq=board.g[pos.r][pos.c];

        // If we have a selection and clicked a hint — make the move
        if(selected.ok()){
            for(auto& h:hints){
                if(h==pos){
                    // Find matching legal move
                    for(auto& m:cachedLegalMoves){
                        if(m.from==selected&&m.to==pos){
                            board.make(m);
                            selected={}; hints.clear(); cachedLegalMoves.clear();
                            update();
                            // Check game over simply
                            bool oppInCheck=board.inCheck(board.turn);
                            auto oppMoves=board.legalMoves(board.turn);
                            if(oppMoves.empty()){
                                gameActive=false;
                                QString winner=(board.turn==Color::White)?"Black":"White";
                                if(onEvent) onEvent(oppInCheck?"checkmate:"+winner:"stalemate");
                            } else if(oppInCheck){
                                if(onEvent) onEvent("check");
                                QTimer::singleShot(400,this,&BoardWidget::doAI);
                            } else {
                                QTimer::singleShot(400,this,&BoardWidget::doAI);
                            }
                            return;
                        }
                    }
                }
            }
        }

        // Select own piece
        if(sq.type!=PType::None&&sq.col==playerColor){
            selected=pos;
            hints.clear();
            cachedLegalMoves=board.legalMoves(playerColor);
            for(auto& m:cachedLegalMoves) if(m.from==pos) hints.push_back(m.to);
            update();
        } else {
            selected={}; hints.clear(); cachedLegalMoves.clear(); update();
        }
    }

private slots:
    void doAI(){
        if(!gameActive||board.turn==playerColor) return;
        Move m=bestMove(board,opp(playerColor),aiDepth);
        if(!m.from.ok()) return;
        board.make(m); update();
        // Check if player has moves
        bool playerInCheck=board.inCheck(playerColor);
        auto playerMoves=board.legalMoves(playerColor);
        if(playerMoves.empty()){
            gameActive=false;
            QString winner=(playerColor==Color::White)?"Black":"White";
            if(onEvent) onEvent(playerInCheck?"checkmate:"+winner:"stalemate");
        } else if(playerInCheck){
            if(onEvent) onEvent("check");
        }
    }

private:
    void checkGameState(){
        auto moves=board.legalMoves(board.turn);
        if(moves.empty()){
            gameActive=false;
            if(board.inCheck(board.turn)){
                QString winner=(board.turn==Color::White)?"Black":"White";
                if(onEvent) onEvent("checkmate:" + winner);
            } else {
                if(onEvent) onEvent("stalemate");
            }
        } else if(board.inCheck(board.turn)){
            if(onEvent) onEvent("check");
        }
    }

    int squareSize() const { return std::min(width(),height())/8; }

    QPoint toScreen(Pos p, int sz) const {
        bool flip=(playerColor==Color::Black);
        int col=flip?7-p.c:p.c;
        int row=flip?p.r:7-p.r;
        return {col*sz,row*sz};
    }

    Pos toBoard(QPoint pt) const {
        int sz=squareSize();
        bool flip=(playerColor==Color::Black);
        int col=pt.x()/sz, row=pt.y()/sz;
        if(flip){ col=7-col; row=7-row; } else { row=7-row; }
        if(col<0||col>7||row<0||row>7) return {};
        return {row,col};
    }
};


// ─── Data System ──────────────────────────────────────────────────────────────
struct MatchRecord {
    QString opponent, result, playerColor, timeControl, date;
    int moves=0, eloChange=0;
};

struct PlayerProfile {
    QString name, joinDate;
    int elo=1200, wins=0, losses=0, draws=0;
    QList<MatchRecord> history;
    int total() const { return wins+losses+draws; }
    double winRate() const { return total()>0?(wins*100.0/total()):0; }
    QString title() const {
        if(elo>=2000) return "Grandmaster";
        if(elo>=1800) return "Master";
        if(elo>=1600) return "Expert";
        if(elo>=1400) return "Knight";
        return "Squire";
    }
    static int calcElo(int myElo, int oppElo, const QString& result){
        double exp=1.0/(1.0+std::pow(10.0,(oppElo-myElo)/400.0));
        double score=(result=="WIN")?1.0:(result=="DRAW")?0.5:0.0;
        return (int)(32*(score-exp));
    }
    QJsonObject toJson() const {
        QJsonObject o;
        o["name"]=name; o["elo"]=elo; o["wins"]=wins;
        o["losses"]=losses; o["draws"]=draws; o["joinDate"]=joinDate;
        QJsonArray arr;
        for(auto& m:history){
            QJsonObject mo;
            mo["opponent"]=m.opponent; mo["result"]=m.result;
            mo["playerColor"]=m.playerColor; mo["timeControl"]=m.timeControl;
            mo["date"]=m.date; mo["moves"]=m.moves; mo["eloChange"]=m.eloChange;
            arr.append(mo);
        }
        o["history"]=arr;
        return o;
    }
    static PlayerProfile fromJson(const QJsonObject& o){
        PlayerProfile p;
        p.name=o["name"].toString(); p.elo=o["elo"].toInt(1200);
        p.wins=o["wins"].toInt(); p.losses=o["losses"].toInt();
        p.draws=o["draws"].toInt(); p.joinDate=o["joinDate"].toString();
        for(auto v:o["history"].toArray()){
            auto mo=v.toObject(); MatchRecord m;
            m.opponent=mo["opponent"].toString(); m.result=mo["result"].toString();
            m.playerColor=mo["playerColor"].toString(); m.timeControl=mo["timeControl"].toString();
            m.date=mo["date"].toString(); m.moves=mo["moves"].toInt(); m.eloChange=mo["eloChange"].toInt();
            p.history.append(m);
        }
        return p;
    }
};

class DataMgr {
public:
    static DataMgr& inst(){ static DataMgr d; return d; }
    PlayerProfile current;
    bool loggedIn=false;

    QString path() const {
        return QStandardPaths::writableLocation(QStandardPaths::DocumentsLocation)+"/RoyalChess/players.json";
    }
    QList<PlayerProfile> loadAll(){
        QFile f(path()); if(!f.exists()||!f.open(QIODevice::ReadOnly)) return {};
        auto arr=QJsonDocument::fromJson(f.readAll()).array(); f.close();
        QList<PlayerProfile> list;
        for(auto v:arr) list.append(PlayerProfile::fromJson(v.toObject()));
        return list;
    }
    void saveAll(const QList<PlayerProfile>& players){
        QDir().mkpath(QFileInfo(path()).absolutePath());
        QJsonArray arr; for(auto& p:players) arr.append(p.toJson());
        QFile f(path()); if(f.open(QIODevice::WriteOnly)){ f.write(QJsonDocument(arr).toJson()); f.close(); }
    }
    bool registerPlayer(const QString& name){
        if(name.trimmed().isEmpty()) return false;
        auto players=loadAll();
        for(auto& p:players) if(p.name.toLower()==name.toLower()) return false;
        PlayerProfile np; np.name=name.trimmed(); np.elo=1200;
        np.joinDate=QDateTime::currentDateTime().toString("MMM yyyy").toUpper();
        players.append(np); saveAll(players); current=np; loggedIn=true; return true;
    }
    bool loginPlayer(const QString& name){
        auto players=loadAll();
        for(auto& p:players){ if(p.name.toLower()==name.trimmed().toLower()){ current=p; loggedIn=true; return true; } }
        return false;
    }
    void saveMatch(const QString& result, const QString& opp, int oppElo, int moves, const QString& col, const QString& tc){
        // If not formally logged in but has a name, create profile on the fly
        if(!loggedIn) {
            if(current.name.isEmpty()) return;
            current.elo=1200; current.wins=0; current.losses=0; current.draws=0;
            current.joinDate=QDateTime::currentDateTime().toString("MMM yyyy").toUpper();
            loggedIn=true;
            auto players=loadAll();
            players.append(current);
            saveAll(players);
        }
        int ec=PlayerProfile::calcElo(current.elo,oppElo,result);
        current.elo=qMax(100,current.elo+ec);
        if(result=="WIN") ++current.wins;
        else if(result=="LOSS") ++current.losses;
        else ++current.draws;
        MatchRecord m; m.opponent=opp; m.result=result; m.playerColor=col;
        m.timeControl=tc; m.moves=moves; m.eloChange=ec;
        m.date=QDateTime::currentDateTime().toString("MMM dd yyyy").toUpper();
        current.history.prepend(m);
        auto players=loadAll();
        for(auto& p:players){ if(p.name.toLower()==current.name.toLower()){ p=current; break; } }
        saveAll(players);
    }
private:
    DataMgr()=default;
};

// ─── Main Window ──────────────────────────────────────────────────────────────
class MainWindow : public QMainWindow {
    Q_OBJECT
    QStackedWidget* stack=nullptr;
    BoardWidget* board=nullptr;
    QLabel* statusLbl=nullptr;
    QLabel* playerNameLbl=nullptr;
    QStackedWidget* homePages=nullptr;
    QWidget* profilePage=nullptr;
    QWidget* ranksPage=nullptr;
    QWidget* historyPage=nullptr;
    QString playerName="Player";
    int playerElo=1200;
    int currentDifficulty=3;
    int currentColorInt=0;
    int movesPlayed=0;
    int gameTimeSecs=600;  // default 10 min
    // Clock labels (updated during game)
    QLabel* playerClockLbl=nullptr;
    QLabel* aiClockLbl=nullptr;
    QLabel* moveLbl=nullptr;
    int playerSecs=600;
    int aiSecs=600;
    int moveStartSecs=0;
    QTimer* playerClockTimer=nullptr;
    QTimer* aiClockTimer=nullptr;
    QTimer* moveTimer=nullptr;
    QList<int> moveTimings;  // time taken per move in seconds

public:
    MainWindow(){
        setWindowTitle("Royal Chess");
        resize(900,650);
        setStyleSheet("QMainWindow,QWidget{background:#1a1208;color:#D4AF37;font-family:Georgia;}");

        stack=new QStackedWidget(this);
        setCentralWidget(stack);

        stack->addWidget(makeRegisterScreen());  // 0
        stack->addWidget(makeHomeScreen());       // 1
        stack->addWidget(makeGameScreen());       // 2
        stack->setCurrentIndex(0);
    }

private:
    QWidget* makeRegisterScreen(){
        auto* w=new QWidget();
        auto* vbox=new QVBoxLayout(w);
        vbox->setAlignment(Qt::AlignCenter);

        // Top sky
        auto* sky=new QWidget(); sky->setFixedHeight(100);
        sky->setStyleSheet("background:#0e0b04;");
        vbox->addWidget(sky);

        auto* card=new QWidget(); card->setFixedWidth(400);
        card->setStyleSheet("background:#2a1c0a;border:1px solid #8B6914;border-radius:12px;");
        auto* cl=new QVBoxLayout(card);
        cl->setContentsMargins(32,28,32,28); cl->setSpacing(14);

        auto* crown=new QLabel("♛"); crown->setAlignment(Qt::AlignCenter);
        crown->setStyleSheet("font-size:44px;color:#D4AF37;border:none;");
        auto* title=new QLabel("ROYAL CHESS"); title->setAlignment(Qt::AlignCenter);
        title->setStyleSheet("font-size:26px;font-weight:bold;color:#D4AF37;letter-spacing:5px;border:none;");
        auto* sub=new QLabel("Enter your name to begin"); sub->setAlignment(Qt::AlignCenter);
        sub->setStyleSheet("font-size:12px;color:#8B6914;border:none;");

        auto* nameInput=new QLineEdit();
        nameInput->setPlaceholderText("Your name...");
        nameInput->setFixedHeight(42);
        nameInput->setStyleSheet("QLineEdit{background:#160f05;color:#D4AF37;border:1px solid #8B6914;border-radius:6px;padding:0 12px;font-size:14px;font-family:Georgia;} QLineEdit:focus{border-color:#D4AF37;}");

        auto* enterBtn=new QPushButton("ENTER THE KINGDOM");
        enterBtn->setFixedHeight(46);
        enterBtn->setStyleSheet("QPushButton{background:#8B6914;color:#F5E6C8;border:2px solid #D4AF37;border-radius:8px;font-size:13px;font-family:Georgia;font-weight:bold;letter-spacing:2px;} QPushButton:hover{background:#a07c1a;}");

        auto* msg=new QLabel(""); msg->setAlignment(Qt::AlignCenter);
        msg->setStyleSheet("font-size:12px;color:#c66;border:none;"); msg->setFixedHeight(18);

        connect(enterBtn,&QPushButton::clicked,[=](){
            QString name=nameInput->text().trimmed();
            if(name.isEmpty()){ msg->setText("Please enter your name"); return; }
            playerName=name; playerElo=1200;
            if(playerNameLbl) playerNameLbl->setText(name);
            stack->setCurrentIndex(1);
        });
        connect(nameInput,&QLineEdit::returnPressed,enterBtn,&QPushButton::click);

        cl->addWidget(crown); cl->addWidget(title); cl->addWidget(sub);
        cl->addSpacing(8); cl->addWidget(nameInput); cl->addWidget(enterBtn); cl->addWidget(msg);
        vbox->addWidget(card,0,Qt::AlignHCenter); vbox->addStretch();
        return w;
    }

    QWidget* makeHomeScreen(){
        auto* w=new QWidget();
        auto* vbox=new QVBoxLayout(w);
        vbox->setContentsMargins(0,0,0,0); vbox->setSpacing(0);

        // Sky
        auto* sky=new QWidget(); sky->setFixedHeight(100);
        sky->setStyleSheet("background:#0e0b04;");
        vbox->addWidget(sky);

        // Scroll area for content
        auto* scroll=new QScrollArea(); scroll->setWidgetResizable(true);
        scroll->setStyleSheet("border:none;background:#1a1208;");
        auto* content=new QWidget(); content->setStyleSheet("background:#1a1208;");
        auto* cl=new QVBoxLayout(content);
        cl->setAlignment(Qt::AlignHCenter); cl->setSpacing(14); cl->setContentsMargins(24,16,24,24);

        // Header
        auto* crown=new QLabel("\u265b"); crown->setAlignment(Qt::AlignCenter);
        crown->setStyleSheet("font-size:36px;color:#D4AF37;");
        auto* title=new QLabel("ROYAL CHESS"); title->setAlignment(Qt::AlignCenter);
        title->setStyleSheet("font-size:30px;font-weight:bold;color:#D4AF37;letter-spacing:6px;");
        playerNameLbl=new QLabel(playerName); playerNameLbl->setAlignment(Qt::AlignCenter);
        playerNameLbl->setStyleSheet("font-size:14px;color:#D4A96A;");
        cl->addWidget(crown); cl->addWidget(title); cl->addWidget(playerNameLbl);

        // Tab bar
        auto* tabBar=new QWidget();
        tabBar->setStyleSheet("background:#1e1407;border:1px solid #8B6914;border-radius:8px;");
        tabBar->setFixedWidth(600);
        auto* tabRow=new QHBoxLayout(tabBar); tabRow->setContentsMargins(0,0,0,0); tabRow->setSpacing(0);
        auto* tabPlay=new QPushButton("PLAY"); auto* tabProfile=new QPushButton("PROFILE");
        auto* tabRanks=new QPushButton("RANKS"); auto* tabHistory=new QPushButton("HISTORY");
        QString tSel="QPushButton{background:#2a1c0a;color:#D4AF37;border:none;padding:8px 0;font-size:10px;font-family:Georgia;letter-spacing:2px;}";
        QString tNorm="QPushButton{background:transparent;color:#8B6914;border:none;padding:8px 0;font-size:10px;font-family:Georgia;letter-spacing:2px;}QPushButton:hover{color:#D4AF37;}";
        tabPlay->setStyleSheet(tSel); tabProfile->setStyleSheet(tNorm);
        tabRanks->setStyleSheet(tNorm); tabHistory->setStyleSheet(tNorm);
        tabRow->addWidget(tabPlay); tabRow->addWidget(tabProfile);
        tabRow->addWidget(tabRanks); tabRow->addWidget(tabHistory);
        cl->addWidget(tabBar,0,Qt::AlignHCenter);

        // Tab content
        homePages=new QStackedWidget(); homePages->setFixedWidth(600);
        homePages->setStyleSheet("background:transparent;border:none;");

        // ── Page 0: Play ──────────────────────────────────────────────────────
        auto* playPage=new QWidget(); playPage->setStyleSheet("background:transparent;");
        auto* playL=new QVBoxLayout(playPage); playL->setSpacing(12); playL->setContentsMargins(0,8,0,0);
        auto* playCard=new QWidget();
        playCard->setStyleSheet("background:#2a1c0a;border:1px solid #8B6914;border-radius:12px;");
        auto* pcl=new QVBoxLayout(playCard); pcl->setContentsMargins(24,20,24,20); pcl->setSpacing(14);

        auto* ct=new QLabel("CHALLENGE THE REALM"); ct->setAlignment(Qt::AlignCenter);
        ct->setStyleSheet("font-size:12px;color:#D4AF37;letter-spacing:2px;");

        // Color
        auto* colorRow=new QHBoxLayout();
        auto* colorLbl=new QLabel("YOUR ALLEGIANCE"); colorLbl->setStyleSheet("font-size:10px;color:#8B6914;");
        auto* whiteBtn=new QPushButton("WHITE"); whiteBtn->setCheckable(true); whiteBtn->setChecked(true);
        auto* blackBtn=new QPushButton("BLACK"); blackBtn->setCheckable(true);
        QString wb="QPushButton{background:#D4A96A;color:#1a1208;border:1px solid #5a3a10;border-radius:5px;padding:5px 14px;font-size:10px;font-family:Georgia;}QPushButton:checked{border-color:#D4AF37;}";
        QString bb="QPushButton{background:#1a1208;color:#D4A96A;border:1px solid #5a3a10;border-radius:5px;padding:5px 14px;font-size:10px;font-family:Georgia;}QPushButton:checked{border-color:#D4AF37;}";
        whiteBtn->setStyleSheet(wb); blackBtn->setStyleSheet(bb);
        connect(whiteBtn,&QPushButton::clicked,[=]{ whiteBtn->setChecked(true); blackBtn->setChecked(false); });
        connect(blackBtn,&QPushButton::clicked,[=]{ blackBtn->setChecked(true); whiteBtn->setChecked(false); });
        colorRow->addWidget(colorLbl); colorRow->addStretch(); colorRow->addWidget(whiteBtn); colorRow->addWidget(blackBtn);

        // Difficulty
        auto* diffRow=new QHBoxLayout();
        auto* diffLbl=new QLabel("ADVERSARY STRENGTH"); diffLbl->setStyleSheet("font-size:10px;color:#8B6914;");
        auto* easyBtn=new QPushButton("SQUIRE"); easyBtn->setCheckable(true);
        auto* medBtn=new QPushButton("KNIGHT"); medBtn->setCheckable(true); medBtn->setChecked(true);
        auto* hardBtn=new QPushButton("KING"); hardBtn->setCheckable(true);
        QString db="QPushButton{background:#1e1407;color:#8B6914;border:1px solid #3a2510;border-radius:5px;padding:5px 12px;font-size:10px;font-family:Georgia;}QPushButton:checked{background:#2a1c0a;color:#D4AF37;border-color:#D4AF37;}QPushButton:hover{border-color:#D4AF37;color:#D4AF37;}";
        easyBtn->setStyleSheet(db); medBtn->setStyleSheet(db); hardBtn->setStyleSheet(db);
        auto chkD=[=](QPushButton* c){ easyBtn->setChecked(false); medBtn->setChecked(false); hardBtn->setChecked(false); c->setChecked(true); };
        connect(easyBtn,&QPushButton::clicked,[=]{ chkD(easyBtn); });
        connect(medBtn, &QPushButton::clicked,[=]{ chkD(medBtn); });
        connect(hardBtn,&QPushButton::clicked,[=]{ chkD(hardBtn); });
        diffRow->addWidget(diffLbl); diffRow->addStretch(); diffRow->addWidget(easyBtn); diffRow->addWidget(medBtn); diffRow->addWidget(hardBtn);

        auto* playBtn=new QPushButton("ENTER BATTLE"); playBtn->setFixedHeight(50);
        playBtn->setStyleSheet("QPushButton{background:#8B6914;color:#F5E6C8;border:2px solid #D4AF37;border-radius:8px;font-size:15px;font-family:Georgia;font-weight:bold;letter-spacing:3px;}QPushButton:hover{background:#a07c1a;}");
        connect(playBtn,&QPushButton::clicked,[=](){
            Color pc=whiteBtn->isChecked()?Color::White:Color::Black;
            int depth=easyBtn->isChecked()?1:hardBtn->isChecked()?4:3;
            currentDifficulty=depth; currentColorInt=(pc==Color::White)?0:1;
            startGame(pc,depth);
        });

        pcl->addWidget(ct); pcl->addLayout(colorRow); pcl->addLayout(diffRow); pcl->addWidget(playBtn);
        playL->addWidget(playCard);
        homePages->addWidget(playPage);

        // ── Page 1: Profile ───────────────────────────────────────────────────
        profilePage=new QWidget(); profilePage->setStyleSheet("background:transparent;");
        buildProfilePage();
        homePages->addWidget(profilePage);

        // ── Page 2: Ranks ─────────────────────────────────────────────────────
        ranksPage=new QWidget(); ranksPage->setStyleSheet("background:transparent;");
        buildRanksPage();
        homePages->addWidget(ranksPage);

        // ── Page 3: History ───────────────────────────────────────────────────
        historyPage=new QWidget(); historyPage->setStyleSheet("background:transparent;");
        buildHistoryPage();
        homePages->addWidget(historyPage);

        // Tab switching
        auto switchTab=[=](int idx, QPushButton* active){
            homePages->setCurrentIndex(idx);
            for(auto* b:{tabPlay,tabProfile,tabRanks,tabHistory}) b->setStyleSheet(tNorm);
            active->setStyleSheet(tSel);
            if(idx==1) buildProfilePage();
            if(idx==2) buildRanksPage();
            if(idx==3) buildHistoryPage();
        };
        connect(tabPlay,   &QPushButton::clicked,[=]{ switchTab(0,tabPlay); });
        connect(tabProfile,&QPushButton::clicked,[=]{ switchTab(1,tabProfile); });
        connect(tabRanks,  &QPushButton::clicked,[=]{ switchTab(2,tabRanks); });
        connect(tabHistory,&QPushButton::clicked,[=]{ switchTab(3,tabHistory); });

        cl->addWidget(homePages,0,Qt::AlignHCenter);
        cl->addStretch();
        scroll->setWidget(content);
        vbox->addWidget(scroll,1);
        return w;
    }

    void buildProfilePage(){
        // Clear layout
        auto* l=profilePage->layout();
        if(l){ while(l->count()){ auto* i=l->takeAt(0); if(i->widget()) delete i->widget(); delete i; } delete l; }

        auto* vl=new QVBoxLayout(profilePage); vl->setSpacing(10); vl->setContentsMargins(0,8,0,0);
        auto& p=DataMgr::inst().current;
        bool li=DataMgr::inst().loggedIn;
        QString name=li?p.name:playerName;
        int elo=li?p.elo:1200;
        int wins=li?p.wins:0, losses=li?p.losses:0, draws=li?p.draws:0;

        // Avatar card
        auto* av=new QWidget(); av->setStyleSheet("background:#2a1c0a;border:1px solid #8B6914;border-radius:12px;");
        auto* avl=new QVBoxLayout(av); avl->setContentsMargins(20,20,20,20); avl->setSpacing(6); avl->setAlignment(Qt::AlignHCenter);
        auto* circle=new QLabel(name.isEmpty()?"?":QString(name[0]).toUpper()); circle->setFixedSize(68,68);
        circle->setAlignment(Qt::AlignCenter);
        circle->setStyleSheet("background:qlineargradient(x1:0,y1:0,x2:1,y2:1,stop:0 #D4AF37,stop:1 #8B6914);color:#1a1208;border-radius:34px;font-size:28px;font-weight:bold;border:3px solid #D4AF37;");
        auto* nm=new QLabel(name); nm->setAlignment(Qt::AlignCenter); nm->setStyleSheet("font-size:18px;color:#D4AF37;font-weight:bold;border:none;");
        auto* jn=new QLabel(li?"JOINED: "+p.joinDate:""); jn->setAlignment(Qt::AlignCenter); jn->setStyleSheet("font-size:9px;color:#8B6914;letter-spacing:2px;border:none;");
        avl->addWidget(circle,0,Qt::AlignHCenter); avl->addWidget(nm); avl->addWidget(jn);
        vl->addWidget(av);

        // Stats grid
        auto* grid=new QWidget(); auto* gl=new QHBoxLayout(grid); gl->setSpacing(10);
        auto mkStat=[](const QString& val,const QString& lbl,const QString& sub,const QString& sc)->QWidget*{
            auto* c=new QWidget(); c->setStyleSheet("background:#2a1c0a;border:1px solid #3a2510;border-radius:10px;");
            auto* cl=new QVBoxLayout(c); cl->setContentsMargins(12,12,12,12); cl->setSpacing(3); cl->setAlignment(Qt::AlignHCenter);
            auto* v=new QLabel(val); v->setAlignment(Qt::AlignCenter); v->setStyleSheet("font-size:26px;font-weight:bold;color:#D4AF37;border:none;");
            auto* l=new QLabel(lbl); l->setAlignment(Qt::AlignCenter); l->setStyleSheet("font-size:9px;letter-spacing:1px;color:#8B6914;border:none;");
            auto* s=new QLabel(sub); s->setAlignment(Qt::AlignCenter); s->setStyleSheet("font-size:10px;color:"+sc+";border:none;");
            cl->addWidget(v); cl->addWidget(l); cl->addWidget(s); return c;
        };
        int total=wins+losses+draws;
        QString wr=total>0?QString::number(wins*100.0/total,'f',1)+"% win rate":"No games yet";
        QString dr=draws>0?QString::number(draws)+" draws":"No draws yet";
        gl->addWidget(mkStat(QString::number(elo),"ELO RATING","","#8B6914"));
        gl->addWidget(mkStat(QString::number(total),"BATTLES FOUGHT","","#8B6914"));
        gl->addWidget(mkStat(QString::number(wins),"VICTORIES",wr,"#4a9"));
        gl->addWidget(mkStat(QString::number(losses),"DEFEATS",dr,"#c66"));
        vl->addWidget(grid);
    }

    void buildRanksPage(){
        auto* l=ranksPage->layout();
        if(l){ while(l->count()){ auto* i=l->takeAt(0); if(i->widget()) delete i->widget(); delete i; } delete l; }
        auto* vl=new QVBoxLayout(ranksPage); vl->setSpacing(8); vl->setContentsMargins(0,8,0,0);
        auto players=DataMgr::inst().loadAll();
        std::sort(players.begin(),players.end(),[](const PlayerProfile& a,const PlayerProfile& b){ return a.elo>b.elo; });
        if(players.isEmpty()){
            auto* e=new QLabel("No players yet"); e->setAlignment(Qt::AlignCenter); e->setStyleSheet("color:#8B6914;font-size:14px;");
            vl->addWidget(e);
        }
        int rank=1;
        QString myName=DataMgr::inst().loggedIn?DataMgr::inst().current.name:playerName;
        for(auto& p:players){
            bool isMe=p.name.toLower()==myName.toLower();
            auto* row=new QWidget();
            row->setStyleSheet(isMe?"background:#2a1c0a;border:1px solid #D4AF37;border-radius:8px;":"background:#2a1c0a;border:1px solid #3a2510;border-radius:8px;");
            auto* rl=new QHBoxLayout(row); rl->setContentsMargins(14,10,14,10); rl->setSpacing(12);
            static const QString medals[]={"①","②","③"};
            static const QString mcolors[]={"#D4AF37","#C0C0C0","#CD7F32"};
            auto* rankLbl=new QLabel(rank<=3?medals[rank-1]:QString::number(rank));
            rankLbl->setFixedWidth(28); rankLbl->setStyleSheet("font-size:18px;color:"+(rank<=3?mcolors[rank-1]:QString("#5a3a10"))+";border:none;");
            auto* av=new QLabel(QString(p.name[0]).toUpper()); av->setFixedSize(36,36); av->setAlignment(Qt::AlignCenter);
            av->setStyleSheet("background:#8B6914;color:#1a1208;border-radius:18px;font-size:14px;font-weight:bold;border:none;");
            auto* info=new QVBoxLayout(); info->setSpacing(1);
            auto* nm=new QLabel(p.name+(isMe?" (YOU)":"")); nm->setStyleSheet("font-size:13px;color:#D4AF37;border:none;");
            auto* tl=new QLabel(p.title()); tl->setStyleSheet("font-size:9px;color:#8B6914;letter-spacing:1px;border:none;");
            info->addWidget(nm); info->addWidget(tl);
            auto* eloLbl=new QLabel(QString::number(p.elo)); eloLbl->setStyleSheet("font-size:16px;color:#D4AF37;font-weight:bold;border:none;");
            rl->addWidget(rankLbl); rl->addWidget(av); rl->addLayout(info,1); rl->addWidget(eloLbl);
            vl->addWidget(row); ++rank;
        }
        vl->addStretch();
    }

    void buildHistoryPage(){
        auto* l=historyPage->layout();
        if(l){ while(l->count()){ auto* i=l->takeAt(0); if(i->widget()) delete i->widget(); delete i; } delete l; }
        auto* vl=new QVBoxLayout(historyPage); vl->setSpacing(8); vl->setContentsMargins(0,8,0,0);
        auto& hist=DataMgr::inst().current.history;
        if(!DataMgr::inst().loggedIn||hist.isEmpty()){
            auto* e=new QLabel("No battles fought yet. Click PLAY to start your first game!"); e->setAlignment(Qt::AlignCenter);
            e->setStyleSheet("color:#8B6914;font-size:13px;"); vl->addWidget(e);
        } else {
            for(auto& m:hist){
                auto* row=new QWidget(); row->setStyleSheet("background:#2a1c0a;border:1px solid #3a2510;border-radius:8px;");
                auto* rl=new QHBoxLayout(row); rl->setContentsMargins(14,10,14,10); rl->setSpacing(12);
                QString bc=m.result=="WIN"?"background:#1a3a10;color:#5a9;border:1px solid #2a5a1a;":
                           m.result=="LOSS"?"background:#3a1010;color:#c66;border:1px solid #5a1a1a;":
                           "background:#2a2510;color:#aa8;border:1px solid #4a4010;";
                auto* badge=new QLabel(m.result); badge->setFixedSize(52,28); badge->setAlignment(Qt::AlignCenter);
                badge->setStyleSheet("font-size:10px;font-weight:bold;border-radius:4px;"+bc);
                auto* info=new QVBoxLayout(); info->setSpacing(2);
                auto* opp=new QLabel(m.opponent); opp->setStyleSheet("font-size:12px;color:#D4AF37;border:none;");
                auto* meta=new QLabel(m.date+" · "+m.playerColor+" · "+m.timeControl); meta->setStyleSheet("font-size:9px;color:#8B6914;letter-spacing:1px;border:none;");
                info->addWidget(opp); info->addWidget(meta);
                QString ec=m.eloChange>0?"▲ +"+QString::number(m.eloChange)+" ELO":m.eloChange<0?"▼ "+QString::number(m.eloChange)+" ELO":"— 0 ELO";
                QString ecol=m.eloChange>0?"#4a9":m.eloChange<0?"#c66":"#aa8";
                auto* eloChg=new QLabel(ec); eloChg->setStyleSheet("font-size:10px;color:"+ecol+";border:none;");
                rl->addWidget(badge); rl->addLayout(info,1); rl->addWidget(eloChg);
                vl->addWidget(row);
            }
        }
        vl->addStretch();
    }

    void refreshHomeData(){
        buildProfilePage(); buildRanksPage(); buildHistoryPage();
        if(playerNameLbl) playerNameLbl->setText(DataMgr::inst().loggedIn?DataMgr::inst().current.name:playerName);
    }


    QString formatTime(int secs){
        int m=secs/60, s=secs%60;
        return QString("%1:%2").arg(m,2,10,QChar('0')).arg(s,2,10,QChar('0'));
    }

    void startClocks(int secs){
        playerSecs=secs; aiSecs=secs; moveTimings.clear(); moveStartSecs=0;

        // Player clock
        if(!playerClockTimer){ playerClockTimer=new QTimer(this); playerClockTimer->setInterval(1000); }
        connect(playerClockTimer,&QTimer::timeout,[this](){
            if(playerSecs<=0){ playerClockTimer->stop(); return; }
            --playerSecs;
            if(playerClockLbl) playerClockLbl->setText(formatTime(playerSecs));
            // Red when low
            if(playerClockLbl) playerClockLbl->setStyleSheet(playerSecs<=30?
                "font-size:20px;font-weight:bold;color:#ff4444;font-family:'Courier New';background:#2a0808;border:1px solid #8B2020;border-radius:6px;padding:4px 10px;":
                "font-size:20px;font-weight:bold;color:#D4AF37;font-family:'Courier New';background:#0e0b04;border:1px solid #5a3a10;border-radius:6px;padding:4px 10px;");
        });

        // AI clock
        if(!aiClockTimer){ aiClockTimer=new QTimer(this); aiClockTimer->setInterval(1000); }
        connect(aiClockTimer,&QTimer::timeout,[this](){
            if(aiSecs<=0){ aiClockTimer->stop(); return; }
            --aiSecs;
            if(aiClockLbl) aiClockLbl->setText(formatTime(aiSecs));
            if(aiClockLbl) aiClockLbl->setStyleSheet(aiSecs<=30?
                "font-size:20px;font-weight:bold;color:#ff4444;font-family:'Courier New';background:#2a0808;border:1px solid #8B2020;border-radius:6px;padding:4px 10px;":
                "font-size:20px;font-weight:bold;color:#D4AF37;font-family:'Courier New';background:#0e0b04;border:1px solid #5a3a10;border-radius:6px;padding:4px 10px;");
        });

        // Move timer
        if(!moveTimer){ moveTimer=new QTimer(this); moveTimer->setInterval(1000); }
        connect(moveTimer,&QTimer::timeout,[this](){
            ++moveStartSecs;
            if(moveLbl) moveLbl->setText(QString("Move time: %1s").arg(moveStartSecs));
        });

        // Start player clock if white, ai clock if black
        if(board->playerColor==Color::White) playerClockTimer->start();
        else aiClockTimer->start();
        moveTimer->start();
    }

    void stopAllClocks(){
        if(playerClockTimer) playerClockTimer->stop();
        if(aiClockTimer) aiClockTimer->stop();
        if(moveTimer) moveTimer->stop();
    }

    void switchClocks(){
        // Record move time
        moveTimings.append(moveStartSecs);
        moveStartSecs=0;
        if(moveLbl) moveLbl->setText("Move time: 0s");

        // Switch which clock is running
        if(board->board.turn==board->playerColor){
            // Now player's turn
            if(aiClockTimer) aiClockTimer->stop();
            if(playerClockTimer) playerClockTimer->start();
        } else {
            // Now AI's turn
            if(playerClockTimer) playerClockTimer->stop();
            if(aiClockTimer) aiClockTimer->start();
        }
        if(moveTimer){ moveTimer->stop(); moveTimer->start(); }
    }

    QWidget* makeGameScreen(){
        auto* w=new QWidget();
        auto* vbox=new QVBoxLayout(w);
        vbox->setContentsMargins(12,8,12,8); vbox->setSpacing(6);

        // Top bar
        auto* topBar=new QHBoxLayout();
        auto* backBtn=new QPushButton("<- Hall");
        backBtn->setFixedSize(80,28);
        backBtn->setStyleSheet("QPushButton{background:#2a1c0a;color:#D4AF37;border:1px solid #8B6914;border-radius:5px;font-size:11px;} QPushButton:hover{border-color:#D4AF37;}");
        connect(backBtn,&QPushButton::clicked,[this](){
            int moves=(int)board->board.history.size();
            if(board->gameActive && moves >= 2){
                QString oppName=currentDifficulty<=1?"Squire Bot":currentDifficulty<=3?"Knight AI":"King AI";
                int oppElo=currentDifficulty<=1?1000:currentDifficulty<=3?1400:1800;
                // Force ensure we have a valid profile
                if(!DataMgr::inst().loggedIn && !playerName.isEmpty()){
                    DataMgr::inst().current.name=playerName;
                    DataMgr::inst().current.elo=1200;
                    DataMgr::inst().current.joinDate=QDateTime::currentDateTime().toString("MMM yyyy").toUpper();
                    DataMgr::inst().loggedIn=true;
                    auto players=DataMgr::inst().loadAll();
                    bool found=false;
                    for(auto& p:players) if(p.name.toLower()==playerName.toLower()){ found=true; break; }
                    if(!found){ players.append(DataMgr::inst().current); DataMgr::inst().saveAll(players); }
                }
                DataMgr::inst().saveMatch("LOSS",oppName,oppElo,moves,
                    board->playerColor==Color::White?"WHITE":"BLACK","10 min");
            }
            board->stopGame();
            stopAllClocks();
            refreshHomeData();
            stack->setCurrentIndex(1);
        });

        statusLbl=new QLabel("White's Turn");
        statusLbl->setAlignment(Qt::AlignCenter);
        statusLbl->setStyleSheet("font-size:13px;color:#D4AF37;letter-spacing:2px;");

        auto* undoBtn=new QPushButton("Undo");
        undoBtn->setFixedSize(70,28);
        undoBtn->setStyleSheet("QPushButton{background:#2a1c0a;color:#D4AF37;border:1px solid #8B6914;border-radius:5px;font-size:11px;} QPushButton:hover{border-color:#D4AF37;}");
        connect(undoBtn,&QPushButton::clicked,[this](){
            if(board->board.history.size()>=2){
                board->board.undo(board->board.history.back());
                board->board.undo(board->board.history.back());
                board->selected={}; board->hints.clear(); board->update();
            }
        });

        topBar->addWidget(backBtn); topBar->addStretch();
        topBar->addWidget(statusLbl); topBar->addStretch(); topBar->addWidget(undoBtn);

        // ── Clock bar ─────────────────────────────────────────────────────────
        auto* clockBar=new QHBoxLayout();
        clockBar->setSpacing(12);

        // AI clock (top)
        auto* aiClockBox=new QWidget();
        aiClockBox->setStyleSheet("background:#2a1c0a;border:1px solid #3a2510;border-radius:8px;");
        auto* aiClockL=new QHBoxLayout(aiClockBox); aiClockL->setContentsMargins(12,6,12,6);
        auto* aiLbl=new QLabel("AI"); aiLbl->setStyleSheet("font-size:11px;color:#8B6914;letter-spacing:1px;");
        aiClockLbl=new QLabel("10:00");
        aiClockLbl->setStyleSheet("font-size:20px;font-weight:bold;color:#D4AF37;font-family:'Courier New';background:#0e0b04;border:1px solid #5a3a10;border-radius:6px;padding:4px 10px;");
        aiClockL->addWidget(aiLbl); aiClockL->addStretch(); aiClockL->addWidget(aiClockLbl);

        // Move time (center)
        moveLbl=new QLabel("Move time: 0s");
        moveLbl->setAlignment(Qt::AlignCenter);
        moveLbl->setStyleSheet("font-size:11px;color:#8B6914;letter-spacing:1px;");

        // Player clock (bottom)
        auto* playerClockBox=new QWidget();
        playerClockBox->setStyleSheet("background:#2a1c0a;border:1px solid #D4AF37;border-radius:8px;");
        auto* playerClockL=new QHBoxLayout(playerClockBox); playerClockL->setContentsMargins(12,6,12,6);
        auto* playerLbl=new QLabel("YOU"); playerLbl->setStyleSheet("font-size:11px;color:#D4AF37;letter-spacing:1px;");
        playerClockLbl=new QLabel("10:00");
        playerClockLbl->setStyleSheet("font-size:20px;font-weight:bold;color:#D4AF37;font-family:'Courier New';background:#0e0b04;border:1px solid #5a3a10;border-radius:6px;padding:4px 10px;");
        playerClockL->addWidget(playerLbl); playerClockL->addStretch(); playerClockL->addWidget(playerClockLbl);

        clockBar->addWidget(aiClockBox,1);
        clockBar->addWidget(moveLbl,0,Qt::AlignCenter);
        clockBar->addWidget(playerClockBox,1);

        // Board
        board=new BoardWidget();
        board->onEvent=[this](const QString& ev){
            if(ev.startsWith("checkmate")){
                QString winner=ev.mid(10);
                statusLbl->setText("Checkmate! " + winner + " wins!");
                QTimer::singleShot(300,[this,winner]{ QMessageBox::information(this,"Game Over","Checkmate! " + winner + " wins!"); });
            } else if(ev=="stalemate"){
                statusLbl->setText("Stalemate - Draw!");
            } else if(ev=="check"){
                QString who=(board->board.turn==Color::White)?"White":"Black";
                statusLbl->setText(who + " is in check!");
            }
        };

        // Use a timer to update status label safely
        auto* timer=new QTimer(this);
        timer->setInterval(100);
        connect(timer,&QTimer::timeout,[this](){
            if(!board->gameActive) return;
            QString who=(board->board.turn==Color::White)?"White":"Black";
            bool myTurn=(board->board.turn==board->playerColor);
            if(myTurn) statusLbl->setText(who + "'s Turn (Your Move)");
            else statusLbl->setText(who + "'s Turn (AI Thinking...)");
        });
        timer->start();

        vbox->addLayout(topBar);
        vbox->addLayout(clockBar);
        vbox->addWidget(board,1);
        return w;
    }

    void startGame(Color pc, int depth){
        stack->setCurrentIndex(2);
        movesPlayed=0;
        stopAllClocks();
        // Reset clock displays
        if(playerClockLbl){ playerClockLbl->setText(formatTime(gameTimeSecs)); playerClockLbl->setStyleSheet("font-size:20px;font-weight:bold;color:#D4AF37;font-family:'Courier New';background:#0e0b04;border:1px solid #5a3a10;border-radius:6px;padding:4px 10px;"); }
        if(aiClockLbl){ aiClockLbl->setText(formatTime(gameTimeSecs)); aiClockLbl->setStyleSheet("font-size:20px;font-weight:bold;color:#D4AF37;font-family:'Courier New';background:#0e0b04;border:1px solid #5a3a10;border-radius:6px;padding:4px 10px;"); }
        if(moveLbl) moveLbl->setText("Move time: 0s");
        board->startGame(pc,depth);
        // Override board onEvent to also save results
        board->onEvent=[this](const QString& ev){
            movesPlayed=(int)board->board.history.size();
            // Ensure logged in before saving
            auto ensureLogin=[this](){
                if(!DataMgr::inst().loggedIn && !playerName.isEmpty()){
                    DataMgr::inst().current.name=playerName;
                    DataMgr::inst().current.elo=playerElo>0?playerElo:1200;
                    DataMgr::inst().current.joinDate=QDateTime::currentDateTime().toString("MMM yyyy").toUpper();
                    DataMgr::inst().loggedIn=true;
                    auto players=DataMgr::inst().loadAll();
                    bool found=false;
                    for(auto& p:players) if(p.name.toLower()==playerName.toLower()){ p=DataMgr::inst().current; found=true; break; }
                    if(!found) players.append(DataMgr::inst().current);
                    DataMgr::inst().saveAll(players);
                }
            };
            if(ev.startsWith("checkmate")){
                QString winner=ev.mid(10);
                bool playerWon=(winner=="White"&&board->playerColor==Color::White)||
                               (winner=="Black"&&board->playerColor==Color::Black);
                QString result=playerWon?"WIN":"LOSS";
                QString oppName=currentDifficulty<=1?"Squire Bot":currentDifficulty<=3?"Knight AI":"King AI";
                int oppElo=currentDifficulty<=1?1000:currentDifficulty<=3?1400:1800;
                ensureLogin();
                DataMgr::inst().saveMatch(result,oppName,oppElo,movesPlayed,
                    board->playerColor==Color::White?"WHITE":"BLACK","10 min");
                playerElo=DataMgr::inst().current.elo;
                refreshHomeData();
                statusLbl->setText("Checkmate! " + winner + " wins!");
                QTimer::singleShot(300,[this,winner]{ QMessageBox::information(this,"Game Over","Checkmate! " + winner + " wins!"); });
            } else if(ev=="stalemate"){
                QString oppName=currentDifficulty<=1?"Squire Bot":currentDifficulty<=3?"Knight AI":"King AI";
                int oppElo=currentDifficulty<=1?1000:currentDifficulty<=3?1400:1800;
                ensureLogin();
                DataMgr::inst().saveMatch("DRAW",oppName,oppElo,movesPlayed,
                    board->playerColor==Color::White?"WHITE":"BLACK","10 min");
                refreshHomeData();
                statusLbl->setText("Stalemate - Draw!");
                QTimer::singleShot(300,[this]{ QMessageBox::information(this,"Draw","Stalemate!"); });
            } else if(ev=="check"){
                QString who=(board->board.turn==Color::White)?"White":"Black";
                statusLbl->setText(who + " is in check!");
            }
        };
        QString who=(pc==Color::White)?"White":"Black";
        statusLbl->setText("You play " + who + " - Good luck!");
        startClocks(gameTimeSecs);

        // Switch clocks when a move is made
        // Hook into board's move via periodic check
        auto* clockSwitcher=new QTimer(this);
        clockSwitcher->setInterval(200);
        int lastMoveCount=0;
        connect(clockSwitcher,&QTimer::timeout,[this,clockSwitcher,lastMoveCount]() mutable {
            if(!board->gameActive){ clockSwitcher->stop(); return; }
            int cur=(int)board->board.history.size();
            if(cur!=lastMoveCount){ lastMoveCount=cur; switchClocks(); }
        });
        clockSwitcher->start();
    }
};

#include "main.moc"

int main(int argc, char* argv[]){
    QApplication app(argc,argv);
    app.setApplicationName("Royal Chess");
    MainWindow w;
    w.show();
    return app.exec();
}
