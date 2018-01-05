#include "SoccerArea.h"
#include <iostream>
#include<fstream>
#include<cstdio>
#include<cmath>
#include<string>
#include<algorithm>
#include<vector>
#include<climits>
#include<float.h>
#include<string.h>
#include<stdint.h>
#include <boost/cstdint.hpp>
#include <QPen>
#include <unistd.h>
using namespace std;

/// begin scram

#define MMDR_DYNA 1
#define MMDR_N5 2
#define MMDR_N4 3
#define MMD_MSD2 4

// options for simulation

#define REPETITIONS 100
//#define ALGORITHM MMDR_DYNA
//#define ALGORITHM MMDR_N5
#define ALGORITHM MMDR_N4
//#define ALGORITHM MMD_MSD2
#define N 100

#define MAXN N

#if ALGORITHM == MMDR_DYNA
#define SOLVER mmdr_dyna
#elif ALGORITHM == MMDR_N5
#define SOLVER mmdr_n5
#elif ALGORITHM == MMDR_N4
#define SOLVER mmdr_n4
#elif ALGORITHM == MMD_MSD2
#define SOLVER mmd_msd2
#endif                          // ALGORITHM

#define SHORTDIST 1
#define NEARPOS 2
#define REASSIGN 3

//-------------------------------------------------------------
//下のからアルゴリズムを選択
//コメントアウトしていないものが実行される
//#define BARALGORITHM SHORTDIST        //手法1
//#define BARALGORITHM NEARPOS          //手法3
#define BARALGORITHM REASSIGN   //手法2
//-------------------------------------------------------------

#if BARALGORITHM == SHORTDIST
#define BAR shortdist
#elif BARALGORITHM == NEARPOS
#define BAR nearpos
#elif BARALGORITHM == REASSIGN
#define BAR reassign
#endif

#include<iostream>
#include<fstream>
#include<cstdio>
#include<cmath>
#include<string>
#include<algorithm>
#include<vector>
#include<climits>
#include<float.h>
#include<string.h>

#include <boost/cstdint.hpp>

typedef uint64_t uint64;

// remove an element from a vector by value.
#define VECREMOVE(vec, v) (vec).erase(  \
    std::remove((vec).begin(), (vec).end(), (v)), (vec).end())

typedef std::pair < double, double >Point;

// Edge looks like (dist, (left node, right node))
typedef std::pair < double, std::pair < int, int >>Edge;

struct Test {
    std::vector < Point > starts;
    std::vector < Point > targets;
};

inline double getdist(const Point & a, const Point & b)
{
    return hypot(a.first - b.first, a.second - b.second);
}

inline bool edgeVectorLessThan(const std::vector < Edge > &a, const std::vector < Edge > &b)
{
    const double ERROR_THRESH = .00005;
    for (unsigned int i = 0; i < a.size(); i++) {
        if (std::abs(a[i].first - b[i].first) < ERROR_THRESH) {
            continue;
        }
        return a[i] < b[i];
    }
    return false;
}

//std::vector<Test> tests;
Test t_org;                     //現在の情報(目的地、ロボットの位置)

bool flag = false;              //初期割り当てが完了したかの判定用
std::vector < Edge > an;        //目的地へのロボットの割り当てを格納する(インデックスのみ)

double move_perx[N];
double move_pery[N];            //ロボットの1ステップあたりの移動量　x+y≒1 double型を使用するため桁落ちあり

double move_posx[N];
double move_posy[N];            //ロボットの現在位置xとy

int distcnt[N];                 //距離(移動完了までの時間)
#define DEFFER 0                //初期状態でのロボット-目的地数 df=10
#define DISTCHECK 0
#define c_grid_num 64

Test ttmp;                      //初期の状態を保存する
std::vector < Point > breakdown;
std::vector < int >no_assign_pos;       //ロボットの崩壊による未割り当ての目的地
int loopcount = 0;
std::vector < int >replaceagent;        //未割り当てのロボットの位置情報へのインデックス
int agn = N;                    //行動可能なロボットの数
int deffer = DEFFER;            //ロボット-目的地の数
int cnt;
std::vector < int >arrival;     //到着したロボットのを格納

FILE *fp;                       //結果を書き込むための宣言

double movedist;                //書き込み用
int step;                       //書き込み用

int randomcount = 2;            //ループの開始2
int loopend = 22;               //ループの終わり50

std::vector < std::vector < Point > >median;

int geo = 1000;                 //ウィンドウの大きさを決める

char grid[c_grid_num][c_grid_num];

clock_t start, end;

////////////  Begin implementation of getMinimalMaxEdgeInPerfectMatching  ////////////////

#if ALGORITHM == MMDR_N4 || ALGORITHM == MMD_MSD2

// We consider a bipartite graph with n nodes on the left and right.

// Global variables used in the floodfill.
// foo[0][i] corresponds to i'th node on left; foo[1][i] for the right.

std::vector < std::vector < int >>out[2];       //adjacency list for each node
std::vector < bool > visited[2];        //reached in floodfill
std::vector < int >back[2];     //way to reach it
std::vector < int >used;        //whether a left node is used
//right nodes are used if and only if out[1][j].size() == 1.

// Floodfill from a node.
//  x in {0, 1}: left or right side
//  y in {0, ..., n-1}: node on side x
//  prev in {-1, 0, ..., n-1}: node on side 1-x that we came in on
//                             (-1 for unassigned node on left)
// Returns:
//  If it reaches an unassigned right node, the index of this node.
//  Otherwise, -1.
int flood(int x, int y, int prev)
{
    visited[x][y] = 1;
    back[x][y] = prev;
    if (x == 1 && out[x][y].size() == 0)        //reached an unassigned right node!
        return y;

    for (unsigned int j = 0; j < out[x][y].size(); j++) {
        if (!visited[1 - x][out[x][y][j]]) {
            int tmp = flood(1 - x, out[x][y][j], y);
            if (tmp != -1)      //Flood reached the end
                return tmp;
        }
    }
    return -1;
}

//            painter->drawRect(d1_x, d1_y, len, len);
//            painter->drawRect(d2_x, d2_y, len, len);

// starting at node (x, y), follow the back pointers and reverse each edge.
// Return the last node reached (i.e., the newly assigned left node)
inline int reverse(int x, int y)
{
    while (true) {
        int prev = back[x][y];
        if (prev == -1)         // Reached the unassigned node on the left
            break;
        out[x][y].push_back(prev);
        VECREMOVE(out[1 - x][prev], y);
        x = 1 - x;
        y = prev;
    }
    return y;
}

// Set visited to 0 and flood from unassigned left nodes.
inline void reset_flooding(int n)
{
    for (int i = 0; i < 2; i++)
        std::fill(visited[i].begin(), visited[i].end(), 0);

    for (int i = 0; i < n; i++)
        if (!used[i])
            flood(0, i, -1);
}

/*
  Add edges in order until k nodes can be matched.

  edges is a sorted vector of (dist, (left, right))

  Returns the index of the last edge added; this edge must appear.
 */
int getMinimalMaxEdgeInPerfectMatching(std::vector < Edge > edges, int n, int k)
{
    for (int i = 0; i < 2; i++) {       //Clear the graph
        out[i].clear();
        out[i].resize(n);
    }
    std::fill(used.begin(), used.end(), 0);
    reset_flooding(n);

    int answer;
    for (answer = 0; answer < edges.size(); answer++) {
        std::pair < int, int >e = edges[answer].second; //startsとtargetsのインデックスの組が入る
        out[0][e.first].push_back(e.second);    //初期値と目的地を関連付け
        //printf("Added edge: %d %d\n", e.first, e.second);
        if (visited[0][e.first] && !visited[1][e.second]) {
            int ans = flood(1, e.second, e.first);
            if (ans != -1) {    //We made it to the end!
                if (--k == 0)
                    break;
                int start = reverse(1, ans);
                used[start] = 1;
                reset_flooding(n);
            }
        }
    }
    // We must use edges[answer] to push k flow with minimal max edge.
    return answer;
}

#endif                          // ALGORITHM == MMDR_N4 || ALGORITHM == MMD_MSD2

////////////  End implementation of getMinimalMaxEdgeInPerfectMatching  ////////////////

////////////  Begin implementation of mmdr_n4  ////////////////

#if ALGORITHM == MMDR_N4

// Begin implementation of hungarian with integer weights solution  ////////

// Code for O(n^3) Hungarian algorithm from http://community.topcoder.com/tc?module=Static&d1=tutorials&d2=hungarianAlgorithm

//#define N 55             //max number of vertices in one part
#define INF DBL_MAX             //just infinity

int cost_int[N][N];             //cost matrix

int n_int, max_match_int;       //n workers and n jobs

int lx_int[N], ly_int[N];       //labels of X and Y parts
int xy_int[N];                  //xy[x] - vertex that is matched with x,
int yx_int[N];                  //yx[y] - vertex that is matched with y
bool S_int[N], T_int[N];        //sets S and T in algorithm
int slack_int[N];               //as in the algorithm description
int slackx_int[N];              //slackx[y] such a vertex, that
// l(slackx[y]) + l(y) - w(slackx[y],y) = slack[y]
int prev_int[N];                //array for memorizing alternating paths

void init_labels_int()
{
    memset(lx_int, 0, sizeof(lx_int));
    memset(ly_int, 0, sizeof(ly_int));
    for (int x = 0; x < n_int; x++)
        for (int y = 0; y < n_int; y++)
            lx_int[x] = std::max(lx_int[x], cost_int[x][y]);
}

void update_labels_int()
{
    int x, y;
    int delta = INT_MAX;        //init delta as infinity
    for (y = 0; y < n_int; y++) //calculate delta using slack
        if (!T_int[y])
            delta = std::min(delta, slack_int[y]);
    for (x = 0; x < n_int; x++) //update X labels
        if (S_int[x])
            lx_int[x] -= delta;
    for (y = 0; y < n_int; y++) //update Y labels
        if (T_int[y])
            ly_int[y] += delta;
    for (y = 0; y < n_int; y++) //update slack_int array
        if (!T_int[y])
            slack_int[y] -= delta;
}

void add_to_tree_int(int x, int prevx)
//x - current vertex,prevx - vertex from X before x in the alternating path,
//so we add edges (prevx, xy[x]), (xy[x], x)
{
    S_int[x] = true;            //add x to S
    prev_int[x] = prevx;        //we need this when augmenting
    for (int y = 0; y < n_int; y++)     //update slacks, because we add new vertex to S
        if (lx_int[x] + ly_int[y] - cost_int[x][y] < slack_int[y]) {
            slack_int[y] = lx_int[x] + ly_int[y] - cost_int[x][y];
            slackx_int[y] = x;
        }
}

bool augment_int()              //main function of the algorithm
{
    if (max_match_int == n_int)
        return true;            //check wether matching is already perfect
    int x, y, root;             //just counters and root vertex
    int q[agn], wr = 0, rd = 0; //q - queue for bfs, wr,rd - write and read
    //pos in queue
    memset(S_int, false, sizeof(S_int));        //init set S
    memset(T_int, false, sizeof(T_int));        //init set T
    memset(prev_int, -1, sizeof(prev_int));     //init set prev - for the alternating tree
    for (x = 0; x < n_int; x++) //finding root of the tree
        if (xy_int[x] == -1) {
            q[wr++] = root = x;
            prev_int[x] = -2;
            S_int[x] = true;
            break;
        }

    for (y = 0; y < n_int; y++) //initializing slack array
    {
        slack_int[y] = lx_int[root] + ly_int[y] - cost_int[root][y];
        slackx_int[y] = root;
    }

    //second part of augment_int() function
    while (true)                //main cycle
    {
        while (rd < wr)         //building tree with bfs cycle
        {
            x = q[rd++];        //current vertex from X part
            for (y = 0; y < n_int; y++) //iterate through all edges in equality graph
                if (cost_int[x][y] == lx_int[x] + ly_int[y] && !T_int[y]) {
                    if (yx_int[y] == -1)
                        break;  //an exposed vertex in Y found, so
                    //augmenting path exists!
                    T_int[y] = true;    //else just add y to T,
                    q[wr++] = yx_int[y];        //add vertex yx[y], which is matched
                    //with y, to the queue
                    add_to_tree_int(yx_int[y], x);      //add edges (x,y) and (y,y
                }
            if (y < n_int)
                break;          //augmenting path found!
        }
        if (y < n_int)
            break;              //augmenting path found!

        update_labels_int();    //augmenting path not found, so improve labeling
        wr = rd = 0;
        for (y = 0; y < n_int; y++)
            //in this cycle we add edges that were added to the equality graph as a
            //result of improving the labeling, we add edge (slackx[y], y) to the tree if
            //and only if !T[y] &&  slack_int[y] == 0, also with this edge we add another one
            //(y, yx[y]) or augment the matching, if y was exposed
            if (!T_int[y] && slack_int[y] == 0) {
                if (yx_int[y] == -1)    //exposed vertex in Y found - augmenting path exists!
                {
                    x = slackx_int[y];
                    break;
                } else {
                    T_int[y] = true;    //else just add y to T,
                    if (!S_int[yx_int[y]]) {
                        q[wr++] = yx_int[y];    //add vertex yx[y], which is matched with
                        //y, to the queue
                        add_to_tree_int(yx_int[y], slackx_int[y]);      //and add edges (x,y) and (y,
                        //yx[y]) to the tree
                    }
                }
            }
        if (y < n_int)
            break;              //augmenting path found!
    }

    if (y < n_int)              //we found augmenting path!
    {
        max_match_int++;        //increment matching
        //in this cycle we inverse edges along augmenting path
        for (int cx = x, cy = y, ty; cx != -2; cx = prev_int[cx], cy = ty) {
            ty = xy_int[cx];
            yx_int[cy] = cx;
            xy_int[cx] = cy;
        }
        //augment3();                                                      //recall function, go to step 1 of the algorithm
        return false;
    }
    return true;
}                               //end of augment3() function

int hungarian_int()
{
    int ret = 0;                //weight of the optimal matching
    n_int = agn;
    max_match_int = 0;          //number of vertices in current matching
    memset(xy_int, -1, sizeof(xy_int));
    memset(yx_int, -1, sizeof(yx_int));

    init_labels_int();          //step 0
    while (!augment_int()) {;
    }                           //steps 1-3
    for (int x = 0; x < n_int; x++)     //forming answer there
        ret += cost_int[x][xy_int[x]];
    return ret;
}

std::vector < Edge > mmdr_n4(Test t)
{
    int n = t.starts.size();
    int nt = t.targets.size();
    std::vector < Edge > edges, edges_tmp;
    std::vector < Edge > answer;

    //memset(cost_int, 0, sizeof(cost_int));
    for (int i = 0; i < n; i++) {
        for (int j = 0; j < nt; j++) {
            cost_int[i][j] = 0;
        }
    }

    memset(xy_int, -1, sizeof(xy_int));
    memset(yx_int, -1, sizeof(yx_int));
    memset(lx_int, 0, sizeof(lx_int));
    memset(ly_int, 0, sizeof(ly_int));
    memset(slack_int, 0, sizeof(slack_int));
    memset(slackx_int, 0, sizeof(slackx_int));
    memset(prev_int, 0, sizeof(prev_int));
    memset(S_int, false, sizeof(S_int));
    memset(T_int, false, sizeof(T_int));
    for (int i = 0; i < 2; i++) {       //Clear the graph
        visited[i].clear();
        back[i].clear();
    }
    used.clear();

    // Create edges from all pairwise distances
    for (int i = 0; i < n; i++)
        for (int j = 0; j < n; j++) {
            if (j < nt) {       //変更点 目的地のほうが少ないためダミーの目的地を生成させる
                edges.push_back(std::make_pair(getdist(t.starts[i], t.targets[j]), std::make_pair(i, j)));
                //printf("edge%d,st(%0.f,%0.f),ta(%0.f,%0.f)\n",i*n+j,t.starts[i].first,t.starts[i].second,t.targets[j].first,t.targets[j].second);
            } else {
                edges.push_back(std::make_pair(DISTCHECK, std::make_pair(i, j)));
                //printf("edge%d,st(%0.f,%0.f),ta(%0.f,%0.f)\n",i*n+j,t.starts[i].first,t.starts[i].second,t.starts[i].first,t.starts[i].second);
            }
        }

    // Make the global variables in the floodfill have the right sizes
    for (int i = 0; i < 2; i++) {
        visited[i].resize(n);
        back[i].resize(n);
    }
    used.resize(n);

    int k = n;

    // Initialize all costs to large value
    // Don't use memset as memory might not be contiguous
    //memset(cost_int, -(n+1), sizeof(cost_int));
    for (int i = 0; i < n; i++) {
        for (int j = 0; j < n; j++) {
            cost_int[i][j] = -(n + 1);
        }
    }

    while (k > 0) {

        std::sort(edges.begin(), edges.end());

        // Call getMinimalMaxEdgeInPerfectMatching to get minimum maximal edge in a perfect matching.
        int choice = getMinimalMaxEdgeInPerfectMatching(edges, n, n);
        double max_edge_value = edges[choice].first;

        // Now remove (make very large) all edges that are greater than max_edge_value
        // Set cost of all max_edge_values to 1 and set cost of smaller edges to 0
        for (int i = 0; i < edges.size(); i++) {
            if (edges[i].first < max_edge_value) {
                cost_int[edges[i].second.first][edges[i].second.second] = 0;
            } else if (edges[i].first == max_edge_value) {
                cost_int[edges[i].second.first][edges[i].second.second] = -1;
            } else {
                cost_int[edges[i].second.first][edges[i].second.second] = -(n + 1);
            }
        }

        // Solve 0-1 sum minimization assignment problem
        int l = -hungarian_int();
        k -= l;

        if (k == 0) {
            // We are done!
            break;
        }
        // Now remove all edges that aren't tight edges and add max_edge_value
        // edges to candidate edges for solution
        edges_tmp.clear();
        for (int i = 0; i < edges.size(); i++) {
            Edge e = edges[i];
            if (lx_int[e.second.first] + ly_int[e.second.second] == cost_int[e.second.first][e.second.second]) {
                // We have a tight edge
                if (e.first == max_edge_value) {
                    // Set distance of edge to -1 so that we don't return it when finding the longest edge
                    // in a perfect matching and also so that we set its cost to 0 when minimizing 0-1 sum.
                    e.first = -1;
                }
                edges_tmp.push_back(e);
            } else {
                // We are removing this edge from consideration
                cost_int[e.second.first][e.second.second] = -(n + 1);
            }
        }
        edges = edges_tmp;
    }

    for (int i = 0; i < n; i++) {       //forming answer there
        //変更点
        if (xy_int[i] < nt) {
            answer.push_back(std::make_pair(getdist(t.starts[i], t.targets[xy_int[i]]), std::make_pair(i, xy_int[i])));
        } else {
            answer.push_back(std::make_pair(getdist(t.starts[i], t.starts[i]), std::make_pair(i, xy_int[i])));
        }
    }
    // answer now contains the correct answer.

    return answer;
}

#endif                          // ALGORTHM == MMDR_N4

////////////  End implementation of mmdr_n4  ////////////////
//---------------------SCRAMの処理終了-----------------------------

// begin shotrdist
//手法3
#if BARALGORITHM == SHORTDIST
void shortdist(Test t)
{
    //printf("breakdown %0.f \n", t.targets.at(no_assign_pos.at(0)).first);
    //an内にあるbreakdownの目的地を自分の位置に変更(移動しないようにする)
    for (int i = 0; i < an.size(); i++) {
        for (int j = 0; j < breakdown.size(); j++) {
            int sp = an.at(i).second.first;
            int tp = an.at(i).second.second;
            if ((t.starts.at(sp) == breakdown.at(j)) && (an[i].second.second != N)) {
                an[i].second.second = N;        //目的地を現在地にすることで移動しないようにする
                move_posx[sp] = t.starts.at(sp).first;
                move_posy[sp] = t.starts.at(sp).second;
            }
        }
    }

    //replaceのインデックス値を持つエージェントから最も目的地(no_assigen_pos)に近いものを割り当てる
    if (no_assign_pos.size() > 0) {
        int in = median.size();
        median.push_back(std::vector < Point > ());
        for (int i = 0; i < N; i++) {
            median[in].push_back(t_org.starts.at(i));
        }
        //未割り当てのエージェントと未割り当ての目的地との間で最も距離が短いものを求めている
        std::vector < int >rep;
        bool loop = true;
        while (loop) {
            bool skip = false;
            int count = -1;
            double tmpdist = 100000;
            for (int i = 0; i < t.starts.size(); i++) {

                if (distcnt[i] <= 0 && (an.at(i).second.second < (N - DEFFER))) {
                    continue;
                }

                for (int k = 0; k < rep.size(); k++) {
                    if (rep.at(k) == i) {
                        skip = true;
                        break;
                    }
                }
                if (skip) {
                    skip = false;
                    continue;
                }
                bool fl = false;        //入れ替わり先の判定用 false壊れていない true壊れている
                double d = getdist(t.starts.at(i), t.targets.at(no_assign_pos.at(0)));
                for (int j = 0; j < breakdown.size(); j++) {    //入れ替える候補が壊れたロボットかの確認
                    if (t.starts.at(i) != breakdown.at(j)) {
                        continue;
                    } else {
                        fl = true;
                        skip = true;
                        break;
                    }
                }

                if (skip) {
                    skip = false;
                    continue;
                }

                if ((d < tmpdist) && !fl) {     //距離が短く、候補が壊れていない場合
                    tmpdist = d;
                    count = i;
                }
            }

            for (int j = 0; j < replaceagent.size(); j++) {     //入れ替わるロボットが未割り当てか否かの確認
                if (replaceagent.at(j) == an.at(count).second.first) {  //未割り当てに割り当てた場合
                    loop = false;
                    replaceagent.erase(replaceagent.begin() + j);
                }
            }

            //printf("count %d\n", count);
            //printf("targets %d\n" , an.at(count).second.second);
            rep.push_back(count);
            an[count].first = tmpdist;
            int tmp = no_assign_pos.at(0);

            no_assign_pos.clear();
            if (loop == true) {
                no_assign_pos.push_back(an[count].second.second);
            }
            an[count].second.second = tmp;
            int sp = an.at(count).second.first;
            distcnt[sp] = tmpdist + 0.5;
            move_posx[sp] = t.starts.at(sp).first;
            move_posy[sp] = t.starts.at(sp).second;

        }
        //iの目的地がfreeになる

    }

}

#endif                          //shortdist決定

//--------------手法3終了--------------------------------

//--------------手法1開始----------------

// begin mearpos
//手法１
#if BARALGORITHM == NEARPOS
void nearpos(Test t)
{
    //printf("breakdown %0.f \n", t.targets.at(no_assign_pos.at(0)).first);
    //an内にあるbreakdownの目的地を自分の位置に変更(移動しないようにする)
    for (int i = 0; i < an.size(); i++) {
        for (int j = 0; j < breakdown.size(); j++) {
            int sp = an.at(i).second.first;
            int tp = an.at(i).second.second;
            if (t.starts.at(sp) == breakdown.at(j)) {
                //t.targets[tp] = t.starts.at(sp);
                an[i].second.second = N;        //目的地を現在地にすることで移動しないようにする
                move_posx[sp] = t.starts.at(sp).first;
                move_posy[sp] = t.starts.at(sp).second;
            }
        }
    }

    //replaceのインデックス値を持つエージェントから最も目的地(no_assigen_pos)に近いものを割り当てる
    if (no_assign_pos.size() > 0) {
        //未割り当てのエージェントと未割り当ての目的地との間で最も距離が短いものを求めている
        int count = 0;
        double tmpdist = 100000;
        for (int i = 0; i < replaceagent.size(); i++) {
            double d = getdist(t.starts.at(replaceagent.at(i)), t.targets.at(no_assign_pos.at(0)));
            if (d < tmpdist) {
                tmpdist = d;
                count = i;
            }
        }

        //replaceのインデックス値はcount、目的地はno_assign_pos、距離はtempdistをanに入れる

        an[replaceagent.at(count)].first = tmpdist;
        an[replaceagent.at(count)].second.second = no_assign_pos.at(0);

        int sp = an.at(replaceagent.at(count)).second.first;
        distcnt[sp] = (int)an.at(sp).first + 0.5;
        move_posx[sp] = t.starts.at(sp).first;
        move_posy[sp] = t.starts.at(sp).second;
        replaceagent.erase(replaceagent.begin() + count);
        no_assign_pos.clear();
    }
}

#endif                          //nearpos決定

//-------------------------手法1終了---------------------------

//-------------------------手法2開始-----------------------------

#if BARALGORITHM == REASSIGN
//手法3

void reassign(Test t)
{
    std::vector < Edge > answer;

    if (no_assign_pos.size() > 0) {
        int in = median.size();
        median.push_back(std::vector < Point > ());
        for (int i = 0; i < N; i++) {
            median[in].push_back(t_org.starts.at(i));
        }

        answer = SOLVER(t);

        //printf("starts size %d, targets size %d \n",t.starts.size(),t.targets.size());
        for (int i = 0; i < answer.size(); i++) {
            int resp = answer.at(i).second.first;
            int retp = answer.at(i).second.second;

            //retp,respはtを参照する
            for (int j = 0; j < an.size(); j++) {
                int sp = an.at(j).second.first;
                int tp = an.at(j).second.second;
                int temp = t_org.targets.size() + 1;
                //anのインデックスを変更する　second.first
                //tに対応したものに変更
                //t_orgのstartsと等しいもの

                if (retp >= t.targets.size()) {
                    if (t.starts.at(resp) == t_org.starts.at(sp)) {
                        /*
                                                an[sp].second.second = temp;
                                                distcnt[sp] = 0;
                                                move_perx[sp] = 0;
                                                move_pery[sp] = 0;
                                                break;
*/
                        //printf("zero check \n");

                    }
                } else if (t.starts.at(resp) == t_org.starts.at(sp)) {
                    for (int k = 0; k < t_org.targets.size(); k++) {
                        if (t_org.targets.at(k) == t.targets.at(retp)) {
                            temp = k;
                            an[sp].second.second = k;
                            //an[sp].first = answer.at(resp).first;
                            an[sp].first = getdist(ttmp.starts.at(sp), ttmp.targets.at(k));
                            distcnt[sp] = (int)answer.at(resp).first + 0.5;
                            break;
                        }
                    }
                    if (temp != t_org.targets.size()) {
                        break;
                    }           /*else{
                                   an[sp].second.second = temp;
                                   distcnt[sp] = 0;
                                   } */
                }
            }
        }
        no_assign_pos.clear();
    }
}

#endif

//--------------手法2終了-------------------

//--------------メイン処理****Main Processing---------------------

SoccerArea::SoccerArea(QWidget * parent):
    QWidget(parent), animation(new QPropertyAnimation(this, "animationInd")), animationInd(0)
{
    for (int i = 0; i < 10; i++) {
        positions[i][0] = i;
        positions[i][1] = i;

    }

    animation->setDuration(10000);
    animation->setStartValue(0);
    animation->setEndValue(30);
    animation->setLoopCount(-1);
    animation->start();

    setGeometry(0, 0, geo, geo);
    setStyleSheet("background-color:green;");
    setWindowTitle("SCRAM & JPS+");
}

//----------------------qtの設定終了------------------------

SoccerArea::~SoccerArea()
{
}

void SoccerArea::paintEvent(QPaintEvent * event)
{
    QPainter *painter = new QPainter(this);

    //srand((unsigned int)time(NULL));

    if (flag) {
        if (no_assign_pos.size() > 0) {

#if BARALGORITHM == REASSIGN
            Test re;

            //for(int i=0;i<N;i++){
            //      printf("distcnt[%2d] , %3d , tp %3d \n" , i, distcnt[i] , an[i].second.second);
            //}
            for (int i = 0; i < N; i++) {
                int sp = an.at(i).second.first;
                int tp = an.at(i).second.second;
                int br = 0;
                if ((distcnt[sp] > 0)) {        //目的地に未到達かつ途中で壊れたエージェントの情報を修正
                    for (int j = 0; j < breakdown.size(); j++) {
                        if (t_org.starts.at(sp) == breakdown.at(j)) {
                            if (an[sp].second.second < t_org.targets.size())
                                re.targets.push_back(t_org.targets.at(an[sp].second.second));
                            br = 1;
                            //an[sp].first =0;
                            an[sp].second.second = N - DEFFER;
                            move_perx[sp] = 0;
                            move_pery[sp] = 0;
                            distcnt[sp] = 0;
                        }
                    }
                    if (br != 1) {
                        //re.starts.push_back(t_org.starts.at(sp));
                        re.targets.push_back(t_org.targets.at(tp));
                        continue;
                    }
                } else if (tp > ttmp.targets.size()) {
                    //re.starts.push_back(t_org.starts.at(sp));
                    continue;
                }
            }

            for (int i = 0; i < N; i++) {
                int ch = 0;
                for (int j = 0; j < arrival.size(); j++) {
                    if (i == arrival.at(j)) {
                        ch++;
                        break;
                    }
                }
                for (int j = 0; j < breakdown.size(); j++) {
                    if (t_org.starts.at(i) == breakdown.at(j)) {
                        ch++;
                        break;
                    }
                }
                if (ch == 0) {
                    re.starts.push_back(t_org.starts.at(i));
                }
            }
            //printf("cnt %d , starts %d, targets %d , breakdown %d\n", cnt,re.starts.size(), re.targets.size(), breakdown.size());

            if (re.starts.size() < N) {
                for (int i = 0; i < N; i++) {
                    re.starts.push_back(std::make_pair(1000000, 1000000));
                    //re.targets.push_back(std::make_pair(1000000,1000000));
                    if (re.starts.size() == N) {
                        break;
                    }
                }

            }
            BAR(re);

#endif

#if BARALGORITHM == SHORTDIST  || BARALGORITHM == NEARPOS

            for (int i = 0; i < replaceagent.size(); i++) {
                //printf("repag %d \n ", replaceagent.at(i));

            }

            BAR(t_org);
#endif

            double max = 0;
            double sum = 0;
            for (int i = 0; i < N; i++) {
                sum += an.at(i).first;
                if (max < an.at(i).first) {
                    max = an.at(i).first;
                }
            }
            //printf("sum %f , ave %f , max %f \n", sum,sum/N,max);
        }
        double sum = 0;
    }
    //以下tをt_org

    if (!flag) {
        srand(randomcount);

        int n = N;
        //変更点 初期位置と目的地をランダムに生成
        if (n > 50) {
            for (int i = 0; i < n; i++) {
                t_org.starts.push_back(std::make_pair(rand() % (geo), rand() % (geo)));
            }
            for (int i = 0; i < agn - DEFFER; i++) {
                t_org.targets.push_back(std::make_pair(rand() % (geo), rand() % (geo)));
            }
        } else {

            for (int i = 0; i < n; i++) {
                t_org.starts.push_back(std::make_pair(rand() % (500), rand() % (500)));
            }
            for (int i = 0; i < agn - DEFFER; i++) {
                t_org.targets.push_back(std::make_pair(rand() % (500), rand() % (500)));
            }
        }
        std::copy(t_org.starts.begin(), t_org.starts.end(), back_inserter(ttmp.starts));
        std::copy(t_org.targets.begin(), t_org.targets.end(), back_inserter(ttmp.targets));

        an = SOLVER(t_org);     //結果を代入

        //組み合わせを表示

        for (int i = 0; i < N; i++) {
            int sp = an.at(i).second.first;
            distcnt[i] = (int)an.at(i).first + 0.5;
            move_posx[i] = t_org.starts.at(sp).first;
            move_posy[i] = t_org.starts.at(sp).second;

        }

        double sum = 0;
        double max = 0;
        for (int i = 0; i < N; i++) {
            sum += an.at(i).first;
            if (max < an.at(i).first) {
                max = an.at(i).first;
            }
        }
        //printf("sum %f , ave %f , max %f \n", sum,sum/N,max);

        fp = fopen("result_first", "a+");
        if (fp == NULL) {
            printf("file open失敗\n");
        } else {

            double max = 0;
            double sum = 0;
            for (int i = 0; i < N; i++) {
                sum += an.at(i).first;
                if (max < an.at(i).first) {
                    max = an.at(i).first;
                }
            }
            //fprintf(fp,"number %d,sum %f , ave %f , max %f \n",randomcount, sum,sum/N,max);
            int maxstep = 0;
            for (int i = 0; i < N; i++) {
                if (maxstep < an.at(i).first) {
                    maxstep = (int)an.at(i).first + 0.5;
                }

            }
            fprintf(fp, " sssss%d, %d , %f , %f , %f \n", randomcount, maxstep, sum, sum / N, max);
        }
        fclose(fp);

    }
#if BARALGORITHM == SHORTDIST || BARALGORITHM == NEARPOS

    //エージェントの移動量を計算
    for (int i = 0; i < N; i++) {
        int sp = an.at(i).second.first;
        int tp = an.at(i).second.second;
        if (tp < N - DEFFER) {
            move_perx[i] = (t_org.targets.at(tp).first - t_org.starts.at(sp).first) / distcnt[i];
            move_pery[i] = (t_org.targets.at(tp).second - t_org.starts.at(sp).second) / distcnt[i];

            fprintf(fp, "");

        } else {
            move_perx[i] = 0;
            move_pery[i] = 0;
        }
        if (distcnt[i] > 0) {
            move_posx[i] = move_posx[i] + move_perx[i];
            t_org.starts[sp].first = move_posx[i];
            move_posy[i] = move_posy[i] + move_pery[i];
            t_org.starts[sp].second = move_posy[i];
            distcnt[i]--;
            movedist += abs(move_perx[i]) + abs(move_pery[i]);
        }

    }

#endif

#if BARALGORITHM == REASSIGN
    for (int i = 0; i < N; i++) {
        int sp = an.at(i).second.first;
        int tp = an.at(i).second.second;

        // **************Drawing the Area from SP to TP to implement JPS+******************
        const QPen pen7(Qt::black, 1);  //grid描画

        const QPen pen8(Qt::black, 1);  //small grids 8X8
        const QPen pen2(Qt::red, 4);  //small grids 8X8



            //                   //initial position
            //painter->drawEllipse(ttmp.starts.at(an.at(i).second.first).first,ttmp.starts.at(an.at(i).second.first).second,5,5);
            //painter->drawRect(ttmp.starts.at(an.at(i).second.first).first,ttmp.starts.at(an.at(i).second.first).second,20,20);



            int d1_x = ttmp.starts.at(sp).first;
            int d1_y = ttmp.starts.at(sp).second;

            //target position
            int d2_x = ttmp.targets.at(tp).first;
            int d2_y = ttmp.targets.at(tp).second;

            // ***********Area Calculation*********
            int d3_x, d3_y, d4_x, d4_y;
            d3_x = (d1_x + d2_x + d1_y - d2_y) / 2;
            d3_y = (d2_x - d1_x + d1_y + d2_y) / 2;

            d4_x = (d1_x + d2_x + d2_y - d1_y) / 2;
            d4_y = (d1_x - d2_x + d1_y + d2_y) / 2;
            int len = sqrt((d3_x - d1_x) * (d3_x - d1_x) + (d3_y - d1_y) * (d3_y - d1_y));
            int gridArea = len * len;
            //*************************************
            painter->setPen(pen7);

            //Area Drawing
//            painter->drawLine(d1_x, d1_y, d3_x, d3_y);
//            painter->drawLine(d2_x, d2_y, d4_x, d4_y);
//            painter->drawLine(d1_x, d1_y, d4_x, d4_y);
//            painter->drawLine(d2_x, d2_y, d3_x, d3_y);

            double ratio = 8/len;
            double x1 = (1-ratio)*d1_x + ratio*d2_x;
            double y1 = (1-ratio)*d1_y + ratio*d2_y;
            double x2= ratio*d3_x + (1-ratio)*d4_x;
            double y2 = ratio*d3_y + (1-ratio)*d4_y;




//            painter->drawEllipse(x1, y1, 5, 5);
//            painter->drawEllipse(x2, y2, 5, 5);

           painter->drawLine(x1, y1, x2, y2);


             //painter->drawRect(d4_x, d4_y, len, len);
            // painter->drawRects(d2_x, d2_y, len, len);
            //                                  painter->drawLine(d2_x,d2_y, d1_x, d1_y);
            //                                  painter->drawLine(d3_x,d3_y, d4_x, d4_y);
            //                                  painter->drawLine(d2_x,d2_y, d3_x, d3_y);
            //                                  painter->drawLine(d4_x,d4_y, d1_x, d1_y);

         //painter->setPen(pen8);
            //painter->drawRect(d1_x, d2_y, (gridArea/64), (gridArea/64));

//                for (int a=0; a< 8;  a++)
//                {
//                    for (int j = 0; j < 8; j++)
//                    {

//                        painter->drawRect(d3_x+(gridArea/8)*a, d3_y+(gridArea/8)*j, (gridArea/8), (gridArea/8));


//                    }
//                }



        //**************End of Drawing the Area from SP to TP to implement JPS+******************

        if (tp < N - DEFFER) {
            move_perx[i] = (t_org.targets.at(tp).first - t_org.starts.at(sp).first) / distcnt[i];
            move_pery[i] = (t_org.targets.at(tp).second - t_org.starts.at(sp).second) / distcnt[i];

        } else {
            move_perx[i] = 0;
            move_pery[i] = 0;
        }

        if (distcnt[i] > 0) {
            move_posx[i] = move_posx[i] + move_perx[i];
            t_org.starts[sp].first = move_posx[i];
            move_posy[i] = move_posy[i] + move_pery[i];
            t_org.starts[sp].second = move_posy[i];
            distcnt[i]--;
            movedist += abs(move_perx[i]) + abs(move_pery[i]);
        }

    }
#endif

    //直線描画設定
    double harf = 1.5;
    const QPen pen1(Qt::white, 3);      //線
    const QPen pen2(Qt::white, 4);      //現在位置
    const QPen pen3(Qt::yellow, 4);     //目的地
    const QPen pen4(Qt::red, 5);        //到着済み
    const QPen pen5(Qt::blue, 4);       //初期位置
    const QPen pen6(Qt::black, 4);      //崩壊


    //
    painter->setPen(pen1);

    if (median.size() == 0) {
        for (int i = 0; i < an.size(); i++) {   //初期位置から現在地まで
            painter->drawLine(ttmp.starts.at(i).first + harf, ttmp.starts.at(i).second + harf,
                              t_org.starts.at(i).first + harf, t_org.starts.at(i).second + harf);
        }
    } else if (median.size() == 1) {
        for (int i = 0; i < an.size(); i++) {   //初期位置から中間地点まで
            painter->drawLine(ttmp.starts.at(i).first + harf, ttmp.starts.at(i).second + harf,
                              median[0][i].first + harf, median[0][i].second + harf);
        }
        for (int j = 0; j < an.size(); j++) {   //中間地点から現在地まで
            painter->drawLine(median[0][j].first + harf, median[0][j].second + harf,
                    t_org.starts.at(j).first + harf, t_org.starts.at(j).second + harf);
        }
    } else if (median.size() > 1) {
        for (int i = 0; i < an.size(); i++) {   //初期位置から中間地点まで
            painter->drawLine(ttmp.starts.at(i).first + harf, ttmp.starts.at(i).second + harf,
                              median[0][i].first + harf, median[0][i].second + harf);
        }
        int i = 0;
        for (i = 0; i < median.size() - 1; i++) {       //中間地点から中間地点まで
            for (int j = 0; j < an.size(); j++) {
                painter->drawLine(median[i][j].first + harf, median[i][j].second + harf,
                                  median[i + 1][j].first + harf, median[i + 1][j].second + harf);
            }
        }
        //i=i-1;
        for (int j = 0; j < an.size(); j++) {   //中間地点から現在地まで
            painter->drawLine(median[i][j].first + harf, median[i][j].second + harf,
                              t_org.starts.at(j).first + harf, t_org.starts.at(j).second + harf);
        }

    }
    //初期位置描画
    painter->setPen(pen5);
    for (int i = 0; i < N; i++) {
        painter->drawEllipse(ttmp.starts.at(an.at(i).second.first).first, ttmp.starts.at(an.at(i).second.first).second,
                             5, 5);
    }

    //現在地描画
    //painter->setBrush(QBrush("white",Qt::SolidPattern));
    painter->setPen(pen2);
    for (int i = 0; i < N; i++) {
        painter->drawEllipse(t_org.starts.at(an.at(i).second.first).first,
                             t_org.starts.at(an.at(i).second.first).second, 5, 5);
    }

    //目的地の描画
    //painter->setBrush(QBrush("red",Qt::SolidPattern));
    painter->setPen(pen3);
    for (int i = 0; i < N; i++) {
        if (i < N - DEFFER) {
            painter->drawEllipse(ttmp.targets.at(i).first, ttmp.targets.at(i).second, 5, 5);

            //painter->drawRect(ttmp.targets.at(i).first,ttmp.targets.at(i).second,20,20);

            //painter->drawLine(t_org.starts.at(an.at(i).second.first).first,t_org.starts.at(an.at(i).second.first).second,ttmp.targets.at(i).first,ttmp.targets.at(i).second);
        }

    }

    cnt = 0;
    //到着した場合
    for (int i = 0; i < N; i++) {
        int tp = an.at(i).second.second;
        if (tp < N - DEFFER) {
            if (distcnt[i] <= 0) {
                painter->setPen(pen4);
                painter->drawEllipse(ttmp.targets.at(an.at(i).second.second).first,
                                     ttmp.targets.at(an.at(i).second.second).second, 5, 5);
                t_org.starts[i] = ttmp.targets[tp];
                arrival.push_back(i);
                cnt++;
            }
        }
    }
    //壊れたエージェントの描画
    for (int i = 0; i < breakdown.size(); i++) {
        //printf("pos %0.f ,%0.f \n" ,breakdown.at(i).first,breakdown.at(i).second);
        painter->setPen(pen6);
        painter->drawEllipse(breakdown.at(i).first, breakdown.at(i).second, 5, 5);
    }

    //置き換え用エージェントの配列を用意
    if (!flag) {
        for (int i = 0; i < t_org.starts.size(); i++) {
            int sp = an.at(i).second.first;
            int tp = an.at(i).second.second;
            if (tp >= N - DEFFER) {
                replaceagent.push_back(sp);
            }
        }
        flag = true;            //割り当てを再度求めないようにする

    }

    std::sort(arrival.begin(), arrival.end());
    arrival.erase(std::unique(arrival.begin(), arrival.end()), arrival.end());

    step++;

    if (cnt == (N - DEFFER)) {

        //-------------------------結果の書き込み----------------------

#if BARALGORITHM == REASSIGN

        fp = fopen("result_reassign", "a+");

#endif

#if BARALGORITHM == SHORTDIST
        fp = fopen("result_shortdist", "a+");
#endif

#if BARALGORITHM == NEARPOS
        fp = fopen("result_nearpos", "a+");
#endif

        if (fp == NULL) {
            printf("file open失敗\n");
        } else {

            double max = 0;
            double sum = 0;
            for (int i = 0; i < N; i++) {
                sum += an.at(i).first;
                if (max < an.at(i).first) {
                    max = an.at(i).first;
                }
            }
            end = clock();
            double dur = (double)(end - start) / CLOCKS_PER_SEC;
            fprintf(fp, " %d, %d , %f , %f , %f , %f , %f \n", randomcount, step, sum, sum / N, max, movedist, dur);
            //fprintf(fp," %d, %d , %f , %f , %f , %f \n",randomcount,step, sum,sum/N,max,movedist);
            //step,ループ回数,合計,平均,最大値,総移動量

            start = clock();

            t_org.starts.clear();
            t_org.targets.clear();
            ttmp.starts.clear();
            ttmp.targets.clear();

            arrival.clear();
            breakdown.clear();
            no_assign_pos.clear();
            replaceagent.clear();
            flag = false;
            randomcount++;

            movedist = 0;
            step = 0;

            if (median.size() > 0)
                for (int i = 0; i < median.size(); i++) {
                    median[i].clear();
                }
            median.clear();

        }

        fclose(fp);
        if (randomcount == loopend) {

            ttmp.starts.at(101);
            //終了処理

        }

    }

    delete painter;

}

//-----------以下ロボットの故障判定---------------------

void SoccerArea::setAnimationInd(int ind)
{

    //処理の遅延用
    if (flag) {
        //usleep(2000);
    }
    //エージェントを壊すための処理
    if (flag) {
        if ((breakdown.size() < DEFFER) && (loopcount == 0)) {
            //printf("enter , breakdownsize %d \n", breakdown.size());
            //srand((unsigned)time(NULL));

            int r = rand() % an.size(); //壊れるエージェントのインデックスを決定
            //printf("rand %d \n" ,r);
            int sp = an.at(r).second.first;
            int tp = an.at(r).second.second;
            //printf("check sp %d, tp  %d ,%d \n \n",sp, tp , N-DEFFER);
            if (tp >= agn - deffer) {
                if (breakdown.size() == 0) {
                    breakdown.push_back(t_org.starts.at(sp));   //壊れたエージェントの配列に追加
                    //no_assign_pos.push_back(tp);  //壊れたエージェントの目的地を追加
                } else {
                    for (int i = 0; i < breakdown.size(); i++) {
                        if (breakdown.at(i) == t_org.starts.at(sp)) {
                            break;
                        }
                        if (breakdown.size() == (i + 1)) {
                            breakdown.push_back(t_org.starts.at(sp));   //壊れたエージェントの配列に追加
                        }
                    }
                }
                //目的地に到着しているならば
            } else if (t_org.starts.at(sp) == t_org.targets.at(tp)) {
                if (breakdown.size() == 0) {
                    breakdown.push_back(t_org.starts.at(sp));   //壊れたエージェントの配列に追加
                    if (tp < agn - deffer)
                        no_assign_pos.push_back(tp);
                } else {
                    for (int i = 0; i < breakdown.size(); i++) {
                        if (breakdown.at(i) == t_org.starts.at(sp)) {
                            break;
                        }
                        if (breakdown.size() == (i + 1)) {
                            //breakdown.push_back(t.starts.at(sp)); //壊れたエージェントの配列に追加
                            //no_assign_pos.push_back(tp);  //壊れたエージェントの目的地を追加
                        }

                    }
                }
            } else {
                if (breakdown.size() == 0) {
                    breakdown.push_back(t_org.starts.at(sp));
                    no_assign_pos.push_back(tp);
                } else {
                    for (int i = 0; i < breakdown.size(); i++) {
                        if (breakdown.at(i) == t_org.starts.at(sp)) {
                            break;
                        }
                        if (breakdown.size() == (i + 1)) {
                            breakdown.push_back(t_org.starts.at(sp));
                            no_assign_pos.push_back(tp);
                        }
                    }
                }

            }

            for (int i = 0; i < breakdown.size(); i++) {
                for (int j = 0; j < replaceagent.size(); j++) {
                    if (breakdown.at(i) == t_org.starts.at(replaceagent.at(j))) {
                        replaceagent.erase(replaceagent.begin() + j);
                    }
                }
            }

            if ((DEFFER - breakdown.size()) == deffer) {
                deffer = DEFFER - breakdown.size();
                agn = N - breakdown.size();
            }
        }
    }

    loopcount++;
    if (loopcount >= 10) {
        loopcount = 0;
    }

    animationInd = ind;
    update();
}
