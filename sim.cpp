#include <cstdio>
#include <cstring>
#include <algorithm>
#include <vector>
#include <queue>
#include <cmath>
#include <string>
#include <random>
#include <memory>
#include <cstdlib>
#include <map>
#include <unordered_map>
#include <set>
#include <chrono>
#include <ctime>
#include "coordinate.h"
#define memcle(a) memset(a, 0, sizeof(a))

using namespace std;
const static int K = 8;
const int N = 8500;
const double pi = acos(-1);
const double R = 6371000; // radius of the earth
const double inf = 1e8;
const int MAX_DEPTH = 40;
const double FIXED_DELAY = 250;
const int ROOT_FANOUT = 64;
const int SECOND_FANOUT = 64;
const int FANOUT = 8;
const int INNER_DEG = 4;
const int MAX_TEST_N = 8000;
const int MAX_OUTBOUND = 8;
//typedef unsigned int int;
double BANDWIDTH = 33000000.0;      // 带宽，单位Mbps
double DATA_SIZE = 300.0;          // 数据大小，单位Byte，可选300B或1MB(1048576B)
//double DATA_SIZE = 1048576.0;  
int n;
mt19937 rd(1000);
bool recv_flag[N];
int recv_parent[N];
double recv_time[N]; 
double recv_dist[N]; 
int depth[N];

int mal_flag[N];
FILE* fig_csv;


// coordinate, using longitude and latitude
class LatLonCoordinate {
  public:
    double lat, lon;
};

LatLonCoordinate coord[N];

// from degree to radian 
double rad(double deg) {return deg * pi / 180;}

// distance between two coordinate
double distance(const LatLonCoordinate &a, const LatLonCoordinate &b) {
    if (abs(a.lat - b.lat) < 0.1 && abs(a.lon - b.lon) < 0.1)
        return 0;
    double latA = rad(a.lat), lonA = rad(a.lon);
    double latB = rad(b.lat), lonB = rad(b.lon);
    double C = cos(latA) * cos(latB) * cos(lonA - lonB) + sin(latA) * sin(latB);
    double dist = acos(C) * R ;
    return dist / 100000 * 2;
}

class message {
  public:
    int root, src, dst, step;
    double send_time, recv_time;

    message(int _root, int _src, int _dst, int _step, double _send_time, double _recv_time) : 
        root(_root), src(_src), dst(_dst), step(_step), send_time(_send_time), recv_time(_recv_time) {

    }

    void print_info() {
        fprintf(stderr, "message rooted at %d sent from node %d to %d\n, step %d", root, src, dst, step);
        fprintf(stderr, "send time at %.2f, recv time at %.2f, delay is %.2f\n", send_time, recv_time, recv_time - send_time);
    }
};

bool operator>(const message &a, const message &b) {
    return a.recv_time > b.recv_time;
}

class graph {
  public:
    vector<int> in_bound[N];
    vector<int> out_bound[N];
    int n; 
    int m;

    graph(int _n) : n(_n) {
       m = 0; 
    }

    bool add_edge(int u, int v) {
        // avoid self-loop and duplicate edge
        if (u == v) return false;
        for (auto nb_u : out_bound[u]) 
            if (nb_u == v) 
                return false;
        out_bound[u].push_back(v);
        in_bound[v].push_back(u);
        m++;
        return true;
    }

    void del_edge(int u, int v) {
        bool ok = false;
        for (size_t i = 0; i < out_bound[u].size(); i++)
            if (out_bound[u][i] == v) {
                int len = out_bound[u].size();
                out_bound[u][i] = out_bound[u][len - 1];
                out_bound[u].pop_back();
                ok = true;
                break;
            }
        if (ok == false)
            printf("cannot del an edge\n");

        for (size_t i = 0; i < in_bound[v].size(); i++)
            if (in_bound[v][i] == u) {
                int len = in_bound[v].size();
                in_bound[v][i] = in_bound[v][len - 1];
                in_bound[v].pop_back();
                break;
            }
    }

    vector<int> outbound(int u) {
        auto v = out_bound[u];
        return v;
    }
    vector<int> inbound(int u) {
        auto v = in_bound[u];
        return v;
    }

    void print_info() {
        double avg_outbound = 0;
        for (int i = 0; i < n; i++) {
            fprintf(stderr, "node %d's outbound:", i);
            avg_outbound += out_bound[i].size();
            for (auto j : out_bound[i])
                fprintf(stderr, " %d", j);
            fprintf(stderr, "\n");
        }
        avg_outbound /= n;
        fprintf(stderr, "%.2f\n", avg_outbound);
    }
};

int random_num(int n) {
    return rand() % n;
}

class basic_algo {
// strategy base class
//
// respond(msg): 
// one message delivered at [msg.dst],
// return the index list of its choice of relay nodes
//

  public:
    basic_algo() {}
    virtual vector<int> respond(message msg) = 0;
    virtual void set_root(int _root) {}
    //static const char* get_algo_name();
};

template<int root_fanout = ROOT_FANOUT, int second_fanout = SECOND_FANOUT, int fanout = FANOUT>
class random_flood : public basic_algo {

// random flood : 
// 1. Connet the graph as a ring to prevent partition
// 2. Every node selects other 7 random outbounds

  private: 
    graph G; // random graph
    static constexpr const char* algo_name = "random_flood";
    int tree_root;

  public:
    const static bool specified_root = true;
    random_flood(int n, LatLonCoordinate *coord, int root = 0) : G(n) {
        tree_root = root;
        // firstly connect a ring, then random connect

        for (int u = 0; u < n; u++) {
            int dg = fanout;
            for (int k = 0; k < dg; k++) {
                int v = random_num(n);
                while (G.add_edge(u, v) == false)
                    v = random_num(n);
            }
        }
    }

    vector<int> respond(message msg)  {
        // Directly return all [msg.dst]'s outbounds.

        int u = msg.dst;
        vector<int> nb_u = G.outbound(u);
        vector<int> ret;
        for (auto v : nb_u) 
            if (v != msg.src) 
                ret.push_back(v);
  
        if (u == tree_root) {
            int remain_deg = root_fanout - ret.size();
            for (int i = 0; i < remain_deg; i++) {
                int v = rand() % n;
                if (v != msg.src) 
                    ret.push_back(v);
            }
        }
        return ret;
    }

    static const char* get_algo_name() {return algo_name;} 
    void print_info() {
        G.print_info();
    }
};

// the difference of lontitudes should be in the range of [-180, 180]
double fit_in_a_ring(double x)  {
    if (x < -180) x += 360;
    if (x > 180) x -= 360;
    return x;
}

// the angle between the vector r ---> u and u ---> v should be in [-90, 90]
// notice: simply use (lontitude, latitude) as the normal 2-d (x, y) coordinate
bool angle_check(const LatLonCoordinate &r, const LatLonCoordinate &u, const LatLonCoordinate &v) {
    double x1 = u.lon - r.lon, y1 = u.lat - r.lat;
    double x2 = v.lon - u.lon, y2 = v.lat - u.lat;
    x1 = fit_in_a_ring(x1);
    x2 = fit_in_a_ring(x2);

    // get the vertical vector of (u - r)
    double x3 = y1, y3 = -x1;

    // use cross dot to check the angle
    return (x3 * y2 - x2 * y3) > -1e-3;
}


template<int root_deg = ROOT_FANOUT, int second_deg = SECOND_FANOUT, int normal_deg = FANOUT>
class static_build_tree : public basic_algo {
// static_build_tree:
// Suppose the broadcast root is [root].
// Firstly, sort the nodes based on the distance between them and [root].
// The sorted list is [list].
//
// Build the broadcast tree as following rules:
// For the node, u = list[i]
// The father should be:
//    v in list[0...i-1]:
//    minimize: tree_distance(root, v) + distance(v, u)
//    subject to: out_bound[v] < 8 

  private: 
    graph G; // random graph
    static constexpr const char* algo_name = "static_build";
    double dist[N];
    int out_bound_cnt[N];
    int list[N];
    int depth[N];
  
  public: 
    const static bool specified_root = true;
    static_build_tree(int n, LatLonCoordinate *coord, int root = 0) : G(n) {
        memcle(dist);
        memcle(out_bound_cnt);
        memcle(list);
        memcle(depth);

        vector<pair<double, int> > rk;
        for (int j = 0; j < n; j++) 
            if (j != root) 
                rk.push_back(make_pair(distance(coord[root], coord[j]), j));
        sort(rk.begin(), rk.end());
        list[0] = root;
        for (int j = 1; j < n - 1; j++) 
            list[j] = rk[j - 1].second;

        for (int i = 0; i < n - 1; i++) {
            int u = list[i + 1];

            double cur_min = 1e100;
            int cur_parent = 0;
            for (int j = 0; j <= i; j++) {
                int v = list[j];
                if ((v == root && out_bound_cnt[v] < root_deg) || (out_bound_cnt[v] < normal_deg && dist[v] + distance(coord[u], coord[v]) + FIXED_DELAY < cur_min)) {
                    cur_min = distance(coord[u], coord[v]) + dist[v] + FIXED_DELAY;
                    cur_parent = v;
                }
            }
            // set parent of u 
            G.add_edge(cur_parent, u);
            dist[u] = cur_min;
            out_bound_cnt[cur_parent]++;
        }

        printf("root deg = %d\n", out_bound_cnt[root]);
    }

    vector<int> respond(message msg)  {
        int u = msg.dst;
        vector<int> nb_u = G.outbound(u);
        vector<int> ret;
        for (auto v : nb_u) 
            if (v != msg.src) 
                ret.push_back(v);
        return ret;
    }

    static const char* get_algo_name() {return algo_name;} 
    void print_info() {
        G.print_info();
    }
};

const static int D = 3;
const static int COORDINATE_UPDATE_ROUND = 100;
VivaldiModel<D> vivaldi_model[N];

void generate_random_virtual_coordinate() {
    for (int i = 0; i < n; i++) {
        vivaldi_model[i] = VivaldiModel<D>(i);
        double tmp[2] = {random_between_0_1() * 1000, random_between_0_1() * 1000};
        vivaldi_model[i].local_coord = Coordinate<D>(tmp, 0, 0.1);
    }
}

void generate_virtual_coordinate() {
    // init
    for (int i = 0; i < n; i++)
        vivaldi_model[i] = VivaldiModel<D>(i);
    
    for (int round = 0; round < COORDINATE_UPDATE_ROUND; round++) {
        //printf("%d\n", round);
        for (int x = 0; x < n; x++) {
            vector<int> selected_neighbor;
            if (vivaldi_model[x].have_enough_peer) {
                for (auto &y: vivaldi_model[x].random_peer_set)
                    selected_neighbor.push_back(y);
            } else {
                for (int j = 0; j < 16; j++) {
                    int y = rand() % n;
                    while (y == x) y = rand() % n;
                    selected_neighbor.push_back(y);
                }
            }

            for (auto y: selected_neighbor)
            {
                double rtt = distance(coord[x], coord[y]) + FIXED_DELAY;
                vivaldi_model[x].observe(y, vivaldi_model[y].coordinate(), rtt);
            }
        }
    }

}

const static int max_iter = 100;
int cluster_cnt[K];
int cluster_result[N];
vector<int> cluster_list[K];

// k_means: 8 cluster
// cluster_cnt[i]: #nodes in cluster i
// cluster_list[i]: list of nodes in cluster i
// cluster_result[u]: u belongs to this cluster

void k_means() {
    srand(11);
    memcle(cluster_cnt);
    memcle(cluster_result);
    LatLonCoordinate center[K];
    LatLonCoordinate avg[K];
    vector<int> tmp_list;

    for (int i = 0; i < K; i++) {
        while (true) {
            int u = random_num(n);
            //int u = i;
            if (find(tmp_list.begin(), tmp_list.end(), u) == tmp_list.end()) {
                center[i] = coord[u];
                tmp_list.push_back(u);
                break;
            }
        }
    }

    // K means
    for (int iter = 0; iter < max_iter; iter++) {

        // find the nearest center
        for (int i = 0; i < n; i++) {
            double dist = 1e100;
            int cur_cluster = 0;
            for (int j = 0; j < K; j++)
                if (distance(center[j], coord[i]) < dist) {
                    dist = distance(center[j], coord[i]);
                    cur_cluster = j;
                }
            cluster_result[i] = cur_cluster;
        }

        // re-calculate center
        memcle(avg);
        memcle(cluster_cnt);
        for (int i = 0; i < n; i++) {
            avg[cluster_result[i]].lon += coord[i].lon;
            avg[cluster_result[i]].lat += coord[i].lat;
            cluster_cnt[cluster_result[i]]++;
        }
        for (int i = 0; i < K; i++) 
            if (cluster_cnt[i] > 0) {
                center[i].lon = avg[i].lon / cluster_cnt[i];
                center[i].lat = avg[i].lat / cluster_cnt[i];
            }
    }


    for (int i = 0; i < K; i++)
        cluster_list[i].clear();

    for (int i = 0; i < n; i++) 
        cluster_list[cluster_result[i]].push_back(i);
    
    printf("cluster result \n");
    for (int i = 0; i < K; i++)
        printf("%lu ", cluster_list[i].size());
    printf("\n");
}
void k_means_based_on_virtual_coordinate() {
    srand(13);
    memcle(cluster_cnt);
    memcle(cluster_result);

    EuclideanVector<D> center[K];
    EuclideanVector<D> avg[K];
    vector<int> tmp_list;

    for (int i = 0; i < K; i++) {
        while (true) {
            int u = random_num(n);
            if (find(tmp_list.begin(), tmp_list.end(), u) == tmp_list.end()) {
                center[i] = vivaldi_model[u].vector();
                tmp_list.push_back(u);
                break;
            }
        }
    }

    // K means
    for (int iter = 0; iter < max_iter; iter++) {

        // find the nearest center
        for (int i = 0; i < n; i++) {
            double dist = 1e100;
            int cur_cluster = 0;
            for (int j = 0; j < K; j++)
                if (distance(center[j], vivaldi_model[i].vector()) < dist) {
                    dist = distance(center[j], vivaldi_model[i].vector());
                    cur_cluster = j;
                }
            cluster_result[i] = cur_cluster;
        }

        // re-calculate center
        memcle(avg);
        memcle(cluster_cnt);
        for (int i = 0; i < n; i++) {
            avg[cluster_result[i]] = avg[cluster_result[i]] + vivaldi_model[i].vector();
            cluster_cnt[cluster_result[i]]++;
        }
        for (int i = 0; i < K; i++) 
            if (cluster_cnt[i] > 0) {
                center[i] = avg[i] / cluster_cnt[i];
            }
    }

    //for (int i = 0; i < n; i++)
    //    printf("%d ", cluster_result[i]);
    //printf("\n");

    for (int i = 0; i < K; i++)
        cluster_list[i].clear();

    for (int i = 0; i < n; i++) 
        cluster_list[cluster_result[i]].push_back(i);

    printf("cluster result \n");
    for (int i = 0; i < K; i++)
        printf("%lu ", cluster_list[i].size());
    printf("\n");
}




template <int root_fanout = ROOT_FANOUT, int second_fanout = SECOND_FANOUT, int fanout = FANOUT, bool enable_nearest = false, bool worst_attack = false>
class k_means_cluster : public basic_algo {
// k_means_cluster:
// firstly build K clusters (K = 8)
// For the [root], it randomly connects to root_deg_per_cluster nodes in every cluster. (1, 2, 4...)
// For other nodes, they randomly connects to 4 nodes in the same cluster and 4 nodes in other clusters.

  private: 
    graph G; // random graph
    graph G_near;
    const int random_out = 4;
    static constexpr const char* algo_name = "cluster";
    mt19937 rng;

  public: 
    const static bool specified_root = true;
    k_means_cluster(int n, LatLonCoordinate *coord, int root = 0) : G(n), G_near(n), rng(100) {
        
        for (int i = 0; i < n; i++)  {
            int c = cluster_result[i];
            // 4 out_bound in the same cluster
            int inner_deg = INNER_DEG;

            if (vivaldi_model[i].coordinate().error() < 0.4) {
                if (cluster_cnt[c] <= inner_deg + 1) {
                    for (int j : cluster_list[c])
                        if (i != j)
                            G.add_edge(i, j);
                } else {
                    int deg = inner_deg;
                    vector<pair<double, int> > cluster_peer;
                    for (int trial = 0, cnt = 0; trial < 100 && cnt < deg; trial++) {
                        int j = cluster_list[c][random_num(cluster_cnt[c])];
                        int j1 = cluster_list[c][random_num(cluster_cnt[c])];
                        if (distance(vivaldi_model[i].vector(), vivaldi_model[j].vector()) > 
                            distance(vivaldi_model[i].vector(), vivaldi_model[j1].vector()))
                                j = j1;
                        if (i != j) {
                            double dist = distance(vivaldi_model[i].vector(), vivaldi_model[j].vector());
                            cluster_peer.push_back(make_pair(dist, j));
                            cnt += 1;
                        }
                    }
                    sort(cluster_peer.begin(), cluster_peer.end());
                    for (int j = 0, cnt = 0; j < cluster_peer.size() && cnt < deg; j++) {
                        if (G.add_edge(i, cluster_peer[j].second)) {
                            cnt += 1;
                        }
                    }
                }

            }

            // build the near graph
            if (vivaldi_model[i].coordinate().error() < 0.4) {
                vector<pair<double, int> > nearest_peer;
                for (int j : cluster_list[c]) {
                    if (i != j) {
                        double dist = distance(vivaldi_model[i].vector(), vivaldi_model[j].vector());
                        nearest_peer.push_back(make_pair(dist, j));
                        for (int k = nearest_peer.size() - 1; k > 0; k--) {
                            if (nearest_peer[k - 1].first > nearest_peer[k].first) 
                                swap(nearest_peer[k - 1], nearest_peer[k]);
                            else 
                                break;
                        }
                        if (nearest_peer.size() > inner_deg) {
                            nearest_peer.pop_back();
                        }
                    }
                }

                for (auto pr: nearest_peer) {
                    //printf("near peer : (%d %d) %.3f\n", i, pr.second, pr.first);
                    G_near.add_edge(i, pr.second);
                }
            }
        }
    }
        
    vector<int> respond(message msg)  {
        int u = msg.dst;
        vector<int> nb_u = G.outbound(u);
        vector<int> ret;


        if (enable_nearest && (cluster_result[msg.src] != cluster_result[u] || msg.step == 0 || msg.recv_time - msg.send_time > 100)) {
            int cnt = 0;
            for (auto v : G_near.out_bound[u]) {
                if (v != msg.src) {
                    ret.push_back(v);
                    cnt++;
                }
            }
        } 
        else {
            int cnt = 0;
            for (auto v : nb_u) 
                if (v != msg.src) {
                    ret.push_back(v);
                    cnt++;
                }
        }

        int remain_deg = 0;
        if (msg.step == 0) {
            remain_deg = root_fanout - ret.size();
        } else if (msg.step == 1) {
            remain_deg = second_fanout - ret.size();
        } else {
            remain_deg = fanout - ret.size();
        }

        // !!!!!!!!!!!!!!!!!
        // If worst_attack happens, we assume all the peer selection related to distance/coordinate/clustering fails
        if (worst_attack == true) {
            ret.clear();
        }

        //printf("remain deg %d\n", remain_deg);

        for (int i = 0; i < remain_deg; i++) {
            int v = rng() % n;
            if (u != v && std::find(ret.begin(), ret.end(), v) == ret.end()) {
                ret.push_back(v);
            }
        }
        return ret;
    }

    static const char* get_algo_name() {return algo_name;} 
    void print_info() {
        G.print_info();
    }
};



class perigee_observation {
  public:
    vector<double> obs; // the time difference
    int u; // src
    int v; // dst

    perigee_observation() {}
    perigee_observation(int _u, int _v) {
        init(_u, _v);
    }
    void init(int _u, int _v) {
        u = _u;
        v = _v;
        obs.clear();
    }

    void add(double t) {
        if (t < 0) {
            printf("t = %.2f\n", t);
            printf("(%d, %d)\n", u, v);
        }
        obs.push_back(t);
    }

    pair<double, double> get_lcb_ucb() {
        int len = obs.size();
        if (len == 0) {
            return make_pair(1e10, 1e10);
        }
        int pos = int(len * 0.9);
        //use fast selection to avoid sorting
        nth_element(obs.begin(), obs.begin() + pos, obs.end()); 

        double per90obs = obs[pos];
        double bias = 125.0 * sqrt(log(len) / (2 * len));
        return make_pair(per90obs - bias, per90obs + bias);
    }
};

template<int root_fanout = ROOT_FANOUT, int fanout = FANOUT, int max_outbound = MAX_OUTBOUND>
class perigee_ubc : public basic_algo {
// perigee_ubc
// https://arxiv.org/pdf/2006.14186.pdf
// Firstly, execute warmup phase for 640 random messages.
// For an edge (u, v), node v will maintain an observation array O.
// When u is sending a message m to v, v will store the timestamp of the 
// receiving time T(u, v, m), and the time difference since v firstly sees the message: 
// T(u, v, m)  - min_u' T(u', v, m)
// For every 10 message, every nodes updates their outbound based on the UBC method

  private: 
    mt19937 rng;
    graph G; // random graph
    //static constexpr int deg = 8;
    static constexpr const char* algo_name = "perigee_ubc";
    //perigee_observation obs[N][deg];
    vector<unique_ptr<perigee_observation> > obs[N];

    // use for warmup phase
    static constexpr int total_warmup_message = 640;
    static constexpr int warmup_round_len = 10; // for every 10 message, execute a reselection
    int recv_flag[N]; // keep track of the newest warmup message token
    double recv_time[N];  // record the new message deliever time

  public: 
    const static bool specified_root = false;
    perigee_ubc(int n, LatLonCoordinate *coord, int root = 0) : rng(root), G(n) {
        for (int u = 0; u < n; u++) {
            int dg = fanout - INNER_DEG;
            //if (u == root)
            //    dg = 32 - 1;
            // should reverse the connection
            for (int k = 0; k < dg; k++) {
                int v = random_num(n);
                while (G.add_edge(u, v) == false)
                    v = random_num(n);
            }
        }

        // TODO: inbound has far more than 8
        for (int u = 0; u < n; u++) {
            int dg = INNER_DEG;
            //if (u == root)
            //    dg = 32 - 1;
            // should reverse the connection
            for (int k = 0; k < dg; k++) {
                int v = random_num(n);
                while (G.add_edge(u, v) == false)
                    v = random_num(n);

                //obs[v][k].init(u, v);
                if (obs[v].size() < INNER_DEG) {
                    unique_ptr<perigee_observation> ptr(new perigee_observation(u, v));
                    obs[v].push_back(move(ptr));
                }
            }
        }

        //warmup phase
        memset(recv_flag, -1, sizeof(recv_flag));

        for (int warmup_message = 0; warmup_message < total_warmup_message; warmup_message++) {

            int root = random_num(n);

            priority_queue<message, vector<message>, greater<message> > msg_queue;
            msg_queue.push(message(root, root, root, 0, 0, 0)); // initial message

            for (; !msg_queue.empty(); ) {
                message msg = msg_queue.top();
                msg_queue.pop();

                int u = msg.dst; // current node

                // a new message
                if (recv_flag[u] < warmup_message) {
                    recv_flag[u] = warmup_message;
                    recv_time[u] = msg.recv_time;

                    {
                    //if (mal_flag[u] == false) {
                        auto relay_list = respond(msg);
                        double delay_time = 0;
                        if (u == root) delay_time = 0;
                        for (auto v : relay_list) {
                            double dist = distance(coord[u], coord[v]) * 3 + FIXED_DELAY; 
                            message new_msg = message(root, u, v, msg.step + 1, recv_time[u] + delay_time, recv_time[u] + dist + delay_time);
                            msg_queue.push(new_msg);
                        }
                    }

                } 
                // add observation, find the corresponding queue
                for (auto &it: obs[u]) 
                    if (it -> u == msg.src) 
                        it -> add(msg.recv_time - recv_time[u]);
            }

            if ((warmup_message + 1) % warmup_round_len == 0) {
                //printf("%d\n", warmup_message);
                int kill_cnt = 0;
                for (int i = 0; i < n; i++)  {
                    if (neighbor_reselection(i) == 1) {
                        //printf("obs size %d\n", obs[i].size());
                        kill_cnt += 1;
                    }
                }
                //printf("round = %d, kill = %d\n", warmup_message / warmup_round_len, kill_cnt);
                //printf("finish\n");
            }
        }

        for (int u = 0; u < n; u++) {
            int dg = max_outbound - G.out_bound[u].size();
            for (int k = 0; k < dg; k++) {
                int v = random_num(n);
                while (G.add_edge(u, v) == false)
                    v = random_num(n);
            }
        }

        double out_bound_pdf[100];
        double avg_outbound = 0;

        memcle(out_bound_pdf);
        for (int i = 0; i < n; i++) {
            size_t s = G.out_bound[i].size();
            out_bound_pdf[s] += 1.0;
            avg_outbound += s;
        }

        avg_outbound /= n;
        printf("avg_outbound = %.3f\n", avg_outbound);

        //for (int i = 0; i < 20; i++) {
        //    out_bound_pdf[i] /= n;
        //    printf("outbound[%d] = %.3f\n", i, out_bound_pdf[i]);
        //}
    }

    // if reselect -- return 1
    int neighbor_reselection(int v) {
        double max_lcb = 0;
        int arg_max_lcb = 0;
        double min_ucb = 1e18;
        int arg_min_ucb = 0;

        for (size_t i = 0; i < obs[v].size(); i++) {
            auto lcb_ucb = obs[v][i] -> get_lcb_ucb();
            if (lcb_ucb.first > max_lcb) {
                arg_max_lcb = i;
                max_lcb = lcb_ucb.first;
            }
            if (lcb_ucb.second < min_ucb) {
                arg_min_ucb = i;
                min_ucb = lcb_ucb.second;
            }
        }

        if (max_lcb > min_ucb) {
            int u = obs[v][arg_max_lcb] -> u;
            //auto lcb_ucb = obs[v][arg_max_lcb] -> get_lcb_ucb();
            //int len = obs[v][arg_max_lcb] -> obs.size();

            //auto bst = obs[v][arg_min_ucb] -> get_lcb_ucb();
            //int bst_u = obs[v][arg_min_ucb] -> u;
            //printf("best (%.2f %.2f) (%d, %d), distance = %.2f\n", bst.first, bst.second, bst_u, v, distance(coord[bst_u], coord[v]));
            //printf("worst (%.2f %.2f) (%d, %d), distance = %.2f\n", lcb_ucb.first, lcb_ucb.second, u, v, distance(coord[u], coord[v]));
            G.del_edge(u, v);

            int new_u = random_num(n);
            while (G.out_bound[new_u].size() >= max_outbound || G.add_edge(new_u, v) == false)
                new_u = random_num(n);

            obs[v][arg_max_lcb].reset(new perigee_observation(new_u, v));
            return 1;
        }
        return 0;
    }
        
    vector<int> respond(message msg)  {
        int u = msg.dst;
        vector<int> nb_u = G.outbound(u);
        vector<int> ret;
        int cnt = 0;
        for (auto v : nb_u) 
            if (v != msg.src) {
                ret.push_back(v);
                cnt++;
            }

        if (msg.step == 0) {
            //mt19937 rng(u);
            int remain_deg = root_fanout - ret.size();
            for (int i = 0; i < remain_deg; i++) {
                int v = rng() % n;
                if (u != v && std::find(ret.begin(), ret.end(), v) == ret.end()) {
                    ret.push_back(v);
                }
            }
        }
        return ret;
    }

    static const char* get_algo_name() {return algo_name;} 
    void print_info() {
        G.print_info();
    }
};



template<int fanout = FANOUT>
class block_p2p : public basic_algo {
// block p2p
// firstly build K clusters (K = 8)
// Inside a cluster, it connects Chord-type graph
// Every cluster has one entry point. One entry point connects to all other entry points.

  private: 
    graph G; // random graph
    static constexpr int random_out = fanout / 2;
    static constexpr int dist_out = fanout - random_out;
    static constexpr const char* algo_name = "blockp2p";


  public: 
    const static bool specified_root = false;
    block_p2p(int n, LatLonCoordinate *coord, int root = 0) : G(n) {
        // the first node in every cluster's list is the entry points
        for (int i = 0; i < K; i++)
            for (int j = 0; j < K; j++)
                if (i != j) {
                    G.add_edge(cluster_list[i][0], cluster_list[j][0]);
                }
            
        // connect a Chord-type graph
        for (int i = 0; i < K; i++) {
            int cn = cluster_cnt[i];
            for (int j = 0; j < cn; j++) {
                int u = cluster_list[i][j];
                if (cn <= 8) {
                    // if the cluster size is small, connect it as a fully-connected graph
                    for (auto v : cluster_list[i])
                        if (u != v)
                            G.add_edge(u, v);
                } else {
                    // Chord-type graph
                    for (int k = 1; k < cn; k *= 2)  
                        G.add_edge(u, cluster_list[i][(j + k) % cn]); // connect u and (u + 2^k) mod cn
                    G.add_edge(u, cluster_list[i][(j + cn / 2) % cn]); // connect the diagonal
                }

            }
        }
    }
        
    vector<int> respond(message msg)  {
        int u = msg.dst;
        vector<int> nb_u = G.outbound(u);
        vector<int> ret;
        //int cnt = 0;
        for (auto v : nb_u) 
            if (v != msg.src) {
                ret.push_back(v);
            }
        return ret;
    }

    static const char* get_algo_name() {return algo_name;} 
    void print_info() {
        G.print_info();
    }
};



class test_result {
  public : 
    double avg_bnd;
    double avg_latency;
    vector<double> latency;
    double depth_cdf[MAX_DEPTH];
    double avg_dist[MAX_DEPTH];

    vector<double> cluster_avg_latency;
    vector<double> cluster_avg_depth;

    test_result() : avg_bnd(0), avg_latency(0), latency(21, 0), 
        cluster_avg_latency(21, 0),
        cluster_avg_depth(21, 0) {
        memcle(depth_cdf);
        memcle(avg_dist);
    }
    void print_info() {
        fprintf(stderr, "bandwidth");
        for (int i = 0; i < 21; i++)
            fprintf(stderr, ", %.2f", i * 0.05);
        fprintf(stderr, "\n");
        fprintf(stderr, "%.2f", avg_bnd);
        for (int i = 0; i < 21; i++)
            fprintf(stderr, ", %.2f", latency[i]);
        fprintf(stderr, "\n");
    }
};

template <class algo_T>
test_result single_root_simulation(int root, int rept_time, double mal_node, shared_ptr<algo_T> algo) {
// Test the latency of the message originated from [root].
// 1) Use a global heap to maintain the message queue and fetch the next delivered message.
// 2) For every delivered message, ignore it if it is a duplicated message.
// 3) Otherwise, invoke algo_T's respond function to get the relay node list.
// 4) Then create new messages to the relay nodes.

// Delay model: 
// When a node receives a message, it has 50ms delay to handle it. Then it sends to other nodes without delay.

    std::default_random_engine generator;
    std::normal_distribution<double> rand_latency(50.0, 10.0);

    test_result result;

    // initialize test algorithm class if it needs a specific root
    if (algo_T::specified_root == true) {
        algo.reset(new algo_T(n, coord, root));
    }
    algo -> set_root(root);

    for (int rept = 0; rept < rept_time; rept++)  {

        priority_queue<message, vector<message>, greater<message> > msg_queue;
        msg_queue.push(message(root, root, root, 0, 0, 0)); // initial message

        memcle(recv_flag);
        memcle(recv_time);
        memcle(recv_dist);
        memset(recv_parent, -1, sizeof(recv_parent));
        memcle(depth);
        vector<int> recv_list;

        int dup_msg = 0;

        for (; !msg_queue.empty(); ) {
            message msg = msg_queue.top();
            msg_queue.pop();

            int u = msg.dst; // current node


            // duplicate msg -- ignore
            if (recv_flag[u] == true) {
                dup_msg++;
                continue;
            }
            //msg.print_info();

            recv_flag[u] = true;
            recv_time[u] = msg.recv_time;
            recv_dist[u] = msg.recv_time - msg.send_time;
            recv_parent[u] = msg.src;
            recv_list.push_back(u);
            if (u != root)
                depth[u] = depth[msg.src] + 1;

            // malicious node -- no response
            if (mal_flag[u] == true) continue;

            auto relay_list = (*algo).respond(msg);
           double Datalatency = ((DATA_SIZE*8 )/ BANDWIDTH) * 1000;  // 转换为ms
            double delay_time = (FIXED_DELAY - 50) + std::min(std::max(rand_latency(generator), 0.0), 100.0);  // avg is 250ms, in simulation: make it 200ms + Gaussian(50, 10)
            for (auto v: relay_list) {
                double dist = distance(coord[u], coord[v]) * 3+ Datalatency;
                if (msg.step == 0) {
                    dist = distance(coord[u], coord[v]) * 3+ Datalatency;
                }
                message new_msg = message(root, u, v, msg.step + 1, recv_time[u] + delay_time, recv_time[u] + dist + delay_time);
                msg_queue.push(new_msg);
            }
        }

        int cluster_recv_count[10];
        memcle(cluster_recv_count);

        int recv_count = 0;
        double avg_latency = 0;

        for (int i = 0; i < n; i++)
            if (recv_flag[i] == false && mal_flag[i] == false) {
                //printf("not receive %d\n", i);
                recv_time[i] = inf;
                recv_list.push_back(i);
                depth[i] = MAX_DEPTH - 1; //uncovered node
            } else {
                recv_count++;
                avg_latency += recv_time[i];

                int c = cluster_result[i];
                cluster_recv_count[c]++;
                result.cluster_avg_depth[c] += depth[i];
                result.cluster_avg_latency[c] += recv_time[i];
            }

        avg_latency /= recv_count;
        for (int c = 0; c < K; c++) {
            result.cluster_avg_depth[c] /= cluster_recv_count[c];
            result.cluster_avg_latency[c] /= cluster_recv_count[c];
        }


        int non_mal_node = recv_list.size();
        result.avg_bnd += (double(dup_msg + non_mal_node) / (non_mal_node));
        int depth_cnt[100];
        memcle(depth_cnt);

        for (int u: recv_list) {
            result.depth_cdf[depth[u]] += 1;
            result.avg_dist[depth[u]] += recv_dist[u];
            depth_cnt[depth[u]] += 1;
        }

        result.avg_latency = avg_latency;

        for (int i = 0; i < MAX_DEPTH; i++) {
            result.depth_cdf[i] /= non_mal_node;
            result.avg_dist[i] /= depth_cnt[i];
        }

        int cnt = 0;
        for (double pct = 0.05; pct <= 1; pct += 0.05, cnt++) {
            int i = non_mal_node * pct;
            result.latency[cnt] += recv_time[recv_list[i]];
        }

    }


    result.avg_bnd /= rept_time; 
    for (int i = 0; i < MAX_DEPTH; i++) 
        result.depth_cdf[i] /= rept_time; 
    for (size_t i = 0; i < result.latency.size(); i++) {
        double tmp = int(result.latency[i] / inf);
        result.latency[i] -= tmp * inf;
        if (rept_time - tmp == 0)
            result.latency[i] = 0;
        else
            result.latency[i] /= (rept_time - tmp);

        if (result.latency[i] < 0.1)
            result.latency[i] = inf;
    }


    // Print the tree structure (only when the root is 0)

    if (algo_T::get_algo_name() == "cluster") {
        FILE* pf = fopen("tree_struct.txt", "w");
        if (pf != NULL) {
            fprintf(pf, "%d %d\n", n, root);
            for (int i = 0; i < n; i++) {
                fprintf(pf, "%d\n", recv_parent[i]);
            }
        } else 
            fprintf(stderr, "cannot open tree_struct.txt\n");
    }
              
    return result;
}

template <class algo_T>
test_result simulation(int rept_time = 1, double mal_node = 0.0) {

// Test the latency and duplication rate for the whole network.
// Firstly ranomly select some malicious nodes.
// Then, for every honest node, do a single_root_simulation.

    srand(100);

    test_result result;

    FILE* output = fopen("sim_output.csv", "a");
    if (output == NULL) {
        fprintf(stderr, "cannot open file\n");
        return result;
    }

    int test_time = 0;
    for (int rept = 0; rept < rept_time; rept++) {
        //fprintf(stderr, "rept %d\n", rept);
        // 1) generate malicious node list
        memcle(mal_flag);
        for (int i = 0; i < mal_node * n; i++){
            int picked_num = random_num(n);
            while (mal_flag[picked_num] == true)  
                picked_num = random_num(n);
            mal_flag[picked_num] = true;
        }

        // 2) simulate the message at source i
        int test_node = 20;

        shared_ptr<algo_T> algo(new algo_T(n, coord, 0)); // initialize an algo instance, regardless of the root
        for (; test_node > 0; test_node--) {
            printf("%d\n", test_node);
            int root = rand() % n;
            while (mal_flag[root] == true) root = rand() % n;
            test_time++;
            auto res = single_root_simulation<algo_T>(root, 1, mal_node, algo);
            //printf("%d\n", test_node);
            result.avg_bnd += res.avg_bnd;
            for (size_t i = 0; i < result.latency.size(); i++) {
                result.latency[i] += res.latency[i];
            }
            for (int i = 0; i < MAX_DEPTH; i++) {
                result.depth_cdf[i] += res.depth_cdf[i];
                result.avg_dist[i] += res.avg_dist[i];
            }
            result.avg_latency += res.avg_latency;

            for (int c = 0; c < K; c++) {
                result.cluster_avg_depth[c] += res.cluster_avg_depth[c];
                result.cluster_avg_latency[c] += res.cluster_avg_latency[c];
            }
        }
    }

    result.avg_latency /= test_time;
    result.avg_bnd /= test_time;
    for (int c = 0; c < K; c++) {
        result.cluster_avg_depth[c] /= test_time;
        result.cluster_avg_latency[c] /= test_time;
    }

    for (size_t i = 0; i < result.latency.size(); i++) {
        double tmp = int(result.latency[i] / inf);
        result.latency[i] -= tmp * inf;
        result.latency[i] /= (test_time - tmp);
        if (test_time - tmp == 0)
            result.latency[i] = 0;
    }
    for (int i = 0; i < MAX_DEPTH; i++) {
        result.depth_cdf[i] /= test_time;
        result.avg_dist[i] /= test_time;
    }

    //fprintf(stderr, "latency sum at 0.95 %.2f\n", result.latency[19]);
    fprintf(output, "%s\n", algo_T::get_algo_name());
    printf("%s\n", algo_T::get_algo_name());
    fprintf(output, "#node, mal node, Bandwidth, ");
    printf("#node, mal node, Bandwidth, ");
    for (double p = 0.05; p <= 1; p += 0.05) {
        fprintf(output, "%.2f, ", p);
        printf("%.2f, ", p);
    }
    fprintf(output, "\n");
    printf("\n");

    fprintf(output, "%d, %.2f, %.2f, ", n, mal_node, result.avg_bnd);
    printf("%d, %.2f, %.2f, ", n, mal_node, result.avg_bnd);
    //printf
    int cnt = 0;
    for (double p = 0.05; p <= 1; p += 0.05, cnt++) {
        fprintf(output, "%.2f, ", result.latency[cnt]);
        printf("%.2f, ", result.latency[cnt]);
    }
    fprintf(output, "\n");
    printf("\n");

    fprintf(output, "depth pdf\n");
    printf("depth pdf\n");
    for (int i = 0; i < MAX_DEPTH; i++) {
        fprintf(output, "%d, ", i);
        printf("%d, ", i);
    }
    fprintf(output, "\n");
    printf("\n");

    double avg = 0;
    for (int i = 0; i < MAX_DEPTH; i++) {
        fprintf(output, "%.4f, ", result.depth_cdf[i]);
        printf("%.4f, ", result.depth_cdf[i]);
        avg += result.depth_cdf[i] * i;
    }
    fprintf(output, "\n");
    printf("\n");

    fprintf(output, "avg depth = %.2f\n", avg);
    printf("avg depth = %.2f\n", avg);
    fprintf(output, "avg latency = %.2f\n", result.avg_latency);
    printf("avg latency = %.2f\n", result.avg_latency);

    fprintf(output, "cluster avg depth\n");
    printf("cluster avg depth\n");
    for (int i = 0; i < K; i++) {
        fprintf(output, "%.2f, ", result.cluster_avg_depth[i]);
        printf("%.2f, ", result.cluster_avg_depth[i]);
    }
    fprintf(output, "\n");
    printf("\n");

    fprintf(output, "cluster avg latency\n");
    printf("cluster avg latency\n");
    for (int i = 0; i < K; i++) {
        fprintf(output, "%.2f, ", result.cluster_avg_latency[i]);
        printf("%.2f, ", result.cluster_avg_latency[i]);
    }
    fprintf(output, "\n");
    printf("\n");

    fprintf(output, "avg distance by depth\n");
    printf("avg distance by depth\n");
    for (int i = 0; i < MAX_DEPTH; i++) {
        fprintf(output, "%.2f, ", result.avg_dist[i]);
        printf("%.2f, ", result.avg_dist[i]);
    }
    fprintf(output, "\n");
    printf("\n");

    fclose(output);



    fig_csv = fopen("fig.csv", "a");
    if (fig_csv == NULL) {
        fprintf(stderr, "cannot open file\n");
        return result;
    }


    fprintf(fig_csv, "%s, ", algo_T::get_algo_name());
    cnt = 0;
    for (double p = 0.05; p <= 1; p += 0.05, cnt++) {
        fprintf(fig_csv, "%.2f, ", result.latency[cnt]);
        printf("%.2f, ", result.latency[cnt]);
    }
    fprintf(fig_csv, "\n");

    fclose(fig_csv);

    return result;
}

void init() { 
    // Read the geo information from input.
    n = 0;
    FILE* f = fopen("Geo.txt", "r");
    fscanf(f, "%d", &n);
    for (int i = 0; i < n; i++) {
        fscanf(f, "%lf%lf", &coord[i].lat, &coord[i].lon);
    }

    n = std::min(n, MAX_TEST_N);

    fclose(f);
}

// 新增完整的Geohash相关函数
const string BASE32 = "0123456789bcdefghjkmnpqrstuvwxyz";
const int GEO_BITS_PER_CHAR = 5;
// const int GEO_PRECISION = 4; // geohash精度，可调参数
// const int GEO_TOTAL_BITS = GEO_PRECISION * GEO_BITS_PER_CHAR; // geohash总位数
// const int K0_BUCKET_THRESHOLD = 15; // k0桶阈值，超过此值使用k-ary树，可调参数
// const int KARY_FACTOR = 3; // k-ary树的分支因子，可调参数
// const int MAX_BUCKET_SIZE = 10; // 每个桶最大存放节点数，可调参数

// 修改后:
int GEO_PRECISION = 6;  // geohash精度，可调参数
int MAX_BUCKET_SIZE = 8;// 每个桶最大存放节点数，可调参数
int K0_BUCKET_THRESHOLD = 9999;// k0桶阈值，超过此值使用k-ary树，可调参数
int KARY_FACTOR = 3; // k-ary树的分支因子，可调参数
int GEO_TOTAL_BITS = GEO_PRECISION * GEO_BITS_PER_CHAR; // geohash总位数

// 前缀树节点结构，用于快速查找特定前缀的节点
struct GeoPrefixNode {
    string prefix;
    vector<int> nodeIds; // 包含该前缀的节点列表
    map<char, GeoPrefixNode*> children; // 子节点
    
    GeoPrefixNode(const string& p) : prefix(p) {}
    ~GeoPrefixNode() {
        for (auto& pair : children) {
            delete pair.second;
        }
    }
};

// k-ary树中的消息结构扩展
struct KaryMessage {
    int root_node; // k-ary树的根节点ID
    bool is_kary; // 是否使用k-ary树传播
    
    KaryMessage() : root_node(-1), is_kary(false) {}
    KaryMessage(int root, bool kary) : root_node(root), is_kary(kary) {}
};

// 用于传递给消息的额外信息
KaryMessage kary_msg_info[N];

// 用于Geohash编码的范围结构
struct GeoRange {
    double min, max;
    
    GeoRange() : min(-90.0), max(90.0) {} // 默认为纬度范围
    GeoRange(double _min, double _max) : min(_min), max(_max) {}
    
    double mid() const {
        return (min + max) / 2.0;
    }
};

// 完整的Geohash实现
class Geohash {
public:
    // 生成Geohash
    static string encode(double lat, double lon, int precision = GEO_PRECISION) {
        if (precision <= 0) return "";
        
        // 初始化范围：纬度[-90,90]，经度[-180,180]
        GeoRange latRange(-90.0, 90.0);
        GeoRange lonRange(-180.0, 180.0);
        
        bool isEven = true; // 偶数位编码经度，奇数位编码纬度
        int bit = 0;
        int idx = 0;
        string geohash;
        
        while (geohash.length() < size_t(precision)) {
            if (isEven) {
                // 处理经度
                double mid = lonRange.mid();
                if (lon >= mid) {
                    idx = idx * 2 + 1;
                    lonRange.min = mid;
                } else {
                    idx = idx * 2;
                    lonRange.max = mid;
                }
            } else {
                // 处理纬度
                double mid = latRange.mid();
                if (lat >= mid) {
                    idx = idx * 2 + 1;
                    latRange.min = mid;
                } else {
                    idx = idx * 2;
                    latRange.max = mid;
                }
            }
            
            isEven = !isEven;
            
            // 每5位生成一个字符
            if (++bit == 5) {
                geohash += BASE32[idx];
                bit = 0;
                idx = 0;
            }
        }
        
        return geohash;
    }
    
    // Geohash解码为经纬度
    static pair<double, double> decode(const string& geohash) {
        GeoRange latRange(-90.0, 90.0);
        GeoRange lonRange(-180.0, 180.0);
        bool isEven = true;
        
        for (char c : geohash) {
            int idx = BASE32.find(c);
            if (idx == string::npos) continue;
            
            // 每个字符表示5位二进制
            for (int i = 4; i >= 0; i--) {
                int bit = (idx >> i) & 1;
                
                if (isEven) {
                    // 经度
                    double mid = lonRange.mid();
                    if (bit) {
                        lonRange.min = mid;
                    } else {
                        lonRange.max = mid;
                    }
                } else {
                    // 纬度
                    double mid = latRange.mid();
                    if (bit) {
                        latRange.min = mid;
                    } else {
                        latRange.max = mid;
                    }
                }
                
                isEven = !isEven;
            }
        }
        
        return make_pair(latRange.mid(), lonRange.mid());
    }
    
    // geohash字符转换为5位二进制
    static string charToBits(char c) {
        int idx = BASE32.find(c);
        if (idx == string::npos) idx = 0;
        
        string bits;
        for (int i = 4; i >= 0; i--) {
            bits += ((idx >> i) & 1) ? '1' : '0';
        }
        return bits;
    }
    
    // 将geohash字符串转为二进制
    static string toBinary(const string& hash) {
        string binary;
        for (char c : hash) {
            binary += charToBits(c);
        }
        return binary;
    }
    
    // 相邻区域查找
    static vector<string> getNeighbors(const string& geohash) {
        if (geohash.empty()) return {};
        
        vector<string> neighbors;
        // 北、东北、东、东南、南、西南、西、西北
        const int dx[] = {0, 1, 1, 1, 0, -1, -1, -1};
        const int dy[] = {1, 1, 0, -1, -1, -1, 0, 1};
        
        pair<double, double> center = decode(geohash);
        double lat = center.first;
        double lon = center.second;
        
        // 估算经纬度变化单位
        double latUnit = 180.0 / pow(2, geohash.length() * 2.5);
        double lonUnit = 360.0 / pow(2, geohash.length() * 2.5);
        
        for (int i = 0; i < 8; i++) {
            double neighborLat = lat + dy[i] * latUnit;
            double neighborLon = lon + dx[i] * lonUnit;
            
            // 处理边界情况
            neighborLat = max(-90.0, min(90.0, neighborLat));
            neighborLon = fmod(fmod(neighborLon + 540.0, 360.0) - 180.0, 360.0);
            
            neighbors.push_back(encode(neighborLat, neighborLon, geohash.length()));
        }
        
        return neighbors;
    }
};

// 计算两个二进制字符串的异或距离
unsigned int xorDistance(const string& a, const string& b) {
    unsigned int distance = 0;
    int maxLen = min(a.length(), b.length());
    
    for (int i = 0; i < maxLen; i++) {
        if (a[i] != b[i]) {
            distance += (1 << (maxLen - i - 1));
        }
    }
    return distance;
}

// 获取geohash桶索引
int getGeoBucketIndex(const string& a, const string& b) {
    string binaryA = Geohash::toBinary(a);
    string binaryB = Geohash::toBinary(b);
    
    unsigned int dist = xorDistance(binaryA, binaryB);
    if (dist == 0) return 0;
    
    int idx = 0;
    while (dist > 0) {
        dist >>= 1;
        idx++;
    }
    return idx;
}

// 将所有节点的geohash打印到文件
void printGeohashToFile(const string node_geohash[], int n, const char* filename) {
    FILE* f = fopen(filename, "w");
    if (f == NULL) {
        fprintf(stderr, "Cannot open file %s for writing\n", filename);
        return;
    }
    
    fprintf(f, "NodeID,Geohash\n");
    for (int i = 0; i < n; i++) {
        fprintf(f, "%d,%s\n", i, node_geohash[i].c_str());
    }
    
    fclose(f);
    printf("Geohash information written to %s\n", filename);
}

// 计算k-ary树中节点的子节点
vector<int> computeKaryChildren(int nodeIdx, int totalNodes, int k) {
    vector<int> children;
    for (int i = 1; i <= k; i++) {
        int childIdx = nodeIdx * k + i;
        if (childIdx < totalNodes) {
            children.push_back(childIdx);
        }
    }
    return children;
}

// 将k桶信息导出到文件
void exportKBucketsToFile(const vector<vector<vector<int>>>& kbuckets, int n, const string node_geohash[], const char* filename) {
    FILE* f = fopen(filename, "w");
    if (!f) {
        fprintf(stderr, "Cannot open file %s for writing\n", filename);
        return;
    }
    
    fprintf(f, "NodeID,Geohash,BucketID,BucketSize,BucketNodes\n");
    
    // 限制导出节点数以避免文件过大
    int max_nodes = min(1000, n);
    printf("Exporting k-bucket info for %d nodes to %s...\n", max_nodes, filename);
    
    int total_buckets = 0;
    int empty_buckets = 0;
    
    for (int i = 0; i < max_nodes && i < (int)kbuckets.size(); i++) {
        for (size_t j = 0; j < kbuckets[i].size(); j++) {
            total_buckets++;
            if (kbuckets[i][j].empty()) {
                empty_buckets++;
                fprintf(f, "%d,%s,%lu,0,\n", i, node_geohash[i].c_str(), j);
            } else {
                fprintf(f, "%d,%s,%lu,%lu,", i, node_geohash[i].c_str(), j, kbuckets[i][j].size());
                for (size_t k = 0; k < kbuckets[i][j].size(); k++) {
                    fprintf(f, "%d", kbuckets[i][j][k]);
                    if (k < kbuckets[i][j].size() - 1) {
                        fprintf(f, "|");
                    }
                }
                fprintf(f, "\n");
            }
        }
        
        if (i % 100 == 0) {
            printf("Exported %d/%d nodes (%.1f%%)\n", i, max_nodes, i * 100.0 / max_nodes);
        }
    }
    
    fprintf(f, "\nSummary:\n");
    fprintf(f, "Total buckets analyzed: %d\n", total_buckets);
    fprintf(f, "Empty buckets: %d (%.1f%%)\n", empty_buckets, empty_buckets * 100.0 / total_buckets);
    
    fclose(f);
    printf("K-bucket information exported to %s\n", filename);
}

// MERCATOR算法实现
template <int root_fanout = ROOT_FANOUT, int second_fanout = SECOND_FANOUT, 
          int fanout = FANOUT, int kBucketSize = MAX_BUCKET_SIZE, 
          int karyFactor = KARY_FACTOR>
class mercator : public basic_algo {
private:
    graph G; // 底层网络拓扑
    string node_geohash[N]; // 每个节点的geohash
    string node_geohash_binary[N]; // 每个节点geohash的二进制形式
    vector<vector<vector<int>>> k_buckets; // 每个节点的k桶
    unordered_map<string, vector<int>> geohash_groups; // 按geohash分组的节点
    GeoPrefixNode* prefix_tree_root; // Geohash前缀树根节点
    int tree_root; // 广播树根节点
    static constexpr const char* algo_name = "mercator";
    bool visited[N][MAX_DEPTH + 1]; // 记录节点在特定步骤是否已访问
    
    // 构建geohash前缀树
    void buildPrefixTree() {
        prefix_tree_root = new GeoPrefixNode("");
        
        for (int i = 0; i < G.n; i++) {
            string hash = node_geohash[i];
            GeoPrefixNode* curr = prefix_tree_root;
            
            // 将节点添加到所有相应的前缀节点
            string prefix = "";
            for (char c : hash) {
                prefix += c;
                if (curr->children.find(c) == curr->children.end()) {
                    curr->children[c] = new GeoPrefixNode(prefix);
                }
                curr = curr->children[c];
                curr->nodeIds.push_back(i);
            }
        }
    }
    
    // 查找具有特定前缀的所有节点
    vector<int> findNodesWithPrefix(const string& prefix) {
        GeoPrefixNode* curr = prefix_tree_root;
        
        for (char c : prefix) {
            if (curr->children.find(c) == curr->children.end()) {
                return vector<int>(); // 前缀不存在
            }
            curr = curr->children[c];
        }
        
        return curr->nodeIds;
    }
    
    // 判断节点是否在k-ary树中需要转发消息
    bool shouldForwardInKaryTree(int src, int dst, int karyRoot, int k_factor) {
        vector<int> sameGeohashNodes = geohash_groups[node_geohash[karyRoot]];
        
        // 对同一geohash组内的节点排序，确保有稳定的k-ary树结构
        sort(sameGeohashNodes.begin(), sameGeohashNodes.end());
        
        // 找到src和dst在有序列表中的位置
        auto srcPos = find(sameGeohashNodes.begin(), sameGeohashNodes.end(), src);
        auto dstPos = find(sameGeohashNodes.begin(), sameGeohashNodes.end(), dst);
        
        if (srcPos == sameGeohashNodes.end() || dstPos == sameGeohashNodes.end()) {
            return false; // 节点不在同一geohash组中
        }
        
        int srcIdx = distance(sameGeohashNodes.begin(), srcPos);
        int dstIdx = distance(sameGeohashNodes.begin(), dstPos);
        
        // 检查dst是否是src在k-ary树中的子节点
        vector<int> children = computeKaryChildren(srcIdx, sameGeohashNodes.size(), k_factor);
        return find(children.begin(), children.end(), dstIdx) != children.end();
    }
    
    // 填充k桶
    void fillKBuckets() {
        printf("Generating geohashes... ");
        auto start_time = chrono::steady_clock::now();
        int total_nodes = G.n;
        
        // 生成所有节点的geohash
        for (int i = 0; i < total_nodes; i++) {
            node_geohash[i] = Geohash::encode(coord[i].lat, coord[i].lon, GEO_PRECISION);
            node_geohash_binary[i] = Geohash::toBinary(node_geohash[i]);
            geohash_groups[node_geohash[i]].push_back(i);
            
            if (i % 500 == 0) {
                auto now = chrono::steady_clock::now();
                auto elapsed = chrono::duration_cast<chrono::seconds>(now - start_time).count();
                if (elapsed > 0) {
                    double progress = i * 100.0 / total_nodes;
                    double remaining = elapsed * (total_nodes - i) / (double)i;
                    printf("\rGenerating geohashes... %.1f%% (ETA: %.0fs)", progress, remaining);
                    fflush(stdout);
                }
            }
        }
        printf("\rGeohashes generated for %d nodes               \n", total_nodes);
        
        // 将geohash信息输出到文件
        printGeohashToFile(node_geohash, total_nodes, "Geohash.txt");
        
        // 初始化k桶
        k_buckets.resize(total_nodes);
        for (int i = 0; i < total_nodes; i++) {
            // 每个节点有GEO_TOTAL_BITS+1个桶 (0到GEO_TOTAL_BITS)
            k_buckets[i].resize(GEO_TOTAL_BITS + 1);
        }
        
        // 构建前缀树
        buildPrefixTree();
        
        // 首先填充K0桶（相同geohash的节点）
        printf("Filling K0 buckets and checking integrity...\n");
        int same_geohash_pairs = 0;
        for (auto& group : geohash_groups) {
            if (group.second.size() > 1) {
                // 将同一geohash组的所有节点互相添加到各自的K0桶中
                for (size_t i = 0; i < group.second.size(); i++) {
                    for (size_t j = 0; j < group.second.size(); j++) {
                        if (i != j) {
                            k_buckets[group.second[i]][0].push_back(group.second[j]);
                            same_geohash_pairs++;
                        }
                    }
                }
            }
        }
        printf("Added %d pairs to K0 buckets\n", same_geohash_pairs);
        
        // 检查k0桶完整性
        printf("Verifying K0 bucket integrity...\n");
        int max_samples = min(100, total_nodes); // 最多检查100个节点样本
        int matched_count = 0;
        int total_count = 0;
        
        for (int i = 0; i < max_samples; i++) {
            int node_idx = (i * total_nodes) / max_samples; // 均匀选择样本
            string hash = node_geohash[node_idx];
            
            // 遍历所有节点，找到具有相同geohash的节点
            for (int j = 0; j < total_nodes; j++) {
                if (j != node_idx && node_geohash[j] == hash) {
                    // 检查j是否在node_idx的k0桶中
                    auto it = find(k_buckets[node_idx][0].begin(), k_buckets[node_idx][0].end(), j);
                    if (it != k_buckets[node_idx][0].end()) {
                        matched_count++;
                    }
                    total_count++;
                }
            }
        }
        
        if (total_count > 0) {
            printf("K0 bucket integrity check: %d/%d (%.1f%%) correct entries found\n", 
                   matched_count, total_count, matched_count * 100.0 / total_count);
        } else {
            printf("No nodes with identical geohashes found in samples\n");
        }
        
        // 然后填充其他k桶
        printf("Filling other K buckets...\n");
        
        auto fill_start = chrono::steady_clock::now();
        int connections = 0;
        
        for (int i = 0; i < total_nodes; i++) {
            string bin_i=node_geohash_binary[i];
            // 对于每个节点，填充其k1到kN桶
            for (int bucket_idx = 1; bucket_idx <= GEO_TOTAL_BITS; bucket_idx++) {
                // 如果桶已经满了，跳过
                if (k_buckets[i][bucket_idx].size() >= kBucketSize) {
                    continue;
                }
                 // 查找满足条件的节点
                vector<pair<double, int>> candidates;
                for (int j = 0; j < total_nodes; j++) {
                    if (i == j) continue;
                        string bin_j = node_geohash_binary[j];

                     // 找出从左往右第一个不同的位
                        int diff_pos = -1;
                         for (int b = 0; b < (int)min(bin_i.size(), bin_j.size()); b++) {
                             if (bin_i[b] != bin_j[b]) {
                                    diff_pos = b;
                                        break;
                                        }
                                }
        // bucket index: 倒数第 diff_pos 位不同
                 int bucket_idx = GEO_TOTAL_BITS - diff_pos;
            if (bucket_idx >= 1 && bucket_idx <= GEO_TOTAL_BITS &&
                 (int)k_buckets[i][bucket_idx].size() < kBucketSize) {
            
                        // 为提高效率可排序再筛选近邻，这里直接加入
                         double dist = distance(coord[i], coord[j]);
                            candidates.push_back({dist, j});


                    k_buckets[i][bucket_idx].push_back(j);
                    connections++;
        }
                }
                    // 按距离排序
                    sort(candidates.begin(), candidates.end());
                    
                    // 选择最近的kBucketSize个节点
                    for (int c = 0; c < min(kBucketSize, (int)candidates.size()); c++) {
                        k_buckets[i][bucket_idx].push_back(candidates[c].second);
                        connections++;
                    }

            }
            
            if (i > 0 && i % 500 == 0) {
                auto now = chrono::steady_clock::now();
                auto elapsed = chrono::duration_cast<chrono::seconds>(now - fill_start).count();
                double progress = i * 100.0 / total_nodes;
                double rate = i / (double)max(1, (int)elapsed);
                double eta = (total_nodes - i) / rate;
                
                printf("\rFilling K buckets... %.1f%% (%d/%d nodes, %d connections, %.1f nodes/s, ETA: %.0fs)", 
                       progress, i, total_nodes, connections, rate, eta);
                fflush(stdout);
            }
        }
        
        printf("\rK buckets filled for %d nodes (%d connections)           \n", total_nodes, connections);
        
        // 构建网络连接
        printf("Building network connections...\n");
        auto connect_start = chrono::steady_clock::now();
        int edges = 0;
        int timeout_seconds = 180; // 超时时间，3分钟
        bool timeout = false;
        
        for (int i = 0; i < total_nodes && !timeout; i++) {
            // 从每个桶添加所有邻居
            for (size_t bucket_idx = 0; bucket_idx < k_buckets[i].size(); bucket_idx++) {
                for (int neighbor : k_buckets[i][bucket_idx]) {
                    if (G.add_edge(i, neighbor)) {
                        edges++;
                    }
                }
                
                // 添加至少一条边，防止节点孤立
                if (bucket_idx == k_buckets[i].size() - 1 && G.out_bound[i].empty() && total_nodes > 1) {
                    int random_node = i;
                    while (random_node == i) {
                        random_node = random_num(total_nodes);
                    }
                    if (G.add_edge(i, random_node)) {
                        edges++;
                    }
                }
            }
            
            if (i > 0 && i % 100 == 0) {
                auto now = chrono::steady_clock::now();
                auto elapsed = chrono::duration_cast<chrono::seconds>(now - connect_start).count();
                
                // 检查是否超时
                if (elapsed > timeout_seconds) {
                    printf("\nTimeout reached after %d seconds. Processed %d/%d nodes.\n", 
                           (int)elapsed, i, total_nodes);
                    timeout = true;
                    break;
                }
                
                double progress = i * 100.0 / total_nodes;
                double rate = i / (double)max(1, (int)elapsed);
                double eta = (total_nodes - i) / rate;
                
                printf("\rBuilding connections... %.1f%% (%d/%d nodes, %d edges, %.1f nodes/s, ETA: %.0fs)", 
                       progress, i, total_nodes, edges, rate, eta);
                fflush(stdout);
            }
        }
        
        printf("\rNetwork connections built: %d edges                      \n", edges);
        
        // 导出k桶信息到文件
        exportKBucketsToFile(k_buckets, total_nodes, node_geohash, "MercatorKbu.txt");
    }

public:
    const static bool specified_root = true;
    
    mercator(int n, LatLonCoordinate *coord, int root = 0) : G(n), tree_root(root) {
        // 填充k桶并构建网络连接
        fillKBuckets();
        
        // 初始化访问标记
        memset(visited, 0, sizeof(visited));
    }
    
    void set_root(int _root) override {
        tree_root = _root;
    }
    
    vector<int> respond(message msg) override {
        int u = msg.dst; // 当前节点
        vector<int> relay_nodes;
        
        // 如果是第一次看到消息，标记为已访问
        if (!visited[u][msg.step]) {
            visited[u][msg.step] = true;
            
            // 如果是消息源节点(发起广播的节点)
            if (msg.step == 0) {
                // 第一步：处理K0桶（相同geohash的节点）
                if (k_buckets[u][0].size() <= K0_BUCKET_THRESHOLD) {
                    // K0桶节点数量少，直接flooding
                    for (int v : k_buckets[u][0]) {
                        if (v != msg.src) {
                            relay_nodes.push_back(v);
                        }
                    }
                } else {
                    // K0桶节点数量多，使用k-ary树
                    // 获取与u有相同geohash的节点列表
                    vector<int> sameGeohashNodes = geohash_groups[node_geohash[u]];
                    sort(sameGeohashNodes.begin(), sameGeohashNodes.end());
                    
                    // 找到u在列表中的位置
                    auto pos = find(sameGeohashNodes.begin(), sameGeohashNodes.end(), u);
                    if (pos != sameGeohashNodes.end()) {
                        int uIdx = distance(sameGeohashNodes.begin(), pos);
                        
                        // 计算k-ary树的子节点
                        vector<int> children = computeKaryChildren(uIdx, sameGeohashNodes.size(), karyFactor);
                        for (int childIdx : children) {
                            if (childIdx < sameGeohashNodes.size()) {
                                int v = sameGeohashNodes[childIdx];
                                if (v != msg.src) {
                                    relay_nodes.push_back(v);
                                    kary_msg_info[v] = KaryMessage(u, true);
                                }
                            }
                        }
                    }
                }
                
                // 第二步：从每个非K0桶中选择节点进行传播
                for (size_t bucket_idx = 1; bucket_idx < k_buckets[u].size(); bucket_idx++) {
                    int count = 0;
                    for (int v : k_buckets[u][bucket_idx]) {
                        if (v != msg.src && count < fanout) {
                            relay_nodes.push_back(v);
                            count++;
                        }
                        if (count >= fanout) break;
                    }
                }
                
                // // 如果是树根且中继节点数量不足，添加随机节点
                // if (u == tree_root && relay_nodes.size() < root_fanout) {
                //     int remain = root_fanout - relay_nodes.size();
                //     for (int i = 0; i < remain; i++) {
                //         int v = rand() % G.n;
                //         if (v != u && find(relay_nodes.begin(), relay_nodes.end(), v) == relay_nodes.end()) {
                //             relay_nodes.push_back(v);
                //         }
                //     }
                // }
            } else {
                // 非消息源节点
                
                // 首先检查是否是k-ary树传播
                if (kary_msg_info[u].is_kary) {
                    int karyRoot = kary_msg_info[u].root_node;
                    vector<int> sameGeohashNodes = geohash_groups[node_geohash[karyRoot]];
                    sort(sameGeohashNodes.begin(), sameGeohashNodes.end());
                    
                    auto pos = find(sameGeohashNodes.begin(), sameGeohashNodes.end(), u);
                    if (pos != sameGeohashNodes.end()) {
                        int uIdx = distance(sameGeohashNodes.begin(), pos);
                        
                        // 计算k-ary树的子节点
                        vector<int> children = computeKaryChildren(uIdx, sameGeohashNodes.size(), karyFactor);
                        for (int childIdx : children) {
                            if (childIdx < sameGeohashNodes.size()) {
                                int v = sameGeohashNodes[childIdx];
                                if (v != msg.src) {
                                    relay_nodes.push_back(v);
                                    kary_msg_info[v] = KaryMessage(karyRoot, true);
                                }
                            }
                        }
                    }
                } else {
                    // 常规传播：处理k0桶
                    if (k_buckets[u][0].size() <= K0_BUCKET_THRESHOLD) {
                        // K0桶flooding
                        for (int v : k_buckets[u][0]) {
                            if (v != msg.src) {
                                relay_nodes.push_back(v);
                            }
                        }
                    } else {
                        // K0桶k-ary树
                        vector<int> sameGeohashNodes = geohash_groups[node_geohash[u]];
                        sort(sameGeohashNodes.begin(), sameGeohashNodes.end());
                        
                        auto pos = find(sameGeohashNodes.begin(), sameGeohashNodes.end(), u);
                        if (pos != sameGeohashNodes.end()) {
                            int uIdx = distance(sameGeohashNodes.begin(), pos);
                            
                            vector<int> children = computeKaryChildren(uIdx, sameGeohashNodes.size(), karyFactor);
                            for (int childIdx : children) {
                                if (childIdx < sameGeohashNodes.size()) {
                                    int v = sameGeohashNodes[childIdx];
                                    if (v != msg.src) {
                                        relay_nodes.push_back(v);
                                        kary_msg_info[v] = KaryMessage(u, true);
                                    }
                                }
                            }
                        }
                    }
                }
                
                // 获取消息源所在的桶号
                int src_bucket = getGeoBucketIndex(node_geohash[u], node_geohash[msg.src]);
                
                // 从小于src_bucket的桶中选择节点转发
                for (int bucket_idx = 1; bucket_idx < src_bucket; bucket_idx++) {
                    int count = 0;
                    for (int v : k_buckets[u][bucket_idx]) {
                        if (v != msg.src && count < fanout) {
                            relay_nodes.push_back(v);
                            count++;
                        }
                        if (count >= fanout) break;
                    }
                }
            }
        }
        
        return relay_nodes;
    }
    
    static const char* get_algo_name() { return algo_name; }
    
    void print_info() {
        G.print_info();
    }
};

// 为mercator算法添加专用的模拟函数，避免重复构建k桶
template <int root_fanout = ROOT_FANOUT, int second_fanout = SECOND_FANOUT, 
          int fanout = FANOUT, int kBucketSize = MAX_BUCKET_SIZE, 
          int karyFactor = KARY_FACTOR>
test_result mercatorsimulation(int rept_time = 1, double mal_node = 0.0) {
    // 确保只能用于mercator算法
    typedef mercator<root_fanout, second_fanout, fanout, kBucketSize, karyFactor> mercator_type;
    
    srand(100);
    test_result result;

    FILE* output = fopen("mercator_sim_output.csv", "a");
    if (output == NULL) {
        fprintf(stderr, "cannot open file\n");
        return result;
    }
    
    // 额外输出fig.csv文件，用于绘制图形
    FILE* fig_output = fopen("fig.csv", "a");
    if (fig_output == NULL) {
        fprintf(stderr, "cannot open fig.csv\n");
        fclose(output);
        return result;
    }

    printf("开始MERCATOR模拟，总共%d次重复测试...\n", rept_time);
    
    int test_time = 0;
    for (int rept = 0; rept < rept_time; rept++) {
        // 1) 生成恶意节点列表
        memcle(mal_flag);
        for (int i = 0; i < mal_node * n; i++){
            int picked_num = random_num(n);
            while (mal_flag[picked_num] == true)  
                picked_num = random_num(n);
            mal_flag[picked_num] = true;
        }

        // 2) 初始化一个mercator实例并只构建一次k桶
        shared_ptr<mercator_type> algo(new mercator_type(n, coord, 0));
        printf("已构建完成k桶，开始模拟测试...\n");
        
        // 3) 使用该实例进行多次不同根节点的测试
        int test_node = 20;
        for (; test_node > 0; test_node--) {
            printf("剩余测试节点数: %d\n", test_node);
            int root = rand() % n;
            while (mal_flag[root] == true) root = rand() % n;
            test_time++;
            
            // 4) 使用mercator_single_root_simulation函数，传入已构建k桶的algo实例
            auto res = mercator_single_root_simulation(root, 1, mal_node, algo);
            
            // 累积结果
            result.avg_bnd += res.avg_bnd;
            for (size_t i = 0; i < result.latency.size(); i++) {
                result.latency[i] += res.latency[i];
            }
            for (int i = 0; i < MAX_DEPTH; i++) {
                result.depth_cdf[i] += res.depth_cdf[i];
                result.avg_dist[i] += res.avg_dist[i];
            }
            result.avg_latency += res.avg_latency;

            for (int c = 0; c < K; c++) {
                result.cluster_avg_depth[c] += res.cluster_avg_depth[c];
                result.cluster_avg_latency[c] += res.cluster_avg_latency[c];
            }
        }
    }

    // 计算平均值
    result.avg_latency /= test_time;
    result.avg_bnd /= test_time;
    for (int c = 0; c < K; c++) {
        result.cluster_avg_depth[c] /= test_time;
        result.cluster_avg_latency[c] /= test_time;
    }

    for (size_t i = 0; i < result.latency.size(); i++) {
        double tmp = int(result.latency[i] / inf);
        result.latency[i] -= tmp * inf;
        result.latency[i] /= (test_time - tmp);
        if (test_time - tmp == 0)
            result.latency[i] = 0;
    }
    for (int i = 0; i < MAX_DEPTH; i++) {
        result.depth_cdf[i] /= test_time;
        result.avg_dist[i] /= test_time;
    }

    // 输出结果到文件
    fprintf(output, "%s\n", "mercator");
    
    // 添加参数信息
    fprintf(output, "GEO_PRECISION=%d, BUCKET_SIZE=%d, K0_THRESHOLD=%d, KARY_FACTOR=%d\n", 
            GEO_PRECISION, kBucketSize, K0_BUCKET_THRESHOLD, karyFactor);
    
    printf("%s\n", "mercator");
    fprintf(output, "#node, mal node, Bandwidth, ");
    printf("#node, mal node, Bandwidth, ");
    for (double p = 0.05; p <= 1; p += 0.05) {
        fprintf(output, "%.2f, ", p);
        printf("%.2f, ", p);
    }
    fprintf(output, "\n");
    printf("\n");

    fprintf(output, "%d, %.2f, %.2f, ", n, mal_node, result.avg_bnd);
    printf("%d, %.2f, %.2f, ", n, mal_node, result.avg_bnd);
    
    int cnt = 0;
    for (double p = 0.05; p <= 1; p += 0.05, cnt++) {
        fprintf(output, "%.2f, ", result.latency[cnt]);
        printf("%.2f, ", result.latency[cnt]);
    }
    fprintf(output, "\n");
    printf("\n");

  // 输出到fig.csv文件，用于绘图
    fprintf(fig_output, "mercator, %d, %.2f, %.2f, GEO=%d, BKT=%d, K0T=%d, KARY=%d, ", 
            n, mal_node, result.avg_bnd, GEO_PRECISION, kBucketSize, K0_BUCKET_THRESHOLD, karyFactor);
 
    for (int i = 0; i < 20; i++) {
        fprintf(fig_output, "%.3f, ", result.latency[i]);
    }
    fprintf(fig_output, "\n");

    // 关闭文件
    fclose(output);
    fclose(fig_output);
    
    printf("MERCATOR模拟完成，结果已写入文件。\n");
    return result;
}

// 为mercator算法优化的单根节点模拟函数
template <int root_fanout, int second_fanout, int fanout, int kBucketSize, int karyFactor>
test_result mercator_single_root_simulation(int root, int rept_time, double mal_node, 
    shared_ptr<mercator<root_fanout, second_fanout, fanout, kBucketSize, karyFactor>> algo) {
    std::default_random_engine generator;
    std::normal_distribution<double> rand_latency(50.0, 10.0);

    test_result result;

    // 设置根节点
    algo->set_root(root);

    for (int rept = 0; rept < rept_time; rept++)  {
        priority_queue<message, vector<message>, greater<message> > msg_queue;
        msg_queue.push(message(root, root, root, 0, 0, 0)); // 初始消息

        memcle(recv_flag);
        memcle(recv_time);
        memcle(recv_dist);
        memset(recv_parent, -1, sizeof(recv_parent));
        memcle(depth);
        vector<int> recv_list;

        int dup_msg = 0;

        for (; !msg_queue.empty(); ) {
            message msg = msg_queue.top();
            msg_queue.pop();

            int u = msg.dst; // 当前节点

            // 重复消息 -- 忽略
            if (recv_flag[u] == true) {
                dup_msg++;
                continue;
            }

            recv_flag[u] = true;
            recv_time[u] = msg.recv_time;
            recv_dist[u] = msg.recv_time - msg.send_time;
            recv_parent[u] = msg.src;
            recv_list.push_back(u);
            if (u != root)
                depth[u] = depth[msg.src] + 1;

            // 恶意节点 -- 不响应
            if (mal_flag[u] == true) continue;
            double Datalatency = ((DATA_SIZE*8 )/ BANDWIDTH) * 1000;  // 转换为ms
            auto relay_list = algo->respond(msg);

            double delay_time = (FIXED_DELAY - 50) + std::min(std::max(rand_latency(generator), 0.0), 100.0);  // 平均为250ms，在模拟中：使其为200ms + 高斯分布(50, 10)
            for (auto v: relay_list) {
                double dist = distance(coord[u], coord[v]) *3 +Datalatency ;
                if (msg.step == 0) {
                    dist = distance(coord[u], coord[v]) * 1+Datalatency ;
                }
                message new_msg = message(root, u, v, msg.step + 1, recv_time[u] + delay_time, recv_time[u] + dist + delay_time);
                msg_queue.push(new_msg);
            }
        }

        int cluster_recv_count[10];
        memcle(cluster_recv_count);

        int recv_count = 0;
        double avg_latency = 0;

        for (int i = 0; i < n; i++)
            if (recv_flag[i] == false && mal_flag[i] == false) {
                recv_time[i] = inf;
                recv_list.push_back(i);
                depth[i] = MAX_DEPTH - 1; // 未覆盖节点
            } else {
                recv_count++;
                avg_latency += recv_time[i];

                int c = cluster_result[i];
                cluster_recv_count[c]++;
                result.cluster_avg_depth[c] += depth[i];
                result.cluster_avg_latency[c] += recv_time[i];
            }

        avg_latency /= recv_count;
        for (int c = 0; c < K; c++) {
            result.cluster_avg_depth[c] /= cluster_recv_count[c];
            result.cluster_avg_latency[c] /= cluster_recv_count[c];
        }

        int non_mal_node = recv_list.size();
        result.avg_bnd += (double(dup_msg + non_mal_node) / (non_mal_node));
        int depth_cnt[100];
        memcle(depth_cnt);

        for (int u: recv_list) {
            result.depth_cdf[depth[u]] += 1;
            result.avg_dist[depth[u]] += recv_dist[u];
            depth_cnt[depth[u]] += 1;
        }

        result.avg_latency = avg_latency;

        for (int i = 0; i < MAX_DEPTH; i++) {
            result.depth_cdf[i] /= non_mal_node;
            result.avg_dist[i] /= depth_cnt[i];
        }

        int cnt = 0;
        for (double pct = 0.05; pct <= 1; pct += 0.05, cnt++) {
            int i = non_mal_node * pct;
            result.latency[cnt] += recv_time[recv_list[i]];
        }
    }

    result.avg_bnd /= rept_time; 
    for (int i = 0; i < MAX_DEPTH; i++) 
        result.depth_cdf[i] /= rept_time; 
    for (size_t i = 0; i < result.latency.size(); i++) {
        double tmp = int(result.latency[i] / inf);
        result.latency[i] -= tmp * inf;
        if (rept_time - tmp == 0)
            result.latency[i] = 0;
        else
            result.latency[i] /= (rept_time - tmp);

        if (result.latency[i] < 0.1)
            result.latency[i] = inf;
    }

    // 可选：打印树结构（仅当根为0时）
    if (root == 0) {
        FILE* pf = fopen("mercator_tree_struct.txt", "w");
        if (pf != NULL) {
            fprintf(pf, "%d %d\n", n, root);
            for (int i = 0; i < n; i++) {
                fprintf(pf, "%d\n", recv_parent[i]);
            }
            fclose(pf);
        } else 
            fprintf(stderr, "cannot open mercator_tree_struct.txt\n");
    }
              
    return result;
}
//测试方案参数
void parameter_sweep() {
    init();
    srand(100);
    // 定义要测试的参数范围
    vector<int> geo_precisions = {4,5,6};                // Geohash位数
    vector<int> bucket_sizes = {12};                 // 传播时桶大小
    vector<int> k0_thresholds = {10,15,20,999};                    // k-ary阈值,999代表nok-ary
    vector<int> kary_factors = {2,3};                           // k-ary树的分支因子
    
    int total_tests = geo_precisions.size() * bucket_sizes.size() * k0_thresholds.size() * kary_factors.size();
    int current_test = 0;
    
    printf("开始参数扫描，共%d种参数组合...\n", total_tests);
    
    // 创建汇总文件
    FILE* summary = fopen("parameter_sweep_summary.csv", "w");
    if (!summary) {
        printf("无法创建汇总文件，退出测试\n");
        return;
    }
    
    fprintf(summary, "GEO_PRECISION,BUCKET_SIZE,K0_THRESHOLD,KARY_FACTOR,AVG_LATENCY,AVG_BANDWIDTH\n");
    fclose(summary);
    
    // 清空mercator_sim_output.csv和fig.csv文件，仅在开始时执行一次
    FILE* output = fopen("mercator_sim_output.csv", "w");
    if (output) {
        fprintf(output, "# MERCATOR参数扫描测试结果\n");
        fprintf(output, "# 格式: GEO_PRECISION,BUCKET_SIZE,K0_THRESHOLD,KARY_FACTOR,测试结果...\n\n");
        fclose(output);
    }
    
    FILE* fig_output = fopen("fig.csv", "w");
    if (fig_output) {
        fprintf(fig_output, "# MERCATOR参数扫描结果图表数据\n");
        fprintf(fig_output, "# 格式: algorithm,nodes,mal_node,bandwidth,GEO,BKT,K0T,KARY,延迟数据...\n\n");
        fclose(fig_output);
    }
    
    // 备份原始值
    int orig_geo_precision = GEO_PRECISION;
    int orig_k0_threshold = K0_BUCKET_THRESHOLD;
    
    // 进行参数扫描
    for (int geo_precision : geo_precisions) {
        GEO_PRECISION = geo_precision;  // 直接修改全局变量
        GEO_TOTAL_BITS = geo_precision * GEO_BITS_PER_CHAR;//修改位数
        for (int bucket_size : bucket_sizes) {
            for (int k0_threshold : k0_thresholds) {
                K0_BUCKET_THRESHOLD = k0_threshold;  // 直接修改全局变量
                
                for (int kary_factor : kary_factors) {
                    current_test++;
                    printf("\n测试组合 %d/%d: GEO_PRECISION=%d, BUCKET_SIZE=%d, K0_THRESHOLD=%d, KARY_FACTOR=%d\n", 
                           current_test, total_tests, GEO_PRECISION, bucket_size, k0_threshold, kary_factor);
                    
                    test_result result;
                    
                    // 使用try-catch捕获任何可能的异常
                    try {
                        // 根据参数执行模拟
                        if (kary_factor == 2) {
                            if (bucket_size == 2) {
                                result = mercatorsimulation<128, 8, 8, 2, 2>(1, 0.0);
                            } else if (bucket_size == 4) {
                                result = mercatorsimulation<128, 8, 8, 4, 2>(1, 0.0);
                            } else if (bucket_size == 6) {
                                result = mercatorsimulation<128, 8, 8, 6, 2>(1, 0.0);
                            } else if (bucket_size == 8) {
                                result = mercatorsimulation<128, 8, 8, 8, 2>(1, 0.0);
                            } else if (bucket_size == 10) {
                                result = mercatorsimulation<128, 8, 8, 10, 2>(1, 0.0);
                            }else if (bucket_size == 12) {
                                result = mercatorsimulation<128, 8, 8, 12, 2>(1, 0.0);
                            }else if (bucket_size == 14) {
                                result = mercatorsimulation<128, 8, 8, 14, 2>(1, 0.0);
                            }
                        } else { // kary_factor == 3
                            if (bucket_size == 2) {
                                result = mercatorsimulation<128, 8, 8, 2, 3>(1, 0.0);
                            } else if (bucket_size == 4) {
                                result = mercatorsimulation<128, 8, 8, 4, 3>(1, 0.0);
                            } else if (bucket_size == 6) {
                                result = mercatorsimulation<128, 8, 8, 6, 3>(1, 0.0);
                            } else if (bucket_size == 8) {
                                result = mercatorsimulation<128, 8, 8, 8, 3>(1, 0.0);
                            } else if (bucket_size == 10) {
                                result = mercatorsimulation<128, 8, 8, 10, 3>(1, 0.0);
                            }else if (bucket_size == 12) {
                                result = mercatorsimulation<128, 8, 8, 12, 3>(1, 0.0);
                            }else if (bucket_size == 14) {
                                result = mercatorsimulation<128, 8, 8, 14, 3>(1, 0.0);
                            }
                        }
                        
                        // 添加结果到汇总文件
                        summary = fopen("parameter_sweep_summary.csv", "a");
                        if (summary) {
                            fprintf(summary, "%d,%d,%d,%d,%.6f,%.6f\n", 
                                    geo_precision, bucket_size, k0_threshold, kary_factor,
                                    result.avg_latency, result.avg_bnd);
                            fclose(summary);
                        }
                        
                        printf("参数组合测试完成\n");
                    }
                    catch (const std::exception& e) {
                        printf("测试出错: %s\n", e.what());
                    }
                    catch (...) {
                        printf("测试过程中发生未知错误\n");
                    }
                }
            }
        }
    }
    
    // 恢复原始值
    GEO_PRECISION = orig_geo_precision;
    K0_BUCKET_THRESHOLD = orig_k0_threshold;
    
    printf("\n参数扫描完成！所有测试结果已保存在mercator_sim_output.csv和fig.csv中\n");
    printf("汇总数据在parameter_sweep_summary.csv\n");
}

int main() {
    int rept = 1;
    double mal_node = 0.00;
    init();
    // 运行参数扫描
    //parameter_sweep();
    
    // //MERCATOR - 使用专用优化函数，避免重复构建k桶,桶数量10，k-ary 3
    mercatorsimulation<128, 8, 8, 8, 3>(rept, mal_node);  
    // //MERCURY
    // generate_virtual_coordinate();
    // k_means_based_on_virtual_coordinate();
    // simulation<k_means_cluster<128, 8, 8, true> >(rept, mal_node);

    
 
    // simulation<k_means_cluster<8, 8, 8, true> >(rept, mal_node);

    // //RANDOM
    // simulation<random_flood<8, 8, 8> >(rept, mal_node);

    // //Perigee
    // simulation<perigee_ubc<6, 6, 8> >(rept, mal_node);
    
    // //BlockP2P
    // k_means();
    // simulation<block_p2p<8> >(rept, mal_node);


    return 0;
}


