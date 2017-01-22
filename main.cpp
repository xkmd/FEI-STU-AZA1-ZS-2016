#include <iostream>
#include <set>
#include <string>
#include <map>
#include <stack>
#include <fstream>
#include <algorithm>
#include <vector>
#include <cmath>

using namespace std;
//  AZA:       Zadanie c.1     //
//  Autor:     KMOTORKA Ivan   //
//  ID:        52551           //
//                             //
//  Strucny popis riesenia:    //
//
//  Pri nacitavani aplikujeme Union-Find algoritmus, ktorym urcime jednotlive mnoziny nacitanych bodov.
//  Kazdy potomok ma smernik na "rodica mnoziny", takze vieme, do ktorej patri.

//  Na suradnice jednotlivych rodicov mapujeme vsetkych ich potomkov a aplikujeme Graham scan algoritmus.
//  Dostavame tak redukovany pocet potomkov, ktori tvoria krajne body(obaly) danych mnozin(zhlukov miest).

//  vytvorime si taziskove body jednotlyvych zhlukov a na ne namapujeme vsetkych potomkovpo (graham scane), ktori tam patria

//  Medzi taziskovymi bodmi vytvorime hrany, ktore zosortujeme podla velkosti vzdialenosti a aplikujeme
//  Kruskalov algoritmus. Vytvori sa minimalna kostra stromu.

//  Pre vsetky krajne body, ktorych rodic(taziskovy bod) je spojeny s najblizsim rodicom, vytvorime hrany,
//  zosortujeme podla najmensej vahy(vzdialenosti), ukladame si prve s najmensimi vahami a dostavame tak riesenie.


//  Vzhladom na zvoleny postup riesenia nemusime vzdy dostat minimalnu kostru, ale celkom slusnu aproximaciu.


//  Implementacia:             //


/***********     trieda pre vrchol    ************/

class Vertex {
public:
    Vertex(int x, int y, int rank){
        coords.first = x;
        coords.second = y;
        this->rank = rank;
    }
    
    void setParent(Vertex *parent){
        this->parent = parent;
    }
    Vertex *getParent(){
        return parent;
    }
    pair<int, int> getCoors(){
        return coords;
    }
    int getRank(){
        return rank;
    }
    void setRank(int rank){
        this->rank = rank;
    }
private:
    int rank;
    Vertex *parent;
    pair<int,int> coords;
};

/***********     trieda pre hranu     ************/

class Edge{
private:
    Vertex *v1, *v2;
    double weight;
    
public:
    Edge(){
        
    }
    Edge(Vertex *v1, Vertex *v2, double weight){
        this->v1 = v1;
        this->v2 = v2;
        this->weight = weight;
    }
    void setVertices(Vertex *v1, Vertex *v2){
        this->v1 = v1;
        this->v2 = v2;
    }
    void setWeight(double weight){
        this->weight = weight;
    }
    Vertex* getV1(){
        return v1;
    }
    Vertex* getV2(){
        return v2;
    }
    double getWeight(){
        return weight;
    }
};

//porovnavacia funkcia pre zotriedenie hran podla vahy

bool cmp(Edge *e1, Edge *e2){
    return e1->getWeight() < e2->getWeight();
}


/*********** hlavicky pre Graham scan ************/
stack<pair<int, int> > grahamScan(vector<pair<int,int> > coordspv, long N);
bool POLAR_ORDER(pair<int,int> va, pair<int,int> vb);
int sqrDist(pair<int,int> va, pair<int,int> vb);
int ccw(pair<int,int> va, pair<int,int> vb, pair<int, int> vc);

/***********     trieda pre graf     ************/

class Graph {
public:
    
    // pridavanie vrcholov do mapy vertices, mapuje sa podla paru suradnic
    // + operacia union nad kazdou pridanou dvojicou vrcholov
    void add_vertices(int x1, int y1, int x2, int y2) {
        pair<int, int> c1, c2;
        c1.first = x1;
        c1.second = y1;
        c2.first = x2;
        c2.second = y2;
        // pridanie vrchola
        if(!vertices[c1]){
            add_new_vertex(c1);
        }
        if (!vertices[c2]){
            add_new_vertex(c2);
        }
        // union nad nacitaym parom vrcholov
        make_union(c1, c2, &vertices);
        
    }
    // do setu parents vkladame rodicov vsetkych nacitanych bodov
    // namapujeme si na suradnice rodicov vektory suradnic potomkov
    // pre Graham scan algoritmus
    void prepare_data() {
        for (auto it : vertices) {
            pair<int,int> coords = fs(it.first, &vertices); //najdeme suradnice rodica
            parents.insert(vertices[coords]);    //vlozime rodica do setu
            
            // vlozime suradnice potomkov do vektora mapovaneho na suradnice rodica
            forGraham[coords].push_back(it.first);
        }
    }
    //metoda na pridanie vrcohla do mapy
    void add_new_vertex(pair<int,int> coords) {
        // treti parameter konstruktora je rank - 0 je default koli union find
        vertices[coords] = new Vertex(coords.first, coords.second, 0);
        
        // nastavenie rodica na sameho seba - init koli union find
        vertices[coords]->setParent(vertices[coords]);
    }
    
    
    /***********     union-find algoritmus     ************/
    // kod prevzaty z :
    // https://github.com/mission-peace/interview/blob/master/src/com/interview/graph/DisjointSet.java
    
    bool make_union(pair<int, int> c1, pair<int,int> c2, map< pair<int, int>, Vertex *> *verts){
        // vyberieme vrcholy podla suradnic
        Vertex* vert1 = verts->at(c1);
        Vertex* vert2 = verts->at(c2);
        // nastavime rodicov
        Vertex* parent1 = findSet(vert1);
        Vertex* parent2 = findSet(vert2);
        
        // ak pridu vrcholy s rovnakymi suradnicami neriesime
        if (parent1->getCoors().first == parent2->getCoors().first && parent1->getCoors().second == parent2->getCoors().second) {
            return false;
        }
        // *rank sme pri vkladani nastavili na nulu aby bol
        // kazdy bod rovnocenny, vid add_new_vertex()*
        // porovname ranky rodicov, ak sa rovnaju tak prvemu rank zvysime o 1
        // ak ma prvy vacsi rank ako druhy tak prvemu ponechame jeho rank a druhemu nastavime
        // rodica prveho
        // ak ma prvy rodic mensi rank, tak druhy rodic bude rodic prveho
        
        if (parent1->getRank() >= parent2->getRank()) {
            parent1->setRank((parent1->getRank() == parent2->getRank()) ? parent1->getRank() + 1 : parent1->getRank());
            parent2->setParent(parent1);
        } else {
            parent1->setParent(parent2);
        }
        //cout << vert1->getParent() << " " << verts[c1]->getParent() << " " << vertices[c1]->getParent() <<endl;
        return true;
    }
    
    
    // metoda na ziskanie suradnic najdeneho rodica potomka
    pair<int, int> fs(pair<int, int> coords , map< pair<int, int>, Vertex *> *verts) {
        return findSet(verts->at(coords))->getCoors();
    }
    
    
    // metoda pre najdenie rodica, vlozime vrchol, opakujeme kym nenarazime
    // na rodica, vraciame rodica
    Vertex* findSet(Vertex *vert){
        Vertex* parent = vert->getParent();
        if (parent == vert) {
            return parent;
        }
        vert->setParent(findSet(vert->getParent()));
        return vert->getParent();
    }
    /******************************************************/
    
    
    // nacitanie grafu zo suboru - pridanie vrcholov do grafu
    void load_graph(const char *input) {
        ifstream file;
        file.open(input);
        
        string new_line;
        int x1, y1 ,x2, y2;
        
        while (getline(file, new_line)) {
            sscanf(new_line.c_str(), "[%d,%d] [%d,%d]", &x1, &y1, &x2, &y2);
            add_vertices(x1, y1, x2, y2);
        }
    }
    // aplikujeme graham scan algoritmus na jednotlive "mnoziny miest"
    // body, ktore tvoria ohranicenie pre jednotlive "mnoziny miest" ukladame do vektorov
    // ktore mapujeme na suradnice rodicov do mapy
    void applyGraham(){
        for(auto it = forGraham.begin(); it != forGraham.end(); it++){
            long N = it->second.size();
            stack<pair<int,int> > hull = grahamScan(it->second, N);
            if(hull.empty()){
                for(long i = 0; i < N; i++){
                    //cout << it->second.at(i).first << " " << it->second.at(i).second << " ";
                    afterGraham[it->first].push_back(vertices[it->second.at(i)]);
                }
                //cout << endl;
            }
            while (!hull.empty())   {
                
                afterGraham[it->first].push_back(vertices[hull.top()]);
                hull.pop();
            }
        }
    }
    
    // metoda pre vypocet vzdialenost v 2D
    double distance(pair<int, int> c1, pair<int, int> c2){
        return sqrt(pow(c2.first - c1.first, 2) + pow(c2.second - c1.second, 2));
    }
    
    // vsetkych rodicov spojime hranami, pre n rodicov vznikne n*(n-1)/2 hran
    // vypocitame vzdialenosti medzi rodicmi - ovahujeme tymi hodnotami hrany
    void setEdges(){
        for(auto it1 : centroidParents){
            for(auto it2 : centroidParents){
                if(it1.second < it2.second){
                    double dist = distance(it1.second->getCoors(), it2.second->getCoors());
                    parentEdges.push_back(new Edge(it1.second, it2.second, dist));
                }
            }
        }
    }
    // zosortujeme hrany podla vah - t.j. podla jednotlivych vzdialenosti koli Kruskal. alg.
    void sortEdges(){
        sort(parentEdges.begin(), parentEdges.end(), cmp);
    }
    
    /***********     Kruskalov algoritmus     ************/
    // kod prevzaty z:
    // https://github.com/mission-peace/interview/blob/master/src/com/interview/graph/KruskalMST.java
    
    void applyKruskal(){
        // vytvorenie taziskovych vrcholov, s ktorymi budeme pracovat
        makeCentroids();
        // spojime vrcholy hranami
        setEdges();
        // hrany zosortujeme od najmensej po najvacsiu
        sortEdges();
        
        for (auto it : parentEdges) {
            // pre kazdu hranu najdeme suradnice "rodicov" vrcholov, ktore hrana spaja
            pair<int, int> parent1 = fs(it->getV1()->getCoors(), &centroidParents);
            pair<int, int> parent2 = fs(it->getV2()->getCoors(), &centroidParents);
            
            //pozreme ci su vrcholu v rovnakej mnozine (maju rovnakych rodicov)
            //ak su vrcholy v rovnakej mnozine tak hranu ignorujeme
            if (parent1.first == parent2.first && parent1.second == parent2.second){
                continue;
            } else {
                // ak su vrcholy v roznych mnozinach tak si hranu pridame do vysledneho
                // vektoraa a spravime zjednotenie tychto dvoch mnozin
                mst.push_back(it);
                make_union(it->getV1()->getCoors(), it->getV2()->getCoors(), &centroidParents);
            }
            
        }
    }
    /*****************************************************/
    
    // najdenie najblizsich hran pomocou najblizsie spojenych taziskovych vrcholov
    // pre kazdu hranu, ktora spaja tieto vrcholy porovname vzdialenosti z jednej "mnoziny" potomkov do druhej,
    // zosortujeme najdene hrany pre dvojicu miest a vlozime najmensiu hranu do
    // vektora hran, ktory bude na konci tvorit riesenie - minimum spanning tree
    void find_closest(){
        double sum =0.0;
        for(auto it : mst){
            vector<Edge*> toSort;
            for(auto it1 : afterCent[it->getV1()->getCoors()]){
                for(auto it2: afterCent[it->getV2()->getCoors()]){
                    double dist = distance(it1->getCoors(), it2->getCoors());
                    Edge *edge = new Edge(it1, it2, dist);
                    toSort.push_back(edge);
                }
            }
            
            sort(toSort.begin(), toSort.end(), cmp);
            
            mstfinal.push_back(toSort[0]);
            
            sum = sum + toSort[0]->getWeight();
        }
        //cout << sum << endl;
        
    }
    // zapis vystupu do suboru
    void write_mst_final(const char *output){
        //cout << mstfinal.size() << endl;
        ofstream myfile;
        myfile.open (output);
        double sum = 0;
        for(auto it : mstfinal){
            myfile << "[" << it->getV1()->getCoors().first << "," << it->getV1()->getCoors().second << "]";
            myfile << " " << "[" << it->getV2()->getCoors().first << "," << it->getV2()->getCoors().second << "]" << endl;
            
            //cout << "[" << it->getV1()->getCoors().first << "," << it->getV1()->getCoors().second << "]";
            //cout << " " << "[" << it->getV2()->getCoors().first << "," << it->getV2()->getCoors().second << "]" << endl;
            sum = sum + it->getWeight();
        }
        //cout << sum << endl;
        myfile.close();
    }
    // vytvorenie tazisiek jednotlivych zhlukov
    void makeCentroids(){
        for(auto parent : afterGraham){
            long n = parent.second.size();
            long xSum = 0;
            long ySum = 0;
            for(int i = 0; i < n; i++){
                xSum = xSum + parent.second.at(i)->getCoors().first;
                ySum = ySum + parent.second.at(i)->getCoors().second ;
            }
            Vertex *centP = new Vertex((int)(xSum / n), (int)(ySum / n), 0);
            centP->setParent(centP);
            
            centroidParents[centP->getCoors()] = centP;
            
            vector<Vertex *> children(parent.second);
            
            afterCent[centP->getCoors()] = children;
            
        }
    }
private:
    // mapa nacitanych vrcholov
    map<pair<int,int>, Vertex* > vertices;
    // mnozina prvotnych rodicov na definovanie zhlukov
    set<Vertex *> parents;
    
    // mapovanie vektorov suradnic potomkov na suradnice rodicov - urcene pre Graham scan
    map<pair<int, int>, vector<pair<int, int> > > forGraham;
    // mapovanie vektorov vrcholov, ktore ohranicuju mesto - vysledok Graham scan
    map<pair<int, int>, vector<Vertex*> > afterGraham;
    
    // novy rodicia, ich suradnice su taziskom zhlukov
    map<pair<int,int>, Vertex* > centroidParents;
    // nove mapovanie potomkov na taziska
    map<pair<int, int>, vector<Vertex*> > afterCent;
    
    // vektor hran, ktory spaja vsetkych rodicov navzajom, pre kruskala
    vector<Edge *> parentEdges;
    // minimum spanning tree pre graf z taziskovych vrcholov
    vector<Edge *> mst;
    // minimum spanning tree pre vysledny graf, po aplikacii najlepsich vzdialenosti
    vector<Edge *> mstfinal;
    
};

/***********     Graham scan algoritmus     ************/
// kod prevzaty z:
// https://github.com/kartikkukreja/blog-codes/blob/master/src/Graham%20Scan%20Convex%20Hull.cpp


// pivot je bod, ktory ma najnizsiu y-suradnicu , pouzivame ho na sortovanie ostatnych bodov
// podla uhla okolo tohoto bodu
pair<int, int> pivot;

// funckia vracia -1 ak body a-> b-> c-> formuju otocenie proti smere hod. ruciciek
// vracia 1 ak body formuju otocenie v smere hodinovych ruciciek
// vracia 0 ak body lezia na jednej priamke
int ccw(pair<int,int> va, pair<int,int> vb, pair<int, int> vc) {
    int area = (vb.first - va.first) * (vc.second - va.second) - (vb.second - va.second) * (vc.first - va.first);
    if (area > 0)
        return -1;
    else if (area < 0)
        return 1;
    return 0;
}

// funkcia vracia stvorec euklidovskej vzdialenosti medzi dvoma bodmi
int sqrDist(pair<int,int> va, pair<int,int> vb)  {
    int dx = va.first - vb.first, dy = va.second - vb.second;
    return dx * dx + dy * dy;
}

// komparacna funkcia ,pouzivame pre sortovanie bodov podla pivota
bool POLAR_ORDER(pair<int,int> va, pair<int,int> vb)  {
    int order = ccw(pivot, va, vb);
    if (order == 0)
        return sqrDist(pivot, va) < sqrDist(pivot, vb);
    return (order == -1);
}

// graham scan, argumenty vektor suradnic pre zhluk miest a pocet miest (bodov)
stack<pair<int, int> > grahamScan(vector<pair<int,int> > coordspv, long N)    {
    stack<pair<int, int> > hull;
    
    if (N < 3)
        return hull;
    
    
    // najdeme bod, ktory ma najmensiu y suradnicu - nas pivot
    // vazby sa rozdelia v prospech nizsich x suradnic
    int leastY = 0;
    for (int i = 1; i < N; i++)
        if ((coordspv[i].second != coordspv[leastY].second && coordspv[i].second < coordspv[leastY].second)
            || (coordspv[i].second == coordspv[leastY].second && coordspv[i].first < coordspv[leastY].first))
            leastY = i;
    
    // vo vektore swapneme najdeneho pivota z prvym bodom
    pair<int,int> temp = coordspv[0];
    coordspv[0] = coordspv[leastY];
    coordspv[leastY] = temp;
    
    // sortneme zvysok bodov podla polarneho poradia okolo pivota
    pivot = coordspv[0];
    sort(&coordspv[1], &coordspv[N - 1], POLAR_ORDER);
    
    // do staku vlozime prve tri oporne body
    hull.push(coordspv[0]);
    hull.push(coordspv[1]);
    hull.push(coordspv[2]);
    
    // prebehneme vsetky zvysne body a zistime ktore tvoria trup nasho zhluku bodov
    // a to tak ze v cykle vzdy zoberieme vrchol zasobnika t.j. pivot
    // popneme ho a na dalsi bod v stacku, pivot a bod z nasho vektora volame funkciu ccw
    // kym sa nezacnu body stacat v smere hodinovych ruciciek
    // medzi tym aktualizujeme pivota a vyberame zo zasobnika
    // ak sa zacnu stacat tak vlozime do zasobnika noveho pivota a za nim
    // dalsi bod z vektora nasich sortnutych suradnic
    
    for (int i = 3; i < N; i++) {
        pair<int,int> top = hull.top();
        hull.pop();
        //cout << "hull top: "<< hull.top().first << " " << hull.top().second << " top: " << top.first << " " << top.second << endl;
        //cout << ccw(hull.top(), top, coordspv[i]) << endl;
        while (ccw(hull.top(), top, coordspv[i]) != -1)   {
            top = hull.top();
            hull.pop();
            if(hull.empty())
                break;
        }
        hull.push(top);
        hull.push(coordspv[i]);
    }
    // vraciame stack nasich bodov ktore tvoria okraj/trup
    return hull;
}

/*****************     Main     *****************/
int main(int argc, const char * argv[]) {
    // insert code here...
    if(argc == 3){
        Graph *G = new Graph();
        G->load_graph(argv[1]);
        G->prepare_data();
        
        G->applyGraham();
        
        G->applyKruskal();
        
        G->find_closest();
        G->write_mst_final(argv[2]);
    }
    else cout << "Bad input command..." << endl;
    return 0;
}
