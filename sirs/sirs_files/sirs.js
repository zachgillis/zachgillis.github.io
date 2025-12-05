// all of the global variables for dynamics
var gpx_black = null;
var gpx_white = null;
var gpx_size = 0;
var canvasN = 512;
var gbuffer;
var gbufferdata;

var gboard = null;
var gN = 256;
var gT = 2.26918531421;
var gCouplingRange = 'nn'; // nn, nnn, nnnn, nnnnn
var gLossImmunityProb = 1.0; // probability that an accepted R->S flip actually happens
var gUsePeriodic = true;     // whether to wrap boundary conditions
var gCornerProb = 0.5;       // probability parameter for probabilistic corner inclusion when using nn_prob (0-4)
var gclusterBoard = null;   // per-site cluster ids for infected sites
var gclusterNextId = 0;     // counter for new spontaneous clusters
var gclusterSizes = {};     // map cluster id -> current infected count
var gclusterMaxSize = {};   // map cluster id -> max infected count reached (for cumulative histogram)

var ge_avg, ge_var, gm_avg, gm_var;

var STATE_S = 0; // susceptible
var STATE_I = 1; // infected
var STATE_R = 2; // recovered
var gJ_SI = 6;
var gh_I = 2;
var gh_R = 0.5;
var gInitInfectedFrac = 0.05;
var gUseCenterSeed = false;

var gt = 0;
var times = [];
var gtimeseries_energy = [];
var gtimeseries_eavg = [];
var gtimeseries_s = [];
var gtimeseries_i = [];
var gtimeseries_r = [];
var genergy = 0;
var gI_current = 0;
var frame = 0;
var sweeps = 0;
var lasttime = 0;

// display variables
var c, c2;
var ctx;
var ctxgraph;
var empty;
var frameskip = 1;
var onefill = 0;
var dodraw = true;
var gh = 150;
var gw = 370;

function rgb(r,g,b) {
    return 'rgb('+r+','+g+','+b+')';
}
function log10(val) {
    return Math.log(val) / Math.LN10;
}

function toFixed(value, precision, negspace) {
    negspace = typeof negspace !== 'undefined' ? negspace : '';
    var precision = precision || 0;
    var sneg = (value < 0) ? "-" : negspace;
    var neg = value < 0;
    var power = Math.pow(10, precision);
    var value = Math.round(value * power);
    var integral = String(Math.abs((neg ? Math.ceil : Math.floor)(value/power)));
    var fraction = String((neg ? -value : value) % power);
    var padding = new Array(Math.max(precision - fraction.length, 0) + 1).join('0');
    return sneg + (precision ? integral + '.' +  padding + fraction : integral);
}

function formatProb(p){
    if (p <= 0) return "0";
    if (p < 1e-4) return p.toExponential(2);
    return toFixed(p, 6);
}

function init_board(N, board){
    gt = 0;
    gboard = [];
    gclusterBoard = [];
    gclusterSizes = {};
    gclusterMaxSize = {};
    gclusterNextId = 0;
    gN = N;

    if (board !== null && board.length >= gN * gN){
        for (var i=0; i<gN*gN; i++){
            gboard[i] = board[i];
            gclusterBoard[i] = -1;
            if (gboard[i] === STATE_I){
                // Treat initial infections as spontaneous seeds with unique ids.
                gclusterBoard[i] = gclusterNextId;
                gclusterSizes[gclusterNextId] = 1;
                gclusterMaxSize[gclusterNextId] = 1;
                gclusterNextId += 1;
            }
        }
    } else if (gUseCenterSeed) {
        for (var i=0; i<gN*gN; i++){
            gboard[i] = STATE_S;
            gclusterBoard[i] = -1;
        }
        var cx = Math.floor(gN/2);
        var cy = Math.floor(gN/2);
        gboard[cx + cy*gN] = STATE_I;
        gclusterBoard[cx + cy*gN] = gclusterNextId;
        gclusterSizes[gclusterNextId] = 1;
        gclusterMaxSize[gclusterNextId] = 1;
        gclusterNextId += 1;
    } else {
        for (var i=0; i<gN*gN; i++){
            gboard[i] = (Math.random() < gInitInfectedFrac) ? STATE_I : STATE_S;
            gclusterBoard[i] = -1;
            if (gboard[i] === STATE_I){
                gclusterBoard[i] = gclusterNextId;
                gclusterSizes[gclusterNextId] = 1;
                gclusterMaxSize[gclusterNextId] = 1;
                gclusterNextId += 1;
            }
        }
    }

    gpx_size = canvasN/gN;
    display_board(gN, gboard);
    draw_all();

    init_measurements();
}

function stateColor(state){
    if (state === STATE_S) return [66, 135, 245];      // blue-ish susceptible
    if (state === STATE_I) return [231, 76, 60];       // red infected
    if (state === STATE_R) return [46, 204, 113];      // green recovered
    return [120, 120, 120];
}

function put_pixel(x, y, size, state){
    var xoff = x*size;
    var yoff = y*size;
    var color = stateColor(state);
    for (var i=0; i<size; i++){
        for (var j=0; j<size; j++){
            var ind = ((yoff+j)*gN*size + xoff+ i)*4;
            gbufferdata[ind+0] = color[0];
            gbufferdata[ind+1] = color[1];
            gbufferdata[ind+2] = color[2];
            gbufferdata[ind+3] = 255;
        }
    }
}

function display_board(N, board){
    for (var i=0; i<N; i++){
        for (var j=0; j<N; j++){
            put_pixel(i, j, gpx_size, board[i+j*N]);
        }
    }
}

function selectRandomDiagonalOffsets(count){
    var diag = [[1,1], [-1,1], [1,-1], [-1,-1]];
    for (var i=diag.length-1; i>0; i--){
        var j = Math.floor(Math.random() * (i+1));
        var tmp = diag[i]; diag[i] = diag[j]; diag[j] = tmp;
    }
    return diag.slice(0, Math.min(count, diag.length));
}

function selectProbCorners(p){
    // p in [0,4]: fractional scheme described by user
    if (isNaN(p)) p = 0;
    if (p < 0) p = 0;
    if (p > 4) p = 4;
    var base = Math.floor(p);
    var frac = p - base;
    var diag = selectRandomDiagonalOffsets(4);
    var selected = [];
    for (var i=0; i<base && i<diag.length; i++){
        selected.push(diag[i]);
    }
    if (base < diag.length && Math.random() < frac){
        selected.push(diag[base]);
    }
    return selected;
}

function neighborIndex(x, y){
    if (gUsePeriodic){
        return ((x.mod(gN)) + (y.mod(gN)) * gN);
    }
    if (x < 0 || x >= gN || y < 0 || y >= gN){
        return -1;
    }
    return x + y*gN;
}

function neighborState(b, x, y){
    var idx = neighborIndex(x, y);
    if (idx < 0) return null;
    return b[idx];
}

function remove_cluster_membership(ind){
    var cid = gclusterBoard[ind];
    if (cid === undefined || cid === null || cid < 0)
        return;
    if (gclusterSizes[cid]){
        gclusterSizes[cid] -= 1;
        if (gclusterSizes[cid] <= 0){
            delete gclusterSizes[cid];
        }
    }
    gclusterBoard[ind] = -1;
}

function gather_infected_neighbor_weights(x, y){
    var weights = {};
    var addNeighbor = function(dx, dy, weight){
        var nind = neighborIndex(x + dx, y + dy);
        if (nind < 0) return;
        if (gboard[nind] === STATE_I){
            var cid = gclusterBoard[nind];
            if (cid !== undefined && cid !== null && cid >= 0){
                if (!weights[cid]) weights[cid] = 0;
                weights[cid] += weight;
            }
        }
    };

    // nearest neighbors
    addNeighbor(0, 1, 1.0);
    addNeighbor(0, -1, 1.0);
    addNeighbor(1, 0, 1.0);
    addNeighbor(-1, 0, 1.0);

    // diagonals
    if (gCouplingRange === 'nn_prob' || gCouplingRange === 'nnn' || gCouplingRange === 'nnnn' || gCouplingRange === 'nnnnn'){
        if (gCouplingRange === 'nn_prob'){
            var diagProb = selectProbCorners(gCornerProb);
            for (var h=0; h<diagProb.length; h++){
                addNeighbor(diagProb[h][0], diagProb[h][1], 1.0);
            }
        } else {
            addNeighbor(1, 1, 1.0);
            addNeighbor(-1, 1, 1.0);
            addNeighbor(1, -1, 1.0);
            addNeighbor(-1, -1, 1.0);
        }
    }

    // distance-2 axial
    if (gCouplingRange === 'nnnn' || gCouplingRange === 'nnnnn'){
        addNeighbor(0, 2, 1.0);
        addNeighbor(0, -2, 1.0);
        addNeighbor(2, 0, 1.0);
        addNeighbor(-2, 0, 1.0);
    }

    // knight moves
    if (gCouplingRange === 'nnnnn'){
        var knightOffsets = [
            [2, 1], [1, 2], [-1, 2], [-2, 1],
            [-2, -1], [-1, -2], [1, -2], [2, -1]
        ];
        for (var k=0; k<knightOffsets.length; k++){
            addNeighbor(knightOffsets[k][0], knightOffsets[k][1], 1.0);
        }
    }
    return weights;
}

function assign_cluster_for_infection(x, y, ind){
    var weights = gather_infected_neighbor_weights(x, y);
    var bestId = null;
    var bestWeight = 0;
    for (var cid in weights){
        if (weights.hasOwnProperty(cid) && weights[cid] > bestWeight){
            bestWeight = weights[cid];
            bestId = parseInt(cid);
        }
    }

    // No infected neighbors means a spontaneous infection.
    if (bestId === null){
        bestId = gclusterNextId;
        gclusterNextId += 1;
    }
    gclusterBoard[ind] = bestId;
    if (!gclusterSizes[bestId]) gclusterSizes[bestId] = 0;
    gclusterSizes[bestId] += 1;
    if (!gclusterMaxSize[bestId]) gclusterMaxSize[bestId] = 0;
    if (gclusterSizes[bestId] > gclusterMaxSize[bestId]) gclusterMaxSize[bestId] = gclusterSizes[bestId];
    return bestId;
}

function repair_cluster_ids(){
    var rebuiltSizes = {};
    var maxId = gclusterNextId - 1;
    for (var y=0; y<gN; y++){
        for (var x=0; x<gN; x++){
            var ind = x + y*gN;
            if (gboard[ind] !== STATE_I) continue;
            var cid = gclusterBoard[ind];
            if (cid === undefined || cid === null || cid < 0){
                // Try to inherit from neighbors; otherwise seed a new spontaneous id.
                var weights = gather_infected_neighbor_weights(x, y);
                var bestId = null;
                var bestWeight = 0;
                for (var nid in weights){
                    if (weights.hasOwnProperty(nid) && weights[nid] > bestWeight){
                        bestWeight = weights[nid];
                        bestId = parseInt(nid);
                    }
                }
                if (bestId === null){
                    bestId = gclusterNextId;
                    gclusterNextId += 1;
                }
                cid = bestId;
                gclusterBoard[ind] = cid;
            }
            if (!rebuiltSizes[cid]) rebuiltSizes[cid] = 0;
            rebuiltSizes[cid] += 1;
            if (cid > maxId) maxId = cid;
        }
    }
    gclusterSizes = rebuiltSizes;
    gclusterNextId = maxId + 1;
    // Update cumulative max sizes
    for (var cid in gclusterSizes){
        if (gclusterSizes.hasOwnProperty(cid)){
            var sz = gclusterSizes[cid];
            if (!gclusterMaxSize[cid] || sz > gclusterMaxSize[cid]){
                gclusterMaxSize[cid] = sz;
            }
        }
    }
}

function energy_site(x, y, s, b, opts){
    var E = 0;
    var up = neighborState(b, x, y+1);
    var down = neighborState(b, x, y-1);
    var right = neighborState(b, x+1, y);
    var left = neighborState(b, x-1, y);

    if (s === STATE_S){
        var addBond = function(neighborState, weight){
            if (neighborState === STATE_I) E += weight * gJ_SI;
        };

        // nearest neighbors
        addBond(up, 1.0);
        addBond(down, 1.0);
        addBond(right, 1.0);
        addBond(left, 1.0);

        // next-to-nearest neighbors (diagonals)
        if (gCouplingRange === 'nn_prob' || gCouplingRange === 'nnn' || gCouplingRange === 'nnnn' || gCouplingRange === 'nnnnn'){
            if (gCouplingRange === 'nn_prob'){
                var probList = selectProbCorners(gCornerProb);
                for (var p=0; p<probList.length; p++){
                    var dxdyProb = probList[p];
                    addBond(neighborState(b, x+dxdyProb[0], y+dxdyProb[1]), 1.0);
                }
            } else {
                addBond(neighborState(b, x+1, y+1), 1.0);
                addBond(neighborState(b, x-1, y+1), 1.0);
                addBond(neighborState(b, x+1, y-1), 1.0);
                addBond(neighborState(b, x-1, y-1), 1.0);
            }
        }

        // next-to-next-to-nearest neighbors
        if (gCouplingRange === 'nnnn' || gCouplingRange === 'nnnnn'){
            var up2 = neighborState(b, x, y+2);
            var down2 = neighborState(b, x, y-2);
            var right2 = neighborState(b, x+2, y);
            var left2 = neighborState(b, x-2, y);
            addBond(up2, 1.0);
            addBond(down2, 1.0);
            addBond(right2, 1.0);
            addBond(left2, 1.0);
        }

        // next-to-next-to-next-to-nearest neighbors
        if (gCouplingRange === 'nnnnn'){
            var knightOffsets = [
                [2, 1], [1, 2], [-1, 2], [-2, 1],
                [-2, -1], [-1, -2], [1, -2], [2, -1]
            ];
            for (var k=0; k<knightOffsets.length; k++){
                var dx = knightOffsets[k][0];
                var dy = knightOffsets[k][1];
                var ns = neighborState(b, x+dx, y+dy);
                addBond(ns, 1.0);
            }
        }
    }

    if (s === STATE_I){
        E += gh_I;
    } else if (s === STATE_R){
        E += gh_R;
    }
    return E;
}

function state_fractions(){
    var counts = [0,0,0];
    for (var i=0; i<gN*gN; i++){
        counts[gboard[i]] += 1;
    }
    return [counts[STATE_S]/(gN*gN), counts[STATE_I]/(gN*gN), counts[STATE_R]/(gN*gN)];
}

function update_metropolis(){
    var x = Math.floor(Math.random()*gN);
    var y = Math.floor(Math.random()*gN);
    var ind = x + y*gN;
    var sold = gboard[ind];
    var snew = sold === STATE_S ? STATE_I : (sold === STATE_I ? STATE_R : STATE_S);
    // For R->S transitions, ignore SI bonds when proposing the move; the new S
    var de = energy_site(x, y, snew, gboard) - energy_site(x, y, sold, gboard);
    var temp = Math.max(gT, 1e-9);
    if (de <= 0 || Math.random() < Math.exp(-de / temp)){
        // For R->S moves, an extra probabilistic gate after Metropolis acceptance.
        if (sold === STATE_R && snew === STATE_S && Math.random() > gLossImmunityProb){
            return; // reject the loss-of-immunity attempt
        }
        // Maintain cluster bookkeeping before applying state updates.
        if (sold === STATE_I && snew !== STATE_I){
            remove_cluster_membership(ind);
        }
        if (sold === STATE_S && snew === STATE_I){
            assign_cluster_for_infection(x, y, ind);
        } else if (snew !== STATE_I){
            gclusterBoard[ind] = -1;
        }

        gboard[ind] = snew;

        if (!onefill)
            put_pixel(x, y, gpx_size, snew);
    }
    gt += 1.0/(gN*gN);
}


function update() {
    update_metropolis();
}

function push_measurement(t, e){
    times.push(t);
    gtimeseries_energy.push(e);
    var fracs = state_fractions();
    gtimeseries_s.push(fracs[0]);
    gtimeseries_i.push(fracs[1]);
    gtimeseries_r.push(fracs[2]);
    var m = fracs[1];
    gI_current = m;

    n = times.length;
    ge0 = ge_avg;
    gm0 = gm_avg;

    // welford's algorithm
    ge_avg = ge_avg + (e - ge_avg)/n;
    ge_var = ((n-1)*ge_var + (e - ge_avg)*(e - ge0)) / n;
    gm_avg = gm_avg + (m - gm_avg)/n;
    gm_var = ((n-1)*gm_var + (m - gm_avg)*(m - gm0)) / n;
    gtimeseries_eavg.push(ge_avg);

    sps = 1000.0*sweeps/(Date.now() - lasttime);
}

function init_measurements(){
    frame = 0;
    sweeps = 0;
    gt = 0;
    ge_avg = ge_var = gm_avg = gm_var = 0;
    times = [];
    gtimeseries_energy = [];
    gtimeseries_eavg = [];
    gtimeseries_s = [];
    gtimeseries_i = [];
    gtimeseries_r = [];
    lasttime = Date.now();
    reset_measurements();
    push_measurement(gt, genergy);
}

function reset_measurements(){
    genergy = 0;
    ge_avg = ge_var = gm_avg = gm_var = 0;
    var fracs = state_fractions();
    gI_current = fracs[1];

    gm_avg = gI_current;
    update_measurements_labels();

    // Reset cumulative cluster history based on current lattice
    repair_cluster_ids();
    gclusterMaxSize = {};
    for (var cid in gclusterSizes){
        if (gclusterSizes.hasOwnProperty(cid)){
            gclusterMaxSize[cid] = gclusterSizes[cid];
        }
    }
}

function update_measurements_labels(){
    lblt = document.getElementById('label_time');
    lble = document.getElementById('label_energy');
    lblm = document.getElementById('label_mag');

    lblt.innerHTML = "time = "+toFixed(gt, 4, ' ')+"   sweeps/sec = "+toFixed(sps, 3, ' ');
    lble.innerHTML = "";
    lblm.innerHTML = "";
}

function hidden_link_download(uri, filename){
    var link = document.createElement('a');
    link.href = uri;
    link.style.display = 'none';
    link.download = filename
    link.id = 'templink';
    document.body.appendChild(link);
    document.getElementById('templink').click();
    document.body.removeChild(document.getElementById('templink'));
}

function download_measurements(){
    var csv = "data:text/csv;charset=utf-8,";
    csv += "# time, energy per spin, infected fraction, S fraction, I fraction, R fraction\n";
    for (var i=0; i<times.length; i++){
        csv += times[i]+", ";
        csv += gtimeseries_energy[i]+", ";
        csv += gtimeseries_i[i]+", ";
        csv += gtimeseries_s[i]+", ";
        csv += gtimeseries_i[i]+", ";
        csv += gtimeseries_r[i]+"\n";
    }
    var encoded = encodeURI(csv).replace(/#/g,'%23');
    hidden_link_download(encoded, 'ising-data.txt');
}

function download_cluster_histogram(){
    repair_cluster_ids();
    // Build histogram from cumulative max size per cluster (includes dead clusters).
    var histogram = {};
    for (var cid in gclusterMaxSize){
        if (gclusterMaxSize.hasOwnProperty(cid)){
            var size = gclusterMaxSize[cid];
            if (size > 0){
                if (!histogram[size]) histogram[size] = 0;
                histogram[size] += 1;
            }
        }
    }

    var csv = "data:text/csv;charset=utf-8,";
    csv += "# cluster_size, count\n";
    var sizes = Object.keys(histogram).map(Number).sort(function(a, b){ return a - b; });
    for (var i=0; i<sizes.length; i++){
        var sz = sizes[i];
        csv += sz + ", " + histogram[sz] + "\n";
    }
    var encoded = encodeURI(csv).replace(/#/g,'%23');
    hidden_link_download(encoded, 'ising-cluster-histogram.txt');
}

function download_field(){
    uri = c.toDataURL("image/png");
    hidden_link_download(uri, 'ising-field.png');
}

function download_graph(){
    uri = c2.toDataURL("image/png");
    hidden_link_download(uri, 'ising-graph.png');
}

function draw_all(){
    if (onefill)
        display_board(gN, gboard);

    gbuffer.data = gbufferdata;
    ctx.putImageData(gbuffer, 0, 0);
    push_measurement(gt, genergy);
    update_measurements_labels();
    draw_graph();
}

function draw_graph(){
    cleargraph();
    draw_multi_series_graph(times, [gtimeseries_s, gtimeseries_i, gtimeseries_r], ['rgb(66,135,245)', 'rgb(231,76,60)', 'rgb(46,204,113)']);
}


/*======================================================================
  the javascript interface stuff
=========================================================================*/
function dotextbox(id){
    idt = id+"_input";
    document.getElementById(id).style.display = 'none';
    document.getElementById(idt).style.display = 'inline';
    document.getElementById(idt).value = document.getElementById(id).innerHTML;
    document.getElementById(idt).focus();
}

function undotextbox(id){
    idt = id.replace("_input", "");
    document.getElementById(idt).style.display = 'inline';
    document.getElementById(id).style.display = 'none';
}

function update_temp(){
    min = document.getElementById('temp').min;
    gTval = parseFloat(document.getElementById('temp').value);
    if (gTval <= min)
        gT = 0;
    else
        gT = Math.pow(10, gTval);
    document.getElementById('label_temp').innerHTML = toFixed(gT,6);
    var tempBox = document.getElementById('temp_box');
    if (tempBox) tempBox.value = gT;
}
function update_hI(){
    gh_I = parseFloat(document.getElementById('hI').value);
    document.getElementById('label_hI').innerHTML = toFixed(gh_I,6);
    var box = document.getElementById('hI_box');
    if (box) box.value = gh_I;
    reset_measurements();
}
function update_hR(){
    gh_R = parseFloat(document.getElementById('hR').value);
    document.getElementById('label_hR').innerHTML = toFixed(gh_R,6);
    var box = document.getElementById('hR_box');
    if (box) box.value = gh_R;
    reset_measurements();
}
function update_corner_prob(){
    gCornerProb = parseFloat(document.getElementById('corner_prob').value);
    if (isNaN(gCornerProb)) gCornerProb = 0;
    if (gCornerProb < 0) gCornerProb = 0;
    if (gCornerProb > 4) gCornerProb = 4;
    document.getElementById('label_corner_prob').innerHTML = toFixed(gCornerProb,4);
    var box = document.getElementById('label_corner_prob_input');
    if (box) box.value = gCornerProb;
}
function update_loss_immunity_prob(){
    var slider = document.getElementById('loss_immunity_prob');
    var prob = gLossImmunityProb;
    if (slider){
        var logVal = parseFloat(slider.value);
        prob = Math.pow(10, logVal);
    }
    if (isNaN(prob)) prob = gLossImmunityProb;
    // clamp to [0,1]
    if (prob < 0) prob = 0;
    if (prob > 1) prob = 1;
    gLossImmunityProb = prob;
    document.getElementById('label_loss_immunity_prob').innerHTML = formatProb(gLossImmunityProb);
    // keep slider synced if called from text entry
    if (slider){
        slider.value = Math.log10(Math.max(gLossImmunityProb, 1e-12));
    }
    var box = document.getElementById('loss_immunity_prob_box');
    if (box) box.value = gLossImmunityProb;
}
function update_J_SI(){
    gJ_SI = parseFloat(document.getElementById('J_SI').value);
    document.getElementById('label_J_SI').innerHTML = toFixed(gJ_SI,6);
    var box = document.getElementById('J_SI_box');
    if (box) box.value = gJ_SI;
    reset_measurements();
}
function update_coupling_range(){
    var selector = document.getElementById('coupling_range');
    if (!selector) return;
    gCouplingRange = selector.value;
    reset_measurements();
}
function update_frames(){
    frameval = parseFloat(document.getElementById('frames').value);
    frameskip = Math.pow(10, frameval);
    onefill = frameskip > 2*gN*gN ? 1 : 0;
    document.getElementById('label_frames').innerHTML = toFixed(frameskip,6);
    var box = document.getElementById('frames_box');
    if (box) box.value = frameskip;
}
function update_init_frac(){
    gInitInfectedFrac = parseFloat(document.getElementById('init_frac').value);
    document.getElementById('label_init_frac').innerHTML = toFixed(gInitInfectedFrac,4);
    var box = document.getElementById('init_frac_box');
    if (box) box.value = gInitInfectedFrac;
}
function update_center_seed(){
    gUseCenterSeed = document.getElementById('center_seed').checked;
}
function update_periodic_boundary(){
    gUsePeriodic = document.getElementById('periodic_boundary').checked;
}

function sync_init_controls(){
    var fracSlider = document.getElementById('init_frac');
    if (fracSlider){
        gInitInfectedFrac = parseFloat(fracSlider.value);
        document.getElementById('label_init_frac').innerHTML = toFixed(gInitInfectedFrac,4);
        var box = document.getElementById('init_frac_box');
        if (box) box.value = gInitInfectedFrac;
    }
    var centerBox = document.getElementById('center_seed');
    if (centerBox){
        gUseCenterSeed = centerBox.checked;
    }
    var periodicBox = document.getElementById('periodic_boundary');
    if (periodicBox){
        gUsePeriodic = periodicBox.checked;
    }
}

function update_display(){
    document.getElementById('label_temp').innerHTML = toFixed(gT,6);
    var tempBox = document.getElementById('temp_box'); if (tempBox) tempBox.value = gT;
    document.getElementById('label_hI').innerHTML = toFixed(gh_I,6);
    var hI_box = document.getElementById('hI_box'); if (hI_box) hI_box.value = gh_I;
    document.getElementById('label_hR').innerHTML = toFixed(gh_R,6);
    var hR_box = document.getElementById('hR_box'); if (hR_box) hR_box.value = gh_R;
    document.getElementById('label_corner_prob').innerHTML = toFixed(gCornerProb,4);
    var corner_box = document.getElementById('label_corner_prob_input'); if (corner_box) corner_box.value = gCornerProb;
    var corner_slider = document.getElementById('corner_prob'); if (corner_slider) corner_slider.value = gCornerProb;
    document.getElementById('label_loss_immunity_prob').innerHTML = formatProb(gLossImmunityProb);
    var loss_box = document.getElementById('loss_immunity_prob_box'); if (loss_box) loss_box.value = gLossImmunityProb;
    var loss_slider = document.getElementById('loss_immunity_prob'); if (loss_slider) loss_slider.value = Math.log10(Math.max(gLossImmunityProb, 1e-12));
    document.getElementById('label_J_SI').innerHTML = toFixed(gJ_SI,6);
    var J_box = document.getElementById('J_SI_box'); if (J_box) J_box.value = gJ_SI;
    var couplingSelector = document.getElementById('coupling_range'); if (couplingSelector) couplingSelector.value = gCouplingRange;
    document.getElementById('label_frames').innerHTML = toFixed(frameskip,6);
    var frame_box = document.getElementById('frames_box'); if (frame_box) frame_box.value = frameskip;
    document.getElementById('label_init_frac').innerHTML = toFixed(gInitInfectedFrac,4);
    var init_box = document.getElementById('init_frac_box'); if (init_box) init_box.value = gInitInfectedFrac;
    document.getElementById('center_seed').checked = gUseCenterSeed;
    var periodicBox = document.getElementById('periodic_boundary'); if (periodicBox) periodicBox.checked = gUsePeriodic;
}

function update_pause(){
    if (dodraw == true){
        document.getElementById('pause').value = 'Start';
        dodraw = false;
    } else {
        document.getElementById('pause').value = 'Pause';
        requestAnimationFrame(tick, c);
        dodraw = true;
    }
}

function update_restart(){
    // Pull latest UI values before rebuilding lattice
    sync_init_controls();
    init_board(gN, null);
}

function update_step(){
    if (dodraw)
        update_pause();

    for (var i=0; i<gN*gN; i++)
        update();
    draw_all();
}

/*===============================================================================
 * graphing
 *=============================================================================*/
var xaxis = 40;
var yaxis = 5;
function x2px(x, xmin, dx) {return ((x - xmin) / dx) * (gw - xaxis) + xaxis; }
function y2px(y, ymin, dy) {return gh - ((y - ymin) / dy * (gh - 2*yaxis) + yaxis); }
var graph_type = "sir";

function draw_series_graph(xl, yl){
    var xllength = xl.length;
    var xmax, xmin, ymax, ymin;
    xmax = ymax = -1e10; xmin = ymin = 1e10;
    var skip = 1;

    for (var i=0; i<xllength; i+=skip){
        if (xl[i] < xmin) xmin = xl[i];
        if (xl[i] > xmax) xmax = xl[i];
        if (yl[i] < ymin) ymin = yl[i];
        if (yl[i] > ymax) ymax = yl[i];
    }

    var dx = xmax - xmin;
    var dy = ymax - ymin;

    var oom_x = Math.abs(dx)<1?Math.round(log10(dx)):Math.floor(log10(dx));
    var oom_y = Math.abs(dy)<1?Math.round(log10(dy)):Math.floor(log10(dy));
    var pow10_x = Math.pow(10, oom_x);
    var pow10_y = Math.pow(10, oom_y);

    var idx = Math.floor(dx / pow10_x);
    var idy = Math.floor(dy / pow10_y);

    if (idx < 1) idx = 10;
    if (idy < 1) idy = 10;

    if (idx == 1 || idx == 2)
        idx *= 5;
    if (idy == 1 || idy == 2)
        idy *= 5;

    xtic_major = dx/idx;
    ytic_major = dy/idy;
    xtic_minor = xtic_major/5;
    ytic_minor = ytic_major/5;

    ctxgraph.font='12px sans-serif';
    ctxgraph.fillStyle='rgba(0,0,0,1)';

    ctxgraph.beginPath();
    ctxgraph.moveTo(xaxis, 0);
    ctxgraph.lineTo(xaxis, gh);
    ctxgraph.stroke();

    ctxgraph.beginPath();
    ctxgraph.moveTo(xaxis, y2px(0, ymin, dy));
    ctxgraph.lineTo(gw, y2px(0, ymin, dy));
    ctxgraph.stroke();

    for (var i=-idy; i<=idy; i++){
        y = y2px(i*ytic_major+(ymin+ymax)/2, ymin, dy);
        ctxgraph.beginPath();
        ctxgraph.moveTo(xaxis-5, y);
        ctxgraph.lineTo(xaxis, y);
        ctxgraph.stroke();
        ctxgraph.fillText(toFixed(i*ytic_major+(ymin+ymax)/2, 3), 0, y+4);
    }

    for (var i=-idy*5; i<=idy*5; i++){
        y = y2px(i*ytic_minor+(ymin+ymax)/2, ymin, dy);
        ctxgraph.beginPath();
        ctxgraph.moveTo(xaxis-2, y);
        ctxgraph.lineTo(xaxis, y);
        ctxgraph.stroke();
    }

    for (var i=0; i<xllength-skip; i+=skip){
        ctxgraph.beginPath();
        ctxgraph.moveTo(x2px(xl[i], xmin, dx), y2px(yl[i], ymin, dy));
        ctxgraph.lineTo(x2px(xl[i+skip], xmin, dx), y2px(yl[i+skip], ymin, dy));
        ctxgraph.stroke();
    }
}

function draw_multi_series_graph(xl, series, colors){
    var xllength = xl.length;
    var xmax, xmin, ymax, ymin;
    xmax = ymax = -1e10; xmin = ymin = 1e10;
    var skip = 1;

    for (var s=0; s<series.length; s++){
        var yl = series[s];
        for (var i=0; i<xllength; i+=skip){
            if (xl[i] < xmin) xmin = xl[i];
            if (xl[i] > xmax) xmax = xl[i];
            if (yl[i] < ymin) ymin = yl[i];
            if (yl[i] > ymax) ymax = yl[i];
        }
    }

    var dx = xmax - xmin;
    var dy = ymax - ymin;

    var oom_x = Math.abs(dx)<1?Math.round(log10(dx)):Math.floor(log10(dx));
    var oom_y = Math.abs(dy)<1?Math.round(log10(dy)):Math.floor(log10(dy));
    var pow10_x = Math.pow(10, oom_x);
    var pow10_y = Math.pow(10, oom_y);

    var idx = Math.floor(dx / pow10_x);
    var idy = Math.floor(dy / pow10_y);

    if (idx < 1) idx = 10;
    if (idy < 1) idy = 10;

    if (idx == 1 || idx == 2)
        idx *= 5;
    if (idy == 1 || idy == 2)
        idy *= 5;

    xtic_major = dx/idx;
    ytic_major = dy/idy;
    xtic_minor = xtic_major/5;
    ytic_minor = ytic_major/5;

    ctxgraph.font='12px sans-serif';
    ctxgraph.fillStyle='rgba(0,0,0,1)';

    ctxgraph.beginPath();
    ctxgraph.moveTo(xaxis, 0);
    ctxgraph.lineTo(xaxis, gh);
    ctxgraph.stroke();

    ctxgraph.beginPath();
    ctxgraph.moveTo(xaxis, y2px(0, ymin, dy));
    ctxgraph.lineTo(gw, y2px(0, ymin, dy));
    ctxgraph.stroke();

    for (var i=-idy; i<=idy; i++){
        y = y2px(i*ytic_major+(ymin+ymax)/2, ymin, dy);
        ctxgraph.beginPath();
        ctxgraph.moveTo(xaxis-5, y);
        ctxgraph.lineTo(xaxis, y);
        ctxgraph.stroke();
        ctxgraph.fillText(toFixed(i*ytic_major+(ymin+ymax)/2, 3), 0, y+4);
    }

    for (var i=-idy*5; i<=idy*5; i++){
        y = y2px(i*ytic_minor+(ymin+ymax)/2, ymin, dy);
        ctxgraph.beginPath();
        ctxgraph.moveTo(xaxis-2, y);
        ctxgraph.lineTo(xaxis, y);
        ctxgraph.stroke();
    }

    for (var s=0; s<series.length; s++){
        var yl = series[s];
        ctxgraph.strokeStyle = colors[s];
        for (var i=0; i<xllength-skip; i+=skip){
            ctxgraph.beginPath();
            ctxgraph.moveTo(x2px(xl[i], xmin, dx), y2px(yl[i], ymin, dy));
            ctxgraph.lineTo(x2px(xl[i+skip], xmin, dx), y2px(yl[i+skip], ymin, dy));
            ctxgraph.stroke();
        }
    }
    ctxgraph.strokeStyle = 'rgba(0,0,0,1)';
}

/*===============================================================================
    initialization and drawing
================================================================================*/
function clear(){
    ctx.fillStyle = 'rgba(200,200,200,0.2)';
    ctx.clearRect(0, 0, c.width, c.height);
    ctx.fillRect(0,0,c.width,c.height);
}

function cleargraph(){
    ctxgraph.fillStyle = 'rgba(200,200,200,0.2)';
    ctxgraph.clearRect(0, 0, c2.width, c2.height);
    ctxgraph.fillRect(0,0,c2.width,c2.height);
}

var tick = function(T) {
    var skip = frameskip * gN * gN;
    if (dodraw == true) {
        for (var i=0; i<skip; i++){
            frame++;
            update();
        }
        sweeps = 1.0*frame / (gN*gN);
        draw_all();
        requestAnimationFrame(tick, c);
    }
};

function change_num(){
    gN = parseInt(document.getElementById('changenum').value);
    init_board(gN, null);
}



var init = function() {
    // create the canvas element
    empty = document.createElement('canvas');
    empty.width = empty.height = 1;
    c = document.getElementById('canvas');
    c.style.cursor = 'url('+empty.toDataURL()+')';
    ctx = c.getContext('2d');
    c2 = document.getElementById('canvas-graph');
    c2.style.cursor = 'url('+empty.toDataURL()+')';
    ctxgraph = c2.getContext('2d');
    gbuffer = ctx.getImageData(0, 0, canvasN, canvasN);
    gbufferdata = gbuffer.data;

    Number.prototype.mod = function(n) {
        return ((this%n)+n)%n;
    }

    document.getElementById('label_temp_input').addEventListener("keydown", function(e) {
        if (e.keyCode == 13){
            e.preventDefault();
            step = document.getElementById('temp').step;
            min = document.getElementById('temp').min;
            tval = parseFloat(document.getElementById('label_temp_input').value);

            if (tval <= Math.pow(10, min))
                logval = min - 2*step;
            else
                logval = log10(tval);

            document.getElementById('temp').value = logval;
            update_temp();
            undotextbox('label_temp_input');
        }
    }, false);

    var tempBox = document.getElementById('temp_box');
    if (tempBox){
        tempBox.addEventListener("change", function(){
            var val = parseFloat(tempBox.value);
            if (!isNaN(val)){
                document.getElementById('temp').value = log10(val);
                update_temp();
            }
        });
    }

    document.getElementById('label_frames_input').addEventListener("keydown", function(e) {
        if (e.keyCode == 13){
            e.preventDefault();
            tval = parseFloat(document.getElementById('label_frames_input').value);
            document.getElementById('frames').value = log10(tval);
            update_frames();
            undotextbox('label_frames_input');
        }
    }, false);

    var frameBox = document.getElementById('frames_box');
    if (frameBox){
        frameBox.addEventListener("change", function(){
            var val = parseFloat(frameBox.value);
            if (!isNaN(val) && val>0){
                document.getElementById('frames').value = log10(val);
                update_frames();
            }
        });
    }

    document.getElementById('label_init_frac_input').addEventListener("keydown", function(e) {
        if (e.keyCode == 13){
            e.preventDefault();
            document.getElementById('init_frac').value = document.getElementById('label_init_frac_input').value;
            update_init_frac();
            undotextbox('label_init_frac_input');
        }
    }, false);

    var initFracBox = document.getElementById('init_frac_box');
    if (initFracBox){
        initFracBox.addEventListener("change", function(){
            var val = parseFloat(initFracBox.value);
            if (!isNaN(val)){
                document.getElementById('init_frac').value = val;
                update_init_frac();
            }
        });
    }

    document.getElementById('label_hI_input').addEventListener("keydown", function(e) {
        if (e.keyCode == 13){
            e.preventDefault();
            document.getElementById('hI').value = document.getElementById('label_hI_input').value;
            update_hI();
            undotextbox('label_hI_input');
        }
    }, false);

    var hIBox = document.getElementById('hI_box');
    if (hIBox){
        hIBox.addEventListener("change", function(){
            var val = parseFloat(hIBox.value);
            if (!isNaN(val)){
                document.getElementById('hI').value = val;
                update_hI();
            }
        });
    }

    document.getElementById('label_hR_input').addEventListener("keydown", function(e) {
        if (e.keyCode == 13){
            e.preventDefault();
            document.getElementById('hR').value = document.getElementById('label_hR_input').value;
            update_hR();
            undotextbox('label_hR_input');
        }
    }, false);

    var hRBox = document.getElementById('hR_box');
    if (hRBox){
        hRBox.addEventListener("change", function(){
            var val = parseFloat(hRBox.value);
            if (!isNaN(val)){
                document.getElementById('hR').value = val;
                update_hR();
            }
        });
    }

    var cornerProbInput = document.getElementById('label_corner_prob_input');
    if (cornerProbInput){
        cornerProbInput.addEventListener("keydown", function(e) {
            if (e.keyCode == 13){
                e.preventDefault();
                var val = parseFloat(cornerProbInput.value);
                if (!isNaN(val)){
                    document.getElementById('corner_prob').value = val;
                    update_corner_prob();
                }
                undotextbox('label_corner_prob_input');
            }
        }, false);
        cornerProbInput.addEventListener("change", function(){
            var val = parseFloat(cornerProbInput.value);
            if (!isNaN(val)){
                document.getElementById('corner_prob').value = val;
                update_corner_prob();
            }
        });
    }

    document.getElementById('label_J_SI_input').addEventListener("keydown", function(e) {
        if (e.keyCode == 13){
            e.preventDefault();
            document.getElementById('J_SI').value = document.getElementById('label_J_SI_input').value;
            update_J_SI();
            undotextbox('label_J_SI_input');
        }
    }, false);

    var JBox = document.getElementById('J_SI_box');
    if (JBox){
        JBox.addEventListener("change", function(){
            var val = parseFloat(JBox.value);
            if (!isNaN(val)){
                document.getElementById('J_SI').value = val;
                update_J_SI();
            }
        });
    }

    document.getElementById('label_loss_immunity_prob_input').addEventListener("keydown", function(e) {
        if (e.keyCode == 13){
            e.preventDefault();
            var val = parseFloat(document.getElementById('label_loss_immunity_prob_input').value);
            if (!isNaN(val)){
                document.getElementById('loss_immunity_prob').value = Math.log10(Math.max(val, 1e-12));
            }
            update_loss_immunity_prob();
            undotextbox('label_loss_immunity_prob_input');
        }
    }, false);

    var lossProbBox = document.getElementById('loss_immunity_prob_box');
    if (lossProbBox){
        lossProbBox.addEventListener("change", function(){
            var val = parseFloat(lossProbBox.value);
            if (!isNaN(val)){
                document.getElementById('loss_immunity_prob').value = Math.log10(Math.max(val, 1e-12));
                update_loss_immunity_prob();
            }
        });
    }
    clear();
    cleargraph();
    sync_init_controls();
    init_board(gN, null);
    update_display();

    document.body.addEventListener('keyup', function(ev) {
        if (ev.keyCode == 32){ ev.preventDefault(); update_pause(); } //space is pause
    }, false);

    document.body.addEventListener('keydown', function(ev) {
    }, false);

    registerAnimationRequest();
    requestAnimationFrame(tick, c);
};
window.onload = init;


// Provides requestAnimationFrame in a cross browser way.
function registerAnimationRequest() {
if ( !window.requestAnimationFrame ) {
    window.requestAnimationFrame = ( function() {
      return window.webkitRequestAnimationFrame ||
      window.mozRequestAnimationFrame ||
      window.oRequestAnimationFrame ||
      window.msRequestAnimationFrame ||
      function( /* function FrameRequestCallback */ callback, /* DOMElement Element */ element ) {
              window.setTimeout( callback, 1 );
      };
    } )();
}
}
