/* South Island Slow Loop — app.js
   Map: MapLibre GL JS + OpenFreeMap vector tiles (OpenStreetMap data); satellite from EOX Sentinel-2 cloudless.
   Road distances: OSRM car routing (FOSSGIS server, fallback OSRM demo server), cached in this browser.
   Place search: Nominatim (OpenStreetMap Foundation).
   Edits are saved in this browser (localStorage); share link and JSON download carry them elsewhere. */
"use strict";

const APP_VERSION = "3.2.0-lab";
const VERSIONS = [
  ["App", APP_VERSION, "Liquid-glass interface, editing of stops and places, share link, JSON import/export; phone layout with draggable bottom sheet (test version)"],
  ["Itinerary data", null, "Default South Island plan, 6 Dec 2026 – 23 Jan 2027 (version stored in the data)"],
  ["Road routing", "1.0", "OSRM car profile per leg; geometry thinned to ~60 m; cached per pair of points"],
  ["Date calculator", "1.0", "Arrival = start date + nights at earlier stops (UTC, no time zones)"],
  ["Photos", "1.0", "Main photo of each place's Wikipedia article, from Wikimedia Commons with credit and licence; maps, flags and logos skipped; non-free images skipped"],
];
const STORE_KEY = "nztrip-lab:trip:v1"; // test copy keeps its own saved edits
const CACHE_KEY = "nztrip:legs:v1";
const OSRM = [
  "https://routing.openstreetmap.de/routed-car/route/v1/driving/",
  "https://router.project-osrm.org/route/v1/driving/",
];
const BASEMAPS = {
  liberty: "https://tiles.openfreemap.org/styles/liberty",
  positron: "https://tiles.openfreemap.org/styles/positron",
  satellite: {
    version: 8,
    sources: { s2: { type: "raster", tileSize: 256, maxzoom: 14,
      tiles: ["https://tiles.maps.eox.at/wmts/1.0.0/s2cloudless-2020_3857/default/g/{z}/{y}/{x}.jpg"],
      attribution: '<a href="https://s2maps.eu" target="_blank" rel="noopener">Sentinel-2 cloudless</a> by EOX IT Services GmbH (contains modified Copernicus Sentinel data 2020)' } },
    layers: [{ id: "s2", type: "raster", source: "s2" }],
  },
};
const POI_TYPES = {
  sight: ["📍", "Sight"], walk: ["🥾", "Walk"], view: ["⛰️", "Viewpoint"], wildlife: ["🐧", "Wildlife"],
  swim: ["🏊", "Swim / hot pools"], food: ["🍽️", "Food & drink"], activity: ["🎟️", "Activity"], stay: ["🛏️", "Place to stay"], other: ["•", "Other"],
};

/* ---------------- helpers ---------------- */
const $ = (s, r = document) => r.querySelector(s);
const esc = (s) => String(s ?? "").replace(/[&<>"']/g, (c) => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" }[c]));
const clone = (o) => JSON.parse(JSON.stringify(o));
const uid = (p) => p + Math.random().toString(36).slice(2, 8);
const css = (n) => getComputedStyle(document.documentElement).getPropertyValue(n).trim();
const reduceMotion = matchMedia("(prefers-reduced-motion: reduce)").matches;
const isPhone = () => innerWidth <= 760;
function lsGet(k) { try { return localStorage.getItem(k); } catch { return null; } }
function lsSet(k, v) { try { localStorage.setItem(k, v); return true; } catch { return false; } }
function lsDel(k) { try { localStorage.removeItem(k); } catch {} }
function fetchT(url, ms = 8000, opts = {}) {
  const c = new AbortController(); const t = setTimeout(() => c.abort(), ms);
  return fetch(url, { ...opts, signal: c.signal }).finally(() => clearTimeout(t));
}
function haversineKm(a, b) {
  const R = 6371, toR = Math.PI / 180;
  const dLat = (b.lat - a.lat) * toR, dLng = (b.lng - a.lng) * toR;
  const h = Math.sin(dLat / 2) ** 2 + Math.cos(a.lat * toR) * Math.cos(b.lat * toR) * Math.sin(dLng / 2) ** 2;
  return 2 * R * Math.asin(Math.sqrt(h));
}
function dur(min) {
  if (min == null) return "";
  const h = Math.floor(min / 60), m = Math.round(min % 60);
  return h ? `${h} h ${String(m).padStart(2, "0")}` : `${m} min`;
}
const MONTHS = ["Jan","Feb","Mar","Apr","May","Jun","Jul","Aug","Sep","Oct","Nov","Dec"];
function addDays(iso, n) { const d = new Date(iso + "T00:00:00Z"); d.setUTCDate(d.getUTCDate() + n); return d; }
function fmtD(d, year = false) { return `${d.getUTCDate()} ${MONTHS[d.getUTCMonth()]}${year ? " " + d.getUTCFullYear() : ""}`; }
function fmtRange(a, b) {
  if (+a === +b) return fmtD(a);
  return a.getUTCMonth() === b.getUTCMonth() ? `${a.getUTCDate()}–${fmtD(b)}` : `${fmtD(a)} – ${fmtD(b)}`;
}
function daysBetween(isoA, isoB) { return Math.round((new Date(isoB + "T00:00:00Z") - new Date(isoA + "T00:00:00Z")) / 86400000); }

/* ---------------- state ---------------- */
let trip = null, original = null;
let legs = [];            // legs[i] = route into stop i (i >= 1)
let sel = null;           // {type:'stop', id} | {type:'poi', stopId, id}
let editing = false;
let pick = null;          // null | 'stop' | 'poi'
let routeGen = 0;
let bakedMap = {};
let legCache = {};
let map, baseKey = "liberty";
const stopMarkers = new Map(), poiMarkers = new Map();

function pairKey(a, b) { return `${(+a.lng).toFixed(4)},${(+a.lat).toFixed(4)};${(+b.lng).toFixed(4)},${(+b.lat).toFixed(4)}`; }
function save() { lsSet(STORE_KEY, JSON.stringify(trip)); }
function stopById(id) { return trip.stops.find((s) => s.id === id); }
function stopIndex(id) { return trip.stops.findIndex((s) => s.id === id); }
function isAirport(s) { return s.kind === "airport"; }
function labelFor(i) {
  const s = trip.stops[i]; if (isAirport(s)) return "✈";
  let n = 0; for (let j = 0; j <= i; j++) if (!isAirport(trip.stops[j])) n++; return String(n);
}
function arrival(i) { let n = 0; for (let j = 0; j < i; j++) n += +trip.stops[j].nights || 0; return addDays(trip.start, n); }
function totalNights() { return trip.stops.reduce((a, s) => a + (+s.nights || 0), 0); }

/* ---------------- boot ---------------- */
async function boot() {
  try { legCache = JSON.parse(lsGet(CACHE_KEY) || "{}"); } catch { legCache = {}; }
  try {
    const r = await fetch("data/trip.json", { cache: "no-cache" });
    original = await r.json();
  } catch (e) { original = null; }
  if (original) for (let i = 1; i < original.stops.length; i++) {
    const b = original.stops[i].baked; if (b) bakedMap[pairKey(original.stops[i - 1], original.stops[i])] = b;
  }
  // Shared link?
  const m = location.hash.match(/^#t=(.+)$/);
  let shared = null;
  if (m && window.LZString) { try { shared = JSON.parse(LZString.decompressFromEncodedURIComponent(m[1])); } catch {} }
  const stored = lsGet(STORE_KEY);
  if (shared && valid(shared)) { trip = shared; showSharedBanner(); }
  else if (stored) { try { trip = JSON.parse(stored); } catch {} }
  if (!trip || !valid(trip)) trip = clone(original);
  else if (original) {            // older saved copies have no photo links: borrow them from the original by id
    const byId = {}; original.stops.forEach((s) => { byId[s.id] = s; (s.pois || []).forEach((p) => (byId[p.id] = p)); });
    trip.stops.forEach((s) => { [s, ...(s.pois || [])].forEach((o) => { if (!o.wiki && !o.img && byId[o.id] && byId[o.id].wiki && byId[o.id].name === o.name) o.wiki = byId[o.id].wiki; }); });
  }
  if (!trip) { toast("Couldn't load the itinerary. Check your connection and reload."); return; }

  await initMap();
  renderAll();
  fitAll(false);
  routeAll();
  loadPhotos();
}
function valid(t) { return t && Array.isArray(t.stops) && t.stops.length >= 2 && t.start && t.stops.every((s) => isFinite(s.lat) && isFinite(s.lng)); }

/* ---------------- map ---------------- */
async function resolveStyle(key) {
  const src = BASEMAPS[key];
  if (typeof src !== "string") return clone(src);
  try { const r = await fetchT(src, 7000); if (!r.ok) throw 0; return await r.json(); }
  catch { toast("Map tiles aren't reachable right now, so the map shows a plain outline."); return fallbackStyle(); }
}
function fallbackStyle() {
  return { version: 8, sources: { coast: { type: "geojson", data: { type: "Feature", properties: {}, geometry: window.NZ_COAST } } },
    layers: [
      { id: "bg", type: "background", paint: { "background-color": css("--map-bg") } },
      { id: "land", type: "fill", source: "coast", paint: { "fill-color": css("--land") } },
      { id: "edge", type: "line", source: "coast", paint: { "line-color": css("--land-edge"), "line-width": 1 } },
    ] };
}
async function initMap() {
  const style = await resolveStyle(baseKey);
  map = new maplibregl.Map({
    container: "map", style, center: [171.2, -43.6], zoom: 5.4, minZoom: 4, maxBounds: [[160, -50], [182, -36]],
    attributionControl: { compact: true }, cooperativeGestures: false,
  });
  map.addControl(new maplibregl.NavigationControl({ visualizePitch: false }), "top-right");
  map.addControl(new maplibregl.ScaleControl({ unit: "metric" }), "bottom-left");
  map.on("style.load", addOverlays);
  map.on("click", onMapClick);
  await new Promise((res) => map.once("load", res));
}
function addOverlays() {
  if (map.getSource("route")) return;
  map.addSource("route", { type: "geojson", data: routeGeoJSON() });
  map.addLayer({ id: "route-casing", type: "line", source: "route", layout: { "line-join": "round", "line-cap": "round" },
    paint: { "line-color": css("--route-casing"), "line-width": 7, "line-opacity": 0.85 } });
  map.addLayer({ id: "route-live", type: "line", source: "route", filter: ["!=", ["get", "approx"], true], layout: { "line-join": "round", "line-cap": "round" },
    paint: { "line-color": css("--route"), "line-width": 4 } });
  map.addLayer({ id: "route-approx", type: "line", source: "route", filter: ["==", ["get", "approx"], true], layout: { "line-join": "round" },
    paint: { "line-color": css("--route"), "line-width": 3.5, "line-dasharray": [1.5, 1.5] } });
}
async function setBase(key) {
  baseKey = key;
  document.querySelectorAll("#menu-layers [data-base]").forEach((b) => b.setAttribute("aria-checked", String(b.dataset.base === key)));
  map.setStyle(await resolveStyle(key));
}
function padding() {
  if (isPhone()) {
    const top = $(".card-summary").getBoundingClientRect().bottom + 10;
    const sh = activeSheet().getBoundingClientRect();
    return { top, bottom: Math.max(80, innerHeight - sh.top + 10), left: 24, right: 24 };
  }
  return { top: 40, bottom: 90, left: 380, right: $("#detail").hidden ? 60 : 420 };
}
function fitAll(animate = true) {
  const b = new maplibregl.LngLatBounds();
  trip.stops.forEach((s) => b.extend([s.lng, s.lat]));
  map.fitBounds(b, { padding: padding(), duration: animate && !reduceMotion ? 800 : 0, maxZoom: 9 });
}
function flyTo(lng, lat, zoom) {
  map.easeTo({ center: [lng, lat], zoom: Math.max(map.getZoom(), zoom || 8), padding: padding(), duration: reduceMotion ? 0 : 700 });
}

/* ---------------- photos (Wikipedia / Wikimedia Commons) ---------------- */
const IMG_KEY = "nztrip:img:v1";
let imgCache = {};
try { imgCache = JSON.parse(lsGet(IMG_KEY) || "{}"); } catch { imgCache = {}; }
const BAD_IMG = /\.svg$|(^|[ _\-(:])(map|maps|locator|location|flag|logo|emblem|seal[ _]of|coat[ _]of[ _]arms|montage)([ _\-).]|$)/i;
function photoKey(o) { if (o.img) return o.img; return o.wiki ? "w:" + o.wiki : null; }
function photo(o) { const k = photoKey(o); const v = k && imgCache[k]; return v && !v.none ? v : null; }
function textOf(html) { const d = new DOMParser().parseFromString(String(html || ""), "text/html"); return (d.body.textContent || "").replace(/\s+/g, " ").trim(); }
const nk = (s) => String(s).replace(/_/g, " ");
function chunks(a, n) { const o = []; for (let i = 0; i < a.length; i += n) o.push(a.slice(i, i + n)); return o; }
let photoBusy = false;
async function loadPhotos() {
  if (photoBusy) return; photoBusy = true;
  try {
    const items = []; trip.stops.forEach((s) => { items.push(s); (s.pois || []).forEach((p) => items.push(p)); });
    const now = Date.now(), TTL = 30 * 864e5;
    const need = [...new Set(items.map(photoKey).filter((k) => k && (!imgCache[k] || now - imgCache[k].t > TTL)))];
    if (!need.length) return;
    const fileFor = {}; const resolved = new Set();
    need.filter((k) => /^https:\/\//.test(k)).forEach((k) => { imgCache[k] = { src: k, page: k, credit: "", license: "", t: now }; });
    need.filter((k) => /^File:/i.test(k)).forEach((k) => { fileFor[k] = k; resolved.add(k); });
    // 1. Wikipedia article -> its main image file
    for (const chunk of chunks(need.filter((k) => k.startsWith("w:")).map((k) => k.slice(2)), 40)) {
      try {
        const u = "https://en.wikipedia.org/w/api.php?action=query&format=json&origin=*&redirects=1&prop=pageimages&piprop=name&titles=" + encodeURIComponent(chunk.join("|"));
        const q = (await (await fetchT(u, 12000)).json()).query || {};
        const fwd = {}; chunk.forEach((x) => (fwd[x] = x));
        (q.normalized || []).forEach((n) => { for (const k in fwd) if (fwd[k] === n.from) fwd[k] = n.to; });
        (q.redirects || []).forEach((n) => { for (const k in fwd) if (fwd[k] === n.from) fwd[k] = n.to; });
        const pages = {}; Object.values(q.pages || {}).forEach((pg) => (pages[pg.title] = pg));
        chunk.forEach((orig) => { const pg = pages[fwd[orig]]; fileFor["w:" + orig] = pg && pg.pageimage ? "File:" + pg.pageimage : null; resolved.add("w:" + orig); });
      } catch {}
    }
    // 2. Commons: image URL, author and licence (non-free local files are not on Commons, so they drop out)
    const files = [...new Set(Object.values(fileFor).filter((f) => f && !BAD_IMG.test(f)))];
    const info = {}; const infoOk = new Set();
    for (const chunk of chunks(files, 40)) {
      try {
        const u = "https://commons.wikimedia.org/w/api.php?action=query&format=json&origin=*&prop=imageinfo&iiprop=url|extmetadata&iiurlwidth=900&iiextmetadatafilter=Artist|LicenseShortName&titles=" + encodeURIComponent(chunk.join("|"));
        const q = (await (await fetchT(u, 12000)).json()).query || {};
        const back = {}; (q.normalized || []).forEach((n) => (back[n.to] = n.from));
        Object.values(q.pages || {}).forEach((pg) => {
          const ii = pg.imageinfo && pg.imageinfo[0]; const md = (ii && ii.extmetadata) || {};
          const v = ii ? { src: ii.thumburl || ii.url, page: ii.descriptionurl, credit: textOf(md.Artist && md.Artist.value).slice(0, 80), license: textOf(md.LicenseShortName && md.LicenseShortName.value) } : null;
          [pg.title, back[pg.title]].forEach((tt) => { if (tt) { info[nk(tt)] = v; infoOk.add(nk(tt)); } });
        });
      } catch {}
    }
    for (const k of need) {
      if (/^https:/.test(k) || !resolved.has(k)) continue;           // unresolved = network failure: try again next load
      const f = fileFor[k];
      if (!f || BAD_IMG.test(f)) { imgCache[k] = { none: true, t: now }; continue; }
      if (!infoOk.has(nk(f))) continue;
      imgCache[k] = info[nk(f)] ? { ...info[f], t: now } : { none: true, t: now };
    }
    lsSet(IMG_KEY, JSON.stringify(imgCache));
    renderList(); if (detailMode === "view") renderDetail();
  } finally { photoBusy = false; }
}
function heroHtml(o, name) {
  const ph = photo(o); if (!ph) return "";
  const credit = [ph.credit, ph.license].filter(Boolean).join(" · ");
  return `<figure class="hero"><img src="${esc(ph.src)}" alt="Photo of ${esc(name)}" loading="lazy" decoding="async" onerror="this.parentNode.remove()">
    <figcaption><a href="${esc(ph.page)}" target="_blank" rel="noopener">${credit ? "Photo: " + esc(credit) : "Photo source"}</a>${ph.page && ph.page.includes("wikimedia") ? " · Wikimedia Commons" : ""}</figcaption></figure>`;
}
function thumbHtml(o, cls = "thumb") { const ph = photo(o); return ph ? `<img class="${cls}" src="${esc(ph.src)}" alt="" loading="lazy" decoding="async" onerror="this.style.visibility='hidden'">` : ""; }
function setPhotoFrom(o, val) {
  val = val.trim();
  delete o.img;
  if (!val) { delete o.wiki; return; }
  if (/^https:\/\//.test(val) && !/wikipedia\.org\/wiki\//.test(val)) o.img = val;
  else if (/^File:/i.test(val)) o.img = val;
  else o.wiki = decodeURIComponent(val.replace(/^https:\/\/en\.(m\.)?wikipedia\.org\/wiki\//, "")).replace(/_/g, " ");
}
function photoField(o, id) {
  return `<label>Photo: Wikipedia article, Commons file or image link<input id="${id}" value="${esc(o.img || o.wiki || "")}" placeholder="e.g. Lake Tekapo"></label>`;
}

/* ---------------- Google Maps links ---------------- */
function gmapsPlace(o) {
  const generic = /^(new (stop|place)|untitled)/i.test(o.name || "");
  const q = generic ? `${o.lat},${o.lng}` : `${o.name.replace(/ · /g, ", ").replace(/ & /g, " ")}, New Zealand`;
  return "https://www.google.com/maps/search/?api=1&query=" + encodeURIComponent(q);
}
function gmapsDir(a, b) {
  return `https://www.google.com/maps/dir/?api=1&origin=${a.lat},${a.lng}&destination=${b.lat},${b.lng}&travelmode=driving`;
}

/* ---------------- routing ---------------- */
function thin(coords) {
  const out = []; let last = null;
  for (const c of coords) {
    const p = [Math.round(c[0] * 1e5) / 1e5, Math.round(c[1] * 1e5) / 1e5];
    if (!last || Math.hypot((p[0] - last[0]) * 0.72, p[1] - last[1]) > 0.0006) { out.push(p); last = p; }
  }
  const end = coords[coords.length - 1]; out.push([end[0], end[1]]);
  return out;
}
async function fetchLeg(a, b) {
  const k = pairKey(a, b);
  if (legCache[k]) return legCache[k];
  for (const base of OSRM) {
    try {
      const r = await fetchT(base + k + "?overview=full&geometries=geojson&alternatives=false&steps=false", 10000);
      if (!r.ok) continue;
      const j = await r.json(); if (j.code !== "Ok" || !j.routes?.length) continue;
      const rt = j.routes[0];
      const v = { km: rt.distance / 1000, min: rt.duration / 60, geom: thin(rt.geometry.coordinates) };
      legCache[k] = v;
      if (!lsSet(CACHE_KEY, JSON.stringify(legCache))) { legCache = { [k]: v }; lsSet(CACHE_KEY, JSON.stringify(legCache)); }
      return v;
    } catch {}
  }
  return null;
}
function provisionalLeg(a, b) {
  const k = pairKey(a, b);
  if (legCache[k]) return { ...legCache[k], approx: false };
  const straight = [[a.lng, a.lat], [b.lng, b.lat]];
  if (bakedMap[k]) return { km: bakedMap[k].km, min: bakedMap[k].min, geom: straight, approx: true, baked: true };
  const km = haversineKm(a, b) * 1.35; // rough road factor until routing answers
  return { km, min: (km / 75) * 60, geom: straight, approx: true };
}
async function routeAll() {
  const gen = ++routeGen;
  const st = trip.stops;
  legs = st.map((s, i) => (i ? provisionalLeg(st[i - 1], s) : null));
  refreshRoute();
  for (let i = 1; i < st.length; i++) {
    if (legs[i] && !legs[i].approx) continue;
    const v = await fetchLeg(st[i - 1], st[i]);
    if (gen !== routeGen) return;
    if (v) { legs[i] = { ...v, approx: false }; refreshRoute(); }
    await new Promise((r) => setTimeout(r, 250)); // be gentle with the free routing servers
  }
}
function routeGeoJSON() {
  return { type: "FeatureCollection", features: legs.map((l, i) => l && ({
    type: "Feature", properties: { i, approx: !!l.approx }, geometry: { type: "LineString", coordinates: l.geom } })).filter(Boolean) };
}
function refreshRoute() {
  map.getSource("route")?.setData(routeGeoJSON());
  renderSummary(); renderList(); if (sel && detailMode === "view") renderDetail();
}

/* ---------------- rendering ---------------- */
function renderAll() { renderSummary(); renderList(); renderMarkers(); renderDetail(); }

function renderSummary() {
  const end = addDays(trip.start, totalNights());
  $("#trip-title").textContent = trip.title || "Trip";
  document.title = trip.title || "Trip";
  $("#trip-dates").textContent = `${fmtD(addDays(trip.start, 0), true)} – ${fmtD(end, true)}`;
  $("#st-nights").textContent = totalNights();
  const live = legs.filter(Boolean);
  const km = live.reduce((a, l) => a + l.km, 0), min = live.reduce((a, l) => a + l.min, 0);
  $("#st-km").textContent = live.length ? Math.round(km).toLocaleString("en-NZ") : "–";
  $("#st-drive").textContent = live.length ? `${Math.round(min / 60)} h` : "–";
  const target = trip.end ? daysBetween(trip.start, trip.end) : null;
  const chip = $("#st-fit"); const diff = target == null ? 0 : totalNights() - target;
  const approxN = live.filter((l) => l.approx).length;
  let text, cls;
  if (target == null || diff === 0) { text = `Fits ${fmtD(addDays(trip.start, 0))} – ${fmtD(end)}`; cls = "ok"; }
  else if (diff > 0) { text = `${diff} night${diff > 1 ? "s" : ""} past ${fmtD(addDays(trip.end, 0))}`; cls = "warn"; }
  else { text = `${-diff} night${diff < -1 ? "s" : ""} still to plan`; cls = "warn"; }
  if (approxN) text += ` · ${approxN} distance${approxN > 1 ? "s" : ""} approx.`;
  chip.textContent = text; chip.className = "chip " + cls;
}

function legText(i) {
  const l = legs[i]; if (!l) return "";
  return `${Math.round(l.km)} km · ${dur(l.min)}`;
}

function renderList() {
  const ol = $("#stop-list"); const keepScroll = ol.scrollTop;
  ol.innerHTML = "";
  let region = null;
  trip.stops.forEach((s, i) => {
    if (s.region && s.region !== region) {
      region = s.region;
      const h = document.createElement("li"); h.className = "region"; h.textContent = region; h.setAttribute("aria-hidden", "true"); ol.appendChild(h);
    }
    if (i > 0 && legs[i]) {
      const l = document.createElement("li"); l.className = "leg" + (legs[i].approx ? " approx" : "");
      l.textContent = legText(i); l.setAttribute("aria-hidden", "true"); ol.appendChild(l);
    }
    const a = arrival(i), d = arrival(i + 1);
    const li = document.createElement("li");
    const btn = document.createElement("button");
    btn.className = "stop-btn"; btn.type = "button";
    const current = sel && (sel.id === s.id || sel.stopId === s.id);
    btn.setAttribute("aria-current", String(!!current));
    const dates = s.nights ? fmtRange(a, d) : fmtD(a);
    btn.setAttribute("aria-label", `${isAirport(s) ? "" : "Stop " + labelFor(i) + ", "}${s.name}, ${dates}${s.nights ? ", " + s.nights + " nights" : ""}${i > 0 && legs[i] ? ", " + legText(i) + " by road from previous stop" : ""}`);
    btn.innerHTML = `<span class="num${isAirport(s) ? " air" : ""}" aria-hidden="true">${labelFor(i)}</span>
      <span><div class="t">${esc(s.name)}</div><div class="d">${dates}${s.nights ? " · " + s.nights + " night" + (s.nights > 1 ? "s" : "") : ""}</div></span>
      <span class="n">${thumbHtml(s, "lthumb")}</span>`;
    btn.addEventListener("click", () => select({ type: "stop", id: s.id }, true));
    li.appendChild(btn); ol.appendChild(li);
  });
  const cr = document.createElement("li"); cr.className = "list-credit"; cr.textContent = "Created by Jason Sawle"; ol.appendChild(cr);
  ol.scrollTop = keepScroll;
}

function makePinEl(cls, label, aria) {
  // MapLibre positions the outer element with a CSS transform, so styling and scaling go on an inner element
  const el = document.createElement("div");
  el.tabIndex = 0; el.setAttribute("role", "button"); el.setAttribute("aria-label", aria);
  const inner = document.createElement("div"); inner.className = cls; inner.textContent = label; inner.setAttribute("aria-hidden", "true");
  el.appendChild(inner);
  return el;
}
function renderMarkers() {
  stopMarkers.forEach((m) => m.remove()); stopMarkers.clear();
  poiMarkers.forEach((m) => m.remove()); poiMarkers.clear();
  // POIs first so stop pins sit on top
  trip.stops.forEach((s) => (s.pois || []).forEach((p) => {
    const t = POI_TYPES[p.type] || POI_TYPES.other;
    const el = makePinEl("poi", t[0], `${p.name} (${t[1]}), near ${s.name}`);
    el.title = p.name;
    const m = new maplibregl.Marker({ element: el, draggable: editing }).setLngLat([p.lng, p.lat]).addTo(map);
    const go = (e) => { e.stopPropagation(); select({ type: "poi", stopId: s.id, id: p.id }, false); };
    el.addEventListener("click", go); el.addEventListener("keydown", (e) => { if (e.key === "Enter" || e.key === " ") { e.preventDefault(); go(e); } });
    m.on("dragend", () => { const ll = m.getLngLat(); p.lng = +ll.lng.toFixed(5); p.lat = +ll.lat.toFixed(5); save(); toast("Place moved"); });
    poiMarkers.set(p.id, m);
  }));
  const seen = new Map();
  trip.stops.forEach((s, i) => {
    const el = makePinEl("pin" + (isAirport(s) ? " air" : ""), labelFor(i), `${s.name}${isAirport(s) ? "" : ", stop " + labelFor(i)}`);
    el.title = s.name;
    // the same airport at start and end: draw once
    const k = `${s.lat},${s.lng}`; if (seen.has(k)) { stopMarkers.set(s.id, seen.get(k)); return; }
    const m = new maplibregl.Marker({ element: el, draggable: editing }).setLngLat([s.lng, s.lat]).addTo(map);
    seen.set(k, m);
    const go = (e) => { e.stopPropagation(); select({ type: "stop", id: s.id }, false); };
    el.addEventListener("click", go); el.addEventListener("keydown", (e) => { if (e.key === "Enter" || e.key === " ") { e.preventDefault(); go(e); } });
    m.on("dragend", () => {
      const ll = m.getLngLat();
      trip.stops.forEach((t) => { if (`${t.lat},${t.lng}` === k) { t.lng = +ll.lng.toFixed(5); t.lat = +ll.lat.toFixed(5); } });
      save(); renderMarkers(); routeAll(); toast("Stop moved. Recalculating road distances…");
    });
    stopMarkers.set(s.id, m);
  });
  highlightMarkers();
}
function highlightMarkers() {
  const inner = (m) => m?.getElement().firstElementChild;
  stopMarkers.forEach((m) => inner(m).classList.remove("on"));
  poiMarkers.forEach((m) => inner(m).classList.remove("on"));
  if (!sel) return;
  inner(sel.type === "stop" ? stopMarkers.get(sel.id) : poiMarkers.get(sel.id))?.classList.add("on");
}

/* ---------------- selection & detail ---------------- */
let detailMode = "view"; // view | edit | add | confirm
function select(s, fromList) {
  sel = s; detailMode = "view";
  if (isPhone() && document.body.dataset.sheet === "peek") setSheet("half");
  renderList(); highlightMarkers(); renderDetail();
  const target = s.type === "stop" ? stopById(s.id) : stopById(s.stopId)?.pois.find((p) => p.id === s.id);
  if (target) flyTo(target.lng, target.lat, s.type === "stop" ? 8 : 10);
  if (!fromList) $("#detail h3")?.focus();
}
function closeDetail() { sel = null; detailMode = "view"; $("#detail").hidden = true; document.body.classList.remove("has-detail"); renderList(); highlightMarkers(); if (isPhone()) setSheet("peek"); }

function renderDetail() {
  const panel = $("#detail"), box = $("#detail-body");
  if (detailMode === "add") return; // add panel renders itself
  document.body.classList.toggle("has-detail", !!sel);
  if (!sel) { panel.hidden = true; return; }
  if (panel.hidden && isPhone() && document.body.dataset.sheet === "peek") setSheet("half");
  panel.hidden = false;
  if (sel.type === "stop") {
    const i = stopIndex(sel.id); if (i < 0) return closeDetail();
    return detailMode === "edit" ? stopEditor(box, i) : stopView(box, i);
  }
  const s = stopById(sel.stopId); const p = s?.pois.find((x) => x.id === sel.id); if (!p) return closeDetail();
  return detailMode === "edit" ? poiEditor(box, s, p) : poiView(box, s, p);
}
const closeBtn = `<button class="icon-btn close" data-act="close" aria-label="Close details"><svg viewBox="0 0 24 24" aria-hidden="true"><path d="M6 6l12 12M18 6L6 18"/></svg></button>`;

function stopView(box, i) {
  const s = trip.stops[i]; const a = arrival(i), d = arrival(i + 1);
  const leg = i > 0 && legs[i];
  const pois = s.pois || [];
  box.innerHTML = `${closeBtn}${heroHtml(s, s.name)}
    <h3 tabindex="-1">${isAirport(s) ? "" : labelFor(i) + ". "}${esc(s.name)}</h3>
    <div class="meta">${s.nights ? fmtRange(a, d) + " · " + s.nights + " night" + (s.nights > 1 ? "s" : "") : fmtD(a)}${s.region ? " · " + esc(s.region) : ""}</div>
    ${leg ? `<p class="meta">From ${esc(trip.stops[i - 1].name)}: <strong>${Math.round(leg.km)} km</strong>, about ${dur(leg.min)} by road${leg.approx ? " (approximate, road route not loaded yet)" : ""}</p>` : ""}
    <p class="links"><a href="${gmapsPlace(s)}" target="_blank" rel="noopener">Open in Google Maps</a>${i > 0 ? `<span class="sep"> · </span><a href="${gmapsDir(trip.stops[i - 1], s)}" target="_blank" rel="noopener">Directions from ${esc(trip.stops[i - 1].name)}</a>` : ""}</p>
    ${s.highlights?.length ? `<ul>${s.highlights.map((h) => `<li>${esc(h)}</li>`).join("")}</ul>` : ""}
    ${s.tip ? `<div class="tip"><b>Tip</b> ${esc(s.tip)}</div>` : ""}
    ${pois.length ? `<div class="section-t">Places nearby</div><ul class="poi-list">${pois.map((p) => {
      const t = POI_TYPES[p.type] || POI_TYPES.other;
      return `<li><button class="poi-btn" data-poi="${p.id}">${thumbHtml(p) || `<span class="thumb ph" aria-hidden="true">${t[0]}</span>`}<span><div class="pn">${esc(p.name)}</div>${p.notes ? `<div class="pd">${esc(p.notes)}</div>` : ""}</span></button></li>`; }).join("")}</ul>` : ""}
    <div class="row">
      <button class="btn" data-act="prev" ${i === 0 ? "disabled" : ""}>← Previous</button>
      <button class="btn" data-act="next" ${i === trip.stops.length - 1 ? "disabled" : ""}>Next →</button>
      <span class="spacer"></span>
      ${editing ? `<button class="btn" data-act="add-poi">Add place</button><button class="btn primary" data-act="edit">Edit</button>` : ""}
    </div>`;
  wireDetail(box, i);
}
function stopEditor(box, i) {
  const s = trip.stops[i];
  const regions = [...new Set(trip.stops.map((x) => x.region).filter(Boolean))];
  box.innerHTML = `${closeBtn}
    <h3 tabindex="-1">Edit stop</h3>
    <form class="form" id="f-stop" autocomplete="off">
      <label>Name<input id="f-name" required value="${esc(s.name)}"></label>
      <div class="two">
        <label>Nights<input id="f-nights" type="number" min="0" max="60" step="1" value="${+s.nights || 0}"></label>
        <label>Region<input id="f-region" list="regions" value="${esc(s.region || "")}"></label>
      </div>
      <datalist id="regions">${regions.map((r) => `<option value="${esc(r)}">`).join("")}</datalist>
      <label>Things to do (one per line)<textarea id="f-hi">${esc((s.highlights || []).join("\n"))}</textarea></label>
      <label>Tip<textarea id="f-tip" style="min-height:60px">${esc(s.tip || "")}</textarea></label>
      ${photoField(s, "f-photo")}
      <p class="hint">To move this stop, drag its pin on the map. Arrives ${fmtD(arrival(i))}.</p>
    </form>
    <div class="row">
      <button class="btn" data-act="up" ${i === 0 ? "disabled" : ""} aria-label="Move earlier in the trip">↑ Earlier</button>
      <button class="btn" data-act="down" ${i === trip.stops.length - 1 ? "disabled" : ""} aria-label="Move later in the trip">↓ Later</button>
      <button class="btn danger" data-act="delete">Delete</button>
      <span class="spacer"></span>
      <button class="btn primary" data-act="done">Done</button>
    </div>
    <div class="row" id="confirm-row" hidden></div>`;
  const upd = () => {
    s.name = $("#f-name").value.trim() || "Untitled stop";
    s.nights = Math.max(0, Math.min(60, parseInt($("#f-nights").value, 10) || 0));
    s.region = $("#f-region").value.trim();
    s.highlights = $("#f-hi").value.split("\n").map((x) => x.trim()).filter(Boolean);
    s.tip = $("#f-tip").value.trim();
    save(); renderSummary(); renderList();
    const el = stopMarkers.get(s.id)?.getElement(); if (el) { el.title = s.name; el.setAttribute("aria-label", s.name); }
  };
  box.querySelectorAll("#f-stop input:not(#f-photo), #f-stop textarea").forEach((el) => el.addEventListener("input", upd));
  $("#f-photo").addEventListener("change", (e) => { setPhotoFrom(s, e.target.value); save(); loadPhotos(); toast("Photo updated"); });
  $("#f-stop").addEventListener("submit", (e) => { e.preventDefault(); detailMode = "view"; renderDetail(); });
  wireDetail(box, i);
}
function poiView(box, s, p) {
  const t = POI_TYPES[p.type] || POI_TYPES.other;
  box.innerHTML = `${closeBtn}${heroHtml(p, p.name)}
    <h3 tabindex="-1">${esc(p.name)}</h3>
    <div class="meta">${t[0]} ${t[1]} · near ${esc(s.name)}</div>
    ${p.notes ? `<p>${esc(p.notes)}</p>` : ""}
    <p class="links"><a href="${gmapsPlace(p)}" target="_blank" rel="noopener">Open in Google Maps</a><span class="sep"> · </span><a href="${gmapsDir(s, p)}" target="_blank" rel="noopener">Directions from ${esc(s.name)}</a></p>
    <div class="row">
      <button class="btn" data-act="back">← ${esc(s.name)}</button>
      <span class="spacer"></span>
      ${editing ? `<button class="btn primary" data-act="edit">Edit</button>` : ""}
    </div>`;
  wireDetail(box, stopIndex(s.id), p);
}
function poiEditor(box, s, p) {
  box.innerHTML = `${closeBtn}
    <h3 tabindex="-1">Edit place</h3>
    <form class="form" id="f-poi" autocomplete="off">
      <label>Name<input id="p-name" required value="${esc(p.name)}"></label>
      <label>Type<select id="p-type">${Object.entries(POI_TYPES).map(([k, v]) => `<option value="${k}" ${k === p.type ? "selected" : ""}>${v[0]} ${v[1]}</option>`).join("")}</select></label>
      <label>Belongs to stop<select id="p-stop">${trip.stops.map((x, j) => `<option value="${x.id}" ${x.id === s.id ? "selected" : ""}>${isAirport(x) ? "✈" : labelFor(j) + "."} ${esc(x.name)}</option>`).join("")}</select></label>
      <label>Notes<textarea id="p-notes">${esc(p.notes || "")}</textarea></label>
      ${photoField(p, "p-photo")}
      <p class="hint">To move this place, drag its icon on the map.</p>
    </form>
    <div class="row">
      <button class="btn danger" data-act="delete">Delete</button>
      <span class="spacer"></span>
      <button class="btn primary" data-act="done">Done</button>
    </div>
    <div class="row" id="confirm-row" hidden></div>`;
  const upd = () => {
    p.name = $("#p-name").value.trim() || "Untitled place";
    p.type = $("#p-type").value; p.notes = $("#p-notes").value.trim();
    const newStop = $("#p-stop").value;
    if (newStop !== s.id) {
      s.pois = s.pois.filter((x) => x.id !== p.id);
      const ns = stopById(newStop); ns.pois = ns.pois || []; ns.pois.push(p);
      sel = { type: "poi", stopId: newStop, id: p.id }; s = ns;
    }
    save(); renderMarkers(); renderList();
  };
  $("#p-photo").addEventListener("change", (e) => { setPhotoFrom(p, e.target.value); save(); loadPhotos(); toast("Photo updated"); });
  box.querySelectorAll("#f-poi input:not(#p-photo), #f-poi textarea, #f-poi select").forEach((el) => el.addEventListener(el.tagName === "SELECT" ? "change" : "input", upd));
  $("#f-poi").addEventListener("submit", (e) => { e.preventDefault(); detailMode = "view"; renderDetail(); });
  wireDetail(box, stopIndex(s.id), p);
}
function wireDetail(box, i, poi) {
  box.querySelectorAll("[data-poi]").forEach((b) => b.addEventListener("click", () => select({ type: "poi", stopId: trip.stops[i].id, id: b.dataset.poi }, true)));
  box.querySelectorAll("[data-act]").forEach((b) => b.addEventListener("click", () => {
    const act = b.dataset.act; const s = trip.stops[i];
    if (act === "close") closeDetail();
    else if (act === "prev") select({ type: "stop", id: trip.stops[i - 1].id }, true);
    else if (act === "next") select({ type: "stop", id: trip.stops[i + 1].id }, true);
    else if (act === "back") select({ type: "stop", id: s.id }, true);
    else if (act === "edit") { detailMode = "edit"; renderDetail(); $("#detail input")?.focus(); }
    else if (act === "done") { detailMode = "view"; renderDetail(); $("#detail h3")?.focus(); }
    else if (act === "add-poi") startPick("poi");
    else if (act === "up" || act === "down") {
      const j = act === "up" ? i - 1 : i + 1;
      [trip.stops[i], trip.stops[j]] = [trip.stops[j], trip.stops[i]];
      save(); renderMarkers(); routeAll(); renderDetail();
      toast(`Moved ${s.name} ${act === "up" ? "earlier" : "later"}`);
    }
    else if (act === "delete") confirmDelete(box, i, poi);
  }));
}
function confirmDelete(box, i, poi) {
  const row = $("#confirm-row", box); const s = trip.stops[i];
  const what = poi ? poi.name : s.name;
  const extra = !poi && s.pois?.length ? ` and its ${s.pois.length} place${s.pois.length > 1 ? "s" : ""}` : "";
  if (!poi && trip.stops.length <= 2) { toast("A trip needs at least two stops."); return; }
  row.hidden = false;
  row.innerHTML = `<span>Delete ${esc(what)}${extra}?</span><span class="spacer"></span><button class="btn danger" id="yes">Delete</button><button class="btn" id="no">Cancel</button>`;
  $("#no", row).onclick = () => { row.hidden = true; };
  $("#yes", row).focus();
  $("#yes", row).onclick = () => {
    if (poi) { s.pois = s.pois.filter((x) => x.id !== poi.id); sel = { type: "stop", id: s.id }; }
    else { trip.stops.splice(i, 1); sel = null; }
    detailMode = "view"; save(); renderMarkers(); renderDetail(); routeAll();
    toast(`Deleted ${what}`);
  };
}

/* ---------------- adding ---------------- */
function startPick(kind) {
  if (kind === "poi") {
    const stopId = sel?.type === "stop" ? sel.id : sel?.stopId;
    if (!stopId) { toast("Select a stop first, then add a place near it."); return; }
    pick = { kind, stopId };
  } else {
    let after = sel ? stopIndex(sel.type === "stop" ? sel.id : sel.stopId) : trip.stops.length - 2;
    if (after >= trip.stops.length - 1) after = trip.stops.length - 2;
    pick = { kind, after };
  }
  document.body.classList.add("picking", "has-detail");
  detailMode = "add";
  const box = $("#detail-body"); $("#detail").hidden = false;
  if (isPhone() && document.body.dataset.sheet !== "full") setSheet("half");
  const ctx = kind === "stop"
    ? `It will go after <strong>${esc(trip.stops[pick.after].name)}</strong>. Select a stop first to put it somewhere else.`
    : `It will be added to <strong>${esc(stopById(pick.stopId).name)}</strong>.`;
  box.innerHTML = `${closeBtn}
    <h3 tabindex="-1">Add ${kind === "stop" ? "an overnight stop" : "a place to visit"}</h3>
    <p class="hint">${ctx}</p>
    <form class="form" id="f-search" role="search">
      <label>Search for a place<input id="q" placeholder="${kind === "stop" ? "e.g. Akaroa" : "e.g. Hooker Valley Track"}" autocomplete="off"></label>
      <div class="row" style="margin-top:0"><button class="btn primary" type="submit">Search</button></div>
    </form>
    <ul class="results" id="results" aria-live="polite"></ul>
    <p class="hint">Or click the map where it should go.</p>
    <div class="row"><span class="spacer"></span><button class="btn" data-act="cancel">Cancel</button></div>`;
  $("#q").focus();
  box.querySelector('[data-act="close"]').onclick = cancelPick;
  box.querySelector('[data-act="cancel"]').onclick = cancelPick;
  $("#f-search").addEventListener("submit", async (e) => {
    e.preventDefault(); const q = $("#q").value.trim(); if (q.length < 2) return;
    const res = $("#results"); res.innerHTML = `<li class="hint">Searching…</li>`;
    try {
      const url = `https://nominatim.openstreetmap.org/search?format=jsonv2&extratags=1&countrycodes=nz&limit=6&accept-language=en&q=${encodeURIComponent(q)}`;
      const r = await fetchT(url, 9000, { headers: { Accept: "application/json" } });
      const j = await r.json();
      if (!j.length) { res.innerHTML = `<li class="hint">No matches in New Zealand. Try another spelling, or click the map.</li>`; return; }
      res.innerHTML = "";
      j.forEach((x) => {
        const li = document.createElement("li"); const b = document.createElement("button"); b.type = "button";
        b.textContent = x.display_name; li.appendChild(b); res.appendChild(li);
        const wp = x.extratags && x.extratags.wikipedia; const wiki = wp && /^en:/.test(wp) ? wp.slice(3) : null;
        b.onclick = () => place(+x.lon, +x.lat, x.name || x.display_name.split(",")[0], wiki);
      });
    } catch { res.innerHTML = `<li class="hint">Search isn't reachable right now. Click the map instead.</li>`; }
  });
  showBanner(`Click the map to place the new ${kind === "stop" ? "stop" : "place"}`, "Cancel", cancelPick);
}
function cancelPick() {
  pick = null; document.body.classList.remove("picking"); hideBanner();
  detailMode = "view"; renderDetail();
}
function onMapClick(e) {
  if (!pick) return;
  place(+e.lngLat.lng.toFixed(5), +e.lngLat.lat.toFixed(5), null);
}
function place(lng, lat, name, wiki) {
  const p = pick; pick = null; document.body.classList.remove("picking"); hideBanner();
  if (p.kind === "stop") {
    const prev = trip.stops[p.after];
    const s = { id: uid("s"), ...(wiki ? { wiki } : {}), name: name || "New stop", region: prev.region || "", lat, lng, nights: 2, highlights: [], tip: "", pois: [] };
    trip.stops.splice(p.after + 1, 0, s);
    sel = { type: "stop", id: s.id };
    toast(`Added ${s.name}. Set its nights to keep the dates right.`);
    routeAll();
  } else {
    const s = stopById(p.stopId); s.pois = s.pois || [];
    const poi = { id: uid("p"), ...(wiki ? { wiki } : {}), name: name || "New place", type: "sight", lat, lng, notes: "" };
    s.pois.push(poi); sel = { type: "poi", stopId: s.id, id: poi.id };
    toast(`Added ${poi.name}`);
  }
  detailMode = "edit"; save(); renderMarkers(); renderList(); renderSummary(); renderDetail(); loadPhotos();
  $("#detail input")?.focus();
}

/* ---------------- edit toggle, menus, share ---------------- */
function setEditing(on) {
  editing = on; document.body.classList.toggle("editing", on);
  $("#btn-edit").setAttribute("aria-pressed", String(on));
  stopMarkers.forEach((m) => m.setDraggable(on)); poiMarkers.forEach((m) => m.setDraggable(on));
  if (!on && pick) cancelPick();
  if (!on && detailMode === "edit") detailMode = "view";
  renderDetail();
  toast(on ? "Editing on: drag pins to move them, or add stops and places" : "Editing off. Changes are saved in this browser");
}
function toggleMenu(id, btn) {
  const m = $(id); const open = m.hidden;
  closeMenus(); if (!open) return;
  m.hidden = false; btn.setAttribute("aria-expanded", "true");
  m.querySelector("button, input")?.focus();
}
function closeMenus() {
  ["#menu-layers", "#menu-more"].forEach((s) => ($(s).hidden = true));
  ["#btn-layers", "#btn-more"].forEach((s) => $(s).setAttribute("aria-expanded", "false"));
}
let toastT;
function toast(msg) { const t = $("#toast"); t.textContent = msg; t.hidden = false; clearTimeout(toastT); toastT = setTimeout(() => (t.hidden = true), 3500); }
function showBanner(msg, btnText, fn, btn2Text, fn2) {
  const b = $("#banner");
  b.innerHTML = `<span>${esc(msg)}</span><button class="btn" id="bn1">${esc(btnText)}</button>${btn2Text ? `<button class="btn" id="bn2">${esc(btn2Text)}</button>` : ""}`;
  b.hidden = false; $("#bn1").onclick = fn; if (btn2Text) $("#bn2").onclick = fn2;
}
function hideBanner() { $("#banner").hidden = true; }
function showSharedBanner() {
  showBanner("You're looking at a shared itinerary", "Keep it", () => {
    save(); history.replaceState(null, "", location.pathname); hideBanner(); toast("Saved in this browser");
  }, "Use my own", () => {
    history.replaceState(null, "", location.pathname); location.reload();
  });
}
async function copyShare() {
  if (!window.LZString) { toast("Sharing isn't available right now."); return; }
  const url = `${location.origin}${location.pathname}#t=${LZString.compressToEncodedURIComponent(JSON.stringify(trip))}`;
  try { await navigator.clipboard.writeText(url); toast("Share link copied. Anyone opening it sees this version"); }
  catch { dialog(`<h3>Share link</h3><p>Copy this link:</p><textarea class="form" style="width:100%;min-height:120px" readonly>${esc(url)}</textarea><div class="row"><span class="spacer"></span><button class="btn primary" value="ok">Close</button></div>`); $("#dlg textarea").select(); }
}
function exportJSON() {
  const blob = new Blob([JSON.stringify(trip, null, 2)], { type: "application/json" });
  const a = document.createElement("a"); a.href = URL.createObjectURL(blob);
  a.download = (trip.title || "trip").toLowerCase().replace(/[^a-z0-9]+/g, "-") + ".json";
  document.body.appendChild(a); a.click(); a.remove(); setTimeout(() => URL.revokeObjectURL(a.href), 1000);
}
function importJSON(file) {
  const r = new FileReader();
  r.onload = () => {
    try { const t = JSON.parse(r.result); if (!valid(t)) throw 0;
      trip = t; sel = null; save(); renderAll(); routeAll(); fitAll(); loadPhotos(); toast("Itinerary loaded");
    } catch { toast("That file isn't an itinerary from this app."); }
  };
  r.readAsText(file);
}
function dialog(html, onOk) {
  const d = $("#dlg"); d.innerHTML = `<form method="dialog">${html}</form>`;
  d.onclose = () => { if (d.returnValue === "ok" && onOk) onOk(); };
  d.showModal();
}
function about() {
  const rows = VERSIONS.map(([n, v, desc]) => `<tr><td>${esc(n)}</td><td>${esc(v || trip.dataVersion || "1.0")}</td><td>${esc(desc)}</td></tr>`).join("");
  dialog(`<h3>About this map</h3>
    <p>A relaxed South Island road trip that starts and ends in Christchurch. Turn on <strong>Edit</strong> to change stops, nights and places. Changes are saved in this browser only. To pass them on, use <em>Copy share link</em> or <em>Download itinerary</em>.</p>
    <table><thead><tr><th>Part</th><th>Version</th><th>What it does</th></tr></thead><tbody>${rows}</tbody></table>
    <p class="hint">Map data © <a href="https://www.openstreetmap.org/copyright" target="_blank" rel="noopener">OpenStreetMap contributors</a>. Map tiles: <a href="https://openfreemap.org" target="_blank" rel="noopener">OpenFreeMap</a> / OpenMapTiles. Satellite: Sentinel-2 cloudless by EOX. Road distances: <a href="https://project-osrm.org" target="_blank" rel="noopener">OSRM</a> on the <a href="https://routing.openstreetmap.de" target="_blank" rel="noopener">FOSSGIS</a> server. Search: <a href="https://nominatim.org" target="_blank" rel="noopener">Nominatim</a>. Photos: <a href="https://commons.wikimedia.org" target="_blank" rel="noopener">Wikimedia Commons</a>, credited on each photo. Place links open Google Maps. Drive times are routing estimates without stops.</p>
    <p class="hint">Created by Jason Sawle.</p>
    <div class="row"><span class="spacer"></span><button class="btn primary" value="ok">Close</button></div>`);
}
function tripSettings() {
  dialog(`<h3>Trip dates and title</h3>
    <div class="form">
      <label>Title<input id="t-title" value="${esc(trip.title || "")}"></label>
      <div class="two"><label>Start<input id="t-start" type="date" value="${trip.start}"></label><label>End<input id="t-end" type="date" value="${trip.end || ""}"></label></div>
    </div>
    <div class="row"><span class="spacer"></span><button class="btn" value="cancel">Cancel</button><button class="btn primary" value="ok">Save</button></div>`, () => {
    trip.title = $("#t-title").value.trim() || trip.title;
    if ($("#t-start").value) trip.start = $("#t-start").value;
    trip.end = $("#t-end").value || null;
    save(); renderAll();
  });
}

/* ---------------- phone bottom sheet ---------------- */
function activeSheet() { return $("#detail").hidden ? $("#itinerary") : $("#detail"); }
function sheetHeights() {
  const bottomY = $(".toolbar").getBoundingClientRect().top - 8;
  const topY = Math.max(8, $(".card-summary").getBoundingClientRect().top);
  const full = Math.max(200, bottomY - topY);
  return { peek: Math.min(156, full), half: Math.min(Math.round(innerHeight * 0.5), full), full };
}
function setSheet(state) {
  if (!isPhone()) return;
  document.body.dataset.sheet = state;
  const h = sheetHeights()[state];
  document.documentElement.style.setProperty("--sheet-h", h + "px");
  document.querySelectorAll(".grab").forEach((g) => g.setAttribute("aria-label", `Resize panel (now ${state === "peek" ? "small" : state === "half" ? "half screen" : "full screen"})`));
  $("#btn-collapse").setAttribute("aria-expanded", String(state !== "peek"));
}
function initSheets() {
  const order = ["peek", "half", "full"];
  document.querySelectorAll(".grab").forEach((g) => {
    let y0 = null, h0 = 0, el = null, moved = false;
    g.addEventListener("pointerdown", (e) => {
      if (!isPhone()) return;
      el = g.closest(".sheet"); y0 = e.clientY; h0 = el.getBoundingClientRect().height; moved = false;
      g.setPointerCapture(e.pointerId); el.classList.add("dragging");
    });
    g.addEventListener("pointermove", (e) => {
      if (y0 == null) return;
      const dy = y0 - e.clientY; if (Math.abs(dy) > 5) moved = true;
      el.style.height = Math.max(60, Math.min(sheetHeights().full, h0 + dy)) + "px";
    });
    const end = () => {
      if (y0 == null) return;
      const h = el.getBoundingClientRect().height; y0 = null;
      el.style.height = ""; el.classList.remove("dragging");
      const cur = document.body.dataset.sheet || "peek";
      if (!moved) { setSheet(cur === "peek" ? "half" : "peek"); return; }
      const hs = sheetHeights();
      if (el.id === "detail" && h < hs.peek * 0.6) { closeDetail(); return; }   // swipe down to close details
      let best = "peek"; for (const k of order) if (Math.abs(hs[k] - h) < Math.abs(hs[best] - h)) best = k;
      setSheet(best);
    };
    g.addEventListener("pointerup", end); g.addEventListener("pointercancel", end);
    g.addEventListener("keydown", (e) => {
      const i = order.indexOf(document.body.dataset.sheet || "peek");
      if (e.key === "ArrowUp") { e.preventDefault(); setSheet(order[Math.min(2, i + 1)]); }
      else if (e.key === "ArrowDown") { e.preventDefault(); setSheet(order[Math.max(0, i - 1)]); }
      else if (e.key === "Enter" || e.key === " ") { e.preventDefault(); setSheet(order[(i + 1) % 3]); }
    });
  });
  setSheet("peek");
  let rt; addEventListener("resize", () => { clearTimeout(rt); rt = setTimeout(() => setSheet(document.body.dataset.sheet || "peek"), 150); });
}

/* ---------------- wiring ---------------- */
function wire() {
  $("#btn-fit").onclick = () => { closeMenus(); fitAll(); };
  $("#btn-edit").onclick = () => setEditing(!editing);
  $("#btn-add-stop").onclick = () => startPick("stop");
  $("#btn-add-poi").onclick = () => startPick("poi");
  $("#btn-layers").onclick = (e) => toggleMenu("#menu-layers", e.currentTarget);
  $("#btn-more").onclick = (e) => toggleMenu("#menu-more", e.currentTarget);
  document.querySelectorAll("#menu-layers [data-base]").forEach((b) => (b.onclick = () => { closeMenus(); setBase(b.dataset.base); }));
  $("#chk-pois").onchange = (e) => document.body.classList.toggle("hide-pois", !e.target.checked);
  $("#btn-share").onclick = () => { closeMenus(); copyShare(); };
  $("#btn-export").onclick = () => { closeMenus(); exportJSON(); };
  $("#btn-import").onclick = () => { closeMenus(); $("#file-import").click(); };
  $("#file-import").onchange = (e) => { if (e.target.files[0]) importJSON(e.target.files[0]); e.target.value = ""; };
  $("#btn-reset").onclick = () => { closeMenus(); if (!original) return;
    dialog(`<h3>Reset to the original plan?</h3><p>This replaces every change saved in this browser.</p><div class="row"><span class="spacer"></span><button class="btn" value="cancel">Cancel</button><button class="btn danger" value="ok">Reset</button></div>`,
      () => { trip = clone(original); sel = null; save(); renderAll(); routeAll(); fitAll(); loadPhotos(); toast("Back to the original plan"); }); };
  $("#btn-about").onclick = () => { closeMenus(); about(); };
  const settings = document.createElement("button"); settings.setAttribute("role", "menuitem"); settings.textContent = "Trip dates and title…";
  settings.className = "edit-only"; settings.onclick = () => { closeMenus(); tripSettings(); };
  $("#menu-more").insertBefore(settings, $("#btn-share"));
  $("#btn-collapse").onclick = (e) => {
    if (isPhone()) { setSheet(document.body.dataset.sheet === "peek" ? "half" : "peek"); return; }
    const p = $("#itinerary"); const c = p.classList.toggle("collapsed");
    e.currentTarget.setAttribute("aria-expanded", String(!c));
    try { localStorage.setItem("nztrip:list-collapsed", c ? "1" : "0"); } catch {}
  };
  if (lsGet("nztrip:list-collapsed") === "1" && !isPhone()) { $("#itinerary").classList.add("collapsed"); $("#btn-collapse").setAttribute("aria-expanded", "false"); }
  document.addEventListener("keydown", (e) => {
    if (e.key !== "Escape") return;
    if (!$("#menu-layers").hidden || !$("#menu-more").hidden) closeMenus();
    else if (pick) cancelPick();
    else if (sel) closeDetail();
  });
  document.addEventListener("click", (e) => { if (!e.target.closest(".menu, #btn-layers, #btn-more")) closeMenus(); });
  matchMedia("(prefers-color-scheme: dark)").addEventListener("change", () => setBase(baseKey));
}
wire();
initSheets();
boot();
