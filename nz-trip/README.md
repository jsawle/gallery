# South Island Slow Loop

An editable map of a relaxed South Island road trip, 6 December 2026 to 23 January 2027. The trip starts and ends at Christchurch Airport.

Live at **https://jsawle.github.io/gallery/nz-trip/**

## What it does
- Shows each overnight stop with its dates, nights and things to do, plus places to visit nearby.
- Measures road distances and drive times with OSRM routing on OpenStreetMap roads.
- Lets you edit the trip: turn on **Edit** to drag pins, add or delete stops and places, change nights, or reorder stops.
- Works on phones (draggable bottom panel) and computers (side panels) from the same page.
- Saves edits in your browser. Use **More → Copy share link** or **Download itinerary** to pass them to someone else.

## Files
- `index.html`, `app.css`, `app.js`: the app
- `data/trip.json`: the default itinerary (edit this to change the plan for everyone)
- `data/nz-coast.js`: coastline used if the map tiles can't load

## Services (all free, none Esri, none in sanctioned countries)
- MapLibre GL JS (open source)
- OpenFreeMap tiles: OpenStreetMap data, hosted in the EU
- Sentinel-2 cloudless satellite imagery by EOX (Austria)
- OSRM routing on the FOSSGIS server (Germany), with the OSRM demo server as a fallback
- Nominatim search (OpenStreetMap Foundation)
- Photos: main image of each place's Wikipedia article, from Wikimedia Commons, credited on each photo
- Place and directions links open Google Maps
- Each place links to its official site, DOC page or regional tourism page (all checked when added)

## Releasing
When changing `app.js` or `app.css`, bump `APP_VERSION` in `app.js` and the `?v=` numbers in `index.html` to match, so browsers load the new files together.

## Versions
| Part | Version |
|---|---|
| App | 3.3.0 |
| Itinerary data | 1.2 |
| Road routing | 1.0 |
| Date calculator | 1.0 |
| Photos | 1.1 |
| Links | 1.0 |

