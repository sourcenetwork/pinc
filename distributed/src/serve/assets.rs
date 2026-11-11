//! The dashboard's pages, styles, scripts and fonts, compiled into the binary from `distributed/web/`.

macro_rules! assets {
    (text { $($path:literal => $ctype:literal),* $(,)? } bytes { $($bpath:literal => $bctype:literal),* $(,)? }) => {
        /// The asset at `path` (`/` is the page) with its content type.
        pub(crate) fn get(path: &str) -> Option<(&'static str, &'static [u8])> {
            let path = if path == "/" { "/index.html" } else { path };
            match path {
                $(concat!("/", $path) => Some(($ctype, include_str!(concat!("../../web/", $path)).as_bytes())),)*
                $(concat!("/", $bpath) => Some(($bctype, include_bytes!(concat!("../../web/", $bpath)).as_slice())),)*
                _ => None,
            }
        }
    };
}

assets! {
    text {
        "index.html" => "text/html; charset=utf-8",
        "style.css" => "text/css; charset=utf-8",
        "app.js" => "text/javascript; charset=utf-8",
        "lib/dom.js" => "text/javascript; charset=utf-8",
        "lib/fmt.js" => "text/javascript; charset=utf-8",
        "lib/topo.js" => "text/javascript; charset=utf-8",
        "lib/chart.js" => "text/javascript; charset=utf-8",
        "views/compose.js" => "text/javascript; charset=utf-8",
        "views/live.js" => "text/javascript; charset=utf-8",
        "views/results.js" => "text/javascript; charset=utf-8",
        "views/host.js" => "text/javascript; charset=utf-8",
        "favicon.svg" => "image/svg+xml",
        "fonts/OFL.txt" => "text/plain; charset=utf-8",
    }
    bytes {
        "fonts/plex-sans-400.woff2" => "font/woff2",
        "fonts/plex-sans-500.woff2" => "font/woff2",
        "fonts/plex-sans-600.woff2" => "font/woff2",
        "fonts/plex-mono-400.woff2" => "font/woff2",
        "fonts/plex-mono-600.woff2" => "font/woff2",
    }
}
