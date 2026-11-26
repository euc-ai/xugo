// The contents column of a long page. On a narrow screen it is folded
// above the text. As the page scrolls, the entry of the section being
// read is marked (aria-current): a section is being read from the moment
// its heading passes the line just under the top bar until the next
// shown heading does, and at the foot of the page the last shown section
// is. A section the page hides (the landmarks filter) is passed over,
// and a change of layout marks again as a scroll does.
(function () {
  "use strict";
  const toc = document.getElementById("toc");
  if (!toc) return;
  if (window.matchMedia("(max-width: 820px)").matches) toc.open = false;

  // The line a heading passes: the page's scroll-padding-top, where a
  // followed link puts its heading, and a little below it.
  const SLACK = 24;
  const column = toc.closest(".toc");
  const entries = [...toc.querySelectorAll('a[href^="#"]')]
    .map(link => [link, document.getElementById(decodeURIComponent(link.hash.slice(1)))])
    .filter(([, heading]) => heading);
  if (entries.length === 0) return;

  let marked = null;
  let queued = false;

  function mark() {
    queued = false;
    const padding = parseFloat(getComputedStyle(document.documentElement).scrollPaddingTop) || 0;
    const line = padding + SLACK;
    const shown = entries.filter(([, heading]) => heading.offsetParent !== null);
    let reading = null;
    for (const [link, heading] of shown) {
      if (heading.getBoundingClientRect().top > line) break;
      reading = link;
    }
    const root = document.documentElement;
    if (shown.length > 0 && window.scrollY > 0 && window.innerHeight + window.scrollY >= root.scrollHeight - 2) {
      reading = shown[shown.length - 1][0];
    }
    if (reading === marked) return;
    if (marked) marked.removeAttribute("aria-current");
    marked = reading;
    if (!reading) return;
    reading.setAttribute("aria-current", "true");
    // The column scrolls on its own when it is taller than the window:
    // the marked entry is kept inside it.
    if (column && column.scrollHeight > column.clientHeight) {
      const top = reading.offsetTop - column.offsetTop;
      if (top < column.scrollTop) column.scrollTop = top;
      else if (top + reading.offsetHeight > column.scrollTop + column.clientHeight) {
        column.scrollTop = top + reading.offsetHeight - column.clientHeight;
      }
    }
  }

  function queue() {
    if (queued) return;
    queued = true;
    requestAnimationFrame(mark);
  }

  addEventListener("scroll", queue, { passive: true });
  new ResizeObserver(queue).observe(document.body);
  mark();
})();
