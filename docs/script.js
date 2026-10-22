// LLM MC #1 showcase site — small, dependency-free interactivity.

(function () {
  "use strict";

  // ---- theme toggle ----
  // The page ships with data-theme="dark" on <html> as the default look.
  // Only touch that attribute once the visitor has an explicit stored
  // preference, or clicks the toggle — never clobber the shipped default.
  var root = document.documentElement;
  var toggle = document.getElementById("themeToggle");

  function readStoredTheme() {
    try {
      return localStorage.getItem("llmmc-theme");
    } catch (e) {
      return null;
    }
  }
  function storeTheme(v) {
    try {
      localStorage.setItem("llmmc-theme", v);
    } catch (e) {
      /* private browsing / blocked storage: just skip persistence */
    }
  }
  function currentIsDark() {
    var attr = root.getAttribute("data-theme");
    return attr ? attr === "dark" : true; // default ships dark
  }
  function setIconFor(isDark) {
    if (!toggle) return;
    toggle.textContent = isDark ? "☀" : "☽"; // sun / crescent moon
    toggle.setAttribute("aria-label", isDark ? "Switch to light theme" : "Switch to dark theme");
  }

  var stored = readStoredTheme();
  if (stored === "dark" || stored === "light") {
    root.setAttribute("data-theme", stored);
  }
  setIconFor(currentIsDark());

  if (toggle) {
    toggle.addEventListener("click", function () {
      var next = currentIsDark() ? "light" : "dark";
      root.setAttribute("data-theme", next);
      storeTheme(next);
      setIconFor(next === "dark");
    });
  }

  // ---- mobile nav ----
  var navToggle = document.querySelector(".navToggle");
  var navLinks = document.querySelector(".navlinks");
  if (navToggle && navLinks) {
    navToggle.addEventListener("click", function () {
      navLinks.classList.toggle("open");
    });
    navLinks.querySelectorAll("a").forEach(function (a) {
      a.addEventListener("click", function () {
        navLinks.classList.remove("open");
      });
    });
  }

  // ---- copy the quick-start command ----
  document.querySelectorAll("button.copy").forEach(function (btn) {
    btn.addEventListener("click", function () {
      var targetId = btn.getAttribute("data-copy-target");
      var el = targetId && document.getElementById(targetId);
      if (!el) return;
      var text = el.textContent.replace(/^\$\s*/gm, "").trim();
      var done = function () {
        var original = btn.textContent;
        btn.textContent = "copied";
        setTimeout(function () {
          btn.textContent = original;
        }, 1400);
      };
      if (navigator.clipboard && navigator.clipboard.writeText) {
        navigator.clipboard.writeText(text).then(done, done);
      } else {
        done();
      }
    });
  });
  // ---- scroll reveal ----
  var reduceMotion = window.matchMedia && window.matchMedia("(prefers-reduced-motion: reduce)").matches;
  var revealEls = document.querySelectorAll(".reveal");
  if (reduceMotion || !("IntersectionObserver" in window)) {
    revealEls.forEach(function (el) { el.classList.add("in"); });
  } else {
    var io = new IntersectionObserver(
      function (entries) {
        entries.forEach(function (entry) {
          if (entry.isIntersecting) {
            entry.target.classList.add("in");
            io.unobserve(entry.target);
          }
        });
      },
      { threshold: 0.12, rootMargin: "0px 0px -40px 0px" }
    );
    revealEls.forEach(function (el) { io.observe(el); });
  }
})();
