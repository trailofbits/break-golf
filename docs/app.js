// break golf — static board. No backend: the manifest and ledger are generated
// files in this directory, and submitting opens a prefilled GitHub issue.

const $ = (id) => document.getElementById(id);
const esc = (s) => String(s).replace(/[&<>"]/g, (c) =>
  ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;" }[c]));
const bits = (budget, num, den, e) => Math.log2(budget / Math.pow(num / den, e));
const fmtBits = (b) => (Number.isFinite(b) ? b.toFixed(2) : "—");

let SITE, MANIFEST, LEDGER;

async function boot() {
  [SITE, MANIFEST, LEDGER] = await Promise.all(
    ["./data/site.json", "./data/manifest.json", "./data/ledger.json"]
      .map((u) => fetch(u).then((r) => r.json())));

  $("site-title").textContent = SITE.title;
  $("site-tagline").textContent = SITE.tagline;
  $("site-status").textContent = SITE.status;
  document.title = SITE.title;
  $("foot-repo").innerHTML = SITE.repo === "OWNER/REPO"
    ? "Repository not configured yet — set <code>repo</code> in <code>docs/data/site.json</code>."
    : `Submissions and verification: <a href="https://github.com/${esc(SITE.repo)}/issues">github.com/${esc(SITE.repo)}/issues</a>`;

  renderChallenges();
  wireForm();
}

function recordsFor(slug) {
  return (LEDGER.records[slug] || []).slice()
    .sort((a, b) => a.bits - b.bits);
}

function renderChallenges() {
  const host = $("challenges");
  host.innerHTML = MANIFEST.challenges.map((c) => {
    const recs = recordsFor(c.slug);
    const best = recs.length ? recs[0].bits : null;
    return `
<h2>${esc(c.title)}</h2>
<div class="card">
  <p>${esc(c.blurb)}</p>
  <div class="tags">${c.tags.map((t) => `<span class="tag">${esc(t)}</span>`).join("")}</div>
  <div class="statrow">
    <div class="stat"><span class="v">${best === null ? "—" : fmtBits(best)}</span><span class="k">best, bits</span></div>
    <div class="stat"><span class="v">${c.par_bits}</span><span class="k">par</span></div>
    <div class="stat"><span class="v">${recs.length}</span><span class="k">records</span></div>
  </div>
  <ul class="files">${c.files.map((f) =>
    `<li><a href="${esc(f.url)}" target="_blank" rel="noopener">${esc(f.name)}</a> — ${esc(f.what)}</li>`).join("")}</ul>
  <details>
    <summary>Build it locally</summary>
    <pre><code>${c.setup.map(esc).join("\n")}</code></pre>
  </details>
</div>
${recs.length ? `<div class="scroller"><table>
  <thead><tr><th scope="col">Bits</th><th scope="col">Queries</th><th scope="col">Advantage</th>
    <th scope="col">Solver</th><th scope="col">Assisted by</th></tr></thead>
  <tbody>${recs.map((r) => `
    <tr>
      <td class="num">${fmtBits(r.bits)}</td>
      <td class="num">${r.budget}</td>
      <td class="num">${r.advNum === r.advDen ? "1" : `${r.advNum}/${r.advDen}`}</td>
      <td>${esc(r.solver)}</td>
      <td class="num">${esc(r.assisted_by || "—")}</td>
    </tr>
    <tr><td colspan="5" style="color:var(--muted);font-size:.8rem;padding-top:0">${esc(r.description || "")}</td></tr>`).join("")}
  </tbody>
</table></div>` : `<p class="empty">No records yet. Brute force sits at ${fmtBits(c.baseline_bits)} bits — anything under ${c.par_bits} breaks the claim.</p>`}`;
  }).join("");
}

function currentChallenge() {
  return MANIFEST.challenges.find((c) => c.slug === $("f-challenge").value);
}

function updateScore() {
  const c = currentChallenge();
  $("f-score").innerHTML =
    `score = log₂(budget / advantage<sup>${c.advantage_exponent}</sup>), par is ${c.par_bits} bits. ` +
    "CI computes it from the <b>budget</b>, <b>advNum</b> and <b>advDen</b> you define in your Lean — " +
    "there is nothing to claim here.";
}

function issueBody() {
  return [
    "**Assisted by:** " + ($("f-assist").value || "_unstated_"),
    `**Notes:** ${$("f-desc").value || "_none_"}`,
    "",
    "### Solve.lean",
    "",
    "```lean",
    $("f-solve").value,
    "```",
    "",
    "---",
    "<sub>The score is not in this issue. Your `budget`, `advNum` and `advDen` are",
    "definitions in the Lean below, and the challenge type is indexed by them — CI",
    "reads them back out of Lean after the proof checks.</sub>",
  ].join("\n");
}

function wireForm() {
  const sel = $("f-challenge");
  sel.innerHTML = MANIFEST.challenges
    .map((c) => `<option value="${esc(c.slug)}">${esc(c.title)}</option>`).join("");
  $("f-solve").value = currentChallenge().solve_template;

  sel.addEventListener("change", () => {
    $("f-solve").value = currentChallenge().solve_template;
    updateScore();
  });
  updateScore();

  $("submit-form").addEventListener("submit", (ev) => {
    ev.preventDefault();
    if (SITE.repo === "OWNER/REPO") {
      $("f-score").innerHTML =
        "No repository is configured for this board yet — set <b>repo</b> in " +
        "<code>docs/data/site.json</code> and the submit button will open an issue there.";
      return;
    }
    const url = new URL(`https://github.com/${SITE.repo}/issues/new`);
    url.searchParams.set("title", `verify: ${currentChallenge().slug}`);
    url.searchParams.set("body", issueBody());
    url.searchParams.set("labels", "submission");
    window.open(url.toString(), "_blank", "noopener");
  });
}

boot().catch((e) => {
  document.body.insertAdjacentHTML("afterbegin",
    `<pre style="margin:1rem">Could not load board data: ${esc(e.message)}</pre>`);
});
