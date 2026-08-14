/**
 * RJ Innovatech - Yoco Checkout Proxy
 * Creates Yoco hosted checkouts for the pricing.html order form and
 * confirms payment via Yoco's webhook (never trust the browser redirect alone).
 *
 * View orders: http://localhost:3002/orders
 */

require('dotenv').config();
const express   = require('express');
const cors      = require('cors');
const helmet    = require('helmet');
const rateLimit = require('express-rate-limit');
const fs        = require('fs');
const path      = require('path');
const crypto    = require('crypto');
const net       = require('net');

const app = express();

// Trust the first hop reverse proxy (Render/Railway/etc all sit behind one) so
// express-rate-limit and req.ip see the real client IP from X-Forwarded-For
// instead of rate-limiting the proxy itself as a single caller.
app.set('trust proxy', 1);

const YOCO_SECRET_KEY     = process.env.YOCO_SECRET_KEY || '';
const YOCO_WEBHOOK_SECRET = process.env.YOCO_WEBHOOK_SECRET || '';
const SITE_URL            = (process.env.SITE_URL || 'https://rjinnovatech.co.za').replace(/\/$/, '');
// Default to SITE_URL rather than '*' - an unset ALLOWED_ORIGIN should fail
// closed (only our own site can call the API), not open (any site can).
const ALLOWED_ORIGIN      = process.env.ALLOWED_ORIGIN || SITE_URL;
const ORDERS_FILE         = path.join(__dirname, 'orders.json');
const ORDERS_USER         = process.env.ORDERS_USER || '';
const ORDERS_PASS         = process.env.ORDERS_PASS || '';

// ── STARTUP CONFIG WARNINGS ───────────────────────────────────────────────────
// Misconfiguration here is a security issue, not just a bug, so make it loud.
if (!YOCO_WEBHOOK_SECRET) console.warn('⚠️  YOCO_WEBHOOK_SECRET is not set - webhook will reject everything until it is.');
if (!ORDERS_USER || !ORDERS_PASS) console.warn('⚠️  ORDERS_USER/ORDERS_PASS not set - /orders will be LOCKED (fails closed), not open.');
if (ALLOWED_ORIGIN === '*') console.warn('⚠️  ALLOWED_ORIGIN is "*" - any website can call this API. Set it to your real site origin.');

// ── FIXED SERVER-SIDE PRICING ────────────────────────────────────────────────
// Amounts are decided here, never taken from the client, so a tampered request
// body can never buy a package below its real price.
const PACKAGES = {
  Business:     { amount: 19900, label: 'Business (R199/mo)' },
  Professional: { amount: 39900, label: 'Professional (R399/mo)' },
  Enterprise:   { amount: 69900, label: 'Enterprise (R699/mo)' },
};

// ── DOMAIN PRICING (matches hostafrica.co.za/domains/ live prices, checked 2026-08-14) ──
// register/transfer are once-off amounts charged through this site; renewal is informational
// only (shown to the customer, billed by HostAfrica directly in later years, not collected here).
// `rdap` = HTTP RDAP lookup base; `whois` = raw WHOIS:43 fallback for TLDs with no public RDAP
// (the .za family - ZACR doesn't run a public RDAP server as of this writing).
//
// WARRANTY_PRIVACY_FEE: HostAfrica's own checkout adds a R99/year "Domain Warranty & Privacy"
// line item (WHOIS privacy + protection against accidental loss) on top of the base registration
// price shown on their pricing page - confirmed live in their cart 2026-08-14. Per the user this
// is always included (not optional), so it's baked into `register` below rather than surfaced as
// a separate line item. Does NOT apply to `transfer` (that add-on only appeared on a fresh
// registration in HostAfrica's cart, not on a transfer) or to `renewal` (informational only, not
// collected here anyway).
const WARRANTY_PRIVACY_FEE = 9900;
const registerTld = (baseRegister, transfer, renewal, lookup) => ({
  register: baseRegister + WARRANTY_PRIVACY_FEE, transfer, renewal, ...lookup,
});
const DOMAIN_TLDS = {
  'co.za':    registerTld(4900,  0,     10900, { whois: 'whois.registry.net.za' }),
  'org.za':   registerTld(9900,  0,     10900, { whois: 'whois.registry.net.za' }),
  'net.za':   registerTld(9900,  0,     10900, { whois: 'whois.registry.net.za' }),
  'com':      registerTld(26900, 26900, 37900, { rdap: 'https://rdap.verisign.com/com/v1/domain/' }),
  'net':      registerTld(24900, 24900, 24900, { rdap: 'https://rdap.verisign.com/net/v1/domain/' }),
  'org':      registerTld(24900, 24900, 24900, { rdap: 'https://rdap.publicinterestregistry.org/rdap/domain/' }),
  'africa':   registerTld(13900, 29900, 29900, { rdap: 'https://rdap.nic.africa/rdap/domain/' }),
  'online':   registerTld(35000, 35000, 35000, { rdap: 'https://rdap.radix.host/rdap/domain/' }),
  'capetown': registerTld(14500, 19900, 19900, { rdap: 'https://rdap.nic.capetown/rdap/domain/' }),
  'joburg':   registerTld(14500, 19900, 19900, { rdap: 'https://rdap.nic.joburg/rdap/domain/' }),
  'durban':   registerTld(14500, 19900, 19900, { rdap: 'https://rdap.nic.durban/rdap/domain/' }),
};

// Strict single DNS label: letters/digits/hyphens, 1-63 chars, no leading/trailing hyphen.
// Critical for the WHOIS path below, which writes this straight into a raw TCP socket -
// this regex is what stands between that and CRLF/command injection, so keep it strict.
const LABEL_RE = /^[a-z0-9]([a-z0-9-]{0,61}[a-z0-9])?$/i;

function whoisLookup(domain, server) {
  return new Promise((resolve, reject) => {
    const sock = net.createConnection(43, server, () => sock.write(domain + '\r\n'));
    let data = '';
    sock.on('data', (d) => { data += d; });
    sock.on('end', () => resolve(data));
    sock.on('error', reject);
    sock.setTimeout(6000, () => { sock.destroy(); reject(new Error('WHOIS timeout')); });
  });
}

// Returns { available: boolean }, or throws if the lookup itself failed (caller must
// treat that as "unknown", never silently report available/taken on a failed lookup).
async function checkDomainAvailability(label, tld) {
  const cfg = DOMAIN_TLDS[tld];
  if (!cfg) throw new Error('Unsupported TLD');
  const domain = `${label}.${tld}`;

  if (cfg.whois) {
    const text = await whoisLookup(domain, cfg.whois);
    if (/^available/im.test(text) || /no match|not found|no information was found/i.test(text)) return { available: true };
    if (/domain name:/i.test(text)) return { available: false };
    throw new Error('Unrecognised WHOIS response');
  }

  const resp = await fetch(cfg.rdap + encodeURIComponent(domain), { signal: AbortSignal.timeout(6000) });
  if (resp.status === 404) return { available: true };
  if (resp.status === 200) return { available: false };
  throw new Error(`Unexpected RDAP status ${resp.status}`);
}

// ── SECURITY HEADERS / CORS ──────────────────────────────────────────────────
// Everything this server serves is either JSON or one self-contained inline-CSS
// HTML page (/orders) with zero external scripts/styles/images, so a strict
// same-origin CSP costs nothing and closes off a class of XSS-via-injected-tag.
app.use(helmet({
  contentSecurityPolicy: {
    directives: {
      defaultSrc: ["'self'"],
      scriptSrc: ["'none'"],
      styleSrc: ["'self'", "'unsafe-inline'"], // /orders uses an inline <style> block
      imgSrc: ["'self'"],
      objectSrc: ["'none'"],
      frameAncestors: ["'none'"],
      baseUri: ["'none'"],
    },
  },
}));
app.use(cors({ origin: ALLOWED_ORIGIN }));

// ── RATE LIMITING ─────────────────────────────────────────────────────────────
const checkoutLimiter = rateLimit({
  windowMs: 15 * 60 * 1000,
  max: 15,
  standardHeaders: true,
  legacyHeaders: false,
  message: { error: 'Too many order attempts. Please wait a few minutes and try again.' },
});
const dashLimiter = rateLimit({ windowMs: 60 * 1000, max: 20, message: { error: 'Too many requests.' } });
// Be polite to upstream WHOIS/RDAP servers too, not just protect ourselves.
const domainLimiter = rateLimit({ windowMs: 60 * 1000, max: 20, message: { error: 'Too many domain checks. Please wait a moment.' } });
// Yoco can legitimately retry/burst webhooks; generous but not unbounded.
const webhookLimiter = rateLimit({ windowMs: 60 * 1000, max: 60, standardHeaders: true, legacyHeaders: false });

// ── /orders BASIC AUTH (fails closed) ────────────────────────────────────────
// Contains customer names, emails, phone numbers - never leave this open.
// If ORDERS_USER/ORDERS_PASS aren't set, every request is rejected rather than
// silently allowed through, so a missed env var can't accidentally expose PII.
function requireOrdersAuth(req, res, next) {
  res.set('WWW-Authenticate', 'Basic realm="RJ Innovatech Orders"');
  if (!ORDERS_USER || !ORDERS_PASS) return res.status(503).send('Orders dashboard is not configured.');

  const header = req.header('authorization') || '';
  const [scheme, encoded] = header.split(' ');
  if (scheme !== 'Basic' || !encoded) return res.status(401).send('Authentication required.');

  let user = '', pass = '';
  try {
    [user, pass] = Buffer.from(encoded, 'base64').toString('utf8').split(':');
  } catch { return res.status(401).send('Authentication required.'); }

  const userBuf = Buffer.from(user || '');
  const passBuf = Buffer.from(pass || '');
  const expectedUserBuf = Buffer.from(ORDERS_USER);
  const expectedPassBuf = Buffer.from(ORDERS_PASS);

  const userOk = userBuf.length === expectedUserBuf.length && crypto.timingSafeEqual(userBuf, expectedUserBuf);
  const passOk = passBuf.length === expectedPassBuf.length && crypto.timingSafeEqual(passBuf, expectedPassBuf);

  if (!userOk || !passOk) return res.status(401).send('Authentication required.');
  next();
}

// ── ORDER LOG ─────────────────────────────────────────────────────────────────
function loadOrders() {
  try {
    if (fs.existsSync(ORDERS_FILE)) return JSON.parse(fs.readFileSync(ORDERS_FILE, 'utf8'));
  } catch (err) { console.error('Failed to read orders.json:', err.message); }
  return [];
}
function saveOrders(orders) {
  try { fs.writeFileSync(ORDERS_FILE, JSON.stringify(orders, null, 2)); }
  catch (err) { console.error('Failed to write orders.json:', err.message); }
}

// ── OPTIONAL WHATSAPP NOTIFICATION (CallMeBot, free) ─────────────────────────
async function notifyOrderPaid(order) {
  const raw = process.env.NOTIFY_WHATSAPP || '';
  const i = raw.indexOf(':');
  if (i === -1) return; // not configured - orders are still logged and visible at /orders
  const phone = raw.slice(0, i).trim();
  const apikey = raw.slice(i + 1).trim();
  if (!phone || !apikey) return;

  const domainLine = order.domainOrder
    ? `Domain: ${order.domainOrder.domain} (${order.domainOrder.option}, R${(order.domainOrder.amount / 100).toFixed(2)})\n`
    : `Domain: ${order.domain} (already owned)\n`;

  const msg =
    '💰 RJ Innovatech - hosting order PAID\n' +
    'Package: ' + order.packageLabel + '\n' +
    'Name: ' + order.name + '\n' +
    'Email: ' + order.email + '\n' +
    'Phone: ' + (order.phone || '-') + '\n' +
    domainLine +
    'Amount: R' + (order.amount / 100).toFixed(2);

  const url = `https://api.callmebot.com/whatsapp.php?phone=${encodeURIComponent(phone)}&text=${encodeURIComponent(msg.slice(0, 1400))}&apikey=${encodeURIComponent(apikey)}`;
  try {
    const resp = await fetch(url);
    console.log(`NOTIFY: CallMeBot WhatsApp -> HTTP ${resp.status}`);
  } catch (err) {
    console.error('NOTIFY: CallMeBot WhatsApp failed:', err.message);
  }
}

// ── DOMAIN LIST + AVAILABILITY CHECK ─────────────────────────────────────────
app.get('/api/domain/tlds', dashLimiter, (_, res) => {
  const list = Object.entries(DOMAIN_TLDS).map(([tld, cfg]) => ({
    tld, register: cfg.register, transfer: cfg.transfer, renewal: cfg.renewal,
  }));
  res.json({ tlds: list });
});

app.get('/api/domain/check', domainLimiter, async (req, res) => {
  const label = String(req.query.domain || '').trim().toLowerCase();
  const tld = String(req.query.tld || '').trim().toLowerCase();

  if (!DOMAIN_TLDS[tld]) return res.status(400).json({ error: 'Unsupported TLD.' });
  if (!LABEL_RE.test(label)) return res.status(400).json({ error: 'Enter a valid domain name.' });

  try {
    const result = await checkDomainAvailability(label, tld);
    const cfg = DOMAIN_TLDS[tld];
    res.json({
      domain: `${label}.${tld}`,
      available: result.available,
      register: cfg.register,
      transfer: cfg.transfer,
      renewal: cfg.renewal,
    });
  } catch (err) {
    console.error('Domain check failed:', label, tld, err.message);
    res.status(502).json({ error: "Couldn't check that domain right now. Please try again shortly." });
  }
});

// ── CREATE CHECKOUT ───────────────────────────────────────────────────────────
app.post('/api/checkout', checkoutLimiter, express.json({ limit: '8kb' }), async (req, res) => {
  if (!YOCO_SECRET_KEY) {
    console.error('YOCO_SECRET_KEY is not configured.');
    return res.status(500).json({ error: 'Payments are not configured yet. Please contact us directly.' });
  }

  const { package: packageName, name, email, phone, domainOption, domainName, domainTld } = req.body || {};
  const domain = req.body && typeof req.body.domain === 'string' ? req.body.domain : '';
  const pkg = PACKAGES[packageName];

  const wantsNewDomain = domainOption === 'register' || domainOption === 'transfer';

  if (!pkg) return res.status(400).json({ error: 'Unknown package selected.' });
  if (!name || !email) return res.status(400).json({ error: 'Name and email are required.' });
  if (!wantsNewDomain && !domain) return res.status(400).json({ error: 'Domain is required.' });
  if (typeof name !== 'string' || typeof email !== 'string') {
    return res.status(400).json({ error: 'Invalid request.' });
  }

  // Domain add-on is entirely re-derived server-side - price and availability are
  // never trusted from the client, same principle as the hosting package price above.
  let domainAmount = 0;
  let domainInfo = null;

  if (wantsNewDomain) {
    const label = String(domainName || '').trim().toLowerCase();
    const tld = String(domainTld || '').trim().toLowerCase();
    const cfg = DOMAIN_TLDS[tld];

    if (!cfg) return res.status(400).json({ error: 'Unsupported domain extension.' });
    if (!LABEL_RE.test(label)) return res.status(400).json({ error: 'Enter a valid domain name.' });

    domainAmount = domainOption === 'transfer' ? cfg.transfer : cfg.register;

    if (domainOption === 'register') {
      try {
        const avail = await checkDomainAvailability(label, tld);
        if (!avail.available) {
          return res.status(409).json({ error: `${label}.${tld} was just taken. Please choose another domain.` });
        }
      } catch (err) {
        console.error('Availability re-check failed at checkout:', err.message);
        return res.status(502).json({ error: "Couldn't verify domain availability. Please try again." });
      }
    }

    domainInfo = { option: domainOption, domain: `${label}.${tld}`, amount: domainAmount };
  }

  const totalAmount = pkg.amount + domainAmount;
  const orderId = 'RJ-' + Date.now().toString(36) + '-' + crypto.randomBytes(3).toString('hex');

  const order = {
    orderId,
    status: 'pending',
    package: packageName,
    packageLabel: pkg.label,
    packageAmount: pkg.amount,
    domain: domain.trim().slice(0, 200),
    domainOption: wantsNewDomain ? domainOption : 'own',
    domainOrder: domainInfo, // {option, domain, amount} when a new domain was bought, else null
    amount: totalAmount,
    name: name.trim().slice(0, 200),
    email: email.trim().slice(0, 200),
    phone: (phone || '').trim().slice(0, 40),
    createdAt: new Date().toISOString(),
    paidAt: null,
    checkoutId: null,
    paymentId: null,
  };

  try {
    const ycRes = await fetch('https://payments.yoco.com/api/checkouts', {
      method: 'POST',
      headers: {
        'Authorization': `Bearer ${YOCO_SECRET_KEY}`,
        'Content-Type': 'application/json',
      },
      body: JSON.stringify({
        amount: totalAmount,
        currency: 'ZAR',
        successUrl: `${SITE_URL}/payment-success.html?ref=${orderId}`,
        cancelUrl: `${SITE_URL}/pricing.html#order`,
        failureUrl: `${SITE_URL}/payment-failed.html?ref=${orderId}`,
        clientReferenceId: orderId,
        metadata: {
          orderId, package: packageName, name: order.name, email: order.email, phone: order.phone,
          domain: order.domain, domainOption: order.domainOption,
          domainPurchase: domainInfo ? domainInfo.domain : '',
        },
      }),
    });

    const ycBody = await ycRes.json();
    if (!ycRes.ok) {
      console.error('Yoco checkout creation failed:', ycRes.status, ycBody);
      return res.status(502).json({ error: 'Could not start payment. Please try again shortly.' });
    }

    order.checkoutId = ycBody.id;

    const orders = loadOrders();
    orders.unshift(order);
    saveOrders(orders);

    res.json({ redirectUrl: ycBody.redirectUrl });
  } catch (err) {
    console.error('Checkout error:', err.message);
    res.status(500).json({ error: 'Could not start payment. Please try again shortly.' });
  }
});

// ── YOCO WEBHOOK (raw body required for signature verification) ──────────────
app.post('/api/yoco/webhooks', webhookLimiter, express.raw({ type: 'application/json', limit: '64kb' }), (req, res) => {
  if (!YOCO_WEBHOOK_SECRET) {
    console.warn('YOCO_WEBHOOK_SECRET is not configured - rejecting webhook.');
    return res.status(500).end();
  }

  const webhookId        = req.header('webhook-id');
  const webhookTimestamp = req.header('webhook-timestamp');
  const webhookSignature = req.header('webhook-signature');
  const rawBody           = req.body; // Buffer

  if (!webhookId || !webhookTimestamp || !webhookSignature || !Buffer.isBuffer(rawBody)) {
    return res.status(400).end();
  }

  // Reject stale/replayed webhooks (>3 min old)
  const tsSeconds = parseInt(webhookTimestamp, 10);
  if (!Number.isFinite(tsSeconds) || Math.abs(Date.now() / 1000 - tsSeconds) > 180) {
    return res.status(400).end();
  }

  try {
    const secretBytes = Buffer.from(YOCO_WEBHOOK_SECRET.split('_')[1], 'base64');
    const signedContent = `${webhookId}.${webhookTimestamp}.${rawBody.toString('utf8')}`;
    const expected = crypto.createHmac('sha256', secretBytes).update(signedContent).digest('base64');

    const candidates = webhookSignature.split(' ').map(part => part.split(',')[1]).filter(Boolean);
    const valid = candidates.some(sig => {
      try {
        return sig.length === expected.length &&
          crypto.timingSafeEqual(Buffer.from(sig), Buffer.from(expected));
      } catch { return false; }
    });

    if (!valid) {
      console.warn('Yoco webhook signature mismatch.');
      return res.status(400).end();
    }
  } catch (err) {
    console.error('Webhook verification error:', err.message);
    return res.status(400).end();
  }

  let event;
  try { event = JSON.parse(rawBody.toString('utf8')); }
  catch { return res.status(400).end(); }

  // Acknowledge immediately - do the bookkeeping after.
  res.status(200).end();

  if (event.type !== 'payment.succeeded' && event.type !== 'payment.failed') return;

  const payload = event.payload || {};
  const orderId = (payload.metadata && payload.metadata.orderId) || null;
  if (!orderId) return;

  const orders = loadOrders();
  const order = orders.find(o => o.orderId === orderId);
  if (!order) { console.warn('Webhook for unknown order:', orderId); return; }

  if (event.type === 'payment.succeeded') {
    if (order.status === 'paid') return; // already processed (webhook retry) - avoid double notify
    order.status = 'paid';
    order.paidAt = new Date().toISOString();
    order.paymentId = payload.id || null;
    saveOrders(orders);
    notifyOrderPaid(order);
  } else {
    order.status = 'failed';
    saveOrders(orders);
  }
});

// ── ORDERS DASHBOARD ───────────────────────────────────────────────────────────
app.get('/orders', dashLimiter, requireOrdersAuth, (_, res) => {
  const orders = loadOrders();

  const statusBadge = (s) => ({
    paid:    '<span class="badge paid">Paid</span>',
    pending: '<span class="badge pending">Pending</span>',
    failed:  '<span class="badge failed">Failed</span>',
  }[s] || s);

  const domainOptionLabel = { own: 'Already owned', register: 'New (register)', transfer: 'New (transfer)' };

  const rows = orders.map(o => {
    const date = new Date(o.createdAt);
    const dateStr = date.toLocaleDateString('en-ZA', { day: '2-digit', month: 'short', year: 'numeric' });
    const timeStr = date.toLocaleTimeString('en-ZA', { hour: '2-digit', minute: '2-digit' });
    const esc = (s) => String(s || '').replace(/</g, '&lt;').replace(/>/g, '&gt;');
    const domainCell = o.domainOrder
      ? `${esc(o.domainOrder.domain)}<br><span class="dim">${domainOptionLabel[o.domainOption] || o.domainOption}</span>`
      : `${esc(o.domain)}<br><span class="dim">${domainOptionLabel.own}</span>`;
    return `
    <tr>
      <td>${dateStr} ${timeStr}</td>
      <td>${statusBadge(o.status)}</td>
      <td>${esc(o.packageLabel)}</td>
      <td>${esc(o.name)}</td>
      <td>${esc(o.email)}<br><span class="dim">${esc(o.phone)}</span></td>
      <td>${domainCell}</td>
      <td>R${(o.amount / 100).toFixed(2)}</td>
    </tr>`;
  }).join('');

  res.send(`<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="UTF-8"/>
  <meta name="viewport" content="width=device-width,initial-scale=1"/>
  <title>Orders - RJ Innovatech</title>
  <style>
    *{box-sizing:border-box;margin:0;padding:0}
    body{font-family:'Segoe UI',sans-serif;background:#080808;color:#f1f5f9;padding:24px}
    h1{font-size:22px;font-weight:700;margin-bottom:4px}
    h1 span{color:#dc2020}
    .sub{color:#94a3b8;font-size:13px;margin-bottom:24px}
    .empty{background:#141414;border-radius:10px;padding:40px;text-align:center;color:#888}
    table{width:100%;border-collapse:collapse;background:#141414;border-radius:10px;overflow:hidden;font-size:13px}
    th{text-align:left;padding:12px 14px;background:#1a1a1a;color:#94a3b8;font-size:11px;text-transform:uppercase;letter-spacing:.06em}
    td{padding:12px 14px;border-top:1px solid #222}
    .dim{color:#666;font-size:12px}
    .badge{display:inline-block;padding:3px 9px;border-radius:20px;font-size:11px;font-weight:600}
    .badge.paid{background:rgba(34,197,94,0.15);color:#4ade80}
    .badge.pending{background:rgba(234,179,8,0.15);color:#facc15}
    .badge.failed{background:rgba(220,32,32,0.15);color:#ff6b6b}
    .refresh{float:right;font-size:12px;color:#dc2020;text-decoration:none;padding:6px 12px;border:1px solid #dc2020;border-radius:6px}
    .refresh:hover{background:#dc2020;color:#fff}
  </style>
</head>
<body>
  <a class="refresh" href="/orders">Refresh</a>
  <h1><span>RJ Innovatech</span> Orders</h1>
  <p class="sub">${orders.length} order${orders.length !== 1 ? 's' : ''} logged</p>
  ${orders.length === 0 ? '<div class="empty">No orders yet.</div>' : `
  <table>
    <thead><tr><th>Date</th><th>Status</th><th>Package</th><th>Name</th><th>Contact</th><th>Domain</th><th>Amount</th></tr></thead>
    <tbody>${rows}</tbody>
  </table>`}
</body>
</html>`);
});

// ── HEALTH CHECK ──────────────────────────────────────────────────────────────
app.get('/health', (_, res) => res.json({ status: 'ok', service: 'rj-innovatech-payments' }));

// ── START ─────────────────────────────────────────────────────────────────────
const PORT = process.env.PORT || 3002;
app.listen(PORT, () => {
  console.log(`RJ Innovatech Payments running on http://localhost:${PORT}`);
  console.log(`Orders:       http://localhost:${PORT}/orders`);
  console.log(`Health check: http://localhost:${PORT}/health`);
});
