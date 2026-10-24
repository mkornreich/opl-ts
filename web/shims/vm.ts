/**
 * node:vm for the browser build.  A context is the sandbox object itself;
 * scripts run at global scope (indirect eval) inside `with (context)`, so
 * the sandbox's names come first and functions declared by one script stay
 * visible to the next, as in OPL.
 */

export type Context = Record<string, unknown>;

export function createContext(g: Context): Context {
  return g;
}

export function runInContext(src: string, ctx: Context): unknown {
  if (src === 'Number.prototype') return Number.prototype;
  const g = globalThis as unknown as { __oplContext?: Context };
  const saved = g.__oplContext;
  g.__oplContext = ctx;
  try {
    return (0, eval)(`with (__oplContext) {${src}\n}`);
  } finally {
    g.__oplContext = saved;
  }
}
