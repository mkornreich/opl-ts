/** Node features that the browser build does not have. */
function unavailable(what: string): never {
  throw new Error(`${what} are not available in the browser version; run the model with the command-line tool`);
}
export function execSync(): never {
  return unavailable('shell commands (IloOplExec)');
}
export function spawn(): never {
  return unavailable('shell commands (IloOplExec)');
}
export function createRequire(): () => never {
  return () => unavailable('databases (DBconnection)');
}
export function read(): never {
  return unavailable('spreadsheets (SheetConnection)');
}
export function write(): never {
  return unavailable('spreadsheets (SheetConnection)');
}
export const utils = new Proxy({}, { get: () => () => unavailable('spreadsheets (SheetConnection)') });
