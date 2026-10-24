/** The few parts of Node's process object the library uses. */
export const process = {
  env: {} as Record<string, string | undefined>,
  platform: 'browser',
  cwd: () => '/work',
  memoryUsage: Object.assign(() => ({ rss: 0, heapTotal: 0, heapUsed: 0, external: 0, arrayBuffers: 0 }), { rss: () => 0 }),
  emitWarning: () => {},
  stdout: { write: (_: string) => true },
  stderr: { write: (_: string) => true },
};
