export interface SourcePos {
  file: string;
  line: number;
  col: number;
}

export class OplError extends Error {
  constructor(
    message: string,
    readonly pos?: SourcePos,
  ) {
    super(pos ? `${pos.file}:${pos.line}:${pos.col}: ${message}` : message);
    this.name = 'OplError';
  }
}

export function fail(message: string, pos?: SourcePos): never {
  throw new OplError(message, pos);
}
