// SEND + MORE = MONEY: give each letter a different digit.

using CP;
{string} Letters = {"S", "E", "N", "D", "M", "O", "R", "Y"};
dvar int d[Letters] in 0..9;

dexpr int SEND = 1000 * d["S"] + 100 * d["E"] + 10 * d["N"] + d["D"];
dexpr int MORE = 1000 * d["M"] + 100 * d["O"] + 10 * d["R"] + d["E"];
dexpr int MONEY = 10000 * d["M"] + 1000 * d["O"] + 100 * d["N"] + 10 * d["E"] + d["Y"];

subject to {
  allDifferent(d);
  d["S"] >= 1;
  d["M"] >= 1;
  SEND + MORE == MONEY;
}

execute {
  writeln("  ", SEND);
  writeln("+ ", MORE);
  writeln("= ", MONEY);
}
