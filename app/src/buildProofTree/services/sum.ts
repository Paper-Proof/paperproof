export default function sum(a: number[], margin: number = 0): number {
  if (a.length == 0) {
    return 0;
  }
  return a.reduce((x, y) => x + y, 0) + (a.length - 1) * margin;
}
