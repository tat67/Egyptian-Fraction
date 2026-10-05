// msclock.h -- wall-clock timing in integer milliseconds, so that no program in this directory
// uses a floating-point type anywhere (timings are reported only; no decision depends on them).
#pragma once
#include <chrono>
#include <cstdio>
#include <string>
inline long long msSince(std::chrono::steady_clock::time_point t) {
  return std::chrono::duration_cast<std::chrono::milliseconds>(std::chrono::steady_clock::now() - t).count();
}
// seconds with 1 or 2 decimals (truncated), e.g. "100.7s", "0.25s"
inline std::string secStr(long long ms, int decimals) {
  char buf[48];
  if (decimals == 1) snprintf(buf, sizeof buf, "%lld.%llds", ms / 1000, (ms % 1000) / 100);
  else snprintf(buf, sizeof buf, "%lld.%02llds", ms / 1000, (ms % 1000) / 10);
  return buf;
}
