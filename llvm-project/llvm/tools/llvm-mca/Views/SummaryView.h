//===--------------------- SummaryView.h ---------------------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
/// \file
///
/// This file implements the summary view.
///
/// The goal of the summary view is to give a very quick overview of the
/// performance throughput. Below is an example of summary view:
///
///
/// Iterations:        300
/// Instructions:      900
/// Total Cycles:      610
/// Dispatch Width:    2
/// IPC:               1.48
/// Block RThroughput: 2.0
///
/// The summary view collects a few performance numbers. The two main
/// performance indicators are 'Total Cycles' and IPC (Instructions Per Cycle).
///
//===----------------------------------------------------------------------===//

#ifndef LLVM_TOOLS_LLVM_MCA_SUMMARYVIEW_H
#define LLVM_TOOLS_LLVM_MCA_SUMMARYVIEW_H

#include "Views/View.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/MC/MCSchedule.h"
#include "llvm/Support/raw_ostream.h"

namespace llvm {
namespace mca {

/// A view that collects and prints a few performance numbers.
class SummaryView : public View {
  const llvm::MCSchedModel &SM;
  llvm::ArrayRef<llvm::MCInst> Source;
  const unsigned DispatchWidth;
  unsigned LastInstructionIdx;
  unsigned TotalCycles;
  // The total number of micro opcodes contributed by a block of instructions.
  unsigned NumMicroOps;

  struct BackPressureInfo {
    // Cycles where backpressure increased.
    unsigned PressureIncreaseCycles;
    // Cycles where backpressure increased because of pipeline pressure.
    unsigned ResourcePressureCycles;
    // Cycles where backpressure increased because of data dependencies.
    unsigned DataDependencyCycles;
    // Cycles where backpressure increased because of register dependencies.
    unsigned RegisterDependencyCycles;
    // Cycles where backpressure increased because of memory dependencies.
    unsigned MemoryDependencyCycles;
  };
  BackPressureInfo BPI;

  // Resource pressure distribution. There is an element for every processor
  // resource declared by the scheduling model. Quantities are number of cycles.
  llvm::SmallVector<unsigned, 8> ResourcePressureDistribution;

  // For each processor resource, this vector stores the cumulative number of
  // resource cycles consumed by the analyzed code block.
  llvm::SmallVector<unsigned, 8> ProcResourceUsage;

  // Each processor resource is associated with a so-called processor resource
  // mask. This vector allows to correlate processor resource IDs with processor
  // resource masks. There is exactly one element per each processor resource
  // declared by the scheduling model.
  llvm::SmallVector<uint64_t, 8> ProcResourceMasks;

  // Used to map resource indices to actual processor resource IDs.
  llvm::SmallVector<unsigned, 8> ResIdx2ProcResID;

  // True if resource pressure events were notified during this cycle.
  bool PressureIncreasedBecauseOfResources;
  bool PressureIncreasedBecauseOfDataDependencies;

  // True if throughput was affected by dispatch stalls.
  bool SeenStallCycles;

  // True if the bottleneck analysis should be displayed.
  bool ShouldEmitBottleneckAnalysis;

  // Compute the reciprocal throughput for the analyzed code block.
  // The reciprocal block throughput is computed as the MAX between:
  //   - NumMicroOps / DispatchWidth
  //   - Total Resource Cycles / #Units   (for every resource consumed).
  double getBlockRThroughput() const;

  // Prints a bottleneck message to OS.
  void printBottleneckHints(llvm::raw_ostream &OS) const;

public:
  SummaryView(const llvm::MCSchedModel &Model, llvm::ArrayRef<llvm::MCInst> S,
              unsigned Width, bool EmitBottleneckAnalysis);

  void onCycleEnd() override {
    ++TotalCycles;
    if (PressureIncreasedBecauseOfResources ||
        PressureIncreasedBecauseOfDataDependencies) {
      ++BPI.PressureIncreaseCycles;
      if (PressureIncreasedBecauseOfDataDependencies)
        ++BPI.DataDependencyCycles;
      PressureIncreasedBecauseOfResources = false;
      PressureIncreasedBecauseOfDataDependencies = false;
    }
  }
  void onEvent(const HWInstructionEvent &Event) override;
  void onEvent(const HWStallEvent &Event) override {
    SeenStallCycles = true;
  }

  void onEvent(const HWPressureEvent &Event) override;

  void printView(llvm::raw_ostream &OS) const override;
};
} // namespace mca
} // namespace llvm

#endif