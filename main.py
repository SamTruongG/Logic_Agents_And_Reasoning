import prover
import os
import time
import io
import contextlib
from dataclasses import dataclass, field
from typing import Iterator, List, Dict, Optional, Tuple
from pathlib import Path


@dataclass
class VerdictCount:
    """Aggregates outcomes from a single test."""
    success: int = 0
    failure: int = 0
    timeout: int = 0
    
    def total(self) -> int:
        return self.success + self.failure + self.timeout
    
    def as_dict(self) -> Dict[str, int]:
        result = {}
        if self.success:
            result['pass'] = self.success
        if self.failure:
            result['fail'] = self.failure
        if self.timeout:
            result['timeout'] = self.timeout
        return result


@dataclass
class Suite:
    """Tracks overall test campaign statistics."""
    files_examined: int = 0
    total_items: int = 0
    verdicts: VerdictCount = field(default_factory=VerdictCount)
    errors: int = 0
    duration: float = 0.0
    
    def success_rate(self) -> float:
        if self.total_items == 0:
            return 0.0
        return (self.verdicts.success / self.total_items) * 100


class FilesystemWalker:
    """Discovers test files in a directory structure."""
    
    @staticmethod
    def locate(base: str) -> Iterator[str]:
        """Yield absolute paths to .p files."""
        base_path = Path(base)
        
        if base_path.is_file():
            yield str(base_path)
        else:
            for entry in base_path.rglob("*.p"):
                yield str(entry)


class TestRunner:
    """Executes proofs and captures results."""
    
    @staticmethod
    def execute(filepath: str) -> Tuple[List, int]:
        """Run prover, suppressing output."""
        with contextlib.redirect_stdout(io.StringIO()):
            outcomes, _ = prover_fix.Run(filepath)
        return outcomes, len(outcomes)
    
    @staticmethod
    def categorize(outcomes: List) -> VerdictCount:
        """Classify proof outcomes."""
        counts = VerdictCount()
        for outcome in outcomes:
            if outcome is True:
                counts.success += 1
            elif outcome is False:
                counts.failure += 1
            else:
                counts.timeout += 1
        return counts


class ReportBuilder:
    """Formats and displays results."""
    
    @staticmethod
    def file_header(index: int, name: str, counts: VerdictCount) -> str:
        """Generate single-file status line."""
        badge = f"[{index}] {name}:"
        details = counts.as_dict()
        
        if not details:
            return f"{badge} no sequents"
        
        parts = [f"{k}={v}" for k, v in details.items()]
        return f"{badge} {' '.join(parts)}"
    
    @staticmethod
    def summary(suite: Suite, source: str) -> None:
        """Print aggregated campaign results."""
        print("\n=== Summary ===")
        print(f"Source:          {source}")
        print(f"Files processed: {suite.files_examined}")
        print(f"Sequents total:  {suite.total_items}")
        print(f"  Passed:    {suite.verdicts.success}")
        print(f"  Failed:    {suite.verdicts.failure}")
        print(f"  Timed out: {suite.verdicts.timeout}")
        if suite.errors:
            print(f"Files errored:   {suite.errors}")
        print(f"Total time:      {suite.duration:.2f} s")


class Campaign:
    """Orchestrates the entire test campaign."""
    
    def __init__(self, base_path: str):
        self.base_path = base_path
        self.suite = Suite()
    
    def run(self) -> Suite:
        """Execute all tests and gather results."""
        tick = time.perf_counter()
        
        for file_index, filepath in enumerate(FilesystemWalker.locate(self.base_path), 1):
            self._process_single(filepath, file_index)
        
        tock = time.perf_counter()
        self.suite.duration = tock - tick
        
        return self.suite
    
    def _process_single(self, filepath: str, ordinal: int) -> None:
        """Handle one file and update suite."""
        basename = os.path.basename(filepath)
        
        try:
            outcomes, count = TestRunner.execute(filepath)
            file_verdicts = TestRunner.categorize(outcomes)
            
            # Update aggregate
            self.suite.files_examined += 1
            self.suite.total_items += count
            self.suite.verdicts.success += file_verdicts.success
            self.suite.verdicts.failure += file_verdicts.failure
            self.suite.verdicts.timeout += file_verdicts.timeout
            
            # Display
            line = ReportBuilder.file_header(ordinal, basename, file_verdicts)
            print(line)
        
        except Exception as e:
            self.suite.errors += 1
            print(f"[ERROR] {basename}: {e}")


def main():
    """Entry point."""
    path = "problems_1000.p"
    
    campaign = Campaign(path)
    results = campaign.run()
    
    ReportBuilder.summary(results, path)


if __name__ == "__main__":
    main()
