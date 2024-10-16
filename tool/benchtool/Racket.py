import os
import re
import json
import subprocess
from benchtool.BenchTool import BenchTool
from benchtool.Types import Config, Entry, LogLevel, ReplaceLevel, TrialArgs

IMPL_DIR = 'src'
STRATEGIES_DIR = 'Strategies'

class Racket(BenchTool):

    def __init__(self,
                 results: str,
                 log_level: LogLevel = LogLevel.INFO,
                 replace_level: ReplaceLevel = ReplaceLevel.REPLACE):
        super().__init__(
            Config(
                start='#|',  # Racket multi-line comment syntax
                end='|#',
                ext='.rkt',
                path='workloads/Racket',
                ignore='util',  # This contains the library code
                strategies= STRATEGIES_DIR,
                impl_path= IMPL_DIR,
                spec_path='src/spec.rkt'),
            results,
            log_level,
            replace_level)

    def all_properties(self, workload: Entry) -> set[str]:
        spec = os.path.join(workload.path, self._config.spec_path)
        with open(spec) as f:
            contents = f.read()
            regex = re.compile(r'prop_[^\s]*')
            matches = regex.findall(contents)
            return list(dict.fromkeys(matches))

    def _build(self, workload_path: str):
        with self._change_dir(workload_path):
            self._shell_command(['raco', 'exe', 'main.rkt'])
        
    def _run_trial(self, workload_path: str, params: TrialArgs):
        with self._change_dir(workload_path):
            cmd = ['./main', params.property]
            results = []
            self._log(
                f"Running {params.workload},{params.strategy},{params.mutant},{params.property}",
                LogLevel.INFO)
            for _ in range(params.trials):
                trial_result = {
                    "workload": params.workload,
                    "discards": None,
                    "foundbug": None,
                    "strategy": params.strategy,
                    "mutant": params.mutant,
                    "passed": None,
                    "property": params.property,
                    "time": None
                }
                try:
                    process = subprocess.Popen(
                        cmd,
                        stdout=subprocess.PIPE,
                        stderr=subprocess.PIPE,
                        text=True
                    )

                    stdout_data, stderr_data = process.communicate(timeout=params.timeout)
                    datasource = stdout_data if len(stdout_data) > 0 else stderr_data
                    start = datasource.find("[|")
                    end = datasource.find("|]")
                    result = datasource[start + 2:end]
                    self._log(f"{params.strategy} Result: {result}", LogLevel.INFO)
                    json_result = json.loads(result)
                    trial_result["foundbug"] = json_result["foundbug"]
                    trial_result["discards"] = 0 # todo: fix this
                    trial_result["passed"] = json_result["passed"]
                    trial_result["time"] = json_result["time"] * 0.001  # ms as string to seconds as float conversion

                except subprocess.TimeoutExpired:
                    process.kill()

                    trial_result["foundbug"] = False
                    trial_result["discards"] = 0
                    trial_result["passed"] = 0
                    trial_result["time"] = params.timeout
                    self._log(f"{params.strategy} Result: Timeout", LogLevel.INFO)

                results.append(trial_result)
                if params.short_circuit and trial_result['time'] == params.timeout:
                    break

            json.dump(results, open(params.file, 'w'))
        
    def _preprocess(self, workload: Entry) -> None:
        pass