import sys
import os
import time
import logging
import subprocess
from abc import ABCMeta, abstractmethod
from typing import Dict

from watchdog.observers import Observer
from watchdog.events import FileSystemEventHandler

from RVerify.file_checker import FileChecker

class RunCheckerInterface:
    __metaclass__ = ABCMeta

    @abstractmethod
    def get_source(self):
        """Get the source from the internal file."""
        raise NotImplementedError

    @abstractmethod
    def run_checker(self):
        """Run the checker."""
        raise NotImplementedError

class CheckingObserver(FileSystemEventHandler):
    """Observes the given file and provides automated checking on file changes.
    """
    def __init__(self, watcher: RunCheckerInterface, path: str):
        self.watcher = watcher
        self.logger = logging.getLogger('CheckingObserver')
        self.path = path

    def on_modified(self, event):
        # Only if the given file matches the file to be watched for.
        if os.path.abspath(event.src_path) == self.path:
            self.logger.info("Running checker because of file changed event.")
            self.watcher.get_source()
            self.watcher.run_checker()

class Watcher(RunCheckerInterface):
    def __init__(self, approximations: str, path: str=None, dump_ast: bool=False,
                 print_smt: bool=False, check: bool=True, print_complete_model: bool=False,
                 show_in_rtest:bool=False,rtest_executable:str="RTest",
                 smt_included: Dict[str,bool]=None):
        self.approximations = approximations
        self.path = path
        self.source = ""
        self.observer = None
        self.logger = logging.getLogger('Watcher')
        self.checking_observer = None
        self.observer = None
        self.dump_ast = dump_ast
        self.print_smt = print_smt
        self.check = check
        self.print_complete_model = print_complete_model
        self.smt_included = smt_included
        self.rtest = None
        if show_in_rtest:
            self.rtest = subprocess.Popen(rtest_executable,
                                          stdin=subprocess.PIPE,
                                          encoding="utf-8",
                                          universal_newlines=True)

    def get_source(self):
        """Gets the source code from the supplied file or stdin into the source field.
        """
        if self.path is None:
            self.source = sys.stdin.read()
        else:
            with open(self.path) as inFile:
                self.source = inFile.read()

        # Search for begin phrase.
        phraseFound = False
        filteredSource = ""
        for line in self.source.splitlines():
            if phraseFound:
                filteredSource += line + "\n"
            if "RVERIFY_BEGIN" in line:
                phraseFound = True

        if phraseFound:
            self.source = filteredSource

    def run_checker(self):
        """Runs the checker from file_checker.py after reading source file/stdin.

        If the path is None, stdin will be used.
        """
        if self.source == "":
            self.get_source()
        
        file_checker = FileChecker(self.approximations, self.source)
        file_checker.parse()

        if self.dump_ast:
            file_checker.dump_ast()

        if self.check:
            result = file_checker.check(self.print_complete_model)
            if self.rtest is not None:
                # Visualise in RTest using stdin API.
                print(result.as_rtest_input(), file=self.rtest.stdin, flush=True)

        if self.print_smt:
            if self.smt_included is None:
                self.logger.error("Must provide smt_included argument!")
                return
            file_checker.dump_smt(self.smt_included)

    def watch(self):
        """Starts a watcher to watch for changes in the given file. 

        Only works when self.path is not None!
        """

        if self.path is None:
            self.logger.error("Could not start watcher, no filename was given!")
            return

        # Get the to-be-observed path.
        abspath = os.path.abspath(self.path)
        dirname = os.path.dirname(abspath)

        self.checking_observer = CheckingObserver(watcher=self,path=abspath)
        self.observer = Observer()
        self.observer.schedule(self.checking_observer, dirname)
        self.observer.start()

        # Run checker for first time.
        self.run_checker()

        self.logger.info("Now waiting for file changed events. Ctrl+C to exit.")

        # Wait for events.
        try:
            while True:
                time.sleep(1)
        except KeyboardInterrupt:
            self.observer.stop()
            self.logger.info("Stopped watching because of keyboard interrupt.")

        self.observer.join()

        if self.rtest:
            self.rtest.communicate(input="<exit />")
