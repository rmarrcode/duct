import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

import module_ as module_
import _dafny as _dafny
import System_ as System_

# Module: YamlToDafnyTranslator

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def Main(args):
        if (len(args)) < (2):
            return
        d_0_path_: _dafny.Seq
        d_0_path_ = (args)[1]
        d_1_content_: _dafny.Seq
        out0_: _dafny.Seq
        out0_ = FileUtils.ReadAllLines(d_0_path_)
        d_1_content_ = out0_
        FileUtils.WriteLine(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Read lines from file")))

