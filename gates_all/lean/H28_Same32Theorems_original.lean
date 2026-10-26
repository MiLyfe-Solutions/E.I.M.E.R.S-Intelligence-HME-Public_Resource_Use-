import V185TrunkScan18Incremental
import H28Certificate

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental

namespace V185TrunkScan19Incremental

def tailWord_4 : List Nat := [2, 3, 2, 4, 2, 1, 5]
def baseStart_4 : Nat := 118140960795 + 4 * 2 ^ 59
def prefixEnd_4 : Nat := 4983230072969 + 3 ^ 40 * 4 * 2
def baseEnd_4 : Nat := 405713130512207405

theorem tailTrace_4 : CollatzResearch.WordTrace tailWord_4 prefixEnd_4 405713130512207405 := by
  apply H28Certificate.checkWord_sound
  decide

theorem cell19_4_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 5].length) (baseStart_4 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_4 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_4 prefixEnd_4 := by exact prefixLift 4
  have htrace : WordTrace (prefixWord ++ tailWord_4) baseStart_4 baseEnd_4 := by
    simpa [prefixWord, tailWord_4, baseEnd_4] using wordTrace_append hprefix tailTrace_4
  have hstable : (prefixWord ++ tailWord_4).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4).length < 2 ^ (prefixWord ++ tailWord_4).sum := by decide
  have hdescent : baseEnd_4 < baseStart_4 := by decide
  rcases family_descends (prefixWord ++ tailWord_4) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46 : List Nat := [4, 1, 3, 1, 1, 2, 2, 5]
def baseStart_46 : Nat := 118140960795 + 46 * 2 ^ 59
def prefixEnd_46 : Nat := 4983230072969 + 3 ^ 40 * 46 * 2
def baseEnd_46 : Nat := 13997102347883688767

theorem tailTrace_46 : CollatzResearch.WordTrace tailWord_46 prefixEnd_46 13997102347883688767 := by
  apply H28Certificate.checkWord_sound
  decide

theorem cell19_46_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 5].length) (baseStart_46 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_46 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_46 prefixEnd_46 := by exact prefixLift 46
  have htrace : WordTrace (prefixWord ++ tailWord_46) baseStart_46 baseEnd_46 := by
    simpa [prefixWord, tailWord_46, baseEnd_46] using wordTrace_append hprefix tailTrace_46
  have hstable : (prefixWord ++ tailWord_46).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46).length < 2 ^ (prefixWord ++ tailWord_46).sum := by decide
  have hdescent : baseEnd_46 < baseStart_46 := by decide
  rcases family_descends (prefixWord ++ tailWord_46) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48 : List Nat := [2, 1, 1, 1, 2, 5, 2, 5]
def baseStart_48 : Nat := 118140960795 + 48 * 2 ^ 59
def prefixEnd_48 : Nat := 4983230072969 + 3 ^ 40 * 48 * 2
def baseEnd_48 : Nat := 14605672012471644317

theorem tailTrace_48 : CollatzResearch.WordTrace tailWord_48 prefixEnd_48 14605672012471644317 := by
  apply H28Certificate.checkWord_sound
  decide

theorem cell19_48_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 5].length) (baseStart_48 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_48 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_48 prefixEnd_48 := by exact prefixLift 48
  have htrace : WordTrace (prefixWord ++ tailWord_48) baseStart_48 baseEnd_48 := by
    simpa [prefixWord, tailWord_48, baseEnd_48] using wordTrace_append hprefix tailTrace_48
  have hstable : (prefixWord ++ tailWord_48).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48).length < 2 ^ (prefixWord ++ tailWord_48).sum := by decide
  have hdescent : baseEnd_48 < baseStart_48 := by decide
  rcases family_descends (prefixWord ++ tailWord_48) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82 : List Nat := [3, 2, 2, 1, 4, 2, 1, 4]
def baseStart_82 : Nat := 118140960795 + 82 * 2 ^ 59
def prefixEnd_82 : Nat := 4983230072969 + 3 ^ 40 * 82 * 2
def baseEnd_82 : Nat := 24951356310466888669

theorem tailTrace_82 : CollatzResearch.WordTrace tailWord_82 prefixEnd_82 24951356310466888669 := by
  apply H28Certificate.checkWord_sound
  decide

theorem cell19_82_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 4].length) (baseStart_82 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_82 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_82 prefixEnd_82 := by exact prefixLift 82
  have htrace : WordTrace (prefixWord ++ tailWord_82) baseStart_82 baseEnd_82 := by
    simpa [prefixWord, tailWord_82, baseEnd_82] using wordTrace_append hprefix tailTrace_82
  have hstable : (prefixWord ++ tailWord_82).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82).length < 2 ^ (prefixWord ++ tailWord_82).sum := by decide
  have hdescent : baseEnd_82 < baseStart_82 := by decide
  rcases family_descends (prefixWord ++ tailWord_82) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103 : List Nat := [1, 1, 5, 1, 1, 2, 5, 3]
def baseStart_103 : Nat := 118140960795 + 103 * 2 ^ 59
def prefixEnd_103 : Nat := 4983230072969 + 3 ^ 40 * 103 * 2
def baseEnd_103 : Nat := 31341337788640421945

theorem tailTrace_103 : CollatzResearch.WordTrace tailWord_103 prefixEnd_103 31341337788640421945 := by
  apply H28Certificate.checkWord_sound
  decide

theorem cell19_103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 5, 3].length) (baseStart_103 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_103 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_103 prefixEnd_103 := by exact prefixLift 103
  have htrace : WordTrace (prefixWord ++ tailWord_103) baseStart_103 baseEnd_103 := by
    simpa [prefixWord, tailWord_103, baseEnd_103] using wordTrace_append hprefix tailTrace_103
  have hstable : (prefixWord ++ tailWord_103).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103).length < 2 ^ (prefixWord ++ tailWord_103).sum := by decide
  have hdescent : baseEnd_103 < baseStart_103 := by decide
  rcases family_descends (prefixWord ++ tailWord_103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124 : List Nat := [2, 2, 2, 1, 1, 5, 6]
def baseStart_124 : Nat := 118140960795 + 124 * 2 ^ 59
def prefixEnd_124 : Nat := 4983230072969 + 3 ^ 40 * 124 * 2
def baseEnd_124 : Nat := 12577106422271318407

theorem tailTrace_124 : CollatzResearch.WordTrace tailWord_124 prefixEnd_124 12577106422271318407 := by
  apply H28Certificate.checkWord_sound
  decide

theorem cell19_124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 6].length) (baseStart_124 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_124 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_124 prefixEnd_124 := by exact prefixLift 124
  have htrace : WordTrace (prefixWord ++ tailWord_124) baseStart_124 baseEnd_124 := by
    simpa [prefixWord, tailWord_124, baseEnd_124] using wordTrace_append hprefix tailTrace_124
  have hstable : (prefixWord ++ tailWord_124).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124).length < 2 ^ (prefixWord ++ tailWord_124).sum := by decide
  have hdescent : baseEnd_124 < baseStart_124 := by decide
  rcases family_descends (prefixWord ++ tailWord_124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150 : List Nat := [5, 3, 2, 1, 1, 2, 2, 3]
def baseStart_150 : Nat := 118140960795 + 150 * 2 ^ 59
def prefixEnd_150 : Nat := 4983230072969 + 3 ^ 40 * 150 * 2
def baseEnd_150 : Nat := 45642724906457377373

theorem tailTrace_150 : CollatzResearch.WordTrace tailWord_150 prefixEnd_150 45642724906457377373 := by
  apply H28Certificate.checkWord_sound
  decide

theorem cell19_150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 2, 3].length) (baseStart_150 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_150 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_150 prefixEnd_150 := by exact prefixLift 150
  have htrace : WordTrace (prefixWord ++ tailWord_150) baseStart_150 baseEnd_150 := by
    simpa [prefixWord, tailWord_150, baseEnd_150] using wordTrace_append hprefix tailTrace_150
  have hstable : (prefixWord ++ tailWord_150).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150).length < 2 ^ (prefixWord ++ tailWord_150).sum := by decide
  have hdescent : baseEnd_150 < baseStart_150 := by decide
  rcases family_descends (prefixWord ++ tailWord_150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158 : List Nat := [4, 3, 1, 1, 3, 1, 1, 5]
def baseStart_158 : Nat := 118140960795 + 158 * 2 ^ 59
def prefixEnd_158 : Nat := 4983230072969 + 3 ^ 40 * 158 * 2
def baseEnd_158 : Nat := 48077003564809199573

theorem tailTrace_158 : CollatzResearch.WordTrace tailWord_158 prefixEnd_158 48077003564809199573 := by
  apply H28Certificate.checkWord_sound
  decide

theorem cell19_158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 5].length) (baseStart_158 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_158 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_158 prefixEnd_158 := by exact prefixLift 158
  have htrace : WordTrace (prefixWord ++ tailWord_158) baseStart_158 baseEnd_158 := by
    simpa [prefixWord, tailWord_158, baseEnd_158] using wordTrace_append hprefix tailTrace_158
  have hstable : (prefixWord ++ tailWord_158).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158).length < 2 ^ (prefixWord ++ tailWord_158).sum := by decide
  have hdescent : baseEnd_158 < baseStart_158 := by decide
  rcases family_descends (prefixWord ++ tailWord_158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160 : List Nat := [2, 1, 1, 4, 2, 2, 4, 3]
def baseStart_160 : Nat := 118140960795 + 160 * 2 ^ 59
def prefixEnd_160 : Nat := 4983230072969 + 3 ^ 40 * 160 * 2
def baseEnd_160 : Nat := 48685573229397155123

theorem tailTrace_160 : CollatzResearch.WordTrace tailWord_160 prefixEnd_160 48685573229397155123 := by
  apply H28Certificate.checkWord_sound
  decide

theorem cell19_160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 4, 3].length) (baseStart_160 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_160 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_160 prefixEnd_160 := by exact prefixLift 160
  have htrace : WordTrace (prefixWord ++ tailWord_160) baseStart_160 baseEnd_160 := by
    simpa [prefixWord, tailWord_160, baseEnd_160] using wordTrace_append hprefix tailTrace_160
  have hstable : (prefixWord ++ tailWord_160).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160).length < 2 ^ (prefixWord ++ tailWord_160).sum := by decide
  have hdescent : baseEnd_160 < baseStart_160 := by decide
  rcases family_descends (prefixWord ++ tailWord_160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177 : List Nat := [1, 2, 2, 5, 3, 1, 5]
def baseStart_177 : Nat := 118140960795 + 177 * 2 ^ 59
def prefixEnd_177 : Nat := 4983230072969 + 3 ^ 40 * 177 * 2
def baseEnd_177 : Nat := 17952805126131592433

theorem tailTrace_177 : CollatzResearch.WordTrace tailWord_177 prefixEnd_177 17952805126131592433 := by
  apply H28Certificate.checkWord_sound
  decide

theorem cell19_177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 5].length) (baseStart_177 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_177 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_177 prefixEnd_177 := by exact prefixLift 177
  have htrace : WordTrace (prefixWord ++ tailWord_177) baseStart_177 baseEnd_177 := by
    simpa [prefixWord, tailWord_177, baseEnd_177] using wordTrace_append hprefix tailTrace_177
  have hstable : (prefixWord ++ tailWord_177).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177).length < 2 ^ (prefixWord ++ tailWord_177).sum := by decide
  have hdescent : baseEnd_177 < baseStart_177 := by decide
  rcases family_descends (prefixWord ++ tailWord_177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194 : List Nat := [3, 5, 1, 1, 1, 2, 2, 4]
def baseStart_194 : Nat := 118140960795 + 194 * 2 ^ 59
def prefixEnd_194 : Nat := 4983230072969 + 3 ^ 40 * 194 * 2
def baseEnd_194 : Nat := 59031257527392399475

theorem tailTrace_194 : CollatzResearch.WordTrace tailWord_194 prefixEnd_194 59031257527392399475 := by
  apply H28Certificate.checkWord_sound
  decide

theorem cell19_194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 4].length) (baseStart_194 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_194 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_194 prefixEnd_194 := by exact prefixLift 194
  have htrace : WordTrace (prefixWord ++ tailWord_194) baseStart_194 baseEnd_194 := by
    simpa [prefixWord, tailWord_194, baseEnd_194] using wordTrace_append hprefix tailTrace_194
  have hstable : (prefixWord ++ tailWord_194).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194).length < 2 ^ (prefixWord ++ tailWord_194).sum := by decide
  have hdescent : baseEnd_194 < baseStart_194 := by decide
  rcases family_descends (prefixWord ++ tailWord_194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348 : List Nat := [2, 2, 4, 3, 1, 2, 5]
def baseStart_348 : Nat := 118140960795 + 348 * 2 ^ 59
def prefixEnd_348 : Nat := 4983230072969 + 3 ^ 40 * 348 * 2
def baseEnd_348 : Nat := 35297040566888325611

theorem tailTrace_348 : CollatzResearch.WordTrace tailWord_348 prefixEnd_348 35297040566888325611 := by
  apply H28Certificate.checkWord_sound
  decide

theorem cell19_348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 5].length) (baseStart_348 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_348 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_348 prefixEnd_348 := by exact prefixLift 348
  have htrace : WordTrace (prefixWord ++ tailWord_348) baseStart_348 baseEnd_348 := by
    simpa [prefixWord, tailWord_348, baseEnd_348] using wordTrace_append hprefix tailTrace_348
  have hstable : (prefixWord ++ tailWord_348).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348).length < 2 ^ (prefixWord ++ tailWord_348).sum := by decide
  have hdescent : baseEnd_348 < baseStart_348 := by decide
  rcases family_descends (prefixWord ++ tailWord_348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424 : List Nat := [2, 1, 6, 1, 1, 3, 1, 4]
def baseStart_424 : Nat := 118140960795 + 424 * 2 ^ 59
def prefixEnd_424 : Nat := 4983230072969 + 3 ^ 40 * 424 * 2
def baseEnd_424 : Nat := 129016768955007287737

theorem tailTrace_424 : CollatzResearch.WordTrace tailWord_424 prefixEnd_424 129016768955007287737 := by
  apply H28Certificate.checkWord_sound
  decide

theorem cell19_424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 4].length) (baseStart_424 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_424 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_424 prefixEnd_424 := by exact prefixLift 424
  have htrace : WordTrace (prefixWord ++ tailWord_424) baseStart_424 baseEnd_424 := by
    simpa [prefixWord, tailWord_424, baseEnd_424] using wordTrace_append hprefix tailTrace_424
  have hstable : (prefixWord ++ tailWord_424).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424).length < 2 ^ (prefixWord ++ tailWord_424).sum := by decide
  have hdescent : baseEnd_424 < baseStart_424 := by decide
  rcases family_descends (prefixWord ++ tailWord_424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445 : List Nat := [1, 4, 1, 2, 2, 3, 3, 3]
def baseStart_445 : Nat := 118140960795 + 445 * 2 ^ 59
def prefixEnd_445 : Nat := 4983230072969 + 3 ^ 40 * 445 * 2
def baseEnd_445 : Nat := 135406750433180821013

theorem tailTrace_445 : CollatzResearch.WordTrace tailWord_445 prefixEnd_445 135406750433180821013 := by
  apply H28Certificate.checkWord_sound
  decide

theorem cell19_445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 3, 3].length) (baseStart_445 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_445 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_445 prefixEnd_445 := by exact prefixLift 445
  have htrace : WordTrace (prefixWord ++ tailWord_445) baseStart_445 baseEnd_445 := by
    simpa [prefixWord, tailWord_445, baseEnd_445] using wordTrace_append hprefix tailTrace_445
  have hstable : (prefixWord ++ tailWord_445).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445).length < 2 ^ (prefixWord ++ tailWord_445).sum := by decide
  have hdescent : baseEnd_445 < baseStart_445 := by decide
  rcases family_descends (prefixWord ++ tailWord_445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498 : List Nat := [3, 2, 1, 4, 3, 1, 2, 3]
def baseStart_498 : Nat := 118140960795 + 498 * 2 ^ 59
def prefixEnd_498 : Nat := 4983230072969 + 3 ^ 40 * 498 * 2
def baseEnd_498 : Nat := 151533846544761643091

theorem tailTrace_498 : CollatzResearch.WordTrace tailWord_498 prefixEnd_498 151533846544761643091 := by
  apply H28Certificate.checkWord_sound
  decide

theorem cell19_498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 2, 3].length) (baseStart_498 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_498 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_498 prefixEnd_498 := by exact prefixLift 498
  have htrace : WordTrace (prefixWord ++ tailWord_498) baseStart_498 baseEnd_498 := by
    simpa [prefixWord, tailWord_498, baseEnd_498] using wordTrace_append hprefix tailTrace_498
  have hstable : (prefixWord ++ tailWord_498).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498).length < 2 ^ (prefixWord ++ tailWord_498).sum := by decide
  have hdescent : baseEnd_498 < baseStart_498 := by decide
  rcases family_descends (prefixWord ++ tailWord_498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523 : List Nat := [1, 1, 1, 1, 7, 3, 5]
def baseStart_523 : Nat := 118140960795 + 523 * 2 ^ 59
def prefixEnd_523 : Nat := 4983230072969 + 3 ^ 40 * 523 * 2
def baseEnd_523 : Nat := 53046989117370362489

theorem tailTrace_523 : CollatzResearch.WordTrace tailWord_523 prefixEnd_523 53046989117370362489 := by
  apply H28Certificate.checkWord_sound
  decide

theorem cell19_523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 5].length) (baseStart_523 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_523 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_523 prefixEnd_523 := by exact prefixLift 523
  have htrace : WordTrace (prefixWord ++ tailWord_523) baseStart_523 baseEnd_523 := by
    simpa [prefixWord, tailWord_523, baseEnd_523] using wordTrace_append hprefix tailTrace_523
  have hstable : (prefixWord ++ tailWord_523).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523).length < 2 ^ (prefixWord ++ tailWord_523).sum := by decide
  have hdescent : baseEnd_523 < baseStart_523 := by decide
  rcases family_descends (prefixWord ++ tailWord_523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩


end V185TrunkScan19Incremental
