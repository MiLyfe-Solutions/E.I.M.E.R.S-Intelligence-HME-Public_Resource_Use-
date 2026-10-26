import V185TrunkScan19Chunk019

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental

namespace V185TrunkScan19Incremental

def tailWord_201535 : List Nat := [1, 1, 2, 2, 5, 3, 1, 4]
def baseStart_201535 : Nat := 118140960795 + 201535 * 2 ^ 59
def prefixEnd_201535 : Nat := 4983230072969 + 3 ^ 40 * 201535 * 2
def baseEnd_201535 : Nat := 61324043676429171606319

theorem tailTrace_201535 : CollatzResearch.WordTrace tailWord_201535 prefixEnd_201535 61324043676429171606319 := by
  unfold tailWord_201535
  simp only [CollatzResearch.WordTrace]
  refine ⟨7350585324880589282838059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4900390216587059521892039 7350585324880589282838059)
  ·
    refine ⟨11025877987320883924257089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7350585324880589282838059 11025877987320883924257089)
    ·
      refine ⟨8269408490490662943192817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11025877987320883924257089 8269408490490662943192817)
      ·
        refine ⟨6202056367867997207394613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8269408490490662943192817 6202056367867997207394613)
        ·
          refine ⟨581442784487624738193245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6202056367867997207394613 581442784487624738193245)
          ·
            refine ⟨218041044182859276822467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 581442784487624738193245 218041044182859276822467)
            ·
              refine ⟨327061566274288915233701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 218041044182859276822467 327061566274288915233701)
              ·
                refine ⟨61324043676429171606319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 327061566274288915233701 61324043676429171606319)
                ·
                  rfl

theorem cell19_201535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 1, 4].length) (baseStart_201535 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_201535 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_201535 prefixEnd_201535 := by exact prefixLift 201535
  have htrace : WordTrace (prefixWord ++ tailWord_201535) baseStart_201535 baseEnd_201535 := by
    simpa [prefixWord, tailWord_201535, baseEnd_201535] using wordTrace_append hprefix tailTrace_201535
  have hstable : (prefixWord ++ tailWord_201535).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201535).length < 2 ^ (prefixWord ++ tailWord_201535).sum := by decide
  have hdescent : baseEnd_201535 < baseStart_201535 := by decide
  rcases family_descends (prefixWord ++ tailWord_201535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201554 : List Nat := [3, 2, 2, 1, 1, 2, 5, 3]
def baseStart_201554 : Nat := 118140960795 + 201554 * 2 ^ 59
def prefixEnd_201554 : Nat := 4983230072969 + 3 ^ 40 * 201554 * 2
def baseEnd_201554 : Nat := 61329825088242757184045

theorem tailTrace_201554 : CollatzResearch.WordTrace tailWord_201554 prefixEnd_201554 61329825088242757184045 := by
  unfold tailWord_201554
  simp only [CollatzResearch.WordTrace]
  refine ⟨1837819577952938881944929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4900852207874503685186477 1837819577952938881944929)
  ·
    refine ⟨1378364683464704161458697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1837819577952938881944929 1378364683464704161458697)
    ·
      refine ⟨1033773512598528121094023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1378364683464704161458697 1033773512598528121094023)
      ·
        refine ⟨1550660268897792181641035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1033773512598528121094023 1550660268897792181641035)
        ·
          refine ⟨2325990403346688272461553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1550660268897792181641035 2325990403346688272461553)
          ·
            refine ⟨1744492802510016204346165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2325990403346688272461553 1744492802510016204346165)
            ·
              refine ⟨163546200235314019157453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1744492802510016204346165 163546200235314019157453)
              ·
                refine ⟨61329825088242757184045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 163546200235314019157453 61329825088242757184045)
                ·
                  rfl

theorem cell19_201554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 5, 3].length) (baseStart_201554 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_201554 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_201554 prefixEnd_201554 := by exact prefixLift 201554
  have htrace : WordTrace (prefixWord ++ tailWord_201554) baseStart_201554 baseEnd_201554 := by
    simpa [prefixWord, tailWord_201554, baseEnd_201554] using wordTrace_append hprefix tailTrace_201554
  have hstable : (prefixWord ++ tailWord_201554).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201554).length < 2 ^ (prefixWord ++ tailWord_201554).sum := by decide
  have hdescent : baseEnd_201554 < baseStart_201554 := by decide
  rcases family_descends (prefixWord ++ tailWord_201554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201575 : List Nat := [1, 1, 5, 1, 2, 3, 6]
def baseStart_201575 : Nat := 118140960795 + 201575 * 2 ^ 59
def prefixEnd_201575 : Nat := 4983230072969 + 3 ^ 40 * 201575 * 2
def baseEnd_201575 : Nat := 20445405023240310239107

theorem tailTrace_201575 : CollatzResearch.WordTrace tailWord_201575 prefixEnd_201575 20445405023240310239107 := by
  unfold tailWord_201575
  simp only [CollatzResearch.WordTrace]
  refine ⟨7352044244735676114294179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4901362829823784076196119 7352044244735676114294179)
  ·
    refine ⟨11028066367103514171441269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7352044244735676114294179 11028066367103514171441269)
    ·
      refine ⟨1033881221915954453572619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11028066367103514171441269 1033881221915954453572619)
      ·
        refine ⟨1550821832873931680358929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1033881221915954453572619 1550821832873931680358929)
        ·
          refine ⟨1163116374655448760269197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1550821832873931680358929 1163116374655448760269197)
          ·
            refine ⟨436168640495793285100949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1163116374655448760269197 436168640495793285100949)
            ·
              refine ⟨20445405023240310239107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 436168640495793285100949 20445405023240310239107)
              ·
                rfl

theorem cell19_201575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 6].length) (baseStart_201575 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_201575 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_201575 prefixEnd_201575 := by exact prefixLift 201575
  have htrace : WordTrace (prefixWord ++ tailWord_201575) baseStart_201575 baseEnd_201575 := by
    simpa [prefixWord, tailWord_201575, baseEnd_201575] using wordTrace_append hprefix tailTrace_201575
  have hstable : (prefixWord ++ tailWord_201575).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201575).length < 2 ^ (prefixWord ++ tailWord_201575).sum := by decide
  have hdescent : baseEnd_201575 < baseStart_201575 := by decide
  rcases family_descends (prefixWord ++ tailWord_201575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201628 : List Nat := [2, 2, 3, 3, 3, 1, 5]
def baseStart_201628 : Nat := 118140960795 + 201628 * 2 ^ 59
def prefixEnd_201628 : Nat := 4983230072969 + 3 ^ 40 * 201628 * 2
def baseEnd_201628 : Nat := 20450780721944170513133

theorem tailTrace_201628 : CollatzResearch.WordTrace tailWord_201628 prefixEnd_201628 20450780721944170513133 := by
  unfold tailWord_201628
  simp only [CollatzResearch.WordTrace]
  refine ⟨3676988656771833082986769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4902651542362444110649025 3676988656771833082986769)
  ·
    refine ⟨2757741492578874812240077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3676988656771833082986769 2757741492578874812240077)
    ·
      refine ⟨1034153059717078054590029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2757741492578874812240077 1034153059717078054590029)
      ·
        refine ⟨387807397393904270471261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1034153059717078054590029 387807397393904270471261)
        ·
          refine ⟨145427774022714101426723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 387807397393904270471261 145427774022714101426723)
          ·
            refine ⟨218141661034071152140085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145427774022714101426723 218141661034071152140085)
            ·
              refine ⟨20450780721944170513133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 218141661034071152140085 20450780721944170513133)
              ·
                rfl

theorem cell19_201628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 5].length) (baseStart_201628 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_201628 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_201628 prefixEnd_201628 := by exact prefixLift 201628
  have htrace : WordTrace (prefixWord ++ tailWord_201628) baseStart_201628 baseEnd_201628 := by
    simpa [prefixWord, tailWord_201628, baseEnd_201628] using wordTrace_append hprefix tailTrace_201628
  have hstable : (prefixWord ++ tailWord_201628).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201628).length < 2 ^ (prefixWord ++ tailWord_201628).sum := by decide
  have hdescent : baseEnd_201628 < baseStart_201628 := by decide
  rcases family_descends (prefixWord ++ tailWord_201628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201649 : List Nat := [1, 2, 2, 4, 3, 1, 2, 4]
def baseStart_201649 : Nat := 118140960795 + 201649 * 2 ^ 59
def prefixEnd_201649 : Nat := 4983230072969 + 3 ^ 40 * 201649 * 2
def baseEnd_201649 : Nat := 61358732147310685072675

theorem tailTrace_201649 : CollatzResearch.WordTrace tailWord_201649 prefixEnd_201649 61358732147310685072675 := by
  unfold tailWord_201649
  simp only [CollatzResearch.WordTrace]
  refine ⟨7354743246467586752488001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4903162164311724501658667 7354743246467586752488001)
  ·
    refine ⟨5516057434850690064366001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7354743246467586752488001 5516057434850690064366001)
    ·
      refine ⟨4137043076138017548274501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5516057434850690064366001 4137043076138017548274501)
      ·
        refine ⟨775695576775878290301469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4137043076138017548274501 775695576775878290301469)
        ·
          refine ⟨290885841290954358863051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 775695576775878290301469 290885841290954358863051)
          ·
            refine ⟨436328761936431538294577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 290885841290954358863051 436328761936431538294577)
            ·
              refine ⟨327246571452323653720933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 436328761936431538294577 327246571452323653720933)
              ·
                refine ⟨61358732147310685072675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 327246571452323653720933 61358732147310685072675)
                ·
                  rfl

theorem cell19_201649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 2, 4].length) (baseStart_201649 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_201649 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_201649 prefixEnd_201649 := by exact prefixLift 201649
  have htrace : WordTrace (prefixWord ++ tailWord_201649) baseStart_201649 baseEnd_201649 := by
    simpa [prefixWord, tailWord_201649, baseEnd_201649] using wordTrace_append hprefix tailTrace_201649
  have hstable : (prefixWord ++ tailWord_201649).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201649).length < 2 ^ (prefixWord ++ tailWord_201649).sum := by decide
  have hdescent : baseEnd_201649 < baseStart_201649 := by decide
  rcases family_descends (prefixWord ++ tailWord_201649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201706 : List Nat := [3, 1, 3, 1, 2, 4, 1, 4]
def baseStart_201706 : Nat := 118140960795 + 201706 * 2 ^ 59
def prefixEnd_201706 : Nat := 4983230072969 + 3 ^ 40 * 201706 * 2
def baseEnd_201706 : Nat := 61376076382751441805853

theorem tailTrace_201706 : CollatzResearch.WordTrace tailWord_201706 prefixEnd_201706 61376076382751441805853 := by
  unfold tailWord_201706
  simp only [CollatzResearch.WordTrace]
  refine ⟨1839205551815271371828243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4904548138174056991541981 1839205551815271371828243)
  ·
    refine ⟨2758808327722907057742365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1839205551815271371828243 2758808327722907057742365)
    ·
      refine ⟨1034553122896090146653387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2758808327722907057742365 1034553122896090146653387)
      ·
        refine ⟨1551829684344135219980081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1034553122896090146653387 1551829684344135219980081)
        ·
          refine ⟨1163872263258101414985061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1551829684344135219980081 1163872263258101414985061)
          ·
            refine ⟨218226049360894015309699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1163872263258101414985061 218226049360894015309699)
            ·
              refine ⟨327339074041341022964549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 218226049360894015309699 327339074041341022964549)
              ·
                refine ⟨61376076382751441805853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 327339074041341022964549 61376076382751441805853)
                ·
                  rfl

theorem cell19_201706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 1, 4].length) (baseStart_201706 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_201706 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_201706 prefixEnd_201706 := by exact prefixLift 201706
  have htrace : WordTrace (prefixWord ++ tailWord_201706) baseStart_201706 baseEnd_201706 := by
    simpa [prefixWord, tailWord_201706, baseEnd_201706] using wordTrace_append hprefix tailTrace_201706
  have hstable : (prefixWord ++ tailWord_201706).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201706).length < 2 ^ (prefixWord ++ tailWord_201706).sum := by decide
  have hdescent : baseEnd_201706 < baseStart_201706 := by decide
  rcases family_descends (prefixWord ++ tailWord_201706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201780 : List Nat := [2, 5, 1, 2, 1, 1, 4, 3]
def baseStart_201780 : Nat := 118140960795 + 201780 * 2 ^ 59
def prefixEnd_201780 : Nat := 4983230072969 + 3 ^ 40 * 201780 * 2
def baseEnd_201780 : Nat := 61398593460341196161207

theorem tailTrace_201780 : CollatzResearch.WordTrace tailWord_201780 prefixEnd_201780 61398593460341196161207 := by
  unfold tailWord_201780
  simp only [CollatzResearch.WordTrace]
  refine ⟨3679760604496498062753397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4906347472661997417004529 3679760604496498062753397)
  ·
    refine ⟨344977556671546693383131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3679760604496498062753397 344977556671546693383131)
    ·
      refine ⟨517466335007320040074697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 344977556671546693383131 517466335007320040074697)
      ·
        refine ⟨388099751255490030056023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 517466335007320040074697 388099751255490030056023)
        ·
          refine ⟨582149626883235045084035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 388099751255490030056023 582149626883235045084035)
          ·
            refine ⟨873224440324852567626053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 582149626883235045084035 873224440324852567626053)
            ·
              refine ⟨163729582560909856429885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 873224440324852567626053 163729582560909856429885)
              ·
                refine ⟨61398593460341196161207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 163729582560909856429885 61398593460341196161207)
                ·
                  rfl

theorem cell19_201780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 4, 3].length) (baseStart_201780 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_201780 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_201780 prefixEnd_201780 := by exact prefixLift 201780
  have htrace : WordTrace (prefixWord ++ tailWord_201780) baseStart_201780 baseEnd_201780 := by
    simpa [prefixWord, tailWord_201780, baseEnd_201780] using wordTrace_append hprefix tailTrace_201780
  have hstable : (prefixWord ++ tailWord_201780).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201780).length < 2 ^ (prefixWord ++ tailWord_201780).sum := by decide
  have hdescent : baseEnd_201780 < baseStart_201780 := by decide
  rcases family_descends (prefixWord ++ tailWord_201780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201782 : List Nat := [5, 1, 2, 1, 1, 3, 1, 5]
def baseStart_201782 : Nat := 118140960795 + 201782 * 2 ^ 59
def prefixEnd_201782 : Nat := 4983230072969 + 3 ^ 40 * 201782 * 2
def baseEnd_201782 : Nat := 61399202030005784116757

theorem tailTrace_201782 : CollatzResearch.WordTrace tailWord_201782 prefixEnd_201782 61399202030005784116757 := by
  unfold tailWord_201782
  simp only [CollatzResearch.WordTrace]
  refine ⟨459974634686609404192475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4906396103323833644719733 459974634686609404192475)
  ·
    refine ⟨689961952029914106288713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 459974634686609404192475 689961952029914106288713)
    ·
      refine ⟨517471464022435579716535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 689961952029914106288713 517471464022435579716535)
      ·
        refine ⟨776207196033653369574803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 517471464022435579716535 776207196033653369574803)
        ·
          refine ⟨1164310794050480054362205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 776207196033653369574803 1164310794050480054362205)
          ·
            refine ⟨436616547768930020385827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1164310794050480054362205 436616547768930020385827)
            ·
              refine ⟨654924821653395030578741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 436616547768930020385827 654924821653395030578741)
              ·
                refine ⟨61399202030005784116757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 654924821653395030578741 61399202030005784116757)
                ·
                  rfl

theorem cell19_201782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_201782 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_201782 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_201782 prefixEnd_201782 := by exact prefixLift 201782
  have htrace : WordTrace (prefixWord ++ tailWord_201782) baseStart_201782 baseEnd_201782 := by
    simpa [prefixWord, tailWord_201782, baseEnd_201782] using wordTrace_append hprefix tailTrace_201782
  have hstable : (prefixWord ++ tailWord_201782).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201782).length < 2 ^ (prefixWord ++ tailWord_201782).sum := by decide
  have hdescent : baseEnd_201782 < baseStart_201782 := by decide
  rcases family_descends (prefixWord ++ tailWord_201782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201784 : List Nat := [2, 1, 2, 1, 5, 2, 1, 5]
def baseStart_201784 : Nat := 118140960795 + 201784 * 2 ^ 59
def prefixEnd_201784 : Nat := 4983230072969 + 3 ^ 40 * 201784 * 2
def baseEnd_201784 : Nat := 61399810599670372072307

theorem tailTrace_201784 : CollatzResearch.WordTrace tailWord_201784 prefixEnd_201784 61399810599670372072307 := by
  unfold tailWord_201784
  simp only [CollatzResearch.WordTrace]
  refine ⟨3679833550489252404326203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4906444733985669872434937 3679833550489252404326203)
  ·
    refine ⟨5519750325733878606489305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3679833550489252404326203 5519750325733878606489305)
    ·
      refine ⟨4139812744300408954866979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5519750325733878606489305 4139812744300408954866979)
      ·
        refine ⟨6209719116450613432300469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4139812744300408954866979 6209719116450613432300469)
        ·
          refine ⟨582161167167245009278169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6209719116450613432300469 582161167167245009278169)
          ·
            refine ⟨436620875375433756958627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 582161167167245009278169 436620875375433756958627)
            ·
              refine ⟨654931313063150635437941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 436620875375433756958627 654931313063150635437941)
              ·
                refine ⟨61399810599670372072307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 654931313063150635437941 61399810599670372072307)
                ·
                  rfl

theorem cell19_201784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 5].length) (baseStart_201784 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_201784 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_201784 prefixEnd_201784 := by exact prefixLift 201784
  have htrace : WordTrace (prefixWord ++ tailWord_201784) baseStart_201784 baseEnd_201784 := by
    simpa [prefixWord, tailWord_201784, baseEnd_201784] using wordTrace_append hprefix tailTrace_201784
  have hstable : (prefixWord ++ tailWord_201784).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201784).length < 2 ^ (prefixWord ++ tailWord_201784).sum := by decide
  have hdescent : baseEnd_201784 < baseStart_201784 := by decide
  rcases family_descends (prefixWord ++ tailWord_201784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201854 : List Nat := [4, 2, 4, 1, 2, 6]
def baseStart_201854 : Nat := 118140960795 + 201854 * 2 ^ 59
def prefixEnd_201854 : Nat := 4983230072969 + 3 ^ 40 * 201854 * 2
def baseEnd_201854 : Nat := 6824567837547883390729

theorem tailTrace_201854 : CollatzResearch.WordTrace tailWord_201854 prefixEnd_201854 6824567837547883390729 := by
  unfold tailWord_201854
  simp only [CollatzResearch.WordTrace]
  refine ⟨920277526340613345462577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4908146807149937842467077 920277526340613345462577)
  ·
    refine ⟨690208144755460009096933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 920277526340613345462577 690208144755460009096933)
    ·
      refine ⟨129414027141648751705675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 690208144755460009096933 129414027141648751705675)
      ·
        refine ⟨194121040712473127558513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129414027141648751705675 194121040712473127558513)
        ·
          refine ⟨145590780534354845668885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194121040712473127558513 145590780534354845668885)
          ·
            refine ⟨6824567837547883390729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 145590780534354845668885 6824567837547883390729)
            ·
              rfl

theorem cell19_201854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 6].length) (baseStart_201854 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_201854 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_201854 prefixEnd_201854 := by exact prefixLift 201854
  have htrace : WordTrace (prefixWord ++ tailWord_201854) baseStart_201854 baseEnd_201854 := by
    simpa [prefixWord, tailWord_201854, baseEnd_201854] using wordTrace_append hprefix tailTrace_201854
  have hstable : (prefixWord ++ tailWord_201854).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201854).length < 2 ^ (prefixWord ++ tailWord_201854).sum := by decide
  have hdescent : baseEnd_201854 < baseStart_201854 := by decide
  rcases family_descends (prefixWord ++ tailWord_201854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201879 : List Nat := [1, 1, 3, 3, 3, 1, 3, 4]
def baseStart_201879 : Nat := 118140960795 + 201879 * 2 ^ 59
def prefixEnd_201879 : Nat := 4983230072969 + 3 ^ 40 * 201879 * 2
def baseEnd_201879 : Nat := 61428717658738299960937

theorem tailTrace_201879 : CollatzResearch.WordTrace tailWord_201879 prefixEnd_201879 61428717658738299960937 := by
  unfold tailWord_201879
  simp only [CollatzResearch.WordTrace]
  refine ⟨7363132035634336033360691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4908754690422890688907127 7363132035634336033360691)
  ·
    refine ⟨11044698053451504050041037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7363132035634336033360691 11044698053451504050041037)
    ·
      refine ⟨4141761770044314018765389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11044698053451504050041037 4141761770044314018765389)
      ·
        refine ⟨1553160663766617757037021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4141761770044314018765389 1553160663766617757037021)
        ·
          refine ⟨582435248912481658888883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1553160663766617757037021 582435248912481658888883)
          ·
            refine ⟨873652873368722488333325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 582435248912481658888883 873652873368722488333325)
            ·
              refine ⟨327619827513270933124997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 873652873368722488333325 327619827513270933124997)
              ·
                refine ⟨61428717658738299960937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 327619827513270933124997 61428717658738299960937)
                ·
                  rfl

theorem cell19_201879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3, 4].length) (baseStart_201879 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_201879 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_201879 prefixEnd_201879 := by exact prefixLift 201879
  have htrace : WordTrace (prefixWord ++ tailWord_201879) baseStart_201879 baseEnd_201879 := by
    simpa [prefixWord, tailWord_201879, baseEnd_201879] using wordTrace_append hprefix tailTrace_201879
  have hstable : (prefixWord ++ tailWord_201879).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201879).length < 2 ^ (prefixWord ++ tailWord_201879).sum := by decide
  have hdescent : baseEnd_201879 < baseStart_201879 := by decide
  rcases family_descends (prefixWord ++ tailWord_201879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201949 : List Nat := [1, 4, 3, 2, 3, 1, 2, 3]
def baseStart_201949 : Nat := 118140960795 + 201949 * 2 ^ 59
def prefixEnd_201949 : Nat := 4983230072969 + 3 ^ 40 * 201949 * 2
def baseEnd_201949 : Nat := 61450017596998878405191

theorem tailTrace_201949 : CollatzResearch.WordTrace tailWord_201949 prefixEnd_201949 61450017596998878405191 := by
  unfold tailWord_201949
  simp only [CollatzResearch.WordTrace]
  refine ⟨7365685145380737988408901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4910456763587158658939267 7365685145380737988408901)
  ·
    refine ⟨1381065964758888372826669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7365685145380737988408901 1381065964758888372826669)
    ·
      refine ⟨517899736784583139810001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1381065964758888372826669 517899736784583139810001)
      ·
        refine ⟨388424802588437354857501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 517899736784583139810001 388424802588437354857501)
        ·
          refine ⟨145659300970664008071563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 388424802588437354857501 145659300970664008071563)
          ·
            refine ⟨218488951455996012107345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145659300970664008071563 218488951455996012107345)
            ·
              refine ⟨163866713591997009080509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 218488951455996012107345 163866713591997009080509)
              ·
                refine ⟨61450017596998878405191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 163866713591997009080509 61450017596998878405191)
                ·
                  rfl

theorem cell19_201949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 2, 3].length) (baseStart_201949 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_201949 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_201949 prefixEnd_201949 := by exact prefixLift 201949
  have htrace : WordTrace (prefixWord ++ tailWord_201949) baseStart_201949 baseEnd_201949 := by
    simpa [prefixWord, tailWord_201949, baseEnd_201949] using wordTrace_append hprefix tailTrace_201949
  have hstable : (prefixWord ++ tailWord_201949).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201949).length < 2 ^ (prefixWord ++ tailWord_201949).sum := by decide
  have hdescent : baseEnd_201949 < baseStart_201949 := by decide
  rcases family_descends (prefixWord ++ tailWord_201949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201953 : List Nat := [1, 2, 3, 1, 3, 4, 2, 3]
def baseStart_201953 : Nat := 118140960795 + 201953 * 2 ^ 59
def prefixEnd_201953 : Nat := 4983230072969 + 3 ^ 40 * 201953 * 2
def baseEnd_201953 : Nat := 61451234736328054316291

theorem tailTrace_201953 : CollatzResearch.WordTrace tailWord_201953 prefixEnd_201953 61451234736328054316291 := by
  unfold tailWord_201953
  simp only [CollatzResearch.WordTrace]
  refine ⟨7365831037366246671554513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4910554024910831114369675 7365831037366246671554513)
  ·
    refine ⟨5524373278024685003665885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7365831037366246671554513 5524373278024685003665885)
    ·
      refine ⟨2071639979259256876374707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5524373278024685003665885 2071639979259256876374707)
      ·
        refine ⟨3107459968888885314562061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2071639979259256876374707 3107459968888885314562061)
        ·
          refine ⟨1165297488333331992960773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3107459968888885314562061 1165297488333331992960773)
          ·
            refine ⟨218493279062499748680145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1165297488333331992960773 218493279062499748680145)
            ·
              refine ⟨163869959296874811510109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 218493279062499748680145 163869959296874811510109)
              ·
                refine ⟨61451234736328054316291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 163869959296874811510109 61451234736328054316291)
                ·
                  rfl

theorem cell19_201953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 2, 3].length) (baseStart_201953 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_201953 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_201953 prefixEnd_201953 := by exact prefixLift 201953
  have htrace : WordTrace (prefixWord ++ tailWord_201953) baseStart_201953 baseEnd_201953 := by
    simpa [prefixWord, tailWord_201953, baseEnd_201953] using wordTrace_append hprefix tailTrace_201953
  have hstable : (prefixWord ++ tailWord_201953).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201953).length < 2 ^ (prefixWord ++ tailWord_201953).sum := by decide
  have hdescent : baseEnd_201953 < baseStart_201953 := by decide
  rcases family_descends (prefixWord ++ tailWord_201953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201995 : List Nat := [1, 1, 1, 1, 5, 3, 1, 6]
def baseStart_201995 : Nat := 118140960795 + 201995 * 2 ^ 59
def prefixEnd_201995 : Nat := 4983230072969 + 3 ^ 40 * 201995 * 2
def baseEnd_201995 : Nat := 61464014699284401382843

theorem tailTrace_201995 : CollatzResearch.WordTrace tailWord_201995 prefixEnd_201995 61464014699284401382843 := by
  unfold tailWord_201995
  simp only [CollatzResearch.WordTrace]
  refine ⟨7367362903214087844583439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4911575268809391896388959 7367362903214087844583439)
  ·
    refine ⟨11051044354821131766875159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7367362903214087844583439 11051044354821131766875159)
    ·
      refine ⟨16576566532231697650312739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11051044354821131766875159 16576566532231697650312739)
      ·
        refine ⟨24864849798347546475469109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16576566532231697650312739 24864849798347546475469109)
        ·
          refine ⟨2331079668595082482075229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24864849798347546475469109 2331079668595082482075229)
          ·
            refine ⟨874154875723155930778211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2331079668595082482075229 874154875723155930778211)
            ·
              refine ⟨1311232313584733896167317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 874154875723155930778211 1311232313584733896167317)
              ·
                refine ⟨61464014699284401382843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1311232313584733896167317 61464014699284401382843)
                ·
                  rfl

theorem cell19_201995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 6].length) (baseStart_201995 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_201995 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_201995 prefixEnd_201995 := by exact prefixLift 201995
  have htrace : WordTrace (prefixWord ++ tailWord_201995) baseStart_201995 baseEnd_201995 := by
    simpa [prefixWord, tailWord_201995, baseEnd_201995] using wordTrace_append hprefix tailTrace_201995
  have hstable : (prefixWord ++ tailWord_201995).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201995).length < 2 ^ (prefixWord ++ tailWord_201995).sum := by decide
  have hdescent : baseEnd_201995 < baseStart_201995 := by decide
  rcases family_descends (prefixWord ++ tailWord_201995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202033 : List Nat := [1, 2, 2, 3, 3, 8]
def baseStart_202033 : Nat := 118140960795 + 202033 * 2 ^ 59
def prefixEnd_202033 : Nat := 4983230072969 + 3 ^ 40 * 202033 * 2
def baseEnd_202033 : Nat := 6830619724767952504255

theorem tailTrace_202033 : CollatzResearch.WordTrace tailWord_202033 prefixEnd_202033 6830619724767952504255 := by
  unfold tailWord_202033
  simp only [CollatzResearch.WordTrace]
  refine ⟨7368748877076420334466753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4912499251384280222977835 7368748877076420334466753)
  ·
    refine ⟨5526561657807315250850065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7368748877076420334466753 5526561657807315250850065)
    ·
      refine ⟨4144921243355486438137549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5526561657807315250850065 4144921243355486438137549)
      ·
        refine ⟨1554345466258307414301581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4144921243355486438137549 1554345466258307414301581)
        ·
          refine ⟨582879549846865280363093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1554345466258307414301581 582879549846865280363093)
          ·
            refine ⟨6830619724767952504255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 582879549846865280363093 6830619724767952504255)
            ·
              rfl

theorem cell19_202033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 8].length) (baseStart_202033 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_202033 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_202033 prefixEnd_202033 := by exact prefixLift 202033
  have htrace : WordTrace (prefixWord ++ tailWord_202033) baseStart_202033 baseEnd_202033 := by
    simpa [prefixWord, tailWord_202033, baseEnd_202033] using wordTrace_append hprefix tailTrace_202033
  have hstable : (prefixWord ++ tailWord_202033).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202033).length < 2 ^ (prefixWord ++ tailWord_202033).sum := by decide
  have hdescent : baseEnd_202033 < baseStart_202033 := by decide
  rcases family_descends (prefixWord ++ tailWord_202033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202088 : List Nat := [2, 1, 4, 2, 3, 1, 6]
def baseStart_202088 : Nat := 118140960795 + 202088 * 2 ^ 59
def prefixEnd_202088 : Nat := 4983230072969 + 3 ^ 40 * 202088 * 2
def baseEnd_202088 : Nat := 20497437729562580438641

theorem tailTrace_202088 : CollatzResearch.WordTrace tailWord_202088 prefixEnd_202088 20497437729562580438641 := by
  unfold tailWord_202088
  simp only [CollatzResearch.WordTrace]
  refine ⟨3685377445938582363859459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4913836594584776485145945 3685377445938582363859459)
  ·
    refine ⟨5528066168907873545789189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3685377445938582363859459 5528066168907873545789189)
    ·
      refine ⟨1036512406670226289835473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5528066168907873545789189 1036512406670226289835473)
      ·
        refine ⟨777384305002669717376605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1036512406670226289835473 777384305002669717376605)
        ·
          refine ⟨291519114376001144016227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 777384305002669717376605 291519114376001144016227)
          ·
            refine ⟨437278671564001716024341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 291519114376001144016227 437278671564001716024341)
            ·
              refine ⟨20497437729562580438641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 437278671564001716024341 20497437729562580438641)
              ·
                rfl

theorem cell19_202088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 6].length) (baseStart_202088 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_202088 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_202088 prefixEnd_202088 := by exact prefixLift 202088
  have htrace : WordTrace (prefixWord ++ tailWord_202088) baseStart_202088 baseEnd_202088 := by
    simpa [prefixWord, tailWord_202088, baseEnd_202088] using wordTrace_append hprefix tailTrace_202088
  have hstable : (prefixWord ++ tailWord_202088).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202088).length < 2 ^ (prefixWord ++ tailWord_202088).sum := by decide
  have hdescent : baseEnd_202088 < baseStart_202088 := by decide
  rcases family_descends (prefixWord ++ tailWord_202088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202109 : List Nat := [1, 4, 1, 1, 2, 2, 2, 6]
def baseStart_202109 : Nat := 118140960795 + 202109 * 2 ^ 59
def prefixEnd_202109 : Nat := 4983230072969 + 3 ^ 40 * 202109 * 2
def baseEnd_202109 : Nat := 61498703170165914849199

theorem tailTrace_202109 : CollatzResearch.WordTrace tailWord_202109 prefixEnd_202109 61498703170165914849199 := by
  unfold tailWord_202109
  simp only [CollatzResearch.WordTrace]
  refine ⟨7371520824801085314233381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4914347216534056876155587 7371520824801085314233381)
  ·
    refine ⟨1382160154650203496418759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7371520824801085314233381 1382160154650203496418759)
    ·
      refine ⟨2073240231975305244628139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1382160154650203496418759 2073240231975305244628139)
      ·
        refine ⟨3109860347962957866942209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2073240231975305244628139 3109860347962957866942209)
        ·
          refine ⟨2332395260972218400206657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3109860347962957866942209 2332395260972218400206657)
          ·
            refine ⟨1749296445729163800154993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2332395260972218400206657 1749296445729163800154993)
            ·
              refine ⟨1311972334296872850116245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1749296445729163800154993 1311972334296872850116245)
              ·
                refine ⟨61498703170165914849199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1311972334296872850116245 61498703170165914849199)
                ·
                  rfl

theorem cell19_202109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 6].length) (baseStart_202109 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_202109 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_202109 prefixEnd_202109 := by exact prefixLift 202109
  have htrace : WordTrace (prefixWord ++ tailWord_202109) baseStart_202109 baseEnd_202109 := by
    simpa [prefixWord, tailWord_202109, baseEnd_202109] using wordTrace_append hprefix tailTrace_202109
  have hstable : (prefixWord ++ tailWord_202109).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202109).length < 2 ^ (prefixWord ++ tailWord_202109).sum := by decide
  have hdescent : baseEnd_202109 < baseStart_202109 := by decide
  rcases family_descends (prefixWord ++ tailWord_202109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202223 : List Nat := [1, 1, 2, 1, 4, 1, 5, 4]
def baseStart_202223 : Nat := 118140960795 + 202223 * 2 ^ 59
def prefixEnd_202223 : Nat := 4983230072969 + 3 ^ 40 * 202223 * 2
def baseEnd_202223 : Nat := 61533391641047428315555

theorem tailTrace_202223 : CollatzResearch.WordTrace tailWord_202223 prefixEnd_202223 61533391641047428315555 := by
  unfold tailWord_202223
  simp only [CollatzResearch.WordTrace]
  refine ⟨7375678746388082783883323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4917119164258721855922215 7375678746388082783883323)
  ·
    refine ⟨11063518119582124175824985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7375678746388082783883323 11063518119582124175824985)
    ·
      refine ⟨8297638589686593131868739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11063518119582124175824985 8297638589686593131868739)
      ·
        refine ⟨12446457884529889697803109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8297638589686593131868739 12446457884529889697803109)
        ·
          refine ⟨2333710853349354318338083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12446457884529889697803109 2333710853349354318338083)
          ·
            refine ⟨3500566280024031477507125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2333710853349354318338083 3500566280024031477507125)
            ·
              refine ⟨328178088752252951016293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3500566280024031477507125 328178088752252951016293)
              ·
                refine ⟨61533391641047428315555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 328178088752252951016293 61533391641047428315555)
                ·
                  rfl

theorem cell19_202223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5, 4].length) (baseStart_202223 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_202223 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_202223 prefixEnd_202223 := by exact prefixLift 202223
  have htrace : WordTrace (prefixWord ++ tailWord_202223) baseStart_202223 baseEnd_202223 := by
    simpa [prefixWord, tailWord_202223, baseEnd_202223] using wordTrace_append hprefix tailTrace_202223
  have hstable : (prefixWord ++ tailWord_202223).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202223).length < 2 ^ (prefixWord ++ tailWord_202223).sum := by decide
  have hdescent : baseEnd_202223 < baseStart_202223 := by decide
  rcases family_descends (prefixWord ++ tailWord_202223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202261 : List Nat := [1, 3, 2, 1, 3, 3, 6]
def baseStart_202261 : Nat := 118140960795 + 202261 * 2 ^ 59
def prefixEnd_202261 : Nat := 4983230072969 + 3 ^ 40 * 202261 * 2
def baseEnd_202261 : Nat := 20514984821558199823669

theorem tailTrace_202261 : CollatzResearch.WordTrace tailWord_202261 prefixEnd_202261 20514984821558199823669 := by
  unfold tailWord_202261
  simp only [CollatzResearch.WordTrace]
  refine ⟨7377064720250415273766637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4918043146833610182511091 7377064720250415273766637)
  ·
    refine ⟨2766399270093905727662489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7377064720250415273766637 2766399270093905727662489)
    ·
      refine ⟨2074799452570429295746867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2766399270093905727662489 2074799452570429295746867)
      ·
        refine ⟨3112199178855643943620301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2074799452570429295746867 3112199178855643943620301)
        ·
          refine ⟨1167074692070866478857613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3112199178855643943620301 1167074692070866478857613)
          ·
            refine ⟨437653009526574929571605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1167074692070866478857613 437653009526574929571605)
            ·
              refine ⟨20514984821558199823669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 437653009526574929571605 20514984821558199823669)
              ·
                rfl

theorem cell19_202261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 6].length) (baseStart_202261 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_202261 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_202261 prefixEnd_202261 := by exact prefixLift 202261
  have htrace : WordTrace (prefixWord ++ tailWord_202261) baseStart_202261 baseEnd_202261 := by
    simpa [prefixWord, tailWord_202261, baseEnd_202261] using wordTrace_append hprefix tailTrace_202261
  have hstable : (prefixWord ++ tailWord_202261).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202261).length < 2 ^ (prefixWord ++ tailWord_202261).sum := by decide
  have hdescent : baseEnd_202261 < baseStart_202261 := by decide
  rcases family_descends (prefixWord ++ tailWord_202261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202297 : List Nat := [1, 2, 1, 5, 1, 2, 4, 3]
def baseStart_202297 : Nat := 118140960795 + 202297 * 2 ^ 59
def prefixEnd_202297 : Nat := 4983230072969 + 3 ^ 40 * 202297 * 2
def baseEnd_202297 : Nat := 61555908718637182670909

theorem tailTrace_202297 : CollatzResearch.WordTrace tailWord_202297 prefixEnd_202297 61555908718637182670909 := by
  unfold tailWord_202297
  simp only [CollatzResearch.WordTrace]
  refine ⟨7378377748119993422077145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4918918498746662281384763 7378377748119993422077145)
  ·
    refine ⟨5533783311089995066557859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7378377748119993422077145 5533783311089995066557859)
    ·
      refine ⟨8300674966634992599836789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5533783311089995066557859 8300674966634992599836789)
      ·
        refine ⟨778188278122030556234699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8300674966634992599836789 778188278122030556234699)
        ·
          refine ⟨1167282417183045834352049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 778188278122030556234699 1167282417183045834352049)
          ·
            refine ⟨875461812887284375764037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1167282417183045834352049 875461812887284375764037)
            ·
              refine ⟨164149089916365820455757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 875461812887284375764037 164149089916365820455757)
              ·
                refine ⟨61555908718637182670909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 164149089916365820455757 61555908718637182670909)
                ·
                  rfl

theorem cell19_202297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 4, 3].length) (baseStart_202297 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_202297 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_202297 prefixEnd_202297 := by exact prefixLift 202297
  have htrace : WordTrace (prefixWord ++ tailWord_202297) baseStart_202297 baseEnd_202297 := by
    simpa [prefixWord, tailWord_202297, baseEnd_202297] using wordTrace_append hprefix tailTrace_202297
  have hstable : (prefixWord ++ tailWord_202297).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202297).length < 2 ^ (prefixWord ++ tailWord_202297).sum := by decide
  have hdescent : baseEnd_202297 < baseStart_202297 := by decide
  rcases family_descends (prefixWord ++ tailWord_202297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202337 : List Nat := [1, 2, 3, 1, 1, 3, 4, 4]
def baseStart_202337 : Nat := 118140960795 + 202337 * 2 ^ 59
def prefixEnd_202337 : Nat := 4983230072969 + 3 ^ 40 * 202337 * 2
def baseEnd_202337 : Nat := 61568080111928941781911

theorem tailTrace_202337 : CollatzResearch.WordTrace tailWord_202337 prefixEnd_202337 61568080111928941781911 := by
  unfold tailWord_202337
  simp only [CollatzResearch.WordTrace]
  refine ⟨7379836667975080253533265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4919891111983386835688843 7379836667975080253533265)
  ·
    refine ⟨5534877500981310190149949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7379836667975080253533265 5534877500981310190149949)
    ·
      refine ⟨2075579062867991321306231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5534877500981310190149949 2075579062867991321306231)
      ·
        refine ⟨3113368594301986981959347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2075579062867991321306231 3113368594301986981959347)
        ·
          refine ⟨4670052891452980472939021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3113368594301986981959347 4670052891452980472939021)
          ·
            refine ⟨1751269834294867677352133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4670052891452980472939021 1751269834294867677352133)
            ·
              refine ⟨328363093930287689503525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1751269834294867677352133 328363093930287689503525)
              ·
                refine ⟨61568080111928941781911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 328363093930287689503525 61568080111928941781911)
                ·
                  rfl

theorem cell19_202337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4, 4].length) (baseStart_202337 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_202337 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_202337 prefixEnd_202337 := by exact prefixLift 202337
  have htrace : WordTrace (prefixWord ++ tailWord_202337) baseStart_202337 baseEnd_202337 := by
    simpa [prefixWord, tailWord_202337, baseEnd_202337] using wordTrace_append hprefix tailTrace_202337
  have hstable : (prefixWord ++ tailWord_202337).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202337).length < 2 ^ (prefixWord ++ tailWord_202337).sum := by decide
  have hdescent : baseEnd_202337 < baseStart_202337 := by decide
  rcases family_descends (prefixWord ++ tailWord_202337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202388 : List Nat := [2, 4, 2, 2, 3, 1, 1, 4]
def baseStart_202388 : Nat := 118140960795 + 202388 * 2 ^ 59
def prefixEnd_202388 : Nat := 4983230072969 + 3 ^ 40 * 202388 * 2
def baseEnd_202388 : Nat := 61583598638375934648439

theorem tailTrace_202388 : CollatzResearch.WordTrace tailWord_202388 prefixEnd_202388 61583598638375934648439 := by
  unfold tailWord_202388
  simp only [CollatzResearch.WordTrace]
  refine ⟨3690848395395157981819909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4921131193860210642426545 3690848395395157981819909)
  ·
    refine ⟨692034074136592121591233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3690848395395157981819909 692034074136592121591233)
    ·
      refine ⟨519025555602444091193425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 692034074136592121591233 519025555602444091193425)
      ·
        refine ⟨389269166701833068395069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 519025555602444091193425 389269166701833068395069)
        ·
          refine ⟨145975937513187400648151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 389269166701833068395069 145975937513187400648151)
          ·
            refine ⟨218963906269781100972227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145975937513187400648151 218963906269781100972227)
            ·
              refine ⟨328445859404671651458341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 218963906269781100972227 328445859404671651458341)
              ·
                refine ⟨61583598638375934648439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 328445859404671651458341 61583598638375934648439)
                ·
                  rfl

theorem cell19_202388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 1, 4].length) (baseStart_202388 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_202388 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_202388 prefixEnd_202388 := by exact prefixLift 202388
  have htrace : WordTrace (prefixWord ++ tailWord_202388) baseStart_202388 baseEnd_202388 := by
    simpa [prefixWord, tailWord_202388, baseEnd_202388] using wordTrace_append hprefix tailTrace_202388
  have hstable : (prefixWord ++ tailWord_202388).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202388).length < 2 ^ (prefixWord ++ tailWord_202388).sum := by decide
  have hdescent : baseEnd_202388 < baseStart_202388 := by decide
  rcases family_descends (prefixWord ++ tailWord_202388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202392 : List Nat := [2, 1, 2, 4, 1, 4, 1, 4]
def baseStart_202392 : Nat := 118140960795 + 202392 * 2 ^ 59
def prefixEnd_202392 : Nat := 4983230072969 + 3 ^ 40 * 202392 * 2
def baseEnd_202392 : Nat := 61584815777705110559539

theorem tailTrace_202392 : CollatzResearch.WordTrace tailWord_202392 prefixEnd_202392 61584815777705110559539 := by
  unfold tailWord_202392
  simp only [CollatzResearch.WordTrace]
  refine ⟨3690921341387912323392715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4921228455183883097856953 3690921341387912323392715)
  ·
    refine ⟨5536382012081868485089073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3690921341387912323392715 5536382012081868485089073)
    ·
      refine ⟨4152286509061401363816805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5536382012081868485089073 4152286509061401363816805)
      ·
        refine ⟨778553720449012755715651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4152286509061401363816805 778553720449012755715651)
        ·
          refine ⟨1167830580673519133573477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 778553720449012755715651 1167830580673519133573477)
          ·
            refine ⟨218968233876284837545027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1167830580673519133573477 218968233876284837545027)
            ·
              refine ⟨328452350814427256317541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 218968233876284837545027 328452350814427256317541)
              ·
                refine ⟨61584815777705110559539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 328452350814427256317541 61584815777705110559539)
                ·
                  rfl

theorem cell19_202392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 1, 4].length) (baseStart_202392 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_202392 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_202392 prefixEnd_202392 := by exact prefixLift 202392
  have htrace : WordTrace (prefixWord ++ tailWord_202392) baseStart_202392 baseEnd_202392 := by
    simpa [prefixWord, tailWord_202392, baseEnd_202392] using wordTrace_append hprefix tailTrace_202392
  have hstable : (prefixWord ++ tailWord_202392).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202392).length < 2 ^ (prefixWord ++ tailWord_202392).sum := by decide
  have hdescent : baseEnd_202392 < baseStart_202392 := by decide
  rcases family_descends (prefixWord ++ tailWord_202392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202624 : List Nat := [2, 1, 1, 2, 1, 2, 4, 6]
def baseStart_202624 : Nat := 118140960795 + 202624 * 2 ^ 59
def prefixEnd_202624 : Nat := 4983230072969 + 3 ^ 40 * 202624 * 2
def baseEnd_202624 : Nat := 61655409858797313403351

theorem tailTrace_202624 : CollatzResearch.WordTrace tailWord_202624 prefixEnd_202624 61655409858797313403351 := by
  unfold tailWord_202624
  simp only [CollatzResearch.WordTrace]
  refine ⟨3695152208967664134615463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4926869611956885512820617 3695152208967664134615463)
  ·
    refine ⟨5542728313451496201923195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3695152208967664134615463 5542728313451496201923195)
    ·
      refine ⟨8314092470177244302884793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5542728313451496201923195 8314092470177244302884793)
      ·
        refine ⟨6235569352632933227163595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8314092470177244302884793 6235569352632933227163595)
        ·
          refine ⟨9353354028949399840745393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6235569352632933227163595 9353354028949399840745393)
          ·
            refine ⟨7015015521712049880559045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9353354028949399840745393 7015015521712049880559045)
            ·
              refine ⟨1315315410321009352604821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7015015521712049880559045 1315315410321009352604821)
              ·
                refine ⟨61655409858797313403351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1315315410321009352604821 61655409858797313403351)
                ·
                  rfl

theorem cell19_202624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 6].length) (baseStart_202624 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_202624 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_202624 prefixEnd_202624 := by exact prefixLift 202624
  have htrace : WordTrace (prefixWord ++ tailWord_202624) baseStart_202624 baseEnd_202624 := by
    simpa [prefixWord, tailWord_202624, baseEnd_202624] using wordTrace_append hprefix tailTrace_202624
  have hstable : (prefixWord ++ tailWord_202624).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202624).length < 2 ^ (prefixWord ++ tailWord_202624).sum := by decide
  have hdescent : baseEnd_202624 < baseStart_202624 := by decide
  rcases family_descends (prefixWord ++ tailWord_202624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202641 : List Nat := [1, 2, 2, 1, 1, 1, 8, 3]
def baseStart_202641 : Nat := 118140960795 + 202641 * 2 ^ 59
def prefixEnd_202641 : Nat := 4983230072969 + 3 ^ 40 * 202641 * 2
def baseEnd_202641 : Nat := 61660582700946311025527

theorem tailTrace_202641 : CollatzResearch.WordTrace tailWord_202641 prefixEnd_202641 61660582700946311025527 := by
  unfold tailWord_202641
  simp only [CollatzResearch.WordTrace]
  refine ⟨7390924458873740172599777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4927282972582493448399851 7390924458873740172599777)
  ·
    refine ⟨5543193344155305129449833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7390924458873740172599777 5543193344155305129449833)
    ·
      refine ⟨4157395008116478847087375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5543193344155305129449833 4157395008116478847087375)
      ·
        refine ⟨6236092512174718270631063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4157395008116478847087375 6236092512174718270631063)
        ·
          refine ⟨9354138768262077405946595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6236092512174718270631063 9354138768262077405946595)
          ·
            refine ⟨14031208152393116108919893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9354138768262077405946595 14031208152393116108919893)
            ·
              refine ⟨164428220535856829401405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 14031208152393116108919893 164428220535856829401405)
              ·
                refine ⟨61660582700946311025527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 164428220535856829401405 61660582700946311025527)
                ·
                  rfl

theorem cell19_202641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 8, 3].length) (baseStart_202641 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_202641 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_202641 prefixEnd_202641 := by exact prefixLift 202641
  have htrace : WordTrace (prefixWord ++ tailWord_202641) baseStart_202641 baseEnd_202641 := by
    simpa [prefixWord, tailWord_202641, baseEnd_202641] using wordTrace_append hprefix tailTrace_202641
  have hstable : (prefixWord ++ tailWord_202641).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202641).length < 2 ^ (prefixWord ++ tailWord_202641).sum := by decide
  have hdescent : baseEnd_202641 < baseStart_202641 := by decide
  rcases family_descends (prefixWord ++ tailWord_202641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202654 : List Nat := [4, 3, 1, 3, 2, 1, 5]
def baseStart_202654 : Nat := 118140960795 + 202654 * 2 ^ 59
def prefixEnd_202654 : Nat := 4983230072969 + 3 ^ 40 * 202654 * 2
def baseEnd_202654 : Nat := 20554846134588710912201

theorem tailTrace_202654 : CollatzResearch.WordTrace tailWord_202654 prefixEnd_202654 20554846134588710912201 := by
  unfold tailWord_202654
  simp only [CollatzResearch.WordTrace]
  refine ⟨923924825978330424102877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4927599071884428928548677 923924825978330424102877)
  ·
    refine ⟨346471809741873909038579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 923924825978330424102877 346471809741873909038579)
    ·
      refine ⟨519707714612810863557869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346471809741873909038579 519707714612810863557869)
      ·
        refine ⟨194890392979804073834201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 519707714612810863557869 194890392979804073834201)
        ·
          refine ⟨146167794734853055375651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194890392979804073834201 146167794734853055375651)
          ·
            refine ⟨219251692102279583063477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146167794734853055375651 219251692102279583063477)
            ·
              refine ⟨20554846134588710912201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 219251692102279583063477 20554846134588710912201)
              ·
                rfl

theorem cell19_202654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 5].length) (baseStart_202654 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_202654 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_202654 prefixEnd_202654 := by exact prefixLift 202654
  have htrace : WordTrace (prefixWord ++ tailWord_202654) baseStart_202654 baseEnd_202654 := by
    simpa [prefixWord, tailWord_202654, baseEnd_202654] using wordTrace_append hprefix tailTrace_202654
  have hstable : (prefixWord ++ tailWord_202654).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202654).length < 2 ^ (prefixWord ++ tailWord_202654).sum := by decide
  have hdescent : baseEnd_202654 < baseStart_202654 := by decide
  rcases family_descends (prefixWord ++ tailWord_202654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202658 : List Nat := [3, 3, 1, 2, 3, 2, 5]
def baseStart_202658 : Nat := 118140960795 + 202658 * 2 ^ 59
def prefixEnd_202658 : Nat := 4983230072969 + 3 ^ 40 * 202658 * 2
def baseEnd_202658 : Nat := 20555251847698436215901

theorem tailTrace_202658 : CollatzResearch.WordTrace tailWord_202658 prefixEnd_202658 20555251847698436215901 := by
  unfold tailWord_202658
  simp only [CollatzResearch.WordTrace]
  refine ⟨1847886124953038018992157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4927696333208101383979085 1847886124953038018992157)
  ·
    refine ⟨692957296857389257122059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1847886124953038018992157 692957296857389257122059)
    ·
      refine ⟨1039435945286083885683089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 692957296857389257122059 1039435945286083885683089)
      ·
        refine ⟨779576958964562914262317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1039435945286083885683089 779576958964562914262317)
        ·
          refine ⟨292341359611711092848369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 779576958964562914262317 292341359611711092848369)
          ·
            refine ⟨219256019708783319636277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 292341359611711092848369 219256019708783319636277)
            ·
              refine ⟨20555251847698436215901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 219256019708783319636277 20555251847698436215901)
              ·
                rfl

theorem cell19_202658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 5].length) (baseStart_202658 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_202658 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_202658 prefixEnd_202658 := by exact prefixLift 202658
  have htrace : WordTrace (prefixWord ++ tailWord_202658) baseStart_202658 baseEnd_202658 := by
    simpa [prefixWord, tailWord_202658, baseEnd_202658] using wordTrace_append hprefix tailTrace_202658
  have hstable : (prefixWord ++ tailWord_202658).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202658).length < 2 ^ (prefixWord ++ tailWord_202658).sum := by decide
  have hdescent : baseEnd_202658 < baseStart_202658 := by decide
  rcases family_descends (prefixWord ++ tailWord_202658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202660 : List Nat := [2, 3, 1, 2, 1, 5, 5]
def baseStart_202660 : Nat := 118140960795 + 202660 * 2 ^ 59
def prefixEnd_202660 : Nat := 4983230072969 + 3 ^ 40 * 202660 * 2
def baseEnd_202660 : Nat := 20555454704253298867751

theorem tailTrace_202660 : CollatzResearch.WordTrace tailWord_202660 prefixEnd_202660 20555454704253298867751 := by
  unfold tailWord_202660
  simp only [CollatzResearch.WordTrace]
  refine ⟨3695808722902453208770717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4927744963869937611694289 3695808722902453208770717)
  ·
    refine ⟨1385928271088419953289019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3695808722902453208770717 1385928271088419953289019)
    ·
      refine ⟨2078892406632629929933529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1385928271088419953289019 2078892406632629929933529)
      ·
        refine ⟨1559169304974472447450147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2078892406632629929933529 1559169304974472447450147)
        ·
          refine ⟨2338753957461708671175221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1559169304974472447450147 2338753957461708671175221)
          ·
            refine ⟨219258183512035187922677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2338753957461708671175221 219258183512035187922677)
            ·
              refine ⟨20555454704253298867751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 219258183512035187922677 20555454704253298867751)
              ·
                rfl

theorem cell19_202660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 5].length) (baseStart_202660 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_202660 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_202660 prefixEnd_202660 := by exact prefixLift 202660
  have htrace : WordTrace (prefixWord ++ tailWord_202660) baseStart_202660 baseEnd_202660 := by
    simpa [prefixWord, tailWord_202660, baseEnd_202660] using wordTrace_append hprefix tailTrace_202660
  have hstable : (prefixWord ++ tailWord_202660).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202660).length < 2 ^ (prefixWord ++ tailWord_202660).sum := by decide
  have hdescent : baseEnd_202660 < baseStart_202660 := by decide
  rcases family_descends (prefixWord ++ tailWord_202660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202717 : List Nat := [1, 4, 3, 1, 3, 7]
def baseStart_202717 : Nat := 118140960795 + 202717 * 2 ^ 59
def prefixEnd_202717 : Nat := 4983230072969 + 3 ^ 40 * 202717 * 2
def baseEnd_202717 : Nat := 6853745372022294815159

theorem tailTrace_202717 : CollatzResearch.WordTrace tailWord_202717 prefixEnd_202717 6853745372022294815159 := by
  unfold tailWord_202717
  simp only [CollatzResearch.WordTrace]
  refine ⟨7393696406598405152366405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4929130937732270101577603 7393696406598405152366405)
  ·
    refine ⟨1386318076237200966068701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7393696406598405152366405 1386318076237200966068701)
    ·
      refine ⟨519869278588950362275763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1386318076237200966068701 519869278588950362275763)
      ·
        refine ⟨779803917883425543413645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 519869278588950362275763 779803917883425543413645)
        ·
          refine ⟨292426469206284578780117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 779803917883425543413645 292426469206284578780117)
          ·
            refine ⟨6853745372022294815159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 292426469206284578780117 6853745372022294815159)
            ·
              rfl

theorem cell19_202717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 7].length) (baseStart_202717 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_202717 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_202717 prefixEnd_202717 := by exact prefixLift 202717
  have htrace : WordTrace (prefixWord ++ tailWord_202717) baseStart_202717 baseEnd_202717 := by
    simpa [prefixWord, tailWord_202717, baseEnd_202717] using wordTrace_append hprefix tailTrace_202717
  have hstable : (prefixWord ++ tailWord_202717).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202717).length < 2 ^ (prefixWord ++ tailWord_202717).sum := by decide
  have hdescent : baseEnd_202717 < baseStart_202717 := by decide
  rcases family_descends (prefixWord ++ tailWord_202717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202719 : List Nat := [1, 1, 2, 3, 4, 8]
def baseStart_202719 : Nat := 118140960795 + 202719 * 2 ^ 59
def prefixEnd_202719 : Nat := 4983230072969 + 3 ^ 40 * 202719 * 2
def baseEnd_202719 : Nat := 6853812990873915699109

theorem tailTrace_202719 : CollatzResearch.WordTrace tailWord_202719 prefixEnd_202719 6853812990873915699109 := by
  unfold tailWord_202719
  simp only [CollatzResearch.WordTrace]
  refine ⟨7393769352591159493939211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4929179568394106329292807 7393769352591159493939211)
  ·
    refine ⟨11090654028886739240908817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7393769352591159493939211 11090654028886739240908817)
    ·
      refine ⟨8317990521665054430681613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11090654028886739240908817 8317990521665054430681613)
      ·
        refine ⟨3119246445624395411505605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8317990521665054430681613 3119246445624395411505605)
        ·
          refine ⟨584858708554574139657301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3119246445624395411505605 584858708554574139657301)
          ·
            refine ⟨6853812990873915699109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 584858708554574139657301 6853812990873915699109)
            ·
              rfl

theorem cell19_202719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 8].length) (baseStart_202719 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_202719 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_202719 prefixEnd_202719 := by exact prefixLift 202719
  have htrace : WordTrace (prefixWord ++ tailWord_202719) baseStart_202719 baseEnd_202719 := by
    simpa [prefixWord, tailWord_202719, baseEnd_202719] using wordTrace_append hprefix tailTrace_202719
  have hstable : (prefixWord ++ tailWord_202719).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202719).length < 2 ^ (prefixWord ++ tailWord_202719).sum := by decide
  have hdescent : baseEnd_202719 < baseStart_202719 := by decide
  rcases family_descends (prefixWord ++ tailWord_202719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202734 : List Nat := [4, 1, 2, 1, 3, 3, 1, 4]
def baseStart_202734 : Nat := 118140960795 + 202734 * 2 ^ 59
def prefixEnd_202734 : Nat := 4983230072969 + 3 ^ 40 * 202734 * 2
def baseEnd_202734 : Nat := 61688881190349650958607

theorem tailTrace_202734 : CollatzResearch.WordTrace tailWord_202734 prefixEnd_202734 61688881190349650958607 := by
  unfold tailWord_202734
  simp only [CollatzResearch.WordTrace]
  refine ⟨924289555942102131966907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4929544298357878037156837 924289555942102131966907)
  ·
    refine ⟨1386434333913153197950361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 924289555942102131966907 1386434333913153197950361)
    ·
      refine ⟨1039825750434864898462771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1386434333913153197950361 1039825750434864898462771)
      ·
        refine ⟨1559738625652297347694157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1039825750434864898462771 1559738625652297347694157)
        ·
          refine ⟨584901984619611505385309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1559738625652297347694157 584901984619611505385309)
          ·
            refine ⟨219338244232354314519491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 584901984619611505385309 219338244232354314519491)
            ·
              refine ⟨329007366348531471779237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 219338244232354314519491 329007366348531471779237)
              ·
                refine ⟨61688881190349650958607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 329007366348531471779237 61688881190349650958607)
                ·
                  rfl

theorem cell19_202734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 1, 4].length) (baseStart_202734 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_202734 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_202734 prefixEnd_202734 := by exact prefixLift 202734
  have htrace : WordTrace (prefixWord ++ tailWord_202734) baseStart_202734 baseEnd_202734 := by
    simpa [prefixWord, tailWord_202734, baseEnd_202734] using wordTrace_append hprefix tailTrace_202734
  have hstable : (prefixWord ++ tailWord_202734).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202734).length < 2 ^ (prefixWord ++ tailWord_202734).sum := by decide
  have hdescent : baseEnd_202734 < baseStart_202734 := by decide
  rcases family_descends (prefixWord ++ tailWord_202734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202776 : List Nat := [2, 1, 2, 3, 2, 1, 8]
def baseStart_202776 : Nat := 118140960795 + 202776 * 2 ^ 59
def prefixEnd_202776 : Nat := 4983230072969 + 3 ^ 40 * 202776 * 2
def baseEnd_202776 : Nat := 20567220384435332675053

theorem tailTrace_202776 : CollatzResearch.WordTrace tailWord_202776 prefixEnd_202776 20567220384435332675053 := by
  unfold tailWord_202776
  simp only [CollatzResearch.WordTrace]
  refine ⟨3697924156692329114382091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4930565542256438819176121 3697924156692329114382091)
  ·
    refine ⟨5546886235038493671573137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3697924156692329114382091 5546886235038493671573137)
    ·
      refine ⟨4160164676278870253679853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5546886235038493671573137 4160164676278870253679853)
      ·
        refine ⟨1560061753604576345129945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4160164676278870253679853 1560061753604576345129945)
        ·
          refine ⟨1170046315203432258847459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1560061753604576345129945 1170046315203432258847459)
          ·
            refine ⟨1755069472805148388271189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1170046315203432258847459 1755069472805148388271189)
            ·
              refine ⟨20567220384435332675053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1755069472805148388271189 20567220384435332675053)
              ·
                rfl

theorem cell19_202776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 8].length) (baseStart_202776 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_202776 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_202776 prefixEnd_202776 := by exact prefixLift 202776
  have htrace : WordTrace (prefixWord ++ tailWord_202776) baseStart_202776 baseEnd_202776 := by
    simpa [prefixWord, tailWord_202776, baseEnd_202776] using wordTrace_append hprefix tailTrace_202776
  have hstable : (prefixWord ++ tailWord_202776).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202776).length < 2 ^ (prefixWord ++ tailWord_202776).sum := by decide
  have hdescent : baseEnd_202776 < baseStart_202776 := by decide
  rcases family_descends (prefixWord ++ tailWord_202776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202808 : List Nat := [2, 1, 2, 1, 7, 1, 2, 3]
def baseStart_202808 : Nat := 118140960795 + 202808 * 2 ^ 59
def prefixEnd_202808 : Nat := 4983230072969 + 3 ^ 40 * 202808 * 2
def baseEnd_202808 : Nat := 61711398267939405313961

theorem tailTrace_202808 : CollatzResearch.WordTrace tailWord_202808 prefixEnd_202808 61711398267939405313961 := by
  unfold tailWord_202808
  simp only [CollatzResearch.WordTrace]
  refine ⟨3698507724634363846964539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4931343632845818462619385 3698507724634363846964539)
  ·
    refine ⟨5547761586951545770446809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3698507724634363846964539 5547761586951545770446809)
    ·
      refine ⟨4160821190213659327835107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5547761586951545770446809 4160821190213659327835107)
      ·
        refine ⟨6241231785320488991752661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4160821190213659327835107 6241231785320488991752661)
        ·
          refine ⟨146278869968448960744203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 6241231785320488991752661 146278869968448960744203)
          ·
            refine ⟨219418304952673441116305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146278869968448960744203 219418304952673441116305)
            ·
              refine ⟨164563728714505080837229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 219418304952673441116305 164563728714505080837229)
              ·
                refine ⟨61711398267939405313961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 164563728714505080837229 61711398267939405313961)
                ·
                  rfl

theorem cell19_202808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 2, 3].length) (baseStart_202808 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_202808 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_202808 prefixEnd_202808 := by exact prefixLift 202808
  have htrace : WordTrace (prefixWord ++ tailWord_202808) baseStart_202808 baseEnd_202808 := by
    simpa [prefixWord, tailWord_202808, baseEnd_202808] using wordTrace_append hprefix tailTrace_202808
  have hstable : (prefixWord ++ tailWord_202808).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202808).length < 2 ^ (prefixWord ++ tailWord_202808).sum := by decide
  have hdescent : baseEnd_202808 < baseStart_202808 := by decide
  rcases family_descends (prefixWord ++ tailWord_202808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202852 : List Nat := [2, 3, 1, 1, 2, 1, 3, 6]
def baseStart_202852 : Nat := 118140960795 + 202852 * 2 ^ 59
def prefixEnd_202852 : Nat := 4983230072969 + 3 ^ 40 * 202852 * 2
def baseEnd_202852 : Nat := 61724786800560340336063

theorem tailTrace_202852 : CollatzResearch.WordTrace tailWord_202852 prefixEnd_202852 61724786800560340336063 := by
  unfold tailWord_202852
  simp only [CollatzResearch.WordTrace]
  refine ⟨3699310130554661604265405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4932413507406215472353873 3699310130554661604265405)
  ·
    refine ⟨1387241298957998101599527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3699310130554661604265405 1387241298957998101599527)
    ·
      refine ⟨2080861948436997152399291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1387241298957998101599527 2080861948436997152399291)
      ·
        refine ⟨3121292922655495728598937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2080861948436997152399291 3121292922655495728598937)
        ·
          refine ⟨2340969691991621796449203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3121292922655495728598937 2340969691991621796449203)
          ·
            refine ⟨3511454537987432694673805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2340969691991621796449203 3511454537987432694673805)
            ·
              refine ⟨1316795451745287260502677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3511454537987432694673805 1316795451745287260502677)
              ·
                refine ⟨61724786800560340336063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1316795451745287260502677 61724786800560340336063)
                ·
                  rfl

theorem cell19_202852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 6].length) (baseStart_202852 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_202852 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_202852 prefixEnd_202852 := by exact prefixLift 202852
  have htrace : WordTrace (prefixWord ++ tailWord_202852) baseStart_202852 baseEnd_202852 := by
    simpa [prefixWord, tailWord_202852, baseEnd_202852] using wordTrace_append hprefix tailTrace_202852
  have hstable : (prefixWord ++ tailWord_202852).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202852).length < 2 ^ (prefixWord ++ tailWord_202852).sum := by decide
  have hdescent : baseEnd_202852 < baseStart_202852 := by decide
  rcases family_descends (prefixWord ++ tailWord_202852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202871 : List Nat := [1, 1, 3, 1, 1, 5, 2, 5]
def baseStart_202871 : Nat := 118140960795 + 202871 * 2 ^ 59
def prefixEnd_202871 : Nat := 4983230072969 + 3 ^ 40 * 202871 * 2
def baseEnd_202871 : Nat := 61730568212373925913789

theorem tailTrace_202871 : CollatzResearch.WordTrace tailWord_202871 prefixEnd_202871 61730568212373925913789 := by
  unfold tailWord_202871
  simp only [CollatzResearch.WordTrace]
  refine ⟨7399313248040489453472467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4932875498693659635648311 7399313248040489453472467)
  ·
    refine ⟨11098969872060734180208701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7399313248040489453472467 11098969872060734180208701)
    ·
      refine ⟨4162113702022775317578263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11098969872060734180208701 4162113702022775317578263)
      ·
        refine ⟨6243170553034162976367395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4162113702022775317578263 6243170553034162976367395)
        ·
          refine ⟨9364755829551244464551093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6243170553034162976367395 9364755829551244464551093)
          ·
            refine ⟨877945859020429168551665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9364755829551244464551093 877945859020429168551665)
            ·
              refine ⟨658459394265321876413749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 877945859020429168551665 658459394265321876413749)
              ·
                refine ⟨61730568212373925913789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 658459394265321876413749 61730568212373925913789)
                ·
                  rfl

theorem cell19_202871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 5].length) (baseStart_202871 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_202871 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_202871 prefixEnd_202871 := by exact prefixLift 202871
  have htrace : WordTrace (prefixWord ++ tailWord_202871) baseStart_202871 baseEnd_202871 := by
    simpa [prefixWord, tailWord_202871, baseEnd_202871] using wordTrace_append hprefix tailTrace_202871
  have hstable : (prefixWord ++ tailWord_202871).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202871).length < 2 ^ (prefixWord ++ tailWord_202871).sum := by decide
  have hdescent : baseEnd_202871 < baseStart_202871 := by decide
  rcases family_descends (prefixWord ++ tailWord_202871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202890 : List Nat := [3, 1, 2, 3, 1, 9]
def baseStart_202890 : Nat := 118140960795 + 202890 * 2 ^ 59
def prefixEnd_202890 : Nat := 4983230072969 + 3 ^ 40 * 202890 * 2
def baseEnd_202890 : Nat := 6859594402687501276835

theorem tailTrace_202890 : CollatzResearch.WordTrace tailWord_202890 prefixEnd_202890 6859594402687501276835 := by
  unfold tailWord_202890
  simp only [CollatzResearch.WordTrace]
  refine ⟨1850001558742913924603531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4933337489981103798942749 1850001558742913924603531)
  ·
    refine ⟨2775002338114370886905297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1850001558742913924603531 2775002338114370886905297)
    ·
      refine ⟨2081251753585778165178973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2775002338114370886905297 2081251753585778165178973)
      ·
        refine ⟨780469407594666811942115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2081251753585778165178973 780469407594666811942115)
        ·
          refine ⟨1170704111392000217913173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 780469407594666811942115 1170704111392000217913173)
          ·
            refine ⟨6859594402687501276835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1170704111392000217913173 6859594402687501276835)
            ·
              rfl

theorem cell19_202890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 9].length) (baseStart_202890 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_202890 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_202890 prefixEnd_202890 := by exact prefixLift 202890
  have htrace : WordTrace (prefixWord ++ tailWord_202890) baseStart_202890 baseEnd_202890 := by
    simpa [prefixWord, tailWord_202890, baseEnd_202890] using wordTrace_append hprefix tailTrace_202890
  have hstable : (prefixWord ++ tailWord_202890).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202890).length < 2 ^ (prefixWord ++ tailWord_202890).sum := by decide
  have hdescent : baseEnd_202890 < baseStart_202890 := by decide
  rcases family_descends (prefixWord ++ tailWord_202890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202922 : List Nat := [3, 1, 5, 1, 2, 1, 3, 3]
def baseStart_202922 : Nat := 118140960795 + 202922 * 2 ^ 59
def prefixEnd_202922 : Nat := 4983230072969 + 3 ^ 40 * 202922 * 2
def baseEnd_202922 : Nat := 61746086738820918780317

theorem tailTrace_202922 : CollatzResearch.WordTrace tailWord_202922 prefixEnd_202922 61746086738820918780317 := by
  unfold tailWord_202922
  simp only [CollatzResearch.WordTrace]
  refine ⟨1850293342713931290894755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4934115580570483442386013 1850293342713931290894755)
  ·
    refine ⟨2775440014070896936342133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1850293342713931290894755 2775440014070896936342133)
    ·
      refine ⟨260197501319146587782075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2775440014070896936342133 260197501319146587782075)
      ·
        refine ⟨390296251978719881673113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260197501319146587782075 390296251978719881673113)
        ·
          refine ⟨292722188984039911254835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 390296251978719881673113 292722188984039911254835)
          ·
            refine ⟨439083283476059866882253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 292722188984039911254835 439083283476059866882253)
            ·
              refine ⟨164656231303522450080845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 439083283476059866882253 164656231303522450080845)
              ·
                refine ⟨61746086738820918780317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 164656231303522450080845 61746086738820918780317)
                ·
                  rfl

theorem cell19_202922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 3, 3].length) (baseStart_202922 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_202922 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_202922 prefixEnd_202922 := by exact prefixLift 202922
  have htrace : WordTrace (prefixWord ++ tailWord_202922) baseStart_202922 baseEnd_202922 := by
    simpa [prefixWord, tailWord_202922, baseEnd_202922] using wordTrace_append hprefix tailTrace_202922
  have hstable : (prefixWord ++ tailWord_202922).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202922).length < 2 ^ (prefixWord ++ tailWord_202922).sum := by decide
  have hdescent : baseEnd_202922 < baseStart_202922 := by decide
  rcases family_descends (prefixWord ++ tailWord_202922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202979 : List Nat := [1, 1, 1, 8, 1, 2, 2, 3]
def baseStart_202979 : Nat := 118140960795 + 202979 * 2 ^ 59
def prefixEnd_202979 : Nat := 4983230072969 + 3 ^ 40 * 202979 * 2
def baseEnd_202979 : Nat := 61763430974261675513495

theorem tailTrace_202979 : CollatzResearch.WordTrace tailWord_202979 prefixEnd_202979 61763430974261675513495 := by
  unfold tailWord_202979
  simp only [CollatzResearch.WordTrace]
  refine ⟨7403252331649223898403991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4935501554432815932269327 7403252331649223898403991)
  ·
    refine ⟨11104878497473835847605987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7403252331649223898403991 11104878497473835847605987)
    ·
      refine ⟨16657317746210753771408981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11104878497473835847605987 16657317746210753771408981)
      ·
        refine ⟨195202942338407270758699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 16657317746210753771408981 195202942338407270758699)
        ·
          refine ⟨292804413507610906138049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195202942338407270758699 292804413507610906138049)
          ·
            refine ⟨219603310130708179603537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 292804413507610906138049 219603310130708179603537)
            ·
              refine ⟨164702482598031134702653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 219603310130708179603537 164702482598031134702653)
              ·
                refine ⟨61763430974261675513495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 164702482598031134702653 61763430974261675513495)
                ·
                  rfl

theorem cell19_202979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 2, 3].length) (baseStart_202979 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_202979 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_202979 prefixEnd_202979 := by exact prefixLift 202979
  have htrace : WordTrace (prefixWord ++ tailWord_202979) baseStart_202979 baseEnd_202979 := by
    simpa [prefixWord, tailWord_202979, baseEnd_202979] using wordTrace_append hprefix tailTrace_202979
  have hstable : (prefixWord ++ tailWord_202979).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202979).length < 2 ^ (prefixWord ++ tailWord_202979).sum := by decide
  have hdescent : baseEnd_202979 < baseStart_202979 := by decide
  rcases family_descends (prefixWord ++ tailWord_202979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202981 : List Nat := [1, 3, 1, 4, 2, 3, 2, 3]
def baseStart_202981 : Nat := 118140960795 + 202981 * 2 ^ 59
def prefixEnd_202981 : Nat := 4983230072969 + 3 ^ 40 * 202981 * 2
def baseEnd_202981 : Nat := 61764039543926263469045

theorem tailTrace_202981 : CollatzResearch.WordTrace tailWord_202981 prefixEnd_202981 61764039543926263469045 := by
  unfold tailWord_202981
  simp only [CollatzResearch.WordTrace]
  refine ⟨7403325277641978239976797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4935550185094652159984531 7403325277641978239976797)
  ·
    refine ⟨2776246979115741839991299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7403325277641978239976797 2776246979115741839991299)
    ·
      refine ⟨4164370468673612759986949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2776246979115741839991299 4164370468673612759986949)
      ·
        refine ⟨780819462876302392497553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4164370468673612759986949 780819462876302392497553)
        ·
          refine ⟨585614597157226794373165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 780819462876302392497553 585614597157226794373165)
          ·
            refine ⟨219605473933960047889937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 585614597157226794373165 219605473933960047889937)
            ·
              refine ⟨164704105450470035917453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 219605473933960047889937 164704105450470035917453)
              ·
                refine ⟨61764039543926263469045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 164704105450470035917453 61764039543926263469045)
                ·
                  rfl

theorem cell19_202981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 2, 3].length) (baseStart_202981 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_202981 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_202981 prefixEnd_202981 := by exact prefixLift 202981
  have htrace : WordTrace (prefixWord ++ tailWord_202981) baseStart_202981 baseEnd_202981 := by
    simpa [prefixWord, tailWord_202981, baseEnd_202981] using wordTrace_append hprefix tailTrace_202981
  have hstable : (prefixWord ++ tailWord_202981).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202981).length < 2 ^ (prefixWord ++ tailWord_202981).sum := by decide
  have hdescent : baseEnd_202981 < baseStart_202981 := by decide
  rcases family_descends (prefixWord ++ tailWord_202981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202983 : List Nat := [1, 1, 5, 3, 1, 2, 1, 5]
def baseStart_202983 : Nat := 118140960795 + 202983 * 2 ^ 59
def prefixEnd_202983 : Nat := 4983230072969 + 3 ^ 40 * 202983 * 2
def baseEnd_202983 : Nat := 61764648113590851424595

theorem tailTrace_202983 : CollatzResearch.WordTrace tailWord_202983 prefixEnd_202983 61764648113590851424595 := by
  unfold tailWord_202983
  simp only [CollatzResearch.WordTrace]
  refine ⟨7403398223634732581549603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4935598815756488387699735 7403398223634732581549603)
  ·
    refine ⟨11105097335452098872324405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7403398223634732581549603 11105097335452098872324405)
    ·
      refine ⟨1041102875198634269280413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11105097335452098872324405 1041102875198634269280413)
      ·
        refine ⟨390413578199487850980155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1041102875198634269280413 390413578199487850980155)
        ·
          refine ⟨585620367299231776470233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 390413578199487850980155 585620367299231776470233)
          ·
            refine ⟨439215275474423832352675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 585620367299231776470233 439215275474423832352675)
            ·
              refine ⟨658822913211635748529013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 439215275474423832352675 658822913211635748529013)
              ·
                refine ⟨61764648113590851424595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 658822913211635748529013 61764648113590851424595)
                ·
                  rfl

theorem cell19_202983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 5].length) (baseStart_202983 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_202983 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_202983 prefixEnd_202983 := by exact prefixLift 202983
  have htrace : WordTrace (prefixWord ++ tailWord_202983) baseStart_202983 baseEnd_202983 := by
    simpa [prefixWord, tailWord_202983, baseEnd_202983] using wordTrace_append hprefix tailTrace_202983
  have hstable : (prefixWord ++ tailWord_202983).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202983).length < 2 ^ (prefixWord ++ tailWord_202983).sum := by decide
  have hdescent : baseEnd_202983 < baseStart_202983 := by decide
  rcases family_descends (prefixWord ++ tailWord_202983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203004 : List Nat := [2, 2, 2, 1, 4, 1, 7]
def baseStart_203004 : Nat := 118140960795 + 203004 * 2 ^ 59
def prefixEnd_203004 : Nat := 4983230072969 + 3 ^ 40 * 203004 * 2
def baseEnd_203004 : Nat := 20590346031689674985957

theorem tailTrace_203004 : CollatzResearch.WordTrace tailWord_203004 prefixEnd_203004 20590346031689674985957 := by
  unfold tailWord_203004
  simp only [CollatzResearch.WordTrace]
  refine ⟨3702082078279326584032033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4936109437705768778709377 3702082078279326584032033)
  ·
    refine ⟨2776561558709494938024025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3702082078279326584032033 2776561558709494938024025)
    ·
      refine ⟨2082421169032121203518019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2776561558709494938024025 2082421169032121203518019)
      ·
        refine ⟨3123631753548181805277029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2082421169032121203518019 3123631753548181805277029)
        ·
          refine ⟨585680953790284088489443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3123631753548181805277029 585680953790284088489443)
          ·
            refine ⟨878521430685426132734165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 585680953790284088489443 878521430685426132734165)
            ·
              refine ⟨20590346031689674985957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 878521430685426132734165 20590346031689674985957)
              ·
                rfl

theorem cell19_203004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 7].length) (baseStart_203004 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_203004 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_203004 prefixEnd_203004 := by exact prefixLift 203004
  have htrace : WordTrace (prefixWord ++ tailWord_203004) baseStart_203004 baseEnd_203004 := by
    simpa [prefixWord, tailWord_203004, baseEnd_203004] using wordTrace_append hprefix tailTrace_203004
  have hstable : (prefixWord ++ tailWord_203004).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203004).length < 2 ^ (prefixWord ++ tailWord_203004).sum := by decide
  have hdescent : baseEnd_203004 < baseStart_203004 := by decide
  rcases family_descends (prefixWord ++ tailWord_203004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203038 : List Nat := [4, 3, 2, 1, 1, 1, 2, 5]
def baseStart_203038 : Nat := 118140960795 + 203038 * 2 ^ 59
def prefixEnd_203038 : Nat := 4983230072969 + 3 ^ 40 * 203038 * 2
def baseEnd_203038 : Nat := 61781383779367020202223

theorem tailTrace_203038 : CollatzResearch.WordTrace tailWord_203038 prefixEnd_203038 61781383779367020202223 := by
  unfold tailWord_203038
  simp only [CollatzResearch.WordTrace]
  refine ⟨925675529804434621850221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4936936158956984649867845 925675529804434621850221)
  ·
    refine ⟨347128323676662983193833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 925675529804434621850221 347128323676662983193833)
    ·
      refine ⟨260346242757497237395375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 347128323676662983193833 260346242757497237395375)
      ·
        refine ⟨390519364136245856093063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260346242757497237395375 390519364136245856093063)
        ·
          refine ⟨585779046204368784139595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 390519364136245856093063 585779046204368784139595)
          ·
            refine ⟨878668569306553176209393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 585779046204368784139595 878668569306553176209393)
            ·
              refine ⟨659001426979914882157045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 878668569306553176209393 659001426979914882157045)
              ·
                refine ⟨61781383779367020202223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 659001426979914882157045 61781383779367020202223)
                ·
                  rfl

theorem cell19_203038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 5].length) (baseStart_203038 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_203038 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_203038 prefixEnd_203038 := by exact prefixLift 203038
  have htrace : WordTrace (prefixWord ++ tailWord_203038) baseStart_203038 baseEnd_203038 := by
    simpa [prefixWord, tailWord_203038, baseEnd_203038] using wordTrace_append hprefix tailTrace_203038
  have hstable : (prefixWord ++ tailWord_203038).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203038).length < 2 ^ (prefixWord ++ tailWord_203038).sum := by decide
  have hdescent : baseEnd_203038 < baseStart_203038 := by decide
  rcases family_descends (prefixWord ++ tailWord_203038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203080 : List Nat := [2, 1, 3, 1, 1, 2, 5, 4]
def baseStart_203080 : Nat := 118140960795 + 203080 * 2 ^ 59
def prefixEnd_203080 : Nat := 4983230072969 + 3 ^ 40 * 203080 * 2
def baseEnd_203080 : Nat := 61794163742323367268775

theorem tailTrace_203080 : CollatzResearch.WordTrace tailWord_203080 prefixEnd_203080 61794163742323367268775 := by
  unfold tailWord_203080
  simp only [CollatzResearch.WordTrace]
  refine ⟨3703468052141659073915347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4937957402855545431887129 3703468052141659073915347)
  ·
    refine ⟨5555202078212488610873021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3703468052141659073915347 5555202078212488610873021)
    ·
      refine ⟨2083200779329683229077383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5555202078212488610873021 2083200779329683229077383)
      ·
        refine ⟨3124801168994524843616075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2083200779329683229077383 3124801168994524843616075)
        ·
          refine ⟨4687201753491787265424113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3124801168994524843616075 4687201753491787265424113)
          ·
            refine ⟨3515401315118840449068085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4687201753491787265424113 3515401315118840449068085)
            ·
              refine ⟨329568873292391292100133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3515401315118840449068085 329568873292391292100133)
              ·
                refine ⟨61794163742323367268775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 329568873292391292100133 61794163742323367268775)
                ·
                  rfl

theorem cell19_203080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5, 4].length) (baseStart_203080 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_203080 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_203080 prefixEnd_203080 := by exact prefixLift 203080
  have htrace : WordTrace (prefixWord ++ tailWord_203080) baseStart_203080 baseEnd_203080 := by
    simpa [prefixWord, tailWord_203080, baseEnd_203080] using wordTrace_append hprefix tailTrace_203080
  have hstable : (prefixWord ++ tailWord_203080).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203080).length < 2 ^ (prefixWord ++ tailWord_203080).sum := by decide
  have hdescent : baseEnd_203080 < baseStart_203080 := by decide
  rcases family_descends (prefixWord ++ tailWord_203080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203175 : List Nat := [1, 1, 6, 1, 1, 2, 7]
def baseStart_203175 : Nat := 118140960795 + 203175 * 2 ^ 59
def prefixEnd_203175 : Nat := 4983230072969 + 3 ^ 40 * 203175 * 2
def baseEnd_203175 : Nat := 20607690267130431719135

theorem tailTrace_203175 : CollatzResearch.WordTrace tailWord_203175 prefixEnd_203175 20607690267130431719135 := by
  unfold tailWord_203175
  simp only [CollatzResearch.WordTrace]
  refine ⟨7410401038939149372538979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4940267359292766248359319 7410401038939149372538979)
  ·
    refine ⟨11115601558408724058808469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7410401038939149372538979 11115601558408724058808469)
    ·
      refine ⟨521043823050408940256647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 11115601558408724058808469 521043823050408940256647)
      ·
        refine ⟨781565734575613410384971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 521043823050408940256647 781565734575613410384971)
        ·
          refine ⟨1172348601863420115577457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 781565734575613410384971 1172348601863420115577457)
          ·
            refine ⟨879261451397565086683093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1172348601863420115577457 879261451397565086683093)
            ·
              refine ⟨20607690267130431719135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 879261451397565086683093 20607690267130431719135)
              ·
                rfl

theorem cell19_203175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 7].length) (baseStart_203175 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_203175 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_203175 prefixEnd_203175 := by exact prefixLift 203175
  have htrace : WordTrace (prefixWord ++ tailWord_203175) baseStart_203175 baseEnd_203175 := by
    simpa [prefixWord, tailWord_203175, baseEnd_203175] using wordTrace_append hprefix tailTrace_203175
  have hstable : (prefixWord ++ tailWord_203175).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203175).length < 2 ^ (prefixWord ++ tailWord_203175).sum := by decide
  have hdescent : baseEnd_203175 < baseStart_203175 := by decide
  rcases family_descends (prefixWord ++ tailWord_203175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203188 : List Nat := [2, 5, 2, 2, 1, 1, 2, 4]
def baseStart_203188 : Nat := 118140960795 + 203188 * 2 ^ 59
def prefixEnd_203188 : Nat := 4983230072969 + 3 ^ 40 * 203188 * 2
def baseEnd_203188 : Nat := 61827026504211116868481

theorem tailTrace_203188 : CollatzResearch.WordTrace tailWord_203188 prefixEnd_203188 61827026504211116868481 := by
  unfold tailWord_203188
  simp only [CollatzResearch.WordTrace]
  refine ⟨3705437593946026296381109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4940583458594701728508145 3705437593946026296381109)
  ·
    refine ⟨347384774432439965285729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3705437593946026296381109 347384774432439965285729)
    ·
      refine ⟨260538580824329973964297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 347384774432439965285729 260538580824329973964297)
      ·
        refine ⟨195403935618247480473223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 260538580824329973964297 195403935618247480473223)
        ·
          refine ⟨293105903427371220709835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195403935618247480473223 293105903427371220709835)
          ·
            refine ⟨439658855141056831064753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 293105903427371220709835 439658855141056831064753)
            ·
              refine ⟨329744141355792623298565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 439658855141056831064753 329744141355792623298565)
              ·
                refine ⟨61827026504211116868481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 329744141355792623298565 61827026504211116868481)
                ·
                  rfl

theorem cell19_203188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 2, 4].length) (baseStart_203188 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_203188 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_203188 prefixEnd_203188 := by exact prefixLift 203188
  have htrace : WordTrace (prefixWord ++ tailWord_203188) baseStart_203188 baseEnd_203188 := by
    simpa [prefixWord, tailWord_203188, baseEnd_203188] using wordTrace_append hprefix tailTrace_203188
  have hstable : (prefixWord ++ tailWord_203188).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203188).length < 2 ^ (prefixWord ++ tailWord_203188).sum := by decide
  have hdescent : baseEnd_203188 < baseStart_203188 := by decide
  rcases family_descends (prefixWord ++ tailWord_203188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203287 : List Nat := [1, 1, 3, 6, 1, 1, 6]
def baseStart_203287 : Nat := 118140960795 + 203287 * 2 ^ 59
def prefixEnd_203287 : Nat := 4983230072969 + 3 ^ 40 * 203287 * 2
def baseEnd_203287 : Nat := 20619050234202740222737

theorem tailTrace_203287 : CollatzResearch.WordTrace tailWord_203287 prefixEnd_203287 20619050234202740222737 := by
  unfold tailWord_203287
  simp only [CollatzResearch.WordTrace]
  refine ⟨7414486014533392500616115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4942990676355595000410743 7414486014533392500616115)
  ·
    refine ⟨11121729021800088750924173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7414486014533392500616115 11121729021800088750924173)
    ·
      refine ⟨4170648383175033281596565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11121729021800088750924173 4170648383175033281596565)
      ·
        refine ⟨195499142961329685074839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 4170648383175033281596565 195499142961329685074839)
        ·
          refine ⟨293248714441994527612259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195499142961329685074839 293248714441994527612259)
          ·
            refine ⟨439873071662991791418389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 293248714441994527612259 439873071662991791418389)
            ·
              refine ⟨20619050234202740222737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 439873071662991791418389 20619050234202740222737)
              ·
                rfl

theorem cell19_203287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 6].length) (baseStart_203287 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_203287 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_203287 prefixEnd_203287 := by exact prefixLift 203287
  have htrace : WordTrace (prefixWord ++ tailWord_203287) baseStart_203287 baseEnd_203287 := by
    simpa [prefixWord, tailWord_203287, baseEnd_203287] using wordTrace_append hprefix tailTrace_203287
  have hstable : (prefixWord ++ tailWord_203287).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203287).length < 2 ^ (prefixWord ++ tailWord_203287).sum := by decide
  have hdescent : baseEnd_203287 < baseStart_203287 := by decide
  rcases family_descends (prefixWord ++ tailWord_203287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203325 : List Nat := [1, 4, 1, 3, 2, 1, 4, 3]
def baseStart_203325 : Nat := 118140960795 + 203325 * 2 ^ 59
def prefixEnd_203325 : Nat := 4983230072969 + 3 ^ 40 * 203325 * 2
def baseEnd_203325 : Nat := 61868713526235391823663

theorem tailTrace_203325 : CollatzResearch.WordTrace tailWord_203325 prefixEnd_203325 61868713526235391823663 := by
  unfold tailWord_203325
  simp only [CollatzResearch.WordTrace]
  refine ⟨7415871988395724990499429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4943914658930483326999619 7415871988395724990499429)
  ·
    refine ⟨1390475997824198435718643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7415871988395724990499429 1390475997824198435718643)
    ·
      refine ⟨2085713996736297653577965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1390475997824198435718643 2085713996736297653577965)
      ·
        refine ⟨782142748776111620091737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2085713996736297653577965 782142748776111620091737)
        ·
          refine ⟨586607061582083715068803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 782142748776111620091737 586607061582083715068803)
          ·
            refine ⟨879910592373125572603205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 586607061582083715068803 879910592373125572603205)
            ·
              refine ⟨164983236069961044863101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 879910592373125572603205 164983236069961044863101)
              ·
                refine ⟨61868713526235391823663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 164983236069961044863101 61868713526235391823663)
                ·
                  rfl

theorem cell19_203325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 4, 3].length) (baseStart_203325 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_203325 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_203325 prefixEnd_203325 := by exact prefixLift 203325
  have htrace : WordTrace (prefixWord ++ tailWord_203325) baseStart_203325 baseEnd_203325 := by
    simpa [prefixWord, tailWord_203325, baseEnd_203325] using wordTrace_append hprefix tailTrace_203325
  have hstable : (prefixWord ++ tailWord_203325).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203325).length < 2 ^ (prefixWord ++ tailWord_203325).sum := by decide
  have hdescent : baseEnd_203325 < baseStart_203325 := by decide
  rcases family_descends (prefixWord ++ tailWord_203325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203418 : List Nat := [3, 1, 1, 6, 1, 2, 1, 4]
def baseStart_203418 : Nat := 118140960795 + 203418 * 2 ^ 59
def prefixEnd_203418 : Nat := 4983230072969 + 3 ^ 40 * 203418 * 2
def baseEnd_203418 : Nat := 61897012015638731756743

theorem tailTrace_203418 : CollatzResearch.WordTrace tailWord_203418 prefixEnd_203418 61897012015638731756743 := by
  unfold tailWord_203418
  simp only [CollatzResearch.WordTrace]
  refine ⟨1854815994264700468408727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4946175984705867915756605 1854815994264700468408727)
  ·
    refine ⟨2782223991397050702613091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1854815994264700468408727 2782223991397050702613091)
    ·
      refine ⟨4173335987095576053919637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2782223991397050702613091 4173335987095576053919637)
      ·
        refine ⟨195625124395105127527483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 4173335987095576053919637 195625124395105127527483)
        ·
          refine ⟨293437686592657691291225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195625124395105127527483 293437686592657691291225)
          ·
            refine ⟨220078264944493268468419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 293437686592657691291225 220078264944493268468419)
            ·
              refine ⟨330117397416739902702629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 220078264944493268468419 330117397416739902702629)
              ·
                refine ⟨61897012015638731756743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 330117397416739902702629 61897012015638731756743)
                ·
                  rfl

theorem cell19_203418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 1, 4].length) (baseStart_203418 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_203418 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_203418 prefixEnd_203418 := by exact prefixLift 203418
  have htrace : WordTrace (prefixWord ++ tailWord_203418) baseStart_203418 baseEnd_203418 := by
    simpa [prefixWord, tailWord_203418, baseEnd_203418] using wordTrace_append hprefix tailTrace_203418
  have hstable : (prefixWord ++ tailWord_203418).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203418).length < 2 ^ (prefixWord ++ tailWord_203418).sum := by decide
  have hdescent : baseEnd_203418 < baseStart_203418 := by decide
  rcases family_descends (prefixWord ++ tailWord_203418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203420 : List Nat := [2, 2, 3, 2, 2, 3, 1, 4]
def baseStart_203420 : Nat := 118140960795 + 203420 * 2 ^ 59
def prefixEnd_203420 : Nat := 4983230072969 + 3 ^ 40 * 203420 * 2
def baseEnd_203420 : Nat := 61897620585303319712293

theorem tailTrace_203420 : CollatzResearch.WordTrace tailWord_203420 prefixEnd_203420 61897620585303319712293 := by
  unfold tailWord_203420
  simp only [CollatzResearch.WordTrace]
  refine ⟨3709668461525778107603857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4946224615367704143471809 3709668461525778107603857)
  ·
    refine ⟨2782251346144333580702893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3709668461525778107603857 2782251346144333580702893)
    ·
      refine ⟨1043344254804125092763585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2782251346144333580702893 1043344254804125092763585)
      ·
        refine ⟨782508191103093819572689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1043344254804125092763585 782508191103093819572689)
        ·
          refine ⟨586881143327320364679517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 782508191103093819572689 586881143327320364679517)
          ·
            refine ⟨220080428747745136754819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 586881143327320364679517 220080428747745136754819)
            ·
              refine ⟨330120643121617705132229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 220080428747745136754819 330120643121617705132229)
              ·
                refine ⟨61897620585303319712293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 330120643121617705132229 61897620585303319712293)
                ·
                  rfl

theorem cell19_203420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 1, 4].length) (baseStart_203420 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_203420 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_203420 prefixEnd_203420 := by exact prefixLift 203420
  have htrace : WordTrace (prefixWord ++ tailWord_203420) baseStart_203420 baseEnd_203420 := by
    simpa [prefixWord, tailWord_203420, baseEnd_203420] using wordTrace_append hprefix tailTrace_203420
  have hstable : (prefixWord ++ tailWord_203420).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203420).length < 2 ^ (prefixWord ++ tailWord_203420).sum := by decide
  have hdescent : baseEnd_203420 < baseStart_203420 := by decide
  rcases family_descends (prefixWord ++ tailWord_203420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203460 : List Nat := [2, 3, 3, 1, 1, 3, 6]
def baseStart_203460 : Nat := 118140960795 + 203460 * 2 ^ 59
def prefixEnd_203460 : Nat := 4983230072969 + 3 ^ 40 * 203460 * 2
def baseEnd_203460 : Nat := 20636597326198359607765

theorem tailTrace_203460 : CollatzResearch.WordTrace tailWord_203460 prefixEnd_203460 20636597326198359607765 := by
  unfold tailWord_203460
  simp only [CollatzResearch.WordTrace]
  refine ⟨3710397921453321523331917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4947197228604428697775889 3710397921453321523331917)
  ·
    refine ⟨1391399220544995571249469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3710397921453321523331917 1391399220544995571249469)
    ·
      refine ⟨521774707704373339218551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1391399220544995571249469 521774707704373339218551)
      ·
        refine ⟨782662061556560008827827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 521774707704373339218551 782662061556560008827827)
        ·
          refine ⟨1173993092334840013241741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 782662061556560008827827 1173993092334840013241741)
          ·
            refine ⟨440247409625565004965653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1173993092334840013241741 440247409625565004965653)
            ·
              refine ⟨20636597326198359607765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 440247409625565004965653 20636597326198359607765)
              ·
                rfl

theorem cell19_203460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 6].length) (baseStart_203460 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_203460 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_203460 prefixEnd_203460 := by exact prefixLift 203460
  have htrace : WordTrace (prefixWord ++ tailWord_203460) baseStart_203460 baseEnd_203460 := by
    simpa [prefixWord, tailWord_203460, baseEnd_203460] using wordTrace_append hprefix tailTrace_203460
  have hstable : (prefixWord ++ tailWord_203460).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203460).length < 2 ^ (prefixWord ++ tailWord_203460).sum := by decide
  have hdescent : baseEnd_203460 < baseStart_203460 := by decide
  rcases family_descends (prefixWord ++ tailWord_203460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203481 : List Nat := [1, 2, 1, 2, 3, 2, 2, 6]
def baseStart_203481 : Nat := 118140960795 + 203481 * 2 ^ 59
def prefixEnd_203481 : Nat := 4983230072969 + 3 ^ 40 * 203481 * 2
def baseEnd_203481 : Nat := 61916181960073252356571

theorem tailTrace_203481 : CollatzResearch.WordTrace tailWord_203481 prefixEnd_203481 61916181960073252356571 := by
  unfold tailWord_203481
  simp only [CollatzResearch.WordTrace]
  refine ⟨7421561775830563633178297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4947707850553709088785531 7421561775830563633178297)
  ·
    refine ⟨5566171331872922724883723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7421561775830563633178297 5566171331872922724883723)
    ·
      refine ⟨8349256997809384087325585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5566171331872922724883723 8349256997809384087325585)
      ·
        refine ⟨6261942748357038065494189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8349256997809384087325585 6261942748357038065494189)
        ·
          refine ⟨2348228530633889274560321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6261942748357038065494189 2348228530633889274560321)
          ·
            refine ⟨1761171397975416955920241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2348228530633889274560321 1761171397975416955920241)
            ·
              refine ⟨1320878548481562716940181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1761171397975416955920241 1320878548481562716940181)
              ·
                refine ⟨61916181960073252356571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1320878548481562716940181 61916181960073252356571)
                ·
                  rfl

theorem cell19_203481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 6].length) (baseStart_203481 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_203481 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_203481 prefixEnd_203481 := by exact prefixLift 203481
  have htrace : WordTrace (prefixWord ++ tailWord_203481) baseStart_203481 baseEnd_203481 := by
    simpa [prefixWord, tailWord_203481, baseEnd_203481] using wordTrace_append hprefix tailTrace_203481
  have hstable : (prefixWord ++ tailWord_203481).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203481).length < 2 ^ (prefixWord ++ tailWord_203481).sum := by decide
  have hdescent : baseEnd_203481 < baseStart_203481 := by decide
  rcases family_descends (prefixWord ++ tailWord_203481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203557 : List Nat := [1, 3, 1, 2, 3, 1, 1, 7]
def baseStart_203557 : Nat := 118140960795 + 203557 * 2 ^ 59
def prefixEnd_203557 : Nat := 4983230072969 + 3 ^ 40 * 203557 * 2
def baseEnd_203557 : Nat := 61939307607327594667475

theorem tailTrace_203557 : CollatzResearch.WordTrace tailWord_203557 prefixEnd_203557 61939307607327594667475 := by
  unfold tailWord_203557
  simp only [CollatzResearch.WordTrace]
  refine ⟨7424333723555228612944925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4949555815703485741963283 7424333723555228612944925)
  ·
    refine ⟨2784125146333210729854347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7424333723555228612944925 2784125146333210729854347)
    ·
      refine ⟨4176187719499816094781521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2784125146333210729854347 4176187719499816094781521)
      ·
        refine ⟨3132140789624862071086141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4176187719499816094781521 3132140789624862071086141)
        ·
          refine ⟨1174552796109323276657303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3132140789624862071086141 1174552796109323276657303)
          ·
            refine ⟨1761829194163984914985955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1174552796109323276657303 1761829194163984914985955)
            ·
              refine ⟨2642743791245977372478933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1761829194163984914985955 2642743791245977372478933)
              ·
                refine ⟨61939307607327594667475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2642743791245977372478933 61939307607327594667475)
                ·
                  rfl

theorem cell19_203557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 7].length) (baseStart_203557 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_203557 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_203557 prefixEnd_203557 := by exact prefixLift 203557
  have htrace : WordTrace (prefixWord ++ tailWord_203557) baseStart_203557 baseEnd_203557 := by
    simpa [prefixWord, tailWord_203557, baseEnd_203557] using wordTrace_append hprefix tailTrace_203557
  have hstable : (prefixWord ++ tailWord_203557).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203557).length < 2 ^ (prefixWord ++ tailWord_203557).sum := by decide
  have hdescent : baseEnd_203557 < baseStart_203557 := by decide
  rcases family_descends (prefixWord ++ tailWord_203557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203572 : List Nat := [2, 5, 1, 1, 4, 6]
def baseStart_203572 : Nat := 118140960795 + 203572 * 2 ^ 59
def prefixEnd_203572 : Nat := 4983230072969 + 3 ^ 40 * 203572 * 2
def baseEnd_203572 : Nat := 6882652431090222703789

theorem tailTrace_203572 : CollatzResearch.WordTrace tailWord_203572 prefixEnd_203572 6882652431090222703789 := by
  unfold tailWord_203572
  simp only [CollatzResearch.WordTrace]
  refine ⟨3712440409250443087370485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4949920545667257449827313 3712440409250443087370485)
  ·
    refine ⟨348041288367229039440983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3712440409250443087370485 348041288367229039440983)
    ·
      refine ⟨522061932550843559161475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348041288367229039440983 522061932550843559161475)
      ·
        refine ⟨783092898826265338742213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 522061932550843559161475 783092898826265338742213)
        ·
          refine ⟨146829918529924751014165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 783092898826265338742213 146829918529924751014165)
          ·
            refine ⟨6882652431090222703789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 146829918529924751014165 6882652431090222703789)
            ·
              rfl

theorem cell19_203572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 6].length) (baseStart_203572 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_203572 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_203572 prefixEnd_203572 := by exact prefixLift 203572
  have htrace : WordTrace (prefixWord ++ tailWord_203572) baseStart_203572 baseEnd_203572 := by
    simpa [prefixWord, tailWord_203572, baseEnd_203572] using wordTrace_append hprefix tailTrace_203572
  have hstable : (prefixWord ++ tailWord_203572).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203572).length < 2 ^ (prefixWord ++ tailWord_203572).sum := by decide
  have hdescent : baseEnd_203572 < baseStart_203572 := by decide
  rcases family_descends (prefixWord ++ tailWord_203572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203574 : List Nat := [5, 1, 2, 2, 9]
def baseStart_203574 : Nat := 118140960795 + 203574 * 2 ^ 59
def prefixEnd_203574 : Nat := 4983230072969 + 3 ^ 40 * 203574 * 2
def baseEnd_203574 : Nat := 2294240016647281195913

theorem tailTrace_203574 : CollatzResearch.WordTrace tailWord_203574 prefixEnd_203574 2294240016647281195913 := by
  unfold tailWord_203574
  simp only [CollatzResearch.WordTrace]
  refine ⟨464059610280852532269611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4949969176329093677542517 464059610280852532269611)
  ·
    refine ⟨696089415421278798404417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 464059610280852532269611 696089415421278798404417)
    ·
      refine ⟨522067061565959098803313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 696089415421278798404417 522067061565959098803313)
      ·
        refine ⟨391550296174469324102485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 522067061565959098803313 391550296174469324102485)
        ·
          refine ⟨2294240016647281195913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 391550296174469324102485 2294240016647281195913)
          ·
            rfl

theorem cell19_203574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 9].length) (baseStart_203574 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_203574 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_203574 prefixEnd_203574 := by exact prefixLift 203574
  have htrace : WordTrace (prefixWord ++ tailWord_203574) baseStart_203574 baseEnd_203574 := by
    simpa [prefixWord, tailWord_203574, baseEnd_203574] using wordTrace_append hprefix tailTrace_203574
  have hstable : (prefixWord ++ tailWord_203574).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203574).length < 2 ^ (prefixWord ++ tailWord_203574).sum := by decide
  have hdescent : baseEnd_203574 < baseStart_203574 := by decide
  rcases family_descends (prefixWord ++ tailWord_203574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203593 : List Nat := [1, 2, 1, 1, 2, 7, 1, 4]
def baseStart_203593 : Nat := 118140960795 + 203593 * 2 ^ 59
def prefixEnd_203593 : Nat := 4983230072969 + 3 ^ 40 * 203593 * 2
def baseEnd_203593 : Nat := 61950261861290177867377

theorem tailTrace_203593 : CollatzResearch.WordTrace tailWord_203593 prefixEnd_203593 61950261861290177867377 := by
  unfold tailWord_203593
  simp only [CollatzResearch.WordTrace]
  refine ⟨7425646751424806761255433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4950431167616537840836955 7425646751424806761255433)
  ·
    refine ⟨5569235063568605070941575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7425646751424806761255433 5569235063568605070941575)
    ·
      refine ⟨8353852595352907606412363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5569235063568605070941575 8353852595352907606412363)
      ·
        refine ⟨12530778893029361409618545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8353852595352907606412363 12530778893029361409618545)
        ·
          refine ⟨9398084169772021057213909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12530778893029361409618545 9398084169772021057213909)
          ·
            refine ⟨220267597729031743528451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 9398084169772021057213909 220267597729031743528451)
            ·
              refine ⟨330401396593547615292677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 220267597729031743528451 330401396593547615292677)
              ·
                refine ⟨61950261861290177867377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 330401396593547615292677 61950261861290177867377)
                ·
                  rfl

theorem cell19_203593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 1, 4].length) (baseStart_203593 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_203593 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_203593 prefixEnd_203593 := by exact prefixLift 203593
  have htrace : WordTrace (prefixWord ++ tailWord_203593) baseStart_203593 baseEnd_203593 := by
    simpa [prefixWord, tailWord_203593, baseEnd_203593] using wordTrace_append hprefix tailTrace_203593
  have hstable : (prefixWord ++ tailWord_203593).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203593).length < 2 ^ (prefixWord ++ tailWord_203593).sum := by decide
  have hdescent : baseEnd_203593 < baseStart_203593 := by decide
  rcases family_descends (prefixWord ++ tailWord_203593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203633 : List Nat := [1, 2, 2, 2, 1, 5, 6]
def baseStart_203633 : Nat := 118140960795 + 203633 * 2 ^ 59
def prefixEnd_203633 : Nat := 4983230072969 + 3 ^ 40 * 203633 * 2
def baseEnd_203633 : Nat := 20654144418193978992793

theorem tailTrace_203633 : CollatzResearch.WordTrace tailWord_203633 prefixEnd_203633 20654144418193978992793 := by
  unfold tailWord_203633
  simp only [CollatzResearch.WordTrace]
  refine ⟨7427105671279893592711553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4951403780853262395141035 7427105671279893592711553)
  ·
    refine ⟨5570329253459920194533665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7427105671279893592711553 5570329253459920194533665)
    ·
      refine ⟨4177746940094940145900249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5570329253459920194533665 4177746940094940145900249)
      ·
        refine ⟨3133310205071205109425187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4177746940094940145900249 3133310205071205109425187)
        ·
          refine ⟨4699965307606807664137781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3133310205071205109425187 4699965307606807664137781)
          ·
            refine ⟨440621747588138218512917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4699965307606807664137781 440621747588138218512917)
            ·
              refine ⟨20654144418193978992793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 440621747588138218512917 20654144418193978992793)
              ·
                rfl

theorem cell19_203633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 6].length) (baseStart_203633 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_203633 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_203633 prefixEnd_203633 := by exact prefixLift 203633
  have htrace : WordTrace (prefixWord ++ tailWord_203633) baseStart_203633 baseEnd_203633 := by
    simpa [prefixWord, tailWord_203633, baseEnd_203633] using wordTrace_append hprefix tailTrace_203633
  have hstable : (prefixWord ++ tailWord_203633).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203633).length < 2 ^ (prefixWord ++ tailWord_203633).sum := by decide
  have hdescent : baseEnd_203633 < baseStart_203633 := by decide
  rcases family_descends (prefixWord ++ tailWord_203633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203652 : List Nat := [2, 3, 2, 1, 1, 1, 1, 8]
def baseStart_203652 : Nat := 118140960795 + 203652 * 2 ^ 59
def prefixEnd_203652 : Nat := 4983230072969 + 3 ^ 40 * 203652 * 2
def baseEnd_203652 : Nat := 61968214666395522556105

theorem tailTrace_203652 : CollatzResearch.WordTrace tailWord_203652 prefixEnd_203652 61968214666395522556105 := by
  unfold tailWord_203652
  simp only [CollatzResearch.WordTrace]
  refine ⟨3713899329105529918826605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4951865772140706558435473 3713899329105529918826605)
  ·
    refine ⟨1392712248414573719559977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3713899329105529918826605 1392712248414573719559977)
    ·
      refine ⟨1044534186310930289669983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1392712248414573719559977 1044534186310930289669983)
      ·
        refine ⟨1566801279466395434504975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1044534186310930289669983 1566801279466395434504975)
        ·
          refine ⟨2350201919199593151757463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1566801279466395434504975 2350201919199593151757463)
          ·
            refine ⟨3525302878799389727636195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2350201919199593151757463 3525302878799389727636195)
            ·
              refine ⟨5287954318199084591454293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3525302878799389727636195 5287954318199084591454293)
              ·
                refine ⟨61968214666395522556105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5287954318199084591454293 61968214666395522556105)
                ·
                  rfl

theorem cell19_203652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 8].length) (baseStart_203652 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_203652 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_203652 prefixEnd_203652 := by exact prefixLift 203652
  have htrace : WordTrace (prefixWord ++ tailWord_203652) baseStart_203652 baseEnd_203652 := by
    simpa [prefixWord, tailWord_203652, baseEnd_203652] using wordTrace_append hprefix tailTrace_203652
  have hstable : (prefixWord ++ tailWord_203652).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203652).length < 2 ^ (prefixWord ++ tailWord_203652).sum := by decide
  have hdescent : baseEnd_203652 < baseStart_203652 := by decide
  rcases family_descends (prefixWord ++ tailWord_203652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203669 : List Nat := [1, 3, 2, 1, 1, 4, 4, 3]
def baseStart_203669 : Nat := 118140960795 + 203669 * 2 ^ 59
def prefixEnd_203669 : Nat := 4983230072969 + 3 ^ 40 * 203669 * 2
def baseEnd_203669 : Nat := 61973387508544520178281

theorem tailTrace_203669 : CollatzResearch.WordTrace tailWord_203669 prefixEnd_203669 61973387508544520178281 := by
  unfold tailWord_203669
  simp only [CollatzResearch.WordTrace]
  refine ⟨7428418699149471741022061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4952279132766314494014707 7428418699149471741022061)
  ·
    refine ⟨2785657012181051902883273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7428418699149471741022061 2785657012181051902883273)
    ·
      refine ⟨2089242759135788927162455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2785657012181051902883273 2089242759135788927162455)
      ·
        refine ⟨3133864138703683390743683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2089242759135788927162455 3133864138703683390743683)
        ·
          refine ⟨4700796208055525086115525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3133864138703683390743683 4700796208055525086115525)
          ·
            refine ⟨881399289010410953646661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4700796208055525086115525 881399289010410953646661)
            ·
              refine ⟨165262366689452053808749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 881399289010410953646661 165262366689452053808749)
              ·
                refine ⟨61973387508544520178281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 165262366689452053808749 61973387508544520178281)
                ·
                  rfl

theorem cell19_203669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 4, 3].length) (baseStart_203669 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_203669 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_203669 prefixEnd_203669 := by exact prefixLift 203669
  have htrace : WordTrace (prefixWord ++ tailWord_203669) baseStart_203669 baseEnd_203669 := by
    simpa [prefixWord, tailWord_203669, baseEnd_203669] using wordTrace_append hprefix tailTrace_203669
  have hstable : (prefixWord ++ tailWord_203669).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203669).length < 2 ^ (prefixWord ++ tailWord_203669).sum := by decide
  have hdescent : baseEnd_203669 < baseStart_203669 := by decide
  rcases family_descends (prefixWord ++ tailWord_203669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203671 : List Nat := [1, 1, 3, 3, 1, 2, 3, 5]
def baseStart_203671 : Nat := 118140960795 + 203671 * 2 ^ 59
def prefixEnd_203671 : Nat := 4983230072969 + 3 ^ 40 * 203671 * 2
def baseEnd_203671 : Nat := 61973996078209108133831

theorem tailTrace_203671 : CollatzResearch.WordTrace tailWord_203671 prefixEnd_203671 61973996078209108133831 := by
  unfold tailWord_203671
  simp only [CollatzResearch.WordTrace]
  refine ⟨7428491645142226082594867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4952327763428150721729911 7428491645142226082594867)
  ·
    refine ⟨11142737467713339123892301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7428491645142226082594867 11142737467713339123892301)
    ·
      refine ⟨4178526550392502171459613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11142737467713339123892301 4178526550392502171459613)
      ·
        refine ⟨1566947456397188314297355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4178526550392502171459613 1566947456397188314297355)
        ·
          refine ⟨2350421184595782471446033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1566947456397188314297355 2350421184595782471446033)
          ·
            refine ⟨1762815888446836853584525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2350421184595782471446033 1762815888446836853584525)
            ·
              refine ⟨661055958167563820094197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1762815888446836853584525 661055958167563820094197)
              ·
                refine ⟨61973996078209108133831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 661055958167563820094197 61973996078209108133831)
                ·
                  rfl

theorem cell19_203671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 5].length) (baseStart_203671 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_203671 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_203671 prefixEnd_203671 := by exact prefixLift 203671
  have htrace : WordTrace (prefixWord ++ tailWord_203671) baseStart_203671 baseEnd_203671 := by
    simpa [prefixWord, tailWord_203671, baseEnd_203671] using wordTrace_append hprefix tailTrace_203671
  have hstable : (prefixWord ++ tailWord_203671).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203671).length < 2 ^ (prefixWord ++ tailWord_203671).sum := by decide
  have hdescent : baseEnd_203671 < baseStart_203671 := by decide
  rcases family_descends (prefixWord ++ tailWord_203671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203783 : List Nat := [1, 1, 4, 3, 1, 1, 5, 3]
def baseStart_203783 : Nat := 118140960795 + 203783 * 2 ^ 59
def prefixEnd_203783 : Nat := 4983230072969 + 3 ^ 40 * 203783 * 2
def baseEnd_203783 : Nat := 62008075979426033644637

theorem tailTrace_203783 : CollatzResearch.WordTrace tailWord_203783 prefixEnd_203783 62008075979426033644637 := by
  unfold tailWord_203783
  simp only [CollatzResearch.WordTrace]
  refine ⟨7432576620736469210672003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4955051080490979473781335 7432576620736469210672003)
  ·
    refine ⟨11148864931104703816008005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7432576620736469210672003 11148864931104703816008005)
    ·
      refine ⟨2090412174582131965501501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11148864931104703816008005 2090412174582131965501501)
      ·
        refine ⟨783904565468299487063063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2090412174582131965501501 783904565468299487063063)
        ·
          refine ⟨1175856848202449230594595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 783904565468299487063063 1175856848202449230594595)
          ·
            refine ⟨1763785272303673845891893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1175856848202449230594595 1763785272303673845891893)
            ·
              refine ⟨165354869278469423052365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1763785272303673845891893 165354869278469423052365)
              ·
                refine ⟨62008075979426033644637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 165354869278469423052365 62008075979426033644637)
                ·
                  rfl

theorem cell19_203783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 5, 3].length) (baseStart_203783 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_203783 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_203783 prefixEnd_203783 := by exact prefixLift 203783
  have htrace : WordTrace (prefixWord ++ tailWord_203783) baseStart_203783 baseEnd_203783 := by
    simpa [prefixWord, tailWord_203783, baseEnd_203783] using wordTrace_append hprefix tailTrace_203783
  have hstable : (prefixWord ++ tailWord_203783).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203783).length < 2 ^ (prefixWord ++ tailWord_203783).sum := by decide
  have hdescent : baseEnd_203783 < baseStart_203783 := by decide
  rcases family_descends (prefixWord ++ tailWord_203783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203838 : List Nat := [4, 2, 1, 3, 1, 1, 4, 3]
def baseStart_203838 : Nat := 118140960795 + 203838 * 2 ^ 59
def prefixEnd_203838 : Nat := 4983230072969 + 3 ^ 40 * 203838 * 2
def baseEnd_203838 : Nat := 62024811645202202422265

theorem tailTrace_203838 : CollatzResearch.WordTrace tailWord_203838 prefixEnd_203838 62024811645202202422265 := by
  unfold tailWord_203838
  simp only [CollatzResearch.WordTrace]
  refine ⟨929322829442151700490521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4956388423691475735949445 929322829442151700490521)
  ·
    refine ⟨696992122081613775367891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 929322829442151700490521 696992122081613775367891)
    ·
      refine ⟨1045488183122420663051837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 696992122081613775367891 1045488183122420663051837)
      ·
        refine ⟨392058068670907748644439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1045488183122420663051837 392058068670907748644439)
        ·
          refine ⟨588087103006361622966659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 392058068670907748644439 588087103006361622966659)
          ·
            refine ⟨882130654509542434449989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 588087103006361622966659 882130654509542434449989)
            ·
              refine ⟨165399497720539206459373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 882130654509542434449989 165399497720539206459373)
              ·
                refine ⟨62024811645202202422265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 165399497720539206459373 62024811645202202422265)
                ·
                  rfl

theorem cell19_203838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 4, 3].length) (baseStart_203838 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_203838 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_203838 prefixEnd_203838 := by exact prefixLift 203838
  have htrace : WordTrace (prefixWord ++ tailWord_203838) baseStart_203838 baseEnd_203838 := by
    simpa [prefixWord, tailWord_203838, baseEnd_203838] using wordTrace_append hprefix tailTrace_203838
  have hstable : (prefixWord ++ tailWord_203838).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203838).length < 2 ^ (prefixWord ++ tailWord_203838).sum := by decide
  have hdescent : baseEnd_203838 < baseStart_203838 := by decide
  rcases family_descends (prefixWord ++ tailWord_203838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203918 : List Nat := [4, 1, 1, 3, 2, 8]
def baseStart_203918 : Nat := 118140960795 + 203918 * 2 ^ 59
def prefixEnd_203918 : Nat := 4983230072969 + 3 ^ 40 * 203918 * 2
def baseEnd_203918 : Nat := 6894350492420635627141

theorem tailTrace_203918 : CollatzResearch.WordTrace tailWord_203918 prefixEnd_203918 6894350492420635627141 := by
  unfold tailWord_203918
  simp only [CollatzResearch.WordTrace]
  refine ⟨929687559405923408354551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4958333650164924844557605 929687559405923408354551)
  ·
    refine ⟨1394531339108885112531827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 929687559405923408354551 1394531339108885112531827)
    ·
      refine ⟨2091797008663327668797741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1394531339108885112531827 2091797008663327668797741)
      ·
        refine ⟨784423878248747875799153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2091797008663327668797741 784423878248747875799153)
        ·
          refine ⟨588317908686560906849365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 784423878248747875799153 588317908686560906849365)
          ·
            refine ⟨6894350492420635627141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 588317908686560906849365 6894350492420635627141)
            ·
              rfl

theorem cell19_203918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 8].length) (baseStart_203918 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_203918 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_203918 prefixEnd_203918 := by exact prefixLift 203918
  have htrace : WordTrace (prefixWord ++ tailWord_203918) baseStart_203918 baseEnd_203918 := by
    simpa [prefixWord, tailWord_203918, baseEnd_203918] using wordTrace_append hprefix tailTrace_203918
  have hstable : (prefixWord ++ tailWord_203918).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203918).length < 2 ^ (prefixWord ++ tailWord_203918).sum := by decide
  have hdescent : baseEnd_203918 < baseStart_203918 := by decide
  rcases family_descends (prefixWord ++ tailWord_203918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203954 : List Nat := [3, 2, 1, 1, 1, 5, 3, 3]
def baseStart_203954 : Nat := 118140960795 + 203954 * 2 ^ 59
def prefixEnd_203954 : Nat := 4983230072969 + 3 ^ 40 * 203954 * 2
def baseEnd_203954 : Nat := 62060108685748303844171

theorem tailTrace_203954 : CollatzResearch.WordTrace tailWord_203954 prefixEnd_203954 62060108685748303844171 := by
  unfold tailWord_203954
  simp only [CollatzResearch.WordTrace]
  refine ⟨1859703375779241353786729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4959209002077976943431277 1859703375779241353786729)
  ·
    refine ⟨1394777531834431015340047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1859703375779241353786729 1394777531834431015340047)
    ·
      refine ⟨2092166297751646523010071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1394777531834431015340047 2092166297751646523010071)
      ·
        refine ⟨3138249446627469784515107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2092166297751646523010071 3138249446627469784515107)
        ·
          refine ⟨4707374169941204676772661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3138249446627469784515107 4707374169941204676772661)
          ·
            refine ⟨441316328431987938447437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4707374169941204676772661 441316328431987938447437)
            ·
              refine ⟨165493623161995476917789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 441316328431987938447437 165493623161995476917789)
              ·
                refine ⟨62060108685748303844171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 165493623161995476917789 62060108685748303844171)
                ·
                  rfl

theorem cell19_203954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 3, 3].length) (baseStart_203954 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_203954 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_203954 prefixEnd_203954 := by exact prefixLift 203954
  have htrace : WordTrace (prefixWord ++ tailWord_203954) baseStart_203954 baseEnd_203954 := by
    simpa [prefixWord, tailWord_203954, baseEnd_203954] using wordTrace_append hprefix tailTrace_203954
  have hstable : (prefixWord ++ tailWord_203954).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203954).length < 2 ^ (prefixWord ++ tailWord_203954).sum := by decide
  have hdescent : baseEnd_203954 < baseStart_203954 := by decide
  rcases family_descends (prefixWord ++ tailWord_203954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204007 : List Nat := [1, 1, 5, 3, 3, 1, 2, 3]
def baseStart_204007 : Nat := 118140960795 + 204007 * 2 ^ 59
def prefixEnd_204007 : Nat := 4983230072969 + 3 ^ 40 * 204007 * 2
def baseEnd_204007 : Nat := 62076235781859884666249

theorem tailTrace_204007 : CollatzResearch.WordTrace tailWord_204007 prefixEnd_204007 62076235781859884666249 := by
  unfold tailWord_204007
  simp only [CollatzResearch.WordTrace]
  refine ⟨7440746571924955466826275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4960497714616636977884183 7440746571924955466826275)
  ·
    refine ⟨11161119857887433200239413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7440746571924955466826275 11161119857887433200239413)
    ·
      refine ⟨1046354986676946862522445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11161119857887433200239413 1046354986676946862522445)
      ·
        refine ⟨392383120003855073445917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1046354986676946862522445 392383120003855073445917)
        ·
          refine ⟨147143670001445652542219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 392383120003855073445917 147143670001445652542219)
          ·
            refine ⟨220715505002168478813329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147143670001445652542219 220715505002168478813329)
            ·
              refine ⟨165536628751626359109997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 220715505002168478813329 165536628751626359109997)
              ·
                refine ⟨62076235781859884666249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 165536628751626359109997 62076235781859884666249)
                ·
                  rfl

theorem cell19_204007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 2, 3].length) (baseStart_204007 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_204007 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_204007 prefixEnd_204007 := by exact prefixLift 204007
  have htrace : WordTrace (prefixWord ++ tailWord_204007) baseStart_204007 baseEnd_204007 := by
    simpa [prefixWord, tailWord_204007, baseEnd_204007] using wordTrace_append hprefix tailTrace_204007
  have hstable : (prefixWord ++ tailWord_204007).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204007).length < 2 ^ (prefixWord ++ tailWord_204007).sum := by decide
  have hdescent : baseEnd_204007 < baseStart_204007 := by decide
  rcases family_descends (prefixWord ++ tailWord_204007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204011 : List Nat := [1, 1, 1, 1, 2, 8, 2, 3]
def baseStart_204011 : Nat := 118140960795 + 204011 * 2 ^ 59
def prefixEnd_204011 : Nat := 4983230072969 + 3 ^ 40 * 204011 * 2
def baseEnd_204011 : Nat := 62077452921189060577349

theorem tailTrace_204011 : CollatzResearch.WordTrace tailWord_204011 prefixEnd_204011 62077452921189060577349 := by
  unfold tailWord_204011
  simp only [CollatzResearch.WordTrace]
  refine ⟨7440892463910464149971887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4960594975940309433314591 7440892463910464149971887)
  ·
    refine ⟨11161338695865696224957831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7440892463910464149971887 11161338695865696224957831)
    ·
      refine ⟨16742008043798544337436747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11161338695865696224957831 16742008043798544337436747)
      ·
        refine ⟨25113012065697816506155121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16742008043798544337436747 25113012065697816506155121)
        ·
          refine ⟨18834759049273362379616341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25113012065697816506155121 18834759049273362379616341)
          ·
            refine ⟨220719832608672215386129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 18834759049273362379616341 220719832608672215386129)
            ·
              refine ⟨165539874456504161539597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 220719832608672215386129 165539874456504161539597)
              ·
                refine ⟨62077452921189060577349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 165539874456504161539597 62077452921189060577349)
                ·
                  rfl

theorem cell19_204011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 2, 3].length) (baseStart_204011 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_204011 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_204011 prefixEnd_204011 := by exact prefixLift 204011
  have htrace : WordTrace (prefixWord ++ tailWord_204011) baseStart_204011 baseEnd_204011 := by
    simpa [prefixWord, tailWord_204011, baseEnd_204011] using wordTrace_append hprefix tailTrace_204011
  have hstable : (prefixWord ++ tailWord_204011).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204011).length < 2 ^ (prefixWord ++ tailWord_204011).sum := by decide
  have hdescent : baseEnd_204011 < baseStart_204011 := by decide
  rcases family_descends (prefixWord ++ tailWord_204011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204030 : List Nat := [4, 2, 2, 1, 1, 4, 5]
def baseStart_204030 : Nat := 118140960795 + 204030 * 2 ^ 59
def prefixEnd_204030 : Nat := 4983230072969 + 3 ^ 40 * 204030 * 2
def baseEnd_204030 : Nat := 20694411444334215385025

theorem tailTrace_204030 : CollatzResearch.WordTrace tailWord_204030 prefixEnd_204030 20694411444334215385025 := by
  unfold tailWord_204030
  simp only [CollatzResearch.WordTrace]
  refine ⟨930198181355203799364193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4961056967227753596609029 930198181355203799364193)
  ·
    refine ⟨697648636016402849523145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 930198181355203799364193 697648636016402849523145)
    ·
      refine ⟨523236477012302137142359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 697648636016402849523145 523236477012302137142359)
      ·
        refine ⟨784854715518453205713539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 523236477012302137142359 784854715518453205713539)
        ·
          refine ⟨1177282073277679808570309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 784854715518453205713539 1177282073277679808570309)
          ·
            refine ⟨220740388739564964106933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1177282073277679808570309 220740388739564964106933)
            ·
              refine ⟨20694411444334215385025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 220740388739564964106933 20694411444334215385025)
              ·
                rfl

theorem cell19_204030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 5].length) (baseStart_204030 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_204030 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_204030 prefixEnd_204030 := by exact prefixLift 204030
  have htrace : WordTrace (prefixWord ++ tailWord_204030) baseStart_204030 baseEnd_204030 := by
    simpa [prefixWord, tailWord_204030, baseEnd_204030] using wordTrace_append hprefix tailTrace_204030
  have hstable : (prefixWord ++ tailWord_204030).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204030).length < 2 ^ (prefixWord ++ tailWord_204030).sum := by decide
  have hdescent : baseEnd_204030 < baseStart_204030 := by decide
  rcases family_descends (prefixWord ++ tailWord_204030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204089 : List Nat := [1, 2, 1, 6, 2, 7]
def baseStart_204089 : Nat := 118140960795 + 204089 * 2 ^ 59
def prefixEnd_204089 : Nat := 4983230072969 + 3 ^ 40 * 204089 * 2
def baseEnd_204089 : Nat := 6900131904234221204867

theorem tailTrace_204089 : CollatzResearch.WordTrace tailWord_204089 prefixEnd_204089 6900131904234221204867 := by
  unfold tailWord_204089
  simp only [CollatzResearch.WordTrace]
  refine ⟨7443737357627883471311321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4962491571751922314207547 7443737357627883471311321)
  ·
    refine ⟨5582803018220912603483491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7443737357627883471311321 5582803018220912603483491)
    ·
      refine ⟨8374204527331368905225237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5582803018220912603483491 8374204527331368905225237)
      ·
        refine ⟨392540837218657917432433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 8374204527331368905225237 392540837218657917432433)
        ·
          refine ⟨294405627913993438074325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 392540837218657917432433 294405627913993438074325)
          ·
            refine ⟨6900131904234221204867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 294405627913993438074325 6900131904234221204867)
            ·
              rfl

theorem cell19_204089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 7].length) (baseStart_204089 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_204089 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_204089 prefixEnd_204089 := by exact prefixLift 204089
  have htrace : WordTrace (prefixWord ++ tailWord_204089) baseStart_204089 baseEnd_204089 := by
    simpa [prefixWord, tailWord_204089, baseEnd_204089] using wordTrace_append hprefix tailTrace_204089
  have hstable : (prefixWord ++ tailWord_204089).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204089).length < 2 ^ (prefixWord ++ tailWord_204089).sum := by decide
  have hdescent : baseEnd_204089 < baseStart_204089 := by decide
  rcases family_descends (prefixWord ++ tailWord_204089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204108 : List Nat := [2, 2, 1, 3, 2, 2, 3, 4]
def baseStart_204108 : Nat := 118140960795 + 204108 * 2 ^ 59
def prefixEnd_204108 : Nat := 4983230072969 + 3 ^ 40 * 204108 * 2
def baseEnd_204108 : Nat := 62106968549921576421529

theorem tailTrace_204108 : CollatzResearch.WordTrace tailWord_204108 prefixEnd_204108 62106968549921576421529 := by
  unfold tailWord_204108
  simp only [CollatzResearch.WordTrace]
  refine ⟨3722215172279524858126489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4962953563039366477501985 3722215172279524858126489)
  ·
    refine ⟨2791661379209643643594867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3722215172279524858126489 2791661379209643643594867)
    ·
      refine ⟨4187492068814465465392301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2791661379209643643594867 4187492068814465465392301)
      ·
        refine ⟨1570309525805424549522113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4187492068814465465392301 1570309525805424549522113)
        ·
          refine ⟨1177732144354068412141585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1570309525805424549522113 1177732144354068412141585)
          ·
            refine ⟨883299108265551309106189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1177732144354068412141585 883299108265551309106189)
            ·
              refine ⟨331237165599581740914821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 883299108265551309106189 331237165599581740914821)
              ·
                refine ⟨62106968549921576421529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 331237165599581740914821 62106968549921576421529)
                ·
                  rfl

theorem cell19_204108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3, 4].length) (baseStart_204108 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_204108 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_204108 prefixEnd_204108 := by exact prefixLift 204108
  have htrace : WordTrace (prefixWord ++ tailWord_204108) baseStart_204108 baseEnd_204108 := by
    simpa [prefixWord, tailWord_204108, baseEnd_204108] using wordTrace_append hprefix tailTrace_204108
  have hstable : (prefixWord ++ tailWord_204108).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204108).length < 2 ^ (prefixWord ++ tailWord_204108).sum := by decide
  have hdescent : baseEnd_204108 < baseStart_204108 := by decide
  rcases family_descends (prefixWord ++ tailWord_204108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204129 : List Nat := [1, 2, 3, 1, 1, 1, 1, 9]
def baseStart_204129 : Nat := 118140960795 + 204129 * 2 ^ 59
def prefixEnd_204129 : Nat := 4983230072969 + 3 ^ 40 * 204129 * 2
def baseEnd_204129 : Nat := 62113358531399749954805

theorem tailTrace_204129 : CollatzResearch.WordTrace tailWord_204129 prefixEnd_204129 62113358531399749954805 := by
  unfold tailWord_204129
  simp only [CollatzResearch.WordTrace]
  refine ⟨7445196277482970302767441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4963464184988646868511627 7445196277482970302767441)
  ·
    refine ⟨5583897208112227727075581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7445196277482970302767441 5583897208112227727075581)
    ·
      refine ⟨2093961453042085397653343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5583897208112227727075581 2093961453042085397653343)
      ·
        refine ⟨3140942179563128096480015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2093961453042085397653343 3140942179563128096480015)
        ·
          refine ⟨4711413269344692144720023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3140942179563128096480015 4711413269344692144720023)
          ·
            refine ⟨7067119904017038217080035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4711413269344692144720023 7067119904017038217080035)
            ·
              refine ⟨10600679856025557325620053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7067119904017038217080035 10600679856025557325620053)
              ·
                refine ⟨62113358531399749954805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10600679856025557325620053 62113358531399749954805)
                ·
                  rfl

theorem cell19_204129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 9].length) (baseStart_204129 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_204129 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_204129 prefixEnd_204129 := by exact prefixLift 204129
  have htrace : WordTrace (prefixWord ++ tailWord_204129) baseStart_204129 baseEnd_204129 := by
    simpa [prefixWord, tailWord_204129, baseEnd_204129] using wordTrace_append hprefix tailTrace_204129
  have hstable : (prefixWord ++ tailWord_204129).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204129).length < 2 ^ (prefixWord ++ tailWord_204129).sum := by decide
  have hdescent : baseEnd_204129 < baseStart_204129 := by decide
  rcases family_descends (prefixWord ++ tailWord_204129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204178 : List Nat := [3, 2, 3, 3, 1, 2, 2, 3]
def baseStart_204178 : Nat := 118140960795 + 204178 * 2 ^ 59
def prefixEnd_204178 : Nat := 4983230072969 + 3 ^ 40 * 204178 * 2
def baseEnd_204178 : Nat := 62128268488182154865783

theorem tailTrace_204178 : CollatzResearch.WordTrace tailWord_204178 prefixEnd_204178 62128268488182154865783 := by
  unfold tailWord_204178
  simp only [CollatzResearch.WordTrace]
  refine ⟨1861745863576362917825297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4964655636203634447534125 1861745863576362917825297)
  ·
    refine ⟨1396309397682272188368973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1861745863576362917825297 1396309397682272188368973)
    ·
      refine ⟨523616024130852070638365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1396309397682272188368973 523616024130852070638365)
      ·
        refine ⟨196356009049069526489387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 523616024130852070638365 196356009049069526489387)
        ·
          refine ⟨294534013573604289734081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196356009049069526489387 294534013573604289734081)
          ·
            refine ⟨220900510180203217300561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 294534013573604289734081 220900510180203217300561)
            ·
              refine ⟨165675382635152412975421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 220900510180203217300561 165675382635152412975421)
              ·
                refine ⟨62128268488182154865783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 165675382635152412975421 62128268488182154865783)
                ·
                  rfl

theorem cell19_204178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 2, 3].length) (baseStart_204178 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_204178 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_204178 prefixEnd_204178 := by exact prefixLift 204178
  have htrace : WordTrace (prefixWord ++ tailWord_204178) baseStart_204178 baseEnd_204178 := by
    simpa [prefixWord, tailWord_204178, baseEnd_204178] using wordTrace_append hprefix tailTrace_204178
  have hstable : (prefixWord ++ tailWord_204178).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204178).length < 2 ^ (prefixWord ++ tailWord_204178).sum := by decide
  have hdescent : baseEnd_204178 < baseStart_204178 := by decide
  rcases family_descends (prefixWord ++ tailWord_204178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204180 : List Nat := [2, 4, 2, 1, 2, 3, 2, 3]
def baseStart_204180 : Nat := 118140960795 + 204180 * 2 ^ 59
def prefixEnd_204180 : Nat := 4983230072969 + 3 ^ 40 * 204180 * 2
def baseEnd_204180 : Nat := 62128877057846742821333

theorem tailTrace_204180 : CollatzResearch.WordTrace tailWord_204180 prefixEnd_204180 62128877057846742821333 := by
  unfold tailWord_204180
  simp only [CollatzResearch.WordTrace]
  refine ⟨3723528200149103006436997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4964704266865470675249329 3723528200149103006436997)
  ·
    refine ⟨698161537527956813706937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3723528200149103006436997 698161537527956813706937)
    ·
      refine ⟨523621153145967610280203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 698161537527956813706937 523621153145967610280203)
      ·
        refine ⟨785431729718951415420305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 523621153145967610280203 785431729718951415420305)
        ·
          refine ⟨589073797289213561565229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 785431729718951415420305 589073797289213561565229)
          ·
            refine ⟨220902673983455085586961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 589073797289213561565229 220902673983455085586961)
            ·
              refine ⟨165677005487591314190221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 220902673983455085586961 165677005487591314190221)
              ·
                refine ⟨62128877057846742821333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 165677005487591314190221 62128877057846742821333)
                ·
                  rfl

theorem cell19_204180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 2, 3].length) (baseStart_204180 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_204180 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_204180 prefixEnd_204180 := by exact prefixLift 204180
  have htrace : WordTrace (prefixWord ++ tailWord_204180) baseStart_204180 baseEnd_204180 := by
    simpa [prefixWord, tailWord_204180, baseEnd_204180] using wordTrace_append hprefix tailTrace_204180
  have hstable : (prefixWord ++ tailWord_204180).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204180).length < 2 ^ (prefixWord ++ tailWord_204180).sum := by decide
  have hdescent : baseEnd_204180 < baseStart_204180 := by decide
  rcases family_descends (prefixWord ++ tailWord_204180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204220 : List Nat := [2, 2, 2, 4, 2, 1, 2, 4]
def baseStart_204220 : Nat := 118140960795 + 204220 * 2 ^ 59
def prefixEnd_204220 : Nat := 4983230072969 + 3 ^ 40 * 204220 * 2
def baseEnd_204220 : Nat := 62141048451138501932335

theorem tailTrace_204220 : CollatzResearch.WordTrace tailWord_204220 prefixEnd_204220 62141048451138501932335 := by
  unfold tailWord_204220
  simp only [CollatzResearch.WordTrace]
  refine ⟨3724257660076646422165057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4965676880102195229553409 3724257660076646422165057)
  ·
    refine ⟨2793193245057484816623793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3724257660076646422165057 2793193245057484816623793)
    ·
      refine ⟨2094894933793113612467845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2793193245057484816623793 2094894933793113612467845)
      ·
        refine ⟨392792800086208802337721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2094894933793113612467845 392792800086208802337721)
        ·
          refine ⟨294594600064656601753291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 392792800086208802337721 294594600064656601753291)
          ·
            refine ⟨441891900096984902629937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 294594600064656601753291 441891900096984902629937)
            ·
              refine ⟨331418925072738676972453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 441891900096984902629937 331418925072738676972453)
              ·
                refine ⟨62141048451138501932335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 331418925072738676972453 62141048451138501932335)
                ·
                  rfl

theorem cell19_204220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 2, 4].length) (baseStart_204220 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_204220 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_204220 prefixEnd_204220 := by exact prefixLift 204220
  have htrace : WordTrace (prefixWord ++ tailWord_204220) baseStart_204220 baseEnd_204220 := by
    simpa [prefixWord, tailWord_204220, baseEnd_204220] using wordTrace_append hprefix tailTrace_204220
  have hstable : (prefixWord ++ tailWord_204220).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204220).length < 2 ^ (prefixWord ++ tailWord_204220).sum := by decide
  have hdescent : baseEnd_204220 < baseStart_204220 := by decide
  rcases family_descends (prefixWord ++ tailWord_204220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204224 : List Nat := [2, 1, 1, 2, 3, 1, 3, 6]
def baseStart_204224 : Nat := 118140960795 + 204224 * 2 ^ 59
def prefixEnd_204224 : Nat := 4983230072969 + 3 ^ 40 * 204224 * 2
def baseEnd_204224 : Nat := 62142265590467677843435

theorem tailTrace_204224 : CollatzResearch.WordTrace tailWord_204224 prefixEnd_204224 62142265590467677843435 := by
  unfold tailWord_204224
  simp only [CollatzResearch.WordTrace]
  refine ⟨3724330606069400763737863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4965774141425867684983817 3724330606069400763737863)
  ·
    refine ⟨5586495909104101145606795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3724330606069400763737863 5586495909104101145606795)
    ·
      refine ⟨8379743863656151718410193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5586495909104101145606795 8379743863656151718410193)
      ·
        refine ⟨6284807897742113788807645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8379743863656151718410193 6284807897742113788807645)
        ·
          refine ⟨2356802961653292670802867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6284807897742113788807645 2356802961653292670802867)
          ·
            refine ⟨3535204442479939006204301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2356802961653292670802867 3535204442479939006204301)
            ·
              refine ⟨1325701665929977127326613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3535204442479939006204301 1325701665929977127326613)
              ·
                refine ⟨62142265590467677843435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1325701665929977127326613 62142265590467677843435)
                ·
                  rfl

theorem cell19_204224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 6].length) (baseStart_204224 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_204224 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_204224 prefixEnd_204224 := by exact prefixLift 204224
  have htrace : WordTrace (prefixWord ++ tailWord_204224) baseStart_204224 baseEnd_204224 := by
    simpa [prefixWord, tailWord_204224, baseEnd_204224] using wordTrace_append hprefix tailTrace_204224
  have hstable : (prefixWord ++ tailWord_204224).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204224).length < 2 ^ (prefixWord ++ tailWord_204224).sum := by decide
  have hdescent : baseEnd_204224 < baseStart_204224 := by decide
  rcases family_descends (prefixWord ++ tailWord_204224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204277 : List Nat := [1, 3, 5, 1, 1, 1, 3, 4]
def baseStart_204277 : Nat := 118140960795 + 204277 * 2 ^ 59
def prefixEnd_204277 : Nat := 4983230072969 + 3 ^ 40 * 204277 * 2
def baseEnd_204277 : Nat := 62158392686579258665513

theorem tailTrace_204277 : CollatzResearch.WordTrace tailWord_204277 prefixEnd_204277 62158392686579258665513 := by
  unfold tailWord_204277
  simp only [CollatzResearch.WordTrace]
  refine ⟨7450594280946791579155085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4967062853964527719436723 7450594280946791579155085)
  ·
    refine ⟨2793972855355046842183157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7450594280946791579155085 2793972855355046842183157)
    ·
      refine ⟨261934955189535641454671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2793972855355046842183157 261934955189535641454671)
      ·
        refine ⟨392902432784303462182007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261934955189535641454671 392902432784303462182007)
        ·
          refine ⟨589353649176455193273011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 392902432784303462182007 589353649176455193273011)
          ·
            refine ⟨884030473764682789909517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 589353649176455193273011 884030473764682789909517)
            ·
              refine ⟨331511427661756046216069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 884030473764682789909517 331511427661756046216069)
              ·
                refine ⟨62158392686579258665513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 331511427661756046216069 62158392686579258665513)
                ·
                  rfl

theorem cell19_204277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 3, 4].length) (baseStart_204277 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_204277 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_204277 prefixEnd_204277 := by exact prefixLift 204277
  have htrace : WordTrace (prefixWord ++ tailWord_204277) baseStart_204277 baseEnd_204277 := by
    simpa [prefixWord, tailWord_204277, baseEnd_204277] using wordTrace_append hprefix tailTrace_204277
  have hstable : (prefixWord ++ tailWord_204277).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204277).length < 2 ^ (prefixWord ++ tailWord_204277).sum := by decide
  have hdescent : baseEnd_204277 < baseStart_204277 := by decide
  rcases family_descends (prefixWord ++ tailWord_204277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204338 : List Nat := [3, 2, 1, 1, 2, 1, 1, 8]
def baseStart_204338 : Nat := 118140960795 + 204338 * 2 ^ 59
def prefixEnd_204338 : Nat := 4983230072969 + 3 ^ 40 * 204338 * 2
def baseEnd_204338 : Nat := 62176954061349191309791

theorem tailTrace_204338 : CollatzResearch.WordTrace tailWord_204338 prefixEnd_204338 62176954061349191309791 := by
  unfold tailWord_204338
  simp only [CollatzResearch.WordTrace]
  refine ⟨1863204783431449749281417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4968546089150532664750445 1863204783431449749281417)
  ·
    refine ⟨1397403587573587311961063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1863204783431449749281417 1397403587573587311961063)
    ·
      refine ⟨2096105381360380967941595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1397403587573587311961063 2096105381360380967941595)
      ·
        refine ⟨3144158072040571451912393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2096105381360380967941595 3144158072040571451912393)
        ·
          refine ⟨2358118554030428588934295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3144158072040571451912393 2358118554030428588934295)
          ·
            refine ⟨3537177831045642883401443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2358118554030428588934295 3537177831045642883401443)
            ·
              refine ⟨5305766746568464325102165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3537177831045642883401443 5305766746568464325102165)
              ·
                refine ⟨62176954061349191309791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5305766746568464325102165 62176954061349191309791)
                ·
                  rfl

theorem cell19_204338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 8].length) (baseStart_204338 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_204338 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_204338 prefixEnd_204338 := by exact prefixLift 204338
  have htrace : WordTrace (prefixWord ++ tailWord_204338) baseStart_204338 baseEnd_204338 := by
    simpa [prefixWord, tailWord_204338, baseEnd_204338] using wordTrace_append hprefix tailTrace_204338
  have hstable : (prefixWord ++ tailWord_204338).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204338).length < 2 ^ (prefixWord ++ tailWord_204338).sum := by decide
  have hdescent : baseEnd_204338 < baseStart_204338 := by decide
  rcases family_descends (prefixWord ++ tailWord_204338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204357 : List Nat := [1, 3, 1, 1, 1, 4, 3, 5]
def baseStart_204357 : Nat := 118140960795 + 204357 * 2 ^ 59
def prefixEnd_204357 : Nat := 4983230072969 + 3 ^ 40 * 204357 * 2
def baseEnd_204357 : Nat := 62182735473162776887517

theorem tailTrace_204357 : CollatzResearch.WordTrace tailWord_204357 prefixEnd_204357 62182735473162776887517 := by
  unfold tailWord_204357
  simp only [CollatzResearch.WordTrace]
  refine ⟨7453512120656965242067325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4969008080437976828044883 7453512120656965242067325)
  ·
    refine ⟨2795067045246361965775247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7453512120656965242067325 2795067045246361965775247)
    ·
      refine ⟨4192600567869542948662871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2795067045246361965775247 4192600567869542948662871)
      ·
        refine ⟨6288900851804314422994307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4192600567869542948662871 6288900851804314422994307)
        ·
          refine ⟨9433351277706471634491461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6288900851804314422994307 9433351277706471634491461)
          ·
            refine ⟨1768753364569963431467149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9433351277706471634491461 1768753364569963431467149)
            ·
              refine ⟨663282511713736286800181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1768753364569963431467149 663282511713736286800181)
              ·
                refine ⟨62182735473162776887517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 663282511713736286800181 62182735473162776887517)
                ·
                  rfl

theorem cell19_204357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 5].length) (baseStart_204357 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_204357 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_204357 prefixEnd_204357 := by exact prefixLift 204357
  have htrace : WordTrace (prefixWord ++ tailWord_204357) baseStart_204357 baseEnd_204357 := by
    simpa [prefixWord, tailWord_204357, baseEnd_204357] using wordTrace_append hprefix tailTrace_204357
  have hstable : (prefixWord ++ tailWord_204357).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204357).length < 2 ^ (prefixWord ++ tailWord_204357).sum := by decide
  have hdescent : baseEnd_204357 < baseStart_204357 := by decide
  rcases family_descends (prefixWord ++ tailWord_204357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204562 : List Nat := [3, 2, 4, 1, 1, 2, 2, 4]
def baseStart_204562 : Nat := 118140960795 + 204562 * 2 ^ 59
def prefixEnd_204562 : Nat := 4983230072969 + 3 ^ 40 * 204562 * 2
def baseEnd_204562 : Nat := 62245113863783042331403

theorem tailTrace_204562 : CollatzResearch.WordTrace tailWord_204562 prefixEnd_204562 62245113863783042331403 := by
  unfold tailWord_204562
  simp only [CollatzResearch.WordTrace]
  refine ⟨1865247271228571313319985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4973992723276190168853293 1865247271228571313319985)
  ·
    refine ⟨1398935453421428484989989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1865247271228571313319985 1398935453421428484989989)
    ·
      refine ⟨262300397516517840935623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1398935453421428484989989 262300397516517840935623)
      ·
        refine ⟨393450596274776761403435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262300397516517840935623 393450596274776761403435)
        ·
          refine ⟨590175894412165142105153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 393450596274776761403435 590175894412165142105153)
          ·
            refine ⟨442631920809123856578865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 590175894412165142105153 442631920809123856578865)
            ·
              refine ⟨331973940606842892434149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 442631920809123856578865 331973940606842892434149)
              ·
                refine ⟨62245113863783042331403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 331973940606842892434149 62245113863783042331403)
                ·
                  rfl

theorem cell19_204562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 2, 4].length) (baseStart_204562 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_204562 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_204562 prefixEnd_204562 := by exact prefixLift 204562
  have htrace : WordTrace (prefixWord ++ tailWord_204562) baseStart_204562 baseEnd_204562 := by
    simpa [prefixWord, tailWord_204562, baseEnd_204562] using wordTrace_append hprefix tailTrace_204562
  have hstable : (prefixWord ++ tailWord_204562).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204562).length < 2 ^ (prefixWord ++ tailWord_204562).sum := by decide
  have hdescent : baseEnd_204562 < baseStart_204562 := by decide
  rcases family_descends (prefixWord ++ tailWord_204562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204640 : List Nat := [2, 1, 1, 3, 3, 3, 3, 3]
def baseStart_204640 : Nat := 118140960795 + 204640 * 2 ^ 59
def prefixEnd_204640 : Nat := 4983230072969 + 3 ^ 40 * 204640 * 2
def baseEnd_204640 : Nat := 62268848080701972597857

theorem tailTrace_204640 : CollatzResearch.WordTrace tailWord_204640 prefixEnd_204640 62268848080701972597857 := by
  unfold tailWord_204640
  simp only [CollatzResearch.WordTrace]
  refine ⟨3731916989315852287309687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4975889319087803049746249 3731916989315852287309687)
  ·
    refine ⟨5597875483973778430964531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3731916989315852287309687 5597875483973778430964531)
    ·
      refine ⟨8396813225960667646446797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5597875483973778430964531 8396813225960667646446797)
      ·
        refine ⟨3148804959735250367417549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8396813225960667646446797 3148804959735250367417549)
        ·
          refine ⟨1180801859900718887781581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3148804959735250367417549 1180801859900718887781581)
          ·
            refine ⟨442800697462769582918093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1180801859900718887781581 442800697462769582918093)
            ·
              refine ⟨166050261548538593594285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 442800697462769582918093 166050261548538593594285)
              ·
                refine ⟨62268848080701972597857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 166050261548538593594285 62268848080701972597857)
                ·
                  rfl

theorem cell19_204640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 3, 3].length) (baseStart_204640 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_204640 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_204640 prefixEnd_204640 := by exact prefixLift 204640
  have htrace : WordTrace (prefixWord ++ tailWord_204640) baseStart_204640 baseEnd_204640 := by
    simpa [prefixWord, tailWord_204640, baseEnd_204640] using wordTrace_append hprefix tailTrace_204640
  have hstable : (prefixWord ++ tailWord_204640).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204640).length < 2 ^ (prefixWord ++ tailWord_204640).sum := by decide
  have hdescent : baseEnd_204640 < baseStart_204640 := by decide
  rcases family_descends (prefixWord ++ tailWord_204640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204661 : List Nat := [1, 3, 4, 1, 1, 1, 8]
def baseStart_204661 : Nat := 118140960795 + 204661 * 2 ^ 59
def prefixEnd_204661 : Nat := 4983230072969 + 3 ^ 40 * 204661 * 2
def baseEnd_204661 : Nat := 20758412687393382043711

theorem tailTrace_204661 : CollatzResearch.WordTrace tailWord_204661 prefixEnd_204661 20758412687393382043711 := by
  unfold tailWord_204661
  simp only [CollatzResearch.WordTrace]
  refine ⟨7464599911555625161133837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4976399941037083440755891 7464599911555625161133837)
  ·
    refine ⟨2799224966833359435425189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7464599911555625161133837 2799224966833359435425189)
    ·
      refine ⟨524854681281254894142223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2799224966833359435425189 524854681281254894142223)
      ·
        refine ⟨787282021921882341213335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 524854681281254894142223 787282021921882341213335)
        ·
          refine ⟨1180923032882823511820003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 787282021921882341213335 1180923032882823511820003)
          ·
            refine ⟨1771384549324235267730005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1180923032882823511820003 1771384549324235267730005)
            ·
              refine ⟨20758412687393382043711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1771384549324235267730005 20758412687393382043711)
              ·
                rfl

theorem cell19_204661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 8].length) (baseStart_204661 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_204661 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_204661 prefixEnd_204661 := by exact prefixLift 204661
  have htrace : WordTrace (prefixWord ++ tailWord_204661) baseStart_204661 baseEnd_204661 := by
    simpa [prefixWord, tailWord_204661, baseEnd_204661] using wordTrace_append hprefix tailTrace_204661
  have hstable : (prefixWord ++ tailWord_204661).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204661).length < 2 ^ (prefixWord ++ tailWord_204661).sum := by decide
  have hdescent : baseEnd_204661 < baseStart_204661 := by decide
  rcases family_descends (prefixWord ++ tailWord_204661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204712 : List Nat := [2, 1, 6, 2, 2, 1, 5]
def baseStart_204712 : Nat := 118140960795 + 204712 * 2 ^ 59
def prefixEnd_204712 : Nat := 4983230072969 + 3 ^ 40 * 204712 * 2
def baseEnd_204712 : Nat := 20763585529542379665887

theorem tailTrace_204712 : CollatzResearch.WordTrace tailWord_204712 prefixEnd_204712 20763585529542379665887 := by
  unfold tailWord_204712
  simp only [CollatzResearch.WordTrace]
  refine ⟨3733230017185430435620195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4977640022913907247493593 3733230017185430435620195)
  ·
    refine ⟨5599845025778145653430293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3733230017185430435620195 5599845025778145653430293)
    ·
      refine ⟨262492735583350577504545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 5599845025778145653430293 262492735583350577504545)
      ·
        refine ⟨196869551687512933128409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 262492735583350577504545 196869551687512933128409)
        ·
          refine ⟨147652163765634699846307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196869551687512933128409 147652163765634699846307)
          ·
            refine ⟨221478245648452049769461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147652163765634699846307 221478245648452049769461)
            ·
              refine ⟨20763585529542379665887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 221478245648452049769461 20763585529542379665887)
              ·
                rfl

theorem cell19_204712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 5].length) (baseStart_204712 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_204712 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_204712 prefixEnd_204712 := by exact prefixLift 204712
  have htrace : WordTrace (prefixWord ++ tailWord_204712) baseStart_204712 baseEnd_204712 := by
    simpa [prefixWord, tailWord_204712, baseEnd_204712] using wordTrace_append hprefix tailTrace_204712
  have hstable : (prefixWord ++ tailWord_204712).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204712).length < 2 ^ (prefixWord ++ tailWord_204712).sum := by decide
  have hdescent : baseEnd_204712 < baseStart_204712 := by decide
  rcases family_descends (prefixWord ++ tailWord_204712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204756 : List Nat := [2, 4, 1, 2, 1, 1, 1, 7]
def baseStart_204756 : Nat := 118140960795 + 204756 * 2 ^ 59
def prefixEnd_204756 : Nat := 4983230072969 + 3 ^ 40 * 204756 * 2
def baseEnd_204756 : Nat := 62304145121248074019763

theorem tailTrace_204756 : CollatzResearch.WordTrace tailWord_204756 prefixEnd_204756 62304145121248074019763 := by
  unfold tailWord_204756
  simp only [CollatzResearch.WordTrace]
  refine ⟨3734032423105728192921061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4978709897474304257228081 3734032423105728192921061)
  ·
    refine ⟨700131079332324036172699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3734032423105728192921061 700131079332324036172699)
    ·
      refine ⟨1050196618998486054259049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 700131079332324036172699 1050196618998486054259049)
      ·
        refine ⟨787647464248864540694287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1050196618998486054259049 787647464248864540694287)
        ·
          refine ⟨1181471196373296811041431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 787647464248864540694287 1181471196373296811041431)
          ·
            refine ⟨1772206794559945216562147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1181471196373296811041431 1772206794559945216562147)
            ·
              refine ⟨2658310191839917824843221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1772206794559945216562147 2658310191839917824843221)
              ·
                refine ⟨62304145121248074019763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2658310191839917824843221 62304145121248074019763)
                ·
                  rfl

theorem cell19_204756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 7].length) (baseStart_204756 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_204756 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_204756 prefixEnd_204756 := by exact prefixLift 204756
  have htrace : WordTrace (prefixWord ++ tailWord_204756) baseStart_204756 baseEnd_204756 := by
    simpa [prefixWord, tailWord_204756, baseEnd_204756] using wordTrace_append hprefix tailTrace_204756
  have hstable : (prefixWord ++ tailWord_204756).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204756).length < 2 ^ (prefixWord ++ tailWord_204756).sum := by decide
  have hdescent : baseEnd_204756 < baseStart_204756 := by decide
  rcases family_descends (prefixWord ++ tailWord_204756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204775 : List Nat := [1, 1, 5, 2, 3, 7]
def baseStart_204775 : Nat := 118140960795 + 204775 * 2 ^ 59
def prefixEnd_204775 : Nat := 4983230072969 + 3 ^ 40 * 204775 * 2
def baseEnd_204775 : Nat := 6923325170340184399721

theorem tailTrace_204775 : CollatzResearch.WordTrace tailWord_204775 prefixEnd_204775 6923325170340184399721 := by
  unfold tailWord_204775
  simp only [CollatzResearch.WordTrace]
  refine ⟨7468757833142622630783779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4979171888761748420522519 7468757833142622630783779)
  ·
    refine ⟨11203136749713933946175669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7468757833142622630783779 11203136749713933946175669)
    ·
      refine ⟨1050294070285681307453969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11203136749713933946175669 1050294070285681307453969)
      ·
        refine ⟨787720552714260980590477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1050294070285681307453969 787720552714260980590477)
        ·
          refine ⟨295395207267847867721429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 787720552714260980590477 295395207267847867721429)
          ·
            refine ⟨6923325170340184399721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 295395207267847867721429 6923325170340184399721)
            ·
              rfl

theorem cell19_204775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 7].length) (baseStart_204775 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_204775 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_204775 prefixEnd_204775 := by exact prefixLift 204775
  have htrace : WordTrace (prefixWord ++ tailWord_204775) baseStart_204775 baseEnd_204775 := by
    simpa [prefixWord, tailWord_204775, baseEnd_204775] using wordTrace_append hprefix tailTrace_204775
  have hstable : (prefixWord ++ tailWord_204775).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204775).length < 2 ^ (prefixWord ++ tailWord_204775).sum := by decide
  have hdescent : baseEnd_204775 < baseStart_204775 := by decide
  rcases family_descends (prefixWord ++ tailWord_204775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204790 : List Nat := [5, 1, 1, 1, 4, 2, 1, 4]
def baseStart_204790 : Nat := 118140960795 + 204790 * 2 ^ 59
def prefixEnd_204790 : Nat := 4983230072969 + 3 ^ 40 * 204790 * 2
def baseEnd_204790 : Nat := 62314490805546069264115

theorem tailTrace_204790 : CollatzResearch.WordTrace tailWord_204790 prefixEnd_204790 62314490805546069264115 := by
  unfold tailWord_204790
  simp only [CollatzResearch.WordTrace]
  refine ⟨466831558005517512036239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4979536618725520128386549 466831558005517512036239)
  ·
    refine ⟨700247337008276268054359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 466831558005517512036239 700247337008276268054359)
    ·
      refine ⟨1050371005512414402081539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 700247337008276268054359 1050371005512414402081539)
      ·
        refine ⟨1575556508268621603122309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1050371005512414402081539 1575556508268621603122309)
        ·
          refine ⟨295416845300366550585433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1575556508268621603122309 295416845300366550585433)
          ·
            refine ⟨221562633975274912939075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 295416845300366550585433 221562633975274912939075)
            ·
              refine ⟨332343950962912369408613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 221562633975274912939075 332343950962912369408613)
              ·
                refine ⟨62314490805546069264115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 332343950962912369408613 62314490805546069264115)
                ·
                  rfl

theorem cell19_204790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_204790 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_204790 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_204790 prefixEnd_204790 := by exact prefixLift 204790
  have htrace : WordTrace (prefixWord ++ tailWord_204790) baseStart_204790 baseEnd_204790 := by
    simpa [prefixWord, tailWord_204790, baseEnd_204790] using wordTrace_append hprefix tailTrace_204790
  have hstable : (prefixWord ++ tailWord_204790).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204790).length < 2 ^ (prefixWord ++ tailWord_204790).sum := by decide
  have hdescent : baseEnd_204790 < baseStart_204790 := by decide
  rcases family_descends (prefixWord ++ tailWord_204790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204906 : List Nat := [3, 1, 3, 2, 3, 1, 2, 4]
def baseStart_204906 : Nat := 118140960795 + 204906 * 2 ^ 59
def prefixEnd_204906 : Nat := 4983230072969 + 3 ^ 40 * 204906 * 2
def baseEnd_204906 : Nat := 62349787846092170686021

theorem tailTrace_204906 : CollatzResearch.WordTrace tailWord_204906 prefixEnd_204906 62349787846092170686021 := by
  unfold tailWord_204906
  simp only [CollatzResearch.WordTrace]
  refine ⟨1868383948917008000950643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4982357197112021335868381 1868383948917008000950643)
  ·
    refine ⟨2802575923375512001425965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1868383948917008000950643 2802575923375512001425965)
    ·
      refine ⟨1050965971265817000534737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2802575923375512001425965 1050965971265817000534737)
      ·
        refine ⟨788224478449362750401053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1050965971265817000534737 788224478449362750401053)
        ·
          refine ⟨295584179418511031400395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 788224478449362750401053 295584179418511031400395)
          ·
            refine ⟨443376269127766547100593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 295584179418511031400395 443376269127766547100593)
            ·
              refine ⟨332532201845824910325445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 443376269127766547100593 332532201845824910325445)
              ·
                refine ⟨62349787846092170686021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 332532201845824910325445 62349787846092170686021)
                ·
                  rfl

theorem cell19_204906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 2, 4].length) (baseStart_204906 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_204906 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_204906 prefixEnd_204906 := by exact prefixLift 204906
  have htrace : WordTrace (prefixWord ++ tailWord_204906) baseStart_204906 baseEnd_204906 := by
    simpa [prefixWord, tailWord_204906, baseEnd_204906] using wordTrace_append hprefix tailTrace_204906
  have hstable : (prefixWord ++ tailWord_204906).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204906).length < 2 ^ (prefixWord ++ tailWord_204906).sum := by decide
  have hdescent : baseEnd_204906 < baseStart_204906 := by decide
  rcases family_descends (prefixWord ++ tailWord_204906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204908 : List Nat := [2, 2, 1, 1, 3, 4, 2, 4]
def baseStart_204908 : Nat := 118140960795 + 204908 * 2 ^ 59
def prefixEnd_204908 : Nat := 4983230072969 + 3 ^ 40 * 204908 * 2
def baseEnd_204908 : Nat := 62350396415756758641571

theorem tailTrace_204908 : CollatzResearch.WordTrace tailWord_204908 prefixEnd_204908 62350396415756758641571 := by
  unfold tailWord_204908
  simp only [CollatzResearch.WordTrace]
  refine ⟨3736804370830393172687689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4982405827773857563583585 3736804370830393172687689)
  ·
    refine ⟨2802603278122794879515767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3736804370830393172687689 2802603278122794879515767)
    ·
      refine ⟨4203904917184192319273651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2802603278122794879515767 4203904917184192319273651)
      ·
        refine ⟨6305857375776288478910477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4203904917184192319273651 6305857375776288478910477)
        ·
          refine ⟨2364696515916108179591429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6305857375776288478910477 2364696515916108179591429)
          ·
            refine ⟨443380596734270283673393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2364696515916108179591429 443380596734270283673393)
            ·
              refine ⟨332535447550702712755045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 443380596734270283673393 332535447550702712755045)
              ·
                refine ⟨62350396415756758641571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 332535447550702712755045 62350396415756758641571)
                ·
                  rfl

theorem cell19_204908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 4].length) (baseStart_204908 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_204908 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_204908 prefixEnd_204908 := by exact prefixLift 204908
  have htrace : WordTrace (prefixWord ++ tailWord_204908) baseStart_204908 baseEnd_204908 := by
    simpa [prefixWord, tailWord_204908, baseEnd_204908] using wordTrace_append hprefix tailTrace_204908
  have hstable : (prefixWord ++ tailWord_204908).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204908).length < 2 ^ (prefixWord ++ tailWord_204908).sum := by decide
  have hdescent : baseEnd_204908 < baseStart_204908 := by decide
  rcases family_descends (prefixWord ++ tailWord_204908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204984 : List Nat := [2, 1, 2, 1, 2, 1, 7, 3]
def baseStart_204984 : Nat := 118140960795 + 204984 * 2 ^ 59
def prefixEnd_204984 : Nat := 4983230072969 + 3 ^ 40 * 204984 * 2
def baseEnd_204984 : Nat := 62373522063011100952475

theorem tailTrace_204984 : CollatzResearch.WordTrace tailWord_204984 prefixEnd_204984 62373522063011100952475 := by
  unfold tailWord_204984
  simp only [CollatzResearch.WordTrace]
  refine ⟨3738190344692725662571003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4984253792923634216761337 3738190344692725662571003)
  ·
    refine ⟨5607285517039088493856505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3738190344692725662571003 5607285517039088493856505)
    ·
      refine ⟨4205464137779316370392379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5607285517039088493856505 4205464137779316370392379)
      ·
        refine ⟨6308196206668974555588569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4205464137779316370392379 6308196206668974555588569)
        ·
          refine ⟨4731147155001730916691427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6308196206668974555588569 4731147155001730916691427)
          ·
            refine ⟨7096720732502596375037141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4731147155001730916691427 7096720732502596375037141)
            ·
              refine ⟨166329392168029602539933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 7096720732502596375037141 166329392168029602539933)
              ·
                refine ⟨62373522063011100952475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 166329392168029602539933 62373522063011100952475)
                ·
                  rfl

theorem cell19_204984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 7, 3].length) (baseStart_204984 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_204984 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_204984 prefixEnd_204984 := by exact prefixLift 204984
  have htrace : WordTrace (prefixWord ++ tailWord_204984) baseStart_204984 baseEnd_204984 := by
    simpa [prefixWord, tailWord_204984, baseEnd_204984] using wordTrace_append hprefix tailTrace_204984
  have hstable : (prefixWord ++ tailWord_204984).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204984).length < 2 ^ (prefixWord ++ tailWord_204984).sum := by decide
  have hdescent : baseEnd_204984 < baseStart_204984 := by decide
  rcases family_descends (prefixWord ++ tailWord_204984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204986 : List Nat := [3, 1, 1, 1, 2, 2, 2, 7]
def baseStart_204986 : Nat := 118140960795 + 204986 * 2 ^ 59
def prefixEnd_204986 : Nat := 4983230072969 + 3 ^ 40 * 204986 * 2
def baseEnd_204986 : Nat := 62374130632675688908025

theorem tailTrace_204986 : CollatzResearch.WordTrace tailWord_204986 prefixEnd_204986 62374130632675688908025 := by
  unfold tailWord_204986
  simp only [CollatzResearch.WordTrace]
  refine ⟨1869113408844551416678703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4984302423585470444476541 1869113408844551416678703)
  ·
    refine ⟨2803670113266827125018055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1869113408844551416678703 2803670113266827125018055)
    ·
      refine ⟨4205505169900240687527083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2803670113266827125018055 4205505169900240687527083)
      ·
        refine ⟨6308257754850361031290625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4205505169900240687527083 6308257754850361031290625)
        ·
          refine ⟨4731193316137770773467969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6308257754850361031290625 4731193316137770773467969)
          ·
            refine ⟨3548394987103328080100977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4731193316137770773467969 3548394987103328080100977)
            ·
              refine ⟨2661296240327496060075733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3548394987103328080100977 2661296240327496060075733)
              ·
                refine ⟨62374130632675688908025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2661296240327496060075733 62374130632675688908025)
                ·
                  rfl

theorem cell19_204986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 7].length) (baseStart_204986 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_204986 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_204986 prefixEnd_204986 := by exact prefixLift 204986
  have htrace : WordTrace (prefixWord ++ tailWord_204986) baseStart_204986 baseEnd_204986 := by
    simpa [prefixWord, tailWord_204986, baseEnd_204986] using wordTrace_append hprefix tailTrace_204986
  have hstable : (prefixWord ++ tailWord_204986).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204986).length < 2 ^ (prefixWord ++ tailWord_204986).sum := by decide
  have hdescent : baseEnd_204986 < baseStart_204986 := by decide
  rcases family_descends (prefixWord ++ tailWord_204986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205024 : List Nat := [2, 1, 1, 3, 1, 3, 2, 6]
def baseStart_205024 : Nat := 118140960795 + 205024 * 2 ^ 59
def prefixEnd_205024 : Nat := 4983230072969 + 3 ^ 40 * 205024 * 2
def baseEnd_205024 : Nat := 62385693456302860063477

theorem tailTrace_205024 : CollatzResearch.WordTrace tailWord_205024 prefixEnd_205024 62385693456302860063477 := by
  unfold tailWord_205024
  simp only [CollatzResearch.WordTrace]
  refine ⟨3738919804620269078299063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4985226406160358771065417 3738919804620269078299063)
  ·
    refine ⟨5608379706930403617448595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3738919804620269078299063 5608379706930403617448595)
    ·
      refine ⟨8412569560395605426172893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5608379706930403617448595 8412569560395605426172893)
      ·
        refine ⟨3154713585148352034814835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8412569560395605426172893 3154713585148352034814835)
        ·
          refine ⟨4732070377722528052222253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3154713585148352034814835 4732070377722528052222253)
          ·
            refine ⟨1774526391645948019583345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4732070377722528052222253 1774526391645948019583345)
            ·
              refine ⟨1330894793734461014687509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1774526391645948019583345 1330894793734461014687509)
              ·
                refine ⟨62385693456302860063477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1330894793734461014687509 62385693456302860063477)
                ·
                  rfl

theorem cell19_205024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 6].length) (baseStart_205024 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_205024 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_205024 prefixEnd_205024 := by exact prefixLift 205024
  have htrace : WordTrace (prefixWord ++ tailWord_205024) baseStart_205024 baseEnd_205024 := by
    simpa [prefixWord, tailWord_205024, baseEnd_205024] using wordTrace_append hprefix tailTrace_205024
  have hstable : (prefixWord ++ tailWord_205024).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205024).length < 2 ^ (prefixWord ++ tailWord_205024).sum := by decide
  have hdescent : baseEnd_205024 < baseStart_205024 := by decide
  rcases family_descends (prefixWord ++ tailWord_205024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205037 : List Nat := [1, 5, 1, 2, 3, 2, 2, 3]
def baseStart_205037 : Nat := 118140960795 + 205037 * 2 ^ 59
def prefixEnd_205037 : Nat := 4983230072969 + 3 ^ 40 * 205037 * 2
def baseEnd_205037 : Nat := 62389649159122681774553

theorem tailTrace_205037 : CollatzResearch.WordTrace tailWord_205037 prefixEnd_205037 62389649159122681774553 := by
  unfold tailWord_205037
  simp only [CollatzResearch.WordTrace]
  refine ⟨7478313758193441376821365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4985542505462294251214243 7478313758193441376821365)
  ·
    refine ⟨701091914830635129077003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7478313758193441376821365 701091914830635129077003)
    ·
      refine ⟨1051637872245952693615505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 701091914830635129077003 1051637872245952693615505)
      ·
        refine ⟨788728404184464520211629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1051637872245952693615505 788728404184464520211629)
        ·
          refine ⟨295773151569174195079361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 788728404184464520211629 295773151569174195079361)
          ·
            refine ⟨221829863676880646309521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 295773151569174195079361 221829863676880646309521)
            ·
              refine ⟨166372397757660484732141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 221829863676880646309521 166372397757660484732141)
              ·
                refine ⟨62389649159122681774553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 166372397757660484732141 62389649159122681774553)
                ·
                  rfl

theorem cell19_205037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 2, 3].length) (baseStart_205037 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_205037 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_205037 prefixEnd_205037 := by exact prefixLift 205037
  have htrace : WordTrace (prefixWord ++ tailWord_205037) baseStart_205037 baseEnd_205037 := by
    simpa [prefixWord, tailWord_205037, baseEnd_205037] using wordTrace_append hprefix tailTrace_205037
  have hstable : (prefixWord ++ tailWord_205037).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205037).length < 2 ^ (prefixWord ++ tailWord_205037).sum := by decide
  have hdescent : baseEnd_205037 < baseStart_205037 := by decide
  rcases family_descends (prefixWord ++ tailWord_205037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205039 : List Nat := [1, 1, 2, 1, 6, 3, 2, 3]
def baseStart_205039 : Nat := 118140960795 + 205039 * 2 ^ 59
def prefixEnd_205039 : Nat := 4983230072969 + 3 ^ 40 * 205039 * 2
def baseEnd_205039 : Nat := 62390257728787269730103

theorem tailTrace_205039 : CollatzResearch.WordTrace tailWord_205039 prefixEnd_205039 62390257728787269730103 := by
  unfold tailWord_205039
  simp only [CollatzResearch.WordTrace]
  refine ⟨7478386704186195718394171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4985591136124130478929447 7478386704186195718394171)
  ·
    refine ⟨11217580056279293577591257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7478386704186195718394171 11217580056279293577591257)
    ·
      refine ⟨8413185042209470183193443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11217580056279293577591257 8413185042209470183193443)
      ·
        refine ⟨12619777563314205274790165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8413185042209470183193443 12619777563314205274790165)
        ·
          refine ⟨591552073280353372255789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 12619777563314205274790165 591552073280353372255789)
          ·
            refine ⟨221832027480132514595921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 591552073280353372255789 221832027480132514595921)
            ·
              refine ⟨166374020610099385946941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 221832027480132514595921 166374020610099385946941)
              ·
                refine ⟨62390257728787269730103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 166374020610099385946941 62390257728787269730103)
                ·
                  rfl

theorem cell19_205039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 2, 3].length) (baseStart_205039 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_205039 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_205039 prefixEnd_205039 := by exact prefixLift 205039
  have htrace : WordTrace (prefixWord ++ tailWord_205039) baseStart_205039 baseEnd_205039 := by
    simpa [prefixWord, tailWord_205039, baseEnd_205039] using wordTrace_append hprefix tailTrace_205039
  have hstable : (prefixWord ++ tailWord_205039).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205039).length < 2 ^ (prefixWord ++ tailWord_205039).sum := by decide
  have hdescent : baseEnd_205039 < baseStart_205039 := by decide
  rcases family_descends (prefixWord ++ tailWord_205039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205041 : List Nat := [1, 2, 2, 2, 2, 1, 6, 3]
def baseStart_205041 : Nat := 118140960795 + 205041 * 2 ^ 59
def prefixEnd_205041 : Nat := 4983230072969 + 3 ^ 40 * 205041 * 2
def baseEnd_205041 : Nat := 62390866298451857685653

theorem tailTrace_205041 : CollatzResearch.WordTrace tailWord_205041 prefixEnd_205041 62390866298451857685653 := by
  unfold tailWord_205041
  simp only [CollatzResearch.WordTrace]
  refine ⟨7478459650178950059966977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4985639766785966706644651 7478459650178950059966977)
  ·
    refine ⟨5608844737634212544975233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7478459650178950059966977 5608844737634212544975233)
    ·
      refine ⟨4206633553225659408731425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5608844737634212544975233 4206633553225659408731425)
      ·
        refine ⟨3154975164919244556548569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4206633553225659408731425 3154975164919244556548569)
        ·
          refine ⟨2366231373689433417411427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3154975164919244556548569 2366231373689433417411427)
          ·
            refine ⟨3549347060534150126117141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2366231373689433417411427 3549347060534150126117141)
            ·
              refine ⟨166375643462538287161741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3549347060534150126117141 166375643462538287161741)
              ·
                refine ⟨62390866298451857685653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 166375643462538287161741 62390866298451857685653)
                ·
                  rfl

theorem cell19_205041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 6, 3].length) (baseStart_205041 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_205041 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_205041 prefixEnd_205041 := by exact prefixLift 205041
  have htrace : WordTrace (prefixWord ++ tailWord_205041) baseStart_205041 baseEnd_205041 := by
    simpa [prefixWord, tailWord_205041, baseEnd_205041] using wordTrace_append hprefix tailTrace_205041
  have hstable : (prefixWord ++ tailWord_205041).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205041).length < 2 ^ (prefixWord ++ tailWord_205041).sum := by decide
  have hdescent : baseEnd_205041 < baseStart_205041 := by decide
  rcases family_descends (prefixWord ++ tailWord_205041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205043 : List Nat := [1, 1, 1, 2, 2, 4, 3, 5]
def baseStart_205043 : Nat := 118140960795 + 205043 * 2 ^ 59
def prefixEnd_205043 : Nat := 4983230072969 + 3 ^ 40 * 205043 * 2
def baseEnd_205043 : Nat := 62391474868116445641203

theorem tailTrace_205043 : CollatzResearch.WordTrace tailWord_205043 prefixEnd_205043 62391474868116445641203 := by
  unfold tailWord_205043
  simp only [CollatzResearch.WordTrace]
  refine ⟨7478532596171704401539783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4985688397447802934359855 7478532596171704401539783)
  ·
    refine ⟨11217798894257556602309675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7478532596171704401539783 11217798894257556602309675)
    ·
      refine ⟨16826698341386334903464513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11217798894257556602309675 16826698341386334903464513)
      ·
        refine ⟨12620023756039751177598385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16826698341386334903464513 12620023756039751177598385)
        ·
          refine ⟨9465017817029813383198789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12620023756039751177598385 9465017817029813383198789)
          ·
            refine ⟨1774690840693090009349773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9465017817029813383198789 1774690840693090009349773)
            ·
              refine ⟨665509065259908753506165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1774690840693090009349773 665509065259908753506165)
              ·
                refine ⟨62391474868116445641203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 665509065259908753506165 62391474868116445641203)
                ·
                  rfl

theorem cell19_205043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 5].length) (baseStart_205043 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_205043 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_205043 prefixEnd_205043 := by exact prefixLift 205043
  have htrace : WordTrace (prefixWord ++ tailWord_205043) baseStart_205043 baseEnd_205043 := by
    simpa [prefixWord, tailWord_205043, baseEnd_205043] using wordTrace_append hprefix tailTrace_205043
  have hstable : (prefixWord ++ tailWord_205043).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205043).length < 2 ^ (prefixWord ++ tailWord_205043).sum := by decide
  have hdescent : baseEnd_205043 < baseStart_205043 := by decide
  rcases family_descends (prefixWord ++ tailWord_205043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205058 : List Nat := [3, 4, 1, 1, 2, 3, 5]
def baseStart_205058 : Nat := 118140960795 + 205058 * 2 ^ 59
def prefixEnd_205058 : Nat := 4983230072969 + 3 ^ 40 * 205058 * 2
def baseEnd_205058 : Nat := 20798679713533618435943

theorem tailTrace_205058 : CollatzResearch.WordTrace tailWord_205058 prefixEnd_205058 20798679713533618435943 := by
  unfold tailWord_205058
  simp only [CollatzResearch.WordTrace]
  refine ⟨1869769922779340490833957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4986053127411574642223885 1869769922779340490833957)
  ·
    refine ⟨350581860521126342031367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1869769922779340490833957 350581860521126342031367)
    ·
      refine ⟨525872790781689513047051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350581860521126342031367 525872790781689513047051)
      ·
        refine ⟨788809186172534269570577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 525872790781689513047051 788809186172534269570577)
        ·
          refine ⟨591606889629400702177933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 788809186172534269570577 591606889629400702177933)
          ·
            refine ⟨221852583611025263316725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 591606889629400702177933 221852583611025263316725)
            ·
              refine ⟨20798679713533618435943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 221852583611025263316725 20798679713533618435943)
              ·
                rfl

theorem cell19_205058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 5].length) (baseStart_205058 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_205058 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_205058 prefixEnd_205058 := by exact prefixLift 205058
  have htrace : WordTrace (prefixWord ++ tailWord_205058) baseStart_205058 baseEnd_205058 := by
    simpa [prefixWord, tailWord_205058, baseEnd_205058] using wordTrace_append hprefix tailTrace_205058
  have hstable : (prefixWord ++ tailWord_205058).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205058).length < 2 ^ (prefixWord ++ tailWord_205058).sum := by decide
  have hdescent : baseEnd_205058 < baseStart_205058 := by decide
  rcases family_descends (prefixWord ++ tailWord_205058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205079 : List Nat := [1, 1, 3, 4, 1, 3, 2, 4]
def baseStart_205079 : Nat := 118140960795 + 205079 * 2 ^ 59
def prefixEnd_205079 : Nat := 4983230072969 + 3 ^ 40 * 205079 * 2
def baseEnd_205079 : Nat := 62402429122079028841105

theorem tailTrace_205079 : CollatzResearch.WordTrace tailWord_205079 prefixEnd_205079 62402429122079028841105 := by
  unfold tailWord_205079
  simp only [CollatzResearch.WordTrace]
  refine ⟨7479845624041282549850291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4986563749360855033233527 7479845624041282549850291)
  ·
    refine ⟨11219768436061923824775437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7479845624041282549850291 11219768436061923824775437)
    ·
      refine ⟨4207413163523221434290789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11219768436061923824775437 4207413163523221434290789)
      ·
        refine ⟨788889968160604018929523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4207413163523221434290789 788889968160604018929523)
        ·
          refine ⟨1183334952240906028394285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 788889968160604018929523 1183334952240906028394285)
          ·
            refine ⟨443750607090339760647857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1183334952240906028394285 443750607090339760647857)
            ·
              refine ⟨332812955317754820485893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 443750607090339760647857 332812955317754820485893)
              ·
                refine ⟨62402429122079028841105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 332812955317754820485893 62402429122079028841105)
                ·
                  rfl

theorem cell19_205079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2, 4].length) (baseStart_205079 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_205079 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_205079 prefixEnd_205079 := by exact prefixLift 205079
  have htrace : WordTrace (prefixWord ++ tailWord_205079) baseStart_205079 baseEnd_205079 := by
    simpa [prefixWord, tailWord_205079, baseEnd_205079] using wordTrace_append hprefix tailTrace_205079
  have hstable : (prefixWord ++ tailWord_205079).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205079).length < 2 ^ (prefixWord ++ tailWord_205079).sum := by decide
  have hdescent : baseEnd_205079 < baseStart_205079 := by decide
  rcases family_descends (prefixWord ++ tailWord_205079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205100 : List Nat := [2, 2, 1, 1, 1, 3, 4, 5]
def baseStart_205100 : Nat := 118140960795 + 205100 * 2 ^ 59
def prefixEnd_205100 : Nat := 4983230072969 + 3 ^ 40 * 205100 * 2
def baseEnd_205100 : Nat := 62408819103557202374381

theorem tailTrace_205100 : CollatzResearch.WordTrace tailWord_205100 prefixEnd_205100 62408819103557202374381 := by
  unfold tailWord_205100
  simp only [CollatzResearch.WordTrace]
  refine ⟨3740305778482601568182377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4987074371310135424243169 3740305778482601568182377)
  ·
    refine ⟨2805229333861951176136783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3740305778482601568182377 2805229333861951176136783)
    ·
      refine ⟨4207844000792926764205175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2805229333861951176136783 4207844000792926764205175)
      ·
        refine ⟨6311766001189390146307763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4207844000792926764205175 6311766001189390146307763)
        ·
          refine ⟨9467649001784085219461645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6311766001189390146307763 9467649001784085219461645)
          ·
            refine ⟨3550368375669031957298117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9467649001784085219461645 3550368375669031957298117)
            ·
              refine ⟨665694070437943491993397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3550368375669031957298117 665694070437943491993397)
              ·
                refine ⟨62408819103557202374381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 665694070437943491993397 62408819103557202374381)
                ·
                  rfl

theorem cell19_205100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 5].length) (baseStart_205100 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_205100 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_205100 prefixEnd_205100 := by exact prefixLift 205100
  have htrace : WordTrace (prefixWord ++ tailWord_205100) baseStart_205100 baseEnd_205100 := by
    simpa [prefixWord, tailWord_205100, baseEnd_205100] using wordTrace_append hprefix tailTrace_205100
  have hstable : (prefixWord ++ tailWord_205100).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205100).length < 2 ^ (prefixWord ++ tailWord_205100).sum := by decide
  have hdescent : baseEnd_205100 < baseStart_205100 := by decide
  rcases family_descends (prefixWord ++ tailWord_205100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205136 : List Nat := [2, 1, 1, 1, 1, 8, 1, 4]
def baseStart_205136 : Nat := 118140960795 + 205136 * 2 ^ 59
def prefixEnd_205136 : Nat := 4983230072969 + 3 ^ 40 * 205136 * 2
def baseEnd_205136 : Nat := 62419773357519785574283

theorem tailTrace_205136 : CollatzResearch.WordTrace tailWord_205136 prefixEnd_205136 62419773357519785574283 := by
  unfold tailWord_205136
  simp only [CollatzResearch.WordTrace]
  refine ⟨3740962292417390642337631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4987949723223187523116841 3740962292417390642337631)
  ·
    refine ⟨5611443438626085963506447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3740962292417390642337631 5611443438626085963506447)
    ·
      refine ⟨8417165157939128945259671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5611443438626085963506447 8417165157939128945259671)
      ·
        refine ⟨12625747736908693417889507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8417165157939128945259671 12625747736908693417889507)
        ·
          refine ⟨18938621605363040126834261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12625747736908693417889507 18938621605363040126834261)
          ·
            refine ⟨221936971937848126486339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 18938621605363040126834261 221936971937848126486339)
            ·
              refine ⟨332905457906772189729509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 221936971937848126486339 332905457906772189729509)
              ·
                refine ⟨62419773357519785574283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 332905457906772189729509 62419773357519785574283)
                ·
                  rfl

theorem cell19_205136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 1, 4].length) (baseStart_205136 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_205136 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_205136 prefixEnd_205136 := by exact prefixLift 205136
  have htrace : WordTrace (prefixWord ++ tailWord_205136) baseStart_205136 baseEnd_205136 := by
    simpa [prefixWord, tailWord_205136, baseEnd_205136] using wordTrace_append hprefix tailTrace_205136
  have hstable : (prefixWord ++ tailWord_205136).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205136).length < 2 ^ (prefixWord ++ tailWord_205136).sum := by decide
  have hdescent : baseEnd_205136 < baseStart_205136 := by decide
  rcases family_descends (prefixWord ++ tailWord_205136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205155 : List Nat := [1, 1, 1, 5, 2, 1, 5, 3]
def baseStart_205155 : Nat := 118140960795 + 205155 * 2 ^ 59
def prefixEnd_205155 : Nat := 4983230072969 + 3 ^ 40 * 205155 * 2
def baseEnd_205155 : Nat := 62425554769333371152009

theorem tailTrace_205155 : CollatzResearch.WordTrace tailWord_205155 prefixEnd_205155 62425554769333371152009 := by
  unfold tailWord_205155
  simp only [CollatzResearch.WordTrace]
  refine ⟨7482617571765947529616919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4988411714510631686411279 7482617571765947529616919)
  ·
    refine ⟨11223926357648921294425379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7482617571765947529616919 11223926357648921294425379)
    ·
      refine ⟨16835889536473381941638069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11223926357648921294425379 16835889536473381941638069)
      ·
        refine ⟨1578364644044379557028569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16835889536473381941638069 1578364644044379557028569)
        ·
          refine ⟨1183773483033284667771427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1578364644044379557028569 1183773483033284667771427)
          ·
            refine ⟨1775660224549927001657141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1183773483033284667771427 1775660224549927001657141)
            ·
              refine ⟨166468146051555656405357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1775660224549927001657141 166468146051555656405357)
              ·
                refine ⟨62425554769333371152009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 166468146051555656405357 62425554769333371152009)
                ·
                  rfl

theorem cell19_205155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 5, 3].length) (baseStart_205155 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_205155 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_205155 prefixEnd_205155 := by exact prefixLift 205155
  have htrace : WordTrace (prefixWord ++ tailWord_205155) baseStart_205155 baseEnd_205155 := by
    simpa [prefixWord, tailWord_205155, baseEnd_205155] using wordTrace_append hprefix tailTrace_205155
  have hstable : (prefixWord ++ tailWord_205155).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205155).length < 2 ^ (prefixWord ++ tailWord_205155).sum := by decide
  have hdescent : baseEnd_205155 < baseStart_205155 := by decide
  rcases family_descends (prefixWord ++ tailWord_205155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205206 : List Nat := [5, 3, 1, 2, 1, 1, 1, 5]
def baseStart_205206 : Nat := 118140960795 + 205206 * 2 ^ 59
def prefixEnd_205206 : Nat := 4983230072969 + 3 ^ 40 * 205206 * 2
def baseEnd_205206 : Nat := 62441073295780364018537

theorem tailTrace_205206 : CollatzResearch.WordTrace tailWord_205206 prefixEnd_205206 62441073295780364018537 := by
  unfold tailWord_205206
  simp only [CollatzResearch.WordTrace]
  refine ⟨467779855911323952482717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4989651796387455493148981 467779855911323952482717)
  ·
    refine ⟨175417445966746482181019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 467779855911323952482717 175417445966746482181019)
    ·
      refine ⟨263126168950119723271529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175417445966746482181019 263126168950119723271529)
      ·
        refine ⟨197344626712589792453647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 263126168950119723271529 197344626712589792453647)
        ·
          refine ⟨296016940068884688680471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197344626712589792453647 296016940068884688680471)
          ·
            refine ⟨444025410103327033020707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 296016940068884688680471 444025410103327033020707)
            ·
              refine ⟨666038115154990549531061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 444025410103327033020707 666038115154990549531061)
              ·
                refine ⟨62441073295780364018537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 666038115154990549531061 62441073295780364018537)
                ·
                  rfl

theorem cell19_205206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 5].length) (baseStart_205206 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_205206 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_205206 prefixEnd_205206 := by exact prefixLift 205206
  have htrace : WordTrace (prefixWord ++ tailWord_205206) baseStart_205206 baseEnd_205206 := by
    simpa [prefixWord, tailWord_205206, baseEnd_205206] using wordTrace_append hprefix tailTrace_205206
  have hstable : (prefixWord ++ tailWord_205206).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205206).length < 2 ^ (prefixWord ++ tailWord_205206).sum := by decide
  have hdescent : baseEnd_205206 < baseStart_205206 := by decide
  rcases family_descends (prefixWord ++ tailWord_205206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205210 : List Nat := [3, 1, 1, 4, 1, 4, 2, 3]
def baseStart_205210 : Nat := 118140960795 + 205210 * 2 ^ 59
def prefixEnd_205210 : Nat := 4983230072969 + 3 ^ 40 * 205210 * 2
def baseEnd_205210 : Nat := 62442290435109539929637

theorem tailTrace_205210 : CollatzResearch.WordTrace tailWord_205210 prefixEnd_205210 62442290435109539929637 := by
  unfold tailWord_205210
  simp only [CollatzResearch.WordTrace]
  refine ⟨1871155896641672980717271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4989749057711127948579389 1871155896641672980717271)
  ·
    refine ⟨2806733844962509471075907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1871155896641672980717271 2806733844962509471075907)
    ·
      refine ⟨4210100767443764206613861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2806733844962509471075907 4210100767443764206613861)
      ·
        refine ⟨789393893895705788740099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4210100767443764206613861 789393893895705788740099)
        ·
          refine ⟨1184090840843558683110149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 789393893895705788740099 1184090840843558683110149)
          ·
            refine ⟨222017032658167253083153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1184090840843558683110149 222017032658167253083153)
            ·
              refine ⟨166512774493625439812365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 222017032658167253083153 166512774493625439812365)
              ·
                refine ⟨62442290435109539929637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 166512774493625439812365 62442290435109539929637)
                ·
                  rfl

theorem cell19_205210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 2, 3].length) (baseStart_205210 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_205210 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_205210 prefixEnd_205210 := by exact prefixLift 205210
  have htrace : WordTrace (prefixWord ++ tailWord_205210) baseStart_205210 baseEnd_205210 := by
    simpa [prefixWord, tailWord_205210, baseEnd_205210] using wordTrace_append hprefix tailTrace_205210
  have hstable : (prefixWord ++ tailWord_205210).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205210).length < 2 ^ (prefixWord ++ tailWord_205210).sum := by decide
  have hdescent : baseEnd_205210 < baseStart_205210 := by decide
  rcases family_descends (prefixWord ++ tailWord_205210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205229 : List Nat := [1, 5, 2, 2, 2, 2, 5]
def baseStart_205229 : Nat := 118140960795 + 205229 * 2 ^ 59
def prefixEnd_205229 : Nat := 4983230072969 + 3 ^ 40 * 205229 * 2
def baseEnd_205229 : Nat := 20816023948974375169121

theorem tailTrace_205229 : CollatzResearch.WordTrace tailWord_205229 prefixEnd_205229 20816023948974375169121 := by
  unfold tailWord_205229
  simp only [CollatzResearch.WordTrace]
  refine ⟨7485316573497858167810741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4990211048998572111873827 7485316573497858167810741)
  ·
    refine ⟨701748428765424203232257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7485316573497858167810741 701748428765424203232257)
    ·
      refine ⟨526311321574068152424193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 701748428765424203232257 526311321574068152424193)
      ·
        refine ⟨394733491180551114318145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 526311321574068152424193 394733491180551114318145)
        ·
          refine ⟨296050118385413335738609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 394733491180551114318145 296050118385413335738609)
          ·
            refine ⟨222037588789060001803957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 296050118385413335738609 222037588789060001803957)
            ·
              refine ⟨20816023948974375169121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 222037588789060001803957 20816023948974375169121)
              ·
                rfl

theorem cell19_205229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 5].length) (baseStart_205229 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_205229 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_205229 prefixEnd_205229 := by exact prefixLift 205229
  have htrace : WordTrace (prefixWord ++ tailWord_205229) baseStart_205229 baseEnd_205229 := by
    simpa [prefixWord, tailWord_205229, baseEnd_205229] using wordTrace_append hprefix tailTrace_205229
  have hstable : (prefixWord ++ tailWord_205229).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205229).length < 2 ^ (prefixWord ++ tailWord_205229).sum := by decide
  have hdescent : baseEnd_205229 < baseStart_205229 := by decide
  rcases family_descends (prefixWord ++ tailWord_205229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205233 : List Nat := [1, 2, 2, 4, 1, 2, 7]
def baseStart_205233 : Nat := 118140960795 + 205233 * 2 ^ 59
def prefixEnd_205233 : Nat := 4983230072969 + 3 ^ 40 * 205233 * 2
def baseEnd_205233 : Nat := 20816429662084100472821

theorem tailTrace_205233 : CollatzResearch.WordTrace tailWord_205233 prefixEnd_205233 20816429662084100472821 := by
  unfold tailWord_205233
  simp only [CollatzResearch.WordTrace]
  refine ⟨7485462465483366850956353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4990308310322244567304235 7485462465483366850956353)
  ·
    refine ⟨5614096849112525138217265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7485462465483366850956353 5614096849112525138217265)
    ·
      refine ⟨4210572636834393853662949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5614096849112525138217265 4210572636834393853662949)
      ·
        refine ⟨789482369406448847561803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4210572636834393853662949 789482369406448847561803)
        ·
          refine ⟨1184223554109673271342705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 789482369406448847561803 1184223554109673271342705)
          ·
            refine ⟨888167665582254953507029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1184223554109673271342705 888167665582254953507029)
            ·
              refine ⟨20816429662084100472821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 888167665582254953507029 20816429662084100472821)
              ·
                rfl

theorem cell19_205233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 7].length) (baseStart_205233 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_205233 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_205233 prefixEnd_205233 := by exact prefixLift 205233
  have htrace : WordTrace (prefixWord ++ tailWord_205233) baseStart_205233 baseEnd_205233 := by
    simpa [prefixWord, tailWord_205233, baseEnd_205233] using wordTrace_append hprefix tailTrace_205233
  have hstable : (prefixWord ++ tailWord_205233).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205233).length < 2 ^ (prefixWord ++ tailWord_205233).sum := by decide
  have hdescent : baseEnd_205233 < baseStart_205233 := by decide
  rcases family_descends (prefixWord ++ tailWord_205233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205290 : List Nat := [3, 1, 3, 1, 3, 8]
def baseStart_205290 : Nat := 118140960795 + 205290 * 2 ^ 59
def prefixEnd_205290 : Nat := 4983230072969 + 3 ^ 40 * 205290 * 2
def baseEnd_205290 : Nat := 6940737024632562016849

theorem tailTrace_205290 : CollatzResearch.WordTrace tailWord_205290 prefixEnd_205290 6940737024632562016849 := by
  unfold tailWord_205290
  simp only [CollatzResearch.WordTrace]
  refine ⟨1871885356569216396445331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4991694284184577057187549 1871885356569216396445331)
  ·
    refine ⟨2807828034853824594667997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1871885356569216396445331 2807828034853824594667997)
    ·
      refine ⟨1052935513070184223000499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2807828034853824594667997 1052935513070184223000499)
      ·
        refine ⟨1579403269605276334500749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1052935513070184223000499 1579403269605276334500749)
        ·
          refine ⟨592276226101978625437781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1579403269605276334500749 592276226101978625437781)
          ·
            refine ⟨6940737024632562016849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 592276226101978625437781 6940737024632562016849)
            ·
              rfl

theorem cell19_205290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 8].length) (baseStart_205290 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_205290 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_205290 prefixEnd_205290 := by exact prefixLift 205290
  have htrace : WordTrace (prefixWord ++ tailWord_205290) baseStart_205290 baseEnd_205290 := by
    simpa [prefixWord, tailWord_205290, baseEnd_205290] using wordTrace_append hprefix tailTrace_205290
  have hstable : (prefixWord ++ tailWord_205290).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205290).length < 2 ^ (prefixWord ++ tailWord_205290).sum := by decide
  have hdescent : baseEnd_205290 < baseStart_205290 := by decide
  rcases family_descends (prefixWord ++ tailWord_205290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205347 : List Nat := [1, 1, 1, 4, 4, 2, 6]
def baseStart_205347 : Nat := 118140960795 + 205347 * 2 ^ 59
def prefixEnd_205347 : Nat := 4983230072969 + 3 ^ 40 * 205347 * 2
def baseEnd_205347 : Nat := 20827992485711271628273

theorem tailTrace_205347 : CollatzResearch.WordTrace tailWord_205347 prefixEnd_205347 20827992485711271628273 := by
  unfold tailWord_205347
  simp only [CollatzResearch.WordTrace]
  refine ⟨7489620387070364320606295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4993080258046909547070863 7489620387070364320606295)
  ·
    refine ⟨11234430580605546480909443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7489620387070364320606295 11234430580605546480909443)
    ·
      refine ⟨16851645870908319721364165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11234430580605546480909443 16851645870908319721364165)
      ·
        refine ⟨3159683600795309947755781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16851645870908319721364165 3159683600795309947755781)
        ·
          refine ⟨592440675149120615204209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3159683600795309947755781 592440675149120615204209)
          ·
            refine ⟨444330506361840461403157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 592440675149120615204209 444330506361840461403157)
            ·
              refine ⟨20827992485711271628273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 444330506361840461403157 20827992485711271628273)
              ·
                rfl

theorem cell19_205347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 6].length) (baseStart_205347 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_205347 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_205347 prefixEnd_205347 := by exact prefixLift 205347
  have htrace : WordTrace (prefixWord ++ tailWord_205347) baseStart_205347 baseEnd_205347 := by
    simpa [prefixWord, tailWord_205347, baseEnd_205347] using wordTrace_append hprefix tailTrace_205347
  have hstable : (prefixWord ++ tailWord_205347).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205347).length < 2 ^ (prefixWord ++ tailWord_205347).sum := by decide
  have hdescent : baseEnd_205347 < baseStart_205347 := by decide
  rcases family_descends (prefixWord ++ tailWord_205347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205383 : List Nat := [1, 1, 4, 1, 4, 1, 4, 3]
def baseStart_205383 : Nat := 118140960795 + 205383 * 2 ^ 59
def prefixEnd_205383 : Nat := 4983230072969 + 3 ^ 40 * 205383 * 2
def baseEnd_205383 : Nat := 62494931711096398084721

theorem tailTrace_205383 : CollatzResearch.WordTrace tailWord_205383 prefixEnd_205383 62494931711096398084721 := by
  unfold tailWord_205383
  simp only [CollatzResearch.WordTrace]
  refine ⟨7490933414939942468916803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4993955609959961645944535 7490933414939942468916803)
  ·
    refine ⟨11236400122409913703375205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7490933414939942468916803 11236400122409913703375205)
    ·
      refine ⟨2106825022951858819382851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11236400122409913703375205 2106825022951858819382851)
      ·
        refine ⟨3160237534427788229074277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2106825022951858819382851 3160237534427788229074277)
        ·
          refine ⟨592544537705210292951427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3160237534427788229074277 592544537705210292951427)
          ·
            refine ⟨888816806557815439427141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 592544537705210292951427 888816806557815439427141)
            ·
              refine ⟨166653151229590394892589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 888816806557815439427141 166653151229590394892589)
              ·
                refine ⟨62494931711096398084721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 166653151229590394892589 62494931711096398084721)
                ·
                  rfl

theorem cell19_205383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 4, 3].length) (baseStart_205383 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_205383 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_205383 prefixEnd_205383 := by exact prefixLift 205383
  have htrace : WordTrace (prefixWord ++ tailWord_205383) baseStart_205383 baseEnd_205383 := by
    simpa [prefixWord, tailWord_205383, baseEnd_205383] using wordTrace_append hprefix tailTrace_205383
  have hstable : (prefixWord ++ tailWord_205383).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205383).length < 2 ^ (prefixWord ++ tailWord_205383).sum := by decide
  have hdescent : baseEnd_205383 < baseStart_205383 := by decide
  rcases family_descends (prefixWord ++ tailWord_205383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205421 : List Nat := [1, 5, 1, 1, 3, 2, 2, 4]
def baseStart_205421 : Nat := 118140960795 + 205421 * 2 ^ 59
def prefixEnd_205421 : Nat := 4983230072969 + 3 ^ 40 * 205421 * 2
def baseEnd_205421 : Nat := 62506494534723569240173

theorem tailTrace_205421 : CollatzResearch.WordTrace tailWord_205421 prefixEnd_205421 62506494534723569240173 := by
  unfold tailWord_205421
  simp only [CollatzResearch.WordTrace]
  refine ⟨7492319388802274958800117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4994879592534849972533411 7492319388802274958800117)
  ·
    refine ⟨702404942700213277387511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7492319388802274958800117 702404942700213277387511)
    ·
      refine ⟨1053607414050319916081267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 702404942700213277387511 1053607414050319916081267)
      ·
        refine ⟨1580411121075479874121901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1053607414050319916081267 1580411121075479874121901)
        ·
          refine ⟨592654170403304952795713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1580411121075479874121901 592654170403304952795713)
          ·
            refine ⟨444490627802478714596785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 592654170403304952795713 444490627802478714596785)
            ·
              refine ⟨333367970851859035947589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 444490627802478714596785 333367970851859035947589)
              ·
                refine ⟨62506494534723569240173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 333367970851859035947589 62506494534723569240173)
                ·
                  rfl

theorem cell19_205421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2, 4].length) (baseStart_205421 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_205421 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_205421 prefixEnd_205421 := by exact prefixLift 205421
  have htrace : WordTrace (prefixWord ++ tailWord_205421) baseStart_205421 baseEnd_205421 := by
    simpa [prefixWord, tailWord_205421, baseEnd_205421] using wordTrace_append hprefix tailTrace_205421
  have hstable : (prefixWord ++ tailWord_205421).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205421).length < 2 ^ (prefixWord ++ tailWord_205421).sum := by decide
  have hdescent : baseEnd_205421 < baseStart_205421 := by decide
  rcases family_descends (prefixWord ++ tailWord_205421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205518 : List Nat := [4, 1, 1, 1, 3, 3, 6]
def baseStart_205518 : Nat := 118140960795 + 205518 * 2 ^ 59
def prefixEnd_205518 : Nat := 4983230072969 + 3 ^ 40 * 205518 * 2
def baseEnd_205518 : Nat := 20845336721152028361451

theorem tailTrace_205518 : CollatzResearch.WordTrace tailWord_205518 prefixEnd_205518 20845336721152028361451 := by
  unfold tailWord_205518
  simp only [CollatzResearch.WordTrace]
  refine ⟨936982158681357565635151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4997238179633907016720805 936982158681357565635151)
  ·
    refine ⟨1405473238022036348452727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 936982158681357565635151 1405473238022036348452727)
    ·
      refine ⟨2108209857033054522679091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1405473238022036348452727 2108209857033054522679091)
      ·
        refine ⟨3162314785549581784018637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2108209857033054522679091 3162314785549581784018637)
        ·
          refine ⟨1185868044581093169006989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3162314785549581784018637 1185868044581093169006989)
          ·
            refine ⟨444700516717909938377621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1185868044581093169006989 444700516717909938377621)
            ·
              refine ⟨20845336721152028361451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 444700516717909938377621 20845336721152028361451)
              ·
                rfl

theorem cell19_205518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 6].length) (baseStart_205518 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_205518 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_205518 prefixEnd_205518 := by exact prefixLift 205518
  have htrace : WordTrace (prefixWord ++ tailWord_205518) baseStart_205518 baseEnd_205518 := by
    simpa [prefixWord, tailWord_205518, baseEnd_205518] using wordTrace_append hprefix tailTrace_205518
  have hstable : (prefixWord ++ tailWord_205518).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205518).length < 2 ^ (prefixWord ++ tailWord_205518).sum := by decide
  have hdescent : baseEnd_205518 < baseStart_205518 := by decide
  rcases family_descends (prefixWord ++ tailWord_205518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205554 : List Nat := [3, 2, 1, 3, 1, 2, 4, 3]
def baseStart_205554 : Nat := 118140960795 + 205554 * 2 ^ 59
def prefixEnd_205554 : Nat := 4983230072969 + 3 ^ 40 * 205554 * 2
def baseEnd_205554 : Nat := 62546964417418668284255

theorem tailTrace_205554 : CollatzResearch.WordTrace tailWord_205554 prefixEnd_205554 62546964417418668284255 := by
  unfold tailWord_205554
  simp only [CollatzResearch.WordTrace]
  refine ⟨1874292574330109668347929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4998113531546959115594477 1874292574330109668347929)
  ·
    refine ⟨1405719430747582251260947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1874292574330109668347929 1405719430747582251260947)
    ·
      refine ⟨2108579146121373376891421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1405719430747582251260947 2108579146121373376891421)
      ·
        refine ⟨790717179795515016334283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2108579146121373376891421 790717179795515016334283)
        ·
          refine ⟨1186075769693272524501425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 790717179795515016334283 1186075769693272524501425)
          ·
            refine ⟨889556827269954393376069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1186075769693272524501425 889556827269954393376069)
            ·
              refine ⟨166791905113116448758013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 889556827269954393376069 166791905113116448758013)
              ·
                refine ⟨62546964417418668284255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 166791905113116448758013 62546964417418668284255)
                ·
                  rfl

theorem cell19_205554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 4, 3].length) (baseStart_205554 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_205554 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_205554 prefixEnd_205554 := by exact prefixLift 205554
  have htrace : WordTrace (prefixWord ++ tailWord_205554) baseStart_205554 baseEnd_205554 := by
    simpa [prefixWord, tailWord_205554, baseEnd_205554] using wordTrace_append hprefix tailTrace_205554
  have hstable : (prefixWord ++ tailWord_205554).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205554).length < 2 ^ (prefixWord ++ tailWord_205554).sum := by decide
  have hdescent : baseEnd_205554 < baseStart_205554 := by decide
  rcases family_descends (prefixWord ++ tailWord_205554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205575 : List Nat := [1, 1, 4, 4, 1, 1, 7]
def baseStart_205575 : Nat := 118140960795 + 205575 * 2 ^ 59
def prefixEnd_205575 : Nat := 4983230072969 + 3 ^ 40 * 205575 * 2
def baseEnd_205575 : Nat := 20851118132965613939177

theorem tailTrace_205575 : CollatzResearch.WordTrace tailWord_205575 prefixEnd_205575 20851118132965613939177 := by
  unfold tailWord_205575
  simp only [CollatzResearch.WordTrace]
  refine ⟨7497936230244359259906179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4998624153496239506604119 7497936230244359259906179)
  ·
    refine ⟨11246904345366538889859269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7497936230244359259906179 11246904345366538889859269)
    ·
      refine ⟨2108794564756226041848613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11246904345366538889859269 2108794564756226041848613)
      ·
        refine ⟨395398980891792382846615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2108794564756226041848613 395398980891792382846615)
        ·
          refine ⟨593098471337688574269923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 395398980891792382846615 593098471337688574269923)
          ·
            refine ⟨889647707006532861404885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 593098471337688574269923 889647707006532861404885)
            ·
              refine ⟨20851118132965613939177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 889647707006532861404885 20851118132965613939177)
              ·
                rfl

theorem cell19_205575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 7].length) (baseStart_205575 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_205575 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_205575 prefixEnd_205575 := by exact prefixLift 205575
  have htrace : WordTrace (prefixWord ++ tailWord_205575) baseStart_205575 baseEnd_205575 := by
    simpa [prefixWord, tailWord_205575, baseEnd_205575] using wordTrace_append hprefix tailTrace_205575
  have hstable : (prefixWord ++ tailWord_205575).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205575).length < 2 ^ (prefixWord ++ tailWord_205575).sum := by decide
  have hdescent : baseEnd_205575 < baseStart_205575 := by decide
  rcases family_descends (prefixWord ++ tailWord_205575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205577 : List Nat := [1, 2, 1, 1, 3, 2, 9]
def baseStart_205577 : Nat := 118140960795 + 205577 * 2 ^ 59
def prefixEnd_205577 : Nat := 4983230072969 + 3 ^ 40 * 205577 * 2
def baseEnd_205577 : Nat := 20851320989520476591027

theorem tailTrace_205577 : CollatzResearch.WordTrace tailWord_205577 prefixEnd_205577 20851320989520476591027 := by
  unfold tailWord_205577
  simp only [CollatzResearch.WordTrace]
  refine ⟨7498009176237113601478985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4998672784158075734319323 7498009176237113601478985)
  ·
    refine ⟨5623506882177835201109239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7498009176237113601478985 5623506882177835201109239)
    ·
      refine ⟨8435260323266752801663859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5623506882177835201109239 8435260323266752801663859)
      ·
        refine ⟨12652890484900129202495789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8435260323266752801663859 12652890484900129202495789)
        ·
          refine ⟨4744833931837548450935921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12652890484900129202495789 4744833931837548450935921)
          ·
            refine ⟨3558625448878161338201941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4744833931837548450935921 3558625448878161338201941)
            ·
              refine ⟨20851320989520476591027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3558625448878161338201941 20851320989520476591027)
              ·
                rfl

theorem cell19_205577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 9].length) (baseStart_205577 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_205577 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_205577 prefixEnd_205577 := by exact prefixLift 205577
  have htrace : WordTrace (prefixWord ++ tailWord_205577) baseStart_205577 baseEnd_205577 := by
    simpa [prefixWord, tailWord_205577, baseEnd_205577] using wordTrace_append hprefix tailTrace_205577
  have hstable : (prefixWord ++ tailWord_205577).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205577).length < 2 ^ (prefixWord ++ tailWord_205577).sum := by decide
  have hdescent : baseEnd_205577 < baseStart_205577 := by decide
  rcases family_descends (prefixWord ++ tailWord_205577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205594 : List Nat := [3, 1, 1, 3, 2, 1, 4, 4]
def baseStart_205594 : Nat := 118140960795 + 205594 * 2 ^ 59
def prefixEnd_205594 : Nat := 4983230072969 + 3 ^ 40 * 205594 * 2
def baseEnd_205594 : Nat := 62559135810710427395257

theorem tailTrace_205594 : CollatzResearch.WordTrace tailWord_205594 prefixEnd_205594 62559135810710427395257 := by
  unfold tailWord_205594
  simp only [CollatzResearch.WordTrace]
  refine ⟨1874657304293881376211959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4999086144783683669898557 1874657304293881376211959)
  ·
    refine ⟨2811985956440822064317939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1874657304293881376211959 2811985956440822064317939)
    ·
      refine ⟨4217978934661233096476909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2811985956440822064317939 4217978934661233096476909)
      ·
        refine ⟨1581742100497962411178841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4217978934661233096476909 1581742100497962411178841)
        ·
          refine ⟨1186306575373471808384131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1581742100497962411178841 1186306575373471808384131)
          ·
            refine ⟨1779459863060207712576197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1186306575373471808384131 1779459863060207712576197)
            ·
              refine ⟨333648724323788946108037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1779459863060207712576197 333648724323788946108037)
              ·
                refine ⟨62559135810710427395257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 333648724323788946108037 62559135810710427395257)
                ·
                  rfl

theorem cell19_205594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4, 4].length) (baseStart_205594 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_205594 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_205594 prefixEnd_205594 := by exact prefixLift 205594
  have htrace : WordTrace (prefixWord ++ tailWord_205594) baseStart_205594 baseEnd_205594 := by
    simpa [prefixWord, tailWord_205594, baseEnd_205594] using wordTrace_append hprefix tailTrace_205594
  have hstable : (prefixWord ++ tailWord_205594).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205594).length < 2 ^ (prefixWord ++ tailWord_205594).sum := by decide
  have hdescent : baseEnd_205594 < baseStart_205594 := by decide
  rcases family_descends (prefixWord ++ tailWord_205594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205630 : List Nat := [4, 2, 1, 2, 4, 6]
def baseStart_205630 : Nat := 118140960795 + 205630 * 2 ^ 59
def prefixEnd_205630 : Nat := 4983230072969 + 3 ^ 40 * 205630 * 2
def baseEnd_205630 : Nat := 6952232229408112288351

theorem tailTrace_205630 : CollatzResearch.WordTrace tailWord_205630 prefixEnd_205630 6952232229408112288351 := by
  unfold tailWord_205630
  simp only [CollatzResearch.WordTrace]
  refine ⟨937492780630637956644793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4999961496696735768772229 937492780630637956644793)
  ·
    refine ⟨703119585472978467483595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 937492780630637956644793 703119585472978467483595)
    ·
      refine ⟨1054679378209467701225393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 703119585472978467483595 1054679378209467701225393)
      ·
        refine ⟨791009533657100775919045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1054679378209467701225393 791009533657100775919045)
        ·
          refine ⟨148314287560706395484821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 791009533657100775919045 148314287560706395484821)
          ·
            refine ⟨6952232229408112288351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 148314287560706395484821 6952232229408112288351)
            ·
              rfl

theorem cell19_205630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 6].length) (baseStart_205630 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_205630 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_205630 prefixEnd_205630 := by exact prefixLift 205630
  have htrace : WordTrace (prefixWord ++ tailWord_205630) baseStart_205630 baseEnd_205630 := by
    simpa [prefixWord, tailWord_205630, baseEnd_205630] using wordTrace_append hprefix tailTrace_205630
  have hstable : (prefixWord ++ tailWord_205630).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205630).length < 2 ^ (prefixWord ++ tailWord_205630).sum := by decide
  have hdescent : baseEnd_205630 < baseStart_205630 := by decide
  rcases family_descends (prefixWord ++ tailWord_205630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205645 : List Nat := [1, 6, 1, 2, 3, 1, 1, 4]
def baseStart_205645 : Nat := 118140960795 + 205645 * 2 ^ 59
def prefixEnd_205645 : Nat := 4983230072969 + 3 ^ 40 * 205645 * 2
def baseEnd_205645 : Nat := 62574654337157420261785

theorem tailTrace_205645 : CollatzResearch.WordTrace tailWord_205645 prefixEnd_205645 62574654337157420261785 := by
  unfold tailWord_205645
  simp only [CollatzResearch.WordTrace]
  refine ⟨7500489339990761214954389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5000326226660507476636259 7500489339990761214954389)
  ·
    refine ⟨351585437812066931950987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 7500489339990761214954389 351585437812066931950987)
    ·
      refine ⟨527378156718100397926481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 351585437812066931950987 527378156718100397926481)
      ·
        refine ⟨395533617538575298444861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 527378156718100397926481 395533617538575298444861)
        ·
          refine ⟨148325106576965736916823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 395533617538575298444861 148325106576965736916823)
          ·
            refine ⟨222487659865448605375235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148325106576965736916823 222487659865448605375235)
            ·
              refine ⟨333731489798172908062853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 222487659865448605375235 333731489798172908062853)
              ·
                refine ⟨62574654337157420261785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 333731489798172908062853 62574654337157420261785)
                ·
                  rfl

theorem cell19_205645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 1, 4].length) (baseStart_205645 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_205645 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_205645 prefixEnd_205645 := by exact prefixLift 205645
  have htrace : WordTrace (prefixWord ++ tailWord_205645) baseStart_205645 baseEnd_205645 := by
    simpa [prefixWord, tailWord_205645, baseEnd_205645] using wordTrace_append hprefix tailTrace_205645
  have hstable : (prefixWord ++ tailWord_205645).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205645).length < 2 ^ (prefixWord ++ tailWord_205645).sum := by decide
  have hdescent : baseEnd_205645 < baseStart_205645 := by decide
  rcases family_descends (prefixWord ++ tailWord_205645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205649 : List Nat := [1, 2, 2, 1, 6, 2, 1, 4]
def baseStart_205649 : Nat := 118140960795 + 205649 * 2 ^ 59
def prefixEnd_205649 : Nat := 4983230072969 + 3 ^ 40 * 205649 * 2
def baseEnd_205649 : Nat := 62575871476486596172885

theorem tailTrace_205649 : CollatzResearch.WordTrace tailWord_205649 prefixEnd_205649 62575871476486596172885 := by
  unfold tailWord_205649
  simp only [CollatzResearch.WordTrace]
  refine ⟨7500635231976269898100001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5000423487984179932066667 7500635231976269898100001)
  ·
    refine ⟨5625476423982202423575001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7500635231976269898100001 5625476423982202423575001)
    ·
      refine ⟨4219107317986651817681251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5625476423982202423575001 4219107317986651817681251)
      ·
        refine ⟨6328660976979977726521877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4219107317986651817681251 6328660976979977726521877)
        ·
          refine ⟨296655983295936455930713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 6328660976979977726521877 296655983295936455930713)
          ·
            refine ⟨222491987471952341948035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 296655983295936455930713 222491987471952341948035)
            ·
              refine ⟨333737981207928512922053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 222491987471952341948035 333737981207928512922053)
              ·
                refine ⟨62575871476486596172885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 333737981207928512922053 62575871476486596172885)
                ·
                  rfl

theorem cell19_205649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 1, 4].length) (baseStart_205649 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_205649 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_205649 prefixEnd_205649 := by exact prefixLift 205649
  have htrace : WordTrace (prefixWord ++ tailWord_205649) baseStart_205649 baseEnd_205649 := by
    simpa [prefixWord, tailWord_205649, baseEnd_205649] using wordTrace_append hprefix tailTrace_205649
  have hstable : (prefixWord ++ tailWord_205649).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205649).length < 2 ^ (prefixWord ++ tailWord_205649).sum := by decide
  have hdescent : baseEnd_205649 < baseStart_205649 := by decide
  rcases family_descends (prefixWord ++ tailWord_205649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205666 : List Nat := [3, 3, 2, 1, 3, 1, 3, 3]
def baseStart_205666 : Nat := 118140960795 + 205666 * 2 ^ 59
def prefixEnd_205666 : Nat := 4983230072969 + 3 ^ 40 * 205666 * 2
def baseEnd_205666 : Nat := 62581044318635593795061

theorem tailTrace_205666 : CollatzResearch.WordTrace tailWord_205666 prefixEnd_205666 62581044318635593795061 := by
  unfold tailWord_205666
  simp only [CollatzResearch.WordTrace]
  refine ⟨1875313818228670450367213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5000836848609787867645901 1875313818228670450367213)
  ·
    refine ⟨703242681835751418887705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1875313818228670450367213 703242681835751418887705)
    ·
      refine ⟨527432011376813564165779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 703242681835751418887705 527432011376813564165779)
      ·
        refine ⟨791148017065220346248669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 527432011376813564165779 791148017065220346248669)
        ·
          refine ⟨296680506399457629843251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 791148017065220346248669 296680506399457629843251)
          ·
            refine ⟨445020759599186444764877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 296680506399457629843251 445020759599186444764877)
            ·
              refine ⟨166882784849694916786829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 445020759599186444764877 166882784849694916786829)
              ·
                refine ⟨62581044318635593795061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 166882784849694916786829 62581044318635593795061)
                ·
                  rfl

theorem cell19_205666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 3, 3].length) (baseStart_205666 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_205666 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_205666 prefixEnd_205666 := by exact prefixLift 205666
  have htrace : WordTrace (prefixWord ++ tailWord_205666) baseStart_205666 baseEnd_205666 := by
    simpa [prefixWord, tailWord_205666, baseEnd_205666] using wordTrace_append hprefix tailTrace_205666
  have hstable : (prefixWord ++ tailWord_205666).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205666).length < 2 ^ (prefixWord ++ tailWord_205666).sum := by decide
  have hdescent : baseEnd_205666 < baseStart_205666 := by decide
  rcases family_descends (prefixWord ++ tailWord_205666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205668 : List Nat := [2, 3, 1, 1, 4, 2, 3, 3]
def baseStart_205668 : Nat := 118140960795 + 205668 * 2 ^ 59
def prefixEnd_205668 : Nat := 4983230072969 + 3 ^ 40 * 205668 * 2
def baseEnd_205668 : Nat := 62581652888300181750611

theorem tailTrace_205668 : CollatzResearch.WordTrace tailWord_205668 prefixEnd_205668 62581652888300181750611 := by
  unfold tailWord_205668
  simp only [CollatzResearch.WordTrace]
  refine ⟨3750664109453718071520829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5000885479271624095361105 3750664109453718071520829)
  ·
    refine ⟨1406499041045144276820311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3750664109453718071520829 1406499041045144276820311)
    ·
      refine ⟨2109748561567716415230467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1406499041045144276820311 2109748561567716415230467)
      ·
        refine ⟨3164622842351574622845701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2109748561567716415230467 3164622842351574622845701)
        ·
          refine ⟨593366782940920241783569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3164622842351574622845701 593366782940920241783569)
          ·
            refine ⟨445025087205690181337677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 593366782940920241783569 445025087205690181337677)
            ·
              refine ⟨166884407702133818001629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 445025087205690181337677 166884407702133818001629)
              ·
                refine ⟨62581652888300181750611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 166884407702133818001629 62581652888300181750611)
                ·
                  rfl

theorem cell19_205668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 3, 3].length) (baseStart_205668 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_205668 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_205668 prefixEnd_205668 := by exact prefixLift 205668
  have htrace : WordTrace (prefixWord ++ tailWord_205668) baseStart_205668 baseEnd_205668 := by
    simpa [prefixWord, tailWord_205668, baseEnd_205668] using wordTrace_append hprefix tailTrace_205668
  have hstable : (prefixWord ++ tailWord_205668).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205668).length < 2 ^ (prefixWord ++ tailWord_205668).sum := by decide
  have hdescent : baseEnd_205668 < baseStart_205668 := by decide
  rcases family_descends (prefixWord ++ tailWord_205668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205727 : List Nat := [1, 1, 2, 5, 2, 2, 1, 5]
def baseStart_205727 : Nat := 118140960795 + 205727 * 2 ^ 59
def prefixEnd_205727 : Nat := 4983230072969 + 3 ^ 40 * 205727 * 2
def baseEnd_205727 : Nat := 62599605693405526439339

theorem tailTrace_205727 : CollatzResearch.WordTrace tailWord_205727 prefixEnd_205727 62599605693405526439339 := by
  unfold tailWord_205727
  simp only [CollatzResearch.WordTrace]
  refine ⟨7503480125693689219439435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5002320083795792812959623 7503480125693689219439435)
  ·
    refine ⟨11255220188540533829159153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7503480125693689219439435 11255220188540533829159153)
    ·
      refine ⟨8441415141405400371869365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11255220188540533829159153 8441415141405400371869365)
      ·
        refine ⟨791382669506756284862753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8441415141405400371869365 791382669506756284862753)
        ·
          refine ⟨593537002130067213647065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 791382669506756284862753 593537002130067213647065)
          ·
            refine ⟨445152751597550410235299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 593537002130067213647065 445152751597550410235299)
            ·
              refine ⟨667729127396325615352949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 445152751597550410235299 667729127396325615352949)
              ·
                refine ⟨62599605693405526439339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 667729127396325615352949 62599605693405526439339)
                ·
                  rfl

theorem cell19_205727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 5].length) (baseStart_205727 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_205727 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_205727 prefixEnd_205727 := by exact prefixLift 205727
  have htrace : WordTrace (prefixWord ++ tailWord_205727) baseStart_205727 baseEnd_205727 := by
    simpa [prefixWord, tailWord_205727, baseEnd_205727] using wordTrace_append hprefix tailTrace_205727
  have hstable : (prefixWord ++ tailWord_205727).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205727).length < 2 ^ (prefixWord ++ tailWord_205727).sum := by decide
  have hdescent : baseEnd_205727 < baseStart_205727 := by decide
  rcases family_descends (prefixWord ++ tailWord_205727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205767 : List Nat := [1, 1, 4, 1, 1, 2, 3, 6]
def baseStart_205767 : Nat := 118140960795 + 205767 * 2 ^ 59
def prefixEnd_205767 : Nat := 4983230072969 + 3 ^ 40 * 205767 * 2
def baseEnd_205767 : Nat := 62611777086697285550341

theorem tailTrace_205767 : CollatzResearch.WordTrace tailWord_205767 prefixEnd_205767 62611777086697285550341 := by
  unfold tailWord_205767
  simp only [CollatzResearch.WordTrace]
  refine ⟨7504939045548776050895555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5003292697032517367263703 7504939045548776050895555)
  ·
    refine ⟨11257408568323164076343333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7504939045548776050895555 11257408568323164076343333)
    ·
      refine ⟨2110764106560593264314375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11257408568323164076343333 2110764106560593264314375)
      ·
        refine ⟨3166146159840889896471563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2110764106560593264314375 3166146159840889896471563)
        ·
          refine ⟨4749219239761334844707345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3166146159840889896471563 4749219239761334844707345)
          ·
            refine ⟨3561914429821001133530509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4749219239761334844707345 3561914429821001133530509)
            ·
              refine ⟨1335717911182875425073941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3561914429821001133530509 1335717911182875425073941)
              ·
                refine ⟨62611777086697285550341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1335717911182875425073941 62611777086697285550341)
                ·
                  rfl

theorem cell19_205767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 6].length) (baseStart_205767 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_205767 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_205767 prefixEnd_205767 := by exact prefixLift 205767
  have htrace : WordTrace (prefixWord ++ tailWord_205767) baseStart_205767 baseEnd_205767 := by
    simpa [prefixWord, tailWord_205767, baseEnd_205767] using wordTrace_append hprefix tailTrace_205767
  have hstable : (prefixWord ++ tailWord_205767).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205767).length < 2 ^ (prefixWord ++ tailWord_205767).sum := by decide
  have hdescent : baseEnd_205767 < baseStart_205767 := by decide
  rcases family_descends (prefixWord ++ tailWord_205767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205782 : List Nat := [5, 2, 1, 1, 2, 1, 2, 5]
def baseStart_205782 : Nat := 118140960795 + 205782 * 2 ^ 59
def prefixEnd_205782 : Nat := 4983230072969 + 3 ^ 40 * 205782 * 2
def baseEnd_205782 : Nat := 62616341359181695216967

theorem tailTrace_205782 : CollatzResearch.WordTrace tailWord_205782 prefixEnd_205782 62616341359181695216967 := by
  unfold tailWord_205782
  simp only [CollatzResearch.WordTrace]
  refine ⟨469092883780902100793225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5003657426996289075127733 469092883780902100793225)
  ·
    refine ⟨351819662835676575594919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 469092883780902100793225 351819662835676575594919)
    ·
      refine ⟨527729494253514863392379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 351819662835676575594919 527729494253514863392379)
      ·
        refine ⟨791594241380272295088569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 527729494253514863392379 791594241380272295088569)
        ·
          refine ⟨593695681035204221316427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 791594241380272295088569 593695681035204221316427)
          ·
            refine ⟨890543521552806331974641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 593695681035204221316427 890543521552806331974641)
            ·
              refine ⟨667907641164604748980981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 890543521552806331974641 667907641164604748980981)
              ·
                refine ⟨62616341359181695216967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 667907641164604748980981 62616341359181695216967)
                ·
                  rfl

theorem cell19_205782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_205782 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_205782 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_205782 prefixEnd_205782 := by exact prefixLift 205782
  have htrace : WordTrace (prefixWord ++ tailWord_205782) baseStart_205782 baseEnd_205782 := by
    simpa [prefixWord, tailWord_205782, baseEnd_205782] using wordTrace_append hprefix tailTrace_205782
  have hstable : (prefixWord ++ tailWord_205782).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205782).length < 2 ^ (prefixWord ++ tailWord_205782).sum := by decide
  have hdescent : baseEnd_205782 < baseStart_205782 := by decide
  rcases family_descends (prefixWord ++ tailWord_205782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205805 : List Nat := [1, 5, 1, 12]
def baseStart_205805 : Nat := 118140960795 + 205805 * 2 ^ 59
def prefixEnd_205805 : Nat := 4983230072969 + 3 ^ 40 * 205805 * 2
def baseEnd_205805 : Nat := 773127653213882181553

theorem tailTrace_205805 : CollatzResearch.WordTrace tailWord_205805 prefixEnd_205805 773127653213882181553 := by
  unfold tailWord_205805
  simp only [CollatzResearch.WordTrace]
  refine ⟨7506325019411108540778869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5004216679607405693852579 7506325019411108540778869)
  ·
    refine ⟨703717970569791425698019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7506325019411108540778869 703717970569791425698019)
    ·
      refine ⟨1055576955854687138547029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 703717970569791425698019 1055576955854687138547029)
      ·
        refine ⟨773127653213882181553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 12 1055576955854687138547029 773127653213882181553)
        ·
          rfl

theorem cell19_205805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 12].length) (baseStart_205805 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_205805 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_205805 prefixEnd_205805 := by exact prefixLift 205805
  have htrace : WordTrace (prefixWord ++ tailWord_205805) baseStart_205805 baseEnd_205805 := by
    simpa [prefixWord, tailWord_205805, baseEnd_205805] using wordTrace_append hprefix tailTrace_205805
  have hstable : (prefixWord ++ tailWord_205805).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205805).length < 2 ^ (prefixWord ++ tailWord_205805).sum := by decide
  have hdescent : baseEnd_205805 < baseStart_205805 := by decide
  rcases family_descends (prefixWord ++ tailWord_205805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205812 : List Nat := [2, 6, 2, 1, 2, 1, 1, 4]
def baseStart_205812 : Nat := 118140960795 + 205812 * 2 ^ 59
def prefixEnd_205812 : Nat := 4983230072969 + 3 ^ 40 * 205812 * 2
def baseEnd_205812 : Nat := 62625469904150514550219

theorem tailTrace_205812 : CollatzResearch.WordTrace tailWord_205812 prefixEnd_205812 62625469904150514550219 := by
  unfold tailWord_205812
  simp only [CollatzResearch.WordTrace]
  refine ⟨3753290165192874368141845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5004386886923832490855793 3753290165192874368141845)
  ·
    refine ⟨175935476493415986006649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 3753290165192874368141845 175935476493415986006649)
    ·
      refine ⟨131951607370061989504987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175935476493415986006649 131951607370061989504987)
      ·
        refine ⟨197927411055092984257481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131951607370061989504987 197927411055092984257481)
        ·
          refine ⟨148445558291319738193111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197927411055092984257481 148445558291319738193111)
          ·
            refine ⟨222668337436979607289667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148445558291319738193111 222668337436979607289667)
            ·
              refine ⟨334002506155469410934501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 222668337436979607289667 334002506155469410934501)
              ·
                refine ⟨62625469904150514550219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 334002506155469410934501 62625469904150514550219)
                ·
                  rfl

theorem cell19_205812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 1, 4].length) (baseStart_205812 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_205812 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_205812 prefixEnd_205812 := by exact prefixLift 205812
  have htrace : WordTrace (prefixWord ++ tailWord_205812) baseStart_205812 baseEnd_205812 := by
    simpa [prefixWord, tailWord_205812, baseEnd_205812] using wordTrace_append hprefix tailTrace_205812
  have hstable : (prefixWord ++ tailWord_205812).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205812).length < 2 ^ (prefixWord ++ tailWord_205812).sum := by decide
  have hdescent : baseEnd_205812 < baseStart_205812 := by decide
  rcases family_descends (prefixWord ++ tailWord_205812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205860 : List Nat := [2, 3, 1, 4, 1, 2, 6]
def baseStart_205860 : Nat := 118140960795 + 205860 * 2 ^ 59
def prefixEnd_205860 : Nat := 4983230072969 + 3 ^ 40 * 205860 * 2
def baseEnd_205860 : Nat := 20880025192033541827807

theorem tailTrace_205860 : CollatzResearch.WordTrace tailWord_205860 prefixEnd_205860 20880025192033541827807 := by
  unfold tailWord_205860
  simp only [CollatzResearch.WordTrace]
  refine ⟨3754165517105926467015517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5005554022807901956020689 3754165517105926467015517)
  ·
    refine ⟨1407812068914722425130819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3754165517105926467015517 1407812068914722425130819)
    ·
      refine ⟨2111718103372083637696229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1407812068914722425130819 2111718103372083637696229)
      ·
        refine ⟨395947144382265682068043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2111718103372083637696229 395947144382265682068043)
        ·
          refine ⟨593920716573398523102065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 395947144382265682068043 593920716573398523102065)
          ·
            refine ⟨445440537430048892326549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 593920716573398523102065 445440537430048892326549)
            ·
              refine ⟨20880025192033541827807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 445440537430048892326549 20880025192033541827807)
              ·
                rfl

theorem cell19_205860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 6].length) (baseStart_205860 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_205860 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_205860 prefixEnd_205860 := by exact prefixLift 205860
  have htrace : WordTrace (prefixWord ++ tailWord_205860) baseStart_205860 baseEnd_205860 := by
    simpa [prefixWord, tailWord_205860, baseEnd_205860] using wordTrace_append hprefix tailTrace_205860
  have hstable : (prefixWord ++ tailWord_205860).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205860).length < 2 ^ (prefixWord ++ tailWord_205860).sum := by decide
  have hdescent : baseEnd_205860 < baseStart_205860 := by decide
  rcases family_descends (prefixWord ++ tailWord_205860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205894 : List Nat := [6, 1, 1, 1, 1, 2, 4, 3]
def baseStart_205894 : Nat := 118140960795 + 205894 * 2 ^ 59
def prefixEnd_205894 : Nat := 4983230072969 + 3 ^ 40 * 205894 * 2
def baseEnd_205894 : Nat := 62650421260398620727773

theorem tailTrace_205894 : CollatzResearch.WordTrace tailWord_205894 prefixEnd_205894 62650421260398620727773 := by
  unfold tailWord_205894
  simp only [CollatzResearch.WordTrace]
  refine ⟨234674097377771148149023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 5006380744059117827179157 234674097377771148149023)
  ·
    refine ⟨352011146066656722223535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234674097377771148149023 352011146066656722223535)
    ·
      refine ⟨528016719099985083335303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352011146066656722223535 528016719099985083335303)
      ·
        refine ⟨792025078649977625002955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 528016719099985083335303 792025078649977625002955)
        ·
          refine ⟨1188037617974966437504433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 792025078649977625002955 1188037617974966437504433)
          ·
            refine ⟨891028213481224828128325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1188037617974966437504433 891028213481224828128325)
            ·
              refine ⟨167067790027729655274061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 891028213481224828128325 167067790027729655274061)
              ·
                refine ⟨62650421260398620727773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 167067790027729655274061 62650421260398620727773)
                ·
                  rfl

theorem cell19_205894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_205894 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_205894 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_205894 prefixEnd_205894 := by exact prefixLift 205894
  have htrace : WordTrace (prefixWord ++ tailWord_205894) baseStart_205894 baseEnd_205894 := by
    simpa [prefixWord, tailWord_205894, baseEnd_205894] using wordTrace_append hprefix tailTrace_205894
  have hstable : (prefixWord ++ tailWord_205894).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205894).length < 2 ^ (prefixWord ++ tailWord_205894).sum := by decide
  have hdescent : baseEnd_205894 < baseStart_205894 := by decide
  rcases family_descends (prefixWord ++ tailWord_205894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205898 : List Nat := [3, 1, 2, 1, 1, 2, 6, 3]
def baseStart_205898 : Nat := 118140960795 + 205898 * 2 ^ 59
def prefixEnd_205898 : Nat := 4983230072969 + 3 ^ 40 * 205898 * 2
def baseEnd_205898 : Nat := 62651638399727796638873

theorem tailTrace_205898 : CollatzResearch.WordTrace tailWord_205898 prefixEnd_205898 62651638399727796638873 := by
  unfold tailWord_205898
  simp only [CollatzResearch.WordTrace]
  refine ⟨1877429252018546355978587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5006478005382790282609565 1877429252018546355978587)
  ·
    refine ⟨2816143878027819533967881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1877429252018546355978587 2816143878027819533967881)
    ·
      refine ⟨2112107908520864650475911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2816143878027819533967881 2112107908520864650475911)
      ·
        refine ⟨3168161862781296975713867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2112107908520864650475911 3168161862781296975713867)
        ·
          refine ⟨4752242794171945463570801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3168161862781296975713867 4752242794171945463570801)
          ·
            refine ⟨3564182095628959097678101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4752242794171945463570801 3564182095628959097678101)
            ·
              refine ⟨167071035732607457703661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3564182095628959097678101 167071035732607457703661)
              ·
                refine ⟨62651638399727796638873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 167071035732607457703661 62651638399727796638873)
                ·
                  rfl

theorem cell19_205898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 6, 3].length) (baseStart_205898 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_205898 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_205898 prefixEnd_205898 := by exact prefixLift 205898
  have htrace : WordTrace (prefixWord ++ tailWord_205898) baseStart_205898 baseEnd_205898 := by
    simpa [prefixWord, tailWord_205898, baseEnd_205898] using wordTrace_append hprefix tailTrace_205898
  have hstable : (prefixWord ++ tailWord_205898).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205898).length < 2 ^ (prefixWord ++ tailWord_205898).sum := by decide
  have hdescent : baseEnd_205898 < baseStart_205898 := by decide
  rcases family_descends (prefixWord ++ tailWord_205898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205976 : List Nat := [2, 1, 2, 4, 2, 8]
def baseStart_205976 : Nat := 118140960795 + 205976 * 2 ^ 59
def prefixEnd_205976 : Nat := 4983230072969 + 3 ^ 40 * 205976 * 2
def baseEnd_205976 : Nat := 6963930290738525211703

theorem tailTrace_205976 : CollatzResearch.WordTrace tailWord_205976 prefixEnd_205976 6963930290738525211703 := by
  unfold tailWord_205976
  simp only [CollatzResearch.WordTrace]
  refine ⟨3756280950895802372626891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5008374601194403163502521 3756280950895802372626891)
  ·
    refine ⟨5634421426343703558940337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3756280950895802372626891 5634421426343703558940337)
    ·
      refine ⟨4225816069757777669205253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5634421426343703558940337 4225816069757777669205253)
      ·
        refine ⟨792340513079583312975985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4225816069757777669205253 792340513079583312975985)
        ·
          refine ⟨594255384809687484731989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 792340513079583312975985 594255384809687484731989)
          ·
            refine ⟨6963930290738525211703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 594255384809687484731989 6963930290738525211703)
            ·
              rfl

theorem cell19_205976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 8].length) (baseStart_205976 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_205976 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_205976 prefixEnd_205976 := by exact prefixLift 205976
  have htrace : WordTrace (prefixWord ++ tailWord_205976) baseStart_205976 baseEnd_205976 := by
    simpa [prefixWord, tailWord_205976, baseEnd_205976] using wordTrace_append hprefix tailTrace_205976
  have hstable : (prefixWord ++ tailWord_205976).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205976).length < 2 ^ (prefixWord ++ tailWord_205976).sum := by decide
  have hdescent : baseEnd_205976 < baseStart_205976 := by decide
  rcases family_descends (prefixWord ++ tailWord_205976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205991 : List Nat := [1, 1, 6, 2, 1, 3, 1, 4]
def baseStart_205991 : Nat := 118140960795 + 205991 * 2 ^ 59
def prefixEnd_205991 : Nat := 4983230072969 + 3 ^ 40 * 205991 * 2
def baseEnd_205991 : Nat := 62679936889131136571953

theorem tailTrace_205991 : CollatzResearch.WordTrace tailWord_205991 prefixEnd_205991 62679936889131136571953 := by
  unfold tailWord_205991
  simp only [CollatzResearch.WordTrace]
  refine ⟨7513108996737262307049827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5008739331158174871366551 7513108996737262307049827)
  ·
    refine ⟨11269663495105893460574741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7513108996737262307049827 11269663495105893460574741)
    ·
      refine ⟨528265476333088755964441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 11269663495105893460574741 528265476333088755964441)
      ·
        refine ⟨396199107249816566973331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 528265476333088755964441 396199107249816566973331)
        ·
          refine ⟨594298660874724850459997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 396199107249816566973331 594298660874724850459997)
          ·
            refine ⟨222861997828021818922499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 594298660874724850459997 222861997828021818922499)
            ·
              refine ⟨334292996742032728383749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 222861997828021818922499 334292996742032728383749)
              ·
                refine ⟨62679936889131136571953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 334292996742032728383749 62679936889131136571953)
                ·
                  rfl

theorem cell19_205991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 1, 4].length) (baseStart_205991 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_205991 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_205991 prefixEnd_205991 := by exact prefixLift 205991
  have htrace : WordTrace (prefixWord ++ tailWord_205991) baseStart_205991 baseEnd_205991 := by
    simpa [prefixWord, tailWord_205991, baseEnd_205991] using wordTrace_append hprefix tailTrace_205991
  have hstable : (prefixWord ++ tailWord_205991).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205991).length < 2 ^ (prefixWord ++ tailWord_205991).sum := by decide
  have hdescent : baseEnd_205991 < baseStart_205991 := by decide
  rcases family_descends (prefixWord ++ tailWord_205991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206006 : List Nat := [5, 1, 3, 2, 1, 1, 3, 3]
def baseStart_206006 : Nat := 118140960795 + 206006 * 2 ^ 59
def prefixEnd_206006 : Nat := 4983230072969 + 3 ^ 40 * 206006 * 2
def baseEnd_206006 : Nat := 62684501161615546238579

theorem tailTrace_206006 : CollatzResearch.WordTrace tailWord_206006 prefixEnd_206006 62684501161615546238579 := by
  unfold tailWord_206006
  simp only [CollatzResearch.WordTrace]
  refine ⟨469603505730182491802867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5009104061121946579230581 469603505730182491802867)
  ·
    refine ⟨704405258595273737704301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 469603505730182491802867 704405258595273737704301)
    ·
      refine ⟨264151971973227651639113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 704405258595273737704301 264151971973227651639113)
      ·
        refine ⟨198113978979920738729335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264151971973227651639113 198113978979920738729335)
        ·
          refine ⟨297170968469881108094003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198113978979920738729335 297170968469881108094003)
          ·
            refine ⟨445756452704821662141005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 297170968469881108094003 445756452704821662141005)
            ·
              refine ⟨167158669764308123302877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 445756452704821662141005 167158669764308123302877)
              ·
                refine ⟨62684501161615546238579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 167158669764308123302877 62684501161615546238579)
                ·
                  rfl

theorem cell19_206006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 3, 3].length) (baseStart_206006 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_206006 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_206006 prefixEnd_206006 := by exact prefixLift 206006
  have htrace : WordTrace (prefixWord ++ tailWord_206006) baseStart_206006 baseEnd_206006 := by
    simpa [prefixWord, tailWord_206006, baseEnd_206006] using wordTrace_append hprefix tailTrace_206006
  have hstable : (prefixWord ++ tailWord_206006).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206006).length < 2 ^ (prefixWord ++ tailWord_206006).sum := by decide
  have hdescent : baseEnd_206006 < baseStart_206006 := by decide
  rcases family_descends (prefixWord ++ tailWord_206006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206088 : List Nat := [2, 1, 3, 2, 4, 2, 5]
def baseStart_206088 : Nat := 118140960795 + 206088 * 2 ^ 59
def prefixEnd_206088 : Nat := 4983230072969 + 3 ^ 40 * 206088 * 2
def baseEnd_206088 : Nat := 20903150839287884138711

theorem tailTrace_206088 : CollatzResearch.WordTrace tailWord_206088 prefixEnd_206088 20903150839287884138711 := by
  unfold tailWord_206088
  simp only [CollatzResearch.WordTrace]
  refine ⟨3758323438692923936665459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5011097918257231915553945 3758323438692923936665459)
  ·
    refine ⟨5637485158039385904998189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3758323438692923936665459 5637485158039385904998189)
    ·
      refine ⟨2114056934264769714374321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5637485158039385904998189 2114056934264769714374321)
      ·
        refine ⟨1585542700698577285780741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2114056934264769714374321 1585542700698577285780741)
        ·
          refine ⟨297289256380983241083889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1585542700698577285780741 297289256380983241083889)
          ·
            refine ⟨222966942285737430812917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 297289256380983241083889 222966942285737430812917)
            ·
              refine ⟨20903150839287884138711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 222966942285737430812917 20903150839287884138711)
              ·
                rfl

theorem cell19_206088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 5].length) (baseStart_206088 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_206088 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_206088 prefixEnd_206088 := by exact prefixLift 206088
  have htrace : WordTrace (prefixWord ++ tailWord_206088) baseStart_206088 baseEnd_206088 := by
    simpa [prefixWord, tailWord_206088, baseEnd_206088] using wordTrace_append hprefix tailTrace_206088
  have hstable : (prefixWord ++ tailWord_206088).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206088).length < 2 ^ (prefixWord ++ tailWord_206088).sum := by decide
  have hdescent : baseEnd_206088 < baseStart_206088 := by decide
  rcases family_descends (prefixWord ++ tailWord_206088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206236 : List Nat := [2, 2, 3, 4, 1, 2, 2, 3]
def baseStart_206236 : Nat := 118140960795 + 206236 * 2 ^ 59
def prefixEnd_206236 : Nat := 4983230072969 + 3 ^ 40 * 206236 * 2
def baseEnd_206236 : Nat := 62754486673043161126841

theorem tailTrace_206236 : CollatzResearch.WordTrace tailWord_206236 prefixEnd_206236 62754486673043161126841 := by
  unfold tailWord_206236
  simp only [CollatzResearch.WordTrace]
  refine ⟨3761022440424834574859281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5014696587233112766479041 3761022440424834574859281)
  ·
    refine ⟨2820766830318625931144461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3761022440424834574859281 2820766830318625931144461)
    ·
      refine ⟨1057787561369484724179173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2820766830318625931144461 1057787561369484724179173)
      ·
        refine ⟨198335167756778385783595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1057787561369484724179173 198335167756778385783595)
        ·
          refine ⟨297502751635167578675393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198335167756778385783595 297502751635167578675393)
          ·
            refine ⟨223127063726375684006545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 297502751635167578675393 223127063726375684006545)
            ·
              refine ⟨167345297794781763004909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 223127063726375684006545 167345297794781763004909)
              ·
                refine ⟨62754486673043161126841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 167345297794781763004909 62754486673043161126841)
                ·
                  rfl

theorem cell19_206236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 2, 3].length) (baseStart_206236 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_206236 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_206236 prefixEnd_206236 := by exact prefixLift 206236
  have htrace : WordTrace (prefixWord ++ tailWord_206236) baseStart_206236 baseEnd_206236 := by
    simpa [prefixWord, tailWord_206236, baseEnd_206236] using wordTrace_append hprefix tailTrace_206236
  have hstable : (prefixWord ++ tailWord_206236).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206236).length < 2 ^ (prefixWord ++ tailWord_206236).sum := by decide
  have hdescent : baseEnd_206236 < baseStart_206236 := by decide
  rcases family_descends (prefixWord ++ tailWord_206236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206238 : List Nat := [4, 3, 1, 2, 2, 1, 1, 5]
def baseStart_206238 : Nat := 118140960795 + 206238 * 2 ^ 59
def prefixEnd_206238 : Nat := 4983230072969 + 3 ^ 40 * 206238 * 2
def baseEnd_206238 : Nat := 62755095242707749082391

theorem tailTrace_206238 : CollatzResearch.WordTrace tailWord_206238 prefixEnd_206238 62755095242707749082391 := by
  unfold tailWord_206238
  simp only [CollatzResearch.WordTrace]
  refine ⟨940264728355302936411421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5014745217894948994194245 940264728355302936411421)
  ·
    refine ⟨352599273133238601154283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 940264728355302936411421 352599273133238601154283)
    ·
      refine ⟨528898909699857901731425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352599273133238601154283 528898909699857901731425)
      ·
        refine ⟨396674182274893426298569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 528898909699857901731425 396674182274893426298569)
        ·
          refine ⟨297505636706170069723927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 396674182274893426298569 297505636706170069723927)
          ·
            refine ⟨446258455059255104585891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 297505636706170069723927 446258455059255104585891)
            ·
              refine ⟨669387682588882656878837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 446258455059255104585891 669387682588882656878837)
              ·
                refine ⟨62755095242707749082391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 669387682588882656878837 62755095242707749082391)
                ·
                  rfl

theorem cell19_206238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 5].length) (baseStart_206238 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_206238 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_206238 prefixEnd_206238 := by exact prefixLift 206238
  have htrace : WordTrace (prefixWord ++ tailWord_206238) baseStart_206238 baseEnd_206238 := by
    simpa [prefixWord, tailWord_206238, baseEnd_206238] using wordTrace_append hprefix tailTrace_206238
  have hstable : (prefixWord ++ tailWord_206238).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206238).length < 2 ^ (prefixWord ++ tailWord_206238).sum := by decide
  have hdescent : baseEnd_206238 < baseStart_206238 := by decide
  rcases family_descends (prefixWord ++ tailWord_206238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206261 : List Nat := [1, 3, 3, 2, 2, 1, 7]
def baseStart_206261 : Nat := 118140960795 + 206261 * 2 ^ 59
def prefixEnd_206261 : Nat := 4983230072969 + 3 ^ 40 * 206261 * 2
def baseEnd_206261 : Nat := 20920697931283503523739

theorem tailTrace_206261 : CollatzResearch.WordTrace tailWord_206261 prefixEnd_206261 20920697931283503523739 := by
  unfold tailWord_206261
  simp only [CollatzResearch.WordTrace]
  refine ⟨7522956705759098419378637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5015304470506065612919091 7522956705759098419378637)
  ·
    refine ⟨2821108764659661907266989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7522956705759098419378637 2821108764659661907266989)
    ·
      refine ⟨1057915786747373215225121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2821108764659661907266989 1057915786747373215225121)
      ·
        refine ⟨793436840060529911418841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1057915786747373215225121 793436840060529911418841)
        ·
          refine ⟨595077630045397433564131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 793436840060529911418841 595077630045397433564131)
          ·
            refine ⟨892616445068096150346197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 595077630045397433564131 892616445068096150346197)
            ·
              refine ⟨20920697931283503523739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 892616445068096150346197 20920697931283503523739)
              ·
                rfl

theorem cell19_206261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 7].length) (baseStart_206261 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_206261 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_206261 prefixEnd_206261 := by exact prefixLift 206261
  have htrace : WordTrace (prefixWord ++ tailWord_206261) baseStart_206261 baseEnd_206261 := by
    simpa [prefixWord, tailWord_206261, baseEnd_206261] using wordTrace_append hprefix tailTrace_206261
  have hstable : (prefixWord ++ tailWord_206261).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206261).length < 2 ^ (prefixWord ++ tailWord_206261).sum := by decide
  have hdescent : baseEnd_206261 < baseStart_206261 := by decide
  rcases family_descends (prefixWord ++ tailWord_206261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206280 : List Nat := [2, 1, 3, 1, 3, 1, 4, 4]
def baseStart_206280 : Nat := 118140960795 + 206280 * 2 ^ 59
def prefixEnd_206280 : Nat := 4983230072969 + 3 ^ 40 * 206280 * 2
def baseEnd_206280 : Nat := 62767875205664096148943

theorem tailTrace_206280 : CollatzResearch.WordTrace tailWord_206280 prefixEnd_206280 62767875205664096148943 := by
  unfold tailWord_206280
  simp only [CollatzResearch.WordTrace]
  refine ⟨3761824846345132332160147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5015766461793509776213529 3761824846345132332160147)
  ·
    refine ⟨5642737269517698498240221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3761824846345132332160147 5642737269517698498240221)
    ·
      refine ⟨2116026476069136936840083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5642737269517698498240221 2116026476069136936840083)
      ·
        refine ⟨3174039714103705405260125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2116026476069136936840083 3174039714103705405260125)
        ·
          refine ⟨1190264892788889526972547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3174039714103705405260125 1190264892788889526972547)
          ·
            refine ⟨1785397339183334290458821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1190264892788889526972547 1785397339183334290458821)
            ·
              refine ⟨334762001096875179461029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1785397339183334290458821 334762001096875179461029)
              ·
                refine ⟨62767875205664096148943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 334762001096875179461029 62767875205664096148943)
                ·
                  rfl

theorem cell19_206280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4, 4].length) (baseStart_206280 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_206280 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_206280 prefixEnd_206280 := by exact prefixLift 206280
  have htrace : WordTrace (prefixWord ++ tailWord_206280) baseStart_206280 baseEnd_206280 := by
    simpa [prefixWord, tailWord_206280, baseEnd_206280] using wordTrace_append hprefix tailTrace_206280
  have hstable : (prefixWord ++ tailWord_206280).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206280).length < 2 ^ (prefixWord ++ tailWord_206280).sum := by decide
  have hdescent : baseEnd_206280 < baseStart_206280 := by decide
  rcases family_descends (prefixWord ++ tailWord_206280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206320 : List Nat := [2, 1, 1, 1, 3, 11]
def baseStart_206320 : Nat := 118140960795 + 206320 * 2 ^ 59
def prefixEnd_206320 : Nat := 4983230072969 + 3 ^ 40 * 206320 * 2
def baseEnd_206320 : Nat := 6975560733217317251105

theorem tailTrace_206320 : CollatzResearch.WordTrace tailWord_206320 prefixEnd_206320 6975560733217317251105 := by
  unfold tailWord_206320
  simp only [CollatzResearch.WordTrace]
  refine ⟨3762554306272675747888207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5016739075030234330517609 3762554306272675747888207)
  ·
    refine ⟨5643831459409013621832311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3762554306272675747888207 5643831459409013621832311)
    ·
      refine ⟨8465747189113520432748467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5643831459409013621832311 8465747189113520432748467)
      ·
        refine ⟨12698620783670280649122701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8465747189113520432748467 12698620783670280649122701)
        ·
          refine ⟨4761982793876355243421013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12698620783670280649122701 4761982793876355243421013)
          ·
            refine ⟨6975560733217317251105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 4761982793876355243421013 6975560733217317251105)
            ·
              rfl

theorem cell19_206320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 11].length) (baseStart_206320 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_206320 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_206320 prefixEnd_206320 := by exact prefixLift 206320
  have htrace : WordTrace (prefixWord ++ tailWord_206320) baseStart_206320 baseEnd_206320 := by
    simpa [prefixWord, tailWord_206320, baseEnd_206320] using wordTrace_append hprefix tailTrace_206320
  have hstable : (prefixWord ++ tailWord_206320).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206320).length < 2 ^ (prefixWord ++ tailWord_206320).sum := by decide
  have hdescent : baseEnd_206320 < baseStart_206320 := by decide
  rcases family_descends (prefixWord ++ tailWord_206320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206339 : List Nat := [1, 1, 1, 3, 2, 1, 2, 8]
def baseStart_206339 : Nat := 118140960795 + 206339 * 2 ^ 59
def prefixEnd_206339 : Nat := 4983230072969 + 3 ^ 40 * 206339 * 2
def baseEnd_206339 : Nat := 62785828010769440837671

theorem tailTrace_206339 : CollatzResearch.WordTrace tailWord_206339 prefixEnd_206339 62785828010769440837671 := by
  unfold tailWord_206339
  simp only [CollatzResearch.WordTrace]
  refine ⟨7525801599476517740718071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5017201066317678493812047 7525801599476517740718071)
  ·
    refine ⟨11288702399214776611077107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7525801599476517740718071 11288702399214776611077107)
    ·
      refine ⟨16933053598822164916615661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11288702399214776611077107 16933053598822164916615661)
      ·
        refine ⟨6349895099558311843730873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16933053598822164916615661 6349895099558311843730873)
        ·
          refine ⟨4762421324668733882798155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6349895099558311843730873 4762421324668733882798155)
          ·
            refine ⟨7143631987003100824197233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4762421324668733882798155 7143631987003100824197233)
            ·
              refine ⟨5357723990252325618147925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7143631987003100824197233 5357723990252325618147925)
              ·
                refine ⟨62785828010769440837671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5357723990252325618147925 62785828010769440837671)
                ·
                  rfl

theorem cell19_206339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 8].length) (baseStart_206339 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_206339 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_206339 prefixEnd_206339 := by exact prefixLift 206339
  have htrace : WordTrace (prefixWord ++ tailWord_206339) baseStart_206339 baseEnd_206339 := by
    simpa [prefixWord, tailWord_206339, baseEnd_206339] using wordTrace_append hprefix tailTrace_206339
  have hstable : (prefixWord ++ tailWord_206339).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206339).length < 2 ^ (prefixWord ++ tailWord_206339).sum := by decide
  have hdescent : baseEnd_206339 < baseStart_206339 := by decide
  rcases family_descends (prefixWord ++ tailWord_206339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206527 : List Nat := [1, 1, 2, 2, 2, 3, 5, 3]
def baseStart_206527 : Nat := 118140960795 + 206527 * 2 ^ 59
def prefixEnd_206527 : Nat := 4983230072969 + 3 ^ 40 * 206527 * 2
def baseEnd_206527 : Nat := 62843033559240708659381

theorem tailTrace_206527 : CollatzResearch.WordTrace tailWord_206527 prefixEnd_206527 62843033559240708659381 := by
  unfold tailWord_206527
  simp only [CollatzResearch.WordTrace]
  refine ⟨7532658522795425848561835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5021772348530283899041223 7532658522795425848561835)
  ·
    refine ⟨11298987784193138772842753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7532658522795425848561835 11298987784193138772842753)
    ·
      refine ⟨8474240838144854079632065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11298987784193138772842753 8474240838144854079632065)
      ·
        refine ⟨6355680628608640559724049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8474240838144854079632065 6355680628608640559724049)
        ·
          refine ⟨4766760471456480419793037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6355680628608640559724049 4766760471456480419793037)
          ·
            refine ⟨1787535176796180157422389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4766760471456480419793037 1787535176796180157422389)
            ·
              refine ⟨167581422824641889758349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1787535176796180157422389 167581422824641889758349)
              ·
                refine ⟨62843033559240708659381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 167581422824641889758349 62843033559240708659381)
                ·
                  rfl

theorem cell19_206527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 5, 3].length) (baseStart_206527 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_206527 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_206527 prefixEnd_206527 := by exact prefixLift 206527
  have htrace : WordTrace (prefixWord ++ tailWord_206527) baseStart_206527 baseEnd_206527 := by
    simpa [prefixWord, tailWord_206527, baseEnd_206527] using wordTrace_append hprefix tailTrace_206527
  have hstable : (prefixWord ++ tailWord_206527).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206527).length < 2 ^ (prefixWord ++ tailWord_206527).sum := by decide
  have hdescent : baseEnd_206527 < baseStart_206527 := by decide
  rcases family_descends (prefixWord ++ tailWord_206527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206546 : List Nat := [3, 2, 2, 2, 2, 2, 6]
def baseStart_206546 : Nat := 118140960795 + 206546 * 2 ^ 59
def prefixEnd_206546 : Nat := 4983230072969 + 3 ^ 40 * 206546 * 2
def baseEnd_206546 : Nat := 20949604990351431412369

theorem tailTrace_206546 : CollatzResearch.WordTrace tailWord_206546 prefixEnd_206546 20949604990351431412369 := by
  unfold tailWord_206546
  simp only [CollatzResearch.WordTrace]
  refine ⟨1883337877431648023375873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5022234339817728062335661 1883337877431648023375873)
  ·
    refine ⟨1412503408073736017531905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1883337877431648023375873 1412503408073736017531905)
    ·
      refine ⟨1059377556055302013148929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1412503408073736017531905 1059377556055302013148929)
      ·
        refine ⟨794533167041476509861697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1059377556055302013148929 794533167041476509861697)
        ·
          refine ⟨595899875281107382396273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 794533167041476509861697 595899875281107382396273)
          ·
            refine ⟨446924906460830536797205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 595899875281107382396273 446924906460830536797205)
            ·
              refine ⟨20949604990351431412369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 446924906460830536797205 20949604990351431412369)
              ·
                rfl

theorem cell19_206546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 6].length) (baseStart_206546 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_206546 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_206546 prefixEnd_206546 := by exact prefixLift 206546
  have htrace : WordTrace (prefixWord ++ tailWord_206546) baseStart_206546 baseEnd_206546 := by
    simpa [prefixWord, tailWord_206546, baseEnd_206546] using wordTrace_append hprefix tailTrace_206546
  have hstable : (prefixWord ++ tailWord_206546).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206546).length < 2 ^ (prefixWord ++ tailWord_206546).sum := by decide
  have hdescent : baseEnd_206546 < baseStart_206546 := by decide
  rcases family_descends (prefixWord ++ tailWord_206546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206580 : List Nat := [2, 6, 1, 1, 1, 2, 1, 5]
def baseStart_206580 : Nat := 118140960795 + 206580 * 2 ^ 59
def prefixEnd_206580 : Nat := 4983230072969 + 3 ^ 40 * 206580 * 2
def baseEnd_206580 : Nat := 62859160655352289481459

theorem tailTrace_206580 : CollatzResearch.WordTrace tailWord_206580 prefixEnd_206580 62859160655352289481459 := by
  unfold tailWord_206580
  simp only [CollatzResearch.WordTrace]
  refine ⟨3767295795801707950120597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5023061061068943933494129 3767295795801707950120597)
  ·
    refine ⟨176591990428205060161903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 3767295795801707950120597 176591990428205060161903)
    ·
      refine ⟨264887985642307590242855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176591990428205060161903 264887985642307590242855)
      ·
        refine ⟨397331978463461385364283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264887985642307590242855 397331978463461385364283)
        ·
          refine ⟨595997967695192078046425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 397331978463461385364283 595997967695192078046425)
          ·
            refine ⟨446998475771394058534819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 595997967695192078046425 446998475771394058534819)
            ·
              refine ⟨670497713657091087802229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 446998475771394058534819 670497713657091087802229)
              ·
                refine ⟨62859160655352289481459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 670497713657091087802229 62859160655352289481459)
                ·
                  rfl

theorem cell19_206580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 5].length) (baseStart_206580 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_206580 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_206580 prefixEnd_206580 := by exact prefixLift 206580
  have htrace : WordTrace (prefixWord ++ tailWord_206580) baseStart_206580 baseEnd_206580 := by
    simpa [prefixWord, tailWord_206580, baseEnd_206580] using wordTrace_append hprefix tailTrace_206580
  have hstable : (prefixWord ++ tailWord_206580).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206580).length < 2 ^ (prefixWord ++ tailWord_206580).sum := by decide
  have hdescent : baseEnd_206580 < baseStart_206580 := by decide
  rcases family_descends (prefixWord ++ tailWord_206580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206582 : List Nat := [5, 1, 1, 1, 1, 3, 4, 3]
def baseStart_206582 : Nat := 118140960795 + 206582 * 2 ^ 59
def prefixEnd_206582 : Nat := 4983230072969 + 3 ^ 40 * 206582 * 2
def baseEnd_206582 : Nat := 62859769225016877437009

theorem tailTrace_206582 : CollatzResearch.WordTrace tailWord_206582 prefixEnd_206582 62859769225016877437009 := by
  unfold tailWord_206582
  simp only [CollatzResearch.WordTrace]
  refine ⟨470916533599760640113375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5023109691730780161209333 470916533599760640113375)
  ·
    refine ⟨706374800399640960170063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 470916533599760640113375 706374800399640960170063)
    ·
      refine ⟨1059562200599461440255095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 706374800399640960170063 1059562200599461440255095)
      ·
        refine ⟨1589343300899192160382643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1059562200599461440255095 1589343300899192160382643)
        ·
          refine ⟨2384014951348788240573965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1589343300899192160382643 2384014951348788240573965)
          ·
            refine ⟨894005606755795590215237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2384014951348788240573965 894005606755795590215237)
            ·
              refine ⟨167626051266711673165357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 894005606755795590215237 167626051266711673165357)
              ·
                refine ⟨62859769225016877437009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 167626051266711673165357 62859769225016877437009)
                ·
                  rfl

theorem cell19_206582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 4, 3].length) (baseStart_206582 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_206582 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_206582 prefixEnd_206582 := by exact prefixLift 206582
  have htrace : WordTrace (prefixWord ++ tailWord_206582) baseStart_206582 baseEnd_206582 := by
    simpa [prefixWord, tailWord_206582, baseEnd_206582] using wordTrace_append hprefix tailTrace_206582
  have hstable : (prefixWord ++ tailWord_206582).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206582).length < 2 ^ (prefixWord ++ tailWord_206582).sum := by decide
  have hdescent : baseEnd_206582 < baseStart_206582 := by decide
  rcases family_descends (prefixWord ++ tailWord_206582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206751 : List Nat := [1, 1, 2, 5, 4, 1, 2, 3]
def baseStart_206751 : Nat := 118140960795 + 206751 * 2 ^ 59
def prefixEnd_206751 : Nat := 4983230072969 + 3 ^ 40 * 206751 * 2
def baseEnd_206751 : Nat := 62911193361674559680993

theorem tailTrace_206751 : CollatzResearch.WordTrace tailWord_206751 prefixEnd_206751 62911193361674559680993 := by
  unfold tailWord_206751
  simp only [CollatzResearch.WordTrace]
  refine ⟨7540828473983912104716107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5027218982655941403144071 7540828473983912104716107)
  ·
    refine ⟨11311242710975868157074161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7540828473983912104716107 11311242710975868157074161)
    ·
      refine ⟨8483432033231901117805621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11311242710975868157074161 8483432033231901117805621)
      ·
        refine ⟨795321753115490729794277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8483432033231901117805621 795321753115490729794277)
        ·
          refine ⟨149122828709154511836427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 795321753115490729794277 149122828709154511836427)
          ·
            refine ⟨223684243063731767754641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149122828709154511836427 223684243063731767754641)
            ·
              refine ⟨167763182297798825815981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 223684243063731767754641 167763182297798825815981)
              ·
                refine ⟨62911193361674559680993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 167763182297798825815981 62911193361674559680993)
                ·
                  rfl

theorem cell19_206751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 2, 3].length) (baseStart_206751 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_206751 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_206751 prefixEnd_206751 := by exact prefixLift 206751
  have htrace : WordTrace (prefixWord ++ tailWord_206751) baseStart_206751 baseEnd_206751 := by
    simpa [prefixWord, tailWord_206751, baseEnd_206751] using wordTrace_append hprefix tailTrace_206751
  have hstable : (prefixWord ++ tailWord_206751).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206751).length < 2 ^ (prefixWord ++ tailWord_206751).sum := by decide
  have hdescent : baseEnd_206751 < baseStart_206751 := by decide
  rcases family_descends (prefixWord ++ tailWord_206751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206795 : List Nat := [1, 1, 1, 1, 3, 4, 4, 4]
def baseStart_206795 : Nat := 118140960795 + 206795 * 2 ^ 59
def prefixEnd_206795 : Nat := 4983230072969 + 3 ^ 40 * 206795 * 2
def baseEnd_206795 : Nat := 62924581894295494703095

theorem tailTrace_206795 : CollatzResearch.WordTrace tailWord_206795 prefixEnd_206795 62924581894295494703095 := by
  unfold tailWord_206795
  simp only [CollatzResearch.WordTrace]
  refine ⟨7542433285824507619317839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5028288857216338412878559 7542433285824507619317839)
  ·
    refine ⟨11313649928736761428976759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7542433285824507619317839 11313649928736761428976759)
    ·
      refine ⟨16970474893105142143465139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11313649928736761428976759 16970474893105142143465139)
      ·
        refine ⟨25455712339657713215197709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16970474893105142143465139 25455712339657713215197709)
        ·
          refine ⟨9545892127371642455699141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25455712339657713215197709 9545892127371642455699141)
          ·
            refine ⟨1789854773882182960443589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9545892127371642455699141 1789854773882182960443589)
            ·
              refine ⟨335597770102909305083173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1789854773882182960443589 335597770102909305083173)
              ·
                refine ⟨62924581894295494703095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 335597770102909305083173 62924581894295494703095)
                ·
                  rfl

theorem cell19_206795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4].length) (baseStart_206795 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_206795 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_206795 prefixEnd_206795 := by exact prefixLift 206795
  have htrace : WordTrace (prefixWord ++ tailWord_206795) baseStart_206795 baseEnd_206795 := by
    simpa [prefixWord, tailWord_206795, baseEnd_206795] using wordTrace_append hprefix tailTrace_206795
  have hstable : (prefixWord ++ tailWord_206795).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206795).length < 2 ^ (prefixWord ++ tailWord_206795).sum := by decide
  have hdescent : baseEnd_206795 < baseStart_206795 := by decide
  rcases family_descends (prefixWord ++ tailWord_206795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206829 : List Nat := [1, 5, 1, 4, 2, 6]
def baseStart_206829 : Nat := 118140960795 + 206829 * 2 ^ 59
def prefixEnd_206829 : Nat := 4983230072969 + 3 ^ 40 * 206829 * 2
def baseEnd_206829 : Nat := 6992769730954832216383

theorem tailTrace_206829 : CollatzResearch.WordTrace tailWord_206829 prefixEnd_206829 6992769730954832216383 := by
  unfold tailWord_206829
  simp only [CollatzResearch.WordTrace]
  refine ⟨7543673367701331426055541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5029115578467554284037027 7543673367701331426055541)
  ·
    refine ⟨707219378221999821192707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7543673367701331426055541 707219378221999821192707)
    ·
      refine ⟨1060829067332999731789061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 707219378221999821192707 1060829067332999731789061)
      ·
        refine ⟨198905450124937449710449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1060829067332999731789061 198905450124937449710449)
        ·
          refine ⟨149179087593703087282837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198905450124937449710449 149179087593703087282837)
          ·
            refine ⟨6992769730954832216383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 149179087593703087282837 6992769730954832216383)
            ·
              rfl

theorem cell19_206829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 6].length) (baseStart_206829 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_206829 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_206829 prefixEnd_206829 := by exact prefixLift 206829
  have htrace : WordTrace (prefixWord ++ tailWord_206829) baseStart_206829 baseEnd_206829 := by
    simpa [prefixWord, tailWord_206829, baseEnd_206829] using wordTrace_append hprefix tailTrace_206829
  have hstable : (prefixWord ++ tailWord_206829).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206829).length < 2 ^ (prefixWord ++ tailWord_206829).sum := by decide
  have hdescent : baseEnd_206829 < baseStart_206829 := by decide
  rcases family_descends (prefixWord ++ tailWord_206829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206833 : List Nat := [1, 2, 2, 2, 5, 7]
def baseStart_206833 : Nat := 118140960795 + 206833 * 2 ^ 59
def prefixEnd_206833 : Nat := 4983230072969 + 3 ^ 40 * 206833 * 2
def baseEnd_206833 : Nat := 6992904968658073984283

theorem tailTrace_206833 : CollatzResearch.WordTrace tailWord_206833 prefixEnd_206833 6992904968658073984283 := by
  unfold tailWord_206833
  simp only [CollatzResearch.WordTrace]
  refine ⟨7543819259686840109201153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5029212839791226739467435 7543819259686840109201153)
  ·
    refine ⟨5657864444765130081900865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7543819259686840109201153 5657864444765130081900865)
    ·
      refine ⟨4243398333573847561425649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5657864444765130081900865 4243398333573847561425649)
      ·
        refine ⟨3182548750180385671069237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4243398333573847561425649 3182548750180385671069237)
        ·
          refine ⟨298363945329411156662741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3182548750180385671069237 298363945329411156662741)
          ·
            refine ⟨6992904968658073984283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 298363945329411156662741 6992904968658073984283)
            ·
              rfl

theorem cell19_206833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 7].length) (baseStart_206833 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_206833 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_206833 prefixEnd_206833 := by exact prefixLift 206833
  have htrace : WordTrace (prefixWord ++ tailWord_206833) baseStart_206833 baseEnd_206833 := by
    simpa [prefixWord, tailWord_206833, baseEnd_206833] using wordTrace_append hprefix tailTrace_206833
  have hstable : (prefixWord ++ tailWord_206833).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206833).length < 2 ^ (prefixWord ++ tailWord_206833).sum := by decide
  have hdescent : baseEnd_206833 < baseStart_206833 := by decide
  rcases family_descends (prefixWord ++ tailWord_206833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206909 : List Nat := [1, 4, 1, 3, 1, 1, 2, 6]
def baseStart_206909 : Nat := 118140960795 + 206909 * 2 ^ 59
def prefixEnd_206909 : Nat := 4983230072969 + 3 ^ 40 * 206909 * 2
def baseEnd_206909 : Nat := 62959270365177008169451

theorem tailTrace_206909 : CollatzResearch.WordTrace tailWord_206909 prefixEnd_206909 62959270365177008169451 := by
  unfold tailWord_206909
  simp only [CollatzResearch.WordTrace]
  refine ⟨7546591207411505088967781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5031060804941003392645187 7546591207411505088967781)
  ·
    refine ⟨1414985851389657204181459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7546591207411505088967781 1414985851389657204181459)
    ·
      refine ⟨2122478777084485806272189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1414985851389657204181459 2122478777084485806272189)
      ·
        refine ⟨795929541406682177352071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2122478777084485806272189 795929541406682177352071)
        ·
          refine ⟨1193894312110023266028107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 795929541406682177352071 1193894312110023266028107)
          ·
            refine ⟨1790841468165034899042161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1193894312110023266028107 1790841468165034899042161)
            ·
              refine ⟨1343131101123776174281621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1790841468165034899042161 1343131101123776174281621)
              ·
                refine ⟨62959270365177008169451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1343131101123776174281621 62959270365177008169451)
                ·
                  rfl

theorem cell19_206909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 6].length) (baseStart_206909 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_206909 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_206909 prefixEnd_206909 := by exact prefixLift 206909
  have htrace : WordTrace (prefixWord ++ tailWord_206909) baseStart_206909 baseEnd_206909 := by
    simpa [prefixWord, tailWord_206909, baseEnd_206909] using wordTrace_append hprefix tailTrace_206909
  have hstable : (prefixWord ++ tailWord_206909).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206909).length < 2 ^ (prefixWord ++ tailWord_206909).sum := by decide
  have hdescent : baseEnd_206909 < baseStart_206909 := by decide
  rcases family_descends (prefixWord ++ tailWord_206909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206926 : List Nat := [4, 1, 1, 1, 1, 4, 4, 3]
def baseStart_206926 : Nat := 118140960795 + 206926 * 2 ^ 59
def prefixEnd_206926 : Nat := 4983230072969 + 3 ^ 40 * 206926 * 2
def baseEnd_206926 : Nat := 62964443207326005791627

theorem tailTrace_206926 : CollatzResearch.WordTrace tailWord_206926 prefixEnd_206926 62964443207326005791627 := by
  unfold tailWord_206926
  simp only [CollatzResearch.WordTrace]
  refine ⟨943401406043739624042079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5031474165566611328224421 943401406043739624042079)
  ·
    refine ⟨1415102109065609436063119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 943401406043739624042079 1415102109065609436063119)
    ·
      refine ⟨2122653163598414154094679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1415102109065609436063119 2122653163598414154094679)
      ·
        refine ⟨3183979745397621231142019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2122653163598414154094679 3183979745397621231142019)
        ·
          refine ⟨4775969618096431846713029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3183979745397621231142019 4775969618096431846713029)
          ·
            refine ⟨895494303393080971258693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4775969618096431846713029 895494303393080971258693)
            ·
              refine ⟨167905181886202682111005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 895494303393080971258693 167905181886202682111005)
              ·
                refine ⟨62964443207326005791627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 167905181886202682111005 62964443207326005791627)
                ·
                  rfl

theorem cell19_206926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 4, 3].length) (baseStart_206926 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_206926 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_206926 prefixEnd_206926 := by exact prefixLift 206926
  have htrace : WordTrace (prefixWord ++ tailWord_206926) baseStart_206926 baseEnd_206926 := by
    simpa [prefixWord, tailWord_206926, baseEnd_206926] using wordTrace_append hprefix tailTrace_206926
  have hstable : (prefixWord ++ tailWord_206926).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206926).length < 2 ^ (prefixWord ++ tailWord_206926).sum := by decide
  have hdescent : baseEnd_206926 < baseStart_206926 := by decide
  rcases family_descends (prefixWord ++ tailWord_206926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206998 : List Nat := [5, 3, 2, 1, 8]
def baseStart_206998 : Nat := 118140960795 + 206998 * 2 ^ 59
def prefixEnd_206998 : Nat := 4983230072969 + 3 ^ 40 * 206998 * 2
def baseEnd_206998 : Nat := 2332827841305598970053

theorem tailTrace_206998 : CollatzResearch.WordTrace tailWord_206998 prefixEnd_206998 2332827841305598970053 := by
  unfold tailWord_206998
  simp only [CollatzResearch.WordTrace]
  refine ⟨471864831505567080559853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5033224869392715525971765 471864831505567080559853)
  ·
    refine ⟨176949311814587655209945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 471864831505567080559853 176949311814587655209945)
    ·
      refine ⟨132711983860940741407459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176949311814587655209945 132711983860940741407459)
      ·
        refine ⟨199067975791411112111189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132711983860940741407459 199067975791411112111189)
        ·
          refine ⟨2332827841305598970053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 199067975791411112111189 2332827841305598970053)
          ·
            rfl

theorem cell19_206998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 8].length) (baseStart_206998 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_206998 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_206998 prefixEnd_206998 := by exact prefixLift 206998
  have htrace : WordTrace (prefixWord ++ tailWord_206998) baseStart_206998 baseEnd_206998 := by
    simpa [prefixWord, tailWord_206998, baseEnd_206998] using wordTrace_append hprefix tailTrace_206998
  have hstable : (prefixWord ++ tailWord_206998).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206998).length < 2 ^ (prefixWord ++ tailWord_206998).sum := by decide
  have hdescent : baseEnd_206998 < baseStart_206998 := by decide
  rcases family_descends (prefixWord ++ tailWord_206998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207002 : List Nat := [3, 1, 1, 5, 3, 6]
def baseStart_207002 : Nat := 118140960795 + 207002 * 2 ^ 59
def prefixEnd_207002 : Nat := 4983230072969 + 3 ^ 40 * 207002 * 2
def baseEnd_207002 : Nat := 6998618761620038678059

theorem tailTrace_207002 : CollatzResearch.WordTrace tailWord_207002 prefixEnd_207002 6998618761620038678059 := by
  unfold tailWord_207002
  simp only [CollatzResearch.WordTrace]
  refine ⟨1887495799018645493025815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5033322130716387981402173 1887495799018645493025815)
  ·
    refine ⟨2831243698527968239538723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1887495799018645493025815 2831243698527968239538723)
    ·
      refine ⟨4246865547791952359308085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2831243698527968239538723 4246865547791952359308085)
      ·
        refine ⟨398143645105495533685133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4246865547791952359308085 398143645105495533685133)
        ·
          refine ⟨149303866914560825131925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 398143645105495533685133 149303866914560825131925)
          ·
            refine ⟨6998618761620038678059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 149303866914560825131925 6998618761620038678059)
            ·
              rfl

theorem cell19_207002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 6].length) (baseStart_207002 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_207002 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_207002 prefixEnd_207002 := by exact prefixLift 207002
  have htrace : WordTrace (prefixWord ++ tailWord_207002) baseStart_207002 baseEnd_207002 := by
    simpa [prefixWord, tailWord_207002, baseEnd_207002] using wordTrace_append hprefix tailTrace_207002
  have hstable : (prefixWord ++ tailWord_207002).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207002).length < 2 ^ (prefixWord ++ tailWord_207002).sum := by decide
  have hdescent : baseEnd_207002 < baseStart_207002 := by decide
  rcases family_descends (prefixWord ++ tailWord_207002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207021 : List Nat := [1, 5, 2, 1, 2, 1, 3, 4]
def baseStart_207021 : Nat := 118140960795 + 207021 * 2 ^ 59
def prefixEnd_207021 : Nat := 4983230072969 + 3 ^ 40 * 207021 * 2
def baseEnd_207021 : Nat := 62993350266393933680257

theorem tailTrace_207021 : CollatzResearch.WordTrace tailWord_207021 prefixEnd_207021 62993350266393933680257 := by
  unfold tailWord_207021
  simp only [CollatzResearch.WordTrace]
  refine ⟨7550676183005748217044917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5033784122003832144696611 7550676183005748217044917)
  ·
    refine ⟨707875892156788895347961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7550676183005748217044917 707875892156788895347961)
    ·
      refine ⟨530906919117591671510971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 707875892156788895347961 530906919117591671510971)
      ·
        refine ⟨796360378676387507266457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 530906919117591671510971 796360378676387507266457)
        ·
          refine ⟨597270284007290630449843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 796360378676387507266457 597270284007290630449843)
          ·
            refine ⟨895905426010935945674765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 597270284007290630449843 895905426010935945674765)
            ·
              refine ⟨335964534754100979628037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 895905426010935945674765 335964534754100979628037)
              ·
                refine ⟨62993350266393933680257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 335964534754100979628037 62993350266393933680257)
                ·
                  rfl

theorem cell19_207021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3, 4].length) (baseStart_207021 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_207021 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_207021 prefixEnd_207021 := by exact prefixLift 207021
  have htrace : WordTrace (prefixWord ++ tailWord_207021) baseStart_207021 baseEnd_207021 := by
    simpa [prefixWord, tailWord_207021, baseEnd_207021] using wordTrace_append hprefix tailTrace_207021
  have hstable : (prefixWord ++ tailWord_207021).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207021).length < 2 ^ (prefixWord ++ tailWord_207021).sum := by decide
  have hdescent : baseEnd_207021 < baseStart_207021 := by decide
  rcases family_descends (prefixWord ++ tailWord_207021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207038 : List Nat := [4, 2, 1, 1, 4, 1, 3, 3]
def baseStart_207038 : Nat := 118140960795 + 207038 * 2 ^ 59
def prefixEnd_207038 : Nat := 4983230072969 + 3 ^ 40 * 207038 * 2
def baseEnd_207038 : Nat := 62998523108542931302433

theorem tailTrace_207038 : CollatzResearch.WordTrace tailWord_207038 prefixEnd_207038 62998523108542931302433 := by
  unfold tailWord_207038
  simp only [CollatzResearch.WordTrace]
  refine ⟨943912027993020015051721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5034197482629440080275845 943912027993020015051721)
  ·
    refine ⟨707934020994765011288791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 943912027993020015051721 707934020994765011288791)
    ·
      refine ⟨1061901031492147516933187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 707934020994765011288791 1061901031492147516933187)
      ·
        refine ⟨1592851547238221275399781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1061901031492147516933187 1592851547238221275399781)
        ·
          refine ⟨298659665107166489137459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1592851547238221275399781 298659665107166489137459)
          ·
            refine ⟨447989497660749733706189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 298659665107166489137459 447989497660749733706189)
            ·
              refine ⟨167996061622781150139821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 447989497660749733706189 167996061622781150139821)
              ·
                refine ⟨62998523108542931302433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 167996061622781150139821 62998523108542931302433)
                ·
                  rfl

theorem cell19_207038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 3, 3].length) (baseStart_207038 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_207038 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_207038 prefixEnd_207038 := by exact prefixLift 207038
  have htrace : WordTrace (prefixWord ++ tailWord_207038) baseStart_207038 baseEnd_207038 := by
    simpa [prefixWord, tailWord_207038, baseEnd_207038] using wordTrace_append hprefix tailTrace_207038
  have hstable : (prefixWord ++ tailWord_207038).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207038).length < 2 ^ (prefixWord ++ tailWord_207038).sum := by decide
  have hdescent : baseEnd_207038 < baseStart_207038 := by decide
  rcases family_descends (prefixWord ++ tailWord_207038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207040 : List Nat := [2, 1, 1, 2, 5, 2, 3, 3]
def baseStart_207040 : Nat := 118140960795 + 207040 * 2 ^ 59
def prefixEnd_207040 : Nat := 4983230072969 + 3 ^ 40 * 207040 * 2
def baseEnd_207040 : Nat := 62999131678207519257983

theorem tailTrace_207040 : CollatzResearch.WordTrace tailWord_207040 prefixEnd_207040 62999131678207519257983 := by
  unfold tailWord_207040
  simp only [CollatzResearch.WordTrace]
  refine ⟨3775684584968457230993287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5034246113291276307991049 3775684584968457230993287)
  ·
    refine ⟨5663526877452685846489931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3775684584968457230993287 5663526877452685846489931)
    ·
      refine ⟨8495290316179028769734897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5663526877452685846489931 8495290316179028769734897)
      ·
        refine ⟨6371467737134271577301173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8495290316179028769734897 6371467737134271577301173)
        ·
          refine ⟨597325100356337960371985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6371467737134271577301173 597325100356337960371985)
          ·
            refine ⟨447993825267253470278989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 597325100356337960371985 447993825267253470278989)
            ·
              refine ⟨167997684475220051354621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 447993825267253470278989 167997684475220051354621)
              ·
                refine ⟨62999131678207519257983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 167997684475220051354621 62999131678207519257983)
                ·
                  rfl

theorem cell19_207040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 3, 3].length) (baseStart_207040 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_207040 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_207040 prefixEnd_207040 := by exact prefixLift 207040
  have htrace : WordTrace (prefixWord ++ tailWord_207040) baseStart_207040 baseEnd_207040 := by
    simpa [prefixWord, tailWord_207040, baseEnd_207040] using wordTrace_append hprefix tailTrace_207040
  have hstable : (prefixWord ++ tailWord_207040).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207040).length < 2 ^ (prefixWord ++ tailWord_207040).sum := by decide
  have hdescent : baseEnd_207040 < baseStart_207040 := by decide
  rcases family_descends (prefixWord ++ tailWord_207040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207253 : List Nat := [1, 3, 2, 1, 1, 2, 1, 8]
def baseStart_207253 : Nat := 118140960795 + 207253 * 2 ^ 59
def prefixEnd_207253 : Nat := 4983230072969 + 3 ^ 40 * 207253 * 2
def baseEnd_207253 : Nat := 63063944347486136524069

theorem tailTrace_207253 : CollatzResearch.WordTrace tailWord_207253 prefixEnd_207253 63063944347486136524069 := by
  unfold tailWord_207253
  simp only [CollatzResearch.WordTrace]
  refine ⟨7559137918165251839490413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5039425278776834559660275 7559137918165251839490413)
  ·
    refine ⟨2834676719311969439808905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7559137918165251839490413 2834676719311969439808905)
    ·
      refine ⟨2126007539483977079856679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2834676719311969439808905 2126007539483977079856679)
      ·
        refine ⟨3189011309225965619785019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2126007539483977079856679 3189011309225965619785019)
        ·
          refine ⟨4783516963838948429677529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3189011309225965619785019 4783516963838948429677529)
          ·
            refine ⟨3587637722879211322258147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4783516963838948429677529 3587637722879211322258147)
            ·
              refine ⟨5381456584318816983387221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3587637722879211322258147 5381456584318816983387221)
              ·
                refine ⟨63063944347486136524069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5381456584318816983387221 63063944347486136524069)
                ·
                  rfl

theorem cell19_207253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 8].length) (baseStart_207253 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_207253 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_207253 prefixEnd_207253 := by exact prefixLift 207253
  have htrace : WordTrace (prefixWord ++ tailWord_207253) baseStart_207253 baseEnd_207253 := by
    simpa [prefixWord, tailWord_207253, baseEnd_207253] using wordTrace_append hprefix tailTrace_207253
  have hstable : (prefixWord ++ tailWord_207253).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207253).length < 2 ^ (prefixWord ++ tailWord_207253).sum := by decide
  have hdescent : baseEnd_207253 < baseStart_207253 := by decide
  rcases family_descends (prefixWord ++ tailWord_207253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207289 : List Nat := [1, 2, 1, 4, 3, 3, 5]
def baseStart_207289 : Nat := 118140960795 + 207289 * 2 ^ 59
def prefixEnd_207289 : Nat := 4983230072969 + 3 ^ 40 * 207289 * 2
def baseEnd_207289 : Nat := 21024966200482906574657

theorem tailTrace_207289 : CollatzResearch.WordTrace tailWord_207289 prefixEnd_207289 21024966200482906574657 := by
  unfold tailWord_207289
  simp only [CollatzResearch.WordTrace]
  refine ⟨7560450946034829987800921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5040300630689886658533947 7560450946034829987800921)
  ·
    refine ⟨5670338209526122490850691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7560450946034829987800921 5670338209526122490850691)
    ·
      refine ⟨8505507314289183736276037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5670338209526122490850691 8505507314289183736276037)
      ·
        refine ⟨1594782621429221950551757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8505507314289183736276037 1594782621429221950551757)
        ·
          refine ⟨598043483035958231456909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1594782621429221950551757 598043483035958231456909)
          ·
            refine ⟨224266306138484336796341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 598043483035958231456909 224266306138484336796341)
            ·
              refine ⟨21024966200482906574657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 224266306138484336796341 21024966200482906574657)
              ·
                rfl

theorem cell19_207289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 5].length) (baseStart_207289 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_207289 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_207289 prefixEnd_207289 := by exact prefixLift 207289
  have htrace : WordTrace (prefixWord ++ tailWord_207289) baseStart_207289 baseEnd_207289 := by
    simpa [prefixWord, tailWord_207289, baseEnd_207289] using wordTrace_append hprefix tailTrace_207289
  have hstable : (prefixWord ++ tailWord_207289).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207289).length < 2 ^ (prefixWord ++ tailWord_207289).sum := by decide
  have hdescent : baseEnd_207289 < baseStart_207289 := by decide
  rcases family_descends (prefixWord ++ tailWord_207289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207329 : List Nat := [1, 2, 3, 1, 2, 2, 1, 7]
def baseStart_207329 : Nat := 118140960795 + 207329 * 2 ^ 59
def prefixEnd_207329 : Nat := 4983230072969 + 3 ^ 40 * 207329 * 2
def baseEnd_207329 : Nat := 63087069994740478834973

theorem tailTrace_207329 : CollatzResearch.WordTrace tailWord_207329 prefixEnd_207329 63087069994740478834973 := by
  unfold tailWord_207329
  simp only [CollatzResearch.WordTrace]
  refine ⟨7561909865889916819257041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5041273243926611212838027 7561909865889916819257041)
  ·
    refine ⟨5671432399417437614442781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7561909865889916819257041 5671432399417437614442781)
    ·
      refine ⟨2126787149781539105416043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5671432399417437614442781 2126787149781539105416043)
      ·
        refine ⟨3190180724672308658124065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2126787149781539105416043 3190180724672308658124065)
        ·
          refine ⟨2392635543504231493593049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3190180724672308658124065 2392635543504231493593049)
          ·
            refine ⟨1794476657628173620194787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2392635543504231493593049 1794476657628173620194787)
            ·
              refine ⟨2691714986442260430292181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1794476657628173620194787 2691714986442260430292181)
              ·
                refine ⟨63087069994740478834973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2691714986442260430292181 63087069994740478834973)
                ·
                  rfl

theorem cell19_207329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 7].length) (baseStart_207329 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_207329 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_207329 prefixEnd_207329 := by exact prefixLift 207329
  have htrace : WordTrace (prefixWord ++ tailWord_207329) baseStart_207329 baseEnd_207329 := by
    simpa [prefixWord, tailWord_207329, baseEnd_207329] using wordTrace_append hprefix tailTrace_207329
  have hstable : (prefixWord ++ tailWord_207329).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207329).length < 2 ^ (prefixWord ++ tailWord_207329).sum := by decide
  have hdescent : baseEnd_207329 < baseStart_207329 := by decide
  rcases family_descends (prefixWord ++ tailWord_207329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207346 : List Nat := [3, 2, 1, 4, 2, 7]
def baseStart_207346 : Nat := 118140960795 + 207346 * 2 ^ 59
def prefixEnd_207346 : Nat := 4983230072969 + 3 ^ 40 * 207346 * 2
def baseEnd_207346 : Nat := 7010249204098830717461

theorem tailTrace_207346 : CollatzResearch.WordTrace tailWord_207346 prefixEnd_207346 7010249204098830717461 := by
  unfold tailWord_207346
  simp only [CollatzResearch.WordTrace]
  refine ⟨1890632476707082180656473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5041686604552219148417261 1890632476707082180656473)
  ·
    refine ⟨1417974357530311635492355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1890632476707082180656473 1417974357530311635492355)
    ·
      refine ⟨2126961536295467453238533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1417974357530311635492355 2126961536295467453238533)
      ·
        refine ⟨398805288055400147482225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2126961536295467453238533 398805288055400147482225)
        ·
          refine ⟨299103966041550110611669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 398805288055400147482225 299103966041550110611669)
          ·
            refine ⟨7010249204098830717461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 299103966041550110611669 7010249204098830717461)
            ·
              rfl

theorem cell19_207346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 7].length) (baseStart_207346 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_207346 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_207346 prefixEnd_207346 := by exact prefixLift 207346
  have htrace : WordTrace (prefixWord ++ tailWord_207346) baseStart_207346 baseEnd_207346 := by
    simpa [prefixWord, tailWord_207346, baseEnd_207346] using wordTrace_append hprefix tailTrace_207346
  have hstable : (prefixWord ++ tailWord_207346).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207346).length < 2 ^ (prefixWord ++ tailWord_207346).sum := by decide
  have hdescent : baseEnd_207346 < baseStart_207346 := by decide
  rcases family_descends (prefixWord ++ tailWord_207346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207380 : List Nat := [2, 4, 3, 1, 1, 2, 3, 3]
def baseStart_207380 : Nat := 118140960795 + 207380 * 2 ^ 59
def prefixEnd_207380 : Nat := 4983230072969 + 3 ^ 40 * 207380 * 2
def baseEnd_207380 : Nat := 63102588521187471701501

theorem tailTrace_207380 : CollatzResearch.WordTrace tailWord_207380 prefixEnd_207380 63102588521187471701501 := by
  unfold tailWord_207380
  simp only [CollatzResearch.WordTrace]
  refine ⟨3781884994352576264681797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5042513325803435019575729 3781884994352576264681797)
  ·
    refine ⟨709103436441108049627837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3781884994352576264681797 709103436441108049627837)
    ·
      refine ⟨265913788665415518610439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 709103436441108049627837 265913788665415518610439)
      ·
        refine ⟨398870682998123277915659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265913788665415518610439 398870682998123277915659)
        ·
          refine ⟨598306024497184916873489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 398870682998123277915659 598306024497184916873489)
          ·
            refine ⟨448729518372888687655117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 598306024497184916873489 448729518372888687655117)
            ·
              refine ⟨168273569389833257870669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 448729518372888687655117 168273569389833257870669)
              ·
                refine ⟨63102588521187471701501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 168273569389833257870669 63102588521187471701501)
                ·
                  rfl

theorem cell19_207380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 3, 3].length) (baseStart_207380 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_207380 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_207380 prefixEnd_207380 := by exact prefixLift 207380
  have htrace : WordTrace (prefixWord ++ tailWord_207380) baseStart_207380 baseEnd_207380 := by
    simpa [prefixWord, tailWord_207380, baseEnd_207380] using wordTrace_append hprefix tailTrace_207380
  have hstable : (prefixWord ++ tailWord_207380).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207380).length < 2 ^ (prefixWord ++ tailWord_207380).sum := by decide
  have hdescent : baseEnd_207380 < baseStart_207380 := by decide
  rcases family_descends (prefixWord ++ tailWord_207380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207386 : List Nat := [3, 1, 1, 3, 1, 1, 2, 7]
def baseStart_207386 : Nat := 118140960795 + 207386 * 2 ^ 59
def prefixEnd_207386 : Nat := 4983230072969 + 3 ^ 40 * 207386 * 2
def baseEnd_207386 : Nat := 63104414230181235568151

theorem tailTrace_207386 : CollatzResearch.WordTrace tailWord_207386 prefixEnd_207386 63104414230181235568151 := by
  unfold tailWord_207386
  simp only [CollatzResearch.WordTrace]
  refine ⟨1890997206670853888520503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5042659217788943702721341 1890997206670853888520503)
  ·
    refine ⟨2836495810006280832780755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1890997206670853888520503 2836495810006280832780755)
    ·
      refine ⟨4254743715009421249171133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2836495810006280832780755 4254743715009421249171133)
      ·
        refine ⟨1595528893128532968439175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4254743715009421249171133 1595528893128532968439175)
        ·
          refine ⟨2393293339692799452658763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1595528893128532968439175 2393293339692799452658763)
          ·
            refine ⟨3589940009539199178988145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2393293339692799452658763 3589940009539199178988145)
            ·
              refine ⟨2692455007154399384241109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3589940009539199178988145 2692455007154399384241109)
              ·
                refine ⟨63104414230181235568151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2692455007154399384241109 63104414230181235568151)
                ·
                  rfl

theorem cell19_207386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 7].length) (baseStart_207386 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_207386 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_207386 prefixEnd_207386 := by exact prefixLift 207386
  have htrace : WordTrace (prefixWord ++ tailWord_207386) baseStart_207386 baseEnd_207386 := by
    simpa [prefixWord, tailWord_207386, baseEnd_207386] using wordTrace_append hprefix tailTrace_207386
  have hstable : (prefixWord ++ tailWord_207386).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207386).length < 2 ^ (prefixWord ++ tailWord_207386).sum := by decide
  have hdescent : baseEnd_207386 < baseStart_207386 := by decide
  rcases family_descends (prefixWord ++ tailWord_207386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207437 : List Nat := [1, 6, 1, 1, 2, 3, 2, 3]
def baseStart_207437 : Nat := 118140960795 + 207437 * 2 ^ 59
def prefixEnd_207437 : Nat := 4983230072969 + 3 ^ 40 * 207437 * 2
def baseEnd_207437 : Nat := 63119932756628228434679

theorem tailTrace_207437 : CollatzResearch.WordTrace tailWord_207437 prefixEnd_207437 63119932756628228434679 := by
  unfold tailWord_207437
  simp only [CollatzResearch.WordTrace]
  refine ⟨7565848949498651264188565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5043899299665767509459043 7565848949498651264188565)
  ·
    refine ⟨354649169507749278008839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 7565848949498651264188565 354649169507749278008839)
    ·
      refine ⟨531973754261623917013259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 354649169507749278008839 531973754261623917013259)
      ·
        refine ⟨797960631392435875519889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 531973754261623917013259 797960631392435875519889)
        ·
          refine ⟨598470473544326906639917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 797960631392435875519889 598470473544326906639917)
          ·
            refine ⟨224426427579122589989969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 598470473544326906639917 224426427579122589989969)
            ·
              refine ⟨168319820684341942492477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 224426427579122589989969 168319820684341942492477)
              ·
                refine ⟨63119932756628228434679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 168319820684341942492477 63119932756628228434679)
                ·
                  rfl

theorem cell19_207437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 2, 3].length) (baseStart_207437 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_207437 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_207437 prefixEnd_207437 := by exact prefixLift 207437
  have htrace : WordTrace (prefixWord ++ tailWord_207437) baseStart_207437 baseEnd_207437 := by
    simpa [prefixWord, tailWord_207437, baseEnd_207437] using wordTrace_append hprefix tailTrace_207437
  have hstable : (prefixWord ++ tailWord_207437).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207437).length < 2 ^ (prefixWord ++ tailWord_207437).sum := by decide
  have hdescent : baseEnd_207437 < baseStart_207437 := by decide
  rcases family_descends (prefixWord ++ tailWord_207437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207441 : List Nat := [1, 2, 2, 1, 3, 3, 4, 3]
def baseStart_207441 : Nat := 118140960795 + 207441 * 2 ^ 59
def prefixEnd_207441 : Nat := 4983230072969 + 3 ^ 40 * 207441 * 2
def baseEnd_207441 : Nat := 63121149895957404345779

theorem tailTrace_207441 : CollatzResearch.WordTrace tailWord_207441 prefixEnd_207441 63121149895957404345779 := by
  unfold tailWord_207441
  simp only [CollatzResearch.WordTrace]
  refine ⟨7565994841484159947334177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5043996560989439964889451 7565994841484159947334177)
  ·
    refine ⟨5674496131113119960500633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7565994841484159947334177 5674496131113119960500633)
    ·
      refine ⟨4255872098334839970375475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5674496131113119960500633 4255872098334839970375475)
      ·
        refine ⟨6383808147502259955563213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4255872098334839970375475 6383808147502259955563213)
        ·
          refine ⟨2393928055313347483336205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6383808147502259955563213 2393928055313347483336205)
          ·
            refine ⟨897723020742505306251077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2393928055313347483336205 897723020742505306251077)
            ·
              refine ⟨168323066389219744922077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 897723020742505306251077 168323066389219744922077)
              ·
                refine ⟨63121149895957404345779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 168323066389219744922077 63121149895957404345779)
                ·
                  rfl

theorem cell19_207441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 4, 3].length) (baseStart_207441 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_207441 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_207441 prefixEnd_207441 := by exact prefixLift 207441
  have htrace : WordTrace (prefixWord ++ tailWord_207441) baseStart_207441 baseEnd_207441 := by
    simpa [prefixWord, tailWord_207441, baseEnd_207441] using wordTrace_append hprefix tailTrace_207441
  have hstable : (prefixWord ++ tailWord_207441).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207441).length < 2 ^ (prefixWord ++ tailWord_207441).sum := by decide
  have hdescent : baseEnd_207441 < baseStart_207441 := by decide
  rcases family_descends (prefixWord ++ tailWord_207441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207454 : List Nat := [4, 4, 1, 2, 1, 2, 5]
def baseStart_207454 : Nat := 118140960795 + 207454 * 2 ^ 59
def prefixEnd_207454 : Nat := 4983230072969 + 3 ^ 40 * 207454 * 2
def baseEnd_207454 : Nat := 21041701866259075352285

theorem tailTrace_207454 : CollatzResearch.WordTrace tailWord_207454 prefixEnd_207454 21041701866259075352285 := by
  unfold tailWord_207454
  simp only [CollatzResearch.WordTrace]
  refine ⟨945808623804632895944677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5044312660291375445038277 945808623804632895944677)
  ·
    refine ⟨177339116963368667989627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 945808623804632895944677 177339116963368667989627)
    ·
      refine ⟨266008675445053001984441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177339116963368667989627 266008675445053001984441)
      ·
        refine ⟨199506506583789751488331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 266008675445053001984441 199506506583789751488331)
        ·
          refine ⟨299259759875684627232497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199506506583789751488331 299259759875684627232497)
          ·
            refine ⟨224444819906763470424373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 299259759875684627232497 224444819906763470424373)
            ·
              refine ⟨21041701866259075352285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 224444819906763470424373 21041701866259075352285)
              ·
                rfl

theorem cell19_207454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 5].length) (baseStart_207454 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_207454 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_207454 prefixEnd_207454 := by exact prefixLift 207454
  have htrace : WordTrace (prefixWord ++ tailWord_207454) baseStart_207454 baseEnd_207454 := by
    simpa [prefixWord, tailWord_207454, baseEnd_207454] using wordTrace_append hprefix tailTrace_207454
  have hstable : (prefixWord ++ tailWord_207454).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207454).length < 2 ^ (prefixWord ++ tailWord_207454).sum := by decide
  have hdescent : baseEnd_207454 < baseStart_207454 := by decide
  rcases family_descends (prefixWord ++ tailWord_207454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207477 : List Nat := [1, 3, 4, 2, 2, 1, 2, 4]
def baseStart_207477 : Nat := 118140960795 + 207477 * 2 ^ 59
def prefixEnd_207477 : Nat := 4983230072969 + 3 ^ 40 * 207477 * 2
def baseEnd_207477 : Nat := 63132104149919987545681

theorem tailTrace_207477 : CollatzResearch.WordTrace tailWord_207477 prefixEnd_207477 63132104149919987545681 := by
  unfold tailWord_207477
  simp only [CollatzResearch.WordTrace]
  refine ⟨7567307869353738095644685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5044871912902492063763123 7567307869353738095644685)
  ·
    refine ⟨2837740451007651785866757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7567307869353738095644685 2837740451007651785866757)
    ·
      refine ⟨532076334563934709850017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2837740451007651785866757 532076334563934709850017)
      ·
        refine ⟨399057250922951032387513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 532076334563934709850017 399057250922951032387513)
        ·
          refine ⟨299292938192213274290635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 399057250922951032387513 299292938192213274290635)
          ·
            refine ⟨448939407288319911435953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 299292938192213274290635 448939407288319911435953)
            ·
              refine ⟨336704555466239933576965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 448939407288319911435953 336704555466239933576965)
              ·
                refine ⟨63132104149919987545681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 336704555466239933576965 63132104149919987545681)
                ·
                  rfl

theorem cell19_207477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 2, 4].length) (baseStart_207477 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_207477 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_207477 prefixEnd_207477 := by exact prefixLift 207477
  have htrace : WordTrace (prefixWord ++ tailWord_207477) baseStart_207477 baseEnd_207477 := by
    simpa [prefixWord, tailWord_207477, baseEnd_207477] using wordTrace_append hprefix tailTrace_207477
  have hstable : (prefixWord ++ tailWord_207477).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207477).length < 2 ^ (prefixWord ++ tailWord_207477).sum := by decide
  have hdescent : baseEnd_207477 < baseStart_207477 := by decide
  rcases family_descends (prefixWord ++ tailWord_207477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207481 : List Nat := [1, 2, 1, 3, 3, 2, 1, 6]
def baseStart_207481 : Nat := 118140960795 + 207481 * 2 ^ 59
def prefixEnd_207481 : Nat := 4983230072969 + 3 ^ 40 * 207481 * 2
def baseEnd_207481 : Nat := 63133321289249163456781

theorem tailTrace_207481 : CollatzResearch.WordTrace tailWord_207481 prefixEnd_207481 63133321289249163456781 := by
  unfold tailWord_207481
  simp only [CollatzResearch.WordTrace]
  refine ⟨7567453761339246778790297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5044969174226164519193531 7567453761339246778790297)
  ·
    refine ⟨5675590321004435084092723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7567453761339246778790297 5675590321004435084092723)
    ·
      refine ⟨8513385481506652626139085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5675590321004435084092723 8513385481506652626139085)
      ·
        refine ⟨3192519555564994734802157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8513385481506652626139085 3192519555564994734802157)
        ·
          refine ⟨1197194833336873025550809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3192519555564994734802157 1197194833336873025550809)
          ·
            refine ⟨897896125002654769163107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1197194833336873025550809 897896125002654769163107)
            ·
              refine ⟨1346844187503982153744661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 897896125002654769163107 1346844187503982153744661)
              ·
                refine ⟨63133321289249163456781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1346844187503982153744661 63133321289249163456781)
                ·
                  rfl

theorem cell19_207481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 6].length) (baseStart_207481 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_207481 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_207481 prefixEnd_207481 := by exact prefixLift 207481
  have htrace : WordTrace (prefixWord ++ tailWord_207481) baseStart_207481 baseEnd_207481 := by
    simpa [prefixWord, tailWord_207481, baseEnd_207481] using wordTrace_append hprefix tailTrace_207481
  have hstable : (prefixWord ++ tailWord_207481).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207481).length < 2 ^ (prefixWord ++ tailWord_207481).sum := by decide
  have hdescent : baseEnd_207481 < baseStart_207481 := by decide
  rcases family_descends (prefixWord ++ tailWord_207481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207530 : List Nat := [3, 1, 5, 2, 2, 1, 1, 4]
def baseStart_207530 : Nat := 118140960795 + 207530 * 2 ^ 59
def prefixEnd_207530 : Nat := 4983230072969 + 3 ^ 40 * 207530 * 2
def baseEnd_207530 : Nat := 63148231246031568367759

theorem tailTrace_207530 : CollatzResearch.WordTrace tailWord_207530 prefixEnd_207530 63148231246031568367759 := by
  unfold tailWord_207530
  simp only [CollatzResearch.WordTrace]
  refine ⟨1892310234540432036831011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5046160625441152098216029 1892310234540432036831011)
  ·
    refine ⟨2838465351810648055246517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1892310234540432036831011 2838465351810648055246517)
    ·
      refine ⟨266106126732248255179361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2838465351810648055246517 266106126732248255179361)
      ·
        refine ⟨199579595049186191384521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 266106126732248255179361 199579595049186191384521)
        ·
          refine ⟨149684696286889643538391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199579595049186191384521 149684696286889643538391)
          ·
            refine ⟨224527044430334465307587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149684696286889643538391 224527044430334465307587)
            ·
              refine ⟨336790566645501697961381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 224527044430334465307587 336790566645501697961381)
              ·
                refine ⟨63148231246031568367759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 336790566645501697961381 63148231246031568367759)
                ·
                  rfl

theorem cell19_207530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 1, 4].length) (baseStart_207530 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_207530 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_207530 prefixEnd_207530 := by exact prefixLift 207530
  have htrace : WordTrace (prefixWord ++ tailWord_207530) baseStart_207530 baseEnd_207530 := by
    simpa [prefixWord, tailWord_207530, baseEnd_207530] using wordTrace_append hprefix tailTrace_207530
  have hstable : (prefixWord ++ tailWord_207530).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207530).length < 2 ^ (prefixWord ++ tailWord_207530).sum := by decide
  have hdescent : baseEnd_207530 < baseStart_207530 := by decide
  rcases family_descends (prefixWord ++ tailWord_207530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207534 : List Nat := [4, 1, 4, 1, 1, 1, 3, 4]
def baseStart_207534 : Nat := 118140960795 + 207534 * 2 ^ 59
def prefixEnd_207534 : Nat := 4983230072969 + 3 ^ 40 * 207534 * 2
def baseEnd_207534 : Nat := 63149448385360744278859

theorem tailTrace_207534 : CollatzResearch.WordTrace tailWord_207534 prefixEnd_207534 63149448385360744278859 := by
  unfold tailWord_207534
  simp only [CollatzResearch.WordTrace]
  refine ⟨946173353768404603808707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5046257886764824553646437 946173353768404603808707)
  ·
    refine ⟨1419260030652606905713061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 946173353768404603808707 1419260030652606905713061)
    ·
      refine ⟨266111255747363794821199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1419260030652606905713061 266111255747363794821199)
      ·
        refine ⟨399166883621045692231799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266111255747363794821199 399166883621045692231799)
        ·
          refine ⟨598750325431568538347699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 399166883621045692231799 598750325431568538347699)
          ·
            refine ⟨898125488147352807521549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 598750325431568538347699 898125488147352807521549)
            ·
              refine ⟨336797058055257302820581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 898125488147352807521549 336797058055257302820581)
              ·
                refine ⟨63149448385360744278859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 336797058055257302820581 63149448385360744278859)
                ·
                  rfl

theorem cell19_207534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 3, 4].length) (baseStart_207534 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_207534 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_207534 prefixEnd_207534 := by exact prefixLift 207534
  have htrace : WordTrace (prefixWord ++ tailWord_207534) baseStart_207534 baseEnd_207534 := by
    simpa [prefixWord, tailWord_207534, baseEnd_207534] using wordTrace_append hprefix tailTrace_207534
  have hstable : (prefixWord ++ tailWord_207534).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207534).length < 2 ^ (prefixWord ++ tailWord_207534).sum := by decide
  have hdescent : baseEnd_207534 < baseStart_207534 := by decide
  rcases family_descends (prefixWord ++ tailWord_207534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207576 : List Nat := [2, 1, 2, 2, 3, 3, 6]
def baseStart_207576 : Nat := 118140960795 + 207576 * 2 ^ 59
def prefixEnd_207576 : Nat := 4983230072969 + 3 ^ 40 * 207576 * 2
def baseEnd_207576 : Nat := 21054076116105697115137

theorem tailTrace_207576 : CollatzResearch.WordTrace tailWord_207576 prefixEnd_207576 21054076116105697115137 := by
  unfold tailWord_207576
  simp only [CollatzResearch.WordTrace]
  refine ⟨3785459347997539001749291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5047279130663385335665721 3785459347997539001749291)
  ·
    refine ⟨5678189021996308502623937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3785459347997539001749291 5678189021996308502623937)
    ·
      refine ⟨4258641766497231376967953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5678189021996308502623937 4258641766497231376967953)
      ·
        refine ⟨3193981324872923532725965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4258641766497231376967953 3193981324872923532725965)
        ·
          refine ⟨1197742996827346324772237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3193981324872923532725965 1197742996827346324772237)
          ·
            refine ⟨449153623810254871789589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1197742996827346324772237 449153623810254871789589)
            ·
              refine ⟨21054076116105697115137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 449153623810254871789589 21054076116105697115137)
              ·
                rfl

theorem cell19_207576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 6].length) (baseStart_207576 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_207576 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_207576 prefixEnd_207576 := by exact prefixLift 207576
  have htrace : WordTrace (prefixWord ++ tailWord_207576) baseStart_207576 baseEnd_207576 := by
    simpa [prefixWord, tailWord_207576, baseEnd_207576] using wordTrace_append hprefix tailTrace_207576
  have hstable : (prefixWord ++ tailWord_207576).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207576).length < 2 ^ (prefixWord ++ tailWord_207576).sum := by decide
  have hdescent : baseEnd_207576 < baseStart_207576 := by decide
  rcases family_descends (prefixWord ++ tailWord_207576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207604 : List Nat := [2, 6, 1, 1, 3, 1, 2, 3]
def baseStart_207604 : Nat := 118140960795 + 207604 * 2 ^ 59
def prefixEnd_207604 : Nat := 4983230072969 + 3 ^ 40 * 207604 * 2
def baseEnd_207604 : Nat := 63170748323621322723113

theorem tailTrace_207604 : CollatzResearch.WordTrace tailWord_207604 prefixEnd_207604 63170748323621322723113 := by
  unfold tailWord_207604
  simp only [CollatzResearch.WordTrace]
  refine ⟨3785969969946819392758933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5047959959929092523678577 3785969969946819392758933)
  ·
    refine ⟨177467342341257159035575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 3785969969946819392758933 177467342341257159035575)
    ·
      refine ⟨266201013511885738553363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177467342341257159035575 266201013511885738553363)
      ·
        refine ⟨399301520267828607830045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266201013511885738553363 399301520267828607830045)
        ·
          refine ⟨149738070100435727936267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 399301520267828607830045 149738070100435727936267)
          ·
            refine ⟨224607105150653591904401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149738070100435727936267 224607105150653591904401)
            ·
              refine ⟨168455328862990193928301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 224607105150653591904401 168455328862990193928301)
              ·
                refine ⟨63170748323621322723113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 168455328862990193928301 63170748323621322723113)
                ·
                  rfl

theorem cell19_207604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 2, 3].length) (baseStart_207604 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_207604 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_207604 prefixEnd_207604 := by exact prefixLift 207604
  have htrace : WordTrace (prefixWord ++ tailWord_207604) baseStart_207604 baseEnd_207604 := by
    simpa [prefixWord, tailWord_207604, baseEnd_207604] using wordTrace_append hprefix tailTrace_207604
  have hstable : (prefixWord ++ tailWord_207604).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207604).length < 2 ^ (prefixWord ++ tailWord_207604).sum := by decide
  have hdescent : baseEnd_207604 < baseStart_207604 := by decide
  rcases family_descends (prefixWord ++ tailWord_207604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207612 : List Nat := [2, 2, 2, 1, 3, 2, 4, 3]
def baseStart_207612 : Nat := 118140960795 + 207612 * 2 ^ 59
def prefixEnd_207612 : Nat := 4983230072969 + 3 ^ 40 * 207612 * 2
def baseEnd_207612 : Nat := 63173182602279674545313

theorem tailTrace_207612 : CollatzResearch.WordTrace tailWord_207612 prefixEnd_207612 63173182602279674545313 := by
  unfold tailWord_207612
  simp only [CollatzResearch.WordTrace]
  refine ⟨3786115861932328075904545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5048154482576437434539393 3786115861932328075904545)
  ·
    refine ⟨2839586896449246056928409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3786115861932328075904545 2839586896449246056928409)
    ·
      refine ⟨2129690172336934542696307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2839586896449246056928409 2129690172336934542696307)
      ·
        refine ⟨3194535258505401814044461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2129690172336934542696307 3194535258505401814044461)
        ·
          refine ⟨1197950721939525680266673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3194535258505401814044461 1197950721939525680266673)
          ·
            refine ⟨898463041454644260200005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1197950721939525680266673 898463041454644260200005)
            ·
              refine ⟨168461820272745798787501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 898463041454644260200005 168461820272745798787501)
              ·
                refine ⟨63173182602279674545313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 168461820272745798787501 63173182602279674545313)
                ·
                  rfl

theorem cell19_207612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 4, 3].length) (baseStart_207612 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_207612 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_207612 prefixEnd_207612 := by exact prefixLift 207612
  have htrace : WordTrace (prefixWord ++ tailWord_207612) baseStart_207612 baseEnd_207612 := by
    simpa [prefixWord, tailWord_207612, baseEnd_207612] using wordTrace_append hprefix tailTrace_207612
  have hstable : (prefixWord ++ tailWord_207612).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207612).length < 2 ^ (prefixWord ++ tailWord_207612).sum := by decide
  have hdescent : baseEnd_207612 < baseStart_207612 := by decide
  rcases family_descends (prefixWord ++ tailWord_207612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207650 : List Nat := [3, 3, 1, 1, 2, 3, 2, 4]
def baseStart_207650 : Nat := 118140960795 + 207650 * 2 ^ 59
def prefixEnd_207650 : Nat := 4983230072969 + 3 ^ 40 * 207650 * 2
def baseEnd_207650 : Nat := 63184745425906845700765

theorem tailTrace_207650 : CollatzResearch.WordTrace tailWord_207650 prefixEnd_207650 63184745425906845700765 := by
  unfold tailWord_207650
  simp only [CollatzResearch.WordTrace]
  refine ⟨1893404424431747160423101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5049078465151325761128269 1893404424431747160423101)
  ·
    refine ⟨710026659161905185158663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1893404424431747160423101 710026659161905185158663)
    ·
      refine ⟨1065039988742857777737995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 710026659161905185158663 1065039988742857777737995)
      ·
        refine ⟨1597559983114286666606993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1065039988742857777737995 1597559983114286666606993)
        ·
          refine ⟨1198169987335714999955245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1597559983114286666606993 1198169987335714999955245)
          ·
            refine ⟨449313745250893124983217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1198169987335714999955245 449313745250893124983217)
            ·
              refine ⟨336985308938169843737413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 449313745250893124983217 336985308938169843737413)
              ·
                refine ⟨63184745425906845700765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 336985308938169843737413 63184745425906845700765)
                ·
                  rfl

theorem cell19_207650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2, 4].length) (baseStart_207650 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_207650 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_207650 prefixEnd_207650 := by exact prefixLift 207650
  have htrace : WordTrace (prefixWord ++ tailWord_207650) baseStart_207650 baseEnd_207650 := by
    simpa [prefixWord, tailWord_207650, baseEnd_207650] using wordTrace_append hprefix tailTrace_207650
  have hstable : (prefixWord ++ tailWord_207650).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207650).length < 2 ^ (prefixWord ++ tailWord_207650).sum := by decide
  have hdescent : baseEnd_207650 < baseStart_207650 := by decide
  rcases family_descends (prefixWord ++ tailWord_207650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207686 : List Nat := [6, 1, 1, 2, 2, 7]
def baseStart_207686 : Nat := 118140960795 + 207686 * 2 ^ 59
def prefixEnd_207686 : Nat := 4983230072969 + 3 ^ 40 * 207686 * 2
def baseEnd_207686 : Nat := 7021744408874380988963

theorem tailTrace_207686 : CollatzResearch.WordTrace tailWord_207686 prefixEnd_207686 7021744408874380988963 := by
  unfold tailWord_207686
  simp only [CollatzResearch.WordTrace]
  refine ⟨236716585174892712187591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 5049953817064377860001941 236716585174892712187591)
  ·
    refine ⟨355074877762339068281387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236716585174892712187591 355074877762339068281387)
    ·
      refine ⟨532612316643508602422081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 355074877762339068281387 532612316643508602422081)
      ·
        refine ⟨399459237482631451816561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 532612316643508602422081 399459237482631451816561)
        ·
          refine ⟨299594428111973588862421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 399459237482631451816561 299594428111973588862421)
          ·
            refine ⟨7021744408874380988963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 299594428111973588862421 7021744408874380988963)
            ·
              rfl

theorem cell19_207686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 7].length) (baseStart_207686 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_207686 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_207686 prefixEnd_207686 := by exact prefixLift 207686
  have htrace : WordTrace (prefixWord ++ tailWord_207686) baseStart_207686 baseEnd_207686 := by
    simpa [prefixWord, tailWord_207686, baseEnd_207686] using wordTrace_append hprefix tailTrace_207686
  have hstable : (prefixWord ++ tailWord_207686).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207686).length < 2 ^ (prefixWord ++ tailWord_207686).sum := by decide
  have hdescent : baseEnd_207686 < baseStart_207686 := by decide
  rcases family_descends (prefixWord ++ tailWord_207686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207783 : List Nat := [1, 1, 6, 1, 3, 1, 1, 5]
def baseStart_207783 : Nat := 118140960795 + 207783 * 2 ^ 59
def prefixEnd_207783 : Nat := 4983230072969 + 3 ^ 40 * 207783 * 2
def baseEnd_207783 : Nat := 63225215308601944744847

theorem tailTrace_207783 : CollatzResearch.WordTrace tailWord_207783 prefixEnd_207783 63225215308601944744847 := by
  unfold tailWord_207783
  simp only [CollatzResearch.WordTrace]
  refine ⟨7578468606245152356284003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5052312404163434904189335 7578468606245152356284003)
  ·
    refine ⟨11367702909367728534426005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7578468606245152356284003 11367702909367728534426005)
    ·
      refine ⟨532861073876612275051219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 11367702909367728534426005 532861073876612275051219)
      ·
        refine ⟨799291610814918412576829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 532861073876612275051219 799291610814918412576829)
        ·
          refine ⟨299734354055594404716311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 799291610814918412576829 299734354055594404716311)
          ·
            refine ⟨449601531083391607074467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 299734354055594404716311 449601531083391607074467)
            ·
              refine ⟨674402296625087410611701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 449601531083391607074467 674402296625087410611701)
              ·
                refine ⟨63225215308601944744847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 674402296625087410611701 63225215308601944744847)
                ·
                  rfl

theorem cell19_207783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 5].length) (baseStart_207783 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_207783 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_207783 prefixEnd_207783 := by exact prefixLift 207783
  have htrace : WordTrace (prefixWord ++ tailWord_207783) baseStart_207783 baseEnd_207783 := by
    simpa [prefixWord, tailWord_207783, baseEnd_207783] using wordTrace_append hprefix tailTrace_207783
  have hstable : (prefixWord ++ tailWord_207783).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207783).length < 2 ^ (prefixWord ++ tailWord_207783).sum := by decide
  have hdescent : baseEnd_207783 < baseStart_207783 := by decide
  rcases family_descends (prefixWord ++ tailWord_207783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207787 : List Nat := [1, 1, 1, 1, 2, 1, 1, 11]
def baseStart_207787 : Nat := 118140960795 + 207787 * 2 ^ 59
def prefixEnd_207787 : Nat := 4983230072969 + 3 ^ 40 * 207787 * 2
def baseEnd_207787 : Nat := 63226432447931120655947

theorem tailTrace_207787 : CollatzResearch.WordTrace tailWord_207787 prefixEnd_207787 63226432447931120655947 := by
  unfold tailWord_207787
  simp only [CollatzResearch.WordTrace]
  refine ⟨7578614498230661039429615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5052409665487107359619743 7578614498230661039429615)
  ·
    refine ⟨11367921747345991559144423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7578614498230661039429615 11367921747345991559144423)
    ·
      refine ⟨17051882621018987338716635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11367921747345991559144423 17051882621018987338716635)
      ·
        refine ⟨25577823931528481008074953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17051882621018987338716635 25577823931528481008074953)
        ·
          refine ⟨19183367948646360756056215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25577823931528481008074953 19183367948646360756056215)
          ·
            refine ⟨28775051922969541134084323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19183367948646360756056215 28775051922969541134084323)
            ·
              refine ⟨43162577884454311701126485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28775051922969541134084323 43162577884454311701126485)
              ·
                refine ⟨63226432447931120655947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 43162577884454311701126485 63226432447931120655947)
                ·
                  rfl

theorem cell19_207787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 11].length) (baseStart_207787 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_207787 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_207787 prefixEnd_207787 := by exact prefixLift 207787
  have htrace : WordTrace (prefixWord ++ tailWord_207787) baseStart_207787 baseEnd_207787 := by
    simpa [prefixWord, tailWord_207787, baseEnd_207787] using wordTrace_append hprefix tailTrace_207787
  have hstable : (prefixWord ++ tailWord_207787).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207787).length < 2 ^ (prefixWord ++ tailWord_207787).sum := by decide
  have hdescent : baseEnd_207787 < baseStart_207787 := by decide
  rcases family_descends (prefixWord ++ tailWord_207787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207823 : List Nat := [1, 1, 2, 1, 1, 7, 2, 4]
def baseStart_207823 : Nat := 118140960795 + 207823 * 2 ^ 59
def prefixEnd_207823 : Nat := 4983230072969 + 3 ^ 40 * 207823 * 2
def baseEnd_207823 : Nat := 63237386701893703855849

theorem tailTrace_207823 : CollatzResearch.WordTrace tailWord_207823 prefixEnd_207823 63237386701893703855849 := by
  unfold tailWord_207823
  simp only [CollatzResearch.WordTrace]
  refine ⟨7579927526100239187740123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5053285017400159458493415 7579927526100239187740123)
  ·
    refine ⟨11369891289150358781610185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7579927526100239187740123 11369891289150358781610185)
    ·
      refine ⟨8527418466862769086207639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11369891289150358781610185 8527418466862769086207639)
      ·
        refine ⟨12791127700294153629311459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8527418466862769086207639 12791127700294153629311459)
        ·
          refine ⟨19186691550441230443967189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12791127700294153629311459 19186691550441230443967189)
          ·
            refine ⟨449688083213466338530481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 19186691550441230443967189 449688083213466338530481)
            ·
              refine ⟨337266062410099753897861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 449688083213466338530481 337266062410099753897861)
              ·
                refine ⟨63237386701893703855849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 337266062410099753897861 63237386701893703855849)
                ·
                  rfl

theorem cell19_207823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2, 4].length) (baseStart_207823 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_207823 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_207823 prefixEnd_207823 := by exact prefixLift 207823
  have htrace : WordTrace (prefixWord ++ tailWord_207823) baseStart_207823 baseEnd_207823 := by
    simpa [prefixWord, tailWord_207823, baseEnd_207823] using wordTrace_append hprefix tailTrace_207823
  have hstable : (prefixWord ++ tailWord_207823).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207823).length < 2 ^ (prefixWord ++ tailWord_207823).sum := by decide
  have hdescent : baseEnd_207823 < baseStart_207823 := by decide
  rcases family_descends (prefixWord ++ tailWord_207823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207874 : List Nat := [3, 4, 1, 3, 1, 2, 1, 4]
def baseStart_207874 : Nat := 118140960795 + 207874 * 2 ^ 59
def prefixEnd_207874 : Nat := 4983230072969 + 3 ^ 40 * 207874 * 2
def baseEnd_207874 : Nat := 63252905228340696722377

theorem tailTrace_207874 : CollatzResearch.WordTrace tailWord_207874 prefixEnd_207874 63252905228340696722377 := by
  unfold tailWord_207874
  simp only [CollatzResearch.WordTrace]
  refine ⟨1895446912228868724461669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5054525099276983265231117 1895446912228868724461669)
  ·
    refine ⟨355396296042912885836563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1895446912228868724461669 355396296042912885836563)
    ·
      refine ⟨533094444064369328754845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 355396296042912885836563 533094444064369328754845)
      ·
        refine ⟨199910416524138498283067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 533094444064369328754845 199910416524138498283067)
        ·
          refine ⟨299865624786207747424601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199910416524138498283067 299865624786207747424601)
          ·
            refine ⟨224899218589655810568451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 299865624786207747424601 224899218589655810568451)
            ·
              refine ⟨337348827884483715852677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 224899218589655810568451 337348827884483715852677)
              ·
                refine ⟨63252905228340696722377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 337348827884483715852677 63252905228340696722377)
                ·
                  rfl

theorem cell19_207874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 1, 4].length) (baseStart_207874 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_207874 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_207874 prefixEnd_207874 := by exact prefixLift 207874
  have htrace : WordTrace (prefixWord ++ tailWord_207874) baseStart_207874 baseEnd_207874 := by
    simpa [prefixWord, tailWord_207874, baseEnd_207874] using wordTrace_append hprefix tailTrace_207874
  have hstable : (prefixWord ++ tailWord_207874).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207874).length < 2 ^ (prefixWord ++ tailWord_207874).sum := by decide
  have hdescent : baseEnd_207874 < baseStart_207874 := by decide
  rcases family_descends (prefixWord ++ tailWord_207874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207880 : List Nat := [2, 1, 3, 2, 1, 3, 3, 4]
def baseStart_207880 : Nat := 118140960795 + 207880 * 2 ^ 59
def prefixEnd_207880 : Nat := 4983230072969 + 3 ^ 40 * 207880 * 2
def baseEnd_207880 : Nat := 63254730937334460589027

theorem tailTrace_207880 : CollatzResearch.WordTrace tailWord_207880 prefixEnd_207880 63254730937334460589027 := by
  unfold tailWord_207880
  simp only [CollatzResearch.WordTrace]
  refine ⟨3791003243446868961282547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5054670991262491948376729 3791003243446868961282547)
  ·
    refine ⟨5686504865170303441923821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3791003243446868961282547 5686504865170303441923821)
    ·
      refine ⟨2132439324438863790721433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5686504865170303441923821 2132439324438863790721433)
      ·
        refine ⟨1599329493329147843041075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2132439324438863790721433 1599329493329147843041075)
        ·
          refine ⟨2398994239993721764561613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1599329493329147843041075 2398994239993721764561613)
          ·
            refine ⟨899622839997645661710605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2398994239993721764561613 899622839997645661710605)
            ·
              refine ⟨337358564999117123141477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 899622839997645661710605 337358564999117123141477)
              ·
                refine ⟨63254730937334460589027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 337358564999117123141477 63254730937334460589027)
                ·
                  rfl

theorem cell19_207880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3, 4].length) (baseStart_207880 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_207880 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_207880 prefixEnd_207880 := by exact prefixLift 207880
  have htrace : WordTrace (prefixWord ++ tailWord_207880) baseStart_207880 baseEnd_207880 := by
    simpa [prefixWord, tailWord_207880, baseEnd_207880] using wordTrace_append hprefix tailTrace_207880
  have hstable : (prefixWord ++ tailWord_207880).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207880).length < 2 ^ (prefixWord ++ tailWord_207880).sum := by decide
  have hdescent : baseEnd_207880 < baseStart_207880 := by decide
  rcases family_descends (prefixWord ++ tailWord_207880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207918 : List Nat := [4, 1, 3, 1, 1, 1, 8]
def baseStart_207918 : Nat := 118140960795 + 207918 * 2 ^ 59
def prefixEnd_207918 : Nat := 4983230072969 + 3 ^ 40 * 207918 * 2
def baseEnd_207918 : Nat := 21088764586987210581493

theorem tailTrace_207918 : CollatzResearch.WordTrace tailWord_207918 prefixEnd_207918 21088764586987210581493 := by
  unfold tailWord_207918
  simp only [CollatzResearch.WordTrace]
  refine ⟨947924057594508801556051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5055594973837380274965605 947924057594508801556051)
  ·
    refine ⟨1421886086391763202334077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 947924057594508801556051 1421886086391763202334077)
    ·
      refine ⟨533207282396911200875279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1421886086391763202334077 533207282396911200875279)
      ·
        refine ⟨799810923595366801312919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 533207282396911200875279 799810923595366801312919)
        ·
          refine ⟨1199716385393050201969379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 799810923595366801312919 1199716385393050201969379)
          ·
            refine ⟨1799574578089575302954069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1199716385393050201969379 1799574578089575302954069)
            ·
              refine ⟨21088764586987210581493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1799574578089575302954069 21088764586987210581493)
              ·
                rfl

theorem cell19_207918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 8].length) (baseStart_207918 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_207918 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_207918 prefixEnd_207918 := by exact prefixLift 207918
  have htrace : WordTrace (prefixWord ++ tailWord_207918) baseStart_207918 baseEnd_207918 := by
    simpa [prefixWord, tailWord_207918, baseEnd_207918] using wordTrace_append hprefix tailTrace_207918
  have hstable : (prefixWord ++ tailWord_207918).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207918).length < 2 ^ (prefixWord ++ tailWord_207918).sum := by decide
  have hdescent : baseEnd_207918 < baseStart_207918 := by decide
  rcases family_descends (prefixWord ++ tailWord_207918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207920 : List Nat := [2, 1, 1, 1, 2, 4, 8]
def baseStart_207920 : Nat := 118140960795 + 207920 * 2 ^ 59
def prefixEnd_207920 : Nat := 4983230072969 + 3 ^ 40 * 207920 * 2
def baseEnd_207920 : Nat := 21088967443542073233343

theorem tailTrace_207920 : CollatzResearch.WordTrace tailWord_207920 prefixEnd_207920 21088967443542073233343 := by
  unfold tailWord_207920
  simp only [CollatzResearch.WordTrace]
  refine ⟨3791732703374412377010607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5055643604499216502680809 3791732703374412377010607)
  ·
    refine ⟨5687599055061618565515911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3791732703374412377010607 5687599055061618565515911)
    ·
      refine ⟨8531398582592427848273867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5687599055061618565515911 8531398582592427848273867)
      ·
        refine ⟨12797097873888641772410801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8531398582592427848273867 12797097873888641772410801)
        ·
          refine ⟨9597823405416481329308101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12797097873888641772410801 9597823405416481329308101)
          ·
            refine ⟨1799591888515590249245269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9597823405416481329308101 1799591888515590249245269)
            ·
              refine ⟨21088967443542073233343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1799591888515590249245269 21088967443542073233343)
              ·
                rfl

theorem cell19_207920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 8].length) (baseStart_207920 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_207920 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_207920 prefixEnd_207920 := by exact prefixLift 207920
  have htrace : WordTrace (prefixWord ++ tailWord_207920) baseStart_207920 baseEnd_207920 := by
    simpa [prefixWord, tailWord_207920, baseEnd_207920] using wordTrace_append hprefix tailTrace_207920
  have hstable : (prefixWord ++ tailWord_207920).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207920).length < 2 ^ (prefixWord ++ tailWord_207920).sum := by decide
  have hdescent : baseEnd_207920 < baseStart_207920 := by decide
  rcases family_descends (prefixWord ++ tailWord_207920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207939 : List Nat := [1, 1, 1, 3, 1, 2, 4, 6]
def baseStart_207939 : Nat := 118140960795 + 207939 * 2 ^ 59
def prefixEnd_207939 : Nat := 4983230072969 + 3 ^ 40 * 207939 * 2
def baseEnd_207939 : Nat := 63272683742439805277755

theorem tailTrace_207939 : CollatzResearch.WordTrace tailWord_207939 prefixEnd_207939 63272683742439805277755 := by
  unfold tailWord_207939
  simp only [CollatzResearch.WordTrace]
  refine ⟨7584158393679990998962871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5056105595786660665975247 7584158393679990998962871)
  ·
    refine ⟨11376237590519986498444307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7584158393679990998962871 11376237590519986498444307)
    ·
      refine ⟨17064356385779979747666461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11376237590519986498444307 17064356385779979747666461)
      ·
        refine ⟨6399133644667492405374923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17064356385779979747666461 6399133644667492405374923)
        ·
          refine ⟨9598700467001238608062385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6399133644667492405374923 9598700467001238608062385)
          ·
            refine ⟨7199025350250928956046789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9598700467001238608062385 7199025350250928956046789)
            ·
              refine ⟨1349817253172049179258773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7199025350250928956046789 1349817253172049179258773)
              ·
                refine ⟨63272683742439805277755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1349817253172049179258773 63272683742439805277755)
                ·
                  rfl

theorem cell19_207939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 6].length) (baseStart_207939 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_207939 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_207939 prefixEnd_207939 := by exact prefixLift 207939
  have htrace : WordTrace (prefixWord ++ tailWord_207939) baseStart_207939 baseEnd_207939 := by
    simpa [prefixWord, tailWord_207939, baseEnd_207939] using wordTrace_append hprefix tailTrace_207939
  have hstable : (prefixWord ++ tailWord_207939).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207939).length < 2 ^ (prefixWord ++ tailWord_207939).sum := by decide
  have hdescent : baseEnd_207939 < baseStart_207939 := by decide
  rcases family_descends (prefixWord ++ tailWord_207939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207954 : List Nat := [3, 2, 2, 1, 3, 1, 4, 3]
def baseStart_207954 : Nat := 118140960795 + 207954 * 2 ^ 59
def prefixEnd_207954 : Nat := 4983230072969 + 3 ^ 40 * 207954 * 2
def baseEnd_207954 : Nat := 63277248014924214944381

theorem tailTrace_207954 : CollatzResearch.WordTrace tailWord_207954 prefixEnd_207954 63277248014924214944381 := by
  unfold tailWord_207954
  simp only [CollatzResearch.WordTrace]
  refine ⟨1896176372156412140189729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5056470325750432373839277 1896176372156412140189729)
  ·
    refine ⟨1422132279117309105142297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1896176372156412140189729 1422132279117309105142297)
    ·
      refine ⟨1066599209337981828856723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1422132279117309105142297 1066599209337981828856723)
      ·
        refine ⟨1599898814006972743285085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1066599209337981828856723 1599898814006972743285085)
        ·
          refine ⟨599962055252614778731907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1599898814006972743285085 599962055252614778731907)
          ·
            refine ⟨899943082878922168097861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 599962055252614778731907 899943082878922168097861)
            ·
              refine ⟨168739328039797906518349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 899943082878922168097861 168739328039797906518349)
              ·
                refine ⟨63277248014924214944381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 168739328039797906518349 63277248014924214944381)
                ·
                  rfl

theorem cell19_207954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 4, 3].length) (baseStart_207954 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_207954 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_207954 prefixEnd_207954 := by exact prefixLift 207954
  have htrace : WordTrace (prefixWord ++ tailWord_207954) baseStart_207954 baseEnd_207954 := by
    simpa [prefixWord, tailWord_207954, baseEnd_207954] using wordTrace_append hprefix tailTrace_207954
  have hstable : (prefixWord ++ tailWord_207954).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207954).length < 2 ^ (prefixWord ++ tailWord_207954).sum := by decide
  have hdescent : baseEnd_207954 < baseStart_207954 := by decide
  rcases family_descends (prefixWord ++ tailWord_207954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207975 : List Nat := [1, 1, 5, 1, 1, 5, 5]
def baseStart_207975 : Nat := 118140960795 + 207975 * 2 ^ 59
def prefixEnd_207975 : Nat := 4983230072969 + 3 ^ 40 * 207975 * 2
def baseEnd_207975 : Nat := 21094545998800796159219

theorem tailTrace_207975 : CollatzResearch.WordTrace tailWord_207975 prefixEnd_207975 21094545998800796159219 := by
  unfold tailWord_207975
  simp only [CollatzResearch.WordTrace]
  refine ⟨7585471421549569147273379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5056980947699712764848919 7585471421549569147273379)
  ·
    refine ⟨11378207132324353720910069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7585471421549569147273379 11378207132324353720910069)
    ·
      refine ⟨1066706918655408161335319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11378207132324353720910069 1066706918655408161335319)
      ·
        refine ⟨1600060377983112242002979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1066706918655408161335319 1600060377983112242002979)
        ·
          refine ⟨2400090566974668363004469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1600060377983112242002979 2400090566974668363004469)
          ·
            refine ⟨225008490653875159031669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2400090566974668363004469 225008490653875159031669)
            ·
              refine ⟨21094545998800796159219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 225008490653875159031669 21094545998800796159219)
              ·
                rfl

theorem cell19_207975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 5].length) (baseStart_207975 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_207975 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_207975 prefixEnd_207975 := by exact prefixLift 207975
  have htrace : WordTrace (prefixWord ++ tailWord_207975) baseStart_207975 baseEnd_207975 := by
    simpa [prefixWord, tailWord_207975, baseEnd_207975] using wordTrace_append hprefix tailTrace_207975
  have hstable : (prefixWord ++ tailWord_207975).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207975).length < 2 ^ (prefixWord ++ tailWord_207975).sum := by decide
  have hdescent : baseEnd_207975 < baseStart_207975 := by decide
  rcases family_descends (prefixWord ++ tailWord_207975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207977 : List Nat := [1, 2, 1, 1, 1, 6, 7]
def baseStart_207977 : Nat := 118140960795 + 207977 * 2 ^ 59
def prefixEnd_207977 : Nat := 4983230072969 + 3 ^ 40 * 207977 * 2
def baseEnd_207977 : Nat := 21094748855355658811069

theorem tailTrace_207977 : CollatzResearch.WordTrace tailWord_207977 prefixEnd_207977 21094748855355658811069 := by
  unfold tailWord_207977
  simp only [CollatzResearch.WordTrace]
  refine ⟨7585544367542323488846185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5057029578361548992564123 7585544367542323488846185)
  ·
    refine ⟨5689158275656742616634639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7585544367542323488846185 5689158275656742616634639)
    ·
      refine ⟨8533737413485113924951959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5689158275656742616634639 8533737413485113924951959)
      ·
        refine ⟨12800606120227670887427939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8533737413485113924951959 12800606120227670887427939)
        ·
          refine ⟨19200909180341506331141909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12800606120227670887427939 19200909180341506331141909)
          ·
            refine ⟨900042617828508109272277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 19200909180341506331141909 900042617828508109272277)
            ·
              refine ⟨21094748855355658811069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 900042617828508109272277 21094748855355658811069)
              ·
                rfl

theorem cell19_207977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 7].length) (baseStart_207977 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_207977 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_207977 prefixEnd_207977 := by exact prefixLift 207977
  have htrace : WordTrace (prefixWord ++ tailWord_207977) baseStart_207977 baseEnd_207977 := by
    simpa [prefixWord, tailWord_207977, baseEnd_207977] using wordTrace_append hprefix tailTrace_207977
  have hstable : (prefixWord ++ tailWord_207977).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207977).length < 2 ^ (prefixWord ++ tailWord_207977).sum := by decide
  have hdescent : baseEnd_207977 < baseStart_207977 := by decide
  rcases family_descends (prefixWord ++ tailWord_207977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208049 : List Nat := [1, 2, 2, 5, 1, 3, 1, 4]
def baseStart_208049 : Nat := 118140960795 + 208049 * 2 ^ 59
def prefixEnd_208049 : Nat := 4983230072969 + 3 ^ 40 * 208049 * 2
def baseEnd_208049 : Nat := 63306155073992142833011

theorem tailTrace_208049 : CollatzResearch.WordTrace tailWord_208049 prefixEnd_208049 63306155073992142833011 := by
  unfold tailWord_208049
  simp only [CollatzResearch.WordTrace]
  refine ⟨7588170423281479785467201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5058780282187653190311467 7588170423281479785467201)
  ·
    refine ⟨5691127817461109839100401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7588170423281479785467201 5691127817461109839100401)
    ·
      refine ⟨4268345863095832379325301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5691127817461109839100401 4268345863095832379325301)
      ·
        refine ⟨400157424665234285561747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4268345863095832379325301 400157424665234285561747)
        ·
          refine ⟨600236136997851428342621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 400157424665234285561747 600236136997851428342621)
          ·
            refine ⟨225088551374194285628483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 600236136997851428342621 225088551374194285628483)
            ·
              refine ⟨337632827061291428442725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 225088551374194285628483 337632827061291428442725)
              ·
                refine ⟨63306155073992142833011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 337632827061291428442725 63306155073992142833011)
                ·
                  rfl

theorem cell19_208049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 1, 4].length) (baseStart_208049 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_208049 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_208049 prefixEnd_208049 := by exact prefixLift 208049
  have htrace : WordTrace (prefixWord ++ tailWord_208049) baseStart_208049 baseEnd_208049 := by
    simpa [prefixWord, tailWord_208049, baseEnd_208049] using wordTrace_append hprefix tailTrace_208049
  have hstable : (prefixWord ++ tailWord_208049).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208049).length < 2 ^ (prefixWord ++ tailWord_208049).sum := by decide
  have hdescent : baseEnd_208049 < baseStart_208049 := by decide
  rcases family_descends (prefixWord ++ tailWord_208049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208072 : List Nat := [2, 1, 3, 1, 2, 1, 2, 7]
def baseStart_208072 : Nat := 118140960795 + 208072 * 2 ^ 59
def prefixEnd_208072 : Nat := 4983230072969 + 3 ^ 40 * 208072 * 2
def baseEnd_208072 : Nat := 63313153625134904321837

theorem tailTrace_208072 : CollatzResearch.WordTrace tailWord_208072 prefixEnd_208072 63313153625134904321837 := by
  unfold tailWord_208072
  simp only [CollatzResearch.WordTrace]
  refine ⟨3794504651099077356777235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5059339534798769809036313 3794504651099077356777235)
  ·
    refine ⟨5691756976648616035165853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3794504651099077356777235 5691756976648616035165853)
    ·
      refine ⟨2134408866243231013187195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5691756976648616035165853 2134408866243231013187195)
      ·
        refine ⟨3201613299364846519780793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2134408866243231013187195 3201613299364846519780793)
        ·
          refine ⟨2401209974523634889835595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3201613299364846519780793 2401209974523634889835595)
          ·
            refine ⟨3601814961785452334753393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2401209974523634889835595 3601814961785452334753393)
            ·
              refine ⟨2701361221339089251065045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3601814961785452334753393 2701361221339089251065045)
              ·
                refine ⟨63313153625134904321837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2701361221339089251065045 63313153625134904321837)
                ·
                  rfl

theorem cell19_208072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 7].length) (baseStart_208072 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_208072 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_208072 prefixEnd_208072 := by exact prefixLift 208072
  have htrace : WordTrace (prefixWord ++ tailWord_208072) baseStart_208072 baseEnd_208072 := by
    simpa [prefixWord, tailWord_208072, baseEnd_208072] using wordTrace_append hprefix tailTrace_208072
  have hstable : (prefixWord ++ tailWord_208072).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208072).length < 2 ^ (prefixWord ++ tailWord_208072).sum := by decide
  have hdescent : baseEnd_208072 < baseStart_208072 := by decide
  rcases family_descends (prefixWord ++ tailWord_208072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208127 : List Nat := [1, 1, 2, 2, 1, 5, 4, 3]
def baseStart_208127 : Nat := 118140960795 + 208127 * 2 ^ 59
def prefixEnd_208127 : Nat := 4983230072969 + 3 ^ 40 * 208127 * 2
def baseEnd_208127 : Nat := 63329889290911073099465

theorem tailTrace_208127 : CollatzResearch.WordTrace tailWord_208127 prefixEnd_208127 63329889290911073099465 := by
  unfold tailWord_208127
  simp only [CollatzResearch.WordTrace]
  refine ⟨7591015316998899106806635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5060676877999266071204423 7591015316998899106806635)
  ·
    refine ⟨11386522975498348660209953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7591015316998899106806635 11386522975498348660209953)
    ·
      refine ⟨8539892231623761495157465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11386522975498348660209953 8539892231623761495157465)
      ·
        refine ⟨6404919173717821121368099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8539892231623761495157465 6404919173717821121368099)
        ·
          refine ⟨9607378760576731682052149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6404919173717821121368099 9607378760576731682052149)
          ·
            refine ⟨900691758804068595192389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9607378760576731682052149 900691758804068595192389)
            ·
              refine ⟨168879704775762861598573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 900691758804068595192389 168879704775762861598573)
              ·
                refine ⟨63329889290911073099465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 168879704775762861598573 63329889290911073099465)
                ·
                  rfl

theorem cell19_208127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 4, 3].length) (baseStart_208127 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_208127 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_208127 prefixEnd_208127 := by exact prefixLift 208127
  have htrace : WordTrace (prefixWord ++ tailWord_208127) baseStart_208127 baseEnd_208127 := by
    simpa [prefixWord, tailWord_208127, baseEnd_208127] using wordTrace_append hprefix tailTrace_208127
  have hstable : (prefixWord ++ tailWord_208127).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208127).length < 2 ^ (prefixWord ++ tailWord_208127).sum := by decide
  have hdescent : baseEnd_208127 < baseStart_208127 := by decide
  rcases family_descends (prefixWord ++ tailWord_208127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208165 : List Nat := [1, 3, 1, 2, 4, 2, 2, 4]
def baseStart_208165 : Nat := 118140960795 + 208165 * 2 ^ 59
def prefixEnd_208165 : Nat := 4983230072969 + 3 ^ 40 * 208165 * 2
def baseEnd_208165 : Nat := 63341452114538244254917

theorem tailTrace_208165 : CollatzResearch.WordTrace tailWord_208165 prefixEnd_208165 63341452114538244254917 := by
  unfold tailWord_208165
  simp only [CollatzResearch.WordTrace]
  refine ⟨7592401290861231596689949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5061600860574154397793299 7592401290861231596689949)
  ·
    refine ⟨2847150484072961848758731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7592401290861231596689949 2847150484072961848758731)
    ·
      refine ⟨4270725726109442773138097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2847150484072961848758731 4270725726109442773138097)
      ·
        refine ⟨3203044294582082079853573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4270725726109442773138097 3203044294582082079853573)
        ·
          refine ⟨600570805234140389972545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3203044294582082079853573 600570805234140389972545)
          ·
            refine ⟨450428103925605292479409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 600570805234140389972545 450428103925605292479409)
            ·
              refine ⟨337821077944203969359557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 450428103925605292479409 337821077944203969359557)
              ·
                refine ⟨63341452114538244254917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 337821077944203969359557 63341452114538244254917)
                ·
                  rfl

theorem cell19_208165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2, 4].length) (baseStart_208165 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_208165 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_208165 prefixEnd_208165 := by exact prefixLift 208165
  have htrace : WordTrace (prefixWord ++ tailWord_208165) baseStart_208165 baseEnd_208165 := by
    simpa [prefixWord, tailWord_208165, baseEnd_208165] using wordTrace_append hprefix tailTrace_208165
  have hstable : (prefixWord ++ tailWord_208165).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208165).length < 2 ^ (prefixWord ++ tailWord_208165).sum := by decide
  have hdescent : baseEnd_208165 < baseStart_208165 := by decide
  rcases family_descends (prefixWord ++ tailWord_208165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208186 : List Nat := [3, 1, 1, 1, 4, 1, 1, 7]
def baseStart_208186 : Nat := 118140960795 + 208186 * 2 ^ 59
def prefixEnd_208186 : Nat := 4983230072969 + 3 ^ 40 * 208186 * 2
def baseEnd_208186 : Nat := 63347842096016417788193

theorem tailTrace_208186 : CollatzResearch.WordTrace tailWord_208186 prefixEnd_208186 63347842096016417788193 := by
  unfold tailWord_208186
  simp only [CollatzResearch.WordTrace]
  refine ⟨1898291805946288045801103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5062111482523434788802941 1898291805946288045801103)
  ·
    refine ⟨2847437708919432068701655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1898291805946288045801103 2847437708919432068701655)
    ·
      refine ⟨4271156563379148103052483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2847437708919432068701655 4271156563379148103052483)
      ·
        refine ⟨6406734845068722154578725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4271156563379148103052483 6406734845068722154578725)
        ·
          refine ⟨1201262783450385403983511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6406734845068722154578725 1201262783450385403983511)
          ·
            refine ⟨1801894175175578105975267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1201262783450385403983511 1801894175175578105975267)
            ·
              refine ⟨2702841262763367158962901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1801894175175578105975267 2702841262763367158962901)
              ·
                refine ⟨63347842096016417788193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2702841262763367158962901 63347842096016417788193)
                ·
                  rfl

theorem cell19_208186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 7].length) (baseStart_208186 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_208186 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_208186 prefixEnd_208186 := by exact prefixLift 208186
  have htrace : WordTrace (prefixWord ++ tailWord_208186) baseStart_208186 baseEnd_208186 := by
    simpa [prefixWord, tailWord_208186, baseEnd_208186] using wordTrace_append hprefix tailTrace_208186
  have hstable : (prefixWord ++ tailWord_208186).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208186).length < 2 ^ (prefixWord ++ tailWord_208186).sum := by decide
  have hdescent : baseEnd_208186 < baseStart_208186 := by decide
  rcases family_descends (prefixWord ++ tailWord_208186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208214 : List Nat := [5, 2, 3, 1, 1, 2, 1, 4]
def baseStart_208214 : Nat := 118140960795 + 208214 * 2 ^ 59
def prefixEnd_208214 : Nat := 4983230072969 + 3 ^ 40 * 208214 * 2
def baseEnd_208214 : Nat := 63356362071320649165895

theorem tailTrace_208214 : CollatzResearch.WordTrace tailWord_208214 prefixEnd_208214 63356362071320649165895 := by
  unfold tailWord_208214
  simp only [CollatzResearch.WordTrace]
  refine ⟨474636779230232060326481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5062792311789141976815797 474636779230232060326481)
  ·
    refine ⟨355977584422674045244861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 474636779230232060326481 355977584422674045244861)
    ·
      refine ⟨133491594158502766966823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 355977584422674045244861 133491594158502766966823)
      ·
        refine ⟨200237391237754150450235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133491594158502766966823 200237391237754150450235)
        ·
          refine ⟨300356086856631225675353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200237391237754150450235 300356086856631225675353)
          ·
            refine ⟨225267065142473419256515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 300356086856631225675353 225267065142473419256515)
            ·
              refine ⟨337900597713710128884773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 225267065142473419256515 337900597713710128884773)
              ·
                refine ⟨63356362071320649165895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 337900597713710128884773 63356362071320649165895)
                ·
                  rfl

theorem cell19_208214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 1, 4].length) (baseStart_208214 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_208214 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_208214 prefixEnd_208214 := by exact prefixLift 208214
  have htrace : WordTrace (prefixWord ++ tailWord_208214) baseStart_208214 baseEnd_208214 := by
    simpa [prefixWord, tailWord_208214, baseEnd_208214] using wordTrace_append hprefix tailTrace_208214
  have hstable : (prefixWord ++ tailWord_208214).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208214).length < 2 ^ (prefixWord ++ tailWord_208214).sum := by decide
  have hdescent : baseEnd_208214 < baseStart_208214 := by decide
  rcases family_descends (prefixWord ++ tailWord_208214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208258 : List Nat := [3, 4, 2, 1, 1, 2, 6]
def baseStart_208258 : Nat := 118140960795 + 208258 * 2 ^ 59
def prefixEnd_208258 : Nat := 4983230072969 + 3 ^ 40 * 208258 * 2
def baseEnd_208258 : Nat := 21123250201313861395999

theorem tailTrace_208258 : CollatzResearch.WordTrace tailWord_208258 prefixEnd_208258 21123250201313861395999 := by
  unfold tailWord_208258
  simp only [CollatzResearch.WordTrace]
  refine ⟨1898948319881077119956357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5063862186349538986550285 1898948319881077119956357)
  ·
    refine ⟨356052809977701959991817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1898948319881077119956357 356052809977701959991817)
    ·
      refine ⟨267039607483276469993863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 356052809977701959991817 267039607483276469993863)
      ·
        refine ⟨400559411224914704990795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267039607483276469993863 400559411224914704990795)
        ·
          refine ⟨600839116837372057486193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 400559411224914704990795 600839116837372057486193)
          ·
            refine ⟨450629337628029043114645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 600839116837372057486193 450629337628029043114645)
            ·
              refine ⟨21123250201313861395999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 450629337628029043114645 21123250201313861395999)
              ·
                rfl

theorem cell19_208258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 6].length) (baseStart_208258 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_208258 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_208258 prefixEnd_208258 := by exact prefixLift 208258
  have htrace : WordTrace (prefixWord ++ tailWord_208258) baseStart_208258 baseEnd_208258 := by
    simpa [prefixWord, tailWord_208258, baseEnd_208258] using wordTrace_append hprefix tailTrace_208258
  have hstable : (prefixWord ++ tailWord_208258).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208258).length < 2 ^ (prefixWord ++ tailWord_208258).sum := by decide
  have hdescent : baseEnd_208258 < baseStart_208258 := by decide
  rcases family_descends (prefixWord ++ tailWord_208258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208296 : List Nat := [2, 1, 6, 1, 2, 1, 1, 5]
def baseStart_208296 : Nat := 118140960795 + 208296 * 2 ^ 59
def prefixEnd_208296 : Nat := 4983230072969 + 3 ^ 40 * 208296 * 2
def baseEnd_208296 : Nat := 63381313427568755343449

theorem tailTrace_208296 : CollatzResearch.WordTrace tailWord_208296 prefixEnd_208296 63381313427568755343449 := by
  unfold tailWord_208296
  simp only [CollatzResearch.WordTrace]
  refine ⟨3798589626693320484854371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5064786168924427313139161 3798589626693320484854371)
  ·
    refine ⟨5697884440039980727281557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3798589626693320484854371 5697884440039980727281557)
    ·
      refine ⟨267088333126874096591323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 5697884440039980727281557 267088333126874096591323)
      ·
        refine ⟨400632499690311144886985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267088333126874096591323 400632499690311144886985)
        ·
          refine ⟨300474374767733358665239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 400632499690311144886985 300474374767733358665239)
          ·
            refine ⟨450711562151600037997859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 300474374767733358665239 450711562151600037997859)
            ·
              refine ⟨676067343227400056996789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 450711562151600037997859 676067343227400056996789)
              ·
                refine ⟨63381313427568755343449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 676067343227400056996789 63381313427568755343449)
                ·
                  rfl

theorem cell19_208296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 5].length) (baseStart_208296 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_208296 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_208296 prefixEnd_208296 := by exact prefixLift 208296
  have htrace : WordTrace (prefixWord ++ tailWord_208296) baseStart_208296 baseEnd_208296 := by
    simpa [prefixWord, tailWord_208296, baseEnd_208296] using wordTrace_append hprefix tailTrace_208296
  have hstable : (prefixWord ++ tailWord_208296).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208296).length < 2 ^ (prefixWord ++ tailWord_208296).sum := by decide
  have hdescent : baseEnd_208296 < baseStart_208296 := by decide
  rcases family_descends (prefixWord ++ tailWord_208296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208412 : List Nat := [2, 2, 3, 1, 2, 1, 5, 3]
def baseStart_208412 : Nat := 118140960795 + 208412 * 2 ^ 59
def prefixEnd_208412 : Nat := 4983230072969 + 3 ^ 40 * 208412 * 2
def baseEnd_208412 : Nat := 63416610468114856765355

theorem tailTrace_208412 : CollatzResearch.WordTrace tailWord_208412 prefixEnd_208412 63416610468114856765355 := by
  unfold tailWord_208412
  simp only [CollatzResearch.WordTrace]
  refine ⟨3800705060483196390465745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5067606747310928520620993 3800705060483196390465745)
  ·
    refine ⟨2850528795362397292849309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3800705060483196390465745 2850528795362397292849309)
    ·
      refine ⟨1068948298260898984818491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2850528795362397292849309 1068948298260898984818491)
      ·
        refine ⟨1603422447391348477227737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1068948298260898984818491 1603422447391348477227737)
        ·
          refine ⟨1202566835543511357920803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1603422447391348477227737 1202566835543511357920803)
          ·
            refine ⟨1803850253315267036881205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1202566835543511357920803 1803850253315267036881205)
            ·
              refine ⟨169110961248306284707613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1803850253315267036881205 169110961248306284707613)
              ·
                refine ⟨63416610468114856765355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 169110961248306284707613 63416610468114856765355)
                ·
                  rfl

theorem cell19_208412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 5, 3].length) (baseStart_208412 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_208412 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_208412 prefixEnd_208412 := by exact prefixLift 208412
  have htrace : WordTrace (prefixWord ++ tailWord_208412) baseStart_208412 baseEnd_208412 := by
    simpa [prefixWord, tailWord_208412, baseEnd_208412] using wordTrace_append hprefix tailTrace_208412
  have hstable : (prefixWord ++ tailWord_208412).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208412).length < 2 ^ (prefixWord ++ tailWord_208412).sum := by decide
  have hdescent : baseEnd_208412 < baseStart_208412 := by decide
  rcases family_descends (prefixWord ++ tailWord_208412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208471 : List Nat := [1, 1, 3, 2, 2, 4, 1, 5]
def baseStart_208471 : Nat := 118140960795 + 208471 * 2 ^ 59
def prefixEnd_208471 : Nat := 4983230072969 + 3 ^ 40 * 208471 * 2
def baseEnd_208471 : Nat := 63434563273220201454083

theorem tailTrace_208471 : CollatzResearch.WordTrace tailWord_208471 prefixEnd_208471 63434563273220201454083 := by
  unfold tailWord_208471
  simp only [CollatzResearch.WordTrace]
  refine ⟨7603562027752645857329267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5069041351835097238219511 7603562027752645857329267)
  ·
    refine ⟨11405343041628968785993901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7603562027752645857329267 11405343041628968785993901)
    ·
      refine ⟨4277003640610863294747713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11405343041628968785993901 4277003640610863294747713)
      ·
        refine ⟨3207752730458147471060785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4277003640610863294747713 3207752730458147471060785)
        ·
          refine ⟨2405814547843610603295589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3207752730458147471060785 2405814547843610603295589)
          ·
            refine ⟨451090227720676988117923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2405814547843610603295589 451090227720676988117923)
            ·
              refine ⟨676635341581015482176885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 451090227720676988117923 676635341581015482176885)
              ·
                refine ⟨63434563273220201454083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 676635341581015482176885 63434563273220201454083)
                ·
                  rfl

theorem cell19_208471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 5].length) (baseStart_208471 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_208471 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_208471 prefixEnd_208471 := by exact prefixLift 208471
  have htrace : WordTrace (prefixWord ++ tailWord_208471) baseStart_208471 baseEnd_208471 := by
    simpa [prefixWord, tailWord_208471, baseEnd_208471] using wordTrace_append hprefix tailTrace_208471
  have hstable : (prefixWord ++ tailWord_208471).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208471).length < 2 ^ (prefixWord ++ tailWord_208471).sum := by decide
  have hdescent : baseEnd_208471 < baseStart_208471 := by decide
  rcases family_descends (prefixWord ++ tailWord_208471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208488 : List Nat := [2, 1, 4, 3, 1, 3, 5]
def baseStart_208488 : Nat := 118140960795 + 208488 * 2 ^ 59
def prefixEnd_208488 : Nat := 4983230072969 + 3 ^ 40 * 208488 * 2
def baseEnd_208488 : Nat := 21146578705123066358753

theorem tailTrace_208488 : CollatzResearch.WordTrace tailWord_208488 prefixEnd_208488 21146578705123066358753 := by
  unfold tailWord_208488
  simp only [CollatzResearch.WordTrace]
  refine ⟨3802091034345528880349059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5069454712460705173798745 3802091034345528880349059)
  ·
    refine ⟨5703136551518293320523589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3802091034345528880349059 5703136551518293320523589)
    ·
      refine ⟨1069338103409679997598173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5703136551518293320523589 1069338103409679997598173)
      ·
        refine ⟨401001788778629999099315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1069338103409679997598173 401001788778629999099315)
        ·
          refine ⟨601502683167944998648973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 401001788778629999099315 601502683167944998648973)
          ·
            refine ⟨225563506187979374493365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 601502683167944998648973 225563506187979374493365)
            ·
              refine ⟨21146578705123066358753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 225563506187979374493365 21146578705123066358753)
              ·
                rfl

theorem cell19_208488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 5].length) (baseStart_208488 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_208488 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_208488 prefixEnd_208488 := by exact prefixLift 208488
  have htrace : WordTrace (prefixWord ++ tailWord_208488) baseStart_208488 baseEnd_208488 := by
    simpa [prefixWord, tailWord_208488, baseEnd_208488] using wordTrace_append hprefix tailTrace_208488
  have hstable : (prefixWord ++ tailWord_208488).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208488).length < 2 ^ (prefixWord ++ tailWord_208488).sum := by decide
  have hdescent : baseEnd_208488 < baseStart_208488 := by decide
  rcases family_descends (prefixWord ++ tailWord_208488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208490 : List Nat := [3, 1, 3, 2, 1, 2, 7]
def baseStart_208490 : Nat := 118140960795 + 208490 * 2 ^ 59
def prefixEnd_208490 : Nat := 4983230072969 + 3 ^ 40 * 208490 * 2
def baseEnd_208490 : Nat := 21146781561677929010603

theorem tailTrace_208490 : CollatzResearch.WordTrace tailWord_208490 prefixEnd_208490 21146781561677929010603 := by
  unfold tailWord_208490
  simp only [CollatzResearch.WordTrace]
  refine ⟨1901063753670953025567731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5069503343122541401513949 1901063753670953025567731)
  ·
    refine ⟨2851595630506429538351597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1901063753670953025567731 2851595630506429538351597)
    ·
      refine ⟨1069348361439911076881849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2851595630506429538351597 1069348361439911076881849)
      ·
        refine ⟨802011271079933307661387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1069348361439911076881849 802011271079933307661387)
        ·
          refine ⟨1203016906619899961492081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 802011271079933307661387 1203016906619899961492081)
          ·
            refine ⟨902262679964924971119061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1203016906619899961492081 902262679964924971119061)
            ·
              refine ⟨21146781561677929010603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 902262679964924971119061 21146781561677929010603)
              ·
                rfl

theorem cell19_208490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 7].length) (baseStart_208490 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_208490 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_208490 prefixEnd_208490 := by exact prefixLift 208490
  have htrace : WordTrace (prefixWord ++ tailWord_208490) baseStart_208490 baseEnd_208490 := by
    simpa [prefixWord, tailWord_208490, baseEnd_208490] using wordTrace_append hprefix tailTrace_208490
  have hstable : (prefixWord ++ tailWord_208490).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208490).length < 2 ^ (prefixWord ++ tailWord_208490).sum := by decide
  have hdescent : baseEnd_208490 < baseStart_208490 := by decide
  rcases family_descends (prefixWord ++ tailWord_208490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208509 : List Nat := [1, 4, 1, 1, 4, 1, 1, 6]
def baseStart_208509 : Nat := 118140960795 + 208509 * 2 ^ 59
def prefixEnd_208509 : Nat := 4983230072969 + 3 ^ 40 * 208509 * 2
def baseEnd_208509 : Nat := 63446126096847372609535

theorem tailTrace_208509 : CollatzResearch.WordTrace tailWord_208509 prefixEnd_208509 63446126096847372609535 := by
  unfold tailWord_208509
  simp only [CollatzResearch.WordTrace]
  refine ⟨7604948001614978347212581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5069965334409985564808387 7604948001614978347212581)
  ·
    refine ⟨1425927750302808440102359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7604948001614978347212581 1425927750302808440102359)
    ·
      refine ⟨2138891625454212660153539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1425927750302808440102359 2138891625454212660153539)
      ·
        refine ⟨3208337438181318990230309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2138891625454212660153539 3208337438181318990230309)
        ·
          refine ⟨601563269658997310668183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3208337438181318990230309 601563269658997310668183)
          ·
            refine ⟨902344904488495966002275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 601563269658997310668183 902344904488495966002275)
            ·
              refine ⟨1353517356732743949003413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 902344904488495966002275 1353517356732743949003413)
              ·
                refine ⟨63446126096847372609535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1353517356732743949003413 63446126096847372609535)
                ·
                  rfl

theorem cell19_208509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 6].length) (baseStart_208509 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_208509 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_208509 prefixEnd_208509 := by exact prefixLift 208509
  have htrace : WordTrace (prefixWord ++ tailWord_208509) baseStart_208509 baseEnd_208509 := by
    simpa [prefixWord, tailWord_208509, baseEnd_208509] using wordTrace_append hprefix tailTrace_208509
  have hstable : (prefixWord ++ tailWord_208509).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208509).length < 2 ^ (prefixWord ++ tailWord_208509).sum := by decide
  have hdescent : baseEnd_208509 < baseStart_208509 := by decide
  rcases family_descends (prefixWord ++ tailWord_208509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208587 : List Nat := [1, 1, 1, 1, 3, 2, 1, 9]
def baseStart_208587 : Nat := 118140960795 + 208587 * 2 ^ 59
def prefixEnd_208587 : Nat := 4983230072969 + 3 ^ 40 * 208587 * 2
def baseEnd_208587 : Nat := 63469860313766302875989

theorem tailTrace_208587 : CollatzResearch.WordTrace tailWord_208587 prefixEnd_208587 63469860313766302875989 := by
  unfold tailWord_208587
  simp only [CollatzResearch.WordTrace]
  refine ⟨7607792895332397668552015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5071861930221598445701343 7607792895332397668552015)
  ·
    refine ⟨11411689342998596502828023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7607792895332397668552015 11411689342998596502828023)
    ·
      refine ⟨17117534014497894754242035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11411689342998596502828023 17117534014497894754242035)
      ·
        refine ⟨25676301021746842131363053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17117534014497894754242035 25676301021746842131363053)
        ·
          refine ⟨9628612883155065799261145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25676301021746842131363053 9628612883155065799261145)
          ·
            refine ⟨7221459662366299349445859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9628612883155065799261145 7221459662366299349445859)
            ·
              refine ⟨10832189493549449024168789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7221459662366299349445859 10832189493549449024168789)
              ·
                refine ⟨63469860313766302875989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10832189493549449024168789 63469860313766302875989)
                ·
                  rfl

theorem cell19_208587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 9].length) (baseStart_208587 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_208587 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_208587 prefixEnd_208587 := by exact prefixLift 208587
  have htrace : WordTrace (prefixWord ++ tailWord_208587) baseStart_208587 baseEnd_208587 := by
    simpa [prefixWord, tailWord_208587, baseEnd_208587] using wordTrace_append hprefix tailTrace_208587
  have hstable : (prefixWord ++ tailWord_208587).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208587).length < 2 ^ (prefixWord ++ tailWord_208587).sum := by decide
  have hdescent : baseEnd_208587 < baseStart_208587 := by decide
  rcases family_descends (prefixWord ++ tailWord_208587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208653 : List Nat := [1, 7, 2, 1, 1, 2, 5]
def baseStart_208653 : Nat := 118140960795 + 208653 * 2 ^ 59
def prefixEnd_208653 : Nat := 4983230072969 + 3 ^ 40 * 208653 * 2
def baseEnd_208653 : Nat := 21163314370899235136381

theorem tailTrace_208653 : CollatzResearch.WordTrace tailWord_208653 prefixEnd_208653 21163314370899235136381 := by
  unfold tailWord_208653
  simp only [CollatzResearch.WordTrace]
  refine ⟨7610200113093290940454613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5073466742062193960303075 7610200113093290940454613)
  ·
    refine ⟨178364065150624006416905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 7610200113093290940454613 178364065150624006416905)
    ·
      refine ⟨133773048862968004812679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178364065150624006416905 133773048862968004812679)
      ·
        refine ⟨200659573294452007219019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133773048862968004812679 200659573294452007219019)
        ·
          refine ⟨300989359941678010828529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200659573294452007219019 300989359941678010828529)
          ·
            refine ⟨225742019956258508121397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 300989359941678010828529 225742019956258508121397)
            ·
              refine ⟨21163314370899235136381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 225742019956258508121397 21163314370899235136381)
              ·
                rfl

theorem cell19_208653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 5].length) (baseStart_208653 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_208653 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_208653 prefixEnd_208653 := by exact prefixLift 208653
  have htrace : WordTrace (prefixWord ++ tailWord_208653) baseStart_208653 baseEnd_208653 := by
    simpa [prefixWord, tailWord_208653, baseEnd_208653] using wordTrace_append hprefix tailTrace_208653
  have hstable : (prefixWord ++ tailWord_208653).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208653).length < 2 ^ (prefixWord ++ tailWord_208653).sum := by decide
  have hdescent : baseEnd_208653 < baseStart_208653 := by decide
  rcases family_descends (prefixWord ++ tailWord_208653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208661 : List Nat := [1, 3, 2, 1, 2, 5, 5]
def baseStart_208661 : Nat := 118140960795 + 208661 * 2 ^ 59
def prefixEnd_208661 : Nat := 4983230072969 + 3 ^ 40 * 208661 * 2
def baseEnd_208661 : Nat := 21164125797118685743781

theorem tailTrace_208661 : CollatzResearch.WordTrace tailWord_208661 prefixEnd_208661 21164125797118685743781 := by
  unfold tailWord_208661
  simp only [CollatzResearch.WordTrace]
  refine ⟨7610491897064308306745837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5073661264709538871163891 7610491897064308306745837)
  ·
    refine ⟨2853934461399115615029689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7610491897064308306745837 2853934461399115615029689)
    ·
      refine ⟨2140450846049336711272267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2853934461399115615029689 2140450846049336711272267)
      ·
        refine ⟨3210676269074005066908401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2140450846049336711272267 3210676269074005066908401)
        ·
          refine ⟨2408007201805503800181301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3210676269074005066908401 2408007201805503800181301)
          ·
            refine ⟨225750675169265981266997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2408007201805503800181301 225750675169265981266997)
            ·
              refine ⟨21164125797118685743781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 225750675169265981266997 21164125797118685743781)
              ·
                rfl

theorem cell19_208661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 5].length) (baseStart_208661 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_208661 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_208661 prefixEnd_208661 := by exact prefixLift 208661
  have htrace : WordTrace (prefixWord ++ tailWord_208661) baseStart_208661 baseEnd_208661 := by
    simpa [prefixWord, tailWord_208661, baseEnd_208661] using wordTrace_append hprefix tailTrace_208661
  have hstable : (prefixWord ++ tailWord_208661).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208661).length < 2 ^ (prefixWord ++ tailWord_208661).sum := by decide
  have hdescent : baseEnd_208661 < baseStart_208661 := by decide
  rcases family_descends (prefixWord ++ tailWord_208661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208680 : List Nat := [2, 1, 5, 1, 1, 2, 1, 6]
def baseStart_208680 : Nat := 118140960795 + 208680 * 2 ^ 59
def prefixEnd_208680 : Nat := 4983230072969 + 3 ^ 40 * 208680 * 2
def baseEnd_208680 : Nat := 63498158803169642809069

theorem tailTrace_208680 : CollatzResearch.WordTrace tailWord_208680 prefixEnd_208680 63498158803169642809069 := by
  unfold tailWord_208680
  simp only [CollatzResearch.WordTrace]
  refine ⟨3805592441997737275843747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5074123255996983034458329 3805592441997737275843747)
  ·
    refine ⟨5708388662996605913765621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3805592441997737275843747 5708388662996605913765621)
    ·
      refine ⟨535161437155931804415527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5708388662996605913765621 535161437155931804415527)
      ·
        refine ⟨802742155733897706623291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 535161437155931804415527 802742155733897706623291)
        ·
          refine ⟨1204113233600846559934937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 802742155733897706623291 1204113233600846559934937)
          ·
            refine ⟨903084925200634919951203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1204113233600846559934937 903084925200634919951203)
            ·
              refine ⟨1354627387800952379926805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 903084925200634919951203 1354627387800952379926805)
              ·
                refine ⟨63498158803169642809069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1354627387800952379926805 63498158803169642809069)
                ·
                  rfl

theorem cell19_208680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 6].length) (baseStart_208680 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_208680 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_208680 prefixEnd_208680 := by exact prefixLift 208680
  have htrace : WordTrace (prefixWord ++ tailWord_208680) baseStart_208680 baseEnd_208680 := by
    simpa [prefixWord, tailWord_208680, baseEnd_208680] using wordTrace_append hprefix tailTrace_208680
  have hstable : (prefixWord ++ tailWord_208680).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208680).length < 2 ^ (prefixWord ++ tailWord_208680).sum := by decide
  have hdescent : baseEnd_208680 < baseStart_208680 := by decide
  rcases family_descends (prefixWord ++ tailWord_208680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208775 : List Nat := [1, 1, 4, 2, 4, 1, 6]
def baseStart_208775 : Nat := 118140960795 + 208775 * 2 ^ 59
def prefixEnd_208775 : Nat := 4983230072969 + 3 ^ 40 * 208775 * 2
def baseEnd_208775 : Nat := 21175688620745856899233

theorem tailTrace_208775 : CollatzResearch.WordTrace tailWord_208775 prefixEnd_208775 21175688620745856899233 := by
  unfold tailWord_208775
  simp only [CollatzResearch.WordTrace]
  refine ⟨7614649818651305776395779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5076433212434203850930519 7614649818651305776395779)
  ·
    refine ⟨11421974727976958664593669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7614649818651305776395779 11421974727976958664593669)
    ·
      refine ⟨2141620261495679749611313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11421974727976958664593669 2141620261495679749611313)
      ·
        refine ⟨1606215196121759812208485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2141620261495679749611313 1606215196121759812208485)
        ·
          refine ⟨301165349272829964789091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1606215196121759812208485 301165349272829964789091)
          ·
            refine ⟨451748023909244947183637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 301165349272829964789091 451748023909244947183637)
            ·
              refine ⟨21175688620745856899233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 451748023909244947183637 21175688620745856899233)
              ·
                rfl

theorem cell19_208775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 6].length) (baseStart_208775 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_208775 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_208775 prefixEnd_208775 := by exact prefixLift 208775
  have htrace : WordTrace (prefixWord ++ tailWord_208775) baseStart_208775 baseEnd_208775 := by
    simpa [prefixWord, tailWord_208775, baseEnd_208775] using wordTrace_append hprefix tailTrace_208775
  have hstable : (prefixWord ++ tailWord_208775).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208775).length < 2 ^ (prefixWord ++ tailWord_208775).sum := by decide
  have hdescent : baseEnd_208775 < baseStart_208775 := by decide
  rcases family_descends (prefixWord ++ tailWord_208775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208777 : List Nat := [1, 2, 1, 1, 5, 1, 8]
def baseStart_208777 : Nat := 118140960795 + 208777 * 2 ^ 59
def prefixEnd_208777 : Nat := 4983230072969 + 3 ^ 40 * 208777 * 2
def baseEnd_208777 : Nat := 21175891477300719551083

theorem tailTrace_208777 : CollatzResearch.WordTrace tailWord_208777 prefixEnd_208777 21175891477300719551083 := by
  unfold tailWord_208777
  simp only [CollatzResearch.WordTrace]
  refine ⟨7614722764644060117968585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5076481843096040078645723 7614722764644060117968585)
  ·
    refine ⟨5711042073483045088476439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7614722764644060117968585 5711042073483045088476439)
    ·
      refine ⟨8566563110224567632714659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5711042073483045088476439 8566563110224567632714659)
      ·
        refine ⟨12849844665336851449071989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8566563110224567632714659 12849844665336851449071989)
        ·
          refine ⟨1204672937375329823350499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12849844665336851449071989 1204672937375329823350499)
          ·
            refine ⟨1807009406062994735025749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1204672937375329823350499 1807009406062994735025749)
            ·
              refine ⟨21175891477300719551083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1807009406062994735025749 21175891477300719551083)
              ·
                rfl

theorem cell19_208777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 8].length) (baseStart_208777 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_208777 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_208777 prefixEnd_208777 := by exact prefixLift 208777
  have htrace : WordTrace (prefixWord ++ tailWord_208777) baseStart_208777 baseEnd_208777 := by
    simpa [prefixWord, tailWord_208777, baseEnd_208777] using wordTrace_append hprefix tailTrace_208777
  have hstable : (prefixWord ++ tailWord_208777).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208777).length < 2 ^ (prefixWord ++ tailWord_208777).sum := by decide
  have hdescent : baseEnd_208777 < baseStart_208777 := by decide
  rcases family_descends (prefixWord ++ tailWord_208777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208815 : List Nat := [1, 1, 2, 1, 2, 2, 5, 5]
def baseStart_208815 : Nat := 118140960795 + 208815 * 2 ^ 59
def prefixEnd_208815 : Nat := 4983230072969 + 3 ^ 40 * 208815 * 2
def baseEnd_208815 : Nat := 63539237255529329808701

theorem tailTrace_208815 : CollatzResearch.WordTrace tailWord_208815 prefixEnd_208815 63539237255529329808701 := by
  unfold tailWord_208815
  simp only [CollatzResearch.WordTrace]
  refine ⟨7616108738506392607851899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5077405825670928405234599 7616108738506392607851899)
  ·
    refine ⟨11424163107759588911777849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7616108738506392607851899 11424163107759588911777849)
    ·
      refine ⟨8568122330819691683833387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11424163107759588911777849 8568122330819691683833387)
      ·
        refine ⟨12852183496229537525750081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8568122330819691683833387 12852183496229537525750081)
        ·
          refine ⟨9639137622172153144312561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12852183496229537525750081 9639137622172153144312561)
          ·
            refine ⟨7229353216629114858234421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9639137622172153144312561 7229353216629114858234421)
            ·
              refine ⟨677751864058979517959477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7229353216629114858234421 677751864058979517959477)
              ·
                refine ⟨63539237255529329808701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 677751864058979517959477 63539237255529329808701)
                ·
                  rfl

theorem cell19_208815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 5].length) (baseStart_208815 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_208815 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_208815 prefixEnd_208815 := by exact prefixLift 208815
  have htrace : WordTrace (prefixWord ++ tailWord_208815) baseStart_208815 baseEnd_208815 := by
    simpa [prefixWord, tailWord_208815, baseEnd_208815] using wordTrace_append hprefix tailTrace_208815
  have hstable : (prefixWord ++ tailWord_208815).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208815).length < 2 ^ (prefixWord ++ tailWord_208815).sum := by decide
  have hdescent : baseEnd_208815 < baseStart_208815 := by decide
  rcases family_descends (prefixWord ++ tailWord_208815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208828 : List Nat := [2, 2, 2, 5, 2, 1, 5]
def baseStart_208828 : Nat := 118140960795 + 208828 * 2 ^ 59
def prefixEnd_208828 : Nat := 4983230072969 + 3 ^ 40 * 208828 * 2
def baseEnd_208828 : Nat := 21181064319449717173259

theorem tailTrace_208828 : CollatzResearch.WordTrace tailWord_208828 prefixEnd_208828 21181064319449717173259 := by
  unfold tailWord_208828
  simp only [CollatzResearch.WordTrace]
  refine ⟨3808291443729647914037569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5077721924972863885383425 3808291443729647914037569)
  ·
    refine ⟨2856218582797235935528177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3808291443729647914037569 2856218582797235935528177)
    ·
      refine ⟨2142163937097926951646133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2856218582797235935528177 2142163937097926951646133)
      ·
        refine ⟨200827869102930651716825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2142163937097926951646133 200827869102930651716825)
        ·
          refine ⟨150620901827197988787619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200827869102930651716825 150620901827197988787619)
          ·
            refine ⟨225931352740796983181429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150620901827197988787619 225931352740796983181429)
            ·
              refine ⟨21181064319449717173259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 225931352740796983181429 21181064319449717173259)
              ·
                rfl

theorem cell19_208828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 5].length) (baseStart_208828 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_208828 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_208828 prefixEnd_208828 := by exact prefixLift 208828
  have htrace : WordTrace (prefixWord ++ tailWord_208828) baseStart_208828 baseEnd_208828 := by
    simpa [prefixWord, tailWord_208828, baseEnd_208828] using wordTrace_append hprefix tailTrace_208828
  have hstable : (prefixWord ++ tailWord_208828).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208828).length < 2 ^ (prefixWord ++ tailWord_208828).sum := by decide
  have hdescent : baseEnd_208828 < baseStart_208828 := by decide
  rcases family_descends (prefixWord ++ tailWord_208828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208906 : List Nat := [3, 1, 2, 2, 4, 2, 1, 4]
def baseStart_208906 : Nat := 118140960795 + 208906 * 2 ^ 59
def prefixEnd_208906 : Nat := 4983230072969 + 3 ^ 40 * 208906 * 2
def baseEnd_208906 : Nat := 63566927175268081786231

theorem tailTrace_208906 : CollatzResearch.WordTrace tailWord_208906 prefixEnd_208906 63566927175268081786231 := by
  unfold tailWord_208906
  simp only [CollatzResearch.WordTrace]
  refine ⟨1904856945294178787353643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5079618520784476766276381 1904856945294178787353643)
  ·
    refine ⟨2857285417941268181030465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1904856945294178787353643 2857285417941268181030465)
    ·
      refine ⟨2142964063455951135772849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2857285417941268181030465 2142964063455951135772849)
      ·
        refine ⟨1607223047591963351829637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2142964063455951135772849 1607223047591963351829637)
        ·
          refine ⟨301354321423493128468057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1607223047591963351829637 301354321423493128468057)
          ·
            refine ⟨226015741067619846351043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 301354321423493128468057 226015741067619846351043)
            ·
              refine ⟨339023611601429769526565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 226015741067619846351043 339023611601429769526565)
              ·
                refine ⟨63566927175268081786231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 339023611601429769526565 63566927175268081786231)
                ·
                  rfl

theorem cell19_208906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 1, 4].length) (baseStart_208906 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_208906 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_208906 prefixEnd_208906 := by exact prefixLift 208906
  have htrace : WordTrace (prefixWord ++ tailWord_208906) baseStart_208906 baseEnd_208906 := by
    simpa [prefixWord, tailWord_208906, baseEnd_208906] using wordTrace_append hprefix tailTrace_208906
  have hstable : (prefixWord ++ tailWord_208906).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208906).length < 2 ^ (prefixWord ++ tailWord_208906).sum := by decide
  have hdescent : baseEnd_208906 < baseStart_208906 := by decide
  rcases family_descends (prefixWord ++ tailWord_208906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208925 : List Nat := [1, 4, 2, 2, 2, 2, 3, 3]
def baseStart_208925 : Nat := 118140960795 + 208925 * 2 ^ 59
def prefixEnd_208925 : Nat := 4983230072969 + 3 ^ 40 * 208925 * 2
def baseEnd_208925 : Nat := 63572708587081667363957

theorem tailTrace_208925 : CollatzResearch.WordTrace tailWord_208925 prefixEnd_208925 63572708587081667363957 := by
  unfold tailWord_208925
  simp only [CollatzResearch.WordTrace]
  refine ⟨7620120768107881394356229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5080080512071920929570819 7620120768107881394356229)
  ·
    refine ⟨1428772644020227761441793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7620120768107881394356229 1428772644020227761441793)
    ·
      refine ⟨1071579483015170821081345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1428772644020227761441793 1071579483015170821081345)
      ·
        refine ⟨803684612261378115811009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1071579483015170821081345 803684612261378115811009)
        ·
          refine ⟨602763459196033586858257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 803684612261378115811009 602763459196033586858257)
          ·
            refine ⟨452072594397025190143693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 602763459196033586858257 452072594397025190143693)
            ·
              refine ⟨169527222898884446303885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 452072594397025190143693 169527222898884446303885)
              ·
                refine ⟨63572708587081667363957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 169527222898884446303885 63572708587081667363957)
                ·
                  rfl

theorem cell19_208925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 3, 3].length) (baseStart_208925 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_208925 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_208925 prefixEnd_208925 := by exact prefixLift 208925
  have htrace : WordTrace (prefixWord ++ tailWord_208925) baseStart_208925 baseEnd_208925 := by
    simpa [prefixWord, tailWord_208925, baseEnd_208925] using wordTrace_append hprefix tailTrace_208925
  have hstable : (prefixWord ++ tailWord_208925).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208925).length < 2 ^ (prefixWord ++ tailWord_208925).sum := by decide
  have hdescent : baseEnd_208925 < baseStart_208925 := by decide
  rcases family_descends (prefixWord ++ tailWord_208925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208927 : List Nat := [1, 1, 2, 4, 1, 2, 5, 3]
def baseStart_208927 : Nat := 118140960795 + 208927 * 2 ^ 59
def prefixEnd_208927 : Nat := 4983230072969 + 3 ^ 40 * 208927 * 2
def baseEnd_208927 : Nat := 63573317156746255319507

theorem tailTrace_208927 : CollatzResearch.WordTrace tailWord_208927 prefixEnd_208927 63573317156746255319507 := by
  unfold tailWord_208927
  simp only [CollatzResearch.WordTrace]
  refine ⟨7620193714100635735929035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5080129142733757157286023 7620193714100635735929035)
  ·
    refine ⟨11430290571150953603893553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7620193714100635735929035 11430290571150953603893553)
    ·
      refine ⟨8572717928363215202920165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11430290571150953603893553 8572717928363215202920165)
      ·
        refine ⟨1607384611568102850547531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8572717928363215202920165 1607384611568102850547531)
        ·
          refine ⟨2411076917352154275821297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1607384611568102850547531 2411076917352154275821297)
          ·
            refine ⟨1808307688014115706865973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2411076917352154275821297 1808307688014115706865973)
            ·
              refine ⟨169528845751323347518685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1808307688014115706865973 169528845751323347518685)
              ·
                refine ⟨63573317156746255319507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 169528845751323347518685 63573317156746255319507)
                ·
                  rfl

theorem cell19_208927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 5, 3].length) (baseStart_208927 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_208927 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_208927 prefixEnd_208927 := by exact prefixLift 208927
  have htrace : WordTrace (prefixWord ++ tailWord_208927) baseStart_208927 baseEnd_208927 := by
    simpa [prefixWord, tailWord_208927, baseEnd_208927] using wordTrace_append hprefix tailTrace_208927
  have hstable : (prefixWord ++ tailWord_208927).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208927).length < 2 ^ (prefixWord ++ tailWord_208927).sum := by decide
  have hdescent : baseEnd_208927 < baseStart_208927 := by decide
  rcases family_descends (prefixWord ++ tailWord_208927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208967 : List Nat := [1, 1, 4, 1, 3, 1, 2, 6]
def baseStart_208967 : Nat := 118140960795 + 208967 * 2 ^ 59
def prefixEnd_208967 : Nat := 4983230072969 + 3 ^ 40 * 208967 * 2
def baseEnd_208967 : Nat := 63585488550038014430509

theorem tailTrace_208967 : CollatzResearch.WordTrace tailWord_208967 prefixEnd_208967 63585488550038014430509 := by
  unfold tailWord_208967
  simp only [CollatzResearch.WordTrace]
  refine ⟨7621652633955722567385155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5081101755970481711590103 7621652633955722567385155)
  ·
    refine ⟨11432478950933583851077733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7621652633955722567385155 11432478950933583851077733)
    ·
      refine ⟨2143589803300046972077075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11432478950933583851077733 2143589803300046972077075)
      ·
        refine ⟨3215384704950070458115613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2143589803300046972077075 3215384704950070458115613)
        ·
          refine ⟨1205769264356276421793355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3215384704950070458115613 1205769264356276421793355)
          ·
            refine ⟨1808653896534414632690033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1205769264356276421793355 1808653896534414632690033)
            ·
              refine ⟨1356490422400810974517525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1808653896534414632690033 1356490422400810974517525)
              ·
                refine ⟨63585488550038014430509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1356490422400810974517525 63585488550038014430509)
                ·
                  rfl

theorem cell19_208967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 6].length) (baseStart_208967 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_208967 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_208967 prefixEnd_208967 := by exact prefixLift 208967
  have htrace : WordTrace (prefixWord ++ tailWord_208967) baseStart_208967 baseEnd_208967 := by
    simpa [prefixWord, tailWord_208967, baseEnd_208967] using wordTrace_append hprefix tailTrace_208967
  have hstable : (prefixWord ++ tailWord_208967).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208967).length < 2 ^ (prefixWord ++ tailWord_208967).sum := by decide
  have hdescent : baseEnd_208967 < baseStart_208967 := by decide
  rcases family_descends (prefixWord ++ tailWord_208967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208984 : List Nat := [2, 1, 2, 2, 1, 4, 4, 3]
def baseStart_208984 : Nat := 118140960795 + 208984 * 2 ^ 59
def prefixEnd_208984 : Nat := 4983230072969 + 3 ^ 40 * 208984 * 2
def baseEnd_208984 : Nat := 63590661392187012052685

theorem tailTrace_208984 : CollatzResearch.WordTrace tailWord_208984 prefixEnd_208984 63590661392187012052685 := by
  unfold tailWord_208984
  simp only [CollatzResearch.WordTrace]
  refine ⟨3811136337447067235377003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5081515116596089647169337 3811136337447067235377003)
  ·
    refine ⟨5716704506170600853065505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3811136337447067235377003 5716704506170600853065505)
    ·
      refine ⟨4287528379627950639799129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5716704506170600853065505 4287528379627950639799129)
      ·
        refine ⟨3215646284720962979849347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4287528379627950639799129 3215646284720962979849347)
        ·
          refine ⟨4823469427081444469774021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3215646284720962979849347 4823469427081444469774021)
          ·
            refine ⟨904400517577770838082629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4823469427081444469774021 904400517577770838082629)
            ·
              refine ⟨169575097045832032140493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 904400517577770838082629 169575097045832032140493)
              ·
                refine ⟨63590661392187012052685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 169575097045832032140493 63590661392187012052685)
                ·
                  rfl

theorem cell19_208984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 4, 3].length) (baseStart_208984 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_208984 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_208984 prefixEnd_208984 := by exact prefixLift 208984
  have htrace : WordTrace (prefixWord ++ tailWord_208984) baseStart_208984 baseEnd_208984 := by
    simpa [prefixWord, tailWord_208984, baseEnd_208984] using wordTrace_append hprefix tailTrace_208984
  have hstable : (prefixWord ++ tailWord_208984).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208984).length < 2 ^ (prefixWord ++ tailWord_208984).sum := by decide
  have hdescent : baseEnd_208984 < baseStart_208984 := by decide
  rcases family_descends (prefixWord ++ tailWord_208984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208986 : List Nat := [3, 1, 1, 2, 1, 1, 5, 5]
def baseStart_208986 : Nat := 118140960795 + 208986 * 2 ^ 59
def prefixEnd_208986 : Nat := 4983230072969 + 3 ^ 40 * 208986 * 2
def baseEnd_208986 : Nat := 63591269961851600008235

theorem tailTrace_208986 : CollatzResearch.WordTrace tailWord_208986 prefixEnd_208986 63591269961851600008235 := by
  unfold tailWord_208986
  simp only [CollatzResearch.WordTrace]
  refine ⟨1905586405221722203081703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5081563747257925874884541 1905586405221722203081703)
  ·
    refine ⟨2858379607832583304622555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1905586405221722203081703 2858379607832583304622555)
    ·
      refine ⟨4287569411748874956933833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2858379607832583304622555 4287569411748874956933833)
      ·
        refine ⟨3215677058811656217700375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4287569411748874956933833 3215677058811656217700375)
        ·
          refine ⟨4823515588217484326550563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3215677058811656217700375 4823515588217484326550563)
          ·
            refine ⟨7235273382326226489825845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4823515588217484326550563 7235273382326226489825845)
            ·
              refine ⟨678306879593083733421173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7235273382326226489825845 678306879593083733421173)
              ·
                refine ⟨63591269961851600008235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 678306879593083733421173 63591269961851600008235)
                ·
                  rfl

theorem cell19_208986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 5].length) (baseStart_208986 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_208986 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_208986 prefixEnd_208986 := by exact prefixLift 208986
  have htrace : WordTrace (prefixWord ++ tailWord_208986) baseStart_208986 baseEnd_208986 := by
    simpa [prefixWord, tailWord_208986, baseEnd_208986] using wordTrace_append hprefix tailTrace_208986
  have hstable : (prefixWord ++ tailWord_208986).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208986).length < 2 ^ (prefixWord ++ tailWord_208986).sum := by decide
  have hdescent : baseEnd_208986 < baseStart_208986 := by decide
  rcases family_descends (prefixWord ++ tailWord_208986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209060 : List Nat := [2, 3, 1, 2, 5, 6]
def baseStart_209060 : Nat := 118140960795 + 209060 * 2 ^ 59
def prefixEnd_209060 : Nat := 4983230072969 + 3 ^ 40 * 209060 * 2
def baseEnd_209060 : Nat := 7068198559937928262621

theorem tailTrace_209060 : CollatzResearch.WordTrace tailWord_209060 prefixEnd_209060 7068198559937928262621 := by
  unfold tailWord_209060
  simp only [CollatzResearch.WordTrace]
  refine ⟨3812522311309399725260317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5083363081745866300347089 3812522311309399725260317)
  ·
    refine ⟨1429695866741024896972619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3812522311309399725260317 1429695866741024896972619)
    ·
      refine ⟨2144543800111537345458929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1429695866741024896972619 2144543800111537345458929)
      ·
        refine ⟨1608407850083653009094197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2144543800111537345458929 1608407850083653009094197)
        ·
          refine ⟨150788235945342469602581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1608407850083653009094197 150788235945342469602581)
          ·
            refine ⟨7068198559937928262621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 150788235945342469602581 7068198559937928262621)
            ·
              rfl

theorem cell19_209060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 6].length) (baseStart_209060 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_209060 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_209060 prefixEnd_209060 := by exact prefixLift 209060
  have htrace : WordTrace (prefixWord ++ tailWord_209060) baseStart_209060 baseEnd_209060 := by
    simpa [prefixWord, tailWord_209060, baseEnd_209060] using wordTrace_append hprefix tailTrace_209060
  have hstable : (prefixWord ++ tailWord_209060).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209060).length < 2 ^ (prefixWord ++ tailWord_209060).sum := by decide
  have hdescent : baseEnd_209060 < baseStart_209060 := by decide
  rcases family_descends (prefixWord ++ tailWord_209060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209079 : List Nat := [1, 1, 3, 1, 4, 4, 1, 4]
def baseStart_209079 : Nat := 118140960795 + 209079 * 2 ^ 59
def prefixEnd_209079 : Nat := 4983230072969 + 3 ^ 40 * 209079 * 2
def baseEnd_209079 : Nat := 63619568451254939941315

theorem tailTrace_209079 : CollatzResearch.WordTrace tailWord_209079 prefixEnd_209079 63619568451254939941315 := by
  unfold tailWord_209079
  simp only [CollatzResearch.WordTrace]
  refine ⟨7625737609549965695462291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5083825073033310463641527 7625737609549965695462291)
  ·
    refine ⟨11438606414324948543193437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7625737609549965695462291 11438606414324948543193437)
    ·
      refine ⟨4289477405371855703697539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11438606414324948543193437 4289477405371855703697539)
      ·
        refine ⟨6434216108057783555546309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4289477405371855703697539 6434216108057783555546309)
        ·
          refine ⟨1206415520260834416664933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6434216108057783555546309 1206415520260834416664933)
          ·
            refine ⟨226202910048906453124675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1206415520260834416664933 226202910048906453124675)
            ·
              refine ⟨339304365073359679687013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 226202910048906453124675 339304365073359679687013)
              ·
                refine ⟨63619568451254939941315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 339304365073359679687013 63619568451254939941315)
                ·
                  rfl

theorem cell19_209079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 1, 4].length) (baseStart_209079 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_209079 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_209079 prefixEnd_209079 := by exact prefixLift 209079
  have htrace : WordTrace (prefixWord ++ tailWord_209079) baseStart_209079 baseEnd_209079 := by
    simpa [prefixWord, tailWord_209079, baseEnd_209079] using wordTrace_append hprefix tailTrace_209079
  have hstable : (prefixWord ++ tailWord_209079).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209079).length < 2 ^ (prefixWord ++ tailWord_209079).sum := by decide
  have hdescent : baseEnd_209079 < baseStart_209079 := by decide
  rcases family_descends (prefixWord ++ tailWord_209079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209098 : List Nat := [3, 1, 2, 1, 3, 1, 5, 3]
def baseStart_209098 : Nat := 118140960795 + 209098 * 2 ^ 59
def prefixEnd_209098 : Nat := 4983230072969 + 3 ^ 40 * 209098 * 2
def baseEnd_209098 : Nat := 63625349863068525519041

theorem tailTrace_209098 : CollatzResearch.WordTrace tailWord_209098 prefixEnd_209098 63625349863068525519041 := by
  unfold tailWord_209098
  simp only [CollatzResearch.WordTrace]
  refine ⟨1906607649120282985100987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5084287064320754626935965 1906607649120282985100987)
  ·
    refine ⟨2859911473680424477651481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1906607649120282985100987 2859911473680424477651481)
    ·
      refine ⟨2144933605260318358238611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2859911473680424477651481 2144933605260318358238611)
      ·
        refine ⟨3217400407890477537357917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2144933605260318358238611 3217400407890477537357917)
        ·
          refine ⟨1206525152958929076509219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3217400407890477537357917 1206525152958929076509219)
          ·
            refine ⟨1809787729438393614763829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1206525152958929076509219 1809787729438393614763829)
            ·
              refine ⟨169667599634849401384109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1809787729438393614763829 169667599634849401384109)
              ·
                refine ⟨63625349863068525519041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 169667599634849401384109 63625349863068525519041)
                ·
                  rfl

theorem cell19_209098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 5, 3].length) (baseStart_209098 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_209098 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_209098 prefixEnd_209098 := by exact prefixLift 209098
  have htrace : WordTrace (prefixWord ++ tailWord_209098) baseStart_209098 baseEnd_209098 := by
    simpa [prefixWord, tailWord_209098, baseEnd_209098] using wordTrace_append hprefix tailTrace_209098
  have hstable : (prefixWord ++ tailWord_209098).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209098).length < 2 ^ (prefixWord ++ tailWord_209098).sum := by decide
  have hdescent : baseEnd_209098 < baseStart_209098 := by decide
  rcases family_descends (prefixWord ++ tailWord_209098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209117 : List Nat := [1, 4, 3, 2, 1, 2, 6]
def baseStart_209117 : Nat := 118140960795 + 209117 * 2 ^ 59
def prefixEnd_209117 : Nat := 4983230072969 + 3 ^ 40 * 209117 * 2
def baseEnd_209117 : Nat := 21210377091627370365589

theorem tailTrace_209117 : CollatzResearch.WordTrace tailWord_209117 prefixEnd_209117 21210377091627370365589 := by
  unfold tailWord_209117
  simp only [CollatzResearch.WordTrace]
  refine ⟨7627123583412298185345605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5084749055608198790230403 7627123583412298185345605)
  ·
    refine ⟨1430085671889805909752301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7627123583412298185345605 1430085671889805909752301)
    ·
      refine ⟨536282126958677216157113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1430085671889805909752301 536282126958677216157113)
      ·
        refine ⟨402211595219007912117835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 536282126958677216157113 402211595219007912117835)
        ·
          refine ⟨603317392828511868176753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 402211595219007912117835 603317392828511868176753)
          ·
            refine ⟨452488044621383901132565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 603317392828511868176753 452488044621383901132565)
            ·
              refine ⟨21210377091627370365589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 452488044621383901132565 21210377091627370365589)
              ·
                rfl

theorem cell19_209117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 6].length) (baseStart_209117 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_209117 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_209117 prefixEnd_209117 := by exact prefixLift 209117
  have htrace : WordTrace (prefixWord ++ tailWord_209117) baseStart_209117 baseEnd_209117 := by
    simpa [prefixWord, tailWord_209117, baseEnd_209117] using wordTrace_append hprefix tailTrace_209117
  have hstable : (prefixWord ++ tailWord_209117).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209117).length < 2 ^ (prefixWord ++ tailWord_209117).sum := by decide
  have hdescent : baseEnd_209117 < baseStart_209117 := by decide
  rcases family_descends (prefixWord ++ tailWord_209117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209248 : List Nat := [2, 1, 1, 3, 6, 1, 1, 4]
def baseStart_209248 : Nat := 118140960795 + 209248 * 2 ^ 59
def prefixEnd_209248 : Nat := 4983230072969 + 3 ^ 40 * 209248 * 2
def baseEnd_209248 : Nat := 63670992587912622185299

theorem tailTrace_209248 : CollatzResearch.WordTrace tailWord_209248 prefixEnd_209248 63670992587912622185299 := by
  unfold tailWord_209248
  simp only [CollatzResearch.WordTrace]
  refine ⟨3815950772968853779182199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5087934363958471705576265 3815950772968853779182199)
  ·
    refine ⟨5723926159453280668773299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3815950772968853779182199 5723926159453280668773299)
    ·
      refine ⟨8585889239179921003159949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5723926159453280668773299 8585889239179921003159949)
      ·
        refine ⟨3219708464692470376184981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8585889239179921003159949 3219708464692470376184981)
        ·
          refine ⟨150923834282459548883671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 3219708464692470376184981 150923834282459548883671)
          ·
            refine ⟨226385751423689323325507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150923834282459548883671 226385751423689323325507)
            ·
              refine ⟨339578627135533984988261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 226385751423689323325507 339578627135533984988261)
              ·
                refine ⟨63670992587912622185299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 339578627135533984988261 63670992587912622185299)
                ·
                  rfl

theorem cell19_209248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 4].length) (baseStart_209248 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_209248 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_209248 prefixEnd_209248 := by exact prefixLift 209248
  have htrace : WordTrace (prefixWord ++ tailWord_209248) baseStart_209248 baseEnd_209248 := by
    simpa [prefixWord, tailWord_209248, baseEnd_209248] using wordTrace_append hprefix tailTrace_209248
  have hstable : (prefixWord ++ tailWord_209248).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209248).length < 2 ^ (prefixWord ++ tailWord_209248).sum := by decide
  have hdescent : baseEnd_209248 < baseStart_209248 := by decide
  rcases family_descends (prefixWord ++ tailWord_209248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209250 : List Nat := [3, 3, 2, 1, 1, 2, 3, 4]
def baseStart_209250 : Nat := 118140960795 + 209250 * 2 ^ 59
def prefixEnd_209250 : Nat := 4983230072969 + 3 ^ 40 * 209250 * 2
def baseEnd_209250 : Nat := 63671601157577210140849

theorem tailTrace_209250 : CollatzResearch.WordTrace tailWord_209250 prefixEnd_209250 63671601157577210140849 := by
  unfold tailWord_209250
  simp only [CollatzResearch.WordTrace]
  refine ⟨1907993622982615474984301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5087982994620307933291469 1907993622982615474984301)
  ·
    refine ⟨715497608618480803119113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1907993622982615474984301 715497608618480803119113)
    ·
      refine ⟨536623206463860602339335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 715497608618480803119113 536623206463860602339335)
      ·
        refine ⟨804934809695790903509003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 536623206463860602339335 804934809695790903509003)
        ·
          refine ⟨1207402214543686355263505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 804934809695790903509003 1207402214543686355263505)
          ·
            refine ⟨905551660907764766447629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1207402214543686355263505 905551660907764766447629)
            ·
              refine ⟨339581872840411787417861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 905551660907764766447629 339581872840411787417861)
              ·
                refine ⟨63671601157577210140849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 339581872840411787417861 63671601157577210140849)
                ·
                  rfl

theorem cell19_209250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3, 4].length) (baseStart_209250 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_209250 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_209250 prefixEnd_209250 := by exact prefixLift 209250
  have htrace : WordTrace (prefixWord ++ tailWord_209250) baseStart_209250 baseEnd_209250 := by
    simpa [prefixWord, tailWord_209250, baseEnd_209250] using wordTrace_append hprefix tailTrace_209250
  have hstable : (prefixWord ++ tailWord_209250).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209250).length < 2 ^ (prefixWord ++ tailWord_209250).sum := by decide
  have hdescent : baseEnd_209250 < baseStart_209250 := by decide
  rcases family_descends (prefixWord ++ tailWord_209250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209322 : List Nat := [3, 1, 6, 1, 1, 1, 1, 5]
def baseStart_209322 : Nat := 118140960795 + 209322 * 2 ^ 59
def prefixEnd_209322 : Nat := 4983230072969 + 3 ^ 40 * 209322 * 2
def baseEnd_209322 : Nat := 63693509665502376540653

theorem tailTrace_209322 : CollatzResearch.WordTrace tailWord_209322 prefixEnd_209322 63693509665502376540653 := by
  unfold tailWord_209322
  simp only [CollatzResearch.WordTrace]
  refine ⟨1908650136917404549139555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5089733698446412131038813 1908650136917404549139555)
  ·
    refine ⟨2862975205376106823709333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1908650136917404549139555 2862975205376106823709333)
    ·
      refine ⟨134201962752005007361375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 2862975205376106823709333 134201962752005007361375)
      ·
        refine ⟨201302944128007511042063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134201962752005007361375 201302944128007511042063)
        ·
          refine ⟨301954416192011266563095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201302944128007511042063 301954416192011266563095)
          ·
            refine ⟨452931624288016899844643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 301954416192011266563095 452931624288016899844643)
            ·
              refine ⟨679397436432025349766965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 452931624288016899844643 679397436432025349766965)
              ·
                refine ⟨63693509665502376540653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 679397436432025349766965 63693509665502376540653)
                ·
                  rfl

theorem cell19_209322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 5].length) (baseStart_209322 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_209322 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_209322 prefixEnd_209322 := by exact prefixLift 209322
  have htrace : WordTrace (prefixWord ++ tailWord_209322) baseStart_209322 baseEnd_209322 := by
    simpa [prefixWord, tailWord_209322, baseEnd_209322] using wordTrace_append hprefix tailTrace_209322
  have hstable : (prefixWord ++ tailWord_209322).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209322).length < 2 ^ (prefixWord ++ tailWord_209322).sum := by decide
  have hdescent : baseEnd_209322 < baseStart_209322 := by decide
  rcases family_descends (prefixWord ++ tailWord_209322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209362 : List Nat := [3, 2, 2, 4, 1, 1, 2, 4]
def baseStart_209362 : Nat := 118140960795 + 209362 * 2 ^ 59
def prefixEnd_209362 : Nat := 4983230072969 + 3 ^ 40 * 209362 * 2
def baseEnd_209362 : Nat := 63705681058794135651655

theorem tailTrace_209362 : CollatzResearch.WordTrace tailWord_209362 prefixEnd_209362 63705681058794135651655 := by
  unfold tailWord_209362
  simp only [CollatzResearch.WordTrace]
  refine ⟨1909014866881176257003585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5090706311683136685342893 1909014866881176257003585)
  ·
    refine ⟨1431761150160882192752689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1909014866881176257003585 1431761150160882192752689)
    ·
      refine ⟨1073820862620661644564517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1431761150160882192752689 1073820862620661644564517)
      ·
        refine ⟨201341411741374058355847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1073820862620661644564517 201341411741374058355847)
        ·
          refine ⟨302012117612061087533771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201341411741374058355847 302012117612061087533771)
          ·
            refine ⟨453018176418091631300657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 302012117612061087533771 453018176418091631300657)
            ·
              refine ⟨339763632313568723475493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 453018176418091631300657 339763632313568723475493)
              ·
                refine ⟨63705681058794135651655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 339763632313568723475493 63705681058794135651655)
                ·
                  rfl

theorem cell19_209362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 2, 4].length) (baseStart_209362 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_209362 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_209362 prefixEnd_209362 := by exact prefixLift 209362
  have htrace : WordTrace (prefixWord ++ tailWord_209362) baseStart_209362 baseEnd_209362 := by
    simpa [prefixWord, tailWord_209362, baseEnd_209362] using wordTrace_append hprefix tailTrace_209362
  have hstable : (prefixWord ++ tailWord_209362).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209362).length < 2 ^ (prefixWord ++ tailWord_209362).sum := by decide
  have hdescent : baseEnd_209362 < baseStart_209362 := by decide
  rcases family_descends (prefixWord ++ tailWord_209362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209364 : List Nat := [2, 4, 1, 2, 2, 2, 2, 4]
def baseStart_209364 : Nat := 118140960795 + 209364 * 2 ^ 59
def prefixEnd_209364 : Nat := 4983230072969 + 3 ^ 40 * 209364 * 2
def baseEnd_209364 : Nat := 63706289628458723607205

theorem tailTrace_209364 : CollatzResearch.WordTrace tailWord_209364 prefixEnd_209364 63706289628458723607205 := by
  unfold tailWord_209364
  simp only [CollatzResearch.WordTrace]
  refine ⟨3818066206758729684793573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5090754942344972913058097 3818066206758729684793573)
  ·
    refine ⟨715887413767261815898795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3818066206758729684793573 715887413767261815898795)
    ·
      refine ⟨1073831120650892723848193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 715887413767261815898795 1073831120650892723848193)
      ·
        refine ⟨805373340488169542886145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1073831120650892723848193 805373340488169542886145)
        ·
          refine ⟨604030005366127157164609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 805373340488169542886145 604030005366127157164609)
          ·
            refine ⟨453022504024595367873457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 604030005366127157164609 453022504024595367873457)
            ·
              refine ⟨339766878018446525905093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 453022504024595367873457 339766878018446525905093)
              ·
                refine ⟨63706289628458723607205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 339766878018446525905093 63706289628458723607205)
                ·
                  rfl

theorem cell19_209364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2, 4].length) (baseStart_209364 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_209364 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_209364 prefixEnd_209364 := by exact prefixLift 209364
  have htrace : WordTrace (prefixWord ++ tailWord_209364) baseStart_209364 baseEnd_209364 := by
    simpa [prefixWord, tailWord_209364, baseEnd_209364] using wordTrace_append hprefix tailTrace_209364
  have hstable : (prefixWord ++ tailWord_209364).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209364).length < 2 ^ (prefixWord ++ tailWord_209364).sum := by decide
  have hdescent : baseEnd_209364 < baseStart_209364 := by decide
  rcases family_descends (prefixWord ++ tailWord_209364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209387 : List Nat := [1, 1, 1, 1, 2, 3, 3, 7]
def baseStart_209387 : Nat := 118140960795 + 209387 * 2 ^ 59
def prefixEnd_209387 : Nat := 4983230072969 + 3 ^ 40 * 209387 * 2
def baseEnd_209387 : Nat := 63713288179601485096031

theorem tailTrace_209387 : CollatzResearch.WordTrace tailWord_209387 prefixEnd_209387 63713288179601485096031 := by
  unfold tailWord_209387
  simp only [CollatzResearch.WordTrace]
  refine ⟨7636971292434134297674415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5091314194956089531782943 7636971292434134297674415)
  ·
    refine ⟨11455456938651201446511623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7636971292434134297674415 11455456938651201446511623)
    ·
      refine ⟨17183185407976802169767435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11455456938651201446511623 17183185407976802169767435)
      ·
        refine ⟨25774778111965203254651153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17183185407976802169767435 25774778111965203254651153)
        ·
          refine ⟨19331083583973902440988365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25774778111965203254651153 19331083583973902440988365)
          ·
            refine ⟨7249156343990213415370637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19331083583973902440988365 7249156343990213415370637)
            ·
              refine ⟨2718433628996330030763989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7249156343990213415370637 2718433628996330030763989)
              ·
                refine ⟨63713288179601485096031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2718433628996330030763989 63713288179601485096031)
                ·
                  rfl

theorem cell19_209387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 7].length) (baseStart_209387 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_209387 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_209387 prefixEnd_209387 := by exact prefixLift 209387
  have htrace : WordTrace (prefixWord ++ tailWord_209387) baseStart_209387 baseEnd_209387 := by
    simpa [prefixWord, tailWord_209387, baseEnd_209387] using wordTrace_append hprefix tailTrace_209387
  have hstable : (prefixWord ++ tailWord_209387).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209387).length < 2 ^ (prefixWord ++ tailWord_209387).sum := by decide
  have hdescent : baseEnd_209387 < baseStart_209387 := by decide
  rcases family_descends (prefixWord ++ tailWord_209387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209425 : List Nat := [1, 2, 2, 1, 1, 2, 2, 8]
def baseStart_209425 : Nat := 118140960795 + 209425 * 2 ^ 59
def prefixEnd_209425 : Nat := 4983230072969 + 3 ^ 40 * 209425 * 2
def baseEnd_209425 : Nat := 63724851003228656251483

theorem tailTrace_209425 : CollatzResearch.WordTrace tailWord_209425 prefixEnd_209425 63724851003228656251483 := by
  unfold tailWord_209425
  simp only [CollatzResearch.WordTrace]
  refine ⟨7638357266296466787557729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5092238177530977858371819 7638357266296466787557729)
  ·
    refine ⟨5728767949722350090668297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7638357266296466787557729 5728767949722350090668297)
    ·
      refine ⟨4296575962291762568001223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5728767949722350090668297 4296575962291762568001223)
      ·
        refine ⟨6444863943437643852001835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4296575962291762568001223 6444863943437643852001835)
        ·
          refine ⟨9667295915156465778002753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6444863943437643852001835 9667295915156465778002753)
          ·
            refine ⟨7250471936367349333502065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9667295915156465778002753 7250471936367349333502065)
            ·
              refine ⟨5437853952275512000126549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7250471936367349333502065 5437853952275512000126549)
              ·
                refine ⟨63724851003228656251483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5437853952275512000126549 63724851003228656251483)
                ·
                  rfl

theorem cell19_209425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 8].length) (baseStart_209425 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_209425 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_209425 prefixEnd_209425 := by exact prefixLift 209425
  have htrace : WordTrace (prefixWord ++ tailWord_209425) baseStart_209425 baseEnd_209425 := by
    simpa [prefixWord, tailWord_209425, baseEnd_209425] using wordTrace_append hprefix tailTrace_209425
  have hstable : (prefixWord ++ tailWord_209425).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209425).length < 2 ^ (prefixWord ++ tailWord_209425).sum := by decide
  have hdescent : baseEnd_209425 < baseStart_209425 := by decide
  rcases family_descends (prefixWord ++ tailWord_209425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209463 : List Nat := [1, 1, 3, 1, 2, 3, 8]
def baseStart_209463 : Nat := 118140960795 + 209463 * 2 ^ 59
def prefixEnd_209463 : Nat := 4983230072969 + 3 ^ 40 * 209463 * 2
def baseEnd_209463 : Nat := 21245471275618609135645

theorem tailTrace_209463 : CollatzResearch.WordTrace tailWord_209463 prefixEnd_209463 21245471275618609135645 := by
  unfold tailWord_209463
  simp only [CollatzResearch.WordTrace]
  refine ⟨7639743240158799277441043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5093162160105866184960695 7639743240158799277441043)
  ·
    refine ⟨11459614860238198916161565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7639743240158799277441043 11459614860238198916161565)
    ·
      refine ⟨4297355572589324593560587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11459614860238198916161565 4297355572589324593560587)
      ·
        refine ⟨6446033358883986890340881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4297355572589324593560587 6446033358883986890340881)
        ·
          refine ⟨4834525019162990167755661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6446033358883986890340881 4834525019162990167755661)
          ·
            refine ⟨1812946882186121312908373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4834525019162990167755661 1812946882186121312908373)
            ·
              refine ⟨21245471275618609135645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1812946882186121312908373 21245471275618609135645)
              ·
                rfl

theorem cell19_209463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 8].length) (baseStart_209463 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_209463 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_209463 prefixEnd_209463 := by exact prefixLift 209463
  have htrace : WordTrace (prefixWord ++ tailWord_209463) baseStart_209463 baseEnd_209463 := by
    simpa [prefixWord, tailWord_209463, baseEnd_209463] using wordTrace_append hprefix tailTrace_209463
  have hstable : (prefixWord ++ tailWord_209463).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209463).length < 2 ^ (prefixWord ++ tailWord_209463).sum := by decide
  have hdescent : baseEnd_209463 < baseStart_209463 := by decide
  rcases family_descends (prefixWord ++ tailWord_209463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209518 : List Nat := [4, 1, 2, 2, 2, 1, 7]
def baseStart_209518 : Nat := 118140960795 + 209518 * 2 ^ 59
def prefixEnd_209518 : Nat := 4983230072969 + 3 ^ 40 * 209518 * 2
def baseEnd_209518 : Nat := 21251049830877332061521

theorem tailTrace_209518 : CollatzResearch.WordTrace tailWord_209518 prefixEnd_209518 21251049830877332061521 := by
  unfold tailWord_209518
  simp only [CollatzResearch.WordTrace]
  refine ⟨955218656869942958836651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5094499503306362447128805 955218656869942958836651)
  ·
    refine ⟨1432827985304914438254977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 955218656869942958836651 1432827985304914438254977)
    ·
      refine ⟨1074620988978685828691233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1432827985304914438254977 1074620988978685828691233)
      ·
        refine ⟨805965741734014371518425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1074620988978685828691233 805965741734014371518425)
        ·
          refine ⟨604474306300510778638819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 805965741734014371518425 604474306300510778638819)
          ·
            refine ⟨906711459450766167958229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 604474306300510778638819 906711459450766167958229)
            ·
              refine ⟨21251049830877332061521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 906711459450766167958229 21251049830877332061521)
              ·
                rfl

theorem cell19_209518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 7].length) (baseStart_209518 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_209518 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_209518 prefixEnd_209518 := by exact prefixLift 209518
  have htrace : WordTrace (prefixWord ++ tailWord_209518) baseStart_209518 baseEnd_209518 := by
    simpa [prefixWord, tailWord_209518, baseEnd_209518] using wordTrace_append hprefix tailTrace_209518
  have hstable : (prefixWord ++ tailWord_209518).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209518).length < 2 ^ (prefixWord ++ tailWord_209518).sum := by decide
  have hdescent : baseEnd_209518 < baseStart_209518 := by decide
  rcases family_descends (prefixWord ++ tailWord_209518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209537 : List Nat := [1, 2, 4, 2, 1, 1, 4, 4]
def baseStart_209537 : Nat := 118140960795 + 209537 * 2 ^ 59
def prefixEnd_209537 : Nat := 4983230072969 + 3 ^ 40 * 209537 * 2
def baseEnd_209537 : Nat := 63758930904445581762289

theorem tailTrace_209537 : CollatzResearch.WordTrace tailWord_209537 prefixEnd_209537 63758930904445581762289 := by
  unfold tailWord_209537
  simp only [CollatzResearch.WordTrace]
  refine ⟨7642442241890709915634865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5094961494593806610423243 7642442241890709915634865)
  ·
    refine ⟨5731831681418032436726149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7642442241890709915634865 5731831681418032436726149)
    ·
      refine ⟨1074718440265881081886153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5731831681418032436726149 1074718440265881081886153)
      ·
        refine ⟨806038830199410811414615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1074718440265881081886153 806038830199410811414615)
        ·
          refine ⟨1209058245299116217121923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 806038830199410811414615 1209058245299116217121923)
          ·
            refine ⟨1813587367948674325682885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1209058245299116217121923 1813587367948674325682885)
            ·
              refine ⟨340047631490376436065541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1813587367948674325682885 340047631490376436065541)
              ·
                refine ⟨63758930904445581762289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 340047631490376436065541 63758930904445581762289)
                ·
                  rfl

theorem cell19_209537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4, 4].length) (baseStart_209537 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_209537 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_209537 prefixEnd_209537 := by exact prefixLift 209537
  have htrace : WordTrace (prefixWord ++ tailWord_209537) baseStart_209537 baseEnd_209537 := by
    simpa [prefixWord, tailWord_209537, baseEnd_209537] using wordTrace_append hprefix tailTrace_209537
  have hstable : (prefixWord ++ tailWord_209537).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209537).length < 2 ^ (prefixWord ++ tailWord_209537).sum := by decide
  have hdescent : baseEnd_209537 < baseStart_209537 := by decide
  rcases family_descends (prefixWord ++ tailWord_209537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209539 : List Nat := [1, 1, 1, 3, 3, 1, 3, 6]
def baseStart_209539 : Nat := 118140960795 + 209539 * 2 ^ 59
def prefixEnd_209539 : Nat := 4983230072969 + 3 ^ 40 * 209539 * 2
def baseEnd_209539 : Nat := 63759539474110169717839

theorem tailTrace_209539 : CollatzResearch.WordTrace tailWord_209539 prefixEnd_209539 63759539474110169717839 := by
  unfold tailWord_209539
  simp only [CollatzResearch.WordTrace]
  refine ⟨7642515187883464257207671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5095010125255642838138447 7642515187883464257207671)
  ·
    refine ⟨11463772781825196385811507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7642515187883464257207671 11463772781825196385811507)
    ·
      refine ⟨17195659172737794578717261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11463772781825196385811507 17195659172737794578717261)
      ·
        refine ⟨6448372189776672967018973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17195659172737794578717261 6448372189776672967018973)
        ·
          refine ⟨2418139571166252362632115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6448372189776672967018973 2418139571166252362632115)
          ·
            refine ⟨3627209356749378543948173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2418139571166252362632115 3627209356749378543948173)
            ·
              refine ⟨1360203508781016953980565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3627209356749378543948173 1360203508781016953980565)
              ·
                refine ⟨63759539474110169717839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1360203508781016953980565 63759539474110169717839)
                ·
                  rfl

theorem cell19_209539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 6].length) (baseStart_209539 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_209539 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_209539 prefixEnd_209539 := by exact prefixLift 209539
  have htrace : WordTrace (prefixWord ++ tailWord_209539) baseStart_209539 baseEnd_209539 := by
    simpa [prefixWord, tailWord_209539, baseEnd_209539] using wordTrace_append hprefix tailTrace_209539
  have hstable : (prefixWord ++ tailWord_209539).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209539).length < 2 ^ (prefixWord ++ tailWord_209539).sum := by decide
  have hdescent : baseEnd_209539 < baseStart_209539 := by decide
  rcases family_descends (prefixWord ++ tailWord_209539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209575 : List Nat := [1, 1, 6, 3, 8]
def baseStart_209575 : Nat := 118140960795 + 209575 * 2 ^ 59
def prefixEnd_209575 : Nat := 4983230072969 + 3 ^ 40 * 209575 * 2
def baseEnd_209575 : Nat := 2361870138076768626583

theorem tailTrace_209575 : CollatzResearch.WordTrace tailWord_209575 prefixEnd_209575 2361870138076768626583 := by
  unfold tailWord_209575
  simp only [CollatzResearch.WordTrace]
  refine ⟨7643828215753042405518179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5095885477168694937012119 7643828215753042405518179)
  ·
    refine ⟨11465742323629563608277269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7643828215753042405518179 11465742323629563608277269)
    ·
      refine ⟨537456671420135794137997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 11465742323629563608277269 537456671420135794137997)
      ·
        refine ⟨201546251782550922801749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 537456671420135794137997 201546251782550922801749)
        ·
          refine ⟨2361870138076768626583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 201546251782550922801749 2361870138076768626583)
          ·
            rfl

theorem cell19_209575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 8].length) (baseStart_209575 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_209575 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_209575 prefixEnd_209575 := by exact prefixLift 209575
  have htrace : WordTrace (prefixWord ++ tailWord_209575) baseStart_209575 baseEnd_209575 := by
    simpa [prefixWord, tailWord_209575, baseEnd_209575] using wordTrace_append hprefix tailTrace_209575
  have hstable : (prefixWord ++ tailWord_209575).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209575).length < 2 ^ (prefixWord ++ tailWord_209575).sum := by decide
  have hdescent : baseEnd_209575 < baseStart_209575 := by decide
  rcases family_descends (prefixWord ++ tailWord_209575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209666 : List Nat := [3, 4, 1, 1, 1, 4, 2, 3]
def baseStart_209666 : Nat := 118140960795 + 209666 * 2 ^ 59
def prefixEnd_209666 : Nat := 4983230072969 + 3 ^ 40 * 209666 * 2
def baseEnd_209666 : Nat := 63798183647811504895271

theorem tailTrace_209666 : CollatzResearch.WordTrace tailWord_209666 prefixEnd_209666 63798183647811504895271 := by
  unfold tailWord_209666
  simp only [CollatzResearch.WordTrace]
  refine ⟨1911786814605841236770213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5098098172282243298053901 1911786814605841236770213)
  ·
    refine ⟨358460027738595231894415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1911786814605841236770213 358460027738595231894415)
    ·
      refine ⟨537690041607892847841623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 358460027738595231894415 537690041607892847841623)
      ·
        refine ⟨806535062411839271762435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 537690041607892847841623 806535062411839271762435)
        ·
          refine ⟨1209802593617758907643653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 806535062411839271762435 1209802593617758907643653)
          ·
            refine ⟨226837986303329795183185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1209802593617758907643653 226837986303329795183185)
            ·
              refine ⟨170128489727497346387389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 226837986303329795183185 170128489727497346387389)
              ·
                refine ⟨63798183647811504895271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 170128489727497346387389 63798183647811504895271)
                ·
                  rfl

theorem cell19_209666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 2, 3].length) (baseStart_209666 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_209666 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_209666 prefixEnd_209666 := by exact prefixLift 209666
  have htrace : WordTrace (prefixWord ++ tailWord_209666) baseStart_209666 baseEnd_209666 := by
    simpa [prefixWord, tailWord_209666, baseEnd_209666] using wordTrace_append hprefix tailTrace_209666
  have hstable : (prefixWord ++ tailWord_209666).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209666).length < 2 ^ (prefixWord ++ tailWord_209666).sum := by decide
  have hdescent : baseEnd_209666 < baseStart_209666 := by decide
  rcases family_descends (prefixWord ++ tailWord_209666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209687 : List Nat := [1, 1, 3, 4, 4, 1, 5]
def baseStart_209687 : Nat := 118140960795 + 209687 * 2 ^ 59
def prefixEnd_209687 : Nat := 4983230072969 + 3 ^ 40 * 209687 * 2
def baseEnd_209687 : Nat := 21268191209763226142849

theorem tailTrace_209687 : CollatzResearch.WordTrace tailWord_209687 prefixEnd_209687 21268191209763226142849 := by
  unfold tailWord_209687
  simp only [CollatzResearch.WordTrace]
  refine ⟨7647913191347285533595315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5098608794231523689063543 7647913191347285533595315)
  ·
    refine ⟨11471869787020928300392973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7647913191347285533595315 11471869787020928300392973)
    ·
      refine ⟨4301951170132848112647365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11471869787020928300392973 4301951170132848112647365)
      ·
        refine ⟨806615844399909021121381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4301951170132848112647365 806615844399909021121381)
        ·
          refine ⟨151240470824982941460259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 806615844399909021121381 151240470824982941460259)
          ·
            refine ⟨226860706237474412190389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151240470824982941460259 226860706237474412190389)
            ·
              refine ⟨21268191209763226142849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 226860706237474412190389 21268191209763226142849)
              ·
                rfl

theorem cell19_209687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 5].length) (baseStart_209687 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_209687 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_209687 prefixEnd_209687 := by exact prefixLift 209687
  have htrace : WordTrace (prefixWord ++ tailWord_209687) baseStart_209687 baseEnd_209687 := by
    simpa [prefixWord, tailWord_209687, baseEnd_209687] using wordTrace_append hprefix tailTrace_209687
  have hstable : (prefixWord ++ tailWord_209687).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209687).length < 2 ^ (prefixWord ++ tailWord_209687).sum := by decide
  have hdescent : baseEnd_209687 < baseStart_209687 := by decide
  rcases family_descends (prefixWord ++ tailWord_209687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209748 : List Nat := [2, 4, 1, 1, 11]
def baseStart_209748 : Nat := 118140960795 + 209748 * 2 ^ 59
def prefixEnd_209748 : Nat := 4983230072969 + 3 ^ 40 * 209748 * 2
def baseEnd_209748 : Nat := 2363819814965170780475

theorem tailTrace_209748 : CollatzResearch.WordTrace tailWord_209748 prefixEnd_209748 2363819814965170780475 := by
  unfold tailWord_209748
  simp only [CollatzResearch.WordTrace]
  refine ⟨3825069022063146475782949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5100092029417528634377265 3825069022063146475782949)
  ·
    refine ⟨717200441636839964209303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3825069022063146475782949 717200441636839964209303)
    ·
      refine ⟨1075800662455259946313955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 717200441636839964209303 1075800662455259946313955)
      ·
        refine ⟨1613700993682889919470933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1075800662455259946313955 1613700993682889919470933)
        ·
          refine ⟨2363819814965170780475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 1613700993682889919470933 2363819814965170780475)
          ·
            rfl

theorem cell19_209748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 11].length) (baseStart_209748 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_209748 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_209748 prefixEnd_209748 := by exact prefixLift 209748
  have htrace : WordTrace (prefixWord ++ tailWord_209748) baseStart_209748 baseEnd_209748 := by
    simpa [prefixWord, tailWord_209748, baseEnd_209748] using wordTrace_append hprefix tailTrace_209748
  have hstable : (prefixWord ++ tailWord_209748).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209748).length < 2 ^ (prefixWord ++ tailWord_209748).sum := by decide
  have hdescent : baseEnd_209748 < baseStart_209748 := by decide
  rcases family_descends (prefixWord ++ tailWord_209748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209841 : List Nat := [1, 2, 2, 4, 3, 1, 1, 5]
def baseStart_209841 : Nat := 118140960795 + 209841 * 2 ^ 59
def prefixEnd_209841 : Nat := 4983230072969 + 3 ^ 40 * 209841 * 2
def baseEnd_209841 : Nat := 63851433493462951005905

theorem tailTrace_209841 : CollatzResearch.WordTrace tailWord_209841 prefixEnd_209841 63851433493462951005905 := by
  unfold tailWord_209841
  simp only [CollatzResearch.WordTrace]
  refine ⟨7653530032789369834701377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5102353355192913223134251 7653530032789369834701377)
  ·
    refine ⟨5740147524592027376026033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7653530032789369834701377 5740147524592027376026033)
    ·
      refine ⟨4305110643444020532019525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5740147524592027376026033 4305110643444020532019525)
      ·
        refine ⟨807208245645753849753661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4305110643444020532019525 807208245645753849753661)
        ·
          refine ⟨302703092117157693657623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 807208245645753849753661 302703092117157693657623)
          ·
            refine ⟨454054638175736540486435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 302703092117157693657623 454054638175736540486435)
            ·
              refine ⟨681081957263604810729653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 454054638175736540486435 681081957263604810729653)
              ·
                refine ⟨63851433493462951005905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 681081957263604810729653 63851433493462951005905)
                ·
                  rfl

theorem cell19_209841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 5].length) (baseStart_209841 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_209841 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_209841 prefixEnd_209841 := by exact prefixLift 209841
  have htrace : WordTrace (prefixWord ++ tailWord_209841) baseStart_209841 baseEnd_209841 := by
    simpa [prefixWord, tailWord_209841, baseEnd_209841] using wordTrace_append hprefix tailTrace_209841
  have hstable : (prefixWord ++ tailWord_209841).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209841).length < 2 ^ (prefixWord ++ tailWord_209841).sum := by decide
  have hdescent : baseEnd_209841 < baseStart_209841 := by decide
  rcases family_descends (prefixWord ++ tailWord_209841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209881 : List Nat := [1, 2, 1, 2, 5, 1, 1, 6]
def baseStart_209881 : Nat := 118140960795 + 209881 * 2 ^ 59
def prefixEnd_209881 : Nat := 4983230072969 + 3 ^ 40 * 209881 * 2
def baseEnd_209881 : Nat := 63863604886754710116907

theorem tailTrace_209881 : CollatzResearch.WordTrace tailWord_209881 prefixEnd_209881 63863604886754710116907 := by
  unfold tailWord_209881
  simp only [CollatzResearch.WordTrace]
  refine ⟨7654988952644456666157497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5103325968429637777438331 7654988952644456666157497)
  ·
    refine ⟨5741241714483342499618123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7654988952644456666157497 5741241714483342499618123)
    ·
      refine ⟨8611862571725013749427185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5741241714483342499618123 8611862571725013749427185)
      ·
        refine ⟨6458896928793760312070389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8611862571725013749427185 6458896928793760312070389)
        ·
          refine ⟨605521587074415029256599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6458896928793760312070389 605521587074415029256599)
          ·
            refine ⟨908282380611622543884899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 605521587074415029256599 908282380611622543884899)
            ·
              refine ⟨1362423570917433815827349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 908282380611622543884899 1362423570917433815827349)
              ·
                refine ⟨63863604886754710116907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1362423570917433815827349 63863604886754710116907)
                ·
                  rfl

theorem cell19_209881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 6].length) (baseStart_209881 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_209881 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_209881 prefixEnd_209881 := by exact prefixLift 209881
  have htrace : WordTrace (prefixWord ++ tailWord_209881) baseStart_209881 baseEnd_209881 := by
    simpa [prefixWord, tailWord_209881, baseEnd_209881] using wordTrace_append hprefix tailTrace_209881
  have hstable : (prefixWord ++ tailWord_209881).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209881).length < 2 ^ (prefixWord ++ tailWord_209881).sum := by decide
  have hdescent : baseEnd_209881 < baseStart_209881 := by decide
  rcases family_descends (prefixWord ++ tailWord_209881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209955 : List Nat := [1, 1, 1, 4, 3, 3, 3, 3]
def baseStart_209955 : Nat := 118140960795 + 209955 * 2 ^ 59
def prefixEnd_209955 : Nat := 4983230072969 + 3 ^ 40 * 209955 * 2
def baseEnd_209955 : Nat := 63886121964344464472261

theorem tailTrace_209955 : CollatzResearch.WordTrace tailWord_209955 prefixEnd_209955 63886121964344464472261 := by
  unfold tailWord_209955
  simp only [CollatzResearch.WordTrace]
  refine ⟨7657687954376367304351319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5105125302917578202900879 7657687954376367304351319)
  ·
    refine ⟨11486531931564550956526979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7657687954376367304351319 11486531931564550956526979)
    ·
      refine ⟨17229797897346826434790469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11486531931564550956526979 17229797897346826434790469)
      ·
        refine ⟨3230587105752529956523213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17229797897346826434790469 3230587105752529956523213)
        ·
          refine ⟨1211470164657198733696205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3230587105752529956523213 1211470164657198733696205)
          ·
            refine ⟨454301311746449525136077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1211470164657198733696205 454301311746449525136077)
            ·
              refine ⟨170362991904918571926029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 454301311746449525136077 170362991904918571926029)
              ·
                refine ⟨63886121964344464472261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 170362991904918571926029 63886121964344464472261)
                ·
                  rfl

theorem cell19_209955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 3, 3].length) (baseStart_209955 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_209955 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_209955 prefixEnd_209955 := by exact prefixLift 209955
  have htrace : WordTrace (prefixWord ++ tailWord_209955) baseStart_209955 baseEnd_209955 := by
    simpa [prefixWord, tailWord_209955, baseEnd_209955] using wordTrace_append hprefix tailTrace_209955
  have hstable : (prefixWord ++ tailWord_209955).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209955).length < 2 ^ (prefixWord ++ tailWord_209955).sum := by decide
  have hdescent : baseEnd_209955 < baseStart_209955 := by decide
  rcases family_descends (prefixWord ++ tailWord_209955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209974 : List Nat := [5, 1, 2, 1, 1, 3, 6]
def baseStart_209974 : Nat := 118140960795 + 209974 * 2 ^ 59
def prefixEnd_209974 : Nat := 4983230072969 + 3 ^ 40 * 209974 * 2
def baseEnd_209974 : Nat := 21297301125386016683329

theorem tailTrace_209974 : CollatzResearch.WordTrace tailWord_209974 prefixEnd_209974 21297301125386016683329 := by
  unfold tailWord_209974
  simp only [CollatzResearch.WordTrace]
  refine ⟨478648808831720846830811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5105587294205022366195317 478648808831720846830811)
  ·
    refine ⟨717973213247581270246217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 478648808831720846830811 717973213247581270246217)
    ·
      refine ⟨538479909935685952684663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 717973213247581270246217 538479909935685952684663)
      ·
        refine ⟨807719864903528929026995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 538479909935685952684663 807719864903528929026995)
        ·
          refine ⟨1211579797355293393540493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 807719864903528929026995 1211579797355293393540493)
          ·
            refine ⟨454342424008235022577685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1211579797355293393540493 454342424008235022577685)
            ·
              refine ⟨21297301125386016683329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 454342424008235022577685 21297301125386016683329)
              ·
                rfl

theorem cell19_209974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 6].length) (baseStart_209974 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_209974 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_209974 prefixEnd_209974 := by exact prefixLift 209974
  have htrace : WordTrace (prefixWord ++ tailWord_209974) baseStart_209974 baseEnd_209974 := by
    simpa [prefixWord, tailWord_209974, baseEnd_209974] using wordTrace_append hprefix tailTrace_209974
  have hstable : (prefixWord ++ tailWord_209974).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209974).length < 2 ^ (prefixWord ++ tailWord_209974).sum := by decide
  have hdescent : baseEnd_209974 < baseStart_209974 := by decide
  rcases family_descends (prefixWord ++ tailWord_209974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209976 : List Nat := [2, 1, 2, 1, 5, 2, 6]
def baseStart_209976 : Nat := 118140960795 + 209976 * 2 ^ 59
def prefixEnd_209976 : Nat := 4983230072969 + 3 ^ 40 * 209976 * 2
def baseEnd_209976 : Nat := 21297503981940879335179

theorem tailTrace_209976 : CollatzResearch.WordTrace tailWord_209976 prefixEnd_209976 21297503981940879335179 := by
  unfold tailWord_209976
  simp only [CollatzResearch.WordTrace]
  refine ⟨3829226943650143945432891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5105635924866858593910521 3829226943650143945432891)
  ·
    refine ⟨5743840415475215918149337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3829226943650143945432891 5743840415475215918149337)
    ·
      refine ⟨4307880311606411938612003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5743840415475215918149337 4307880311606411938612003)
      ·
        refine ⟨6461820467409617907918005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4307880311606411938612003 6461820467409617907918005)
        ·
          refine ⟨605795668819651678867313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6461820467409617907918005 605795668819651678867313)
          ·
            refine ⟨454346751614738759150485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 605795668819651678867313 454346751614738759150485)
            ·
              refine ⟨21297503981940879335179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 454346751614738759150485 21297503981940879335179)
              ·
                rfl

theorem cell19_209976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 6].length) (baseStart_209976 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_209976 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_209976 prefixEnd_209976 := by exact prefixLift 209976
  have htrace : WordTrace (prefixWord ++ tailWord_209976) baseStart_209976 baseEnd_209976 := by
    simpa [prefixWord, tailWord_209976, baseEnd_209976] using wordTrace_append hprefix tailTrace_209976
  have hstable : (prefixWord ++ tailWord_209976).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209976).length < 2 ^ (prefixWord ++ tailWord_209976).sum := by decide
  have hdescent : baseEnd_209976 < baseStart_209976 := by decide
  rcases family_descends (prefixWord ++ tailWord_209976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210006 : List Nat := [5, 2, 2, 1, 2, 2, 2, 3]
def baseStart_210006 : Nat := 118140960795 + 210006 * 2 ^ 59
def prefixEnd_210006 : Nat := 4983230072969 + 3 ^ 40 * 210006 * 2
def baseEnd_210006 : Nat := 63901640490791457338789

theorem tailTrace_210006 : CollatzResearch.WordTrace tailWord_210006 prefixEnd_210006 63901640490791457338789 := by
  unfold tailWord_210006
  simp only [CollatzResearch.WordTrace]
  refine ⟨478721754824475188403617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5106365384794402009638581 478721754824475188403617)
  ·
    refine ⟨359041316118356391302713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 478721754824475188403617 359041316118356391302713)
    ·
      refine ⟨269280987088767293477035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 359041316118356391302713 269280987088767293477035)
      ·
        refine ⟨403921480633150940215553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269280987088767293477035 403921480633150940215553)
        ·
          refine ⟨302941110474863205161665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 403921480633150940215553 302941110474863205161665)
          ·
            refine ⟨227205832856147403871249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 302941110474863205161665 227205832856147403871249)
            ·
              refine ⟨170404374642110552903437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 227205832856147403871249 170404374642110552903437)
              ·
                refine ⟨63901640490791457338789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 170404374642110552903437 63901640490791457338789)
                ·
                  rfl

theorem cell19_210006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 2, 3].length) (baseStart_210006 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_210006 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_210006 prefixEnd_210006 := by exact prefixLift 210006
  have htrace : WordTrace (prefixWord ++ tailWord_210006) baseStart_210006 baseEnd_210006 := by
    simpa [prefixWord, tailWord_210006, baseEnd_210006] using wordTrace_append hprefix tailTrace_210006
  have hstable : (prefixWord ++ tailWord_210006).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210006).length < 2 ^ (prefixWord ++ tailWord_210006).sum := by decide
  have hdescent : baseEnd_210006 < baseStart_210006 := by decide
  rcases family_descends (prefixWord ++ tailWord_210006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210052 : List Nat := [2, 3, 2, 1, 2, 2, 1, 6]
def baseStart_210052 : Nat := 118140960795 + 210052 * 2 ^ 59
def prefixEnd_210052 : Nat := 4983230072969 + 3 ^ 40 * 210052 * 2
def baseEnd_210052 : Nat := 63915637593076980316441

theorem tailTrace_210052 : CollatzResearch.WordTrace tailWord_210052 prefixEnd_210052 63915637593076980316441 := by
  unfold tailWord_210052
  simp only [CollatzResearch.WordTrace]
  refine ⟨3830612917512476435316205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5107483890016635247088273 3830612917512476435316205)
  ·
    refine ⟨1436479844067178663243577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3830612917512476435316205 1436479844067178663243577)
    ·
      refine ⟨1077359883050383997432683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1436479844067178663243577 1077359883050383997432683)
      ·
        refine ⟨1616039824575575996149025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1077359883050383997432683 1616039824575575996149025)
        ·
          refine ⟨1212029868431681997111769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1616039824575575996149025 1212029868431681997111769)
          ·
            refine ⟨909022401323761497833827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1212029868431681997111769 909022401323761497833827)
            ·
              refine ⟨1363533601985642246750741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 909022401323761497833827 1363533601985642246750741)
              ·
                refine ⟨63915637593076980316441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1363533601985642246750741 63915637593076980316441)
                ·
                  rfl

theorem cell19_210052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 6].length) (baseStart_210052 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_210052 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_210052 prefixEnd_210052 := by exact prefixLift 210052
  have htrace : WordTrace (prefixWord ++ tailWord_210052) baseStart_210052 baseEnd_210052 := by
    simpa [prefixWord, tailWord_210052, baseEnd_210052] using wordTrace_append hprefix tailTrace_210052
  have hstable : (prefixWord ++ tailWord_210052).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210052).length < 2 ^ (prefixWord ++ tailWord_210052).sum := by decide
  have hdescent : baseEnd_210052 < baseStart_210052 := by decide
  rcases family_descends (prefixWord ++ tailWord_210052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210071 : List Nat := [1, 1, 3, 3, 3, 1, 2, 5]
def baseStart_210071 : Nat := 118140960795 + 210071 * 2 ^ 59
def prefixEnd_210071 : Nat := 4983230072969 + 3 ^ 40 * 210071 * 2
def baseEnd_210071 : Nat := 63921419004890565894167

theorem tailTrace_210071 : CollatzResearch.WordTrace tailWord_210071 prefixEnd_210071 63921419004890565894167 := by
  unfold tailWord_210071
  simp only [CollatzResearch.WordTrace]
  refine ⟨7661918821956119115574067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5107945881304079410382711 7661918821956119115574067)
  ·
    refine ⟨11492878232934178673361101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7661918821956119115574067 11492878232934178673361101)
    ·
      refine ⟨4309829337350317002510413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11492878232934178673361101 4309829337350317002510413)
      ·
        refine ⟨1616186001506368875941405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4309829337350317002510413 1616186001506368875941405)
        ·
          refine ⟨606069750564888328478027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1616186001506368875941405 606069750564888328478027)
          ·
            refine ⟨909104625847332492717041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 606069750564888328478027 909104625847332492717041)
            ·
              refine ⟨681828469385499369537781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 909104625847332492717041 681828469385499369537781)
              ·
                refine ⟨63921419004890565894167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 681828469385499369537781 63921419004890565894167)
                ·
                  rfl

theorem cell19_210071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 5].length) (baseStart_210071 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_210071 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_210071 prefixEnd_210071 := by exact prefixLift 210071
  have htrace : WordTrace (prefixWord ++ tailWord_210071) baseStart_210071 baseEnd_210071 := by
    simpa [prefixWord, tailWord_210071, baseEnd_210071] using wordTrace_append hprefix tailTrace_210071
  have hstable : (prefixWord ++ tailWord_210071).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210071).length < 2 ^ (prefixWord ++ tailWord_210071).sum := by decide
  have hdescent : baseEnd_210071 < baseStart_210071 := by decide
  rcases family_descends (prefixWord ++ tailWord_210071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210109 : List Nat := [1, 4, 1, 2, 1, 1, 5, 4]
def baseStart_210109 : Nat := 118140960795 + 210109 * 2 ^ 59
def prefixEnd_210109 : Nat := 4983230072969 + 3 ^ 40 * 210109 * 2
def baseEnd_210109 : Nat := 63932981828517737049619

theorem tailTrace_210109 : CollatzResearch.WordTrace tailWord_210109 prefixEnd_210109 63932981828517737049619 := by
  unfold tailWord_210109
  simp only [CollatzResearch.WordTrace]
  refine ⟨7663304795818451605457381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5108869863878967736971587 7663304795818451605457381)
  ·
    refine ⟨1436869649215959676023259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7663304795818451605457381 1436869649215959676023259)
    ·
      refine ⟨2155304473823939514034889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1436869649215959676023259 2155304473823939514034889)
      ·
        refine ⟨1616478355367954635526167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2155304473823939514034889 1616478355367954635526167)
        ·
          refine ⟨2424717533051931953289251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1616478355367954635526167 2424717533051931953289251)
          ·
            refine ⟨3637076299577897929933877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2424717533051931953289251 3637076299577897929933877)
            ·
              refine ⟨340975903085427930931301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3637076299577897929933877 340975903085427930931301)
              ·
                refine ⟨63932981828517737049619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 340975903085427930931301 63932981828517737049619)
                ·
                  rfl

theorem cell19_210109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5, 4].length) (baseStart_210109 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_210109 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_210109 prefixEnd_210109 := by exact prefixLift 210109
  have htrace : WordTrace (prefixWord ++ tailWord_210109) baseStart_210109 baseEnd_210109 := by
    simpa [prefixWord, tailWord_210109, baseEnd_210109] using wordTrace_append hprefix tailTrace_210109
  have hstable : (prefixWord ++ tailWord_210109).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210109).length < 2 ^ (prefixWord ++ tailWord_210109).sum := by decide
  have hdescent : baseEnd_210109 < baseStart_210109 := by decide
  rcases family_descends (prefixWord ++ tailWord_210109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210166 : List Nat := [5, 1, 1, 1, 1, 1, 1, 8]
def baseStart_210166 : Nat := 118140960795 + 210166 * 2 ^ 59
def prefixEnd_210166 : Nat := 4983230072969 + 3 ^ 40 * 210166 * 2
def baseEnd_210166 : Nat := 63950326063958493782797

theorem tailTrace_210166 : CollatzResearch.WordTrace tailWord_210166 prefixEnd_210166 63950326063958493782797 := by
  unfold tailWord_210166
  simp only [CollatzResearch.WordTrace]
  refine ⟨479086484788246896267647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5110255837741300226854901 479086484788246896267647)
  ·
    refine ⟨718629727182370344401471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 479086484788246896267647 718629727182370344401471)
    ·
      refine ⟨1077944590773555516602207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 718629727182370344401471 1077944590773555516602207)
      ·
        refine ⟨1616916886160333274903311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1077944590773555516602207 1616916886160333274903311)
        ·
          refine ⟨2425375329240499912354967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1616916886160333274903311 2425375329240499912354967)
          ·
            refine ⟨3638062993860749868532451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2425375329240499912354967 3638062993860749868532451)
            ·
              refine ⟨5457094490791124802798677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3638062993860749868532451 5457094490791124802798677)
              ·
                refine ⟨63950326063958493782797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5457094490791124802798677 63950326063958493782797)
                ·
                  rfl

theorem cell19_210166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_210166 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_210166 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_210166 prefixEnd_210166 := by exact prefixLift 210166
  have htrace : WordTrace (prefixWord ++ tailWord_210166) baseStart_210166 baseEnd_210166 := by
    simpa [prefixWord, tailWord_210166, baseEnd_210166] using wordTrace_append hprefix tailTrace_210166
  have hstable : (prefixWord ++ tailWord_210166).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210166).length < 2 ^ (prefixWord ++ tailWord_210166).sum := by decide
  have hdescent : baseEnd_210166 < baseStart_210166 := by decide
  rcases family_descends (prefixWord ++ tailWord_210166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210221 : List Nat := [1, 5, 3, 1, 1, 1, 1, 6]
def baseStart_210221 : Nat := 118140960795 + 210221 * 2 ^ 59
def prefixEnd_210221 : Nat := 4983230072969 + 3 ^ 40 * 210221 * 2
def baseEnd_210221 : Nat := 63967061729734662560425

theorem tailTrace_210221 : CollatzResearch.WordTrace tailWord_210221 prefixEnd_210221 63967061729734662560425 := by
  unfold tailWord_210221
  simp only [CollatzResearch.WordTrace]
  refine ⟨7667389771412694733534517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5111593180941796489023011 7667389771412694733534517)
  ·
    refine ⟨718817791069940131268861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7667389771412694733534517 718817791069940131268861)
    ·
      refine ⟨269556671651227549225823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 718817791069940131268861 269556671651227549225823)
      ·
        refine ⟨404335007476841323838735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269556671651227549225823 404335007476841323838735)
        ·
          refine ⟨606502511215261985758103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 404335007476841323838735 606502511215261985758103)
          ·
            refine ⟨909753766822892978637155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 606502511215261985758103 909753766822892978637155)
            ·
              refine ⟨1364630650234339467955733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 909753766822892978637155 1364630650234339467955733)
              ·
                refine ⟨63967061729734662560425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1364630650234339467955733 63967061729734662560425)
                ·
                  rfl

theorem cell19_210221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 6].length) (baseStart_210221 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_210221 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_210221 prefixEnd_210221 := by exact prefixLift 210221
  have htrace : WordTrace (prefixWord ++ tailWord_210221) baseStart_210221 baseEnd_210221 := by
    simpa [prefixWord, tailWord_210221, baseEnd_210221] using wordTrace_append hprefix tailTrace_210221
  have hstable : (prefixWord ++ tailWord_210221).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210221).length < 2 ^ (prefixWord ++ tailWord_210221).sum := by decide
  have hdescent : baseEnd_210221 < baseStart_210221 := by decide
  rcases family_descends (prefixWord ++ tailWord_210221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210263 : List Nat := [1, 1, 3, 2, 3, 9]
def baseStart_210263 : Nat := 118140960795 + 210263 * 2 ^ 59
def prefixEnd_210263 : Nat := 4983230072969 + 3 ^ 40 * 210263 * 2
def baseEnd_210263 : Nat := 7108871299187889958553

theorem tailTrace_210263 : CollatzResearch.WordTrace tailWord_210263 prefixEnd_210263 7108871299187889958553 := by
  unfold tailWord_210263
  simp only [CollatzResearch.WordTrace]
  refine ⟨7668921637260535906563443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5112614424840357271042295 7668921637260535906563443)
  ·
    refine ⟨11503382455890803859845165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7668921637260535906563443 11503382455890803859845165)
    ·
      refine ⟨4313768420959051447441937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11503382455890803859845165 4313768420959051447441937)
      ·
        refine ⟨3235326315719288585581453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4313768420959051447441937 3235326315719288585581453)
        ·
          refine ⟨1213247368394733219593045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3235326315719288585581453 1213247368394733219593045)
          ·
            refine ⟨7108871299187889958553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1213247368394733219593045 7108871299187889958553)
            ·
              rfl

theorem cell19_210263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 9].length) (baseStart_210263 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_210263 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_210263 prefixEnd_210263 := by exact prefixLift 210263
  have htrace : WordTrace (prefixWord ++ tailWord_210263) baseStart_210263 baseEnd_210263 := by
    simpa [prefixWord, tailWord_210263, baseEnd_210263] using wordTrace_append hprefix tailTrace_210263
  have hstable : (prefixWord ++ tailWord_210263).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210263).length < 2 ^ (prefixWord ++ tailWord_210263).sum := by decide
  have hdescent : baseEnd_210263 < baseStart_210263 := by decide
  rcases family_descends (prefixWord ++ tailWord_210263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210299 : List Nat := [1, 1, 1, 1, 1, 6, 5, 3]
def baseStart_210299 : Nat := 118140960795 + 210299 * 2 ^ 59
def prefixEnd_210299 : Nat := 4983230072969 + 3 ^ 40 * 210299 * 2
def baseEnd_210299 : Nat := 63990795946653592826879

theorem tailTrace_210299 : CollatzResearch.WordTrace tailWord_210299 prefixEnd_210299 63990795946653592826879 := by
  unfold tailWord_210299
  simp only [CollatzResearch.WordTrace]
  refine ⟨7670234665130114054873951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5113489776753409369915967 7670234665130114054873951)
  ·
    refine ⟨11505351997695171082310927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7670234665130114054873951 11505351997695171082310927)
    ·
      refine ⟨17258027996542756623466391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11505351997695171082310927 17258027996542756623466391)
      ·
        refine ⟨25887041994814134935199587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17258027996542756623466391 25887041994814134935199587)
        ·
          refine ⟨38830562992221202402799381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25887041994814134935199587 38830562992221202402799381)
          ·
            refine ⟨1820182640260368862631221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 38830562992221202402799381 1820182640260368862631221)
            ·
              refine ⟨170642122524409580871677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1820182640260368862631221 170642122524409580871677)
              ·
                refine ⟨63990795946653592826879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 170642122524409580871677 63990795946653592826879)
                ·
                  rfl

theorem cell19_210299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 5, 3].length) (baseStart_210299 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_210299 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_210299 prefixEnd_210299 := by exact prefixLift 210299
  have htrace : WordTrace (prefixWord ++ tailWord_210299) baseStart_210299 baseEnd_210299 := by
    simpa [prefixWord, tailWord_210299, baseEnd_210299] using wordTrace_append hprefix tailTrace_210299
  have hstable : (prefixWord ++ tailWord_210299).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210299).length < 2 ^ (prefixWord ++ tailWord_210299).sum := by decide
  have hdescent : baseEnd_210299 < baseStart_210299 := by decide
  rcases family_descends (prefixWord ++ tailWord_210299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210339 : List Nat := [1, 1, 1, 4, 1, 3, 2, 6]
def baseStart_210339 : Nat := 118140960795 + 210339 * 2 ^ 59
def prefixEnd_210339 : Nat := 4983230072969 + 3 ^ 40 * 210339 * 2
def baseEnd_210339 : Nat := 64002967339945351937881

theorem tailTrace_210339 : CollatzResearch.WordTrace tailWord_210339 prefixEnd_210339 64002967339945351937881 := by
  unfold tailWord_210339
  simp only [CollatzResearch.WordTrace]
  refine ⟨7671693584985200886330071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5114462389990133924220047 7671693584985200886330071)
  ·
    refine ⟨11507540377477801329495107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7671693584985200886330071 11507540377477801329495107)
    ·
      refine ⟨17261310566216701994242661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11507540377477801329495107 17261310566216701994242661)
      ·
        refine ⟨3236495731165631623920499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17261310566216701994242661 3236495731165631623920499)
        ·
          refine ⟨4854743596748447435880749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3236495731165631623920499 4854743596748447435880749)
          ·
            refine ⟨1820528848780667788455281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4854743596748447435880749 1820528848780667788455281)
            ·
              refine ⟨1365396636585500841341461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1820528848780667788455281 1365396636585500841341461)
              ·
                refine ⟨64002967339945351937881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1365396636585500841341461 64002967339945351937881)
                ·
                  rfl

theorem cell19_210339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 6].length) (baseStart_210339 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_210339 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_210339 prefixEnd_210339 := by exact prefixLift 210339
  have htrace : WordTrace (prefixWord ++ tailWord_210339) baseStart_210339 baseEnd_210339 := by
    simpa [prefixWord, tailWord_210339, baseEnd_210339] using wordTrace_append hprefix tailTrace_210339
  have hstable : (prefixWord ++ tailWord_210339).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210339).length < 2 ^ (prefixWord ++ tailWord_210339).sum := by decide
  have hdescent : baseEnd_210339 < baseStart_210339 := by decide
  rcases family_descends (prefixWord ++ tailWord_210339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210394 : List Nat := [3, 1, 1, 2, 3, 3, 2, 4]
def baseStart_210394 : Nat := 118140960795 + 210394 * 2 ^ 59
def prefixEnd_210394 : Nat := 4983230072969 + 3 ^ 40 * 210394 * 2
def baseEnd_210394 : Nat := 64019703005721520715509

theorem tailTrace_210394 : CollatzResearch.WordTrace tailWord_210394 prefixEnd_210394 64019703005721520715509 := by
  unfold tailWord_210394
  simp only [CollatzResearch.WordTrace]
  refine ⟨1918424899946486319895559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5115799733190630186388157 1918424899946486319895559)
  ·
    refine ⟨2877637349919729479843339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1918424899946486319895559 2877637349919729479843339)
    ·
      refine ⟨4316456024879594219765009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2877637349919729479843339 4316456024879594219765009)
      ·
        refine ⟨3237342018659695664823757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4316456024879594219765009 3237342018659695664823757)
        ·
          refine ⟨1214003256997385874308909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3237342018659695664823757 1214003256997385874308909)
          ·
            refine ⟨455251221374019702865841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1214003256997385874308909 455251221374019702865841)
            ·
              refine ⟨341438416030514777149381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 455251221374019702865841 341438416030514777149381)
              ·
                refine ⟨64019703005721520715509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 341438416030514777149381 64019703005721520715509)
                ·
                  rfl

theorem cell19_210394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2, 4].length) (baseStart_210394 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_210394 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_210394 prefixEnd_210394 := by exact prefixLift 210394
  have htrace : WordTrace (prefixWord ++ tailWord_210394) baseStart_210394 baseEnd_210394 := by
    simpa [prefixWord, tailWord_210394, baseEnd_210394] using wordTrace_append hprefix tailTrace_210394
  have hstable : (prefixWord ++ tailWord_210394).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210394).length < 2 ^ (prefixWord ++ tailWord_210394).sum := by decide
  have hdescent : baseEnd_210394 < baseStart_210394 := by decide
  rcases family_descends (prefixWord ++ tailWord_210394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210415 : List Nat := [1, 1, 2, 1, 4, 1, 4, 5]
def baseStart_210415 : Nat := 118140960795 + 210415 * 2 ^ 59
def prefixEnd_210415 : Nat := 4983230072969 + 3 ^ 40 * 210415 * 2
def baseEnd_210415 : Nat := 64026092987199694248785

theorem tailTrace_210415 : CollatzResearch.WordTrace tailWord_210415 prefixEnd_210415 64026092987199694248785 := by
  unfold tailWord_210415
  simp only [CollatzResearch.WordTrace]
  refine ⟨7674465532709865866096699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5116310355139910577397799 7674465532709865866096699)
  ·
    refine ⟨11511698299064798799145049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7674465532709865866096699 11511698299064798799145049)
    ·
      refine ⟨8633773724298599099358787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11511698299064798799145049 8633773724298599099358787)
      ·
        refine ⟨12950660586447898649038181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8633773724298599099358787 12950660586447898649038181)
        ·
          refine ⟨2428248859958980996694659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12950660586447898649038181 2428248859958980996694659)
          ·
            refine ⟨3642373289938471495041989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2428248859958980996694659 3642373289938471495041989)
            ·
              refine ⟨682944991863463405320373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3642373289938471495041989 682944991863463405320373)
              ·
                refine ⟨64026092987199694248785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 682944991863463405320373 64026092987199694248785)
                ·
                  rfl

theorem cell19_210415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 5].length) (baseStart_210415 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_210415 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_210415 prefixEnd_210415 := by exact prefixLift 210415
  have htrace : WordTrace (prefixWord ++ tailWord_210415) baseStart_210415 baseEnd_210415 := by
    simpa [prefixWord, tailWord_210415, baseEnd_210415] using wordTrace_append hprefix tailTrace_210415
  have hstable : (prefixWord ++ tailWord_210415).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210415).length < 2 ^ (prefixWord ++ tailWord_210415).sum := by decide
  have hdescent : baseEnd_210415 < baseStart_210415 := by decide
  rcases family_descends (prefixWord ++ tailWord_210415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210430 : List Nat := [4, 2, 2, 3, 1, 7]
def baseStart_210430 : Nat := 118140960795 + 210430 * 2 ^ 59
def prefixEnd_210430 : Nat := 4983230072969 + 3 ^ 40 * 210430 * 2
def baseEnd_210430 : Nat := 7114517473298233768379

theorem tailTrace_210430 : CollatzResearch.WordTrace tailWord_210430 prefixEnd_210430 7114517473298233768379 := by
  unfold tailWord_210430
  simp only [CollatzResearch.WordTrace]
  refine ⟨959376578456940428486593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5116675085103682285261829 959376578456940428486593)
  ·
    refine ⟨719532433842705321364945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 959376578456940428486593 719532433842705321364945)
    ·
      refine ⟨539649325382028991023709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 719532433842705321364945 539649325382028991023709)
      ·
        refine ⟨202368497018260871633891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 539649325382028991023709 202368497018260871633891)
        ·
          refine ⟨303552745527391307450837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202368497018260871633891 303552745527391307450837)
          ·
            refine ⟨7114517473298233768379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 303552745527391307450837 7114517473298233768379)
            ·
              rfl

theorem cell19_210430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 7].length) (baseStart_210430 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_210430 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_210430 prefixEnd_210430 := by exact prefixLift 210430
  have htrace : WordTrace (prefixWord ++ tailWord_210430) baseStart_210430 baseEnd_210430 := by
    simpa [prefixWord, tailWord_210430, baseEnd_210430] using wordTrace_append hprefix tailTrace_210430
  have hstable : (prefixWord ++ tailWord_210430).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210430).length < 2 ^ (prefixWord ++ tailWord_210430).sum := by decide
  have hdescent : baseEnd_210430 < baseStart_210430 := by decide
  rcases family_descends (prefixWord ++ tailWord_210430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210445 : List Nat := [1, 7, 1, 1, 2, 2, 1, 4]
def baseStart_210445 : Nat := 118140960795 + 210445 * 2 ^ 59
def prefixEnd_210445 : Nat := 4983230072969 + 3 ^ 40 * 210445 * 2
def baseEnd_210445 : Nat := 64035221532168513582037

theorem tailTrace_210445 : CollatzResearch.WordTrace tailWord_210445 prefixEnd_210445 64035221532168513582037 := by
  unfold tailWord_210445
  simp only [CollatzResearch.WordTrace]
  refine ⟨7675559722601180989688789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5117039815067453993125859 7675559722601180989688789)
  ·
    refine ⟨179895930998465179445831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 7675559722601180989688789 179895930998465179445831)
    ·
      refine ⟨269843896497697769168747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179895930998465179445831 269843896497697769168747)
      ·
        refine ⟨404765844746546653753121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269843896497697769168747 404765844746546653753121)
        ·
          refine ⟨303574383559909990314841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 404765844746546653753121 303574383559909990314841)
          ·
            refine ⟨227680787669932492736131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 303574383559909990314841 227680787669932492736131)
            ·
              refine ⟨341521181504898739104197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 227680787669932492736131 341521181504898739104197)
              ·
                refine ⟨64035221532168513582037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 341521181504898739104197 64035221532168513582037)
                ·
                  rfl

theorem cell19_210445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 1, 4].length) (baseStart_210445 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_210445 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_210445 prefixEnd_210445 := by exact prefixLift 210445
  have htrace : WordTrace (prefixWord ++ tailWord_210445) baseStart_210445 baseEnd_210445 := by
    simpa [prefixWord, tailWord_210445, baseEnd_210445] using wordTrace_append hprefix tailTrace_210445
  have hstable : (prefixWord ++ tailWord_210445).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210445).length < 2 ^ (prefixWord ++ tailWord_210445).sum := by decide
  have hdescent : baseEnd_210445 < baseStart_210445 := by decide
  rcases family_descends (prefixWord ++ tailWord_210445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210451 : List Nat := [1, 1, 1, 2, 1, 8, 1, 4]
def baseStart_210451 : Nat := 118140960795 + 210451 * 2 ^ 59
def prefixEnd_210451 : Nat := 4983230072969 + 3 ^ 40 * 210451 * 2
def baseEnd_210451 : Nat := 64037047241162277448687

theorem tailTrace_210451 : CollatzResearch.WordTrace tailWord_210451 prefixEnd_210451 64037047241162277448687 := by
  unfold tailWord_210451
  simp only [CollatzResearch.WordTrace]
  refine ⟨7675778560579444014407207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5117185707052962676271471 7675778560579444014407207)
  ·
    refine ⟨11513667840869166021610811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7675778560579444014407207 11513667840869166021610811)
    ·
      refine ⟨17270501761303749032416217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11513667840869166021610811 17270501761303749032416217)
      ·
        refine ⟨12952876320977811774312163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17270501761303749032416217 12952876320977811774312163)
        ·
          refine ⟨19429314481466717661468245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12952876320977811774312163 19429314481466717661468245)
          ·
            refine ⟨227687279079688097595331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 19429314481466717661468245 227687279079688097595331)
            ·
              refine ⟨341530918619532146392997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 227687279079688097595331 341530918619532146392997)
              ·
                refine ⟨64037047241162277448687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 341530918619532146392997 64037047241162277448687)
                ·
                  rfl

theorem cell19_210451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 1, 4].length) (baseStart_210451 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_210451 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_210451 prefixEnd_210451 := by exact prefixLift 210451
  have htrace : WordTrace (prefixWord ++ tailWord_210451) baseStart_210451 baseEnd_210451 := by
    simpa [prefixWord, tailWord_210451, baseEnd_210451] using wordTrace_append hprefix tailTrace_210451
  have hstable : (prefixWord ++ tailWord_210451).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210451).length < 2 ^ (prefixWord ++ tailWord_210451).sum := by decide
  have hdescent : baseEnd_210451 < baseStart_210451 := by decide
  rcases family_descends (prefixWord ++ tailWord_210451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210462 : List Nat := [4, 3, 3, 1, 1, 1, 3, 3]
def baseStart_210462 : Nat := 118140960795 + 210462 * 2 ^ 59
def prefixEnd_210462 : Nat := 4983230072969 + 3 ^ 40 * 210462 * 2
def baseEnd_210462 : Nat := 64040394374317511204213

theorem tailTrace_210462 : CollatzResearch.WordTrace tailWord_210462 prefixEnd_210462 64040394374317511204213 := by
  unfold tailWord_210462
  simp only [CollatzResearch.WordTrace]
  refine ⟨959522470442449111632205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5117453175693061928705093 959522470442449111632205)
  ·
    refine ⟨359820926415918416862077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 959522470442449111632205 359820926415918416862077)
    ·
      refine ⟨134932847405969406323279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 359820926415918416862077 134932847405969406323279)
      ·
        refine ⟨202399271108954109484919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134932847405969406323279 202399271108954109484919)
        ·
          refine ⟨303598906663431164227379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202399271108954109484919 303598906663431164227379)
          ·
            refine ⟨455398359995146746341069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 303598906663431164227379 455398359995146746341069)
            ·
              refine ⟨170774384998180029877901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 455398359995146746341069 170774384998180029877901)
              ·
                refine ⟨64040394374317511204213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 170774384998180029877901 64040394374317511204213)
                ·
                  rfl

theorem cell19_210462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 3, 3].length) (baseStart_210462 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_210462 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_210462 prefixEnd_210462 := by exact prefixLift 210462
  have htrace : WordTrace (prefixWord ++ tailWord_210462) baseStart_210462 baseEnd_210462 := by
    simpa [prefixWord, tailWord_210462, baseEnd_210462] using wordTrace_append hprefix tailTrace_210462
  have hstable : (prefixWord ++ tailWord_210462).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210462).length < 2 ^ (prefixWord ++ tailWord_210462).sum := by decide
  have hdescent : baseEnd_210462 < baseStart_210462 := by decide
  rcases family_descends (prefixWord ++ tailWord_210462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210510 : List Nat := [4, 1, 1, 1, 1, 2, 1, 8]
def baseStart_210510 : Nat := 118140960795 + 210510 * 2 ^ 59
def prefixEnd_210510 : Nat := 4983230072969 + 3 ^ 40 * 210510 * 2
def baseEnd_210510 : Nat := 64055000046267622137415

theorem tailTrace_210510 : CollatzResearch.WordTrace tailWord_210510 prefixEnd_210510 64055000046267622137415 := by
  unfold tailWord_210510
  simp only [CollatzResearch.WordTrace]
  refine ⟨959741308420712136350623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5118620311577131393869989 959741308420712136350623)
  ·
    refine ⟨1439611962631068204525935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 959741308420712136350623 1439611962631068204525935)
    ·
      refine ⟨2159417943946602306788903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1439611962631068204525935 2159417943946602306788903)
      ·
        refine ⟨3239126915919903460183355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2159417943946602306788903 3239126915919903460183355)
        ·
          refine ⟨4858690373879855190275033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3239126915919903460183355 4858690373879855190275033)
          ·
            refine ⟨3644017780409891392706275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4858690373879855190275033 3644017780409891392706275)
            ·
              refine ⟨5466026670614837089059413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3644017780409891392706275 5466026670614837089059413)
              ·
                refine ⟨64055000046267622137415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5466026670614837089059413 64055000046267622137415)
                ·
                  rfl

theorem cell19_210510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_210510 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_210510 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_210510 prefixEnd_210510 := by exact prefixLift 210510
  have htrace : WordTrace (prefixWord ++ tailWord_210510) baseStart_210510 baseEnd_210510 := by
    simpa [prefixWord, tailWord_210510, baseEnd_210510] using wordTrace_append hprefix tailTrace_210510
  have hstable : (prefixWord ++ tailWord_210510).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210510).length < 2 ^ (prefixWord ++ tailWord_210510).sum := by decide
  have hdescent : baseEnd_210510 < baseStart_210510 := by decide
  rcases family_descends (prefixWord ++ tailWord_210510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210529 : List Nat := [1, 2, 3, 1, 1, 3, 3, 5]
def baseStart_210529 : Nat := 118140960795 + 210529 * 2 ^ 59
def prefixEnd_210529 : Nat := 4983230072969 + 3 ^ 40 * 210529 * 2
def baseEnd_210529 : Nat := 64060781458081207715141

theorem tailTrace_210529 : CollatzResearch.WordTrace tailWord_210529 prefixEnd_210529 64060781458081207715141 := by
  unfold tailWord_210529
  simp only [CollatzResearch.WordTrace]
  refine ⟨7678623454296863335746641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5119082302864575557164427 7678623454296863335746641)
  ·
    refine ⟨5758967590722647501809981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7678623454296863335746641 5758967590722647501809981)
    ·
      refine ⟨2159612846520992813178743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5758967590722647501809981 2159612846520992813178743)
      ·
        refine ⟨3239419269781489219768115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2159612846520992813178743 3239419269781489219768115)
        ·
          refine ⟨4859128904672233829652173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3239419269781489219768115 4859128904672233829652173)
          ·
            refine ⟨1822173339252087686119565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4859128904672233829652173 1822173339252087686119565)
            ·
              refine ⟨683315002219532882294837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1822173339252087686119565 683315002219532882294837)
              ·
                refine ⟨64060781458081207715141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 683315002219532882294837 64060781458081207715141)
                ·
                  rfl

theorem cell19_210529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 5].length) (baseStart_210529 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_210529 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_210529 prefixEnd_210529 := by exact prefixLift 210529
  have htrace : WordTrace (prefixWord ++ tailWord_210529) baseStart_210529 baseEnd_210529 := by
    simpa [prefixWord, tailWord_210529, baseEnd_210529] using wordTrace_append hprefix tailTrace_210529
  have hstable : (prefixWord ++ tailWord_210529).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210529).length < 2 ^ (prefixWord ++ tailWord_210529).sum := by decide
  have hdescent : baseEnd_210529 < baseStart_210529 := by decide
  rcases family_descends (prefixWord ++ tailWord_210529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210546 : List Nat := [3, 2, 1, 2, 3, 3, 5]
def baseStart_210546 : Nat := 118140960795 + 210546 * 2 ^ 59
def prefixEnd_210546 : Nat := 4983230072969 + 3 ^ 40 * 210546 * 2
def baseEnd_210546 : Nat := 21355318100076735112439

theorem tailTrace_210546 : CollatzResearch.WordTrace tailWord_210546 prefixEnd_210546 21355318100076735112439 := by
  unfold tailWord_210546
  simp only [CollatzResearch.WordTrace]
  refine ⟨1919810873808818809778873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5119495663490183492743661 1919810873808818809778873)
  ·
    refine ⟨1439858155356614107334155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1919810873808818809778873 1439858155356614107334155)
    ·
      refine ⟨2159787233034921161001233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1439858155356614107334155 2159787233034921161001233)
      ·
        refine ⟨1619840424776190870750925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2159787233034921161001233 1619840424776190870750925)
        ·
          refine ⟨607440159291071576531597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1619840424776190870750925 607440159291071576531597)
          ·
            refine ⟨227790059734151841199349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 607440159291071576531597 227790059734151841199349)
            ·
              refine ⟨21355318100076735112439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 227790059734151841199349 21355318100076735112439)
              ·
                rfl

theorem cell19_210546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 5].length) (baseStart_210546 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_210546 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_210546 prefixEnd_210546 := by exact prefixLift 210546
  have htrace : WordTrace (prefixWord ++ tailWord_210546) baseStart_210546 baseEnd_210546 := by
    simpa [prefixWord, tailWord_210546, baseEnd_210546] using wordTrace_append hprefix tailTrace_210546
  have hstable : (prefixWord ++ tailWord_210546).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210546).length < 2 ^ (prefixWord ++ tailWord_210546).sum := by decide
  have hdescent : baseEnd_210546 < baseStart_210546 := by decide
  rcases family_descends (prefixWord ++ tailWord_210546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210567 : List Nat := [1, 1, 4, 2, 1, 3, 1, 6]
def baseStart_210567 : Nat := 118140960795 + 210567 * 2 ^ 59
def prefixEnd_210567 : Nat := 4983230072969 + 3 ^ 40 * 210567 * 2
def baseEnd_210567 : Nat := 64072344281708378870593

theorem tailTrace_210567 : CollatzResearch.WordTrace tailWord_210567 prefixEnd_210567 64072344281708378870593 := by
  unfold tailWord_210567
  simp only [CollatzResearch.WordTrace]
  refine ⟨7680009428159195825629955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5120006285439463883753303 7680009428159195825629955)
  ·
    refine ⟨11520014142238793738444933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7680009428159195825629955 11520014142238793738444933)
    ·
      refine ⟨2160002651669773825958425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11520014142238793738444933 2160002651669773825958425)
      ·
        refine ⟨1620001988752330369468819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2160002651669773825958425 1620001988752330369468819)
        ·
          refine ⟨2430002983128495554203229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1620001988752330369468819 2430002983128495554203229)
          ·
            refine ⟨911251118673185832826211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2430002983128495554203229 911251118673185832826211)
            ·
              refine ⟨1366876678009778749239317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 911251118673185832826211 1366876678009778749239317)
              ·
                refine ⟨64072344281708378870593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1366876678009778749239317 64072344281708378870593)
                ·
                  rfl

theorem cell19_210567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 6].length) (baseStart_210567 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_210567 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_210567 prefixEnd_210567 := by exact prefixLift 210567
  have htrace : WordTrace (prefixWord ++ tailWord_210567) baseStart_210567 baseEnd_210567 := by
    simpa [prefixWord, tailWord_210567, baseEnd_210567] using wordTrace_append hprefix tailTrace_210567
  have hstable : (prefixWord ++ tailWord_210567).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210567).length < 2 ^ (prefixWord ++ tailWord_210567).sum := by decide
  have hdescent : baseEnd_210567 < baseStart_210567 := by decide
  rcases family_descends (prefixWord ++ tailWord_210567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210622 : List Nat := [4, 2, 1, 1, 2, 2, 3, 4]
def baseStart_210622 : Nat := 118140960795 + 210622 * 2 ^ 59
def prefixEnd_210622 : Nat := 4983230072969 + 3 ^ 40 * 210622 * 2
def baseEnd_210622 : Nat := 64089079947484547648221

theorem tailTrace_210622 : CollatzResearch.WordTrace tailWord_210622 prefixEnd_210622 64089079947484547648221 := by
  unfold tailWord_210622
  simp only [CollatzResearch.WordTrace]
  refine ⟨960251930369992527360265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5121343628639960145921413 960251930369992527360265)
  ·
    refine ⟨720188947777494395520199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 960251930369992527360265 720188947777494395520199)
    ·
      refine ⟨1080283421666241593280299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 720188947777494395520199 1080283421666241593280299)
      ·
        refine ⟨1620425132499362389920449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1080283421666241593280299 1620425132499362389920449)
        ·
          refine ⟨1215318849374521792440337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1620425132499362389920449 1215318849374521792440337)
          ·
            refine ⟨911489137030891344330253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1215318849374521792440337 911489137030891344330253)
            ·
              refine ⟨341808426386584254123845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 911489137030891344330253 341808426386584254123845)
              ·
                refine ⟨64089079947484547648221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 341808426386584254123845 64089079947484547648221)
                ·
                  rfl

theorem cell19_210622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3, 4].length) (baseStart_210622 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_210622 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_210622 prefixEnd_210622 := by exact prefixLift 210622
  have htrace : WordTrace (prefixWord ++ tailWord_210622) baseStart_210622 baseEnd_210622 := by
    simpa [prefixWord, tailWord_210622, baseEnd_210622] using wordTrace_append hprefix tailTrace_210622
  have hstable : (prefixWord ++ tailWord_210622).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210622).length < 2 ^ (prefixWord ++ tailWord_210622).sum := by decide
  have hdescent : baseEnd_210622 < baseStart_210622 := by decide
  rcases family_descends (prefixWord ++ tailWord_210622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210637 : List Nat := [1, 6, 2, 1, 1, 2, 3, 3]
def baseStart_210637 : Nat := 118140960795 + 210637 * 2 ^ 59
def prefixEnd_210637 : Nat := 4983230072969 + 3 ^ 40 * 210637 * 2
def baseEnd_210637 : Nat := 64093644219968957314847

theorem tailTrace_210637 : CollatzResearch.WordTrace tailWord_210637 prefixEnd_210637 64093644219968957314847 := by
  unfold tailWord_210637
  simp only [CollatzResearch.WordTrace]
  refine ⟨7682562537905597780678165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5121708358603731853785443 7682562537905597780678165)
  ·
    refine ⟨360120118964324895969289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 7682562537905597780678165 360120118964324895969289)
    ·
      refine ⟨270090089223243671976967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 360120118964324895969289 270090089223243671976967)
      ·
        refine ⟨405135133834865507965451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270090089223243671976967 405135133834865507965451)
        ·
          refine ⟨607702700752298261948177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 405135133834865507965451 607702700752298261948177)
          ·
            refine ⟨455777025564223696461133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 607702700752298261948177 455777025564223696461133)
            ·
              refine ⟨170916384586583886172925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 455777025564223696461133 170916384586583886172925)
              ·
                refine ⟨64093644219968957314847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 170916384586583886172925 64093644219968957314847)
                ·
                  rfl

theorem cell19_210637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 3, 3].length) (baseStart_210637 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_210637 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_210637 prefixEnd_210637 := by exact prefixLift 210637
  have htrace : WordTrace (prefixWord ++ tailWord_210637) baseStart_210637 baseEnd_210637 := by
    simpa [prefixWord, tailWord_210637, baseEnd_210637] using wordTrace_append hprefix tailTrace_210637
  have hstable : (prefixWord ++ tailWord_210637).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210637).length < 2 ^ (prefixWord ++ tailWord_210637).sum := by decide
  have hdescent : baseEnd_210637 < baseStart_210637 := by decide
  rcases family_descends (prefixWord ++ tailWord_210637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210641 : List Nat := [1, 2, 2, 1, 2, 5, 3, 3]
def baseStart_210641 : Nat := 118140960795 + 210641 * 2 ^ 59
def prefixEnd_210641 : Nat := 4983230072969 + 3 ^ 40 * 210641 * 2
def baseEnd_210641 : Nat := 64094861359298133225947

theorem tailTrace_210641 : CollatzResearch.WordTrace tailWord_210641 prefixEnd_210641 64094861359298133225947 := by
  unfold tailWord_210641
  simp only [CollatzResearch.WordTrace]
  refine ⟨7682708429891106463823777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5121805619927404309215851 7682708429891106463823777)
  ·
    refine ⟨5762031322418329847867833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7682708429891106463823777 5762031322418329847867833)
    ·
      refine ⟨4321523491813747385900875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5762031322418329847867833 4321523491813747385900875)
      ·
        refine ⟨6482285237720621078851313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4321523491813747385900875 6482285237720621078851313)
        ·
          refine ⟨4861713928290465809138485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6482285237720621078851313 4861713928290465809138485)
          ·
            refine ⟨455785680777231169606733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4861713928290465809138485 455785680777231169606733)
            ·
              refine ⟨170919630291461688602525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 455785680777231169606733 170919630291461688602525)
              ·
                refine ⟨64094861359298133225947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 170919630291461688602525 64094861359298133225947)
                ·
                  rfl

theorem cell19_210641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 3, 3].length) (baseStart_210641 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_210641 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_210641 prefixEnd_210641 := by exact prefixLift 210641
  have htrace : WordTrace (prefixWord ++ tailWord_210641) baseStart_210641 baseEnd_210641 := by
    simpa [prefixWord, tailWord_210641, baseEnd_210641] using wordTrace_append hprefix tailTrace_210641
  have hstable : (prefixWord ++ tailWord_210641).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210641).length < 2 ^ (prefixWord ++ tailWord_210641).sum := by decide
  have hdescent : baseEnd_210641 < baseStart_210641 := by decide
  rcases family_descends (prefixWord ++ tailWord_210641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210698 : List Nat := [3, 1, 2, 2, 1, 3, 4, 3]
def baseStart_210698 : Nat := 118140960795 + 210698 * 2 ^ 59
def prefixEnd_210698 : Nat := 4983230072969 + 3 ^ 40 * 210698 * 2
def baseEnd_210698 : Nat := 64112205594738889959125

theorem tailTrace_210698 : CollatzResearch.WordTrace tailWord_210698 prefixEnd_210698 64112205594738889959125 := by
  unfold tailWord_210698
  simp only [CollatzResearch.WordTrace]
  refine ⟨1921196847671151299662187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5123191593789736799099165 1921196847671151299662187)
  ·
    refine ⟨2881795271506726949493281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1921196847671151299662187 2881795271506726949493281)
    ·
      refine ⟨2161346453630045212119961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2881795271506726949493281 2161346453630045212119961)
      ·
        refine ⟨1621009840222533909089971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2161346453630045212119961 1621009840222533909089971)
        ·
          refine ⟨2431514760333800863634957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1621009840222533909089971 2431514760333800863634957)
          ·
            refine ⟨911818035125175323863109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2431514760333800863634957 911818035125175323863109)
            ·
              refine ⟨170965881585970373224333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 911818035125175323863109 170965881585970373224333)
              ·
                refine ⟨64112205594738889959125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 170965881585970373224333 64112205594738889959125)
                ·
                  rfl

theorem cell19_210698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 4, 3].length) (baseStart_210698 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_210698 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_210698 prefixEnd_210698 := by exact prefixLift 210698
  have htrace : WordTrace (prefixWord ++ tailWord_210698) baseStart_210698 baseEnd_210698 := by
    simpa [prefixWord, tailWord_210698, baseEnd_210698] using wordTrace_append hprefix tailTrace_210698
  have hstable : (prefixWord ++ tailWord_210698).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210698).length < 2 ^ (prefixWord ++ tailWord_210698).sum := by decide
  have hdescent : baseEnd_210698 < baseStart_210698 := by decide
  rcases family_descends (prefixWord ++ tailWord_210698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210734 : List Nat := [4, 1, 3, 2, 2, 1, 2, 4]
def baseStart_210734 : Nat := 118140960795 + 210734 * 2 ^ 59
def prefixEnd_210734 : Nat := 4983230072969 + 3 ^ 40 * 210734 * 2
def baseEnd_210734 : Nat := 64123159848701473159027

theorem tailTrace_210734 : CollatzResearch.WordTrace tailWord_210734 prefixEnd_210734 64123159848701473159027 := by
  unfold tailWord_210734
  simp only [CollatzResearch.WordTrace]
  refine ⟨960762552319272918369907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5124066945702788897972837 960762552319272918369907)
  ·
    refine ⟨1441143828478909377554861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 960762552319272918369907 1441143828478909377554861)
    ·
      refine ⟨540428935679591016583073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1441143828478909377554861 540428935679591016583073)
      ·
        refine ⟨405321701759693262437305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 540428935679591016583073 405321701759693262437305)
        ·
          refine ⟨303991276319769946827979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 405321701759693262437305 303991276319769946827979)
          ·
            refine ⟨455986914479654920241969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 303991276319769946827979 455986914479654920241969)
            ·
              refine ⟨341990185859741190181477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 455986914479654920241969 341990185859741190181477)
              ·
                refine ⟨64123159848701473159027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 341990185859741190181477 64123159848701473159027)
                ·
                  rfl

theorem cell19_210734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 2, 4].length) (baseStart_210734 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_210734 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_210734 prefixEnd_210734 := by exact prefixLift 210734
  have htrace : WordTrace (prefixWord ++ tailWord_210734) baseStart_210734 baseEnd_210734 := by
    simpa [prefixWord, tailWord_210734, baseEnd_210734] using wordTrace_append hprefix tailTrace_210734
  have hstable : (prefixWord ++ tailWord_210734).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210734).length < 2 ^ (prefixWord ++ tailWord_210734).sum := by decide
  have hdescent : baseEnd_210734 < baseStart_210734 := by decide
  rcases family_descends (prefixWord ++ tailWord_210734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210738 : List Nat := [3, 2, 1, 1, 3, 2, 1, 6]
def baseStart_210738 : Nat := 118140960795 + 210738 * 2 ^ 59
def prefixEnd_210738 : Nat := 4983230072969 + 3 ^ 40 * 210738 * 2
def baseEnd_210738 : Nat := 64124376988030649070127

theorem tailTrace_210738 : CollatzResearch.WordTrace tailWord_210738 prefixEnd_210738 64124376988030649070127 := by
  unfold tailWord_210738
  simp only [CollatzResearch.WordTrace]
  refine ⟨1921561577634923007526217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5124164207026461353403245 1921561577634923007526217)
  ·
    refine ⟨1441171183226192255644663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1921561577634923007526217 1441171183226192255644663)
    ·
      refine ⟨2161756774839288383466995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1441171183226192255644663 2161756774839288383466995)
      ·
        refine ⟨3242635162258932575200493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2161756774839288383466995 3242635162258932575200493)
        ·
          refine ⟨1215988185847099715700185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3242635162258932575200493 1215988185847099715700185)
          ·
            refine ⟨911991139385324786775139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1215988185847099715700185 911991139385324786775139)
            ·
              refine ⟨1367986709077987180162709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 911991139385324786775139 1367986709077987180162709)
              ·
                refine ⟨64124376988030649070127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1367986709077987180162709 64124376988030649070127)
                ·
                  rfl

theorem cell19_210738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 6].length) (baseStart_210738 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_210738 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_210738 prefixEnd_210738 := by exact prefixLift 210738
  have htrace : WordTrace (prefixWord ++ tailWord_210738) baseStart_210738 baseEnd_210738 := by
    simpa [prefixWord, tailWord_210738, baseEnd_210738] using wordTrace_append hprefix tailTrace_210738
  have hstable : (prefixWord ++ tailWord_210738).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210738).length < 2 ^ (prefixWord ++ tailWord_210738).sum := by decide
  have hdescent : baseEnd_210738 < baseStart_210738 := by decide
  rcases family_descends (prefixWord ++ tailWord_210738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210869 : List Nat := [1, 3, 3, 2, 1, 2, 4, 3]
def baseStart_210869 : Nat := 118140960795 + 210869 * 2 ^ 59
def prefixEnd_210869 : Nat := 4983230072969 + 3 ^ 40 * 210869 * 2
def baseEnd_210869 : Nat := 64164238301061160158659

theorem tailTrace_210869 : CollatzResearch.WordTrace tailWord_210869 prefixEnd_210869 64164238301061160158659 := by
  unfold tailWord_210869
  simp only [CollatzResearch.WordTrace]
  refine ⟨7691024273065101403123661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5127349515376734268749107 7691024273065101403123661)
  ·
    refine ⟨2884134102399413026171373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7691024273065101403123661 2884134102399413026171373)
    ·
      refine ⟨1081550288399779884814265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2884134102399413026171373 1081550288399779884814265)
      ·
        refine ⟨811162716299834913610699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1081550288399779884814265 811162716299834913610699)
        ·
          refine ⟨1216744074449752370416049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 811162716299834913610699 1216744074449752370416049)
          ·
            refine ⟨912558055837314277812037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1216744074449752370416049 912558055837314277812037)
            ·
              refine ⟨171104635469496427089757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 912558055837314277812037 171104635469496427089757)
              ·
                refine ⟨64164238301061160158659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 171104635469496427089757 64164238301061160158659)
                ·
                  rfl

theorem cell19_210869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 4, 3].length) (baseStart_210869 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_210869 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_210869 prefixEnd_210869 := by exact prefixLift 210869
  have htrace : WordTrace (prefixWord ++ tailWord_210869) baseStart_210869 baseEnd_210869 := by
    simpa [prefixWord, tailWord_210869, baseEnd_210869] using wordTrace_append hprefix tailTrace_210869
  have hstable : (prefixWord ++ tailWord_210869).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210869).length < 2 ^ (prefixWord ++ tailWord_210869).sum := by decide
  have hdescent : baseEnd_210869 < baseStart_210869 := by decide
  rcases family_descends (prefixWord ++ tailWord_210869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210949 : List Nat := [1, 3, 1, 1, 2, 11]
def baseStart_210949 : Nat := 118140960795 + 210949 * 2 ^ 59
def prefixEnd_210949 : Nat := 4983230072969 + 3 ^ 40 * 210949 * 2
def baseEnd_210949 : Nat := 7132064565293853153407

theorem tailTrace_210949 : CollatzResearch.WordTrace tailWord_210949 prefixEnd_210949 7132064565293853153407 := by
  unfold tailWord_210949
  simp only [CollatzResearch.WordTrace]
  refine ⟨7693942112775275066035901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5129294741850183377357267 7693942112775275066035901)
  ·
    refine ⟨2885228292290728149763463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7693942112775275066035901 2885228292290728149763463)
    ·
      refine ⟨4327842438436092224645195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2885228292290728149763463 4327842438436092224645195)
      ·
        refine ⟨6491763657654138336967793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4327842438436092224645195 6491763657654138336967793)
        ·
          refine ⟨4868822743240603752725845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6491763657654138336967793 4868822743240603752725845)
          ·
            refine ⟨7132064565293853153407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 4868822743240603752725845 7132064565293853153407)
            ·
              rfl

theorem cell19_210949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 11].length) (baseStart_210949 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_210949 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_210949 prefixEnd_210949 := by exact prefixLift 210949
  have htrace : WordTrace (prefixWord ++ tailWord_210949) baseStart_210949 baseEnd_210949 := by
    simpa [prefixWord, tailWord_210949, baseEnd_210949] using wordTrace_append hprefix tailTrace_210949
  have hstable : (prefixWord ++ tailWord_210949).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210949).length < 2 ^ (prefixWord ++ tailWord_210949).sum := by decide
  have hdescent : baseEnd_210949 < baseStart_210949 := by decide
  rcases family_descends (prefixWord ++ tailWord_210949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211025 : List Nat := [1, 2, 2, 1, 3, 1, 1, 8]
def baseStart_211025 : Nat := 118140960795 + 211025 * 2 ^ 59
def prefixEnd_211025 : Nat := 4983230072969 + 3 ^ 40 * 211025 * 2
def baseEnd_211025 : Nat := 64211706734899020691567

theorem tailTrace_211025 : CollatzResearch.WordTrace tailWord_211025 prefixEnd_211025 64211706734899020691567 := by
  unfold tailWord_211025
  simp only [CollatzResearch.WordTrace]
  refine ⟨7696714060499940045802529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5131142706999960030535019 7696714060499940045802529)
  ·
    refine ⟨5772535545374955034351897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7696714060499940045802529 5772535545374955034351897)
    ·
      refine ⟨4329401659031216275763923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5772535545374955034351897 4329401659031216275763923)
      ·
        refine ⟨6494102488546824413645885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4329401659031216275763923 6494102488546824413645885)
        ·
          refine ⟨2435288433205059155117207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6494102488546824413645885 2435288433205059155117207)
          ·
            refine ⟨3652932649807588732675811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2435288433205059155117207 3652932649807588732675811)
            ·
              refine ⟨5479398974711383099013717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3652932649807588732675811 5479398974711383099013717)
              ·
                refine ⟨64211706734899020691567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5479398974711383099013717 64211706734899020691567)
                ·
                  rfl

theorem cell19_211025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 8].length) (baseStart_211025 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_211025 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_211025 prefixEnd_211025 := by exact prefixLift 211025
  have htrace : WordTrace (prefixWord ++ tailWord_211025) baseStart_211025 baseEnd_211025 := by
    simpa [prefixWord, tailWord_211025, baseEnd_211025] using wordTrace_append hprefix tailTrace_211025
  have hstable : (prefixWord ++ tailWord_211025).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211025).length < 2 ^ (prefixWord ++ tailWord_211025).sum := by decide
  have hdescent : baseEnd_211025 < baseStart_211025 := by decide
  rcases family_descends (prefixWord ++ tailWord_211025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan19Incremental
