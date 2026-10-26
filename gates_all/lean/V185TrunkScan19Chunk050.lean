import V185TrunkScan19Chunk049

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental

namespace V185TrunkScan19Incremental

def tailWord_501075 : List Nat := [1, 1, 1, 2, 1, 1, 9, 3]
def baseStart_501075 : Nat := 118140960795 + 501075 * 2 ^ 59
def prefixEnd_501075 : Nat := 4983230072969 + 3 ^ 40 * 501075 * 2
def baseEnd_501075 : Nat := 152469522341767274345543

theorem tailTrace_501075 : CollatzResearch.WordTrace tailWord_501075 prefixEnd_501075 152469522341767274345543 := by
  unfold tailWord_501075
  simp only [CollatzResearch.WordTrace]
  refine ⟨18275706659698326641992679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12183804439798884427995119 18275706659698326641992679)
  ·
    refine ⟨27413559989547489962989019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18275706659698326641992679 27413559989547489962989019)
    ·
      refine ⟨41120339984321234944483529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27413559989547489962989019 41120339984321234944483529)
      ·
        refine ⟨30840254988240926208362647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41120339984321234944483529 30840254988240926208362647)
        ·
          refine ⟨46260382482361389312543971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30840254988240926208362647 46260382482361389312543971)
          ·
            refine ⟨69390573723542083968815957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46260382482361389312543971 69390573723542083968815957)
            ·
              refine ⟨406585392911379398254781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 69390573723542083968815957 406585392911379398254781)
              ·
                refine ⟨152469522341767274345543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 406585392911379398254781 152469522341767274345543)
                ·
                  rfl

theorem cell19_501075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 9, 3].length) (baseStart_501075 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_501075 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_501075 prefixEnd_501075 := by exact prefixLift 501075
  have htrace : WordTrace (prefixWord ++ tailWord_501075) baseStart_501075 baseEnd_501075 := by
    simpa [prefixWord, tailWord_501075, baseEnd_501075] using wordTrace_append hprefix tailTrace_501075
  have hstable : (prefixWord ++ tailWord_501075).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501075).length < 2 ^ (prefixWord ++ tailWord_501075).sum := by decide
  have hdescent : baseEnd_501075 < baseStart_501075 := by decide
  rcases family_descends (prefixWord ++ tailWord_501075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501115 : List Nat := [1, 1, 1, 1, 1, 6, 2, 6]
def baseStart_501115 : Nat := 118140960795 + 501115 * 2 ^ 59
def prefixEnd_501115 : Nat := 4983230072969 + 3 ^ 40 * 501115 * 2
def baseEnd_501115 : Nat := 152481693735059033456545

theorem tailTrace_501115 : CollatzResearch.WordTrace tailWord_501115 prefixEnd_501115 152481693735059033456545 := by
  unfold tailWord_501115
  simp only [CollatzResearch.WordTrace]
  refine ⟨18277165579553413473448799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12184777053035608982299199 18277165579553413473448799)
  ·
    refine ⟨27415748369330120210173199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18277165579553413473448799 27415748369330120210173199)
    ·
      refine ⟨41123622553995180315259799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27415748369330120210173199 41123622553995180315259799)
      ·
        refine ⟨61685433830992770472889699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41123622553995180315259799 61685433830992770472889699)
        ·
          refine ⟨92528150746489155709334549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61685433830992770472889699 92528150746489155709334549)
          ·
            refine ⟨4337257066241679173875057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 92528150746489155709334549 4337257066241679173875057)
            ·
              refine ⟨3252942799681259380406293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4337257066241679173875057 3252942799681259380406293)
              ·
                refine ⟨152481693735059033456545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3252942799681259380406293 152481693735059033456545)
                ·
                  rfl

theorem cell19_501115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 6].length) (baseStart_501115 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_501115 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_501115 prefixEnd_501115 := by exact prefixLift 501115
  have htrace : WordTrace (prefixWord ++ tailWord_501115) baseStart_501115 baseEnd_501115 := by
    simpa [prefixWord, tailWord_501115, baseEnd_501115] using wordTrace_append hprefix tailTrace_501115
  have hstable : (prefixWord ++ tailWord_501115).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501115).length < 2 ^ (prefixWord ++ tailWord_501115).sum := by decide
  have hdescent : baseEnd_501115 < baseStart_501115 := by decide
  rcases family_descends (prefixWord ++ tailWord_501115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501151 : List Nat := [1, 1, 2, 5, 1, 4, 5]
def baseStart_501151 : Nat := 118140960795 + 501151 * 2 ^ 59
def prefixEnd_501151 : Nat := 4983230072969 + 3 ^ 40 * 501151 * 2
def baseEnd_501151 : Nat := 50830882663007205552149

theorem tailTrace_501151 : CollatzResearch.WordTrace tailWord_501151 prefixEnd_501151 50830882663007205552149 := by
  unfold tailWord_501151
  simp only [CollatzResearch.WordTrace]
  refine ⟨18278478607422991621759307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12185652404948661081172871 18278478607422991621759307)
  ·
    refine ⟨27417717911134487432638961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18278478607422991621759307 27417717911134487432638961)
    ·
      refine ⟨20563288433350865574479221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27417717911134487432638961 20563288433350865574479221)
      ·
        refine ⟨1927808290626643647607427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20563288433350865574479221 1927808290626643647607427)
        ·
          refine ⟨2891712435939965471411141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1927808290626643647607427 2891712435939965471411141)
          ·
            refine ⟨542196081738743525889589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2891712435939965471411141 542196081738743525889589)
            ·
              refine ⟨50830882663007205552149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 542196081738743525889589 50830882663007205552149)
              ·
                rfl

theorem cell19_501151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 5].length) (baseStart_501151 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_501151 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_501151 prefixEnd_501151 := by exact prefixLift 501151
  have htrace : WordTrace (prefixWord ++ tailWord_501151) baseStart_501151 baseEnd_501151 := by
    simpa [prefixWord, tailWord_501151, baseEnd_501151] using wordTrace_append hprefix tailTrace_501151
  have hstable : (prefixWord ++ tailWord_501151).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501151).length < 2 ^ (prefixWord ++ tailWord_501151).sum := by decide
  have hdescent : baseEnd_501151 < baseStart_501151 := by decide
  rcases family_descends (prefixWord ++ tailWord_501151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501191 : List Nat := [1, 1, 4, 1, 1, 3, 1, 7]
def baseStart_501191 : Nat := 118140960795 + 501191 * 2 ^ 59
def prefixEnd_501191 : Nat := 4983230072969 + 3 ^ 40 * 501191 * 2
def baseEnd_501191 : Nat := 152504819382313375767449

theorem tailTrace_501191 : CollatzResearch.WordTrace tailWord_501191 prefixEnd_501191 152504819382313375767449 := by
  unfold tailWord_501191
  simp only [CollatzResearch.WordTrace]
  refine ⟨18279937527278078453215427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12186625018185385635476951 18279937527278078453215427)
  ·
    refine ⟨27419906290917117679823141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18279937527278078453215427 27419906290917117679823141)
    ·
      refine ⟨5141232429546959564966839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27419906290917117679823141 5141232429546959564966839)
      ·
        refine ⟨7711848644320439347450259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5141232429546959564966839 7711848644320439347450259)
        ·
          refine ⟨11567772966480659021175389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7711848644320439347450259 11567772966480659021175389)
          ·
            refine ⟨4337914862430247132940771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11567772966480659021175389 4337914862430247132940771)
            ·
              refine ⟨6506872293645370699411157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4337914862430247132940771 6506872293645370699411157)
              ·
                refine ⟨152504819382313375767449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6506872293645370699411157 152504819382313375767449)
                ·
                  rfl

theorem cell19_501191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 7].length) (baseStart_501191 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_501191 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_501191 prefixEnd_501191 := by exact prefixLift 501191
  have htrace : WordTrace (prefixWord ++ tailWord_501191) baseStart_501191 baseEnd_501191 := by
    simpa [prefixWord, tailWord_501191, baseEnd_501191] using wordTrace_append hprefix tailTrace_501191
  have hstable : (prefixWord ++ tailWord_501191).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501191).length < 2 ^ (prefixWord ++ tailWord_501191).sum := by decide
  have hdescent : baseEnd_501191 < baseStart_501191 := by decide
  rcases family_descends (prefixWord ++ tailWord_501191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501210 : List Nat := [3, 1, 1, 2, 3, 9]
def baseStart_501210 : Nat := 118140960795 + 501210 * 2 ^ 59
def prefixEnd_501210 : Nat := 4983230072969 + 3 ^ 40 * 501210 * 2
def baseEnd_501210 : Nat := 16945622310458551260575

theorem tailTrace_501210 : CollatzResearch.WordTrace tailWord_501210 prefixEnd_501210 16945622310458551260575 := by
  unfold tailWord_501210
  simp only [CollatzResearch.WordTrace]
  refine ⟨4570157628552311174539271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12187087009472829798771389 4570157628552311174539271)
  ·
    refine ⟨6855236442828466761808907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4570157628552311174539271 6855236442828466761808907)
    ·
      refine ⟨10282854664242700142713361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6855236442828466761808907 10282854664242700142713361)
      ·
        refine ⟨7712140998182025107035021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10282854664242700142713361 7712140998182025107035021)
        ·
          refine ⟨2892052874318259415138133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7712140998182025107035021 2892052874318259415138133)
          ·
            refine ⟨16945622310458551260575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2892052874318259415138133 16945622310458551260575)
            ·
              rfl

theorem cell19_501210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 9].length) (baseStart_501210 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_501210 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_501210 prefixEnd_501210 := by exact prefixLift 501210
  have htrace : WordTrace (prefixWord ++ tailWord_501210) baseStart_501210 baseEnd_501210 := by
    simpa [prefixWord, tailWord_501210, baseEnd_501210] using wordTrace_append hprefix tailTrace_501210
  have hstable : (prefixWord ++ tailWord_501210).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501210).length < 2 ^ (prefixWord ++ tailWord_501210).sum := by decide
  have hdescent : baseEnd_501210 < baseStart_501210 := by decide
  rcases family_descends (prefixWord ++ tailWord_501210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501261 : List Nat := [1, 7, 1, 1, 2, 1, 6]
def baseStart_501261 : Nat := 118140960795 + 501261 * 2 ^ 59
def prefixEnd_501261 : Nat := 4983230072969 + 3 ^ 40 * 501261 * 2
def baseEnd_501261 : Nat := 50842039773524651403901

theorem tailTrace_501261 : CollatzResearch.WordTrace tailWord_501261 prefixEnd_501261 50842039773524651403901 := by
  unfold tailWord_501261
  simp only [CollatzResearch.WordTrace]
  refine ⟨18282490637024480408263637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12188327091349653605509091 18282490637024480408263637)
  ·
    refine ⟨428495874305261259568679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 18282490637024480408263637 428495874305261259568679)
    ·
      refine ⟨642743811457891889353019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 428495874305261259568679 642743811457891889353019)
      ·
        refine ⟨964115717186837834029529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 642743811457891889353019 964115717186837834029529)
        ·
          refine ⟨723086787890128375522147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 964115717186837834029529 723086787890128375522147)
          ·
            refine ⟨1084630181835192563283221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 723086787890128375522147 1084630181835192563283221)
            ·
              refine ⟨50842039773524651403901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1084630181835192563283221 50842039773524651403901)
              ·
                rfl

theorem cell19_501261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 6].length) (baseStart_501261 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_501261 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_501261 prefixEnd_501261 := by exact prefixLift 501261
  have htrace : WordTrace (prefixWord ++ tailWord_501261) baseStart_501261 baseEnd_501261 := by
    simpa [prefixWord, tailWord_501261, baseEnd_501261] using wordTrace_append hprefix tailTrace_501261
  have hstable : (prefixWord ++ tailWord_501261).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501261).length < 2 ^ (prefixWord ++ tailWord_501261).sum := by decide
  have hdescent : baseEnd_501261 < baseStart_501261 := by decide
  rcases family_descends (prefixWord ++ tailWord_501261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501267 : List Nat := [1, 1, 1, 2, 1, 7, 6]
def baseStart_501267 : Nat := 118140960795 + 501267 * 2 ^ 59
def prefixEnd_501267 : Nat := 4983230072969 + 3 ^ 40 * 501267 * 2
def baseEnd_501267 : Nat := 50842648343189239359451

theorem tailTrace_501267 : CollatzResearch.WordTrace tailWord_501267 prefixEnd_501267 50842648343189239359451 := by
  unfold tailWord_501267
  simp only [CollatzResearch.WordTrace]
  refine ⟨18282709475002743432982055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12188472983335162288654703 18282709475002743432982055)
  ·
    refine ⟨27424064212504115149473083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18282709475002743432982055 27424064212504115149473083)
    ·
      refine ⟨41136096318756172724209625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27424064212504115149473083 41136096318756172724209625)
      ·
        refine ⟨30852072239067129543157219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41136096318756172724209625 30852072239067129543157219)
        ·
          refine ⟨46278108358600694314735829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30852072239067129543157219 46278108358600694314735829)
          ·
            refine ⟨1084643164654703773001621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 46278108358600694314735829 1084643164654703773001621)
            ·
              refine ⟨50842648343189239359451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1084643164654703773001621 50842648343189239359451)
              ·
                rfl

theorem cell19_501267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 6].length) (baseStart_501267 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_501267 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_501267 prefixEnd_501267 := by exact prefixLift 501267
  have htrace : WordTrace (prefixWord ++ tailWord_501267) baseStart_501267 baseEnd_501267 := by
    simpa [prefixWord, tailWord_501267, baseEnd_501267] using wordTrace_append hprefix tailTrace_501267
  have hstable : (prefixWord ++ tailWord_501267).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501267).length < 2 ^ (prefixWord ++ tailWord_501267).sum := by decide
  have hdescent : baseEnd_501267 < baseStart_501267 := by decide
  rcases family_descends (prefixWord ++ tailWord_501267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501301 : List Nat := [1, 3, 3, 1, 1, 5, 2, 3]
def baseStart_501301 : Nat := 118140960795 + 501301 * 2 ^ 59
def prefixEnd_501301 : Nat := 4983230072969 + 3 ^ 40 * 501301 * 2
def baseEnd_501301 : Nat := 152538290713865713322705

theorem tailTrace_501301 : CollatzResearch.WordTrace tailWord_501301 prefixEnd_501301 152538290713865713322705 := by
  unfold tailWord_501301
  simp only [CollatzResearch.WordTrace]
  refine ⟨18283949556879567239719757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12189299704586378159813171 18283949556879567239719757)
  ·
    refine ⟨6856481083829837714894909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18283949556879567239719757 6856481083829837714894909)
    ·
      refine ⟨2571180406436189143085591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6856481083829837714894909 2571180406436189143085591)
      ·
        refine ⟨3856770609654283714628387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2571180406436189143085591 3856770609654283714628387)
        ·
          refine ⟨5785155914481425571942581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3856770609654283714628387 5785155914481425571942581)
          ·
            refine ⟨542358366982633647369617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5785155914481425571942581 542358366982633647369617)
            ·
              refine ⟨406768775236975235527213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 542358366982633647369617 406768775236975235527213)
              ·
                refine ⟨152538290713865713322705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 406768775236975235527213 152538290713865713322705)
                ·
                  rfl

theorem cell19_501301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 2, 3].length) (baseStart_501301 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_501301 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_501301 prefixEnd_501301 := by exact prefixLift 501301
  have htrace : WordTrace (prefixWord ++ tailWord_501301) baseStart_501301 baseEnd_501301 := by
    simpa [prefixWord, tailWord_501301, baseEnd_501301] using wordTrace_append hprefix tailTrace_501301
  have hstable : (prefixWord ++ tailWord_501301).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501301).length < 2 ^ (prefixWord ++ tailWord_501301).sum := by decide
  have hdescent : baseEnd_501301 < baseStart_501301 := by decide
  rcases family_descends (prefixWord ++ tailWord_501301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501303 : List Nat := [1, 1, 3, 1, 2, 4, 4, 3]
def baseStart_501303 : Nat := 118140960795 + 501303 * 2 ^ 59
def prefixEnd_501303 : Nat := 4983230072969 + 3 ^ 40 * 501303 * 2
def baseEnd_501303 : Nat := 152538899283530301278255

theorem tailTrace_501303 : CollatzResearch.WordTrace tailWord_501303 prefixEnd_501303 152538899283530301278255 := by
  unfold tailWord_501303
  simp only [CollatzResearch.WordTrace]
  refine ⟨18284022502872321581292563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12189348335248214387528375 18284022502872321581292563)
  ·
    refine ⟨27426033754308482371938845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18284022502872321581292563 27426033754308482371938845)
    ·
      refine ⟨10284762657865680889477067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27426033754308482371938845 10284762657865680889477067)
      ·
        refine ⟨15427143986798521334215601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10284762657865680889477067 15427143986798521334215601)
        ·
          refine ⟨11570357990098891000661701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15427143986798521334215601 11570357990098891000661701)
          ·
            refine ⟨2169442123143542062624069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11570357990098891000661701 2169442123143542062624069)
            ·
              refine ⟨406770398089414136742013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2169442123143542062624069 406770398089414136742013)
              ·
                refine ⟨152538899283530301278255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 406770398089414136742013 152538899283530301278255)
                ·
                  rfl

theorem cell19_501303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 4, 3].length) (baseStart_501303 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_501303 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_501303 prefixEnd_501303 := by exact prefixLift 501303
  have htrace : WordTrace (prefixWord ++ tailWord_501303) baseStart_501303 baseEnd_501303 := by
    simpa [prefixWord, tailWord_501303, baseEnd_501303] using wordTrace_append hprefix tailTrace_501303
  have hstable : (prefixWord ++ tailWord_501303).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501303).length < 2 ^ (prefixWord ++ tailWord_501303).sum := by decide
  have hdescent : baseEnd_501303 < baseStart_501303 := by decide
  rcases family_descends (prefixWord ++ tailWord_501303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501318 : List Nat := [6, 1, 1, 1, 3, 2, 5]
def baseStart_501318 : Nat := 118140960795 + 501318 * 2 ^ 59
def prefixEnd_501318 : Nat := 4983230072969 + 3 ^ 40 * 501318 * 2
def baseEnd_501318 : Nat := 50847821185338236981627

theorem tailTrace_501318 : CollatzResearch.WordTrace tailWord_501318 prefixEnd_501318 50847821185338236981627 := by
  unfold tailWord_501318
  simp only [CollatzResearch.WordTrace]
  refine ⟨571392799931811848221519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 12189713065211986095392405 571392799931811848221519)
  ·
    refine ⟨857089199897717772332279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 571392799931811848221519 857089199897717772332279)
    ·
      refine ⟨1285633799846576658498419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 857089199897717772332279 1285633799846576658498419)
      ·
        refine ⟨1928450699769864987747629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1285633799846576658498419 1928450699769864987747629)
        ·
          refine ⟨723169012413699370405361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1928450699769864987747629 723169012413699370405361)
          ·
            refine ⟨542376759310274527804021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 723169012413699370405361 542376759310274527804021)
            ·
              refine ⟨50847821185338236981627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 542376759310274527804021 50847821185338236981627)
              ·
                rfl

theorem cell19_501318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 5].length) (baseStart_501318 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_501318 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_501318 prefixEnd_501318 := by exact prefixLift 501318
  have htrace : WordTrace (prefixWord ++ tailWord_501318) baseStart_501318 baseEnd_501318 := by
    simpa [prefixWord, tailWord_501318, baseEnd_501318] using wordTrace_append hprefix tailTrace_501318
  have hstable : (prefixWord ++ tailWord_501318).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501318).length < 2 ^ (prefixWord ++ tailWord_501318).sum := by decide
  have hdescent : baseEnd_501318 < baseStart_501318 := by decide
  rcases family_descends (prefixWord ++ tailWord_501318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501324 : List Nat := [2, 2, 1, 3, 1, 3, 7]
def baseStart_501324 : Nat := 118140960795 + 501324 * 2 ^ 59
def prefixEnd_501324 : Nat := 4983230072969 + 3 ^ 40 * 501324 * 2
def baseEnd_501324 : Nat := 50848429755002824937177

theorem tailTrace_501324 : CollatzResearch.WordTrace tailWord_501324 prefixEnd_501324 50848429755002824937177 := by
  unfold tailWord_501324
  simp only [CollatzResearch.WordTrace]
  refine ⟨9142394217898121083903513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12189858957197494778538017 9142394217898121083903513)
  ·
    refine ⟨6856795663423590812927635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9142394217898121083903513 6856795663423590812927635)
    ·
      refine ⟨10285193495135386219391453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6856795663423590812927635 10285193495135386219391453)
      ·
        refine ⟨3856947560675769832271795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10285193495135386219391453 3856947560675769832271795)
        ·
          refine ⟨5785421341013654748407693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3856947560675769832271795 5785421341013654748407693)
          ·
            refine ⟨2169533002880120530652885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5785421341013654748407693 2169533002880120530652885)
            ·
              refine ⟨50848429755002824937177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2169533002880120530652885 50848429755002824937177)
              ·
                rfl

theorem cell19_501324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 7].length) (baseStart_501324 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_501324 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_501324 prefixEnd_501324 := by exact prefixLift 501324
  have htrace : WordTrace (prefixWord ++ tailWord_501324) baseStart_501324 baseEnd_501324 := by
    simpa [prefixWord, tailWord_501324, baseEnd_501324] using wordTrace_append hprefix tailTrace_501324
  have hstable : (prefixWord ++ tailWord_501324).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501324).length < 2 ^ (prefixWord ++ tailWord_501324).sum := by decide
  have hdescent : baseEnd_501324 < baseStart_501324 := by decide
  rcases family_descends (prefixWord ++ tailWord_501324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501394 : List Nat := [3, 2, 3, 1, 4, 1, 1, 4]
def baseStart_501394 : Nat := 118140960795 + 501394 * 2 ^ 59
def prefixEnd_501394 : Nat := 4983230072969 + 3 ^ 40 * 501394 * 2
def baseEnd_501394 : Nat := 152566589203269053255785

theorem tailTrace_501394 : CollatzResearch.WordTrace tailWord_501394 prefixEnd_501394 152566589203269053255785 := by
  unfold tailWord_501394
  simp only [CollatzResearch.WordTrace]
  refine ⟨4571835386385661030713809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12191561030361762748570157 4571835386385661030713809)
  ·
    refine ⟨3428876539789245773035357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4571835386385661030713809 3428876539789245773035357)
    ·
      refine ⟨1285828702420967164888259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3428876539789245773035357 1285828702420967164888259)
      ·
        refine ⟨1928743053631450747332389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1285828702420967164888259 1928743053631450747332389)
        ·
          refine ⟨361639322555897015124823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1928743053631450747332389 361639322555897015124823)
          ·
            refine ⟨542458983833845522687235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 361639322555897015124823 542458983833845522687235)
            ·
              refine ⟨813688475750768284030853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 542458983833845522687235 813688475750768284030853)
              ·
                refine ⟨152566589203269053255785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 813688475750768284030853 152566589203269053255785)
                ·
                  rfl

theorem cell19_501394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 1, 4].length) (baseStart_501394 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_501394 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_501394 prefixEnd_501394 := by exact prefixLift 501394
  have htrace : WordTrace (prefixWord ++ tailWord_501394) baseStart_501394 baseEnd_501394 := by
    simpa [prefixWord, tailWord_501394, baseEnd_501394] using wordTrace_append hprefix tailTrace_501394
  have hstable : (prefixWord ++ tailWord_501394).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501394).length < 2 ^ (prefixWord ++ tailWord_501394).sum := by decide
  have hdescent : baseEnd_501394 < baseStart_501394 := by decide
  rcases family_descends (prefixWord ++ tailWord_501394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501468 : List Nat := [2, 2, 5, 1, 3, 1, 2, 3]
def baseStart_501468 : Nat := 118140960795 + 501468 * 2 ^ 59
def prefixEnd_501468 : Nat := 4983230072969 + 3 ^ 40 * 501468 * 2
def baseEnd_501468 : Nat := 152589106280858807611139

theorem tailTrace_501468 : CollatzResearch.WordTrace tailWord_501468 prefixEnd_501468 152589106280858807611139 := by
  unfold tailWord_501468
  simp only [CollatzResearch.WordTrace]
  refine ⟨9145020273637277380524529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12193360364849703174032705 9145020273637277380524529)
  ·
    refine ⟨6858765205227958035393397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9145020273637277380524529 6858765205227958035393397)
    ·
      refine ⟨643009237990121065818131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6858765205227958035393397 643009237990121065818131)
      ·
        refine ⟨964513856985181598727197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 643009237990121065818131 964513856985181598727197)
        ·
          refine ⟨361692696369443099522699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 964513856985181598727197 361692696369443099522699)
          ·
            refine ⟨542539044554164649284049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 361692696369443099522699 542539044554164649284049)
            ·
              refine ⟨406904283415623486963037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 542539044554164649284049 406904283415623486963037)
              ·
                refine ⟨152589106280858807611139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 406904283415623486963037 152589106280858807611139)
                ·
                  rfl

theorem cell19_501468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 2, 3].length) (baseStart_501468 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_501468 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_501468 prefixEnd_501468 := by exact prefixLift 501468
  have htrace : WordTrace (prefixWord ++ tailWord_501468) baseStart_501468 baseEnd_501468 := by
    simpa [prefixWord, tailWord_501468, baseEnd_501468] using wordTrace_append hprefix tailTrace_501468
  have hstable : (prefixWord ++ tailWord_501468).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501468).length < 2 ^ (prefixWord ++ tailWord_501468).sum := by decide
  have hdescent : baseEnd_501468 < baseStart_501468 := by decide
  rcases family_descends (prefixWord ++ tailWord_501468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501476 : List Nat := [2, 3, 1, 1, 1, 3, 3, 5]
def baseStart_501476 : Nat := 118140960795 + 501476 * 2 ^ 59
def prefixEnd_501476 : Nat := 4983230072969 + 3 ^ 40 * 501476 * 2
def baseEnd_501476 : Nat := 152591540559517159433339

theorem tailTrace_501476 : CollatzResearch.WordTrace tailWord_501476 prefixEnd_501476 152591540559517159433339 := by
  unfold tailWord_501476
  simp only [CollatzResearch.WordTrace]
  refine ⟨9145166165622786063670141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12193554887497048084893521 9145166165622786063670141)
  ·
    refine ⟨3429437312108544773876303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9145166165622786063670141 3429437312108544773876303)
    ·
      refine ⟨5144155968162817160814455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3429437312108544773876303 5144155968162817160814455)
      ·
        refine ⟨7716233952244225741221683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5144155968162817160814455 7716233952244225741221683)
        ·
          refine ⟨11574350928366338611832525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7716233952244225741221683 11574350928366338611832525)
          ·
            refine ⟨4340381598137376979437197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11574350928366338611832525 4340381598137376979437197)
            ·
              refine ⟨1627643099301516367288949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4340381598137376979437197 1627643099301516367288949)
              ·
                refine ⟨152591540559517159433339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1627643099301516367288949 152591540559517159433339)
                ·
                  rfl

theorem cell19_501476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 5].length) (baseStart_501476 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_501476 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_501476 prefixEnd_501476 := by exact prefixLift 501476
  have htrace : WordTrace (prefixWord ++ tailWord_501476) baseStart_501476 baseEnd_501476 := by
    simpa [prefixWord, tailWord_501476, baseEnd_501476] using wordTrace_append hprefix tailTrace_501476
  have hstable : (prefixWord ++ tailWord_501476).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501476).length < 2 ^ (prefixWord ++ tailWord_501476).sum := by decide
  have hdescent : baseEnd_501476 < baseStart_501476 := by decide
  rcases family_descends (prefixWord ++ tailWord_501476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501514 : List Nat := [3, 1, 2, 2, 1, 3, 1, 6]
def baseStart_501514 : Nat := 118140960795 + 501514 * 2 ^ 59
def prefixEnd_501514 : Nat := 4983230072969 + 3 ^ 40 * 501514 * 2
def baseEnd_501514 : Nat := 152603103383144330588791

theorem tailTrace_501514 : CollatzResearch.WordTrace tailWord_501514 prefixEnd_501514 152603103383144330588791 := by
  unfold tailWord_501514
  simp only [CollatzResearch.WordTrace]
  refine ⟨4572929576276976154305899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12194478870071936411482397 4572929576276976154305899)
  ·
    refine ⟨6859394364415464231458849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4572929576276976154305899 6859394364415464231458849)
    ·
      refine ⟨5144545773311598173594137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6859394364415464231458849 5144545773311598173594137)
      ·
        refine ⟨3858409329983698630195603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5144545773311598173594137 3858409329983698630195603)
        ·
          refine ⟨5787613994975547945293405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3858409329983698630195603 5787613994975547945293405)
          ·
            refine ⟨2170355248115830479485027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5787613994975547945293405 2170355248115830479485027)
            ·
              refine ⟨3255532872173745719227541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2170355248115830479485027 3255532872173745719227541)
              ·
                refine ⟨152603103383144330588791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3255532872173745719227541 152603103383144330588791)
                ·
                  rfl

theorem cell19_501514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 6].length) (baseStart_501514 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_501514 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_501514 prefixEnd_501514 := by exact prefixLift 501514
  have htrace : WordTrace (prefixWord ++ tailWord_501514) baseStart_501514 baseEnd_501514 := by
    simpa [prefixWord, tailWord_501514, baseEnd_501514] using wordTrace_append hprefix tailTrace_501514
  have hstable : (prefixWord ++ tailWord_501514).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501514).length < 2 ^ (prefixWord ++ tailWord_501514).sum := by decide
  have hdescent : baseEnd_501514 < baseStart_501514 := by decide
  rcases family_descends (prefixWord ++ tailWord_501514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501550 : List Nat := [4, 1, 3, 2, 2, 7]
def baseStart_501550 : Nat := 118140960795 + 501550 * 2 ^ 59
def prefixEnd_501550 : Nat := 4983230072969 + 3 ^ 40 * 501550 * 2
def baseEnd_501550 : Nat := 16957117515234101532077

theorem tailTrace_501550 : CollatzResearch.WordTrace tailWord_501550 prefixEnd_501550 16957117515234101532077 := by
  unfold tailWord_501550
  simp only [CollatzResearch.WordTrace]
  refine ⟨2286628916622185345691763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12195354221984988510356069 2286628916622185345691763)
  ·
    refine ⟨3429943374933278018537645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2286628916622185345691763 3429943374933278018537645)
    ·
      refine ⟨1286228765599979256951617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3429943374933278018537645 1286228765599979256951617)
      ·
        refine ⟨964671574199984442713713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1286228765599979256951617 964671574199984442713713)
        ·
          refine ⟨723503680649988332035285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 964671574199984442713713 723503680649988332035285)
          ·
            refine ⟨16957117515234101532077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 723503680649988332035285 16957117515234101532077)
            ·
              rfl

theorem cell19_501550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 7].length) (baseStart_501550 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_501550 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_501550 prefixEnd_501550 := by exact prefixLift 501550
  have htrace : WordTrace (prefixWord ++ tailWord_501550) baseStart_501550 baseEnd_501550 := by
    simpa [prefixWord, tailWord_501550, baseEnd_501550] using wordTrace_append hprefix tailTrace_501550
  have hstable : (prefixWord ++ tailWord_501550).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501550).length < 2 ^ (prefixWord ++ tailWord_501550).sum := by decide
  have hdescent : baseEnd_501550 < baseStart_501550 := by decide
  rcases family_descends (prefixWord ++ tailWord_501550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501567 : List Nat := [1, 1, 2, 2, 7, 1, 1, 4]
def baseStart_501567 : Nat := 118140960795 + 501567 * 2 ^ 59
def prefixEnd_501567 : Nat := 4983230072969 + 3 ^ 40 * 501567 * 2
def baseEnd_501567 : Nat := 152619230479255911410869

theorem tailTrace_501567 : CollatzResearch.WordTrace tailWord_501567 prefixEnd_501567 152619230479255911410869 := by
  unfold tailWord_501567
  simp only [CollatzResearch.WordTrace]
  refine ⟨18293651373915894668902955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12195767582610596445935303 18293651373915894668902955)
  ·
    refine ⟨27440477060873842003354433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18293651373915894668902955 27440477060873842003354433)
    ·
      refine ⟨20580357795655381502515825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27440477060873842003354433 20580357795655381502515825)
      ·
        refine ⟨15435268346741536126886869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20580357795655381502515825 15435268346741536126886869)
        ·
          refine ⟨361764101876754752973911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 15435268346741536126886869 361764101876754752973911)
          ·
            refine ⟨542646152815132129460867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 361764101876754752973911 542646152815132129460867)
            ·
              refine ⟨813969229222698194191301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 542646152815132129460867 813969229222698194191301)
              ·
                refine ⟨152619230479255911410869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 813969229222698194191301 152619230479255911410869)
                ·
                  rfl

theorem cell19_501567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 1, 4].length) (baseStart_501567 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_501567 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_501567 prefixEnd_501567 := by exact prefixLift 501567
  have htrace : WordTrace (prefixWord ++ tailWord_501567) baseStart_501567 baseEnd_501567 := by
    simpa [prefixWord, tailWord_501567, baseEnd_501567] using wordTrace_append hprefix tailTrace_501567
  have hstable : (prefixWord ++ tailWord_501567).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501567).length < 2 ^ (prefixWord ++ tailWord_501567).sum := by decide
  have hdescent : baseEnd_501567 < baseStart_501567 := by decide
  rcases family_descends (prefixWord ++ tailWord_501567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501571 : List Nat := [1, 1, 1, 3, 1, 5, 3, 4]
def baseStart_501571 : Nat := 118140960795 + 501571 * 2 ^ 59
def prefixEnd_501571 : Nat := 4983230072969 + 3 ^ 40 * 501571 * 2
def baseEnd_501571 : Nat := 152620447618585087321969

theorem tailTrace_501571 : CollatzResearch.WordTrace tailWord_501571 prefixEnd_501571 152620447618585087321969 := by
  unfold tailWord_501571
  simp only [CollatzResearch.WordTrace]
  refine ⟨18293797265901403352048567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12195864843934268901365711 18293797265901403352048567)
  ·
    refine ⟨27440695898852105028072851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18293797265901403352048567 27440695898852105028072851)
    ·
      refine ⟨41161043848278157542109277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27440695898852105028072851 41161043848278157542109277)
      ·
        refine ⟨15435391443104309078290979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41161043848278157542109277 15435391443104309078290979)
        ·
          refine ⟨23153087164656463617436469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15435391443104309078290979 23153087164656463617436469)
          ·
            refine ⟨2170601921686543464134669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23153087164656463617436469 2170601921686543464134669)
            ·
              refine ⟨813975720632453799050501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2170601921686543464134669 813975720632453799050501)
              ·
                refine ⟨152620447618585087321969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 813975720632453799050501 152620447618585087321969)
                ·
                  rfl

theorem cell19_501571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3, 4].length) (baseStart_501571 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_501571 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_501571 prefixEnd_501571 := by exact prefixLift 501571
  have htrace : WordTrace (prefixWord ++ tailWord_501571) baseStart_501571 baseEnd_501571 := by
    simpa [prefixWord, tailWord_501571, baseEnd_501571] using wordTrace_append hprefix tailTrace_501571
  have hstable : (prefixWord ++ tailWord_501571).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501571).length < 2 ^ (prefixWord ++ tailWord_501571).sum := by decide
  have hdescent : baseEnd_501571 < baseStart_501571 := by decide
  rcases family_descends (prefixWord ++ tailWord_501571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501685 : List Nat := [1, 3, 3, 2, 1, 2, 1, 6]
def baseStart_501685 : Nat := 118140960795 + 501685 * 2 ^ 59
def prefixEnd_501685 : Nat := 4983230072969 + 3 ^ 40 * 501685 * 2
def baseEnd_501685 : Nat := 152655136089466600788325

theorem tailTrace_501685 : CollatzResearch.WordTrace tailWord_501685 prefixEnd_501685 152655136089466600788325 := by
  unfold tailWord_501685
  simp only [CollatzResearch.WordTrace]
  refine ⟨18297955187488400821698509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12198636791658933881132339 18297955187488400821698509)
  ·
    refine ⟨6861733195308150308136941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18297955187488400821698509 6861733195308150308136941)
    ·
      refine ⟨2573149948240556365551353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6861733195308150308136941 2573149948240556365551353)
      ·
        refine ⟨1929862461180417274163515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2573149948240556365551353 1929862461180417274163515)
        ·
          refine ⟨2894793691770625911245273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1929862461180417274163515 2894793691770625911245273)
          ·
            refine ⟨2171095268827969433433955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2894793691770625911245273 2171095268827969433433955)
            ·
              refine ⟨3256642903241954150150933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2171095268827969433433955 3256642903241954150150933)
              ·
                refine ⟨152655136089466600788325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3256642903241954150150933 152655136089466600788325)
                ·
                  rfl

theorem cell19_501685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 6].length) (baseStart_501685 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_501685 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_501685 prefixEnd_501685 := by exact prefixLift 501685
  have htrace : WordTrace (prefixWord ++ tailWord_501685) baseStart_501685 baseEnd_501685 := by
    simpa [prefixWord, tailWord_501685, baseEnd_501685] using wordTrace_append hprefix tailTrace_501685
  have hstable : (prefixWord ++ tailWord_501685).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501685).length < 2 ^ (prefixWord ++ tailWord_501685).sum := by decide
  have hdescent : baseEnd_501685 < baseStart_501685 := by decide
  rcases family_descends (prefixWord ++ tailWord_501685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501704 : List Nat := [2, 1, 3, 1, 4, 1, 2, 5]
def baseStart_501704 : Nat := 118140960795 + 501704 * 2 ^ 59
def prefixEnd_501704 : Nat := 4983230072969 + 3 ^ 40 * 501704 * 2
def baseEnd_501704 : Nat := 152660917501280186366051

theorem tailTrace_501704 : CollatzResearch.WordTrace tailWord_501704 prefixEnd_501704 152660917501280186366051 := by
  unfold tailWord_501704
  simp only [CollatzResearch.WordTrace]
  refine ⟨9149324087209783533320083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12199098782946378044426777 9149324087209783533320083)
  ·
    refine ⟨13723986130814675299980125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9149324087209783533320083 13723986130814675299980125)
    ·
      refine ⟨5146494799055503237492547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13723986130814675299980125 5146494799055503237492547)
      ·
        refine ⟨7719742198583254856238821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5146494799055503237492547 7719742198583254856238821)
        ·
          refine ⟨1447451662234360285544779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7719742198583254856238821 1447451662234360285544779)
          ·
            refine ⟨2171177493351540428317169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1447451662234360285544779 2171177493351540428317169)
            ·
              refine ⟨1628383120013655321237877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2171177493351540428317169 1628383120013655321237877)
              ·
                refine ⟨152660917501280186366051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1628383120013655321237877 152660917501280186366051)
                ·
                  rfl

theorem cell19_501704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 5].length) (baseStart_501704 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_501704 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_501704 prefixEnd_501704 := by exact prefixLift 501704
  have htrace : WordTrace (prefixWord ++ tailWord_501704) baseStart_501704 baseEnd_501704 := by
    simpa [prefixWord, tailWord_501704, baseEnd_501704] using wordTrace_append hprefix tailTrace_501704
  have hstable : (prefixWord ++ tailWord_501704).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501704).length < 2 ^ (prefixWord ++ tailWord_501704).sum := by decide
  have hdescent : baseEnd_501704 < baseStart_501704 := by decide
  rcases family_descends (prefixWord ++ tailWord_501704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501763 : List Nat := [1, 1, 1, 3, 2, 1, 1, 9]
def baseStart_501763 : Nat := 118140960795 + 501763 * 2 ^ 59
def prefixEnd_501763 : Nat := 4983230072969 + 3 ^ 40 * 501763 * 2
def baseEnd_501763 : Nat := 152678870306385531054779

theorem tailTrace_501763 : CollatzResearch.WordTrace tailWord_501763 prefixEnd_501763 152678870306385531054779 := by
  unfold tailWord_501763
  simp only [CollatzResearch.WordTrace]
  refine ⟨18300800081205820143037943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12200533387470546762025295 18300800081205820143037943)
  ·
    refine ⟨27451200121808730214556915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18300800081205820143037943 27451200121808730214556915)
    ·
      refine ⟨41176800182713095321835373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27451200121808730214556915 41176800182713095321835373)
      ·
        refine ⟨15441300068517410745688265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41176800182713095321835373 15441300068517410745688265)
        ·
          refine ⟨11580975051388058059266199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15441300068517410745688265 11580975051388058059266199)
          ·
            refine ⟨17371462577082087088899299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11580975051388058059266199 17371462577082087088899299)
            ·
              refine ⟨26057193865623130633348949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17371462577082087088899299 26057193865623130633348949)
              ·
                refine ⟨152678870306385531054779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26057193865623130633348949 152678870306385531054779)
                ·
                  rfl

theorem cell19_501763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 9].length) (baseStart_501763 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_501763 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_501763 prefixEnd_501763 := by exact prefixLift 501763
  have htrace : WordTrace (prefixWord ++ tailWord_501763) baseStart_501763 baseEnd_501763 := by
    simpa [prefixWord, tailWord_501763, baseEnd_501763] using wordTrace_append hprefix tailTrace_501763
  have hstable : (prefixWord ++ tailWord_501763).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501763).length < 2 ^ (prefixWord ++ tailWord_501763).sum := by decide
  have hdescent : baseEnd_501763 < baseStart_501763 := by decide
  rcases family_descends (prefixWord ++ tailWord_501763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501812 : List Nat := [2, 5, 1, 2, 2, 2, 2, 3]
def baseStart_501812 : Nat := 118140960795 + 501812 * 2 ^ 59
def prefixEnd_501812 : Nat := 4983230072969 + 3 ^ 40 * 501812 * 2
def baseEnd_501812 : Nat := 152693780263167935965757

theorem tailTrace_501812 : CollatzResearch.WordTrace tailWord_501812 prefixEnd_501812 152693780263167935965757 := by
  unfold tailWord_501812
  simp only [CollatzResearch.WordTrace]
  refine ⟨9151293629014150755785845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12201724838685534341047793 9151293629014150755785845)
  ·
    refine ⟨857933777720076633354923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9151293629014150755785845 857933777720076633354923)
    ·
      refine ⟨1286900666580114950032385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 857933777720076633354923 1286900666580114950032385)
      ·
        refine ⟨965175499935086212524289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1286900666580114950032385 965175499935086212524289)
        ·
          refine ⟨723881624951314659393217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 965175499935086212524289 723881624951314659393217)
          ·
            refine ⟨542911218713485994544913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 723881624951314659393217 542911218713485994544913)
            ·
              refine ⟨407183414035114495908685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 542911218713485994544913 407183414035114495908685)
              ·
                refine ⟨152693780263167935965757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 407183414035114495908685 152693780263167935965757)
                ·
                  rfl

theorem cell19_501812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 2, 3].length) (baseStart_501812 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_501812 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_501812 prefixEnd_501812 := by exact prefixLift 501812
  have htrace : WordTrace (prefixWord ++ tailWord_501812) baseStart_501812 baseEnd_501812 := by
    simpa [prefixWord, tailWord_501812, baseEnd_501812] using wordTrace_append hprefix tailTrace_501812
  have hstable : (prefixWord ++ tailWord_501812).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501812).length < 2 ^ (prefixWord ++ tailWord_501812).sum := by decide
  have hdescent : baseEnd_501812 < baseStart_501812 := by decide
  rcases family_descends (prefixWord ++ tailWord_501812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501856 : List Nat := [2, 1, 1, 3, 2, 4, 2, 4]
def baseStart_501856 : Nat := 118140960795 + 501856 * 2 ^ 59
def prefixEnd_501856 : Nat := 4983230072969 + 3 ^ 40 * 501856 * 2
def baseEnd_501856 : Nat := 152707168795788870987859

theorem tailTrace_501856 : CollatzResearch.WordTrace tailWord_501856 prefixEnd_501856 152707168795788870987859 := by
  unfold tailWord_501856
  simp only [CollatzResearch.WordTrace]
  refine ⟨9152096034934448513086711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12202794713245931350782281 9152096034934448513086711)
  ·
    refine ⟨13728144052401672769630067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9152096034934448513086711 13728144052401672769630067)
    ·
      refine ⟨20592216078602509154445101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13728144052401672769630067 20592216078602509154445101)
      ·
        refine ⟨7722081029475940932916913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20592216078602509154445101 7722081029475940932916913)
        ·
          refine ⟨5791560772106955699687685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7722081029475940932916913 5791560772106955699687685)
          ·
            refine ⟨1085917644770054193691441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5791560772106955699687685 1085917644770054193691441)
            ·
              refine ⟨814438233577540645268581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1085917644770054193691441 814438233577540645268581)
              ·
                refine ⟨152707168795788870987859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 814438233577540645268581 152707168795788870987859)
                ·
                  rfl

theorem cell19_501856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2, 4].length) (baseStart_501856 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_501856 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_501856 prefixEnd_501856 := by exact prefixLift 501856
  have htrace : WordTrace (prefixWord ++ tailWord_501856) baseStart_501856 baseEnd_501856 := by
    simpa [prefixWord, tailWord_501856, baseEnd_501856] using wordTrace_append hprefix tailTrace_501856
  have hstable : (prefixWord ++ tailWord_501856).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501856).length < 2 ^ (prefixWord ++ tailWord_501856).sum := by decide
  have hdescent : baseEnd_501856 < baseStart_501856 := by decide
  rcases family_descends (prefixWord ++ tailWord_501856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501911 : List Nat := [1, 1, 3, 3, 4, 2, 1, 4]
def baseStart_501911 : Nat := 118140960795 + 501911 * 2 ^ 59
def prefixEnd_501911 : Nat := 4983230072969 + 3 ^ 40 * 501911 * 2
def baseEnd_501911 : Nat := 152723904461565039765487

theorem tailTrace_501911 : CollatzResearch.WordTrace tailWord_501911 prefixEnd_501911 152723904461565039765487 := by
  unfold tailWord_501911
  simp only [CollatzResearch.WordTrace]
  refine ⟨18306198084669641419425587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12204132056446427612950391 18306198084669641419425587)
  ·
    refine ⟨27459297127004462129138381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18306198084669641419425587 27459297127004462129138381)
    ·
      refine ⟨10297236422626673298426893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27459297127004462129138381 10297236422626673298426893)
      ·
        refine ⟨3861463658485002486910085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10297236422626673298426893 3861463658485002486910085)
        ·
          refine ⟨724024435965937966295641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3861463658485002486910085 724024435965937966295641)
          ·
            refine ⟨543018326974453474721731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 724024435965937966295641 543018326974453474721731)
            ·
              refine ⟨814527490461680212082597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 543018326974453474721731 814527490461680212082597)
              ·
                refine ⟨152723904461565039765487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 814527490461680212082597 152723904461565039765487)
                ·
                  rfl

theorem cell19_501911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 1, 4].length) (baseStart_501911 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_501911 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_501911 prefixEnd_501911 := by exact prefixLift 501911
  have htrace : WordTrace (prefixWord ++ tailWord_501911) baseStart_501911 baseEnd_501911 := by
    simpa [prefixWord, tailWord_501911, baseEnd_501911] using wordTrace_append hprefix tailTrace_501911
  have hstable : (prefixWord ++ tailWord_501911).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501911).length < 2 ^ (prefixWord ++ tailWord_501911).sum := by decide
  have hdescent : baseEnd_501911 < baseStart_501911 := by decide
  rcases family_descends (prefixWord ++ tailWord_501911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501987 : List Nat := [1, 1, 1, 8, 1, 1, 1, 5]
def baseStart_501987 : Nat := 118140960795 + 501987 * 2 ^ 59
def prefixEnd_501987 : Nat := 4983230072969 + 3 ^ 40 * 501987 * 2
def baseEnd_501987 : Nat := 152747030108819382076391

theorem tailTrace_501987 : CollatzResearch.WordTrace tailWord_501987 prefixEnd_501987 152747030108819382076391 := by
  unfold tailWord_501987
  simp only [CollatzResearch.WordTrace]
  refine ⟨18308970032394306399192215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12205980021596204266128143 18308970032394306399192215)
  ·
    refine ⟨27463455048591459598788323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18308970032394306399192215 27463455048591459598788323)
    ·
      refine ⟨41195182572887189398182485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27463455048591459598788323 41195182572887189398182485)
      ·
        refine ⟨482756045776021750759951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 41195182572887189398182485 482756045776021750759951)
        ·
          refine ⟨724134068664032626139927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 482756045776021750759951 724134068664032626139927)
          ·
            refine ⟨1086201102996048939209891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 724134068664032626139927 1086201102996048939209891)
            ·
              refine ⟨1629301654494073408814837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1086201102996048939209891 1629301654494073408814837)
              ·
                refine ⟨152747030108819382076391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1629301654494073408814837 152747030108819382076391)
                ·
                  rfl

theorem cell19_501987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 5].length) (baseStart_501987 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_501987 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_501987 prefixEnd_501987 := by exact prefixLift 501987
  have htrace : WordTrace (prefixWord ++ tailWord_501987) baseStart_501987 baseEnd_501987 := by
    simpa [prefixWord, tailWord_501987, baseEnd_501987] using wordTrace_append hprefix tailTrace_501987
  have hstable : (prefixWord ++ tailWord_501987).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501987).length < 2 ^ (prefixWord ++ tailWord_501987).sum := by decide
  have hdescent : baseEnd_501987 < baseStart_501987 := by decide
  rcases family_descends (prefixWord ++ tailWord_501987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501989 : List Nat := [1, 3, 1, 4, 2, 2, 1, 5]
def baseStart_501989 : Nat := 118140960795 + 501989 * 2 ^ 59
def prefixEnd_501989 : Nat := 4983230072969 + 3 ^ 40 * 501989 * 2
def baseEnd_501989 : Nat := 152747638678483970031941

theorem tailTrace_501989 : CollatzResearch.WordTrace tailWord_501989 prefixEnd_501989 152747638678483970031941 := by
  unfold tailWord_501989
  simp only [CollatzResearch.WordTrace]
  refine ⟨18309042978387060740765021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12206028652258040493843347 18309042978387060740765021)
  ·
    refine ⟨6865891116895147777786883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18309042978387060740765021 6865891116895147777786883)
    ·
      refine ⟨10298836675342721666680325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6865891116895147777786883 10298836675342721666680325)
      ·
        refine ⟨1931031876626760312502561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10298836675342721666680325 1931031876626760312502561)
        ·
          refine ⟨1448273907470070234376921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1931031876626760312502561 1448273907470070234376921)
          ·
            refine ⟨1086205430602552675782691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1448273907470070234376921 1086205430602552675782691)
            ·
              refine ⟨1629308145903829013674037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1086205430602552675782691 1629308145903829013674037)
              ·
                refine ⟨152747638678483970031941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1629308145903829013674037 152747638678483970031941)
                ·
                  rfl

theorem cell19_501989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 5].length) (baseStart_501989 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_501989 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_501989 prefixEnd_501989 := by exact prefixLift 501989
  have htrace : WordTrace (prefixWord ++ tailWord_501989) baseStart_501989 baseEnd_501989 := by
    simpa [prefixWord, tailWord_501989, baseEnd_501989] using wordTrace_append hprefix tailTrace_501989
  have hstable : (prefixWord ++ tailWord_501989).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501989).length < 2 ^ (prefixWord ++ tailWord_501989).sum := by decide
  have hdescent : baseEnd_501989 < baseStart_501989 := by decide
  rcases family_descends (prefixWord ++ tailWord_501989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502010 : List Nat := [3, 1, 1, 1, 1, 5, 7]
def baseStart_502010 : Nat := 118140960795 + 502010 * 2 ^ 59
def prefixEnd_502010 : Nat := 4983230072969 + 3 ^ 40 * 502010 * 2
def baseEnd_502010 : Nat := 50918009553320714521739

theorem tailTrace_502010 : CollatzResearch.WordTrace tailWord_502010 prefixEnd_502010 50918009553320714521739 := by
  unfold tailWord_502010
  simp only [CollatzResearch.WordTrace]
  refine ⟨4577452227827745331819871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12206539274207320884852989 4577452227827745331819871)
  ·
    refine ⟨6866178341741617997729807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4577452227827745331819871 6866178341741617997729807)
    ·
      refine ⟨10299267512612426996594711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6866178341741617997729807 10299267512612426996594711)
      ·
        refine ⟨15448901268918640494892067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10299267512612426996594711 15448901268918640494892067)
        ·
          refine ⟨23173351903377960742338101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15448901268918640494892067 23173351903377960742338101)
          ·
            refine ⟨2172501740941683819594197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23173351903377960742338101 2172501740941683819594197)
            ·
              refine ⟨50918009553320714521739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2172501740941683819594197 50918009553320714521739)
              ·
                rfl

theorem cell19_502010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 7].length) (baseStart_502010 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_502010 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_502010 prefixEnd_502010 := by exact prefixLift 502010
  have htrace : WordTrace (prefixWord ++ tailWord_502010) baseStart_502010 baseEnd_502010 := by
    simpa [prefixWord, tailWord_502010, baseEnd_502010] using wordTrace_append hprefix tailTrace_502010
  have hstable : (prefixWord ++ tailWord_502010).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502010).length < 2 ^ (prefixWord ++ tailWord_502010).sum := by decide
  have hdescent : baseEnd_502010 < baseStart_502010 := by decide
  rcases family_descends (prefixWord ++ tailWord_502010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502065 : List Nat := [1, 2, 2, 3, 5, 6]
def baseStart_502065 : Nat := 118140960795 + 502065 * 2 ^ 59
def prefixEnd_502065 : Nat := 4983230072969 + 3 ^ 40 * 502065 * 2
def baseEnd_502065 : Nat := 16974529369526479149205

theorem tailTrace_502065 : CollatzResearch.WordTrace tailWord_502065 prefixEnd_502065 16974529369526479149205 := by
  unfold tailWord_502065
  simp only [CollatzResearch.WordTrace]
  refine ⟨18311814926111725720531649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12207876617407817147021099 18311814926111725720531649)
  ·
    refine ⟨13733861194583794290398737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18311814926111725720531649 13733861194583794290398737)
    ·
      refine ⟨10300395895937845717799053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13733861194583794290398737 10300395895937845717799053)
      ·
        refine ⟨3862648460976692144174645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10300395895937845717799053 3862648460976692144174645)
        ·
          refine ⟨362123293216564888516373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3862648460976692144174645 362123293216564888516373)
          ·
            refine ⟨16974529369526479149205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 362123293216564888516373 16974529369526479149205)
            ·
              rfl

theorem cell19_502065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 6].length) (baseStart_502065 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_502065 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_502065 prefixEnd_502065 := by exact prefixLift 502065
  have htrace : WordTrace (prefixWord ++ tailWord_502065) baseStart_502065 baseEnd_502065 := by
    simpa [prefixWord, tailWord_502065, baseEnd_502065] using wordTrace_append hprefix tailTrace_502065
  have hstable : (prefixWord ++ tailWord_502065).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502065).length < 2 ^ (prefixWord ++ tailWord_502065).sum := by decide
  have hdescent : baseEnd_502065 < baseStart_502065 := by decide
  rcases family_descends (prefixWord ++ tailWord_502065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502101 : List Nat := [1, 3, 2, 2, 4, 1, 3, 3]
def baseStart_502101 : Nat := 118140960795 + 502101 * 2 ^ 59
def prefixEnd_502101 : Nat := 4983230072969 + 3 ^ 40 * 502101 * 2
def baseEnd_502101 : Nat := 152781718579700895542747

theorem tailTrace_502101 : CollatzResearch.WordTrace tailWord_502101 prefixEnd_502101 152781718579700895542747 := by
  unfold tailWord_502101
  simp only [CollatzResearch.WordTrace]
  refine ⟨18313127953981303868842157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12208751969320869245894771 18313127953981303868842157)
  ·
    refine ⟨6867422982742988950815809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18313127953981303868842157 6867422982742988950815809)
    ·
      refine ⟨5150567237057241713111857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6867422982742988950815809 5150567237057241713111857)
      ·
        refine ⟨3862925427792931284833893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5150567237057241713111857 3862925427792931284833893)
        ·
          refine ⟨724298517711174615906355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3862925427792931284833893 724298517711174615906355)
          ·
            refine ⟨1086447776566761923859533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 724298517711174615906355 1086447776566761923859533)
            ·
              refine ⟨407417916212535721447325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1086447776566761923859533 407417916212535721447325)
              ·
                refine ⟨152781718579700895542747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 407417916212535721447325 152781718579700895542747)
                ·
                  rfl

theorem cell19_502101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 3, 3].length) (baseStart_502101 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_502101 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_502101 prefixEnd_502101 := by exact prefixLift 502101
  have htrace : WordTrace (prefixWord ++ tailWord_502101) baseStart_502101 baseEnd_502101 := by
    simpa [prefixWord, tailWord_502101, baseEnd_502101] using wordTrace_append hprefix tailTrace_502101
  have hstable : (prefixWord ++ tailWord_502101).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502101).length < 2 ^ (prefixWord ++ tailWord_502101).sum := by decide
  have hdescent : baseEnd_502101 < baseStart_502101 := by decide
  rcases family_descends (prefixWord ++ tailWord_502101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502103 : List Nat := [1, 1, 3, 2, 3, 1, 5, 3]
def baseStart_502103 : Nat := 118140960795 + 502103 * 2 ^ 59
def prefixEnd_502103 : Nat := 4983230072969 + 3 ^ 40 * 502103 * 2
def baseEnd_502103 : Nat := 152782327149365483498297

theorem tailTrace_502103 : CollatzResearch.WordTrace tailWord_502103 prefixEnd_502103 152782327149365483498297 := by
  unfold tailWord_502103
  simp only [CollatzResearch.WordTrace]
  refine ⟨18313200899974058210414963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12208800599982705473609975 18313200899974058210414963)
  ·
    refine ⟨27469801349961087315622445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18313200899974058210414963 27469801349961087315622445)
    ·
      refine ⟨10301175506235407743358417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27469801349961087315622445 10301175506235407743358417)
      ·
        refine ⟨7725881629676555807518813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10301175506235407743358417 7725881629676555807518813)
        ·
          refine ⟨2897205611128708427819555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7725881629676555807518813 2897205611128708427819555)
          ·
            refine ⟨4345808416693062641729333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2897205611128708427819555 4345808416693062641729333)
            ·
              refine ⟨407419539064974622662125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4345808416693062641729333 407419539064974622662125)
              ·
                refine ⟨152782327149365483498297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 407419539064974622662125 152782327149365483498297)
                ·
                  rfl

theorem cell19_502103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 5, 3].length) (baseStart_502103 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_502103 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_502103 prefixEnd_502103 := by exact prefixLift 502103
  have htrace : WordTrace (prefixWord ++ tailWord_502103) baseStart_502103 baseEnd_502103 := by
    simpa [prefixWord, tailWord_502103, baseEnd_502103] using wordTrace_append hprefix tailTrace_502103
  have hstable : (prefixWord ++ tailWord_502103).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502103).length < 2 ^ (prefixWord ++ tailWord_502103).sum := by decide
  have hdescent : baseEnd_502103 < baseStart_502103 := by decide
  rcases family_descends (prefixWord ++ tailWord_502103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502122 : List Nat := [3, 1, 3, 3, 1, 2, 6]
def baseStart_502122 : Nat := 118140960795 + 502122 * 2 ^ 59
def prefixEnd_502122 : Nat := 4983230072969 + 3 ^ 40 * 502122 * 2
def baseEnd_502122 : Nat := 50929369520393023025341

theorem tailTrace_502122 : CollatzResearch.WordTrace tailWord_502122 prefixEnd_502122 50929369520393023025341 := by
  unfold tailWord_502122
  simp only [CollatzResearch.WordTrace]
  refine ⟨4578473471726306113839155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12209262591270149636904413 4578473471726306113839155)
  ·
    refine ⟨6867710207589459170758733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4578473471726306113839155 6867710207589459170758733)
    ·
      refine ⟨2575391327846047189034525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6867710207589459170758733 2575391327846047189034525)
      ·
        refine ⟨965771747942267695887947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2575391327846047189034525 965771747942267695887947)
        ·
          refine ⟨1448657621913401543831921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 965771747942267695887947 1448657621913401543831921)
          ·
            refine ⟨1086493216435051157873941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1448657621913401543831921 1086493216435051157873941)
            ·
              refine ⟨50929369520393023025341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1086493216435051157873941 50929369520393023025341)
              ·
                rfl

theorem cell19_502122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 6].length) (baseStart_502122 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_502122 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_502122 prefixEnd_502122 := by exact prefixLift 502122
  have htrace : WordTrace (prefixWord ++ tailWord_502122) baseStart_502122 baseEnd_502122 := by
    simpa [prefixWord, tailWord_502122, baseEnd_502122] using wordTrace_append hprefix tailTrace_502122
  have hstable : (prefixWord ++ tailWord_502122).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502122).length < 2 ^ (prefixWord ++ tailWord_502122).sum := by decide
  have hdescent : baseEnd_502122 < baseStart_502122 := by decide
  rcases family_descends (prefixWord ++ tailWord_502122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502154 : List Nat := [3, 1, 2, 5, 2, 1, 2, 3]
def baseStart_502154 : Nat := 118140960795 + 502154 * 2 ^ 59
def prefixEnd_502154 : Nat := 4983230072969 + 3 ^ 40 * 502154 * 2
def baseEnd_502154 : Nat := 152797845675812476364825

theorem tailTrace_502154 : CollatzResearch.WordTrace tailWord_502154 prefixEnd_502154 152797845675812476364825 := by
  unfold tailWord_502154
  simp only [CollatzResearch.WordTrace]
  refine ⟨4578765255697323480130379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12210040681859529280347677 4578765255697323480130379)
  ·
    refine ⟨6868147883545985220195569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4578765255697323480130379 6868147883545985220195569)
    ·
      refine ⟨5151110912659488915146677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6868147883545985220195569 5151110912659488915146677)
      ·
        refine ⟨482916648061827085795001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5151110912659488915146677 482916648061827085795001)
        ·
          refine ⟨362187486046370314346251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 482916648061827085795001 362187486046370314346251)
          ·
            refine ⟨543281229069555471519377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 362187486046370314346251 543281229069555471519377)
            ·
              refine ⟨407460921802166603639533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 543281229069555471519377 407460921802166603639533)
              ·
                refine ⟨152797845675812476364825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 407460921802166603639533 152797845675812476364825)
                ·
                  rfl

theorem cell19_502154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 2, 3].length) (baseStart_502154 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_502154 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_502154 prefixEnd_502154 := by exact prefixLift 502154
  have htrace : WordTrace (prefixWord ++ tailWord_502154) baseStart_502154 baseEnd_502154 := by
    simpa [prefixWord, tailWord_502154, baseEnd_502154] using wordTrace_append hprefix tailTrace_502154
  have hstable : (prefixWord ++ tailWord_502154).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502154).length < 2 ^ (prefixWord ++ tailWord_502154).sum := by decide
  have hdescent : baseEnd_502154 < baseStart_502154 := by decide
  rcases family_descends (prefixWord ++ tailWord_502154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502158 : List Nat := [4, 1, 1, 4, 1, 1, 4, 3]
def baseStart_502158 : Nat := 118140960795 + 502158 * 2 ^ 59
def prefixEnd_502158 : Nat := 4983230072969 + 3 ^ 40 * 502158 * 2
def baseEnd_502158 : Nat := 152799062815141652275925

theorem tailTrace_502158 : CollatzResearch.WordTrace tailWord_502158 prefixEnd_502158 152799062815141652275925 := by
  unfold tailWord_502158
  simp only [CollatzResearch.WordTrace]
  refine ⟨2289400864346850325458391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12210137943183201735778085 2289400864346850325458391)
  ·
    refine ⟨3434101296520275488187587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2289400864346850325458391 3434101296520275488187587)
    ·
      refine ⟨5151151944780413232281381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3434101296520275488187587 5151151944780413232281381)
      ·
        refine ⟨965840989646327481052759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5151151944780413232281381 965840989646327481052759)
        ·
          refine ⟨1448761484469491221579139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 965840989646327481052759 1448761484469491221579139)
          ·
            refine ⟨2173142226704236832368709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1448761484469491221579139 2173142226704236832368709)
            ·
              refine ⟨407464167507044406069133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2173142226704236832368709 407464167507044406069133)
              ·
                refine ⟨152799062815141652275925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 407464167507044406069133 152799062815141652275925)
                ·
                  rfl

theorem cell19_502158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 4, 3].length) (baseStart_502158 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_502158 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_502158 prefixEnd_502158 := by exact prefixLift 502158
  have htrace : WordTrace (prefixWord ++ tailWord_502158) baseStart_502158 baseEnd_502158 := by
    simpa [prefixWord, tailWord_502158, baseEnd_502158] using wordTrace_append hprefix tailTrace_502158
  have hstable : (prefixWord ++ tailWord_502158).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502158).length < 2 ^ (prefixWord ++ tailWord_502158).sum := by decide
  have hdescent : baseEnd_502158 < baseStart_502158 := by decide
  rcases family_descends (prefixWord ++ tailWord_502158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502177 : List Nat := [1, 2, 3, 5, 1, 2, 5]
def baseStart_502177 : Nat := 118140960795 + 502177 * 2 ^ 59
def prefixEnd_502177 : Nat := 4983230072969 + 3 ^ 40 * 502177 * 2
def baseEnd_502177 : Nat := 50934948075651745951217

theorem tailTrace_502177 : CollatzResearch.WordTrace tailWord_502177 prefixEnd_502177 50934948075651745951217 := by
  unfold tailWord_502177
  simp only [CollatzResearch.WordTrace]
  refine ⟨18315899901705968848608785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12210599934470645899072523 18315899901705968848608785)
  ·
    refine ⟨13736924926279476636456589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18315899901705968848608785 13736924926279476636456589)
    ·
      refine ⟨5151346847354803738671221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13736924926279476636456589 5151346847354803738671221)
      ·
        refine ⟨482938766939512850500427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5151346847354803738671221 482938766939512850500427)
        ·
          refine ⟨724408150409269275750641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 482938766939512850500427 724408150409269275750641)
          ·
            refine ⟨543306112806951956812981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 724408150409269275750641 543306112806951956812981)
            ·
              refine ⟨50934948075651745951217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 543306112806951956812981 50934948075651745951217)
              ·
                rfl

theorem cell19_502177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 5].length) (baseStart_502177 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_502177 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_502177 prefixEnd_502177 := by exact prefixLift 502177
  have htrace : WordTrace (prefixWord ++ tailWord_502177) baseStart_502177 baseEnd_502177 := by
    simpa [prefixWord, tailWord_502177, baseEnd_502177] using wordTrace_append hprefix tailTrace_502177
  have hstable : (prefixWord ++ tailWord_502177).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502177).length < 2 ^ (prefixWord ++ tailWord_502177).sum := by decide
  have hdescent : baseEnd_502177 < baseStart_502177 := by decide
  rcases family_descends (prefixWord ++ tailWord_502177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502253 : List Nat := [1, 5, 1, 3, 1, 3, 1, 4]
def baseStart_502253 : Nat := 118140960795 + 502253 * 2 ^ 59
def prefixEnd_502253 : Nat := 4983230072969 + 3 ^ 40 * 502253 * 2
def baseEnd_502253 : Nat := 152827969874209580164555

theorem tailTrace_502253 : CollatzResearch.WordTrace tailWord_502253 prefixEnd_502253 152827969874209580164555 := by
  unfold tailWord_502253
  simp only [CollatzResearch.WordTrace]
  refine ⟨18318671849430633828375413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12212447899620422552250275 18318671849430633828375413)
  ·
    refine ⟨1717375485884121921410195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18318671849430633828375413 1717375485884121921410195)
    ·
      refine ⟨2576063228826182882115293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1717375485884121921410195 2576063228826182882115293)
      ·
        refine ⟨966023710809818580793235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2576063228826182882115293 966023710809818580793235)
        ·
          refine ⟨1449035566214727871189853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 966023710809818580793235 1449035566214727871189853)
          ·
            refine ⟨543388337330522951696195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1449035566214727871189853 543388337330522951696195)
            ·
              refine ⟨815082505995784427544293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 543388337330522951696195 815082505995784427544293)
              ·
                refine ⟨152827969874209580164555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 815082505995784427544293 152827969874209580164555)
                ·
                  rfl

theorem cell19_502253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 1, 4].length) (baseStart_502253 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_502253 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_502253 prefixEnd_502253 := by exact prefixLift 502253
  have htrace : WordTrace (prefixWord ++ tailWord_502253) baseStart_502253 baseEnd_502253 := by
    simpa [prefixWord, tailWord_502253, baseEnd_502253] using wordTrace_append hprefix tailTrace_502253
  have hstable : (prefixWord ++ tailWord_502253).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502253).length < 2 ^ (prefixWord ++ tailWord_502253).sum := by decide
  have hdescent : baseEnd_502253 < baseStart_502253 := by decide
  rcases family_descends (prefixWord ++ tailWord_502253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502371 : List Nat := [1, 1, 1, 5, 1, 2, 4, 4]
def baseStart_502371 : Nat := 118140960795 + 502371 * 2 ^ 59
def prefixEnd_502371 : Nat := 4983230072969 + 3 ^ 40 * 502371 * 2
def baseEnd_502371 : Nat := 152863875484420269542011

theorem tailTrace_502371 : CollatzResearch.WordTrace tailWord_502371 prefixEnd_502371 152863875484420269542011 := by
  unfold tailWord_502371
  simp only [CollatzResearch.WordTrace]
  refine ⟨18322975663003139981170967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12215317108668759987447311 18322975663003139981170967)
  ·
    refine ⟨27484463494504709971756451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18322975663003139981170967 27484463494504709971756451)
    ·
      refine ⟨41226695241757064957634677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27484463494504709971756451 41226695241757064957634677)
      ·
        refine ⟨3865002678914724839778251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41226695241757064957634677 3865002678914724839778251)
        ·
          refine ⟨5797504018372087259667377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3865002678914724839778251 5797504018372087259667377)
          ·
            refine ⟨4348128013779065444750533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5797504018372087259667377 4348128013779065444750533)
            ·
              refine ⟨815274002583574770890725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4348128013779065444750533 815274002583574770890725)
              ·
                refine ⟨152863875484420269542011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 815274002583574770890725 152863875484420269542011)
                ·
                  rfl

theorem cell19_502371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4, 4].length) (baseStart_502371 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_502371 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_502371 prefixEnd_502371 := by exact prefixLift 502371
  have htrace : WordTrace (prefixWord ++ tailWord_502371) baseStart_502371 baseEnd_502371 := by
    simpa [prefixWord, tailWord_502371, baseEnd_502371] using wordTrace_append hprefix tailTrace_502371
  have hstable : (prefixWord ++ tailWord_502371).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502371).length < 2 ^ (prefixWord ++ tailWord_502371).sum := by decide
  have hdescent : baseEnd_502371 < baseStart_502371 := by decide
  rcases family_descends (prefixWord ++ tailWord_502371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502517 : List Nat := [1, 3, 6, 1, 1, 2, 5]
def baseStart_502517 : Nat := 118140960795 + 502517 * 2 ^ 59
def prefixEnd_502517 : Nat := 4983230072969 + 3 ^ 40 * 502517 * 2
def baseEnd_502517 : Nat := 50969433689978396765723

theorem tailTrace_502517 : CollatzResearch.WordTrace tailWord_502517 prefixEnd_502517 50969433689978396765723 := by
  unfold tailWord_502517
  simp only [CollatzResearch.WordTrace]
  refine ⟨18328300720474206915985805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12218867146982804610657203 18328300720474206915985805)
  ·
    refine ⟨6873112770177827593494677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18328300720474206915985805 6873112770177827593494677)
    ·
      refine ⟨322177161102085668445063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 6873112770177827593494677 322177161102085668445063)
      ·
        refine ⟨483265741653128502667595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322177161102085668445063 483265741653128502667595)
        ·
          refine ⟨724898612479692754001393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 483265741653128502667595 724898612479692754001393)
          ·
            refine ⟨543673959359769565501045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 724898612479692754001393 543673959359769565501045)
            ·
              refine ⟨50969433689978396765723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 543673959359769565501045 50969433689978396765723)
              ·
                rfl

theorem cell19_502517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 5].length) (baseStart_502517 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_502517 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_502517 prefixEnd_502517 := by exact prefixLift 502517
  have htrace : WordTrace (prefixWord ++ tailWord_502517) baseStart_502517 baseEnd_502517 := by
    simpa [prefixWord, tailWord_502517, baseEnd_502517] using wordTrace_append hprefix tailTrace_502517
  have hstable : (prefixWord ++ tailWord_502517).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502517).length < 2 ^ (prefixWord ++ tailWord_502517).sum := by decide
  have hdescent : baseEnd_502517 < baseStart_502517 := by decide
  rcases family_descends (prefixWord ++ tailWord_502517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502580 : List Nat := [2, 5, 1, 1, 10]
def baseStart_502580 : Nat := 118140960795 + 502580 * 2 ^ 59
def prefixEnd_502580 : Nat := 4983230072969 + 3 ^ 40 * 502580 * 2
def baseEnd_502580 : Nat := 5663980407939618922111

theorem tailTrace_502580 : CollatzResearch.WordTrace tailWord_502580 prefixEnd_502580 5663980407939618922111 := by
  unfold tailWord_502580
  simp only [CollatzResearch.WordTrace]
  refine ⟨9165299259622984337764597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12220399012830645783686129 9165299259622984337764597)
  ·
    refine ⟨859246805589654781665431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9165299259622984337764597 859246805589654781665431)
    ·
      refine ⟨1288870208384482172498147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 859246805589654781665431 1288870208384482172498147)
      ·
        refine ⟨1933305312576723258747221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1288870208384482172498147 1933305312576723258747221)
        ·
          refine ⟨5663980407939618922111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1933305312576723258747221 5663980407939618922111)
          ·
            rfl

theorem cell19_502580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 10].length) (baseStart_502580 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_502580 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_502580 prefixEnd_502580 := by exact prefixLift 502580
  have htrace : WordTrace (prefixWord ++ tailWord_502580) baseStart_502580 baseEnd_502580 := by
    simpa [prefixWord, tailWord_502580, baseEnd_502580] using wordTrace_append hprefix tailTrace_502580
  have hstable : (prefixWord ++ tailWord_502580).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502580).length < 2 ^ (prefixWord ++ tailWord_502580).sum := by decide
  have hdescent : baseEnd_502580 < baseStart_502580 := by decide
  rcases family_descends (prefixWord ++ tailWord_502580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502593 : List Nat := [1, 2, 5, 3, 2, 1, 1, 4]
def baseStart_502593 : Nat := 118140960795 + 502593 * 2 ^ 59
def prefixEnd_502593 : Nat := 4983230072969 + 3 ^ 40 * 502593 * 2
def baseEnd_502593 : Nat := 152931426717189532608073

theorem tailTrace_502593 : CollatzResearch.WordTrace tailWord_502593 prefixEnd_502593 152931426717189532608073 := by
  unfold tailWord_502593
  simp only [CollatzResearch.WordTrace]
  refine ⟨18331072668198871895752433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12220715112132581263834955 18331072668198871895752433)
  ·
    refine ⟨13748304501149153921814325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18331072668198871895752433 13748304501149153921814325)
    ·
      refine ⟨1288903546982733180170093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13748304501149153921814325 1288903546982733180170093)
      ·
        refine ⟨483338830118524942563785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1288903546982733180170093 483338830118524942563785)
        ·
          refine ⟨362504122588893706922839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 483338830118524942563785 362504122588893706922839)
          ·
            refine ⟨543756183883340560384259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 362504122588893706922839 543756183883340560384259)
            ·
              refine ⟨815634275825010840576389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 543756183883340560384259 815634275825010840576389)
              ·
                refine ⟨152931426717189532608073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 815634275825010840576389 152931426717189532608073)
                ·
                  rfl

theorem cell19_502593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 1, 4].length) (baseStart_502593 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_502593 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_502593 prefixEnd_502593 := by exact prefixLift 502593
  have htrace : WordTrace (prefixWord ++ tailWord_502593) baseStart_502593 baseEnd_502593 := by
    simpa [prefixWord, tailWord_502593, baseEnd_502593] using wordTrace_append hprefix tailTrace_502593
  have hstable : (prefixWord ++ tailWord_502593).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502593).length < 2 ^ (prefixWord ++ tailWord_502593).sum := by decide
  have hdescent : baseEnd_502593 < baseStart_502593 := by decide
  rcases family_descends (prefixWord ++ tailWord_502593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502713 : List Nat := [1, 2, 1, 4, 2, 3, 2, 4]
def baseStart_502713 : Nat := 118140960795 + 502713 * 2 ^ 59
def prefixEnd_502713 : Nat := 4983230072969 + 3 ^ 40 * 502713 * 2
def baseEnd_502713 : Nat := 152967940897064809941079

theorem tailTrace_502713 : CollatzResearch.WordTrace tailWord_502713 prefixEnd_502713 152967940897064809941079 := by
  unfold tailWord_502713
  simp only [CollatzResearch.WordTrace]
  refine ⟨18335449427764132390120793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12223632951842754926747195 18335449427764132390120793)
  ·
    refine ⟨13751587070823099292590595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18335449427764132390120793 13751587070823099292590595)
    ·
      refine ⟨20627380606234648938885893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13751587070823099292590595 20627380606234648938885893)
      ·
        refine ⟨3867633863668996676041105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20627380606234648938885893 3867633863668996676041105)
        ·
          refine ⟨2900725397751747507030829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3867633863668996676041105 2900725397751747507030829)
          ·
            refine ⟨1087772024156905315136561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2900725397751747507030829 1087772024156905315136561)
            ·
              refine ⟨815829018117678986352421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1087772024156905315136561 815829018117678986352421)
              ·
                refine ⟨152967940897064809941079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 815829018117678986352421 152967940897064809941079)
                ·
                  rfl

theorem cell19_502713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2, 4].length) (baseStart_502713 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_502713 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_502713 prefixEnd_502713 := by exact prefixLift 502713
  have htrace : WordTrace (prefixWord ++ tailWord_502713) baseStart_502713 baseEnd_502713 := by
    simpa [prefixWord, tailWord_502713, baseEnd_502713] using wordTrace_append hprefix tailTrace_502713
  have hstable : (prefixWord ++ tailWord_502713).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502713).length < 2 ^ (prefixWord ++ tailWord_502713).sum := by decide
  have hdescent : baseEnd_502713 < baseStart_502713 := by decide
  rcases family_descends (prefixWord ++ tailWord_502713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502751 : List Nat := [1, 1, 2, 3, 6, 6]
def baseStart_502751 : Nat := 118140960795 + 502751 * 2 ^ 59
def prefixEnd_502751 : Nat := 4983230072969 + 3 ^ 40 * 502751 * 2
def baseEnd_502751 : Nat := 16997722635632442344059

theorem tailTrace_502751 : CollatzResearch.WordTrace tailWord_502751 prefixEnd_502751 16997722635632442344059 := by
  unfold tailWord_502751
  simp only [CollatzResearch.WordTrace]
  refine ⟨18336835401626464880004107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12224556934417643253336071 18336835401626464880004107)
  ·
    refine ⟨27505253102439697320006161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18336835401626464880004107 27505253102439697320006161)
    ·
      refine ⟨20628939826829772990004621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27505253102439697320006161 20628939826829772990004621)
      ·
        refine ⟨7735852435061164871251733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20628939826829772990004621 7735852435061164871251733)
        ·
          refine ⟨362618082893492103339925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 7735852435061164871251733 362618082893492103339925)
          ·
            refine ⟨16997722635632442344059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 362618082893492103339925 16997722635632442344059)
            ·
              rfl

theorem cell19_502751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 6].length) (baseStart_502751 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_502751 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_502751 prefixEnd_502751 := by exact prefixLift 502751
  have htrace : WordTrace (prefixWord ++ tailWord_502751) baseStart_502751 baseEnd_502751 := by
    simpa [prefixWord, tailWord_502751, baseEnd_502751] using wordTrace_append hprefix tailTrace_502751
  have hstable : (prefixWord ++ tailWord_502751).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502751).length < 2 ^ (prefixWord ++ tailWord_502751).sum := by decide
  have hdescent : baseEnd_502751 < baseStart_502751 := by decide
  rcases family_descends (prefixWord ++ tailWord_502751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502766 : List Nat := [4, 1, 2, 1, 5, 1, 1, 4]
def baseStart_502766 : Nat := 118140960795 + 502766 * 2 ^ 59
def prefixEnd_502766 : Nat := 4983230072969 + 3 ^ 40 * 502766 * 2
def baseEnd_502766 : Nat := 152984067993176390763157

theorem tailTrace_502766 : CollatzResearch.WordTrace tailWord_502766 prefixEnd_502766 152984067993176390763157 := by
  unfold tailWord_502766
  simp only [CollatzResearch.WordTrace]
  refine ⟨2292172812071515305225019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12224921664381414961200101 2292172812071515305225019)
  ·
    refine ⟨3438259218107272957837529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2292172812071515305225019 3438259218107272957837529)
    ·
      refine ⟨2578694413580454718378147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3438259218107272957837529 2578694413580454718378147)
      ·
        refine ⟨3868041620370682077567221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2578694413580454718378147 3868041620370682077567221)
        ·
          refine ⟨362628901909751444771927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3868041620370682077567221 362628901909751444771927)
          ·
            refine ⟨543943352864627167157891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 362628901909751444771927 543943352864627167157891)
            ·
              refine ⟨815915029296940750736837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 543943352864627167157891 815915029296940750736837)
              ·
                refine ⟨152984067993176390763157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 815915029296940750736837 152984067993176390763157)
                ·
                  rfl

theorem cell19_502766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 1, 4].length) (baseStart_502766 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_502766 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_502766 prefixEnd_502766 := by exact prefixLift 502766
  have htrace : WordTrace (prefixWord ++ tailWord_502766) baseStart_502766 baseEnd_502766 := by
    simpa [prefixWord, tailWord_502766, baseEnd_502766] using wordTrace_append hprefix tailTrace_502766
  have hstable : (prefixWord ++ tailWord_502766).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502766).length < 2 ^ (prefixWord ++ tailWord_502766).sum := by decide
  have hdescent : baseEnd_502766 < baseStart_502766 := by decide
  rcases family_descends (prefixWord ++ tailWord_502766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502789 : List Nat := [1, 3, 1, 1, 2, 3, 5, 3]
def baseStart_502789 : Nat := 118140960795 + 502789 * 2 ^ 59
def prefixEnd_502789 : Nat := 4983230072969 + 3 ^ 40 * 502789 * 2
def baseEnd_502789 : Nat := 152991066544319152251983

theorem tailTrace_502789 : CollatzResearch.WordTrace tailWord_502789 prefixEnd_502789 152991066544319152251983 := by
  unfold tailWord_502789
  simp only [CollatzResearch.WordTrace]
  refine ⟨18338221375488797369887421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12225480916992531579924947 18338221375488797369887421)
  ·
    refine ⟨6876833015808299013707783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18338221375488797369887421 6876833015808299013707783)
    ·
      refine ⟨10315249523712448520561675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6876833015808299013707783 10315249523712448520561675)
      ·
        refine ⟨15472874285568672780842513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10315249523712448520561675 15472874285568672780842513)
        ·
          refine ⟨11604655714176504585631885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15472874285568672780842513 11604655714176504585631885)
          ·
            refine ⟨4351745892816189219611957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11604655714176504585631885 4351745892816189219611957)
            ·
              refine ⟨407976177451517739338621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4351745892816189219611957 407976177451517739338621)
              ·
                refine ⟨152991066544319152251983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 407976177451517739338621 152991066544319152251983)
                ·
                  rfl

theorem cell19_502789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 5, 3].length) (baseStart_502789 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_502789 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_502789 prefixEnd_502789 := by exact prefixLift 502789
  have htrace : WordTrace (prefixWord ++ tailWord_502789) baseStart_502789 baseEnd_502789 := by
    simpa [prefixWord, tailWord_502789, baseEnd_502789] using wordTrace_append hprefix tailTrace_502789
  have hstable : (prefixWord ++ tailWord_502789).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502789).length < 2 ^ (prefixWord ++ tailWord_502789).sum := by decide
  have hdescent : baseEnd_502789 < baseStart_502789 := by decide
  rcases family_descends (prefixWord ++ tailWord_502789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502810 : List Nat := [3, 1, 1, 3, 1, 2, 8]
def baseStart_502810 : Nat := 118140960795 + 502810 * 2 ^ 59
def prefixEnd_502810 : Nat := 4983230072969 + 3 ^ 40 * 502810 * 2
def baseEnd_502810 : Nat := 50999152175265775261753

theorem tailTrace_502810 : CollatzResearch.WordTrace tailWord_502810 prefixEnd_502810 50999152175265775261753 := by
  unfold tailWord_502810
  simp only [CollatzResearch.WordTrace]
  refine ⟨4584746827103179489100471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12225991538941811970934589 4584746827103179489100471)
  ·
    refine ⟨6877120240654769233650707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4584746827103179489100471 6877120240654769233650707)
    ·
      refine ⟨10315680360982153850476061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6877120240654769233650707 10315680360982153850476061)
      ·
        refine ⟨3868380135368307693928523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10315680360982153850476061 3868380135368307693928523)
        ·
          refine ⟨5802570203052461540892785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3868380135368307693928523 5802570203052461540892785)
          ·
            refine ⟨4351927652289346155669589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5802570203052461540892785 4351927652289346155669589)
            ·
              refine ⟨50999152175265775261753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4351927652289346155669589 50999152175265775261753)
              ·
                rfl

theorem cell19_502810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 8].length) (baseStart_502810 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_502810 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_502810 prefixEnd_502810 := by exact prefixLift 502810
  have htrace : WordTrace (prefixWord ++ tailWord_502810) baseStart_502810 baseEnd_502810 := by
    simpa [prefixWord, tailWord_502810, baseEnd_502810] using wordTrace_append hprefix tailTrace_502810
  have hstable : (prefixWord ++ tailWord_502810).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502810).length < 2 ^ (prefixWord ++ tailWord_502810).sum := by decide
  have hdescent : baseEnd_502810 < baseStart_502810 := by decide
  rcases family_descends (prefixWord ++ tailWord_502810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502844 : List Nat := [2, 2, 2, 2, 2, 4, 2, 3]
def baseStart_502844 : Nat := 118140960795 + 502844 * 2 ^ 59
def prefixEnd_502844 : Nat := 4983230072969 + 3 ^ 40 * 502844 * 2
def baseEnd_502844 : Nat := 153007802210095321029611

theorem tailTrace_502844 : CollatzResearch.WordTrace tailWord_502844 prefixEnd_502844 153007802210095321029611 := by
  unfold tailWord_502844
  simp only [CollatzResearch.WordTrace]
  refine ⟨9170113695144770881569793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12226818260193027842093057 9170113695144770881569793)
  ·
    refine ⟨6877585271358578161177345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9170113695144770881569793 6877585271358578161177345)
    ·
      refine ⟨5158188953518933620883009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6877585271358578161177345 5158188953518933620883009)
      ·
        refine ⟨3868641715139200215662257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5158188953518933620883009 3868641715139200215662257)
        ·
          refine ⟨2901481286354400161746693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3868641715139200215662257 2901481286354400161746693)
          ·
            refine ⟨544027741191450030327505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2901481286354400161746693 544027741191450030327505)
            ·
              refine ⟨408020805893587522745629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 544027741191450030327505 408020805893587522745629)
              ·
                refine ⟨153007802210095321029611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 408020805893587522745629 153007802210095321029611)
                ·
                  rfl

theorem cell19_502844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 2, 3].length) (baseStart_502844 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_502844 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_502844 prefixEnd_502844 := by exact prefixLift 502844
  have htrace : WordTrace (prefixWord ++ tailWord_502844) baseStart_502844 baseEnd_502844 := by
    simpa [prefixWord, tailWord_502844, baseEnd_502844] using wordTrace_append hprefix tailTrace_502844
  have hstable : (prefixWord ++ tailWord_502844).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502844).length < 2 ^ (prefixWord ++ tailWord_502844).sum := by decide
  have hdescent : baseEnd_502844 < baseStart_502844 := by decide
  rcases family_descends (prefixWord ++ tailWord_502844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502848 : List Nat := [2, 1, 1, 2, 2, 3, 3, 5]
def baseStart_502848 : Nat := 118140960795 + 502848 * 2 ^ 59
def prefixEnd_502848 : Nat := 4983230072969 + 3 ^ 40 * 502848 * 2
def baseEnd_502848 : Nat := 153009019349424496940711

theorem tailTrace_502848 : CollatzResearch.WordTrace tailWord_502848 prefixEnd_502848 153009019349424496940711 := by
  unfold tailWord_502848
  simp only [CollatzResearch.WordTrace]
  refine ⟨9170186641137525223142599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12226915521516700297523465 9170186641137525223142599)
  ·
    refine ⟨13755279961706287834713899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9170186641137525223142599 13755279961706287834713899)
    ·
      refine ⟨20632919942559431752070849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13755279961706287834713899 20632919942559431752070849)
      ·
        refine ⟨15474689956919573814053137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20632919942559431752070849 15474689956919573814053137)
        ·
          refine ⟨11606017467689680360539853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15474689956919573814053137 11606017467689680360539853)
          ·
            refine ⟨4352256550383630135202445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11606017467689680360539853 4352256550383630135202445)
            ·
              refine ⟨1632096206393861300700917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4352256550383630135202445 1632096206393861300700917)
              ·
                refine ⟨153009019349424496940711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1632096206393861300700917 153009019349424496940711)
                ·
                  rfl

theorem cell19_502848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 5].length) (baseStart_502848 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_502848 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_502848 prefixEnd_502848 := by exact prefixLift 502848
  have htrace : WordTrace (prefixWord ++ tailWord_502848) baseStart_502848 baseEnd_502848 := by
    simpa [prefixWord, tailWord_502848, baseEnd_502848] using wordTrace_append hprefix tailTrace_502848
  have hstable : (prefixWord ++ tailWord_502848).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502848).length < 2 ^ (prefixWord ++ tailWord_502848).sum := by decide
  have hdescent : baseEnd_502848 < baseStart_502848 := by decide
  rcases family_descends (prefixWord ++ tailWord_502848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502882 : List Nat := [3, 3, 2, 2, 1, 2, 2, 4]
def baseStart_502882 : Nat := 118140960795 + 502882 * 2 ^ 59
def prefixEnd_502882 : Nat := 4983230072969 + 3 ^ 40 * 502882 * 2
def baseEnd_502882 : Nat := 153019365033722492185063

theorem tailTrace_502882 : CollatzResearch.WordTrace tailWord_502882 prefixEnd_502882 153019365033722492185063 := by
  unfold tailWord_502882
  simp only [CollatzResearch.WordTrace]
  refine ⟨4585403341037968563255725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12227742242767916168681933 4585403341037968563255725)
  ·
    refine ⟨1719526252889238211220897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4585403341037968563255725 1719526252889238211220897)
    ·
      refine ⟨1289644689666928658415673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1719526252889238211220897 1289644689666928658415673)
      ·
        refine ⟨967233517250196493811755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1289644689666928658415673 967233517250196493811755)
        ·
          refine ⟨1450850275875294740717633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 967233517250196493811755 1450850275875294740717633)
          ·
            refine ⟨1088137706906471055538225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1450850275875294740717633 1088137706906471055538225)
            ·
              refine ⟨816103280179853291653669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1088137706906471055538225 816103280179853291653669)
              ·
                refine ⟨153019365033722492185063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 816103280179853291653669 153019365033722492185063)
                ·
                  rfl

theorem cell19_502882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2, 4].length) (baseStart_502882 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_502882 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_502882 prefixEnd_502882 := by exact prefixLift 502882
  have htrace : WordTrace (prefixWord ++ tailWord_502882) baseStart_502882 baseEnd_502882 := by
    simpa [prefixWord, tailWord_502882, baseEnd_502882] using wordTrace_append hprefix tailTrace_502882
  have hstable : (prefixWord ++ tailWord_502882).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502882).length < 2 ^ (prefixWord ++ tailWord_502882).sum := by decide
  have hdescent : baseEnd_502882 < baseStart_502882 := by decide
  rcases family_descends (prefixWord ++ tailWord_502882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503013 : List Nat := [1, 3, 1, 4, 4, 1, 2, 3]
def baseStart_503013 : Nat := 118140960795 + 503013 * 2 ^ 59
def prefixEnd_503013 : Nat := 4983230072969 + 3 ^ 40 * 503013 * 2
def baseEnd_503013 : Nat := 153059226346753003273595

theorem tailTrace_503013 : CollatzResearch.WordTrace tailWord_503013 prefixEnd_503013 153059226346753003273595 := by
  unfold tailWord_503013
  simp only [CollatzResearch.WordTrace]
  refine ⟨18346391326677283626041693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12230927551118189084027795 18346391326677283626041693)
  ·
    refine ⟨6879896747503981359765635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18346391326677283626041693 6879896747503981359765635)
    ·
      refine ⟨10319845121255972039648453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6879896747503981359765635 10319845121255972039648453)
      ·
        refine ⟨1934970960235494757434085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10319845121255972039648453 1934970960235494757434085)
        ·
          refine ⟨362807055044155267018891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1934970960235494757434085 362807055044155267018891)
          ·
            refine ⟨544210582566232900528337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 362807055044155267018891 544210582566232900528337)
            ·
              refine ⟨408157936924674675396253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 544210582566232900528337 408157936924674675396253)
              ·
                refine ⟨153059226346753003273595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 408157936924674675396253 153059226346753003273595)
                ·
                  rfl

theorem cell19_503013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 2, 3].length) (baseStart_503013 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_503013 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_503013 prefixEnd_503013 := by exact prefixLift 503013
  have htrace : WordTrace (prefixWord ++ tailWord_503013) baseStart_503013 baseEnd_503013 := by
    simpa [prefixWord, tailWord_503013, baseEnd_503013] using wordTrace_append hprefix tailTrace_503013
  have hstable : (prefixWord ++ tailWord_503013).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503013).length < 2 ^ (prefixWord ++ tailWord_503013).sum := by decide
  have hdescent : baseEnd_503013 < baseStart_503013 := by decide
  rcases family_descends (prefixWord ++ tailWord_503013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503019 : List Nat := [1, 1, 1, 1, 2, 7, 1, 5]
def baseStart_503019 : Nat := 118140960795 + 503019 * 2 ^ 59
def prefixEnd_503019 : Nat := 4983230072969 + 3 ^ 40 * 503019 * 2
def baseEnd_503019 : Nat := 153061052055746767140245

theorem tailTrace_503019 : CollatzResearch.WordTrace tailWord_503019 prefixEnd_503019 153061052055746767140245 := by
  unfold tailWord_503019
  simp only [CollatzResearch.WordTrace]
  refine ⟨18346610164655546650760111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12231073443103697767173407 18346610164655546650760111)
  ·
    refine ⟨27519915246983319976140167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18346610164655546650760111 27519915246983319976140167)
    ·
      refine ⟨41279872870474979964210251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27519915246983319976140167 41279872870474979964210251)
      ·
        refine ⟨61919809305712469946315377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41279872870474979964210251 61919809305712469946315377)
        ·
          refine ⟨46439856979284352459736533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61919809305712469946315377 46439856979284352459736533)
          ·
            refine ⟨1088434147951977010775075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 46439856979284352459736533 1088434147951977010775075)
            ·
              refine ⟨1632651221927965516162613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1088434147951977010775075 1632651221927965516162613)
              ·
                refine ⟨153061052055746767140245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1632651221927965516162613 153061052055746767140245)
                ·
                  rfl

theorem cell19_503019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 5].length) (baseStart_503019 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_503019 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_503019 prefixEnd_503019 := by exact prefixLift 503019
  have htrace : WordTrace (prefixWord ++ tailWord_503019) baseStart_503019 baseEnd_503019 := by
    simpa [prefixWord, tailWord_503019, baseEnd_503019] using wordTrace_append hprefix tailTrace_503019
  have hstable : (prefixWord ++ tailWord_503019).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503019).length < 2 ^ (prefixWord ++ tailWord_503019).sum := by decide
  have hdescent : baseEnd_503019 < baseStart_503019 := by decide
  rcases family_descends (prefixWord ++ tailWord_503019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503036 : List Nat := [2, 2, 2, 1, 5, 2, 5]
def baseStart_503036 : Nat := 118140960795 + 503036 * 2 ^ 59
def prefixEnd_503036 : Nat := 4983230072969 + 3 ^ 40 * 503036 * 2
def baseEnd_503036 : Nat := 51022074965965254920807

theorem tailTrace_503036 : CollatzResearch.WordTrace tailWord_503036 prefixEnd_503036 51022074965965254920807 := by
  unfold tailWord_503036
  simp only [CollatzResearch.WordTrace]
  refine ⟨9173615102796979277064481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12231486803729305702752641 9173615102796979277064481)
  ·
    refine ⟨6880211327097734457798361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9173615102796979277064481 6880211327097734457798361)
    ·
      refine ⟨5160158495323300843348771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6880211327097734457798361 5160158495323300843348771)
      ·
        refine ⟨7740237742984951265023157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5160158495323300843348771 7740237742984951265023157)
        ·
          refine ⟨725647288404839181095921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7740237742984951265023157 725647288404839181095921)
          ·
            refine ⟨544235466303629385821941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 725647288404839181095921 544235466303629385821941)
            ·
              refine ⟨51022074965965254920807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 544235466303629385821941 51022074965965254920807)
              ·
                rfl

theorem cell19_503036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 5].length) (baseStart_503036 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_503036 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_503036 prefixEnd_503036 := by exact prefixLift 503036
  have htrace : WordTrace (prefixWord ++ tailWord_503036) baseStart_503036 baseEnd_503036 := by
    simpa [prefixWord, tailWord_503036, baseEnd_503036] using wordTrace_append hprefix tailTrace_503036
  have hstable : (prefixWord ++ tailWord_503036).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503036).length < 2 ^ (prefixWord ++ tailWord_503036).sum := by decide
  have hdescent : baseEnd_503036 < baseStart_503036 := by decide
  rcases family_descends (prefixWord ++ tailWord_503036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503057 : List Nat := [1, 2, 2, 1, 1, 4, 4, 4]
def baseStart_503057 : Nat := 118140960795 + 503057 * 2 ^ 59
def prefixEnd_503057 : Nat := 4983230072969 + 3 ^ 40 * 503057 * 2
def baseEnd_503057 : Nat := 153072614879373938295697

theorem tailTrace_503057 : CollatzResearch.WordTrace tailWord_503057 prefixEnd_503057 153072614879373938295697 := by
  unfold tailWord_503057
  simp only [CollatzResearch.WordTrace]
  refine ⟨18347996138517879140643425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12231997425678586093762283 18347996138517879140643425)
  ·
    refine ⟨13760997103888409355482569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18347996138517879140643425 13760997103888409355482569)
    ·
      refine ⟨10320747827916307016611927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13760997103888409355482569 10320747827916307016611927)
      ·
        refine ⟨15481121741874460524917891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10320747827916307016611927 15481121741874460524917891)
        ·
          refine ⟨23221682612811690787376837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15481121741874460524917891 23221682612811690787376837)
          ·
            refine ⟨4354065489902192022633157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23221682612811690787376837 4354065489902192022633157)
            ·
              refine ⟨816387279356661004243717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4354065489902192022633157 816387279356661004243717)
              ·
                refine ⟨153072614879373938295697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 816387279356661004243717 153072614879373938295697)
                ·
                  rfl

theorem cell19_503057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4, 4].length) (baseStart_503057 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_503057 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_503057 prefixEnd_503057 := by exact prefixLift 503057
  have htrace : WordTrace (prefixWord ++ tailWord_503057) baseStart_503057 baseEnd_503057 := by
    simpa [prefixWord, tailWord_503057, baseEnd_503057] using wordTrace_append hprefix tailTrace_503057
  have hstable : (prefixWord ++ tailWord_503057).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503057).length < 2 ^ (prefixWord ++ tailWord_503057).sum := by decide
  have hdescent : baseEnd_503057 < baseStart_503057 := by decide
  rcases family_descends (prefixWord ++ tailWord_503057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503076 : List Nat := [2, 3, 1, 3, 1, 1, 1, 7]
def baseStart_503076 : Nat := 118140960795 + 503076 * 2 ^ 59
def prefixEnd_503076 : Nat := 4983230072969 + 3 ^ 40 * 503076 * 2
def baseEnd_503076 : Nat := 153078396291187523873423

theorem tailTrace_503076 : CollatzResearch.WordTrace tailWord_503076 prefixEnd_503076 153078396291187523873423 := by
  unfold tailWord_503076
  simp only [CollatzResearch.WordTrace]
  refine ⟨9174344562724522692792541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12232459416966030257056721 9174344562724522692792541)
  ·
    refine ⟨3440379211021696009797203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9174344562724522692792541 3440379211021696009797203)
    ·
      refine ⟨5160568816532544014695805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3440379211021696009797203 5160568816532544014695805)
      ·
        refine ⟨1935213306199704005510927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5160568816532544014695805 1935213306199704005510927)
        ·
          refine ⟨2902819959299556008266391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1935213306199704005510927 2902819959299556008266391)
          ·
            refine ⟨4354229938949334012399587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2902819959299556008266391 4354229938949334012399587)
            ·
              refine ⟨6531344908424001018599381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4354229938949334012399587 6531344908424001018599381)
              ·
                refine ⟨153078396291187523873423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6531344908424001018599381 153078396291187523873423)
                ·
                  rfl

theorem cell19_503076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 7].length) (baseStart_503076 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_503076 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_503076 prefixEnd_503076 := by exact prefixLift 503076
  have htrace : WordTrace (prefixWord ++ tailWord_503076) baseStart_503076 baseEnd_503076 := by
    simpa [prefixWord, tailWord_503076, baseEnd_503076] using wordTrace_append hprefix tailTrace_503076
  have hstable : (prefixWord ++ tailWord_503076).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503076).length < 2 ^ (prefixWord ++ tailWord_503076).sum := by decide
  have hdescent : baseEnd_503076 < baseStart_503076 := by decide
  rcases family_descends (prefixWord ++ tailWord_503076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503186 : List Nat := [3, 2, 3, 3, 1, 1, 1, 5]
def baseStart_503186 : Nat := 118140960795 + 503186 * 2 ^ 59
def prefixEnd_503186 : Nat := 4983230072969 + 3 ^ 40 * 503186 * 2
def baseEnd_503186 : Nat := 153111867622739861428679

theorem tailTrace_503186 : CollatzResearch.WordTrace tailWord_503186 prefixEnd_503186 153111867622739861428679 := by
  unfold tailWord_503186
  simp only [CollatzResearch.WordTrace]
  refine ⟨4588175288762633543022353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12235134103367022781392941 4588175288762633543022353)
  ·
    refine ⟨3441131466571975157266765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4588175288762633543022353 3441131466571975157266765)
    ·
      refine ⟨1290424299964490683975037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3441131466571975157266765 1290424299964490683975037)
      ·
        refine ⟨483909112486684006490639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1290424299964490683975037 483909112486684006490639)
        ·
          refine ⟨725863668730026009735959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 483909112486684006490639 725863668730026009735959)
          ·
            refine ⟨1088795503095039014603939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 725863668730026009735959 1088795503095039014603939)
            ·
              refine ⟨1633193254642558521905909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1088795503095039014603939 1633193254642558521905909)
              ·
                refine ⟨153111867622739861428679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1633193254642558521905909 153111867622739861428679)
                ·
                  rfl

theorem cell19_503186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 5].length) (baseStart_503186 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_503186 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_503186 prefixEnd_503186 := by exact prefixLift 503186
  have htrace : WordTrace (prefixWord ++ tailWord_503186) baseStart_503186 baseEnd_503186 := by
    simpa [prefixWord, tailWord_503186, baseEnd_503186] using wordTrace_append hprefix tailTrace_503186
  have hstable : (prefixWord ++ tailWord_503186).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503186).length < 2 ^ (prefixWord ++ tailWord_503186).sum := by decide
  have hdescent : baseEnd_503186 < baseStart_503186 := by decide
  rcases family_descends (prefixWord ++ tailWord_503186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503188 : List Nat := [2, 4, 2, 1, 2, 2, 1, 5]
def baseStart_503188 : Nat := 118140960795 + 503188 * 2 ^ 59
def prefixEnd_503188 : Nat := 4983230072969 + 3 ^ 40 * 503188 * 2
def baseEnd_503188 : Nat := 153112476192404449384229

theorem tailTrace_503188 : CollatzResearch.WordTrace tailWord_503188 prefixEnd_503188 153112476192404449384229 := by
  unfold tailWord_503188
  simp only [CollatzResearch.WordTrace]
  refine ⟨9176387050521644256831109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12235182734028859009108145 9176387050521644256831109)
  ·
    refine ⟨1720572571972808298155833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9176387050521644256831109 1720572571972808298155833)
    ·
      refine ⟨1290429428979606223616875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1720572571972808298155833 1290429428979606223616875)
      ·
        refine ⟨1935644143469409335425313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1290429428979606223616875 1935644143469409335425313)
        ·
          refine ⟨1451733107602057001568985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1935644143469409335425313 1451733107602057001568985)
          ·
            refine ⟨1088799830701542751176739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1451733107602057001568985 1088799830701542751176739)
            ·
              refine ⟨1633199746052314126765109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1088799830701542751176739 1633199746052314126765109)
              ·
                refine ⟨153112476192404449384229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1633199746052314126765109 153112476192404449384229)
                ·
                  rfl

theorem cell19_503188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 5].length) (baseStart_503188 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_503188 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_503188 prefixEnd_503188 := by exact prefixLift 503188
  have htrace : WordTrace (prefixWord ++ tailWord_503188) baseStart_503188 baseEnd_503188 := by
    simpa [prefixWord, tailWord_503188, baseEnd_503188] using wordTrace_append hprefix tailTrace_503188
  have hstable : (prefixWord ++ tailWord_503188).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503188).length < 2 ^ (prefixWord ++ tailWord_503188).sum := by decide
  have hdescent : baseEnd_503188 < baseStart_503188 := by decide
  rcases family_descends (prefixWord ++ tailWord_503188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503266 : List Nat := [3, 3, 3, 10]
def baseStart_503266 : Nat := 118140960795 + 503266 * 2 ^ 59
def prefixEnd_503266 : Nat := 4983230072969 + 3 ^ 40 * 503266 * 2
def baseEnd_503266 : Nat := 1890570498880535551243

theorem tailTrace_503266 : CollatzResearch.WordTrace tailWord_503266 prefixEnd_503266 1890570498880535551243 := by
  unfold tailWord_503266
  simp only [CollatzResearch.WordTrace]
  refine ⟨4588904748690176958750413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12237079329840471890001101 4588904748690176958750413)
  ·
    refine ⟨1720839280758816359531405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4588904748690176958750413 1720839280758816359531405)
    ·
      refine ⟨645314730284556134824277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1720839280758816359531405 645314730284556134824277)
      ·
        refine ⟨1890570498880535551243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 10 645314730284556134824277 1890570498880535551243)
        ·
          rfl

theorem cell19_503266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 10].length) (baseStart_503266 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_503266 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_503266 prefixEnd_503266 := by exact prefixLift 503266
  have htrace : WordTrace (prefixWord ++ tailWord_503266) baseStart_503266 baseEnd_503266 := by
    simpa [prefixWord, tailWord_503266, baseEnd_503266] using wordTrace_append hprefix tailTrace_503266
  have hstable : (prefixWord ++ tailWord_503266).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503266).length < 2 ^ (prefixWord ++ tailWord_503266).sum := by decide
  have hdescent : baseEnd_503266 < baseStart_503266 := by decide
  rcases family_descends (prefixWord ++ tailWord_503266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503287 : List Nat := [1, 1, 3, 1, 1, 1, 1, 10]
def baseStart_503287 : Nat := 118140960795 + 503287 * 2 ^ 59
def prefixEnd_503287 : Nat := 4983230072969 + 3 ^ 40 * 503287 * 2
def baseEnd_503287 : Nat := 153142600390801553183959

theorem tailTrace_503287 : CollatzResearch.WordTrace tailWord_503287 prefixEnd_503287 153142600390801553183959 := by
  unfold tailWord_503287
  simp only [CollatzResearch.WordTrace]
  refine ⟨18356384927684628421516115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12237589951789752281010743 18356384927684628421516115)
  ·
    refine ⟨27534577391526942632274173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18356384927684628421516115 27534577391526942632274173)
    ·
      refine ⟨10325466521822603487102815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27534577391526942632274173 10325466521822603487102815)
      ·
        refine ⟨15488199782733905230654223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10325466521822603487102815 15488199782733905230654223)
        ·
          refine ⟨23232299674100857845981335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15488199782733905230654223 23232299674100857845981335)
          ·
            refine ⟨34848449511151286768972003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23232299674100857845981335 34848449511151286768972003)
            ·
              refine ⟨52272674266726930153458005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34848449511151286768972003 52272674266726930153458005)
              ·
                refine ⟨153142600390801553183959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 52272674266726930153458005 153142600390801553183959)
                ·
                  rfl

theorem cell19_503287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 10].length) (baseStart_503287 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_503287 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_503287 prefixEnd_503287 := by exact prefixLift 503287
  have htrace : WordTrace (prefixWord ++ tailWord_503287) baseStart_503287 baseEnd_503287 := by
    simpa [prefixWord, tailWord_503287, baseEnd_503287] using wordTrace_append hprefix tailTrace_503287
  have hstable : (prefixWord ++ tailWord_503287).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503287).length < 2 ^ (prefixWord ++ tailWord_503287).sum := by decide
  have hdescent : baseEnd_503287 < baseStart_503287 := by decide
  rcases family_descends (prefixWord ++ tailWord_503287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503300 : List Nat := [2, 3, 2, 3, 2, 1, 3, 3]
def baseStart_503300 : Nat := 118140960795 + 503300 * 2 ^ 59
def prefixEnd_503300 : Nat := 4983230072969 + 3 ^ 40 * 503300 * 2
def baseEnd_503300 : Nat := 153146556093621374895035

theorem tailTrace_503300 : CollatzResearch.WordTrace tailWord_503300 prefixEnd_503300 153146556093621374895035 := by
  unfold tailWord_503300
  simp only [CollatzResearch.WordTrace]
  refine ⟨9178429538318765820869677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12237906051091687761159569 9178429538318765820869677)
  ·
    refine ⟨3441911076869537182826129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9178429538318765820869677 3441911076869537182826129)
    ·
      refine ⟨2581433307652152887119597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3441911076869537182826129 2581433307652152887119597)
      ·
        refine ⟨968037490369557332669849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2581433307652152887119597 968037490369557332669849)
        ·
          refine ⟨726028117777167999502387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 968037490369557332669849 726028117777167999502387)
          ·
            refine ⟨1089042176665751999253581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 726028117777167999502387 1089042176665751999253581)
            ·
              refine ⟨408390816249656999720093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1089042176665751999253581 408390816249656999720093)
              ·
                refine ⟨153146556093621374895035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 408390816249656999720093 153146556093621374895035)
                ·
                  rfl

theorem cell19_503300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 3, 3].length) (baseStart_503300 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_503300 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_503300 prefixEnd_503300 := by exact prefixLift 503300
  have htrace : WordTrace (prefixWord ++ tailWord_503300) baseStart_503300 baseEnd_503300 := by
    simpa [prefixWord, tailWord_503300, baseEnd_503300] using wordTrace_append hprefix tailTrace_503300
  have hstable : (prefixWord ++ tailWord_503300).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503300).length < 2 ^ (prefixWord ++ tailWord_503300).sum := by decide
  have hdescent : baseEnd_503300 < baseStart_503300 := by decide
  rcases family_descends (prefixWord ++ tailWord_503300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503344 : List Nat := [2, 1, 1, 1, 2, 3, 1, 8]
def baseStart_503344 : Nat := 118140960795 + 503344 * 2 ^ 59
def prefixEnd_503344 : Nat := 4983230072969 + 3 ^ 40 * 503344 * 2
def baseEnd_503344 : Nat := 153159944626242309917137

theorem tailTrace_503344 : CollatzResearch.WordTrace tailWord_503344 prefixEnd_503344 153159944626242309917137 := by
  unfold tailWord_503344
  simp only [CollatzResearch.WordTrace]
  refine ⟨9179231944239063578170543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12238975925652084770894057 9179231944239063578170543)
  ·
    refine ⟨13768847916358595367255815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9179231944239063578170543 13768847916358595367255815)
    ·
      refine ⟨20653271874537893050883723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13768847916358595367255815 20653271874537893050883723)
      ·
        refine ⟨30979907811806839576325585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20653271874537893050883723 30979907811806839576325585)
        ·
          refine ⟨23234930858855129682244189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30979907811806839576325585 23234930858855129682244189)
          ·
            refine ⟨8713099072070673630841571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23234930858855129682244189 8713099072070673630841571)
            ·
              refine ⟨13069648608106010446262357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8713099072070673630841571 13069648608106010446262357)
              ·
                refine ⟨153159944626242309917137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13069648608106010446262357 153159944626242309917137)
                ·
                  rfl

theorem cell19_503344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 8].length) (baseStart_503344 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_503344 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_503344 prefixEnd_503344 := by exact prefixLift 503344
  have htrace : WordTrace (prefixWord ++ tailWord_503344) baseStart_503344 baseEnd_503344 := by
    simpa [prefixWord, tailWord_503344, baseEnd_503344] using wordTrace_append hprefix tailTrace_503344
  have hstable : (prefixWord ++ tailWord_503344).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503344).length < 2 ^ (prefixWord ++ tailWord_503344).sum := by decide
  have hdescent : baseEnd_503344 < baseStart_503344 := by decide
  rcases family_descends (prefixWord ++ tailWord_503344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503357 : List Nat := [1, 4, 1, 3, 3, 2, 2, 3]
def baseStart_503357 : Nat := 118140960795 + 503357 * 2 ^ 59
def prefixEnd_503357 : Nat := 4983230072969 + 3 ^ 40 * 503357 * 2
def baseEnd_503357 : Nat := 153163900329062131628213

theorem tailTrace_503357 : CollatzResearch.WordTrace tailWord_503357 prefixEnd_503357 153163900329062131628213 := by
  unfold tailWord_503357
  simp only [CollatzResearch.WordTrace]
  refine ⟨18358938037431030376564325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12239292024954020251042883 18358938037431030376564325)
  ·
    refine ⟨3442300882018318195605811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18358938037431030376564325 3442300882018318195605811)
    ·
      refine ⟨5163451323027477293408717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3442300882018318195605811 5163451323027477293408717)
      ·
        refine ⟨1936294246135303985028269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5163451323027477293408717 1936294246135303985028269)
        ·
          refine ⟨726110342300738994385601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1936294246135303985028269 726110342300738994385601)
          ·
            refine ⟨544582756725554245789201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 726110342300738994385601 544582756725554245789201)
            ·
              refine ⟨408437067544165684341901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 544582756725554245789201 408437067544165684341901)
              ·
                refine ⟨153163900329062131628213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 408437067544165684341901 153163900329062131628213)
                ·
                  rfl

theorem cell19_503357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 2, 3].length) (baseStart_503357 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_503357 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_503357 prefixEnd_503357 := by exact prefixLift 503357
  have htrace : WordTrace (prefixWord ++ tailWord_503357) baseStart_503357 baseEnd_503357 := by
    simpa [prefixWord, tailWord_503357, baseEnd_503357] using wordTrace_append hprefix tailTrace_503357
  have hstable : (prefixWord ++ tailWord_503357).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503357).length < 2 ^ (prefixWord ++ tailWord_503357).sum := by decide
  have hdescent : baseEnd_503357 < baseStart_503357 := by decide
  rcases family_descends (prefixWord ++ tailWord_503357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503359 : List Nat := [1, 1, 2, 2, 3, 5, 2, 3]
def baseStart_503359 : Nat := 118140960795 + 503359 * 2 ^ 59
def prefixEnd_503359 : Nat := 4983230072969 + 3 ^ 40 * 503359 * 2
def baseEnd_503359 : Nat := 153164508898726719583763

theorem tailTrace_503359 : CollatzResearch.WordTrace tailWord_503359 prefixEnd_503359 153164508898726719583763 := by
  unfold tailWord_503359
  simp only [CollatzResearch.WordTrace]
  refine ⟨18359010983423784718137131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12239340655615856478758087 18359010983423784718137131)
  ·
    refine ⟨27538516475135677077205697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18359010983423784718137131 27538516475135677077205697)
    ·
      refine ⟨20653887356351757807904273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27538516475135677077205697 20653887356351757807904273)
      ·
        refine ⟨15490415517263818355928205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20653887356351757807904273 15490415517263818355928205)
        ·
          refine ⟨5808905818973931883473077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15490415517263818355928205 5808905818973931883473077)
          ·
            refine ⟨544584920528806114075601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5808905818973931883473077 544584920528806114075601)
            ·
              refine ⟨408438690396604585556701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 544584920528806114075601 408438690396604585556701)
              ·
                refine ⟨153164508898726719583763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 408438690396604585556701 153164508898726719583763)
                ·
                  rfl

theorem cell19_503359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 2, 3].length) (baseStart_503359 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_503359 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_503359 prefixEnd_503359 := by exact prefixLift 503359
  have htrace : WordTrace (prefixWord ++ tailWord_503359) baseStart_503359 baseEnd_503359 := by
    simpa [prefixWord, tailWord_503359, baseEnd_503359] using wordTrace_append hprefix tailTrace_503359
  have hstable : (prefixWord ++ tailWord_503359).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503359).length < 2 ^ (prefixWord ++ tailWord_503359).sum := by decide
  have hdescent : baseEnd_503359 < baseStart_503359 := by decide
  rcases family_descends (prefixWord ++ tailWord_503359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503361 : List Nat := [1, 2, 5, 1, 1, 1, 3, 5]
def baseStart_503361 : Nat := 118140960795 + 503361 * 2 ^ 59
def prefixEnd_503361 : Nat := 4983230072969 + 3 ^ 40 * 503361 * 2
def baseEnd_503361 : Nat := 153165117468391307539313

theorem tailTrace_503361 : CollatzResearch.WordTrace tailWord_503361 prefixEnd_503361 153165117468391307539313 := by
  unfold tailWord_503361
  simp only [CollatzResearch.WordTrace]
  refine ⟨18359083929416539059709937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12239389286277692706473291 18359083929416539059709937)
  ·
    refine ⟨13769312947062404294782453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18359083929416539059709937 13769312947062404294782453)
    ·
      refine ⟨1290873088787100402635855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13769312947062404294782453 1290873088787100402635855)
      ·
        refine ⟨1936309633180650603953783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1290873088787100402635855 1936309633180650603953783)
        ·
          refine ⟨2904464449770975905930675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1936309633180650603953783 2904464449770975905930675)
          ·
            refine ⟨4356696674656463858896013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2904464449770975905930675 4356696674656463858896013)
            ·
              refine ⟨1633761252996173947086005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4356696674656463858896013 1633761252996173947086005)
              ·
                refine ⟨153165117468391307539313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1633761252996173947086005 153165117468391307539313)
                ·
                  rfl

theorem cell19_503361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 5].length) (baseStart_503361 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_503361 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_503361 prefixEnd_503361 := by exact prefixLift 503361
  have htrace : WordTrace (prefixWord ++ tailWord_503361) baseStart_503361 baseEnd_503361 := by
    simpa [prefixWord, tailWord_503361, baseEnd_503361] using wordTrace_append hprefix tailTrace_503361
  have hstable : (prefixWord ++ tailWord_503361).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503361).length < 2 ^ (prefixWord ++ tailWord_503361).sum := by decide
  have hdescent : baseEnd_503361 < baseStart_503361 := by decide
  rcases family_descends (prefixWord ++ tailWord_503361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503401 : List Nat := [1, 2, 1, 1, 1, 4, 3, 6]
def baseStart_503401 : Nat := 118140960795 + 503401 * 2 ^ 59
def prefixEnd_503401 : Nat := 4983230072969 + 3 ^ 40 * 503401 * 2
def baseEnd_503401 : Nat := 153177288861683066650315

theorem tailTrace_503401 : CollatzResearch.WordTrace tailWord_503401 prefixEnd_503401 153177288861683066650315 := by
  unfold tailWord_503401
  simp only [CollatzResearch.WordTrace]
  refine ⟨18360542849271625891166057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12240361899514417260777371 18360542849271625891166057)
  ·
    refine ⟨13770407136953719418374543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18360542849271625891166057 13770407136953719418374543)
    ·
      refine ⟨20655610705430579127561815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13770407136953719418374543 20655610705430579127561815)
      ·
        refine ⟨30983416058145868691342723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20655610705430579127561815 30983416058145868691342723)
        ·
          refine ⟨46475124087218803037014085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30983416058145868691342723 46475124087218803037014085)
          ·
            refine ⟨8714085766353525569440141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46475124087218803037014085 8714085766353525569440141)
            ·
              refine ⟨3267782162382572088540053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8714085766353525569440141 3267782162382572088540053)
              ·
                refine ⟨153177288861683066650315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3267782162382572088540053 153177288861683066650315)
                ·
                  rfl

theorem cell19_503401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 6].length) (baseStart_503401 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_503401 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_503401 prefixEnd_503401 := by exact prefixLift 503401
  have htrace : WordTrace (prefixWord ++ tailWord_503401) baseStart_503401 baseEnd_503401 := by
    simpa [prefixWord, tailWord_503401, baseEnd_503401] using wordTrace_append hprefix tailTrace_503401
  have hstable : (prefixWord ++ tailWord_503401).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503401).length < 2 ^ (prefixWord ++ tailWord_503401).sum := by decide
  have hdescent : baseEnd_503401 < baseStart_503401 := by decide
  rcases family_descends (prefixWord ++ tailWord_503401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503452 : List Nat := [2, 2, 3, 2, 4, 1, 1, 4]
def baseStart_503452 : Nat := 118140960795 + 503452 * 2 ^ 59
def prefixEnd_503452 : Nat := 4983230072969 + 3 ^ 40 * 503452 * 2
def baseEnd_503452 : Nat := 153192807388130059516843

theorem tailTrace_503452 : CollatzResearch.WordTrace tailWord_503452 prefixEnd_503452 153192807388130059516843 := by
  unfold tailWord_503452
  simp only [CollatzResearch.WordTrace]
  refine ⟨9181201486043430800636305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12241601981391241067515073 9181201486043430800636305)
  ·
    refine ⟨6885901114532573100477229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9181201486043430800636305 6885901114532573100477229)
    ·
      refine ⟨2582212917949714912678961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6885901114532573100477229 2582212917949714912678961)
      ·
        refine ⟨1936659688462286184509221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2582212917949714912678961 1936659688462286184509221)
        ·
          refine ⟨363123691586678659595479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1936659688462286184509221 363123691586678659595479)
          ·
            refine ⟨544685537380017989393219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 363123691586678659595479 544685537380017989393219)
            ·
              refine ⟨817028306070026984089829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 544685537380017989393219 817028306070026984089829)
              ·
                refine ⟨153192807388130059516843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 817028306070026984089829 153192807388130059516843)
                ·
                  rfl

theorem cell19_503452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 1, 4].length) (baseStart_503452 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_503452 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_503452 prefixEnd_503452 := by exact prefixLift 503452
  have htrace : WordTrace (prefixWord ++ tailWord_503452) baseStart_503452 baseEnd_503452 := by
    simpa [prefixWord, tailWord_503452, baseEnd_503452] using wordTrace_append hprefix tailTrace_503452
  have hstable : (prefixWord ++ tailWord_503452).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503452).length < 2 ^ (prefixWord ++ tailWord_503452).sum := by decide
  have hdescent : baseEnd_503452 < baseStart_503452 := by decide
  rcases family_descends (prefixWord ++ tailWord_503452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503454 : List Nat := [4, 3, 1, 1, 1, 2, 3, 4]
def baseStart_503454 : Nat := 118140960795 + 503454 * 2 ^ 59
def prefixEnd_503454 : Nat := 4983230072969 + 3 ^ 40 * 503454 * 2
def baseEnd_503454 : Nat := 153193415957794647472393

theorem tailTrace_503454 : CollatzResearch.WordTrace tailWord_503454 prefixEnd_503454 153193415957794647472393 := by
  unfold tailWord_503454
  simp only [CollatzResearch.WordTrace]
  refine ⟨2295309489759951992855677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12241650612053077295230277 2295309489759951992855677)
  ·
    refine ⟨860741058659981997320879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2295309489759951992855677 860741058659981997320879)
    ·
      refine ⟨1291111587989972995981319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 860741058659981997320879 1291111587989972995981319)
      ·
        refine ⟨1936667381984959493971979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1291111587989972995981319 1936667381984959493971979)
        ·
          refine ⟨2905001072977439240957969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1936667381984959493971979 2905001072977439240957969)
          ·
            refine ⟨2178750804733079430718477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2905001072977439240957969 2178750804733079430718477)
            ·
              refine ⟨817031551774904786519429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2178750804733079430718477 817031551774904786519429)
              ·
                refine ⟨153193415957794647472393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 817031551774904786519429 153193415957794647472393)
                ·
                  rfl

theorem cell19_503454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 3, 4].length) (baseStart_503454 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_503454 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_503454 prefixEnd_503454 := by exact prefixLift 503454
  have htrace : WordTrace (prefixWord ++ tailWord_503454) baseStart_503454 baseEnd_503454 := by
    simpa [prefixWord, tailWord_503454, baseEnd_503454] using wordTrace_append hprefix tailTrace_503454
  have hstable : (prefixWord ++ tailWord_503454).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503454).length < 2 ^ (prefixWord ++ tailWord_503454).sum := by decide
  have hdescent : baseEnd_503454 < baseStart_503454 := by decide
  rcases family_descends (prefixWord ++ tailWord_503454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503456 : List Nat := [2, 1, 1, 4, 3, 1, 3, 4]
def baseStart_503456 : Nat := 118140960795 + 503456 * 2 ^ 59
def prefixEnd_503456 : Nat := 4983230072969 + 3 ^ 40 * 503456 * 2
def baseEnd_503456 : Nat := 153194024527459235427943

theorem tailTrace_503456 : CollatzResearch.WordTrace tailWord_503456 prefixEnd_503456 153194024527459235427943 := by
  unfold tailWord_503456
  simp only [CollatzResearch.WordTrace]
  refine ⟨9181274432036185142209111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12241699242714913522945481 9181274432036185142209111)
  ·
    refine ⟨13771911648054277713313667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9181274432036185142209111 13771911648054277713313667)
    ·
      refine ⟨20657867472081416569970501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13771911648054277713313667 20657867472081416569970501)
      ·
        refine ⟨3873350151015265606869469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20657867472081416569970501 3873350151015265606869469)
        ·
          refine ⟨1452506306630724602576051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3873350151015265606869469 1452506306630724602576051)
          ·
            refine ⟨2178759459946086903864077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1452506306630724602576051 2178759459946086903864077)
            ·
              refine ⟨817034797479782588949029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2178759459946086903864077 817034797479782588949029)
              ·
                refine ⟨153194024527459235427943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 817034797479782588949029 153194024527459235427943)
                ·
                  rfl

theorem cell19_503456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3, 4].length) (baseStart_503456 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_503456 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_503456 prefixEnd_503456 := by exact prefixLift 503456
  have htrace : WordTrace (prefixWord ++ tailWord_503456) baseStart_503456 baseEnd_503456 := by
    simpa [prefixWord, tailWord_503456, baseEnd_503456] using wordTrace_append hprefix tailTrace_503456
  have hstable : (prefixWord ++ tailWord_503456).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503456).length < 2 ^ (prefixWord ++ tailWord_503456).sum := by decide
  have hdescent : baseEnd_503456 < baseStart_503456 := by decide
  rcases family_descends (prefixWord ++ tailWord_503456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503475 : List Nat := [1, 1, 1, 2, 3, 3, 5, 3]
def baseStart_503475 : Nat := 118140960795 + 503475 * 2 ^ 59
def prefixEnd_503475 : Nat := 4983230072969 + 3 ^ 40 * 503475 * 2
def baseEnd_503475 : Nat := 153199805939272821005669

theorem tailTrace_503475 : CollatzResearch.WordTrace tailWord_503475 prefixEnd_503475 153199805939272821005669 := by
  unfold tailWord_503475
  simp only [CollatzResearch.WordTrace]
  refine ⟨18363241851003536529359879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12242161234002357686239919 18363241851003536529359879)
  ·
    refine ⟨27544862776505304794039819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18363241851003536529359879 27544862776505304794039819)
    ·
      refine ⟨41317294164757957191059729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27544862776505304794039819 41317294164757957191059729)
      ·
        refine ⟨30987970623568467893294797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41317294164757957191059729 30987970623568467893294797)
        ·
          refine ⟨11620488983838175459985549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30987970623568467893294797 11620488983838175459985549)
          ·
            refine ⟨4357683368939315797494581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11620488983838175459985549 4357683368939315797494581)
            ·
              refine ⟨408532815838060856015117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4357683368939315797494581 408532815838060856015117)
              ·
                refine ⟨153199805939272821005669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 408532815838060856015117 153199805939272821005669)
                ·
                  rfl

theorem cell19_503475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 5, 3].length) (baseStart_503475 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_503475 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_503475 prefixEnd_503475 := by exact prefixLift 503475
  have htrace : WordTrace (prefixWord ++ tailWord_503475) baseStart_503475 baseEnd_503475 := by
    simpa [prefixWord, tailWord_503475, baseEnd_503475] using wordTrace_append hprefix tailTrace_503475
  have hstable : (prefixWord ++ tailWord_503475).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503475).length < 2 ^ (prefixWord ++ tailWord_503475).sum := by decide
  have hdescent : baseEnd_503475 < baseStart_503475 := by decide
  rcases family_descends (prefixWord ++ tailWord_503475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503496 : List Nat := [2, 1, 3, 1, 2, 2, 8]
def baseStart_503496 : Nat := 118140960795 + 503496 * 2 ^ 59
def prefixEnd_503496 : Nat := 4983230072969 + 3 ^ 40 * 503496 * 2
def baseEnd_503496 : Nat := 51068731973583664846315

theorem tailTrace_503496 : CollatzResearch.WordTrace tailWord_503496 prefixEnd_503496 51068731973583664846315 := by
  unfold tailWord_503496
  simp only [CollatzResearch.WordTrace]
  refine ⟨9182003891963728557937171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12242671855951638077249561 9182003891963728557937171)
  ·
    refine ⟨13773005837945592836905757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9182003891963728557937171 13773005837945592836905757)
    ·
      refine ⟨5164877189229597313839659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13773005837945592836905757 5164877189229597313839659)
      ·
        refine ⟨7747315783844395970759489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5164877189229597313839659 7747315783844395970759489)
        ·
          refine ⟨5810486837883296978069617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7747315783844395970759489 5810486837883296978069617)
          ·
            refine ⟨4357865128412472733552213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5810486837883296978069617 4357865128412472733552213)
            ·
              refine ⟨51068731973583664846315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4357865128412472733552213 51068731973583664846315)
              ·
                rfl

theorem cell19_503496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 8].length) (baseStart_503496 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_503496 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_503496 prefixEnd_503496 := by exact prefixLift 503496
  have htrace : WordTrace (prefixWord ++ tailWord_503496) baseStart_503496 baseEnd_503496 := by
    simpa [prefixWord, tailWord_503496, baseEnd_503496] using wordTrace_append hprefix tailTrace_503496
  have hstable : (prefixWord ++ tailWord_503496).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503496).length < 2 ^ (prefixWord ++ tailWord_503496).sum := by decide
  have hdescent : baseEnd_503496 < baseStart_503496 := by decide
  rcases family_descends (prefixWord ++ tailWord_503496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503532 : List Nat := [2, 2, 1, 1, 2, 2, 6, 3]
def baseStart_503532 : Nat := 118140960795 + 503532 * 2 ^ 59
def prefixEnd_503532 : Nat := 4983230072969 + 3 ^ 40 * 503532 * 2
def baseEnd_503532 : Nat := 153217150174713577738847

theorem tailTrace_503532 : CollatzResearch.WordTrace tailWord_503532 prefixEnd_503532 153217150174713577738847 := by
  unfold tailWord_503532
  simp only [CollatzResearch.WordTrace]
  refine ⟨9182660405898517632092425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12243547207864690176123233 9182660405898517632092425)
  ·
    refine ⟨6886995304423888224069319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9182660405898517632092425 6886995304423888224069319)
    ·
      refine ⟨10330492956635832336103979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6886995304423888224069319 10330492956635832336103979)
      ·
        refine ⟨15495739434953748504155969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10330492956635832336103979 15495739434953748504155969)
        ·
          refine ⟨11621804576215311378116977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15495739434953748504155969 11621804576215311378116977)
          ·
            refine ⟨8716353432161483533587733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11621804576215311378116977 8716353432161483533587733)
            ·
              refine ⟨408579067132569540636925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 8716353432161483533587733 408579067132569540636925)
              ·
                refine ⟨153217150174713577738847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 408579067132569540636925 153217150174713577738847)
                ·
                  rfl

theorem cell19_503532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 6, 3].length) (baseStart_503532 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_503532 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_503532 prefixEnd_503532 := by exact prefixLift 503532
  have htrace : WordTrace (prefixWord ++ tailWord_503532) baseStart_503532 baseEnd_503532 := by
    simpa [prefixWord, tailWord_503532, baseEnd_503532] using wordTrace_append hprefix tailTrace_503532
  have hstable : (prefixWord ++ tailWord_503532).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503532).length < 2 ^ (prefixWord ++ tailWord_503532).sum := by decide
  have hdescent : baseEnd_503532 < baseStart_503532 := by decide
  rcases family_descends (prefixWord ++ tailWord_503532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503553 : List Nat := [1, 2, 4, 1, 1, 1, 9]
def baseStart_503553 : Nat := 118140960795 + 503553 * 2 ^ 59
def prefixEnd_503553 : Nat := 4983230072969 + 3 ^ 40 * 503553 * 2
def baseEnd_503553 : Nat := 51074513385397250424041

theorem tailTrace_503553 : CollatzResearch.WordTrace tailWord_503553 prefixEnd_503553 51074513385397250424041 := by
  unfold tailWord_503553
  simp only [CollatzResearch.WordTrace]
  refine ⟨18366086744720955850699313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12244057829813970567132875 18366086744720955850699313)
  ·
    refine ⟨13774565058540716888024485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18366086744720955850699313 13774565058540716888024485)
    ·
      refine ⟨2582730948476384416504591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13774565058540716888024485 2582730948476384416504591)
      ·
        refine ⟨3874096422714576624756887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2582730948476384416504591 3874096422714576624756887)
        ·
          refine ⟨5811144634071864937135331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3874096422714576624756887 5811144634071864937135331)
          ·
            refine ⟨8716716951107797405702997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5811144634071864937135331 8716716951107797405702997)
            ·
              refine ⟨51074513385397250424041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8716716951107797405702997 51074513385397250424041)
              ·
                rfl

theorem cell19_503553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 9].length) (baseStart_503553 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_503553 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_503553 prefixEnd_503553 := by exact prefixLift 503553
  have htrace : WordTrace (prefixWord ++ tailWord_503553) baseStart_503553 baseEnd_503553 := by
    simpa [prefixWord, tailWord_503553, baseEnd_503553] using wordTrace_append hprefix tailTrace_503553
  have hstable : (prefixWord ++ tailWord_503553).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503553).length < 2 ^ (prefixWord ++ tailWord_503553).sum := by decide
  have hdescent : baseEnd_503553 < baseStart_503553 := by decide
  rcases family_descends (prefixWord ++ tailWord_503553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503610 : List Nat := [3, 1, 1, 1, 5, 8]
def baseStart_503610 : Nat := 118140960795 + 503610 * 2 ^ 59
def prefixEnd_503610 : Nat := 4983230072969 + 3 ^ 40 * 503610 * 2
def baseEnd_503610 : Nat := 17026764932403612000589

theorem tailTrace_503610 : CollatzResearch.WordTrace tailWord_503610 prefixEnd_503610 17026764932403612000589 := by
  unfold tailWord_503610
  simp only [CollatzResearch.WordTrace]
  refine ⟨4592041426378613646381071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12245443803676303057016189 4592041426378613646381071)
  ·
    refine ⟨6888062139567920469571607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4592041426378613646381071 6888062139567920469571607)
    ·
      refine ⟨10332093209351880704357411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6888062139567920469571607 10332093209351880704357411)
      ·
        refine ⟨15498139814027821056536117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10332093209351880704357411 15498139814027821056536117)
        ·
          refine ⟨1452950607565108224050261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15498139814027821056536117 1452950607565108224050261)
          ·
            refine ⟨17026764932403612000589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1452950607565108224050261 17026764932403612000589)
            ·
              rfl

theorem cell19_503610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 8].length) (baseStart_503610 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_503610 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_503610 prefixEnd_503610 := by exact prefixLift 503610
  have htrace : WordTrace (prefixWord ++ tailWord_503610) baseStart_503610 baseEnd_503610 := by
    simpa [prefixWord, tailWord_503610, baseEnd_503610] using wordTrace_append hprefix tailTrace_503610
  have hstable : (prefixWord ++ tailWord_503610).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503610).length < 2 ^ (prefixWord ++ tailWord_503610).sum := by decide
  have hdescent : baseEnd_503610 < baseStart_503610 := by decide
  rcases family_descends (prefixWord ++ tailWord_503610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503703 : List Nat := [1, 1, 3, 3, 1, 3, 4, 3]
def baseStart_503703 : Nat := 118140960795 + 503703 * 2 ^ 59
def prefixEnd_503703 : Nat := 4983230072969 + 3 ^ 40 * 503703 * 2
def baseEnd_503703 : Nat := 153269182881035847938381

theorem tailTrace_503703 : CollatzResearch.WordTrace tailWord_503703 prefixEnd_503703 153269182881035847938381 := by
  unfold tailWord_503703
  simp only [CollatzResearch.WordTrace]
  refine ⟨18371557694177531468659763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12247705129451687645773175 18371557694177531468659763)
  ·
    refine ⟨27557336541266297202989645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18371557694177531468659763 27557336541266297202989645)
    ·
      refine ⟨10334001202974861451121117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27557336541266297202989645 10334001202974861451121117)
      ·
        refine ⟨3875250451115573044170419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10334001202974861451121117 3875250451115573044170419)
        ·
          refine ⟨5812875676673359566255629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3875250451115573044170419 5812875676673359566255629)
          ·
            refine ⟨2179828378752509837345861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5812875676673359566255629 2179828378752509837345861)
            ·
              refine ⟨408717821016095594502349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2179828378752509837345861 408717821016095594502349)
              ·
                refine ⟨153269182881035847938381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 408717821016095594502349 153269182881035847938381)
                ·
                  rfl

theorem cell19_503703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 4, 3].length) (baseStart_503703 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_503703 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_503703 prefixEnd_503703 := by exact prefixLift 503703
  have htrace : WordTrace (prefixWord ++ tailWord_503703) baseStart_503703 baseEnd_503703 := by
    simpa [prefixWord, tailWord_503703, baseEnd_503703] using wordTrace_append hprefix tailTrace_503703
  have hstable : (prefixWord ++ tailWord_503703).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503703).length < 2 ^ (prefixWord ++ tailWord_503703).sum := by decide
  have hdescent : baseEnd_503703 < baseStart_503703 := by decide
  rcases family_descends (prefixWord ++ tailWord_503703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503741 : List Nat := [1, 4, 1, 2, 3, 2, 2, 4]
def baseStart_503741 : Nat := 118140960795 + 503741 * 2 ^ 59
def prefixEnd_503741 : Nat := 4983230072969 + 3 ^ 40 * 503741 * 2
def baseEnd_503741 : Nat := 153280745704663019093833

theorem tailTrace_503741 : CollatzResearch.WordTrace tailWord_503741 prefixEnd_503741 153280745704663019093833 := by
  unfold tailWord_503741
  simp only [CollatzResearch.WordTrace]
  refine ⟨18372943668039863958543077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12248629112026575972362051 18372943668039863958543077)
  ·
    refine ⟨3444926937757474492226827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18372943668039863958543077 3444926937757474492226827)
    ·
      refine ⟨5167390406636211738340241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3444926937757474492226827 5167390406636211738340241)
      ·
        refine ⟨3875542804977158803755181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5167390406636211738340241 3875542804977158803755181)
        ·
          refine ⟨1453328551866434551408193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3875542804977158803755181 1453328551866434551408193)
          ·
            refine ⟨1089996413899825913556145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1453328551866434551408193 1089996413899825913556145)
            ·
              refine ⟨817497310424869435167109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1089996413899825913556145 817497310424869435167109)
              ·
                refine ⟨153280745704663019093833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 817497310424869435167109 153280745704663019093833)
                ·
                  rfl

theorem cell19_503741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2, 4].length) (baseStart_503741 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_503741 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_503741 prefixEnd_503741 := by exact prefixLift 503741
  have htrace : WordTrace (prefixWord ++ tailWord_503741) baseStart_503741 baseEnd_503741 := by
    simpa [prefixWord, tailWord_503741, baseEnd_503741] using wordTrace_append hprefix tailTrace_503741
  have hstable : (prefixWord ++ tailWord_503741).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503741).length < 2 ^ (prefixWord ++ tailWord_503741).sum := by decide
  have hdescent : baseEnd_503741 < baseStart_503741 := by decide
  rcases family_descends (prefixWord ++ tailWord_503741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503743 : List Nat := [1, 1, 2, 2, 2, 1, 6, 4]
def baseStart_503743 : Nat := 118140960795 + 503743 * 2 ^ 59
def prefixEnd_503743 : Nat := 4983230072969 + 3 ^ 40 * 503743 * 2
def baseEnd_503743 : Nat := 153281354274327607049383

theorem tailTrace_503743 : CollatzResearch.WordTrace tailWord_503743 prefixEnd_503743 153281354274327607049383 := by
  unfold tailWord_503743
  simp only [CollatzResearch.WordTrace]
  refine ⟨18373016614032618300115883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12248677742688412200077255 18373016614032618300115883)
  ·
    refine ⟨27559524921048927450173825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18373016614032618300115883 27559524921048927450173825)
    ·
      refine ⟨20669643690786695587630369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27559524921048927450173825 20669643690786695587630369)
      ·
        refine ⟨15502232768090021690722777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20669643690786695587630369 15502232768090021690722777)
        ·
          refine ⟨11626674576067516268042083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15502232768090021690722777 11626674576067516268042083)
          ·
            refine ⟨17440011864101274402063125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11626674576067516268042083 17440011864101274402063125)
            ·
              refine ⟨817500556129747237596709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 17440011864101274402063125 817500556129747237596709)
              ·
                refine ⟨153281354274327607049383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 817500556129747237596709 153281354274327607049383)
                ·
                  rfl

theorem cell19_503743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6, 4].length) (baseStart_503743 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_503743 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_503743 prefixEnd_503743 := by exact prefixLift 503743
  have htrace : WordTrace (prefixWord ++ tailWord_503743) baseStart_503743 baseEnd_503743 := by
    simpa [prefixWord, tailWord_503743, baseEnd_503743] using wordTrace_append hprefix tailTrace_503743
  have hstable : (prefixWord ++ tailWord_503743).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503743).length < 2 ^ (prefixWord ++ tailWord_503743).sum := by decide
  have hdescent : baseEnd_503743 < baseStart_503743 := by decide
  rcases family_descends (prefixWord ++ tailWord_503743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503800 : List Nat := [2, 1, 2, 1, 1, 3, 5, 4]
def baseStart_503800 : Nat := 118140960795 + 503800 * 2 ^ 59
def prefixEnd_503800 : Nat := 4983230072969 + 3 ^ 40 * 503800 * 2
def baseEnd_503800 : Nat := 153298698509768363782561

theorem tailTrace_503800 : CollatzResearch.WordTrace tailWord_503800 prefixEnd_503800 153298698509768363782561 := by
  unfold tailWord_503800
  simp only [CollatzResearch.WordTrace]
  refine ⟨9187547787413058517470427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12250063716550744689960569 9187547787413058517470427)
  ·
    refine ⟨13781321681119587776205641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9187547787413058517470427 13781321681119587776205641)
    ·
      refine ⟨10335991260839690832154231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13781321681119587776205641 10335991260839690832154231)
      ·
        refine ⟨15503986891259536248231347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10335991260839690832154231 15503986891259536248231347)
        ·
          refine ⟨23255980336889304372347021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15503986891259536248231347 23255980336889304372347021)
          ·
            refine ⟨8720992626333489139630133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23255980336889304372347021 8720992626333489139630133)
            ·
              refine ⟨817593058718764606840325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8720992626333489139630133 817593058718764606840325)
              ·
                refine ⟨153298698509768363782561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 817593058718764606840325 153298698509768363782561)
                ·
                  rfl

theorem cell19_503800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5, 4].length) (baseStart_503800 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_503800 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_503800 prefixEnd_503800 := by exact prefixLift 503800
  have htrace : WordTrace (prefixWord ++ tailWord_503800) baseStart_503800 baseEnd_503800 := by
    simpa [prefixWord, tailWord_503800, baseEnd_503800] using wordTrace_append hprefix tailTrace_503800
  have hstable : (prefixWord ++ tailWord_503800).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503800).length < 2 ^ (prefixWord ++ tailWord_503800).sum := by decide
  have hdescent : baseEnd_503800 < baseStart_503800 := by decide
  rcases family_descends (prefixWord ++ tailWord_503800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503870 : List Nat := [4, 2, 1, 3, 2, 2, 2, 3]
def baseStart_503870 : Nat := 118140960795 + 503870 * 2 ^ 59
def prefixEnd_503870 : Nat := 4983230072969 + 3 ^ 40 * 503870 * 2
def baseEnd_503870 : Nat := 153319998448028942226815

theorem tailTrace_503870 : CollatzResearch.WordTrace tailWord_503870 prefixEnd_503870 153319998448028942226815 := by
  unfold tailWord_503870
  simp only [CollatzResearch.WordTrace]
  refine ⟨2297206085571564873748633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12251765789715012659992709 2297206085571564873748633)
  ·
    refine ⟨1722904564178673655311475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2297206085571564873748633 1722904564178673655311475)
    ·
      refine ⟨2584356846268010482967213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1722904564178673655311475 2584356846268010482967213)
      ·
        refine ⟨969133817350503931112705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2584356846268010482967213 969133817350503931112705)
        ·
          refine ⟨726850363012877948334529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 969133817350503931112705 726850363012877948334529)
          ·
            refine ⟨545137772259658461250897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 726850363012877948334529 545137772259658461250897)
            ·
              refine ⟨408853329194743845938173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 545137772259658461250897 408853329194743845938173)
              ·
                refine ⟨153319998448028942226815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 408853329194743845938173 153319998448028942226815)
                ·
                  rfl

theorem cell19_503870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 2, 3].length) (baseStart_503870 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_503870 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_503870 prefixEnd_503870 := by exact prefixLift 503870
  have htrace : WordTrace (prefixWord ++ tailWord_503870) baseStart_503870 baseEnd_503870 := by
    simpa [prefixWord, tailWord_503870, baseEnd_503870] using wordTrace_append hprefix tailTrace_503870
  have hstable : (prefixWord ++ tailWord_503870).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503870).length < 2 ^ (prefixWord ++ tailWord_503870).sum := by decide
  have hdescent : baseEnd_503870 < baseStart_503870 := by decide
  rcases family_descends (prefixWord ++ tailWord_503870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503933 : List Nat := [1, 4, 1, 1, 3, 2, 2, 5]
def baseStart_503933 : Nat := 118140960795 + 503933 * 2 ^ 59
def prefixEnd_503933 : Nat := 4983230072969 + 3 ^ 40 * 503933 * 2
def baseEnd_503933 : Nat := 153339168392463462826643

theorem tailTrace_503933 : CollatzResearch.WordTrace tailWord_503933 prefixEnd_503933 153339168392463462826643 := by
  unfold tailWord_503933
  simp only [CollatzResearch.WordTrace]
  refine ⟨18379946483344280749532453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12253297655562853833021635 18379946483344280749532453)
  ·
    refine ⟨3446239965627052640537335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18379946483344280749532453 3446239965627052640537335)
    ·
      refine ⟨5169359948440578960806003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3446239965627052640537335 5169359948440578960806003)
      ·
        refine ⟨7754039922660868441209005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5169359948440578960806003 7754039922660868441209005)
        ·
          refine ⟨2907764970997825665453377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7754039922660868441209005 2907764970997825665453377)
          ·
            refine ⟨2180823728248369249090033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2907764970997825665453377 2180823728248369249090033)
            ·
              refine ⟨1635617796186276936817525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2180823728248369249090033 1635617796186276936817525)
              ·
                refine ⟨153339168392463462826643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1635617796186276936817525 153339168392463462826643)
                ·
                  rfl

theorem cell19_503933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 5].length) (baseStart_503933 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_503933 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_503933 prefixEnd_503933 := by exact prefixLift 503933
  have htrace : WordTrace (prefixWord ++ tailWord_503933) baseStart_503933 baseEnd_503933 := by
    simpa [prefixWord, tailWord_503933, baseEnd_503933] using wordTrace_append hprefix tailTrace_503933
  have hstable : (prefixWord ++ tailWord_503933).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503933).length < 2 ^ (prefixWord ++ tailWord_503933).sum := by decide
  have hdescent : baseEnd_503933 < baseStart_503933 := by decide
  rcases family_descends (prefixWord ++ tailWord_503933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503950 : List Nat := [4, 1, 1, 3, 4, 6]
def baseStart_503950 : Nat := 118140960795 + 503950 * 2 ^ 59
def prefixEnd_503950 : Nat := 4983230072969 + 3 ^ 40 * 503950 * 2
def baseEnd_503950 : Nat := 17038260137179162272091

theorem tailTrace_503950 : CollatzResearch.WordTrace tailWord_503950 prefixEnd_503950 17038260137179162272091 := by
  unfold tailWord_503950
  simp only [CollatzResearch.WordTrace]
  refine ⟨2297570815535336581612663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12253711016188461768600869 2297570815535336581612663)
  ·
    refine ⟨3446356223303004872418995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2297570815535336581612663 3446356223303004872418995)
    ·
      refine ⟨5169534334954507308628493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3446356223303004872418995 5169534334954507308628493)
      ·
        refine ⟨1938575375607940240735685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5169534334954507308628493 1938575375607940240735685)
        ·
          refine ⟨363482882926488795137941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1938575375607940240735685 363482882926488795137941)
          ·
            refine ⟨17038260137179162272091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 363482882926488795137941 17038260137179162272091)
            ·
              rfl

theorem cell19_503950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 6].length) (baseStart_503950 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_503950 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_503950 prefixEnd_503950 := by exact prefixLift 503950
  have htrace : WordTrace (prefixWord ++ tailWord_503950) baseStart_503950 baseEnd_503950 := by
    simpa [prefixWord, tailWord_503950, baseEnd_503950] using wordTrace_append hprefix tailTrace_503950
  have hstable : (prefixWord ++ tailWord_503950).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503950).length < 2 ^ (prefixWord ++ tailWord_503950).sum := by decide
  have hdescent : baseEnd_503950 < baseStart_503950 := by decide
  rcases family_descends (prefixWord ++ tailWord_503950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503969 : List Nat := [1, 2, 3, 3, 1, 4, 1, 4]
def baseStart_503969 : Nat := 118140960795 + 503969 * 2 ^ 59
def prefixEnd_503969 : Nat := 4983230072969 + 3 ^ 40 * 503969 * 2
def baseEnd_503969 : Nat := 153350122646426046026545

theorem tailTrace_503969 : CollatzResearch.WordTrace tailWord_503969 prefixEnd_503969 153350122646426046026545 := by
  unfold tailWord_503969
  simp only [CollatzResearch.WordTrace]
  refine ⟨18381259511213858897842961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12254173007475905931895307 18381259511213858897842961)
  ·
    refine ⟨13785944633410394173382221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18381259511213858897842961 13785944633410394173382221)
    ·
      refine ⟨5169729237528897815018333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13785944633410394173382221 5169729237528897815018333)
      ·
        refine ⟨1938648464073336680631875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5169729237528897815018333 1938648464073336680631875)
        ·
          refine ⟨2907972696110005020947813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1938648464073336680631875 2907972696110005020947813)
          ·
            refine ⟨545244880520625941427715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2907972696110005020947813 545244880520625941427715)
            ·
              refine ⟨817867320780938912141573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 545244880520625941427715 817867320780938912141573)
              ·
                refine ⟨153350122646426046026545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 817867320780938912141573 153350122646426046026545)
                ·
                  rfl

theorem cell19_503969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 1, 4].length) (baseStart_503969 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_503969 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_503969 prefixEnd_503969 := by exact prefixLift 503969
  have htrace : WordTrace (prefixWord ++ tailWord_503969) baseStart_503969 baseEnd_503969 := by
    simpa [prefixWord, tailWord_503969, baseEnd_503969] using wordTrace_append hprefix tailTrace_503969
  have hstable : (prefixWord ++ tailWord_503969).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503969).length < 2 ^ (prefixWord ++ tailWord_503969).sum := by decide
  have hdescent : baseEnd_503969 < baseStart_503969 := by decide
  rcases family_descends (prefixWord ++ tailWord_503969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504011 : List Nat := [1, 1, 1, 1, 3, 2, 10]
def baseStart_504011 : Nat := 118140960795 + 504011 * 2 ^ 59
def prefixEnd_504011 : Nat := 4983230072969 + 3 ^ 40 * 504011 * 2
def baseEnd_504011 : Nat := 51120967536460797697699

theorem tailTrace_504011 : CollatzResearch.WordTrace tailWord_504011 prefixEnd_504011 51120967536460797697699 := by
  unfold tailWord_504011
  simp only [CollatzResearch.WordTrace]
  refine ⟨18382791377061700070871887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12255194251374466713914591 18382791377061700070871887)
  ·
    refine ⟨27574187065592550106307831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18382791377061700070871887 27574187065592550106307831)
    ·
      refine ⟨41361280598388825159461747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27574187065592550106307831 41361280598388825159461747)
      ·
        refine ⟨62041920897583237739192621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41361280598388825159461747 62041920897583237739192621)
        ·
          refine ⟨23265720336593714152197233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62041920897583237739192621 23265720336593714152197233)
          ·
            refine ⟨17449290252445285614147925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23265720336593714152197233 17449290252445285614147925)
            ·
              refine ⟨51120967536460797697699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17449290252445285614147925 51120967536460797697699)
              ·
                rfl

theorem cell19_504011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 10].length) (baseStart_504011 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_504011 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_504011 prefixEnd_504011 := by exact prefixLift 504011
  have htrace : WordTrace (prefixWord ++ tailWord_504011) baseStart_504011 baseEnd_504011 := by
    simpa [prefixWord, tailWord_504011, baseEnd_504011] using wordTrace_append hprefix tailTrace_504011
  have hstable : (prefixWord ++ tailWord_504011).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504011).length < 2 ^ (prefixWord ++ tailWord_504011).sum := by decide
  have hdescent : baseEnd_504011 < baseStart_504011 := by decide
  rcases family_descends (prefixWord ++ tailWord_504011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504045 : List Nat := [1, 5, 1, 2, 3, 1, 1, 5]
def baseStart_504045 : Nat := 118140960795 + 504045 * 2 ^ 59
def prefixEnd_504045 : Nat := 4983230072969 + 3 ^ 40 * 504045 * 2
def baseEnd_504045 : Nat := 153373248293680388337449

theorem tailTrace_504045 : CollatzResearch.WordTrace tailWord_504045 prefixEnd_504045 153373248293680388337449 := by
  unfold tailWord_504045
  simp only [CollatzResearch.WordTrace]
  refine ⟨18384031458938523877609589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12256020972625682585073059 18384031458938523877609589)
  ·
    refine ⟨1723502949275486613525899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18384031458938523877609589 1723502949275486613525899)
    ·
      refine ⟨2585254423913229920288849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1723502949275486613525899 2585254423913229920288849)
      ·
        refine ⟨1938940817934922440216637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2585254423913229920288849 1938940817934922440216637)
        ·
          refine ⟨727102806725595915081239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1938940817934922440216637 727102806725595915081239)
          ·
            refine ⟨1090654210088393872621859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 727102806725595915081239 1090654210088393872621859)
            ·
              refine ⟨1635981315132590808932789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1090654210088393872621859 1635981315132590808932789)
              ·
                refine ⟨153373248293680388337449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1635981315132590808932789 153373248293680388337449)
                ·
                  rfl

theorem cell19_504045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 5].length) (baseStart_504045 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_504045 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_504045 prefixEnd_504045 := by exact prefixLift 504045
  have htrace : WordTrace (prefixWord ++ tailWord_504045) baseStart_504045 baseEnd_504045 := by
    simpa [prefixWord, tailWord_504045, baseEnd_504045] using wordTrace_append hprefix tailTrace_504045
  have hstable : (prefixWord ++ tailWord_504045).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504045).length < 2 ^ (prefixWord ++ tailWord_504045).sum := by decide
  have hdescent : baseEnd_504045 < baseStart_504045 := by decide
  rcases family_descends (prefixWord ++ tailWord_504045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504047 : List Nat := [1, 1, 2, 1, 6, 2, 1, 5]
def baseStart_504047 : Nat := 118140960795 + 504047 * 2 ^ 59
def prefixEnd_504047 : Nat := 4983230072969 + 3 ^ 40 * 504047 * 2
def baseEnd_504047 : Nat := 153373856863344976292999

theorem tailTrace_504047 : CollatzResearch.WordTrace tailWord_504047 prefixEnd_504047 153373856863344976292999 := by
  unfold tailWord_504047
  simp only [CollatzResearch.WordTrace]
  refine ⟨18384104404931278219182395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12256069603287518812788263 18384104404931278219182395)
  ·
    refine ⟨27576156607396917328773593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18384104404931278219182395 27576156607396917328773593)
    ·
      refine ⟨20682117455547687996580195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27576156607396917328773593 20682117455547687996580195)
      ·
        refine ⟨31023176183321531994870293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20682117455547687996580195 31023176183321531994870293)
        ·
          refine ⟨1454211383593196812259545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 31023176183321531994870293 1454211383593196812259545)
          ·
            refine ⟨1090658537694897609194659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1454211383593196812259545 1090658537694897609194659)
            ·
              refine ⟨1635987806542346413791989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1090658537694897609194659 1635987806542346413791989)
              ·
                refine ⟨153373856863344976292999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1635987806542346413791989 153373856863344976292999)
                ·
                  rfl

theorem cell19_504047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 5].length) (baseStart_504047 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_504047 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_504047 prefixEnd_504047 := by exact prefixLift 504047
  have htrace : WordTrace (prefixWord ++ tailWord_504047) baseStart_504047 baseEnd_504047 := by
    simpa [prefixWord, tailWord_504047, baseEnd_504047] using wordTrace_append hprefix tailTrace_504047
  have hstable : (prefixWord ++ tailWord_504047).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504047).length < 2 ^ (prefixWord ++ tailWord_504047).sum := by decide
  have hdescent : baseEnd_504047 < baseStart_504047 := by decide
  rcases family_descends (prefixWord ++ tailWord_504047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504125 : List Nat := [1, 4, 1, 13]
def baseStart_504125 : Nat := 118140960795 + 504125 * 2 ^ 59
def prefixEnd_504125 : Nat := 4983230072969 + 3 ^ 40 * 504125 * 2
def baseEnd_504125 : Nat := 1893797420743998846413

theorem tailTrace_504125 : CollatzResearch.WordTrace tailWord_504125 prefixEnd_504125 1893797420743998846413 := by
  unfold tailWord_504125
  simp only [CollatzResearch.WordTrace]
  refine ⟨18386949298648697540521829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12257966199099131693681219 18386949298648697540521829)
  ·
    refine ⟨3447552993496630788847843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18386949298648697540521829 3447552993496630788847843)
    ·
      refine ⟨5171329490244946183271765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3447552993496630788847843 5171329490244946183271765)
      ·
        refine ⟨1893797420743998846413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 5171329490244946183271765 1893797420743998846413)
        ·
          rfl

theorem cell19_504125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 13].length) (baseStart_504125 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_504125 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_504125 prefixEnd_504125 := by exact prefixLift 504125
  have htrace : WordTrace (prefixWord ++ tailWord_504125) baseStart_504125 baseEnd_504125 := by
    simpa [prefixWord, tailWord_504125, baseEnd_504125] using wordTrace_append hprefix tailTrace_504125
  have hstable : (prefixWord ++ tailWord_504125).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504125).length < 2 ^ (prefixWord ++ tailWord_504125).sum := by decide
  have hdescent : baseEnd_504125 < baseStart_504125 := by decide
  rcases family_descends (prefixWord ++ tailWord_504125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504212 : List Nat := [2, 4, 2, 1, 4, 1, 2, 3]
def baseStart_504212 : Nat := 118140960795 + 504212 * 2 ^ 59
def prefixEnd_504212 : Nat := 4983230072969 + 3 ^ 40 * 504212 * 2
def baseEnd_504212 : Nat := 153424063860673482625883

theorem tailTrace_504212 : CollatzResearch.WordTrace tailWord_504212 prefixEnd_504212 153424063860673482625883 := by
  unfold tailWord_504212
  simp only [CollatzResearch.WordTrace]
  refine ⟨9195061224666755699469445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12260081632889007599292593 9195061224666755699469445)
  ·
    refine ⟨1724073979625016693650521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9195061224666755699469445 1724073979625016693650521)
    ·
      refine ⟨1293055484718762520237891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1724073979625016693650521 1293055484718762520237891)
      ·
        refine ⟨1939583227078143780356837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1293055484718762520237891 1939583227078143780356837)
        ·
          refine ⟨363671855077151958816907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1939583227078143780356837 363671855077151958816907)
          ·
            refine ⟨545507782615727938225361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 363671855077151958816907 545507782615727938225361)
            ·
              refine ⟨409130836961795953669021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 545507782615727938225361 409130836961795953669021)
              ·
                refine ⟨153424063860673482625883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 409130836961795953669021 153424063860673482625883)
                ·
                  rfl

theorem cell19_504212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 2, 3].length) (baseStart_504212 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_504212 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_504212 prefixEnd_504212 := by exact prefixLift 504212
  have htrace : WordTrace (prefixWord ++ tailWord_504212) baseStart_504212 baseEnd_504212 := by
    simpa [prefixWord, tailWord_504212, baseEnd_504212] using wordTrace_append hprefix tailTrace_504212
  have hstable : (prefixWord ++ tailWord_504212).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504212).length < 2 ^ (prefixWord ++ tailWord_504212).sum := by decide
  have hdescent : baseEnd_504212 < baseStart_504212 := by decide
  rcases family_descends (prefixWord ++ tailWord_504212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504216 : List Nat := [2, 1, 2, 5, 1, 1, 4, 3]
def baseStart_504216 : Nat := 118140960795 + 504216 * 2 ^ 59
def prefixEnd_504216 : Nat := 4983230072969 + 3 ^ 40 * 504216 * 2
def baseEnd_504216 : Nat := 153425281000002658536983

theorem tailTrace_504216 : CollatzResearch.WordTrace tailWord_504216 prefixEnd_504216 153425281000002658536983 := by
  unfold tailWord_504216
  simp only [CollatzResearch.WordTrace]
  refine ⟨9195134170659510041042251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12260178894212680054723001 9195134170659510041042251)
  ·
    refine ⟨13792701255989265061563377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9195134170659510041042251 13792701255989265061563377)
    ·
      refine ⟨10344525941991948796172533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13792701255989265061563377 10344525941991948796172533)
      ·
        refine ⟨969799307061745199641175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10344525941991948796172533 969799307061745199641175)
        ·
          refine ⟨1454698960592617799461763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 969799307061745199641175 1454698960592617799461763)
          ·
            refine ⟨2182048440888926699192645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1454698960592617799461763 2182048440888926699192645)
            ·
              refine ⟨409134082666673756098621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2182048440888926699192645 409134082666673756098621)
              ·
                refine ⟨153425281000002658536983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 409134082666673756098621 153425281000002658536983)
                ·
                  rfl

theorem cell19_504216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 4, 3].length) (baseStart_504216 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_504216 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_504216 prefixEnd_504216 := by exact prefixLift 504216
  have htrace : WordTrace (prefixWord ++ tailWord_504216) baseStart_504216 baseEnd_504216 := by
    simpa [prefixWord, tailWord_504216, baseEnd_504216] using wordTrace_append hprefix tailTrace_504216
  have hstable : (prefixWord ++ tailWord_504216).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504216).length < 2 ^ (prefixWord ++ tailWord_504216).sum := by decide
  have hdescent : baseEnd_504216 < baseStart_504216 := by decide
  rcases family_descends (prefixWord ++ tailWord_504216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504218 : List Nat := [3, 1, 1, 4, 1, 3, 1, 5]
def baseStart_504218 : Nat := 118140960795 + 504218 * 2 ^ 59
def prefixEnd_504218 : Nat := 4983230072969 + 3 ^ 40 * 504218 * 2
def baseEnd_504218 : Nat := 153425889569667246492533

theorem tailTrace_504218 : CollatzResearch.WordTrace tailWord_504218 prefixEnd_504218 153425889569667246492533 := by
  unfold tailWord_504218
  simp only [CollatzResearch.WordTrace]
  refine ⟨4597585321827943605914327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12260227524874516282438205 4597585321827943605914327)
  ·
    refine ⟨6896377982741915408871491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4597585321827943605914327 6896377982741915408871491)
    ·
      refine ⟨10344566974112873113307237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6896377982741915408871491 10344566974112873113307237)
      ·
        refine ⟨1939606307646163708745107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10344566974112873113307237 1939606307646163708745107)
        ·
          refine ⟨2909409461469245563117661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1939606307646163708745107 2909409461469245563117661)
          ·
            refine ⟨1091028548050967086169123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2909409461469245563117661 1091028548050967086169123)
            ·
              refine ⟨1636542822076450629253685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1091028548050967086169123 1636542822076450629253685)
              ·
                refine ⟨153425889569667246492533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1636542822076450629253685 153425889569667246492533)
                ·
                  rfl

theorem cell19_504218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 5].length) (baseStart_504218 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_504218 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_504218 prefixEnd_504218 := by exact prefixLift 504218
  have htrace : WordTrace (prefixWord ++ tailWord_504218) baseStart_504218 baseEnd_504218 := by
    simpa [prefixWord, tailWord_504218, baseEnd_504218] using wordTrace_append hprefix tailTrace_504218
  have hstable : (prefixWord ++ tailWord_504218).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504218).length < 2 ^ (prefixWord ++ tailWord_504218).sum := by decide
  have hdescent : baseEnd_504218 < baseStart_504218 := by decide
  rcases family_descends (prefixWord ++ tailWord_504218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504290 : List Nat := [3, 3, 3, 2, 2, 6]
def baseStart_504290 : Nat := 118140960795 + 504290 * 2 ^ 59
def prefixEnd_504290 : Nat := 4983230072969 + 3 ^ 40 * 504290 * 2
def baseEnd_504290 : Nat := 17049755341954712543593

theorem tailTrace_504290 : CollatzResearch.WordTrace tailWord_504290 prefixEnd_504290 17049755341954712543593 := by
  unfold tailWord_504290
  simp only [CollatzResearch.WordTrace]
  refine ⟨4598241835762732680069581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12261978228700620480185549 4598241835762732680069581)
  ·
    refine ⟨1724340688411024755026093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4598241835762732680069581 1724340688411024755026093)
    ·
      refine ⟨646627758154134283134785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1724340688411024755026093 646627758154134283134785)
      ·
        refine ⟨484970818615600712351089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 646627758154134283134785 484970818615600712351089)
        ·
          refine ⟨363728113961700534263317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 484970818615600712351089 363728113961700534263317)
          ·
            refine ⟨17049755341954712543593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 363728113961700534263317 17049755341954712543593)
            ·
              rfl

theorem cell19_504290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 6].length) (baseStart_504290 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_504290 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_504290 prefixEnd_504290 := by exact prefixLift 504290
  have htrace : WordTrace (prefixWord ++ tailWord_504290) baseStart_504290 baseEnd_504290 := by
    simpa [prefixWord, tailWord_504290, baseEnd_504290] using wordTrace_append hprefix tailTrace_504290
  have hstable : (prefixWord ++ tailWord_504290).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504290).length < 2 ^ (prefixWord ++ tailWord_504290).sum := by decide
  have hdescent : baseEnd_504290 < baseStart_504290 := by decide
  rcases family_descends (prefixWord ++ tailWord_504290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504296 : List Nat := [2, 1, 4, 1, 1, 10]
def baseStart_504296 : Nat := 118140960795 + 504296 * 2 ^ 59
def prefixEnd_504296 : Nat := 4983230072969 + 3 ^ 40 * 504296 * 2
def baseEnd_504296 : Nat := 17049958198509575195443

theorem tailTrace_504296 : CollatzResearch.WordTrace tailWord_504296 prefixEnd_504296 17049958198509575195443 := by
  unfold tailWord_504296
  simp only [CollatzResearch.WordTrace]
  refine ⟨9196593090514596872498371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12262124120686129163331161 9196593090514596872498371)
  ·
    refine ⟨13794889635771895308747557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9196593090514596872498371 13794889635771895308747557)
    ·
      refine ⟨2586541806707230370390167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13794889635771895308747557 2586541806707230370390167)
      ·
        refine ⟨3879812710060845555585251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2586541806707230370390167 3879812710060845555585251)
        ·
          refine ⟨5819719065091268333377877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3879812710060845555585251 5819719065091268333377877)
          ·
            refine ⟨17049958198509575195443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5819719065091268333377877 17049958198509575195443)
            ·
              rfl

theorem cell19_504296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 10].length) (baseStart_504296 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_504296 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_504296 prefixEnd_504296 := by exact prefixLift 504296
  have htrace : WordTrace (prefixWord ++ tailWord_504296) baseStart_504296 baseEnd_504296 := by
    simpa [prefixWord, tailWord_504296, baseEnd_504296] using wordTrace_append hprefix tailTrace_504296
  have hstable : (prefixWord ++ tailWord_504296).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504296).length < 2 ^ (prefixWord ++ tailWord_504296).sum := by decide
  have hdescent : baseEnd_504296 < baseStart_504296 := by decide
  rcases family_descends (prefixWord ++ tailWord_504296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504309 : List Nat := [1, 3, 5, 1, 2, 2, 1, 4]
def baseStart_504309 : Nat := 118140960795 + 504309 * 2 ^ 59
def prefixEnd_504309 : Nat := 4983230072969 + 3 ^ 40 * 504309 * 2
def baseEnd_504309 : Nat := 153453579489405998470063

theorem tailTrace_504309 : CollatzResearch.WordTrace tailWord_504309 prefixEnd_504309 153453579489405998470063 := by
  unfold tailWord_504309
  simp only [CollatzResearch.WordTrace]
  refine ⟨18393660329982096965219981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12262440219988064643479987 18393660329982096965219981)
  ·
    refine ⟨6897622623743286361957493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18393660329982096965219981 6897622623743286361957493)
    ·
      refine ⟨646652120975933096433515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6897622623743286361957493 646652120975933096433515)
      ·
        refine ⟨969978181463899644650273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 646652120975933096433515 969978181463899644650273)
        ·
          refine ⟨727483636097924733487705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 969978181463899644650273 727483636097924733487705)
          ·
            refine ⟨545612727073443550115779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 727483636097924733487705 545612727073443550115779)
            ·
              refine ⟨818419090610165325173669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 545612727073443550115779 818419090610165325173669)
              ·
                refine ⟨153453579489405998470063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 818419090610165325173669 153453579489405998470063)
                ·
                  rfl

theorem cell19_504309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 1, 4].length) (baseStart_504309 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_504309 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_504309 prefixEnd_504309 := by exact prefixLift 504309
  have htrace : WordTrace (prefixWord ++ tailWord_504309) baseStart_504309 baseEnd_504309 := by
    simpa [prefixWord, tailWord_504309, baseEnd_504309] using wordTrace_append hprefix tailTrace_504309
  have hstable : (prefixWord ++ tailWord_504309).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504309).length < 2 ^ (prefixWord ++ tailWord_504309).sum := by decide
  have hdescent : baseEnd_504309 < baseStart_504309 := by decide
  rcases family_descends (prefixWord ++ tailWord_504309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504353 : List Nat := [1, 2, 3, 2, 2, 1, 8]
def baseStart_504353 : Nat := 118140960795 + 504353 * 2 ^ 59
def prefixEnd_504353 : Nat := 4983230072969 + 3 ^ 40 * 504353 * 2
def baseEnd_504353 : Nat := 51155656007342311164055

theorem tailTrace_504353 : CollatzResearch.WordTrace tailWord_504353 prefixEnd_504353 51155656007342311164055 := by
  unfold tailWord_504353
  simp only [CollatzResearch.WordTrace]
  refine ⟨18395265141822692479821713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12263510094548461653214475 18395265141822692479821713)
  ·
    refine ⟨13796448856367019359866285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18395265141822692479821713 13796448856367019359866285)
    ·
      refine ⟨5173668321137632259949857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13796448856367019359866285 5173668321137632259949857)
      ·
        refine ⟨3880251240853224194962393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5173668321137632259949857 3880251240853224194962393)
        ·
          refine ⟨2910188430639918146221795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3880251240853224194962393 2910188430639918146221795)
          ·
            refine ⟨4365282645959877219332693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2910188430639918146221795 4365282645959877219332693)
            ·
              refine ⟨51155656007342311164055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4365282645959877219332693 51155656007342311164055)
              ·
                rfl

theorem cell19_504353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 8].length) (baseStart_504353 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_504353 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_504353 prefixEnd_504353 := by exact prefixLift 504353
  have htrace : WordTrace (prefixWord ++ tailWord_504353) baseStart_504353 baseEnd_504353 := by
    simpa [prefixWord, tailWord_504353, baseEnd_504353] using wordTrace_append hprefix tailTrace_504353
  have hstable : (prefixWord ++ tailWord_504353).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504353).length < 2 ^ (prefixWord ++ tailWord_504353).sum := by decide
  have hdescent : baseEnd_504353 < baseStart_504353 := by decide
  rcases family_descends (prefixWord ++ tailWord_504353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504389 : List Nat := [1, 3, 1, 1, 1, 5, 4, 3]
def baseStart_504389 : Nat := 118140960795 + 504389 * 2 ^ 59
def prefixEnd_504389 : Nat := 4983230072969 + 3 ^ 40 * 504389 * 2
def baseEnd_504389 : Nat := 153477922275989516692067

theorem tailTrace_504389 : CollatzResearch.WordTrace tailWord_504389 prefixEnd_504389 153477922275989516692067 := by
  unfold tailWord_504389
  simp only [CollatzResearch.WordTrace]
  refine ⟨18396578169692270628132221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12264385446461513752088147 18396578169692270628132221)
  ·
    refine ⟨6898716813634601485549583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18396578169692270628132221 6898716813634601485549583)
    ·
      refine ⟨10348075220451902228324375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6898716813634601485549583 10348075220451902228324375)
      ·
        refine ⟨15522112830677853342486563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10348075220451902228324375 15522112830677853342486563)
        ·
          refine ⟨23283169246016780013729845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15522112830677853342486563 23283169246016780013729845)
          ·
            refine ⟨2182797116814073126287173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23283169246016780013729845 2182797116814073126287173)
            ·
              refine ⟨409274459402638711178845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2182797116814073126287173 409274459402638711178845)
              ·
                refine ⟨153477922275989516692067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 409274459402638711178845 153477922275989516692067)
                ·
                  rfl

theorem cell19_504389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 4, 3].length) (baseStart_504389 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_504389 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_504389 prefixEnd_504389 := by exact prefixLift 504389
  have htrace : WordTrace (prefixWord ++ tailWord_504389) baseStart_504389 baseEnd_504389 := by
    simpa [prefixWord, tailWord_504389, baseEnd_504389] using wordTrace_append hprefix tailTrace_504389
  have hstable : (prefixWord ++ tailWord_504389).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504389).length < 2 ^ (prefixWord ++ tailWord_504389).sum := by decide
  have hdescent : baseEnd_504389 < baseStart_504389 := by decide
  rcases family_descends (prefixWord ++ tailWord_504389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504448 : List Nat := [2, 1, 1, 2, 1, 5, 2, 5]
def baseStart_504448 : Nat := 118140960795 + 504448 * 2 ^ 59
def prefixEnd_504448 : Nat := 4983230072969 + 3 ^ 40 * 504448 * 2
def baseEnd_504448 : Nat := 153495875081094861380795

theorem tailTrace_504448 : CollatzResearch.WordTrace tailWord_504448 prefixEnd_504448 153495875081094861380795 := by
  unfold tailWord_504448
  simp only [CollatzResearch.WordTrace]
  refine ⟨9199365038239261852264999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12265820050985682469686665 9199365038239261852264999)
  ·
    refine ⟨13799047557358892778397499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9199365038239261852264999 13799047557358892778397499)
    ·
      refine ⟨20698571336038339167596249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13799047557358892778397499 20698571336038339167596249)
      ·
        refine ⟨15523928502028754375697187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20698571336038339167596249 15523928502028754375697187)
        ·
          refine ⟨23285892753043131563545781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15523928502028754375697187 23285892753043131563545781)
          ·
            refine ⟨2183052445597793584082417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23285892753043131563545781 2183052445597793584082417)
            ·
              refine ⟨1637289334198345188061813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2183052445597793584082417 1637289334198345188061813)
              ·
                refine ⟨153495875081094861380795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1637289334198345188061813 153495875081094861380795)
                ·
                  rfl

theorem cell19_504448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 5].length) (baseStart_504448 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_504448 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_504448 prefixEnd_504448 := by exact prefixLift 504448
  have htrace : WordTrace (prefixWord ++ tailWord_504448) baseStart_504448 baseEnd_504448 := by
    simpa [prefixWord, tailWord_504448, baseEnd_504448] using wordTrace_append hprefix tailTrace_504448
  have hstable : (prefixWord ++ tailWord_504448).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504448).length < 2 ^ (prefixWord ++ tailWord_504448).sum := by decide
  have hdescent : baseEnd_504448 < baseStart_504448 := by decide
  rcases family_descends (prefixWord ++ tailWord_504448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504501 : List Nat := [1, 3, 3, 3, 1, 2, 3, 3]
def baseStart_504501 : Nat := 118140960795 + 504501 * 2 ^ 59
def prefixEnd_504501 : Nat := 4983230072969 + 3 ^ 40 * 504501 * 2
def baseEnd_504501 : Nat := 153512002177206442202873

theorem tailTrace_504501 : CollatzResearch.WordTrace tailWord_504501 prefixEnd_504501 153512002177206442202873 := by
  unfold tailWord_504501
  simp only [CollatzResearch.WordTrace]
  refine ⟨18400663145286513756209357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12267108763524342504139571 18400663145286513756209357)
  ·
    refine ⟨6900248679482442658578509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18400663145286513756209357 6900248679482442658578509)
    ·
      refine ⟨2587593254805915996966941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6900248679482442658578509 2587593254805915996966941)
      ·
        refine ⟨970347470552218498862603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2587593254805915996966941 970347470552218498862603)
        ·
          refine ⟨1455521205828327748293905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 970347470552218498862603 1455521205828327748293905)
          ·
            refine ⟨1091640904371245811220429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1455521205828327748293905 1091640904371245811220429)
            ·
              refine ⟨409365339139217179207661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1091640904371245811220429 409365339139217179207661)
              ·
                refine ⟨153512002177206442202873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 409365339139217179207661 153512002177206442202873)
                ·
                  rfl

theorem cell19_504501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 3, 3].length) (baseStart_504501 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_504501 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_504501 prefixEnd_504501 := by exact prefixLift 504501
  have htrace : WordTrace (prefixWord ++ tailWord_504501) baseStart_504501 baseEnd_504501 := by
    simpa [prefixWord, tailWord_504501, baseEnd_504501] using wordTrace_append hprefix tailTrace_504501
  have hstable : (prefixWord ++ tailWord_504501).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504501).length < 2 ^ (prefixWord ++ tailWord_504501).sum := by decide
  have hdescent : baseEnd_504501 < baseStart_504501 := by decide
  rcases family_descends (prefixWord ++ tailWord_504501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504518 : List Nat := [6, 1, 2, 1, 2, 1, 6]
def baseStart_504518 : Nat := 118140960795 + 504518 * 2 ^ 59
def prefixEnd_504518 : Nat := 4983230072969 + 3 ^ 40 * 504518 * 2
def baseEnd_504518 : Nat := 51172391673118479941683

theorem tailTrace_504518 : CollatzResearch.WordTrace tailWord_504518 prefixEnd_504518 51172391673118479941683 := by
  unfold tailWord_504518
  simp only [CollatzResearch.WordTrace]
  refine ⟨575040099569528926861819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 12267522124149950439718805 575040099569528926861819)
  ·
    refine ⟨862560149354293390292729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 575040099569528926861819 862560149354293390292729)
    ·
      refine ⟨646920112015720042719547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 862560149354293390292729 646920112015720042719547)
      ·
        refine ⟨970380168023580064079321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 646920112015720042719547 970380168023580064079321)
        ·
          refine ⟨727785126017685048059491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 970380168023580064079321 727785126017685048059491)
          ·
            refine ⟨1091677689026527572089237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 727785126017685048059491 1091677689026527572089237)
            ·
              refine ⟨51172391673118479941683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1091677689026527572089237 51172391673118479941683)
              ·
                rfl

theorem cell19_504518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 6].length) (baseStart_504518 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_504518 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_504518 prefixEnd_504518 := by exact prefixLift 504518
  have htrace : WordTrace (prefixWord ++ tailWord_504518) baseStart_504518 baseEnd_504518 := by
    simpa [prefixWord, tailWord_504518, baseEnd_504518] using wordTrace_append hprefix tailTrace_504518
  have hstable : (prefixWord ++ tailWord_504518).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504518).length < 2 ^ (prefixWord ++ tailWord_504518).sum := by decide
  have hdescent : baseEnd_504518 < baseStart_504518 := by decide
  rcases family_descends (prefixWord ++ tailWord_504518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504558 : List Nat := [4, 1, 2, 1, 1, 5, 2, 3]
def baseStart_504558 : Nat := 118140960795 + 504558 * 2 ^ 59
def prefixEnd_504558 : Nat := 4983230072969 + 3 ^ 40 * 504558 * 2
def baseEnd_504558 : Nat := 153529346412647198936051

theorem tailTrace_504558 : CollatzResearch.WordTrace tailWord_504558 prefixEnd_504558 153529346412647198936051 := by
  unfold tailWord_504558
  simp only [CollatzResearch.WordTrace]
  refine ⟨2300342763260001561379291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12268494737386674994022885 2300342763260001561379291)
  ·
    refine ⟨3450514144890002342068937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2300342763260001561379291 3450514144890002342068937)
    ·
      refine ⟨2587885608667501756551703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3450514144890002342068937 2587885608667501756551703)
      ·
        refine ⟨3881828413001252634827555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2587885608667501756551703 3881828413001252634827555)
        ·
          refine ⟨5822742619501878952241333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3881828413001252634827555 5822742619501878952241333)
          ·
            refine ⟨545882120578301151772625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5822742619501878952241333 545882120578301151772625)
            ·
              refine ⟨409411590433725863829469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 545882120578301151772625 409411590433725863829469)
              ·
                refine ⟨153529346412647198936051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 409411590433725863829469 153529346412647198936051)
                ·
                  rfl

theorem cell19_504558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 2, 3].length) (baseStart_504558 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_504558 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_504558 prefixEnd_504558 := by exact prefixLift 504558
  have htrace : WordTrace (prefixWord ++ tailWord_504558) baseStart_504558 baseEnd_504558 := by
    simpa [prefixWord, tailWord_504558, baseEnd_504558] using wordTrace_append hprefix tailTrace_504558
  have hstable : (prefixWord ++ tailWord_504558).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504558).length < 2 ^ (prefixWord ++ tailWord_504558).sum := by decide
  have hdescent : baseEnd_504558 < baseStart_504558 := by decide
  rcases family_descends (prefixWord ++ tailWord_504558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504638 : List Nat := [4, 2, 1, 2, 10]
def baseStart_504638 : Nat := 118140960795 + 504638 * 2 ^ 59
def prefixEnd_504638 : Nat := 4983230072969 + 3 ^ 40 * 504638 * 2
def baseEnd_504638 : Nat := 5687173674045582116965

theorem tailTrace_504638 : CollatzResearch.WordTrace tailWord_504638 prefixEnd_504638 5687173674045582116965 := by
  unfold tailWord_504638
  simp only [CollatzResearch.WordTrace]
  refine ⟨2300707493223773269243321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12270439963860124102631045 2300707493223773269243321)
  ·
    refine ⟨1725530619917829951932491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2300707493223773269243321 1725530619917829951932491)
    ·
      refine ⟨2588295929876744927898737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1725530619917829951932491 2588295929876744927898737)
      ·
        refine ⟨1941221947407558695924053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2588295929876744927898737 1941221947407558695924053)
        ·
          refine ⟨5687173674045582116965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1941221947407558695924053 5687173674045582116965)
          ·
            rfl

theorem cell19_504638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 10].length) (baseStart_504638 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_504638 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_504638 prefixEnd_504638 := by exact prefixLift 504638
  have htrace : WordTrace (prefixWord ++ tailWord_504638) baseStart_504638 baseEnd_504638 := by
    simpa [prefixWord, tailWord_504638, baseEnd_504638] using wordTrace_append hprefix tailTrace_504638
  have hstable : (prefixWord ++ tailWord_504638).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504638).length < 2 ^ (prefixWord ++ tailWord_504638).sum := by decide
  have hdescent : baseEnd_504638 < baseStart_504638 := by decide
  rcases family_descends (prefixWord ++ tailWord_504638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504733 : List Nat := [1, 4, 2, 1, 2, 1, 3, 5]
def baseStart_504733 : Nat := 118140960795 + 504733 * 2 ^ 59
def prefixEnd_504733 : Nat := 4983230072969 + 3 ^ 40 * 504733 * 2
def baseEnd_504733 : Nat := 153582596258298645046685

theorem tailTrace_504733 : CollatzResearch.WordTrace tailWord_504733 prefixEnd_504733 153582596258298645046685 := by
  unfold tailWord_504733
  simp only [CollatzResearch.WordTrace]
  refine ⟨18409124880446017378654853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12272749920297344919103235 18409124880446017378654853)
  ·
    refine ⟨3451710915083628258497785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18409124880446017378654853 3451710915083628258497785)
    ·
      refine ⟨2588783186312721193873339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3451710915083628258497785 2588783186312721193873339)
      ·
        refine ⟨3883174779469081790810009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2588783186312721193873339 3883174779469081790810009)
        ·
          refine ⟨2912381084601811343107507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3883174779469081790810009 2912381084601811343107507)
          ·
            refine ⟨4368571626902717014661261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2912381084601811343107507 4368571626902717014661261)
            ·
              refine ⟨1638214360088518880497973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4368571626902717014661261 1638214360088518880497973)
              ·
                refine ⟨153582596258298645046685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1638214360088518880497973 153582596258298645046685)
                ·
                  rfl

theorem cell19_504733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 5].length) (baseStart_504733 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_504733 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_504733 prefixEnd_504733 := by exact prefixLift 504733
  have htrace : WordTrace (prefixWord ++ tailWord_504733) baseStart_504733 baseEnd_504733 := by
    simpa [prefixWord, tailWord_504733, baseEnd_504733] using wordTrace_append hprefix tailTrace_504733
  have hstable : (prefixWord ++ tailWord_504733).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504733).length < 2 ^ (prefixWord ++ tailWord_504733).sum := by decide
  have hdescent : baseEnd_504733 < baseStart_504733 := by decide
  rcases family_descends (prefixWord ++ tailWord_504733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504828 : List Nat := [2, 2, 2, 1, 2, 3, 3, 4]
def baseStart_504828 : Nat := 118140960795 + 504828 * 2 ^ 59
def prefixEnd_504828 : Nat := 4983230072969 + 3 ^ 40 * 504828 * 2
def baseEnd_504828 : Nat := 153611503317366572935315

theorem tailTrace_504828 : CollatzResearch.WordTrace tailWord_504828 prefixEnd_504828 153611503317366572935315 := by
  unfold tailWord_504828
  simp only [CollatzResearch.WordTrace]
  refine ⟨9206294907550924301681569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12275059876734565735575425 9206294907550924301681569)
  ·
    refine ⟨6904721180663193226261177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9206294907550924301681569 6904721180663193226261177)
    ·
      refine ⟨5178540885497394919695883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6904721180663193226261177 5178540885497394919695883)
      ·
        refine ⟨7767811328246092379543825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5178540885497394919695883 7767811328246092379543825)
        ·
          refine ⟨5825858496184569284657869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7767811328246092379543825 5825858496184569284657869)
          ·
            refine ⟨2184696936069213481746701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5825858496184569284657869 2184696936069213481746701)
            ·
              refine ⟨819261351025955055655013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2184696936069213481746701 819261351025955055655013)
              ·
                refine ⟨153611503317366572935315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 819261351025955055655013 153611503317366572935315)
                ·
                  rfl

theorem cell19_504828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 4].length) (baseStart_504828 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_504828 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_504828 prefixEnd_504828 := by exact prefixLift 504828
  have htrace : WordTrace (prefixWord ++ tailWord_504828) baseStart_504828 baseEnd_504828 := by
    simpa [prefixWord, tailWord_504828, baseEnd_504828] using wordTrace_append hprefix tailTrace_504828
  have hstable : (prefixWord ++ tailWord_504828).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504828).length < 2 ^ (prefixWord ++ tailWord_504828).sum := by decide
  have hdescent : baseEnd_504828 < baseStart_504828 := by decide
  rcases family_descends (prefixWord ++ tailWord_504828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504849 : List Nat := [1, 2, 2, 1, 1, 2, 1, 9]
def baseStart_504849 : Nat := 118140960795 + 504849 * 2 ^ 59
def prefixEnd_504849 : Nat := 4983230072969 + 3 ^ 40 * 504849 * 2
def baseEnd_504849 : Nat := 153617893298844746468591

theorem tailTrace_504849 : CollatzResearch.WordTrace tailWord_504849 prefixEnd_504849 153617893298844746468591 := by
  unfold tailWord_504849
  simp only [CollatzResearch.WordTrace]
  refine ⟨18413355748025769189877601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12275570498683846126585067 18413355748025769189877601)
  ·
    refine ⟨13810016811019326892408201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18413355748025769189877601 13810016811019326892408201)
    ·
      refine ⟨10357512608264495169306151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13810016811019326892408201 10357512608264495169306151)
      ·
        refine ⟨15536268912396742753959227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10357512608264495169306151 15536268912396742753959227)
        ·
          refine ⟨23304403368595114130938841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15536268912396742753959227 23304403368595114130938841)
          ·
            refine ⟨17478302526446335598204131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23304403368595114130938841 17478302526446335598204131)
            ·
              refine ⟨26217453789669503397306197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17478302526446335598204131 26217453789669503397306197)
              ·
                refine ⟨153617893298844746468591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26217453789669503397306197 153617893298844746468591)
                ·
                  rfl

theorem cell19_504849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 9].length) (baseStart_504849 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_504849 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_504849 prefixEnd_504849 := by exact prefixLift 504849
  have htrace : WordTrace (prefixWord ++ tailWord_504849) baseStart_504849 baseEnd_504849 := by
    simpa [prefixWord, tailWord_504849, baseEnd_504849] using wordTrace_append hprefix tailTrace_504849
  have hstable : (prefixWord ++ tailWord_504849).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504849).length < 2 ^ (prefixWord ++ tailWord_504849).sum := by decide
  have hdescent : baseEnd_504849 < baseStart_504849 := by decide
  rcases family_descends (prefixWord ++ tailWord_504849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504864 : List Nat := [2, 1, 1, 7, 1, 1, 6]
def baseStart_504864 : Nat := 118140960795 + 504864 * 2 ^ 59
def prefixEnd_504864 : Nat := 4983230072969 + 3 ^ 40 * 504864 * 2
def baseEnd_504864 : Nat := 51207485857109718711739

theorem tailTrace_504864 : CollatzResearch.WordTrace tailWord_504864 prefixEnd_504864 51207485857109718711739 := by
  unfold tailWord_504864
  simp only [CollatzResearch.WordTrace]
  refine ⟨9206951421485713375836823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12275935228647617834449097 9206951421485713375836823)
  ·
    refine ⟨13810427132228570063755235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9206951421485713375836823 13810427132228570063755235)
    ·
      refine ⟨20715640698342855095632853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13810427132228570063755235 20715640698342855095632853)
      ·
        refine ⟨485522828867410666303895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 20715640698342855095632853 485522828867410666303895)
        ·
          refine ⟨728284243301115999455843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 485522828867410666303895 728284243301115999455843)
          ·
            refine ⟨1092426364951673999183765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 728284243301115999455843 1092426364951673999183765)
            ·
              refine ⟨51207485857109718711739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1092426364951673999183765 51207485857109718711739)
              ·
                rfl

theorem cell19_504864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 6].length) (baseStart_504864 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_504864 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_504864 prefixEnd_504864 := by exact prefixLift 504864
  have htrace : WordTrace (prefixWord ++ tailWord_504864) baseStart_504864 baseEnd_504864 := by
    simpa [prefixWord, tailWord_504864, baseEnd_504864] using wordTrace_append hprefix tailTrace_504864
  have hstable : (prefixWord ++ tailWord_504864).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504864).length < 2 ^ (prefixWord ++ tailWord_504864).sum := by decide
  have hdescent : baseEnd_504864 < baseStart_504864 := by decide
  rcases family_descends (prefixWord ++ tailWord_504864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504866 : List Nat := [3, 3, 1, 1, 1, 4, 6]
def baseStart_504866 : Nat := 118140960795 + 504866 * 2 ^ 59
def prefixEnd_504866 : Nat := 4983230072969 + 3 ^ 40 * 504866 * 2
def baseEnd_504866 : Nat := 51207688713664581363589

theorem tailTrace_504866 : CollatzResearch.WordTrace tailWord_504866 prefixEnd_504866 51207688713664581363589 := by
  unfold tailWord_504866
  simp only [CollatzResearch.WordTrace]
  refine ⟨4603493947241045273311613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12275983859309454062164301 4603493947241045273311613)
  ·
    refine ⟨1726310230215391977491855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4603493947241045273311613 1726310230215391977491855)
    ·
      refine ⟨2589465345323087966237783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1726310230215391977491855 2589465345323087966237783)
      ·
        refine ⟨3884198017984631949356675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2589465345323087966237783 3884198017984631949356675)
        ·
          refine ⟨5826297026976947924035013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3884198017984631949356675 5826297026976947924035013)
          ·
            refine ⟨1092430692558177735756565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5826297026976947924035013 1092430692558177735756565)
            ·
              refine ⟨51207688713664581363589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1092430692558177735756565 51207688713664581363589)
              ·
                rfl

theorem cell19_504866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 6].length) (baseStart_504866 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_504866 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_504866 prefixEnd_504866 := by exact prefixLift 504866
  have htrace : WordTrace (prefixWord ++ tailWord_504866) baseStart_504866 baseEnd_504866 := by
    simpa [prefixWord, tailWord_504866, baseEnd_504866] using wordTrace_append hprefix tailTrace_504866
  have hstable : (prefixWord ++ tailWord_504866).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504866).length < 2 ^ (prefixWord ++ tailWord_504866).sum := by decide
  have hdescent : baseEnd_504866 < baseStart_504866 := by decide
  rcases family_descends (prefixWord ++ tailWord_504866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504887 : List Nat := [1, 1, 3, 1, 2, 2, 1, 8]
def baseStart_504887 : Nat := 118140960795 + 504887 * 2 ^ 59
def prefixEnd_504887 : Nat := 4983230072969 + 3 ^ 40 * 504887 * 2
def baseEnd_504887 : Nat := 153629456122471917624043

theorem tailTrace_504887 : CollatzResearch.WordTrace tailWord_504887 prefixEnd_504887 153629456122471917624043 := by
  unfold tailWord_504887
  simp only [CollatzResearch.WordTrace]
  refine ⟨18414741721888101679760915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12276494481258734453173943 18414741721888101679760915)
  ·
    refine ⟨27622112582832152519641373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18414741721888101679760915 27622112582832152519641373)
    ·
      refine ⟨10358292218562057194865515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27622112582832152519641373 10358292218562057194865515)
      ·
        refine ⟨15537438327843085792298273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10358292218562057194865515 15537438327843085792298273)
        ·
          refine ⟨11653078745882314344223705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15537438327843085792298273 11653078745882314344223705)
          ·
            refine ⟨8739809059411735758167779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11653078745882314344223705 8739809059411735758167779)
            ·
              refine ⟨13109713589117603637251669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8739809059411735758167779 13109713589117603637251669)
              ·
                refine ⟨153629456122471917624043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13109713589117603637251669 153629456122471917624043)
                ·
                  rfl

theorem cell19_504887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 8].length) (baseStart_504887 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_504887 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_504887 prefixEnd_504887 := by exact prefixLift 504887
  have htrace : WordTrace (prefixWord ++ tailWord_504887) baseStart_504887 baseEnd_504887 := by
    simpa [prefixWord, tailWord_504887, baseEnd_504887] using wordTrace_append hprefix tailTrace_504887
  have hstable : (prefixWord ++ tailWord_504887).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504887).length < 2 ^ (prefixWord ++ tailWord_504887).sum := by decide
  have hdescent : baseEnd_504887 < baseStart_504887 := by decide
  rcases family_descends (prefixWord ++ tailWord_504887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504942 : List Nat := [4, 1, 2, 2, 1, 2, 1, 6]
def baseStart_504942 : Nat := 118140960795 + 504942 * 2 ^ 59
def prefixEnd_504942 : Nat := 4983230072969 + 3 ^ 40 * 504942 * 2
def baseEnd_504942 : Nat := 153646191788248086401671

theorem tailTrace_504942 : CollatzResearch.WordTrace tailWord_504942 prefixEnd_504942 153646191788248086401671 := by
  unfold tailWord_504942
  simp only [CollatzResearch.WordTrace]
  refine ⟨2302093467086105759126635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12277831824459230715342053 2302093467086105759126635)
  ·
    refine ⟨3453140200629158638689953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2302093467086105759126635 3453140200629158638689953)
    ·
      refine ⟨2589855150471868979017465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3453140200629158638689953 2589855150471868979017465)
      ·
        refine ⟨1942391362853901734263099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2589855150471868979017465 1942391362853901734263099)
        ·
          refine ⟨2913587044280852601394649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1942391362853901734263099 2913587044280852601394649)
          ·
            refine ⟨2185190283210639451045987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2913587044280852601394649 2185190283210639451045987)
            ·
              refine ⟨3277785424815959176568981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2185190283210639451045987 3277785424815959176568981)
              ·
                refine ⟨153646191788248086401671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3277785424815959176568981 153646191788248086401671)
                ·
                  rfl

theorem cell19_504942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_504942 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_504942 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_504942 prefixEnd_504942 := by exact prefixLift 504942
  have htrace : WordTrace (prefixWord ++ tailWord_504942) baseStart_504942 baseEnd_504942 := by
    simpa [prefixWord, tailWord_504942, baseEnd_504942] using wordTrace_append hprefix tailTrace_504942
  have hstable : (prefixWord ++ tailWord_504942).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504942).length < 2 ^ (prefixWord ++ tailWord_504942).sum := by decide
  have hdescent : baseEnd_504942 < baseStart_504942 := by decide
  rcases family_descends (prefixWord ++ tailWord_504942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504961 : List Nat := [1, 2, 4, 2, 2, 1, 2, 5]
def baseStart_504961 : Nat := 118140960795 + 504961 * 2 ^ 59
def prefixEnd_504961 : Nat := 4983230072969 + 3 ^ 40 * 504961 * 2
def baseEnd_504961 : Nat := 153651973200061671979397

theorem tailTrace_504961 : CollatzResearch.WordTrace tailWord_504961 prefixEnd_504961 153651973200061671979397 := by
  unfold tailWord_504961
  simp only [CollatzResearch.WordTrace]
  refine ⟨18417440723620012317954737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12278293815746674878636491 18417440723620012317954737)
  ·
    refine ⟨13813080542715009238466053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18417440723620012317954737 13813080542715009238466053)
    ·
      refine ⟨2589952601759064232212385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13813080542715009238466053 2589952601759064232212385)
      ·
        refine ⟨1942464451319298174159289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2589952601759064232212385 1942464451319298174159289)
        ·
          refine ⟨1456848338489473630619467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1942464451319298174159289 1456848338489473630619467)
          ·
            refine ⟨2185272507734210445929201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1456848338489473630619467 2185272507734210445929201)
            ·
              refine ⟨1638954380800657834446901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2185272507734210445929201 1638954380800657834446901)
              ·
                refine ⟨153651973200061671979397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1638954380800657834446901 153651973200061671979397)
                ·
                  rfl

theorem cell19_504961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 5].length) (baseStart_504961 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_504961 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_504961 prefixEnd_504961 := by exact prefixLift 504961
  have htrace : WordTrace (prefixWord ++ tailWord_504961) baseStart_504961 baseEnd_504961 := by
    simpa [prefixWord, tailWord_504961, baseEnd_504961] using wordTrace_append hprefix tailTrace_504961
  have hstable : (prefixWord ++ tailWord_504961).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504961).length < 2 ^ (prefixWord ++ tailWord_504961).sum := by decide
  have hdescent : baseEnd_504961 < baseStart_504961 := by decide
  rcases family_descends (prefixWord ++ tailWord_504961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504963 : List Nat := [1, 1, 1, 3, 3, 2, 1, 7]
def baseStart_504963 : Nat := 118140960795 + 504963 * 2 ^ 59
def prefixEnd_504963 : Nat := 4983230072969 + 3 ^ 40 * 504963 * 2
def baseEnd_504963 : Nat := 153652581769726259934947

theorem tailTrace_504963 : CollatzResearch.WordTrace tailWord_504963 prefixEnd_504963 153652581769726259934947 := by
  unfold tailWord_504963
  simp only [CollatzResearch.WordTrace]
  refine ⟨18417513669612766659527543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12278342446408511106351695 18417513669612766659527543)
  ·
    refine ⟨27626270504419149989291315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18417513669612766659527543 27626270504419149989291315)
    ·
      refine ⟨41439405756628724983936973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27626270504419149989291315 41439405756628724983936973)
      ·
        refine ⟨15539777158735771868976365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41439405756628724983936973 15539777158735771868976365)
        ·
          refine ⟨5827416434525914450866137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15539777158735771868976365 5827416434525914450866137)
          ·
            refine ⟨4370562325894435838149603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5827416434525914450866137 4370562325894435838149603)
            ·
              refine ⟨6555843488841653757224405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4370562325894435838149603 6555843488841653757224405)
              ·
                refine ⟨153652581769726259934947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6555843488841653757224405 153652581769726259934947)
                ·
                  rfl

theorem cell19_504963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 7].length) (baseStart_504963 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_504963 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_504963 prefixEnd_504963 := by exact prefixLift 504963
  have htrace : WordTrace (prefixWord ++ tailWord_504963) baseStart_504963 baseEnd_504963 := by
    simpa [prefixWord, tailWord_504963, baseEnd_504963] using wordTrace_append hprefix tailTrace_504963
  have hstable : (prefixWord ++ tailWord_504963).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504963).length < 2 ^ (prefixWord ++ tailWord_504963).sum := by decide
  have hdescent : baseEnd_504963 < baseStart_504963 := by decide
  rcases family_descends (prefixWord ++ tailWord_504963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505071 : List Nat := [1, 1, 2, 1, 8, 1, 2, 3]
def baseStart_505071 : Nat := 118140960795 + 505071 * 2 ^ 59
def prefixEnd_505071 : Nat := 4983230072969 + 3 ^ 40 * 505071 * 2
def baseEnd_505071 : Nat := 153685444531614009534653

theorem tailTrace_505071 : CollatzResearch.WordTrace tailWord_505071 prefixEnd_505071 153685444531614009534653 := by
  unfold tailWord_505071
  simp only [CollatzResearch.WordTrace]
  refine ⟨18421452753221501104459067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12280968502147667402972711 18421452753221501104459067)
  ·
    refine ⟨27632179129832251656688601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18421452753221501104459067 27632179129832251656688601)
    ·
      refine ⟨20724134347374188742516451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27632179129832251656688601 20724134347374188742516451)
      ·
        refine ⟨31086201521061283113774677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20724134347374188742516451 31086201521061283113774677)
        ·
          refine ⟨364291424074936911489547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 31086201521061283113774677 364291424074936911489547)
          ·
            refine ⟨546437136112405367234321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 364291424074936911489547 546437136112405367234321)
            ·
              refine ⟨409827852084304025425741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 546437136112405367234321 409827852084304025425741)
              ·
                refine ⟨153685444531614009534653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 409827852084304025425741 153685444531614009534653)
                ·
                  rfl

theorem cell19_505071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 2, 3].length) (baseStart_505071 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_505071 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_505071 prefixEnd_505071 := by exact prefixLift 505071
  have htrace : WordTrace (prefixWord ++ tailWord_505071) baseStart_505071 baseEnd_505071 := by
    simpa [prefixWord, tailWord_505071, baseEnd_505071] using wordTrace_append hprefix tailTrace_505071
  have hstable : (prefixWord ++ tailWord_505071).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505071).length < 2 ^ (prefixWord ++ tailWord_505071).sum := by decide
  have hdescent : baseEnd_505071 < baseStart_505071 := by decide
  rcases family_descends (prefixWord ++ tailWord_505071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505075 : List Nat := [1, 1, 1, 2, 2, 5, 4, 3]
def baseStart_505075 : Nat := 118140960795 + 505075 * 2 ^ 59
def prefixEnd_505075 : Nat := 4983230072969 + 3 ^ 40 * 505075 * 2
def baseEnd_505075 : Nat := 153686661670943185445753

theorem tailTrace_505075 : CollatzResearch.WordTrace tailWord_505075 prefixEnd_505075 153686661670943185445753 := by
  unfold tailWord_505075
  simp only [CollatzResearch.WordTrace]
  refine ⟨18421598645207009787604679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12281065763471339858403119 18421598645207009787604679)
  ·
    refine ⟨27632397967810514681407019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18421598645207009787604679 27632397967810514681407019)
    ·
      refine ⟨41448596951715772022110529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27632397967810514681407019 41448596951715772022110529)
      ·
        refine ⟨31086447713786829016582897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41448596951715772022110529 31086447713786829016582897)
        ·
          refine ⟨23314835785340121762437173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31086447713786829016582897 23314835785340121762437173)
          ·
            refine ⟨2185765854875636415228485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23314835785340121762437173 2185765854875636415228485)
            ·
              refine ⟨409831097789181827855341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2185765854875636415228485 409831097789181827855341)
              ·
                refine ⟨153686661670943185445753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 409831097789181827855341 153686661670943185445753)
                ·
                  rfl

theorem cell19_505075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 4, 3].length) (baseStart_505075 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_505075 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_505075 prefixEnd_505075 := by exact prefixLift 505075
  have htrace : WordTrace (prefixWord ++ tailWord_505075) baseStart_505075 baseEnd_505075 := by
    simpa [prefixWord, tailWord_505075, baseEnd_505075] using wordTrace_append hprefix tailTrace_505075
  have hstable : (prefixWord ++ tailWord_505075).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505075).length < 2 ^ (prefixWord ++ tailWord_505075).sum := by decide
  have hdescent : baseEnd_505075 < baseStart_505075 := by decide
  rcases family_descends (prefixWord ++ tailWord_505075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505090 : List Nat := [3, 4, 1, 1, 4, 1, 5]
def baseStart_505090 : Nat := 118140960795 + 505090 * 2 ^ 59
def prefixEnd_505090 : Nat := 4983230072969 + 3 ^ 40 * 505090 * 2
def baseEnd_505090 : Nat := 51230408647809198370793

theorem tailTrace_505090 : CollatzResearch.WordTrace tailWord_505090 prefixEnd_505090 51230408647809198370793 := by
  unfold tailWord_505090
  simp only [CollatzResearch.WordTrace]
  refine ⟨4605536435038166837350181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12281430493435111566267149 4605536435038166837350181)
  ·
    refine ⟨863538081569656282003159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4605536435038166837350181 863538081569656282003159)
    ·
      refine ⟨1295307122354484423004739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 863538081569656282003159 1295307122354484423004739)
      ·
        refine ⟨1942960683531726634507109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1295307122354484423004739 1942960683531726634507109)
        ·
          refine ⟨364305128162198743970083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1942960683531726634507109 364305128162198743970083)
          ·
            refine ⟨546457692243298115955125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 364305128162198743970083 546457692243298115955125)
            ·
              refine ⟨51230408647809198370793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 546457692243298115955125 51230408647809198370793)
              ·
                rfl

theorem cell19_505090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 5].length) (baseStart_505090 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_505090 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_505090 prefixEnd_505090 := by exact prefixLift 505090
  have htrace : WordTrace (prefixWord ++ tailWord_505090) baseStart_505090 baseEnd_505090 := by
    simpa [prefixWord, tailWord_505090, baseEnd_505090] using wordTrace_append hprefix tailTrace_505090
  have hstable : (prefixWord ++ tailWord_505090).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505090).length < 2 ^ (prefixWord ++ tailWord_505090).sum := by decide
  have hdescent : baseEnd_505090 < baseStart_505090 := by decide
  rcases family_descends (prefixWord ++ tailWord_505090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505149 : List Nat := [1, 4, 1, 5, 2, 6]
def baseStart_505149 : Nat := 118140960795 + 505149 * 2 ^ 59
def prefixEnd_505149 : Nat := 4983230072969 + 3 ^ 40 * 505149 * 2
def baseEnd_505149 : Nat := 17078797638725882200123

theorem tailTrace_505149 : CollatzResearch.WordTrace tailWord_505149 prefixEnd_505149 17078797638725882200123 := by
  unfold tailWord_505149
  simp only [CollatzResearch.WordTrace]
  refine ⟨18424297646938920425798501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12282865097959280283865667 18424297646938920425798501)
  ·
    refine ⟨3454555808801047579837219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18424297646938920425798501 3454555808801047579837219)
    ·
      refine ⟨5181833713201571369755829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3454555808801047579837219 5181833713201571369755829)
      ·
        refine ⟨485796910612647315914609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5181833713201571369755829 485796910612647315914609)
        ·
          refine ⟨364347682959485486935957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 485796910612647315914609 364347682959485486935957)
          ·
            refine ⟨17078797638725882200123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 364347682959485486935957 17078797638725882200123)
            ·
              rfl

theorem cell19_505149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 6].length) (baseStart_505149 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_505149 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_505149 prefixEnd_505149 := by exact prefixLift 505149
  have htrace : WordTrace (prefixWord ++ tailWord_505149) baseStart_505149 baseEnd_505149 := by
    simpa [prefixWord, tailWord_505149, baseEnd_505149] using wordTrace_append hprefix tailTrace_505149
  have hstable : (prefixWord ++ tailWord_505149).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505149).length < 2 ^ (prefixWord ++ tailWord_505149).sum := by decide
  have hdescent : baseEnd_505149 < baseStart_505149 := by decide
  rcases family_descends (prefixWord ++ tailWord_505149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505189 : List Nat := [1, 3, 1, 3, 1, 2, 5, 3]
def baseStart_505189 : Nat := 118140960795 + 505189 * 2 ^ 59
def prefixEnd_505189 : Nat := 4983230072969 + 3 ^ 40 * 505189 * 2
def baseEnd_505189 : Nat := 153721350141824698912109

theorem tailTrace_505189 : CollatzResearch.WordTrace tailWord_505189 prefixEnd_505189 153721350141824698912109 := by
  unfold tailWord_505189
  simp only [CollatzResearch.WordTrace]
  refine ⟨18425756566794007257254621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12283837711196004838169747 18425756566794007257254621)
  ·
    refine ⟨6909658712547752721470483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18425756566794007257254621 6909658712547752721470483)
    ·
      refine ⟨10364488068821629082205725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6909658712547752721470483 10364488068821629082205725)
      ·
        refine ⟨3886683025808110905827147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10364488068821629082205725 3886683025808110905827147)
        ·
          refine ⟨5830024538712166358740721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3886683025808110905827147 5830024538712166358740721)
          ·
            refine ⟨4372518404034124769055541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5830024538712166358740721 4372518404034124769055541)
            ·
              refine ⟨409923600378199197098957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4372518404034124769055541 409923600378199197098957)
              ·
                refine ⟨153721350141824698912109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 409923600378199197098957 153721350141824698912109)
                ·
                  rfl

theorem cell19_505189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 5, 3].length) (baseStart_505189 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_505189 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_505189 prefixEnd_505189 := by exact prefixLift 505189
  have htrace : WordTrace (prefixWord ++ tailWord_505189) baseStart_505189 baseEnd_505189 := by
    simpa [prefixWord, tailWord_505189, baseEnd_505189] using wordTrace_append hprefix tailTrace_505189
  have hstable : (prefixWord ++ tailWord_505189).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505189).length < 2 ^ (prefixWord ++ tailWord_505189).sum := by decide
  have hdescent : baseEnd_505189 < baseStart_505189 := by decide
  rcases family_descends (prefixWord ++ tailWord_505189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505244 : List Nat := [2, 2, 3, 4, 1, 1, 1, 5]
def baseStart_505244 : Nat := 118140960795 + 505244 * 2 ^ 59
def prefixEnd_505244 : Nat := 4983230072969 + 3 ^ 40 * 505244 * 2
def baseEnd_505244 : Nat := 153738085807600867689737

theorem tailTrace_505244 : CollatzResearch.WordTrace tailWord_505244 prefixEnd_505244 153738085807600867689737 := by
  unfold tailWord_505244
  simp only [CollatzResearch.WordTrace]
  refine ⟨9213881290797375825253393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12285175054396501100337857 9213881290797375825253393)
  ·
    refine ⟨6910410968098031868940045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9213881290797375825253393 6910410968098031868940045)
    ·
      refine ⟨2591404113036761950852517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6910410968098031868940045 2591404113036761950852517)
      ·
        refine ⟨485888271194392865784847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2591404113036761950852517 485888271194392865784847)
        ·
          refine ⟨728832406791589298677271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 485888271194392865784847 728832406791589298677271)
          ·
            refine ⟨1093248610187383948015907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 728832406791589298677271 1093248610187383948015907)
            ·
              refine ⟨1639872915281075922023861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1093248610187383948015907 1639872915281075922023861)
              ·
                refine ⟨153738085807600867689737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1639872915281075922023861 153738085807600867689737)
                ·
                  rfl

theorem cell19_505244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 5].length) (baseStart_505244 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_505244 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_505244 prefixEnd_505244 := by exact prefixLift 505244
  have htrace : WordTrace (prefixWord ++ tailWord_505244) baseStart_505244 baseEnd_505244 := by
    simpa [prefixWord, tailWord_505244, baseEnd_505244] using wordTrace_append hprefix tailTrace_505244
  have hstable : (prefixWord ++ tailWord_505244).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505244).length < 2 ^ (prefixWord ++ tailWord_505244).sum := by decide
  have hdescent : baseEnd_505244 < baseStart_505244 := by decide
  rcases family_descends (prefixWord ++ tailWord_505244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505248 : List Nat := [2, 1, 1, 4, 1, 2, 3, 5]
def baseStart_505248 : Nat := 118140960795 + 505248 * 2 ^ 59
def prefixEnd_505248 : Nat := 4983230072969 + 3 ^ 40 * 505248 * 2
def baseEnd_505248 : Nat := 153739302946930043600837

theorem tailTrace_505248 : CollatzResearch.WordTrace tailWord_505248 prefixEnd_505248 153739302946930043600837 := by
  unfold tailWord_505248
  simp only [CollatzResearch.WordTrace]
  refine ⟨9213954236790130166826199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12285272315720173555768265 9213954236790130166826199)
  ·
    refine ⟨13820931355185195250239299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9213954236790130166826199 13820931355185195250239299)
    ·
      refine ⟨20731397032777792875358949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13820931355185195250239299 20731397032777792875358949)
      ·
        refine ⟨3887136943645836164129803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20731397032777792875358949 3887136943645836164129803)
        ·
          refine ⟨5830705415468754246194705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3887136943645836164129803 5830705415468754246194705)
          ·
            refine ⟨4373029061601565684646029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5830705415468754246194705 4373029061601565684646029)
            ·
              refine ⟨1639885898100587131742261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4373029061601565684646029 1639885898100587131742261)
              ·
                refine ⟨153739302946930043600837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1639885898100587131742261 153739302946930043600837)
                ·
                  rfl

theorem cell19_505248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 5].length) (baseStart_505248 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_505248 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_505248 prefixEnd_505248 := by exact prefixLift 505248
  have htrace : WordTrace (prefixWord ++ tailWord_505248) baseStart_505248 baseEnd_505248 := by
    simpa [prefixWord, tailWord_505248, baseEnd_505248] using wordTrace_append hprefix tailTrace_505248
  have hstable : (prefixWord ++ tailWord_505248).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505248).length < 2 ^ (prefixWord ++ tailWord_505248).sum := by decide
  have hdescent : baseEnd_505248 < baseStart_505248 := by decide
  rcases family_descends (prefixWord ++ tailWord_505248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505284 : List Nat := [2, 3, 3, 2, 1, 1, 1, 6]
def baseStart_505284 : Nat := 118140960795 + 505284 * 2 ^ 59
def prefixEnd_505284 : Nat := 4983230072969 + 3 ^ 40 * 505284 * 2
def baseEnd_505284 : Nat := 153750257200892626800739

theorem tailTrace_505284 : CollatzResearch.WordTrace tailWord_505284 prefixEnd_505284 153750257200892626800739 := by
  unfold tailWord_505284
  simp only [CollatzResearch.WordTrace]
  refine ⟨9214610750724919240981453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12286147667633225654641937 9214610750724919240981453)
  ·
    refine ⟨3455479031521844715368045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9214610750724919240981453 3455479031521844715368045)
    ·
      refine ⟨1295804636820691768263017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3455479031521844715368045 1295804636820691768263017)
      ·
        refine ⟨971853477615518826197263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1295804636820691768263017 971853477615518826197263)
        ·
          refine ⟨1457780216423278239295895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 971853477615518826197263 1457780216423278239295895)
          ·
            refine ⟨2186670324634917358943843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1457780216423278239295895 2186670324634917358943843)
            ·
              refine ⟨3280005486952376038415765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2186670324634917358943843 3280005486952376038415765)
              ·
                refine ⟨153750257200892626800739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3280005486952376038415765 153750257200892626800739)
                ·
                  rfl

theorem cell19_505284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 6].length) (baseStart_505284 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_505284 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_505284 prefixEnd_505284 := by exact prefixLift 505284
  have htrace : WordTrace (prefixWord ++ tailWord_505284) baseStart_505284 baseEnd_505284 := by
    simpa [prefixWord, tailWord_505284, baseEnd_505284] using wordTrace_append hprefix tailTrace_505284
  have hstable : (prefixWord ++ tailWord_505284).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505284).length < 2 ^ (prefixWord ++ tailWord_505284).sum := by decide
  have hdescent : baseEnd_505284 < baseStart_505284 := by decide
  rcases family_descends (prefixWord ++ tailWord_505284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505305 : List Nat := [1, 2, 1, 2, 4, 2, 2, 5]
def baseStart_505305 : Nat := 118140960795 + 505305 * 2 ^ 59
def prefixEnd_505305 : Nat := 4983230072969 + 3 ^ 40 * 505305 * 2
def baseEnd_505305 : Nat := 153756647182370800334015

theorem tailTrace_505305 : CollatzResearch.WordTrace tailWord_505305 prefixEnd_505305 153756647182370800334015 := by
  unfold tailWord_505305
  simp only [CollatzResearch.WordTrace]
  refine ⟨18429987434373759068477369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12286658289582506045651579 18429987434373759068477369)
  ·
    refine ⟨13822490575780319301358027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18429987434373759068477369 13822490575780319301358027)
    ·
      refine ⟨20733735863670478952037041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13822490575780319301358027 20733735863670478952037041)
      ·
        refine ⟨15550301897752859214027781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20733735863670478952037041 15550301897752859214027781)
        ·
          refine ⟨2915681605828661102630209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15550301897752859214027781 2915681605828661102630209)
          ·
            refine ⟨2186761204371495826972657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2915681605828661102630209 2186761204371495826972657)
            ·
              refine ⟨1640070903278621870229493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2186761204371495826972657 1640070903278621870229493)
              ·
                refine ⟨153756647182370800334015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1640070903278621870229493 153756647182370800334015)
                ·
                  rfl

theorem cell19_505305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 5].length) (baseStart_505305 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_505305 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_505305 prefixEnd_505305 := by exact prefixLift 505305
  have htrace : WordTrace (prefixWord ++ tailWord_505305) baseStart_505305 baseEnd_505305 := by
    simpa [prefixWord, tailWord_505305, baseEnd_505305] using wordTrace_append hprefix tailTrace_505305
  have hstable : (prefixWord ++ tailWord_505305).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505305).length < 2 ^ (prefixWord ++ tailWord_505305).sum := by decide
  have hdescent : baseEnd_505305 < baseStart_505305 := by decide
  rcases family_descends (prefixWord ++ tailWord_505305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505322 : List Nat := [3, 1, 3, 1, 5, 6]
def baseStart_505322 : Nat := 118140960795 + 505322 * 2 ^ 59
def prefixEnd_505322 : Nat := 4983230072969 + 3 ^ 40 * 505322 * 2
def baseEnd_505322 : Nat := 17084646669391088661799

theorem tailTrace_505322 : CollatzResearch.WordTrace tailWord_505322 prefixEnd_505322 17084646669391088661799 := by
  unfold tailWord_505322
  simp only [CollatzResearch.WordTrace]
  refine ⟨4607651868828042742961555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12287071650208113981230813 4607651868828042742961555)
  ·
    refine ⟨6911477803242064114442333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4607651868828042742961555 6911477803242064114442333)
    ·
      refine ⟨2591804176215774042915875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6911477803242064114442333 2591804176215774042915875)
      ·
        refine ⟨3887706264323661064373813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2591804176215774042915875 3887706264323661064373813)
        ·
          refine ⟨364472462280343224785045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3887706264323661064373813 364472462280343224785045)
          ·
            refine ⟨17084646669391088661799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 364472462280343224785045 17084646669391088661799)
            ·
              rfl

theorem cell19_505322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 6].length) (baseStart_505322 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_505322 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_505322 prefixEnd_505322 := by exact prefixLift 505322
  have htrace : WordTrace (prefixWord ++ tailWord_505322) baseStart_505322 baseEnd_505322 := by
    simpa [prefixWord, tailWord_505322, baseEnd_505322] using wordTrace_append hprefix tailTrace_505322
  have hstable : (prefixWord ++ tailWord_505322).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505322).length < 2 ^ (prefixWord ++ tailWord_505322).sum := by decide
  have hdescent : baseEnd_505322 < baseStart_505322 := by decide
  rcases family_descends (prefixWord ++ tailWord_505322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505341 : List Nat := [1, 4, 1, 1, 1, 6, 1, 4]
def baseStart_505341 : Nat := 118140960795 + 505341 * 2 ^ 59
def prefixEnd_505341 : Nat := 4983230072969 + 3 ^ 40 * 505341 * 2
def baseEnd_505341 : Nat := 153767601436333383533917

theorem tailTrace_505341 : CollatzResearch.WordTrace tailWord_505341 prefixEnd_505341 153767601436333383533917 := by
  unfold tailWord_505341
  simp only [CollatzResearch.WordTrace]
  refine ⟨18431300462243337216787877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12287533641495558144525251 18431300462243337216787877)
  ·
    refine ⟨3455868836670625728147727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18431300462243337216787877 3455868836670625728147727)
    ·
      refine ⟨5183803255005938592221591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3455868836670625728147727 5183803255005938592221591)
      ·
        refine ⟨7775704882508907888332387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5183803255005938592221591 7775704882508907888332387)
        ·
          refine ⟨11663557323763361832498581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7775704882508907888332387 11663557323763361832498581)
          ·
            refine ⟨546729249551407585898371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 11663557323763361832498581 546729249551407585898371)
            ·
              refine ⟨820093874327111378847557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 546729249551407585898371 820093874327111378847557)
              ·
                refine ⟨153767601436333383533917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 820093874327111378847557 153767601436333383533917)
                ·
                  rfl

theorem cell19_505341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 1, 4].length) (baseStart_505341 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_505341 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_505341 prefixEnd_505341 := by exact prefixLift 505341
  have htrace : WordTrace (prefixWord ++ tailWord_505341) baseStart_505341 baseEnd_505341 := by
    simpa [prefixWord, tailWord_505341, baseEnd_505341] using wordTrace_append hprefix tailTrace_505341
  have hstable : (prefixWord ++ tailWord_505341).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505341).length < 2 ^ (prefixWord ++ tailWord_505341).sum := by decide
  have hdescent : baseEnd_505341 < baseStart_505341 := by decide
  rcases family_descends (prefixWord ++ tailWord_505341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505358 : List Nat := [4, 1, 1, 2, 4, 1, 3, 3]
def baseStart_505358 : Nat := 118140960795 + 505358 * 2 ^ 59
def prefixEnd_505358 : Nat := 4983230072969 + 3 ^ 40 * 505358 * 2
def baseEnd_505358 : Nat := 153772774278482381156093

theorem tailTrace_505358 : CollatzResearch.WordTrace tailWord_505358 prefixEnd_505358 153772774278482381156093 := by
  unfold tailWord_505358
  simp only [CollatzResearch.WordTrace]
  refine ⟨2303990062897718640019591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12287947002121166080104485 2303990062897718640019591)
  ·
    refine ⟨3455985094346577960029387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2303990062897718640019591 3455985094346577960029387)
    ·
      refine ⟨5183977641519866940044081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3455985094346577960029387 5183977641519866940044081)
      ·
        refine ⟨3887983231139900205033061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5183977641519866940044081 3887983231139900205033061)
        ·
          refine ⟨728996855838731288443699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3887983231139900205033061 728996855838731288443699)
          ·
            refine ⟨1093495283758096932665549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 728996855838731288443699 1093495283758096932665549)
            ·
              refine ⟨410060731409286349749581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1093495283758096932665549 410060731409286349749581)
              ·
                refine ⟨153772774278482381156093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 410060731409286349749581 153772774278482381156093)
                ·
                  rfl

theorem cell19_505358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 3, 3].length) (baseStart_505358 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_505358 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_505358 prefixEnd_505358 := by exact prefixLift 505358
  have htrace : WordTrace (prefixWord ++ tailWord_505358) baseStart_505358 baseEnd_505358 := by
    simpa [prefixWord, tailWord_505358, baseEnd_505358] using wordTrace_append hprefix tailTrace_505358
  have hstable : (prefixWord ++ tailWord_505358).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505358).length < 2 ^ (prefixWord ++ tailWord_505358).sum := by decide
  have hdescent : baseEnd_505358 < baseStart_505358 := by decide
  rcases family_descends (prefixWord ++ tailWord_505358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505415 : List Nat := [1, 1, 4, 1, 5, 2, 2, 3]
def baseStart_505415 : Nat := 118140960795 + 505415 * 2 ^ 59
def prefixEnd_505415 : Nat := 4983230072969 + 3 ^ 40 * 505415 * 2
def baseEnd_505415 : Nat := 153790118513923137889271

theorem tailTrace_505415 : CollatzResearch.WordTrace tailWord_505415 prefixEnd_505415 153790118513923137889271 := by
  unfold tailWord_505415
  simp only [CollatzResearch.WordTrace]
  refine ⟨18433999463975247854981699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12289332975983498569987799 18433999463975247854981699)
  ·
    refine ⟨27650999195962871782472549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18433999463975247854981699 27650999195962871782472549)
    ·
      refine ⟨5184562349243038459213603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27650999195962871782472549 5184562349243038459213603)
      ·
        refine ⟨7776843523864557688820405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5184562349243038459213603 7776843523864557688820405)
        ·
          refine ⟨729079080362302283326913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7776843523864557688820405 729079080362302283326913)
          ·
            refine ⟨546809310271726712495185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 729079080362302283326913 546809310271726712495185)
            ·
              refine ⟨410106982703795034371389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 546809310271726712495185 410106982703795034371389)
              ·
                refine ⟨153790118513923137889271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 410106982703795034371389 153790118513923137889271)
                ·
                  rfl

theorem cell19_505415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 2, 3].length) (baseStart_505415 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_505415 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_505415 prefixEnd_505415 := by exact prefixLift 505415
  have htrace : WordTrace (prefixWord ++ tailWord_505415) baseStart_505415 baseEnd_505415 := by
    simpa [prefixWord, tailWord_505415, baseEnd_505415] using wordTrace_append hprefix tailTrace_505415
  have hstable : (prefixWord ++ tailWord_505415).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505415).length < 2 ^ (prefixWord ++ tailWord_505415).sum := by decide
  have hdescent : baseEnd_505415 < baseStart_505415 := by decide
  rcases family_descends (prefixWord ++ tailWord_505415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505430 : List Nat := [5, 2, 2, 2, 2, 1, 5]
def baseStart_505430 : Nat := 118140960795 + 505430 * 2 ^ 59
def prefixEnd_505430 : Nat := 4983230072969 + 3 ^ 40 * 505430 * 2
def baseEnd_505430 : Nat := 51264894262135849185299

theorem tailTrace_505430 : CollatzResearch.WordTrace tailWord_505430 prefixEnd_505430 51264894262135849185299 := by
  unfold tailWord_505430
  simp only [CollatzResearch.WordTrace]
  refine ⟨1152159159932556588548609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12289697705947270277851829 1152159159932556588548609)
  ·
    refine ⟨864119369949417441411457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1152159159932556588548609 864119369949417441411457)
    ·
      refine ⟨648089527462063081058593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 864119369949417441411457 648089527462063081058593)
      ·
        refine ⟨486067145596547310793945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 648089527462063081058593 486067145596547310793945)
        ·
          refine ⟨364550359197410483095459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 486067145596547310793945 364550359197410483095459)
          ·
            refine ⟨546825538796115724643189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 364550359197410483095459 546825538796115724643189)
            ·
              refine ⟨51264894262135849185299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 546825538796115724643189 51264894262135849185299)
              ·
                rfl

theorem cell19_505430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 5].length) (baseStart_505430 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_505430 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_505430 prefixEnd_505430 := by exact prefixLift 505430
  have htrace : WordTrace (prefixWord ++ tailWord_505430) baseStart_505430 baseEnd_505430 := by
    simpa [prefixWord, tailWord_505430, baseEnd_505430] using wordTrace_append hprefix tailTrace_505430
  have hstable : (prefixWord ++ tailWord_505430).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505430).length < 2 ^ (prefixWord ++ tailWord_505430).sum := by decide
  have hdescent : baseEnd_505430 < baseStart_505430 := by decide
  rcases family_descends (prefixWord ++ tailWord_505430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505436 : List Nat := [2, 2, 4, 1, 2, 3, 5]
def baseStart_505436 : Nat := 118140960795 + 505436 * 2 ^ 59
def prefixEnd_505436 : Nat := 4983230072969 + 3 ^ 40 * 505436 * 2
def baseEnd_505436 : Nat := 51265502831800437140849

theorem tailTrace_505436 : CollatzResearch.WordTrace tailWord_505436 prefixEnd_505436 51265502831800437140849 := by
  unfold tailWord_505436
  simp only [CollatzResearch.WordTrace]
  refine ⟨9217382698449584220748081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12289843597932778960997441 9217382698449584220748081)
  ·
    refine ⟨6913037023837188165561061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9217382698449584220748081 6913037023837188165561061)
    ·
      refine ⟨1296194441969472781042699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6913037023837188165561061 1296194441969472781042699)
      ·
        refine ⟨1944291662954209171564049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1296194441969472781042699 1944291662954209171564049)
        ·
          refine ⟨1458218747215656878673037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1944291662954209171564049 1458218747215656878673037)
          ·
            refine ⟨546832030205871329502389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1458218747215656878673037 546832030205871329502389)
            ·
              refine ⟨51265502831800437140849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 546832030205871329502389 51265502831800437140849)
              ·
                rfl

theorem cell19_505436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 5].length) (baseStart_505436 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_505436 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_505436 prefixEnd_505436 := by exact prefixLift 505436
  have htrace : WordTrace (prefixWord ++ tailWord_505436) baseStart_505436 baseEnd_505436 := by
    simpa [prefixWord, tailWord_505436, baseEnd_505436] using wordTrace_append hprefix tailTrace_505436
  have hstable : (prefixWord ++ tailWord_505436).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505436).length < 2 ^ (prefixWord ++ tailWord_505436).sum := by decide
  have hdescent : baseEnd_505436 < baseStart_505436 := by decide
  rcases family_descends (prefixWord ++ tailWord_505436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505607 : List Nat := [1, 1, 4, 4, 2, 2, 5]
def baseStart_505607 : Nat := 118140960795 + 505607 * 2 ^ 59
def prefixEnd_505607 : Nat := 4983230072969 + 3 ^ 40 * 505607 * 2
def baseEnd_505607 : Nat := 51282847067241193874027

theorem tailTrace_505607 : CollatzResearch.WordTrace tailWord_505607 prefixEnd_505607 51282847067241193874027 := by
  unfold tailWord_505607
  simp only [CollatzResearch.WordTrace]
  refine ⟨18441002279279664645971075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12294001519519776430647383 18441002279279664645971075)
  ·
    refine ⟨27661503418919496968956613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18441002279279664645971075 27661503418919496968956613)
    ·
      refine ⟨5186531891047405681679365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27661503418919496968956613 5186531891047405681679365)
      ·
        refine ⟨972474729571388565314881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5186531891047405681679365 972474729571388565314881)
        ·
          refine ⟨729356047178541423986161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 972474729571388565314881 729356047178541423986161)
          ·
            refine ⟨547017035383906067989621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 729356047178541423986161 547017035383906067989621)
            ·
              refine ⟨51282847067241193874027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 547017035383906067989621 51282847067241193874027)
              ·
                rfl

theorem cell19_505607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 5].length) (baseStart_505607 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_505607 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_505607 prefixEnd_505607 := by exact prefixLift 505607
  have htrace : WordTrace (prefixWord ++ tailWord_505607) baseStart_505607 baseEnd_505607 := by
    simpa [prefixWord, tailWord_505607, baseEnd_505607] using wordTrace_append hprefix tailTrace_505607
  have hstable : (prefixWord ++ tailWord_505607).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505607).length < 2 ^ (prefixWord ++ tailWord_505607).sum := by decide
  have hdescent : baseEnd_505607 < baseStart_505607 := by decide
  rcases family_descends (prefixWord ++ tailWord_505607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505611 : List Nat := [1, 1, 1, 1, 5, 1, 9]
def baseStart_505611 : Nat := 118140960795 + 505611 * 2 ^ 59
def prefixEnd_505611 : Nat := 4983230072969 + 3 ^ 40 * 505611 * 2
def baseEnd_505611 : Nat := 51283252780350919177727

theorem tailTrace_505611 : CollatzResearch.WordTrace tailWord_505611 prefixEnd_505611 51283252780350919177727 := by
  unfold tailWord_505611
  simp only [CollatzResearch.WordTrace]
  refine ⟨18441148171265173329116687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12294098780843448886077791 18441148171265173329116687)
  ·
    refine ⟨27661722256897759993675031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18441148171265173329116687 27661722256897759993675031)
    ·
      refine ⟨41492583385346639990512547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27661722256897759993675031 41492583385346639990512547)
      ·
        refine ⟨62238875078019959985768821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41492583385346639990512547 62238875078019959985768821)
        ·
          refine ⟨5834894538564371248665827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62238875078019959985768821 5834894538564371248665827)
          ·
            refine ⟨8752341807846556872998741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5834894538564371248665827 8752341807846556872998741)
            ·
              refine ⟨51283252780350919177727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8752341807846556872998741 51283252780350919177727)
              ·
                rfl

theorem cell19_505611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 9].length) (baseStart_505611 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_505611 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_505611 prefixEnd_505611 := by exact prefixLift 505611
  have htrace : WordTrace (prefixWord ++ tailWord_505611) baseStart_505611 baseEnd_505611 := by
    simpa [prefixWord, tailWord_505611, baseEnd_505611] using wordTrace_append hprefix tailTrace_505611
  have hstable : (prefixWord ++ tailWord_505611).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505611).length < 2 ^ (prefixWord ++ tailWord_505611).sum := by decide
  have hdescent : baseEnd_505611 < baseStart_505611 := by decide
  rcases family_descends (prefixWord ++ tailWord_505611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505628 : List Nat := [2, 2, 3, 1, 1, 2, 4, 4]
def baseStart_505628 : Nat := 118140960795 + 505628 * 2 ^ 59
def prefixEnd_505628 : Nat := 4983230072969 + 3 ^ 40 * 505628 * 2
def baseEnd_505628 : Nat := 153854931183201755155357

theorem tailTrace_505628 : CollatzResearch.WordTrace tailWord_505628 prefixEnd_505628 153854931183201755155357 := by
  unfold tailWord_505628
  simp only [CollatzResearch.WordTrace]
  refine ⟨9220884106101792616242769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12294512141469056821657025 9220884106101792616242769)
  ·
    refine ⟨6915663079576344462182077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9220884106101792616242769 6915663079576344462182077)
    ·
      refine ⟨2593373654841129173318279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6915663079576344462182077 2593373654841129173318279)
      ·
        refine ⟨3890060482261693759977419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2593373654841129173318279 3890060482261693759977419)
        ·
          refine ⟨5835090723392540639966129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3890060482261693759977419 5835090723392540639966129)
          ·
            refine ⟨4376318042544405479974597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5835090723392540639966129 4376318042544405479974597)
            ·
              refine ⟨820559632977076027495237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4376318042544405479974597 820559632977076027495237)
              ·
                refine ⟨153854931183201755155357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 820559632977076027495237 153854931183201755155357)
                ·
                  rfl

theorem cell19_505628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4, 4].length) (baseStart_505628 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_505628 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_505628 prefixEnd_505628 := by exact prefixLift 505628
  have htrace : WordTrace (prefixWord ++ tailWord_505628) baseStart_505628 baseEnd_505628 := by
    simpa [prefixWord, tailWord_505628, baseEnd_505628] using wordTrace_append hprefix tailTrace_505628
  have hstable : (prefixWord ++ tailWord_505628).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505628).length < 2 ^ (prefixWord ++ tailWord_505628).sum := by decide
  have hdescent : baseEnd_505628 < baseStart_505628 := by decide
  rcases family_descends (prefixWord ++ tailWord_505628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505685 : List Nat := [1, 3, 2, 2, 2, 2, 3, 4]
def baseStart_505685 : Nat := 118140960795 + 505685 * 2 ^ 59
def prefixEnd_505685 : Nat := 4983230072969 + 3 ^ 40 * 505685 * 2
def baseEnd_505685 : Nat := 153872275418642511888535

theorem tailTrace_505685 : CollatzResearch.WordTrace tailWord_505685 prefixEnd_505685 153872275418642511888535 := by
  unfold tailWord_505685
  simp only [CollatzResearch.WordTrace]
  refine ⟨18443847172997083967310509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12295898115331389311540339 18443847172997083967310509)
  ·
    refine ⟨6916442689873906487741441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18443847172997083967310509 6916442689873906487741441)
    ·
      refine ⟨5187332017405429865806081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6916442689873906487741441 5187332017405429865806081)
      ·
        refine ⟨3890499013054072399354561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5187332017405429865806081 3890499013054072399354561)
        ·
          refine ⟨2917874259790554299515921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3890499013054072399354561 2917874259790554299515921)
          ·
            refine ⟨2188405694842915724636941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2917874259790554299515921 2188405694842915724636941)
            ·
              refine ⟨820652135566093396738853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2188405694842915724636941 820652135566093396738853)
              ·
                refine ⟨153872275418642511888535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 820652135566093396738853 153872275418642511888535)
                ·
                  rfl

theorem cell19_505685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3, 4].length) (baseStart_505685 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_505685 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_505685 prefixEnd_505685 := by exact prefixLift 505685
  have htrace : WordTrace (prefixWord ++ tailWord_505685) baseStart_505685 baseEnd_505685 := by
    simpa [prefixWord, tailWord_505685, baseEnd_505685] using wordTrace_append hprefix tailTrace_505685
  have hstable : (prefixWord ++ tailWord_505685).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505685).length < 2 ^ (prefixWord ++ tailWord_505685).sum := by decide
  have hdescent : baseEnd_505685 < baseStart_505685 := by decide
  rcases family_descends (prefixWord ++ tailWord_505685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505774 : List Nat := [4, 1, 5, 1, 1, 2, 5]
def baseStart_505774 : Nat := 118140960795 + 505774 * 2 ^ 59
def prefixEnd_505774 : Nat := 4983230072969 + 3 ^ 40 * 505774 * 2
def baseEnd_505774 : Nat := 51299785589572225303505

theorem tailTrace_505774 : CollatzResearch.WordTrace tailWord_505774 prefixEnd_505774 51299785589572225303505 := by
  unfold tailWord_505774
  simp only [CollatzResearch.WordTrace]
  refine ⟨2305886658709331520912547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12298062179783101444866917 2305886658709331520912547)
  ·
    refine ⟨3458829988063997281368821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2305886658709331520912547 3458829988063997281368821)
    ·
      refine ⟨324265311380999745128327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3458829988063997281368821 324265311380999745128327)
      ·
        refine ⟨486397967071499617692491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324265311380999745128327 486397967071499617692491)
        ·
          refine ⟨729596950607249426538737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 486397967071499617692491 729596950607249426538737)
          ·
            refine ⟨547197712955437069904053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 729596950607249426538737 547197712955437069904053)
            ·
              refine ⟨51299785589572225303505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 547197712955437069904053 51299785589572225303505)
              ·
                rfl

theorem cell19_505774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 5].length) (baseStart_505774 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_505774 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_505774 prefixEnd_505774 := by exact prefixLift 505774
  have htrace : WordTrace (prefixWord ++ tailWord_505774) baseStart_505774 baseEnd_505774 := by
    simpa [prefixWord, tailWord_505774, baseEnd_505774] using wordTrace_append hprefix tailTrace_505774
  have hstable : (prefixWord ++ tailWord_505774).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505774).length < 2 ^ (prefixWord ++ tailWord_505774).sum := by decide
  have hdescent : baseEnd_505774 < baseStart_505774 := by decide
  rcases family_descends (prefixWord ++ tailWord_505774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505837 : List Nat := [1, 5, 1, 4, 8]
def baseStart_505837 : Nat := 118140960795 + 505837 * 2 ^ 59
def prefixEnd_505837 : Nat := 4983230072969 + 3 ^ 40 * 505837 * 2
def baseEnd_505837 : Nat := 5700686174561155426309

theorem tailTrace_505837 : CollatzResearch.WordTrace tailWord_505837 prefixEnd_505837 5700686174561155426309 := by
  unfold tailWord_505837
  simp only [CollatzResearch.WordTrace]
  refine ⟨18449391068446413926843765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12299594045630942617895843 18449391068446413926843765)
  ·
    refine ⟨1729630412666851305641603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18449391068446413926843765 1729630412666851305641603)
    ·
      refine ⟨2594445619000276958462405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1729630412666851305641603 2594445619000276958462405)
      ·
        refine ⟨486458553562551929711701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2594445619000276958462405 486458553562551929711701)
        ·
          refine ⟨5700686174561155426309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 486458553562551929711701 5700686174561155426309)
          ·
            rfl

theorem cell19_505837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 8].length) (baseStart_505837 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_505837 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_505837 prefixEnd_505837 := by exact prefixLift 505837
  have htrace : WordTrace (prefixWord ++ tailWord_505837) baseStart_505837 baseEnd_505837 := by
    simpa [prefixWord, tailWord_505837, baseEnd_505837] using wordTrace_append hprefix tailTrace_505837
  have hstable : (prefixWord ++ tailWord_505837).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505837).length < 2 ^ (prefixWord ++ tailWord_505837).sum := by decide
  have hdescent : baseEnd_505837 < baseStart_505837 := by decide
  rcases family_descends (prefixWord ++ tailWord_505837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505854 : List Nat := [4, 2, 2, 2, 1, 1, 3, 4]
def baseStart_505854 : Nat := 118140960795 + 505854 * 2 ^ 59
def prefixEnd_505854 : Nat := 4983230072969 + 3 ^ 40 * 505854 * 2
def baseEnd_505854 : Nat := 153923699555300194132519

theorem tailTrace_505854 : CollatzResearch.WordTrace tailWord_505854 prefixEnd_505854 153923699555300194132519 := by
  unfold tailWord_505854
  simp only [CollatzResearch.WordTrace]
  refine ⟨2306251388673103228776577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12300007406256550553475077 2306251388673103228776577)
  ·
    refine ⟨1729688541504827421582433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2306251388673103228776577 1729688541504827421582433)
    ·
      refine ⟨1297266406128620566186825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1729688541504827421582433 1297266406128620566186825)
      ·
        refine ⟨972949804596465424640119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1297266406128620566186825 972949804596465424640119)
        ·
          refine ⟨1459424706894698136960179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 972949804596465424640119 1459424706894698136960179)
          ·
            refine ⟨2189137060342047205440269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1459424706894698136960179 2189137060342047205440269)
            ·
              refine ⟨820926397628267702040101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2189137060342047205440269 820926397628267702040101)
              ·
                refine ⟨153923699555300194132519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 820926397628267702040101 153923699555300194132519)
                ·
                  rfl

theorem cell19_505854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3, 4].length) (baseStart_505854 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_505854 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_505854 prefixEnd_505854 := by exact prefixLift 505854
  have htrace : WordTrace (prefixWord ++ tailWord_505854) baseStart_505854 baseEnd_505854 := by
    simpa [prefixWord, tailWord_505854, baseEnd_505854] using wordTrace_append hprefix tailTrace_505854
  have hstable : (prefixWord ++ tailWord_505854).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505854).length < 2 ^ (prefixWord ++ tailWord_505854).sum := by decide
  have hdescent : baseEnd_505854 < baseStart_505854 := by decide
  rcases family_descends (prefixWord ++ tailWord_505854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505932 : List Nat := [2, 2, 1, 3, 1, 1, 6, 3]
def baseStart_505932 : Nat := 118140960795 + 505932 * 2 ^ 59
def prefixEnd_505932 : Nat := 4983230072969 + 3 ^ 40 * 505932 * 2
def baseEnd_505932 : Nat := 153947433772219124398973

theorem tailTrace_505932 : CollatzResearch.WordTrace tailWord_505932 prefixEnd_505932 153947433772219124398973 := by
  unfold tailWord_505932
  simp only [CollatzResearch.WordTrace]
  refine ⟨9226428001551122575776025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12301904002068163434368033 9226428001551122575776025)
  ·
    refine ⟨6919821001163341931832019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9226428001551122575776025 6919821001163341931832019)
    ·
      refine ⟨10379731501745012897748029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6919821001163341931832019 10379731501745012897748029)
      ·
        refine ⟨3892399313154379836655511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10379731501745012897748029 3892399313154379836655511)
        ·
          refine ⟨5838598969731569754983267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3892399313154379836655511 5838598969731569754983267)
          ·
            refine ⟨8757898454597354632474901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5838598969731569754983267 8757898454597354632474901)
            ·
              refine ⟨410526490059250998397261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 8757898454597354632474901 410526490059250998397261)
              ·
                refine ⟨153947433772219124398973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 410526490059250998397261 153947433772219124398973)
                ·
                  rfl

theorem cell19_505932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 6, 3].length) (baseStart_505932 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_505932 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_505932 prefixEnd_505932 := by exact prefixLift 505932
  have htrace : WordTrace (prefixWord ++ tailWord_505932) baseStart_505932 baseEnd_505932 := by
    simpa [prefixWord, tailWord_505932, baseEnd_505932] using wordTrace_append hprefix tailTrace_505932
  have hstable : (prefixWord ++ tailWord_505932).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505932).length < 2 ^ (prefixWord ++ tailWord_505932).sum := by decide
  have hdescent : baseEnd_505932 < baseStart_505932 := by decide
  rcases family_descends (prefixWord ++ tailWord_505932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505949 : List Nat := [1, 4, 4, 1, 1, 3, 5]
def baseStart_505949 : Nat := 118140960795 + 505949 * 2 ^ 59
def prefixEnd_505949 : Nat := 4983230072969 + 3 ^ 40 * 505949 * 2
def baseEnd_505949 : Nat := 51317535538122707340383

theorem tailTrace_505949 : CollatzResearch.WordTrace tailWord_505949 prefixEnd_505949 51317535538122707340383 := by
  unfold tailWord_505949
  simp only [CollatzResearch.WordTrace]
  refine ⟨18453476044040657054920901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12302317362693771369947267 18453476044040657054920901)
  ·
    refine ⟨3460026758257623197797669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18453476044040657054920901 3460026758257623197797669)
    ·
      refine ⟨648755017173304349587063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3460026758257623197797669 648755017173304349587063)
      ·
        refine ⟨973132525759956524380595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 648755017173304349587063 973132525759956524380595)
        ·
          refine ⟨1459698788639934786570893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 973132525759956524380595 1459698788639934786570893)
          ·
            refine ⟨547387045739975544964085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1459698788639934786570893 547387045739975544964085)
            ·
              refine ⟨51317535538122707340383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 547387045739975544964085 51317535538122707340383)
              ·
                rfl

theorem cell19_505949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 5].length) (baseStart_505949 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_505949 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_505949 prefixEnd_505949 := by exact prefixLift 505949
  have htrace : WordTrace (prefixWord ++ tailWord_505949) baseStart_505949 baseEnd_505949 := by
    simpa [prefixWord, tailWord_505949, baseEnd_505949] using wordTrace_append hprefix tailTrace_505949
  have hstable : (prefixWord ++ tailWord_505949).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505949).length < 2 ^ (prefixWord ++ tailWord_505949).sum := by decide
  have hdescent : baseEnd_505949 < baseStart_505949 := by decide
  rcases family_descends (prefixWord ++ tailWord_505949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505970 : List Nat := [3, 2, 1, 2, 2, 3, 2, 4]
def baseStart_505970 : Nat := 118140960795 + 505970 * 2 ^ 59
def prefixEnd_505970 : Nat := 4983230072969 + 3 ^ 40 * 505970 * 2
def baseEnd_505970 : Nat := 153958996595846295554425

theorem tailTrace_505970 : CollatzResearch.WordTrace tailWord_505970 prefixEnd_505970 153958996595846295554425 := by
  unfold tailWord_505970
  simp only [CollatzResearch.WordTrace]
  refine ⟨4613560494241144410358841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12302827984643051760956909 4613560494241144410358841)
  ·
    refine ⟨3460170370680858307769131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4613560494241144410358841 3460170370680858307769131)
    ·
      refine ⟨5190255556021287461653697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3460170370680858307769131 5190255556021287461653697)
      ·
        refine ⟨3892691667015965596240273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5190255556021287461653697 3892691667015965596240273)
        ·
          refine ⟨2919518750261974197180205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3892691667015965596240273 2919518750261974197180205)
          ·
            refine ⟨1094819531348240323942577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2919518750261974197180205 1094819531348240323942577)
            ·
              refine ⟨821114648511180242956933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1094819531348240323942577 821114648511180242956933)
              ·
                refine ⟨153958996595846295554425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 821114648511180242956933 153958996595846295554425)
                ·
                  rfl

theorem cell19_505970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2, 4].length) (baseStart_505970 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_505970 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_505970 prefixEnd_505970 := by exact prefixLift 505970
  have htrace : WordTrace (prefixWord ++ tailWord_505970) baseStart_505970 baseEnd_505970 := by
    simpa [prefixWord, tailWord_505970, baseEnd_505970] using wordTrace_append hprefix tailTrace_505970
  have hstable : (prefixWord ++ tailWord_505970).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505970).length < 2 ^ (prefixWord ++ tailWord_505970).sum := by decide
  have hdescent : baseEnd_505970 < baseStart_505970 := by decide
  rcases family_descends (prefixWord ++ tailWord_505970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505991 : List Nat := [1, 1, 4, 2, 1, 1, 4, 5]
def baseStart_505991 : Nat := 118140960795 + 505991 * 2 ^ 59
def prefixEnd_505991 : Nat := 4983230072969 + 3 ^ 40 * 505991 * 2
def baseEnd_505991 : Nat := 153965386577324469087701

theorem tailTrace_505991 : CollatzResearch.WordTrace tailWord_505991 prefixEnd_505991 153965386577324469087701 := by
  unfold tailWord_505991
  simp only [CollatzResearch.WordTrace]
  refine ⟨18455007909888498227949827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12303338606592332151966551 18455007909888498227949827)
  ·
    refine ⟨27682511864832747341924741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18455007909888498227949827 27682511864832747341924741)
    ·
      refine ⟨5190470974656140126610889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27682511864832747341924741 5190470974656140126610889)
      ·
        refine ⟨3892853230992105094958167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5190470974656140126610889 3892853230992105094958167)
        ·
          refine ⟨5839279846488157642437251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3892853230992105094958167 5839279846488157642437251)
          ·
            refine ⟨8758919769732236463655877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5839279846488157642437251 8758919769732236463655877)
            ·
              refine ⟨1642297456824794336935477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8758919769732236463655877 1642297456824794336935477)
              ·
                refine ⟨153965386577324469087701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1642297456824794336935477 153965386577324469087701)
                ·
                  rfl

theorem cell19_505991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 5].length) (baseStart_505991 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_505991 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_505991 prefixEnd_505991 := by exact prefixLift 505991
  have htrace : WordTrace (prefixWord ++ tailWord_505991) baseStart_505991 baseEnd_505991 := by
    simpa [prefixWord, tailWord_505991, baseEnd_505991] using wordTrace_append hprefix tailTrace_505991
  have hstable : (prefixWord ++ tailWord_505991).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505991).length < 2 ^ (prefixWord ++ tailWord_505991).sum := by decide
  have hdescent : baseEnd_505991 < baseStart_505991 := by decide
  rcases family_descends (prefixWord ++ tailWord_505991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506008 : List Nat := [2, 1, 2, 4, 4, 6]
def baseStart_506008 : Nat := 118140960795 + 506008 * 2 ^ 59
def prefixEnd_506008 : Nat := 4983230072969 + 3 ^ 40 * 506008 * 2
def baseEnd_506008 : Nat := 17107839935497051856653

theorem tailTrace_506008 : CollatzResearch.WordTrace tailWord_506008 prefixEnd_506008 17107839935497051856653 := by
  unfold tailWord_506008
  simp only [CollatzResearch.WordTrace]
  refine ⟨9227813975413455065659339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12303751967217940087545785 9227813975413455065659339)
  ·
    refine ⟨13841720963120182598489009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9227813975413455065659339 13841720963120182598489009)
    ·
      refine ⟨10381290722340136948866757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13841720963120182598489009 10381290722340136948866757)
      ·
        refine ⟨1946492010438775677912517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10381290722340136948866757 1946492010438775677912517)
        ·
          refine ⟨364967251957270439608597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1946492010438775677912517 364967251957270439608597)
          ·
            refine ⟨17107839935497051856653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 364967251957270439608597 17107839935497051856653)
            ·
              rfl

theorem cell19_506008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 6].length) (baseStart_506008 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_506008 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_506008 prefixEnd_506008 := by exact prefixLift 506008
  have htrace : WordTrace (prefixWord ++ tailWord_506008) baseStart_506008 baseEnd_506008 := by
    simpa [prefixWord, tailWord_506008, baseEnd_506008] using wordTrace_append hprefix tailTrace_506008
  have hstable : (prefixWord ++ tailWord_506008).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506008).length < 2 ^ (prefixWord ++ tailWord_506008).sum := by decide
  have hdescent : baseEnd_506008 < baseStart_506008 := by decide
  rcases family_descends (prefixWord ++ tailWord_506008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506010 : List Nat := [3, 1, 1, 5, 9]
def baseStart_506010 : Nat := 118140960795 + 506010 * 2 ^ 59
def prefixEnd_506010 : Nat := 4983230072969 + 3 ^ 40 * 506010 * 2
def baseEnd_506010 : Nat := 5702635851449557580201

theorem tailTrace_506010 : CollatzResearch.WordTrace tailWord_506010 prefixEnd_506010 5702635851449557580201 := by
  unfold tailWord_506010
  simp only [CollatzResearch.WordTrace]
  refine ⟨4613925224204916118222871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12303800597879776315260989 4613925224204916118222871)
  ·
    refine ⟨6920887836307374177334307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4613925224204916118222871 6920887836307374177334307)
    ·
      refine ⟨10381331754461061266001461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6920887836307374177334307 10381331754461061266001461)
      ·
        refine ⟨973249851980724493687637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10381331754461061266001461 973249851980724493687637)
        ·
          refine ⟨5702635851449557580201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 973249851980724493687637 5702635851449557580201)
          ·
            rfl

theorem cell19_506010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 9].length) (baseStart_506010 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_506010 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_506010 prefixEnd_506010 := by exact prefixLift 506010
  have htrace : WordTrace (prefixWord ++ tailWord_506010) baseStart_506010 baseEnd_506010 := by
    simpa [prefixWord, tailWord_506010, baseEnd_506010] using wordTrace_append hprefix tailTrace_506010
  have hstable : (prefixWord ++ tailWord_506010).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506010).length < 2 ^ (prefixWord ++ tailWord_506010).sum := by decide
  have hdescent : baseEnd_506010 < baseStart_506010 := by decide
  rcases family_descends (prefixWord ++ tailWord_506010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506023 : List Nat := [1, 1, 6, 2, 3, 1, 1, 4]
def baseStart_506023 : Nat := 118140960795 + 506023 * 2 ^ 59
def prefixEnd_506023 : Nat := 4983230072969 + 3 ^ 40 * 506023 * 2
def baseEnd_506023 : Nat := 153975123691957876376503

theorem tailTrace_506023 : CollatzResearch.WordTrace tailWord_506023 prefixEnd_506023 153975123691957876376503 := by
  unfold tailWord_506023
  simp only [CollatzResearch.WordTrace]
  refine ⟨18456175045772567693114723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12304116697181711795409815 18456175045772567693114723)
  ·
    refine ⟨27684262568658851539672085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18456175045772567693114723 27684262568658851539672085)
    ·
      refine ⟨1297699807905883665922129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 27684262568658851539672085 1297699807905883665922129)
      ·
        refine ⟨973274855929412749441597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1297699807905883665922129 973274855929412749441597)
        ·
          refine ⟨364978070973529781040599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 973274855929412749441597 364978070973529781040599)
          ·
            refine ⟨547467106460294671560899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 364978070973529781040599 547467106460294671560899)
            ·
              refine ⟨821200659690442007341349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 547467106460294671560899 821200659690442007341349)
              ·
                refine ⟨153975123691957876376503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 821200659690442007341349 153975123691957876376503)
                ·
                  rfl

theorem cell19_506023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 1, 4].length) (baseStart_506023 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_506023 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_506023 prefixEnd_506023 := by exact prefixLift 506023
  have htrace : WordTrace (prefixWord ++ tailWord_506023) baseStart_506023 baseEnd_506023 := by
    simpa [prefixWord, tailWord_506023, baseEnd_506023] using wordTrace_append hprefix tailTrace_506023
  have hstable : (prefixWord ++ tailWord_506023).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506023).length < 2 ^ (prefixWord ++ tailWord_506023).sum := by decide
  have hdescent : baseEnd_506023 < baseStart_506023 := by decide
  rcases family_descends (prefixWord ++ tailWord_506023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506044 : List Nat := [2, 2, 2, 3, 3, 1, 3, 3]
def baseStart_506044 : Nat := 118140960795 + 506044 * 2 ^ 59
def prefixEnd_506044 : Nat := 4983230072969 + 3 ^ 40 * 506044 * 2
def baseEnd_506044 : Nat := 153981513673436049909779

theorem tailTrace_506044 : CollatzResearch.WordTrace tailWord_506044 prefixEnd_506044 153981513673436049909779 := by
  unfold tailWord_506044
  simp only [CollatzResearch.WordTrace]
  refine ⟨9228470489348244139814593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12304627319130992186419457 9228470489348244139814593)
  ·
    refine ⟨6921352867011183104860945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9228470489348244139814593 6921352867011183104860945)
    ·
      refine ⟨5191014650258387328645709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6921352867011183104860945 5191014650258387328645709)
      ·
        refine ⟨1946630493846895248242141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5191014650258387328645709 1946630493846895248242141)
        ·
          refine ⟨729986435192585718090803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1946630493846895248242141 729986435192585718090803)
          ·
            refine ⟨1094979652788878577136205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 729986435192585718090803 1094979652788878577136205)
            ·
              refine ⟨410617369795829466426077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1094979652788878577136205 410617369795829466426077)
              ·
                refine ⟨153981513673436049909779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 410617369795829466426077 153981513673436049909779)
                ·
                  rfl

theorem cell19_506044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 3, 3].length) (baseStart_506044 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_506044 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_506044 prefixEnd_506044 := by exact prefixLift 506044
  have htrace : WordTrace (prefixWord ++ tailWord_506044) baseStart_506044 baseEnd_506044 := by
    simpa [prefixWord, tailWord_506044, baseEnd_506044] using wordTrace_append hprefix tailTrace_506044
  have hstable : (prefixWord ++ tailWord_506044).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506044).length < 2 ^ (prefixWord ++ tailWord_506044).sum := by decide
  have hdescent : baseEnd_506044 < baseStart_506044 := by decide
  rcases family_descends (prefixWord ++ tailWord_506044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506143 : List Nat := [1, 1, 2, 4, 3, 1, 1, 6]
def baseStart_506143 : Nat := 118140960795 + 506143 * 2 ^ 59
def prefixEnd_506143 : Nat := 4983230072969 + 3 ^ 40 * 506143 * 2
def baseEnd_506143 : Nat := 154011637871833153709509

theorem tailTrace_506143 : CollatzResearch.WordTrace tailWord_506143 prefixEnd_506143 154011637871833153709509 := by
  unfold tailWord_506143
  simp only [CollatzResearch.WordTrace]
  refine ⟨18460551805337828187483083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12307034536891885458322055 18460551805337828187483083)
  ·
    refine ⟨27690827708006742281224625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18460551805337828187483083 27690827708006742281224625)
    ·
      refine ⟨20768120781005056710918469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27690827708006742281224625 20768120781005056710918469)
      ·
        refine ⟨3894022646438448133297213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20768120781005056710918469 3894022646438448133297213)
        ·
          refine ⟨1460258492414418049986455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3894022646438448133297213 1460258492414418049986455)
          ·
            refine ⟨2190387738621627074979683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1460258492414418049986455 2190387738621627074979683)
            ·
              refine ⟨3285581607932440612469525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2190387738621627074979683 3285581607932440612469525)
              ·
                refine ⟨154011637871833153709509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3285581607932440612469525 154011637871833153709509)
                ·
                  rfl

theorem cell19_506143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 6].length) (baseStart_506143 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_506143 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_506143 prefixEnd_506143 := by exact prefixLift 506143
  have htrace : WordTrace (prefixWord ++ tailWord_506143) baseStart_506143 baseEnd_506143 := by
    simpa [prefixWord, tailWord_506143, baseEnd_506143] using wordTrace_append hprefix tailTrace_506143
  have hstable : (prefixWord ++ tailWord_506143).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506143).length < 2 ^ (prefixWord ++ tailWord_506143).sum := by decide
  have hdescent : baseEnd_506143 < baseStart_506143 := by decide
  rcases family_descends (prefixWord ++ tailWord_506143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506270 : List Nat := [4, 3, 1, 2, 1, 3, 2, 3]
def baseStart_506270 : Nat := 118140960795 + 506270 * 2 ^ 59
def prefixEnd_506270 : Nat := 4983230072969 + 3 ^ 40 * 506270 * 2
def baseEnd_506270 : Nat := 154050282045534488886941

theorem tailTrace_506270 : CollatzResearch.WordTrace tailWord_506270 prefixEnd_506270 154050282045534488886941 := by
  unfold tailWord_506270
  simp only [CollatzResearch.WordTrace]
  refine ⟨2308147984484716109669533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12310122583918485918237509 2308147984484716109669533)
  ·
    refine ⟨865555494181768541126075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2308147984484716109669533 865555494181768541126075)
    ·
      refine ⟨1298333241272652811689113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 865555494181768541126075 1298333241272652811689113)
      ·
        refine ⟨973749930954489608766835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1298333241272652811689113 973749930954489608766835)
        ·
          refine ⟨1460624896431734413150253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 973749930954489608766835 1460624896431734413150253)
          ·
            refine ⟨547734336161900404931345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1460624896431734413150253 547734336161900404931345)
            ·
              refine ⟨410800752121425303698509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 547734336161900404931345 410800752121425303698509)
              ·
                refine ⟨154050282045534488886941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 410800752121425303698509 154050282045534488886941)
                ·
                  rfl

theorem cell19_506270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 2, 3].length) (baseStart_506270 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_506270 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_506270 prefixEnd_506270 := by exact prefixLift 506270
  have htrace : WordTrace (prefixWord ++ tailWord_506270) baseStart_506270 baseEnd_506270 := by
    simpa [prefixWord, tailWord_506270, baseEnd_506270] using wordTrace_append hprefix tailTrace_506270
  have hstable : (prefixWord ++ tailWord_506270).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506270).length < 2 ^ (prefixWord ++ tailWord_506270).sum := by decide
  have hdescent : baseEnd_506270 < baseStart_506270 := by decide
  rcases family_descends (prefixWord ++ tailWord_506270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506293 : List Nat := [1, 3, 3, 2, 3, 2, 5]
def baseStart_506293 : Nat := 118140960795 + 506293 * 2 ^ 59
def prefixEnd_506293 : Nat := 4983230072969 + 3 ^ 40 * 506293 * 2
def baseEnd_506293 : Nat := 51352426865559083458589

theorem tailTrace_506293 : CollatzResearch.WordTrace tailWord_506293 prefixEnd_506293 51352426865559083458589 := by
  unfold tailWord_506293
  simp only [CollatzResearch.WordTrace]
  refine ⟨18466022754794403805443533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12310681836529602536962355 18466022754794403805443533)
  ·
    refine ⟨6924758533047901427041325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18466022754794403805443533 6924758533047901427041325)
    ·
      refine ⟨2596784449892963035140497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6924758533047901427041325 2596784449892963035140497)
      ·
        refine ⟨1947588337419722276355373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2596784449892963035140497 1947588337419722276355373)
        ·
          refine ⟨730345626532395853633265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1947588337419722276355373 730345626532395853633265)
          ·
            refine ⟨547759219899296890224949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 730345626532395853633265 547759219899296890224949)
            ·
              refine ⟨51352426865559083458589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 547759219899296890224949 51352426865559083458589)
              ·
                rfl

theorem cell19_506293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 5].length) (baseStart_506293 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_506293 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_506293 prefixEnd_506293 := by exact prefixLift 506293
  have htrace : WordTrace (prefixWord ++ tailWord_506293) baseStart_506293 baseEnd_506293 := by
    simpa [prefixWord, tailWord_506293, baseEnd_506293] using wordTrace_append hprefix tailTrace_506293
  have hstable : (prefixWord ++ tailWord_506293).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506293).length < 2 ^ (prefixWord ++ tailWord_506293).sum := by decide
  have hdescent : baseEnd_506293 < baseStart_506293 := by decide
  rcases family_descends (prefixWord ++ tailWord_506293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506295 : List Nat := [1, 1, 3, 1, 3, 5, 5]
def baseStart_506295 : Nat := 118140960795 + 506295 * 2 ^ 59
def prefixEnd_506295 : Nat := 4983230072969 + 3 ^ 40 * 506295 * 2
def baseEnd_506295 : Nat := 51352629722113946110439

theorem tailTrace_506295 : CollatzResearch.WordTrace tailWord_506295 prefixEnd_506295 51352629722113946110439 := by
  unfold tailWord_506295
  simp only [CollatzResearch.WordTrace]
  refine ⟨18466095700787158147016339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12310730467191438764677559 18466095700787158147016339)
  ·
    refine ⟨27699143551180737220524509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18466095700787158147016339 27699143551180737220524509)
    ·
      refine ⟨10387178831692776457696691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27699143551180737220524509 10387178831692776457696691)
      ·
        refine ⟨15580768247539164686545037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10387178831692776457696691 15580768247539164686545037)
        ·
          refine ⟨5842788092827186757454389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15580768247539164686545037 5842788092827186757454389)
          ·
            refine ⟨547761383702548758511349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5842788092827186757454389 547761383702548758511349)
            ·
              refine ⟨51352629722113946110439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 547761383702548758511349 51352629722113946110439)
              ·
                rfl

theorem cell19_506295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 5].length) (baseStart_506295 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_506295 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_506295 prefixEnd_506295 := by exact prefixLift 506295
  have htrace : WordTrace (prefixWord ++ tailWord_506295) baseStart_506295 baseEnd_506295 := by
    simpa [prefixWord, tailWord_506295, baseEnd_506295] using wordTrace_append hprefix tailTrace_506295
  have hstable : (prefixWord ++ tailWord_506295).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506295).length < 2 ^ (prefixWord ++ tailWord_506295).sum := by decide
  have hdescent : baseEnd_506295 < baseStart_506295 := by decide
  rcases family_descends (prefixWord ++ tailWord_506295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506314 : List Nat := [3, 1, 2, 1, 2, 2, 4, 4]
def baseStart_506314 : Nat := 118140960795 + 506314 * 2 ^ 59
def prefixEnd_506314 : Nat := 4983230072969 + 3 ^ 40 * 506314 * 2
def baseEnd_506314 : Nat := 154063670578155423909043

theorem tailTrace_506314 : CollatzResearch.WordTrace tailWord_506314 prefixEnd_506314 154063670578155423909043 := by
  unfold tailWord_506314
  simp only [CollatzResearch.WordTrace]
  refine ⟨4616697171929581097989499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12311192458478882927971997 4616697171929581097989499)
  ·
    refine ⟨6925045757894371646984249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4616697171929581097989499 6925045757894371646984249)
    ·
      refine ⟨5193784318420778735238187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6925045757894371646984249 5193784318420778735238187)
      ·
        refine ⟨7790676477631168102857281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5193784318420778735238187 7790676477631168102857281)
        ·
          refine ⟨5843007358223376077142961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7790676477631168102857281 5843007358223376077142961)
          ·
            refine ⟨4382255518667532057857221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5843007358223376077142961 4382255518667532057857221)
            ·
              refine ⟨821672909750162260848229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4382255518667532057857221 821672909750162260848229)
              ·
                refine ⟨154063670578155423909043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 821672909750162260848229 154063670578155423909043)
                ·
                  rfl

theorem cell19_506314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4, 4].length) (baseStart_506314 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_506314 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_506314 prefixEnd_506314 := by exact prefixLift 506314
  have htrace : WordTrace (prefixWord ++ tailWord_506314) baseStart_506314 baseEnd_506314 := by
    simpa [prefixWord, tailWord_506314, baseEnd_506314] using wordTrace_append hprefix tailTrace_506314
  have hstable : (prefixWord ++ tailWord_506314).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506314).length < 2 ^ (prefixWord ++ tailWord_506314).sum := by decide
  have hdescent : baseEnd_506314 < baseStart_506314 := by decide
  rcases family_descends (prefixWord ++ tailWord_506314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506333 : List Nat := [1, 4, 3, 1, 1, 1, 1, 7]
def baseStart_506333 : Nat := 118140960795 + 506333 * 2 ^ 59
def prefixEnd_506333 : Nat := 4983230072969 + 3 ^ 40 * 506333 * 2
def baseEnd_506333 : Nat := 154069451989969009486769

theorem tailTrace_506333 : CollatzResearch.WordTrace tailWord_506333 prefixEnd_506333 154069451989969009486769 := by
  unfold tailWord_506333
  simp only [CollatzResearch.WordTrace]
  refine ⟨18467481674649490636899653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12311654449766327091266435 18467481674649490636899653)
  ·
    refine ⟨3462652813996779494418685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18467481674649490636899653 3462652813996779494418685)
    ·
      refine ⟨1298494805248792310407007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3462652813996779494418685 1298494805248792310407007)
      ·
        refine ⟨1947742207873188465610511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1298494805248792310407007 1947742207873188465610511)
        ·
          refine ⟨2921613311809782698415767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1947742207873188465610511 2921613311809782698415767)
          ·
            refine ⟨4382419967714674047623651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2921613311809782698415767 4382419967714674047623651)
            ·
              refine ⟨6573629951572011071435477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4382419967714674047623651 6573629951572011071435477)
              ·
                refine ⟨154069451989969009486769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6573629951572011071435477 154069451989969009486769)
                ·
                  rfl

theorem cell19_506333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 7].length) (baseStart_506333 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_506333 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_506333 prefixEnd_506333 := by exact prefixLift 506333
  have htrace : WordTrace (prefixWord ++ tailWord_506333) baseStart_506333 baseEnd_506333 := by
    simpa [prefixWord, tailWord_506333, baseEnd_506333] using wordTrace_append hprefix tailTrace_506333
  have hstable : (prefixWord ++ tailWord_506333).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506333).length < 2 ^ (prefixWord ++ tailWord_506333).sum := by decide
  have hdescent : baseEnd_506333 < baseStart_506333 := by decide
  rcases family_descends (prefixWord ++ tailWord_506333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506369 : List Nat := [1, 2, 4, 1, 3, 3, 1, 4]
def baseStart_506369 : Nat := 118140960795 + 506369 * 2 ^ 59
def prefixEnd_506369 : Nat := 4983230072969 + 3 ^ 40 * 506369 * 2
def baseEnd_506369 : Nat := 154080406243931592686671

theorem tailTrace_506369 : CollatzResearch.WordTrace tailWord_506369 prefixEnd_506369 154080406243931592686671 := by
  unfold tailWord_506369
  simp only [CollatzResearch.WordTrace]
  refine ⟨18468794702519068785210161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12312529801679379190140107 18468794702519068785210161)
  ·
    refine ⟨13851596026889301588907621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18468794702519068785210161 13851596026889301588907621)
    ·
      refine ⟨2597174255041744047920179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13851596026889301588907621 2597174255041744047920179)
      ·
        refine ⟨3895761382562616071880269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2597174255041744047920179 3895761382562616071880269)
        ·
          refine ⟨1460910518460981026955101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3895761382562616071880269 1460910518460981026955101)
          ·
            refine ⟨547841444422867885108163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1460910518460981026955101 547841444422867885108163)
            ·
              refine ⟨821762166634301827662245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 547841444422867885108163 821762166634301827662245)
              ·
                refine ⟨154080406243931592686671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 821762166634301827662245 154080406243931592686671)
                ·
                  rfl

theorem cell19_506369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 1, 4].length) (baseStart_506369 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_506369 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_506369 prefixEnd_506369 := by exact prefixLift 506369
  have htrace : WordTrace (prefixWord ++ tailWord_506369) baseStart_506369 baseEnd_506369 := by
    simpa [prefixWord, tailWord_506369, baseEnd_506369] using wordTrace_append hprefix tailTrace_506369
  have hstable : (prefixWord ++ tailWord_506369).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506369).length < 2 ^ (prefixWord ++ tailWord_506369).sum := by decide
  have hdescent : baseEnd_506369 < baseStart_506369 := by decide
  rcases family_descends (prefixWord ++ tailWord_506369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506445 : List Nat := [1, 6, 1, 1, 2, 2, 1, 5]
def baseStart_506445 : Nat := 118140960795 + 506445 * 2 ^ 59
def prefixEnd_506445 : Nat := 4983230072969 + 3 ^ 40 * 506445 * 2
def baseEnd_506445 : Nat := 154103531891185934997575

theorem tailTrace_506445 : CollatzResearch.WordTrace tailWord_506445 prefixEnd_506445 154103531891185934997575 := by
  unfold tailWord_506445
  simp only [CollatzResearch.WordTrace]
  refine ⟨18471566650243733764976789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12314377766829155843317859 18471566650243733764976789)
  ·
    refine ⟨865854686730175020233287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 18471566650243733764976789 865854686730175020233287)
    ·
      refine ⟨1298782030095262530349931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 865854686730175020233287 1298782030095262530349931)
      ·
        refine ⟨1948173045142893795524897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1298782030095262530349931 1948173045142893795524897)
        ·
          refine ⟨1461129783857170346643673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1948173045142893795524897 1461129783857170346643673)
          ·
            refine ⟨1095847337892877759982755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1461129783857170346643673 1095847337892877759982755)
            ·
              refine ⟨1643771006839316639974133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1095847337892877759982755 1643771006839316639974133)
              ·
                refine ⟨154103531891185934997575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1643771006839316639974133 154103531891185934997575)
                ·
                  rfl

theorem cell19_506445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 5].length) (baseStart_506445 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_506445 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_506445 prefixEnd_506445 := by exact prefixLift 506445
  have htrace : WordTrace (prefixWord ++ tailWord_506445) baseStart_506445 baseEnd_506445 := by
    simpa [prefixWord, tailWord_506445, baseEnd_506445] using wordTrace_append hprefix tailTrace_506445
  have hstable : (prefixWord ++ tailWord_506445).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506445).length < 2 ^ (prefixWord ++ tailWord_506445).sum := by decide
  have hdescent : baseEnd_506445 < baseStart_506445 := by decide
  rcases family_descends (prefixWord ++ tailWord_506445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506447 : List Nat := [1, 1, 2, 1, 1, 2, 8, 3]
def baseStart_506447 : Nat := 118140960795 + 506447 * 2 ^ 59
def prefixEnd_506447 : Nat := 4983230072969 + 3 ^ 40 * 506447 * 2
def baseEnd_506447 : Nat := 154104140460850522953125

theorem tailTrace_506447 : CollatzResearch.WordTrace tailWord_506447 prefixEnd_506447 154104140460850522953125 := by
  unfold tailWord_506447
  simp only [CollatzResearch.WordTrace]
  refine ⟨18471639596236488106549595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12314426397490992071033063 18471639596236488106549595)
  ·
    refine ⟨27707459394354732159824393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18471639596236488106549595 27707459394354732159824393)
    ·
      refine ⟨20780594545766049119868295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27707459394354732159824393 20780594545766049119868295)
      ·
        refine ⟨31170891818649073679802443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20780594545766049119868295 31170891818649073679802443)
        ·
          refine ⟨46756337727973610519703665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31170891818649073679802443 46756337727973610519703665)
          ·
            refine ⟨35067253295980207889777749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46756337727973610519703665 35067253295980207889777749)
            ·
              refine ⟨410944374562268061208333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 35067253295980207889777749 410944374562268061208333)
              ·
                refine ⟨154104140460850522953125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 410944374562268061208333 154104140460850522953125)
                ·
                  rfl

theorem cell19_506447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 8, 3].length) (baseStart_506447 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_506447 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_506447 prefixEnd_506447 := by exact prefixLift 506447
  have htrace : WordTrace (prefixWord ++ tailWord_506447) baseStart_506447 baseEnd_506447 := by
    simpa [prefixWord, tailWord_506447, baseEnd_506447] using wordTrace_append hprefix tailTrace_506447
  have hstable : (prefixWord ++ tailWord_506447).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506447).length < 2 ^ (prefixWord ++ tailWord_506447).sum := by decide
  have hdescent : baseEnd_506447 < baseStart_506447 := by decide
  rcases family_descends (prefixWord ++ tailWord_506447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506487 : List Nat := [1, 1, 3, 1, 1, 3, 3, 6]
def baseStart_506487 : Nat := 118140960795 + 506487 * 2 ^ 59
def prefixEnd_506487 : Nat := 4983230072969 + 3 ^ 40 * 506487 * 2
def baseEnd_506487 : Nat := 154116311854142282064127

theorem tailTrace_506487 : CollatzResearch.WordTrace tailWord_506487 prefixEnd_506487 154116311854142282064127 := by
  unfold tailWord_506487
  simp only [CollatzResearch.WordTrace]
  refine ⟨18473098516091574938005715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12315399010727716625337143 18473098516091574938005715)
  ·
    refine ⟨27709647774137362407008573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18473098516091574938005715 27709647774137362407008573)
    ·
      refine ⟨10391117915301510902628215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27709647774137362407008573 10391117915301510902628215)
      ·
        refine ⟨15586676872952266353942323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10391117915301510902628215 15586676872952266353942323)
        ·
          refine ⟨23380015309428399530913485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15586676872952266353942323 23380015309428399530913485)
          ·
            refine ⟨8767505741035649824092557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23380015309428399530913485 8767505741035649824092557)
            ·
              refine ⟨3287814652888368684034709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8767505741035649824092557 3287814652888368684034709)
              ·
                refine ⟨154116311854142282064127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3287814652888368684034709 154116311854142282064127)
                ·
                  rfl

theorem cell19_506487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 6].length) (baseStart_506487 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_506487 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_506487 prefixEnd_506487 := by exact prefixLift 506487
  have htrace : WordTrace (prefixWord ++ tailWord_506487) baseStart_506487 baseEnd_506487 := by
    simpa [prefixWord, tailWord_506487, baseEnd_506487] using wordTrace_append hprefix tailTrace_506487
  have hstable : (prefixWord ++ tailWord_506487).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506487).length < 2 ^ (prefixWord ++ tailWord_506487).sum := by decide
  have hdescent : baseEnd_506487 < baseStart_506487 := by decide
  rcases family_descends (prefixWord ++ tailWord_506487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506618 : List Nat := [3, 1, 1, 1, 1, 3, 6, 3]
def baseStart_506618 : Nat := 118140960795 + 506618 * 2 ^ 59
def prefixEnd_506618 : Nat := 4983230072969 + 3 ^ 40 * 506618 * 2
def baseEnd_506618 : Nat := 154156173167172793152659

theorem tailTrace_506618 : CollatzResearch.WordTrace tailWord_506618 prefixEnd_506618 154156173167172793152659 := by
  unfold tailWord_506618
  simp only [CollatzResearch.WordTrace]
  refine ⟨4619469119654246077756127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12318584319077989540683005 4619469119654246077756127)
  ·
    refine ⟨6929203679481369116634191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4619469119654246077756127 6929203679481369116634191)
    ·
      refine ⟨10393805519222053674951287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6929203679481369116634191 10393805519222053674951287)
      ·
        refine ⟨15590708278833080512426931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10393805519222053674951287 15590708278833080512426931)
        ·
          refine ⟨23386062418249620768640397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15590708278833080512426931 23386062418249620768640397)
          ·
            refine ⟨8769773406843607788240149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23386062418249620768640397 8769773406843607788240149)
            ·
              refine ⟨411083128445794115073757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 8769773406843607788240149 411083128445794115073757)
              ·
                refine ⟨154156173167172793152659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 411083128445794115073757 154156173167172793152659)
                ·
                  rfl

theorem cell19_506618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 6, 3].length) (baseStart_506618 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_506618 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_506618 prefixEnd_506618 := by exact prefixLift 506618
  have htrace : WordTrace (prefixWord ++ tailWord_506618) baseStart_506618 baseEnd_506618 := by
    simpa [prefixWord, tailWord_506618, baseEnd_506618] using wordTrace_append hprefix tailTrace_506618
  have hstable : (prefixWord ++ tailWord_506618).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506618).length < 2 ^ (prefixWord ++ tailWord_506618).sum := by decide
  have hdescent : baseEnd_506618 < baseStart_506618 := by decide
  rcases family_descends (prefixWord ++ tailWord_506618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506656 : List Nat := [2, 1, 1, 5, 1, 3, 2, 4]
def baseStart_506656 : Nat := 118140960795 + 506656 * 2 ^ 59
def prefixEnd_506656 : Nat := 4983230072969 + 3 ^ 40 * 506656 * 2
def baseEnd_506656 : Nat := 154167735990799964308111

theorem tailTrace_506656 : CollatzResearch.WordTrace tailWord_506656 prefixEnd_506656 154167735990799964308111 := by
  unfold tailWord_506656
  simp only [CollatzResearch.WordTrace]
  refine ⟨9239631226239658400453911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12319508301652877867271881 9239631226239658400453911)
  ·
    refine ⟨13859446839359487600680867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9239631226239658400453911 13859446839359487600680867)
    ·
      refine ⟨20789170259039231401021301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13859446839359487600680867 20789170259039231401021301)
      ·
        refine ⟨1948984711784927943845747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20789170259039231401021301 1948984711784927943845747)
        ·
          refine ⟨2923477067677391915768621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1948984711784927943845747 2923477067677391915768621)
          ·
            refine ⟨1096303900379021968413233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2923477067677391915768621 1096303900379021968413233)
            ·
              refine ⟨822227925284266476309925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1096303900379021968413233 822227925284266476309925)
              ·
                refine ⟨154167735990799964308111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 822227925284266476309925 154167735990799964308111)
                ·
                  rfl

theorem cell19_506656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2, 4].length) (baseStart_506656 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_506656 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_506656 prefixEnd_506656 := by exact prefixLift 506656
  have htrace : WordTrace (prefixWord ++ tailWord_506656) baseStart_506656 baseEnd_506656 := by
    simpa [prefixWord, tailWord_506656, baseEnd_506656] using wordTrace_append hprefix tailTrace_506656
  have hstable : (prefixWord ++ tailWord_506656).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506656).length < 2 ^ (prefixWord ++ tailWord_506656).sum := by decide
  have hdescent : baseEnd_506656 < baseStart_506656 := by decide
  rcases family_descends (prefixWord ++ tailWord_506656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506692 : List Nat := [2, 3, 4, 2, 1, 7]
def baseStart_506692 : Nat := 118140960795 + 506692 * 2 ^ 59
def prefixEnd_506692 : Nat := 4983230072969 + 3 ^ 40 * 506692 * 2
def baseEnd_506692 : Nat := 17130965582751394167557

theorem tailTrace_506692 : CollatzResearch.WordTrace tailWord_506692 prefixEnd_506692 17130965582751394167557 := by
  unfold tailWord_506692
  simp only [CollatzResearch.WordTrace]
  refine ⟨9240287740174447474609165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12320383653565929966145553 9240287740174447474609165)
  ·
    refine ⟨3465107902565417802978437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9240287740174447474609165 3465107902565417802978437)
    ·
      refine ⟨649707731731015838058457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3465107902565417802978437 649707731731015838058457)
      ·
        refine ⟨487280798798261878543843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 649707731731015838058457 487280798798261878543843)
        ·
          refine ⟨730921198197392817815765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 487280798798261878543843 730921198197392817815765)
          ·
            refine ⟨17130965582751394167557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 730921198197392817815765 17130965582751394167557)
            ·
              rfl

theorem cell19_506692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 7].length) (baseStart_506692 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_506692 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_506692 prefixEnd_506692 := by exact prefixLift 506692
  have htrace : WordTrace (prefixWord ++ tailWord_506692) baseStart_506692 baseEnd_506692 := by
    simpa [prefixWord, tailWord_506692, baseEnd_506692] using wordTrace_append hprefix tailTrace_506692
  have hstable : (prefixWord ++ tailWord_506692).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506692).length < 2 ^ (prefixWord ++ tailWord_506692).sum := by decide
  have hdescent : baseEnd_506692 < baseStart_506692 := by decide
  rcases family_descends (prefixWord ++ tailWord_506692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506713 : List Nat := [1, 2, 1, 2, 2, 6, 1, 4]
def baseStart_506713 : Nat := 118140960795 + 506713 * 2 ^ 59
def prefixEnd_506713 : Nat := 4983230072969 + 3 ^ 40 * 506713 * 2
def baseEnd_506713 : Nat := 154185080226240721041289

theorem tailTrace_506713 : CollatzResearch.WordTrace tailWord_506713 prefixEnd_506713 154185080226240721041289 := by
  unfold tailWord_506713
  simp only [CollatzResearch.WordTrace]
  refine ⟨18481341413272815535732793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12320894275515210357155195 18481341413272815535732793)
  ·
    refine ⟨13861006059954611651799595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18481341413272815535732793 13861006059954611651799595)
    ·
      refine ⟨20791509089931917477699393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13861006059954611651799595 20791509089931917477699393)
      ·
        refine ⟨15593631817448938108274545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20791509089931917477699393 15593631817448938108274545)
        ·
          refine ⟨11695223863086703581205909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15593631817448938108274545 11695223863086703581205909)
          ·
            refine ⟨548213618582189230369027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 11695223863086703581205909 548213618582189230369027)
            ·
              refine ⟨822320427873283845553541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 548213618582189230369027 822320427873283845553541)
              ·
                refine ⟨154185080226240721041289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 822320427873283845553541 154185080226240721041289)
                ·
                  rfl

theorem cell19_506713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 1, 4].length) (baseStart_506713 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_506713 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_506713 prefixEnd_506713 := by exact prefixLift 506713
  have htrace : WordTrace (prefixWord ++ tailWord_506713) baseStart_506713 baseEnd_506713 := by
    simpa [prefixWord, tailWord_506713, baseEnd_506713] using wordTrace_append hprefix tailTrace_506713
  have hstable : (prefixWord ++ tailWord_506713).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506713).length < 2 ^ (prefixWord ++ tailWord_506713).sum := by decide
  have hdescent : baseEnd_506713 < baseStart_506713 := by decide
  rcases family_descends (prefixWord ++ tailWord_506713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506732 : List Nat := [2, 2, 1, 1, 4, 1, 5, 3]
def baseStart_506732 : Nat := 118140960795 + 506732 * 2 ^ 59
def prefixEnd_506732 : Nat := 4983230072969 + 3 ^ 40 * 506732 * 2
def baseEnd_506732 : Nat := 154190861638054306619015

theorem tailTrace_506732 : CollatzResearch.WordTrace tailWord_506732 prefixEnd_506732 154190861638054306619015 := by
  unfold tailWord_506732
  simp only [CollatzResearch.WordTrace]
  refine ⟨9241017200101990890337225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12321356266802654520449633 9241017200101990890337225)
  ·
    refine ⟨6930762900076493167752919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9241017200101990890337225 6930762900076493167752919)
    ·
      refine ⟨10396144350114739751629379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6930762900076493167752919 10396144350114739751629379)
      ·
        refine ⟨15594216525172109627444069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10396144350114739751629379 15594216525172109627444069)
        ·
          refine ⟨2923915598469770555145763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15594216525172109627444069 2923915598469770555145763)
          ·
            refine ⟨4385873397704655832718645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2923915598469770555145763 4385873397704655832718645)
            ·
              refine ⟨411175631034811484317373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4385873397704655832718645 411175631034811484317373)
              ·
                refine ⟨154190861638054306619015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 411175631034811484317373 154190861638054306619015)
                ·
                  rfl

theorem cell19_506732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 5, 3].length) (baseStart_506732 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_506732 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_506732 prefixEnd_506732 := by exact prefixLift 506732
  have htrace : WordTrace (prefixWord ++ tailWord_506732) baseStart_506732 baseEnd_506732 := by
    simpa [prefixWord, tailWord_506732, baseEnd_506732] using wordTrace_append hprefix tailTrace_506732
  have hstable : (prefixWord ++ tailWord_506732).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506732).length < 2 ^ (prefixWord ++ tailWord_506732).sum := by decide
  have hdescent : baseEnd_506732 < baseStart_506732 := by decide
  rcases family_descends (prefixWord ++ tailWord_506732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506922 : List Nat := [3, 1, 4, 1, 3, 1, 6]
def baseStart_506922 : Nat := 118140960795 + 506922 * 2 ^ 59
def prefixEnd_506922 : Nat := 4983230072969 + 3 ^ 40 * 506922 * 2
def baseEnd_506922 : Nat := 51416225252063387465425

theorem tailTrace_506922 : CollatzResearch.WordTrace tailWord_506922 prefixEnd_506922 51416225252063387465425 := by
  unfold tailWord_506922
  simp only [CollatzResearch.WordTrace]
  refine ⟨4622241067378911057522755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12325976179677096153394013 4622241067378911057522755)
  ·
    refine ⟨6933361601068366586284133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4622241067378911057522755 6933361601068366586284133)
    ·
      refine ⟨1300005300200318734928275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6933361601068366586284133 1300005300200318734928275)
      ·
        refine ⟨1950007950300478102392413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1300005300200318734928275 1950007950300478102392413)
        ·
          refine ⟨731252981362679288397155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1950007950300478102392413 731252981362679288397155)
          ·
            refine ⟨1096879472044018932595733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 731252981362679288397155 1096879472044018932595733)
            ·
              refine ⟨51416225252063387465425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1096879472044018932595733 51416225252063387465425)
              ·
                rfl

theorem cell19_506922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 6].length) (baseStart_506922 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_506922 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_506922 prefixEnd_506922 := by exact prefixLift 506922
  have htrace : WordTrace (prefixWord ++ tailWord_506922) baseStart_506922 baseEnd_506922 := by
    simpa [prefixWord, tailWord_506922, baseEnd_506922] using wordTrace_append hprefix tailTrace_506922
  have hstable : (prefixWord ++ tailWord_506922).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506922).length < 2 ^ (prefixWord ++ tailWord_506922).sum := by decide
  have hdescent : baseEnd_506922 < baseStart_506922 := by decide
  rcases family_descends (prefixWord ++ tailWord_506922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506998 : List Nat := [5, 1, 1, 2, 1, 1, 4, 4]
def baseStart_506998 : Nat := 118140960795 + 506998 * 2 ^ 59
def prefixEnd_506998 : Nat := 4983230072969 + 3 ^ 40 * 506998 * 2
def baseEnd_506998 : Nat := 154271801403444504707179

theorem tailTrace_506998 : CollatzResearch.WordTrace tailWord_506998 prefixEnd_506998 154271801403444504707179 := by
  unfold tailWord_506998
  simp only [CollatzResearch.WordTrace]
  refine ⟨1155733513577519325616103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12327824144826872806571765 1155733513577519325616103)
  ·
    refine ⟨1733600270366278988424155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1155733513577519325616103 1733600270366278988424155)
    ·
      refine ⟨2600400405549418482636233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1733600270366278988424155 2600400405549418482636233)
      ·
        refine ⟨1950300304162063861977175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2600400405549418482636233 1950300304162063861977175)
        ·
          refine ⟨2925450456243095792965763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1950300304162063861977175 2925450456243095792965763)
          ·
            refine ⟨4388175684364643689448645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2925450456243095792965763 4388175684364643689448645)
            ·
              refine ⟨822782940818370691771621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4388175684364643689448645 822782940818370691771621)
              ·
                refine ⟨154271801403444504707179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 822782940818370691771621 154271801403444504707179)
                ·
                  rfl

theorem cell19_506998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_506998 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_506998 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_506998 prefixEnd_506998 := by exact prefixLift 506998
  have htrace : WordTrace (prefixWord ++ tailWord_506998) baseStart_506998 baseEnd_506998 := by
    simpa [prefixWord, tailWord_506998, baseEnd_506998] using wordTrace_append hprefix tailTrace_506998
  have hstable : (prefixWord ++ tailWord_506998).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506998).length < 2 ^ (prefixWord ++ tailWord_506998).sum := by decide
  have hdescent : baseEnd_506998 < baseStart_506998 := by decide
  rcases family_descends (prefixWord ++ tailWord_506998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507053 : List Nat := [1, 5, 2, 1, 3, 2, 1, 4]
def baseStart_507053 : Nat := 118140960795 + 507053 * 2 ^ 59
def prefixEnd_507053 : Nat := 4983230072969 + 3 ^ 40 * 507053 * 2
def baseEnd_507053 : Nat := 154288537069220673484807

theorem tailTrace_507053 : CollatzResearch.WordTrace tailWord_507053 prefixEnd_507053 154288537069220673484807 := by
  unfold tailWord_507053
  simp only [CollatzResearch.WordTrace]
  refine ⟨18493742232041053603109813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12329161488027369068739875 18493742232041053603109813)
  ·
    refine ⟨1733788334253848775291545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18493742232041053603109813 1733788334253848775291545)
    ·
      refine ⟨1300341250690386581468659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1733788334253848775291545 1300341250690386581468659)
      ·
        refine ⟨1950511876035579872202989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1300341250690386581468659 1950511876035579872202989)
        ·
          refine ⟨731441953513342452076121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1950511876035579872202989 731441953513342452076121)
          ·
            refine ⟨548581465135006839057091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 731441953513342452076121 548581465135006839057091)
            ·
              refine ⟨822872197702510258585637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 548581465135006839057091 822872197702510258585637)
              ·
                refine ⟨154288537069220673484807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 822872197702510258585637 154288537069220673484807)
                ·
                  rfl

theorem cell19_507053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 1, 4].length) (baseStart_507053 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_507053 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_507053 prefixEnd_507053 := by exact prefixLift 507053
  have htrace : WordTrace (prefixWord ++ tailWord_507053) baseStart_507053 baseEnd_507053 := by
    simpa [prefixWord, tailWord_507053, baseEnd_507053] using wordTrace_append hprefix tailTrace_507053
  have hstable : (prefixWord ++ tailWord_507053).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507053).length < 2 ^ (prefixWord ++ tailWord_507053).sum := by decide
  have hdescent : baseEnd_507053 < baseStart_507053 := by decide
  rcases family_descends (prefixWord ++ tailWord_507053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507171 : List Nat := [1, 1, 1, 4, 2, 4, 2, 4]
def baseStart_507171 : Nat := 118140960795 + 507171 * 2 ^ 59
def prefixEnd_507171 : Nat := 4983230072969 + 3 ^ 40 * 507171 * 2
def baseEnd_507171 : Nat := 154324442679431362862263

theorem tailTrace_507171 : CollatzResearch.WordTrace tailWord_507171 prefixEnd_507171 154324442679431362862263 := by
  unfold tailWord_507171
  simp only [CollatzResearch.WordTrace]
  refine ⟨18498046045613559755905367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12332030697075706503936911 18498046045613559755905367)
  ·
    refine ⟨27747069068420339633858051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18498046045613559755905367 27747069068420339633858051)
    ·
      refine ⟨41620603602630509450787077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27747069068420339633858051 41620603602630509450787077)
      ·
        refine ⟨7803863175493220522022577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41620603602630509450787077 7803863175493220522022577)
        ·
          refine ⟨5852897381619915391516933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7803863175493220522022577 5852897381619915391516933)
          ·
            refine ⟨1097418259053734135909425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5852897381619915391516933 1097418259053734135909425)
            ·
              refine ⟨823063694290300601932069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1097418259053734135909425 823063694290300601932069)
              ·
                refine ⟨154324442679431362862263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 823063694290300601932069 154324442679431362862263)
                ·
                  rfl

theorem cell19_507171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2, 4].length) (baseStart_507171 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_507171 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_507171 prefixEnd_507171 := by exact prefixLift 507171
  have htrace : WordTrace (prefixWord ++ tailWord_507171) baseStart_507171 baseEnd_507171 := by
    simpa [prefixWord, tailWord_507171, baseEnd_507171] using wordTrace_append hprefix tailTrace_507171
  have hstable : (prefixWord ++ tailWord_507171).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507171).length < 2 ^ (prefixWord ++ tailWord_507171).sum := by decide
  have hdescent : baseEnd_507171 < baseStart_507171 := by decide
  rcases family_descends (prefixWord ++ tailWord_507171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507245 : List Nat := [1, 5, 1, 1, 1, 4, 3, 3]
def baseStart_507245 : Nat := 118140960795 + 507245 * 2 ^ 59
def prefixEnd_507245 : Nat := 4983230072969 + 3 ^ 40 * 507245 * 2
def baseEnd_507245 : Nat := 154346959757021117217617

theorem tailTrace_507245 : CollatzResearch.WordTrace tailWord_507245 prefixEnd_507245 154346959757021117217617 := by
  unfold tailWord_507245
  simp only [CollatzResearch.WordTrace]
  refine ⟨18500745047345470394099189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12333830031563646929399459 18500745047345470394099189)
  ·
    refine ⟨1734444848188637849446799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18500745047345470394099189 1734444848188637849446799)
    ·
      refine ⟨2601667272282956774170199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1734444848188637849446799 2601667272282956774170199)
      ·
        refine ⟨3902500908424435161255299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2601667272282956774170199 3902500908424435161255299)
        ·
          refine ⟨5853751362636652741882949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3902500908424435161255299 5853751362636652741882949)
          ·
            refine ⟨1097578380494372389103053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5853751362636652741882949 1097578380494372389103053)
            ·
              refine ⟨411591892685389645913645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1097578380494372389103053 411591892685389645913645)
              ·
                refine ⟨154346959757021117217617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 411591892685389645913645 154346959757021117217617)
                ·
                  rfl

theorem cell19_507245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 3, 3].length) (baseStart_507245 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_507245 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_507245 prefixEnd_507245 := by exact prefixLift 507245
  have htrace : WordTrace (prefixWord ++ tailWord_507245) baseStart_507245 baseEnd_507245 := by
    simpa [prefixWord, tailWord_507245, baseEnd_507245] using wordTrace_append hprefix tailTrace_507245
  have hstable : (prefixWord ++ tailWord_507245).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507245).length < 2 ^ (prefixWord ++ tailWord_507245).sum := by decide
  have hdescent : baseEnd_507245 < baseStart_507245 := by decide
  rcases family_descends (prefixWord ++ tailWord_507245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507247 : List Nat := [1, 1, 2, 1, 3, 1, 7, 3]
def baseStart_507247 : Nat := 118140960795 + 507247 * 2 ^ 59
def prefixEnd_507247 : Nat := 4983230072969 + 3 ^ 40 * 507247 * 2
def baseEnd_507247 : Nat := 154347568326685705173167

theorem tailTrace_507247 : CollatzResearch.WordTrace tailWord_507247 prefixEnd_507247 154347568326685705173167 := by
  unfold tailWord_507247
  simp only [CollatzResearch.WordTrace]
  refine ⟨18500817993338224735671995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12333878662225483157114663 18500817993338224735671995)
  ·
    refine ⟨27751226990007337103507993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18500817993338224735671995 27751226990007337103507993)
    ·
      refine ⟨20813420242505502827630995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27751226990007337103507993 20813420242505502827630995)
      ·
        refine ⟨31220130363758254241446493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20813420242505502827630995 31220130363758254241446493)
        ·
          refine ⟨11707548886409345340542435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31220130363758254241446493 11707548886409345340542435)
          ·
            refine ⟨17561323329614018010813653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11707548886409345340542435 17561323329614018010813653)
            ·
              refine ⟨411593515537828547128445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 17561323329614018010813653 411593515537828547128445)
              ·
                refine ⟨154347568326685705173167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 411593515537828547128445 154347568326685705173167)
                ·
                  rfl

theorem cell19_507247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 7, 3].length) (baseStart_507247 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_507247 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_507247 prefixEnd_507247 := by exact prefixLift 507247
  have htrace : WordTrace (prefixWord ++ tailWord_507247) baseStart_507247 baseEnd_507247 := by
    simpa [prefixWord, tailWord_507247, baseEnd_507247] using wordTrace_append hprefix tailTrace_507247
  have hstable : (prefixWord ++ tailWord_507247).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507247).length < 2 ^ (prefixWord ++ tailWord_507247).sum := by decide
  have hdescent : baseEnd_507247 < baseStart_507247 := by decide
  rcases family_descends (prefixWord ++ tailWord_507247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507249 : List Nat := [1, 2, 2, 2, 1, 2, 2, 7]
def baseStart_507249 : Nat := 118140960795 + 507249 * 2 ^ 59
def prefixEnd_507249 : Nat := 4983230072969 + 3 ^ 40 * 507249 * 2
def baseEnd_507249 : Nat := 154348176896350293128717

theorem tailTrace_507249 : CollatzResearch.WordTrace tailWord_507249 prefixEnd_507249 154348176896350293128717 := by
  unfold tailWord_507249
  simp only [CollatzResearch.WordTrace]
  refine ⟨18500890939330979077244801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12333927292887319384829867 18500890939330979077244801)
  ·
    refine ⟨13875668204498234307933601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18500890939330979077244801 13875668204498234307933601)
    ·
      refine ⟨10406751153373675730950201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13875668204498234307933601 10406751153373675730950201)
      ·
        refine ⟨7805063365030256798212651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10406751153373675730950201 7805063365030256798212651)
        ·
          refine ⟨11707595047545385197318977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7805063365030256798212651 11707595047545385197318977)
          ·
            refine ⟨8780696285659038897989233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11707595047545385197318977 8780696285659038897989233)
            ·
              refine ⟨6585522214244279173491925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8780696285659038897989233 6585522214244279173491925)
              ·
                refine ⟨154348176896350293128717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6585522214244279173491925 154348176896350293128717)
                ·
                  rfl

theorem cell19_507249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 7].length) (baseStart_507249 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_507249 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_507249 prefixEnd_507249 := by exact prefixLift 507249
  have htrace : WordTrace (prefixWord ++ tailWord_507249) baseStart_507249 baseEnd_507249 := by
    simpa [prefixWord, tailWord_507249, baseEnd_507249] using wordTrace_append hprefix tailTrace_507249
  have hstable : (prefixWord ++ tailWord_507249).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507249).length < 2 ^ (prefixWord ++ tailWord_507249).sum := by decide
  have hdescent : baseEnd_507249 < baseStart_507249 := by decide
  rcases family_descends (prefixWord ++ tailWord_507249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507262 : List Nat := [4, 2, 3, 2, 1, 1, 6]
def baseStart_507262 : Nat := 118140960795 + 507262 * 2 ^ 59
def prefixEnd_507262 : Nat := 4983230072969 + 3 ^ 40 * 507262 * 2
def baseEnd_507262 : Nat := 51450710866390038279931

theorem tailTrace_507262 : CollatzResearch.WordTrace tailWord_507262 prefixEnd_507262 51450710866390038279931 := by
  unfold tailWord_507262
  simp only [CollatzResearch.WordTrace]
  refine ⟨2312670636035485287183505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12334243392189254864978693 2312670636035485287183505)
  ·
    refine ⟨1734502977026613965387629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2312670636035485287183505 1734502977026613965387629)
    ·
      refine ⟨650438616384980237020361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1734502977026613965387629 650438616384980237020361)
      ·
        refine ⟨487828962288735177765271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 650438616384980237020361 487828962288735177765271)
        ·
          refine ⟨731743443433102766647907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 487828962288735177765271 731743443433102766647907)
          ·
            refine ⟨1097615165149654149971861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 731743443433102766647907 1097615165149654149971861)
            ·
              refine ⟨51450710866390038279931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1097615165149654149971861 51450710866390038279931)
              ·
                rfl

theorem cell19_507262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 6].length) (baseStart_507262 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_507262 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_507262 prefixEnd_507262 := by exact prefixLift 507262
  have htrace : WordTrace (prefixWord ++ tailWord_507262) baseStart_507262 baseEnd_507262 := by
    simpa [prefixWord, tailWord_507262, baseEnd_507262] using wordTrace_append hprefix tailTrace_507262
  have hstable : (prefixWord ++ tailWord_507262).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507262).length < 2 ^ (prefixWord ++ tailWord_507262).sum := by decide
  have hdescent : baseEnd_507262 < baseStart_507262 := by decide
  rcases family_descends (prefixWord ++ tailWord_507262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507287 : List Nat := [1, 1, 3, 3, 1, 1, 1, 8]
def baseStart_507287 : Nat := 118140960795 + 507287 * 2 ^ 59
def prefixEnd_507287 : Nat := 4983230072969 + 3 ^ 40 * 507287 * 2
def baseEnd_507287 : Nat := 154359739719977464284169

theorem tailTrace_507287 : CollatzResearch.WordTrace tailWord_507287 prefixEnd_507287 154359739719977464284169 := by
  unfold tailWord_507287
  simp only [CollatzResearch.WordTrace]
  refine ⟨18502276913193311567128115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12334851275462207711418743 18502276913193311567128115)
  ·
    refine ⟨27753415369789967350692173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18502276913193311567128115 27753415369789967350692173)
    ·
      refine ⟨10407530763671237756509565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27753415369789967350692173 10407530763671237756509565)
      ·
        refine ⟨3902824036376714158691087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10407530763671237756509565 3902824036376714158691087)
        ·
          refine ⟨5854236054565071238036631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3902824036376714158691087 5854236054565071238036631)
          ·
            refine ⟨8781354081847606857054947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5854236054565071238036631 8781354081847606857054947)
            ·
              refine ⟨13172031122771410285582421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8781354081847606857054947 13172031122771410285582421)
              ·
                refine ⟨154359739719977464284169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13172031122771410285582421 154359739719977464284169)
                ·
                  rfl

theorem cell19_507287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 8].length) (baseStart_507287 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_507287 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_507287 prefixEnd_507287 := by exact prefixLift 507287
  have htrace : WordTrace (prefixWord ++ tailWord_507287) baseStart_507287 baseEnd_507287 := by
    simpa [prefixWord, tailWord_507287, baseEnd_507287] using wordTrace_append hprefix tailTrace_507287
  have hstable : (prefixWord ++ tailWord_507287).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507287).length < 2 ^ (prefixWord ++ tailWord_507287).sum := by decide
  have hdescent : baseEnd_507287 < baseStart_507287 := by decide
  rcases family_descends (prefixWord ++ tailWord_507287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507321 : List Nat := [1, 2, 1, 4, 5, 1, 5]
def baseStart_507321 : Nat := 118140960795 + 507321 * 2 ^ 59
def prefixEnd_507321 : Nat := 4983230072969 + 3 ^ 40 * 507321 * 2
def baseEnd_507321 : Nat := 51456695134758486509507

theorem tailTrace_507321 : CollatzResearch.WordTrace tailWord_507321 prefixEnd_507321 51456695134758486509507 := by
  unfold tailWord_507321
  simp only [CollatzResearch.WordTrace]
  refine ⟨18503516995070135373865817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12335677996713423582577211 18503516995070135373865817)
  ·
    refine ⟨13877637746302601530399363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18503516995070135373865817 13877637746302601530399363)
    ·
      refine ⟨20816456619453902295599045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13877637746302601530399363 20816456619453902295599045)
      ·
        refine ⟨3903085616147606680424821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20816456619453902295599045 3903085616147606680424821)
        ·
          refine ⟨365914276513838126289827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3903085616147606680424821 365914276513838126289827)
          ·
            refine ⟨548871414770757189434741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 365914276513838126289827 548871414770757189434741)
            ·
              refine ⟨51456695134758486509507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 548871414770757189434741 51456695134758486509507)
              ·
                rfl

theorem cell19_507321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 5].length) (baseStart_507321 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_507321 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_507321 prefixEnd_507321 := by exact prefixLift 507321
  have htrace : WordTrace (prefixWord ++ tailWord_507321) baseStart_507321 baseEnd_507321 := by
    simpa [prefixWord, tailWord_507321, baseEnd_507321] using wordTrace_append hprefix tailTrace_507321
  have hstable : (prefixWord ++ tailWord_507321).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507321).length < 2 ^ (prefixWord ++ tailWord_507321).sum := by decide
  have hdescent : baseEnd_507321 < baseStart_507321 := by decide
  rcases family_descends (prefixWord ++ tailWord_507321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507399 : List Nat := [1, 1, 4, 3, 2, 1, 3, 4]
def baseStart_507399 : Nat := 118140960795 + 507399 * 2 ^ 59
def prefixEnd_507399 : Nat := 4983230072969 + 3 ^ 40 * 507399 * 2
def baseEnd_507399 : Nat := 154393819621194389794975

theorem tailTrace_507399 : CollatzResearch.WordTrace tailWord_507399 prefixEnd_507399 154393819621194389794975 := by
  unfold tailWord_507399
  simp only [CollatzResearch.WordTrace]
  refine ⟨18506361888787554695205251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12337574592525036463470167 18506361888787554695205251)
  ·
    refine ⟨27759542833181332042807877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18506361888787554695205251 27759542833181332042807877)
    ·
      refine ⟨5204914281221499758026477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27759542833181332042807877 5204914281221499758026477)
      ·
        refine ⟨1951842855458062409259929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5204914281221499758026477 1951842855458062409259929)
        ·
          refine ⟨1463882141593546806944947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1951842855458062409259929 1463882141593546806944947)
          ·
            refine ⟨2195823212390320210417421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1463882141593546806944947 2195823212390320210417421)
            ·
              refine ⟨823433704646370078906533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2195823212390320210417421 823433704646370078906533)
              ·
                refine ⟨154393819621194389794975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 823433704646370078906533 154393819621194389794975)
                ·
                  rfl

theorem cell19_507399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3, 4].length) (baseStart_507399 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_507399 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_507399 prefixEnd_507399 := by exact prefixLift 507399
  have htrace : WordTrace (prefixWord ++ tailWord_507399) baseStart_507399 baseEnd_507399 := by
    simpa [prefixWord, tailWord_507399, baseEnd_507399] using wordTrace_append hprefix tailTrace_507399
  have hstable : (prefixWord ++ tailWord_507399).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507399).length < 2 ^ (prefixWord ++ tailWord_507399).sum := by decide
  have hdescent : baseEnd_507399 < baseStart_507399 := by decide
  rcases family_descends (prefixWord ++ tailWord_507399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507416 : List Nat := [2, 1, 2, 3, 4, 1, 3, 3]
def baseStart_507416 : Nat := 118140960795 + 507416 * 2 ^ 59
def prefixEnd_507416 : Nat := 4983230072969 + 3 ^ 40 * 507416 * 2
def baseEnd_507416 : Nat := 154398992463343387417151

theorem tailTrace_507416 : CollatzResearch.WordTrace tailWord_507416 prefixEnd_507416 154398992463343387417151 := by
  unfold tailWord_507416
  simp only [CollatzResearch.WordTrace]
  refine ⟨9253490964862983299287051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12337987953150644399049401 9253490964862983299287051)
  ·
    refine ⟨13880236447294474948930577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9253490964862983299287051 13880236447294474948930577)
    ·
      refine ⟨10410177335470856211697933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13880236447294474948930577 10410177335470856211697933)
      ·
        refine ⟨3903816500801571079386725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10410177335470856211697933 3903816500801571079386725)
        ·
          refine ⟨731965593900294577385011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3903816500801571079386725 731965593900294577385011)
          ·
            refine ⟨1097948390850441866077517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 731965593900294577385011 1097948390850441866077517)
            ·
              refine ⟨411730646568915699779069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1097948390850441866077517 411730646568915699779069)
              ·
                refine ⟨154398992463343387417151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 411730646568915699779069 154398992463343387417151)
                ·
                  rfl

theorem cell19_507416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 3, 3].length) (baseStart_507416 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_507416 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_507416 prefixEnd_507416 := by exact prefixLift 507416
  have htrace : WordTrace (prefixWord ++ tailWord_507416) baseStart_507416 baseEnd_507416 := by
    simpa [prefixWord, tailWord_507416, baseEnd_507416] using wordTrace_append hprefix tailTrace_507416
  have hstable : (prefixWord ++ tailWord_507416).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507416).length < 2 ^ (prefixWord ++ tailWord_507416).sum := by decide
  have hdescent : baseEnd_507416 < baseStart_507416 := by decide
  rcases family_descends (prefixWord ++ tailWord_507416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507469 : List Nat := [1, 6, 1, 1, 4, 1, 2, 3]
def baseStart_507469 : Nat := 118140960795 + 507469 * 2 ^ 59
def prefixEnd_507469 : Nat := 4983230072969 + 3 ^ 40 * 507469 * 2
def baseEnd_507469 : Nat := 154415119559454968239229

theorem tailTrace_507469 : CollatzResearch.WordTrace tailWord_507469 prefixEnd_507469 154415119559454968239229 := by
  unfold tailWord_507469
  simp only [CollatzResearch.WordTrace]
  refine ⟨18508914998533956650253461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12339276665689304433502307 18508914998533956650253461)
  ·
    refine ⟨867605390556279217980631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 18508914998533956650253461 867605390556279217980631)
    ·
      refine ⟨1301408085834418826970947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 867605390556279217980631 1301408085834418826970947)
      ·
        refine ⟨1952112128751628240456421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1301408085834418826970947 1952112128751628240456421)
        ·
          refine ⟨366021024140930295085579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1952112128751628240456421 366021024140930295085579)
          ·
            refine ⟨549031536211395442628369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 366021024140930295085579 549031536211395442628369)
            ·
              refine ⟨411773652158546581971277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 549031536211395442628369 411773652158546581971277)
              ·
                refine ⟨154415119559454968239229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 411773652158546581971277 154415119559454968239229)
                ·
                  rfl

theorem cell19_507469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 2, 3].length) (baseStart_507469 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_507469 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_507469 prefixEnd_507469 := by exact prefixLift 507469
  have htrace : WordTrace (prefixWord ++ tailWord_507469) baseStart_507469 baseEnd_507469 := by
    simpa [prefixWord, tailWord_507469, baseEnd_507469] using wordTrace_append hprefix tailTrace_507469
  have hstable : (prefixWord ++ tailWord_507469).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507469).length < 2 ^ (prefixWord ++ tailWord_507469).sum := by decide
  have hdescent : baseEnd_507469 < baseStart_507469 := by decide
  rcases family_descends (prefixWord ++ tailWord_507469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507515 : List Nat := [1, 1, 1, 1, 1, 4, 6, 4]
def baseStart_507515 : Nat := 118140960795 + 507515 * 2 ^ 59
def prefixEnd_507515 : Nat := 4983230072969 + 3 ^ 40 * 507515 * 2
def baseEnd_507515 : Nat := 154429116661740491216881

theorem tailTrace_507515 : CollatzResearch.WordTrace tailWord_507515 prefixEnd_507515 154429116661740491216881 := by
  unfold tailWord_507515
  simp only [CollatzResearch.WordTrace]
  refine ⟨18510592756367306506427999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12340395170911537670951999 18510592756367306506427999)
  ·
    refine ⟨27765889134550959759641999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18510592756367306506427999 27765889134550959759641999)
    ·
      refine ⟨41648833701826439639462999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27765889134550959759641999 41648833701826439639462999)
      ·
        refine ⟨62473250552739659459194499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41648833701826439639462999 62473250552739659459194499)
        ·
          refine ⟨93709875829109489188791749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62473250552739659459194499 93709875829109489188791749)
          ·
            refine ⟨17570601717958029222898453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93709875829109489188791749 17570601717958029222898453)
            ·
              refine ⟨823621955529282619823365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 17570601717958029222898453 823621955529282619823365)
              ·
                refine ⟨154429116661740491216881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 823621955529282619823365 154429116661740491216881)
                ·
                  rfl

theorem cell19_507515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6, 4].length) (baseStart_507515 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_507515 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_507515 prefixEnd_507515 := by exact prefixLift 507515
  have htrace : WordTrace (prefixWord ++ tailWord_507515) baseStart_507515 baseEnd_507515 := by
    simpa [prefixWord, tailWord_507515, baseEnd_507515] using wordTrace_append hprefix tailTrace_507515
  have hstable : (prefixWord ++ tailWord_507515).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507515).length < 2 ^ (prefixWord ++ tailWord_507515).sum := by decide
  have hdescent : baseEnd_507515 < baseStart_507515 := by decide
  rcases family_descends (prefixWord ++ tailWord_507515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507551 : List Nat := [1, 1, 2, 7, 1, 7]
def baseStart_507551 : Nat := 118140960795 + 507551 * 2 ^ 59
def prefixEnd_507551 : Nat := 4983230072969 + 3 ^ 40 * 507551 * 2
def baseEnd_507551 : Nat := 17160007879522563824087

theorem tailTrace_507551 : CollatzResearch.WordTrace tailWord_507551 prefixEnd_507551 17160007879522563824087 := by
  unfold tailWord_507551
  simp only [CollatzResearch.WordTrace]
  refine ⟨18511905784236884654738507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12341270522824589769825671 18511905784236884654738507)
  ·
    refine ⟨27767858676355326982107761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18511905784236884654738507 27767858676355326982107761)
    ·
      refine ⟨20825894007266495236580821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27767858676355326982107761 20825894007266495236580821)
      ·
        refine ⟨488106890795308482107363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 20825894007266495236580821 488106890795308482107363)
        ·
          refine ⟨732160336192962723161045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 488106890795308482107363 732160336192962723161045)
          ·
            refine ⟨17160007879522563824087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 732160336192962723161045 17160007879522563824087)
            ·
              rfl

theorem cell19_507551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 7].length) (baseStart_507551 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_507551 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_507551 prefixEnd_507551 := by exact prefixLift 507551
  have htrace : WordTrace (prefixWord ++ tailWord_507551) baseStart_507551 baseEnd_507551 := by
    simpa [prefixWord, tailWord_507551, baseEnd_507551] using wordTrace_append hprefix tailTrace_507551
  have hstable : (prefixWord ++ tailWord_507551).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507551).length < 2 ^ (prefixWord ++ tailWord_507551).sum := by decide
  have hdescent : baseEnd_507551 < baseStart_507551 := by decide
  rcases family_descends (prefixWord ++ tailWord_507551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507553 : List Nat := [1, 2, 3, 3, 2, 8]
def baseStart_507553 : Nat := 118140960795 + 507553 * 2 ^ 59
def prefixEnd_507553 : Nat := 4983230072969 + 3 ^ 40 * 507553 * 2
def baseEnd_507553 : Nat := 17160075498374184708037

theorem tailTrace_507553 : CollatzResearch.WordTrace tailWord_507553 prefixEnd_507553 17160075498374184708037 := by
  unfold tailWord_507553
  simp only [CollatzResearch.WordTrace]
  refine ⟨18511978730229638996311313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12341319153486425997540875 18511978730229638996311313)
  ·
    refine ⟨13883984047672229247233485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18511978730229638996311313 13883984047672229247233485)
    ·
      refine ⟨5206494017877085967712557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13883984047672229247233485 5206494017877085967712557)
      ·
        refine ⟨1952435256703907237892209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5206494017877085967712557 1952435256703907237892209)
        ·
          refine ⟨1464326442527930428419157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1952435256703907237892209 1464326442527930428419157)
          ·
            refine ⟨17160075498374184708037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1464326442527930428419157 17160075498374184708037)
            ·
              rfl

theorem cell19_507553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 8].length) (baseStart_507553 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_507553 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_507553 prefixEnd_507553 := by exact prefixLift 507553
  have htrace : WordTrace (prefixWord ++ tailWord_507553) baseStart_507553 baseEnd_507553 := by
    simpa [prefixWord, tailWord_507553, baseEnd_507553] using wordTrace_append hprefix tailTrace_507553
  have hstable : (prefixWord ++ tailWord_507553).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507553).length < 2 ^ (prefixWord ++ tailWord_507553).sum := by decide
  have hdescent : baseEnd_507553 < baseStart_507553 := by decide
  rcases family_descends (prefixWord ++ tailWord_507553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507566 : List Nat := [4, 1, 4, 1, 2, 2, 1, 4]
def baseStart_507566 : Nat := 118140960795 + 507566 * 2 ^ 59
def prefixEnd_507566 : Nat := 4983230072969 + 3 ^ 40 * 507566 * 2
def baseEnd_507566 : Nat := 154444635188187484083409

theorem tailTrace_507566 : CollatzResearch.WordTrace tailWord_507566 prefixEnd_507566 154444635188187484083409 := by
  unfold tailWord_507566
  simp only [CollatzResearch.WordTrace]
  refine ⟨2314056609897817777066819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12341635252788361477689701 2314056609897817777066819)
  ·
    refine ⟨3471084914846726665600229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2314056609897817777066819 3471084914846726665600229)
    ·
      refine ⟨650828421533761249800043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3471084914846726665600229 650828421533761249800043)
      ·
        refine ⟨976242632300641874700065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 650828421533761249800043 976242632300641874700065)
        ·
          refine ⟨732181974225481406025049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 976242632300641874700065 732181974225481406025049)
          ·
            refine ⟨549136480669111054518787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 732181974225481406025049 549136480669111054518787)
            ·
              refine ⟨823704721003666581778181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 549136480669111054518787 823704721003666581778181)
              ·
                refine ⟨154444635188187484083409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 823704721003666581778181 154444635188187484083409)
                ·
                  rfl

theorem cell19_507566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 1, 4].length) (baseStart_507566 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_507566 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_507566 prefixEnd_507566 := by exact prefixLift 507566
  have htrace : WordTrace (prefixWord ++ tailWord_507566) baseStart_507566 baseEnd_507566 := by
    simpa [prefixWord, tailWord_507566, baseEnd_507566] using wordTrace_append hprefix tailTrace_507566
  have hstable : (prefixWord ++ tailWord_507566).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507566).length < 2 ^ (prefixWord ++ tailWord_507566).sum := by decide
  have hdescent : baseEnd_507566 < baseStart_507566 := by decide
  rcases family_descends (prefixWord ++ tailWord_507566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507610 : List Nat := [3, 1, 1, 2, 2, 4, 6]
def baseStart_507610 : Nat := 118140960795 + 507610 * 2 ^ 59
def prefixEnd_507610 : Nat := 4983230072969 + 3 ^ 40 * 507610 * 2
def baseEnd_507610 : Nat := 51486007906936139701837

theorem tailTrace_507610 : CollatzResearch.WordTrace tailWord_507610 prefixEnd_507610 51486007906936139701837 := by
  unfold tailWord_507610
  simp only [CollatzResearch.WordTrace]
  refine ⟨4628514422755784432784071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12342705127348758487424189 4628514422755784432784071)
  ·
    refine ⟨6942771634133676649176107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4628514422755784432784071 6942771634133676649176107)
    ·
      refine ⟨10414157451200514973764161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6942771634133676649176107 10414157451200514973764161)
      ·
        refine ⟨7810618088400386230323121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10414157451200514973764161 7810618088400386230323121)
        ·
          refine ⟨5857963566300289672742341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7810618088400386230323121 5857963566300289672742341)
          ·
            refine ⟨1098368168681304313639189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5857963566300289672742341 1098368168681304313639189)
            ·
              refine ⟨51486007906936139701837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1098368168681304313639189 51486007906936139701837)
              ·
                rfl

theorem cell19_507610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 6].length) (baseStart_507610 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_507610 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_507610 prefixEnd_507610 := by exact prefixLift 507610
  have htrace : WordTrace (prefixWord ++ tailWord_507610) baseStart_507610 baseEnd_507610 := by
    simpa [prefixWord, tailWord_507610, baseEnd_507610] using wordTrace_append hprefix tailTrace_507610
  have hstable : (prefixWord ++ tailWord_507610).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507610).length < 2 ^ (prefixWord ++ tailWord_507610).sum := by decide
  have hdescent : baseEnd_507610 < baseStart_507610 := by decide
  rcases family_descends (prefixWord ++ tailWord_507610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507684 : List Nat := [2, 3, 1, 3, 2, 2, 2, 4]
def baseStart_507684 : Nat := 118140960795 + 507684 * 2 ^ 59
def prefixEnd_507684 : Nat := 4983230072969 + 3 ^ 40 * 507684 * 2
def baseEnd_507684 : Nat := 154480540798398173460865

theorem tailTrace_507684 : CollatzResearch.WordTrace tailWord_507684 prefixEnd_507684 154480540798398173460865 := by
  unfold tailWord_507684
  simp only [CollatzResearch.WordTrace]
  refine ⟨9258378346377524184665053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12344504461836698912886737 9258378346377524184665053)
  ·
    refine ⟨3471891879891571569249395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9258378346377524184665053 3471891879891571569249395)
    ·
      refine ⟨5207837819837357353874093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3471891879891571569249395 5207837819837357353874093)
      ·
        refine ⟨1952939182439009007702785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5207837819837357353874093 1952939182439009007702785)
        ·
          refine ⟨1464704386829256755777089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1952939182439009007702785 1464704386829256755777089)
          ·
            refine ⟨1098528290121942566832817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1464704386829256755777089 1098528290121942566832817)
            ·
              refine ⟨823896217591456925124613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1098528290121942566832817 823896217591456925124613)
              ·
                refine ⟨154480540798398173460865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 823896217591456925124613 154480540798398173460865)
                ·
                  rfl

theorem cell19_507684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2, 4].length) (baseStart_507684 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_507684 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_507684 prefixEnd_507684 := by exact prefixLift 507684
  have htrace : WordTrace (prefixWord ++ tailWord_507684) baseStart_507684 baseEnd_507684 := by
    simpa [prefixWord, tailWord_507684, baseEnd_507684] using wordTrace_append hprefix tailTrace_507684
  have hstable : (prefixWord ++ tailWord_507684).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507684).length < 2 ^ (prefixWord ++ tailWord_507684).sum := by decide
  have hdescent : baseEnd_507684 < baseStart_507684 := by decide
  rcases family_descends (prefixWord ++ tailWord_507684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507724 : List Nat := [2, 2, 1, 3, 4, 7]
def baseStart_507724 : Nat := 118140960795 + 507724 * 2 ^ 59
def prefixEnd_507724 : Nat := 4983230072969 + 3 ^ 40 * 507724 * 2
def baseEnd_507724 : Nat := 17165856910187770285763

theorem tailTrace_507724 : CollatzResearch.WordTrace tailWord_507724 prefixEnd_507724 17165856910187770285763 := by
  unfold tailWord_507724
  simp only [CollatzResearch.WordTrace]
  refine ⟨9259107806305067600393113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12345477075073423467190817 9259107806305067600393113)
  ·
    refine ⟨6944330854728800700294835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9259107806305067600393113 6944330854728800700294835)
    ·
      refine ⟨10416496282093201050442253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6944330854728800700294835 10416496282093201050442253)
      ·
        refine ⟨3906186105784950393915845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10416496282093201050442253 3906186105784950393915845)
        ·
          refine ⟨732409894834678198859221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3906186105784950393915845 732409894834678198859221)
          ·
            refine ⟨17165856910187770285763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 732409894834678198859221 17165856910187770285763)
            ·
              rfl

theorem cell19_507724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 7].length) (baseStart_507724 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_507724 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_507724 prefixEnd_507724 := by exact prefixLift 507724
  have htrace : WordTrace (prefixWord ++ tailWord_507724) baseStart_507724 baseEnd_507724 := by
    simpa [prefixWord, tailWord_507724, baseEnd_507724] using wordTrace_append hprefix tailTrace_507724
  have hstable : (prefixWord ++ tailWord_507724).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507724).length < 2 ^ (prefixWord ++ tailWord_507724).sum := by decide
  have hdescent : baseEnd_507724 < baseStart_507724 := by decide
  rcases family_descends (prefixWord ++ tailWord_507724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507743 : List Nat := [1, 1, 2, 3, 1, 4, 3, 4]
def baseStart_507743 : Nat := 118140960795 + 507743 * 2 ^ 59
def prefixEnd_507743 : Nat := 4983230072969 + 3 ^ 40 * 507743 * 2
def baseEnd_507743 : Nat := 154498493603503518149593

theorem tailTrace_507743 : CollatzResearch.WordTrace tailWord_507743 prefixEnd_507743 154498493603503518149593 := by
  unfold tailWord_507743
  simp only [CollatzResearch.WordTrace]
  refine ⟨18518908599541301445727883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12345939066360867630485255 18518908599541301445727883)
  ·
    refine ⟨27778362899311952168591825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18518908599541301445727883 27778362899311952168591825)
    ·
      refine ⟨20833772174483964126443869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27778362899311952168591825 20833772174483964126443869)
      ·
        refine ⟨7812664565431486547416451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20833772174483964126443869 7812664565431486547416451)
        ·
          refine ⟨11718996848147229821124677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7812664565431486547416451 11718996848147229821124677)
          ·
            refine ⟨2197311909027605591460877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11718996848147229821124677 2197311909027605591460877)
            ·
              refine ⟨823991965885352096797829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2197311909027605591460877 823991965885352096797829)
              ·
                refine ⟨154498493603503518149593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 823991965885352096797829 154498493603503518149593)
                ·
                  rfl

theorem cell19_507743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3, 4].length) (baseStart_507743 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_507743 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_507743 prefixEnd_507743 := by exact prefixLift 507743
  have htrace : WordTrace (prefixWord ++ tailWord_507743) baseStart_507743 baseEnd_507743 := by
    simpa [prefixWord, tailWord_507743, baseEnd_507743] using wordTrace_append hprefix tailTrace_507743
  have hstable : (prefixWord ++ tailWord_507743).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507743).length < 2 ^ (prefixWord ++ tailWord_507743).sum := by decide
  have hdescent : baseEnd_507743 < baseStart_507743 := by decide
  rcases family_descends (prefixWord ++ tailWord_507743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507758 : List Nat := [4, 1, 2, 3, 1, 2, 3, 3]
def baseStart_507758 : Nat := 118140960795 + 507758 * 2 ^ 59
def prefixEnd_507758 : Nat := 4983230072969 + 3 ^ 40 * 507758 * 2
def baseEnd_507758 : Nat := 154503057875987927816219

theorem tailTrace_507758 : CollatzResearch.WordTrace tailWord_507758 prefixEnd_507758 154503057875987927816219 := by
  unfold tailWord_507758
  simp only [CollatzResearch.WordTrace]
  refine ⟨2314931961810869875940491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12346303796324639338349285 2314931961810869875940491)
  ·
    refine ⟨3472397942716304813910737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2314931961810869875940491 3472397942716304813910737)
    ·
      refine ⟨2604298457037228610433053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3472397942716304813910737 2604298457037228610433053)
      ·
        refine ⟨976611921388960728912395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2604298457037228610433053 976611921388960728912395)
        ·
          refine ⟨1464917882083441093368593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 976611921388960728912395 1464917882083441093368593)
          ·
            refine ⟨1098688411562580820026445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1464917882083441093368593 1098688411562580820026445)
            ·
              refine ⟨412008154335967807509917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1098688411562580820026445 412008154335967807509917)
              ·
                refine ⟨154503057875987927816219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 412008154335967807509917 154503057875987927816219)
                ·
                  rfl

theorem cell19_507758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 3, 3].length) (baseStart_507758 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_507758 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_507758 prefixEnd_507758 := by exact prefixLift 507758
  have htrace : WordTrace (prefixWord ++ tailWord_507758) baseStart_507758 baseEnd_507758 := by
    simpa [prefixWord, tailWord_507758, baseEnd_507758] using wordTrace_append hprefix tailTrace_507758
  have hstable : (prefixWord ++ tailWord_507758).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507758).length < 2 ^ (prefixWord ++ tailWord_507758).sum := by decide
  have hdescent : baseEnd_507758 < baseStart_507758 := by decide
  rcases family_descends (prefixWord ++ tailWord_507758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507815 : List Nat := [1, 1, 6, 1, 2, 3, 2, 3]
def baseStart_507815 : Nat := 118140960795 + 507815 * 2 ^ 59
def prefixEnd_507815 : Nat := 4983230072969 + 3 ^ 40 * 507815 * 2
def baseEnd_507815 : Nat := 154520402111428684549397

theorem tailTrace_507815 : CollatzResearch.WordTrace tailWord_507815 prefixEnd_507815 154520402111428684549397 := by
  unfold tailWord_507815
  simp only [CollatzResearch.WordTrace]
  refine ⟨18521534655280457742348899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12347689770186971828232599 18521534655280457742348899)
  ·
    refine ⟨27782301982920686613523349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18521534655280457742348899 27782301982920686613523349)
    ·
      refine ⟨1302295405449407185008907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 27782301982920686613523349 1302295405449407185008907)
      ·
        refine ⟨1953443108174110777513361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1302295405449407185008907 1953443108174110777513361)
        ·
          refine ⟨1465082331130583083135021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1953443108174110777513361 1465082331130583083135021)
          ·
            refine ⟨549405874173968656175633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1465082331130583083135021 549405874173968656175633)
            ·
              refine ⟨412054405630476492131725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 549405874173968656175633 412054405630476492131725)
              ·
                refine ⟨154520402111428684549397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 412054405630476492131725 154520402111428684549397)
                ·
                  rfl

theorem cell19_507815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 2, 3].length) (baseStart_507815 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_507815 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_507815 prefixEnd_507815 := by exact prefixLift 507815
  have htrace : WordTrace (prefixWord ++ tailWord_507815) baseStart_507815 baseEnd_507815 := by
    simpa [prefixWord, tailWord_507815, baseEnd_507815] using wordTrace_append hprefix tailTrace_507815
  have hstable : (prefixWord ++ tailWord_507815).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507815).length < 2 ^ (prefixWord ++ tailWord_507815).sum := by decide
  have hdescent : baseEnd_507815 < baseStart_507815 := by decide
  rcases family_descends (prefixWord ++ tailWord_507815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507838 : List Nat := [4, 2, 1, 1, 1, 3, 7]
def baseStart_507838 : Nat := 118140960795 + 507838 * 2 ^ 59
def prefixEnd_507838 : Nat := 4983230072969 + 3 ^ 40 * 507838 * 2
def baseEnd_507838 : Nat := 51509133554190482012741

theorem tailTrace_507838 : CollatzResearch.WordTrace tailWord_507838 prefixEnd_507838 51509133554190482012741 := by
  unfold tailWord_507838
  simp only [CollatzResearch.WordTrace]
  refine ⟨2315296691774641583804521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12348249022798088446957445 2315296691774641583804521)
  ·
    refine ⟨1736472518830981187853391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2315296691774641583804521 1736472518830981187853391)
    ·
      refine ⟨2604708778246471781780087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1736472518830981187853391 2604708778246471781780087)
      ·
        refine ⟨3907063167369707672670131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2604708778246471781780087 3907063167369707672670131)
        ·
          refine ⟨5860594751054561509005197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3907063167369707672670131 5860594751054561509005197)
          ·
            refine ⟨2197723031645460565876949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5860594751054561509005197 2197723031645460565876949)
            ·
              refine ⟨51509133554190482012741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2197723031645460565876949 51509133554190482012741)
              ·
                rfl

theorem cell19_507838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 7].length) (baseStart_507838 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_507838 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_507838 prefixEnd_507838 := by exact prefixLift 507838
  have htrace : WordTrace (prefixWord ++ tailWord_507838) baseStart_507838 baseEnd_507838 := by
    simpa [prefixWord, tailWord_507838, baseEnd_507838] using wordTrace_append hprefix tailTrace_507838
  have hstable : (prefixWord ++ tailWord_507838).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507838).length < 2 ^ (prefixWord ++ tailWord_507838).sum := by decide
  have hdescent : baseEnd_507838 < baseStart_507838 := by decide
  rcases family_descends (prefixWord ++ tailWord_507838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507897 : List Nat := [1, 2, 1, 3, 1, 11]
def baseStart_507897 : Nat := 118140960795 + 507897 * 2 ^ 59
def prefixEnd_507897 : Nat := 4983230072969 + 3 ^ 40 * 507897 * 2
def baseEnd_507897 : Nat := 17171705940852976747439

theorem tailTrace_507897 : CollatzResearch.WordTrace tailWord_507897 prefixEnd_507897 17171705940852976747439 := by
  unfold tailWord_507897
  simp only [CollatzResearch.WordTrace]
  refine ⟨18524525440983385746833945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12349683627322257164555963 18524525440983385746833945)
  ·
    refine ⟨13893394080737539310125459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18524525440983385746833945 13893394080737539310125459)
    ·
      refine ⟨20840091121106308965188189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13893394080737539310125459 20840091121106308965188189)
      ·
        refine ⟨7815034170414865861945571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20840091121106308965188189 7815034170414865861945571)
        ·
          refine ⟨11722551255622298792918357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7815034170414865861945571 11722551255622298792918357)
          ·
            refine ⟨17171705940852976747439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 11722551255622298792918357 17171705940852976747439)
            ·
              rfl

theorem cell19_507897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 11].length) (baseStart_507897 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_507897 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_507897 prefixEnd_507897 := by exact prefixLift 507897
  have htrace : WordTrace (prefixWord ++ tailWord_507897) baseStart_507897 baseEnd_507897 := by
    simpa [prefixWord, tailWord_507897, baseEnd_507897] using wordTrace_append hprefix tailTrace_507897
  have hstable : (prefixWord ++ tailWord_507897).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507897).length < 2 ^ (prefixWord ++ tailWord_507897).sum := by decide
  have hdescent : baseEnd_507897 < baseStart_507897 := by decide
  rcases family_descends (prefixWord ++ tailWord_507897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507908 : List Nat := [2, 3, 2, 4, 2, 1, 1, 4]
def baseStart_507908 : Nat := 118140960795 + 507908 * 2 ^ 59
def prefixEnd_507908 : Nat := 4983230072969 + 3 ^ 40 * 507908 * 2
def baseEnd_507908 : Nat := 154548700600832024482477

theorem tailTrace_507908 : CollatzResearch.WordTrace tailWord_507908 prefixEnd_507908 154548700600832024482477 := by
  unfold tailWord_507908
  simp only [CollatzResearch.WordTrace]
  refine ⟨9262463321971767312742189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12349951095962356416989585 9262463321971767312742189)
  ·
    refine ⟨3473423745739412742278321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9262463321971767312742189 3473423745739412742278321)
    ·
      refine ⟨2605067809304559556708741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3473423745739412742278321 2605067809304559556708741)
      ·
        refine ⟨488450214244604916882889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2605067809304559556708741 488450214244604916882889)
        ·
          refine ⟨366337660683453687662167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 488450214244604916882889 366337660683453687662167)
          ·
            refine ⟨549506491025180531493251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 366337660683453687662167 549506491025180531493251)
            ·
              refine ⟨824259736537770797239877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 549506491025180531493251 824259736537770797239877)
              ·
                refine ⟨154548700600832024482477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 824259736537770797239877 154548700600832024482477)
                ·
                  rfl

theorem cell19_507908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 1, 4].length) (baseStart_507908 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_507908 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_507908 prefixEnd_507908 := by exact prefixLift 507908
  have htrace : WordTrace (prefixWord ++ tailWord_507908) baseStart_507908 baseEnd_507908 := by
    simpa [prefixWord, tailWord_507908, baseEnd_507908] using wordTrace_append hprefix tailTrace_507908
  have hstable : (prefixWord ++ tailWord_507908).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507908).length < 2 ^ (prefixWord ++ tailWord_507908).sum := by decide
  have hdescent : baseEnd_507908 < baseStart_507908 := by decide
  rcases family_descends (prefixWord ++ tailWord_507908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507973 : List Nat := [1, 3, 1, 1, 1, 3, 1, 8]
def baseStart_507973 : Nat := 118140960795 + 507973 * 2 ^ 59
def prefixEnd_507973 : Nat := 4983230072969 + 3 ^ 40 * 507973 * 2
def baseEnd_507973 : Nat := 154568479114931133037855

theorem tailTrace_507973 : CollatzResearch.WordTrace tailWord_507973 prefixEnd_507973 154568479114931133037855 := by
  unfold tailWord_507973
  simp only [CollatzResearch.WordTrace]
  refine ⟨18527297388708050726600573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12351531592472033817733715 18527297388708050726600573)
  ·
    refine ⟨6947736520765519022475215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18527297388708050726600573 6947736520765519022475215)
    ·
      refine ⟨10421604781148278533712823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6947736520765519022475215 10421604781148278533712823)
      ·
        refine ⟨15632407171722417800569235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10421604781148278533712823 15632407171722417800569235)
        ·
          refine ⟨23448610757583626700853853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15632407171722417800569235 23448610757583626700853853)
          ·
            refine ⟨8793229034093860012820195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23448610757583626700853853 8793229034093860012820195)
            ·
              refine ⟨13189843551140790019230293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8793229034093860012820195 13189843551140790019230293)
              ·
                refine ⟨154568479114931133037855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13189843551140790019230293 154568479114931133037855)
                ·
                  rfl

theorem cell19_507973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 8].length) (baseStart_507973 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_507973 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_507973 prefixEnd_507973 := by exact prefixLift 507973
  have htrace : WordTrace (prefixWord ++ tailWord_507973) baseStart_507973 baseEnd_507973 := by
    simpa [prefixWord, tailWord_507973, baseEnd_507973] using wordTrace_append hprefix tailTrace_507973
  have hstable : (prefixWord ++ tailWord_507973).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507973).length < 2 ^ (prefixWord ++ tailWord_507973).sum := by decide
  have hdescent : baseEnd_507973 < baseStart_507973 := by decide
  rcases family_descends (prefixWord ++ tailWord_507973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507986 : List Nat := [3, 2, 2, 1, 4, 2, 2, 3]
def baseStart_507986 : Nat := 118140960795 + 507986 * 2 ^ 59
def prefixEnd_507986 : Nat := 4983230072969 + 3 ^ 40 * 507986 * 2
def baseEnd_507986 : Nat := 154572434817750954748931

theorem tailTrace_507986 : CollatzResearch.WordTrace tailWord_507986 prefixEnd_507986 154572434817750954748931 := by
  unfold tailWord_507986
  simp only [CollatzResearch.WordTrace]
  refine ⟨4631942884415238486705953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12351847691773969297882541 4631942884415238486705953)
  ·
    refine ⟨3473957163311428865029465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4631942884415238486705953 3473957163311428865029465)
    ·
      refine ⟨2605467872483571648772099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3473957163311428865029465 2605467872483571648772099)
      ·
        refine ⟨3908201808725357473158149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2605467872483571648772099 3908201808725357473158149)
        ·
          refine ⟨732787839136004526217153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3908201808725357473158149 732787839136004526217153)
          ·
            refine ⟨549590879352003394662865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 732787839136004526217153 549590879352003394662865)
            ·
              refine ⟨412193159514002545997149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 549590879352003394662865 412193159514002545997149)
              ·
                refine ⟨154572434817750954748931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 412193159514002545997149 154572434817750954748931)
                ·
                  rfl

theorem cell19_507986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 2, 3].length) (baseStart_507986 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_507986 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_507986 prefixEnd_507986 := by exact prefixLift 507986
  have htrace : WordTrace (prefixWord ++ tailWord_507986) baseStart_507986 baseEnd_507986 := by
    simpa [prefixWord, tailWord_507986, baseEnd_507986] using wordTrace_append hprefix tailTrace_507986
  have hstable : (prefixWord ++ tailWord_507986).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507986).length < 2 ^ (prefixWord ++ tailWord_507986).sum := by decide
  have hdescent : baseEnd_507986 < baseStart_507986 := by decide
  rcases family_descends (prefixWord ++ tailWord_507986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508028 : List Nat := [2, 2, 2, 1, 1, 5, 2, 4]
def baseStart_508028 : Nat := 118140960795 + 508028 * 2 ^ 59
def prefixEnd_508028 : Nat := 4983230072969 + 3 ^ 40 * 508028 * 2
def baseEnd_508028 : Nat := 154585214780707301815483

theorem tailTrace_508028 : CollatzResearch.WordTrace tailWord_508028 prefixEnd_508028 154585214780707301815483 := by
  unfold tailWord_508028
  simp only [CollatzResearch.WordTrace]
  refine ⟨9264651701754397559926369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12352868935672530079901825 9264651701754397559926369)
  ·
    refine ⟨6948488776315798169944777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9264651701754397559926369 6948488776315798169944777)
    ·
      refine ⟨5211366582236848627458583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6948488776315798169944777 5211366582236848627458583)
      ·
        refine ⟨7817049873355272941187875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5211366582236848627458583 7817049873355272941187875)
        ·
          refine ⟨11725574810032909411781813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7817049873355272941187875 11725574810032909411781813)
          ·
            refine ⟨1099272638440585257354545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11725574810032909411781813 1099272638440585257354545)
            ·
              refine ⟨824454478830438943015909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1099272638440585257354545 824454478830438943015909)
              ·
                refine ⟨154585214780707301815483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 824454478830438943015909 154585214780707301815483)
                ·
                  rfl

theorem cell19_508028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2, 4].length) (baseStart_508028 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_508028 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_508028 prefixEnd_508028 := by exact prefixLift 508028
  have htrace : WordTrace (prefixWord ++ tailWord_508028) baseStart_508028 baseEnd_508028 := by
    simpa [prefixWord, tailWord_508028, baseEnd_508028] using wordTrace_append hprefix tailTrace_508028
  have hstable : (prefixWord ++ tailWord_508028).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508028).length < 2 ^ (prefixWord ++ tailWord_508028).sum := by decide
  have hdescent : baseEnd_508028 < baseStart_508028 := by decide
  rcases family_descends (prefixWord ++ tailWord_508028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508066 : List Nat := [3, 3, 1, 3, 1, 8]
def baseStart_508066 : Nat := 118140960795 + 508066 * 2 ^ 59
def prefixEnd_508066 : Nat := 4983230072969 + 3 ^ 40 * 508066 * 2
def baseEnd_508066 : Nat := 17177419733814941441215

theorem tailTrace_508066 : CollatzResearch.WordTrace tailWord_508066 prefixEnd_508066 17177419733814941441215 := by
  unfold tailWord_508066
  simp only [CollatzResearch.WordTrace]
  refine ⟨4632672344342781902434013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12353792918247418406490701 4632672344342781902434013)
  ·
    refine ⟨1737252129128543213412755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4632672344342781902434013 1737252129128543213412755)
    ·
      refine ⟨2605878193692814820119133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1737252129128543213412755 2605878193692814820119133)
      ·
        refine ⟨977204322634805557544675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2605878193692814820119133 977204322634805557544675)
        ·
          refine ⟨1465806483952208336317013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 977204322634805557544675 1465806483952208336317013)
          ·
            refine ⟨17177419733814941441215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1465806483952208336317013 17177419733814941441215)
            ·
              rfl

theorem cell19_508066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 8].length) (baseStart_508066 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_508066 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_508066 prefixEnd_508066 := by exact prefixLift 508066
  have htrace : WordTrace (prefixWord ++ tailWord_508066) baseStart_508066 baseEnd_508066 := by
    simpa [prefixWord, tailWord_508066, baseEnd_508066] using wordTrace_append hprefix tailTrace_508066
  have hstable : (prefixWord ++ tailWord_508066).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508066).length < 2 ^ (prefixWord ++ tailWord_508066).sum := by decide
  have hdescent : baseEnd_508066 < baseStart_508066 := by decide
  rcases family_descends (prefixWord ++ tailWord_508066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508068 : List Nat := [2, 3, 1, 2, 11]
def baseStart_508068 : Nat := 118140960795 + 508068 * 2 ^ 59
def prefixEnd_508068 : Nat := 4983230072969 + 3 ^ 40 * 508068 * 2
def baseEnd_508068 : Nat := 5725829117555520775055

theorem tailTrace_508068 : CollatzResearch.WordTrace tailWord_508068 prefixEnd_508068 5725829117555520775055 := by
  unfold tailWord_508068
  simp only [CollatzResearch.WordTrace]
  refine ⟨9265381161681940975654429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12353841548909254634205905 9265381161681940975654429)
  ·
    refine ⟨3474517935630727865870411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9265381161681940975654429 3474517935630727865870411)
    ·
      refine ⟨5211776903446091798805617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3474517935630727865870411 5211776903446091798805617)
      ·
        refine ⟨3908832677584568849104213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5211776903446091798805617 3908832677584568849104213)
        ·
          refine ⟨5725829117555520775055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 3908832677584568849104213 5725829117555520775055)
          ·
            rfl

theorem cell19_508068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 11].length) (baseStart_508068 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_508068 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_508068 prefixEnd_508068 := by exact prefixLift 508068
  have htrace : WordTrace (prefixWord ++ tailWord_508068) baseStart_508068 baseEnd_508068 := by
    simpa [prefixWord, tailWord_508068, baseEnd_508068] using wordTrace_append hprefix tailTrace_508068
  have hstable : (prefixWord ++ tailWord_508068).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508068).length < 2 ^ (prefixWord ++ tailWord_508068).sum := by decide
  have hdescent : baseEnd_508068 < baseStart_508068 := by decide
  rcases family_descends (prefixWord ++ tailWord_508068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508081 : List Nat := [1, 2, 2, 5, 3, 1, 1, 4]
def baseStart_508081 : Nat := 118140960795 + 508081 * 2 ^ 59
def prefixEnd_508081 : Nat := 4983230072969 + 3 ^ 40 * 508081 * 2
def baseEnd_508081 : Nat := 154601341876818882637561

theorem tailTrace_508081 : CollatzResearch.WordTrace tailWord_508081 prefixEnd_508081 154601341876818882637561 := by
  unfold tailWord_508081
  simp only [CollatzResearch.WordTrace]
  refine ⟨18531236472316785171532097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12354157648211190114354731 18531236472316785171532097)
  ·
    refine ⟨13898427354237588878649073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18531236472316785171532097 13898427354237588878649073)
    ·
      refine ⟨10423820515678191658986805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13898427354237588878649073 10423820515678191658986805)
      ·
        refine ⟨977233173344830468030013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10423820515678191658986805 977233173344830468030013)
        ·
          refine ⟨366462440004311425511255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 977233173344830468030013 366462440004311425511255)
          ·
            refine ⟨549693660006467138266883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 366462440004311425511255 549693660006467138266883)
            ·
              refine ⟨824540490009700707400325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 549693660006467138266883 824540490009700707400325)
              ·
                refine ⟨154601341876818882637561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 824540490009700707400325 154601341876818882637561)
                ·
                  rfl

theorem cell19_508081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 1, 4].length) (baseStart_508081 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_508081 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_508081 prefixEnd_508081 := by exact prefixLift 508081
  have htrace : WordTrace (prefixWord ++ tailWord_508081) baseStart_508081 baseEnd_508081 := by
    simpa [prefixWord, tailWord_508081, baseEnd_508081] using wordTrace_append hprefix tailTrace_508081
  have hstable : (prefixWord ++ tailWord_508081).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508081).length < 2 ^ (prefixWord ++ tailWord_508081).sum := by decide
  have hdescent : baseEnd_508081 < baseStart_508081 := by decide
  rcases family_descends (prefixWord ++ tailWord_508081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508098 : List Nat := [3, 5, 1, 1, 1, 2, 3, 3]
def baseStart_508098 : Nat := 118140960795 + 508098 * 2 ^ 59
def prefixEnd_508098 : Nat := 4983230072969 + 3 ^ 40 * 508098 * 2
def baseEnd_508098 : Nat := 154606514718967880259737

theorem tailTrace_508098 : CollatzResearch.WordTrace tailWord_508098 prefixEnd_508098 154606514718967880259737 := by
  unfold tailWord_508098
  simp only [CollatzResearch.WordTrace]
  refine ⟨4632964128313799268725237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12354571008836798049933965 4632964128313799268725237)
  ·
    refine ⟨434340387029418681442991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4632964128313799268725237 434340387029418681442991)
    ·
      refine ⟨651510580544128022164487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434340387029418681442991 651510580544128022164487)
      ·
        refine ⟨977265870816192033246731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 651510580544128022164487 977265870816192033246731)
        ·
          refine ⟨1465898806224288049870097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 977265870816192033246731 1465898806224288049870097)
          ·
            refine ⟨1099424104668216037402573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1465898806224288049870097 1099424104668216037402573)
            ·
              refine ⟨412284039250581014025965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1099424104668216037402573 412284039250581014025965)
              ·
                refine ⟨154606514718967880259737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 412284039250581014025965 154606514718967880259737)
                ·
                  rfl

theorem cell19_508098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 3, 3].length) (baseStart_508098 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_508098 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_508098 prefixEnd_508098 := by exact prefixLift 508098
  have htrace : WordTrace (prefixWord ++ tailWord_508098) baseStart_508098 baseEnd_508098 := by
    simpa [prefixWord, tailWord_508098, baseEnd_508098] using wordTrace_append hprefix tailTrace_508098
  have hstable : (prefixWord ++ tailWord_508098).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508098).length < 2 ^ (prefixWord ++ tailWord_508098).sum := by decide
  have hdescent : baseEnd_508098 < baseStart_508098 := by decide
  rcases family_descends (prefixWord ++ tailWord_508098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508163 : List Nat := [1, 1, 1, 3, 2, 3, 3, 5]
def baseStart_508163 : Nat := 118140960795 + 508163 * 2 ^ 59
def prefixEnd_508163 : Nat := 4983230072969 + 3 ^ 40 * 508163 * 2
def baseEnd_508163 : Nat := 154626293233066988815115

theorem tailTrace_508163 : CollatzResearch.WordTrace tailWord_508163 prefixEnd_508163 154626293233066988815115 := by
  unfold tailWord_508163
  simp only [CollatzResearch.WordTrace]
  refine ⟨18534227258019713176017143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12356151505346475450678095 18534227258019713176017143)
  ·
    refine ⟨27801340887029569764025715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18534227258019713176017143 27801340887029569764025715)
    ·
      refine ⟨41702011330544354646038573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27801340887029569764025715 41702011330544354646038573)
      ·
        refine ⟨15638254248954132992264465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41702011330544354646038573 15638254248954132992264465)
        ·
          refine ⟨11728690686715599744198349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15638254248954132992264465 11728690686715599744198349)
          ·
            refine ⟨4398259007518349904074381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11728690686715599744198349 4398259007518349904074381)
            ·
              refine ⟨1649347127819381214027893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4398259007518349904074381 1649347127819381214027893)
              ·
                refine ⟨154626293233066988815115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1649347127819381214027893 154626293233066988815115)
                ·
                  rfl

theorem cell19_508163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 5].length) (baseStart_508163 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_508163 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_508163 prefixEnd_508163 := by exact prefixLift 508163
  have htrace : WordTrace (prefixWord ++ tailWord_508163) baseStart_508163 baseEnd_508163 := by
    simpa [prefixWord, tailWord_508163, baseEnd_508163] using wordTrace_append hprefix tailTrace_508163
  have hstable : (prefixWord ++ tailWord_508163).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508163).length < 2 ^ (prefixWord ++ tailWord_508163).sum := by decide
  have hdescent : baseEnd_508163 < baseStart_508163 := by decide
  rcases family_descends (prefixWord ++ tailWord_508163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508220 : List Nat := [2, 2, 2, 2, 1, 2, 1, 7]
def baseStart_508220 : Nat := 118140960795 + 508220 * 2 ^ 59
def prefixEnd_508220 : Nat := 4983230072969 + 3 ^ 40 * 508220 * 2
def baseEnd_508220 : Nat := 154643637468507745548293

theorem tailTrace_508220 : CollatzResearch.WordTrace tailWord_508220 prefixEnd_508220 154643637468507745548293 := by
  unfold tailWord_508220
  simp only [CollatzResearch.WordTrace]
  refine ⟨9268153109406605955421057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12357537479208807940561409 9268153109406605955421057)
  ·
    refine ⟨6951114832054954466565793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9268153109406605955421057 6951114832054954466565793)
    ·
      refine ⟨5213336124041215849924345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6951114832054954466565793 5213336124041215849924345)
      ·
        refine ⟨3910002093030911887443259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5213336124041215849924345 3910002093030911887443259)
        ·
          refine ⟨5865003139546367831164889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3910002093030911887443259 5865003139546367831164889)
          ·
            refine ⟨4398752354659775873373667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5865003139546367831164889 4398752354659775873373667)
            ·
              refine ⟨6598128531989663810060501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4398752354659775873373667 6598128531989663810060501)
              ·
                refine ⟨154643637468507745548293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6598128531989663810060501 154643637468507745548293)
                ·
                  rfl

theorem cell19_508220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 7].length) (baseStart_508220 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_508220 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_508220 prefixEnd_508220 := by exact prefixLift 508220
  have htrace : WordTrace (prefixWord ++ tailWord_508220) baseStart_508220 baseEnd_508220 := by
    simpa [prefixWord, tailWord_508220, baseEnd_508220] using wordTrace_append hprefix tailTrace_508220
  have hstable : (prefixWord ++ tailWord_508220).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508220).length < 2 ^ (prefixWord ++ tailWord_508220).sum := by decide
  have hdescent : baseEnd_508220 < baseStart_508220 := by decide
  rcases family_descends (prefixWord ++ tailWord_508220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508252 : List Nat := [2, 2, 4, 3, 1, 2, 1, 4]
def baseStart_508252 : Nat := 118140960795 + 508252 * 2 ^ 59
def prefixEnd_508252 : Nat := 4983230072969 + 3 ^ 40 * 508252 * 2
def baseEnd_508252 : Nat := 154653374583141152837095

theorem tailTrace_508252 : CollatzResearch.WordTrace tailWord_508252 prefixEnd_508252 154653374583141152837095 := by
  unfold tailWord_508252
  simp only [CollatzResearch.WordTrace]
  refine ⟨9268736677348640688003505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12358315569798187584004673 9268736677348640688003505)
  ·
    refine ⟨6951552508011480516002629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9268736677348640688003505 6951552508011480516002629)
    ·
      refine ⟨1303416095252152596750493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6951552508011480516002629 1303416095252152596750493)
      ·
        refine ⟨488781035719557223781435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1303416095252152596750493 488781035719557223781435)
        ·
          refine ⟨733171553579335835672153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 488781035719557223781435 733171553579335835672153)
          ·
            refine ⟨549878665184501876754115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 733171553579335835672153 549878665184501876754115)
            ·
              refine ⟨824817997776752815131173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 549878665184501876754115 824817997776752815131173)
              ·
                refine ⟨154653374583141152837095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 824817997776752815131173 154653374583141152837095)
                ·
                  rfl

theorem cell19_508252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 1, 4].length) (baseStart_508252 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_508252 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_508252 prefixEnd_508252 := by exact prefixLift 508252
  have htrace : WordTrace (prefixWord ++ tailWord_508252) baseStart_508252 baseEnd_508252 := by
    simpa [prefixWord, tailWord_508252, baseEnd_508252] using wordTrace_append hprefix tailTrace_508252
  have hstable : (prefixWord ++ tailWord_508252).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508252).length < 2 ^ (prefixWord ++ tailWord_508252).sum := by decide
  have hdescent : baseEnd_508252 < baseStart_508252 := by decide
  rcases family_descends (prefixWord ++ tailWord_508252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508296 : List Nat := [2, 1, 3, 3, 1, 1, 8]
def baseStart_508296 : Nat := 118140960795 + 508296 * 2 ^ 59
def prefixEnd_508296 : Nat := 4983230072969 + 3 ^ 40 * 508296 * 2
def baseEnd_508296 : Nat := 51555587705254029286399

theorem tailTrace_508296 : CollatzResearch.WordTrace tailWord_508296 prefixEnd_508296 51555587705254029286399 := by
  unfold tailWord_508296
  simp only [CollatzResearch.WordTrace]
  refine ⟨9269539083268938445304371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12359385444358584593739161 9269539083268938445304371)
  ·
    refine ⟨13904308624903407667956557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9269539083268938445304371 13904308624903407667956557)
    ·
      refine ⟨5214115734338777875483709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13904308624903407667956557 5214115734338777875483709)
      ·
        refine ⟨1955293400377041703306391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5214115734338777875483709 1955293400377041703306391)
        ·
          refine ⟨2932940100565562554959587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1955293400377041703306391 2932940100565562554959587)
          ·
            refine ⟨4399410150848343832439381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2932940100565562554959587 4399410150848343832439381)
            ·
              refine ⟨51555587705254029286399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4399410150848343832439381 51555587705254029286399)
              ·
                rfl

theorem cell19_508296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 8].length) (baseStart_508296 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_508296 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_508296 prefixEnd_508296 := by exact prefixLift 508296
  have htrace : WordTrace (prefixWord ++ tailWord_508296) baseStart_508296 baseEnd_508296 := by
    simpa [prefixWord, tailWord_508296, baseEnd_508296] using wordTrace_append hprefix tailTrace_508296
  have hstable : (prefixWord ++ tailWord_508296).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508296).length < 2 ^ (prefixWord ++ tailWord_508296).sum := by decide
  have hdescent : baseEnd_508296 < baseStart_508296 := by decide
  rcases family_descends (prefixWord ++ tailWord_508296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508328 : List Nat := [2, 1, 6, 1, 1, 3, 2, 3]
def baseStart_508328 : Nat := 118140960795 + 508328 * 2 ^ 59
def prefixEnd_508328 : Nat := 4983230072969 + 3 ^ 40 * 508328 * 2
def baseEnd_508328 : Nat := 154676500230395495147999

theorem tailTrace_508328 : CollatzResearch.WordTrace tailWord_508328 prefixEnd_508328 154676500230395495147999 := by
  unfold tailWord_508328
  simp only [CollatzResearch.WordTrace]
  refine ⟨9270122651210973177886819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12360163534947964237182425 9270122651210973177886819)
  ·
    refine ⟨13905183976816459766830229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9270122651210973177886819 13905183976816459766830229)
    ·
      refine ⟨651805498913271551570167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 13905183976816459766830229 651805498913271551570167)
      ·
        refine ⟨977708248369907327355251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 651805498913271551570167 977708248369907327355251)
        ·
          refine ⟨1466562372554860991032877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 977708248369907327355251 1466562372554860991032877)
          ·
            refine ⟨549960889708072871637329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1466562372554860991032877 549960889708072871637329)
            ·
              refine ⟨412470667281054653727997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 549960889708072871637329 412470667281054653727997)
              ·
                refine ⟨154676500230395495147999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 412470667281054653727997 154676500230395495147999)
                ·
                  rfl

theorem cell19_508328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 2, 3].length) (baseStart_508328 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_508328 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_508328 prefixEnd_508328 := by exact prefixLift 508328
  have htrace : WordTrace (prefixWord ++ tailWord_508328) baseStart_508328 baseEnd_508328 := by
    simpa [prefixWord, tailWord_508328, baseEnd_508328] using wordTrace_append hprefix tailTrace_508328
  have hstable : (prefixWord ++ tailWord_508328).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508328).length < 2 ^ (prefixWord ++ tailWord_508328).sum := by decide
  have hdescent : baseEnd_508328 < baseStart_508328 := by decide
  rcases family_descends (prefixWord ++ tailWord_508328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508391 : List Nat := [1, 1, 5, 2, 1, 1, 1, 7]
def baseStart_508391 : Nat := 118140960795 + 508391 * 2 ^ 59
def prefixEnd_508391 : Nat := 4983230072969 + 3 ^ 40 * 508391 * 2
def baseEnd_508391 : Nat := 154695670174830015747827

theorem tailTrace_508391 : CollatzResearch.WordTrace tailWord_508391 prefixEnd_508391 154695670174830015747827 := by
  unfold tailWord_508391
  simp only [CollatzResearch.WordTrace]
  refine ⟨18542543101193708115317027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12361695400795805410211351 18542543101193708115317027)
  ·
    refine ⟨27813814651790562172975541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18542543101193708115317027 27813814651790562172975541)
    ·
      refine ⟨2607545123605365203716457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27813814651790562172975541 2607545123605365203716457)
      ·
        refine ⟨1955658842704023902787343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2607545123605365203716457 1955658842704023902787343)
        ·
          refine ⟨2933488264056035854181015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1955658842704023902787343 2933488264056035854181015)
          ·
            refine ⟨4400232396084053781271523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2933488264056035854181015 4400232396084053781271523)
            ·
              refine ⟨6600348594126080671907285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4400232396084053781271523 6600348594126080671907285)
              ·
                refine ⟨154695670174830015747827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6600348594126080671907285 154695670174830015747827)
                ·
                  rfl

theorem cell19_508391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 7].length) (baseStart_508391 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_508391 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_508391 prefixEnd_508391 := by exact prefixLift 508391
  have htrace : WordTrace (prefixWord ++ tailWord_508391) baseStart_508391 baseEnd_508391 := by
    simpa [prefixWord, tailWord_508391, baseEnd_508391] using wordTrace_append hprefix tailTrace_508391
  have hstable : (prefixWord ++ tailWord_508391).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508391).length < 2 ^ (prefixWord ++ tailWord_508391).sum := by decide
  have hdescent : baseEnd_508391 < baseStart_508391 := by decide
  rcases family_descends (prefixWord ++ tailWord_508391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508427 : List Nat := [1, 1, 1, 1, 7, 3, 1, 4]
def baseStart_508427 : Nat := 118140960795 + 508427 * 2 ^ 59
def prefixEnd_508427 : Nat := 4983230072969 + 3 ^ 40 * 508427 * 2
def baseEnd_508427 : Nat := 154706624428792598947729

theorem tailTrace_508427 : CollatzResearch.WordTrace tailWord_508427 prefixEnd_508427 154706624428792598947729 := by
  unfold tailWord_508427
  simp only [CollatzResearch.WordTrace]
  refine ⟨18543856129063286263627535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12362570752708857509085023 18543856129063286263627535)
  ·
    refine ⟨27815784193594929395441303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18543856129063286263627535 27815784193594929395441303)
    ·
      refine ⟨41723676290392394093161955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27815784193594929395441303 41723676290392394093161955)
      ·
        refine ⟨62585514435588591139742933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41723676290392394093161955 62585514435588591139742933)
        ·
          refine ⟨1466847994584107604837725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 62585514435588591139742933 1466847994584107604837725)
          ·
            refine ⟨550067997969040351814147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1466847994584107604837725 550067997969040351814147)
            ·
              refine ⟨825101996953560527721221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 550067997969040351814147 825101996953560527721221)
              ·
                refine ⟨154706624428792598947729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 825101996953560527721221 154706624428792598947729)
                ·
                  rfl

theorem cell19_508427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 1, 4].length) (baseStart_508427 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_508427 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_508427 prefixEnd_508427 := by exact prefixLift 508427
  have htrace : WordTrace (prefixWord ++ tailWord_508427) baseStart_508427 baseEnd_508427 := by
    simpa [prefixWord, tailWord_508427, baseEnd_508427] using wordTrace_append hprefix tailTrace_508427
  have hstable : (prefixWord ++ tailWord_508427).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508427).length < 2 ^ (prefixWord ++ tailWord_508427).sum := by decide
  have hdescent : baseEnd_508427 < baseStart_508427 := by decide
  rcases family_descends (prefixWord ++ tailWord_508427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508461 : List Nat := [1, 5, 4, 1, 1, 1, 6]
def baseStart_508461 : Nat := 118140960795 + 508461 * 2 ^ 59
def prefixEnd_508461 : Nat := 4983230072969 + 3 ^ 40 * 508461 * 2
def baseEnd_508461 : Nat := 51572323371030198064027

theorem tailTrace_508461 : CollatzResearch.WordTrace tailWord_508461 prefixEnd_508461 51572323371030198064027 := by
  unfold tailWord_508461
  simp only [CollatzResearch.WordTrace]
  refine ⟨18545096210940110070365237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12363397473960073380243491 18545096210940110070365237)
  ·
    refine ⟨1738602769775635319096741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18545096210940110070365237 1738602769775635319096741)
    ·
      refine ⟨325988019332931622330639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1738602769775635319096741 325988019332931622330639)
      ·
        refine ⟨488982028999397433495959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325988019332931622330639 488982028999397433495959)
        ·
          refine ⟨733473043499096150243939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 488982028999397433495959 733473043499096150243939)
          ·
            refine ⟨1100209565248644225365909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 733473043499096150243939 1100209565248644225365909)
            ·
              refine ⟨51572323371030198064027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1100209565248644225365909 51572323371030198064027)
              ·
                rfl

theorem cell19_508461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 6].length) (baseStart_508461 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_508461 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_508461 prefixEnd_508461 := by exact prefixLift 508461
  have htrace : WordTrace (prefixWord ++ tailWord_508461) baseStart_508461 baseEnd_508461 := by
    simpa [prefixWord, tailWord_508461, baseEnd_508461] using wordTrace_append hprefix tailTrace_508461
  have hstable : (prefixWord ++ tailWord_508461).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508461).length < 2 ^ (prefixWord ++ tailWord_508461).sum := by decide
  have hdescent : baseEnd_508461 < baseStart_508461 := by decide
  rcases family_descends (prefixWord ++ tailWord_508461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508520 : List Nat := [2, 1, 4, 3, 3, 1, 5]
def baseStart_508520 : Nat := 118140960795 + 508520 * 2 ^ 59
def prefixEnd_508520 : Nat := 4983230072969 + 3 ^ 40 * 508520 * 2
def baseEnd_508520 : Nat := 51578307639398646293603

theorem tailTrace_508520 : CollatzResearch.WordTrace tailWord_508520 prefixEnd_508520 51578307639398646293603 := by
  unfold tailWord_508520
  simp only [CollatzResearch.WordTrace]
  refine ⟨9273624058863181573381507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12364832078484242097842009 9273624058863181573381507)
  ·
    refine ⟨13910436088294772360072261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9273624058863181573381507 13910436088294772360072261)
    ·
      refine ⟨2608206766555269817513549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13910436088294772360072261 2608206766555269817513549)
      ·
        refine ⟨978077537458226181567581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2608206766555269817513549 978077537458226181567581)
        ·
          refine ⟨366779076546834818087843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 978077537458226181567581 366779076546834818087843)
          ·
            refine ⟨550168614820252227131765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 366779076546834818087843 550168614820252227131765)
            ·
              refine ⟨51578307639398646293603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 550168614820252227131765 51578307639398646293603)
              ·
                rfl

theorem cell19_508520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 5].length) (baseStart_508520 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_508520 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_508520 prefixEnd_508520 := by exact prefixLift 508520
  have htrace : WordTrace (prefixWord ++ tailWord_508520) baseStart_508520 baseEnd_508520 := by
    simpa [prefixWord, tailWord_508520, baseEnd_508520] using wordTrace_append hprefix tailTrace_508520
  have hstable : (prefixWord ++ tailWord_508520).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508520).length < 2 ^ (prefixWord ++ tailWord_508520).sum := by decide
  have hdescent : baseEnd_508520 < baseStart_508520 := by decide
  rcases family_descends (prefixWord ++ tailWord_508520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508541 : List Nat := [1, 4, 1, 1, 5, 1, 2, 4]
def baseStart_508541 : Nat := 118140960795 + 508541 * 2 ^ 59
def prefixEnd_508541 : Nat := 4983230072969 + 3 ^ 40 * 508541 * 2
def baseEnd_508541 : Nat := 154741312899674112414085

theorem tailTrace_508541 : CollatzResearch.WordTrace tailWord_508541 prefixEnd_508541 154741312899674112414085 := by
  unfold tailWord_508541
  simp only [CollatzResearch.WordTrace]
  refine ⟨18548014050650283733277477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12365342700433522488851651 18548014050650283733277477)
  ·
    refine ⟨3477752634496928199989527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18548014050650283733277477 3477752634496928199989527)
    ·
      refine ⟨5216628951745392299984291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3477752634496928199989527 5216628951745392299984291)
      ·
        refine ⟨7824943427618088449976437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5216628951745392299984291 7824943427618088449976437)
        ·
          refine ⟨733588446339195792185291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7824943427618088449976437 733588446339195792185291)
          ·
            refine ⟨1100382669508793688277937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 733588446339195792185291 1100382669508793688277937)
            ·
              refine ⟨825287002131595266208453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1100382669508793688277937 825287002131595266208453)
              ·
                refine ⟨154741312899674112414085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 825287002131595266208453 154741312899674112414085)
                ·
                  rfl

theorem cell19_508541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 2, 4].length) (baseStart_508541 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_508541 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_508541 prefixEnd_508541 := by exact prefixLift 508541
  have htrace : WordTrace (prefixWord ++ tailWord_508541) baseStart_508541 baseEnd_508541 := by
    simpa [prefixWord, tailWord_508541, baseEnd_508541] using wordTrace_append hprefix tailTrace_508541
  have hstable : (prefixWord ++ tailWord_508541).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508541).length < 2 ^ (prefixWord ++ tailWord_508541).sum := by decide
  have hdescent : baseEnd_508541 < baseStart_508541 := by decide
  rcases family_descends (prefixWord ++ tailWord_508541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508636 : List Nat := [2, 2, 5, 1, 1, 2, 6]
def baseStart_508636 : Nat := 118140960795 + 508636 * 2 ^ 59
def prefixEnd_508636 : Nat := 4983230072969 + 3 ^ 40 * 508636 * 2
def baseEnd_508636 : Nat := 51590073319580680100905

theorem tailTrace_508636 : CollatzResearch.WordTrace tailWord_508636 prefixEnd_508636 51590073319580680100905 := by
  unfold tailWord_508636
  simp only [CollatzResearch.WordTrace]
  refine ⟨9275739492653057478992881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12367652656870743305323841 9275739492653057478992881)
  ·
    refine ⟨6956804619489793109244661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9275739492653057478992881 6956804619489793109244661)
    ·
      refine ⟨652200433077168103991687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6956804619489793109244661 652200433077168103991687)
      ·
        refine ⟨978300649615752155987531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 652200433077168103991687 978300649615752155987531)
        ·
          refine ⟨1467450974423628233981297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 978300649615752155987531 1467450974423628233981297)
          ·
            refine ⟨1100588230817721175485973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1467450974423628233981297 1100588230817721175485973)
            ·
              refine ⟨51590073319580680100905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1100588230817721175485973 51590073319580680100905)
              ·
                rfl

theorem cell19_508636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 6].length) (baseStart_508636 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_508636 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_508636 prefixEnd_508636 := by exact prefixLift 508636
  have htrace : WordTrace (prefixWord ++ tailWord_508636) baseStart_508636 baseEnd_508636 := by
    simpa [prefixWord, tailWord_508636, baseEnd_508636] using wordTrace_append hprefix tailTrace_508636
  have hstable : (prefixWord ++ tailWord_508636).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508636).length < 2 ^ (prefixWord ++ tailWord_508636).sum := by decide
  have hdescent : baseEnd_508636 < baseStart_508636 := by decide
  rcases family_descends (prefixWord ++ tailWord_508636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508659 : List Nat := [1, 1, 1, 2, 2, 3, 1, 8]
def baseStart_508659 : Nat := 118140960795 + 508659 * 2 ^ 59
def prefixEnd_508659 : Nat := 4983230072969 + 3 ^ 40 * 508659 * 2
def baseEnd_508659 : Nat := 154777218509884801791541

theorem tailTrace_508659 : CollatzResearch.WordTrace tailWord_508659 prefixEnd_508659 154777218509884801791541 := by
  unfold tailWord_508659
  simp only [CollatzResearch.WordTrace]
  refine ⟨18552317864222789886073031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12368211909481859924048687 18552317864222789886073031)
  ·
    refine ⟨27828476796334184829109547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18552317864222789886073031 27828476796334184829109547)
    ·
      refine ⟨41742715194501277243664321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27828476796334184829109547 41742715194501277243664321)
      ·
        refine ⟨31307036395875957932748241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41742715194501277243664321 31307036395875957932748241)
        ·
          refine ⟨23480277296906968449561181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31307036395875957932748241 23480277296906968449561181)
          ·
            refine ⟨8805103986340113168585443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23480277296906968449561181 8805103986340113168585443)
            ·
              refine ⟨13207655979510169752878165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8805103986340113168585443 13207655979510169752878165)
              ·
                refine ⟨154777218509884801791541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13207655979510169752878165 154777218509884801791541)
                ·
                  rfl

theorem cell19_508659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 8].length) (baseStart_508659 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_508659 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_508659 prefixEnd_508659 := by exact prefixLift 508659
  have htrace : WordTrace (prefixWord ++ tailWord_508659) baseStart_508659 baseEnd_508659 := by
    simpa [prefixWord, tailWord_508659, baseEnd_508659] using wordTrace_append hprefix tailTrace_508659
  have hstable : (prefixWord ++ tailWord_508659).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508659).length < 2 ^ (prefixWord ++ tailWord_508659).sum := by decide
  have hdescent : baseEnd_508659 < baseStart_508659 := by decide
  rcases family_descends (prefixWord ++ tailWord_508659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508674 : List Nat := [3, 4, 1, 1, 1, 3, 1, 5]
def baseStart_508674 : Nat := 118140960795 + 508674 * 2 ^ 59
def prefixEnd_508674 : Nat := 4983230072969 + 3 ^ 40 * 508674 * 2
def baseEnd_508674 : Nat := 154781782782369211458167

theorem tailTrace_508674 : CollatzResearch.WordTrace tailWord_508674 prefixEnd_508674 154781782782369211458167 := by
  unfold tailWord_508674
  simp only [CollatzResearch.WordTrace]
  refine ⟨4638216239792111861967269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12368576639445631631912717 4638216239792111861967269)
  ·
    refine ⟨869665544961020974118863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4638216239792111861967269 869665544961020974118863)
    ·
      refine ⟨1304498317441531461178295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 869665544961020974118863 1304498317441531461178295)
      ·
        refine ⟨1956747476162297191767443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1304498317441531461178295 1956747476162297191767443)
        ·
          refine ⟨2935121214243445787651165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1956747476162297191767443 2935121214243445787651165)
          ·
            refine ⟨1100670455341292170369187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2935121214243445787651165 1100670455341292170369187)
            ·
              refine ⟨1651005683011938255553781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1100670455341292170369187 1651005683011938255553781)
              ·
                refine ⟨154781782782369211458167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1651005683011938255553781 154781782782369211458167)
                ·
                  rfl

theorem cell19_508674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 5].length) (baseStart_508674 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_508674 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_508674 prefixEnd_508674 := by exact prefixLift 508674
  have htrace : WordTrace (prefixWord ++ tailWord_508674) baseStart_508674 baseEnd_508674 := by
    simpa [prefixWord, tailWord_508674, baseEnd_508674] using wordTrace_append hprefix tailTrace_508674
  have hstable : (prefixWord ++ tailWord_508674).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508674).length < 2 ^ (prefixWord ++ tailWord_508674).sum := by decide
  have hdescent : baseEnd_508674 < baseStart_508674 := by decide
  rcases family_descends (prefixWord ++ tailWord_508674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508676 : List Nat := [2, 3, 2, 2, 1, 1, 3, 5]
def baseStart_508676 : Nat := 118140960795 + 508676 * 2 ^ 59
def prefixEnd_508676 : Nat := 4983230072969 + 3 ^ 40 * 508676 * 2
def baseEnd_508676 : Nat := 154782391352033799413717

theorem tailTrace_508676 : CollatzResearch.WordTrace tailWord_508676 prefixEnd_508676 154782391352033799413717 := by
  unfold tailWord_508676
  simp only [CollatzResearch.WordTrace]
  refine ⟨9276468952580600894720941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12368625270107467859627921 9276468952580600894720941)
  ·
    refine ⟨3478675857217725335520353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9276468952580600894720941 3478675857217725335520353)
    ·
      refine ⟨2609006892913294001640265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3478675857217725335520353 2609006892913294001640265)
      ·
        refine ⟨1956755169684970501230199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2609006892913294001640265 1956755169684970501230199)
        ·
          refine ⟨2935132754527455751845299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1956755169684970501230199 2935132754527455751845299)
          ·
            refine ⟨4402699131791183627767949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2935132754527455751845299 4402699131791183627767949)
            ·
              refine ⟨1651012174421693860412981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4402699131791183627767949 1651012174421693860412981)
              ·
                refine ⟨154782391352033799413717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1651012174421693860412981 154782391352033799413717)
                ·
                  rfl

theorem cell19_508676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 5].length) (baseStart_508676 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_508676 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_508676 prefixEnd_508676 := by exact prefixLift 508676
  have htrace : WordTrace (prefixWord ++ tailWord_508676) baseStart_508676 baseEnd_508676 := by
    simpa [prefixWord, tailWord_508676, baseEnd_508676] using wordTrace_append hprefix tailTrace_508676
  have hstable : (prefixWord ++ tailWord_508676).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508676).length < 2 ^ (prefixWord ++ tailWord_508676).sum := by decide
  have hdescent : baseEnd_508676 < baseStart_508676 := by decide
  rcases family_descends (prefixWord ++ tailWord_508676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508771 : List Nat := [1, 1, 1, 5, 3, 1, 3, 4]
def baseStart_508771 : Nat := 118140960795 + 508771 * 2 ^ 59
def prefixEnd_508771 : Nat := 4983230072969 + 3 ^ 40 * 508771 * 2
def baseEnd_508771 : Nat := 154811298411101727302347

theorem tailTrace_508771 : CollatzResearch.WordTrace tailWord_508771 prefixEnd_508771 154811298411101727302347 := by
  unfold tailWord_508771
  simp only [CollatzResearch.WordTrace]
  refine ⟨18556402839817033014150167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12370935226544688676100111 18556402839817033014150167)
  ·
    refine ⟨27834604259725549521225251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18556402839817033014150167 27834604259725549521225251)
    ·
      refine ⟨41751906389588324281837877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27834604259725549521225251 41751906389588324281837877)
      ·
        refine ⟨3914241224023905401422301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41751906389588324281837877 3914241224023905401422301)
        ·
          refine ⟨1467840459008964525533363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3914241224023905401422301 1467840459008964525533363)
          ·
            refine ⟨2201760688513446788300045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1467840459008964525533363 2201760688513446788300045)
            ·
              refine ⟨825660258192542545612517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2201760688513446788300045 825660258192542545612517)
              ·
                refine ⟨154811298411101727302347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 825660258192542545612517 154811298411101727302347)
                ·
                  rfl

theorem cell19_508771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3, 4].length) (baseStart_508771 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_508771 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_508771 prefixEnd_508771 := by exact prefixLift 508771
  have htrace : WordTrace (prefixWord ++ tailWord_508771) baseStart_508771 baseEnd_508771 := by
    simpa [prefixWord, tailWord_508771, baseEnd_508771] using wordTrace_append hprefix tailTrace_508771
  have hstable : (prefixWord ++ tailWord_508771).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508771).length < 2 ^ (prefixWord ++ tailWord_508771).sum := by decide
  have hdescent : baseEnd_508771 < baseStart_508771 := by decide
  rcases family_descends (prefixWord ++ tailWord_508771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508942 : List Nat := [4, 1, 1, 2, 2, 2, 3, 4]
def baseStart_508942 : Nat := 118140960795 + 508942 * 2 ^ 59
def prefixEnd_508942 : Nat := 4983230072969 + 3 ^ 40 * 508942 * 2
def baseEnd_508942 : Nat := 154863331117423997501881

theorem tailTrace_508942 : CollatzResearch.WordTrace tailWord_508942 prefixEnd_508942 154863331117423997501881 := by
  unfold tailWord_508942
  simp only [CollatzResearch.WordTrace]
  refine ⟨2320329965274691152328135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12375093148131686145750053 2320329965274691152328135)
  ·
    refine ⟨3480494947912036728492203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2320329965274691152328135 3480494947912036728492203)
    ·
      refine ⟨5220742421868055092738305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3480494947912036728492203 5220742421868055092738305)
      ·
        refine ⟨3915556816401041319553729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5220742421868055092738305 3915556816401041319553729)
        ·
          refine ⟨2936667612300780989665297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3915556816401041319553729 2936667612300780989665297)
          ·
            refine ⟨2202500709225585742248973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2936667612300780989665297 2202500709225585742248973)
            ·
              refine ⟨825937765959594653343365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2202500709225585742248973 825937765959594653343365)
              ·
                refine ⟨154863331117423997501881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 825937765959594653343365 154863331117423997501881)
                ·
                  rfl

theorem cell19_508942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3, 4].length) (baseStart_508942 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_508942 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_508942 prefixEnd_508942 := by exact prefixLift 508942
  have htrace : WordTrace (prefixWord ++ tailWord_508942) baseStart_508942 baseEnd_508942 := by
    simpa [prefixWord, tailWord_508942, baseEnd_508942] using wordTrace_append hprefix tailTrace_508942
  have hstable : (prefixWord ++ tailWord_508942).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508942).length < 2 ^ (prefixWord ++ tailWord_508942).sum := by decide
  have hdescent : baseEnd_508942 < baseStart_508942 := by decide
  rcases family_descends (prefixWord ++ tailWord_508942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509014 : List Nat := [5, 2, 2, 1, 2, 1, 1, 5]
def baseStart_509014 : Nat := 118140960795 + 509014 * 2 ^ 59
def prefixEnd_509014 : Nat := 4983230072969 + 3 ^ 40 * 509014 * 2
def baseEnd_509014 : Nat := 154885239625349163901685

theorem tailTrace_509014 : CollatzResearch.WordTrace tailWord_509014 prefixEnd_509014 154885239625349163901685 := by
  unfold tailWord_509014
  simp only [CollatzResearch.WordTrace]
  refine ⟨1160329111121042844702881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12376843851957790343497397 1160329111121042844702881)
  ·
    refine ⟨870246833340782133527161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1160329111121042844702881 870246833340782133527161)
    ·
      refine ⟨652685125005586600145371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 870246833340782133527161 652685125005586600145371)
      ·
        refine ⟨979027687508379900218057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 652685125005586600145371 979027687508379900218057)
        ·
          refine ⟨734270765631284925163543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 979027687508379900218057 734270765631284925163543)
          ·
            refine ⟨1101406148446927387745315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 734270765631284925163543 1101406148446927387745315)
            ·
              refine ⟨1652109222670391081617973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1101406148446927387745315 1652109222670391081617973)
              ·
                refine ⟨154885239625349163901685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1652109222670391081617973 154885239625349163901685)
                ·
                  rfl

theorem cell19_509014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_509014 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_509014 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_509014 prefixEnd_509014 := by exact prefixLift 509014
  have htrace : WordTrace (prefixWord ++ tailWord_509014) baseStart_509014 baseEnd_509014 := by
    simpa [prefixWord, tailWord_509014, baseEnd_509014] using wordTrace_append hprefix tailTrace_509014
  have hstable : (prefixWord ++ tailWord_509014).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509014).length < 2 ^ (prefixWord ++ tailWord_509014).sum := by decide
  have hdescent : baseEnd_509014 < baseStart_509014 := by decide
  rcases family_descends (prefixWord ++ tailWord_509014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509037 : List Nat := [1, 5, 1, 1, 2, 4, 5]
def baseStart_509037 : Nat := 118140960795 + 509037 * 2 ^ 59
def prefixEnd_509037 : Nat := 4983230072969 + 3 ^ 40 * 509037 * 2
def baseEnd_509037 : Nat := 51630746058830641796837

theorem tailTrace_509037 : CollatzResearch.WordTrace tailWord_509037 prefixEnd_509037 51630746058830641796837 := by
  unfold tailWord_509037
  simp only [CollatzResearch.WordTrace]
  refine ⟨18566104656853360443333365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12377403104568906962222243 18566104656853360443333365)
  ·
    refine ⟨1740572311580002541562503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18566104656853360443333365 1740572311580002541562503)
    ·
      refine ⟨2610858467370003812343755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1740572311580002541562503 2610858467370003812343755)
      ·
        refine ⟨3916287701055005718515633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2610858467370003812343755 3916287701055005718515633)
        ·
          refine ⟨2937215775791254288886725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3916287701055005718515633 2937215775791254288886725)
          ·
            refine ⟨550727957960860179166261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2937215775791254288886725 550727957960860179166261)
            ·
              refine ⟨51630746058830641796837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 550727957960860179166261 51630746058830641796837)
              ·
                rfl

theorem cell19_509037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 5].length) (baseStart_509037 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_509037 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_509037 prefixEnd_509037 := by exact prefixLift 509037
  have htrace : WordTrace (prefixWord ++ tailWord_509037) baseStart_509037 baseEnd_509037 := by
    simpa [prefixWord, tailWord_509037, baseEnd_509037] using wordTrace_append hprefix tailTrace_509037
  have hstable : (prefixWord ++ tailWord_509037).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509037).length < 2 ^ (prefixWord ++ tailWord_509037).sum := by decide
  have hdescent : baseEnd_509037 < baseStart_509037 := by decide
  rcases family_descends (prefixWord ++ tailWord_509037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509113 : List Nat := [1, 2, 1, 4, 1, 5, 1, 4]
def baseStart_509113 : Nat := 118140960795 + 509113 * 2 ^ 59
def prefixEnd_509113 : Nat := 4983230072969 + 3 ^ 40 * 509113 * 2
def baseEnd_509113 : Nat := 154915363823746267701415

theorem tailTrace_509113 : CollatzResearch.WordTrace tailWord_509113 prefixEnd_509113 154915363823746267701415 := by
  unfold tailWord_509113
  simp only [CollatzResearch.WordTrace]
  refine ⟨18568876604578025423099993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12379251069718683615399995 18568876604578025423099993)
  ·
    refine ⟨13926657453433519067324995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18568876604578025423099993 13926657453433519067324995)
    ·
      refine ⟨20889986180150278600987493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13926657453433519067324995 20889986180150278600987493)
      ·
        refine ⟨3916872408778177237685155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20889986180150278600987493 3916872408778177237685155)
        ·
          refine ⟨5875308613167265856527733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3916872408778177237685155 5875308613167265856527733)
          ·
            refine ⟨550810182484431174049475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5875308613167265856527733 550810182484431174049475)
            ·
              refine ⟨826215273726646761074213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 550810182484431174049475 826215273726646761074213)
              ·
                refine ⟨154915363823746267701415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 826215273726646761074213 154915363823746267701415)
                ·
                  rfl

theorem cell19_509113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 1, 4].length) (baseStart_509113 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_509113 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_509113 prefixEnd_509113 := by exact prefixLift 509113
  have htrace : WordTrace (prefixWord ++ tailWord_509113) baseStart_509113 baseEnd_509113 := by
    simpa [prefixWord, tailWord_509113, baseEnd_509113] using wordTrace_append hprefix tailTrace_509113
  have hstable : (prefixWord ++ tailWord_509113).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509113).length < 2 ^ (prefixWord ++ tailWord_509113).sum := by decide
  have hdescent : baseEnd_509113 < baseStart_509113 := by decide
  rcases family_descends (prefixWord ++ tailWord_509113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509153 : List Nat := [1, 2, 3, 1, 3, 3, 6]
def baseStart_509153 : Nat := 118140960795 + 509153 * 2 ^ 59
def prefixEnd_509153 : Nat := 4983230072969 + 3 ^ 40 * 509153 * 2
def baseEnd_509153 : Nat := 51642511739012675604139

theorem tailTrace_509153 : CollatzResearch.WordTrace tailWord_509153 prefixEnd_509153 51642511739012675604139 := by
  unfold tailWord_509153
  simp only [CollatzResearch.WordTrace]
  refine ⟨18570335524433112254556113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12380223682955408169704075 18570335524433112254556113)
  ·
    refine ⟨13927751643324834190917085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18570335524433112254556113 13927751643324834190917085)
    ·
      refine ⟨5222906866246812821593907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13927751643324834190917085 5222906866246812821593907)
      ·
        refine ⟨7834360299370219232390861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5222906866246812821593907 7834360299370219232390861)
        ·
          refine ⟨2937885112263832212146573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7834360299370219232390861 2937885112263832212146573)
          ·
            refine ⟨1101706917098937079554965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2937885112263832212146573 1101706917098937079554965)
            ·
              refine ⟨51642511739012675604139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1101706917098937079554965 51642511739012675604139)
              ·
                rfl

theorem cell19_509153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 6].length) (baseStart_509153 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_509153 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_509153 prefixEnd_509153 := by exact prefixLift 509153
  have htrace : WordTrace (prefixWord ++ tailWord_509153) baseStart_509153 baseEnd_509153 := by
    simpa [prefixWord, tailWord_509153, baseEnd_509153] using wordTrace_append hprefix tailTrace_509153
  have hstable : (prefixWord ++ tailWord_509153).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509153).length < 2 ^ (prefixWord ++ tailWord_509153).sum := by decide
  have hdescent : baseEnd_509153 < baseStart_509153 := by decide
  rcases family_descends (prefixWord ++ tailWord_509153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509210 : List Nat := [3, 1, 1, 3, 3, 1, 7]
def baseStart_509210 : Nat := 118140960795 + 509210 * 2 ^ 59
def prefixEnd_509210 : Nat := 4983230072969 + 3 ^ 40 * 509210 * 2
def baseEnd_509210 : Nat := 51648293150826261181865

theorem tailTrace_509210 : CollatzResearch.WordTrace tailWord_509210 prefixEnd_509210 51648293150826261181865 := by
  unfold tailWord_509210
  simp only [CollatzResearch.WordTrace]
  refine ⟨4643103621306652747345271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12381609656817740659587389 4643103621306652747345271)
  ·
    refine ⟨6964655431959979121017907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4643103621306652747345271 6964655431959979121017907)
    ·
      refine ⟨10446983147939968681526861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6964655431959979121017907 10446983147939968681526861)
      ·
        refine ⟨3917618680477488255572573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10446983147939968681526861 3917618680477488255572573)
        ·
          refine ⟨1469107005179058095839715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3917618680477488255572573 1469107005179058095839715)
          ·
            refine ⟨2203660507768587143759573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1469107005179058095839715 2203660507768587143759573)
            ·
              refine ⟨51648293150826261181865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2203660507768587143759573 51648293150826261181865)
              ·
                rfl

theorem cell19_509210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 7].length) (baseStart_509210 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_509210 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_509210 prefixEnd_509210 := by exact prefixLift 509210
  have htrace : WordTrace (prefixWord ++ tailWord_509210) baseStart_509210 baseEnd_509210 := by
    simpa [prefixWord, tailWord_509210, baseEnd_509210] using wordTrace_append hprefix tailTrace_509210
  have hstable : (prefixWord ++ tailWord_509210).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509210).length < 2 ^ (prefixWord ++ tailWord_509210).sum := by decide
  have hdescent : baseEnd_509210 < baseStart_509210 := by decide
  rcases family_descends (prefixWord ++ tailWord_509210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509284 : List Nat := [2, 3, 1, 1, 3, 4, 1, 4]
def baseStart_509284 : Nat := 118140960795 + 509284 * 2 ^ 59
def prefixEnd_509284 : Nat := 4983230072969 + 3 ^ 40 * 509284 * 2
def baseEnd_509284 : Nat := 154967396530068537900949

theorem tailTrace_509284 : CollatzResearch.WordTrace tailWord_509284 prefixEnd_509284 154967396530068537900949 := by
  unfold tailWord_509284
  simp only [CollatzResearch.WordTrace]
  refine ⟨9287556743479260813787453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12383408991305681085049937 9287556743479260813787453)
  ·
    refine ⟨3482833778804722805170295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9287556743479260813787453 3482833778804722805170295)
    ·
      refine ⟨5224250668207084207755443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3482833778804722805170295 5224250668207084207755443)
      ·
        refine ⟨7836376002310626311633165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5224250668207084207755443 7836376002310626311633165)
        ·
          refine ⟨2938641000866484866862437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7836376002310626311633165 2938641000866484866862437)
          ·
            refine ⟨550995187662465912536707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2938641000866484866862437 550995187662465912536707)
            ·
              refine ⟨826492781493698868805061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 550995187662465912536707 826492781493698868805061)
              ·
                refine ⟨154967396530068537900949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 826492781493698868805061 154967396530068537900949)
                ·
                  rfl

theorem cell19_509284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 1, 4].length) (baseStart_509284 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_509284 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_509284 prefixEnd_509284 := by exact prefixLift 509284
  have htrace : WordTrace (prefixWord ++ tailWord_509284) baseStart_509284 baseEnd_509284 := by
    simpa [prefixWord, tailWord_509284, baseEnd_509284] using wordTrace_append hprefix tailTrace_509284
  have hstable : (prefixWord ++ tailWord_509284).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509284).length < 2 ^ (prefixWord ++ tailWord_509284).sum := by decide
  have hdescent : baseEnd_509284 < baseStart_509284 := by decide
  rcases family_descends (prefixWord ++ tailWord_509284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509301 : List Nat := [1, 3, 4, 1, 3, 1, 3, 3]
def baseStart_509301 : Nat := 118140960795 + 509301 * 2 ^ 59
def prefixEnd_509301 : Nat := 4983230072969 + 3 ^ 40 * 509301 * 2
def baseEnd_509301 : Nat := 154972569372217535523125

theorem tailTrace_509301 : CollatzResearch.WordTrace tailWord_509301 prefixEnd_509301 154972569372217535523125 := by
  unfold tailWord_509301
  simp only [CollatzResearch.WordTrace]
  refine ⟨18575733527896933530943757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12383822351931289020629171 18575733527896933530943757)
  ·
    refine ⟨6965900072961350074103909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18575733527896933530943757 6965900072961350074103909)
    ·
      refine ⟨1306106263680253138894483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6965900072961350074103909 1306106263680253138894483)
      ·
        refine ⟨1959159395520379708341725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1306106263680253138894483 1959159395520379708341725)
        ·
          refine ⟨734684773320142390628147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1959159395520379708341725 734684773320142390628147)
          ·
            refine ⟨1102027159980213585942221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 734684773320142390628147 1102027159980213585942221)
            ·
              refine ⟨413260184992580094728333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1102027159980213585942221 413260184992580094728333)
              ·
                refine ⟨154972569372217535523125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 413260184992580094728333 154972569372217535523125)
                ·
                  rfl

theorem cell19_509301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 3, 3].length) (baseStart_509301 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_509301 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_509301 prefixEnd_509301 := by exact prefixLift 509301
  have htrace : WordTrace (prefixWord ++ tailWord_509301) baseStart_509301 baseEnd_509301 := by
    simpa [prefixWord, tailWord_509301, baseEnd_509301] using wordTrace_append hprefix tailTrace_509301
  have hstable : (prefixWord ++ tailWord_509301).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509301).length < 2 ^ (prefixWord ++ tailWord_509301).sum := by decide
  have hdescent : baseEnd_509301 < baseStart_509301 := by decide
  rcases family_descends (prefixWord ++ tailWord_509301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509398 : List Nat := [5, 2, 1, 1, 1, 2, 1, 6]
def baseStart_509398 : Nat := 118140960795 + 509398 * 2 ^ 59
def prefixEnd_509398 : Nat := 4983230072969 + 3 ^ 40 * 509398 * 2
def baseEnd_509398 : Nat := 155002085000950051367305

theorem tailTrace_509398 : CollatzResearch.WordTrace tailWord_509398 prefixEnd_509398 155002085000950051367305 := by
  unfold tailWord_509398
  simp only [CollatzResearch.WordTrace]
  refine ⟨1161204463034094943576553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12386180939030346064816565 1161204463034094943576553)
  ·
    refine ⟨870903347275571207682415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1161204463034094943576553 870903347275571207682415)
    ·
      refine ⟨1306355020913356811523623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 870903347275571207682415 1306355020913356811523623)
      ·
        refine ⟨1959532531370035217285435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1306355020913356811523623 1959532531370035217285435)
        ·
          refine ⟨2939298797055052825928153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1959532531370035217285435 2939298797055052825928153)
          ·
            refine ⟨2204474097791289619446115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2939298797055052825928153 2204474097791289619446115)
            ·
              refine ⟨3306711146686934429169173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2204474097791289619446115 3306711146686934429169173)
              ·
                refine ⟨155002085000950051367305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3306711146686934429169173 155002085000950051367305)
                ·
                  rfl

theorem cell19_509398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_509398 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_509398 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_509398 prefixEnd_509398 := by exact prefixLift 509398
  have htrace : WordTrace (prefixWord ++ tailWord_509398) baseStart_509398 baseEnd_509398 := by
    simpa [prefixWord, tailWord_509398, baseEnd_509398] using wordTrace_append hprefix tailTrace_509398
  have hstable : (prefixWord ++ tailWord_509398).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509398).length < 2 ^ (prefixWord ++ tailWord_509398).sum := by decide
  have hdescent : baseEnd_509398 < baseStart_509398 := by decide
  rcases family_descends (prefixWord ++ tailWord_509398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509550 : List Nat := [4, 1, 2, 2, 3, 2, 5]
def baseStart_509550 : Nat := 118140960795 + 509550 * 2 ^ 59
def prefixEnd_509550 : Nat := 4983230072969 + 3 ^ 40 * 509550 * 2
def baseEnd_509550 : Nat := 51682778765152911996371

theorem tailTrace_509550 : CollatzResearch.WordTrace tailWord_509550 prefixEnd_509550 51682778765152911996371 := by
  unfold tailWord_509550
  simp only [CollatzResearch.WordTrace]
  refine ⟨2323101912999356132094763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12389876869329899371172069 2323101912999356132094763)
  ·
    refine ⟨3484652869499034198142145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2323101912999356132094763 3484652869499034198142145)
    ·
      refine ⟨2613489652124275648606609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3484652869499034198142145 2613489652124275648606609)
      ·
        refine ⟨1960117239093206736454957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2613489652124275648606609 1960117239093206736454957)
        ·
          refine ⟨735043964659952526170609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1960117239093206736454957 735043964659952526170609)
          ·
            refine ⟨551282973494964394627957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 735043964659952526170609 551282973494964394627957)
            ·
              refine ⟨51682778765152911996371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 551282973494964394627957 51682778765152911996371)
              ·
                rfl

theorem cell19_509550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 5].length) (baseStart_509550 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_509550 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_509550 prefixEnd_509550 := by exact prefixLift 509550
  have htrace : WordTrace (prefixWord ++ tailWord_509550) baseStart_509550 baseEnd_509550 := by
    simpa [prefixWord, tailWord_509550, baseEnd_509550] using wordTrace_append hprefix tailTrace_509550
  have hstable : (prefixWord ++ tailWord_509550).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509550).length < 2 ^ (prefixWord ++ tailWord_509550).sum := by decide
  have hdescent : baseEnd_509550 < baseStart_509550 := by decide
  rcases family_descends (prefixWord ++ tailWord_509550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509552 : List Nat := [2, 1, 1, 1, 6, 3, 5]
def baseStart_509552 : Nat := 118140960795 + 509552 * 2 ^ 59
def prefixEnd_509552 : Nat := 4983230072969 + 3 ^ 40 * 509552 * 2
def baseEnd_509552 : Nat := 51682981621707774648221

theorem tailTrace_509552 : CollatzResearch.WordTrace tailWord_509552 prefixEnd_509552 51682981621707774648221 := by
  unfold tailWord_509552
  simp only [CollatzResearch.WordTrace]
  refine ⟨9292444124993801699165455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12389925499991735598887273 9292444124993801699165455)
  ·
    refine ⟨13938666187490702548748183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9292444124993801699165455 13938666187490702548748183)
    ·
      refine ⟨20907999281236053823122275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13938666187490702548748183 20907999281236053823122275)
      ·
        refine ⟨31361998921854080734683413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20907999281236053823122275 31361998921854080734683413)
        ·
          refine ⟨1470093699461910034438285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 31361998921854080734683413 1470093699461910034438285)
          ·
            refine ⟨551285137298216262914357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1470093699461910034438285 551285137298216262914357)
            ·
              refine ⟨51682981621707774648221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 551285137298216262914357 51682981621707774648221)
              ·
                rfl

theorem cell19_509552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 5].length) (baseStart_509552 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_509552 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_509552 prefixEnd_509552 := by exact prefixLift 509552
  have htrace : WordTrace (prefixWord ++ tailWord_509552) baseStart_509552 baseEnd_509552 := by
    simpa [prefixWord, tailWord_509552, baseEnd_509552] using wordTrace_append hprefix tailTrace_509552
  have hstable : (prefixWord ++ tailWord_509552).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509552).length < 2 ^ (prefixWord ++ tailWord_509552).sum := by decide
  have hdescent : baseEnd_509552 < baseStart_509552 := by decide
  rcases family_descends (prefixWord ++ tailWord_509552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509628 : List Nat := [2, 2, 2, 3, 1, 2, 3, 4]
def baseStart_509628 : Nat := 118140960795 + 509628 * 2 ^ 59
def prefixEnd_509628 : Nat := 4983230072969 + 3 ^ 40 * 509628 * 2
def baseEnd_509628 : Nat := 155072070512377666255567

theorem tailTrace_509628 : CollatzResearch.WordTrace tailWord_509628 prefixEnd_509628 155072070512377666255567 := by
  unfold tailWord_509628
  simp only [CollatzResearch.WordTrace]
  refine ⟨9293830098856134189048769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12391773465141512252065025 9293830098856134189048769)
  ·
    refine ⟨6970372574142100641786577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9293830098856134189048769 6970372574142100641786577)
    ·
      refine ⟨5227779430606575481339933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6970372574142100641786577 5227779430606575481339933)
      ·
        refine ⟨1960417286477465805502475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5227779430606575481339933 1960417286477465805502475)
        ·
          refine ⟨2940625929716198708253713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1960417286477465805502475 2940625929716198708253713)
          ·
            refine ⟨2205469447287149031190285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2940625929716198708253713 2205469447287149031190285)
            ·
              refine ⟨827051042732680886696357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2205469447287149031190285 827051042732680886696357)
              ·
                refine ⟨155072070512377666255567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 827051042732680886696357 155072070512377666255567)
                ·
                  rfl

theorem cell19_509628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 4].length) (baseStart_509628 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_509628 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_509628 prefixEnd_509628 := by exact prefixLift 509628
  have htrace : WordTrace (prefixWord ++ tailWord_509628) baseStart_509628 baseEnd_509628 := by
    simpa [prefixWord, tailWord_509628, baseEnd_509628] using wordTrace_append hprefix tailTrace_509628
  have hstable : (prefixWord ++ tailWord_509628).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509628).length < 2 ^ (prefixWord ++ tailWord_509628).sum := by decide
  have hdescent : baseEnd_509628 < baseStart_509628 := by decide
  rcases family_descends (prefixWord ++ tailWord_509628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509668 : List Nat := [2, 3, 1, 1, 1, 3, 8]
def baseStart_509668 : Nat := 118140960795 + 509668 * 2 ^ 59
def prefixEnd_509668 : Nat := 4983230072969 + 3 ^ 40 * 509668 * 2
def baseEnd_509668 : Nat := 51694747301889808455523

theorem tailTrace_509668 : CollatzResearch.WordTrace tailWord_509668 prefixEnd_509668 51694747301889808455523 := by
  unfold tailWord_509668
  simp only [CollatzResearch.WordTrace]
  refine ⟨9294559558783677604776829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12392746078378236806369105 9294559558783677604776829)
  ·
    refine ⟨3485459834543879101791311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9294559558783677604776829 3485459834543879101791311)
    ·
      refine ⟨5228189751815818652686967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3485459834543879101791311 5228189751815818652686967)
      ·
        refine ⟨7842284627723727979030451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5228189751815818652686967 7842284627723727979030451)
        ·
          refine ⟨11763426941585591968545677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7842284627723727979030451 11763426941585591968545677)
          ·
            refine ⟨4411285103094596988204629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11763426941585591968545677 4411285103094596988204629)
            ·
              refine ⟨51694747301889808455523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4411285103094596988204629 51694747301889808455523)
              ·
                rfl

theorem cell19_509668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 8].length) (baseStart_509668 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_509668 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_509668 prefixEnd_509668 := by exact prefixLift 509668
  have htrace : WordTrace (prefixWord ++ tailWord_509668) baseStart_509668 baseEnd_509668 := by
    simpa [prefixWord, tailWord_509668, baseEnd_509668] using wordTrace_append hprefix tailTrace_509668
  have hstable : (prefixWord ++ tailWord_509668).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509668).length < 2 ^ (prefixWord ++ tailWord_509668).sum := by decide
  have hdescent : baseEnd_509668 < baseStart_509668 := by decide
  rcases family_descends (prefixWord ++ tailWord_509668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509763 : List Nat := [1, 1, 1, 3, 1, 5, 2, 5]
def baseStart_509763 : Nat := 118140960795 + 509763 * 2 ^ 59
def prefixEnd_509763 : Nat := 4983230072969 + 3 ^ 40 * 509763 * 2
def baseEnd_509763 : Nat := 155113148964737353255199

theorem tailTrace_509763 : CollatzResearch.WordTrace tailWord_509763 prefixEnd_509763 155113148964737353255199 := by
  unfold tailWord_509763
  simp only [CollatzResearch.WordTrace]
  refine ⟨18592584052223186434261943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12395056034815457622841295 18592584052223186434261943)
  ·
    refine ⟨27888876078334779651392915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18592584052223186434261943 27888876078334779651392915)
    ·
      refine ⟨41833314117502169477089373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27888876078334779651392915 41833314117502169477089373)
      ·
        refine ⟨15687492794063313553908515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41833314117502169477089373 15687492794063313553908515)
        ·
          refine ⟨23531239191094970330862773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15687492794063313553908515 23531239191094970330862773)
          ·
            refine ⟨2206053674165153468518385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23531239191094970330862773 2206053674165153468518385)
            ·
              refine ⟨1654540255623865101388789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2206053674165153468518385 1654540255623865101388789)
              ·
                refine ⟨155113148964737353255199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1654540255623865101388789 155113148964737353255199)
                ·
                  rfl

theorem cell19_509763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 5].length) (baseStart_509763 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_509763 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_509763 prefixEnd_509763 := by exact prefixLift 509763
  have htrace : WordTrace (prefixWord ++ tailWord_509763) baseStart_509763 baseEnd_509763 := by
    simpa [prefixWord, tailWord_509763, baseEnd_509763] using wordTrace_append hprefix tailTrace_509763
  have hstable : (prefixWord ++ tailWord_509763).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509763).length < 2 ^ (prefixWord ++ tailWord_509763).sum := by decide
  have hdescent : baseEnd_509763 < baseStart_509763 := by decide
  rcases family_descends (prefixWord ++ tailWord_509763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509814 : List Nat := [5, 1, 1, 3, 2, 1, 3, 3]
def baseStart_509814 : Nat := 118140960795 + 509814 * 2 ^ 59
def prefixEnd_509814 : Nat := 4983230072969 + 3 ^ 40 * 509814 * 2
def baseEnd_509814 : Nat := 155128667491184346121727

theorem tailTrace_509814 : CollatzResearch.WordTrace tailWord_509814 prefixEnd_509814 155128667491184346121727 := by
  unfold tailWord_509814
  simp only [CollatzResearch.WordTrace]
  refine ⟨1162152760939901384023031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12396296116692281429578997 1162152760939901384023031)
  ·
    refine ⟨1743229141409852076034547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1162152760939901384023031 1743229141409852076034547)
    ·
      refine ⟨2614843712114778114051821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1743229141409852076034547 2614843712114778114051821)
      ·
        refine ⟨980566392043041792769433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2614843712114778114051821 980566392043041792769433)
        ·
          refine ⟨735424794032281344577075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 980566392043041792769433 735424794032281344577075)
          ·
            refine ⟨1103137191048422016865613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 735424794032281344577075 1103137191048422016865613)
            ·
              refine ⟨413676446643158256324605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1103137191048422016865613 413676446643158256324605)
              ·
                refine ⟨155128667491184346121727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 413676446643158256324605 155128667491184346121727)
                ·
                  rfl

theorem cell19_509814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 3, 3].length) (baseStart_509814 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_509814 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_509814 prefixEnd_509814 := by exact prefixLift 509814
  have htrace : WordTrace (prefixWord ++ tailWord_509814) baseStart_509814 baseEnd_509814 := by
    simpa [prefixWord, tailWord_509814, baseEnd_509814] using wordTrace_append hprefix tailTrace_509814
  have hstable : (prefixWord ++ tailWord_509814).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509814).length < 2 ^ (prefixWord ++ tailWord_509814).sum := by decide
  have hdescent : baseEnd_509814 < baseStart_509814 := by decide
  rcases family_descends (prefixWord ++ tailWord_509814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509873 : List Nat := [1, 2, 2, 4, 2, 3, 2, 3]
def baseStart_509873 : Nat := 118140960795 + 509873 * 2 ^ 59
def prefixEnd_509873 : Nat := 4983230072969 + 3 ^ 40 * 509873 * 2
def baseEnd_509873 : Nat := 155146620296289690810455

theorem tailTrace_509873 : CollatzResearch.WordTrace tailWord_509873 prefixEnd_509873 155146620296289690810455 := by
  unfold tailWord_509873
  simp only [CollatzResearch.WordTrace]
  refine ⟨18596596081824675220766273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12397730721216450147177515 18596596081824675220766273)
  ·
    refine ⟨13947447061368506415574705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18596596081824675220766273 13947447061368506415574705)
    ·
      refine ⟨10460585296026379811681029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13947447061368506415574705 10460585296026379811681029)
      ·
        refine ⟨1961359743004946214690193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10460585296026379811681029 1961359743004946214690193)
        ·
          refine ⟨1471019807253709661017645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1961359743004946214690193 1471019807253709661017645)
          ·
            refine ⟨551632427720141122881617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1471019807253709661017645 551632427720141122881617)
            ·
              refine ⟨413724320790105842161213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 551632427720141122881617 413724320790105842161213)
              ·
                refine ⟨155146620296289690810455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 413724320790105842161213 155146620296289690810455)
                ·
                  rfl

theorem cell19_509873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 2, 3].length) (baseStart_509873 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_509873 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_509873 prefixEnd_509873 := by exact prefixLift 509873
  have htrace : WordTrace (prefixWord ++ tailWord_509873) baseStart_509873 baseEnd_509873 := by
    simpa [prefixWord, tailWord_509873, baseEnd_509873] using wordTrace_append hprefix tailTrace_509873
  have hstable : (prefixWord ++ tailWord_509873).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509873).length < 2 ^ (prefixWord ++ tailWord_509873).sum := by decide
  have hdescent : baseEnd_509873 < baseStart_509873 := by decide
  rcases family_descends (prefixWord ++ tailWord_509873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509896 : List Nat := [2, 1, 3, 1, 4, 1, 7]
def baseStart_509896 : Nat := 118140960795 + 509896 * 2 ^ 59
def prefixEnd_509896 : Nat := 4983230072969 + 3 ^ 40 * 509896 * 2
def baseEnd_509896 : Nat := 51717872949144150766427

theorem tailTrace_509896 : CollatzResearch.WordTrace tailWord_509896 prefixEnd_509896 51717872949144150766427 := by
  unfold tailWord_509896
  simp only [CollatzResearch.WordTrace]
  refine ⟨9298717480370675074426771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12398289973827566765902361 9298717480370675074426771)
  ·
    refine ⟨13948076220556012611640157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9298717480370675074426771 13948076220556012611640157)
    ·
      refine ⟨5230528582708504729365059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13948076220556012611640157 5230528582708504729365059)
      ·
        refine ⟨7845792874062757094047589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5230528582708504729365059 7845792874062757094047589)
        ·
          refine ⟨1471086163886766955133923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7845792874062757094047589 1471086163886766955133923)
          ·
            refine ⟨2206629245830150432700885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1471086163886766955133923 2206629245830150432700885)
            ·
              refine ⟨51717872949144150766427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2206629245830150432700885 51717872949144150766427)
              ·
                rfl

theorem cell19_509896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 7].length) (baseStart_509896 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_509896 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_509896 prefixEnd_509896 := by exact prefixLift 509896
  have htrace : WordTrace (prefixWord ++ tailWord_509896) baseStart_509896 baseEnd_509896 := by
    simpa [prefixWord, tailWord_509896, baseEnd_509896] using wordTrace_append hprefix tailTrace_509896
  have hstable : (prefixWord ++ tailWord_509896).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509896).length < 2 ^ (prefixWord ++ tailWord_509896).sum := by decide
  have hdescent : baseEnd_509896 < baseStart_509896 := by decide
  rcases family_descends (prefixWord ++ tailWord_509896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509913 : List Nat := [1, 2, 1, 2, 6, 1, 2, 4]
def baseStart_509913 : Nat := 118140960795 + 509913 * 2 ^ 59
def prefixEnd_509913 : Nat := 4983230072969 + 3 ^ 40 * 509913 * 2
def baseEnd_509913 : Nat := 155158791689581449921457

theorem tailTrace_509913 : CollatzResearch.WordTrace tailWord_509913 prefixEnd_509913 155158791689581449921457 := by
  unfold tailWord_509913
  simp only [CollatzResearch.WordTrace]
  refine ⟨18598055001679762052222393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12398703334453174701481595 18598055001679762052222393)
  ·
    refine ⟨13948541251259821539166795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18598055001679762052222393 13948541251259821539166795)
    ·
      refine ⟨20922811876889732308750193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13948541251259821539166795 20922811876889732308750193)
      ·
        refine ⟨15692108907667299231562645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20922811876889732308750193 15692108907667299231562645)
        ·
          refine ⟨735567605046904651479499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 15692108907667299231562645 735567605046904651479499)
          ·
            refine ⟨1103351407570356977219249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 735567605046904651479499 1103351407570356977219249)
            ·
              refine ⟨827513555677767732914437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1103351407570356977219249 827513555677767732914437)
              ·
                refine ⟨155158791689581449921457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 827513555677767732914437 155158791689581449921457)
                ·
                  rfl

theorem cell19_509913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 2, 4].length) (baseStart_509913 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_509913 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_509913 prefixEnd_509913 := by exact prefixLift 509913
  have htrace : WordTrace (prefixWord ++ tailWord_509913) baseStart_509913 baseEnd_509913 := by
    simpa [prefixWord, tailWord_509913, baseEnd_509913] using wordTrace_append hprefix tailTrace_509913
  have hstable : (prefixWord ++ tailWord_509913).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509913).length < 2 ^ (prefixWord ++ tailWord_509913).sum := by decide
  have hdescent : baseEnd_509913 < baseStart_509913 := by decide
  rcases family_descends (prefixWord ++ tailWord_509913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509989 : List Nat := [1, 3, 1, 2, 2, 4, 3, 3]
def baseStart_509989 : Nat := 118140960795 + 509989 * 2 ^ 59
def prefixEnd_509989 : Nat := 4983230072969 + 3 ^ 40 * 509989 * 2
def baseEnd_509989 : Nat := 155181917336835792232361

theorem tailTrace_509989 : CollatzResearch.WordTrace tailWord_509989 prefixEnd_509989 155181917336835792232361 := by
  unfold tailWord_509989
  simp only [CollatzResearch.WordTrace]
  refine ⟨18600826949404427031989021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12400551299602951354659347 18600826949404427031989021)
  ·
    refine ⟨6975310106026660136995883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18600826949404427031989021 6975310106026660136995883)
    ·
      refine ⟨10462965159039990205493825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6975310106026660136995883 10462965159039990205493825)
      ·
        refine ⟨7847223869279992654120369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10462965159039990205493825 7847223869279992654120369)
        ·
          refine ⟨5885417901959994490590277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7847223869279992654120369 5885417901959994490590277)
          ·
            refine ⟨1103515856617498966985677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5885417901959994490590277 1103515856617498966985677)
            ·
              refine ⟨413818446231562112619629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1103515856617498966985677 413818446231562112619629)
              ·
                refine ⟨155181917336835792232361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 413818446231562112619629 155181917336835792232361)
                ·
                  rfl

theorem cell19_509989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 3, 3].length) (baseStart_509989 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_509989 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_509989 prefixEnd_509989 := by exact prefixLift 509989
  have htrace : WordTrace (prefixWord ++ tailWord_509989) baseStart_509989 baseEnd_509989 := by
    simpa [prefixWord, tailWord_509989, baseEnd_509989] using wordTrace_append hprefix tailTrace_509989
  have hstable : (prefixWord ++ tailWord_509989).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509989).length < 2 ^ (prefixWord ++ tailWord_509989).sum := by decide
  have hdescent : baseEnd_509989 < baseStart_509989 := by decide
  rcases family_descends (prefixWord ++ tailWord_509989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510044 : List Nat := [2, 2, 4, 1, 1, 4, 2, 3]
def baseStart_510044 : Nat := 118140960795 + 510044 * 2 ^ 59
def prefixEnd_510044 : Nat := 4983230072969 + 3 ^ 40 * 510044 * 2
def baseEnd_510044 : Nat := 155198653002611961009989

theorem tailTrace_510044 : CollatzResearch.WordTrace tailWord_510044 prefixEnd_510044 155198653002611961009989 := by
  unfold tailWord_510044
  simp only [CollatzResearch.WordTrace]
  refine ⟨9301416482102585712620593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12401888642803447616827457 9301416482102585712620593)
  ·
    refine ⟨6976062361576939284465445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9301416482102585712620593 6976062361576939284465445)
    ·
      refine ⟨1308011692795676115837271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6976062361576939284465445 1308011692795676115837271)
      ·
        refine ⟨1962017539193514173755907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1308011692795676115837271 1962017539193514173755907)
        ·
          refine ⟨2943026308790271260633861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1962017539193514173755907 2943026308790271260633861)
          ·
            refine ⟨551817432898175861368849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2943026308790271260633861 551817432898175861368849)
            ·
              refine ⟨413863074673631896026637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 551817432898175861368849 413863074673631896026637)
              ·
                refine ⟨155198653002611961009989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 413863074673631896026637 155198653002611961009989)
                ·
                  rfl

theorem cell19_510044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 2, 3].length) (baseStart_510044 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_510044 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_510044 prefixEnd_510044 := by exact prefixLift 510044
  have htrace : WordTrace (prefixWord ++ tailWord_510044) baseStart_510044 baseEnd_510044 := by
    simpa [prefixWord, tailWord_510044, baseEnd_510044] using wordTrace_append hprefix tailTrace_510044
  have hstable : (prefixWord ++ tailWord_510044).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510044).length < 2 ^ (prefixWord ++ tailWord_510044).sum := by decide
  have hdescent : baseEnd_510044 < baseStart_510044 := by decide
  rcases family_descends (prefixWord ++ tailWord_510044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510048 : List Nat := [2, 1, 1, 3, 2, 4, 1, 5]
def baseStart_510048 : Nat := 118140960795 + 510048 * 2 ^ 59
def prefixEnd_510048 : Nat := 4983230072969 + 3 ^ 40 * 510048 * 2
def baseEnd_510048 : Nat := 155199870141941136921089

theorem tailTrace_510048 : CollatzResearch.WordTrace tailWord_510048 prefixEnd_510048 155199870141941136921089 := by
  unfold tailWord_510048
  simp only [CollatzResearch.WordTrace]
  refine ⟨9301489428095340054193399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12401985904127120072257865 9301489428095340054193399)
  ·
    refine ⟨13952234142143010081290099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9301489428095340054193399 13952234142143010081290099)
    ·
      refine ⟨20928351213214515121935149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13952234142143010081290099 20928351213214515121935149)
      ·
        refine ⟨7848131704955443170725681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20928351213214515121935149 7848131704955443170725681)
        ·
          refine ⟨5886098778716582378044261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7848131704955443170725681 5886098778716582378044261)
          ·
            refine ⟨1103643521009359195883299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5886098778716582378044261 1103643521009359195883299)
            ·
              refine ⟨1655465281514038793824949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1103643521009359195883299 1655465281514038793824949)
              ·
                refine ⟨155199870141941136921089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1655465281514038793824949 155199870141941136921089)
                ·
                  rfl

theorem cell19_510048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 5].length) (baseStart_510048 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_510048 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_510048 prefixEnd_510048 := by exact prefixLift 510048
  have htrace : WordTrace (prefixWord ++ tailWord_510048) baseStart_510048 baseEnd_510048 := by
    simpa [prefixWord, tailWord_510048, baseEnd_510048] using wordTrace_append hprefix tailTrace_510048
  have hstable : (prefixWord ++ tailWord_510048).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510048).length < 2 ^ (prefixWord ++ tailWord_510048).sum := by decide
  have hdescent : baseEnd_510048 < baseStart_510048 := by decide
  rcases family_descends (prefixWord ++ tailWord_510048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510107 : List Nat := [1, 1, 1, 1, 1, 1, 2, 11]
def baseStart_510107 : Nat := 118140960795 + 510107 * 2 ^ 59
def prefixEnd_510107 : Nat := 4983230072969 + 3 ^ 40 * 510107 * 2
def baseEnd_510107 : Nat := 155217822947046481609817

theorem tailTrace_510107 : CollatzResearch.WordTrace tailWord_510107 prefixEnd_510107 155217822947046481609817 := by
  unfold tailWord_510107
  simp only [CollatzResearch.WordTrace]
  refine ⟨18605130762976933184784575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12403420508651288789856383 18605130762976933184784575)
  ·
    refine ⟨27907696144465399777176863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18605130762976933184784575 27907696144465399777176863)
    ·
      refine ⟨41861544216698099665765295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27907696144465399777176863 41861544216698099665765295)
      ·
        refine ⟨62792316325047149498647943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41861544216698099665765295 62792316325047149498647943)
        ·
          refine ⟨94188474487570724247971915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62792316325047149498647943 94188474487570724247971915)
          ·
            refine ⟨141282711731356086371957873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94188474487570724247971915 141282711731356086371957873)
            ·
              refine ⟨105962033798517064778968405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141282711731356086371957873 105962033798517064778968405)
              ·
                refine ⟨155217822947046481609817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 105962033798517064778968405 155217822947046481609817)
                ·
                  rfl

theorem cell19_510107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 11].length) (baseStart_510107 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_510107 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_510107 prefixEnd_510107 := by exact prefixLift 510107
  have htrace : WordTrace (prefixWord ++ tailWord_510107) baseStart_510107 baseEnd_510107 := by
    simpa [prefixWord, tailWord_510107, baseEnd_510107] using wordTrace_append hprefix tailTrace_510107
  have hstable : (prefixWord ++ tailWord_510107).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510107).length < 2 ^ (prefixWord ++ tailWord_510107).sum := by decide
  have hdescent : baseEnd_510107 < baseStart_510107 := by decide
  rcases family_descends (prefixWord ++ tailWord_510107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510122 : List Nat := [3, 1, 5, 1, 2, 7]
def baseStart_510122 : Nat := 118140960795 + 510122 * 2 ^ 59
def prefixEnd_510122 : Nat := 4983230072969 + 3 ^ 40 * 510122 * 2
def baseEnd_510122 : Nat := 17246931913281210141827

theorem tailTrace_510122 : CollatzResearch.WordTrace tailWord_510122 prefixEnd_510122 17246931913281210141827 := by
  unfold tailWord_510122
  simp only [CollatzResearch.WordTrace]
  refine ⟨4651419464480647686645155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12403785238615060497720413 4651419464480647686645155)
  ·
    refine ⟨6977129196720971529967733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4651419464480647686645155 6977129196720971529967733)
    ·
      refine ⟨654105862192591080934475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6977129196720971529967733 654105862192591080934475)
      ·
        refine ⟨981158793288886621401713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 654105862192591080934475 981158793288886621401713)
        ·
          refine ⟨735869094966664966051285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 981158793288886621401713 735869094966664966051285)
          ·
            refine ⟨17246931913281210141827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 735869094966664966051285 17246931913281210141827)
            ·
              rfl

theorem cell19_510122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 7].length) (baseStart_510122 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_510122 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_510122 prefixEnd_510122 := by exact prefixLift 510122
  have htrace : WordTrace (prefixWord ++ tailWord_510122) baseStart_510122 baseEnd_510122 := by
    simpa [prefixWord, tailWord_510122, baseEnd_510122] using wordTrace_append hprefix tailTrace_510122
  have hstable : (prefixWord ++ tailWord_510122).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510122).length < 2 ^ (prefixWord ++ tailWord_510122).sum := by decide
  have hdescent : baseEnd_510122 < baseStart_510122 := by decide
  rcases family_descends (prefixWord ++ tailWord_510122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510179 : List Nat := [1, 1, 1, 8, 1, 1, 6]
def baseStart_510179 : Nat := 118140960795 + 510179 * 2 ^ 59
def prefixEnd_510179 : Nat := 4983230072969 + 3 ^ 40 * 510179 * 2
def baseEnd_510179 : Nat := 51746577151657216003207

theorem tailTrace_510179 : CollatzResearch.WordTrace tailWord_510179 prefixEnd_510179 51746577151657216003207 := by
  unfold tailWord_510179
  simp only [CollatzResearch.WordTrace]
  refine ⟨18607756818716089481405591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12405171212477392987603727 18607756818716089481405591)
  ·
    refine ⟨27911635228074134222108387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18607756818716089481405591 27911635228074134222108387)
    ·
      refine ⟨41867452842111201333162581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27911635228074134222108387 41867452842111201333162581)
      ·
        refine ⟨490634212993490640622999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 41867452842111201333162581 490634212993490640622999)
        ·
          refine ⟨735951319490235960934499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 490634212993490640622999 735951319490235960934499)
          ·
            refine ⟨1103926979235353941401749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 735951319490235960934499 1103926979235353941401749)
            ·
              refine ⟨51746577151657216003207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1103926979235353941401749 51746577151657216003207)
              ·
                rfl

theorem cell19_510179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 6].length) (baseStart_510179 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_510179 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_510179 prefixEnd_510179 := by exact prefixLift 510179
  have htrace : WordTrace (prefixWord ++ tailWord_510179) baseStart_510179 baseEnd_510179 := by
    simpa [prefixWord, tailWord_510179, baseEnd_510179] using wordTrace_append hprefix tailTrace_510179
  have hstable : (prefixWord ++ tailWord_510179).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510179).length < 2 ^ (prefixWord ++ tailWord_510179).sum := by decide
  have hdescent : baseEnd_510179 < baseStart_510179 := by decide
  rcases family_descends (prefixWord ++ tailWord_510179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510181 : List Nat := [1, 3, 1, 4, 2, 2, 6]
def baseStart_510181 : Nat := 118140960795 + 510181 * 2 ^ 59
def prefixEnd_510181 : Nat := 4983230072969 + 3 ^ 40 * 510181 * 2
def baseEnd_510181 : Nat := 51746780008212078655057

theorem tailTrace_510181 : CollatzResearch.WordTrace tailWord_510181 prefixEnd_510181 51746780008212078655057 := by
  unfold tailWord_510181
  simp only [CollatzResearch.WordTrace]
  refine ⟨18607829764708843822978397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12405219843139229215318931 18607829764708843822978397)
  ·
    refine ⟨6977936161765816433616899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18607829764708843822978397 6977936161765816433616899)
    ·
      refine ⟨10466904242648724650425349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6977936161765816433616899 10466904242648724650425349)
      ·
        refine ⟨1962544545496635871954753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10466904242648724650425349 1962544545496635871954753)
        ·
          refine ⟨1471908409122476903966065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1962544545496635871954753 1471908409122476903966065)
          ·
            refine ⟨1103931306841857677974549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1471908409122476903966065 1103931306841857677974549)
            ·
              refine ⟨51746780008212078655057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1103931306841857677974549 51746780008212078655057)
              ·
                rfl

theorem cell19_510181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 6].length) (baseStart_510181 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_510181 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_510181 prefixEnd_510181 := by exact prefixLift 510181
  have htrace : WordTrace (prefixWord ++ tailWord_510181) baseStart_510181 baseEnd_510181 := by
    simpa [prefixWord, tailWord_510181, baseEnd_510181] using wordTrace_append hprefix tailTrace_510181
  have hstable : (prefixWord ++ tailWord_510181).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510181).length < 2 ^ (prefixWord ++ tailWord_510181).sum := by decide
  have hdescent : baseEnd_510181 < baseStart_510181 := by decide
  rcases family_descends (prefixWord ++ tailWord_510181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510217 : List Nat := [1, 2, 1, 1, 3, 6, 2, 3]
def baseStart_510217 : Nat := 118140960795 + 510217 * 2 ^ 59
def prefixEnd_510217 : Nat := 4983230072969 + 3 ^ 40 * 510217 * 2
def baseEnd_510217 : Nat := 155251294278598819165073

theorem tailTrace_510217 : CollatzResearch.WordTrace tailWord_510217 prefixEnd_510217 155251294278598819165073 := by
  unfold tailWord_510217
  simp only [CollatzResearch.WordTrace]
  refine ⟨18609142792578421971288905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12406095195052281314192603 18609142792578421971288905)
  ·
    refine ⟨13956857094433816478466679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18609142792578421971288905 13956857094433816478466679)
    ·
      refine ⟨20935285641650724717700019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13956857094433816478466679 20935285641650724717700019)
      ·
        refine ⟨31402928462476087076550029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20935285641650724717700019 31402928462476087076550029)
        ·
          refine ⟨11776098173428532653706261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31402928462476087076550029 11776098173428532653706261)
          ·
            refine ⟨552004601879462468142481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 11776098173428532653706261 552004601879462468142481)
            ·
              refine ⟨414003451409596851106861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 552004601879462468142481 414003451409596851106861)
              ·
                refine ⟨155251294278598819165073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 414003451409596851106861 155251294278598819165073)
                ·
                  rfl

theorem cell19_510217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 2, 3].length) (baseStart_510217 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_510217 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_510217 prefixEnd_510217 := by exact prefixLift 510217
  have htrace : WordTrace (prefixWord ++ tailWord_510217) baseStart_510217 baseEnd_510217 := by
    simpa [prefixWord, tailWord_510217, baseEnd_510217] using wordTrace_append hprefix tailTrace_510217
  have hstable : (prefixWord ++ tailWord_510217).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510217).length < 2 ^ (prefixWord ++ tailWord_510217).sum := by decide
  have hdescent : baseEnd_510217 < baseStart_510217 := by decide
  rcases family_descends (prefixWord ++ tailWord_510217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510253 : List Nat := [1, 5, 3, 1, 2, 1, 2, 4]
def baseStart_510253 : Nat := 118140960795 + 510253 * 2 ^ 59
def prefixEnd_510253 : Nat := 4983230072969 + 3 ^ 40 * 510253 * 2
def baseEnd_510253 : Nat := 155262248532561402364975

theorem tailTrace_510253 : CollatzResearch.WordTrace tailWord_510253 prefixEnd_510253 155262248532561402364975 := by
  unfold tailWord_510253
  simp only [CollatzResearch.WordTrace]
  refine ⟨18610455820448000119599413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12406970546965333413066275 18610455820448000119599413)
  ·
    refine ⟨1744730233167000011212445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18610455820448000119599413 1744730233167000011212445)
    ·
      refine ⟨654273837437625004204667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1744730233167000011212445 654273837437625004204667)
      ·
        refine ⟨981410756156437506307001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 654273837437625004204667 981410756156437506307001)
        ·
          refine ⟨736058067117328129730251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 981410756156437506307001 736058067117328129730251)
          ·
            refine ⟨1104087100675992194595377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 736058067117328129730251 1104087100675992194595377)
            ·
              refine ⟨828065325506994145946533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1104087100675992194595377 828065325506994145946533)
              ·
                refine ⟨155262248532561402364975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 828065325506994145946533 155262248532561402364975)
                ·
                  rfl

theorem cell19_510253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 2, 4].length) (baseStart_510253 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_510253 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_510253 prefixEnd_510253 := by exact prefixLift 510253
  have htrace : WordTrace (prefixWord ++ tailWord_510253) baseStart_510253 baseEnd_510253 := by
    simpa [prefixWord, tailWord_510253, baseEnd_510253] using wordTrace_append hprefix tailTrace_510253
  have hstable : (prefixWord ++ tailWord_510253).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510253).length < 2 ^ (prefixWord ++ tailWord_510253).sum := by decide
  have hdescent : baseEnd_510253 < baseStart_510253 := by decide
  rcases family_descends (prefixWord ++ tailWord_510253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510312 : List Nat := [2, 1, 4, 2, 2, 3, 1, 4]
def baseStart_510312 : Nat := 118140960795 + 510312 * 2 ^ 59
def prefixEnd_510312 : Nat := 4983230072969 + 3 ^ 40 * 510312 * 2
def baseEnd_510312 : Nat := 155280201337666747053703

theorem tailTrace_510312 : CollatzResearch.WordTrace tailWord_510312 prefixEnd_510312 155280201337666747053703 := by
  unfold tailWord_510312
  simp only [CollatzResearch.WordTrace]
  refine ⟨9306303863617126597998595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12408405151489502130664793 9306303863617126597998595)
  ·
    refine ⟨13959455795425689896997893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9306303863617126597998595 13959455795425689896997893)
    ·
      refine ⟨2617397961642316855687105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13959455795425689896997893 2617397961642316855687105)
      ·
        refine ⟨1963048471231737641765329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2617397961642316855687105 1963048471231737641765329)
        ·
          refine ⟨1472286353423803231323997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1963048471231737641765329 1472286353423803231323997)
          ·
            refine ⟨552107382533926211746499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1472286353423803231323997 552107382533926211746499)
            ·
              refine ⟨828161073800889317619749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 552107382533926211746499 828161073800889317619749)
              ·
                refine ⟨155280201337666747053703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 828161073800889317619749 155280201337666747053703)
                ·
                  rfl

theorem cell19_510312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 1, 4].length) (baseStart_510312 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_510312 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_510312 prefixEnd_510312 := by exact prefixLift 510312
  have htrace : WordTrace (prefixWord ++ tailWord_510312) baseStart_510312 baseEnd_510312 := by
    simpa [prefixWord, tailWord_510312, baseEnd_510312] using wordTrace_append hprefix tailTrace_510312
  have hstable : (prefixWord ++ tailWord_510312).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510312).length < 2 ^ (prefixWord ++ tailWord_510312).sum := by decide
  have hdescent : baseEnd_510312 < baseStart_510312 := by decide
  rcases family_descends (prefixWord ++ tailWord_510312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510373 : List Nat := [1, 3, 1, 2, 1, 1, 4, 6]
def baseStart_510373 : Nat := 118140960795 + 510373 * 2 ^ 59
def prefixEnd_510373 : Nat := 4983230072969 + 3 ^ 40 * 510373 * 2
def baseEnd_510373 : Nat := 155298762712436679697981

theorem tailTrace_510373 : CollatzResearch.WordTrace tailWord_510373 prefixEnd_510373 155298762712436679697981 := by
  unfold tailWord_510373
  simp only [CollatzResearch.WordTrace]
  refine ⟨18614832580013260613967773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12409888386675507075978515 18614832580013260613967773)
  ·
    refine ⟨6980562217504972730237915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18614832580013260613967773 6980562217504972730237915)
    ·
      refine ⟨10470843326257459095356873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6980562217504972730237915 10470843326257459095356873)
      ·
        refine ⟨7853132494693094321517655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10470843326257459095356873 7853132494693094321517655)
        ·
          refine ⟨11779698742039641482276483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7853132494693094321517655 11779698742039641482276483)
          ·
            refine ⟨17669548113059462223414725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11779698742039641482276483 17669548113059462223414725)
            ·
              refine ⟨3313040271198649166890261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17669548113059462223414725 3313040271198649166890261)
              ·
                refine ⟨155298762712436679697981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3313040271198649166890261 155298762712436679697981)
                ·
                  rfl

theorem cell19_510373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 6].length) (baseStart_510373 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_510373 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_510373 prefixEnd_510373 := by exact prefixLift 510373
  have htrace : WordTrace (prefixWord ++ tailWord_510373) baseStart_510373 baseEnd_510373 := by
    simpa [prefixWord, tailWord_510373, baseEnd_510373] using wordTrace_append hprefix tailTrace_510373
  have hstable : (prefixWord ++ tailWord_510373).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510373).length < 2 ^ (prefixWord ++ tailWord_510373).sum := by decide
  have hdescent : baseEnd_510373 < baseStart_510373 := by decide
  rcases family_descends (prefixWord ++ tailWord_510373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510449 : List Nat := [1, 2, 2, 2, 3, 1, 1, 7]
def baseStart_510449 : Nat := 118140960795 + 510449 * 2 ^ 59
def prefixEnd_510449 : Nat := 4983230072969 + 3 ^ 40 * 510449 * 2
def baseEnd_510449 : Nat := 155321888359691022008885

theorem tailTrace_510449 : CollatzResearch.WordTrace tailWord_510449 prefixEnd_510449 155321888359691022008885 := by
  unfold tailWord_510449
  simp only [CollatzResearch.WordTrace]
  refine ⟨18617604527737925593734401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12411736351825283729156267 18617604527737925593734401)
  ·
    refine ⟨13963203395803444195300801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18617604527737925593734401 13963203395803444195300801)
    ·
      refine ⟨10472402546852583146475601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13963203395803444195300801 10472402546852583146475601)
      ·
        refine ⟨7854301910139437359856701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10472402546852583146475601 7854301910139437359856701)
        ·
          refine ⟨2945363216302289009946263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7854301910139437359856701 2945363216302289009946263)
          ·
            refine ⟨4418044824453433514919395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2945363216302289009946263 4418044824453433514919395)
            ·
              refine ⟨6627067236680150272379093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4418044824453433514919395 6627067236680150272379093)
              ·
                refine ⟨155321888359691022008885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6627067236680150272379093 155321888359691022008885)
                ·
                  rfl

theorem cell19_510449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 7].length) (baseStart_510449 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_510449 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_510449 prefixEnd_510449 := by exact prefixLift 510449
  have htrace : WordTrace (prefixWord ++ tailWord_510449) baseStart_510449 baseEnd_510449 := by
    simpa [prefixWord, tailWord_510449, baseEnd_510449] using wordTrace_append hprefix tailTrace_510449
  have hstable : (prefixWord ++ tailWord_510449).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510449).length < 2 ^ (prefixWord ++ tailWord_510449).sum := by decide
  have hdescent : baseEnd_510449 < baseStart_510449 := by decide
  rcases family_descends (prefixWord ++ tailWord_510449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510466 : List Nat := [3, 4, 1, 2, 9]
def baseStart_510466 : Nat := 118140960795 + 510466 * 2 ^ 59
def prefixEnd_510466 : Nat := 4983230072969 + 3 ^ 40 * 510466 * 2
def baseEnd_510466 : Nat := 5752854118586667393743

theorem tailTrace_510466 : CollatzResearch.WordTrace tailWord_510466 prefixEnd_510466 5752854118586667393743 := by
  unfold tailWord_510466
  simp only [CollatzResearch.WordTrace]
  refine ⟨4654556142169084374275813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12412149712450891664735501 4654556142169084374275813)
  ·
    refine ⟨872729276656703320176715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4654556142169084374275813 872729276656703320176715)
    ·
      refine ⟨1309093914985054980265073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 872729276656703320176715 1309093914985054980265073)
      ·
        refine ⟨981820436238791235198805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1309093914985054980265073 981820436238791235198805)
        ·
          refine ⟨5752854118586667393743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 981820436238791235198805 5752854118586667393743)
          ·
            rfl

theorem cell19_510466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 9].length) (baseStart_510466 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_510466 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_510466 prefixEnd_510466 := by exact prefixLift 510466
  have htrace : WordTrace (prefixWord ++ tailWord_510466) baseStart_510466 baseEnd_510466 := by
    simpa [prefixWord, tailWord_510466, baseEnd_510466] using wordTrace_append hprefix tailTrace_510466
  have hstable : (prefixWord ++ tailWord_510466).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510466).length < 2 ^ (prefixWord ++ tailWord_510466).sum := by decide
  have hdescent : baseEnd_510466 < baseStart_510466 := by decide
  rcases family_descends (prefixWord ++ tailWord_510466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510500 : List Nat := [2, 3, 1, 5, 1, 1, 3, 3]
def baseStart_510500 : Nat := 118140960795 + 510500 * 2 ^ 59
def prefixEnd_510500 : Nat := 4983230072969 + 3 ^ 40 * 510500 * 2
def baseEnd_510500 : Nat := 155337406886138014875413

theorem tailTrace_510500 : CollatzResearch.WordTrace tailWord_510500 prefixEnd_510500 155337406886138014875413 := by
  unfold tailWord_510500
  simp only [CollatzResearch.WordTrace]
  refine ⟨9309732325276580651920477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12412976433702107535893969 9309732325276580651920477)
  ·
    refine ⟨3491149621978717744470179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9309732325276580651920477 3491149621978717744470179)
    ·
      refine ⟨5236724432968076616705269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3491149621978717744470179 5236724432968076616705269)
      ·
        refine ⟨490942915590757182816119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5236724432968076616705269 490942915590757182816119)
        ·
          refine ⟨736414373386135774224179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 490942915590757182816119 736414373386135774224179)
          ·
            refine ⟨1104621560079203661336269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 736414373386135774224179 1104621560079203661336269)
            ·
              refine ⟨414233085029701373001101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1104621560079203661336269 414233085029701373001101)
              ·
                refine ⟨155337406886138014875413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 414233085029701373001101 155337406886138014875413)
                ·
                  rfl

theorem cell19_510500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 3, 3].length) (baseStart_510500 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_510500 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_510500 prefixEnd_510500 := by exact prefixLift 510500
  have htrace : WordTrace (prefixWord ++ tailWord_510500) baseStart_510500 baseEnd_510500 := by
    simpa [prefixWord, tailWord_510500, baseEnd_510500] using wordTrace_append hprefix tailTrace_510500
  have hstable : (prefixWord ++ tailWord_510500).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510500).length < 2 ^ (prefixWord ++ tailWord_510500).sum := by decide
  have hdescent : baseEnd_510500 < baseStart_510500 := by decide
  rcases family_descends (prefixWord ++ tailWord_510500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510561 : List Nat := [1, 2, 3, 1, 1, 4, 4, 3]
def baseStart_510561 : Nat := 118140960795 + 510561 * 2 ^ 59
def prefixEnd_510561 : Nat := 4983230072969 + 3 ^ 40 * 510561 * 2
def baseEnd_510561 : Nat := 155355968260907947519691

theorem tailTrace_510561 : CollatzResearch.WordTrace tailWord_510561 prefixEnd_510561 155355968260907947519691 := by
  unfold tailWord_510561
  simp only [CollatzResearch.WordTrace]
  refine ⟨18621689503332168721811537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12414459668888112481207691 18621689503332168721811537)
  ·
    refine ⟨13966267127499126541358653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18621689503332168721811537 13966267127499126541358653)
    ·
      refine ⟨5237350172812172453009495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13966267127499126541358653 5237350172812172453009495)
      ·
        refine ⟨7856025259218258679514243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5237350172812172453009495 7856025259218258679514243)
        ·
          refine ⟨11784037888827388019271365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7856025259218258679514243 11784037888827388019271365)
          ·
            refine ⟨2209507104155135253613381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11784037888827388019271365 2209507104155135253613381)
            ·
              refine ⟨414282582029087860052509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2209507104155135253613381 414282582029087860052509)
              ·
                refine ⟨155355968260907947519691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 414282582029087860052509 155355968260907947519691)
                ·
                  rfl

theorem cell19_510561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 4, 3].length) (baseStart_510561 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_510561 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_510561 prefixEnd_510561 := by exact prefixLift 510561
  have htrace : WordTrace (prefixWord ++ tailWord_510561) baseStart_510561 baseEnd_510561 := by
    simpa [prefixWord, tailWord_510561, baseEnd_510561] using wordTrace_append hprefix tailTrace_510561
  have hstable : (prefixWord ++ tailWord_510561).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510561).length < 2 ^ (prefixWord ++ tailWord_510561).sum := by decide
  have hdescent : baseEnd_510561 < baseStart_510561 := by decide
  rcases family_descends (prefixWord ++ tailWord_510561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510563 : List Nat := [1, 1, 1, 5, 1, 2, 3, 5]
def baseStart_510563 : Nat := 118140960795 + 510563 * 2 ^ 59
def prefixEnd_510563 : Nat := 4983230072969 + 3 ^ 40 * 510563 * 2
def baseEnd_510563 : Nat := 155356576830572535475241

theorem tailTrace_510563 : CollatzResearch.WordTrace tailWord_510563 prefixEnd_510563 155356576830572535475241 := by
  unfold tailWord_510563
  simp only [CollatzResearch.WordTrace]
  refine ⟨18621762449324923063384343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12414508299549948708922895 18621762449324923063384343)
  ·
    refine ⟨27932643673987384595076515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18621762449324923063384343 27932643673987384595076515)
    ·
      refine ⟨41898965510981076892614773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27932643673987384595076515 41898965510981076892614773)
      ·
        refine ⟨3928028016654475958682635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41898965510981076892614773 3928028016654475958682635)
        ·
          refine ⟨5892042024981713938023953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3928028016654475958682635 5892042024981713938023953)
          ·
            refine ⟨4419031518736285453517965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5892042024981713938023953 4419031518736285453517965)
            ·
              refine ⟨1657136819526107045069237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4419031518736285453517965 1657136819526107045069237)
              ·
                refine ⟨155356576830572535475241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1657136819526107045069237 155356576830572535475241)
                ·
                  rfl

theorem cell19_510563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 5].length) (baseStart_510563 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_510563 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_510563 prefixEnd_510563 := by exact prefixLift 510563
  have htrace : WordTrace (prefixWord ++ tailWord_510563) baseStart_510563 baseEnd_510563 := by
    simpa [prefixWord, tailWord_510563, baseEnd_510563] using wordTrace_append hprefix tailTrace_510563
  have hstable : (prefixWord ++ tailWord_510563).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510563).length < 2 ^ (prefixWord ++ tailWord_510563).sum := by decide
  have hdescent : baseEnd_510563 < baseStart_510563 := by decide
  rcases family_descends (prefixWord ++ tailWord_510563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510578 : List Nat := [3, 2, 1, 2, 5, 1, 5]
def baseStart_510578 : Nat := 118140960795 + 510578 * 2 ^ 59
def prefixEnd_510578 : Nat := 4983230072969 + 3 ^ 40 * 510578 * 2
def baseEnd_510578 : Nat := 51787047034352315047289

theorem tailTrace_510578 : CollatzResearch.WordTrace tailWord_510578 prefixEnd_510578 51787047034352315047289 := by
  unfold tailWord_510578
  simp only [CollatzResearch.WordTrace]
  refine ⟨4655577386067645156295097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12414873029513720416786925 4655577386067645156295097)
  ·
    refine ⟨3491683039550733867221323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4655577386067645156295097 3491683039550733867221323)
    ·
      refine ⟨5237524559326100800831985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3491683039550733867221323 5237524559326100800831985)
      ·
        refine ⟨3928143419494575600623989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5237524559326100800831985 3928143419494575600623989)
        ·
          refine ⟨368263445577616462558499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3928143419494575600623989 368263445577616462558499)
          ·
            refine ⟨552395168366424693837749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 368263445577616462558499 552395168366424693837749)
            ·
              refine ⟨51787047034352315047289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 552395168366424693837749 51787047034352315047289)
              ·
                rfl

theorem cell19_510578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 5].length) (baseStart_510578 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_510578 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_510578 prefixEnd_510578 := by exact prefixLift 510578
  have htrace : WordTrace (prefixWord ++ tailWord_510578) baseStart_510578 baseEnd_510578 := by
    simpa [prefixWord, tailWord_510578, baseEnd_510578] using wordTrace_append hprefix tailTrace_510578
  have hstable : (prefixWord ++ tailWord_510578).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510578).length < 2 ^ (prefixWord ++ tailWord_510578).sum := by decide
  have hdescent : baseEnd_510578 < baseStart_510578 := by decide
  rcases family_descends (prefixWord ++ tailWord_510578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510656 : List Nat := [2, 1, 1, 2, 4, 4, 1, 4]
def baseStart_510656 : Nat := 118140960795 + 510656 * 2 ^ 59
def prefixEnd_510656 : Nat := 4983230072969 + 3 ^ 40 * 510656 * 2
def baseEnd_510656 : Nat := 155384875319975875408321

theorem tailTrace_510656 : CollatzResearch.WordTrace tailWord_510656 prefixEnd_510656 155384875319975875408321 := by
  unfold tailWord_510656
  simp only [CollatzResearch.WordTrace]
  refine ⟨9312577218993999973259911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12416769625325333297679881 9312577218993999973259911)
  ·
    refine ⟨13968865828490999959889867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9312577218993999973259911 13968865828490999959889867)
    ·
      refine ⟨20953298742736499939834801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13968865828490999959889867 20953298742736499939834801)
      ·
        refine ⟨15714974057052374954876101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20953298742736499939834801 15714974057052374954876101)
        ·
          refine ⟨2946557635697320304039269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15714974057052374954876101 2946557635697320304039269)
          ·
            refine ⟨552479556693247557007363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2946557635697320304039269 552479556693247557007363)
            ·
              refine ⟨828719335039871335511045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 552479556693247557007363 828719335039871335511045)
              ·
                refine ⟨155384875319975875408321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 828719335039871335511045 155384875319975875408321)
                ·
                  rfl

theorem cell19_510656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 1, 4].length) (baseStart_510656 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_510656 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_510656 prefixEnd_510656 := by exact prefixLift 510656
  have htrace : WordTrace (prefixWord ++ tailWord_510656) baseStart_510656 baseEnd_510656 := by
    simpa [prefixWord, tailWord_510656, baseEnd_510656] using wordTrace_append hprefix tailTrace_510656
  have hstable : (prefixWord ++ tailWord_510656).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510656).length < 2 ^ (prefixWord ++ tailWord_510656).sum := by decide
  have hdescent : baseEnd_510656 < baseStart_510656 := by decide
  rcases family_descends (prefixWord ++ tailWord_510656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510749 : List Nat := [1, 4, 2, 4, 1, 2, 5]
def baseStart_510749 : Nat := 118140960795 + 510749 * 2 ^ 59
def prefixEnd_510749 : Nat := 4983230072969 + 3 ^ 40 * 510749 * 2
def baseEnd_510749 : Nat := 51804391269793071780467

theorem tailTrace_510749 : CollatzResearch.WordTrace tailWord_510749 prefixEnd_510749 51804391269793071780467 := by
  unfold tailWord_510749
  simp only [CollatzResearch.WordTrace]
  refine ⟨18628546426651076829655301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12419030951100717886436867 18628546426651076829655301)
  ·
    refine ⟨3492852454997076905560369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18628546426651076829655301 3492852454997076905560369)
    ·
      refine ⟨2619639341247807679170277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3492852454997076905560369 2619639341247807679170277)
      ·
        refine ⟨491182376483963939844427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2619639341247807679170277 491182376483963939844427)
        ·
          refine ⟨736773564725945909766641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 491182376483963939844427 736773564725945909766641)
          ·
            refine ⟨552580173544459432324981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 736773564725945909766641 552580173544459432324981)
            ·
              refine ⟨51804391269793071780467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 552580173544459432324981 51804391269793071780467)
              ·
                rfl

theorem cell19_510749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 5].length) (baseStart_510749 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_510749 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_510749 prefixEnd_510749 := by exact prefixLift 510749
  have htrace : WordTrace (prefixWord ++ tailWord_510749) baseStart_510749 baseEnd_510749 := by
    simpa [prefixWord, tailWord_510749, baseEnd_510749] using wordTrace_append hprefix tailTrace_510749
  have hstable : (prefixWord ++ tailWord_510749).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510749).length < 2 ^ (prefixWord ++ tailWord_510749).sum := by decide
  have hdescent : baseEnd_510749 < baseStart_510749 := by decide
  rcases family_descends (prefixWord ++ tailWord_510749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510905 : List Nat := [1, 2, 1, 4, 2, 3, 1, 5]
def baseStart_510905 : Nat := 118140960795 + 510905 * 2 ^ 59
def prefixEnd_510905 : Nat := 4983230072969 + 3 ^ 40 * 510905 * 2
def baseEnd_510905 : Nat := 155460642243217075874309

theorem tailTrace_510905 : CollatzResearch.WordTrace tailWord_510905 prefixEnd_510905 155460642243217075874309 := by
  unfold tailWord_510905
  simp only [CollatzResearch.WordTrace]
  refine ⟨18634236214085915472334169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12422824142723943648222779 18634236214085915472334169)
  ·
    refine ⟨13975677160564436604250627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18634236214085915472334169 13975677160564436604250627)
    ·
      refine ⟨20963515740846654906375941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13975677160564436604250627 20963515740846654906375941)
      ·
        refine ⟨3930659201408747794945489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20963515740846654906375941 3930659201408747794945489)
        ·
          refine ⟨2947994401056560846209117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3930659201408747794945489 2947994401056560846209117)
          ·
            refine ⟨1105497900396210317328419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2947994401056560846209117 1105497900396210317328419)
            ·
              refine ⟨1658246850594315475992629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1105497900396210317328419 1658246850594315475992629)
              ·
                refine ⟨155460642243217075874309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1658246850594315475992629 155460642243217075874309)
                ·
                  rfl

theorem cell19_510905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 5].length) (baseStart_510905 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_510905 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_510905 prefixEnd_510905 := by exact prefixLift 510905
  have htrace : WordTrace (prefixWord ++ tailWord_510905) baseStart_510905 baseEnd_510905 := by
    simpa [prefixWord, tailWord_510905, baseEnd_510905] using wordTrace_append hprefix tailTrace_510905
  have hstable : (prefixWord ++ tailWord_510905).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510905).length < 2 ^ (prefixWord ++ tailWord_510905).sum := by decide
  have hdescent : baseEnd_510905 < baseStart_510905 := by decide
  rcases family_descends (prefixWord ++ tailWord_510905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510941 : List Nat := [1, 4, 3, 1, 2, 2, 2, 4]
def baseStart_510941 : Nat := 118140960795 + 510941 * 2 ^ 59
def prefixEnd_510941 : Nat := 4983230072969 + 3 ^ 40 * 510941 * 2
def baseEnd_510941 : Nat := 155471596497179659074211

theorem tailTrace_510941 : CollatzResearch.WordTrace tailWord_510941 prefixEnd_510941 155471596497179659074211 := by
  unfold tailWord_510941
  simp only [CollatzResearch.WordTrace]
  refine ⟨18635549241955493620644677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12423699494636995747096451 18635549241955493620644677)
  ·
    refine ⟨3494165482866655053870877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18635549241955493620644677 3494165482866655053870877)
    ·
      refine ⟨1310312056074995645201579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3494165482866655053870877 1310312056074995645201579)
      ·
        refine ⟨1965468084112493467802369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1310312056074995645201579 1965468084112493467802369)
        ·
          refine ⟨1474101063084370100851777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1965468084112493467802369 1474101063084370100851777)
          ·
            refine ⟨1105575797313277575638833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1474101063084370100851777 1105575797313277575638833)
            ·
              refine ⟨829181847984958181729125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1105575797313277575638833 829181847984958181729125)
              ·
                refine ⟨155471596497179659074211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 829181847984958181729125 155471596497179659074211)
                ·
                  rfl

theorem cell19_510941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2, 4].length) (baseStart_510941 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_510941 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_510941 prefixEnd_510941 := by exact prefixLift 510941
  have htrace : WordTrace (prefixWord ++ tailWord_510941) baseStart_510941 baseEnd_510941 := by
    simpa [prefixWord, tailWord_510941, baseEnd_510941] using wordTrace_append hprefix tailTrace_510941
  have hstable : (prefixWord ++ tailWord_510941).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510941).length < 2 ^ (prefixWord ++ tailWord_510941).sum := by decide
  have hdescent : baseEnd_510941 < baseStart_510941 := by decide
  rcases family_descends (prefixWord ++ tailWord_510941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511000 : List Nat := [2, 1, 2, 3, 2, 2, 3, 4]
def baseStart_511000 : Nat := 118140960795 + 511000 * 2 ^ 59
def prefixEnd_511000 : Nat := 4983230072969 + 3 ^ 40 * 511000 * 2
def baseEnd_511000 : Nat := 155489549302285003762939

theorem tailTrace_511000 : CollatzResearch.WordTrace tailWord_511000 prefixEnd_511000 155489549302285003762939 := by
  unfold tailWord_511000
  simp only [CollatzResearch.WordTrace]
  refine ⟨9318850574370873348521227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12425134099161164464694969 9318850574370873348521227)
  ·
    refine ⟨13978275861556310022781841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9318850574370873348521227 13978275861556310022781841)
    ·
      refine ⟨10483706896167232517086381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13978275861556310022781841 10483706896167232517086381)
      ·
        refine ⟨3931390086062712193907393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10483706896167232517086381 3931390086062712193907393)
        ·
          refine ⟨2948542564547034145430545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3931390086062712193907393 2948542564547034145430545)
          ·
            refine ⟨2211406923410275609072909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2948542564547034145430545 2211406923410275609072909)
            ·
              refine ⟨829277596278853353402341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2211406923410275609072909 829277596278853353402341)
              ·
                refine ⟨155489549302285003762939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 829277596278853353402341 155489549302285003762939)
                ·
                  rfl

theorem cell19_511000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3, 4].length) (baseStart_511000 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_511000 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_511000 prefixEnd_511000 := by exact prefixLift 511000
  have htrace : WordTrace (prefixWord ++ tailWord_511000) baseStart_511000 baseEnd_511000 := by
    simpa [prefixWord, tailWord_511000, baseEnd_511000] using wordTrace_append hprefix tailTrace_511000
  have hstable : (prefixWord ++ tailWord_511000).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511000).length < 2 ^ (prefixWord ++ tailWord_511000).sum := by decide
  have hdescent : baseEnd_511000 < baseStart_511000 := by decide
  rcases family_descends (prefixWord ++ tailWord_511000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511015 : List Nat := [1, 1, 7, 1, 1, 2, 3, 3]
def baseStart_511015 : Nat := 118140960795 + 511015 * 2 ^ 59
def prefixEnd_511015 : Nat := 4983230072969 + 3 ^ 40 * 511015 * 2
def baseEnd_511015 : Nat := 155494113574769413429565

theorem tailTrace_511015 : CollatzResearch.WordTrace tailWord_511015 prefixEnd_511015 155494113574769413429565 := by
  unfold tailWord_511015
  simp only [CollatzResearch.WordTrace]
  refine ⟨18638248243687404258838499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12425498829124936172558999 18638248243687404258838499)
  ·
    refine ⟨27957372365531106388257749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18638248243687404258838499 27957372365531106388257749)
    ·
      refine ⟨655250914817135305974791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 27957372365531106388257749 655250914817135305974791)
      ·
        refine ⟨982876372225702958962187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 655250914817135305974791 982876372225702958962187)
        ·
          refine ⟨1474314558338554438443281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 982876372225702958962187 1474314558338554438443281)
          ·
            refine ⟨1105735918753915828832461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1474314558338554438443281 1105735918753915828832461)
            ·
              refine ⟨414650969532718435812173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1105735918753915828832461 414650969532718435812173)
              ·
                refine ⟨155494113574769413429565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 414650969532718435812173 155494113574769413429565)
                ·
                  rfl

theorem cell19_511015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 3, 3].length) (baseStart_511015 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_511015 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_511015 prefixEnd_511015 := by exact prefixLift 511015
  have htrace : WordTrace (prefixWord ++ tailWord_511015) baseStart_511015 baseEnd_511015 := by
    simpa [prefixWord, tailWord_511015, baseEnd_511015] using wordTrace_append hprefix tailTrace_511015
  have hstable : (prefixWord ++ tailWord_511015).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511015).length < 2 ^ (prefixWord ++ tailWord_511015).sum := by decide
  have hdescent : baseEnd_511015 < baseStart_511015 := by decide
  rcases family_descends (prefixWord ++ tailWord_511015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511019 : List Nat := [1, 1, 1, 1, 2, 1, 9, 3]
def baseStart_511019 : Nat := 118140960795 + 511019 * 2 ^ 59
def prefixEnd_511019 : Nat := 4983230072969 + 3 ^ 40 * 511019 * 2
def baseEnd_511019 : Nat := 155495330714098589340665

theorem tailTrace_511019 : CollatzResearch.WordTrace tailWord_511019 prefixEnd_511019 155495330714098589340665 := by
  unfold tailWord_511019
  simp only [CollatzResearch.WordTrace]
  refine ⟨18638394135672912941984111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12425596090448608627989407 18638394135672912941984111)
  ·
    refine ⟨27957591203509369412976167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18638394135672912941984111 27957591203509369412976167)
    ·
      refine ⟨41936386805264054119464251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27957591203509369412976167 41936386805264054119464251)
      ·
        refine ⟨62904580207896081179196377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41936386805264054119464251 62904580207896081179196377)
        ·
          refine ⟨47178435155922060884397283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62904580207896081179196377 47178435155922060884397283)
          ·
            refine ⟨70767652733883091326595925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47178435155922060884397283 70767652733883091326595925)
            ·
              refine ⟨414654215237596238241773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 70767652733883091326595925 414654215237596238241773)
              ·
                refine ⟨155495330714098589340665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 414654215237596238241773 155495330714098589340665)
                ·
                  rfl

theorem cell19_511019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 9, 3].length) (baseStart_511019 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_511019 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_511019 prefixEnd_511019 := by exact prefixLift 511019
  have htrace : WordTrace (prefixWord ++ tailWord_511019) baseStart_511019 baseEnd_511019 := by
    simpa [prefixWord, tailWord_511019, baseEnd_511019] using wordTrace_append hprefix tailTrace_511019
  have hstable : (prefixWord ++ tailWord_511019).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511019).length < 2 ^ (prefixWord ++ tailWord_511019).sum := by decide
  have hdescent : baseEnd_511019 < baseStart_511019 := by decide
  rcases family_descends (prefixWord ++ tailWord_511019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511040 : List Nat := [2, 1, 1, 2, 2, 3, 8]
def baseStart_511040 : Nat := 118140960795 + 511040 * 2 ^ 59
def prefixEnd_511040 : Nat := 4983230072969 + 3 ^ 40 * 511040 * 2
def baseEnd_511040 : Nat := 51833906898525587624647

theorem tailTrace_511040 : CollatzResearch.WordTrace tailWord_511040 prefixEnd_511040 51833906898525587624647 := by
  unfold tailWord_511040
  simp only [CollatzResearch.WordTrace]
  refine ⟨9319580034298416764249287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12426106712397889018999049 9319580034298416764249287)
  ·
    refine ⟨13979370051447625146373931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9319580034298416764249287 13979370051447625146373931)
    ·
      refine ⟨20969055077171437719560897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13979370051447625146373931 20969055077171437719560897)
      ·
        refine ⟨15726791307878578289670673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20969055077171437719560897 15726791307878578289670673)
        ·
          refine ⟨11795093480908933717253005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15726791307878578289670673 11795093480908933717253005)
          ·
            refine ⟨4423160055340850143969877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11795093480908933717253005 4423160055340850143969877)
            ·
              refine ⟨51833906898525587624647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4423160055340850143969877 51833906898525587624647)
              ·
                rfl

theorem cell19_511040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 8].length) (baseStart_511040 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_511040 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_511040 prefixEnd_511040 := by exact prefixLift 511040
  have htrace : WordTrace (prefixWord ++ tailWord_511040) baseStart_511040 baseEnd_511040 := by
    simpa [prefixWord, tailWord_511040, baseEnd_511040] using wordTrace_append hprefix tailTrace_511040
  have hstable : (prefixWord ++ tailWord_511040).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511040).length < 2 ^ (prefixWord ++ tailWord_511040).sum := by decide
  have hdescent : baseEnd_511040 < baseStart_511040 := by decide
  rcases family_descends (prefixWord ++ tailWord_511040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511070 : List Nat := [4, 4, 1, 1, 1, 1, 4, 3]
def baseStart_511070 : Nat := 118140960795 + 511070 * 2 ^ 59
def prefixEnd_511070 : Nat := 4983230072969 + 3 ^ 40 * 511070 * 2
def baseEnd_511070 : Nat := 155510849240545582207193

theorem tailTrace_511070 : CollatzResearch.WordTrace tailWord_511070 prefixEnd_511070 155510849240545582207193 := by
  unfold tailWord_511070
  simp only [CollatzResearch.WordTrace]
  refine ⟨2330031782311018581511333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12426836172325432434727109 2330031782311018581511333)
  ·
    refine ⟨436880959183315984033375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2330031782311018581511333 436880959183315984033375)
    ·
      refine ⟨655321438774973976050063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 436880959183315984033375 655321438774973976050063)
      ·
        refine ⟨982982158162460964075095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 655321438774973976050063 982982158162460964075095)
        ·
          refine ⟨1474473237243691446112643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 982982158162460964075095 1474473237243691446112643)
          ·
            refine ⟨2211709855865537169168965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1474473237243691446112643 2211709855865537169168965)
            ·
              refine ⟨414695597974788219219181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2211709855865537169168965 414695597974788219219181)
              ·
                refine ⟨155510849240545582207193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 414695597974788219219181 155510849240545582207193)
                ·
                  rfl

theorem cell19_511070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 4, 3].length) (baseStart_511070 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_511070 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_511070 prefixEnd_511070 := by exact prefixLift 511070
  have htrace : WordTrace (prefixWord ++ tailWord_511070) baseStart_511070 baseEnd_511070 := by
    simpa [prefixWord, tailWord_511070, baseEnd_511070] using wordTrace_append hprefix tailTrace_511070
  have hstable : (prefixWord ++ tailWord_511070).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511070).length < 2 ^ (prefixWord ++ tailWord_511070).sum := by decide
  have hdescent : baseEnd_511070 < baseStart_511070 := by decide
  rcases family_descends (prefixWord ++ tailWord_511070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511074 : List Nat := [3, 3, 2, 2, 1, 2, 1, 5]
def baseStart_511074 : Nat := 118140960795 + 511074 * 2 ^ 59
def prefixEnd_511074 : Nat := 4983230072969 + 3 ^ 40 * 511074 * 2
def baseEnd_511074 : Nat := 155512066379874758118293

theorem tailTrace_511074 : CollatzResearch.WordTrace tailWord_511074 prefixEnd_511074 155512066379874758118293 := by
  unfold tailWord_511074
  simp only [CollatzResearch.WordTrace]
  refine ⟨4660100037618414333809069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12426933433649104890157517 4660100037618414333809069)
  ·
    refine ⟨1747537514106905375178401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4660100037618414333809069 1747537514106905375178401)
    ·
      refine ⟨1310653135580179031383801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1747537514106905375178401 1310653135580179031383801)
      ·
        refine ⟨982989851685134273537851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1310653135580179031383801 982989851685134273537851)
        ·
          refine ⟨1474484777527701410306777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 982989851685134273537851 1474484777527701410306777)
          ·
            refine ⟨1105863583145776057730083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1474484777527701410306777 1105863583145776057730083)
            ·
              refine ⟨1658795374718664086595125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1105863583145776057730083 1658795374718664086595125)
              ·
                refine ⟨155512066379874758118293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1658795374718664086595125 155512066379874758118293)
                ·
                  rfl

theorem cell19_511074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 5].length) (baseStart_511074 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_511074 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_511074 prefixEnd_511074 := by exact prefixLift 511074
  have htrace : WordTrace (prefixWord ++ tailWord_511074) baseStart_511074 baseEnd_511074 := by
    simpa [prefixWord, tailWord_511074, baseEnd_511074] using wordTrace_append hprefix tailTrace_511074
  have hstable : (prefixWord ++ tailWord_511074).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511074).length < 2 ^ (prefixWord ++ tailWord_511074).sum := by decide
  have hdescent : baseEnd_511074 < baseStart_511074 := by decide
  rcases family_descends (prefixWord ++ tailWord_511074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511112 : List Nat := [2, 1, 3, 4, 2, 1, 2, 4]
def baseStart_511112 : Nat := 118140960795 + 511112 * 2 ^ 59
def prefixEnd_511112 : Nat := 4983230072969 + 3 ^ 40 * 511112 * 2
def baseEnd_511112 : Nat := 155523629203501929273745

theorem tailTrace_511112 : CollatzResearch.WordTrace tailWord_511112 prefixEnd_511112 155523629203501929273745 := by
  unfold tailWord_511112
  simp only [CollatzResearch.WordTrace]
  refine ⟨9320893062167994912559795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12427857416223993216746393 9320893062167994912559795)
  ·
    refine ⟨13981339593251992368839693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9320893062167994912559795 13981339593251992368839693)
    ·
      refine ⟨5243002347469497138314885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13981339593251992368839693 5243002347469497138314885)
      ·
        refine ⟨983062940150530713434041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5243002347469497138314885 983062940150530713434041)
        ·
          refine ⟨737297205112898035075531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 983062940150530713434041 737297205112898035075531)
          ·
            refine ⟨1105945807669347052613297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 737297205112898035075531 1105945807669347052613297)
            ·
              refine ⟨829459355752010289459973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1105945807669347052613297 829459355752010289459973)
              ·
                refine ⟨155523629203501929273745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 829459355752010289459973 155523629203501929273745)
                ·
                  rfl

theorem cell19_511112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 2, 4].length) (baseStart_511112 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_511112 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_511112 prefixEnd_511112 := by exact prefixLift 511112
  have htrace : WordTrace (prefixWord ++ tailWord_511112) baseStart_511112 baseEnd_511112 := by
    simpa [prefixWord, tailWord_511112, baseEnd_511112] using wordTrace_append hprefix tailTrace_511112
  have hstable : (prefixWord ++ tailWord_511112).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511112).length < 2 ^ (prefixWord ++ tailWord_511112).sum := by decide
  have hdescent : baseEnd_511112 < baseStart_511112 := by decide
  rcases family_descends (prefixWord ++ tailWord_511112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511114 : List Nat := [3, 1, 2, 3, 1, 1, 4, 4]
def baseStart_511114 : Nat := 118140960795 + 511114 * 2 ^ 59
def prefixEnd_511114 : Nat := 4983230072969 + 3 ^ 40 * 511114 * 2
def baseEnd_511114 : Nat := 155524237773166517229295

theorem tailTrace_511114 : CollatzResearch.WordTrace tailWord_511114 prefixEnd_511114 155524237773166517229295 := by
  unfold tailWord_511114
  simp only [CollatzResearch.WordTrace]
  refine ⟨4660464767582186041673099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12427906046885829444461597 4660464767582186041673099)
  ·
    refine ⟨6990697151373279062509649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4660464767582186041673099 6990697151373279062509649)
    ·
      refine ⟨5243022863529959296882237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6990697151373279062509649 5243022863529959296882237)
      ·
        refine ⟨1966133573823734736330839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5243022863529959296882237 1966133573823734736330839)
        ·
          refine ⟨2949200360735602104496259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1966133573823734736330839 2949200360735602104496259)
          ·
            refine ⟨4423800541103403156744389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2949200360735602104496259 4423800541103403156744389)
            ·
              refine ⟨829462601456888091889573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4423800541103403156744389 829462601456888091889573)
              ·
                refine ⟨155524237773166517229295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 829462601456888091889573 155524237773166517229295)
                ·
                  rfl

theorem cell19_511114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4, 4].length) (baseStart_511114 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_511114 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_511114 prefixEnd_511114 := by exact prefixLift 511114
  have htrace : WordTrace (prefixWord ++ tailWord_511114) baseStart_511114 baseEnd_511114 := by
    simpa [prefixWord, tailWord_511114, baseEnd_511114] using wordTrace_append hprefix tailTrace_511114
  have hstable : (prefixWord ++ tailWord_511114).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511114).length < 2 ^ (prefixWord ++ tailWord_511114).sum := by decide
  have hdescent : baseEnd_511114 < baseStart_511114 := by decide
  rcases family_descends (prefixWord ++ tailWord_511114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511154 : List Nat := [3, 2, 1, 1, 1, 11]
def baseStart_511154 : Nat := 118140960795 + 511154 * 2 ^ 59
def prefixEnd_511154 : Nat := 4983230072969 + 3 ^ 40 * 511154 * 2
def baseEnd_511154 : Nat := 17281823240717586260033

theorem tailTrace_511154 : CollatzResearch.WordTrace tailWord_511154 prefixEnd_511154 17281823240717586260033 := by
  unfold tailWord_511154
  simp only [CollatzResearch.WordTrace]
  refine ⟨4660829497545957749537129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12428878660122553998765677 4660829497545957749537129)
  ·
    refine ⟨3495622123159468312152847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4660829497545957749537129 3495622123159468312152847)
    ·
      refine ⟨5243433184739202468229271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3495622123159468312152847 5243433184739202468229271)
      ·
        refine ⟨7865149777108803702343907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5243433184739202468229271 7865149777108803702343907)
        ·
          refine ⟨11797724665663205553515861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7865149777108803702343907 11797724665663205553515861)
          ·
            refine ⟨17281823240717586260033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 11797724665663205553515861 17281823240717586260033)
            ·
              rfl

theorem cell19_511154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 11].length) (baseStart_511154 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_511154 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_511154 prefixEnd_511154 := by exact prefixLift 511154
  have htrace : WordTrace (prefixWord ++ tailWord_511154) baseStart_511154 baseEnd_511154 := by
    simpa [prefixWord, tailWord_511154, baseEnd_511154] using wordTrace_append hprefix tailTrace_511154
  have hstable : (prefixWord ++ tailWord_511154).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511154).length < 2 ^ (prefixWord ++ tailWord_511154).sum := by decide
  have hdescent : baseEnd_511154 < baseStart_511154 := by decide
  rcases family_descends (prefixWord ++ tailWord_511154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511169 : List Nat := [1, 2, 6, 1, 1, 1, 3, 4]
def baseStart_511169 : Nat := 118140960795 + 511169 * 2 ^ 59
def prefixEnd_511169 : Nat := 4983230072969 + 3 ^ 40 * 511169 * 2
def baseEnd_511169 : Nat := 155540973438942686006923

theorem tailTrace_511169 : CollatzResearch.WordTrace tailWord_511169 prefixEnd_511169 155540973438942686006923 := by
  unfold tailWord_511169
  simp only [CollatzResearch.WordTrace]
  refine ⟨18643865085129488559944561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12429243390086325706629707 18643865085129488559944561)
  ·
    refine ⟨13982898813847116419958421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18643865085129488559944561 13982898813847116419958421)
    ·
      refine ⟨655448381899083582185551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 13982898813847116419958421 655448381899083582185551)
      ·
        refine ⟨983172572848625373278327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 655448381899083582185551 983172572848625373278327)
        ·
          refine ⟨1474758859272938059917491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 983172572848625373278327 1474758859272938059917491)
          ·
            refine ⟨2212138288909407089876237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1474758859272938059917491 2212138288909407089876237)
            ·
              refine ⟨829551858341027658703589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2212138288909407089876237 829551858341027658703589)
              ·
                refine ⟨155540973438942686006923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 829551858341027658703589 155540973438942686006923)
                ·
                  rfl

theorem cell19_511169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 3, 4].length) (baseStart_511169 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_511169 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_511169 prefixEnd_511169 := by exact prefixLift 511169
  have htrace : WordTrace (prefixWord ++ tailWord_511169) baseStart_511169 baseEnd_511169 := by
    simpa [prefixWord, tailWord_511169, baseEnd_511169] using wordTrace_append hprefix tailTrace_511169
  have hstable : (prefixWord ++ tailWord_511169).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511169).length < 2 ^ (prefixWord ++ tailWord_511169).sum := by decide
  have hdescent : baseEnd_511169 < baseStart_511169 := by decide
  rcases family_descends (prefixWord ++ tailWord_511169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511211 : List Nat := [1, 1, 1, 1, 2, 7, 6]
def baseStart_511211 : Nat := 118140960795 + 511211 * 2 ^ 59
def prefixEnd_511211 : Nat := 4983230072969 + 3 ^ 40 * 511211 * 2
def baseEnd_511211 : Nat := 51851251133966344357825

theorem tailTrace_511211 : CollatzResearch.WordTrace tailWord_511211 prefixEnd_511211 51851251133966344357825 := by
  unfold tailWord_511211
  simp only [CollatzResearch.WordTrace]
  refine ⟨18645396950977329732973487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12430264633984886488648991 18645396950977329732973487)
  ·
    refine ⟨27968095426465994599460231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18645396950977329732973487 27968095426465994599460231)
    ·
      refine ⟨41952143139698991899190347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27968095426465994599460231 41952143139698991899190347)
      ·
        refine ⟨62928214709548487848785521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41952143139698991899190347 62928214709548487848785521)
        ·
          refine ⟨47196161032161365886589141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62928214709548487848785521 47196161032161365886589141)
          ·
            refine ⟨1106160024191282012966933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 47196161032161365886589141 1106160024191282012966933)
            ·
              refine ⟨51851251133966344357825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1106160024191282012966933 51851251133966344357825)
              ·
                rfl

theorem cell19_511211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 6].length) (baseStart_511211 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_511211 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_511211 prefixEnd_511211 := by exact prefixLift 511211
  have htrace : WordTrace (prefixWord ++ tailWord_511211) baseStart_511211 baseEnd_511211 := by
    simpa [prefixWord, tailWord_511211, baseEnd_511211] using wordTrace_append hprefix tailTrace_511211
  have hstable : (prefixWord ++ tailWord_511211).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511211).length < 2 ^ (prefixWord ++ tailWord_511211).sum := by decide
  have hdescent : baseEnd_511211 < baseStart_511211 := by decide
  rcases family_descends (prefixWord ++ tailWord_511211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511249 : List Nat := [1, 2, 2, 1, 1, 4, 3, 5]
def baseStart_511249 : Nat := 118140960795 + 511249 * 2 ^ 59
def prefixEnd_511249 : Nat := 4983230072969 + 3 ^ 40 * 511249 * 2
def baseEnd_511249 : Nat := 155565316225526204228927

theorem tailTrace_511249 : CollatzResearch.WordTrace tailWord_511249 prefixEnd_511249 155565316225526204228927 := by
  unfold tailWord_511249
  simp only [CollatzResearch.WordTrace]
  refine ⟨18646782924839662222856801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12431188616559774815237867 18646782924839662222856801)
  ·
    refine ⟨13985087193629746667142601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18646782924839662222856801 13985087193629746667142601)
    ·
      refine ⟨10488815395222310000356951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13985087193629746667142601 10488815395222310000356951)
      ·
        refine ⟨15733223092833465000535427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10488815395222310000356951 15733223092833465000535427)
        ·
          refine ⟨23599834639250197500803141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15733223092833465000535427 23599834639250197500803141)
          ·
            refine ⟨4424968994859412031400589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23599834639250197500803141 4424968994859412031400589)
            ·
              refine ⟨1659363373072279511775221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4424968994859412031400589 1659363373072279511775221)
              ·
                refine ⟨155565316225526204228927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1659363373072279511775221 155565316225526204228927)
                ·
                  rfl

theorem cell19_511249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 5].length) (baseStart_511249 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_511249 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_511249 prefixEnd_511249 := by exact prefixLift 511249
  have htrace : WordTrace (prefixWord ++ tailWord_511249) baseStart_511249 baseEnd_511249 := by
    simpa [prefixWord, tailWord_511249, baseEnd_511249] using wordTrace_append hprefix tailTrace_511249
  have hstable : (prefixWord ++ tailWord_511249).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511249).length < 2 ^ (prefixWord ++ tailWord_511249).sum := by decide
  have hdescent : baseEnd_511249 < baseStart_511249 := by decide
  rcases family_descends (prefixWord ++ tailWord_511249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511262 : List Nat := [4, 3, 2, 1, 2, 2, 5]
def baseStart_511262 : Nat := 118140960795 + 511262 * 2 ^ 59
def prefixEnd_511262 : Nat := 4983230072969 + 3 ^ 40 * 511262 * 2
def baseEnd_511262 : Nat := 51856423976115341980001

theorem tailTrace_511262 : CollatzResearch.WordTrace tailWord_511262 prefixEnd_511262 51856423976115341980001 := by
  unfold tailWord_511262
  simp only [CollatzResearch.WordTrace]
  refine ⟨2330907134224070680385005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12431504715861710295386693 2330907134224070680385005)
  ·
    refine ⟨874090175334026505144377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2330907134224070680385005 874090175334026505144377)
    ·
      refine ⟨655567631500519878858283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 874090175334026505144377 655567631500519878858283)
      ·
        refine ⟨983351447250779818287425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 655567631500519878858283 983351447250779818287425)
        ·
          refine ⟨737513585438084863715569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 983351447250779818287425 737513585438084863715569)
          ·
            refine ⟨553135189078563647786677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 737513585438084863715569 553135189078563647786677)
            ·
              refine ⟨51856423976115341980001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 553135189078563647786677 51856423976115341980001)
              ·
                rfl

theorem cell19_511262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 5].length) (baseStart_511262 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_511262 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_511262 prefixEnd_511262 := by exact prefixLift 511262
  have htrace : WordTrace (prefixWord ++ tailWord_511262) baseStart_511262 baseEnd_511262 := by
    simpa [prefixWord, tailWord_511262, baseEnd_511262] using wordTrace_append hprefix tailTrace_511262
  have hstable : (prefixWord ++ tailWord_511262).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511262).length < 2 ^ (prefixWord ++ tailWord_511262).sum := by decide
  have hdescent : baseEnd_511262 < baseStart_511262 := by decide
  rcases family_descends (prefixWord ++ tailWord_511262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511264 : List Nat := [2, 1, 1, 5, 4, 1, 5]
def baseStart_511264 : Nat := 118140960795 + 511264 * 2 ^ 59
def prefixEnd_511264 : Nat := 4983230072969 + 3 ^ 40 * 511264 * 2
def baseEnd_511264 : Nat := 51856626832670204631851

theorem tailTrace_511264 : CollatzResearch.WordTrace tailWord_511264 prefixEnd_511264 51856626832670204631851 := by
  unfold tailWord_511264
  simp only [CollatzResearch.WordTrace]
  refine ⟨9323665009892659892326423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12431553346523546523101897 9323665009892659892326423)
  ·
    refine ⟨13985497514838989838489635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9323665009892659892326423 13985497514838989838489635)
    ·
      refine ⟨20978246272258484757734453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13985497514838989838489635 20978246272258484757734453)
      ·
        refine ⟨1966710588024232946037605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20978246272258484757734453 1966710588024232946037605)
        ·
          refine ⟨368758235254543677382051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1966710588024232946037605 368758235254543677382051)
          ·
            refine ⟨553137352881815516073077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 368758235254543677382051 553137352881815516073077)
            ·
              refine ⟨51856626832670204631851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 553137352881815516073077 51856626832670204631851)
              ·
                rfl

theorem cell19_511264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 5].length) (baseStart_511264 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_511264 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_511264 prefixEnd_511264 := by exact prefixLift 511264
  have htrace : WordTrace (prefixWord ++ tailWord_511264) baseStart_511264 baseEnd_511264 := by
    simpa [prefixWord, tailWord_511264, baseEnd_511264] using wordTrace_append hprefix tailTrace_511264
  have hstable : (prefixWord ++ tailWord_511264).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511264).length < 2 ^ (prefixWord ++ tailWord_511264).sum := by decide
  have hdescent : baseEnd_511264 < baseStart_511264 := by decide
  rcases family_descends (prefixWord ++ tailWord_511264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511285 : List Nat := [1, 3, 3, 1, 2, 3, 2, 4]
def baseStart_511285 : Nat := 118140960795 + 511285 * 2 ^ 59
def prefixEnd_511285 : Nat := 4983230072969 + 3 ^ 40 * 511285 * 2
def baseEnd_511285 : Nat := 155576270479488787428829

theorem tailTrace_511285 : CollatzResearch.WordTrace tailWord_511285 prefixEnd_511285 155576270479488787428829 := by
  unfold tailWord_511285
  simp only [CollatzResearch.WordTrace]
  refine ⟨18648095952709240371167309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12432063968472826914111539 18648095952709240371167309)
  ·
    refine ⟨6993035982265965139187741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18648095952709240371167309 6993035982265965139187741)
    ·
      refine ⟨2622388493349736927195403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6993035982265965139187741 2622388493349736927195403)
      ·
        refine ⟨3933582740024605390793105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2622388493349736927195403 3933582740024605390793105)
        ·
          refine ⟨2950187055018454043094829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3933582740024605390793105 2950187055018454043094829)
          ·
            refine ⟨1106320145631920266160561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2950187055018454043094829 1106320145631920266160561)
            ·
              refine ⟨829740109223940199620421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1106320145631920266160561 829740109223940199620421)
              ·
                refine ⟨155576270479488787428829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 829740109223940199620421 155576270479488787428829)
                ·
                  rfl

theorem cell19_511285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2, 4].length) (baseStart_511285 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_511285 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_511285 prefixEnd_511285 := by exact prefixLift 511285
  have htrace : WordTrace (prefixWord ++ tailWord_511285) baseStart_511285 baseEnd_511285 := by
    simpa [prefixWord, tailWord_511285, baseEnd_511285] using wordTrace_append hprefix tailTrace_511285
  have hstable : (prefixWord ++ tailWord_511285).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511285).length < 2 ^ (prefixWord ++ tailWord_511285).sum := by decide
  have hdescent : baseEnd_511285 < baseStart_511285 := by decide
  rcases family_descends (prefixWord ++ tailWord_511285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511338 : List Nat := [3, 1, 3, 3, 3, 1, 1, 4]
def baseStart_511338 : Nat := 118140960795 + 511338 * 2 ^ 59
def prefixEnd_511338 : Nat := 4983230072969 + 3 ^ 40 * 511338 * 2
def baseEnd_511338 : Nat := 155592397575600368250907

theorem tailTrace_511338 : CollatzResearch.WordTrace tailWord_511338 prefixEnd_511338 155592397575600368250907 := by
  unfold tailWord_511338
  simp only [CollatzResearch.WordTrace]
  refine ⟨4662507255379307605711667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12433352681011486948564445 4662507255379307605711667)
  ·
    refine ⟨6993760883068961408567501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4662507255379307605711667 6993760883068961408567501)
    ·
      refine ⟨2622660331150860528212813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6993760883068961408567501 2622660331150860528212813)
      ·
        refine ⟨983497624181572698079805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2622660331150860528212813 983497624181572698079805)
        ·
          refine ⟨368811609068089761779927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 983497624181572698079805 368811609068089761779927)
          ·
            refine ⟨553217413602134642669891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 368811609068089761779927 553217413602134642669891)
            ·
              refine ⟨829826120403201964004837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 553217413602134642669891 829826120403201964004837)
              ·
                refine ⟨155592397575600368250907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 829826120403201964004837 155592397575600368250907)
                ·
                  rfl

theorem cell19_511338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 1, 4].length) (baseStart_511338 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_511338 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_511338 prefixEnd_511338 := by exact prefixLift 511338
  have htrace : WordTrace (prefixWord ++ tailWord_511338) baseStart_511338 baseEnd_511338 := by
    simpa [prefixWord, tailWord_511338, baseEnd_511338] using wordTrace_append hprefix tailTrace_511338
  have hstable : (prefixWord ++ tailWord_511338).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511338).length < 2 ^ (prefixWord ++ tailWord_511338).sum := by decide
  have hdescent : baseEnd_511338 < baseStart_511338 := by decide
  rcases family_descends (prefixWord ++ tailWord_511338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511378 : List Nat := [3, 2, 3, 3, 1, 1, 6]
def baseStart_511378 : Nat := 118140960795 + 511378 * 2 ^ 59
def prefixEnd_511378 : Nat := 4983230072969 + 3 ^ 40 * 511378 * 2
def baseEnd_511378 : Nat := 51868189656297375787303

theorem tailTrace_511378 : CollatzResearch.WordTrace tailWord_511378 prefixEnd_511378 51868189656297375787303 := by
  unfold tailWord_511378
  simp only [CollatzResearch.WordTrace]
  refine ⟨4662871985343079313575697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12434325294248211502868525 4662871985343079313575697)
  ·
    refine ⟨3497153989007309485181773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4662871985343079313575697 3497153989007309485181773)
    ·
      refine ⟨1311432745877741056943165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3497153989007309485181773 1311432745877741056943165)
      ·
        refine ⟨491787279704152896353687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1311432745877741056943165 491787279704152896353687)
        ·
          refine ⟨737680919556229344530531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 491787279704152896353687 737680919556229344530531)
          ·
            refine ⟨1106521379334344016795797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 737680919556229344530531 1106521379334344016795797)
            ·
              refine ⟨51868189656297375787303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1106521379334344016795797 51868189656297375787303)
              ·
                rfl

theorem cell19_511378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 6].length) (baseStart_511378 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_511378 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_511378 prefixEnd_511378 := by exact prefixLift 511378
  have htrace : WordTrace (prefixWord ++ tailWord_511378) baseStart_511378 baseEnd_511378 := by
    simpa [prefixWord, tailWord_511378, baseEnd_511378] using wordTrace_append hprefix tailTrace_511378
  have hstable : (prefixWord ++ tailWord_511378).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511378).length < 2 ^ (prefixWord ++ tailWord_511378).sum := by decide
  have hdescent : baseEnd_511378 < baseStart_511378 := by decide
  rcases family_descends (prefixWord ++ tailWord_511378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511380 : List Nat := [2, 4, 2, 1, 2, 2, 6]
def baseStart_511380 : Nat := 118140960795 + 511380 * 2 ^ 59
def prefixEnd_511380 : Nat := 4983230072969 + 3 ^ 40 * 511380 * 2
def baseEnd_511380 : Nat := 51868392512852238439153

theorem tailTrace_511380 : CollatzResearch.WordTrace tailWord_511380 prefixEnd_511380 51868392512852238439153 := by
  unfold tailWord_511380
  simp only [CollatzResearch.WordTrace]
  refine ⟨9325780443682535797937797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12434373924910047730583729 9325780443682535797937797)
  ·
    refine ⟨1748583833190475462113337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9325780443682535797937797 1748583833190475462113337)
    ·
      refine ⟨1311437874892856596585003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1748583833190475462113337 1311437874892856596585003)
      ·
        refine ⟨1967156812339284894877505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1311437874892856596585003 1967156812339284894877505)
        ·
          refine ⟨1475367609254463671158129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1967156812339284894877505 1475367609254463671158129)
          ·
            refine ⟨1106525706940847753368597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1475367609254463671158129 1106525706940847753368597)
            ·
              refine ⟨51868392512852238439153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1106525706940847753368597 51868392512852238439153)
              ·
                rfl

theorem cell19_511380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 6].length) (baseStart_511380 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_511380 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_511380 prefixEnd_511380 := by exact prefixLift 511380
  have htrace : WordTrace (prefixWord ++ tailWord_511380) baseStart_511380 baseEnd_511380 := by
    simpa [prefixWord, tailWord_511380, baseEnd_511380] using wordTrace_append hprefix tailTrace_511380
  have hstable : (prefixWord ++ tailWord_511380).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511380).length < 2 ^ (prefixWord ++ tailWord_511380).sum := by decide
  have hdescent : baseEnd_511380 < baseStart_511380 := by decide
  rcases family_descends (prefixWord ++ tailWord_511380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511553 : List Nat := [1, 2, 5, 1, 1, 1, 8]
def baseStart_511553 : Nat := 118140960795 + 511553 * 2 ^ 59
def prefixEnd_511553 : Nat := 4983230072969 + 3 ^ 40 * 511553 * 2
def baseEnd_511553 : Nat := 51885939604847857824181

theorem tailTrace_511553 : CollatzResearch.WordTrace tailWord_511553 prefixEnd_511553 51885939604847857824181 := by
  unfold tailWord_511553
  simp only [CollatzResearch.WordTrace]
  refine ⟨18657870715738322141923313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12438580477158881427948875 18657870715738322141923313)
  ·
    refine ⟨13993403036803741606442485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18657870715738322141923313 13993403036803741606442485)
    ·
      refine ⟨1311881534700350775603983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13993403036803741606442485 1311881534700350775603983)
      ·
        refine ⟨1967822302050526163405975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1311881534700350775603983 1967822302050526163405975)
        ·
          refine ⟨2951733453075789245108963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1967822302050526163405975 2951733453075789245108963)
          ·
            refine ⟨4427600179613683867663445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2951733453075789245108963 4427600179613683867663445)
            ·
              refine ⟨51885939604847857824181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4427600179613683867663445 51885939604847857824181)
              ·
                rfl

theorem cell19_511553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 8].length) (baseStart_511553 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_511553 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_511553 prefixEnd_511553 := by exact prefixLift 511553
  have htrace : WordTrace (prefixWord ++ tailWord_511553) baseStart_511553 baseEnd_511553 := by
    simpa [prefixWord, tailWord_511553, baseEnd_511553] using wordTrace_append hprefix tailTrace_511553
  have hstable : (prefixWord ++ tailWord_511553).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511553).length < 2 ^ (prefixWord ++ tailWord_511553).sum := by decide
  have hdescent : baseEnd_511553 < baseStart_511553 := by decide
  rcases family_descends (prefixWord ++ tailWord_511553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511572 : List Nat := [2, 4, 1, 1, 1, 2, 2, 6]
def baseStart_511572 : Nat := 118140960795 + 511572 * 2 ^ 59
def prefixEnd_511572 : Nat := 4983230072969 + 3 ^ 40 * 511572 * 2
def baseEnd_511572 : Nat := 155663600226357159050269

theorem tailTrace_511572 : CollatzResearch.WordTrace tailWord_511572 prefixEnd_511572 155663600226357159050269 := by
  unfold tailWord_511572
  simp only [CollatzResearch.WordTrace]
  refine ⟨9329281851334744193432485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12439042468446325591243313 9329281851334744193432485)
  ·
    refine ⟨1749240347125264536268591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9329281851334744193432485 1749240347125264536268591)
    ·
      refine ⟨2623860520687896804402887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1749240347125264536268591 2623860520687896804402887)
      ·
        refine ⟨3935790781031845206604331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2623860520687896804402887 3935790781031845206604331)
        ·
          refine ⟨5903686171547767809906497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3935790781031845206604331 5903686171547767809906497)
          ·
            refine ⟨4427764628660825857429873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5903686171547767809906497 4427764628660825857429873)
            ·
              refine ⟨3320823471495619393072405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4427764628660825857429873 3320823471495619393072405)
              ·
                refine ⟨155663600226357159050269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3320823471495619393072405 155663600226357159050269)
                ·
                  rfl

theorem cell19_511572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 6].length) (baseStart_511572 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_511572 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_511572 prefixEnd_511572 := by exact prefixLift 511572
  have htrace : WordTrace (prefixWord ++ tailWord_511572) baseStart_511572 baseEnd_511572 := by
    simpa [prefixWord, tailWord_511572, baseEnd_511572] using wordTrace_append hprefix tailTrace_511572
  have hstable : (prefixWord ++ tailWord_511572).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511572).length < 2 ^ (prefixWord ++ tailWord_511572).sum := by decide
  have hdescent : baseEnd_511572 < baseStart_511572 := by decide
  rcases family_descends (prefixWord ++ tailWord_511572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan19Incremental
