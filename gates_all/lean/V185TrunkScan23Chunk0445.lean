import V185TrunkScan23Chunk0444

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2631101 : List Nat := [1, 4, 1, 2, 2, 1, 5, 1, 1, 2, 3]
def baseStart_2631101 : Nat := 118140960795 + 2631101 * 2 ^ 59
def prefixEnd_2631101 : Nat := 4983230072969 + 3 ^ 40 * 2631101 * 2
def baseEnd_2631101 : Nat := 1351019463525415538937293

theorem tailTrace_2631101 : CollatzResearch.WordTrace tailWord_2631101 prefixEnd_2631101 1351019463525415538937293 := by
  unfold tailWord_2631101
  simp only [CollatzResearch.WordTrace]
  refine ⟨95964137240977908120829157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63976091493985272080552771 95964137240977908120829157)
  ·
    refine ⟨17993275732683357772655467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95964137240977908120829157 17993275732683357772655467)
    ·
      refine ⟨26989913599025036658983201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17993275732683357772655467 26989913599025036658983201)
      ·
        refine ⟨20242435199268777494237401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26989913599025036658983201 20242435199268777494237401)
        ·
          refine ⟨15181826399451583120678051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20242435199268777494237401 15181826399451583120678051)
          ·
            refine ⟨22772739599177374681017077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15181826399451583120678051 22772739599177374681017077)
            ·
              refine ⟨2134944337422878876345351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22772739599177374681017077 2134944337422878876345351)
              ·
                refine ⟨3202416506134318314518027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2134944337422878876345351 3202416506134318314518027)
                ·
                  refine ⟨4803624759201477471777041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3202416506134318314518027 4803624759201477471777041)
                  ·
                    refine ⟨3602718569401108103832781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4803624759201477471777041 3602718569401108103832781)
                    ·
                      refine ⟨1351019463525415538937293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3602718569401108103832781 1351019463525415538937293)
                      ·
                        rfl

theorem cell23_2631101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 5, 1, 1, 2, 3].length) (baseStart_2631101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2631101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2631101 prefixEnd_2631101 := by exact prefixLift 2631101
  have htrace : WordTrace (prefixWord ++ tailWord_2631101) baseStart_2631101 baseEnd_2631101 := by
    simpa [prefixWord, tailWord_2631101, baseEnd_2631101] using wordTrace_append hprefix tailTrace_2631101
  have hstable : (prefixWord ++ tailWord_2631101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2631101).length < 2 ^ (prefixWord ++ tailWord_2631101).sum := by decide
  have hdescent : baseEnd_2631101 < baseStart_2631101 := by decide
  rcases family_descends (prefixWord ++ tailWord_2631101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2631141 : List Nat := [1, 3, 1, 5, 1, 1, 2, 1, 3, 3, 2]
def baseStart_2631141 : Nat := 118140960795 + 2631141 * 2 ^ 59
def prefixEnd_2631141 : Nat := 4983230072969 + 3 ^ 40 * 2631141 * 2
def baseEnd_2631141 : Nat := 1351040002751595382437109

theorem tailTrace_2631141 : CollatzResearch.WordTrace tailWord_2631141 prefixEnd_2631141 1351040002751595382437109 := by
  unfold tailWord_2631141
  simp only [CollatzResearch.WordTrace]
  refine ⟨95965596160832994952285277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63977064107221996634856851 95965596160832994952285277)
  ·
    refine ⟨35987098560312373107106979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95965596160832994952285277 35987098560312373107106979)
    ·
      refine ⟨53980647840468559660660469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35987098560312373107106979 53980647840468559660660469)
      ·
        refine ⟨5060685735043927468186919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 53980647840468559660660469 5060685735043927468186919)
        ·
          refine ⟨7591028602565891202280379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5060685735043927468186919 7591028602565891202280379)
          ·
            refine ⟨11386542903848836803420569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7591028602565891202280379 11386542903848836803420569)
            ·
              refine ⟨8539907177886627602565427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11386542903848836803420569 8539907177886627602565427)
              ·
                refine ⟨12809860766829941403848141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8539907177886627602565427 12809860766829941403848141)
                ·
                  refine ⟨4803697787561228026443053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12809860766829941403848141 4803697787561228026443053)
                  ·
                    refine ⟨1801386670335460509916145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4803697787561228026443053 1801386670335460509916145)
                    ·
                      refine ⟨1351040002751595382437109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1801386670335460509916145 1351040002751595382437109)
                      ·
                        rfl

theorem cell23_2631141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 1, 3, 3, 2].length) (baseStart_2631141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2631141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2631141 prefixEnd_2631141 := by exact prefixLift 2631141
  have htrace : WordTrace (prefixWord ++ tailWord_2631141) baseStart_2631141 baseEnd_2631141 := by
    simpa [prefixWord, tailWord_2631141, baseEnd_2631141] using wordTrace_append hprefix tailTrace_2631141
  have hstable : (prefixWord ++ tailWord_2631141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2631141).length < 2 ^ (prefixWord ++ tailWord_2631141).sum := by decide
  have hdescent : baseEnd_2631141 < baseStart_2631141 := by decide
  rcases family_descends (prefixWord ++ tailWord_2631141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2631158 : List Nat := [5, 1, 1, 1, 2, 3, 1, 3, 1, 3, 2]
def baseStart_2631158 : Nat := 118140960795 + 2631158 * 2 ^ 59
def prefixEnd_2631158 : Nat := 4983230072969 + 3 ^ 40 * 2631158 * 2
def baseEnd_2631158 : Nat := 1351048731922721815924531

theorem tailTrace_2631158 : CollatzResearch.WordTrace tailWord_2631158 prefixEnd_2631158 1351048731922721815924531 := by
  unfold tailWord_2631158
  simp only [CollatzResearch.WordTrace]
  refine ⟨5997888512610712928478383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 63977477467847604570436085 5997888512610712928478383)
  ·
    refine ⟨8996832768916069392717575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5997888512610712928478383 8996832768916069392717575)
    ·
      refine ⟨13495249153374104089076363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8996832768916069392717575 13495249153374104089076363)
      ·
        refine ⟨20242873730061156133614545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13495249153374104089076363 20242873730061156133614545)
        ·
          refine ⟨15182155297545867100210909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20242873730061156133614545 15182155297545867100210909)
          ·
            refine ⟨5693308236579700162579091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15182155297545867100210909 5693308236579700162579091)
            ·
              refine ⟨8539962354869550243868637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5693308236579700162579091 8539962354869550243868637)
              ·
                refine ⟨3202485883076081341450739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8539962354869550243868637 3202485883076081341450739)
                ·
                  refine ⟨4803728824614122012176109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3202485883076081341450739 4803728824614122012176109)
                  ·
                    refine ⟨1801398309230295754566041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4803728824614122012176109 1801398309230295754566041)
                    ·
                      refine ⟨1351048731922721815924531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1801398309230295754566041 1351048731922721815924531)
                      ·
                        rfl

theorem cell23_2631158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 3, 1, 3, 2].length) (baseStart_2631158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2631158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2631158 prefixEnd_2631158 := by exact prefixLift 2631158
  have htrace : WordTrace (prefixWord ++ tailWord_2631158) baseStart_2631158 baseEnd_2631158 := by
    simpa [prefixWord, tailWord_2631158, baseEnd_2631158] using wordTrace_append hprefix tailTrace_2631158
  have hstable : (prefixWord ++ tailWord_2631158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2631158).length < 2 ^ (prefixWord ++ tailWord_2631158).sum := by decide
  have hdescent : baseEnd_2631158 < baseStart_2631158 := by decide
  rcases family_descends (prefixWord ++ tailWord_2631158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2631171 : List Nat := [1, 1, 1, 3, 2, 1, 2, 6, 2, 2, 2]
def baseStart_2631171 : Nat := 118140960795 + 2631171 * 2 ^ 59
def prefixEnd_2631171 : Nat := 4983230072969 + 3 ^ 40 * 2631171 * 2
def baseEnd_2631171 : Nat := 1351055407171230265061971

theorem tailTrace_2631171 : CollatzResearch.WordTrace tailWord_2631171 prefixEnd_2631171 1351055407171230265061971 := by
  unfold tailWord_2631171
  simp only [CollatzResearch.WordTrace]
  refine ⟨95966690350724310075877367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63977793567149540050584911 95966690350724310075877367)
  ·
    refine ⟨143950035526086465113816051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95966690350724310075877367 143950035526086465113816051)
    ·
      refine ⟨215925053289129697670724077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143950035526086465113816051 215925053289129697670724077)
      ·
        refine ⟨80971894983423636626521529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 215925053289129697670724077 80971894983423636626521529)
        ·
          refine ⟨60728921237567727469891147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80971894983423636626521529 60728921237567727469891147)
          ·
            refine ⟨91093381856351591204836721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60728921237567727469891147 91093381856351591204836721)
            ·
              refine ⟨68320036392263693403627541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91093381856351591204836721 68320036392263693403627541)
              ·
                refine ⟨3202501705887360628295041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 68320036392263693403627541 3202501705887360628295041)
                ·
                  refine ⟨2401876279415520471221281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3202501705887360628295041 2401876279415520471221281)
                  ·
                    refine ⟨1801407209561640353415961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2401876279415520471221281 1801407209561640353415961)
                    ·
                      refine ⟨1351055407171230265061971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1801407209561640353415961 1351055407171230265061971)
                      ·
                        rfl

theorem cell23_2631171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 6, 2, 2, 2].length) (baseStart_2631171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2631171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2631171 prefixEnd_2631171 := by exact prefixLift 2631171
  have htrace : WordTrace (prefixWord ++ tailWord_2631171) baseStart_2631171 baseEnd_2631171 := by
    simpa [prefixWord, tailWord_2631171, baseEnd_2631171] using wordTrace_append hprefix tailTrace_2631171
  have hstable : (prefixWord ++ tailWord_2631171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2631171).length < 2 ^ (prefixWord ++ tailWord_2631171).sum := by decide
  have hdescent : baseEnd_2631171 < baseStart_2631171 := by decide
  rcases family_descends (prefixWord ++ tailWord_2631171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2631177 : List Nat := [1, 2, 1, 1, 3, 1, 6, 1, 7]
def baseStart_2631177 : Nat := 118140960795 + 2631177 * 2 ^ 59
def prefixEnd_2631177 : Nat := 4983230072969 + 3 ^ 40 * 2631177 * 2
def baseEnd_2631177 : Nat := 150117609783906360176327

theorem tailTrace_2631177 : CollatzResearch.WordTrace tailWord_2631177 prefixEnd_2631177 150117609783906360176327 := by
  unfold tailWord_2631177
  simp only [CollatzResearch.WordTrace]
  refine ⟨95966909188702573100595785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63977939459135048733730523 95966909188702573100595785)
  ·
    refine ⟨71975181891526929825446839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95966909188702573100595785 71975181891526929825446839)
    ·
      refine ⟨107962772837290394738170259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71975181891526929825446839 107962772837290394738170259)
      ·
        refine ⟨161944159255935592107255389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107962772837290394738170259 161944159255935592107255389)
        ·
          refine ⟨60729059720975847040220771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 161944159255935592107255389 60729059720975847040220771)
          ·
            refine ⟨91093589581463770560331157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60729059720975847040220771 91093589581463770560331157)
            ·
              refine ⟨4270012011631114245015523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 91093589581463770560331157 4270012011631114245015523)
              ·
                refine ⟨6405018017446671367523285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4270012011631114245015523 6405018017446671367523285)
                ·
                  refine ⟨150117609783906360176327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6405018017446671367523285 150117609783906360176327)
                  ·
                    rfl

theorem cell23_2631177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6, 1, 7].length) (baseStart_2631177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2631177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2631177 prefixEnd_2631177 := by exact prefixLift 2631177
  have htrace : WordTrace (prefixWord ++ tailWord_2631177) baseStart_2631177 baseEnd_2631177 := by
    simpa [prefixWord, tailWord_2631177, baseEnd_2631177] using wordTrace_append hprefix tailTrace_2631177
  have hstable : (prefixWord ++ tailWord_2631177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2631177).length < 2 ^ (prefixWord ++ tailWord_2631177).sum := by decide
  have hdescent : baseEnd_2631177 < baseStart_2631177 := by decide
  rcases family_descends (prefixWord ++ tailWord_2631177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2631217 : List Nat := [1, 2, 2, 3, 1, 1, 1, 4, 1, 2, 5]
def baseStart_2631217 : Nat := 118140960795 + 2631217 * 2 ^ 59
def prefixEnd_2631217 : Nat := 4983230072969 + 3 ^ 40 * 2631217 * 2
def baseEnd_2631217 : Nat := 1351079027281337085086759

theorem tailTrace_2631217 : CollatzResearch.WordTrace tailWord_2631217 prefixEnd_2631217 1351079027281337085086759 := by
  unfold tailWord_2631217
  simp only [CollatzResearch.WordTrace]
  refine ⟨95968368108557659932051905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63978912072371773288034603 95968368108557659932051905)
  ·
    refine ⟨71976276081418244949038929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95968368108557659932051905 71976276081418244949038929)
    ·
      refine ⟨53982207061063683711779197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71976276081418244949038929 53982207061063683711779197)
      ·
        refine ⟨20243327647898881391917199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53982207061063683711779197 20243327647898881391917199)
        ·
          refine ⟨30364991471848322087875799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20243327647898881391917199 30364991471848322087875799)
          ·
            refine ⟨45547487207772483131813699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30364991471848322087875799 45547487207772483131813699)
            ·
              refine ⟨68321230811658724697720549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45547487207772483131813699 68321230811658724697720549)
              ·
                refine ⟨12810230777186010880822603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68321230811658724697720549 12810230777186010880822603)
                ·
                  refine ⟨19215346165779016321233905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12810230777186010880822603 19215346165779016321233905)
                  ·
                    refine ⟨14411509624334262240925429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19215346165779016321233905 14411509624334262240925429)
                    ·
                      refine ⟨1351079027281337085086759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14411509624334262240925429 1351079027281337085086759)
                      ·
                        rfl

theorem cell23_2631217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 4, 1, 2, 5].length) (baseStart_2631217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2631217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2631217 prefixEnd_2631217 := by exact prefixLift 2631217
  have htrace : WordTrace (prefixWord ++ tailWord_2631217) baseStart_2631217 baseEnd_2631217 := by
    simpa [prefixWord, tailWord_2631217, baseEnd_2631217] using wordTrace_append hprefix tailTrace_2631217
  have hstable : (prefixWord ++ tailWord_2631217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2631217).length < 2 ^ (prefixWord ++ tailWord_2631217).sum := by decide
  have hdescent : baseEnd_2631217 < baseStart_2631217 := by decide
  rcases family_descends (prefixWord ++ tailWord_2631217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2631224 : List Nat := [2, 1, 2, 1, 4, 3, 1, 2, 2, 5]
def baseStart_2631224 : Nat := 118140960795 + 2631224 * 2 ^ 59
def prefixEnd_2631224 : Nat := 4983230072969 + 3 ^ 40 * 2631224 * 2
def baseEnd_2631224 : Nat := 450360873881972852566409

theorem tailTrace_2631224 : CollatzResearch.WordTrace tailWord_2631224 prefixEnd_2631224 450360873881972852566409 := by
  unfold tailWord_2631224
  simp only [CollatzResearch.WordTrace]
  refine ⟨47984311709766150063778363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63979082279688200085037817 47984311709766150063778363)
  ·
    refine ⟨71976467564649225095667545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47984311709766150063778363 71976467564649225095667545)
    ·
      refine ⟨53982350673486918821750659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71976467564649225095667545 53982350673486918821750659)
      ·
        refine ⟨80973526010230378232625989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53982350673486918821750659 80973526010230378232625989)
        ·
          refine ⟨15182536126918195918617373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80973526010230378232625989 15182536126918195918617373)
          ·
            refine ⟨5693451047594323469481515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15182536126918195918617373 5693451047594323469481515)
            ·
              refine ⟨8540176571391485204222273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5693451047594323469481515 8540176571391485204222273)
              ·
                refine ⟨6405132428543613903166705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8540176571391485204222273 6405132428543613903166705)
                ·
                  refine ⟨4803849321407710427375029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6405132428543613903166705 4803849321407710427375029)
                  ·
                    refine ⟨450360873881972852566409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4803849321407710427375029 450360873881972852566409)
                    ·
                      rfl

theorem cell23_2631224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 2, 2, 5].length) (baseStart_2631224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2631224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2631224 prefixEnd_2631224 := by exact prefixLift 2631224
  have htrace : WordTrace (prefixWord ++ tailWord_2631224) baseStart_2631224 baseEnd_2631224 := by
    simpa [prefixWord, tailWord_2631224, baseEnd_2631224] using wordTrace_append hprefix tailTrace_2631224
  have hstable : (prefixWord ++ tailWord_2631224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2631224).length < 2 ^ (prefixWord ++ tailWord_2631224).sum := by decide
  have hdescent : baseEnd_2631224 < baseStart_2631224 := by decide
  rcases family_descends (prefixWord ++ tailWord_2631224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2631228 : List Nat := [2, 2, 2, 2, 4, 1, 3, 2, 5]
def baseStart_2631228 : Nat := 118140960795 + 2631228 * 2 ^ 59
def prefixEnd_2631228 : Nat := 4983230072969 + 3 ^ 40 * 2631228 * 2
def baseEnd_2631228 : Nat := 150120519507615171338801

theorem tailTrace_2631228 : CollatzResearch.WordTrace tailWord_2631228 prefixEnd_2631228 150120519507615171338801 := by
  unfold tailWord_2631228
  simp only [CollatzResearch.WordTrace]
  refine ⟨47984384655758904405351169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63979179541011872540468225 47984384655758904405351169)
  ·
    refine ⟨35988288491819178304013377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47984384655758904405351169 35988288491819178304013377)
    ·
      refine ⟨26991216368864383728010033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35988288491819178304013377 26991216368864383728010033)
      ·
        refine ⟨20243412276648287796007525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26991216368864383728010033 20243412276648287796007525)
        ·
          refine ⟨3795639801871553961751411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20243412276648287796007525 3795639801871553961751411)
          ·
            refine ⟨5693459702807330942627117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3795639801871553961751411 5693459702807330942627117)
            ·
              refine ⟨2135047388552749103485169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5693459702807330942627117 2135047388552749103485169)
              ·
                refine ⟨1601285541414561827613877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2135047388552749103485169 1601285541414561827613877)
                ·
                  refine ⟨150120519507615171338801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1601285541414561827613877 150120519507615171338801)
                  ·
                    rfl

theorem cell23_2631228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 3, 2, 5].length) (baseStart_2631228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2631228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2631228 prefixEnd_2631228 := by exact prefixLift 2631228
  have htrace : WordTrace (prefixWord ++ tailWord_2631228) baseStart_2631228 baseEnd_2631228 := by
    simpa [prefixWord, tailWord_2631228, baseEnd_2631228] using wordTrace_append hprefix tailTrace_2631228
  have hstable : (prefixWord ++ tailWord_2631228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2631228).length < 2 ^ (prefixWord ++ tailWord_2631228).sum := by decide
  have hdescent : baseEnd_2631228 < baseStart_2631228 := by decide
  rcases family_descends (prefixWord ++ tailWord_2631228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2631257 : List Nat := [1, 2, 1, 2, 2, 1, 1, 3, 2, 4, 4]
def baseStart_2631257 : Nat := 118140960795 + 2631257 * 2 ^ 59
def prefixEnd_2631257 : Nat := 4983230072969 + 3 ^ 40 * 2631257 * 2
def baseEnd_2631257 : Nat := 1351099566507516928586575

theorem tailTrace_2631257 : CollatzResearch.WordTrace tailWord_2631257 prefixEnd_2631257 1351099566507516928586575 := by
  unfold tailWord_2631257
  simp only [CollatzResearch.WordTrace]
  refine ⟨95969827028412746763508025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63979884685608497842338683 95969827028412746763508025)
  ·
    refine ⟨71977370271309560072631019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95969827028412746763508025 71977370271309560072631019)
    ·
      refine ⟨107966055406964340108946529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71977370271309560072631019 107966055406964340108946529)
      ·
        refine ⟨80974541555223255081709897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107966055406964340108946529 80974541555223255081709897)
        ·
          refine ⟨60730906166417441311282423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80974541555223255081709897 60730906166417441311282423)
          ·
            refine ⟨91096359249626161966923635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60730906166417441311282423 91096359249626161966923635)
            ·
              refine ⟨136644538874439242950385453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91096359249626161966923635 136644538874439242950385453)
              ·
                refine ⟨51241702077914716106394545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 136644538874439242950385453 51241702077914716106394545)
                ·
                  refine ⟨38431276558436037079795909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51241702077914716106394545 38431276558436037079795909)
                  ·
                    refine ⟨7205864354706756952461733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38431276558436037079795909 7205864354706756952461733)
                    ·
                      refine ⟨1351099566507516928586575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7205864354706756952461733 1351099566507516928586575)
                      ·
                        rfl

theorem cell23_2631257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 2, 4, 4].length) (baseStart_2631257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2631257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2631257 prefixEnd_2631257 := by exact prefixLift 2631257
  have htrace : WordTrace (prefixWord ++ tailWord_2631257) baseStart_2631257 baseEnd_2631257 := by
    simpa [prefixWord, tailWord_2631257, baseEnd_2631257] using wordTrace_append hprefix tailTrace_2631257
  have hstable : (prefixWord ++ tailWord_2631257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2631257).length < 2 ^ (prefixWord ++ tailWord_2631257).sum := by decide
  have hdescent : baseEnd_2631257 < baseStart_2631257 := by decide
  rcases family_descends (prefixWord ++ tailWord_2631257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2631287 : List Nat := [1, 1, 3, 1, 1, 3, 1, 3, 1, 2, 6]
def baseStart_2631287 : Nat := 118140960795 + 2631287 * 2 ^ 59
def prefixEnd_2631287 : Nat := 4983230072969 + 3 ^ 40 * 2631287 * 2
def baseEnd_2631287 : Nat := 1351114970927151811211437

theorem tailTrace_2631287 : CollatzResearch.WordTrace tailWord_2631287 prefixEnd_2631287 1351114970927151811211437 := by
  unfold tailWord_2631287
  simp only [CollatzResearch.WordTrace]
  refine ⟨95970921218304061887100115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63980614145536041258066743 95970921218304061887100115)
  ·
    refine ⟨143956381827456092830650173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95970921218304061887100115 143956381827456092830650173)
    ·
      refine ⟨53983643185296034811493815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143956381827456092830650173 53983643185296034811493815)
      ·
        refine ⟨80975464777944052217240723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53983643185296034811493815 80975464777944052217240723)
        ·
          refine ⟨121463197166916078325861085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80975464777944052217240723 121463197166916078325861085)
          ·
            refine ⟨45548698937593529372197907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 121463197166916078325861085 45548698937593529372197907)
            ·
              refine ⟨68323048406390294058296861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45548698937593529372197907 68323048406390294058296861)
              ·
                refine ⟨25621143152396360271861323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68323048406390294058296861 25621143152396360271861323)
                ·
                  refine ⟨38431714728594540407791985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25621143152396360271861323 38431714728594540407791985)
                  ·
                    refine ⟨28823786046445905305843989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38431714728594540407791985 28823786046445905305843989)
                    ·
                      refine ⟨1351114970927151811211437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28823786046445905305843989 1351114970927151811211437)
                      ·
                        rfl

theorem cell23_2631287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 3, 1, 2, 6].length) (baseStart_2631287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2631287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2631287 prefixEnd_2631287 := by exact prefixLift 2631287
  have htrace : WordTrace (prefixWord ++ tailWord_2631287) baseStart_2631287 baseEnd_2631287 := by
    simpa [prefixWord, tailWord_2631287, baseEnd_2631287] using wordTrace_append hprefix tailTrace_2631287
  have hstable : (prefixWord ++ tailWord_2631287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2631287).length < 2 ^ (prefixWord ++ tailWord_2631287).sum := by decide
  have hdescent : baseEnd_2631287 < baseStart_2631287 := by decide
  rcases family_descends (prefixWord ++ tailWord_2631287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2631307 : List Nat := [1, 1, 1, 1, 4, 1, 3, 1, 2, 1, 7]
def baseStart_2631307 : Nat := 118140960795 + 2631307 * 2 ^ 59
def prefixEnd_2631307 : Nat := 4983230072969 + 3 ^ 40 * 2631307 * 2
def baseEnd_2631307 : Nat := 1351125240540241732961345

theorem tailTrace_2631307 : CollatzResearch.WordTrace tailWord_2631307 prefixEnd_2631307 1351125240540241732961345 := by
  unfold tailWord_2631307
  simp only [CollatzResearch.WordTrace]
  refine ⟨95971650678231605302828175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63981100452154403535218783 95971650678231605302828175)
  ·
    refine ⟨143957476017347407954242263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95971650678231605302828175 143957476017347407954242263)
    ·
      refine ⟨215936214026021111931363395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143957476017347407954242263 215936214026021111931363395)
      ·
        refine ⟨323904321039031667897045093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215936214026021111931363395 323904321039031667897045093)
        ·
          refine ⟨60732060194818437730695955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 323904321039031667897045093 60732060194818437730695955)
          ·
            refine ⟨91098090292227656596043933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60732060194818437730695955 91098090292227656596043933)
            ·
              refine ⟨34161783859585371223516475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91098090292227656596043933 34161783859585371223516475)
              ·
                refine ⟨51242675789378056835274713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34161783859585371223516475 51242675789378056835274713)
                ·
                  refine ⟨38432006842033542626456035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51242675789378056835274713 38432006842033542626456035)
                  ·
                    refine ⟨57648010263050313939684053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38432006842033542626456035 57648010263050313939684053)
                    ·
                      refine ⟨1351125240540241732961345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 57648010263050313939684053 1351125240540241732961345)
                      ·
                        rfl

theorem cell23_2631307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 2, 1, 7].length) (baseStart_2631307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2631307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2631307 prefixEnd_2631307 := by exact prefixLift 2631307
  have htrace : WordTrace (prefixWord ++ tailWord_2631307) baseStart_2631307 baseEnd_2631307 := by
    simpa [prefixWord, tailWord_2631307, baseEnd_2631307] using wordTrace_append hprefix tailTrace_2631307
  have hstable : (prefixWord ++ tailWord_2631307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2631307).length < 2 ^ (prefixWord ++ tailWord_2631307).sum := by decide
  have hdescent : baseEnd_2631307 < baseStart_2631307 := by decide
  rcases family_descends (prefixWord ++ tailWord_2631307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2631321 : List Nat := [1, 2, 1, 2, 1, 2, 2, 5, 2, 3, 2]
def baseStart_2631321 : Nat := 118140960795 + 2631321 * 2 ^ 59
def prefixEnd_2631321 : Nat := 4983230072969 + 3 ^ 40 * 2631321 * 2
def baseEnd_2631321 : Nat := 1351132429269404678186281

theorem tailTrace_2631321 : CollatzResearch.WordTrace tailWord_2631321 prefixEnd_2631321 1351132429269404678186281 := by
  unfold tailWord_2631321
  simp only [CollatzResearch.WordTrace]
  refine ⟨95972161300180885693837817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63981440866787257129225211 95972161300180885693837817)
  ·
    refine ⟨71979120975135664270378363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95972161300180885693837817 71979120975135664270378363)
    ·
      refine ⟨107968681462703496405567545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71979120975135664270378363 107968681462703496405567545)
      ·
        refine ⟨80976511097027622304175659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107968681462703496405567545 80976511097027622304175659)
        ·
          refine ⟨121464766645541433456263489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80976511097027622304175659 121464766645541433456263489)
          ·
            refine ⟨91098574984156075092197617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121464766645541433456263489 91098574984156075092197617)
            ·
              refine ⟨68323931238117056319148213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91098574984156075092197617 68323931238117056319148213)
              ·
                refine ⟨6405368553573474029920145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 68323931238117056319148213 6405368553573474029920145)
                ·
                  refine ⟨4804026415180105522440109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6405368553573474029920145 4804026415180105522440109)
                  ·
                    refine ⟨1801509905692539570915041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4804026415180105522440109 1801509905692539570915041)
                    ·
                      refine ⟨1351132429269404678186281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1801509905692539570915041 1351132429269404678186281)
                      ·
                        rfl

theorem cell23_2631321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 5, 2, 3, 2].length) (baseStart_2631321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2631321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2631321 prefixEnd_2631321 := by exact prefixLift 2631321
  have htrace : WordTrace (prefixWord ++ tailWord_2631321) baseStart_2631321 baseEnd_2631321 := by
    simpa [prefixWord, tailWord_2631321, baseEnd_2631321] using wordTrace_append hprefix tailTrace_2631321
  have hstable : (prefixWord ++ tailWord_2631321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2631321).length < 2 ^ (prefixWord ++ tailWord_2631321).sum := by decide
  have hdescent : baseEnd_2631321 < baseStart_2631321 := by decide
  rcases family_descends (prefixWord ++ tailWord_2631321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2631354 : List Nat := [3, 1, 1, 1, 2, 4, 1, 1, 3, 1, 5]
def baseStart_2631354 : Nat := 118140960795 + 2631354 * 2 ^ 59
def prefixEnd_2631354 : Nat := 4983230072969 + 3 ^ 40 * 2631354 * 2
def baseEnd_2631354 : Nat := 1351149374131003049073629

theorem tailTrace_2631354 : CollatzResearch.WordTrace tailWord_2631354 prefixEnd_2631354 1351149374131003049073629 := by
  unfold tailWord_2631354
  simp only [CollatzResearch.WordTrace]
  refine ⟨23993341227265333082447279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63982243272707554886526077 23993341227265333082447279)
  ·
    refine ⟨35990011840897999623670919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23993341227265333082447279 35990011840897999623670919)
    ·
      refine ⟨53985017761346999435506379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35990011840897999623670919 53985017761346999435506379)
      ·
        refine ⟨80977526642020499153259569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53985017761346999435506379 80977526642020499153259569)
        ·
          refine ⟨60733144981515374364944677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80977526642020499153259569 60733144981515374364944677)
          ·
            refine ⟨11387464684034132693427127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60733144981515374364944677 11387464684034132693427127)
            ·
              refine ⟨17081197026051199040140691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11387464684034132693427127 17081197026051199040140691)
              ·
                refine ⟨25621795539076798560211037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17081197026051199040140691 25621795539076798560211037)
                ·
                  refine ⟨9608173327153799460079139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25621795539076798560211037 9608173327153799460079139)
                  ·
                    refine ⟨14412259990730699190118709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9608173327153799460079139 14412259990730699190118709)
                    ·
                      refine ⟨1351149374131003049073629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14412259990730699190118709 1351149374131003049073629)
                      ·
                        rfl

theorem cell23_2631354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 1, 3, 1, 5].length) (baseStart_2631354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2631354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2631354 prefixEnd_2631354 := by exact prefixLift 2631354
  have htrace : WordTrace (prefixWord ++ tailWord_2631354) baseStart_2631354 baseEnd_2631354 := by
    simpa [prefixWord, tailWord_2631354, baseEnd_2631354] using wordTrace_append hprefix tailTrace_2631354
  have hstable : (prefixWord ++ tailWord_2631354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2631354).length < 2 ^ (prefixWord ++ tailWord_2631354).sum := by decide
  have hdescent : baseEnd_2631354 < baseStart_2631354 := by decide
  rcases family_descends (prefixWord ++ tailWord_2631354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2631368 : List Nat := [2, 1, 3, 1, 2, 2, 1, 4, 3, 2, 2]
def baseStart_2631368 : Nat := 118140960795 + 2631368 * 2 ^ 59
def prefixEnd_2631368 : Nat := 4983230072969 + 3 ^ 40 * 2631368 * 2
def baseEnd_2631368 : Nat := 1351156562860165994298565

theorem tailTrace_2631368 : CollatzResearch.WordTrace tailWord_2631368 prefixEnd_2631368 1351156562860165994298565 := by
  unfold tailWord_2631368
  simp only [CollatzResearch.WordTrace]
  refine ⟨47986937765505306360399379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63982583687340408480532505 47986937765505306360399379)
  ·
    refine ⟨71980406648257959540599069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47986937765505306360399379 71980406648257959540599069)
    ·
      refine ⟨26992652493096734827724651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71980406648257959540599069 26992652493096734827724651)
      ·
        refine ⟨40488978739645102241586977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26992652493096734827724651 40488978739645102241586977)
        ·
          refine ⟨30366734054733826681190233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40488978739645102241586977 30366734054733826681190233)
          ·
            refine ⟨22775050541050370010892675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30366734054733826681190233 22775050541050370010892675)
            ·
              refine ⟨34162575811575555016339013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22775050541050370010892675 34162575811575555016339013)
              ·
                refine ⟨6405482964670416565563565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34162575811575555016339013 6405482964670416565563565)
                ·
                  refine ⟨2402056111751406212086337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6405482964670416565563565 2402056111751406212086337)
                  ·
                    refine ⟨1801542083813554659064753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2402056111751406212086337 1801542083813554659064753)
                    ·
                      refine ⟨1351156562860165994298565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1801542083813554659064753 1351156562860165994298565)
                      ·
                        rfl

theorem cell23_2631368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 4, 3, 2, 2].length) (baseStart_2631368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2631368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2631368 prefixEnd_2631368 := by exact prefixLift 2631368
  have htrace : WordTrace (prefixWord ++ tailWord_2631368) baseStart_2631368 baseEnd_2631368 := by
    simpa [prefixWord, tailWord_2631368, baseEnd_2631368] using wordTrace_append hprefix tailTrace_2631368
  have hstable : (prefixWord ++ tailWord_2631368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2631368).length < 2 ^ (prefixWord ++ tailWord_2631368).sum := by decide
  have hdescent : baseEnd_2631368 < baseStart_2631368 := by decide
  rcases family_descends (prefixWord ++ tailWord_2631368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2631374 : List Nat := [4, 1, 1, 1, 3, 1, 3, 9]
def baseStart_2631374 : Nat := 118140960795 + 2631374 * 2 ^ 59
def prefixEnd_2631374 : Nat := 4983230072969 + 3 ^ 40 * 2631374 * 2
def baseEnd_2631374 : Nat := 50042949768299739660131

theorem tailTrace_2631374 : CollatzResearch.WordTrace tailWord_2631374 prefixEnd_2631374 50042949768299739660131 := by
  unfold tailWord_2631374
  simp only [CollatzResearch.WordTrace]
  refine ⟨11996761796123609468189647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63982729579325917163678117 11996761796123609468189647)
  ·
    refine ⟨17995142694185414202284471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11996761796123609468189647 17995142694185414202284471)
    ·
      refine ⟨26992714041278121303426707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17995142694185414202284471 26992714041278121303426707)
      ·
        refine ⟨40489071061917181955140061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26992714041278121303426707 40489071061917181955140061)
        ·
          refine ⟨15183401648218943233177523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40489071061917181955140061 15183401648218943233177523)
          ·
            refine ⟨22775102472328414849766285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15183401648218943233177523 22775102472328414849766285)
            ·
              refine ⟨8540663427123155568662357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22775102472328414849766285 8540663427123155568662357)
              ·
                refine ⟨50042949768299739660131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8540663427123155568662357 50042949768299739660131)
                ·
                  rfl

theorem cell23_2631374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 9].length) (baseStart_2631374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2631374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2631374 prefixEnd_2631374 := by exact prefixLift 2631374
  have htrace : WordTrace (prefixWord ++ tailWord_2631374) baseStart_2631374 baseEnd_2631374 := by
    simpa [prefixWord, tailWord_2631374, baseEnd_2631374] using wordTrace_append hprefix tailTrace_2631374
  have hstable : (prefixWord ++ tailWord_2631374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2631374).length < 2 ^ (prefixWord ++ tailWord_2631374).sum := by decide
  have hdescent : baseEnd_2631374 < baseStart_2631374 := by decide
  rcases family_descends (prefixWord ++ tailWord_2631374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2631412 : List Nat := [2, 6, 1, 1, 1, 2, 1, 3, 2, 4]
def baseStart_2631412 : Nat := 118140960795 + 2631412 * 2 ^ 59
def prefixEnd_2631412 : Nat := 4983230072969 + 3 ^ 40 * 2631412 * 2
def baseEnd_2631412 : Nat := 450393052002987940716121

theorem tailTrace_2631412 : CollatzResearch.WordTrace tailWord_2631412 prefixEnd_2631412 450393052002987940716121 := by
  unfold tailWord_2631412
  simp only [CollatzResearch.WordTrace]
  refine ⟨47987740171425604117700245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63983653561900805490266993 47987740171425604117700245)
  ·
    refine ⟨2249425320535575193017199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 47987740171425604117700245 2249425320535575193017199)
    ·
      refine ⟨3374137980803362789525799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2249425320535575193017199 3374137980803362789525799)
      ·
        refine ⟨5061206971205044184288699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3374137980803362789525799 5061206971205044184288699)
        ·
          refine ⟨7591810456807566276433049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5061206971205044184288699 7591810456807566276433049)
          ·
            refine ⟨5693857842605674707324787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7591810456807566276433049 5693857842605674707324787)
            ·
              refine ⟨8540786763908512060987181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5693857842605674707324787 8540786763908512060987181)
              ·
                refine ⟨3202795036465692022870193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8540786763908512060987181 3202795036465692022870193)
                ·
                  refine ⟨2402096277349269017152645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3202795036465692022870193 2402096277349269017152645)
                  ·
                    refine ⟨450393052002987940716121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2402096277349269017152645 450393052002987940716121)
                    ·
                      rfl

theorem cell23_2631412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_2631412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2631412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2631412 prefixEnd_2631412 := by exact prefixLift 2631412
  have htrace : WordTrace (prefixWord ++ tailWord_2631412) baseStart_2631412 baseEnd_2631412 := by
    simpa [prefixWord, tailWord_2631412, baseEnd_2631412] using wordTrace_append hprefix tailTrace_2631412
  have hstable : (prefixWord ++ tailWord_2631412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2631412).length < 2 ^ (prefixWord ++ tailWord_2631412).sum := by decide
  have hdescent : baseEnd_2631412 < baseStart_2631412 := by decide
  rcases family_descends (prefixWord ++ tailWord_2631412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2631422 : List Nat := [4, 2, 2, 1, 3, 2, 1, 2, 1, 2, 3]
def baseStart_2631422 : Nat := 118140960795 + 2631422 * 2 ^ 59
def prefixEnd_2631422 : Nat := 4983230072969 + 3 ^ 40 * 2631422 * 2
def baseEnd_2631422 : Nat := 1351184290815508783023317

theorem tailTrace_2631422 : CollatzResearch.WordTrace tailWord_2631422 prefixEnd_2631422 1351184290815508783023317 := by
  unfold tailWord_2631422
  simp only [CollatzResearch.WordTrace]
  refine ⟨11996980634101872492908065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63983896715209986628843013 11996980634101872492908065)
  ·
    refine ⟨8997735475576404369681049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11996980634101872492908065 8997735475576404369681049)
    ·
      refine ⟨6748301606682303277260787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8997735475576404369681049 6748301606682303277260787)
      ·
        refine ⟨10122452410023454915891181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6748301606682303277260787 10122452410023454915891181)
        ·
          refine ⟨3795919653758795593459193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10122452410023454915891181 3795919653758795593459193)
          ·
            refine ⟨2846939740319096695094395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3795919653758795593459193 2846939740319096695094395)
            ·
              refine ⟨4270409610478645042641593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2846939740319096695094395 4270409610478645042641593)
              ·
                refine ⟨3202807207858983781981195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4270409610478645042641593 3202807207858983781981195)
                ·
                  refine ⟨4804210811788475672971793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3202807207858983781981195 4804210811788475672971793)
                  ·
                    refine ⟨3603158108841356754728845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4804210811788475672971793 3603158108841356754728845)
                    ·
                      refine ⟨1351184290815508783023317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3603158108841356754728845 1351184290815508783023317)
                      ·
                        rfl

theorem cell23_2631422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 1, 2, 1, 2, 3].length) (baseStart_2631422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2631422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2631422 prefixEnd_2631422 := by exact prefixLift 2631422
  have htrace : WordTrace (prefixWord ++ tailWord_2631422) baseStart_2631422 baseEnd_2631422 := by
    simpa [prefixWord, tailWord_2631422, baseEnd_2631422] using wordTrace_append hprefix tailTrace_2631422
  have hstable : (prefixWord ++ tailWord_2631422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2631422).length < 2 ^ (prefixWord ++ tailWord_2631422).sum := by decide
  have hdescent : baseEnd_2631422 < baseStart_2631422 := by decide
  rcases family_descends (prefixWord ++ tailWord_2631422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2631424 : List Nat := [2, 1, 1, 2, 1, 1, 2, 4, 2, 3, 4]
def baseStart_2631424 : Nat := 118140960795 + 2631424 * 2 ^ 59
def prefixEnd_2631424 : Nat := 4983230072969 + 3 ^ 40 * 2631424 * 2
def baseEnd_2631424 : Nat := 1351185317776817775198307

theorem tailTrace_2631424 : CollatzResearch.WordTrace tailWord_2631424 prefixEnd_2631424 1351185317776817775198307 := by
  unfold tailWord_2631424
  simp only [CollatzResearch.WordTrace]
  refine ⟨47987959009403867142418663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63983945345871822856558217 47987959009403867142418663)
  ·
    refine ⟨71981938514105800713627995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47987959009403867142418663 71981938514105800713627995)
    ·
      refine ⟨107972907771158701070441993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71981938514105800713627995 107972907771158701070441993)
      ·
        refine ⟨80979680828369025802831495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107972907771158701070441993 80979680828369025802831495)
        ·
          refine ⟨121469521242553538704247243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80979680828369025802831495 121469521242553538704247243)
          ·
            refine ⟨182204281863830308056370865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121469521242553538704247243 182204281863830308056370865)
            ·
              refine ⟨136653211397872731042278149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 182204281863830308056370865 136653211397872731042278149)
              ·
                refine ⟨25622477137101137070427153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 136653211397872731042278149 25622477137101137070427153)
                ·
                  refine ⟨19216857852825852802820365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25622477137101137070427153 19216857852825852802820365)
                  ·
                    refine ⟨7206321694809694801057637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19216857852825852802820365 7206321694809694801057637)
                    ·
                      refine ⟨1351185317776817775198307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7206321694809694801057637 1351185317776817775198307)
                      ·
                        rfl

theorem cell23_2631424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3, 4].length) (baseStart_2631424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2631424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2631424 prefixEnd_2631424 := by exact prefixLift 2631424
  have htrace : WordTrace (prefixWord ++ tailWord_2631424) baseStart_2631424 baseEnd_2631424 := by
    simpa [prefixWord, tailWord_2631424, baseEnd_2631424] using wordTrace_append hprefix tailTrace_2631424
  have hstable : (prefixWord ++ tailWord_2631424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2631424).length < 2 ^ (prefixWord ++ tailWord_2631424).sum := by decide
  have hdescent : baseEnd_2631424 < baseStart_2631424 := by decide
  rcases family_descends (prefixWord ++ tailWord_2631424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2631458 : List Nat := [3, 3, 1, 1, 2, 1, 1, 2, 3, 4, 2]
def baseStart_2631458 : Nat := 118140960795 + 2631458 * 2 ^ 59
def prefixEnd_2631458 : Nat := 4983230072969 + 3 ^ 40 * 2631458 * 2
def baseEnd_2631458 : Nat := 1351202776119070642173151

theorem tailTrace_2631458 : CollatzResearch.WordTrace tailWord_2631458 prefixEnd_2631458 1351202776119070642173151 := by
  unfold tailWord_2631458
  simp only [CollatzResearch.WordTrace]
  refine ⟨23994289525171139522893757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63984772067123038727716685 23994289525171139522893757)
  ·
    refine ⟨8997858571939177321085159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23994289525171139522893757 8997858571939177321085159)
    ·
      refine ⟨13496787857908765981627739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8997858571939177321085159 13496787857908765981627739)
      ·
        refine ⟨20245181786863148972441609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13496787857908765981627739 20245181786863148972441609)
        ·
          refine ⟨15183886340147361729331207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20245181786863148972441609 15183886340147361729331207)
          ·
            refine ⟨22775829510221042593996811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15183886340147361729331207 22775829510221042593996811)
            ·
              refine ⟨34163744265331563890995217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22775829510221042593996811 34163744265331563890995217)
              ·
                refine ⟨25622808198998672918246413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34163744265331563890995217 25622808198998672918246413)
                ·
                  refine ⟨9608553074624502344342405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25622808198998672918246413 9608553074624502344342405)
                  ·
                    refine ⟨1801603701492094189564201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9608553074624502344342405 1801603701492094189564201)
                    ·
                      refine ⟨1351202776119070642173151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1801603701492094189564201 1351202776119070642173151)
                      ·
                        rfl

theorem cell23_2631458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 2, 3, 4, 2].length) (baseStart_2631458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2631458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2631458 prefixEnd_2631458 := by exact prefixLift 2631458
  have htrace : WordTrace (prefixWord ++ tailWord_2631458) baseStart_2631458 baseEnd_2631458 := by
    simpa [prefixWord, tailWord_2631458, baseEnd_2631458] using wordTrace_append hprefix tailTrace_2631458
  have hstable : (prefixWord ++ tailWord_2631458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2631458).length < 2 ^ (prefixWord ++ tailWord_2631458).sum := by decide
  have hdescent : baseEnd_2631458 < baseStart_2631458 := by decide
  rcases family_descends (prefixWord ++ tailWord_2631458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2631461 : List Nat := [1, 3, 1, 2, 3, 2, 1, 1, 2, 4, 3]
def baseStart_2631461 : Nat := 118140960795 + 2631461 * 2 ^ 59
def prefixEnd_2631461 : Nat := 4983230072969 + 3 ^ 40 * 2631461 * 2
def baseEnd_2631461 : Nat := 1351204316561034130435637

theorem tailTrace_2631461 : CollatzResearch.WordTrace tailWord_2631461 prefixEnd_2631461 1351204316561034130435637 := by
  unfold tailWord_2631461
  simp only [CollatzResearch.WordTrace]
  refine ⟨95977267519673689603934237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63984845013115793069289491 95977267519673689603934237)
  ·
    refine ⟨35991475319877633601475339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95977267519673689603934237 35991475319877633601475339)
    ·
      refine ⟨53987212979816450402213009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35991475319877633601475339 53987212979816450402213009)
      ·
        refine ⟨40490409734862337801659757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53987212979816450402213009 40490409734862337801659757)
        ·
          refine ⟨15183903650573376675622409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40490409734862337801659757 15183903650573376675622409)
          ·
            refine ⟨11387927737930032506716807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15183903650573376675622409 11387927737930032506716807)
            ·
              refine ⟨17081891606895048760075211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11387927737930032506716807 17081891606895048760075211)
              ·
                refine ⟨25622837410342573140112817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17081891606895048760075211 25622837410342573140112817)
                ·
                  refine ⟨19217128057756929855084613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25622837410342573140112817 19217128057756929855084613)
                  ·
                    refine ⟨3603211510829424347828365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19217128057756929855084613 3603211510829424347828365)
                    ·
                      refine ⟨1351204316561034130435637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3603211510829424347828365 1351204316561034130435637)
                      ·
                        rfl

theorem cell23_2631461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 1, 2, 4, 3].length) (baseStart_2631461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2631461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2631461 prefixEnd_2631461 := by exact prefixLift 2631461
  have htrace : WordTrace (prefixWord ++ tailWord_2631461) baseStart_2631461 baseEnd_2631461 := by
    simpa [prefixWord, tailWord_2631461, baseEnd_2631461] using wordTrace_append hprefix tailTrace_2631461
  have hstable : (prefixWord ++ tailWord_2631461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2631461).length < 2 ^ (prefixWord ++ tailWord_2631461).sum := by decide
  have hdescent : baseEnd_2631461 < baseStart_2631461 := by decide
  rcases family_descends (prefixWord ++ tailWord_2631461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2631475 : List Nat := [1, 1, 1, 2, 7, 1, 2, 1, 1, 4, 2]
def baseStart_2631475 : Nat := 118140960795 + 2631475 * 2 ^ 59
def prefixEnd_2631475 : Nat := 4983230072969 + 3 ^ 40 * 2631475 * 2
def baseEnd_2631475 : Nat := 1351211505290197075660573

theorem tailTrace_2631475 : CollatzResearch.WordTrace tailWord_2631475 prefixEnd_2631475 1351211505290197075660573 := by
  unfold tailWord_2631475
  simp only [CollatzResearch.WordTrace]
  refine ⟨95977778141622969994943879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63985185427748646663295919 95977778141622969994943879)
  ·
    refine ⟨143966667212434454992415819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95977778141622969994943879 143966667212434454992415819)
    ·
      refine ⟨215950000818651682488623729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143966667212434454992415819 215950000818651682488623729)
      ·
        refine ⟨161962500613988761866467797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 215950000818651682488623729 161962500613988761866467797)
        ·
          refine ⟨3795996108140361606245339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 161962500613988761866467797 3795996108140361606245339)
          ·
            refine ⟨5693994162210542409368009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3795996108140361606245339 5693994162210542409368009)
            ·
              refine ⟨4270495621657906807026007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5693994162210542409368009 4270495621657906807026007)
              ·
                refine ⟨6405743432486860210539011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4270495621657906807026007 6405743432486860210539011)
                ·
                  refine ⟨9608615148730290315808517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6405743432486860210539011 9608615148730290315808517)
                  ·
                    refine ⟨1801615340386929434214097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9608615148730290315808517 1801615340386929434214097)
                    ·
                      refine ⟨1351211505290197075660573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1801615340386929434214097 1351211505290197075660573)
                      ·
                        rfl

theorem cell23_2631475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 2, 1, 1, 4, 2].length) (baseStart_2631475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2631475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2631475 prefixEnd_2631475 := by exact prefixLift 2631475
  have htrace : WordTrace (prefixWord ++ tailWord_2631475) baseStart_2631475 baseEnd_2631475 := by
    simpa [prefixWord, tailWord_2631475, baseEnd_2631475] using wordTrace_append hprefix tailTrace_2631475
  have hstable : (prefixWord ++ tailWord_2631475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2631475).length < 2 ^ (prefixWord ++ tailWord_2631475).sum := by decide
  have hdescent : baseEnd_2631475 < baseStart_2631475 := by decide
  rcases family_descends (prefixWord ++ tailWord_2631475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2631498 : List Nat := [3, 1, 2, 1, 1, 1, 6, 3, 5]
def baseStart_2631498 : Nat := 118140960795 + 2631498 * 2 ^ 59
def prefixEnd_2631498 : Nat := 4983230072969 + 3 ^ 40 * 2631498 * 2
def baseEnd_2631498 : Nat := 150135923927250053963663

theorem tailTrace_2631498 : CollatzResearch.WordTrace tailWord_2631498 prefixEnd_2631498 150135923927250053963663 := by
  unfold tailWord_2631498
  simp only [CollatzResearch.WordTrace]
  refine ⟨23994654255134911230757787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63985744680359763282020765 23994654255134911230757787)
  ·
    refine ⟨35991981382702366846136681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23994654255134911230757787 35991981382702366846136681)
    ·
      refine ⟨26993986037026775134602511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35991981382702366846136681 26993986037026775134602511)
      ·
        refine ⟨40490979055540162701903767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26993986037026775134602511 40490979055540162701903767)
        ·
          refine ⟨60736468583310244052855651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40490979055540162701903767 60736468583310244052855651)
          ·
            refine ⟨91104702874965366079283477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60736468583310244052855651 91104702874965366079283477)
            ·
              refine ⟨4270532947264001534966413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 91104702874965366079283477 4270532947264001534966413)
              ·
                refine ⟨1601449855224000575612405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4270532947264001534966413 1601449855224000575612405)
                ·
                  refine ⟨150135923927250053963663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1601449855224000575612405 150135923927250053963663)
                  ·
                    rfl

theorem cell23_2631498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6, 3, 5].length) (baseStart_2631498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2631498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2631498 prefixEnd_2631498 := by exact prefixLift 2631498
  have htrace : WordTrace (prefixWord ++ tailWord_2631498) baseStart_2631498 baseEnd_2631498 := by
    simpa [prefixWord, tailWord_2631498, baseEnd_2631498] using wordTrace_append hprefix tailTrace_2631498
  have hstable : (prefixWord ++ tailWord_2631498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2631498).length < 2 ^ (prefixWord ++ tailWord_2631498).sum := by decide
  have hdescent : baseEnd_2631498 < baseStart_2631498 := by decide
  rcases family_descends (prefixWord ++ tailWord_2631498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2631508 : List Nat := [2, 4, 1, 1, 3, 1, 1, 2, 2, 3, 3]
def baseStart_2631508 : Nat := 118140960795 + 2631508 * 2 ^ 59
def prefixEnd_2631508 : Nat := 4983230072969 + 3 ^ 40 * 2631508 * 2
def baseEnd_2631508 : Nat := 1351228450151795446547921

theorem tailTrace_2631508 : CollatzResearch.WordTrace tailWord_2631508 prefixEnd_2631508 1351228450151795446547921 := by
  unfold tailWord_2631508
  simp only [CollatzResearch.WordTrace]
  refine ⟨47989490875251708315447589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63985987833668944420596785 47989490875251708315447589)
  ·
    refine ⟨8998029539109695309146423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47989490875251708315447589 8998029539109695309146423)
    ·
      refine ⟨13497044308664542963719635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8998029539109695309146423 13497044308664542963719635)
      ·
        refine ⟨20245566462996814445579453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13497044308664542963719635 20245566462996814445579453)
        ·
          refine ⟨7592087423623805417092295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20245566462996814445579453 7592087423623805417092295)
          ·
            refine ⟨11388131135435708125638443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7592087423623805417092295 11388131135435708125638443)
            ·
              refine ⟨17082196703153562188457665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11388131135435708125638443 17082196703153562188457665)
              ·
                refine ⟨12811647527365171641343249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17082196703153562188457665 12811647527365171641343249)
                ·
                  refine ⟨9608735645523878731007437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12811647527365171641343249 9608735645523878731007437)
                  ·
                    refine ⟨3603275867071454524127789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9608735645523878731007437 3603275867071454524127789)
                    ·
                      refine ⟨1351228450151795446547921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3603275867071454524127789 1351228450151795446547921)
                      ·
                        rfl

theorem cell23_2631508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 2, 2, 3, 3].length) (baseStart_2631508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2631508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2631508 prefixEnd_2631508 := by exact prefixLift 2631508
  have htrace : WordTrace (prefixWord ++ tailWord_2631508) baseStart_2631508 baseEnd_2631508 := by
    simpa [prefixWord, tailWord_2631508, baseEnd_2631508] using wordTrace_append hprefix tailTrace_2631508
  have hstable : (prefixWord ++ tailWord_2631508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2631508).length < 2 ^ (prefixWord ++ tailWord_2631508).sum := by decide
  have hdescent : baseEnd_2631508 < baseStart_2631508 := by decide
  rcases family_descends (prefixWord ++ tailWord_2631508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2631541 : List Nat := [1, 3, 4, 1, 1, 1, 1, 1, 2, 8]
def baseStart_2631541 : Nat := 118140960795 + 2631541 * 2 ^ 59
def prefixEnd_2631541 : Nat := 4983230072969 + 3 ^ 40 * 2631541 * 2
def baseEnd_2631541 : Nat := 450415131671131272478423

theorem tailTrace_2631541 : CollatzResearch.WordTrace tailWord_2631541 prefixEnd_2631541 450415131671131272478423 := by
  unfold tailWord_2631541
  simp only [CollatzResearch.WordTrace]
  refine ⟨95980185359383863266846477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63986790239589242177897651 95980185359383863266846477)
  ·
    refine ⟨35992569509768948725067429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95980185359383863266846477 35992569509768948725067429)
    ·
      refine ⟨6748606783081677885950143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35992569509768948725067429 6748606783081677885950143)
      ·
        refine ⟨10122910174622516828925215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6748606783081677885950143 10122910174622516828925215)
        ·
          refine ⟨15184365261933775243387823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10122910174622516828925215 15184365261933775243387823)
          ·
            refine ⟨22776547892900662865081735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15184365261933775243387823 22776547892900662865081735)
            ·
              refine ⟨34164821839350994297622603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22776547892900662865081735 34164821839350994297622603)
              ·
                refine ⟨51247232759026491446433905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34164821839350994297622603 51247232759026491446433905)
                ·
                  refine ⟨38435424569269868584825429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51247232759026491446433905 38435424569269868584825429)
                  ·
                    refine ⟨450415131671131272478423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 38435424569269868584825429 450415131671131272478423)
                    ·
                      rfl

theorem cell23_2631541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_2631541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2631541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2631541 prefixEnd_2631541 := by exact prefixLift 2631541
  have htrace : WordTrace (prefixWord ++ tailWord_2631541) baseStart_2631541 baseEnd_2631541 := by
    simpa [prefixWord, tailWord_2631541, baseEnd_2631541] using wordTrace_append hprefix tailTrace_2631541
  have hstable : (prefixWord ++ tailWord_2631541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2631541).length < 2 ^ (prefixWord ++ tailWord_2631541).sum := by decide
  have hdescent : baseEnd_2631541 < baseStart_2631541 := by decide
  rcases family_descends (prefixWord ++ tailWord_2631541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2631575 : List Nat := [1, 1, 3, 3, 1, 5, 1, 1, 3, 4]
def baseStart_2631575 : Nat := 118140960795 + 2631575 * 2 ^ 59
def prefixEnd_2631575 : Nat := 4983230072969 + 3 ^ 40 * 2631575 * 2
def baseEnd_2631575 : Nat := 450420951118548894803371

theorem tailTrace_2631575 : CollatzResearch.WordTrace tailWord_2631575 prefixEnd_2631575 450420951118548894803371 := by
  unfold tailWord_2631575
  simp only [CollatzResearch.WordTrace]
  refine ⟨95981425441260687073584179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63987616960840458049056119 95981425441260687073584179)
  ·
    refine ⟨143972138161891030610376269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95981425441260687073584179 143972138161891030610376269)
    ·
      refine ⟨53989551810709136478891101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143972138161891030610376269 53989551810709136478891101)
      ·
        refine ⟨20246081929015926179584163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53989551810709136478891101 20246081929015926179584163)
        ·
          refine ⟨30369122893523889269376245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20246081929015926179584163 30369122893523889269376245)
          ·
            refine ⟨2847105271267864619004023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30369122893523889269376245 2847105271267864619004023)
            ·
              refine ⟨4270657906901796928506035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2847105271267864619004023 4270657906901796928506035)
              ·
                refine ⟨6405986860352695392759053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4270657906901796928506035 6405986860352695392759053)
                ·
                  refine ⟨2402245072632260772284645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6405986860352695392759053 2402245072632260772284645)
                  ·
                    refine ⟨450420951118548894803371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2402245072632260772284645 450420951118548894803371)
                    ·
                      rfl

theorem cell23_2631575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 1, 1, 3, 4].length) (baseStart_2631575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2631575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2631575 prefixEnd_2631575 := by exact prefixLift 2631575
  have htrace : WordTrace (prefixWord ++ tailWord_2631575) baseStart_2631575 baseEnd_2631575 := by
    simpa [prefixWord, tailWord_2631575, baseEnd_2631575] using wordTrace_append hprefix tailTrace_2631575
  have hstable : (prefixWord ++ tailWord_2631575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2631575).length < 2 ^ (prefixWord ++ tailWord_2631575).sum := by decide
  have hdescent : baseEnd_2631575 < baseStart_2631575 := by decide
  rcases family_descends (prefixWord ++ tailWord_2631575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2631588 : List Nat := [2, 3, 1, 2, 1, 4, 1, 3, 6]
def baseStart_2631588 : Nat := 118140960795 + 2631588 * 2 ^ 59
def prefixEnd_2631588 : Nat := 4983230072969 + 3 ^ 40 * 2631588 * 2
def baseEnd_2631588 : Nat := 150141058733795014838617

theorem tailTrace_2631588 : CollatzResearch.WordTrace tailWord_2631588 prefixEnd_2631588 150141058733795014838617 := by
  unfold tailWord_2631588
  simp only [CollatzResearch.WordTrace]
  refine ⟨47990949795106795146903709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63987933060142393529204945 47990949795106795146903709)
  ·
    refine ⟨17996606173165048180088891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47990949795106795146903709 17996606173165048180088891)
    ·
      refine ⟨26994909259747572270133337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17996606173165048180088891 26994909259747572270133337)
      ·
        refine ⟨20246181944810679202600003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26994909259747572270133337 20246181944810679202600003)
        ·
          refine ⟨30369272917216018803900005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20246181944810679202600003 30369272917216018803900005)
          ·
            refine ⟨5694238671978003525731251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30369272917216018803900005 5694238671978003525731251)
            ·
              refine ⟨8541358007967005288596877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5694238671978003525731251 8541358007967005288596877)
              ·
                refine ⟨3203009252987626983223829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8541358007967005288596877 3203009252987626983223829)
                ·
                  refine ⟨150141058733795014838617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3203009252987626983223829 150141058733795014838617)
                  ·
                    rfl

theorem cell23_2631588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 3, 6].length) (baseStart_2631588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2631588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2631588 prefixEnd_2631588 := by exact prefixLift 2631588
  have htrace : WordTrace (prefixWord ++ tailWord_2631588) baseStart_2631588 baseEnd_2631588 := by
    simpa [prefixWord, tailWord_2631588, baseEnd_2631588] using wordTrace_append hprefix tailTrace_2631588
  have hstable : (prefixWord ++ tailWord_2631588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2631588).length < 2 ^ (prefixWord ++ tailWord_2631588).sum := by decide
  have hdescent : baseEnd_2631588 < baseStart_2631588 := by decide
  rcases family_descends (prefixWord ++ tailWord_2631588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2631631 : List Nat := [1, 1, 2, 1, 1, 5, 1, 2, 3, 6]
def baseStart_2631631 : Nat := 118140960795 + 2631631 * 2 ^ 59
def prefixEnd_2631631 : Nat := 4983230072969 + 3 ^ 40 * 2631631 * 2
def baseEnd_2631631 : Nat := 450430536090766155103285

theorem tailTrace_2631631 : CollatzResearch.WordTrace tailWord_2631631 prefixEnd_2631631 450430536090766155103285 := by
  unfold tailWord_2631631
  simp only [CollatzResearch.WordTrace]
  refine ⟨95983467929057808637622747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63988978619371872425081831 95983467929057808637622747)
  ·
    refine ⟨143975201893586712956434121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95983467929057808637622747 143975201893586712956434121)
    ·
      refine ⟨107981401420190034717325591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143975201893586712956434121 107981401420190034717325591)
      ·
        refine ⟨161972102130285052075988387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107981401420190034717325591 161972102130285052075988387)
        ·
          refine ⟨242958153195427578113982581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161972102130285052075988387 242958153195427578113982581)
          ·
            refine ⟨22777326862071335448185867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 242958153195427578113982581 22777326862071335448185867)
            ·
              refine ⟨34165990293107003172278801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22777326862071335448185867 34165990293107003172278801)
              ·
                refine ⟨25624492719830252379209101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34165990293107003172278801 25624492719830252379209101)
                ·
                  refine ⟨9609184769936344642203413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25624492719830252379209101 9609184769936344642203413)
                  ·
                    refine ⟨450430536090766155103285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9609184769936344642203413 450430536090766155103285)
                    ·
                      rfl

theorem cell23_2631631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 2, 3, 6].length) (baseStart_2631631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2631631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2631631 prefixEnd_2631631 := by exact prefixLift 2631631
  have htrace : WordTrace (prefixWord ++ tailWord_2631631) baseStart_2631631 baseEnd_2631631 := by
    simpa [prefixWord, tailWord_2631631, baseEnd_2631631] using wordTrace_append hprefix tailTrace_2631631
  have hstable : (prefixWord ++ tailWord_2631631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2631631).length < 2 ^ (prefixWord ++ tailWord_2631631).sum := by decide
  have hdescent : baseEnd_2631631 < baseStart_2631631 := by decide
  rcases family_descends (prefixWord ++ tailWord_2631631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2631722 : List Nat := [3, 1, 4, 1, 2, 1, 1, 2, 4, 1, 3]
def baseStart_2631722 : Nat := 118140960795 + 2631722 * 2 ^ 59
def prefixEnd_2631722 : Nat := 4983230072969 + 3 ^ 40 * 2631722 * 2
def baseEnd_2631722 : Nat := 1351338335011857609271937

theorem tailTrace_2631722 : CollatzResearch.WordTrace tailWord_2631722 prefixEnd_2631722 1351338335011857609271937 := by
  unfold tailWord_2631722
  simp only [CollatzResearch.WordTrace]
  refine ⟨23996696742932032794796355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63991191314485420786123613 23996696742932032794796355)
  ·
    refine ⟨35995045114398049192194533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23996696742932032794796355 35995045114398049192194533)
    ·
      refine ⟨6749070958949634223536475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35995045114398049192194533 6749070958949634223536475)
      ·
        refine ⟨10123606438424451335304713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6749070958949634223536475 10123606438424451335304713)
        ·
          refine ⟨7592704828818338501478535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10123606438424451335304713 7592704828818338501478535)
          ·
            refine ⟨11389057243227507752217803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7592704828818338501478535 11389057243227507752217803)
            ·
              refine ⟨17083585864841261628326705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11389057243227507752217803 17083585864841261628326705)
              ·
                refine ⟨12812689398630946221245029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17083585864841261628326705 12812689398630946221245029)
                ·
                  refine ⟨2402379262243302416483443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12812689398630946221245029 2402379262243302416483443)
                  ·
                    refine ⟨3603568893364953624725165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2402379262243302416483443 3603568893364953624725165)
                    ·
                      refine ⟨1351338335011857609271937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3603568893364953624725165 1351338335011857609271937)
                      ·
                        rfl

theorem cell23_2631722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 2, 4, 1, 3].length) (baseStart_2631722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2631722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2631722 prefixEnd_2631722 := by exact prefixLift 2631722
  have htrace : WordTrace (prefixWord ++ tailWord_2631722) baseStart_2631722 baseEnd_2631722 := by
    simpa [prefixWord, tailWord_2631722, baseEnd_2631722] using wordTrace_append hprefix tailTrace_2631722
  have hstable : (prefixWord ++ tailWord_2631722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2631722).length < 2 ^ (prefixWord ++ tailWord_2631722).sum := by decide
  have hdescent : baseEnd_2631722 < baseStart_2631722 := by decide
  rcases family_descends (prefixWord ++ tailWord_2631722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2631766 : List Nat := [5, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2]
def baseStart_2631766 : Nat := 118140960795 + 2631766 * 2 ^ 59
def prefixEnd_2631766 : Nat := 4983230072969 + 3 ^ 40 * 2631766 * 2
def baseEnd_2631766 : Nat := 1351360928160655437121735

theorem tailTrace_2631766 : CollatzResearch.WordTrace tailWord_2631766 prefixEnd_2631766 1351360928160655437121735 := by
  unfold tailWord_2631766
  simp only [CollatzResearch.WordTrace]
  refine ⟨5999274486473045418361697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 63992261189045817795858101 5999274486473045418361697)
  ·
    refine ⟨4499455864854784063771273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5999274486473045418361697 4499455864854784063771273)
    ·
      refine ⟨3374591898641088047828455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4499455864854784063771273 3374591898641088047828455)
      ·
        refine ⟨5061887847961632071742683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3374591898641088047828455 5061887847961632071742683)
        ·
          refine ⟨7592831771942448107614025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5061887847961632071742683 7592831771942448107614025)
          ·
            refine ⟨5694623828956836080710519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7592831771942448107614025 5694623828956836080710519)
            ·
              refine ⟨8541935743435254121065779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5694623828956836080710519 8541935743435254121065779)
              ·
                refine ⟨12812903615152881181598669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8541935743435254121065779 12812903615152881181598669)
                ·
                  refine ⟨4804838855682330443099501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12812903615152881181598669 4804838855682330443099501)
                  ·
                    refine ⟨1801814570880873916162313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4804838855682330443099501 1801814570880873916162313)
                    ·
                      refine ⟨1351360928160655437121735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1801814570880873916162313 1351360928160655437121735)
                      ·
                        rfl

theorem cell23_2631766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2].length) (baseStart_2631766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2631766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2631766 prefixEnd_2631766 := by exact prefixLift 2631766
  have htrace : WordTrace (prefixWord ++ tailWord_2631766) baseStart_2631766 baseEnd_2631766 := by
    simpa [prefixWord, tailWord_2631766, baseEnd_2631766] using wordTrace_append hprefix tailTrace_2631766
  have hstable : (prefixWord ++ tailWord_2631766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2631766).length < 2 ^ (prefixWord ++ tailWord_2631766).sum := by decide
  have hdescent : baseEnd_2631766 < baseStart_2631766 := by decide
  rcases family_descends (prefixWord ++ tailWord_2631766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2631785 : List Nat := [1, 2, 1, 1, 1, 5, 2, 5, 5]
def baseStart_2631785 : Nat := 118140960795 + 2631785 * 2 ^ 59
def prefixEnd_2631785 : Nat := 4983230072969 + 3 ^ 40 * 2631785 * 2
def baseEnd_2631785 : Nat := 150152298254787873642683

theorem tailTrace_2631785 : CollatzResearch.WordTrace tailWord_2631785 prefixEnd_2631785 150152298254787873642683 := by
  unfold tailWord_2631785
  simp only [CollatzResearch.WordTrace]
  refine ⟨95989084770499892938728809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63992723180333261959152539 95989084770499892938728809)
  ·
    refine ⟨71991813577874919704046607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95989084770499892938728809 71991813577874919704046607)
    ·
      refine ⟨107987720366812379556069911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71991813577874919704046607 107987720366812379556069911)
      ·
        refine ⟨161981580550218569334104867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107987720366812379556069911 161981580550218569334104867)
        ·
          refine ⟨242972370825327854001157301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161981580550218569334104867 242972370825327854001157301)
          ·
            refine ⟨22778659764874486312608497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 242972370825327854001157301 22778659764874486312608497)
            ·
              refine ⟨17083994823655864734456373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22778659764874486312608497 17083994823655864734456373)
              ·
                refine ⟨1601624514717737318855285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17083994823655864734456373 1601624514717737318855285)
                ·
                  refine ⟨150152298254787873642683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1601624514717737318855285 150152298254787873642683)
                  ·
                    rfl

theorem cell23_2631785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 5, 5].length) (baseStart_2631785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2631785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2631785 prefixEnd_2631785 := by exact prefixLift 2631785
  have htrace : WordTrace (prefixWord ++ tailWord_2631785) baseStart_2631785 baseEnd_2631785 := by
    simpa [prefixWord, tailWord_2631785, baseEnd_2631785] using wordTrace_append hprefix tailTrace_2631785
  have hstable : (prefixWord ++ tailWord_2631785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2631785).length < 2 ^ (prefixWord ++ tailWord_2631785).sum := by decide
  have hdescent : baseEnd_2631785 < baseStart_2631785 := by decide
  rcases family_descends (prefixWord ++ tailWord_2631785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2631835 : List Nat := [1, 1, 1, 1, 1, 1, 2, 6, 1, 6, 2]
def baseStart_2631835 : Nat := 118140960795 + 2631835 * 2 ^ 59
def prefixEnd_2631835 : Nat := 4983230072969 + 3 ^ 40 * 2631835 * 2
def baseEnd_2631835 : Nat := 1351396358325815667158917

theorem tailTrace_2631835 : CollatzResearch.WordTrace tailWord_2631835 prefixEnd_2631835 1351396358325815667158917 := by
  unfold tailWord_2631835
  simp only [CollatzResearch.WordTrace]
  refine ⟨95990908420318751478048959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63993938946879167652032639 95990908420318751478048959)
  ·
    refine ⟨143986362630478127217073439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95990908420318751478048959 143986362630478127217073439)
    ·
      refine ⟨215979543945717190825610159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143986362630478127217073439 215979543945717190825610159)
      ·
        refine ⟨323969315918575786238415239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215979543945717190825610159 323969315918575786238415239)
        ·
          refine ⟨485953973877863679357622859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 323969315918575786238415239 485953973877863679357622859)
          ·
            refine ⟨728930960816795519036434289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 485953973877863679357622859 728930960816795519036434289)
            ·
              refine ⟨546698220612596639277325717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 728930960816795519036434289 546698220612596639277325717)
              ·
                refine ⟨25626479091215467466124643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 546698220612596639277325717 25626479091215467466124643)
                ·
                  refine ⟨38439718636823201199186965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25626479091215467466124643 38439718636823201199186965)
                  ·
                    refine ⟨1801861811101087556211889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 38439718636823201199186965 1801861811101087556211889)
                    ·
                      refine ⟨1351396358325815667158917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1801861811101087556211889 1351396358325815667158917)
                      ·
                        rfl

theorem cell23_2631835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6, 1, 6, 2].length) (baseStart_2631835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2631835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2631835 prefixEnd_2631835 := by exact prefixLift 2631835
  have htrace : WordTrace (prefixWord ++ tailWord_2631835) baseStart_2631835 baseEnd_2631835 := by
    simpa [prefixWord, tailWord_2631835, baseEnd_2631835] using wordTrace_append hprefix tailTrace_2631835
  have hstable : (prefixWord ++ tailWord_2631835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2631835).length < 2 ^ (prefixWord ++ tailWord_2631835).sum := by decide
  have hdescent : baseEnd_2631835 < baseStart_2631835 := by decide
  rcases family_descends (prefixWord ++ tailWord_2631835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2631845 : List Nat := [1, 3, 1, 2, 1, 3, 1, 2, 5, 4]
def baseStart_2631845 : Nat := 118140960795 + 2631845 * 2 ^ 59
def prefixEnd_2631845 : Nat := 4983230072969 + 3 ^ 40 * 2631845 * 2
def baseEnd_2631845 : Nat := 450467164377453542677957

theorem tailTrace_2631845 : CollatzResearch.WordTrace tailWord_2631845 prefixEnd_2631845 450467164377453542677957 := by
  unfold tailWord_2631845
  simp only [CollatzResearch.WordTrace]
  refine ⟨95991273150282523185912989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63994182100188348790608659 95991273150282523185912989)
  ·
    refine ⟨35996727431355946194717371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95991273150282523185912989 35996727431355946194717371)
    ·
      refine ⟨53995091147033919292076057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35996727431355946194717371 53995091147033919292076057)
      ·
        refine ⟨40496318360275439469057043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53995091147033919292076057 40496318360275439469057043)
        ·
          refine ⟨60744477540413159203585565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40496318360275439469057043 60744477540413159203585565)
          ·
            refine ⟨22779179077654934701344587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60744477540413159203585565 22779179077654934701344587)
            ·
              refine ⟨34168768616482402052016881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22779179077654934701344587 34168768616482402052016881)
              ·
                refine ⟨25626576462361801539012661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34168768616482402052016881 25626576462361801539012661)
                ·
                  refine ⟨2402491543346418894282437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25626576462361801539012661 2402491543346418894282437)
                  ·
                    refine ⟨450467164377453542677957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2402491543346418894282437 450467164377453542677957)
                    ·
                      rfl

theorem cell23_2631845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 2, 5, 4].length) (baseStart_2631845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2631845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2631845 prefixEnd_2631845 := by exact prefixLift 2631845
  have htrace : WordTrace (prefixWord ++ tailWord_2631845) baseStart_2631845 baseEnd_2631845 := by
    simpa [prefixWord, tailWord_2631845, baseEnd_2631845] using wordTrace_append hprefix tailTrace_2631845
  have hstable : (prefixWord ++ tailWord_2631845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2631845).length < 2 ^ (prefixWord ++ tailWord_2631845).sum := by decide
  have hdescent : baseEnd_2631845 < baseStart_2631845 := by decide
  rcases family_descends (prefixWord ++ tailWord_2631845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2631855 : List Nat := [1, 1, 2, 1, 2, 3, 1, 3, 4, 2, 3]
def baseStart_2631855 : Nat := 118140960795 + 2631855 * 2 ^ 59
def prefixEnd_2631855 : Nat := 4983230072969 + 3 ^ 40 * 2631855 * 2
def baseEnd_2631855 : Nat := 1351406627938905588908825

theorem tailTrace_2631855 : CollatzResearch.WordTrace tailWord_2631855 prefixEnd_2631855 1351406627938905588908825 := by
  unfold tailWord_2631855
  simp only [CollatzResearch.WordTrace]
  refine ⟨95991637880246294893777019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63994425253497529929184679 95991637880246294893777019)
  ·
    refine ⟨143987456820369442340665529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95991637880246294893777019 143987456820369442340665529)
    ·
      refine ⟨107990592615277081755499147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143987456820369442340665529 107990592615277081755499147)
      ·
        refine ⟨161985888922915622633248721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107990592615277081755499147 161985888922915622633248721)
        ·
          refine ⟨121489416692186716974936541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 161985888922915622633248721 121489416692186716974936541)
          ·
            refine ⟨45558531259570018865601203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 121489416692186716974936541 45558531259570018865601203)
            ·
              refine ⟨68337796889355028298401805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45558531259570018865601203 68337796889355028298401805)
              ·
                refine ⟨25626673833508135611900677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68337796889355028298401805 25626673833508135611900677)
                ·
                  refine ⟨4805001343782775427231377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25626673833508135611900677 4805001343782775427231377)
                  ·
                    refine ⟨3603751007837081570423533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4805001343782775427231377 3603751007837081570423533)
                    ·
                      refine ⟨1351406627938905588908825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3603751007837081570423533 1351406627938905588908825)
                      ·
                        rfl

theorem cell23_2631855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 3, 4, 2, 3].length) (baseStart_2631855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2631855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2631855 prefixEnd_2631855 := by exact prefixLift 2631855
  have htrace : WordTrace (prefixWord ++ tailWord_2631855) baseStart_2631855 baseEnd_2631855 := by
    simpa [prefixWord, tailWord_2631855, baseEnd_2631855] using wordTrace_append hprefix tailTrace_2631855
  have hstable : (prefixWord ++ tailWord_2631855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2631855).length < 2 ^ (prefixWord ++ tailWord_2631855).sum := by decide
  have hdescent : baseEnd_2631855 < baseStart_2631855 := by decide
  rcases family_descends (prefixWord ++ tailWord_2631855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2631888 : List Nat := [2, 1, 1, 1, 1, 2, 1, 1, 4, 9]
def baseStart_2631888 : Nat := 118140960795 + 2631888 * 2 ^ 59
def prefixEnd_2631888 : Nat := 4983230072969 + 3 ^ 40 * 2631888 * 2
def baseEnd_2631888 : Nat := 450474524266834653265391

theorem tailTrace_2631888 : CollatzResearch.WordTrace tailWord_2631888 prefixEnd_2631888 450474524266834653265391 := by
  unfold tailWord_2631888
  simp only [CollatzResearch.WordTrace]
  refine ⟨47996420744563370764864159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63995227659417827686485545 47996420744563370764864159)
  ·
    refine ⟨71994631116845056147296239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47996420744563370764864159 71994631116845056147296239)
    ·
      refine ⟨107991946675267584220944359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71994631116845056147296239 107991946675267584220944359)
      ·
        refine ⟨161987920012901376331416539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107991946675267584220944359 161987920012901376331416539)
        ·
          refine ⟨242981880019352064497124809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161987920012901376331416539 242981880019352064497124809)
          ·
            refine ⟨182236410014514048372843607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 242981880019352064497124809 182236410014514048372843607)
            ·
              refine ⟨273354615021771072559265411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 182236410014514048372843607 273354615021771072559265411)
              ·
                refine ⟨410031922532656608838898117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 273354615021771072559265411 410031922532656608838898117)
                ·
                  refine ⟨76880985474873114157293397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 410031922532656608838898117 76880985474873114157293397)
                  ·
                    refine ⟨450474524266834653265391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 76880985474873114157293397 450474524266834653265391)
                    ·
                      rfl

theorem cell23_2631888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 4, 9].length) (baseStart_2631888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2631888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2631888 prefixEnd_2631888 := by exact prefixLift 2631888
  have htrace : WordTrace (prefixWord ++ tailWord_2631888) baseStart_2631888 baseEnd_2631888 := by
    simpa [prefixWord, tailWord_2631888, baseEnd_2631888] using wordTrace_append hprefix tailTrace_2631888
  have hstable : (prefixWord ++ tailWord_2631888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2631888).length < 2 ^ (prefixWord ++ tailWord_2631888).sum := by decide
  have hdescent : baseEnd_2631888 < baseStart_2631888 := by decide
  rcases family_descends (prefixWord ++ tailWord_2631888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2631896 : List Nat := [2, 1, 2, 2, 4, 3, 1, 3, 1, 4]
def baseStart_2631896 : Nat := 118140960795 + 2631896 * 2 ^ 59
def prefixEnd_2631896 : Nat := 4983230072969 + 3 ^ 40 * 2631896 * 2
def baseEnd_2631896 : Nat := 450475893548579976165379

theorem tailTrace_2631896 : CollatzResearch.WordTrace tailWord_2631896 prefixEnd_2631896 450475893548579976165379 := by
  unfold tailWord_2631896
  simp only [CollatzResearch.WordTrace]
  refine ⟨47996566636548879448009771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63995422182065172597346361 47996566636548879448009771)
  ·
    refine ⟨71994849954823319172014657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47996566636548879448009771 71994849954823319172014657)
    ·
      refine ⟨53996137466117489379010993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71994849954823319172014657 53996137466117489379010993)
      ·
        refine ⟨40497103099588117034258245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53996137466117489379010993 40497103099588117034258245)
        ·
          refine ⟨7593206831172771943923421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40497103099588117034258245 7593206831172771943923421)
          ·
            refine ⟨2847452561689789478971283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7593206831172771943923421 2847452561689789478971283)
            ·
              refine ⟨4271178842534684218456925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2847452561689789478971283 4271178842534684218456925)
              ·
                refine ⟨1601692065950506581921347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4271178842534684218456925 1601692065950506581921347)
                ·
                  refine ⟨2402538098925759872882021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1601692065950506581921347 2402538098925759872882021)
                  ·
                    refine ⟨450475893548579976165379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2402538098925759872882021 450475893548579976165379)
                    ·
                      rfl

theorem cell23_2631896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 1, 3, 1, 4].length) (baseStart_2631896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2631896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2631896 prefixEnd_2631896 := by exact prefixLift 2631896
  have htrace : WordTrace (prefixWord ++ tailWord_2631896) baseStart_2631896 baseEnd_2631896 := by
    simpa [prefixWord, tailWord_2631896, baseEnd_2631896] using wordTrace_append hprefix tailTrace_2631896
  have hstable : (prefixWord ++ tailWord_2631896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2631896).length < 2 ^ (prefixWord ++ tailWord_2631896).sum := by decide
  have hdescent : baseEnd_2631896 < baseStart_2631896 := by decide
  rcases family_descends (prefixWord ++ tailWord_2631896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2631919 : List Nat := [1, 1, 2, 1, 6, 1, 3, 1, 3, 1, 3]
def baseStart_2631919 : Nat := 118140960795 + 2631919 * 2 ^ 59
def prefixEnd_2631919 : Nat := 4983230072969 + 3 ^ 40 * 2631919 * 2
def baseEnd_2631919 : Nat := 1351439490700793338508531

theorem tailTrace_2631919 : CollatzResearch.WordTrace tailWord_2631919 prefixEnd_2631919 1351439490700793338508531 := by
  unfold tailWord_2631919
  simp only [CollatzResearch.WordTrace]
  refine ⟨95993972152014433824106811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63995981434676289216071207 95993972152014433824106811)
  ·
    refine ⟨143990958228021650736160217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95993972152014433824106811 143990958228021650736160217)
    ·
      refine ⟨107993218671016238052120163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143990958228021650736160217 107993218671016238052120163)
      ·
        refine ⟨161989828006524357078180245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107993218671016238052120163 161989828006524357078180245)
        ·
          refine ⟨7593273187805829238039699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 161989828006524357078180245 7593273187805829238039699)
          ·
            refine ⟨11389909781708743857059549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7593273187805829238039699 11389909781708743857059549)
            ·
              refine ⟨4271216168140778946397331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11389909781708743857059549 4271216168140778946397331)
              ·
                refine ⟨6406824252211168419595997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4271216168140778946397331 6406824252211168419595997)
                ·
                  refine ⟨2402559094579188157348499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6406824252211168419595997 2402559094579188157348499)
                  ·
                    refine ⟨3603838641868782236022749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2402559094579188157348499 3603838641868782236022749)
                    ·
                      refine ⟨1351439490700793338508531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3603838641868782236022749 1351439490700793338508531)
                      ·
                        rfl

theorem cell23_2631919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3, 1, 3, 1, 3].length) (baseStart_2631919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2631919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2631919 prefixEnd_2631919 := by exact prefixLift 2631919
  have htrace : WordTrace (prefixWord ++ tailWord_2631919) baseStart_2631919 baseEnd_2631919 := by
    simpa [prefixWord, tailWord_2631919, baseEnd_2631919] using wordTrace_append hprefix tailTrace_2631919
  have hstable : (prefixWord ++ tailWord_2631919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2631919).length < 2 ^ (prefixWord ++ tailWord_2631919).sum := by decide
  have hdescent : baseEnd_2631919 < baseStart_2631919 := by decide
  rcases family_descends (prefixWord ++ tailWord_2631919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2631935 : List Nat := [1, 1, 2, 2, 1, 4, 2, 3, 1, 6]
def baseStart_2631935 : Nat := 118140960795 + 2631935 * 2 ^ 59
def prefixEnd_2631935 : Nat := 4983230072969 + 3 ^ 40 * 2631935 * 2
def baseEnd_2631935 : Nat := 450482568797088425302819

theorem tailTrace_2631935 : CollatzResearch.WordTrace tailWord_2631935 prefixEnd_2631935 450482568797088425302819 := by
  unfold tailWord_2631935
  simp only [CollatzResearch.WordTrace]
  refine ⟨95994555719956468556689259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63996370479970979037792839 95994555719956468556689259)
  ·
    refine ⟨143991833579934702835033889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95994555719956468556689259 143991833579934702835033889)
    ·
      refine ⟨107993875184951027126275417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143991833579934702835033889 107993875184951027126275417)
      ·
        refine ⟨80995406388713270344706563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107993875184951027126275417 80995406388713270344706563)
        ·
          refine ⟨121493109583069905517059845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80995406388713270344706563 121493109583069905517059845)
          ·
            refine ⟨22779958046825607284448721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 121493109583069905517059845 22779958046825607284448721)
            ·
              refine ⟨17084968535119205463336541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22779958046825607284448721 17084968535119205463336541)
              ·
                refine ⟨6406863200669702048751203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17084968535119205463336541 6406863200669702048751203)
                ·
                  refine ⟨9610294801004553073126805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6406863200669702048751203 9610294801004553073126805)
                  ·
                    refine ⟨450482568797088425302819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9610294801004553073126805 450482568797088425302819)
                    ·
                      rfl

theorem cell23_2631935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 3, 1, 6].length) (baseStart_2631935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2631935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2631935 prefixEnd_2631935 := by exact prefixLift 2631935
  have htrace : WordTrace (prefixWord ++ tailWord_2631935) baseStart_2631935 baseEnd_2631935 := by
    simpa [prefixWord, tailWord_2631935, baseEnd_2631935] using wordTrace_append hprefix tailTrace_2631935
  have hstable : (prefixWord ++ tailWord_2631935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2631935).length < 2 ^ (prefixWord ++ tailWord_2631935).sum := by decide
  have hdescent : baseEnd_2631935 < baseStart_2631935 := by decide
  rcases family_descends (prefixWord ++ tailWord_2631935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2631965 : List Nat := [1, 4, 2, 3, 13]
def baseStart_2631965 : Nat := 118140960795 + 2631965 * 2 ^ 59
def prefixEnd_2631965 : Nat := 4983230072969 + 3 ^ 40 * 2631965 * 2
def baseEnd_2631965 : Nat := 1853858862566392535711

theorem tailTrace_2631965 : CollatzResearch.WordTrace tailWord_2631965 prefixEnd_2631965 1853858862566392535711 := by
  unfold tailWord_2631965
  simp only [CollatzResearch.WordTrace]
  refine ⟨95995649909847783680281349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63997099939898522453520899 95995649909847783680281349)
  ·
    refine ⟨17999184358096459440052753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95995649909847783680281349 17999184358096459440052753)
    ·
      refine ⟨13499388268572344580039565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17999184358096459440052753 13499388268572344580039565)
      ·
        refine ⟨5062270600714629217514837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13499388268572344580039565 5062270600714629217514837)
        ·
          refine ⟨1853858862566392535711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 5062270600714629217514837 1853858862566392535711)
          ·
            rfl

theorem cell23_2631965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 13].length) (baseStart_2631965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2631965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2631965 prefixEnd_2631965 := by exact prefixLift 2631965
  have htrace : WordTrace (prefixWord ++ tailWord_2631965) baseStart_2631965 baseEnd_2631965 := by
    simpa [prefixWord, tailWord_2631965, baseEnd_2631965] using wordTrace_append hprefix tailTrace_2631965
  have hstable : (prefixWord ++ tailWord_2631965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2631965).length < 2 ^ (prefixWord ++ tailWord_2631965).sum := by decide
  have hdescent : baseEnd_2631965 < baseStart_2631965 := by decide
  rcases family_descends (prefixWord ++ tailWord_2631965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2631970 : List Nat := [3, 3, 1, 1, 3, 3, 2, 2, 1, 1, 3]
def baseStart_2631970 : Nat := 118140960795 + 2631970 * 2 ^ 59
def prefixEnd_2631970 : Nat := 4983230072969 + 3 ^ 40 * 2631970 * 2
def baseEnd_2631970 : Nat := 1351465678214172638970797

theorem tailTrace_2631970 : CollatzResearch.WordTrace tailWord_2631970 prefixEnd_2631970 1351465678214172638970797 := by
  unfold tailWord_2631970
  simp only [CollatzResearch.WordTrace]
  refine ⟨23998958068707417383553341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63997221516553113022808909 23998958068707417383553341)
  ·
    refine ⟨8999609275765281518832503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23998958068707417383553341 8999609275765281518832503)
    ·
      refine ⟨13499413913647922278248755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8999609275765281518832503 13499413913647922278248755)
      ·
        refine ⟨20249120870471883417373133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13499413913647922278248755 20249120870471883417373133)
        ·
          refine ⟨7593420326426956281514925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20249120870471883417373133 7593420326426956281514925)
          ·
            refine ⟨2847532622410108605568097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7593420326426956281514925 2847532622410108605568097)
            ·
              refine ⟨2135649466807581454176073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2847532622410108605568097 2135649466807581454176073)
              ·
                refine ⟨1601737100105686090632055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2135649466807581454176073 1601737100105686090632055)
                ·
                  refine ⟨2402605650158529135948083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1601737100105686090632055 2402605650158529135948083)
                  ·
                    refine ⟨3603908475237793703922125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2402605650158529135948083 3603908475237793703922125)
                    ·
                      refine ⟨1351465678214172638970797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3603908475237793703922125 1351465678214172638970797)
                      ·
                        rfl

theorem cell23_2631970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 2, 2, 1, 1, 3].length) (baseStart_2631970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2631970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2631970 prefixEnd_2631970 := by exact prefixLift 2631970
  have htrace : WordTrace (prefixWord ++ tailWord_2631970) baseStart_2631970 baseEnd_2631970 := by
    simpa [prefixWord, tailWord_2631970, baseEnd_2631970] using wordTrace_append hprefix tailTrace_2631970
  have hstable : (prefixWord ++ tailWord_2631970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2631970).length < 2 ^ (prefixWord ++ tailWord_2631970).sum := by decide
  have hdescent : baseEnd_2631970 < baseStart_2631970 := by decide
  rcases family_descends (prefixWord ++ tailWord_2631970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2631992 : List Nat := [2, 1, 2, 1, 3, 1, 3, 3, 1, 3, 3]
def baseStart_2631992 : Nat := 118140960795 + 2631992 * 2 ^ 59
def prefixEnd_2631992 : Nat := 4983230072969 + 3 ^ 40 * 2631992 * 2
def baseEnd_2631992 : Nat := 1351476974788571552895695

theorem tailTrace_2631992 : CollatzResearch.WordTrace tailWord_2631992 prefixEnd_2631992 1351476974788571552895695 := by
  unfold tailWord_2631992
  simp only [CollatzResearch.WordTrace]
  refine ⟨47998317340374983645757115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63997756453833311527676153 47998317340374983645757115)
  ·
    refine ⟨71997476010562475468635673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47998317340374983645757115 71997476010562475468635673)
    ·
      refine ⟨53998107007921856601476755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71997476010562475468635673 53998107007921856601476755)
      ·
        refine ⟨80997160511882784902215133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53998107007921856601476755 80997160511882784902215133)
        ·
          refine ⟨30373935191956044338330675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80997160511882784902215133 30373935191956044338330675)
          ·
            refine ⟨45560902787934066507496013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30373935191956044338330675 45560902787934066507496013)
            ·
              refine ⟨17085338545475274940311005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45560902787934066507496013 17085338545475274940311005)
              ·
                refine ⟨6407001954553228102616627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17085338545475274940311005 6407001954553228102616627)
                ·
                  refine ⟨9610502931829842153924941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6407001954553228102616627 9610502931829842153924941)
                  ·
                    refine ⟨3603938599436190807721853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9610502931829842153924941 3603938599436190807721853)
                    ·
                      refine ⟨1351476974788571552895695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3603938599436190807721853 1351476974788571552895695)
                      ·
                        rfl

theorem cell23_2631992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 3, 1, 3, 3].length) (baseStart_2631992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2631992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2631992 prefixEnd_2631992 := by exact prefixLift 2631992
  have htrace : WordTrace (prefixWord ++ tailWord_2631992) baseStart_2631992 baseEnd_2631992 := by
    simpa [prefixWord, tailWord_2631992, baseEnd_2631992] using wordTrace_append hprefix tailTrace_2631992
  have hstable : (prefixWord ++ tailWord_2631992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2631992).length < 2 ^ (prefixWord ++ tailWord_2631992).sum := by decide
  have hdescent : baseEnd_2631992 < baseStart_2631992 := by decide
  rcases family_descends (prefixWord ++ tailWord_2631992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2632015 : List Nat := [1, 1, 2, 1, 1, 2, 1, 4, 1, 5, 4]
def baseStart_2632015 : Nat := 118140960795 + 2632015 * 2 ^ 59
def prefixEnd_2632015 : Nat := 4983230072969 + 3 ^ 40 * 2632015 * 2
def baseEnd_2632015 : Nat := 1351488784843624962908089

theorem tailTrace_2632015 : CollatzResearch.WordTrace tailWord_2632015 prefixEnd_2632015 1351488784843624962908089 := by
  unfold tailWord_2632015
  simp only [CollatzResearch.WordTrace]
  refine ⟨95997473559666642219601499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63998315706444428146400999 95997473559666642219601499)
  ·
    refine ⟨143996210339499963329402249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95997473559666642219601499 143996210339499963329402249)
    ·
      refine ⟨107997157754624972497051687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143996210339499963329402249 107997157754624972497051687)
      ·
        refine ⟨161995736631937458745577531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107997157754624972497051687 161995736631937458745577531)
        ·
          refine ⟨242993604947906188118366297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161995736631937458745577531 242993604947906188118366297)
          ·
            refine ⟨182245203710929641088774723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 242993604947906188118366297 182245203710929641088774723)
            ·
              refine ⟨273367805566394461633162085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 182245203710929641088774723 273367805566394461633162085)
              ·
                refine ⟨51256463543698961556217891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 273367805566394461633162085 51256463543698961556217891)
                ·
                  refine ⟨76884695315548442334326837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51256463543698961556217891 76884695315548442334326837)
                  ·
                    refine ⟨7207940185832666468843141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 76884695315548442334326837 7207940185832666468843141)
                    ·
                      refine ⟨1351488784843624962908089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7207940185832666468843141 1351488784843624962908089)
                      ·
                        rfl

theorem cell23_2632015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 5, 4].length) (baseStart_2632015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2632015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2632015 prefixEnd_2632015 := by exact prefixLift 2632015
  have htrace : WordTrace (prefixWord ++ tailWord_2632015) baseStart_2632015 baseEnd_2632015 := by
    simpa [prefixWord, tailWord_2632015, baseEnd_2632015] using wordTrace_append hprefix tailTrace_2632015
  have hstable : (prefixWord ++ tailWord_2632015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2632015).length < 2 ^ (prefixWord ++ tailWord_2632015).sum := by decide
  have hdescent : baseEnd_2632015 < baseStart_2632015 := by decide
  rcases family_descends (prefixWord ++ tailWord_2632015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2632030 : List Nat := [4, 4, 2, 1, 1, 1, 1, 2, 1, 1, 5]
def baseStart_2632030 : Nat := 118140960795 + 2632030 * 2 ^ 59
def prefixEnd_2632030 : Nat := 4983230072969 + 3 ^ 40 * 2632030 * 2
def baseEnd_2632030 : Nat := 1351496487053442404220521

theorem tailTrace_2632030 : CollatzResearch.WordTrace tailWord_2632030 prefixEnd_2632030 1351496487053442404220521 := by
  unfold tailWord_2632030
  simp only [CollatzResearch.WordTrace]
  refine ⟨11999752581826537472674693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63998680436408199854265029 11999752581826537472674693)
  ·
    refine ⟨2249953609092475776126505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11999752581826537472674693 2249953609092475776126505)
    ·
      refine ⟨1687465206819356832094879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2249953609092475776126505 1687465206819356832094879)
      ·
        refine ⟨2531197810229035248142319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1687465206819356832094879 2531197810229035248142319)
        ·
          refine ⟨3796796715343552872213479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2531197810229035248142319 3796796715343552872213479)
          ·
            refine ⟨5695195073015329308320219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3796796715343552872213479 5695195073015329308320219)
            ·
              refine ⟨8542792609522993962480329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5695195073015329308320219 8542792609522993962480329)
              ·
                refine ⟨6407094457142245471860247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8542792609522993962480329 6407094457142245471860247)
                ·
                  refine ⟨9610641685713368207790371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6407094457142245471860247 9610641685713368207790371)
                  ·
                    refine ⟨14415962528570052311685557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9610641685713368207790371 14415962528570052311685557)
                    ·
                      refine ⟨1351496487053442404220521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14415962528570052311685557 1351496487053442404220521)
                      ·
                        rfl

theorem cell23_2632030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_2632030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2632030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2632030 prefixEnd_2632030 := by exact prefixLift 2632030
  have htrace : WordTrace (prefixWord ++ tailWord_2632030) baseStart_2632030 baseEnd_2632030 := by
    simpa [prefixWord, tailWord_2632030, baseEnd_2632030] using wordTrace_append hprefix tailTrace_2632030
  have hstable : (prefixWord ++ tailWord_2632030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2632030).length < 2 ^ (prefixWord ++ tailWord_2632030).sum := by decide
  have hdescent : baseEnd_2632030 < baseStart_2632030 := by decide
  rcases family_descends (prefixWord ++ tailWord_2632030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2632053 : List Nat := [1, 3, 4, 1, 2, 2, 2, 2, 1, 3, 2]
def baseStart_2632053 : Nat := 118140960795 + 2632053 * 2 ^ 59
def prefixEnd_2632053 : Nat := 4983230072969 + 3 ^ 40 * 2632053 * 2
def baseEnd_2632053 : Nat := 1351508297108495814232915

theorem tailTrace_2632053 : CollatzResearch.WordTrace tailWord_2632053 prefixEnd_2632053 1351508297108495814232915 := by
  unfold tailWord_2632053
  simp only [CollatzResearch.WordTrace]
  refine ⟨95998859533528974709484813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63999239689019316472989875 95998859533528974709484813)
  ·
    refine ⟨35999572325073365516056805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95998859533528974709484813 35999572325073365516056805)
    ·
      refine ⟨6749919810951256034260651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35999572325073365516056805 6749919810951256034260651)
      ·
        refine ⟨10124879716426884051390977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6749919810951256034260651 10124879716426884051390977)
        ·
          refine ⟨7593659787320163038543233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10124879716426884051390977 7593659787320163038543233)
          ·
            refine ⟨5695244840490122278907425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7593659787320163038543233 5695244840490122278907425)
            ·
              refine ⟨4271433630367591709180569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5695244840490122278907425 4271433630367591709180569)
              ·
                refine ⟨3203575222775693781885427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4271433630367591709180569 3203575222775693781885427)
                ·
                  refine ⟨4805362834163540672828141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3203575222775693781885427 4805362834163540672828141)
                  ·
                    refine ⟨1802011062811327752310553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4805362834163540672828141 1802011062811327752310553)
                    ·
                      refine ⟨1351508297108495814232915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1802011062811327752310553 1351508297108495814232915)
                      ·
                        rfl

theorem cell23_2632053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2, 2, 1, 3, 2].length) (baseStart_2632053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2632053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2632053 prefixEnd_2632053 := by exact prefixLift 2632053
  have htrace : WordTrace (prefixWord ++ tailWord_2632053) baseStart_2632053 baseEnd_2632053 := by
    simpa [prefixWord, tailWord_2632053, baseEnd_2632053] using wordTrace_append hprefix tailTrace_2632053
  have hstable : (prefixWord ++ tailWord_2632053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2632053).length < 2 ^ (prefixWord ++ tailWord_2632053).sum := by decide
  have hdescent : baseEnd_2632053 < baseStart_2632053 := by decide
  rcases family_descends (prefixWord ++ tailWord_2632053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2632055 : List Nat := [1, 1, 3, 1, 1, 2, 2, 3, 9]
def baseStart_2632055 : Nat := 118140960795 + 2632055 * 2 ^ 59
def prefixEnd_2632055 : Nat := 4983230072969 + 3 ^ 40 * 2632055 * 2
def baseEnd_2632055 : Nat := 150167702674422756267545

theorem tailTrace_2632055 : CollatzResearch.WordTrace tailWord_2632055 prefixEnd_2632055 150167702674422756267545 := by
  unfold tailWord_2632055
  simp only [CollatzResearch.WordTrace]
  refine ⟨95998932479521729051057619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63999288319681152700705079 95998932479521729051057619)
  ·
    refine ⟨143998398719282593576586429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95998932479521729051057619 143998398719282593576586429)
    ·
      refine ⟨53999399519730972591219911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143998398719282593576586429 53999399519730972591219911)
      ·
        refine ⟨80999099279596458886829867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53999399519730972591219911 80999099279596458886829867)
        ·
          refine ⟨121498648919394688330244801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80999099279596458886829867 121498648919394688330244801)
          ·
            refine ⟨91123986689546016247683601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121498648919394688330244801 91123986689546016247683601)
            ·
              refine ⟨68342990017159512185762701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91123986689546016247683601 68342990017159512185762701)
              ·
                refine ⟨25628621256434817069661013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68342990017159512185762701 25628621256434817069661013)
                ·
                  refine ⟨150167702674422756267545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 25628621256434817069661013 150167702674422756267545)
                  ·
                    rfl

theorem cell23_2632055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 3, 9].length) (baseStart_2632055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2632055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2632055 prefixEnd_2632055 := by exact prefixLift 2632055
  have htrace : WordTrace (prefixWord ++ tailWord_2632055) baseStart_2632055 baseEnd_2632055 := by
    simpa [prefixWord, tailWord_2632055, baseEnd_2632055] using wordTrace_append hprefix tailTrace_2632055
  have hstable : (prefixWord ++ tailWord_2632055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2632055).length < 2 ^ (prefixWord ++ tailWord_2632055).sum := by decide
  have hdescent : baseEnd_2632055 < baseStart_2632055 := by decide
  rcases family_descends (prefixWord ++ tailWord_2632055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2632119 : List Nat := [1, 1, 3, 1, 3, 4, 2, 1, 2, 5]
def baseStart_2632119 : Nat := 118140960795 + 2632119 * 2 ^ 59
def prefixEnd_2632119 : Nat := 4983230072969 + 3 ^ 40 * 2632119 * 2
def baseEnd_2632119 : Nat := 450514062277230852002537

theorem tailTrace_2632119 : CollatzResearch.WordTrace tailWord_2632119 prefixEnd_2632119 450514062277230852002537 := by
  unfold tailWord_2632119
  simp only [CollatzResearch.WordTrace]
  refine ⟨96001266751289867981387411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64000844500859911987591607 96001266751289867981387411)
  ·
    refine ⟨144001900126934801972081117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96001266751289867981387411 144001900126934801972081117)
    ·
      refine ⟨54000712547600550739530419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144001900126934801972081117 54000712547600550739530419)
      ·
        refine ⟨81001068821400826109295629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54000712547600550739530419 81001068821400826109295629)
        ·
          refine ⟨30375400808025309790985861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81001068821400826109295629 30375400808025309790985861)
          ·
            refine ⟨5695387651504745585809849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30375400808025309790985861 5695387651504745585809849)
            ·
              refine ⟨4271540738628559189357387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5695387651504745585809849 4271540738628559189357387)
              ·
                refine ⟨6407311107942838784036081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4271540738628559189357387 6407311107942838784036081)
                ·
                  refine ⟨4805483330957129088027061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6407311107942838784036081 4805483330957129088027061)
                  ·
                    refine ⟨450514062277230852002537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4805483330957129088027061 450514062277230852002537)
                    ·
                      rfl

theorem cell23_2632119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 1, 2, 5].length) (baseStart_2632119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2632119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2632119 prefixEnd_2632119 := by exact prefixLift 2632119
  have htrace : WordTrace (prefixWord ++ tailWord_2632119) baseStart_2632119 baseEnd_2632119 := by
    simpa [prefixWord, tailWord_2632119, baseEnd_2632119] using wordTrace_append hprefix tailTrace_2632119
  have hstable : (prefixWord ++ tailWord_2632119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2632119).length < 2 ^ (prefixWord ++ tailWord_2632119).sum := by decide
  have hdescent : baseEnd_2632119 < baseStart_2632119 := by decide
  rcases family_descends (prefixWord ++ tailWord_2632119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2632122 : List Nat := [3, 1, 1, 1, 2, 1, 1, 5, 1, 3, 4]
def baseStart_2632122 : Nat := 118140960795 + 2632122 * 2 ^ 59
def prefixEnd_2632122 : Nat := 4983230072969 + 3 ^ 40 * 2632122 * 2
def baseEnd_2632122 : Nat := 1351543727273656044270097

theorem tailTrace_2632122 : CollatzResearch.WordTrace tailWord_2632122 prefixEnd_2632122 1351543727273656044270097 := by
  unfold tailWord_2632122
  simp only [CollatzResearch.WordTrace]
  refine ⟨24000344042569749873436655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64000917446852666329164413 24000344042569749873436655)
  ·
    refine ⟨36000516063854624810154983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24000344042569749873436655 36000516063854624810154983)
    ·
      refine ⟨54000774095781937215232475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36000516063854624810154983 54000774095781937215232475)
      ·
        refine ⟨81001161143672905822848713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54000774095781937215232475 81001161143672905822848713)
        ·
          refine ⟨60750870857754679367136535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81001161143672905822848713 60750870857754679367136535)
          ·
            refine ⟨91126306286632019050704803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60750870857754679367136535 91126306286632019050704803)
            ·
              refine ⟨136689459429948028576057205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91126306286632019050704803 136689459429948028576057205)
              ·
                refine ⟨12814636821557627679005363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 136689459429948028576057205 12814636821557627679005363)
                ·
                  refine ⟨19221955232336441518508045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12814636821557627679005363 19221955232336441518508045)
                  ·
                    refine ⟨7208233212126165569440517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19221955232336441518508045 7208233212126165569440517)
                    ·
                      refine ⟨1351543727273656044270097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7208233212126165569440517 1351543727273656044270097)
                      ·
                        rfl

theorem cell23_2632122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 5, 1, 3, 4].length) (baseStart_2632122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2632122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2632122 prefixEnd_2632122 := by exact prefixLift 2632122
  have htrace : WordTrace (prefixWord ++ tailWord_2632122) baseStart_2632122 baseEnd_2632122 := by
    simpa [prefixWord, tailWord_2632122, baseEnd_2632122] using wordTrace_append hprefix tailTrace_2632122
  have hstable : (prefixWord ++ tailWord_2632122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2632122).length < 2 ^ (prefixWord ++ tailWord_2632122).sum := by decide
  have hdescent : baseEnd_2632122 < baseStart_2632122 := by decide
  rcases family_descends (prefixWord ++ tailWord_2632122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2632139 : List Nat := [1, 1, 1, 1, 3, 3, 1, 4, 2, 4, 2]
def baseStart_2632139 : Nat := 118140960795 + 2632139 * 2 ^ 59
def prefixEnd_2632139 : Nat := 4983230072969 + 3 ^ 40 * 2632139 * 2
def baseEnd_2632139 : Nat := 1351552456444782477757519

theorem tailTrace_2632139 : CollatzResearch.WordTrace tailWord_2632139 prefixEnd_2632139 1351552456444782477757519 := by
  unfold tailWord_2632139
  simp only [CollatzResearch.WordTrace]
  refine ⟨96001996211217411397115471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64001330807478274264743647 96001996211217411397115471)
  ·
    refine ⟨144002994316826117095673207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96001996211217411397115471 144002994316826117095673207)
    ·
      refine ⟨216004491475239175643509811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144002994316826117095673207 216004491475239175643509811)
      ·
        refine ⟨324006737212858763465264717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216004491475239175643509811 324006737212858763465264717)
        ·
          refine ⟨121502526454822036299474269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 324006737212858763465264717 121502526454822036299474269)
          ·
            refine ⟨45563447420558263612302851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 121502526454822036299474269 45563447420558263612302851)
            ·
              refine ⟨68345171130837395418454277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45563447420558263612302851 68345171130837395418454277)
              ·
                refine ⟨12814719587032011640960177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68345171130837395418454277 12814719587032011640960177)
                ·
                  refine ⟨9611039690274008730720133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12814719587032011640960177 9611039690274008730720133)
                  ·
                    refine ⟨1802069941926376637010025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9611039690274008730720133 1802069941926376637010025)
                    ·
                      refine ⟨1351552456444782477757519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1802069941926376637010025 1351552456444782477757519)
                      ·
                        rfl

theorem cell23_2632139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 4, 2, 4, 2].length) (baseStart_2632139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2632139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2632139 prefixEnd_2632139 := by exact prefixLift 2632139
  have htrace : WordTrace (prefixWord ++ tailWord_2632139) baseStart_2632139 baseEnd_2632139 := by
    simpa [prefixWord, tailWord_2632139, baseEnd_2632139] using wordTrace_append hprefix tailTrace_2632139
  have hstable : (prefixWord ++ tailWord_2632139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2632139).length < 2 ^ (prefixWord ++ tailWord_2632139).sum := by decide
  have hdescent : baseEnd_2632139 < baseStart_2632139 := by decide
  rcases family_descends (prefixWord ++ tailWord_2632139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2632140 : List Nat := [2, 2, 1, 4, 4, 1, 2, 2, 5]
def baseStart_2632140 : Nat := 118140960795 + 2632140 * 2 ^ 59
def prefixEnd_2632140 : Nat := 4983230072969 + 3 ^ 40 * 2632140 * 2
def baseEnd_2632140 : Nat := 150172552213937441538335

theorem tailTrace_2632140 : CollatzResearch.WordTrace tailWord_2632140 prefixEnd_2632140 150172552213937441538335 := by
  unfold tailWord_2632140
  simp only [CollatzResearch.WordTrace]
  refine ⟨48001016342106894283950937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64001355122809192378601249 48001016342106894283950937)
  ·
    refine ⟨36000762256580170712963203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48001016342106894283950937 36000762256580170712963203)
    ·
      refine ⟨54001143384870256069444805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36000762256580170712963203 54001143384870256069444805)
      ·
        refine ⟨10125214384663173013020901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54001143384870256069444805 10125214384663173013020901)
        ·
          refine ⟨1898477697124344939941419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10125214384663173013020901 1898477697124344939941419)
          ·
            refine ⟨2847716545686517409912129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1898477697124344939941419 2847716545686517409912129)
            ·
              refine ⟨2135787409264888057434097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2847716545686517409912129 2135787409264888057434097)
              ·
                refine ⟨1601840556948666043075573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2135787409264888057434097 1601840556948666043075573)
                ·
                  refine ⟨150172552213937441538335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1601840556948666043075573 150172552213937441538335)
                  ·
                    rfl

theorem cell23_2632140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 2, 2, 5].length) (baseStart_2632140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2632140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2632140 prefixEnd_2632140 := by exact prefixLift 2632140
  have htrace : WordTrace (prefixWord ++ tailWord_2632140) baseStart_2632140 baseEnd_2632140 := by
    simpa [prefixWord, tailWord_2632140, baseEnd_2632140] using wordTrace_append hprefix tailTrace_2632140
  have hstable : (prefixWord ++ tailWord_2632140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2632140).length < 2 ^ (prefixWord ++ tailWord_2632140).sum := by decide
  have hdescent : baseEnd_2632140 < baseStart_2632140 := by decide
  rcases family_descends (prefixWord ++ tailWord_2632140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2632142 : List Nat := [4, 1, 1, 1, 2, 1, 1, 1, 1, 5, 5]
def baseStart_2632142 : Nat := 118140960795 + 2632142 * 2 ^ 59
def prefixEnd_2632142 : Nat := 4983230072969 + 3 ^ 40 * 2632142 * 2
def baseEnd_2632142 : Nat := 1351553996886745966020005

theorem tailTrace_2632142 : CollatzResearch.WordTrace tailWord_2632142 prefixEnd_2632142 1351553996886745966020005 := by
  unfold tailWord_2632142
  simp only [CollatzResearch.WordTrace]
  refine ⟨12000263203775817863684335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64001403753471028606316453 12000263203775817863684335)
  ·
    refine ⟨18000394805663726795526503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12000263203775817863684335 18000394805663726795526503)
    ·
      refine ⟨27000592208495590193289755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18000394805663726795526503 27000592208495590193289755)
      ·
        refine ⟨40500888312743385289934633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27000592208495590193289755 40500888312743385289934633)
        ·
          refine ⟨30375666234557538967450975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40500888312743385289934633 30375666234557538967450975)
          ·
            refine ⟨45563499351836308451176463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30375666234557538967450975 45563499351836308451176463)
            ·
              refine ⟨68345249027754462676764695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45563499351836308451176463 68345249027754462676764695)
              ·
                refine ⟨102517873541631694015147043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68345249027754462676764695 102517873541631694015147043)
                ·
                  refine ⟨153776810312447541022720565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 102517873541631694015147043 153776810312447541022720565)
                  ·
                    refine ⟨14416575966791956970880053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 153776810312447541022720565 14416575966791956970880053)
                    ·
                      refine ⟨1351553996886745966020005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14416575966791956970880053 1351553996886745966020005)
                      ·
                        rfl

theorem cell23_2632142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 1, 5, 5].length) (baseStart_2632142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2632142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2632142 prefixEnd_2632142 := by exact prefixLift 2632142
  have htrace : WordTrace (prefixWord ++ tailWord_2632142) baseStart_2632142 baseEnd_2632142 := by
    simpa [prefixWord, tailWord_2632142, baseEnd_2632142] using wordTrace_append hprefix tailTrace_2632142
  have hstable : (prefixWord ++ tailWord_2632142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2632142).length < 2 ^ (prefixWord ++ tailWord_2632142).sum := by decide
  have hdescent : baseEnd_2632142 < baseStart_2632142 := by decide
  rcases family_descends (prefixWord ++ tailWord_2632142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2632152 : List Nat := [2, 1, 2, 2, 2, 1, 1, 2, 2, 4, 4]
def baseStart_2632152 : Nat := 118140960795 + 2632152 * 2 ^ 59
def prefixEnd_2632152 : Nat := 4983230072969 + 3 ^ 40 * 2632152 * 2
def baseEnd_2632152 : Nat := 1351559131693290926894959

theorem tailTrace_2632152 : CollatzResearch.WordTrace tailWord_2632152 prefixEnd_2632152 1351559131693290926894959 := by
  unfold tailWord_2632152
  simp only [CollatzResearch.WordTrace]
  refine ⟨48001235180085157308669355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64001646906780209744892473 48001235180085157308669355)
  ·
    refine ⟨72001852770127735963004033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48001235180085157308669355 72001852770127735963004033)
    ·
      refine ⟨54001389577595801972253025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72001852770127735963004033 54001389577595801972253025)
      ·
        refine ⟨40501042183196851479189769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54001389577595801972253025 40501042183196851479189769)
        ·
          refine ⟨30375781637397638609392327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40501042183196851479189769 30375781637397638609392327)
          ·
            refine ⟨45563672456096457914088491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30375781637397638609392327 45563672456096457914088491)
            ·
              refine ⟨68345508684144686871132737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45563672456096457914088491 68345508684144686871132737)
              ·
                refine ⟨51259131513108515153349553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68345508684144686871132737 51259131513108515153349553)
                ·
                  refine ⟨38444348634831386365012165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51259131513108515153349553 38444348634831386365012165)
                  ·
                    refine ⟨7208315369030884943439781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38444348634831386365012165 7208315369030884943439781)
                    ·
                      refine ⟨1351559131693290926894959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7208315369030884943439781 1351559131693290926894959)
                      ·
                        rfl

theorem cell23_2632152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 2, 4, 4].length) (baseStart_2632152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2632152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2632152 prefixEnd_2632152 := by exact prefixLift 2632152
  have htrace : WordTrace (prefixWord ++ tailWord_2632152) baseStart_2632152 baseEnd_2632152 := by
    simpa [prefixWord, tailWord_2632152, baseEnd_2632152] using wordTrace_append hprefix tailTrace_2632152
  have hstable : (prefixWord ++ tailWord_2632152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2632152).length < 2 ^ (prefixWord ++ tailWord_2632152).sum := by decide
  have hdescent : baseEnd_2632152 < baseStart_2632152 := by decide
  rcases family_descends (prefixWord ++ tailWord_2632152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2632173 : List Nat := [1, 5, 1, 3, 1, 3, 1, 1, 2, 1, 4]
def baseStart_2632173 : Nat := 118140960795 + 2632173 * 2 ^ 59
def prefixEnd_2632173 : Nat := 4983230072969 + 3 ^ 40 * 2632173 * 2
def baseEnd_2632173 : Nat := 1351569914787035344732363

theorem tailTrace_2632173 : CollatzResearch.WordTrace tailWord_2632173 prefixEnd_2632173 1351569914787035344732363 := by
  unfold tailWord_2632173
  simp only [CollatzResearch.WordTrace]
  refine ⟨96003236293094235203853173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64002157528729490135902115 96003236293094235203853173)
  ·
    refine ⟨9000303402477584550361235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 96003236293094235203853173 9000303402477584550361235)
    ·
      refine ⟨13500455103716376825541853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9000303402477584550361235 13500455103716376825541853)
      ·
        refine ⟨5062670663893641309578195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13500455103716376825541853 5062670663893641309578195)
        ·
          refine ⟨7594005995840461964367293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5062670663893641309578195 7594005995840461964367293)
          ·
            refine ⟨2847752248440173236637735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7594005995840461964367293 2847752248440173236637735)
            ·
              refine ⟨4271628372660259854956603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2847752248440173236637735 4271628372660259854956603)
              ·
                refine ⟨6407442558990389782434905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4271628372660259854956603 6407442558990389782434905)
                ·
                  refine ⟨4805581919242792336826179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6407442558990389782434905 4805581919242792336826179)
                  ·
                    refine ⟨7208372878864188505239269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4805581919242792336826179 7208372878864188505239269)
                    ·
                      refine ⟨1351569914787035344732363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7208372878864188505239269 1351569914787035344732363)
                      ·
                        rfl

theorem cell23_2632173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_2632173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2632173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2632173 prefixEnd_2632173 := by exact prefixLift 2632173
  have htrace : WordTrace (prefixWord ++ tailWord_2632173) baseStart_2632173 baseEnd_2632173 := by
    simpa [prefixWord, tailWord_2632173, baseEnd_2632173] using wordTrace_append hprefix tailTrace_2632173
  have hstable : (prefixWord ++ tailWord_2632173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2632173).length < 2 ^ (prefixWord ++ tailWord_2632173).sum := by decide
  have hdescent : baseEnd_2632173 < baseStart_2632173 := by decide
  rcases family_descends (prefixWord ++ tailWord_2632173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2632196 : List Nat := [2, 3, 2, 3, 1, 1, 3, 2, 6]
def baseStart_2632196 : Nat := 118140960795 + 2632196 * 2 ^ 59
def prefixEnd_2632196 : Nat := 4983230072969 + 3 ^ 40 * 2632196 * 2
def baseEnd_2632196 : Nat := 150175747204676528304973

theorem tailTrace_2632196 : CollatzResearch.WordTrace tailWord_2632196 prefixEnd_2632196 150175747204676528304973 := by
  unfold tailWord_2632196
  simp only [CollatzResearch.WordTrace]
  refine ⟨48002037586005455065970221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64002716781340606754626961 48002037586005455065970221)
  ·
    refine ⟨18000764094752045649738833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48002037586005455065970221 18000764094752045649738833)
    ·
      refine ⟨13500573071064034237304125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18000764094752045649738833 13500573071064034237304125)
      ·
        refine ⟨5062714901649012838989047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13500573071064034237304125 5062714901649012838989047)
        ·
          refine ⟨7594072352473519258483571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5062714901649012838989047 7594072352473519258483571)
          ·
            refine ⟨11391108528710278887725357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7594072352473519258483571 11391108528710278887725357)
            ·
              refine ⟨4271665698266354582897009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11391108528710278887725357 4271665698266354582897009)
              ·
                refine ⟨3203749273699765937172757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4271665698266354582897009 3203749273699765937172757)
                ·
                  refine ⟨150175747204676528304973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3203749273699765937172757 150175747204676528304973)
                  ·
                    rfl

theorem cell23_2632196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3, 2, 6].length) (baseStart_2632196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2632196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2632196 prefixEnd_2632196 := by exact prefixLift 2632196
  have htrace : WordTrace (prefixWord ++ tailWord_2632196) baseStart_2632196 baseEnd_2632196 := by
    simpa [prefixWord, tailWord_2632196, baseEnd_2632196] using wordTrace_append hprefix tailTrace_2632196
  have hstable : (prefixWord ++ tailWord_2632196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2632196).length < 2 ^ (prefixWord ++ tailWord_2632196).sum := by decide
  have hdescent : baseEnd_2632196 < baseStart_2632196 := by decide
  rcases family_descends (prefixWord ++ tailWord_2632196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2632216 : List Nat := [2, 1, 2, 3, 3, 1, 1, 2, 1, 5, 2]
def baseStart_2632216 : Nat := 118140960795 + 2632216 * 2 ^ 59
def prefixEnd_2632216 : Nat := 4983230072969 + 3 ^ 40 * 2632216 * 2
def baseEnd_2632216 : Nat := 1351591994455178676494665

theorem tailTrace_2632216 : CollatzResearch.WordTrace tailWord_2632216 prefixEnd_2632216 1351591994455178676494665 := by
  unfold tailWord_2632216
  simp only [CollatzResearch.WordTrace]
  refine ⟨48002402315969226773834251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64003203087958969031779001 48002402315969226773834251)
  ·
    refine ⟨72003603473953840160751377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48002402315969226773834251 72003603473953840160751377)
    ·
      refine ⟨54002702605465380120563533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72003603473953840160751377 54002702605465380120563533)
      ·
        refine ⟨20251013477049517545211325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54002702605465380120563533 20251013477049517545211325)
        ·
          refine ⟨7594130053893569079454247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20251013477049517545211325 7594130053893569079454247)
          ·
            refine ⟨11391195080840353619181371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7594130053893569079454247 11391195080840353619181371)
            ·
              refine ⟨17086792621260530428772057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11391195080840353619181371 17086792621260530428772057)
              ·
                refine ⟨12815094465945397821579043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17086792621260530428772057 12815094465945397821579043)
                ·
                  refine ⟨19222641698918096732368565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12815094465945397821579043 19222641698918096732368565)
                  ·
                    refine ⟨1802122659273571568659553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19222641698918096732368565 1802122659273571568659553)
                    ·
                      refine ⟨1351591994455178676494665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1802122659273571568659553 1351591994455178676494665)
                      ·
                        rfl

theorem cell23_2632216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 2, 1, 5, 2].length) (baseStart_2632216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2632216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2632216 prefixEnd_2632216 := by exact prefixLift 2632216
  have htrace : WordTrace (prefixWord ++ tailWord_2632216) baseStart_2632216 baseEnd_2632216 := by
    simpa [prefixWord, tailWord_2632216, baseEnd_2632216] using wordTrace_append hprefix tailTrace_2632216
  have hstable : (prefixWord ++ tailWord_2632216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2632216).length < 2 ^ (prefixWord ++ tailWord_2632216).sum := by decide
  have hdescent : baseEnd_2632216 < baseStart_2632216 := by decide
  rcases family_descends (prefixWord ++ tailWord_2632216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2632229 : List Nat := [1, 3, 1, 2, 2, 1, 2, 3, 3, 1, 4]
def baseStart_2632229 : Nat := 118140960795 + 2632229 * 2 ^ 59
def prefixEnd_2632229 : Nat := 4983230072969 + 3 ^ 40 * 2632229 * 2
def baseEnd_2632229 : Nat := 1351598669703687125632105

theorem tailTrace_2632229 : CollatzResearch.WordTrace tailWord_2632229 prefixEnd_2632229 1351598669703687125632105 := by
  unfold tailWord_2632229
  simp only [CollatzResearch.WordTrace]
  refine ⟨96005278780891356767891741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64003519187260904511927827 96005278780891356767891741)
  ·
    refine ⟨36001979542834258787959403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96005278780891356767891741 36001979542834258787959403)
    ·
      refine ⟨54002969314251388181939105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36001979542834258787959403 54002969314251388181939105)
      ·
        refine ⟨40502226985688541136454329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54002969314251388181939105 40502226985688541136454329)
        ·
          refine ⟨30376670239266405852340747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40502226985688541136454329 30376670239266405852340747)
          ·
            refine ⟨45565005358899608778511121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30376670239266405852340747 45565005358899608778511121)
            ·
              refine ⟨34173754019174706583883341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45565005358899608778511121 34173754019174706583883341)
              ·
                refine ⟨12815157757190514968956253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34173754019174706583883341 12815157757190514968956253)
                ·
                  refine ⟨4805684158946443113358595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12815157757190514968956253 4805684158946443113358595)
                  ·
                    refine ⟨7208526238419664670037893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4805684158946443113358595 7208526238419664670037893)
                    ·
                      refine ⟨1351598669703687125632105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7208526238419664670037893 1351598669703687125632105)
                      ·
                        rfl

theorem cell23_2632229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 3, 3, 1, 4].length) (baseStart_2632229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2632229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2632229 prefixEnd_2632229 := by exact prefixLift 2632229
  have htrace : WordTrace (prefixWord ++ tailWord_2632229) baseStart_2632229 baseEnd_2632229 := by
    simpa [prefixWord, tailWord_2632229, baseEnd_2632229] using wordTrace_append hprefix tailTrace_2632229
  have hstable : (prefixWord ++ tailWord_2632229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2632229).length < 2 ^ (prefixWord ++ tailWord_2632229).sum := by decide
  have hdescent : baseEnd_2632229 < baseStart_2632229 := by decide
  rcases family_descends (prefixWord ++ tailWord_2632229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2632257 : List Nat := [1, 2, 5, 1, 1, 3, 3, 2, 1, 1, 3]
def baseStart_2632257 : Nat := 118140960795 + 2632257 * 2 ^ 59
def prefixEnd_2632257 : Nat := 4983230072969 + 3 ^ 40 * 2632257 * 2
def baseEnd_2632257 : Nat := 1351613047162013016081977

theorem tailTrace_2632257 : CollatzResearch.WordTrace tailWord_2632257 prefixEnd_2632257 1351613047162013016081977 := by
  unfold tailWord_2632257
  simp only [CollatzResearch.WordTrace]
  refine ⟨96006300024789917549911025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64004200016526611699940683 96006300024789917549911025)
  ·
    refine ⟨72004725018592438162433269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96006300024789917549911025 72004725018592438162433269)
    ·
      refine ⟨6750442970493041077728119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 72004725018592438162433269 6750442970493041077728119)
      ·
        refine ⟨10125664455739561616592179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6750442970493041077728119 10125664455739561616592179)
        ·
          refine ⟨15188496683609342424888269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10125664455739561616592179 15188496683609342424888269)
          ·
            refine ⟨5695686256353503409333101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15188496683609342424888269 5695686256353503409333101)
            ·
              refine ⟨2135882346132563778499913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5695686256353503409333101 2135882346132563778499913)
              ·
                refine ⟨1601911759599422833874935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2135882346132563778499913 1601911759599422833874935)
                ·
                  refine ⟨2402867639399134250812403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1601911759599422833874935 2402867639399134250812403)
                  ·
                    refine ⟨3604301459098701376218605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2402867639399134250812403 3604301459098701376218605)
                    ·
                      refine ⟨1351613047162013016081977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3604301459098701376218605 1351613047162013016081977)
                      ·
                        rfl

theorem cell23_2632257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 3, 2, 1, 1, 3].length) (baseStart_2632257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2632257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2632257 prefixEnd_2632257 := by exact prefixLift 2632257
  have htrace : WordTrace (prefixWord ++ tailWord_2632257) baseStart_2632257 baseEnd_2632257 := by
    simpa [prefixWord, tailWord_2632257, baseEnd_2632257] using wordTrace_append hprefix tailTrace_2632257
  have hstable : (prefixWord ++ tailWord_2632257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2632257).length < 2 ^ (prefixWord ++ tailWord_2632257).sum := by decide
  have hdescent : baseEnd_2632257 < baseStart_2632257 := by decide
  rcases family_descends (prefixWord ++ tailWord_2632257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2632273 : List Nat := [1, 2, 2, 1, 3, 3, 4, 1, 2, 4]
def baseStart_2632273 : Nat := 118140960795 + 2632273 * 2 ^ 59
def prefixEnd_2632273 : Nat := 4983230072969 + 3 ^ 40 * 2632273 * 2
def baseEnd_2632273 : Nat := 450540420950828317827301

theorem tailTrace_2632273 : CollatzResearch.WordTrace tailWord_2632273 prefixEnd_2632273 450540420950828317827301 := by
  unfold tailWord_2632273
  simp only [CollatzResearch.WordTrace]
  refine ⟨96006883592731952282493473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64004589061821301521662315 96006883592731952282493473)
  ·
    refine ⟨72005162694548964211870105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96006883592731952282493473 72005162694548964211870105)
    ·
      refine ⟨54003872020911723158902579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72005162694548964211870105 54003872020911723158902579)
      ·
        refine ⟨81005808031367584738353869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54003872020911723158902579 81005808031367584738353869)
        ·
          refine ⟨30377178011762844276882701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81005808031367584738353869 30377178011762844276882701)
          ·
            refine ⟨11391441754411066603831013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30377178011762844276882701 11391441754411066603831013)
            ·
              refine ⟨2135895328952074988218315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11391441754411066603831013 2135895328952074988218315)
              ·
                refine ⟨3203842993428112482327473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2135895328952074988218315 3203842993428112482327473)
                ·
                  refine ⟨2402882245071084361745605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3203842993428112482327473 2402882245071084361745605)
                  ·
                    refine ⟨450540420950828317827301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2402882245071084361745605 450540420950828317827301)
                    ·
                      rfl

theorem cell23_2632273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 4, 1, 2, 4].length) (baseStart_2632273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2632273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2632273 prefixEnd_2632273 := by exact prefixLift 2632273
  have htrace : WordTrace (prefixWord ++ tailWord_2632273) baseStart_2632273 baseEnd_2632273 := by
    simpa [prefixWord, tailWord_2632273, baseEnd_2632273] using wordTrace_append hprefix tailTrace_2632273
  have hstable : (prefixWord ++ tailWord_2632273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2632273).length < 2 ^ (prefixWord ++ tailWord_2632273).sum := by decide
  have hdescent : baseEnd_2632273 < baseStart_2632273 := by decide
  rcases family_descends (prefixWord ++ tailWord_2632273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2632313 : List Nat := [1, 2, 1, 3, 3, 2, 1, 4, 2, 1, 3]
def baseStart_2632313 : Nat := 118140960795 + 2632313 * 2 ^ 59
def prefixEnd_2632313 : Nat := 4983230072969 + 3 ^ 40 * 2632313 * 2
def baseEnd_2632313 : Nat := 1351641802078664796981719

theorem tailTrace_2632313 : CollatzResearch.WordTrace tailWord_2632313 prefixEnd_2632313 1351641802078664796981719 := by
  unfold tailWord_2632313
  simp only [CollatzResearch.WordTrace]
  refine ⟨96008342512587039113949593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64005561675058026075966395 96008342512587039113949593)
  ·
    refine ⟨72006256884440279335462195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96008342512587039113949593 72006256884440279335462195)
    ·
      refine ⟨108009385326660419003193293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72006256884440279335462195 108009385326660419003193293)
      ·
        refine ⟨40503519497497657126197485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108009385326660419003193293 40503519497497657126197485)
        ·
          refine ⟨15188819811561621422324057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40503519497497657126197485 15188819811561621422324057)
          ·
            refine ⟨11391614858671216066743043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15188819811561621422324057 11391614858671216066743043)
            ·
              refine ⟨17087422288006824100114565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11391614858671216066743043 17087422288006824100114565)
              ·
                refine ⟨3203891679001279518771481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17087422288006824100114565 3203891679001279518771481)
                ·
                  refine ⟨2402918759250959639078611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3203891679001279518771481 2402918759250959639078611)
                  ·
                    refine ⟨3604378138876439458617917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2402918759250959639078611 3604378138876439458617917)
                    ·
                      refine ⟨1351641802078664796981719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3604378138876439458617917 1351641802078664796981719)
                      ·
                        rfl

theorem cell23_2632313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 4, 2, 1, 3].length) (baseStart_2632313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2632313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2632313 prefixEnd_2632313 := by exact prefixLift 2632313
  have htrace : WordTrace (prefixWord ++ tailWord_2632313) baseStart_2632313 baseEnd_2632313 := by
    simpa [prefixWord, tailWord_2632313, baseEnd_2632313] using wordTrace_append hprefix tailTrace_2632313
  have hstable : (prefixWord ++ tailWord_2632313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2632313).length < 2 ^ (prefixWord ++ tailWord_2632313).sum := by decide
  have hdescent : baseEnd_2632313 < baseStart_2632313 := by decide
  rcases family_descends (prefixWord ++ tailWord_2632313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2632340 : List Nat := [2, 4, 2, 2, 1, 1, 2, 1, 3, 3, 2]
def baseStart_2632340 : Nat := 118140960795 + 2632340 * 2 ^ 59
def prefixEnd_2632340 : Nat := 4983230072969 + 3 ^ 40 * 2632340 * 2
def baseEnd_2632340 : Nat := 1351655666056336191344095

theorem tailTrace_2632340 : CollatzResearch.WordTrace tailWord_2632340 prefixEnd_2632340 1351655666056336191344095 := by
  unfold tailWord_2632340
  simp only [CollatzResearch.WordTrace]
  refine ⟨48004663641744611362591237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64006218188992815150121649 48004663641744611362591237)
  ·
    refine ⟨9000874432827114630485857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48004663641744611362591237 9000874432827114630485857)
    ·
      refine ⟨6750655824620335972864393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9000874432827114630485857 6750655824620335972864393)
      ·
        refine ⟨5062991868465251979648295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6750655824620335972864393 5062991868465251979648295)
        ·
          refine ⟨7594487802697877969472443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5062991868465251979648295 7594487802697877969472443)
          ·
            refine ⟨11391731704046816954208665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7594487802697877969472443 11391731704046816954208665)
            ·
              refine ⟨8543798778035112715656499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11391731704046816954208665 8543798778035112715656499)
              ·
                refine ⟨12815698167052669073484749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8543798778035112715656499 12815698167052669073484749)
                ·
                  refine ⟨4805886812644750902556781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12815698167052669073484749 4805886812644750902556781)
                  ·
                    refine ⟨1802207554741781588458793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4805886812644750902556781 1802207554741781588458793)
                    ·
                      refine ⟨1351655666056336191344095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1802207554741781588458793 1351655666056336191344095)
                      ·
                        rfl

theorem cell23_2632340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 1, 3, 3, 2].length) (baseStart_2632340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2632340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2632340 prefixEnd_2632340 := by exact prefixLift 2632340
  have htrace : WordTrace (prefixWord ++ tailWord_2632340) baseStart_2632340 baseEnd_2632340 := by
    simpa [prefixWord, tailWord_2632340, baseEnd_2632340] using wordTrace_append hprefix tailTrace_2632340
  have hstable : (prefixWord ++ tailWord_2632340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2632340).length < 2 ^ (prefixWord ++ tailWord_2632340).sum := by decide
  have hdescent : baseEnd_2632340 < baseStart_2632340 := by decide
  rcases family_descends (prefixWord ++ tailWord_2632340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2632399 : List Nat := [1, 1, 2, 1, 1, 3, 1, 1, 5, 2, 5]
def baseStart_2632399 : Nat := 118140960795 + 2632399 * 2 ^ 59
def prefixEnd_2632399 : Nat := 4983230072969 + 3 ^ 40 * 2632399 * 2
def baseEnd_2632399 : Nat := 1351685961414951460506323

theorem tailTrace_2632399 : CollatzResearch.WordTrace tailWord_2632399 prefixEnd_2632399 1351685961414951460506323 := by
  unfold tailWord_2632399
  simp only [CollatzResearch.WordTrace]
  refine ⟨96011479190275475801580251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64007652793516983867720167 96011479190275475801580251)
  ·
    refine ⟨144017218785413213702370377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96011479190275475801580251 144017218785413213702370377)
    ·
      refine ⟨108012914089059910276777783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144017218785413213702370377 108012914089059910276777783)
      ·
        refine ⟨162019371133589865415166675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108012914089059910276777783 162019371133589865415166675)
        ·
          refine ⟨243029056700384798122750013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162019371133589865415166675 243029056700384798122750013)
          ·
            refine ⟨91135896262644299296031255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 243029056700384798122750013 91135896262644299296031255)
            ·
              refine ⟨136703844393966448944046883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91135896262644299296031255 136703844393966448944046883)
              ·
                refine ⟨205055766590949673416070325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 136703844393966448944046883 205055766590949673416070325)
                ·
                  refine ⟨19223978117901531882756593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 205055766590949673416070325 19223978117901531882756593)
                  ·
                    refine ⟨14417983588426148912067445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19223978117901531882756593 14417983588426148912067445)
                    ·
                      refine ⟨1351685961414951460506323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14417983588426148912067445 1351685961414951460506323)
                      ·
                        rfl

theorem cell23_2632399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 5, 2, 5].length) (baseStart_2632399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2632399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2632399 prefixEnd_2632399 := by exact prefixLift 2632399
  have htrace : WordTrace (prefixWord ++ tailWord_2632399) baseStart_2632399 baseEnd_2632399 := by
    simpa [prefixWord, tailWord_2632399, baseEnd_2632399] using wordTrace_append hprefix tailTrace_2632399
  have hstable : (prefixWord ++ tailWord_2632399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2632399).length < 2 ^ (prefixWord ++ tailWord_2632399).sum := by decide
  have hdescent : baseEnd_2632399 < baseStart_2632399 := by decide
  rcases family_descends (prefixWord ++ tailWord_2632399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2632463 : List Nat := [1, 1, 2, 1, 1, 1, 8, 1, 2, 2, 3]
def baseStart_2632463 : Nat := 118140960795 + 2632463 * 2 ^ 59
def prefixEnd_2632463 : Nat := 4983230072969 + 3 ^ 40 * 2632463 * 2
def baseEnd_2632463 : Nat := 1351718824176839210106029

theorem tailTrace_2632463 : CollatzResearch.WordTrace tailWord_2632463 prefixEnd_2632463 1351718824176839210106029 := by
  unfold tailWord_2632463
  simp only [CollatzResearch.WordTrace]
  refine ⟨96013813462043614731910043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64009208974695743154606695 96013813462043614731910043)
  ·
    refine ⟨144020720193065422097865065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96013813462043614731910043 144020720193065422097865065)
    ·
      refine ⟨108015540144799066573398799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144020720193065422097865065 108015540144799066573398799)
      ·
        refine ⟨162023310217198599860098199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108015540144799066573398799 162023310217198599860098199)
        ·
          refine ⟨243034965325797899790147299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162023310217198599860098199 243034965325797899790147299)
          ·
            refine ⟨364552447988696849685220949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 243034965325797899790147299 364552447988696849685220949)
            ·
              refine ⟨4272098999867541207248683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 364552447988696849685220949 4272098999867541207248683)
              ·
                refine ⟨6408148499801311810873025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4272098999867541207248683 6408148499801311810873025)
                ·
                  refine ⟨4806111374850983858154769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6408148499801311810873025 4806111374850983858154769)
                  ·
                    refine ⟨3604583531138237893616077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4806111374850983858154769 3604583531138237893616077)
                    ·
                      refine ⟨1351718824176839210106029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3604583531138237893616077 1351718824176839210106029)
                      ·
                        rfl

theorem cell23_2632463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 1, 2, 2, 3].length) (baseStart_2632463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2632463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2632463 prefixEnd_2632463 := by exact prefixLift 2632463
  have htrace : WordTrace (prefixWord ++ tailWord_2632463) baseStart_2632463 baseEnd_2632463 := by
    simpa [prefixWord, tailWord_2632463, baseEnd_2632463] using wordTrace_append hprefix tailTrace_2632463
  have hstable : (prefixWord ++ tailWord_2632463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2632463).length < 2 ^ (prefixWord ++ tailWord_2632463).sum := by decide
  have hdescent : baseEnd_2632463 < baseStart_2632463 := by decide
  rcases family_descends (prefixWord ++ tailWord_2632463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2632503 : List Nat := [1, 1, 3, 1, 2, 1, 4, 2, 1, 5, 2]
def baseStart_2632503 : Nat := 118140960795 + 2632503 * 2 ^ 59
def prefixEnd_2632503 : Nat := 4983230072969 + 3 ^ 40 * 2632503 * 2
def baseEnd_2632503 : Nat := 1351739363403019053605845

theorem tailTrace_2632503 : CollatzResearch.WordTrace tailWord_2632503 prefixEnd_2632503 1351739363403019053605845 := by
  unfold tailWord_2632503
  simp only [CollatzResearch.WordTrace]
  refine ⟨96015272381898701563366163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64010181587932467708910775 96015272381898701563366163)
  ·
    refine ⟨144022908572848052345049245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96015272381898701563366163 144022908572848052345049245)
    ·
      refine ⟨54008590714818019629393467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144022908572848052345049245 54008590714818019629393467)
      ·
        refine ⟨81012886072227029444090201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54008590714818019629393467 81012886072227029444090201)
        ·
          refine ⟨60759664554170272083067651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81012886072227029444090201 60759664554170272083067651)
          ·
            refine ⟨91139496831255408124601477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60759664554170272083067651 91139496831255408124601477)
            ·
              refine ⟨17088655655860389023362777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 91139496831255408124601477 17088655655860389023362777)
              ·
                refine ⟨12816491741895291767522083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17088655655860389023362777 12816491741895291767522083)
                ·
                  refine ⟨19224737612842937651283125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12816491741895291767522083 19224737612842937651283125)
                  ·
                    refine ⟨1802319151204025404807793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19224737612842937651283125 1802319151204025404807793)
                    ·
                      refine ⟨1351739363403019053605845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1802319151204025404807793 1351739363403019053605845)
                      ·
                        rfl

theorem cell23_2632503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 2, 1, 5, 2].length) (baseStart_2632503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2632503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2632503 prefixEnd_2632503 := by exact prefixLift 2632503
  have htrace : WordTrace (prefixWord ++ tailWord_2632503) baseStart_2632503 baseEnd_2632503 := by
    simpa [prefixWord, tailWord_2632503, baseEnd_2632503] using wordTrace_append hprefix tailTrace_2632503
  have hstable : (prefixWord ++ tailWord_2632503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2632503).length < 2 ^ (prefixWord ++ tailWord_2632503).sum := by decide
  have hdescent : baseEnd_2632503 < baseStart_2632503 := by decide
  rcases family_descends (prefixWord ++ tailWord_2632503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2632536 : List Nat := [2, 1, 2, 2, 1, 1, 1, 2, 5, 1, 5]
def baseStart_2632536 : Nat := 118140960795 + 2632536 * 2 ^ 59
def prefixEnd_2632536 : Nat := 4983230072969 + 3 ^ 40 * 2632536 * 2
def baseEnd_2632536 : Nat := 1351756308264617424493193

theorem tailTrace_2632536 : CollatzResearch.WordTrace tailWord_2632536 prefixEnd_2632536 1351756308264617424493193 := by
  unfold tailWord_2632536
  simp only [CollatzResearch.WordTrace]
  refine ⟨48008237995389574099658731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64010983993852765466211641 48008237995389574099658731)
  ·
    refine ⟨72012356993084361149488097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48008237995389574099658731 72012356993084361149488097)
    ·
      refine ⟨54009267744813270862116073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72012356993084361149488097 54009267744813270862116073)
      ·
        refine ⟨40506950808609953146587055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54009267744813270862116073 40506950808609953146587055)
        ·
          refine ⟨60760426212914929719880583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40506950808609953146587055 60760426212914929719880583)
          ·
            refine ⟨91140639319372394579820875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60760426212914929719880583 91140639319372394579820875)
            ·
              refine ⟨136710958979058591869731313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91140639319372394579820875 136710958979058591869731313)
              ·
                refine ⟨102533219234293943902298485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 136710958979058591869731313 102533219234293943902298485)
                ·
                  refine ⟨9612489303215057240840483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 102533219234293943902298485 9612489303215057240840483)
                  ·
                    refine ⟨14418733954822585861260725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9612489303215057240840483 14418733954822585861260725)
                    ·
                      refine ⟨1351756308264617424493193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14418733954822585861260725 1351756308264617424493193)
                      ·
                        rfl

theorem cell23_2632536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 5, 1, 5].length) (baseStart_2632536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2632536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2632536 prefixEnd_2632536 := by exact prefixLift 2632536
  have htrace : WordTrace (prefixWord ++ tailWord_2632536) baseStart_2632536 baseEnd_2632536 := by
    simpa [prefixWord, tailWord_2632536, baseEnd_2632536] using wordTrace_append hprefix tailTrace_2632536
  have hstable : (prefixWord ++ tailWord_2632536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2632536).length < 2 ^ (prefixWord ++ tailWord_2632536).sum := by decide
  have hdescent : baseEnd_2632536 < baseStart_2632536 := by decide
  rcases family_descends (prefixWord ++ tailWord_2632536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2632543 : List Nat := [1, 1, 2, 3, 1, 3, 3, 1, 4, 4]
def baseStart_2632543 : Nat := 118140960795 + 2632543 * 2 ^ 59
def prefixEnd_2632543 : Nat := 4983230072969 + 3 ^ 40 * 2632543 * 2
def baseEnd_2632543 : Nat := 450586634209732965701887

theorem tailTrace_2632543 : CollatzResearch.WordTrace tailWord_2632543 prefixEnd_2632543 450586634209732965701887 := by
  unfold tailWord_2632543
  simp only [CollatzResearch.WordTrace]
  refine ⟨96016731301753788394822283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64011154201169192263214855 96016731301753788394822283)
  ·
    refine ⟨144025096952630682592233425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96016731301753788394822283 144025096952630682592233425)
    ·
      refine ⟨108018822714473011944175069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144025096952630682592233425 108018822714473011944175069)
      ·
        refine ⟨40507058517927379479065651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108018822714473011944175069 40507058517927379479065651)
        ·
          refine ⟨60760587776891069218598477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40507058517927379479065651 60760587776891069218598477)
          ·
            refine ⟨22785220416334150956974429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60760587776891069218598477 22785220416334150956974429)
            ·
              refine ⟨8544457656125306608865411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22785220416334150956974429 8544457656125306608865411)
              ·
                refine ⟨12816686484187959913298117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8544457656125306608865411 12816686484187959913298117)
                ·
                  refine ⟨2403128715785242483743397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12816686484187959913298117 2403128715785242483743397)
                  ·
                    refine ⟨450586634209732965701887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2403128715785242483743397 450586634209732965701887)
                    ·
                      rfl

theorem cell23_2632543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 1, 4, 4].length) (baseStart_2632543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2632543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2632543 prefixEnd_2632543 := by exact prefixLift 2632543
  have htrace : WordTrace (prefixWord ++ tailWord_2632543) baseStart_2632543 baseEnd_2632543 := by
    simpa [prefixWord, tailWord_2632543, baseEnd_2632543] using wordTrace_append hprefix tailTrace_2632543
  have hstable : (prefixWord ++ tailWord_2632543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2632543).length < 2 ^ (prefixWord ++ tailWord_2632543).sum := by decide
  have hdescent : baseEnd_2632543 < baseStart_2632543 := by decide
  rcases family_descends (prefixWord ++ tailWord_2632543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2632556 : List Nat := [2, 2, 1, 1, 4, 1, 2, 10]
def baseStart_2632556 : Nat := 118140960795 + 2632556 * 2 ^ 59
def prefixEnd_2632556 : Nat := 4983230072969 + 3 ^ 40 * 2632556 * 2
def baseEnd_2632556 : Nat := 50065428810285457268263

theorem tailTrace_2632556 : CollatzResearch.WordTrace tailWord_2632556 prefixEnd_2632556 50065428810285457268263 := by
  unfold tailWord_2632556
  simp only [CollatzResearch.WordTrace]
  refine ⟨48008602725353345807522761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64011470300471127743363681 48008602725353345807522761)
  ·
    refine ⟨36006452044015009355642071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48008602725353345807522761 36006452044015009355642071)
    ·
      refine ⟨54009678066022514033463107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36006452044015009355642071 54009678066022514033463107)
      ·
        refine ⟨81014517099033771050194661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54009678066022514033463107 81014517099033771050194661)
        ·
          refine ⟨15190221956068832071911499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81014517099033771050194661 15190221956068832071911499)
          ·
            refine ⟨22785332934103248107867249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15190221956068832071911499 22785332934103248107867249)
            ·
              refine ⟨17088999700577436080900437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22785332934103248107867249 17088999700577436080900437)
              ·
                refine ⟨50065428810285457268263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 17088999700577436080900437 50065428810285457268263)
                ·
                  rfl

theorem cell23_2632556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 10].length) (baseStart_2632556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2632556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2632556 prefixEnd_2632556 := by exact prefixLift 2632556
  have htrace : WordTrace (prefixWord ++ tailWord_2632556) baseStart_2632556 baseEnd_2632556 := by
    simpa [prefixWord, tailWord_2632556, baseEnd_2632556] using wordTrace_append hprefix tailTrace_2632556
  have hstable : (prefixWord ++ tailWord_2632556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2632556).length < 2 ^ (prefixWord ++ tailWord_2632556).sum := by decide
  have hdescent : baseEnd_2632556 < baseStart_2632556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2632556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2632563 : List Nat := [1, 1, 1, 2, 2, 1, 7, 1, 1, 2, 4]
def baseStart_2632563 : Nat := 118140960795 + 2632563 * 2 ^ 59
def prefixEnd_2632563 : Nat := 4983230072969 + 3 ^ 40 * 2632563 * 2
def baseEnd_2632563 : Nat := 1351770172242288818855569

theorem tailTrace_2632563 : CollatzResearch.WordTrace tailWord_2632563 prefixEnd_2632563 1351770172242288818855569 := by
  unfold tailWord_2632563
  simp only [CollatzResearch.WordTrace]
  refine ⟨96017460761681331810550343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64011640507787554540366895 96017460761681331810550343)
  ·
    refine ⟨144026191142521997715825515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96017460761681331810550343 144026191142521997715825515)
    ·
      refine ⟨216039286713782996573738273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144026191142521997715825515 216039286713782996573738273)
      ·
        refine ⟨162029465035337247430303705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 216039286713782996573738273 162029465035337247430303705)
        ·
          refine ⟨121522098776502935572727779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162029465035337247430303705 121522098776502935572727779)
          ·
            refine ⟨182283148164754403359091669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121522098776502935572727779 182283148164754403359091669)
            ·
              refine ⟨4272261285111431328728711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 182283148164754403359091669 4272261285111431328728711)
              ·
                refine ⟨6408391927667146993093067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4272261285111431328728711 6408391927667146993093067)
                ·
                  refine ⟨9612587891500720489639601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6408391927667146993093067 9612587891500720489639601)
                  ·
                    refine ⟨7209440918625540367229701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9612587891500720489639601 7209440918625540367229701)
                    ·
                      refine ⟨1351770172242288818855569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7209440918625540367229701 1351770172242288818855569)
                      ·
                        rfl

theorem cell23_2632563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7, 1, 1, 2, 4].length) (baseStart_2632563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2632563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2632563 prefixEnd_2632563 := by exact prefixLift 2632563
  have htrace : WordTrace (prefixWord ++ tailWord_2632563) baseStart_2632563 baseEnd_2632563 := by
    simpa [prefixWord, tailWord_2632563, baseEnd_2632563] using wordTrace_append hprefix tailTrace_2632563
  have hstable : (prefixWord ++ tailWord_2632563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2632563).length < 2 ^ (prefixWord ++ tailWord_2632563).sum := by decide
  have hdescent : baseEnd_2632563 < baseStart_2632563 := by decide
  rcases family_descends (prefixWord ++ tailWord_2632563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2632573 : List Nat := [1, 4, 1, 1, 2, 1, 6, 7]
def baseStart_2632573 : Nat := 118140960795 + 2632573 * 2 ^ 59
def prefixEnd_2632573 : Nat := 4983230072969 + 3 ^ 40 * 2632573 * 2
def baseEnd_2632573 : Nat := 50065752112919769619649

theorem tailTrace_2632573 : CollatzResearch.WordTrace tailWord_2632573 prefixEnd_2632573 50065752112919769619649 := by
  unfold tailWord_2632573
  simp only [CollatzResearch.WordTrace]
  refine ⟨96017825491645103518414373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64011883661096735678942915 96017825491645103518414373)
  ·
    refine ⟨18003342279683456909702695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96017825491645103518414373 18003342279683456909702695)
    ·
      refine ⟨27005013419525185364554043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18003342279683456909702695 27005013419525185364554043)
      ·
        refine ⟨40507520129287778046831065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27005013419525185364554043 40507520129287778046831065)
        ·
          refine ⟨30380640096965833535123299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40507520129287778046831065 30380640096965833535123299)
          ·
            refine ⟨45570960145448750302684949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30380640096965833535123299 45570960145448750302684949)
            ·
              refine ⟨2136138756817910170438357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 45570960145448750302684949 2136138756817910170438357)
              ·
                refine ⟨50065752112919769619649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2136138756817910170438357 50065752112919769619649)
                ·
                  rfl

theorem cell23_2632573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 6, 7].length) (baseStart_2632573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2632573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2632573 prefixEnd_2632573 := by exact prefixLift 2632573
  have htrace : WordTrace (prefixWord ++ tailWord_2632573) baseStart_2632573 baseEnd_2632573 := by
    simpa [prefixWord, tailWord_2632573, baseEnd_2632573] using wordTrace_append hprefix tailTrace_2632573
  have hstable : (prefixWord ++ tailWord_2632573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2632573).length < 2 ^ (prefixWord ++ tailWord_2632573).sum := by decide
  have hdescent : baseEnd_2632573 < baseStart_2632573 := by decide
  rcases family_descends (prefixWord ++ tailWord_2632573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2632621 : List Nat := [1, 5, 2, 3, 1, 2, 1, 2, 1, 2, 3]
def baseStart_2632621 : Nat := 118140960795 + 2632621 * 2 ^ 59
def prefixEnd_2632621 : Nat := 4983230072969 + 3 ^ 40 * 2632621 * 2
def baseEnd_2632621 : Nat := 1351799954120249591930303

theorem tailTrace_2632621 : CollatzResearch.WordTrace tailWord_2632621 prefixEnd_2632621 1351799954120249591930303 := by
  unfold tailWord_2632621
  simp only [CollatzResearch.WordTrace]
  refine ⟨96019576195471207716161717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64013050796980805144107811 96019576195471207716161717)
  ·
    refine ⟨9001835268325425723390161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 96019576195471207716161717 9001835268325425723390161)
    ·
      refine ⟨6751376451244069292542621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9001835268325425723390161 6751376451244069292542621)
      ·
        refine ⟨2531766169216525984703483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6751376451244069292542621 2531766169216525984703483)
        ·
          refine ⟨3797649253824788977055225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2531766169216525984703483 3797649253824788977055225)
          ·
            refine ⟨2848236940368591732791419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3797649253824788977055225 2848236940368591732791419)
            ·
              refine ⟨4272355410552887599187129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2848236940368591732791419 4272355410552887599187129)
              ·
                refine ⟨3204266557914665699390347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4272355410552887599187129 3204266557914665699390347)
                ·
                  refine ⟨4806399836871998549085521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3204266557914665699390347 4806399836871998549085521)
                  ·
                    refine ⟨3604799877653998911814141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4806399836871998549085521 3604799877653998911814141)
                    ·
                      refine ⟨1351799954120249591930303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3604799877653998911814141 1351799954120249591930303)
                      ·
                        rfl

theorem cell23_2632621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_2632621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2632621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2632621 prefixEnd_2632621 := by exact prefixLift 2632621
  have htrace : WordTrace (prefixWord ++ tailWord_2632621) baseStart_2632621 baseEnd_2632621 := by
    simpa [prefixWord, tailWord_2632621, baseEnd_2632621] using wordTrace_append hprefix tailTrace_2632621
  have hstable : (prefixWord ++ tailWord_2632621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2632621).length < 2 ^ (prefixWord ++ tailWord_2632621).sum := by decide
  have hdescent : baseEnd_2632621 < baseStart_2632621 := by decide
  rcases family_descends (prefixWord ++ tailWord_2632621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2632640 : List Nat := [2, 1, 1, 2, 3, 3, 1, 1, 3, 4, 2]
def baseStart_2632640 : Nat := 118140960795 + 2632640 * 2 ^ 59
def prefixEnd_2632640 : Nat := 4983230072969 + 3 ^ 40 * 2632640 * 2
def baseEnd_2632640 : Nat := 1351809710252685017592715

theorem tailTrace_2632640 : CollatzResearch.WordTrace tailWord_2632640 prefixEnd_2632640 1351809710252685017592715 := by
  unfold tailWord_2632640
  simp only [CollatzResearch.WordTrace]
  refine ⟨48010134591201186980551687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64013512788268249307402249 48010134591201186980551687)
  ·
    refine ⟨72015201886801780470827531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48010134591201186980551687 72015201886801780470827531)
    ·
      refine ⟨108022802830202670706241297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72015201886801780470827531 108022802830202670706241297)
      ·
        refine ⟨81017102122652003029680973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108022802830202670706241297 81017102122652003029680973)
        ·
          refine ⟨30381413295994501136130365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81017102122652003029680973 30381413295994501136130365)
          ·
            refine ⟨11393029985997937926048887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30381413295994501136130365 11393029985997937926048887)
            ·
              refine ⟨17089544978996906889073331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11393029985997937926048887 17089544978996906889073331)
              ·
                refine ⟨25634317468495360333609997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17089544978996906889073331 25634317468495360333609997)
                ·
                  refine ⟨9612869050685760125103749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25634317468495360333609997 9612869050685760125103749)
                  ·
                    refine ⟨1802412947003580023456953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9612869050685760125103749 1802412947003580023456953)
                    ·
                      refine ⟨1351809710252685017592715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1802412947003580023456953 1351809710252685017592715)
                      ·
                        rfl

theorem cell23_2632640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 1, 3, 4, 2].length) (baseStart_2632640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2632640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2632640 prefixEnd_2632640 := by exact prefixLift 2632640
  have htrace : WordTrace (prefixWord ++ tailWord_2632640) baseStart_2632640 baseEnd_2632640 := by
    simpa [prefixWord, tailWord_2632640, baseEnd_2632640] using wordTrace_append hprefix tailTrace_2632640
  have hstable : (prefixWord ++ tailWord_2632640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2632640).length < 2 ^ (prefixWord ++ tailWord_2632640).sum := by decide
  have hdescent : baseEnd_2632640 < baseStart_2632640 := by decide
  rcases family_descends (prefixWord ++ tailWord_2632640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2632660 : List Nat := [2, 4, 1, 2, 1, 2, 1, 1, 2, 4, 3]
def baseStart_2632660 : Nat := 118140960795 + 2632660 * 2 ^ 59
def prefixEnd_2632660 : Nat := 4983230072969 + 3 ^ 40 * 2632660 * 2
def baseEnd_2632660 : Nat := 1351819979865774939342623

theorem tailTrace_2632660 : CollatzResearch.WordTrace tailWord_2632660 prefixEnd_2632660 1351819979865774939342623 := by
  unfold tailWord_2632660
  simp only [CollatzResearch.WordTrace]
  refine ⟨48010499321164958688415717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64013999094886611584554289 48010499321164958688415717)
  ·
    refine ⟨9001968622718429754077947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48010499321164958688415717 9001968622718429754077947)
    ·
      refine ⟨13502952934077644631116921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9001968622718429754077947 13502952934077644631116921)
      ·
        refine ⟨10127214700558233473337691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13502952934077644631116921 10127214700558233473337691)
        ·
          refine ⟨15190822050837350210006537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10127214700558233473337691 15190822050837350210006537)
          ·
            refine ⟨11393116538128012657504903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15190822050837350210006537 11393116538128012657504903)
            ·
              refine ⟨17089674807192018986257355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11393116538128012657504903 17089674807192018986257355)
              ·
                refine ⟨25634512210788028479386033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17089674807192018986257355 25634512210788028479386033)
                ·
                  refine ⟨19225884158091021359539525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25634512210788028479386033 19225884158091021359539525)
                  ·
                    refine ⟨3604853279642066504913661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19225884158091021359539525 3604853279642066504913661)
                    ·
                      refine ⟨1351819979865774939342623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3604853279642066504913661 1351819979865774939342623)
                      ·
                        rfl

theorem cell23_2632660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 1, 2, 4, 3].length) (baseStart_2632660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2632660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2632660 prefixEnd_2632660 := by exact prefixLift 2632660
  have htrace : WordTrace (prefixWord ++ tailWord_2632660) baseStart_2632660 baseEnd_2632660 := by
    simpa [prefixWord, tailWord_2632660, baseEnd_2632660] using wordTrace_append hprefix tailTrace_2632660
  have hstable : (prefixWord ++ tailWord_2632660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2632660).length < 2 ^ (prefixWord ++ tailWord_2632660).sum := by decide
  have hdescent : baseEnd_2632660 < baseStart_2632660 := by decide
  rcases family_descends (prefixWord ++ tailWord_2632660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2632674 : List Nat := [3, 3, 3, 1, 1, 1, 1, 3, 1, 4, 2]
def baseStart_2632674 : Nat := 118140960795 + 2632674 * 2 ^ 59
def prefixEnd_2632674 : Nat := 4983230072969 + 3 ^ 40 * 2632674 * 2
def baseEnd_2632674 : Nat := 1351827168594937884567559

theorem tailTrace_2632674 : CollatzResearch.WordTrace tailWord_2632674 prefixEnd_2632674 1351827168594937884567559 := by
  unfold tailWord_2632674
  simp only [CollatzResearch.WordTrace]
  refine ⟨24005377316069799441960269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64014339509519465178560717 24005377316069799441960269)
  ·
    refine ⟨9002016493526174790735101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24005377316069799441960269 9002016493526174790735101)
    ·
      refine ⟨3375756185072315546525663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9002016493526174790735101 3375756185072315546525663)
      ·
        refine ⟨5063634277608473319788495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3375756185072315546525663 5063634277608473319788495)
        ·
          refine ⟨7595451416412709979682743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5063634277608473319788495 7595451416412709979682743)
          ·
            refine ⟨11393177124619064969524115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7595451416412709979682743 11393177124619064969524115)
            ·
              refine ⟨17089765686928597454286173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11393177124619064969524115 17089765686928597454286173)
              ·
                refine ⟨6408662132598224045357315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17089765686928597454286173 6408662132598224045357315)
                ·
                  refine ⟨9612993198897336068035973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6408662132598224045357315 9612993198897336068035973)
                  ·
                    refine ⟨1802436224793250512756745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9612993198897336068035973 1802436224793250512756745)
                    ·
                      refine ⟨1351827168594937884567559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1802436224793250512756745 1351827168594937884567559)
                      ·
                        rfl

theorem cell23_2632674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 3, 1, 4, 2].length) (baseStart_2632674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2632674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2632674 prefixEnd_2632674 := by exact prefixLift 2632674
  have htrace : WordTrace (prefixWord ++ tailWord_2632674) baseStart_2632674 baseEnd_2632674 := by
    simpa [prefixWord, tailWord_2632674, baseEnd_2632674] using wordTrace_append hprefix tailTrace_2632674
  have hstable : (prefixWord ++ tailWord_2632674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2632674).length < 2 ^ (prefixWord ++ tailWord_2632674).sum := by decide
  have hdescent : baseEnd_2632674 < baseStart_2632674 := by decide
  rcases family_descends (prefixWord ++ tailWord_2632674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2632753 : List Nat := [1, 2, 2, 3, 1, 2, 1, 1, 10]
def baseStart_2632753 : Nat := 118140960795 + 2632753 * 2 ^ 59
def prefixEnd_2632753 : Nat := 4983230072969 + 3 ^ 40 * 2632753 * 2
def baseEnd_2632753 : Nat := 150207525951849230608855

theorem tailTrace_2632753 : CollatzResearch.WordTrace tailWord_2632753 prefixEnd_2632753 150207525951849230608855 := by
  unfold tailWord_2632753
  simp only [CollatzResearch.WordTrace]
  refine ⟨96024390630992994259966913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64016260420661996173311275 96024390630992994259966913)
  ·
    refine ⟨72018292973244745694975185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96024390630992994259966913 72018292973244745694975185)
    ·
      refine ⟨54013719729933559271231389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72018292973244745694975185 54013719729933559271231389)
      ·
        refine ⟨20255144898725084726711771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54013719729933559271231389 20255144898725084726711771)
        ·
          refine ⟨30382717348087627090067657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20255144898725084726711771 30382717348087627090067657)
          ·
            refine ⟨22787038011065720317550743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30382717348087627090067657 22787038011065720317550743)
            ·
              refine ⟨34180557016598580476326115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22787038011065720317550743 34180557016598580476326115)
              ·
                refine ⟨51270835524897870714489173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34180557016598580476326115 51270835524897870714489173)
                ·
                  refine ⟨150207525951849230608855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 51270835524897870714489173 150207525951849230608855)
                  ·
                    rfl

theorem cell23_2632753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 10].length) (baseStart_2632753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2632753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2632753 prefixEnd_2632753 := by exact prefixLift 2632753
  have htrace : WordTrace (prefixWord ++ tailWord_2632753) baseStart_2632753 baseEnd_2632753 := by
    simpa [prefixWord, tailWord_2632753, baseEnd_2632753] using wordTrace_append hprefix tailTrace_2632753
  have hstable : (prefixWord ++ tailWord_2632753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2632753).length < 2 ^ (prefixWord ++ tailWord_2632753).sum := by decide
  have hdescent : baseEnd_2632753 < baseStart_2632753 := by decide
  rcases family_descends (prefixWord ++ tailWord_2632753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2632773 : List Nat := [1, 3, 1, 1, 1, 3, 2, 1, 1, 1, 8]
def baseStart_2632773 : Nat := 118140960795 + 2632773 * 2 ^ 59
def prefixEnd_2632773 : Nat := 4983230072969 + 3 ^ 40 * 2632773 * 2
def baseEnd_2632773 : Nat := 1351878003179732997229603

theorem tailTrace_2632773 : CollatzResearch.WordTrace tailWord_2632773 prefixEnd_2632773 1351878003179732997229603 := by
  unfold tailWord_2632773
  simp only [CollatzResearch.WordTrace]
  refine ⟨96025120090920537675694973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64016746727280358450463315 96025120090920537675694973)
  ·
    refine ⟨36009420034095201628385615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96025120090920537675694973 36009420034095201628385615)
    ·
      refine ⟨54014130051142802442578423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36009420034095201628385615 54014130051142802442578423)
      ·
        refine ⟨81021195076714203663867635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54014130051142802442578423 81021195076714203663867635)
        ·
          refine ⟨121531792615071305495801453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81021195076714203663867635 121531792615071305495801453)
          ·
            refine ⟨45574422230651739560925545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 121531792615071305495801453 45574422230651739560925545)
            ·
              refine ⟨34180816672988804670694159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45574422230651739560925545 34180816672988804670694159)
              ·
                refine ⟨51271225009483207006041239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34180816672988804670694159 51271225009483207006041239)
                ·
                  refine ⟨76906837514224810509061859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51271225009483207006041239 76906837514224810509061859)
                  ·
                    refine ⟨115360256271337215763592789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 76906837514224810509061859 115360256271337215763592789)
                    ·
                      refine ⟨1351878003179732997229603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 115360256271337215763592789 1351878003179732997229603)
                      ·
                        rfl

theorem cell23_2632773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 1, 8].length) (baseStart_2632773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2632773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2632773 prefixEnd_2632773 := by exact prefixLift 2632773
  have htrace : WordTrace (prefixWord ++ tailWord_2632773) baseStart_2632773 baseEnd_2632773 := by
    simpa [prefixWord, tailWord_2632773, baseEnd_2632773] using wordTrace_append hprefix tailTrace_2632773
  have hstable : (prefixWord ++ tailWord_2632773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2632773).length < 2 ^ (prefixWord ++ tailWord_2632773).sum := by decide
  have hdescent : baseEnd_2632773 < baseStart_2632773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2632773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2632793 : List Nat := [1, 2, 1, 2, 2, 1, 2, 1, 1, 3, 7]
def baseStart_2632793 : Nat := 118140960795 + 2632793 * 2 ^ 59
def prefixEnd_2632793 : Nat := 4983230072969 + 3 ^ 40 * 2632793 * 2
def baseEnd_2632793 : Nat := 1351888272792822918979511

theorem tailTrace_2632793 : CollatzResearch.WordTrace tailWord_2632793 prefixEnd_2632793 1351888272792822918979511 := by
  unfold tailWord_2632793
  simp only [CollatzResearch.WordTrace]
  refine ⟨96025849550848081091423033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64017233033898720727615355 96025849550848081091423033)
  ·
    refine ⟨72019387163136060818567275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96025849550848081091423033 72019387163136060818567275)
    ·
      refine ⟨108029080744704091227850913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72019387163136060818567275 108029080744704091227850913)
      ·
        refine ⟨81021810558528068420888185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108029080744704091227850913 81021810558528068420888185)
        ·
          refine ⟨60766357918896051315666139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81021810558528068420888185 60766357918896051315666139)
          ·
            refine ⟨91149536878344076973499209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60766357918896051315666139 91149536878344076973499209)
            ·
              refine ⟨68362152658758057730124407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91149536878344076973499209 68362152658758057730124407)
              ·
                refine ⟨102543228988137086595186611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68362152658758057730124407 102543228988137086595186611)
                ·
                  refine ⟨153814843482205629892779917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 102543228988137086595186611 153814843482205629892779917)
                  ·
                    refine ⟨57680566305827111209792469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 153814843482205629892779917 57680566305827111209792469)
                    ·
                      refine ⟨1351888272792822918979511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 57680566305827111209792469 1351888272792822918979511)
                      ·
                        rfl

theorem cell23_2632793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 3, 7].length) (baseStart_2632793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2632793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2632793 prefixEnd_2632793 := by exact prefixLift 2632793
  have htrace : WordTrace (prefixWord ++ tailWord_2632793) baseStart_2632793 baseEnd_2632793 := by
    simpa [prefixWord, tailWord_2632793, baseEnd_2632793] using wordTrace_append hprefix tailTrace_2632793
  have hstable : (prefixWord ++ tailWord_2632793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2632793).length < 2 ^ (prefixWord ++ tailWord_2632793).sum := by decide
  have hdescent : baseEnd_2632793 < baseStart_2632793 := by decide
  rcases family_descends (prefixWord ++ tailWord_2632793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2632800 : List Nat := [2, 1, 1, 3, 2, 2, 3, 1, 3, 5]
def baseStart_2632800 : Nat := 118140960795 + 2632800 * 2 ^ 59
def prefixEnd_2632800 : Nat := 4983230072969 + 3 ^ 40 * 2632800 * 2
def baseEnd_2632800 : Nat := 450630622385801463863993

theorem tailTrace_2632800 : CollatzResearch.WordTrace tailWord_2632800 prefixEnd_2632800 450630622385801463863993 := by
  unfold tailWord_2632800
  simp only [CollatzResearch.WordTrace]
  refine ⟨48013052430911360643463927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64017403241215147524618569 48013052430911360643463927)
  ·
    refine ⟨72019578646367040965195891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48013052430911360643463927 72019578646367040965195891)
    ·
      refine ⟨108029367969550561447793837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72019578646367040965195891 108029367969550561447793837)
      ·
        refine ⟨40511012988581460542922689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108029367969550561447793837 40511012988581460542922689)
        ·
          refine ⟨30383259741436095407192017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40511012988581460542922689 30383259741436095407192017)
          ·
            refine ⟨22787444806077071555394013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30383259741436095407192017 22787444806077071555394013)
            ·
              refine ⟨8545291802278901833272755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22787444806077071555394013 8545291802278901833272755)
              ·
                refine ⟨12817937703418352749909133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8545291802278901833272755 12817937703418352749909133)
                ·
                  refine ⟨4806726638781882281215925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12817937703418352749909133 4806726638781882281215925)
                  ·
                    refine ⟨450630622385801463863993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4806726638781882281215925 450630622385801463863993)
                    ·
                      rfl

theorem cell23_2632800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 1, 3, 5].length) (baseStart_2632800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2632800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2632800 prefixEnd_2632800 := by exact prefixLift 2632800
  have htrace : WordTrace (prefixWord ++ tailWord_2632800) baseStart_2632800 baseEnd_2632800 := by
    simpa [prefixWord, tailWord_2632800, baseEnd_2632800] using wordTrace_append hprefix tailTrace_2632800
  have hstable : (prefixWord ++ tailWord_2632800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2632800).length < 2 ^ (prefixWord ++ tailWord_2632800).sum := by decide
  have hdescent : baseEnd_2632800 < baseStart_2632800 := by decide
  rcases family_descends (prefixWord ++ tailWord_2632800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2632871 : List Nat := [1, 1, 6, 2, 1, 1, 4, 1, 1, 1, 4]
def baseStart_2632871 : Nat := 118140960795 + 2632871 * 2 ^ 59
def prefixEnd_2632871 : Nat := 4983230072969 + 3 ^ 40 * 2632871 * 2
def baseEnd_2632871 : Nat := 1351928324283873613804153

theorem tailTrace_2632871 : CollatzResearch.WordTrace tailWord_2632871 prefixEnd_2632871 1351928324283873613804153 := by
  unfold tailWord_2632871
  simp only [CollatzResearch.WordTrace]
  refine ⟨96028694444565500412762467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64019129629710333608508311 96028694444565500412762467)
  ·
    refine ⟨144043041666848250619143701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96028694444565500412762467 144043041666848250619143701)
    ·
      refine ⟨6752017578133511747772361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 144043041666848250619143701 6752017578133511747772361)
      ·
        refine ⟨5064013183600133810829271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6752017578133511747772361 5064013183600133810829271)
        ·
          refine ⟨7596019775400200716243907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5064013183600133810829271 7596019775400200716243907)
          ·
            refine ⟨11394029663100301074365861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7596019775400200716243907 11394029663100301074365861)
            ·
              refine ⟨2136380561831306451443599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11394029663100301074365861 2136380561831306451443599)
              ·
                refine ⟨3204570842746959677165399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2136380561831306451443599 3204570842746959677165399)
                ·
                  refine ⟨4806856264120439515748099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3204570842746959677165399 4806856264120439515748099)
                  ·
                    refine ⟨7210284396180659273622149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4806856264120439515748099 7210284396180659273622149)
                    ·
                      refine ⟨1351928324283873613804153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7210284396180659273622149 1351928324283873613804153)
                      ·
                        rfl

theorem cell23_2632871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 4, 1, 1, 1, 4].length) (baseStart_2632871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2632871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2632871 prefixEnd_2632871 := by exact prefixLift 2632871
  have htrace : WordTrace (prefixWord ++ tailWord_2632871) baseStart_2632871 baseEnd_2632871 := by
    simpa [prefixWord, tailWord_2632871, baseEnd_2632871] using wordTrace_append hprefix tailTrace_2632871
  have hstable : (prefixWord ++ tailWord_2632871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2632871).length < 2 ^ (prefixWord ++ tailWord_2632871).sum := by decide
  have hdescent : baseEnd_2632871 < baseStart_2632871 := by decide
  rcases family_descends (prefixWord ++ tailWord_2632871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2632877 : List Nat := [1, 5, 2, 1, 3, 1, 10]
def baseStart_2632877 : Nat := 118140960795 + 2632877 * 2 ^ 59
def prefixEnd_2632877 : Nat := 4983230072969 + 3 ^ 40 * 2632877 * 2
def baseEnd_2632877 : Nat := 16690511174911118399125

theorem tailTrace_2632877 : CollatzResearch.WordTrace tailWord_2632877 prefixEnd_2632877 16690511174911118399125 := by
  unfold tailWord_2632877
  simp only [CollatzResearch.WordTrace]
  refine ⟨96028913282543763437480885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64019275521695842291653923 96028913282543763437480885)
  ·
    refine ⟨9002710620238477822263833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 96028913282543763437480885 9002710620238477822263833)
    ·
      refine ⟨6752032965178858366697875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9002710620238477822263833 6752032965178858366697875)
      ·
        refine ⟨10128049447768287550046813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6752032965178858366697875 10128049447768287550046813)
        ·
          refine ⟨3798018542913107831267555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10128049447768287550046813 3798018542913107831267555)
          ·
            refine ⟨5697027814369661746901333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3798018542913107831267555 5697027814369661746901333)
            ·
              refine ⟨16690511174911118399125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5697027814369661746901333 16690511174911118399125)
              ·
                rfl

theorem cell23_2632877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 10].length) (baseStart_2632877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2632877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2632877 prefixEnd_2632877 := by exact prefixLift 2632877
  have htrace : WordTrace (prefixWord ++ tailWord_2632877) baseStart_2632877 baseEnd_2632877 := by
    simpa [prefixWord, tailWord_2632877, baseEnd_2632877] using wordTrace_append hprefix tailTrace_2632877
  have hstable : (prefixWord ++ tailWord_2632877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2632877).length < 2 ^ (prefixWord ++ tailWord_2632877).sum := by decide
  have hdescent : baseEnd_2632877 < baseStart_2632877 := by decide
  rcases family_descends (prefixWord ++ tailWord_2632877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2632881 : List Nat := [1, 2, 2, 5, 1, 3, 1, 2, 2, 4]
def baseStart_2632881 : Nat := 118140960795 + 2632881 * 2 ^ 59
def prefixEnd_2632881 : Nat := 4983230072969 + 3 ^ 40 * 2632881 * 2
def baseEnd_2632881 : Nat := 450644486363472858226369

theorem tailTrace_2632881 : CollatzResearch.WordTrace tailWord_2632881 prefixEnd_2632881 450644486363472858226369 := by
  unfold tailWord_2632881
  simp only [CollatzResearch.WordTrace]
  refine ⟨96029059174529272120626497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64019372783019514747084331 96029059174529272120626497)
  ·
    refine ⟨72021794380896954090469873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96029059174529272120626497 72021794380896954090469873)
    ·
      refine ⟨54016345785672715567852405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72021794380896954090469873 54016345785672715567852405)
      ·
        refine ⟨5064032417406817084486163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 54016345785672715567852405 5064032417406817084486163)
        ·
          refine ⟨7596048626110225626729245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5064032417406817084486163 7596048626110225626729245)
          ·
            refine ⟨2848518234791334610023467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7596048626110225626729245 2848518234791334610023467)
            ·
              refine ⟨4272777352187001915035201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2848518234791334610023467 4272777352187001915035201)
              ·
                refine ⟨3204583014140251436276401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4272777352187001915035201 3204583014140251436276401)
                ·
                  refine ⟨2403437260605188577207301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3204583014140251436276401 2403437260605188577207301)
                  ·
                    refine ⟨450644486363472858226369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2403437260605188577207301 450644486363472858226369)
                    ·
                      rfl

theorem cell23_2632881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 1, 2, 2, 4].length) (baseStart_2632881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2632881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2632881 prefixEnd_2632881 := by exact prefixLift 2632881
  have htrace : WordTrace (prefixWord ++ tailWord_2632881) baseStart_2632881 baseEnd_2632881 := by
    simpa [prefixWord, tailWord_2632881, baseEnd_2632881] using wordTrace_append hprefix tailTrace_2632881
  have hstable : (prefixWord ++ tailWord_2632881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2632881).length < 2 ^ (prefixWord ++ tailWord_2632881).sum := by decide
  have hdescent : baseEnd_2632881 < baseStart_2632881 := by decide
  rcases family_descends (prefixWord ++ tailWord_2632881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2632898 : List Nat := [3, 5, 1, 1, 2, 2, 1, 1, 1, 6]
def baseStart_2632898 : Nat := 118140960795 + 2632898 * 2 ^ 59
def prefixEnd_2632898 : Nat := 4983230072969 + 3 ^ 40 * 2632898 * 2
def baseEnd_2632898 : Nat := 450647396087181669388843

theorem tailTrace_2632898 : CollatzResearch.WordTrace tailWord_2632898 prefixEnd_2632898 450647396087181669388843 := by
  unfold tailWord_2632898
  simp only [CollatzResearch.WordTrace]
  refine ⟨24007419803866921005998837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64019786143645122682663565 24007419803866921005998837)
  ·
    refine ⟨2250695606612523844312391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24007419803866921005998837 2250695606612523844312391)
    ·
      refine ⟨3376043409918785766468587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2250695606612523844312391 3376043409918785766468587)
      ·
        refine ⟨5064065114878178649702881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3376043409918785766468587 5064065114878178649702881)
        ·
          refine ⟨3798048836158633987277161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5064065114878178649702881 3798048836158633987277161)
          ·
            refine ⟨2848536627118975490457871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3798048836158633987277161 2848536627118975490457871)
            ·
              refine ⟨4272804940678463235686807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2848536627118975490457871 4272804940678463235686807)
              ·
                refine ⟨6409207411017694853530211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4272804940678463235686807 6409207411017694853530211)
                ·
                  refine ⟨9613811116526542280295317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6409207411017694853530211 9613811116526542280295317)
                  ·
                    refine ⟨450647396087181669388843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9613811116526542280295317 450647396087181669388843)
                    ·
                      rfl

theorem cell23_2632898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_2632898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2632898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2632898 prefixEnd_2632898 := by exact prefixLift 2632898
  have htrace : WordTrace (prefixWord ++ tailWord_2632898) baseStart_2632898 baseEnd_2632898 := by
    simpa [prefixWord, tailWord_2632898, baseEnd_2632898] using wordTrace_append hprefix tailTrace_2632898
  have hstable : (prefixWord ++ tailWord_2632898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2632898).length < 2 ^ (prefixWord ++ tailWord_2632898).sum := by decide
  have hdescent : baseEnd_2632898 < baseStart_2632898 := by decide
  rcases family_descends (prefixWord ++ tailWord_2632898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2632904 : List Nat := [2, 1, 3, 1, 2, 1, 2, 5, 2, 1, 3]
def baseStart_2632904 : Nat := 118140960795 + 2632904 * 2 ^ 59
def prefixEnd_2632904 : Nat := 4983230072969 + 3 ^ 40 * 2632904 * 2
def baseEnd_2632904 : Nat := 1351945269145471984691501

theorem tailTrace_2632904 : CollatzResearch.WordTrace tailWord_2632904 prefixEnd_2632904 1351945269145471984691501 := by
  unfold tailWord_2632904
  simp only [CollatzResearch.WordTrace]
  refine ⟨48014949026722973524356883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64019932035630631365809177 48014949026722973524356883)
  ·
    refine ⟨72022423540084460286535325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48014949026722973524356883 72022423540084460286535325)
    ·
      refine ⟨27008408827531672607450747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72022423540084460286535325 27008408827531672607450747)
      ·
        refine ⟨40512613241297508911176121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27008408827531672607450747 40512613241297508911176121)
        ·
          refine ⟨30384459930973131683382091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40512613241297508911176121 30384459930973131683382091)
          ·
            refine ⟨45576689896459697525073137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30384459930973131683382091 45576689896459697525073137)
            ·
              refine ⟨34182517422344773143804853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45576689896459697525073137 34182517422344773143804853)
              ·
                refine ⟨3204611008344822482231705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34182517422344773143804853 3204611008344822482231705)
                ·
                  refine ⟨2403458256258616861673779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3204611008344822482231705 2403458256258616861673779)
                  ·
                    refine ⟨3605187384387925292510669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2403458256258616861673779 3605187384387925292510669)
                    ·
                      refine ⟨1351945269145471984691501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3605187384387925292510669 1351945269145471984691501)
                      ·
                        rfl

theorem cell23_2632904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 5, 2, 1, 3].length) (baseStart_2632904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2632904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2632904 prefixEnd_2632904 := by exact prefixLift 2632904
  have htrace : WordTrace (prefixWord ++ tailWord_2632904) baseStart_2632904 baseEnd_2632904 := by
    simpa [prefixWord, tailWord_2632904, baseEnd_2632904] using wordTrace_append hprefix tailTrace_2632904
  have hstable : (prefixWord ++ tailWord_2632904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2632904).length < 2 ^ (prefixWord ++ tailWord_2632904).sum := by decide
  have hdescent : baseEnd_2632904 < baseStart_2632904 := by decide
  rcases family_descends (prefixWord ++ tailWord_2632904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2632917 : List Nat := [1, 3, 2, 4, 1, 1, 1, 1, 2, 2, 5]
def baseStart_2632917 : Nat := 118140960795 + 2632917 * 2 ^ 59
def prefixEnd_2632917 : Nat := 4983230072969 + 3 ^ 40 * 2632917 * 2
def baseEnd_2632917 : Nat := 1351951944393980433828941

theorem tailTrace_2632917 : CollatzResearch.WordTrace tailWord_2632917 prefixEnd_2632917 1351951944393980433828941 := by
  unfold tailWord_2632917
  simp only [CollatzResearch.WordTrace]
  refine ⟨96030372202398850268937005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64020248134932566845958003 96030372202398850268937005)
  ·
    refine ⟨36011389575899568850851377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96030372202398850268937005 36011389575899568850851377)
    ·
      refine ⟨27008542181924676638138533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36011389575899568850851377 27008542181924676638138533)
      ·
        refine ⟨5064101659110876869650975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27008542181924676638138533 5064101659110876869650975)
        ·
          refine ⟨7596152488666315304476463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5064101659110876869650975 7596152488666315304476463)
          ·
            refine ⟨11394228732999472956714695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7596152488666315304476463 11394228732999472956714695)
            ·
              refine ⟨17091343099499209435072043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11394228732999472956714695 17091343099499209435072043)
              ·
                refine ⟨25637014649248814152608065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17091343099499209435072043 25637014649248814152608065)
                ·
                  refine ⟨19227760986936610614456049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25637014649248814152608065 19227760986936610614456049)
                  ·
                    refine ⟨14420820740202457960842037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19227760986936610614456049 14420820740202457960842037)
                    ·
                      refine ⟨1351951944393980433828941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14420820740202457960842037 1351951944393980433828941)
                      ·
                        rfl

theorem cell23_2632917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_2632917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2632917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2632917 prefixEnd_2632917 := by exact prefixLift 2632917
  have htrace : WordTrace (prefixWord ++ tailWord_2632917) baseStart_2632917 baseEnd_2632917 := by
    simpa [prefixWord, tailWord_2632917, baseEnd_2632917] using wordTrace_append hprefix tailTrace_2632917
  have hstable : (prefixWord ++ tailWord_2632917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2632917).length < 2 ^ (prefixWord ++ tailWord_2632917).sum := by decide
  have hdescent : baseEnd_2632917 < baseStart_2632917 := by decide
  rcases family_descends (prefixWord ++ tailWord_2632917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2633044 : List Nat := [2, 4, 1, 1, 2, 1, 1, 2, 5, 4]
def baseStart_2633044 : Nat := 118140960795 + 2633044 * 2 ^ 59
def prefixEnd_2633044 : Nat := 4983230072969 + 3 ^ 40 * 2633044 * 2
def baseEnd_2633044 : Nat := 450672385479033812313619

theorem tailTrace_2633044 : CollatzResearch.WordTrace tailWord_2633044 prefixEnd_2633044 450672385479033812313619 := by
  unfold tailWord_2633044
  simp only [CollatzResearch.WordTrace]
  refine ⟨48017502136469375479405093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64023336181959167305873457 48017502136469375479405093)
  ·
    refine ⟨9003281650588007902388455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48017502136469375479405093 9003281650588007902388455)
    ·
      refine ⟨13504922475882011853582683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9003281650588007902388455 13504922475882011853582683)
      ·
        refine ⟨20257383713823017780374025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13504922475882011853582683 20257383713823017780374025)
        ·
          refine ⟨15193037785367263335280519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20257383713823017780374025 15193037785367263335280519)
          ·
            refine ⟨22789556678050895002920779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15193037785367263335280519 22789556678050895002920779)
            ·
              refine ⟨34184335017076342504381169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22789556678050895002920779 34184335017076342504381169)
              ·
                refine ⟨25638251262807256878285877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34184335017076342504381169 25638251262807256878285877)
                ·
                  refine ⟨2403586055888180332339301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25638251262807256878285877 2403586055888180332339301)
                  ·
                    refine ⟨450672385479033812313619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2403586055888180332339301 450672385479033812313619)
                    ·
                      rfl

theorem cell23_2633044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 5, 4].length) (baseStart_2633044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2633044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2633044 prefixEnd_2633044 := by exact prefixLift 2633044
  have htrace : WordTrace (prefixWord ++ tailWord_2633044) baseStart_2633044 baseEnd_2633044 := by
    simpa [prefixWord, tailWord_2633044, baseEnd_2633044] using wordTrace_append hprefix tailTrace_2633044
  have hstable : (prefixWord ++ tailWord_2633044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2633044).length < 2 ^ (prefixWord ++ tailWord_2633044).sum := by decide
  have hdescent : baseEnd_2633044 < baseStart_2633044 := by decide
  rcases family_descends (prefixWord ++ tailWord_2633044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2633046 : List Nat := [5, 2, 3, 1, 1, 2, 1, 2, 2, 2, 2]
def baseStart_2633046 : Nat := 118140960795 + 2633046 * 2 ^ 59
def prefixEnd_2633046 : Nat := 4983230072969 + 3 ^ 40 * 2633046 * 2
def baseEnd_2633046 : Nat := 1352018183398410429115849

theorem tailTrace_2633046 : CollatzResearch.WordTrace tailWord_2633046 prefixEnd_2633046 1352018183398410429115849 := by
  unfold tailWord_2633046
  simp only [CollatzResearch.WordTrace]
  refine ⟨6002192326183219081273937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 64023384812621003533588661 6002192326183219081273937)
  ·
    refine ⟨4501644244637414310955453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6002192326183219081273937 4501644244637414310955453)
    ·
      refine ⟨1688116591739030366608295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4501644244637414310955453 1688116591739030366608295)
      ·
        refine ⟨2532174887608545549912443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1688116591739030366608295 2532174887608545549912443)
        ·
          refine ⟨3798262331412818324868665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2532174887608545549912443 3798262331412818324868665)
          ·
            refine ⟨2848696748559613743651499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3798262331412818324868665 2848696748559613743651499)
            ·
              refine ⟨4273045122839420615477249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2848696748559613743651499 4273045122839420615477249)
              ·
                refine ⟨3204783842129565461607937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4273045122839420615477249 3204783842129565461607937)
                ·
                  refine ⟨2403587881597174096205953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3204783842129565461607937 2403587881597174096205953)
                  ·
                    refine ⟨1802690911197880572154465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2403587881597174096205953 1802690911197880572154465)
                    ·
                      refine ⟨1352018183398410429115849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1802690911197880572154465 1352018183398410429115849)
                      ·
                        rfl

theorem cell23_2633046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_2633046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2633046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2633046 prefixEnd_2633046 := by exact prefixLift 2633046
  have htrace : WordTrace (prefixWord ++ tailWord_2633046) baseStart_2633046 baseEnd_2633046 := by
    simpa [prefixWord, tailWord_2633046, baseEnd_2633046] using wordTrace_append hprefix tailTrace_2633046
  have hstable : (prefixWord ++ tailWord_2633046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2633046).length < 2 ^ (prefixWord ++ tailWord_2633046).sum := by decide
  have hdescent : baseEnd_2633046 < baseStart_2633046 := by decide
  rcases family_descends (prefixWord ++ tailWord_2633046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2633047 : List Nat := [1, 1, 3, 2, 3, 2, 1, 1, 2, 1, 6]
def baseStart_2633047 : Nat := 118140960795 + 2633047 * 2 ^ 59
def prefixEnd_2633047 : Nat := 4983230072969 + 3 ^ 40 * 2633047 * 2
def baseEnd_2633047 : Nat := 1352018696879064925203343

theorem tailTrace_2633047 : CollatzResearch.WordTrace tailWord_2633047 prefixEnd_2633047 1352018696879064925203343 := by
  unfold tailWord_2633047
  simp only [CollatzResearch.WordTrace]
  refine ⟨96035113691927882471169395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64023409127951921647446263 96035113691927882471169395)
  ·
    refine ⟨144052670537891823706754093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96035113691927882471169395 144052670537891823706754093)
    ·
      refine ⟨54019751451709433890032785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144052670537891823706754093 54019751451709433890032785)
      ·
        refine ⟨40514813588782075417524589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54019751451709433890032785 40514813588782075417524589)
        ·
          refine ⟨15193055095793278281571721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40514813588782075417524589 15193055095793278281571721)
          ·
            refine ⟨11394791321844958711178791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15193055095793278281571721 11394791321844958711178791)
            ·
              refine ⟨17092186982767438066768187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11394791321844958711178791 17092186982767438066768187)
              ·
                refine ⟨25638280474151157100152281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17092186982767438066768187 25638280474151157100152281)
                ·
                  refine ⟨19228710355613367825114211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25638280474151157100152281 19228710355613367825114211)
                  ·
                    refine ⟨28843065533420051737671317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19228710355613367825114211 28843065533420051737671317)
                    ·
                      refine ⟨1352018696879064925203343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28843065533420051737671317 1352018696879064925203343)
                      ·
                        rfl

theorem cell23_2633047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 1, 2, 1, 6].length) (baseStart_2633047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2633047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2633047 prefixEnd_2633047 := by exact prefixLift 2633047
  have htrace : WordTrace (prefixWord ++ tailWord_2633047) baseStart_2633047 baseEnd_2633047 := by
    simpa [prefixWord, tailWord_2633047, baseEnd_2633047] using wordTrace_append hprefix tailTrace_2633047
  have hstable : (prefixWord ++ tailWord_2633047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2633047).length < 2 ^ (prefixWord ++ tailWord_2633047).sum := by decide
  have hdescent : baseEnd_2633047 < baseStart_2633047 := by decide
  rcases family_descends (prefixWord ++ tailWord_2633047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2633061 : List Nat := [1, 3, 1, 3, 1, 2, 1, 6, 1, 4]
def baseStart_2633061 : Nat := 118140960795 + 2633061 * 2 ^ 59
def prefixEnd_2633061 : Nat := 4983230072969 + 3 ^ 40 * 2633061 * 2
def baseEnd_2633061 : Nat := 450675295202742623476093

theorem tailTrace_2633061 : CollatzResearch.WordTrace tailWord_2633061 prefixEnd_2633061 450675295202742623476093 := by
  unfold tailWord_2633061
  simp only [CollatzResearch.WordTrace]
  refine ⟨96035624313877162862179037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64023749542584775241452691 96035624313877162862179037)
  ·
    refine ⟨36013359117703936073317139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96035624313877162862179037 36013359117703936073317139)
    ·
      refine ⟨54020038676555904109975709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36013359117703936073317139 54020038676555904109975709)
      ·
        refine ⟨20257514503708464041240891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54020038676555904109975709 20257514503708464041240891)
        ·
          refine ⟨30386271755562696061861337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20257514503708464041240891 30386271755562696061861337)
          ·
            refine ⟨22789703816672022046396003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30386271755562696061861337 22789703816672022046396003)
            ·
              refine ⟨34184555725008033069594005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22789703816672022046396003 34184555725008033069594005)
              ·
                refine ⟨1602401049609751550137219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 34184555725008033069594005 1602401049609751550137219)
                ·
                  refine ⟨2403601574414627325205829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1602401049609751550137219 2403601574414627325205829)
                  ·
                    refine ⟨450675295202742623476093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2403601574414627325205829 450675295202742623476093)
                    ·
                      rfl

theorem cell23_2633061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 6, 1, 4].length) (baseStart_2633061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2633061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2633061 prefixEnd_2633061 := by exact prefixLift 2633061
  have htrace : WordTrace (prefixWord ++ tailWord_2633061) baseStart_2633061 baseEnd_2633061 := by
    simpa [prefixWord, tailWord_2633061, baseEnd_2633061] using wordTrace_append hprefix tailTrace_2633061
  have hstable : (prefixWord ++ tailWord_2633061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2633061).length < 2 ^ (prefixWord ++ tailWord_2633061).sum := by decide
  have hdescent : baseEnd_2633061 < baseStart_2633061 := by decide
  rcases family_descends (prefixWord ++ tailWord_2633061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2633067 : List Nat := [1, 1, 1, 1, 2, 2, 2, 1, 4, 5, 3]
def baseStart_2633067 : Nat := 118140960795 + 2633067 * 2 ^ 59
def prefixEnd_2633067 : Nat := 4983230072969 + 3 ^ 40 * 2633067 * 2
def baseEnd_2633067 : Nat := 1352028966492154846953251

theorem tailTrace_2633067 : CollatzResearch.WordTrace tailWord_2633067 prefixEnd_2633067 1352028966492154846953251 := by
  unfold tailWord_2633067
  simp only [CollatzResearch.WordTrace]
  refine ⟨96035843151855425886897455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64023895434570283924598303 96035843151855425886897455)
  ·
    refine ⟨144053764727783138830346183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96035843151855425886897455 144053764727783138830346183)
    ·
      refine ⟨216080647091674708245519275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144053764727783138830346183 216080647091674708245519275)
      ·
        refine ⟨324120970637512062368278913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216080647091674708245519275 324120970637512062368278913)
        ·
          refine ⟨243090727978134046776209185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 324120970637512062368278913 243090727978134046776209185)
          ·
            refine ⟨182318045983600535082156889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 243090727978134046776209185 182318045983600535082156889)
            ·
              refine ⟨136738534487700401311617667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 182318045983600535082156889 136738534487700401311617667)
              ·
                refine ⟨205107801731550601967426501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 136738534487700401311617667 205107801731550601967426501)
                ·
                  refine ⟨38457712824665737868892469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 205107801731550601967426501 38457712824665737868892469)
                  ·
                    refine ⟨3605410577312412925208669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38457712824665737868892469 3605410577312412925208669)
                    ·
                      refine ⟨1352028966492154846953251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3605410577312412925208669 1352028966492154846953251)
                      ·
                        rfl

theorem cell23_2633067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 4, 5, 3].length) (baseStart_2633067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2633067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2633067 prefixEnd_2633067 := by exact prefixLift 2633067
  have htrace : WordTrace (prefixWord ++ tailWord_2633067) baseStart_2633067 baseEnd_2633067 := by
    simpa [prefixWord, tailWord_2633067, baseEnd_2633067] using wordTrace_append hprefix tailTrace_2633067
  have hstable : (prefixWord ++ tailWord_2633067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2633067).length < 2 ^ (prefixWord ++ tailWord_2633067).sum := by decide
  have hdescent : baseEnd_2633067 < baseStart_2633067 := by decide
  rcases family_descends (prefixWord ++ tailWord_2633067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2633124 : List Nat := [2, 3, 1, 2, 1, 1, 1, 4, 3, 1, 4]
def baseStart_2633124 : Nat := 118140960795 + 2633124 * 2 ^ 59
def prefixEnd_2633124 : Nat := 4983230072969 + 3 ^ 40 * 2633124 * 2
def baseEnd_2633124 : Nat := 1352058234889461123940489

theorem tailTrace_2633124 : CollatzResearch.WordTrace tailWord_2633124 prefixEnd_2633124 1352058234889461123940489 := by
  unfold tailWord_2633124
  simp only [CollatzResearch.WordTrace]
  refine ⟨48018961056324462310861213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64025281408432616414481617 48018961056324462310861213)
  ·
    refine ⟨18007110396121673366572955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48018961056324462310861213 18007110396121673366572955)
    ·
      refine ⟨27010665594182510049859433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18007110396121673366572955 27010665594182510049859433)
      ·
        refine ⟨20257999195636882537394575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27010665594182510049859433 20257999195636882537394575)
        ·
          refine ⟨30386998793455323806091863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20257999195636882537394575 30386998793455323806091863)
          ·
            refine ⟨45580498190182985709137795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30386998793455323806091863 45580498190182985709137795)
            ·
              refine ⟨68370747285274478563706693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45580498190182985709137795 68370747285274478563706693)
              ·
                refine ⟨12819515115988964730695005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68370747285274478563706693 12819515115988964730695005)
                ·
                  refine ⟨4807318168495861774010627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12819515115988964730695005 4807318168495861774010627)
                  ·
                    refine ⟨7210977252743792661015941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4807318168495861774010627 7210977252743792661015941)
                    ·
                      refine ⟨1352058234889461123940489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7210977252743792661015941 1352058234889461123940489)
                      ·
                        rfl

theorem cell23_2633124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 4, 3, 1, 4].length) (baseStart_2633124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2633124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2633124 prefixEnd_2633124 := by exact prefixLift 2633124
  have htrace : WordTrace (prefixWord ++ tailWord_2633124) baseStart_2633124 baseEnd_2633124 := by
    simpa [prefixWord, tailWord_2633124, baseEnd_2633124] using wordTrace_append hprefix tailTrace_2633124
  have hstable : (prefixWord ++ tailWord_2633124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2633124).length < 2 ^ (prefixWord ++ tailWord_2633124).sum := by decide
  have hdescent : baseEnd_2633124 < baseStart_2633124 := by decide
  rcases family_descends (prefixWord ++ tailWord_2633124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2633141 : List Nat := [1, 3, 3, 2, 2, 2, 1, 1, 3, 1, 4]
def baseStart_2633141 : Nat := 118140960795 + 2633141 * 2 ^ 59
def prefixEnd_2633141 : Nat := 4983230072969 + 3 ^ 40 * 2633141 * 2
def baseEnd_2633141 : Nat := 1352066964060587557427911

theorem tailTrace_2633141 : CollatzResearch.WordTrace tailWord_2633141 prefixEnd_2633141 1352066964060587557427911 := by
  unfold tailWord_2633141
  simp only [CollatzResearch.WordTrace]
  refine ⟨96038542153587336525091277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64025694769058224350060851 96038542153587336525091277)
  ·
    refine ⟨36014453307595251196909229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96038542153587336525091277 36014453307595251196909229)
    ·
      refine ⟨13505419990348219198840961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36014453307595251196909229 13505419990348219198840961)
      ·
        refine ⟨10129064992761164399130721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13505419990348219198840961 10129064992761164399130721)
        ·
          refine ⟨7596798744570873299348041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10129064992761164399130721 7596798744570873299348041)
          ·
            refine ⟨5697599058428154974511031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7596798744570873299348041 5697599058428154974511031)
            ·
              refine ⟨8546398587642232461766547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5697599058428154974511031 8546398587642232461766547)
              ·
                refine ⟨12819597881463348692649821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8546398587642232461766547 12819597881463348692649821)
                ·
                  refine ⟨4807349205548755759743683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12819597881463348692649821 4807349205548755759743683)
                  ·
                    refine ⟨7211023808323133639615525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4807349205548755759743683 7211023808323133639615525)
                    ·
                      refine ⟨1352066964060587557427911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7211023808323133639615525 1352066964060587557427911)
                      ·
                        rfl

theorem cell23_2633141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_2633141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2633141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2633141 prefixEnd_2633141 := by exact prefixLift 2633141
  have htrace : WordTrace (prefixWord ++ tailWord_2633141) baseStart_2633141 baseEnd_2633141 := by
    simpa [prefixWord, tailWord_2633141, baseEnd_2633141] using wordTrace_append hprefix tailTrace_2633141
  have hstable : (prefixWord ++ tailWord_2633141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2633141).length < 2 ^ (prefixWord ++ tailWord_2633141).sum := by decide
  have hdescent : baseEnd_2633141 < baseStart_2633141 := by decide
  rcases family_descends (prefixWord ++ tailWord_2633141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2633181 : List Nat := [1, 4, 3, 1, 1, 4, 1, 8]
def baseStart_2633181 : Nat := 118140960795 + 2633181 * 2 ^ 59
def prefixEnd_2633181 : Nat := 4983230072969 + 3 ^ 40 * 2633181 * 2
def baseEnd_2633181 : Nat := 50077314936546940775101

theorem tailTrace_2633181 : CollatzResearch.WordTrace tailWord_2633181 prefixEnd_2633181 50077314936546940775101 := by
  unfold tailWord_2633181
  simp only [CollatzResearch.WordTrace]
  refine ⟨96040001073442423356547397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64026667382294948904364931 96040001073442423356547397)
  ·
    refine ⟨18007500201270454379352637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96040001073442423356547397 18007500201270454379352637)
    ·
      refine ⟨6752812575476420392257239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18007500201270454379352637 6752812575476420392257239)
      ·
        refine ⟨10129218863214630588385859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6752812575476420392257239 10129218863214630588385859)
        ·
          refine ⟨15193828294821945882578789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10129218863214630588385859 15193828294821945882578789)
          ·
            refine ⟨2848842805279114852983523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15193828294821945882578789 2848842805279114852983523)
            ·
              refine ⟨4273264207918672279475285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2848842805279114852983523 4273264207918672279475285)
              ·
                refine ⟨50077314936546940775101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4273264207918672279475285 50077314936546940775101)
                ·
                  rfl

theorem cell23_2633181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 1, 8].length) (baseStart_2633181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2633181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2633181 prefixEnd_2633181 := by exact prefixLift 2633181
  have htrace : WordTrace (prefixWord ++ tailWord_2633181) baseStart_2633181 baseEnd_2633181 := by
    simpa [prefixWord, tailWord_2633181, baseEnd_2633181] using wordTrace_append hprefix tailTrace_2633181
  have hstable : (prefixWord ++ tailWord_2633181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2633181).length < 2 ^ (prefixWord ++ tailWord_2633181).sum := by decide
  have hdescent : baseEnd_2633181 < baseStart_2633181 := by decide
  rcases family_descends (prefixWord ++ tailWord_2633181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2633191 : List Nat := [1, 1, 5, 2, 1, 2, 1, 3, 1, 3, 3]
def baseStart_2633191 : Nat := 118140960795 + 2633191 * 2 ^ 59
def prefixEnd_2633191 : Nat := 4983230072969 + 3 ^ 40 * 2633191 * 2
def baseEnd_2633191 : Nat := 1352092638093312361802681

theorem tailTrace_2633191 : CollatzResearch.WordTrace tailWord_2633191 prefixEnd_2633191 1352092638093312361802681 := by
  unfold tailWord_2633191
  simp only [CollatzResearch.WordTrace]
  refine ⟨96040365803406195064411427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64026910535604130042940951 96040365803406195064411427)
  ·
    refine ⟨144060548705109292596617141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96040365803406195064411427 144060548705109292596617141)
    ·
      refine ⟨13505676441103996180932857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 144060548705109292596617141 13505676441103996180932857)
      ·
        refine ⟨10129257330827997135699643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13505676441103996180932857 10129257330827997135699643)
        ·
          refine ⟨15193885996241995703549465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10129257330827997135699643 15193885996241995703549465)
          ·
            refine ⟨11395414497181496777662099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15193885996241995703549465 11395414497181496777662099)
            ·
              refine ⟨17093121745772245166493149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11395414497181496777662099 17093121745772245166493149)
              ·
                refine ⟨6409920654664591937434931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17093121745772245166493149 6409920654664591937434931)
                ·
                  refine ⟨9614880981996887906152397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6409920654664591937434931 9614880981996887906152397)
                  ·
                    refine ⟨3605580368248832964807149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9614880981996887906152397 3605580368248832964807149)
                    ·
                      refine ⟨1352092638093312361802681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3605580368248832964807149 1352092638093312361802681)
                      ·
                        rfl

theorem cell23_2633191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 3, 1, 3, 3].length) (baseStart_2633191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2633191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2633191 prefixEnd_2633191 := by exact prefixLift 2633191
  have htrace : WordTrace (prefixWord ++ tailWord_2633191) baseStart_2633191 baseEnd_2633191 := by
    simpa [prefixWord, tailWord_2633191, baseEnd_2633191] using wordTrace_append hprefix tailTrace_2633191
  have hstable : (prefixWord ++ tailWord_2633191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2633191).length < 2 ^ (prefixWord ++ tailWord_2633191).sum := by decide
  have hdescent : baseEnd_2633191 < baseStart_2633191 := by decide
  rcases family_descends (prefixWord ++ tailWord_2633191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2633224 : List Nat := [2, 1, 3, 2, 1, 1, 3, 2, 2, 6]
def baseStart_2633224 : Nat := 118140960795 + 2633224 * 2 ^ 59
def prefixEnd_2633224 : Nat := 4983230072969 + 3 ^ 40 * 2633224 * 2
def baseEnd_2633224 : Nat := 450703194318303577563343

theorem tailTrace_2633224 : CollatzResearch.WordTrace tailWord_2633224 prefixEnd_2633224 450703194318303577563343 := by
  unfold tailWord_2633224
  simp only [CollatzResearch.WordTrace]
  refine ⟨48020784706143320850181363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64027712941524427800241817 48020784706143320850181363)
  ·
    refine ⟨72031177059214981275272045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48020784706143320850181363 72031177059214981275272045)
    ·
      refine ⟨27011691397205617978227017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72031177059214981275272045 27011691397205617978227017)
      ·
        refine ⟨20258768547904213483670263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27011691397205617978227017 20258768547904213483670263)
        ·
          refine ⟨30388152821856320225505395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20258768547904213483670263 30388152821856320225505395)
          ·
            refine ⟨45582229232784480338258093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30388152821856320225505395 45582229232784480338258093)
            ·
              refine ⟨17093335962294180126846785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45582229232784480338258093 17093335962294180126846785)
              ·
                refine ⟨12820001971720635095135089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17093335962294180126846785 12820001971720635095135089)
                ·
                  refine ⟨9615001478790476321351317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12820001971720635095135089 9615001478790476321351317)
                  ·
                    refine ⟨450703194318303577563343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9615001478790476321351317 450703194318303577563343)
                    ·
                      rfl

theorem cell23_2633224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 2, 2, 6].length) (baseStart_2633224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2633224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2633224 prefixEnd_2633224 := by exact prefixLift 2633224
  have htrace : WordTrace (prefixWord ++ tailWord_2633224) baseStart_2633224 baseEnd_2633224 := by
    simpa [prefixWord, tailWord_2633224, baseEnd_2633224] using wordTrace_append hprefix tailTrace_2633224
  have hstable : (prefixWord ++ tailWord_2633224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2633224).length < 2 ^ (prefixWord ++ tailWord_2633224).sum := by decide
  have hdescent : baseEnd_2633224 < baseStart_2633224 := by decide
  rcases family_descends (prefixWord ++ tailWord_2633224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2633291 : List Nat := [1, 1, 1, 1, 3, 1, 3, 3, 2, 5, 2]
def baseStart_2633291 : Nat := 118140960795 + 2633291 * 2 ^ 59
def prefixEnd_2633291 : Nat := 4983230072969 + 3 ^ 40 * 2633291 * 2
def baseEnd_2633291 : Nat := 1352143986158761970552221

theorem tailTrace_2633291 : CollatzResearch.WordTrace tailWord_2633291 prefixEnd_2633291 1352143986158761970552221 := by
  unfold tailWord_2633291
  simp only [CollatzResearch.WordTrace]
  refine ⟨96044013103043912143051727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64029342068695941428701151 96044013103043912143051727)
  ·
    refine ⟨144066019654565868214577591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96044013103043912143051727 144066019654565868214577591)
    ·
      refine ⟨216099029481848802321866387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144066019654565868214577591 216099029481848802321866387)
      ·
        refine ⟨324148544222773203482799581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216099029481848802321866387 324148544222773203482799581)
        ·
          refine ⟨121555704083539951306049843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 324148544222773203482799581 121555704083539951306049843)
          ·
            refine ⟨182333556125309926959074765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121555704083539951306049843 182333556125309926959074765)
            ·
              refine ⟨68375083546991222609653037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 182333556125309926959074765 68375083546991222609653037)
              ·
                refine ⟨25640656330121708478619889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68375083546991222609653037 25640656330121708478619889)
                ·
                  refine ⟨19230492247591281358964917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25640656330121708478619889 19230492247591281358964917)
                  ·
                    refine ⟨1802858648211682627402961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19230492247591281358964917 1802858648211682627402961)
                    ·
                      refine ⟨1352143986158761970552221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1802858648211682627402961 1352143986158761970552221)
                      ·
                        rfl

theorem cell23_2633291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 2, 5, 2].length) (baseStart_2633291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2633291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2633291 prefixEnd_2633291 := by exact prefixLift 2633291
  have htrace : WordTrace (prefixWord ++ tailWord_2633291) baseStart_2633291 baseEnd_2633291 := by
    simpa [prefixWord, tailWord_2633291, baseEnd_2633291] using wordTrace_append hprefix tailTrace_2633291
  have hstable : (prefixWord ++ tailWord_2633291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2633291).length < 2 ^ (prefixWord ++ tailWord_2633291).sum := by decide
  have hdescent : baseEnd_2633291 < baseStart_2633291 := by decide
  rcases family_descends (prefixWord ++ tailWord_2633291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2633321 : List Nat := [1, 2, 1, 1, 1, 4, 3, 3, 2, 1, 4]
def baseStart_2633321 : Nat := 118140960795 + 2633321 * 2 ^ 59
def prefixEnd_2633321 : Nat := 4983230072969 + 3 ^ 40 * 2633321 * 2
def baseEnd_2633321 : Nat := 1352159390578396853177083

theorem tailTrace_2633321 : CollatzResearch.WordTrace tailWord_2633321 prefixEnd_2633321 1352159390578396853177083 := by
  unfold tailWord_2633321
  simp only [CollatzResearch.WordTrace]
  refine ⟨96045107292935227266643817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64030071528623484844429211 96045107292935227266643817)
  ·
    refine ⟨72033830469701420449982863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96045107292935227266643817 72033830469701420449982863)
    ·
      refine ⟨108050745704552130674974295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72033830469701420449982863 108050745704552130674974295)
      ·
        refine ⟨162076118556828196012461443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108050745704552130674974295 162076118556828196012461443)
        ·
          refine ⟨243114177835242294018692165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162076118556828196012461443 243114177835242294018692165)
          ·
            refine ⟨45583908344107930128504781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 243114177835242294018692165 45583908344107930128504781)
            ·
              refine ⟨17093965629040473798189293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45583908344107930128504781 17093965629040473798189293)
              ·
                refine ⟨6410237110890177674320985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17093965629040473798189293 6410237110890177674320985)
                ·
                  refine ⟨4807677833167633255740739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6410237110890177674320985 4807677833167633255740739)
                  ·
                    refine ⟨7211516749751449883611109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4807677833167633255740739 7211516749751449883611109)
                    ·
                      refine ⟨1352159390578396853177083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7211516749751449883611109 1352159390578396853177083)
                      ·
                        rfl

theorem cell23_2633321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 3, 2, 1, 4].length) (baseStart_2633321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2633321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2633321 prefixEnd_2633321 := by exact prefixLift 2633321
  have htrace : WordTrace (prefixWord ++ tailWord_2633321) baseStart_2633321 baseEnd_2633321 := by
    simpa [prefixWord, tailWord_2633321, baseEnd_2633321] using wordTrace_append hprefix tailTrace_2633321
  have hstable : (prefixWord ++ tailWord_2633321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2633321).length < 2 ^ (prefixWord ++ tailWord_2633321).sum := by decide
  have hdescent : baseEnd_2633321 < baseStart_2633321 := by decide
  rcases family_descends (prefixWord ++ tailWord_2633321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2633372 : List Nat := [2, 2, 3, 2, 4, 1, 1, 1, 2, 1, 4]
def baseStart_2633372 : Nat := 118140960795 + 2633372 * 2 ^ 59
def prefixEnd_2633372 : Nat := 4983230072969 + 3 ^ 40 * 2633372 * 2
def baseEnd_2633372 : Nat := 1352185578091776153639349

theorem tailTrace_2633372 : CollatzResearch.WordTrace tailWord_2633372 prefixEnd_2633372 1352185578091776153639349 := by
  unfold tailWord_2633372
  simp only [CollatzResearch.WordTrace]
  refine ⟨48023483707875231488375185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64031311610500308651166913 48023483707875231488375185)
  ·
    refine ⟨36017612780906423616281389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48023483707875231488375185 36017612780906423616281389)
    ·
      refine ⟨13506604792839908856105521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36017612780906423616281389 13506604792839908856105521)
      ·
        refine ⟨10129953594629931642079141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13506604792839908856105521 10129953594629931642079141)
        ·
          refine ⟨1899366298993112182889839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10129953594629931642079141 1899366298993112182889839)
          ·
            refine ⟨2849049448489668274334759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1899366298993112182889839 2849049448489668274334759)
            ·
              refine ⟨4273574172734502411502139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2849049448489668274334759 4273574172734502411502139)
              ·
                refine ⟨6410361259101753617253209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4273574172734502411502139 6410361259101753617253209)
                ·
                  refine ⟨4807770944326315212939907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6410361259101753617253209 4807770944326315212939907)
                  ·
                    refine ⟨7211656416489472819409861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4807770944326315212939907 7211656416489472819409861)
                    ·
                      refine ⟨1352185578091776153639349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7211656416489472819409861 1352185578091776153639349)
                      ·
                        rfl

theorem cell23_2633372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 1, 1, 2, 1, 4].length) (baseStart_2633372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2633372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2633372 prefixEnd_2633372 := by exact prefixLift 2633372
  have htrace : WordTrace (prefixWord ++ tailWord_2633372) baseStart_2633372 baseEnd_2633372 := by
    simpa [prefixWord, tailWord_2633372, baseEnd_2633372] using wordTrace_append hprefix tailTrace_2633372
  have hstable : (prefixWord ++ tailWord_2633372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2633372).length < 2 ^ (prefixWord ++ tailWord_2633372).sum := by decide
  have hdescent : baseEnd_2633372 < baseStart_2633372 := by decide
  rcases family_descends (prefixWord ++ tailWord_2633372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2633375 : List Nat := [1, 1, 2, 7, 1, 1, 1, 1, 1, 4, 3]
def baseStart_2633375 : Nat := 118140960795 + 2633375 * 2 ^ 59
def prefixEnd_2633375 : Nat := 4983230072969 + 3 ^ 40 * 2633375 * 2
def baseEnd_2633375 : Nat := 1352187118533739641901835

theorem tailTrace_2633375 : CollatzResearch.WordTrace tailWord_2633375 prefixEnd_2633375 1352187118533739641901835 := by
  unfold tailWord_2633375
  simp only [CollatzResearch.WordTrace]
  refine ⟨96047076834739594489109579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64031384556493062992739719 96047076834739594489109579)
  ·
    refine ⟨144070615252109391733664369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96047076834739594489109579 144070615252109391733664369)
    ·
      refine ⟨108052961439082043800248277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144070615252109391733664369 108052961439082043800248277)
      ·
        refine ⟨2532491283728485401568319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 108052961439082043800248277 2532491283728485401568319)
        ·
          refine ⟨3798736925592728102352479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2532491283728485401568319 3798736925592728102352479)
          ·
            refine ⟨5698105388389092153528719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3798736925592728102352479 5698105388389092153528719)
            ·
              refine ⟨8547158082583638230293079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5698105388389092153528719 8547158082583638230293079)
              ·
                refine ⟨12820737123875457345439619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8547158082583638230293079 12820737123875457345439619)
                ·
                  refine ⟨19231105685813186018159429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12820737123875457345439619 19231105685813186018159429)
                  ·
                    refine ⟨3605832316089972378404893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19231105685813186018159429 3605832316089972378404893)
                    ·
                      refine ⟨1352187118533739641901835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3605832316089972378404893 1352187118533739641901835)
                      ·
                        rfl

theorem cell23_2633375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_2633375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2633375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2633375 prefixEnd_2633375 := by exact prefixLift 2633375
  have htrace : WordTrace (prefixWord ++ tailWord_2633375) baseStart_2633375 baseEnd_2633375 := by
    simpa [prefixWord, tailWord_2633375, baseEnd_2633375] using wordTrace_append hprefix tailTrace_2633375
  have hstable : (prefixWord ++ tailWord_2633375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2633375).length < 2 ^ (prefixWord ++ tailWord_2633375).sum := by decide
  have hdescent : baseEnd_2633375 < baseStart_2633375 := by decide
  rcases family_descends (prefixWord ++ tailWord_2633375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2633405 : List Nat := [1, 4, 1, 2, 1, 2, 4, 1, 3, 1, 3]
def baseStart_2633405 : Nat := 118140960795 + 2633405 * 2 ^ 59
def prefixEnd_2633405 : Nat := 4983230072969 + 3 ^ 40 * 2633405 * 2
def baseEnd_2633405 : Nat := 1352202522953374524526697

theorem tailTrace_2633405 : CollatzResearch.WordTrace tailWord_2633405 prefixEnd_2633405 1352202522953374524526697 := by
  unfold tailWord_2633405
  simp only [CollatzResearch.WordTrace]
  refine ⟨96048171024630909612701669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64032114016420606408467779 96048171024630909612701669)
  ·
    refine ⟨18009032067118295552381563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96048171024630909612701669 18009032067118295552381563)
    ·
      refine ⟨27013548100677443328572345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18009032067118295552381563 27013548100677443328572345)
      ·
        refine ⟨20260161075508082496429259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27013548100677443328572345 20260161075508082496429259)
        ·
          refine ⟨30390241613262123744643889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20260161075508082496429259 30390241613262123744643889)
          ·
            refine ⟨22792681209946592808482917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30390241613262123744643889 22792681209946592808482917)
            ·
              refine ⟨4273627726864986151590547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22792681209946592808482917 4273627726864986151590547)
              ·
                refine ⟨6410441590297479227385821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4273627726864986151590547 6410441590297479227385821)
                ·
                  refine ⟨2403915596361554710269683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6410441590297479227385821 2403915596361554710269683)
                  ·
                    refine ⟨3605873394542332065404525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2403915596361554710269683 3605873394542332065404525)
                    ·
                      refine ⟨1352202522953374524526697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3605873394542332065404525 1352202522953374524526697)
                      ·
                        rfl

theorem cell23_2633405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4, 1, 3, 1, 3].length) (baseStart_2633405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2633405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2633405 prefixEnd_2633405 := by exact prefixLift 2633405
  have htrace : WordTrace (prefixWord ++ tailWord_2633405) baseStart_2633405 baseEnd_2633405 := by
    simpa [prefixWord, tailWord_2633405, baseEnd_2633405] using wordTrace_append hprefix tailTrace_2633405
  have hstable : (prefixWord ++ tailWord_2633405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2633405).length < 2 ^ (prefixWord ++ tailWord_2633405).sum := by decide
  have hdescent : baseEnd_2633405 < baseStart_2633405 := by decide
  rcases family_descends (prefixWord ++ tailWord_2633405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2633431 : List Nat := [1, 1, 3, 2, 1, 3, 1, 2, 3, 1, 5]
def baseStart_2633431 : Nat := 118140960795 + 2633431 * 2 ^ 59
def prefixEnd_2633431 : Nat := 4983230072969 + 3 ^ 40 * 2633431 * 2
def baseEnd_2633431 : Nat := 1352215873450391422801577

theorem tailTrace_2633431 : CollatzResearch.WordTrace tailWord_2633431 prefixEnd_2633431 1352215873450391422801577 := by
  unfold tailWord_2633431
  simp only [CollatzResearch.WordTrace]
  refine ⟨96049119322536716053148147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64032746215024477368765431 96049119322536716053148147)
  ·
    refine ⟨144073678983805074079722221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96049119322536716053148147 144073678983805074079722221)
    ·
      refine ⟨54027629618926902779895833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144073678983805074079722221 54027629618926902779895833)
      ·
        refine ⟨40520722214195177084921875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54027629618926902779895833 40520722214195177084921875)
        ·
          refine ⟨60781083321292765627382813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40520722214195177084921875 60781083321292765627382813)
          ·
            refine ⟨22792906245484787110268555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60781083321292765627382813 22792906245484787110268555)
            ·
              refine ⟨34189359368227180665402833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22792906245484787110268555 34189359368227180665402833)
              ·
                refine ⟨25642019526170385499052125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34189359368227180665402833 25642019526170385499052125)
                ·
                  refine ⟨9615757322313894562144547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25642019526170385499052125 9615757322313894562144547)
                  ·
                    refine ⟨14423635983470841843216821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9615757322313894562144547 14423635983470841843216821)
                    ·
                      refine ⟨1352215873450391422801577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14423635983470841843216821 1352215873450391422801577)
                      ·
                        rfl

theorem cell23_2633431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 2, 3, 1, 5].length) (baseStart_2633431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2633431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2633431 prefixEnd_2633431 := by exact prefixLift 2633431
  have htrace : WordTrace (prefixWord ++ tailWord_2633431) baseStart_2633431 baseEnd_2633431 := by
    simpa [prefixWord, tailWord_2633431, baseEnd_2633431] using wordTrace_append hprefix tailTrace_2633431
  have hstable : (prefixWord ++ tailWord_2633431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2633431).length < 2 ^ (prefixWord ++ tailWord_2633431).sum := by decide
  have hdescent : baseEnd_2633431 < baseStart_2633431 := by decide
  rcases family_descends (prefixWord ++ tailWord_2633431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2633448 : List Nat := [2, 1, 4, 1, 3, 1, 1, 3, 1, 1, 5]
def baseStart_2633448 : Nat := 118140960795 + 2633448 * 2 ^ 59
def prefixEnd_2633448 : Nat := 4983230072969 + 3 ^ 40 * 2633448 * 2
def baseEnd_2633448 : Nat := 1352224602621517856288999

theorem tailTrace_2633448 : CollatzResearch.WordTrace tailWord_2633448 prefixEnd_2633448 1352224602621517856288999 := by
  unfold tailWord_2633448
  simp only [CollatzResearch.WordTrace]
  refine ⟨48024869681737563978258499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64033159575650085304344665 48024869681737563978258499)
  ·
    refine ⟨72037304522606345967387749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48024869681737563978258499 72037304522606345967387749)
    ·
      refine ⟨13506994597988689868885203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72037304522606345967387749 13506994597988689868885203)
      ·
        refine ⟨20260491896983034803327805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13506994597988689868885203 20260491896983034803327805)
        ·
          refine ⟨7597684461368638051247927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20260491896983034803327805 7597684461368638051247927)
          ·
            refine ⟨11396526692052957076871891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7597684461368638051247927 11396526692052957076871891)
            ·
              refine ⟨17094790038079435615307837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11396526692052957076871891 17094790038079435615307837)
              ·
                refine ⟨6410546264279788355740439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17094790038079435615307837 6410546264279788355740439)
                ·
                  refine ⟨9615819396419682533610659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6410546264279788355740439 9615819396419682533610659)
                  ·
                    refine ⟨14423729094629523800415989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9615819396419682533610659 14423729094629523800415989)
                    ·
                      refine ⟨1352224602621517856288999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14423729094629523800415989 1352224602621517856288999)
                      ·
                        rfl

theorem cell23_2633448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 3, 1, 1, 5].length) (baseStart_2633448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2633448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2633448 prefixEnd_2633448 := by exact prefixLift 2633448
  have htrace : WordTrace (prefixWord ++ tailWord_2633448) baseStart_2633448 baseEnd_2633448 := by
    simpa [prefixWord, tailWord_2633448, baseEnd_2633448] using wordTrace_append hprefix tailTrace_2633448
  have hstable : (prefixWord ++ tailWord_2633448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2633448).length < 2 ^ (prefixWord ++ tailWord_2633448).sum := by decide
  have hdescent : baseEnd_2633448 < baseStart_2633448 := by decide
  rcases family_descends (prefixWord ++ tailWord_2633448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2633479 : List Nat := [1, 1, 4, 4, 3, 1, 1, 2, 1, 1, 4]
def baseStart_2633479 : Nat := 118140960795 + 2633479 * 2 ^ 59
def prefixEnd_2633479 : Nat := 4983230072969 + 3 ^ 40 * 2633479 * 2
def baseEnd_2633479 : Nat := 1352240520521807235001357

theorem tailTrace_2633479 : CollatzResearch.WordTrace tailWord_2633479 prefixEnd_2633479 1352240520521807235001357 := by
  unfold tailWord_2633479
  simp only [CollatzResearch.WordTrace]
  refine ⟨96050870026362820250895491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64033913350908546833930327 96050870026362820250895491)
  ·
    refine ⟨144076305039544230376343237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96050870026362820250895491 144076305039544230376343237)
    ·
      refine ⟨27014307194914543195564357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 144076305039544230376343237 27014307194914543195564357)
      ·
        refine ⟨5065182599046476849168317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27014307194914543195564357 5065182599046476849168317)
        ·
          refine ⟨1899443474642428818438119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5065182599046476849168317 1899443474642428818438119)
          ·
            refine ⟨2849165211963643227657179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1899443474642428818438119 2849165211963643227657179)
            ·
              refine ⟨4273747817945464841485769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2849165211963643227657179 4273747817945464841485769)
              ·
                refine ⟨3205310863459098631114327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4273747817945464841485769 3205310863459098631114327)
                ·
                  refine ⟨4807966295188647946671491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3205310863459098631114327 4807966295188647946671491)
                  ·
                    refine ⟨7211949442782971920007237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4807966295188647946671491 7211949442782971920007237)
                    ·
                      refine ⟨1352240520521807235001357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7211949442782971920007237 1352240520521807235001357)
                      ·
                        rfl

theorem cell23_2633479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 2, 1, 1, 4].length) (baseStart_2633479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2633479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2633479 prefixEnd_2633479 := by exact prefixLift 2633479
  have htrace : WordTrace (prefixWord ++ tailWord_2633479) baseStart_2633479 baseEnd_2633479 := by
    simpa [prefixWord, tailWord_2633479, baseEnd_2633479] using wordTrace_append hprefix tailTrace_2633479
  have hstable : (prefixWord ++ tailWord_2633479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2633479).length < 2 ^ (prefixWord ++ tailWord_2633479).sum := by decide
  have hdescent : baseEnd_2633479 < baseStart_2633479 := by decide
  rcases family_descends (prefixWord ++ tailWord_2633479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2633482 : List Nat := [3, 1, 2, 2, 1, 5, 1, 2, 1, 2, 3]
def baseStart_2633482 : Nat := 118140960795 + 2633482 * 2 ^ 59
def prefixEnd_2633482 : Nat := 4983230072969 + 3 ^ 40 * 2633482 * 2
def baseEnd_2633482 : Nat := 1352242060963770723263843

theorem tailTrace_2633482 : CollatzResearch.WordTrace tailWord_2633482 prefixEnd_2633482 1352242060963770723263843 := by
  unfold tailWord_2633482
  simp only [CollatzResearch.WordTrace]
  refine ⟨24012744861337987940813675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64033986296901301175503133 24012744861337987940813675)
  ·
    refine ⟨36019117292006981911220513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24012744861337987940813675 36019117292006981911220513)
    ·
      refine ⟨27014337969005236433415385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36019117292006981911220513 27014337969005236433415385)
      ·
        refine ⟨20260753476753927325061539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27014337969005236433415385 20260753476753927325061539)
        ·
          refine ⟨30391130215130890987592309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20260753476753927325061539 30391130215130890987592309)
          ·
            refine ⟨2849168457668521030086779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30391130215130890987592309 2849168457668521030086779)
            ·
              refine ⟨4273752686502781545130169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2849168457668521030086779 4273752686502781545130169)
              ·
                refine ⟨3205314514877086158847627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4273752686502781545130169 3205314514877086158847627)
                ·
                  refine ⟨4807971772315629238271441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3205314514877086158847627 4807971772315629238271441)
                  ·
                    refine ⟨3605978829236721928703581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4807971772315629238271441 3605978829236721928703581)
                    ·
                      refine ⟨1352242060963770723263843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3605978829236721928703581 1352242060963770723263843)
                      ·
                        rfl

theorem cell23_2633482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 1, 2, 1, 2, 3].length) (baseStart_2633482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2633482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2633482 prefixEnd_2633482 := by exact prefixLift 2633482
  have htrace : WordTrace (prefixWord ++ tailWord_2633482) baseStart_2633482 baseEnd_2633482 := by
    simpa [prefixWord, tailWord_2633482, baseEnd_2633482] using wordTrace_append hprefix tailTrace_2633482
  have hstable : (prefixWord ++ tailWord_2633482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2633482).length < 2 ^ (prefixWord ++ tailWord_2633482).sum := by decide
  have hdescent : baseEnd_2633482 < baseStart_2633482 := by decide
  rcases family_descends (prefixWord ++ tailWord_2633482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2633491 : List Nat := [1, 1, 1, 2, 1, 3, 2, 3, 2, 2, 5]
def baseStart_2633491 : Nat := 118140960795 + 2633491 * 2 ^ 59
def prefixEnd_2633491 : Nat := 4983230072969 + 3 ^ 40 * 2633491 * 2
def baseEnd_2633491 : Nat := 1352246682289661188051301

theorem tailTrace_2633491 : CollatzResearch.WordTrace tailWord_2633491 prefixEnd_2633491 1352246682289661188051301 := by
  unfold tailWord_2633491
  simp only [CollatzResearch.WordTrace]
  refine ⟨96051307702319346300332327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64034205134879564200221551 96051307702319346300332327)
  ·
    refine ⟨144076961553479019450498491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96051307702319346300332327 144076961553479019450498491)
    ·
      refine ⟨216115442330218529175747737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144076961553479019450498491 216115442330218529175747737)
      ·
        refine ⟨162086581747663896881810803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 216115442330218529175747737 162086581747663896881810803)
        ·
          refine ⟨243129872621495845322716205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162086581747663896881810803 243129872621495845322716205)
          ·
            refine ⟨91173702233060941996018577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 243129872621495845322716205 91173702233060941996018577)
            ·
              refine ⟨68380276674795706497013933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91173702233060941996018577 68380276674795706497013933)
              ·
                refine ⟨25642603753048389936380225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68380276674795706497013933 25642603753048389936380225)
                ·
                  refine ⟨19231952814786292452285169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25642603753048389936380225 19231952814786292452285169)
                  ·
                    refine ⟨14423964611089719339213877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19231952814786292452285169 14423964611089719339213877)
                    ·
                      refine ⟨1352246682289661188051301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14423964611089719339213877 1352246682289661188051301)
                      ·
                        rfl

theorem cell23_2633491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 3, 2, 2, 5].length) (baseStart_2633491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2633491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2633491 prefixEnd_2633491 := by exact prefixLift 2633491
  have htrace : WordTrace (prefixWord ++ tailWord_2633491) baseStart_2633491 baseEnd_2633491 := by
    simpa [prefixWord, tailWord_2633491, baseEnd_2633491] using wordTrace_append hprefix tailTrace_2633491
  have hstable : (prefixWord ++ tailWord_2633491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2633491).length < 2 ^ (prefixWord ++ tailWord_2633491).sum := by decide
  have hdescent : baseEnd_2633491 < baseStart_2633491 := by decide
  rcases family_descends (prefixWord ++ tailWord_2633491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2633495 : List Nat := [1, 1, 3, 4, 2, 2, 1, 2, 1, 3, 3]
def baseStart_2633495 : Nat := 118140960795 + 2633495 * 2 ^ 59
def prefixEnd_2633495 : Nat := 4983230072969 + 3 ^ 40 * 2633495 * 2
def baseEnd_2633495 : Nat := 1352248736212279172401283

theorem tailTrace_2633495 : CollatzResearch.WordTrace tailWord_2633495 prefixEnd_2633495 1352248736212279172401283 := by
  unfold tailWord_2633495
  simp only [CollatzResearch.WordTrace]
  refine ⟨96051453594304854983477939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64034302396203236655651959 96051453594304854983477939)
  ·
    refine ⟨144077180391457282475216909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96051453594304854983477939 144077180391457282475216909)
    ·
      refine ⟨54028942646796480928206341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144077180391457282475216909 54028942646796480928206341)
      ·
        refine ⟨10130426746274340174038689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54028942646796480928206341 10130426746274340174038689)
        ·
          refine ⟨7597820059705755130529017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10130426746274340174038689 7597820059705755130529017)
          ·
            refine ⟨5698365044779316347896763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7597820059705755130529017 5698365044779316347896763)
            ·
              refine ⟨8547547567168974521845145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5698365044779316347896763 8547547567168974521845145)
              ·
                refine ⟨6410660675376730891383859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8547547567168974521845145 6410660675376730891383859)
                ·
                  refine ⟨9615991013065096337075789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6410660675376730891383859 9615991013065096337075789)
                  ·
                    refine ⟨3605996629899411126403421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9615991013065096337075789 3605996629899411126403421)
                    ·
                      refine ⟨1352248736212279172401283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3605996629899411126403421 1352248736212279172401283)
                      ·
                        rfl

theorem cell23_2633495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 2, 1, 3, 3].length) (baseStart_2633495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2633495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2633495 prefixEnd_2633495 := by exact prefixLift 2633495
  have htrace : WordTrace (prefixWord ++ tailWord_2633495) baseStart_2633495 baseEnd_2633495 := by
    simpa [prefixWord, tailWord_2633495, baseEnd_2633495] using wordTrace_append hprefix tailTrace_2633495
  have hstable : (prefixWord ++ tailWord_2633495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2633495).length < 2 ^ (prefixWord ++ tailWord_2633495).sum := by decide
  have hdescent : baseEnd_2633495 < baseStart_2633495 := by decide
  rcases family_descends (prefixWord ++ tailWord_2633495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2633502 : List Nat := [4, 3, 2, 2, 2, 10]
def baseStart_2633502 : Nat := 118140960795 + 2633502 * 2 ^ 59
def prefixEnd_2633502 : Nat := 4983230072969 + 3 ^ 40 * 2633502 * 2
def baseEnd_2633502 : Nat := 5564824405666093189357

theorem tailTrace_2633502 : CollatzResearch.WordTrace tailWord_2633502 prefixEnd_2633502 5564824405666093189357 := by
  unfold tailWord_2633502
  simp only [CollatzResearch.WordTrace]
  refine ⟨12006463613159936897372845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64034472603519663452655173 12006463613159936897372845)
  ·
    refine ⟨4502423854934976336514817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12006463613159936897372845 4502423854934976336514817)
    ·
      refine ⟨3376817891201232252386113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4502423854934976336514817 3376817891201232252386113)
      ·
        refine ⟨2532613418400924189289585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3376817891201232252386113 2532613418400924189289585)
        ·
          refine ⟨1899460063800693141967189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2532613418400924189289585 1899460063800693141967189)
          ·
            refine ⟨5564824405666093189357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1899460063800693141967189 5564824405666093189357)
            ·
              rfl

theorem cell23_2633502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 10].length) (baseStart_2633502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2633502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2633502 prefixEnd_2633502 := by exact prefixLift 2633502
  have htrace : WordTrace (prefixWord ++ tailWord_2633502) baseStart_2633502 baseEnd_2633502 := by
    simpa [prefixWord, tailWord_2633502, baseEnd_2633502] using wordTrace_append hprefix tailTrace_2633502
  have hstable : (prefixWord ++ tailWord_2633502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2633502).length < 2 ^ (prefixWord ++ tailWord_2633502).sum := by decide
  have hdescent : baseEnd_2633502 < baseStart_2633502 := by decide
  rcases family_descends (prefixWord ++ tailWord_2633502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2633512 : List Nat := [2, 1, 5, 1, 1, 2, 1, 4, 2, 1, 3]
def baseStart_2633512 : Nat := 118140960795 + 2633512 * 2 ^ 59
def prefixEnd_2633512 : Nat := 4983230072969 + 3 ^ 40 * 2633512 * 2
def baseEnd_2633512 : Nat := 1352257465383405605888705

theorem tailTrace_2633512 : CollatzResearch.WordTrace tailWord_2633512 prefixEnd_2633512 1352257465383405605888705 := by
  unfold tailWord_2633512
  simp only [CollatzResearch.WordTrace]
  refine ⟨48026036817621633443423395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64034715756828844591231193 48026036817621633443423395)
  ·
    refine ⟨72039055226432450165135093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48026036817621633443423395 72039055226432450165135093)
    ·
      refine ⟨6753661427478042202981415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 72039055226432450165135093 6753661427478042202981415)
      ·
        refine ⟨10130492141217063304472123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6753661427478042202981415 10130492141217063304472123)
        ·
          refine ⟨15195738211825594956708185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10130492141217063304472123 15195738211825594956708185)
          ·
            refine ⟨11396803658869196217531139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15195738211825594956708185 11396803658869196217531139)
            ·
              refine ⟨17095205488303794326296709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11396803658869196217531139 17095205488303794326296709)
              ·
                refine ⟨3205351029056961436180633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17095205488303794326296709 3205351029056961436180633)
                ·
                  refine ⟨2404013271792721077135475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3205351029056961436180633 2404013271792721077135475)
                  ·
                    refine ⟨3606019907689081615703213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2404013271792721077135475 3606019907689081615703213)
                    ·
                      refine ⟨1352257465383405605888705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3606019907689081615703213 1352257465383405605888705)
                      ·
                        rfl

theorem cell23_2633512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 4, 2, 1, 3].length) (baseStart_2633512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2633512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2633512 prefixEnd_2633512 := by exact prefixLift 2633512
  have htrace : WordTrace (prefixWord ++ tailWord_2633512) baseStart_2633512 baseEnd_2633512 := by
    simpa [prefixWord, tailWord_2633512, baseEnd_2633512] using wordTrace_append hprefix tailTrace_2633512
  have hstable : (prefixWord ++ tailWord_2633512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2633512).length < 2 ^ (prefixWord ++ tailWord_2633512).sum := by decide
  have hdescent : baseEnd_2633512 < baseStart_2633512 := by decide
  rcases family_descends (prefixWord ++ tailWord_2633512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2633528 : List Nat := [2, 1, 2, 1, 3, 4, 1, 1, 2, 6]
def baseStart_2633528 : Nat := 118140960795 + 2633528 * 2 ^ 59
def prefixEnd_2633528 : Nat := 4983230072969 + 3 ^ 40 * 2633528 * 2
def baseEnd_2633528 : Nat := 450755227024625847762877

theorem tailTrace_2633528 : CollatzResearch.WordTrace tailWord_2633528 prefixEnd_2633528 450755227024625847762877 := by
  unfold tailWord_2633528
  simp only [CollatzResearch.WordTrace]
  refine ⟨48026328601592650809714619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64035104802123534412952825 48026328601592650809714619)
  ·
    refine ⟨72039492902388976214571929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48026328601592650809714619 72039492902388976214571929)
    ·
      refine ⟨54029619676791732160928947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72039492902388976214571929 54029619676791732160928947)
      ·
        refine ⟨81044429515187598241393421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54029619676791732160928947 81044429515187598241393421)
        ·
          refine ⟨30391661068195349340522533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81044429515187598241393421 30391661068195349340522533)
          ·
            refine ⟨5698436450286628001347975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30391661068195349340522533 5698436450286628001347975)
            ·
              refine ⟨8547654675429942002021963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5698436450286628001347975 8547654675429942002021963)
              ·
                refine ⟨12821482013144913003032945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8547654675429942002021963 12821482013144913003032945)
                ·
                  refine ⟨9616111509858684752274709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12821482013144913003032945 9616111509858684752274709)
                  ·
                    refine ⟨450755227024625847762877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9616111509858684752274709 450755227024625847762877)
                    ·
                      rfl

theorem cell23_2633528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 1, 2, 6].length) (baseStart_2633528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2633528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2633528 prefixEnd_2633528 := by exact prefixLift 2633528
  have htrace : WordTrace (prefixWord ++ tailWord_2633528) baseStart_2633528 baseEnd_2633528 := by
    simpa [prefixWord, tailWord_2633528, baseEnd_2633528] using wordTrace_append hprefix tailTrace_2633528
  have hstable : (prefixWord ++ tailWord_2633528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2633528).length < 2 ^ (prefixWord ++ tailWord_2633528).sum := by decide
  have hdescent : baseEnd_2633528 < baseStart_2633528 := by decide
  rcases family_descends (prefixWord ++ tailWord_2633528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2633556 : List Nat := [2, 4, 1, 1, 3, 3, 2, 1, 1, 3, 2]
def baseStart_2633556 : Nat := 118140960795 + 2633556 * 2 ^ 59
def prefixEnd_2633556 : Nat := 4983230072969 + 3 ^ 40 * 2633556 * 2
def baseEnd_2633556 : Nat := 1352280058532203433738503

theorem tailTrace_2633556 : CollatzResearch.WordTrace tailWord_2633556 prefixEnd_2633556 1352280058532203433738503 := by
  unfold tailWord_2633556
  simp only [CollatzResearch.WordTrace]
  refine ⟨48026839223541931200724261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64035785631389241600965681 48026839223541931200724261)
  ·
    refine ⟨9005032354414112100135799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48026839223541931200724261 9005032354414112100135799)
    ·
      refine ⟨13507548531621168150203699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9005032354414112100135799 13507548531621168150203699)
      ·
        refine ⟨20261322797431752225305549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13507548531621168150203699 20261322797431752225305549)
        ·
          refine ⟨7597996049036907084489581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20261322797431752225305549 7597996049036907084489581)
          ·
            refine ⟨2849248518388840156683593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7597996049036907084489581 2849248518388840156683593)
            ·
              refine ⟨2136936388791630117512695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2849248518388840156683593 2136936388791630117512695)
              ·
                refine ⟨3205404583187445176269043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2136936388791630117512695 3205404583187445176269043)
                ·
                  refine ⟨4808106874781167764403565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3205404583187445176269043 4808106874781167764403565)
                  ·
                    refine ⟨1803040078042937911651337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4808106874781167764403565 1803040078042937911651337)
                    ·
                      refine ⟨1352280058532203433738503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1803040078042937911651337 1352280058532203433738503)
                      ·
                        rfl

theorem cell23_2633556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 2, 1, 1, 3, 2].length) (baseStart_2633556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2633556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2633556 prefixEnd_2633556 := by exact prefixLift 2633556
  have htrace : WordTrace (prefixWord ++ tailWord_2633556) baseStart_2633556 baseEnd_2633556 := by
    simpa [prefixWord, tailWord_2633556, baseEnd_2633556] using wordTrace_append hprefix tailTrace_2633556
  have hstable : (prefixWord ++ tailWord_2633556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2633556).length < 2 ^ (prefixWord ++ tailWord_2633556).sum := by decide
  have hdescent : baseEnd_2633556 < baseStart_2633556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2633556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2633575 : List Nat := [1, 1, 5, 1, 2, 1, 1, 6, 5]
def baseStart_2633575 : Nat := 118140960795 + 2633575 * 2 ^ 59
def prefixEnd_2633575 : Nat := 4983230072969 + 3 ^ 40 * 2633575 * 2
def baseEnd_2633575 : Nat := 150254423851626539933435

theorem tailTrace_2633575 : CollatzResearch.WordTrace tailWord_2633575 prefixEnd_2633575 150254423851626539933435 := by
  unfold tailWord_2633575
  simp only [CollatzResearch.WordTrace]
  refine ⟨96054371434015028646390179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64036247622676685764260119 96054371434015028646390179)
  ·
    refine ⟨144081557151022542969585269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96054371434015028646390179 144081557151022542969585269)
    ·
      refine ⟨13507645982908363403398619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 144081557151022542969585269 13507645982908363403398619)
      ·
        refine ⟨20261468974362545105097929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13507645982908363403398619 20261468974362545105097929)
        ·
          refine ⟨15196101730771908828823447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20261468974362545105097929 15196101730771908828823447)
          ·
            refine ⟨22794152596157863243235171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15196101730771908828823447 22794152596157863243235171)
            ·
              refine ⟨34191228894236794864852757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22794152596157863243235171 34191228894236794864852757)
              ·
                refine ⟨1602713854417349759289973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 34191228894236794864852757 1602713854417349759289973)
                ·
                  refine ⟨150254423851626539933435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1602713854417349759289973 150254423851626539933435)
                  ·
                    rfl

theorem cell23_2633575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 6, 5].length) (baseStart_2633575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2633575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2633575 prefixEnd_2633575 := by exact prefixLift 2633575
  have htrace : WordTrace (prefixWord ++ tailWord_2633575) baseStart_2633575 baseEnd_2633575 := by
    simpa [prefixWord, tailWord_2633575, baseEnd_2633575] using wordTrace_append hprefix tailTrace_2633575
  have hstable : (prefixWord ++ tailWord_2633575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2633575).length < 2 ^ (prefixWord ++ tailWord_2633575).sum := by decide
  have hdescent : baseEnd_2633575 < baseStart_2633575 := by decide
  rcases family_descends (prefixWord ++ tailWord_2633575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2633625 : List Nat := [1, 2, 1, 2, 1, 3, 2, 1, 4, 4, 2]
def baseStart_2633625 : Nat := 118140960795 + 2633625 * 2 ^ 59
def prefixEnd_2633625 : Nat := 4983230072969 + 3 ^ 40 * 2633625 * 2
def baseEnd_2633625 : Nat := 1352315488697363663775685

theorem tailTrace_2633625 : CollatzResearch.WordTrace tailWord_2633625 prefixEnd_2633625 1352315488697363663775685 := by
  unfold tailWord_2633625
  simp only [CollatzResearch.WordTrace]
  refine ⟨96056195083833887185710329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64037463389222591457140219 96056195083833887185710329)
  ·
    refine ⟨72042146312875415389282747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96056195083833887185710329 72042146312875415389282747)
    ·
      refine ⟨108063219469313123083924121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72042146312875415389282747 108063219469313123083924121)
      ·
        refine ⟨81047414601984842312943091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108063219469313123083924121 81047414601984842312943091)
        ·
          refine ⟨121571121902977263469414637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81047414601984842312943091 121571121902977263469414637)
          ·
            refine ⟨45589170713616473801030489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 121571121902977263469414637 45589170713616473801030489)
            ·
              refine ⟨34191878035212355350772867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45589170713616473801030489 34191878035212355350772867)
              ·
                refine ⟨51287817052818533026159301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34191878035212355350772867 51287817052818533026159301)
                ·
                  refine ⟨9616465697403474942404869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51287817052818533026159301 9616465697403474942404869)
                  ·
                    refine ⟨1803087318263151551700913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9616465697403474942404869 1803087318263151551700913)
                    ·
                      refine ⟨1352315488697363663775685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1803087318263151551700913 1352315488697363663775685)
                      ·
                        rfl

theorem cell23_2633625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 4, 4, 2].length) (baseStart_2633625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2633625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2633625 prefixEnd_2633625 := by exact prefixLift 2633625
  have htrace : WordTrace (prefixWord ++ tailWord_2633625) baseStart_2633625 baseEnd_2633625 := by
    simpa [prefixWord, tailWord_2633625, baseEnd_2633625] using wordTrace_append hprefix tailTrace_2633625
  have hstable : (prefixWord ++ tailWord_2633625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2633625).length < 2 ^ (prefixWord ++ tailWord_2633625).sum := by decide
  have hdescent : baseEnd_2633625 < baseStart_2633625 := by decide
  rcases family_descends (prefixWord ++ tailWord_2633625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2633662 : List Nat := [4, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3]
def baseStart_2633662 : Nat := 118140960795 + 2633662 * 2 ^ 59
def prefixEnd_2633662 : Nat := 4983230072969 + 3 ^ 40 * 2633662 * 2
def baseEnd_2633662 : Nat := 1352334487481580019013015

theorem tailTrace_2633662 : CollatzResearch.WordTrace tailWord_2633662 prefixEnd_2633662 1352334487481580019013015 := by
  unfold tailWord_2633662
  simp only [CollatzResearch.WordTrace]
  refine ⟨12007193073087480313100905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64038363056466561669871493 12007193073087480313100905)
  ·
    refine ⟨9005394804815610234825679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12007193073087480313100905 9005394804815610234825679)
    ·
      refine ⟨13508092207223415352238519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9005394804815610234825679 13508092207223415352238519)
      ·
        refine ⟨20262138310835123028357779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13508092207223415352238519 20262138310835123028357779)
        ·
          refine ⟨30393207466252684542536669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20262138310835123028357779 30393207466252684542536669)
          ·
            refine ⟨11397452799844756703451251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30393207466252684542536669 11397452799844756703451251)
            ·
              refine ⟨17096179199767135055176877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11397452799844756703451251 17096179199767135055176877)
              ·
                refine ⟨6411067199912675645691329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17096179199767135055176877 6411067199912675645691329)
                ·
                  refine ⟨4808300399934506734268497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6411067199912675645691329 4808300399934506734268497)
                  ·
                    refine ⟨3606225299950880050701373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4808300399934506734268497 3606225299950880050701373)
                    ·
                      refine ⟨1352334487481580019013015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3606225299950880050701373 1352334487481580019013015)
                      ·
                        rfl

theorem cell23_2633662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3].length) (baseStart_2633662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2633662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2633662 prefixEnd_2633662 := by exact prefixLift 2633662
  have htrace : WordTrace (prefixWord ++ tailWord_2633662) baseStart_2633662 baseEnd_2633662 := by
    simpa [prefixWord, tailWord_2633662, baseEnd_2633662] using wordTrace_append hprefix tailTrace_2633662
  have hstable : (prefixWord ++ tailWord_2633662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2633662).length < 2 ^ (prefixWord ++ tailWord_2633662).sum := by decide
  have hdescent : baseEnd_2633662 < baseStart_2633662 := by decide
  rcases family_descends (prefixWord ++ tailWord_2633662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2633695 : List Nat := [1, 1, 2, 3, 4, 1, 1, 2, 3, 5]
def baseStart_2633695 : Nat := 118140960795 + 2633695 * 2 ^ 59
def prefixEnd_2633695 : Nat := 4983230072969 + 3 ^ 40 * 2633695 * 2
def baseEnd_2633695 : Nat := 450783810781059463300121

theorem tailTrace_2633695 : CollatzResearch.WordTrace tailWord_2633695 prefixEnd_2633695 450783810781059463300121 := by
  unfold tailWord_2633695
  simp only [CollatzResearch.WordTrace]
  refine ⟨96058748193580289140758539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64039165462386859427172359 96058748193580289140758539)
  ·
    refine ⟨144088122290370433711137809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96058748193580289140758539 144088122290370433711137809)
    ·
      refine ⟨108066091717777825283353357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144088122290370433711137809 108066091717777825283353357)
      ·
        refine ⟨40524784394166684481257509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108066091717777825283353357 40524784394166684481257509)
        ·
          refine ⟨7598397073906253340235783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40524784394166684481257509 7598397073906253340235783)
          ·
            refine ⟨11397595610859380010353675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7598397073906253340235783 11397595610859380010353675)
            ·
              refine ⟨17096393416289070015530513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11397595610859380010353675 17096393416289070015530513)
              ·
                refine ⟨12822295062216802511647885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17096393416289070015530513 12822295062216802511647885)
                ·
                  refine ⟨4808360648331300941867957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12822295062216802511647885 4808360648331300941867957)
                  ·
                    refine ⟨450783810781059463300121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4808360648331300941867957 450783810781059463300121)
                    ·
                      rfl

theorem cell23_2633695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 2, 3, 5].length) (baseStart_2633695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2633695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2633695 prefixEnd_2633695 := by exact prefixLift 2633695
  have htrace : WordTrace (prefixWord ++ tailWord_2633695) baseStart_2633695 baseEnd_2633695 := by
    simpa [prefixWord, tailWord_2633695, baseEnd_2633695] using wordTrace_append hprefix tailTrace_2633695
  have hstable : (prefixWord ++ tailWord_2633695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2633695).length < 2 ^ (prefixWord ++ tailWord_2633695).sum := by decide
  have hdescent : baseEnd_2633695 < baseStart_2633695 := by decide
  rcases family_descends (prefixWord ++ tailWord_2633695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2633725 : List Nat := [1, 4, 1, 1, 1, 2, 4, 2, 1, 6]
def baseStart_2633725 : Nat := 118140960795 + 2633725 * 2 ^ 59
def prefixEnd_2633725 : Nat := 4983230072969 + 3 ^ 40 * 2633725 * 2
def baseEnd_2633725 : Nat := 450788945587604424175075

theorem tailTrace_2633725 : CollatzResearch.WordTrace tailWord_2633725 prefixEnd_2633725 450788945587604424175075 := by
  unfold tailWord_2633725
  simp only [CollatzResearch.WordTrace]
  refine ⟨96059842383471604264350629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64039894922314402842900419 96059842383471604264350629)
  ·
    refine ⟨18011220446900925799565743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96059842383471604264350629 18011220446900925799565743)
    ·
      refine ⟨27016830670351388699348615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18011220446900925799565743 27016830670351388699348615)
      ·
        refine ⟨40525246005527083049022923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27016830670351388699348615 40525246005527083049022923)
        ·
          refine ⟨60787869008290624573534385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40525246005527083049022923 60787869008290624573534385)
          ·
            refine ⟨45590901756217968430150789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60787869008290624573534385 45590901756217968430150789)
            ·
              refine ⟨8548294079290869080653273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45590901756217968430150789 8548294079290869080653273)
              ·
                refine ⟨6411220559468151810489955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8548294079290869080653273 6411220559468151810489955)
                ·
                  refine ⟨9616830839202227715734933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6411220559468151810489955 9616830839202227715734933)
                  ·
                    refine ⟨450788945587604424175075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9616830839202227715734933 450788945587604424175075)
                    ·
                      rfl

theorem cell23_2633725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 2, 1, 6].length) (baseStart_2633725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2633725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2633725 prefixEnd_2633725 := by exact prefixLift 2633725
  have htrace : WordTrace (prefixWord ++ tailWord_2633725) baseStart_2633725 baseEnd_2633725 := by
    simpa [prefixWord, tailWord_2633725, baseEnd_2633725] using wordTrace_append hprefix tailTrace_2633725
  have hstable : (prefixWord ++ tailWord_2633725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2633725).length < 2 ^ (prefixWord ++ tailWord_2633725).sum := by decide
  have hdescent : baseEnd_2633725 < baseStart_2633725 := by decide
  rcases family_descends (prefixWord ++ tailWord_2633725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2633742 : List Nat := [4, 1, 1, 2, 2, 1, 3, 1, 4, 4]
def baseStart_2633742 : Nat := 118140960795 + 2633742 * 2 ^ 59
def prefixEnd_2633742 : Nat := 4983230072969 + 3 ^ 40 * 2633742 * 2
def baseEnd_2633742 : Nat := 450791855311313235337549

theorem tailTrace_2633742 : CollatzResearch.WordTrace tailWord_2633742 prefixEnd_2633742 450791855311313235337549 := by
  unfold tailWord_2633742
  simp only [CollatzResearch.WordTrace]
  refine ⟨12007557803051252020964935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64040308282940010778479653 12007557803051252020964935)
  ·
    refine ⟨18011336704576878031447403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12007557803051252020964935 18011336704576878031447403)
    ·
      refine ⟨27017005056865317047171105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18011336704576878031447403 27017005056865317047171105)
      ·
        refine ⟨20262753792648987785378329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27017005056865317047171105 20262753792648987785378329)
        ·
          refine ⟨15197065344486740839033747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20262753792648987785378329 15197065344486740839033747)
          ·
            refine ⟨22795598016730111258550621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15197065344486740839033747 22795598016730111258550621)
            ·
              refine ⟨8548349256273791721956483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22795598016730111258550621 8548349256273791721956483)
              ·
                refine ⟨12822523884410687582934725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8548349256273791721956483 12822523884410687582934725)
                ·
                  refine ⟨2404223228327003921800261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12822523884410687582934725 2404223228327003921800261)
                  ·
                    refine ⟨450791855311313235337549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2404223228327003921800261 450791855311313235337549)
                    ·
                      rfl

theorem cell23_2633742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 1, 4, 4].length) (baseStart_2633742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2633742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2633742 prefixEnd_2633742 := by exact prefixLift 2633742
  have htrace : WordTrace (prefixWord ++ tailWord_2633742) baseStart_2633742 baseEnd_2633742 := by
    simpa [prefixWord, tailWord_2633742, baseEnd_2633742] using wordTrace_append hprefix tailTrace_2633742
  have hstable : (prefixWord ++ tailWord_2633742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2633742).length < 2 ^ (prefixWord ++ tailWord_2633742).sum := by decide
  have hdescent : baseEnd_2633742 < baseStart_2633742 := by decide
  rcases family_descends (prefixWord ++ tailWord_2633742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2633759 : List Nat := [1, 1, 2, 4, 1, 2, 5, 1, 2, 4]
def baseStart_2633759 : Nat := 118140960795 + 2633759 * 2 ^ 59
def prefixEnd_2633759 : Nat := 4983230072969 + 3 ^ 40 * 2633759 * 2
def baseEnd_2633759 : Nat := 450794765035022046500023

theorem tailTrace_2633759 : CollatzResearch.WordTrace tailWord_2633759 prefixEnd_2633759 450794765035022046500023 := by
  unfold tailWord_2633759
  simp only [CollatzResearch.WordTrace]
  refine ⟨96061082465348428071088331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64040721643565618714058887 96061082465348428071088331)
  ·
    refine ⟨144091623698022642106632497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96061082465348428071088331 144091623698022642106632497)
    ·
      refine ⟨108068717773516981579974373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144091623698022642106632497 108068717773516981579974373)
      ·
        refine ⟨20262884582534434046245195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 108068717773516981579974373 20262884582534434046245195)
        ·
          refine ⟨30394326873801651069367793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20262884582534434046245195 30394326873801651069367793)
          ·
            refine ⟨22795745155351238302025845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30394326873801651069367793 22795745155351238302025845)
            ·
              refine ⟨2137101108314178590814923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22795745155351238302025845 2137101108314178590814923)
              ·
                refine ⟨3205651662471267886222385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2137101108314178590814923 3205651662471267886222385)
                ·
                  refine ⟨2404238746853450914666789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3205651662471267886222385 2404238746853450914666789)
                  ·
                    refine ⟨450794765035022046500023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2404238746853450914666789 450794765035022046500023)
                    ·
                      rfl

theorem cell23_2633759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 5, 1, 2, 4].length) (baseStart_2633759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2633759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2633759 prefixEnd_2633759 := by exact prefixLift 2633759
  have htrace : WordTrace (prefixWord ++ tailWord_2633759) baseStart_2633759 baseEnd_2633759 := by
    simpa [prefixWord, tailWord_2633759, baseEnd_2633759] using wordTrace_append hprefix tailTrace_2633759
  have hstable : (prefixWord ++ tailWord_2633759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2633759).length < 2 ^ (prefixWord ++ tailWord_2633759).sum := by decide
  have hdescent : baseEnd_2633759 < baseStart_2633759 := by decide
  rcases family_descends (prefixWord ++ tailWord_2633759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2633799 : List Nat := [1, 1, 4, 1, 3, 1, 2, 4, 2, 1, 3]
def baseStart_2633799 : Nat := 118140960795 + 2633799 * 2 ^ 59
def prefixEnd_2633799 : Nat := 4983230072969 + 3 ^ 40 * 2633799 * 2
def baseEnd_2633799 : Nat := 1352404834331245982999885

theorem tailTrace_2633799 : CollatzResearch.WordTrace tailWord_2633799 prefixEnd_2633799 1352404834331245982999885 := by
  unfold tailWord_2633799
  simp only [CollatzResearch.WordTrace]
  refine ⟨96062541385203514902544451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64041694256802343268362967 96062541385203514902544451)
  ·
    refine ⟨144093812077805272353816677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96062541385203514902544451 144093812077805272353816677)
    ·
      refine ⟨27017589764588488566340627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 144093812077805272353816677 27017589764588488566340627)
      ·
        refine ⟨40526384646882732849510941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27017589764588488566340627 40526384646882732849510941)
        ·
          refine ⟨15197394242581024818566603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40526384646882732849510941 15197394242581024818566603)
          ·
            refine ⟨22796091363871537227849905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15197394242581024818566603 22796091363871537227849905)
            ·
              refine ⟨17097068522903652920887429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22796091363871537227849905 17097068522903652920887429)
              ·
                refine ⟨3205700348044434922666393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17097068522903652920887429 3205700348044434922666393)
                ·
                  refine ⟨2404275261033326191999795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3205700348044434922666393 2404275261033326191999795)
                  ·
                    refine ⟨3606412891549989287999693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2404275261033326191999795 3606412891549989287999693)
                    ·
                      refine ⟨1352404834331245982999885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3606412891549989287999693 1352404834331245982999885)
                      ·
                        rfl

theorem cell23_2633799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 4, 2, 1, 3].length) (baseStart_2633799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2633799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2633799 prefixEnd_2633799 := by exact prefixLift 2633799
  have htrace : WordTrace (prefixWord ++ tailWord_2633799) baseStart_2633799 baseEnd_2633799 := by
    simpa [prefixWord, tailWord_2633799, baseEnd_2633799] using wordTrace_append hprefix tailTrace_2633799
  have hstable : (prefixWord ++ tailWord_2633799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2633799).length < 2 ^ (prefixWord ++ tailWord_2633799).sum := by decide
  have hdescent : baseEnd_2633799 < baseStart_2633799 := by decide
  rcases family_descends (prefixWord ++ tailWord_2633799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2633815 : List Nat := [1, 1, 3, 2, 2, 1, 2, 3, 2, 6]
def baseStart_2633815 : Nat := 118140960795 + 2633815 * 2 ^ 59
def prefixEnd_2633815 : Nat := 4983230072969 + 3 ^ 40 * 2633815 * 2
def baseEnd_2633815 : Nat := 450804350007239306799937

theorem tailTrace_2633815 : CollatzResearch.WordTrace tailWord_2633815 prefixEnd_2633815 450804350007239306799937 := by
  unfold tailWord_2633815
  simp only [CollatzResearch.WordTrace]
  refine ⟨96063124953145549635126899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64042083302097033090084599 96063124953145549635126899)
  ·
    refine ⟨144094687429718324452690349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96063124953145549635126899 144094687429718324452690349)
    ·
      refine ⟨54035507786144371669758881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144094687429718324452690349 54035507786144371669758881)
      ·
        refine ⟨40526630839608278752319161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54035507786144371669758881 40526630839608278752319161)
        ·
          refine ⟨30394973129706209064239371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40526630839608278752319161 30394973129706209064239371)
          ·
            refine ⟨45592459694559313596359057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30394973129706209064239371 45592459694559313596359057)
            ·
              refine ⟨34194344770919485197269293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45592459694559313596359057 34194344770919485197269293)
              ·
                refine ⟨12822879289094806948975985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34194344770919485197269293 12822879289094806948975985)
                ·
                  refine ⟨9617159466821105211731989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12822879289094806948975985 9617159466821105211731989)
                  ·
                    refine ⟨450804350007239306799937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9617159466821105211731989 450804350007239306799937)
                    ·
                      rfl

theorem cell23_2633815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 3, 2, 6].length) (baseStart_2633815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2633815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2633815 prefixEnd_2633815 := by exact prefixLift 2633815
  have htrace : WordTrace (prefixWord ++ tailWord_2633815) baseStart_2633815 baseEnd_2633815 := by
    simpa [prefixWord, tailWord_2633815, baseEnd_2633815] using wordTrace_append hprefix tailTrace_2633815
  have hstable : (prefixWord ++ tailWord_2633815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2633815).length < 2 ^ (prefixWord ++ tailWord_2633815).sum := by decide
  have hdescent : baseEnd_2633815 < baseStart_2633815 := by decide
  rcases family_descends (prefixWord ++ tailWord_2633815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2633816 : List Nat := [2, 1, 2, 2, 1, 4, 4, 1, 2, 1, 3]
def baseStart_2633816 : Nat := 118140960795 + 2633816 * 2 ^ 59
def prefixEnd_2633816 : Nat := 4983230072969 + 3 ^ 40 * 2633816 * 2
def baseEnd_2633816 : Nat := 1352413563502372416487307

theorem tailTrace_2633816 : CollatzResearch.WordTrace tailWord_2633816 prefixEnd_2633816 1352413563502372416487307 := by
  unfold tailWord_2633816
  simp only [CollatzResearch.WordTrace]
  refine ⟨48031580713070963402956651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64042107617427951203942201 48031580713070963402956651)
  ·
    refine ⟨72047371069606445104434977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48031580713070963402956651 72047371069606445104434977)
    ·
      refine ⟨54035528302204833828326233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72047371069606445104434977 54035528302204833828326233)
      ·
        refine ⟨40526646226653625371244675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54035528302204833828326233 40526646226653625371244675)
        ·
          refine ⟨60789969339980438056867013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40526646226653625371244675 60789969339980438056867013)
          ·
            refine ⟨11398119251246332135662565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60789969339980438056867013 11398119251246332135662565)
            ·
              refine ⟨2137147359608687275436731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11398119251246332135662565 2137147359608687275436731)
              ·
                refine ⟨3205721039413030913155097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2137147359608687275436731 3205721039413030913155097)
                ·
                  refine ⟨2404290779559773184866323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3205721039413030913155097 2404290779559773184866323)
                  ·
                    refine ⟨3606436169339659777299485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2404290779559773184866323 3606436169339659777299485)
                    ·
                      refine ⟨1352413563502372416487307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3606436169339659777299485 1352413563502372416487307)
                      ·
                        rfl

theorem cell23_2633816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 4, 1, 2, 1, 3].length) (baseStart_2633816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2633816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2633816 prefixEnd_2633816 := by exact prefixLift 2633816
  have htrace : WordTrace (prefixWord ++ tailWord_2633816) baseStart_2633816 baseEnd_2633816 := by
    simpa [prefixWord, tailWord_2633816, baseEnd_2633816] using wordTrace_append hprefix tailTrace_2633816
  have hstable : (prefixWord ++ tailWord_2633816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2633816).length < 2 ^ (prefixWord ++ tailWord_2633816).sum := by decide
  have hdescent : baseEnd_2633816 < baseStart_2633816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2633816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2633839 : List Nat := [1, 1, 2, 1, 3, 5, 1, 2, 1, 4, 2]
def baseStart_2633839 : Nat := 118140960795 + 2633839 * 2 ^ 59
def prefixEnd_2633839 : Nat := 4983230072969 + 3 ^ 40 * 2633839 * 2
def baseEnd_2633839 : Nat := 1352425373557425826499701

theorem tailTrace_2633839 : CollatzResearch.WordTrace tailWord_2633839 prefixEnd_2633839 1352425373557425826499701 := by
  unfold tailWord_2633839
  simp only [CollatzResearch.WordTrace]
  refine ⟨96064000305058601734000571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64042666870039067822667047 96064000305058601734000571)
  ·
    refine ⟨144096000457587902601000857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96064000305058601734000571 144096000457587902601000857)
    ·
      refine ⟨108072000343190926950750643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144096000457587902601000857 108072000343190926950750643)
      ·
        refine ⟨162108000514786390426125965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108072000343190926950750643 162108000514786390426125965)
        ·
          refine ⟨60790500193044896409797237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 162108000514786390426125965 60790500193044896409797237)
          ·
            refine ⟨5699109393097959038418491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 60790500193044896409797237 5699109393097959038418491)
            ·
              refine ⟨8548664089646938557627737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5699109393097959038418491 8548664089646938557627737)
              ·
                refine ⟨6411498067235203918220803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8548664089646938557627737 6411498067235203918220803)
                ·
                  refine ⟨9617247100852805877331205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6411498067235203918220803 9617247100852805877331205)
                  ·
                    refine ⟨1803233831409901101999601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9617247100852805877331205 1803233831409901101999601)
                    ·
                      refine ⟨1352425373557425826499701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1803233831409901101999601 1352425373557425826499701)
                      ·
                        rfl

theorem cell23_2633839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 2, 1, 4, 2].length) (baseStart_2633839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2633839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2633839 prefixEnd_2633839 := by exact prefixLift 2633839
  have htrace : WordTrace (prefixWord ++ tailWord_2633839) baseStart_2633839 baseEnd_2633839 := by
    simpa [prefixWord, tailWord_2633839, baseEnd_2633839] using wordTrace_append hprefix tailTrace_2633839
  have hstable : (prefixWord ++ tailWord_2633839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2633839).length < 2 ^ (prefixWord ++ tailWord_2633839).sum := by decide
  have hdescent : baseEnd_2633839 < baseStart_2633839 := by decide
  rcases family_descends (prefixWord ++ tailWord_2633839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2633842 : List Nat := [3, 2, 1, 2, 2, 2, 2, 1, 2, 1, 5]
def baseStart_2633842 : Nat := 118140960795 + 2633842 * 2 ^ 59
def prefixEnd_2633842 : Nat := 4983230072969 + 3 ^ 40 * 2633842 * 2
def baseEnd_2633842 : Nat := 1352426913999389314762187

theorem tailTrace_2633842 : CollatzResearch.WordTrace tailWord_2633842 prefixEnd_2633842 1352426913999389314762187 := by
  unfold tailWord_2633842
  simp only [CollatzResearch.WordTrace]
  refine ⟨24016027431011933311589945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64042739816031822164239853 24016027431011933311589945)
  ·
    refine ⟨18012020573258949983692459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24016027431011933311589945 18012020573258949983692459)
    ·
      refine ⟨27018030859888424975538689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18012020573258949983692459 27018030859888424975538689)
      ·
        refine ⟨20263523144916318731654017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27018030859888424975538689 20263523144916318731654017)
        ·
          refine ⟨15197642358687239048740513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20263523144916318731654017 15197642358687239048740513)
          ·
            refine ⟨11398231769015429286555385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15197642358687239048740513 11398231769015429286555385)
            ·
              refine ⟨8548673826761571964916539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11398231769015429286555385 8548673826761571964916539)
              ·
                refine ⟨12823010740142357947374809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8548673826761571964916539 12823010740142357947374809)
                ·
                  refine ⟨9617258055106768460531107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12823010740142357947374809 9617258055106768460531107)
                  ·
                    refine ⟨14425887082660152690796661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9617258055106768460531107 14425887082660152690796661)
                    ·
                      refine ⟨1352426913999389314762187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14425887082660152690796661 1352426913999389314762187)
                      ·
                        rfl

theorem cell23_2633842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 1, 2, 1, 5].length) (baseStart_2633842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2633842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2633842 prefixEnd_2633842 := by exact prefixLift 2633842
  have htrace : WordTrace (prefixWord ++ tailWord_2633842) baseStart_2633842 baseEnd_2633842 := by
    simpa [prefixWord, tailWord_2633842, baseEnd_2633842] using wordTrace_append hprefix tailTrace_2633842
  have hstable : (prefixWord ++ tailWord_2633842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2633842).length < 2 ^ (prefixWord ++ tailWord_2633842).sum := by decide
  have hdescent : baseEnd_2633842 < baseStart_2633842 := by decide
  rcases family_descends (prefixWord ++ tailWord_2633842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2633872 : List Nat := [2, 1, 1, 1, 1, 1, 7, 1, 2, 3, 3]
def baseStart_2633872 : Nat := 118140960795 + 2633872 * 2 ^ 59
def prefixEnd_2633872 : Nat := 4983230072969 + 3 ^ 40 * 2633872 * 2
def baseEnd_2633872 : Nat := 1352442318419024197387049

theorem tailTrace_2633872 : CollatzResearch.WordTrace tailWord_2633872 prefixEnd_2633872 1352442318419024197387049 := by
  unfold tailWord_2633872
  simp only [CollatzResearch.WordTrace]
  refine ⟨48032601956969524184975935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64043469275959365579967913 48032601956969524184975935)
  ·
    refine ⟨72048902935454286277463903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48032601956969524184975935 72048902935454286277463903)
    ·
      refine ⟨108073354403181429416195855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72048902935454286277463903 108073354403181429416195855)
      ·
        refine ⟨162110031604772144124293783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108073354403181429416195855 162110031604772144124293783)
        ·
          refine ⟨243165047407158216186440675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162110031604772144124293783 243165047407158216186440675)
          ·
            refine ⟨364747571110737324279661013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 243165047407158216186440675 364747571110737324279661013)
            ·
              refine ⟨8548771197907906037804555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 364747571110737324279661013 8548771197907906037804555)
              ·
                refine ⟨12823156796861859056706833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8548771197907906037804555 12823156796861859056706833)
                ·
                  refine ⟨9617367597646394292530125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12823156796861859056706833 9617367597646394292530125)
                  ·
                    refine ⟨3606512849117397859698797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9617367597646394292530125 3606512849117397859698797)
                    ·
                      refine ⟨1352442318419024197387049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3606512849117397859698797 1352442318419024197387049)
                      ·
                        rfl

theorem cell23_2633872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 1, 2, 3, 3].length) (baseStart_2633872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2633872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2633872 prefixEnd_2633872 := by exact prefixLift 2633872
  have htrace : WordTrace (prefixWord ++ tailWord_2633872) baseStart_2633872 baseEnd_2633872 := by
    simpa [prefixWord, tailWord_2633872, baseEnd_2633872] using wordTrace_append hprefix tailTrace_2633872
  have hstable : (prefixWord ++ tailWord_2633872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2633872).length < 2 ^ (prefixWord ++ tailWord_2633872).sum := by decide
  have hdescent : baseEnd_2633872 < baseStart_2633872 := by decide
  rcases family_descends (prefixWord ++ tailWord_2633872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2633875 : List Nat := [1, 1, 1, 2, 1, 2, 3, 4, 1, 7]
def baseStart_2633875 : Nat := 118140960795 + 2633875 * 2 ^ 59
def prefixEnd_2633875 : Nat := 4983230072969 + 3 ^ 40 * 2633875 * 2
def baseEnd_2633875 : Nat := 450814619620329228549845

theorem tailTrace_2633875 : CollatzResearch.WordTrace tailWord_2633875 prefixEnd_2633875 450814619620329228549845 := by
  unfold tailWord_2633875
  simp only [CollatzResearch.WordTrace]
  refine ⟨96065313332928179882311079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64043542221952119921540719 96065313332928179882311079)
  ·
    refine ⟨144097969999392269823466619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96065313332928179882311079 144097969999392269823466619)
    ·
      refine ⟨216146954999088404735199929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144097969999392269823466619 216146954999088404735199929)
      ·
        refine ⟨162110216249316303551399947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 216146954999088404735199929 162110216249316303551399947)
        ·
          refine ⟨243165324373974455327099921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162110216249316303551399947 243165324373974455327099921)
          ·
            refine ⟨182373993280480841495324941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 243165324373974455327099921 182373993280480841495324941)
            ·
              refine ⟨68390247480180315560746853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 182373993280480841495324941 68390247480180315560746853)
              ·
                refine ⟨12823171402533809167640035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68390247480180315560746853 12823171402533809167640035)
                ·
                  refine ⟨19234757103800713751460053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12823171402533809167640035 19234757103800713751460053)
                  ·
                    refine ⟨450814619620329228549845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19234757103800713751460053 450814619620329228549845)
                    ·
                      rfl

theorem cell23_2633875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 4, 1, 7].length) (baseStart_2633875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2633875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2633875 prefixEnd_2633875 := by exact prefixLift 2633875
  have htrace : WordTrace (prefixWord ++ tailWord_2633875) baseStart_2633875 baseEnd_2633875 := by
    simpa [prefixWord, tailWord_2633875, baseEnd_2633875] using wordTrace_append hprefix tailTrace_2633875
  have hstable : (prefixWord ++ tailWord_2633875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2633875).length < 2 ^ (prefixWord ++ tailWord_2633875).sum := by decide
  have hdescent : baseEnd_2633875 < baseStart_2633875 := by decide
  rcases family_descends (prefixWord ++ tailWord_2633875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2633912 : List Nat := [2, 1, 2, 1, 2, 1, 4, 1, 4, 1, 4]
def baseStart_2633912 : Nat := 118140960795 + 2633912 * 2 ^ 59
def prefixEnd_2633912 : Nat := 4983230072969 + 3 ^ 40 * 2633912 * 2
def baseEnd_2633912 : Nat := 1352462857645204040886865

theorem tailTrace_2633912 : CollatzResearch.WordTrace tailWord_2633912 prefixEnd_2633912 1352462857645204040886865 := by
  unfold tailWord_2633912
  simp only [CollatzResearch.WordTrace]
  refine ⟨48033331416897067600703995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64044441889196090134271993 48033331416897067600703995)
  ·
    refine ⟨72049997125345601401055993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48033331416897067600703995 72049997125345601401055993)
    ·
      refine ⟨54037497844009201050791995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72049997125345601401055993 54037497844009201050791995)
      ·
        refine ⟨81056246766013801576187993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54037497844009201050791995 81056246766013801576187993)
        ·
          refine ⟨60792185074510351182140995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81056246766013801576187993 60792185074510351182140995)
          ·
            refine ⟨91188277611765526773211493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60792185074510351182140995 91188277611765526773211493)
            ·
              refine ⟨17097802052206036269977155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 91188277611765526773211493 17097802052206036269977155)
              ·
                refine ⟨25646703078309054404965733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17097802052206036269977155 25646703078309054404965733)
                ·
                  refine ⟨4808756827182947700931075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25646703078309054404965733 4808756827182947700931075)
                  ·
                    refine ⟨7213135240774421551396613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4808756827182947700931075 7213135240774421551396613)
                    ·
                      refine ⟨1352462857645204040886865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7213135240774421551396613 1352462857645204040886865)
                      ·
                        rfl

theorem cell23_2633912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 1, 4, 1, 4].length) (baseStart_2633912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2633912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2633912 prefixEnd_2633912 := by exact prefixLift 2633912
  have htrace : WordTrace (prefixWord ++ tailWord_2633912) baseStart_2633912 baseEnd_2633912 := by
    simpa [prefixWord, tailWord_2633912, baseEnd_2633912] using wordTrace_append hprefix tailTrace_2633912
  have hstable : (prefixWord ++ tailWord_2633912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2633912).length < 2 ^ (prefixWord ++ tailWord_2633912).sum := by decide
  have hdescent : baseEnd_2633912 < baseStart_2633912 := by decide
  rcases family_descends (prefixWord ++ tailWord_2633912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2633986 : List Nat := [3, 4, 1, 1, 2, 2, 1, 3, 6]
def baseStart_2633986 : Nat := 118140960795 + 2633986 * 2 ^ 59
def prefixEnd_2633986 : Nat := 4983230072969 + 3 ^ 40 * 2633986 * 2
def baseEnd_2633986 : Nat := 150277872801515194595725

theorem tailTrace_2633986 : CollatzResearch.WordTrace tailWord_2633986 prefixEnd_2633986 150277872801515194595725 := by
  unfold tailWord_2633986
  simp only [CollatzResearch.WordTrace]
  refine ⟨24017340458881511459900453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64046241223684030559734541 24017340458881511459900453)
  ·
    refine ⟨4503251336040283398731335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24017340458881511459900453 4503251336040283398731335)
    ·
      refine ⟨6754877004060425098097003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4503251336040283398731335 6754877004060425098097003)
      ·
        refine ⟨10132315506090637647145505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6754877004060425098097003 10132315506090637647145505)
        ·
          refine ⟨7599236629567978235359129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10132315506090637647145505 7599236629567978235359129)
          ·
            refine ⟨5699427472175983676519347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7599236629567978235359129 5699427472175983676519347)
            ·
              refine ⟨8549141208263975514779021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5699427472175983676519347 8549141208263975514779021)
              ·
                refine ⟨3205927953098990818042133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8549141208263975514779021 3205927953098990818042133)
                ·
                  refine ⟨150277872801515194595725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3205927953098990818042133 150277872801515194595725)
                  ·
                    rfl

theorem cell23_2633986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 3, 6].length) (baseStart_2633986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2633986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2633986 prefixEnd_2633986 := by exact prefixLift 2633986
  have htrace : WordTrace (prefixWord ++ tailWord_2633986) baseStart_2633986 baseEnd_2633986 := by
    simpa [prefixWord, tailWord_2633986, baseEnd_2633986] using wordTrace_append hprefix tailTrace_2633986
  have hstable : (prefixWord ++ tailWord_2633986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2633986).length < 2 ^ (prefixWord ++ tailWord_2633986).sum := by decide
  have hdescent : baseEnd_2633986 < baseStart_2633986 := by decide
  rcases family_descends (prefixWord ++ tailWord_2633986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2633989 : List Nat := [1, 3, 1, 1, 2, 1, 2, 4, 1, 5, 2]
def baseStart_2633989 : Nat := 118140960795 + 2633989 * 2 ^ 59
def prefixEnd_2633989 : Nat := 4983230072969 + 3 ^ 40 * 2633989 * 2
def baseEnd_2633989 : Nat := 1352502395655600239624011

theorem tailTrace_2633989 : CollatzResearch.WordTrace tailWord_2633989 prefixEnd_2633989 1352502395655600239624011 := by
  unfold tailWord_2633989
  simp only [CollatzResearch.WordTrace]
  refine ⟨96069471254515177351961021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64046314169676784901307347 96069471254515177351961021)
  ·
    refine ⟨36026051720443191506985383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96069471254515177351961021 36026051720443191506985383)
    ·
      refine ⟨54039077580664787260478075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36026051720443191506985383 54039077580664787260478075)
      ·
        refine ⟨81058616370997180890717113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54039077580664787260478075 81058616370997180890717113)
        ·
          refine ⟨60793962278247885668037835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81058616370997180890717113 60793962278247885668037835)
          ·
            refine ⟨91190943417371828502056753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60793962278247885668037835 91190943417371828502056753)
            ·
              refine ⟨68393207563028871376542565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91190943417371828502056753 68393207563028871376542565)
              ·
                refine ⟨12823726418067913383101731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68393207563028871376542565 12823726418067913383101731)
                ·
                  refine ⟨19235589627101870074652597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12823726418067913383101731 19235589627101870074652597)
                  ·
                    refine ⟨1803336527540800319498681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19235589627101870074652597 1803336527540800319498681)
                    ·
                      refine ⟨1352502395655600239624011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1803336527540800319498681 1352502395655600239624011)
                      ·
                        rfl

theorem cell23_2633989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 4, 1, 5, 2].length) (baseStart_2633989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2633989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2633989 prefixEnd_2633989 := by exact prefixLift 2633989
  have htrace : WordTrace (prefixWord ++ tailWord_2633989) baseStart_2633989 baseEnd_2633989 := by
    simpa [prefixWord, tailWord_2633989, baseEnd_2633989] using wordTrace_append hprefix tailTrace_2633989
  have hstable : (prefixWord ++ tailWord_2633989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2633989).length < 2 ^ (prefixWord ++ tailWord_2633989).sum := by decide
  have hdescent : baseEnd_2633989 < baseStart_2633989 := by decide
  rcases family_descends (prefixWord ++ tailWord_2633989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2634032 : List Nat := [2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 6]
def baseStart_2634032 : Nat := 118140960795 + 2634032 * 2 ^ 59
def prefixEnd_2634032 : Nat := 4983230072969 + 3 ^ 40 * 2634032 * 2
def baseEnd_2634032 : Nat := 1352524475323743571386313

theorem tailTrace_2634032 : CollatzResearch.WordTrace tailWord_2634032 prefixEnd_2634032 1352524475323743571386313 := by
  unfold tailWord_2634032
  simp only [CollatzResearch.WordTrace]
  refine ⟨48035519796679697847888175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64047359728906263797184233 48035519796679697847888175)
  ·
    refine ⟨72053279695019546771832263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48035519796679697847888175 72053279695019546771832263)
    ·
      refine ⟨108079919542529320157748395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72053279695019546771832263 108079919542529320157748395)
      ·
        refine ⟨162119879313793980236622593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108079919542529320157748395 162119879313793980236622593)
        ·
          refine ⟨121589909485345485177466945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162119879313793980236622593 121589909485345485177466945)
          ·
            refine ⟨91192432114009113883100209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121589909485345485177466945 91192432114009113883100209)
            ·
              refine ⟨68394324085506835412325157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91192432114009113883100209 68394324085506835412325157)
              ·
                refine ⟨12823935766032531639810967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68394324085506835412325157 12823935766032531639810967)
                ·
                  refine ⟨19235903649048797459716451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12823935766032531639810967 19235903649048797459716451)
                  ·
                    refine ⟨28853855473573196189574677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19235903649048797459716451 28853855473573196189574677)
                    ·
                      refine ⟨1352524475323743571386313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28853855473573196189574677 1352524475323743571386313)
                      ·
                        rfl

theorem cell23_2634032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 6].length) (baseStart_2634032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2634032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2634032 prefixEnd_2634032 := by exact prefixLift 2634032
  have htrace : WordTrace (prefixWord ++ tailWord_2634032) baseStart_2634032 baseEnd_2634032 := by
    simpa [prefixWord, tailWord_2634032, baseEnd_2634032] using wordTrace_append hprefix tailTrace_2634032
  have hstable : (prefixWord ++ tailWord_2634032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2634032).length < 2 ^ (prefixWord ++ tailWord_2634032).sum := by decide
  have hdescent : baseEnd_2634032 < baseStart_2634032 := by decide
  rcases family_descends (prefixWord ++ tailWord_2634032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2634036 : List Nat := [2, 5, 1, 1, 1, 2, 1, 2, 3, 1, 4]
def baseStart_2634036 : Nat := 118140960795 + 2634036 * 2 ^ 59
def prefixEnd_2634036 : Nat := 4983230072969 + 3 ^ 40 * 2634036 * 2
def baseEnd_2634036 : Nat := 1352526529246361555736295

theorem tailTrace_2634036 : CollatzResearch.WordTrace tailWord_2634036 prefixEnd_2634036 1352526529246361555736295 := by
  unfold tailWord_2634036
  simp only [CollatzResearch.WordTrace]
  refine ⟨48035592742672452189460981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64047456990229936252614641 48035592742672452189460981)
  ·
    refine ⟨4503336819625542392761967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 48035592742672452189460981 4503336819625542392761967)
    ·
      refine ⟨6755005229438313589142951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4503336819625542392761967 6755005229438313589142951)
      ·
        refine ⟨10132507844157470383714427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6755005229438313589142951 10132507844157470383714427)
        ·
          refine ⟨15198761766236205575571641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10132507844157470383714427 15198761766236205575571641)
          ·
            refine ⟨11399071324677154181678731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15198761766236205575571641 11399071324677154181678731)
            ·
              refine ⟨17098606987015731272518097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11399071324677154181678731 17098606987015731272518097)
              ·
                refine ⟨12823955240261798454388573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17098606987015731272518097 12823955240261798454388573)
                ·
                  refine ⟨4808983215098174420395715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12823955240261798454388573 4808983215098174420395715)
                  ·
                    refine ⟨7213474822647261630593573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4808983215098174420395715 7213474822647261630593573)
                    ·
                      refine ⟨1352526529246361555736295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7213474822647261630593573 1352526529246361555736295)
                      ·
                        rfl

theorem cell23_2634036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_2634036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2634036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2634036 prefixEnd_2634036 := by exact prefixLift 2634036
  have htrace : WordTrace (prefixWord ++ tailWord_2634036) baseStart_2634036 baseEnd_2634036 := by
    simpa [prefixWord, tailWord_2634036, baseEnd_2634036] using wordTrace_append hprefix tailTrace_2634036
  have hstable : (prefixWord ++ tailWord_2634036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2634036).length < 2 ^ (prefixWord ++ tailWord_2634036).sum := by decide
  have hdescent : baseEnd_2634036 < baseStart_2634036 := by decide
  rcases family_descends (prefixWord ++ tailWord_2634036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2634046 : List Nat := [4, 2, 1, 2, 1, 3, 2, 1, 1, 6]
def baseStart_2634046 : Nat := 118140960795 + 2634046 * 2 ^ 59
def prefixEnd_2634046 : Nat := 4983230072969 + 3 ^ 40 * 2634046 * 2
def baseEnd_2634046 : Nat := 450843888017635505537083

theorem tailTrace_2634046 : CollatzResearch.WordTrace tailWord_2634046 prefixEnd_2634046 450843888017635505537083 := by
  unfold tailWord_2634046
  simp only [CollatzResearch.WordTrace]
  refine ⟨12008943776913584510848249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64047700143539117391190661 12008943776913584510848249)
  ·
    refine ⟨9006707832685188383136187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12008943776913584510848249 9006707832685188383136187)
    ·
      refine ⟨13510061749027782574704281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9006707832685188383136187 13510061749027782574704281)
      ·
        refine ⟨10132546311770836931028211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13510061749027782574704281 10132546311770836931028211)
        ·
          refine ⟨15198819467656255396542317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10132546311770836931028211 15198819467656255396542317)
          ·
            refine ⟨5699557300371095773703369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15198819467656255396542317 5699557300371095773703369)
            ·
              refine ⟨4274667975278321830277527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5699557300371095773703369 4274667975278321830277527)
              ·
                refine ⟨6412001962917482745416291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4274667975278321830277527 6412001962917482745416291)
                ·
                  refine ⟨9618002944376224118124437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6412001962917482745416291 9618002944376224118124437)
                  ·
                    refine ⟨450843888017635505537083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9618002944376224118124437 450843888017635505537083)
                    ·
                      rfl

theorem cell23_2634046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2, 1, 1, 6].length) (baseStart_2634046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2634046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2634046 prefixEnd_2634046 := by exact prefixLift 2634046
  have htrace : WordTrace (prefixWord ++ tailWord_2634046) baseStart_2634046 baseEnd_2634046 := by
    simpa [prefixWord, tailWord_2634046, baseEnd_2634046] using wordTrace_append hprefix tailTrace_2634046
  have hstable : (prefixWord ++ tailWord_2634046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2634046).length < 2 ^ (prefixWord ++ tailWord_2634046).sum := by decide
  have hdescent : baseEnd_2634046 < baseStart_2634046 := by decide
  rcases family_descends (prefixWord ++ tailWord_2634046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2634072 : List Nat := [2, 1, 2, 2, 1, 1, 2, 2, 1, 9]
def baseStart_2634072 : Nat := 118140960795 + 2634072 * 2 ^ 59
def prefixEnd_2634072 : Nat := 4983230072969 + 3 ^ 40 * 2634072 * 2
def baseEnd_2634072 : Nat := 450848338183307804962043

theorem tailTrace_2634072 : CollatzResearch.WordTrace tailWord_2634072 prefixEnd_2634072 450848338183307804962043 := by
  unfold tailWord_2634072
  simp only [CollatzResearch.WordTrace]
  refine ⟨48036249256607241263616235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64048332342142988351488313 48036249256607241263616235)
  ·
    refine ⟨72054373884910861895424353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48036249256607241263616235 72054373884910861895424353)
    ·
      refine ⟨54040780413683146421568265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72054373884910861895424353 54040780413683146421568265)
      ·
        refine ⟨40530585310262359816176199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54040780413683146421568265 40530585310262359816176199)
        ·
          refine ⟨60795877965393539724264299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40530585310262359816176199 60795877965393539724264299)
          ·
            refine ⟨91193816948090309586396449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60795877965393539724264299 91193816948090309586396449)
            ·
              refine ⟨68395362711067732189797337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91193816948090309586396449 68395362711067732189797337)
              ·
                refine ⟨51296522033300799142348003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68395362711067732189797337 51296522033300799142348003)
                ·
                  refine ⟨76944783049951198713522005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51296522033300799142348003 76944783049951198713522005)
                  ·
                    refine ⟨450848338183307804962043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 76944783049951198713522005 450848338183307804962043)
                    ·
                      rfl

theorem cell23_2634072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 1, 9].length) (baseStart_2634072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2634072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2634072 prefixEnd_2634072 := by exact prefixLift 2634072
  have htrace : WordTrace (prefixWord ++ tailWord_2634072) baseStart_2634072 baseEnd_2634072 := by
    simpa [prefixWord, tailWord_2634072, baseEnd_2634072] using wordTrace_append hprefix tailTrace_2634072
  have hstable : (prefixWord ++ tailWord_2634072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2634072).length < 2 ^ (prefixWord ++ tailWord_2634072).sum := by decide
  have hdescent : baseEnd_2634072 < baseStart_2634072 := by decide
  rcases family_descends (prefixWord ++ tailWord_2634072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2634076 : List Nat := [2, 2, 4, 3, 1, 1, 10]
def baseStart_2634076 : Nat := 118140960795 + 2634076 * 2 ^ 59
def prefixEnd_2634076 : Nat := 4983230072969 + 3 ^ 40 * 2634076 * 2
def baseEnd_2634076 : Nat := 16698111956451128385631

theorem tailTrace_2634076 : CollatzResearch.WordTrace tailWord_2634076 prefixEnd_2634076 16698111956451128385631 := by
  unfold tailWord_2634076
  simp only [CollatzResearch.WordTrace]
  refine ⟨48036322202599995605189041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64048429603466660806918721 48036322202599995605189041)
  ·
    refine ⟨36027241651949996703891781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48036322202599995605189041 36027241651949996703891781)
    ·
      refine ⟨6755107809740624381979709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36027241651949996703891781 6755107809740624381979709)
      ·
        refine ⟨2533165428652734143242391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6755107809740624381979709 2533165428652734143242391)
        ·
          refine ⟨3799748142979101214863587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2533165428652734143242391 3799748142979101214863587)
          ·
            refine ⟨5699622214468651822295381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3799748142979101214863587 5699622214468651822295381)
            ·
              refine ⟨16698111956451128385631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5699622214468651822295381 16698111956451128385631)
              ·
                rfl

theorem cell23_2634076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 10].length) (baseStart_2634076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2634076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2634076 prefixEnd_2634076 := by exact prefixLift 2634076
  have htrace : WordTrace (prefixWord ++ tailWord_2634076) baseStart_2634076 baseEnd_2634076 := by
    simpa [prefixWord, tailWord_2634076, baseEnd_2634076] using wordTrace_append hprefix tailTrace_2634076
  have hstable : (prefixWord ++ tailWord_2634076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2634076).length < 2 ^ (prefixWord ++ tailWord_2634076).sum := by decide
  have hdescent : baseEnd_2634076 < baseStart_2634076 := by decide
  rcases family_descends (prefixWord ++ tailWord_2634076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2634080 : List Nat := [2, 1, 1, 3, 6, 1, 1, 2, 2, 4]
def baseStart_2634080 : Nat := 118140960795 + 2634080 * 2 ^ 59
def prefixEnd_2634080 : Nat := 4983230072969 + 3 ^ 40 * 2634080 * 2
def baseEnd_2634080 : Nat := 450849707465053127862031

theorem tailTrace_2634080 : CollatzResearch.WordTrace tailWord_2634080 prefixEnd_2634080 450849707465053127862031 := by
  unfold tailWord_2634080
  simp only [CollatzResearch.WordTrace]
  refine ⟨48036395148592749946761847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64048526864790333262349129 48036395148592749946761847)
  ·
    refine ⟨72054592722889124920142771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48036395148592749946761847 72054592722889124920142771)
    ·
      refine ⟨108081889084333687380214157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72054592722889124920142771 108081889084333687380214157)
      ·
        refine ⟨40530708406625132767580309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108081889084333687380214157 40530708406625132767580309)
        ·
          refine ⟨1899876956560553098480327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 40530708406625132767580309 1899876956560553098480327)
          ·
            refine ⟨2849815434840829647720491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1899876956560553098480327 2849815434840829647720491)
            ·
              refine ⟨4274723152261244471580737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2849815434840829647720491 4274723152261244471580737)
              ·
                refine ⟨3206042364195933353685553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4274723152261244471580737 3206042364195933353685553)
                ·
                  refine ⟨2404531773146950015264165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3206042364195933353685553 2404531773146950015264165)
                  ·
                    refine ⟨450849707465053127862031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2404531773146950015264165 450849707465053127862031)
                    ·
                      rfl

theorem cell23_2634080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 2, 2, 4].length) (baseStart_2634080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2634080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2634080 prefixEnd_2634080 := by exact prefixLift 2634080
  have htrace : WordTrace (prefixWord ++ tailWord_2634080) baseStart_2634080 baseEnd_2634080 := by
    simpa [prefixWord, tailWord_2634080, baseEnd_2634080] using wordTrace_append hprefix tailTrace_2634080
  have hstable : (prefixWord ++ tailWord_2634080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2634080).length < 2 ^ (prefixWord ++ tailWord_2634080).sum := by decide
  have hdescent : baseEnd_2634080 < baseStart_2634080 := by decide
  rcases family_descends (prefixWord ++ tailWord_2634080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2634143 : List Nat := [1, 1, 2, 5, 1, 1, 1, 3, 4, 2, 2]
def baseStart_2634143 : Nat := 118140960795 + 2634143 * 2 ^ 59
def prefixEnd_2634143 : Nat := 4983230072969 + 3 ^ 40 * 2634143 * 2
def baseEnd_2634143 : Nat := 1352581471676392637098303

theorem tailTrace_2634143 : CollatzResearch.WordTrace tailWord_2634143 prefixEnd_2634143 1352581471676392637098303 := by
  unfold tailWord_2634143
  simp only [CollatzResearch.WordTrace]
  refine ⟨96075088095957261653067083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64050058730638174435378055 96075088095957261653067083)
  ·
    refine ⟨144112632143935892479600625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96075088095957261653067083 144112632143935892479600625)
    ·
      refine ⟨108084474107951919359700469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144112632143935892479600625 108084474107951919359700469)
      ·
        refine ⟨10132919447620492439971919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 108084474107951919359700469 10132919447620492439971919)
        ·
          refine ⟨15199379171430738659957879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10132919447620492439971919 15199379171430738659957879)
          ·
            refine ⟨22799068757146107989936819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15199379171430738659957879 22799068757146107989936819)
            ·
              refine ⟨34198603135719161984905229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22799068757146107989936819 34198603135719161984905229)
              ·
                refine ⟨12824476175894685744339461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34198603135719161984905229 12824476175894685744339461)
                ·
                  refine ⟨2404589282980253577063649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12824476175894685744339461 2404589282980253577063649)
                  ·
                    refine ⟨1803441962235190182797737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2404589282980253577063649 1803441962235190182797737)
                    ·
                      refine ⟨1352581471676392637098303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1803441962235190182797737 1352581471676392637098303)
                      ·
                        rfl

theorem cell23_2634143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 3, 4, 2, 2].length) (baseStart_2634143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2634143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2634143 prefixEnd_2634143 := by exact prefixLift 2634143
  have htrace : WordTrace (prefixWord ++ tailWord_2634143) baseStart_2634143 baseEnd_2634143 := by
    simpa [prefixWord, tailWord_2634143, baseEnd_2634143] using wordTrace_append hprefix tailTrace_2634143
  have hstable : (prefixWord ++ tailWord_2634143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2634143).length < 2 ^ (prefixWord ++ tailWord_2634143).sum := by decide
  have hdescent : baseEnd_2634143 < baseStart_2634143 := by decide
  rcases family_descends (prefixWord ++ tailWord_2634143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2634146 : List Nat := [3, 3, 1, 2, 1, 1, 2, 1, 2, 4, 3]
def baseStart_2634146 : Nat := 118140960795 + 2634146 * 2 ^ 59
def prefixEnd_2634146 : Nat := 4983230072969 + 3 ^ 40 * 2634146 * 2
def baseEnd_2634146 : Nat := 1352583012118356125360789

theorem tailTrace_2634146 : CollatzResearch.WordTrace tailWord_2634146 prefixEnd_2634146 1352583012118356125360789 := by
  unfold tailWord_2634146
  simp only [CollatzResearch.WordTrace]
  refine ⟨24018799378736598291356573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64050131676630928776950861 24018799378736598291356573)
  ·
    refine ⟨9007049767026224359258715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24018799378736598291356573 9007049767026224359258715)
    ·
      refine ⟨13510574650539336538888073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9007049767026224359258715 13510574650539336538888073)
      ·
        refine ⟨10132930987904502404166055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13510574650539336538888073 10132930987904502404166055)
        ·
          refine ⟨15199396481856753606249083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10132930987904502404166055 15199396481856753606249083)
          ·
            refine ⟨22799094722785130409373625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15199396481856753606249083 22799094722785130409373625)
            ·
              refine ⟨17099321042088847807030219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22799094722785130409373625 17099321042088847807030219)
              ·
                refine ⟨25648981563133271710545329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17099321042088847807030219 25648981563133271710545329)
                ·
                  refine ⟨19236736172349953782908997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25648981563133271710545329 19236736172349953782908997)
                  ·
                    refine ⟨3606888032315616334295437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19236736172349953782908997 3606888032315616334295437)
                    ·
                      refine ⟨1352583012118356125360789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3606888032315616334295437 1352583012118356125360789)
                      ·
                        rfl

theorem cell23_2634146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 1, 2, 4, 3].length) (baseStart_2634146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2634146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2634146 prefixEnd_2634146 := by exact prefixLift 2634146
  have htrace : WordTrace (prefixWord ++ tailWord_2634146) baseStart_2634146 baseEnd_2634146 := by
    simpa [prefixWord, tailWord_2634146, baseEnd_2634146] using wordTrace_append hprefix tailTrace_2634146
  have hstable : (prefixWord ++ tailWord_2634146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2634146).length < 2 ^ (prefixWord ++ tailWord_2634146).sum := by decide
  have hdescent : baseEnd_2634146 < baseStart_2634146 := by decide
  rcases family_descends (prefixWord ++ tailWord_2634146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2634154 : List Nat := [3, 1, 6, 1, 1, 1, 1, 3, 2, 1, 3]
def baseStart_2634154 : Nat := 118140960795 + 2634154 * 2 ^ 59
def prefixEnd_2634154 : Nat := 4983230072969 + 3 ^ 40 * 2634154 * 2
def baseEnd_2634154 : Nat := 1352587119963592094060753

theorem tailTrace_2634154 : CollatzResearch.WordTrace tailWord_2634154 prefixEnd_2634154 1352587119963592094060753 := by
  unfold tailWord_2634154
  simp only [CollatzResearch.WordTrace]
  refine ⟨24018872324729352632929379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64050326199278273687811677 24018872324729352632929379)
  ·
    refine ⟨36028308487094028949394069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24018872324729352632929379 36028308487094028949394069)
    ·
      refine ⟨1688826960332532607002847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 36028308487094028949394069 1688826960332532607002847)
      ·
        refine ⟨2533240440498798910504271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1688826960332532607002847 2533240440498798910504271)
        ·
          refine ⟨3799860660748198365756407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2533240440498798910504271 3799860660748198365756407)
          ·
            refine ⟨5699790991122297548634611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3799860660748198365756407 5699790991122297548634611)
            ·
              refine ⟨8549686486683446322951917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5699790991122297548634611 8549686486683446322951917)
              ·
                refine ⟨3206132432506292371106969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8549686486683446322951917 3206132432506292371106969)
                ·
                  refine ⟨2404599324379719278330227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3206132432506292371106969 2404599324379719278330227)
                  ·
                    refine ⟨3606898986569578917495341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2404599324379719278330227 3606898986569578917495341)
                    ·
                      refine ⟨1352587119963592094060753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3606898986569578917495341 1352587119963592094060753)
                      ·
                        rfl

theorem cell23_2634154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_2634154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2634154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2634154 prefixEnd_2634154 := by exact prefixLift 2634154
  have htrace : WordTrace (prefixWord ++ tailWord_2634154) baseStart_2634154 baseEnd_2634154 := by
    simpa [prefixWord, tailWord_2634154, baseEnd_2634154] using wordTrace_append hprefix tailTrace_2634154
  have hstable : (prefixWord ++ tailWord_2634154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2634154).length < 2 ^ (prefixWord ++ tailWord_2634154).sum := by decide
  have hdescent : baseEnd_2634154 < baseStart_2634154 := by decide
  rcases family_descends (prefixWord ++ tailWord_2634154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2634194 : List Nat := [3, 2, 2, 4, 1, 1, 2, 2, 2, 2, 2]
def baseStart_2634194 : Nat := 118140960795 + 2634194 * 2 ^ 59
def prefixEnd_2634194 : Nat := 4983230072969 + 3 ^ 40 * 2634194 * 2
def baseEnd_2634194 : Nat := 1352607659189771937560569

theorem tailTrace_2634194 : CollatzResearch.WordTrace tailWord_2634194 prefixEnd_2634194 1352607659189771937560569 := by
  unfold tailWord_2634194
  simp only [CollatzResearch.WordTrace]
  refine ⟨24019237054693124340793409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64051298812514998242115757 24019237054693124340793409)
  ·
    refine ⟨18014427791019843255595057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24019237054693124340793409 18014427791019843255595057)
    ·
      refine ⟨13510820843264882441696293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18014427791019843255595057 13510820843264882441696293)
      ·
        refine ⟨2533278908112165457818055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13510820843264882441696293 2533278908112165457818055)
        ·
          refine ⟨3799918362168248186727083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2533278908112165457818055 3799918362168248186727083)
          ·
            refine ⟨5699877543252372280090625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3799918362168248186727083 5699877543252372280090625)
            ·
              refine ⟨4274908157439279210067969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5699877543252372280090625 4274908157439279210067969)
              ·
                refine ⟨3206181118079459407550977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4274908157439279210067969 3206181118079459407550977)
                ·
                  refine ⟨2404635838559594555663233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3206181118079459407550977 2404635838559594555663233)
                  ·
                    refine ⟨1803476878919695916747425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2404635838559594555663233 1803476878919695916747425)
                    ·
                      refine ⟨1352607659189771937560569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1803476878919695916747425 1352607659189771937560569)
                      ·
                        rfl

theorem cell23_2634194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_2634194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2634194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2634194 prefixEnd_2634194 := by exact prefixLift 2634194
  have htrace : WordTrace (prefixWord ++ tailWord_2634194) baseStart_2634194 baseEnd_2634194 := by
    simpa [prefixWord, tailWord_2634194, baseEnd_2634194] using wordTrace_append hprefix tailTrace_2634194
  have hstable : (prefixWord ++ tailWord_2634194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2634194).length < 2 ^ (prefixWord ++ tailWord_2634194).sum := by decide
  have hdescent : baseEnd_2634194 < baseStart_2634194 := by decide
  rcases family_descends (prefixWord ++ tailWord_2634194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2634199 : List Nat := [1, 1, 3, 2, 1, 1, 1, 1, 5, 3, 4]
def baseStart_2634199 : Nat := 118140960795 + 2634199 * 2 ^ 59
def prefixEnd_2634199 : Nat := 4983230072969 + 3 ^ 40 * 2634199 * 2
def baseEnd_2634199 : Nat := 1352610226593044417998045

theorem tailTrace_2634199 : CollatzResearch.WordTrace tailWord_2634199 prefixEnd_2634199 1352610226593044417998045 := by
  unfold tailWord_2634199
  simp only [CollatzResearch.WordTrace]
  refine ⟨96077130583754383217105651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64051420389169588811403767 96077130583754383217105651)
  ·
    refine ⟨144115695875631574825658477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96077130583754383217105651 144115695875631574825658477)
    ·
      refine ⟨54043385953361840559621929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144115695875631574825658477 54043385953361840559621929)
      ·
        refine ⟨40532539465021380419716447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54043385953361840559621929 40532539465021380419716447)
        ·
          refine ⟨60798809197532070629574671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40532539465021380419716447 60798809197532070629574671)
          ·
            refine ⟨91198213796298105944362007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60798809197532070629574671 91198213796298105944362007)
            ·
              refine ⟨136797320694447158916543011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91198213796298105944362007 136797320694447158916543011)
              ·
                refine ⟨205195981041670738374814517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 136797320694447158916543011 205195981041670738374814517)
                ·
                  refine ⟨19237123222656631722638861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 205195981041670738374814517 19237123222656631722638861)
                  ·
                    refine ⟨7213921208496236895989573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19237123222656631722638861 7213921208496236895989573)
                    ·
                      refine ⟨1352610226593044417998045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7213921208496236895989573 1352610226593044417998045)
                      ·
                        rfl

theorem cell23_2634199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 5, 3, 4].length) (baseStart_2634199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2634199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2634199 prefixEnd_2634199 := by exact prefixLift 2634199
  have htrace : WordTrace (prefixWord ++ tailWord_2634199) baseStart_2634199 baseEnd_2634199 := by
    simpa [prefixWord, tailWord_2634199, baseEnd_2634199] using wordTrace_append hprefix tailTrace_2634199
  have hstable : (prefixWord ++ tailWord_2634199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2634199).length < 2 ^ (prefixWord ++ tailWord_2634199).sum := by decide
  have hdescent : baseEnd_2634199 < baseStart_2634199 := by decide
  rcases family_descends (prefixWord ++ tailWord_2634199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2634239 : List Nat := [1, 1, 2, 2, 1, 2, 4, 2, 8]
def baseStart_2634239 : Nat := 118140960795 + 2634239 * 2 ^ 59
def prefixEnd_2634239 : Nat := 4983230072969 + 3 ^ 40 * 2634239 * 2
def baseEnd_2634239 : Nat := 150292307313247140166429

theorem tailTrace_2634239 : CollatzResearch.WordTrace tailWord_2634239 prefixEnd_2634239 150292307313247140166429 := by
  unfold tailWord_2634239
  simp only [CollatzResearch.WordTrace]
  refine ⟨96078589503609470048561771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64052393002406313365707847 96078589503609470048561771)
  ·
    refine ⟨144117884255414205072842657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96078589503609470048561771 144117884255414205072842657)
    ·
      refine ⟨108088413191560653804631993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144117884255414205072842657 108088413191560653804631993)
      ·
        refine ⟨81066309893670490353473995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108088413191560653804631993 81066309893670490353473995)
        ·
          refine ⟨121599464840505735530210993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81066309893670490353473995 121599464840505735530210993)
          ·
            refine ⟨91199598630379301647658245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121599464840505735530210993 91199598630379301647658245)
            ·
              refine ⟨17099924743196119058935921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 91199598630379301647658245 17099924743196119058935921)
              ·
                refine ⟨12824943557397089294201941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17099924743196119058935921 12824943557397089294201941)
                ·
                  refine ⟨150292307313247140166429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12824943557397089294201941 150292307313247140166429)
                  ·
                    rfl

theorem cell23_2634239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 2, 8].length) (baseStart_2634239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2634239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2634239 prefixEnd_2634239 := by exact prefixLift 2634239
  have htrace : WordTrace (prefixWord ++ tailWord_2634239) baseStart_2634239 baseEnd_2634239 := by
    simpa [prefixWord, tailWord_2634239, baseEnd_2634239] using wordTrace_append hprefix tailTrace_2634239
  have hstable : (prefixWord ++ tailWord_2634239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2634239).length < 2 ^ (prefixWord ++ tailWord_2634239).sum := by decide
  have hdescent : baseEnd_2634239 < baseStart_2634239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2634239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2634259 : List Nat := [1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 8]
def baseStart_2634259 : Nat := 118140960795 + 2634259 * 2 ^ 59
def prefixEnd_2634259 : Nat := 4983230072969 + 3 ^ 40 * 2634259 * 2
def baseEnd_2634259 : Nat := 1352641035432314183247769

theorem tailTrace_2634259 : CollatzResearch.WordTrace tailWord_2634259 prefixEnd_2634259 1352641035432314183247769 := by
  unfold tailWord_2634259
  simp only [CollatzResearch.WordTrace]
  refine ⟨96079318963537013464289831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64052879309024675642859887 96079318963537013464289831)
  ·
    refine ⟨144118978445305520196434747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96079318963537013464289831 144118978445305520196434747)
    ·
      refine ⟨216178467667958280294652121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144118978445305520196434747 216178467667958280294652121)
      ·
        refine ⟨162133850750968710220989091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 216178467667958280294652121 162133850750968710220989091)
        ·
          refine ⟨243200776126453065331483637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162133850750968710220989091 243200776126453065331483637)
          ·
            refine ⟨22800072761854974874826591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 243200776126453065331483637 22800072761854974874826591)
            ·
              refine ⟨34200109142782462312239887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22800072761854974874826591 34200109142782462312239887)
              ·
                refine ⟨51300163714173693468359831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34200109142782462312239887 51300163714173693468359831)
                ·
                  refine ⟨76950245571260540202539747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51300163714173693468359831 76950245571260540202539747)
                  ·
                    refine ⟨115425368356890810303809621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 76950245571260540202539747 115425368356890810303809621)
                    ·
                      refine ⟨1352641035432314183247769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 115425368356890810303809621 1352641035432314183247769)
                      ·
                        rfl

theorem cell23_2634259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 8].length) (baseStart_2634259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2634259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2634259 prefixEnd_2634259 := by exact prefixLift 2634259
  have htrace : WordTrace (prefixWord ++ tailWord_2634259) baseStart_2634259 baseEnd_2634259 := by
    simpa [prefixWord, tailWord_2634259, baseEnd_2634259] using wordTrace_append hprefix tailTrace_2634259
  have hstable : (prefixWord ++ tailWord_2634259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2634259).length < 2 ^ (prefixWord ++ tailWord_2634259).sum := by decide
  have hdescent : baseEnd_2634259 < baseStart_2634259 := by decide
  rcases family_descends (prefixWord ++ tailWord_2634259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2634260 : List Nat := [2, 4, 3, 1, 1, 1, 1, 3, 3, 4]
def baseStart_2634260 : Nat := 118140960795 + 2634260 * 2 ^ 59
def prefixEnd_2634260 : Nat := 4983230072969 + 3 ^ 40 * 2634260 * 2
def baseEnd_2634260 : Nat := 450880516304322893111755

theorem tailTrace_2634260 : CollatzResearch.WordTrace tailWord_2634260 prefixEnd_2634260 450880516304322893111755 := by
  unfold tailWord_2634260
  simp only [CollatzResearch.WordTrace]
  refine ⟨48039677718266695317538117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64052903624355593756717489 48039677718266695317538117)
  ·
    refine ⟨9007439572175005372038397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48039677718266695317538117 9007439572175005372038397)
    ·
      refine ⟨3377789839565627014514399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9007439572175005372038397 3377789839565627014514399)
      ·
        refine ⟨5066684759348440521771599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3377789839565627014514399 5066684759348440521771599)
        ·
          refine ⟨7600027139022660782657399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5066684759348440521771599 7600027139022660782657399)
          ·
            refine ⟨11400040708533991173986099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7600027139022660782657399 11400040708533991173986099)
            ·
              refine ⟨17100061062800986760979149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11400040708533991173986099 17100061062800986760979149)
              ·
                refine ⟨6412522898550370035367181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17100061062800986760979149 6412522898550370035367181)
                ·
                  refine ⟨2404696086956388763262693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6412522898550370035367181 2404696086956388763262693)
                  ·
                    refine ⟨450880516304322893111755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2404696086956388763262693 450880516304322893111755)
                    ·
                      rfl

theorem cell23_2634260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_2634260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2634260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2634260 prefixEnd_2634260 := by exact prefixLift 2634260
  have htrace : WordTrace (prefixWord ++ tailWord_2634260) baseStart_2634260 baseEnd_2634260 := by
    simpa [prefixWord, tailWord_2634260, baseEnd_2634260] using wordTrace_append hprefix tailTrace_2634260
  have hstable : (prefixWord ++ tailWord_2634260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2634260).length < 2 ^ (prefixWord ++ tailWord_2634260).sum := by decide
  have hdescent : baseEnd_2634260 < baseStart_2634260 := by decide
  rcases family_descends (prefixWord ++ tailWord_2634260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2634273 : List Nat := [1, 2, 3, 2, 2, 1, 5, 1, 6]
def baseStart_2634273 : Nat := 118140960795 + 2634273 * 2 ^ 59
def prefixEnd_2634273 : Nat := 4983230072969 + 3 ^ 40 * 2634273 * 2
def baseEnd_2634273 : Nat := 150294247129053014274745

theorem tailTrace_2634273 : CollatzResearch.WordTrace tailWord_2634273 prefixEnd_2634273 150294247129053014274745 := by
  unfold tailWord_2634273
  simp only [CollatzResearch.WordTrace]
  refine ⟨96079829585486293855299473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64053219723657529236866315 96079829585486293855299473)
  ·
    refine ⟨72059872189114720391474605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96079829585486293855299473 72059872189114720391474605)
    ·
      refine ⟨27022452070918020146802977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72059872189114720391474605 27022452070918020146802977)
      ·
        refine ⟨20266839053188515110102233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27022452070918020146802977 20266839053188515110102233)
        ·
          refine ⟨15200129289891386332576675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20266839053188515110102233 15200129289891386332576675)
          ·
            refine ⟨22800193934837079498865013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15200129289891386332576675 22800193934837079498865013)
            ·
              refine ⟨2137518181390976203018595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22800193934837079498865013 2137518181390976203018595)
              ·
                refine ⟨3206277272086464304527893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2137518181390976203018595 3206277272086464304527893)
                ·
                  refine ⟨150294247129053014274745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3206277272086464304527893 150294247129053014274745)
                  ·
                    rfl

theorem cell23_2634273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 5, 1, 6].length) (baseStart_2634273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2634273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2634273 prefixEnd_2634273 := by exact prefixLift 2634273
  have htrace : WordTrace (prefixWord ++ tailWord_2634273) baseStart_2634273 baseEnd_2634273 := by
    simpa [prefixWord, tailWord_2634273, baseEnd_2634273] using wordTrace_append hprefix tailTrace_2634273
  have hstable : (prefixWord ++ tailWord_2634273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2634273).length < 2 ^ (prefixWord ++ tailWord_2634273).sum := by decide
  have hdescent : baseEnd_2634273 < baseStart_2634273 := by decide
  rcases family_descends (prefixWord ++ tailWord_2634273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2634293 : List Nat := [1, 3, 3, 1, 1, 2, 1, 3, 1, 5, 2]
def baseStart_2634293 : Nat := 118140960795 + 2634293 * 2 ^ 59
def prefixEnd_2634293 : Nat := 4983230072969 + 3 ^ 40 * 2634293 * 2
def baseEnd_2634293 : Nat := 1352658493774567050222613

theorem tailTrace_2634293 : CollatzResearch.WordTrace tailWord_2634293 prefixEnd_2634293 1352658493774567050222613 := by
  unfold tailWord_2634293
  simp only [CollatzResearch.WordTrace]
  refine ⟨96080559045413837271027533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64053706030275891514018355 96080559045413837271027533)
  ·
    refine ⟨36030209642030188976635325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96080559045413837271027533 36030209642030188976635325)
    ·
      refine ⟨13511328615761320866238247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36030209642030188976635325 13511328615761320866238247)
      ·
        refine ⟨20266992923641981299357371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13511328615761320866238247 20266992923641981299357371)
        ·
          refine ⟨30400489385462971949036057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20266992923641981299357371 30400489385462971949036057)
          ·
            refine ⟨22800367039097228961777043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30400489385462971949036057 22800367039097228961777043)
            ·
              refine ⟨34200550558645843442665565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22800367039097228961777043 34200550558645843442665565)
              ·
                refine ⟨12825206459492191290999587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34200550558645843442665565 12825206459492191290999587)
                ·
                  refine ⟨19237809689238286936499381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12825206459492191290999587 19237809689238286936499381)
                  ·
                    refine ⟨1803544658366089400296817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19237809689238286936499381 1803544658366089400296817)
                    ·
                      refine ⟨1352658493774567050222613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1803544658366089400296817 1352658493774567050222613)
                      ·
                        rfl

theorem cell23_2634293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 3, 1, 5, 2].length) (baseStart_2634293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2634293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2634293 prefixEnd_2634293 := by exact prefixLift 2634293
  have htrace : WordTrace (prefixWord ++ tailWord_2634293) baseStart_2634293 baseEnd_2634293 := by
    simpa [prefixWord, tailWord_2634293, baseEnd_2634293] using wordTrace_append hprefix tailTrace_2634293
  have hstable : (prefixWord ++ tailWord_2634293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2634293).length < 2 ^ (prefixWord ++ tailWord_2634293).sum := by decide
  have hdescent : baseEnd_2634293 < baseStart_2634293 := by decide
  rcases family_descends (prefixWord ++ tailWord_2634293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2634294 : List Nat := [5, 1, 2, 1, 2, 3, 1, 3, 1, 4]
def baseStart_2634294 : Nat := 118140960795 + 2634294 * 2 ^ 59
def prefixEnd_2634294 : Nat := 4983230072969 + 3 ^ 40 * 2634294 * 2
def baseEnd_2634294 : Nat := 450886335751740515436703

theorem tailTrace_2634294 : CollatzResearch.WordTrace tailWord_2634294 prefixEnd_2634294 450886335751740515436703 := by
  unfold tailWord_2634294
  simp only [CollatzResearch.WordTrace]
  refine ⟨6005037219900638402613371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 64053730345606809627875957 6005037219900638402613371)
  ·
    refine ⟨9007555829850957603920057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6005037219900638402613371 9007555829850957603920057)
    ·
      refine ⟨6755666872388218202940043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9007555829850957603920057 6755666872388218202940043)
      ·
        refine ⟨10133500308582327304410065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6755666872388218202940043 10133500308582327304410065)
        ·
          refine ⟨7600125231436745478307549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10133500308582327304410065 7600125231436745478307549)
          ·
            refine ⟨2850046961788779554365331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7600125231436745478307549 2850046961788779554365331)
            ·
              refine ⟨4275070442683169331547997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2850046961788779554365331 4275070442683169331547997)
              ·
                refine ⟨1603151416006188499330499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4275070442683169331547997 1603151416006188499330499)
                ·
                  refine ⟨2404727124009282748995749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1603151416006188499330499 2404727124009282748995749)
                  ·
                    refine ⟨450886335751740515436703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2404727124009282748995749 450886335751740515436703)
                    ·
                      rfl

theorem cell23_2634294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 1, 3, 1, 4].length) (baseStart_2634294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2634294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2634294 prefixEnd_2634294 := by exact prefixLift 2634294
  have htrace : WordTrace (prefixWord ++ tailWord_2634294) baseStart_2634294 baseEnd_2634294 := by
    simpa [prefixWord, tailWord_2634294, baseEnd_2634294] using wordTrace_append hprefix tailTrace_2634294
  have hstable : (prefixWord ++ tailWord_2634294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2634294).length < 2 ^ (prefixWord ++ tailWord_2634294).sum := by decide
  have hdescent : baseEnd_2634294 < baseStart_2634294 := by decide
  rcases family_descends (prefixWord ++ tailWord_2634294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2634317 : List Nat := [1, 6, 1, 1, 2, 1, 3, 1, 3, 1, 3]
def baseStart_2634317 : Nat := 118140960795 + 2634317 * 2 ^ 59
def prefixEnd_2634317 : Nat := 4983230072969 + 3 ^ 40 * 2634317 * 2
def baseEnd_2634317 : Nat := 1352670817310274956322503

theorem tailTrace_2634317 : CollatzResearch.WordTrace tailWord_2634317 prefixEnd_2634317 1352670817310274956322503 := by
  unfold tailWord_2634317
  simp only [CollatzResearch.WordTrace]
  refine ⟨96081434397326889369901205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64054289598217926246600803 96081434397326889369901205)
  ·
    refine ⟨4503817237374697939214119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 96081434397326889369901205 4503817237374697939214119)
    ·
      refine ⟨6755725856062046908821179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4503817237374697939214119 6755725856062046908821179)
      ·
        refine ⟨10133588784093070363231769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6755725856062046908821179 10133588784093070363231769)
        ·
          refine ⟨7600191588069802772423827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10133588784093070363231769 7600191588069802772423827)
          ·
            refine ⟨11400287382104704158635741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7600191588069802772423827 11400287382104704158635741)
            ·
              refine ⟨4275107768289264059488403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11400287382104704158635741 4275107768289264059488403)
              ·
                refine ⟨6412661652433896089232605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4275107768289264059488403 6412661652433896089232605)
                ·
                  refine ⟨2404748119662711033462227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6412661652433896089232605 2404748119662711033462227)
                  ·
                    refine ⟨3607122179494066550193341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2404748119662711033462227 3607122179494066550193341)
                    ·
                      refine ⟨1352670817310274956322503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3607122179494066550193341 1352670817310274956322503)
                      ·
                        rfl

theorem cell23_2634317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 3, 1, 3, 1, 3].length) (baseStart_2634317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2634317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2634317 prefixEnd_2634317 := by exact prefixLift 2634317
  have htrace : WordTrace (prefixWord ++ tailWord_2634317) baseStart_2634317 baseEnd_2634317 := by
    simpa [prefixWord, tailWord_2634317, baseEnd_2634317] using wordTrace_append hprefix tailTrace_2634317
  have hstable : (prefixWord ++ tailWord_2634317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2634317).length < 2 ^ (prefixWord ++ tailWord_2634317).sum := by decide
  have hdescent : baseEnd_2634317 < baseStart_2634317 := by decide
  rcases family_descends (prefixWord ++ tailWord_2634317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2634336 : List Nat := [2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 6]
def baseStart_2634336 : Nat := 118140960795 + 2634336 * 2 ^ 59
def prefixEnd_2634336 : Nat := 4983230072969 + 3 ^ 40 * 2634336 * 2
def baseEnd_2634336 : Nat := 1352680573442710381984915

theorem tailTrace_2634336 : CollatzResearch.WordTrace tailWord_2634336 prefixEnd_2634336 1352680573442710381984915 := by
  unfold tailWord_2634336
  simp only [CollatzResearch.WordTrace]
  refine ⟨48041063692129027807421431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64054751589505370409895241 48041063692129027807421431)
  ·
    refine ⟨72061595538193541711132147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48041063692129027807421431 72061595538193541711132147)
    ·
      refine ⟨108092393307290312566698221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72061595538193541711132147 108092393307290312566698221)
      ·
        refine ⟨40534647490233867212511833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108092393307290312566698221 40534647490233867212511833)
        ·
          refine ⟨30400985617675400409383875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40534647490233867212511833 30400985617675400409383875)
          ·
            refine ⟨45601478426513100614075813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30400985617675400409383875 45601478426513100614075813)
            ·
              refine ⟨8550277204971206365139215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45601478426513100614075813 8550277204971206365139215)
              ·
                refine ⟨12825415807456809547708823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8550277204971206365139215 12825415807456809547708823)
                ·
                  refine ⟨19238123711185214321563235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12825415807456809547708823 19238123711185214321563235)
                  ·
                    refine ⟨28857185566777821482344853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19238123711185214321563235 28857185566777821482344853)
                    ·
                      refine ⟨1352680573442710381984915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28857185566777821482344853 1352680573442710381984915)
                      ·
                        rfl

theorem cell23_2634336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 6].length) (baseStart_2634336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2634336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2634336 prefixEnd_2634336 := by exact prefixLift 2634336
  have htrace : WordTrace (prefixWord ++ tailWord_2634336) baseStart_2634336 baseEnd_2634336 := by
    simpa [prefixWord, tailWord_2634336, baseEnd_2634336] using wordTrace_append hprefix tailTrace_2634336
  have hstable : (prefixWord ++ tailWord_2634336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2634336).length < 2 ^ (prefixWord ++ tailWord_2634336).sum := by decide
  have hdescent : baseEnd_2634336 < baseStart_2634336 := by decide
  rcases family_descends (prefixWord ++ tailWord_2634336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2634340 : List Nat := [2, 3, 1, 1, 2, 2, 2, 1, 5, 2, 2]
def baseStart_2634340 : Nat := 118140960795 + 2634340 * 2 ^ 59
def prefixEnd_2634340 : Nat := 4983230072969 + 3 ^ 40 * 2634340 * 2
def baseEnd_2634340 : Nat := 1352682627365328366334897

theorem tailTrace_2634340 : CollatzResearch.WordTrace tailWord_2634340 prefixEnd_2634340 1352682627365328366334897 := by
  unfold tailWord_2634340
  simp only [CollatzResearch.WordTrace]
  refine ⟨48041136638121782148994237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64054848850829042865325649 48041136638121782148994237)
  ·
    refine ⟨18015426239295668305872839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48041136638121782148994237 18015426239295668305872839)
    ·
      refine ⟨27023139358943502458809259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18015426239295668305872839 27023139358943502458809259)
      ·
        refine ⟨40534709038415253688213889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27023139358943502458809259 40534709038415253688213889)
        ·
          refine ⟨30401031778811440266160417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40534709038415253688213889 30401031778811440266160417)
          ·
            refine ⟨22800773834108580199620313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30401031778811440266160417 22800773834108580199620313)
            ·
              refine ⟨17100580375581435149715235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22800773834108580199620313 17100580375581435149715235)
              ·
                refine ⟨25650870563372152724572853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17100580375581435149715235 25650870563372152724572853)
                ·
                  refine ⟨2404769115316139317928705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25650870563372152724572853 2404769115316139317928705)
                  ·
                    refine ⟨1803576836487104488446529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2404769115316139317928705 1803576836487104488446529)
                    ·
                      refine ⟨1352682627365328366334897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1803576836487104488446529 1352682627365328366334897)
                      ·
                        rfl

theorem cell23_2634340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 1, 5, 2, 2].length) (baseStart_2634340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2634340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2634340 prefixEnd_2634340 := by exact prefixLift 2634340
  have htrace : WordTrace (prefixWord ++ tailWord_2634340) baseStart_2634340 baseEnd_2634340 := by
    simpa [prefixWord, tailWord_2634340, baseEnd_2634340] using wordTrace_append hprefix tailTrace_2634340
  have hstable : (prefixWord ++ tailWord_2634340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2634340).length < 2 ^ (prefixWord ++ tailWord_2634340).sum := by decide
  have hdescent : baseEnd_2634340 < baseStart_2634340 := by decide
  rcases family_descends (prefixWord ++ tailWord_2634340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2634346 : List Nat := [3, 1, 3, 2, 1, 1, 1, 11]
def baseStart_2634346 : Nat := 118140960795 + 2634346 * 2 ^ 59
def prefixEnd_2634346 : Nat := 4983230072969 + 3 ^ 40 * 2634346 * 2
def baseEnd_2634346 : Nat := 50099470675898346031847

theorem tailTrace_2634346 : CollatzResearch.WordTrace tailWord_2634346 prefixEnd_2634346 50099470675898346031847 := by
  unfold tailWord_2634346
  simp only [CollatzResearch.WordTrace]
  refine ⟨24020623028555456830676723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64054994742814551548471261 24020623028555456830676723)
  ·
    refine ⟨36030934542833185246015085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24020623028555456830676723 36030934542833185246015085)
    ·
      refine ⟨13511600453562444467255657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36030934542833185246015085 13511600453562444467255657)
      ·
        refine ⟨10133700340171833350441743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13511600453562444467255657 10133700340171833350441743)
        ·
          refine ⟨15200550510257750025662615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10133700340171833350441743 15200550510257750025662615)
          ·
            refine ⟨22800825765386625038493923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15200550510257750025662615 22800825765386625038493923)
            ·
              refine ⟨34201238648079937557740885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22800825765386625038493923 34201238648079937557740885)
              ·
                refine ⟨50099470675898346031847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 34201238648079937557740885 50099470675898346031847)
                ·
                  rfl

theorem cell23_2634346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 11].length) (baseStart_2634346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2634346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2634346 prefixEnd_2634346 := by exact prefixLift 2634346
  have htrace : WordTrace (prefixWord ++ tailWord_2634346) baseStart_2634346 baseEnd_2634346 := by
    simpa [prefixWord, tailWord_2634346, baseEnd_2634346] using wordTrace_append hprefix tailTrace_2634346
  have hstable : (prefixWord ++ tailWord_2634346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2634346).length < 2 ^ (prefixWord ++ tailWord_2634346).sum := by decide
  have hdescent : baseEnd_2634346 < baseStart_2634346 := by decide
  rcases family_descends (prefixWord ++ tailWord_2634346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2634416 : List Nat := [2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 5]
def baseStart_2634416 : Nat := 118140960795 + 2634416 * 2 ^ 59
def prefixEnd_2634416 : Nat := 4983230072969 + 3 ^ 40 * 2634416 * 2
def baseEnd_2634416 : Nat := 1352721651895070068984547

theorem tailTrace_2634416 : CollatzResearch.WordTrace tailWord_2634416 prefixEnd_2634416 1352721651895070068984547 := by
  unfold tailWord_2634416
  simp only [CollatzResearch.WordTrace]
  refine ⟨48042522611984114638877551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64056696815978819518503401 48042522611984114638877551)
  ·
    refine ⟨72063783917976171958316327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48042522611984114638877551 72063783917976171958316327)
    ·
      refine ⟨108095675876964257937474491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72063783917976171958316327 108095675876964257937474491)
      ·
        refine ⟨162143513815446386906211737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108095675876964257937474491 162143513815446386906211737)
        ·
          refine ⟨121607635361584790179658803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162143513815446386906211737 121607635361584790179658803)
          ·
            refine ⟨182411453042377185269488205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121607635361584790179658803 182411453042377185269488205)
            ·
              refine ⟨68404294890891444476058077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 182411453042377185269488205 68404294890891444476058077)
              ·
                refine ⟨25651610584084291678521779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68404294890891444476058077 25651610584084291678521779)
                ·
                  refine ⟨38477415876126437517782669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25651610584084291678521779 38477415876126437517782669)
                  ·
                    refine ⟨14429030953547414069168501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38477415876126437517782669 14429030953547414069168501)
                    ·
                      refine ⟨1352721651895070068984547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14429030953547414069168501 1352721651895070068984547)
                      ·
                        rfl

theorem cell23_2634416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 5].length) (baseStart_2634416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2634416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2634416 prefixEnd_2634416 := by exact prefixLift 2634416
  have htrace : WordTrace (prefixWord ++ tailWord_2634416) baseStart_2634416 baseEnd_2634416 := by
    simpa [prefixWord, tailWord_2634416, baseEnd_2634416] using wordTrace_append hprefix tailTrace_2634416
  have hstable : (prefixWord ++ tailWord_2634416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2634416).length < 2 ^ (prefixWord ++ tailWord_2634416).sum := by decide
  have hdescent : baseEnd_2634416 < baseStart_2634416 := by decide
  rcases family_descends (prefixWord ++ tailWord_2634416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2634493 : List Nat := [1, 4, 1, 1, 1, 1, 5, 1, 1, 2, 5]
def baseStart_2634493 : Nat := 118140960795 + 2634493 * 2 ^ 59
def prefixEnd_2634493 : Nat := 4983230072969 + 3 ^ 40 * 2634493 * 2
def baseEnd_2634493 : Nat := 1352761189905466267721693

theorem tailTrace_2634493 : CollatzResearch.WordTrace tailWord_2634493 prefixEnd_2634493 1352761189905466267721693 := by
  unfold tailWord_2634493
  simp only [CollatzResearch.WordTrace]
  refine ⟨96087853644689271428308133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64058569096459514285538755 96087853644689271428308133)
  ·
    refine ⟨18016472558379238392807775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96087853644689271428308133 18016472558379238392807775)
    ·
      refine ⟨27024708837568857589211663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18016472558379238392807775 27024708837568857589211663)
      ·
        refine ⟨40537063256353286383817495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27024708837568857589211663 40537063256353286383817495)
        ·
          refine ⟨60805594884529929575726243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40537063256353286383817495 60805594884529929575726243)
          ·
            refine ⟨91208392326794894363589365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60805594884529929575726243 91208392326794894363589365)
            ·
              refine ⟨8550786780637021346586503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 91208392326794894363589365 8550786780637021346586503)
              ·
                refine ⟨12826180170955532019879755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8550786780637021346586503 12826180170955532019879755)
                ·
                  refine ⟨19239270256433298029819633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12826180170955532019879755 19239270256433298029819633)
                  ·
                    refine ⟨14429452692324973522364725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19239270256433298029819633 14429452692324973522364725)
                    ·
                      refine ⟨1352761189905466267721693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14429452692324973522364725 1352761189905466267721693)
                      ·
                        rfl

theorem cell23_2634493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 1, 1, 2, 5].length) (baseStart_2634493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2634493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2634493 prefixEnd_2634493 := by exact prefixLift 2634493
  have htrace : WordTrace (prefixWord ++ tailWord_2634493) baseStart_2634493 baseEnd_2634493 := by
    simpa [prefixWord, tailWord_2634493, baseEnd_2634493] using wordTrace_append hprefix tailTrace_2634493
  have hstable : (prefixWord ++ tailWord_2634493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2634493).length < 2 ^ (prefixWord ++ tailWord_2634493).sum := by decide
  have hdescent : baseEnd_2634493 < baseStart_2634493 := by decide
  rcases family_descends (prefixWord ++ tailWord_2634493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2634498 : List Nat := [3, 4, 1, 1, 1, 4, 2, 1, 2, 2, 2]
def baseStart_2634498 : Nat := 118140960795 + 2634498 * 2 ^ 59
def prefixEnd_2634498 : Nat := 4983230072969 + 3 ^ 40 * 2634498 * 2
def baseEnd_2634498 : Nat := 1352763757308738748159171

theorem tailTrace_2634498 : CollatzResearch.WordTrace tailWord_2634498 prefixEnd_2634498 1352763757308738748159171 := by
  unfold tailWord_2634498
  simp only [CollatzResearch.WordTrace]
  refine ⟨24022009002417789320560037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64058690673114104854826765 24022009002417789320560037)
  ·
    refine ⟨4504126687953335497605007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24022009002417789320560037 4504126687953335497605007)
    ·
      refine ⟨6756190031930003246407511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4504126687953335497605007 6756190031930003246407511)
      ·
        refine ⟨10134285047895004869611267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6756190031930003246407511 10134285047895004869611267)
        ·
          refine ⟨15201427571842507304416901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10134285047895004869611267 15201427571842507304416901)
          ·
            refine ⟨2850267669720470119578169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15201427571842507304416901 2850267669720470119578169)
            ·
              refine ⟨2137700752290352589683627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2850267669720470119578169 2137700752290352589683627)
              ·
                refine ⟨3206551128435528884525441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2137700752290352589683627 3206551128435528884525441)
                ·
                  refine ⟨2404913346326646663394081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3206551128435528884525441 2404913346326646663394081)
                  ·
                    refine ⟨1803685009744984997545561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2404913346326646663394081 1803685009744984997545561)
                    ·
                      refine ⟨1352763757308738748159171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1803685009744984997545561 1352763757308738748159171)
                      ·
                        rfl

theorem cell23_2634498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 2, 1, 2, 2, 2].length) (baseStart_2634498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2634498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2634498 prefixEnd_2634498 := by exact prefixLift 2634498
  have htrace : WordTrace (prefixWord ++ tailWord_2634498) baseStart_2634498 baseEnd_2634498 := by
    simpa [prefixWord, tailWord_2634498, baseEnd_2634498] using wordTrace_append hprefix tailTrace_2634498
  have hstable : (prefixWord ++ tailWord_2634498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2634498).length < 2 ^ (prefixWord ++ tailWord_2634498).sum := by decide
  have hdescent : baseEnd_2634498 < baseStart_2634498 := by decide
  rcases family_descends (prefixWord ++ tailWord_2634498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2634520 : List Nat := [2, 1, 2, 3, 1, 1, 1, 2, 4, 4, 2]
def baseStart_2634520 : Nat := 118140960795 + 2634520 * 2 ^ 59
def prefixEnd_2634520 : Nat := 4983230072969 + 3 ^ 40 * 2634520 * 2
def baseEnd_2634520 : Nat := 1352775053883137662084069

theorem tailTrace_2634520 : CollatzResearch.WordTrace tailWord_2634520 prefixEnd_2634520 1352775053883137662084069 := by
  unfold tailWord_2634520
  simp only [CollatzResearch.WordTrace]
  refine ⟨48044419207795727519770507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64059225610394303359694009 48044419207795727519770507)
  ·
    refine ⟨72066628811693591279655761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48044419207795727519770507 72066628811693591279655761)
    ·
      refine ⟨54049971608770193459741821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72066628811693591279655761 54049971608770193459741821)
      ·
        refine ⟨20268739353288822547403183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54049971608770193459741821 20268739353288822547403183)
        ·
          refine ⟨30403109029933233821104775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20268739353288822547403183 30403109029933233821104775)
          ·
            refine ⟨45604663544899850731657163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30403109029933233821104775 45604663544899850731657163)
            ·
              refine ⟨68406995317349776097485745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45604663544899850731657163 68406995317349776097485745)
              ·
                refine ⟨51305246488012332073114309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68406995317349776097485745 51305246488012332073114309)
                ·
                  refine ⟨9619733716502312263708933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51305246488012332073114309 9619733716502312263708933)
                  ·
                    refine ⟨1803700071844183549445425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9619733716502312263708933 1803700071844183549445425)
                    ·
                      refine ⟨1352775053883137662084069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1803700071844183549445425 1352775053883137662084069)
                      ·
                        rfl

theorem cell23_2634520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 4, 4, 2].length) (baseStart_2634520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2634520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2634520 prefixEnd_2634520 := by exact prefixLift 2634520
  have htrace : WordTrace (prefixWord ++ tailWord_2634520) baseStart_2634520 baseEnd_2634520 := by
    simpa [prefixWord, tailWord_2634520, baseEnd_2634520] using wordTrace_append hprefix tailTrace_2634520
  have hstable : (prefixWord ++ tailWord_2634520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2634520).length < 2 ^ (prefixWord ++ tailWord_2634520).sum := by decide
  have hdescent : baseEnd_2634520 < baseStart_2634520 := by decide
  rcases family_descends (prefixWord ++ tailWord_2634520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2634533 : List Nat := [1, 3, 1, 2, 3, 1, 2, 1, 2, 1, 6]
def baseStart_2634533 : Nat := 118140960795 + 2634533 * 2 ^ 59
def prefixEnd_2634533 : Nat := 4983230072969 + 3 ^ 40 * 2634533 * 2
def baseEnd_2634533 : Nat := 1352781729131646111221509

theorem tailTrace_2634533 : CollatzResearch.WordTrace tailWord_2634533 prefixEnd_2634533 1352781729131646111221509 := by
  unfold tailWord_2634533
  simp only [CollatzResearch.WordTrace]
  refine ⟨96089312564544358259764253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64059541709696238839842835 96089312564544358259764253)
  ·
    refine ⟨36033492211704134347411595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96089312564544358259764253 36033492211704134347411595)
    ·
      refine ⟨54050238317556201521117393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36033492211704134347411595 54050238317556201521117393)
      ·
        refine ⟨40537678738167151140838045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54050238317556201521117393 40537678738167151140838045)
        ·
          refine ⟨15201629526812681677814267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40537678738167151140838045 15201629526812681677814267)
          ·
            refine ⟨22802444290219022516721401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15201629526812681677814267 22802444290219022516721401)
            ·
              refine ⟨17101833217664266887541051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22802444290219022516721401 17101833217664266887541051)
              ·
                refine ⟨25652749826496400331311577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17101833217664266887541051 25652749826496400331311577)
                ·
                  refine ⟨19239562369872300248483683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25652749826496400331311577 19239562369872300248483683)
                  ·
                    refine ⟨28859343554808450372725525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19239562369872300248483683 28859343554808450372725525)
                    ·
                      refine ⟨1352781729131646111221509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28859343554808450372725525 1352781729131646111221509)
                      ·
                        rfl

theorem cell23_2634533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 1, 2, 1, 6].length) (baseStart_2634533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2634533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2634533 prefixEnd_2634533 := by exact prefixLift 2634533
  have htrace : WordTrace (prefixWord ++ tailWord_2634533) baseStart_2634533 baseEnd_2634533 := by
    simpa [prefixWord, tailWord_2634533, baseEnd_2634533] using wordTrace_append hprefix tailTrace_2634533
  have hstable : (prefixWord ++ tailWord_2634533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2634533).length < 2 ^ (prefixWord ++ tailWord_2634533).sum := by decide
  have hdescent : baseEnd_2634533 < baseStart_2634533 := by decide
  rcases family_descends (prefixWord ++ tailWord_2634533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2634538 : List Nat := [3, 1, 4, 3, 2, 1, 2, 2, 5]
def baseStart_2634538 : Nat := 118140960795 + 2634538 * 2 ^ 59
def prefixEnd_2634538 : Nat := 4983230072969 + 3 ^ 40 * 2634538 * 2
def baseEnd_2634538 : Nat := 150309366281657621295443

theorem tailTrace_2634538 : CollatzResearch.WordTrace tailWord_2634538 prefixEnd_2634538 150309366281657621295443 := by
  unfold tailWord_2634538
  simp only [CollatzResearch.WordTrace]
  refine ⟨24022373732381561028424067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64059663286350829409130845 24022373732381561028424067)
  ·
    refine ⟨36033560598572341542636101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24022373732381561028424067 36033560598572341542636101)
    ·
      refine ⟨6756292612232314039244269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36033560598572341542636101 6756292612232314039244269)
      ·
        refine ⟨2533609729587117764716601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6756292612232314039244269 2533609729587117764716601)
        ·
          refine ⟨1900207297190338323537451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2533609729587117764716601 1900207297190338323537451)
          ·
            refine ⟨2850310945785507485306177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1900207297190338323537451 2850310945785507485306177)
            ·
              refine ⟨2137733209339130613979633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2850310945785507485306177 2137733209339130613979633)
              ·
                refine ⟨1603299907004347960484725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2137733209339130613979633 1603299907004347960484725)
                ·
                  refine ⟨150309366281657621295443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1603299907004347960484725 150309366281657621295443)
                  ·
                    rfl

theorem cell23_2634538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 2, 2, 5].length) (baseStart_2634538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2634538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2634538 prefixEnd_2634538 := by exact prefixLift 2634538
  have htrace : WordTrace (prefixWord ++ tailWord_2634538) baseStart_2634538 baseEnd_2634538 := by
    simpa [prefixWord, tailWord_2634538, baseEnd_2634538] using wordTrace_append hprefix tailTrace_2634538
  have hstable : (prefixWord ++ tailWord_2634538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2634538).length < 2 ^ (prefixWord ++ tailWord_2634538).sum := by decide
  have hdescent : baseEnd_2634538 < baseStart_2634538 := by decide
  rcases family_descends (prefixWord ++ tailWord_2634538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2634540 : List Nat := [2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 3]
def baseStart_2634540 : Nat := 118140960795 + 2634540 * 2 ^ 59
def prefixEnd_2634540 : Nat := 4983230072969 + 3 ^ 40 * 2634540 * 2
def baseEnd_2634540 : Nat := 1352785323496227583833977

theorem tailTrace_2634540 : CollatzResearch.WordTrace tailWord_2634540 prefixEnd_2634540 1352785323496227583833977 := by
  unfold tailWord_2634540
  simp only [CollatzResearch.WordTrace]
  refine ⟨48044783937759499227634537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64059711917012665636846049 48044783937759499227634537)
  ·
    refine ⟨36033587953319624420725903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48044783937759499227634537 36033587953319624420725903)
    ·
      refine ⟨54050381929979436631088855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36033587953319624420725903 54050381929979436631088855)
      ·
        refine ⟨81075572894969154946633283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54050381929979436631088855 81075572894969154946633283)
        ·
          refine ⟨121613359342453732419949925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81075572894969154946633283 121613359342453732419949925)
          ·
            refine ⟨22802504876710074828740611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 121613359342453732419949925 22802504876710074828740611)
            ·
              refine ⟨34203757315065112243110917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22802504876710074828740611 34203757315065112243110917)
              ·
                refine ⟨6413204496574708545583297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34203757315065112243110917 6413204496574708545583297)
                ·
                  refine ⟨4809903372431031409187473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6413204496574708545583297 4809903372431031409187473)
                  ·
                    refine ⟨3607427529323273556890605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4809903372431031409187473 3607427529323273556890605)
                    ·
                      refine ⟨1352785323496227583833977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3607427529323273556890605 1352785323496227583833977)
                      ·
                        rfl

theorem cell23_2634540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 3].length) (baseStart_2634540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2634540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2634540 prefixEnd_2634540 := by exact prefixLift 2634540
  have htrace : WordTrace (prefixWord ++ tailWord_2634540) baseStart_2634540 baseEnd_2634540 := by
    simpa [prefixWord, tailWord_2634540, baseEnd_2634540] using wordTrace_append hprefix tailTrace_2634540
  have hstable : (prefixWord ++ tailWord_2634540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2634540).length < 2 ^ (prefixWord ++ tailWord_2634540).sum := by decide
  have hdescent : baseEnd_2634540 < baseStart_2634540 := by decide
  rcases family_descends (prefixWord ++ tailWord_2634540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2634594 : List Nat := [3, 3, 2, 1, 3, 2, 1, 2, 6]
def baseStart_2634594 : Nat := 118140960795 + 2634594 * 2 ^ 59
def prefixEnd_2634594 : Nat := 4983230072969 + 3 ^ 40 * 2634594 * 2
def baseEnd_2634594 : Nat := 150312561272396708062081

theorem tailTrace_2634594 : CollatzResearch.WordTrace tailWord_2634594 prefixEnd_2634594 150312561272396708062081 := by
  unfold tailWord_2634594
  simp only [CollatzResearch.WordTrace]
  refine ⟨24022884354330841419433709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64061024944882243785156557 24022884354330841419433709)
  ·
    refine ⟨9008581632874065532287641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24022884354330841419433709 9008581632874065532287641)
    ·
      refine ⟨6756436224655549149215731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9008581632874065532287641 6756436224655549149215731)
      ·
        refine ⟨10134654336983323723823597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6756436224655549149215731 10134654336983323723823597)
        ·
          refine ⟨3800495376368746396433849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10134654336983323723823597 3800495376368746396433849)
          ·
            refine ⟨2850371532276559797325387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3800495376368746396433849 2850371532276559797325387)
            ·
              refine ⟨4275557298414839695988081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2850371532276559797325387 4275557298414839695988081)
              ·
                refine ⟨3206667973811129771991061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4275557298414839695988081 3206667973811129771991061)
                ·
                  refine ⟨150312561272396708062081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3206667973811129771991061 150312561272396708062081)
                  ·
                    rfl

theorem cell23_2634594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 1, 2, 6].length) (baseStart_2634594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2634594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2634594 prefixEnd_2634594 := by exact prefixLift 2634594
  have htrace : WordTrace (prefixWord ++ tailWord_2634594) baseStart_2634594 baseEnd_2634594 := by
    simpa [prefixWord, tailWord_2634594, baseEnd_2634594] using wordTrace_append hprefix tailTrace_2634594
  have hstable : (prefixWord ++ tailWord_2634594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2634594).length < 2 ^ (prefixWord ++ tailWord_2634594).sum := by decide
  have hdescent : baseEnd_2634594 < baseStart_2634594 := by decide
  rcases family_descends (prefixWord ++ tailWord_2634594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2634597 : List Nat := [1, 3, 1, 3, 1, 1, 2, 4, 2, 3, 2]
def baseStart_2634597 : Nat := 118140960795 + 2634597 * 2 ^ 59
def prefixEnd_2634597 : Nat := 4983230072969 + 3 ^ 40 * 2634597 * 2
def baseEnd_2634597 : Nat := 1352814591893533860821215

theorem tailTrace_2634597 : CollatzResearch.WordTrace tailWord_2634597 prefixEnd_2634597 1352814591893533860821215 := by
  unfold tailWord_2634597
  simp only [CollatzResearch.WordTrace]
  refine ⟨96091646836312497190094045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64061097890874998126729363 96091646836312497190094045)
  ·
    refine ⟨36034367563617186446285267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96091646836312497190094045 36034367563617186446285267)
    ·
      refine ⟨54051551345425779669427901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36034367563617186446285267 54051551345425779669427901)
      ·
        refine ⟨20269331754534667376035463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54051551345425779669427901 20269331754534667376035463)
        ·
          refine ⟨30403997631802001064053195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20269331754534667376035463 30403997631802001064053195)
          ·
            refine ⟨45605996447703001596079793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30403997631802001064053195 45605996447703001596079793)
            ·
              refine ⟨34204497335777251197059845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45605996447703001596079793 34204497335777251197059845)
              ·
                refine ⟨6413343250458234599448721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34204497335777251197059845 6413343250458234599448721)
                ·
                  refine ⟨4810007437843675949586541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6413343250458234599448721 4810007437843675949586541)
                  ·
                    refine ⟨1803752789191378481094953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4810007437843675949586541 1803752789191378481094953)
                    ·
                      refine ⟨1352814591893533860821215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1803752789191378481094953 1352814591893533860821215)
                      ·
                        rfl

theorem cell23_2634597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 4, 2, 3, 2].length) (baseStart_2634597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2634597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2634597 prefixEnd_2634597 := by exact prefixLift 2634597
  have htrace : WordTrace (prefixWord ++ tailWord_2634597) baseStart_2634597 baseEnd_2634597 := by
    simpa [prefixWord, tailWord_2634597, baseEnd_2634597] using wordTrace_append hprefix tailTrace_2634597
  have hstable : (prefixWord ++ tailWord_2634597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2634597).length < 2 ^ (prefixWord ++ tailWord_2634597).sum := by decide
  have hdescent : baseEnd_2634597 < baseStart_2634597 := by decide
  rcases family_descends (prefixWord ++ tailWord_2634597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2634603 : List Nat := [1, 1, 1, 1, 2, 2, 4, 2, 3, 6]
def baseStart_2634603 : Nat := 118140960795 + 2634603 * 2 ^ 59
def prefixEnd_2634603 : Nat := 4983230072969 + 3 ^ 40 * 2634603 * 2
def baseEnd_2634603 : Nat := 450939224259153612448729

theorem tailTrace_2634603 : CollatzResearch.WordTrace tailWord_2634603 prefixEnd_2634603 450939224259153612448729 := by
  unfold tailWord_2634603
  simp only [CollatzResearch.WordTrace]
  refine ⟨96091865674290760214812463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64061243782860506809874975 96091865674290760214812463)
  ·
    refine ⟨144137798511436140322218695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96091865674290760214812463 144137798511436140322218695)
    ·
      refine ⟨216206697767154210483328043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144137798511436140322218695 216206697767154210483328043)
      ·
        refine ⟨324310046650731315724992065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216206697767154210483328043 324310046650731315724992065)
        ·
          refine ⟨243232534988048486793744049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 324310046650731315724992065 243232534988048486793744049)
          ·
            refine ⟨182424401241036365095308037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 243232534988048486793744049 182424401241036365095308037)
            ·
              refine ⟨34204575232694318455370257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 182424401241036365095308037 34204575232694318455370257)
              ·
                refine ⟨25653431424520738841527693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34204575232694318455370257 25653431424520738841527693)
                ·
                  refine ⟨9620036784195277065572885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25653431424520738841527693 9620036784195277065572885)
                  ·
                    refine ⟨450939224259153612448729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9620036784195277065572885 450939224259153612448729)
                    ·
                      rfl

theorem cell23_2634603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 2, 3, 6].length) (baseStart_2634603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2634603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2634603 prefixEnd_2634603 := by exact prefixLift 2634603
  have htrace : WordTrace (prefixWord ++ tailWord_2634603) baseStart_2634603 baseEnd_2634603 := by
    simpa [prefixWord, tailWord_2634603, baseEnd_2634603] using wordTrace_append hprefix tailTrace_2634603
  have hstable : (prefixWord ++ tailWord_2634603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2634603).length < 2 ^ (prefixWord ++ tailWord_2634603).sum := by decide
  have hdescent : baseEnd_2634603 < baseStart_2634603 := by decide
  rcases family_descends (prefixWord ++ tailWord_2634603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2634604 : List Nat := [2, 2, 1, 1, 4, 1, 1, 6, 1, 1, 3]
def baseStart_2634604 : Nat := 118140960795 + 2634604 * 2 ^ 59
def prefixEnd_2634604 : Nat := 4983230072969 + 3 ^ 40 * 2634604 * 2
def baseEnd_2634604 : Nat := 1352818186258115333433683

theorem tailTrace_2634604 : CollatzResearch.WordTrace tailWord_2634604 prefixEnd_2634604 1352818186258115333433683 := by
  unfold tailWord_2634604
  simp only [CollatzResearch.WordTrace]
  refine ⟨48045951073643568692799433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64061268098191424923732577 48045951073643568692799433)
  ·
    refine ⟨36034463305232676519599575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48045951073643568692799433 36034463305232676519599575)
    ·
      refine ⟨54051694957849014779399363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36034463305232676519599575 54051694957849014779399363)
      ·
        refine ⟨81077542436773522169099045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54051694957849014779399363 81077542436773522169099045)
        ·
          refine ⟨15202039206895035406706071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81077542436773522169099045 15202039206895035406706071)
          ·
            refine ⟨22803058810342553110059107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15202039206895035406706071 22803058810342553110059107)
            ·
              refine ⟨34204588215513829665088661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22803058810342553110059107 34204588215513829665088661)
              ·
                refine ⟨1603340072602210765551031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 34204588215513829665088661 1603340072602210765551031)
                ·
                  refine ⟨2405010108903316148326547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1603340072602210765551031 2405010108903316148326547)
                  ·
                    refine ⟨3607515163354974222489821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2405010108903316148326547 3607515163354974222489821)
                    ·
                      refine ⟨1352818186258115333433683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3607515163354974222489821 1352818186258115333433683)
                      ·
                        rfl

theorem cell23_2634604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 6, 1, 1, 3].length) (baseStart_2634604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2634604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2634604 prefixEnd_2634604 := by exact prefixLift 2634604
  have htrace : WordTrace (prefixWord ++ tailWord_2634604) baseStart_2634604 baseEnd_2634604 := by
    simpa [prefixWord, tailWord_2634604, baseEnd_2634604] using wordTrace_append hprefix tailTrace_2634604
  have hstable : (prefixWord ++ tailWord_2634604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2634604).length < 2 ^ (prefixWord ++ tailWord_2634604).sum := by decide
  have hdescent : baseEnd_2634604 < baseStart_2634604 := by decide
  rcases family_descends (prefixWord ++ tailWord_2634604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2634610 : List Nat := [3, 2, 1, 2, 1, 1, 2, 1, 5, 1, 4]
def baseStart_2634610 : Nat := 118140960795 + 2634610 * 2 ^ 59
def prefixEnd_2634610 : Nat := 4983230072969 + 3 ^ 40 * 2634610 * 2
def baseEnd_2634610 : Nat := 1352821267142042309958655

theorem tailTrace_2634610 : CollatzResearch.WordTrace tailWord_2634610 prefixEnd_2634610 1352821267142042309958655 := by
  unfold tailWord_2634610
  simp only [CollatzResearch.WordTrace]
  refine ⟨24023030246316350102579321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64061413990176933606878189 24023030246316350102579321)
  ·
    refine ⟨18017272684737262576934491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24023030246316350102579321 18017272684737262576934491)
    ·
      refine ⟨27025909027105893865401737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18017272684737262576934491 27025909027105893865401737)
      ·
        refine ⟨20269431770329420399051303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27025909027105893865401737 20269431770329420399051303)
        ·
          refine ⟨30404147655494130598576955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20269431770329420399051303 30404147655494130598576955)
          ·
            refine ⟨45606221483241195897865433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30404147655494130598576955 45606221483241195897865433)
            ·
              refine ⟨34204666112430896923399075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45606221483241195897865433 34204666112430896923399075)
              ·
                refine ⟨51306999168646345385098613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34204666112430896923399075 51306999168646345385098613)
                ·
                  refine ⟨4810031172060594879852995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51306999168646345385098613 4810031172060594879852995)
                  ·
                    refine ⟨7215046758090892319779493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4810031172060594879852995 7215046758090892319779493)
                    ·
                      refine ⟨1352821267142042309958655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7215046758090892319779493 1352821267142042309958655)
                      ·
                        rfl

theorem cell23_2634610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 5, 1, 4].length) (baseStart_2634610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2634610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2634610 prefixEnd_2634610 := by exact prefixLift 2634610
  have htrace : WordTrace (prefixWord ++ tailWord_2634610) baseStart_2634610 baseEnd_2634610 := by
    simpa [prefixWord, tailWord_2634610, baseEnd_2634610] using wordTrace_append hprefix tailTrace_2634610
  have hstable : (prefixWord ++ tailWord_2634610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2634610).length < 2 ^ (prefixWord ++ tailWord_2634610).sum := by decide
  have hdescent : baseEnd_2634610 < baseStart_2634610 := by decide
  rcases family_descends (prefixWord ++ tailWord_2634610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2634614 : List Nat := [5, 1, 1, 3, 1, 1, 1, 2, 1, 5, 2]
def baseStart_2634614 : Nat := 118140960795 + 2634614 * 2 ^ 59
def prefixEnd_2634614 : Nat := 4983230072969 + 3 ^ 40 * 2634614 * 2
def baseEnd_2634614 : Nat := 1352823321064660294308637

theorem tailTrace_2634614 : CollatzResearch.WordTrace tailWord_2634614 prefixEnd_2634614 1352823321064660294308637 := by
  unfold tailWord_2634614
  simp only [CollatzResearch.WordTrace]
  refine ⟨6005766679828181818341431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 64061511251500606062308597 6005766679828181818341431)
  ·
    refine ⟨9008650019742272727512147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6005766679828181818341431 9008650019742272727512147)
    ·
      refine ⟨13512975029613409091268221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9008650019742272727512147 13512975029613409091268221)
      ·
        refine ⟨5067365636105028409225583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13512975029613409091268221 5067365636105028409225583)
        ·
          refine ⟨7601048454157542613838375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5067365636105028409225583 7601048454157542613838375)
          ·
            refine ⟨11401572681236313920757563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7601048454157542613838375 11401572681236313920757563)
            ·
              refine ⟨17102359021854470881136345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11401572681236313920757563 17102359021854470881136345)
              ·
                refine ⟨12826769266390853160852259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17102359021854470881136345 12826769266390853160852259)
                ·
                  refine ⟨19240153899586279741278389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12826769266390853160852259 19240153899586279741278389)
                  ·
                    refine ⟨1803764428086213725744849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19240153899586279741278389 1803764428086213725744849)
                    ·
                      refine ⟨1352823321064660294308637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1803764428086213725744849 1352823321064660294308637)
                      ·
                        rfl

theorem cell23_2634614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 2, 1, 5, 2].length) (baseStart_2634614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2634614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2634614 prefixEnd_2634614 := by exact prefixLift 2634614
  have htrace : WordTrace (prefixWord ++ tailWord_2634614) baseStart_2634614 baseEnd_2634614 := by
    simpa [prefixWord, tailWord_2634614, baseEnd_2634614] using wordTrace_append hprefix tailTrace_2634614
  have hstable : (prefixWord ++ tailWord_2634614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2634614).length < 2 ^ (prefixWord ++ tailWord_2634614).sum := by decide
  have hdescent : baseEnd_2634614 < baseStart_2634614 := by decide
  rcases family_descends (prefixWord ++ tailWord_2634614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2634627 : List Nat := [1, 1, 1, 3, 4, 1, 4, 2, 1, 1, 4]
def baseStart_2634627 : Nat := 118140960795 + 2634627 * 2 ^ 59
def prefixEnd_2634627 : Nat := 4983230072969 + 3 ^ 40 * 2634627 * 2
def baseEnd_2634627 : Nat := 1352829996313168743446077

theorem tailTrace_2634627 : CollatzResearch.WordTrace tailWord_2634627 prefixEnd_2634627 1352829996313168743446077 := by
  unfold tailWord_2634627
  simp only [CollatzResearch.WordTrace]
  refine ⟨96092741026203812313686135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64061827350802541542457423 96092741026203812313686135)
  ·
    refine ⟨144139111539305718470529203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96092741026203812313686135 144139111539305718470529203)
    ·
      refine ⟨216208667308958577705793805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144139111539305718470529203 216208667308958577705793805)
      ·
        refine ⟨81078250240859466639672677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 216208667308958577705793805 81078250240859466639672677)
        ·
          refine ⟨15202171920161149994938627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81078250240859466639672677 15202171920161149994938627)
          ·
            refine ⟨22803257880241724992407941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15202171920161149994938627 22803257880241724992407941)
            ·
              refine ⟨4275610852545323436076489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22803257880241724992407941 4275610852545323436076489)
              ·
                refine ⟨3206708139408992577057367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4275610852545323436076489 3206708139408992577057367)
                ·
                  refine ⟨4810062209113488865586051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3206708139408992577057367 4810062209113488865586051)
                  ·
                    refine ⟨7215093313670233298379077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4810062209113488865586051 7215093313670233298379077)
                    ·
                      refine ⟨1352829996313168743446077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7215093313670233298379077 1352829996313168743446077)
                      ·
                        rfl

theorem cell23_2634627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4, 2, 1, 1, 4].length) (baseStart_2634627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2634627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2634627 prefixEnd_2634627 := by exact prefixLift 2634627
  have htrace : WordTrace (prefixWord ++ tailWord_2634627) baseStart_2634627 baseEnd_2634627 := by
    simpa [prefixWord, tailWord_2634627, baseEnd_2634627] using wordTrace_append hprefix tailTrace_2634627
  have hstable : (prefixWord ++ tailWord_2634627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2634627).length < 2 ^ (prefixWord ++ tailWord_2634627).sum := by decide
  have hdescent : baseEnd_2634627 < baseStart_2634627 := by decide
  rcases family_descends (prefixWord ++ tailWord_2634627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2634647 : List Nat := [1, 1, 3, 3, 1, 2, 1, 5, 1, 2, 3]
def baseStart_2634647 : Nat := 118140960795 + 2634647 * 2 ^ 59
def prefixEnd_2634647 : Nat := 4983230072969 + 3 ^ 40 * 2634647 * 2
def baseEnd_2634647 : Nat := 1352840265926258665195985

theorem tailTrace_2634647 : CollatzResearch.WordTrace tailWord_2634647 prefixEnd_2634647 1352840265926258665195985 := by
  unfold tailWord_2634647
  simp only [CollatzResearch.WordTrace]
  refine ⟨96093470486131355729414195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64062313657420903819609463 96093470486131355729414195)
  ·
    refine ⟨144140205729197033594121293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96093470486131355729414195 144140205729197033594121293)
    ·
      refine ⟨54052577148448887597795485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144140205729197033594121293 54052577148448887597795485)
      ·
        refine ⟨20269716430668332849173307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54052577148448887597795485 20269716430668332849173307)
        ·
          refine ⟨30404574646002499273759961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20269716430668332849173307 30404574646002499273759961)
          ·
            refine ⟨22803430984501874455319971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30404574646002499273759961 22803430984501874455319971)
            ·
              refine ⟨34205146476752811682979957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22803430984501874455319971 34205146476752811682979957)
              ·
                refine ⟨3206732482195576095279371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34205146476752811682979957 3206732482195576095279371)
                ·
                  refine ⟨4810098723293364142919057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3206732482195576095279371 4810098723293364142919057)
                  ·
                    refine ⟨3607574042470023107189293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4810098723293364142919057 3607574042470023107189293)
                    ·
                      refine ⟨1352840265926258665195985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3607574042470023107189293 1352840265926258665195985)
                      ·
                        rfl

theorem cell23_2634647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 5, 1, 2, 3].length) (baseStart_2634647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2634647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2634647 prefixEnd_2634647 := by exact prefixLift 2634647
  have htrace : WordTrace (prefixWord ++ tailWord_2634647) baseStart_2634647 baseEnd_2634647 := by
    simpa [prefixWord, tailWord_2634647, baseEnd_2634647] using wordTrace_append hprefix tailTrace_2634647
  have hstable : (prefixWord ++ tailWord_2634647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2634647).length < 2 ^ (prefixWord ++ tailWord_2634647).sum := by decide
  have hdescent : baseEnd_2634647 < baseStart_2634647 := by decide
  rcases family_descends (prefixWord ++ tailWord_2634647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2634677 : List Nat := [1, 3, 3, 2, 1, 1, 2, 3, 1, 3, 3]
def baseStart_2634677 : Nat := 118140960795 + 2634677 * 2 ^ 59
def prefixEnd_2634677 : Nat := 4983230072969 + 3 ^ 40 * 2634677 * 2
def baseEnd_2634677 : Nat := 1352855670345893547820847

theorem tailTrace_2634677 : CollatzResearch.WordTrace tailWord_2634677 prefixEnd_2634677 1352855670345893547820847 := by
  unfold tailWord_2634677
  simp only [CollatzResearch.WordTrace]
  refine ⟨96094564676022670853006285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64063043117348447235337523 96094564676022670853006285)
  ·
    refine ⟨36035461753508501569877357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96094564676022670853006285 36035461753508501569877357)
    ·
      refine ⟨13513298157565688088704009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36035461753508501569877357 13513298157565688088704009)
      ·
        refine ⟨10134973618174266066528007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13513298157565688088704009 10134973618174266066528007)
        ·
          refine ⟨15202460427261399099792011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10134973618174266066528007 15202460427261399099792011)
          ·
            refine ⟨22803690640892098649688017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15202460427261399099792011 22803690640892098649688017)
            ·
              refine ⟨17102767980669073987266013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22803690640892098649688017 17102767980669073987266013)
              ·
                refine ⟨6413537992750902745224755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17102767980669073987266013 6413537992750902745224755)
                ·
                  refine ⟨9620306989126354117837133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6413537992750902745224755 9620306989126354117837133)
                  ·
                    refine ⟨3607615120922382794188925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9620306989126354117837133 3607615120922382794188925)
                    ·
                      refine ⟨1352855670345893547820847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3607615120922382794188925 1352855670345893547820847)
                      ·
                        rfl

theorem cell23_2634677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 3, 1, 3, 3].length) (baseStart_2634677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2634677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2634677 prefixEnd_2634677 := by exact prefixLift 2634677
  have htrace : WordTrace (prefixWord ++ tailWord_2634677) baseStart_2634677 baseEnd_2634677 := by
    simpa [prefixWord, tailWord_2634677, baseEnd_2634677] using wordTrace_append hprefix tailTrace_2634677
  have hstable : (prefixWord ++ tailWord_2634677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2634677).length < 2 ^ (prefixWord ++ tailWord_2634677).sum := by decide
  have hdescent : baseEnd_2634677 < baseStart_2634677 := by decide
  rcases family_descends (prefixWord ++ tailWord_2634677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2634678 : List Nat := [5, 1, 4, 1, 1, 1, 1, 1, 3, 1, 4]
def baseStart_2634678 : Nat := 118140960795 + 2634678 * 2 ^ 59
def prefixEnd_2634678 : Nat := 4983230072969 + 3 ^ 40 * 2634678 * 2
def baseEnd_2634678 : Nat := 1352856183826548043908343

theorem tailTrace_2634678 : CollatzResearch.WordTrace tailWord_2634678 prefixEnd_2634678 1352856183826548043908343 := by
  unfold tailWord_2634678
  simp only [CollatzResearch.WordTrace]
  refine ⟨6005912571813690501487043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 64063067432679365349195125 6005912571813690501487043)
  ·
    refine ⟨9008868857720535752230565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6005912571813690501487043 9008868857720535752230565)
    ·
      refine ⟨1689162910822600453543231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9008868857720535752230565 1689162910822600453543231)
      ·
        refine ⟨2533744366233900680314847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1689162910822600453543231 2533744366233900680314847)
        ·
          refine ⟨3800616549350851020472271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2533744366233900680314847 3800616549350851020472271)
          ·
            refine ⟨5700924824026276530708407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3800616549350851020472271 5700924824026276530708407)
            ·
              refine ⟨8551387236039414796062611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5700924824026276530708407 8551387236039414796062611)
              ·
                refine ⟨12827080854059122194093917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8551387236039414796062611 12827080854059122194093917)
                ·
                  refine ⟨4810155320272170822785219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12827080854059122194093917 4810155320272170822785219)
                  ·
                    refine ⟨7215232980408256234177829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4810155320272170822785219 7215232980408256234177829)
                    ·
                      refine ⟨1352856183826548043908343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7215232980408256234177829 1352856183826548043908343)
                      ·
                        rfl

theorem cell23_2634678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_2634678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2634678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2634678 prefixEnd_2634678 := by exact prefixLift 2634678
  have htrace : WordTrace (prefixWord ++ tailWord_2634678) baseStart_2634678 baseEnd_2634678 := by
    simpa [prefixWord, tailWord_2634678, baseEnd_2634678] using wordTrace_append hprefix tailTrace_2634678
  have hstable : (prefixWord ++ tailWord_2634678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2634678).length < 2 ^ (prefixWord ++ tailWord_2634678).sum := by decide
  have hdescent : baseEnd_2634678 < baseStart_2634678 := by decide
  rcases family_descends (prefixWord ++ tailWord_2634678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2634701 : List Nat := [1, 6, 3, 1, 2, 10]
def baseStart_2634701 : Nat := 118140960795 + 2634701 * 2 ^ 59
def prefixEnd_2634701 : Nat := 4983230072969 + 3 ^ 40 * 2634701 * 2
def baseEnd_2634701 : Nat := 5567357999512763184859

theorem tailTrace_2634701 : CollatzResearch.WordTrace tailWord_2634701 prefixEnd_2634701 5567357999512763184859 := by
  unfold tailWord_2634701
  simp only [CollatzResearch.WordTrace]
  refine ⟨96095440027935722951879957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64063626685290481967919971 96095440027935722951879957)
  ·
    refine ⟨4504473751309487013369373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 96095440027935722951879957 4504473751309487013369373)
    ·
      refine ⟨1689177656741057630013515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4504473751309487013369373 1689177656741057630013515)
      ·
        refine ⟨2533766485111586445020273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1689177656741057630013515 2533766485111586445020273)
        ·
          refine ⟨1900324863833689833765205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2533766485111586445020273 1900324863833689833765205)
          ·
            refine ⟨5567357999512763184859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1900324863833689833765205 5567357999512763184859)
            ·
              rfl

theorem cell23_2634701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 10].length) (baseStart_2634701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2634701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2634701 prefixEnd_2634701 := by exact prefixLift 2634701
  have htrace : WordTrace (prefixWord ++ tailWord_2634701) baseStart_2634701 baseEnd_2634701 := by
    simpa [prefixWord, tailWord_2634701, baseEnd_2634701] using wordTrace_append hprefix tailTrace_2634701
  have hstable : (prefixWord ++ tailWord_2634701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2634701).length < 2 ^ (prefixWord ++ tailWord_2634701).sum := by decide
  have hdescent : baseEnd_2634701 < baseStart_2634701 := by decide
  rcases family_descends (prefixWord ++ tailWord_2634701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2634717 : List Nat := [1, 4, 3, 1, 2, 1, 1, 1, 2, 3, 4]
def baseStart_2634717 : Nat := 118140960795 + 2634717 * 2 ^ 59
def prefixEnd_2634717 : Nat := 4983230072969 + 3 ^ 40 * 2634717 * 2
def baseEnd_2634717 : Nat := 1352876209572073391320663

theorem tailTrace_2634717 : CollatzResearch.WordTrace tailWord_2634717 prefixEnd_2634717 1352876209572073391320663 := by
  unfold tailWord_2634717
  simp only [CollatzResearch.WordTrace]
  refine ⟨96096023595877757684462405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64064015730585171789641603 96096023595877757684462405)
  ·
    refine ⟨18018004424227079565836701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96096023595877757684462405 18018004424227079565836701)
    ·
      refine ⟨6756751659085154837188763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18018004424227079565836701 6756751659085154837188763)
      ·
        refine ⟨10135127488627732255783145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6756751659085154837188763 10135127488627732255783145)
        ·
          refine ⟨7601345616470799191837359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10135127488627732255783145 7601345616470799191837359)
          ·
            refine ⟨11402018424706198787756039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7601345616470799191837359 11402018424706198787756039)
            ·
              refine ⟨17103027637059298181634059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11402018424706198787756039 17103027637059298181634059)
              ·
                refine ⟨25654541455588947272451089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17103027637059298181634059 25654541455588947272451089)
                ·
                  refine ⟨19240906091691710454338317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25654541455588947272451089 19240906091691710454338317)
                  ·
                    refine ⟨7215339784384391420376869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19240906091691710454338317 7215339784384391420376869)
                    ·
                      refine ⟨1352876209572073391320663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7215339784384391420376869 1352876209572073391320663)
                      ·
                        rfl

theorem cell23_2634717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_2634717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2634717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2634717 prefixEnd_2634717 := by exact prefixLift 2634717
  have htrace : WordTrace (prefixWord ++ tailWord_2634717) baseStart_2634717 baseEnd_2634717 := by
    simpa [prefixWord, tailWord_2634717, baseEnd_2634717] using wordTrace_append hprefix tailTrace_2634717
  have hstable : (prefixWord ++ tailWord_2634717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2634717).length < 2 ^ (prefixWord ++ tailWord_2634717).sum := by decide
  have hdescent : baseEnd_2634717 < baseStart_2634717 := by decide
  rcases family_descends (prefixWord ++ tailWord_2634717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2634727 : List Nat := [1, 1, 5, 2, 2, 2, 1, 1, 2, 6]
def baseStart_2634727 : Nat := 118140960795 + 2634727 * 2 ^ 59
def prefixEnd_2634727 : Nat := 4983230072969 + 3 ^ 40 * 2634727 * 2
def baseEnd_2634727 : Nat := 450960448126206117398539

theorem tailTrace_2634727 : CollatzResearch.WordTrace tailWord_2634727 prefixEnd_2634727 450960448126206117398539 := by
  unfold tailWord_2634727
  simp only [CollatzResearch.WordTrace]
  refine ⟨96096388325841529392326435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64064258883894352928217623 96096388325841529392326435)
  ·
    refine ⟨144144582488762294088489653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96096388325841529392326435 144144582488762294088489653)
    ·
      refine ⟨13513554608321465070795905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 144144582488762294088489653 13513554608321465070795905)
      ·
        refine ⟨10135165956241098803096929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13513554608321465070795905 10135165956241098803096929)
        ·
          refine ⟨7601374467180824102322697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10135165956241098803096929 7601374467180824102322697)
          ·
            refine ⟨5701030850385618076742023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7601374467180824102322697 5701030850385618076742023)
            ·
              refine ⟨8551546275578427115113035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5701030850385618076742023 8551546275578427115113035)
              ·
                refine ⟨12827319413367640672669553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8551546275578427115113035 12827319413367640672669553)
                ·
                  refine ⟨9620489560025730504502165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12827319413367640672669553 9620489560025730504502165)
                  ·
                    refine ⟨450960448126206117398539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9620489560025730504502165 450960448126206117398539)
                    ·
                      rfl

theorem cell23_2634727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 1, 2, 6].length) (baseStart_2634727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2634727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2634727 prefixEnd_2634727 := by exact prefixLift 2634727
  have htrace : WordTrace (prefixWord ++ tailWord_2634727) baseStart_2634727 baseEnd_2634727 := by
    simpa [prefixWord, tailWord_2634727, baseEnd_2634727] using wordTrace_append hprefix tailTrace_2634727
  have hstable : (prefixWord ++ tailWord_2634727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2634727).length < 2 ^ (prefixWord ++ tailWord_2634727).sum := by decide
  have hdescent : baseEnd_2634727 < baseStart_2634727 := by decide
  rcases family_descends (prefixWord ++ tailWord_2634727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2634777 : List Nat := [1, 2, 1, 2, 1, 1, 4, 1, 1, 7, 2]
def baseStart_2634777 : Nat := 118140960795 + 2634777 * 2 ^ 59
def prefixEnd_2634777 : Nat := 4983230072969 + 3 ^ 40 * 2634777 * 2
def baseEnd_2634777 : Nat := 1352907018411343156570387

theorem tailTrace_2634777 : CollatzResearch.WordTrace tailWord_2634777 prefixEnd_2634777 1352907018411343156570387 := by
  unfold tailWord_2634777
  simp only [CollatzResearch.WordTrace]
  refine ⟨96098211975660387931646585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64065474650440258621097723 96098211975660387931646585)
  ·
    refine ⟨72073658981745290948734939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96098211975660387931646585 72073658981745290948734939)
    ·
      refine ⟨108110488472617936423102409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72073658981745290948734939 108110488472617936423102409)
      ·
        refine ⟨81082866354463452317326807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108110488472617936423102409 81082866354463452317326807)
        ·
          refine ⟨121624299531695178475990211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81082866354463452317326807 121624299531695178475990211)
          ·
            refine ⟨182436449297542767713985317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121624299531695178475990211 182436449297542767713985317)
            ·
              refine ⟨34206834243289268946372247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 182436449297542767713985317 34206834243289268946372247)
              ·
                refine ⟨51310251364933903419558371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34206834243289268946372247 51310251364933903419558371)
                ·
                  refine ⟨76965377047400855129337557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51310251364933903419558371 76965377047400855129337557)
                  ·
                    refine ⟨1803876024548457542093849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 76965377047400855129337557 1803876024548457542093849)
                    ·
                      refine ⟨1352907018411343156570387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1803876024548457542093849 1352907018411343156570387)
                      ·
                        rfl

theorem cell23_2634777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 7, 2].length) (baseStart_2634777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2634777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2634777 prefixEnd_2634777 := by exact prefixLift 2634777
  have htrace : WordTrace (prefixWord ++ tailWord_2634777) baseStart_2634777 baseEnd_2634777 := by
    simpa [prefixWord, tailWord_2634777, baseEnd_2634777] using wordTrace_append hprefix tailTrace_2634777
  have hstable : (prefixWord ++ tailWord_2634777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2634777).length < 2 ^ (prefixWord ++ tailWord_2634777).sum := by decide
  have hdescent : baseEnd_2634777 < baseStart_2634777 := by decide
  rcases family_descends (prefixWord ++ tailWord_2634777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2634800 : List Nat := [2, 1, 1, 1, 2, 4, 1, 1, 2, 8]
def baseStart_2634800 : Nat := 118140960795 + 2634800 * 2 ^ 59
def prefixEnd_2634800 : Nat := 4983230072969 + 3 ^ 40 * 2634800 * 2
def baseEnd_2634800 : Nat := 450972942822132188860927

theorem tailTrace_2634800 : CollatzResearch.WordTrace tailWord_2634800 prefixEnd_2634800 450972942822132188860927 := by
  unfold tailWord_2634800
  simp only [CollatzResearch.WordTrace]
  refine ⟨48049525427288531429866927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64066033903051375239822569 48049525427288531429866927)
  ·
    refine ⟨72074288140932797144800391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48049525427288531429866927 72074288140932797144800391)
    ·
      refine ⟨108111432211399195717200587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72074288140932797144800391 108111432211399195717200587)
      ·
        refine ⟨162167148317098793575800881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108111432211399195717200587 162167148317098793575800881)
        ·
          refine ⟨121625361237824095181850661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162167148317098793575800881 121625361237824095181850661)
          ·
            refine ⟨22804755232092017846596999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 121625361237824095181850661 22804755232092017846596999)
            ·
              refine ⟨34207132848138026769895499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22804755232092017846596999 34207132848138026769895499)
              ·
                refine ⟨51310699272207040154843249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34207132848138026769895499 51310699272207040154843249)
                ·
                  refine ⟨38483024454155280116132437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51310699272207040154843249 38483024454155280116132437)
                  ·
                    refine ⟨450972942822132188860927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 38483024454155280116132437 450972942822132188860927)
                    ·
                      rfl

theorem cell23_2634800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 2, 8].length) (baseStart_2634800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2634800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2634800 prefixEnd_2634800 := by exact prefixLift 2634800
  have htrace : WordTrace (prefixWord ++ tailWord_2634800) baseStart_2634800 baseEnd_2634800 := by
    simpa [prefixWord, tailWord_2634800, baseEnd_2634800] using wordTrace_append hprefix tailTrace_2634800
  have hstable : (prefixWord ++ tailWord_2634800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2634800).length < 2 ^ (prefixWord ++ tailWord_2634800).sum := by decide
  have hdescent : baseEnd_2634800 < baseStart_2634800 := by decide
  rcases family_descends (prefixWord ++ tailWord_2634800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2634804 : List Nat := [2, 5, 1, 2, 1, 1, 2, 1, 1, 7]
def baseStart_2634804 : Nat := 118140960795 + 2634804 * 2 ^ 59
def prefixEnd_2634804 : Nat := 4983230072969 + 3 ^ 40 * 2634804 * 2
def baseEnd_2634804 : Nat := 450973627463004850310921

theorem tailTrace_2634804 : CollatzResearch.WordTrace tailWord_2634804 prefixEnd_2634804 450973627463004850310921 := by
  unfold tailWord_2634804
  simp only [CollatzResearch.WordTrace]
  refine ⟨48049598373281285771439733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64066131164375047695252977 48049598373281285771439733)
  ·
    refine ⟨4504649847495120541072475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 48049598373281285771439733 4504649847495120541072475)
    ·
      refine ⟨6756974771242680811608713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4504649847495120541072475 6756974771242680811608713)
      ·
        refine ⟨5067731078432010608706535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6756974771242680811608713 5067731078432010608706535)
        ·
          refine ⟨7601596617648015913059803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5067731078432010608706535 7601596617648015913059803)
          ·
            refine ⟨11402394926472023869589705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7601596617648015913059803 11402394926472023869589705)
            ·
              refine ⟨8551796194854017902192279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11402394926472023869589705 8551796194854017902192279)
              ·
                refine ⟨12827694292281026853288419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8551796194854017902192279 12827694292281026853288419)
                ·
                  refine ⟨19241541438421540279932629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12827694292281026853288419 19241541438421540279932629)
                  ·
                    refine ⟨450973627463004850310921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19241541438421540279932629 450973627463004850310921)
                    ·
                      rfl

theorem cell23_2634804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_2634804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2634804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2634804 prefixEnd_2634804 := by exact prefixLift 2634804
  have htrace : WordTrace (prefixWord ++ tailWord_2634804) baseStart_2634804 baseEnd_2634804 := by
    simpa [prefixWord, tailWord_2634804, baseEnd_2634804] using wordTrace_append hprefix tailTrace_2634804
  have hstable : (prefixWord ++ tailWord_2634804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2634804).length < 2 ^ (prefixWord ++ tailWord_2634804).sum := by decide
  have hdescent : baseEnd_2634804 < baseStart_2634804 := by decide
  rcases family_descends (prefixWord ++ tailWord_2634804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2634807 : List Nat := [1, 1, 3, 1, 2, 2, 1, 5, 2, 1, 4]
def baseStart_2634807 : Nat := 118140960795 + 2634807 * 2 ^ 59
def prefixEnd_2634807 : Nat := 4983230072969 + 3 ^ 40 * 2634807 * 2
def baseEnd_2634807 : Nat := 1352922422830978039195249

theorem tailTrace_2634807 : CollatzResearch.WordTrace tailWord_2634807 prefixEnd_2634807 1352922422830978039195249 := by
  unfold tailWord_2634807
  simp only [CollatzResearch.WordTrace]
  refine ⟨96099306165551703055238675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64066204110367802036825783 96099306165551703055238675)
  ·
    refine ⟨144148959248327554582858013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96099306165551703055238675 144148959248327554582858013)
    ·
      refine ⟨54055859718122832968571755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144148959248327554582858013 54055859718122832968571755)
      ·
        refine ⟨81083789577184249452857633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54055859718122832968571755 81083789577184249452857633)
        ·
          refine ⟨60812842182888187089643225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81083789577184249452857633 60812842182888187089643225)
          ·
            refine ⟨45609631637166140317232419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60812842182888187089643225 45609631637166140317232419)
            ·
              refine ⟨68414447455749210475848629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45609631637166140317232419 68414447455749210475848629)
              ·
                refine ⟨6413854448976488482110809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 68414447455749210475848629 6413854448976488482110809)
                ·
                  refine ⟨4810390836732366361583107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6413854448976488482110809 4810390836732366361583107)
                  ·
                    refine ⟨7215586255098549542374661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4810390836732366361583107 7215586255098549542374661)
                    ·
                      refine ⟨1352922422830978039195249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7215586255098549542374661 1352922422830978039195249)
                      ·
                        rfl

theorem cell23_2634807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 5, 2, 1, 4].length) (baseStart_2634807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2634807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2634807 prefixEnd_2634807 := by exact prefixLift 2634807
  have htrace : WordTrace (prefixWord ++ tailWord_2634807) baseStart_2634807 baseEnd_2634807 := by
    simpa [prefixWord, tailWord_2634807, baseEnd_2634807] using wordTrace_append hprefix tailTrace_2634807
  have hstable : (prefixWord ++ tailWord_2634807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2634807).length < 2 ^ (prefixWord ++ tailWord_2634807).sum := by decide
  have hdescent : baseEnd_2634807 < baseStart_2634807 := by decide
  rcases family_descends (prefixWord ++ tailWord_2634807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2634844 : List Nat := [2, 2, 4, 1, 1, 1, 1, 2, 4, 2, 3]
def baseStart_2634844 : Nat := 118140960795 + 2634844 * 2 ^ 59
def prefixEnd_2634844 : Nat := 4983230072969 + 3 ^ 40 * 2634844 * 2
def baseEnd_2634844 : Nat := 1352941421615194394432579

theorem tailTrace_2634844 : CollatzResearch.WordTrace tailWord_2634844 prefixEnd_2634844 1352941421615194394432579 := by
  unfold tailWord_2634844
  simp only [CollatzResearch.WordTrace]
  refine ⟨48050327833208829187167793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64067103777611772249557057 48050327833208829187167793)
  ·
    refine ⟨36037745874906621890375845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48050327833208829187167793 36037745874906621890375845)
    ·
      refine ⟨6757077351544991604445471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36037745874906621890375845 6757077351544991604445471)
      ·
        refine ⟨10135616027317487406668207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6757077351544991604445471 10135616027317487406668207)
        ·
          refine ⟨15203424040976231110002311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10135616027317487406668207 15203424040976231110002311)
          ·
            refine ⟨22805136061464346665003467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15203424040976231110002311 22805136061464346665003467)
            ·
              refine ⟨34207704092196519997505201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22805136061464346665003467 34207704092196519997505201)
              ·
                refine ⟨25655778069147389998128901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34207704092196519997505201 25655778069147389998128901)
                ·
                  refine ⟨4810458387965135624649169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25655778069147389998128901 4810458387965135624649169)
                  ·
                    refine ⟨3607843790973851718486877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4810458387965135624649169 3607843790973851718486877)
                    ·
                      refine ⟨1352941421615194394432579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3607843790973851718486877 1352941421615194394432579)
                      ·
                        rfl

theorem cell23_2634844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 2, 4, 2, 3].length) (baseStart_2634844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2634844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2634844 prefixEnd_2634844 := by exact prefixLift 2634844
  have htrace : WordTrace (prefixWord ++ tailWord_2634844) baseStart_2634844 baseEnd_2634844 := by
    simpa [prefixWord, tailWord_2634844, baseEnd_2634844] using wordTrace_append hprefix tailTrace_2634844
  have hstable : (prefixWord ++ tailWord_2634844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2634844).length < 2 ^ (prefixWord ++ tailWord_2634844).sum := by decide
  have hdescent : baseEnd_2634844 < baseStart_2634844 := by decide
  rcases family_descends (prefixWord ++ tailWord_2634844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2634847 : List Nat := [1, 1, 2, 3, 1, 1, 5, 3, 6]
def baseStart_2634847 : Nat := 118140960795 + 2634847 * 2 ^ 59
def prefixEnd_2634847 : Nat := 4983230072969 + 3 ^ 40 * 2634847 * 2
def baseEnd_2634847 : Nat := 150326995784128653632785

theorem tailTrace_2634847 : CollatzResearch.WordTrace tailWord_2634847 prefixEnd_2634847 150326995784128653632785 := by
  unfold tailWord_2634847
  simp only [CollatzResearch.WordTrace]
  refine ⟨96100765085406789886694795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64067176723604526591129863 96100765085406789886694795)
  ·
    refine ⟨144151147628110184830042193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96100765085406789886694795 144151147628110184830042193)
    ·
      refine ⟨108113360721082638622531645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144151147628110184830042193 108113360721082638622531645)
      ·
        refine ⟨40542510270405989483449367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108113360721082638622531645 40542510270405989483449367)
        ·
          refine ⟨60813765405608984225174051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40542510270405989483449367 60813765405608984225174051)
          ·
            refine ⟨91220648108413476337761077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60813765405608984225174051 91220648108413476337761077)
            ·
              refine ⟨8551935760163763406665101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 91220648108413476337761077 8551935760163763406665101)
              ·
                refine ⟨3206975910061411277499413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8551935760163763406665101 3206975910061411277499413)
                ·
                  refine ⟨150326995784128653632785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3206975910061411277499413 150326995784128653632785)
                  ·
                    rfl

theorem cell23_2634847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 3, 6].length) (baseStart_2634847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2634847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2634847 prefixEnd_2634847 := by exact prefixLift 2634847
  have htrace : WordTrace (prefixWord ++ tailWord_2634847) baseStart_2634847 baseEnd_2634847 := by
    simpa [prefixWord, tailWord_2634847, baseEnd_2634847] using wordTrace_append hprefix tailTrace_2634847
  have hstable : (prefixWord ++ tailWord_2634847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2634847).length < 2 ^ (prefixWord ++ tailWord_2634847).sum := by decide
  have hdescent : baseEnd_2634847 < baseStart_2634847 := by decide
  rcases family_descends (prefixWord ++ tailWord_2634847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2634861 : List Nat := [1, 5, 1, 1, 2, 3, 2, 1, 2, 2, 3]
def baseStart_2634861 : Nat := 118140960795 + 2634861 * 2 ^ 59
def prefixEnd_2634861 : Nat := 4983230072969 + 3 ^ 40 * 2634861 * 2
def baseEnd_2634861 : Nat := 1352950150786320827920001

theorem tailTrace_2634861 : CollatzResearch.WordTrace tailWord_2634861 prefixEnd_2634861 1352950150786320827920001 := by
  unfold tailWord_2634861
  simp only [CollatzResearch.WordTrace]
  refine ⟨96101275707356070277704437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64067517138237380185136291 96101275707356070277704437)
  ·
    refine ⟨9009494597564631588534791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 96101275707356070277704437 9009494597564631588534791)
    ·
      refine ⟨13514241896346947382802187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9009494597564631588534791 13514241896346947382802187)
      ·
        refine ⟨20271362844520421074203281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13514241896346947382802187 20271362844520421074203281)
        ·
          refine ⟨15203522133390315805652461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20271362844520421074203281 15203522133390315805652461)
          ·
            refine ⟨5701320800021368427119673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15203522133390315805652461 5701320800021368427119673)
            ·
              refine ⟨4275990600016026320339755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5701320800021368427119673 4275990600016026320339755)
              ·
                refine ⟨6413985900024039480509633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4275990600016026320339755 6413985900024039480509633)
                ·
                  refine ⟨4810489425018029610382225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6413985900024039480509633 4810489425018029610382225)
                  ·
                    refine ⟨3607867068763522207786669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4810489425018029610382225 3607867068763522207786669)
                    ·
                      refine ⟨1352950150786320827920001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3607867068763522207786669 1352950150786320827920001)
                      ·
                        rfl

theorem cell23_2634861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2, 1, 2, 2, 3].length) (baseStart_2634861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2634861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2634861 prefixEnd_2634861 := by exact prefixLift 2634861
  have htrace : WordTrace (prefixWord ++ tailWord_2634861) baseStart_2634861 baseEnd_2634861 := by
    simpa [prefixWord, tailWord_2634861, baseEnd_2634861] using wordTrace_append hprefix tailTrace_2634861
  have hstable : (prefixWord ++ tailWord_2634861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2634861).length < 2 ^ (prefixWord ++ tailWord_2634861).sum := by decide
  have hdescent : baseEnd_2634861 < baseStart_2634861 := by decide
  rcases family_descends (prefixWord ++ tailWord_2634861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2634885 : List Nat := [1, 3, 1, 1, 6, 2, 2, 2, 1, 4]
def baseStart_2634885 : Nat := 118140960795 + 2634885 * 2 ^ 59
def prefixEnd_2634885 : Nat := 4983230072969 + 3 ^ 40 * 2634885 * 2
def baseEnd_2634885 : Nat := 450987491440676244673297

theorem tailTrace_2634885 : CollatzResearch.WordTrace tailWord_2634885 prefixEnd_2634885 450987491440676244673297 := by
  unfold tailWord_2634885
  simp only [CollatzResearch.WordTrace]
  refine ⟨96102151059269122376578109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64068100706179414917718739 96102151059269122376578109)
  ·
    refine ⟨36038306647225920891216791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96102151059269122376578109 36038306647225920891216791)
    ·
      refine ⟨54057459970838881336825187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36038306647225920891216791 54057459970838881336825187)
      ·
        refine ⟨81086189956258322005237781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54057459970838881336825187 81086189956258322005237781)
        ·
          refine ⟨3800915154199608843995521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 81086189956258322005237781 3800915154199608843995521)
          ·
            refine ⟨2850686365649706632996641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3800915154199608843995521 2850686365649706632996641)
            ·
              refine ⟨2138014774237279974747481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2850686365649706632996641 2138014774237279974747481)
              ·
                refine ⟨1603511080677959981060611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2138014774237279974747481 1603511080677959981060611)
                ·
                  refine ⟨2405266621016939971590917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1603511080677959981060611 2405266621016939971590917)
                  ·
                    refine ⟨450987491440676244673297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2405266621016939971590917 450987491440676244673297)
                    ·
                      rfl

theorem cell23_2634885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 2, 2, 1, 4].length) (baseStart_2634885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2634885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2634885 prefixEnd_2634885 := by exact prefixLift 2634885
  have htrace : WordTrace (prefixWord ++ tailWord_2634885) baseStart_2634885 baseEnd_2634885 := by
    simpa [prefixWord, tailWord_2634885, baseEnd_2634885] using wordTrace_append hprefix tailTrace_2634885
  have hstable : (prefixWord ++ tailWord_2634885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2634885).length < 2 ^ (prefixWord ++ tailWord_2634885).sum := by decide
  have hdescent : baseEnd_2634885 < baseStart_2634885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2634885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2634894 : List Nat := [4, 1, 1, 3, 2, 1, 1, 2, 3, 5]
def baseStart_2634894 : Nat := 118140960795 + 2634894 * 2 ^ 59
def prefixEnd_2634894 : Nat := 4983230072969 + 3 ^ 40 * 2634894 * 2
def baseEnd_2634894 : Nat := 450989031882639732935783

theorem tailTrace_2634894 : CollatzResearch.WordTrace tailWord_2634894 prefixEnd_2634894 450989031882639732935783 := by
  unfold tailWord_2634894
  simp only [CollatzResearch.WordTrace]
  refine ⟨12012809914529564614206967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64068319544157677942437157 12012809914529564614206967)
  ·
    refine ⟨18019214871794346921310451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12012809914529564614206967 18019214871794346921310451)
    ·
      refine ⟨27028822307691520381965677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18019214871794346921310451 27028822307691520381965677)
      ·
        refine ⟨10135808365384320143237129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27028822307691520381965677 10135808365384320143237129)
        ·
          refine ⟨7601856274038240107427847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10135808365384320143237129 7601856274038240107427847)
          ·
            refine ⟨11402784411057360161141771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7601856274038240107427847 11402784411057360161141771)
            ·
              refine ⟨17104176616586040241712657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11402784411057360161141771 17104176616586040241712657)
              ·
                refine ⟨12828132462439530181284493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17104176616586040241712657 12828132462439530181284493)
                ·
                  refine ⟨4810549673414823817981685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12828132462439530181284493 4810549673414823817981685)
                  ·
                    refine ⟨450989031882639732935783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4810549673414823817981685 450989031882639732935783)
                    ·
                      rfl

theorem cell23_2634894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 2, 3, 5].length) (baseStart_2634894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2634894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2634894 prefixEnd_2634894 := by exact prefixLift 2634894
  have htrace : WordTrace (prefixWord ++ tailWord_2634894) baseStart_2634894 baseEnd_2634894 := by
    simpa [prefixWord, tailWord_2634894, baseEnd_2634894] using wordTrace_append hprefix tailTrace_2634894
  have hstable : (prefixWord ++ tailWord_2634894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2634894).length < 2 ^ (prefixWord ++ tailWord_2634894).sum := by decide
  have hdescent : baseEnd_2634894 < baseStart_2634894 := by decide
  rcases family_descends (prefixWord ++ tailWord_2634894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2634931 : List Nat := [1, 1, 1, 2, 3, 2, 6, 1, 1, 1, 4]
def baseStart_2634931 : Nat := 118140960795 + 2634931 * 2 ^ 59
def prefixEnd_2634931 : Nat := 4983230072969 + 3 ^ 40 * 2634931 * 2
def baseEnd_2634931 : Nat := 1352986094432135554044679

theorem tailTrace_2634931 : CollatzResearch.WordTrace tailWord_2634931 prefixEnd_2634931 1352986094432135554044679 := by
  unfold tailWord_2634931
  simp only [CollatzResearch.WordTrace]
  refine ⟨96103828817102472232752647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64069219211401648155168431 96103828817102472232752647)
  ·
    refine ⟨144155743225653708349128971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96103828817102472232752647 144155743225653708349128971)
    ·
      refine ⟨216233614838480562523693457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144155743225653708349128971 216233614838480562523693457)
      ·
        refine ⟨162175211128860421892770093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 216233614838480562523693457 162175211128860421892770093)
        ·
          refine ⟨60815704173322658209788785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 162175211128860421892770093 60815704173322658209788785)
          ·
            refine ⟨45611778129991993657341589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60815704173322658209788785 45611778129991993657341589)
            ·
              refine ⟨2138052099843374702687887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 45611778129991993657341589 2138052099843374702687887)
              ·
                refine ⟨3207078149765062054031831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2138052099843374702687887 3207078149765062054031831)
                ·
                  refine ⟨4810617224647593081047747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3207078149765062054031831 4810617224647593081047747)
                  ·
                    refine ⟨7215925836971389621571621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4810617224647593081047747 7215925836971389621571621)
                    ·
                      refine ⟨1352986094432135554044679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7215925836971389621571621 1352986094432135554044679)
                      ·
                        rfl

theorem cell23_2634931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 6, 1, 1, 1, 4].length) (baseStart_2634931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2634931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2634931 prefixEnd_2634931 := by exact prefixLift 2634931
  have htrace : WordTrace (prefixWord ++ tailWord_2634931) baseStart_2634931 baseEnd_2634931 := by
    simpa [prefixWord, tailWord_2634931, baseEnd_2634931] using wordTrace_append hprefix tailTrace_2634931
  have hstable : (prefixWord ++ tailWord_2634931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2634931).length < 2 ^ (prefixWord ++ tailWord_2634931).sum := by decide
  have hdescent : baseEnd_2634931 < baseStart_2634931 := by decide
  rcases family_descends (prefixWord ++ tailWord_2634931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2634937 : List Nat := [1, 2, 1, 4, 1, 4, 10]
def baseStart_2634937 : Nat := 118140960795 + 2634937 * 2 ^ 59
def prefixEnd_2634937 : Nat := 4983230072969 + 3 ^ 40 * 2634937 * 2
def baseEnd_2634937 : Nat := 16703570065630401611971

theorem tailTrace_2634937 : CollatzResearch.WordTrace tailWord_2634937 prefixEnd_2634937 16703570065630401611971 := by
  unfold tailWord_2634937
  simp only [CollatzResearch.WordTrace]
  refine ⟨96104047655080735257471065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64069365103387156838314043 96104047655080735257471065)
  ·
    refine ⟨72078035741310551443103299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96104047655080735257471065 72078035741310551443103299)
    ·
      refine ⟨108117053611965827164654949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72078035741310551443103299 108117053611965827164654949)
      ·
        refine ⟨20271947552243592593372803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 108117053611965827164654949 20271947552243592593372803)
        ·
          refine ⟨30407921328365388890059205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20271947552243592593372803 30407921328365388890059205)
          ·
            refine ⟨5701485249068510416886101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30407921328365388890059205 5701485249068510416886101)
            ·
              refine ⟨16703570065630401611971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5701485249068510416886101 16703570065630401611971)
              ·
                rfl

theorem cell23_2634937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 10].length) (baseStart_2634937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2634937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2634937 prefixEnd_2634937 := by exact prefixLift 2634937
  have htrace : WordTrace (prefixWord ++ tailWord_2634937) baseStart_2634937 baseEnd_2634937 := by
    simpa [prefixWord, tailWord_2634937, baseEnd_2634937] using wordTrace_append hprefix tailTrace_2634937
  have hstable : (prefixWord ++ tailWord_2634937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2634937).length < 2 ^ (prefixWord ++ tailWord_2634937).sum := by decide
  have hdescent : baseEnd_2634937 < baseStart_2634937 := by decide
  rcases family_descends (prefixWord ++ tailWord_2634937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2634941 : List Nat := [1, 4, 1, 2, 1, 1, 5, 2, 2, 4]
def baseStart_2634941 : Nat := 118140960795 + 2634941 * 2 ^ 59
def prefixEnd_2634941 : Nat := 4983230072969 + 3 ^ 40 * 2634941 * 2
def baseEnd_2634941 : Nat := 450997076412893504973211

theorem tailTrace_2634941 : CollatzResearch.WordTrace tailWord_2634941 prefixEnd_2634941 450997076412893504973211 := by
  unfold tailWord_2634941
  simp only [CollatzResearch.WordTrace]
  refine ⟨96104193547066243940616677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64069462364710829293744451 96104193547066243940616677)
  ·
    refine ⟨18019536290074920738865627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96104193547066243940616677 18019536290074920738865627)
    ·
      refine ⟨27029304435112381108298441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18019536290074920738865627 27029304435112381108298441)
      ·
        refine ⟨20271978326334285831223831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27029304435112381108298441 20271978326334285831223831)
        ·
          refine ⟨30407967489501428746835747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20271978326334285831223831 30407967489501428746835747)
          ·
            refine ⟨45611951234252143120253621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30407967489501428746835747 45611951234252143120253621)
            ·
              refine ⟨4276120428211138417523777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45611951234252143120253621 4276120428211138417523777)
              ·
                refine ⟨3207090321158353813142833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4276120428211138417523777 3207090321158353813142833)
                ·
                  refine ⟨2405317740868765359857125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3207090321158353813142833 2405317740868765359857125)
                  ·
                    refine ⟨450997076412893504973211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2405317740868765359857125 450997076412893504973211)
                    ·
                      rfl

theorem cell23_2634941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5, 2, 2, 4].length) (baseStart_2634941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2634941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2634941 prefixEnd_2634941 := by exact prefixLift 2634941
  have htrace : WordTrace (prefixWord ++ tailWord_2634941) baseStart_2634941 baseEnd_2634941 := by
    simpa [prefixWord, tailWord_2634941, baseEnd_2634941] using wordTrace_append hprefix tailTrace_2634941
  have hstable : (prefixWord ++ tailWord_2634941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2634941).length < 2 ^ (prefixWord ++ tailWord_2634941).sum := by decide
  have hdescent : baseEnd_2634941 < baseStart_2634941 := by decide
  rcases family_descends (prefixWord ++ tailWord_2634941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2634958 : List Nat := [4, 1, 1, 1, 6, 1, 1, 1, 1, 6]
def baseStart_2634958 : Nat := 118140960795 + 2634958 * 2 ^ 59
def prefixEnd_2634958 : Nat := 4983230072969 + 3 ^ 40 * 2634958 * 2
def baseEnd_2634958 : Nat := 450999986136602316135685

theorem tailTrace_2634958 : CollatzResearch.WordTrace tailWord_2634958 prefixEnd_2634958 450999986136602316135685 := by
  unfold tailWord_2634958
  simp only [CollatzResearch.WordTrace]
  refine ⟨12013101698500581980498191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64069875725336437229323685 12013101698500581980498191)
  ·
    refine ⟨18019652547750872970747287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12013101698500581980498191 18019652547750872970747287)
    ·
      refine ⟨27029478821626309456120931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18019652547750872970747287 27029478821626309456120931)
      ·
        refine ⟨40544218232439464184181397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27029478821626309456120931 40544218232439464184181397)
        ·
          refine ⟨1900510229645599883633503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 40544218232439464184181397 1900510229645599883633503)
          ·
            refine ⟨2850765344468399825450255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1900510229645599883633503 2850765344468399825450255)
            ·
              refine ⟨4276148016702599738175383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2850765344468399825450255 4276148016702599738175383)
              ·
                refine ⟨6414222025053899607263075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4276148016702599738175383 6414222025053899607263075)
                ·
                  refine ⟨9621333037580849410894613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6414222025053899607263075 9621333037580849410894613)
                  ·
                    refine ⟨450999986136602316135685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9621333037580849410894613 450999986136602316135685)
                    ·
                      rfl

theorem cell23_2634958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 1, 1, 1, 6].length) (baseStart_2634958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2634958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2634958 prefixEnd_2634958 := by exact prefixLift 2634958
  have htrace : WordTrace (prefixWord ++ tailWord_2634958) baseStart_2634958 baseEnd_2634958 := by
    simpa [prefixWord, tailWord_2634958, baseEnd_2634958] using wordTrace_append hprefix tailTrace_2634958
  have hstable : (prefixWord ++ tailWord_2634958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2634958).length < 2 ^ (prefixWord ++ tailWord_2634958).sum := by decide
  have hdescent : baseEnd_2634958 < baseStart_2634958 := by decide
  rcases family_descends (prefixWord ++ tailWord_2634958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2634967 : List Nat := [1, 1, 3, 2, 1, 2, 2, 2, 2, 7]
def baseStart_2634967 : Nat := 118140960795 + 2634967 * 2 ^ 59
def prefixEnd_2634967 : Nat := 4983230072969 + 3 ^ 40 * 2634967 * 2
def baseEnd_2634967 : Nat := 451001526578565804398171

theorem tailTrace_2634967 : CollatzResearch.WordTrace tailWord_2634967 prefixEnd_2634967 451001526578565804398171 := by
  unfold tailWord_2634967
  simp only [CollatzResearch.WordTrace]
  refine ⟨96105141844972050381063155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64070094563314700254042103 96105141844972050381063155)
  ·
    refine ⟨144157712767458075571594733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96105141844972050381063155 144157712767458075571594733)
    ·
      refine ⟨54059142287796778339348025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144157712767458075571594733 54059142287796778339348025)
      ·
        refine ⟨40544356715847583754511019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54059142287796778339348025 40544356715847583754511019)
        ·
          refine ⟨60816535073771375631766529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40544356715847583754511019 60816535073771375631766529)
          ·
            refine ⟨45612401305328531723824897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60816535073771375631766529 45612401305328531723824897)
            ·
              refine ⟨34209300978996398792868673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45612401305328531723824897 34209300978996398792868673)
              ·
                refine ⟨25656975734247299094651505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34209300978996398792868673 25656975734247299094651505)
                ·
                  refine ⟨19242731800685474320988629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25656975734247299094651505 19242731800685474320988629)
                  ·
                    refine ⟨451001526578565804398171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19242731800685474320988629 451001526578565804398171)
                    ·
                      rfl

theorem cell23_2634967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 2, 2, 7].length) (baseStart_2634967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2634967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2634967 prefixEnd_2634967 := by exact prefixLift 2634967
  have htrace : WordTrace (prefixWord ++ tailWord_2634967) baseStart_2634967 baseEnd_2634967 := by
    simpa [prefixWord, tailWord_2634967, baseEnd_2634967] using wordTrace_append hprefix tailTrace_2634967
  have hstable : (prefixWord ++ tailWord_2634967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2634967).length < 2 ^ (prefixWord ++ tailWord_2634967).sum := by decide
  have hdescent : baseEnd_2634967 < baseStart_2634967 := by decide
  rcases family_descends (prefixWord ++ tailWord_2634967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2634968 : List Nat := [2, 1, 2, 2, 5, 1, 2, 2, 1, 2, 3]
def baseStart_2634968 : Nat := 118140960795 + 2634968 * 2 ^ 59
def prefixEnd_2634968 : Nat := 4983230072969 + 3 ^ 40 * 2634968 * 2
def baseEnd_2634968 : Nat := 1353005093216351909282009

theorem tailTrace_2634968 : CollatzResearch.WordTrace tailWord_2634968 prefixEnd_2634968 1353005093216351909282009 := by
  unfold tailWord_2634968
  simp only [CollatzResearch.WordTrace]
  refine ⟨48052589158984213775924779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64070118878645618367899705 48052589158984213775924779)
  ·
    refine ⟨72078883738476320663887169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48052589158984213775924779 72078883738476320663887169)
    ·
      refine ⟨54059162803857240497915377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72078883738476320663887169 54059162803857240497915377)
      ·
        refine ⟨40544372102892930373436533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54059162803857240497915377 40544372102892930373436533)
        ·
          refine ⟨3801034884646212222509675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 40544372102892930373436533 3801034884646212222509675)
          ·
            refine ⟨5701552326969318333764513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3801034884646212222509675 5701552326969318333764513)
            ·
              refine ⟨4276164245226988750323385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5701552326969318333764513 4276164245226988750323385)
              ·
                refine ⟨3207123183920241562742539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4276164245226988750323385 3207123183920241562742539)
                ·
                  refine ⟨4810684775880362344113809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3207123183920241562742539 4810684775880362344113809)
                  ·
                    refine ⟨3608013581910271758085357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4810684775880362344113809 3608013581910271758085357)
                    ·
                      refine ⟨1353005093216351909282009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3608013581910271758085357 1353005093216351909282009)
                      ·
                        rfl

theorem cell23_2634968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 2, 2, 1, 2, 3].length) (baseStart_2634968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2634968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2634968 prefixEnd_2634968 := by exact prefixLift 2634968
  have htrace : WordTrace (prefixWord ++ tailWord_2634968) baseStart_2634968 baseEnd_2634968 := by
    simpa [prefixWord, tailWord_2634968, baseEnd_2634968] using wordTrace_append hprefix tailTrace_2634968
  have hstable : (prefixWord ++ tailWord_2634968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2634968).length < 2 ^ (prefixWord ++ tailWord_2634968).sum := by decide
  have hdescent : baseEnd_2634968 < baseStart_2634968 := by decide
  rcases family_descends (prefixWord ++ tailWord_2634968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2634998 : List Nat := [5, 1, 1, 1, 1, 1, 1, 6, 2, 1, 3]
def baseStart_2634998 : Nat := 118140960795 + 2634998 * 2 ^ 59
def prefixEnd_2634998 : Nat := 4983230072969 + 3 ^ 40 * 2634998 * 2
def baseEnd_2634998 : Nat := 1353020497635986791906871

theorem tailTrace_2634998 : CollatzResearch.WordTrace tailWord_2634998 prefixEnd_2634998 1353020497635986791906871 := by
  unfold tailWord_2634998
  simp only [CollatzResearch.WordTrace]
  refine ⟨6006642031741233917215103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 64070848338573161783627765 6006642031741233917215103)
  ·
    refine ⟨9009963047611850875822655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6006642031741233917215103 9009963047611850875822655)
    ·
      refine ⟨13514944571417776313733983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9009963047611850875822655 13514944571417776313733983)
      ·
        refine ⟨20272416857126664470600975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13514944571417776313733983 20272416857126664470600975)
        ·
          refine ⟨30408625285689996705901463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20272416857126664470600975 30408625285689996705901463)
          ·
            refine ⟨45612937928534995058852195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30408625285689996705901463 45612937928534995058852195)
            ·
              refine ⟨68419406892802492588278293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45612937928534995058852195 68419406892802492588278293)
              ·
                refine ⟨3207159698100116840075545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 68419406892802492588278293 3207159698100116840075545)
                ·
                  refine ⟨2405369773575087630056659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3207159698100116840075545 2405369773575087630056659)
                  ·
                    refine ⟨3608054660362631445084989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2405369773575087630056659 3608054660362631445084989)
                    ·
                      refine ⟨1353020497635986791906871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3608054660362631445084989 1353020497635986791906871)
                      ·
                        rfl

theorem cell23_2634998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 6, 2, 1, 3].length) (baseStart_2634998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2634998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2634998 prefixEnd_2634998 := by exact prefixLift 2634998
  have htrace : WordTrace (prefixWord ++ tailWord_2634998) baseStart_2634998 baseEnd_2634998 := by
    simpa [prefixWord, tailWord_2634998, baseEnd_2634998] using wordTrace_append hprefix tailTrace_2634998
  have hstable : (prefixWord ++ tailWord_2634998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2634998).length < 2 ^ (prefixWord ++ tailWord_2634998).sum := by decide
  have hdescent : baseEnd_2634998 < baseStart_2634998 := by decide
  rcases family_descends (prefixWord ++ tailWord_2634998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2635042 : List Nat := [3, 3, 1, 1, 4, 1, 3, 1, 1, 3, 2]
def baseStart_2635042 : Nat := 118140960795 + 2635042 * 2 ^ 59
def prefixEnd_2635042 : Nat := 4983230072969 + 3 ^ 40 * 2635042 * 2
def baseEnd_2635042 : Nat := 1353043090784784619756669

theorem tailTrace_2635042 : CollatzResearch.WordTrace tailWord_2635042 prefixEnd_2635042 1353043090784784619756669 := by
  unfold tailWord_2635042
  simp only [CollatzResearch.WordTrace]
  refine ⟨24026969329925084547510845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64071918213133558793362253 24026969329925084547510845)
  ·
    refine ⟨9010113498721906705316567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24026969329925084547510845 9010113498721906705316567)
    ·
      refine ⟨13515170248082860057974851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9010113498721906705316567 13515170248082860057974851)
      ·
        refine ⟨20272755372124290086962277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13515170248082860057974851 20272755372124290086962277)
        ·
          refine ⟨3801141632273304391305427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20272755372124290086962277 3801141632273304391305427)
          ·
            refine ⟨5701712448409956586958141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3801141632273304391305427 5701712448409956586958141)
            ·
              refine ⟨2138142168153733720109303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5701712448409956586958141 2138142168153733720109303)
              ·
                refine ⟨3207213252230600580163955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2138142168153733720109303 3207213252230600580163955)
                ·
                  refine ⟨4810819878345900870245933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3207213252230600580163955 4810819878345900870245933)
                  ·
                    refine ⟨1804057454379712826342225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4810819878345900870245933 1804057454379712826342225)
                    ·
                      refine ⟨1353043090784784619756669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1804057454379712826342225 1353043090784784619756669)
                      ·
                        rfl

theorem cell23_2635042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 3, 1, 1, 3, 2].length) (baseStart_2635042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2635042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2635042 prefixEnd_2635042 := by exact prefixLift 2635042
  have htrace : WordTrace (prefixWord ++ tailWord_2635042) baseStart_2635042 baseEnd_2635042 := by
    simpa [prefixWord, tailWord_2635042, baseEnd_2635042] using wordTrace_append hprefix tailTrace_2635042
  have hstable : (prefixWord ++ tailWord_2635042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2635042).length < 2 ^ (prefixWord ++ tailWord_2635042).sum := by decide
  have hdescent : baseEnd_2635042 < baseStart_2635042 := by decide
  rcases family_descends (prefixWord ++ tailWord_2635042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2635071 : List Nat := [1, 1, 2, 2, 4, 3, 1, 1, 2, 3, 3]
def baseStart_2635071 : Nat := 118140960795 + 2635071 * 2 ^ 59
def prefixEnd_2635071 : Nat := 4983230072969 + 3 ^ 40 * 2635071 * 2
def baseEnd_2635071 : Nat := 1353057981723765006294035

theorem tailTrace_2635071 : CollatzResearch.WordTrace tailWord_2635071 prefixEnd_2635071 1353057981723765006294035 := by
  unfold tailWord_2635071
  simp only [CollatzResearch.WordTrace]
  refine ⟨96108935036595276142849067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64072623357730184095232711 96108935036595276142849067)
  ·
    refine ⟨144163402554892914214273601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96108935036595276142849067 144163402554892914214273601)
    ·
      refine ⟨108122551916169685660705201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144163402554892914214273601 108122551916169685660705201)
      ·
        refine ⟨81091913937127264245528901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108122551916169685660705201 81091913937127264245528901)
        ·
          refine ⟨15204733863211362046036669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81091913937127264245528901 15204733863211362046036669)
          ·
            refine ⟨5701775198704260767263751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15204733863211362046036669 5701775198704260767263751)
            ·
              refine ⟨8552662798056391150895627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5701775198704260767263751 8552662798056391150895627)
              ·
                refine ⟨12828994197084586726343441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8552662798056391150895627 12828994197084586726343441)
                ·
                  refine ⟨9621745647813440044757581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12828994197084586726343441 9621745647813440044757581)
                  ·
                    refine ⟨3608154617930040016784093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9621745647813440044757581 3608154617930040016784093)
                    ·
                      refine ⟨1353057981723765006294035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3608154617930040016784093 1353057981723765006294035)
                      ·
                        rfl

theorem cell23_2635071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 1, 2, 3, 3].length) (baseStart_2635071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2635071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2635071 prefixEnd_2635071 := by exact prefixLift 2635071
  have htrace : WordTrace (prefixWord ++ tailWord_2635071) baseStart_2635071 baseEnd_2635071 := by
    simpa [prefixWord, tailWord_2635071, baseEnd_2635071] using wordTrace_append hprefix tailTrace_2635071
  have hstable : (prefixWord ++ tailWord_2635071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2635071).length < 2 ^ (prefixWord ++ tailWord_2635071).sum := by decide
  have hdescent : baseEnd_2635071 < baseStart_2635071 := by decide
  rcases family_descends (prefixWord ++ tailWord_2635071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2635121 : List Nat := [1, 2, 2, 2, 1, 2, 3, 3, 3, 4]
def baseStart_2635121 : Nat := 118140960795 + 2635121 * 2 ^ 59
def prefixEnd_2635121 : Nat := 4983230072969 + 3 ^ 40 * 2635121 * 2
def baseEnd_2635121 : Nat := 451027885252163270222935

theorem tailTrace_2635121 : CollatzResearch.WordTrace tailWord_2635121 prefixEnd_2635121 451027885252163270222935 := by
  unfold tailWord_2635121
  simp only [CollatzResearch.WordTrace]
  refine ⟨96110758686414134682169217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64073839124276089788112811 96110758686414134682169217)
  ·
    refine ⟨72083069014810601011626913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96110758686414134682169217 72083069014810601011626913)
    ·
      refine ⟨54062301761107950758720185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72083069014810601011626913 54062301761107950758720185)
      ·
        refine ⟨40546726320830963069040139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54062301761107950758720185 40546726320830963069040139)
        ·
          refine ⟨60820089481246444603560209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40546726320830963069040139 60820089481246444603560209)
          ·
            refine ⟨45615067110934833452670157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60820089481246444603560209 45615067110934833452670157)
            ·
              refine ⟨17105650166600562544751309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45615067110934833452670157 17105650166600562544751309)
              ·
                refine ⟨6414618812475210954281741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17105650166600562544751309 6414618812475210954281741)
                ·
                  refine ⟨2405482054678204107855653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6414618812475210954281741 2405482054678204107855653)
                  ·
                    refine ⟨451027885252163270222935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2405482054678204107855653 451027885252163270222935)
                    ·
                      rfl

theorem cell23_2635121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 3, 3, 4].length) (baseStart_2635121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2635121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2635121 prefixEnd_2635121 := by exact prefixLift 2635121
  have htrace : WordTrace (prefixWord ++ tailWord_2635121) baseStart_2635121 baseEnd_2635121 := by
    simpa [prefixWord, tailWord_2635121, baseEnd_2635121] using wordTrace_append hprefix tailTrace_2635121
  have hstable : (prefixWord ++ tailWord_2635121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2635121).length < 2 ^ (prefixWord ++ tailWord_2635121).sum := by decide
  have hdescent : baseEnd_2635121 < baseStart_2635121 := by decide
  rcases family_descends (prefixWord ++ tailWord_2635121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2635211 : List Nat := [1, 1, 1, 1, 3, 3, 2, 1, 6, 4]
def baseStart_2635211 : Nat := 118140960795 + 2635211 * 2 ^ 59
def prefixEnd_2635211 : Nat := 4983230072969 + 3 ^ 40 * 2635211 * 2
def baseEnd_2635211 : Nat := 451043289671798152847797

theorem tailTrace_2635211 : CollatzResearch.WordTrace tailWord_2635211 prefixEnd_2635211 451043289671798152847797 := by
  unfold tailWord_2635211
  simp only [CollatzResearch.WordTrace]
  refine ⟨96114041256088080052945487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64076027504058720035296991 96114041256088080052945487)
  ·
    refine ⟨144171061884132120079418231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96114041256088080052945487 144171061884132120079418231)
    ·
      refine ⟨216256592826198180119127347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144171061884132120079418231 216256592826198180119127347)
      ·
        refine ⟨324384889239297270178691021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216256592826198180119127347 324384889239297270178691021)
        ·
          refine ⟨121644333464736476317009133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 324384889239297270178691021 121644333464736476317009133)
          ·
            refine ⟨45616625049276178618878425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 121644333464736476317009133 45616625049276178618878425)
            ·
              refine ⟨34212468786957133964158819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45616625049276178618878425 34212468786957133964158819)
              ·
                refine ⟨51318703180435700946238229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34212468786957133964158819 51318703180435700946238229)
                ·
                  refine ⟨2405564211582923481854917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 51318703180435700946238229 2405564211582923481854917)
                  ·
                    refine ⟨451043289671798152847797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2405564211582923481854917 451043289671798152847797)
                    ·
                      rfl

theorem cell23_2635211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 6, 4].length) (baseStart_2635211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2635211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2635211 prefixEnd_2635211 := by exact prefixLift 2635211
  have htrace : WordTrace (prefixWord ++ tailWord_2635211) baseStart_2635211 baseEnd_2635211 := by
    simpa [prefixWord, tailWord_2635211, baseEnd_2635211] using wordTrace_append hprefix tailTrace_2635211
  have hstable : (prefixWord ++ tailWord_2635211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2635211).length < 2 ^ (prefixWord ++ tailWord_2635211).sum := by decide
  have hdescent : baseEnd_2635211 < baseStart_2635211 := by decide
  rcases family_descends (prefixWord ++ tailWord_2635211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2635222 : List Nat := [5, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2]
def baseStart_2635222 : Nat := 118140960795 + 2635222 * 2 ^ 59
def prefixEnd_2635222 : Nat := 4983230072969 + 3 ^ 40 * 2635222 * 2
def baseEnd_2635222 : Nat := 1353135517302593915505841

theorem tailTrace_2635222 : CollatzResearch.WordTrace tailWord_2635222 prefixEnd_2635222 1353135517302593915505841 := by
  unfold tailWord_2635222
  simp only [CollatzResearch.WordTrace]
  refine ⟨6007152653690514308224745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 64076294972698819287730613 6007152653690514308224745)
  ·
    refine ⟨4505364490267885731168559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6007152653690514308224745 4505364490267885731168559)
    ·
      refine ⟨6758046735401828596752839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4505364490267885731168559 6758046735401828596752839)
      ·
        refine ⟨10137070103102742895129259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6758046735401828596752839 10137070103102742895129259)
        ·
          refine ⟨15205605154654114342693889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10137070103102742895129259 15205605154654114342693889)
          ·
            refine ⟨11404203865990585757020417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15205605154654114342693889 11404203865990585757020417)
            ·
              refine ⟨8553152899492939317765313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11404203865990585757020417 8553152899492939317765313)
              ·
                refine ⟨6414864674619704488323985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8553152899492939317765313 6414864674619704488323985)
                ·
                  refine ⟨4811148505964778366242989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6414864674619704488323985 4811148505964778366242989)
                  ·
                    refine ⟨1804180689736791887341121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4811148505964778366242989 1804180689736791887341121)
                    ·
                      refine ⟨1353135517302593915505841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1804180689736791887341121 1353135517302593915505841)
                      ·
                        rfl

theorem cell23_2635222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2].length) (baseStart_2635222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2635222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2635222 prefixEnd_2635222 := by exact prefixLift 2635222
  have htrace : WordTrace (prefixWord ++ tailWord_2635222) baseStart_2635222 baseEnd_2635222 := by
    simpa [prefixWord, tailWord_2635222, baseEnd_2635222] using wordTrace_append hprefix tailTrace_2635222
  have hstable : (prefixWord ++ tailWord_2635222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2635222).length < 2 ^ (prefixWord ++ tailWord_2635222).sum := by decide
  have hdescent : baseEnd_2635222 < baseStart_2635222 := by decide
  rcases family_descends (prefixWord ++ tailWord_2635222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2635229 : List Nat := [1, 4, 3, 1, 1, 2, 4, 2, 1, 1, 3]
def baseStart_2635229 : Nat := 118140960795 + 2635229 * 2 ^ 59
def prefixEnd_2635229 : Nat := 4983230072969 + 3 ^ 40 * 2635229 * 2
def baseEnd_2635229 : Nat := 1353139111667175388118309

theorem tailTrace_2635229 : CollatzResearch.WordTrace tailWord_2635229 prefixEnd_2635229 1353139111667175388118309 := by
  unfold tailWord_2635229
  simp only [CollatzResearch.WordTrace]
  refine ⟨96114697770022869127100741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64076465180015246084733827 96114697770022869127100741)
  ·
    refine ⟨18021505831879287961331389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96114697770022869127100741 18021505831879287961331389)
    ·
      refine ⟨6758064686954732985499271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18021505831879287961331389 6758064686954732985499271)
      ·
        refine ⟨10137097030432099478248907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6758064686954732985499271 10137097030432099478248907)
        ·
          refine ⟨15205645545648149217373361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10137097030432099478248907 15205645545648149217373361)
          ·
            refine ⟨11404234159236111913030021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15205645545648149217373361 11404234159236111913030021)
            ·
              refine ⟨2138293904856770983693129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11404234159236111913030021 2138293904856770983693129)
              ·
                refine ⟨1603720428642578237769847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2138293904856770983693129 1603720428642578237769847)
                ·
                  refine ⟨2405580642963867356654771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1603720428642578237769847 2405580642963867356654771)
                  ·
                    refine ⟨3608370964445801034982157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2405580642963867356654771 3608370964445801034982157)
                    ·
                      refine ⟨1353139111667175388118309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3608370964445801034982157 1353139111667175388118309)
                      ·
                        rfl

theorem cell23_2635229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 4, 2, 1, 1, 3].length) (baseStart_2635229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2635229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2635229 prefixEnd_2635229 := by exact prefixLift 2635229
  have htrace : WordTrace (prefixWord ++ tailWord_2635229) baseStart_2635229 baseEnd_2635229 := by
    simpa [prefixWord, tailWord_2635229, baseEnd_2635229] using wordTrace_append hprefix tailTrace_2635229
  have hstable : (prefixWord ++ tailWord_2635229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2635229).length < 2 ^ (prefixWord ++ tailWord_2635229).sum := by decide
  have hdescent : baseEnd_2635229 < baseStart_2635229 := by decide
  rcases family_descends (prefixWord ++ tailWord_2635229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2635231 : List Nat := [1, 1, 2, 3, 3, 1, 1, 2, 3, 2, 4]
def baseStart_2635231 : Nat := 118140960795 + 2635231 * 2 ^ 59
def prefixEnd_2635231 : Nat := 4983230072969 + 3 ^ 40 * 2635231 * 2
def baseEnd_2635231 : Nat := 1353140138628484380293299

theorem tailTrace_2635231 : CollatzResearch.WordTrace tailWord_2635231 prefixEnd_2635231 1353140138628484380293299 := by
  unfold tailWord_2635231
  simp only [CollatzResearch.WordTrace]
  refine ⟨96114770716015623468673547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64076513810677082312449031 96114770716015623468673547)
  ·
    refine ⟨144172156074023435203010321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96114770716015623468673547 144172156074023435203010321)
    ·
      refine ⟨108129117055517576402257741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144172156074023435203010321 108129117055517576402257741)
      ·
        refine ⟨40548418895819091150846653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108129117055517576402257741 40548418895819091150846653)
        ·
          refine ⟨15205657085932159181567495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40548418895819091150846653 15205657085932159181567495)
          ·
            refine ⟨22808485628898238772351243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15205657085932159181567495 22808485628898238772351243)
            ·
              refine ⟨34212728443347358158526865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22808485628898238772351243 34212728443347358158526865)
              ·
                refine ⟨25659546332510518618895149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34212728443347358158526865 25659546332510518618895149)
                ·
                  refine ⟨9622329874691444482085681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25659546332510518618895149 9622329874691444482085681)
                  ·
                    refine ⟨7216747406018583361564261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9622329874691444482085681 7216747406018583361564261)
                    ·
                      refine ⟨1353140138628484380293299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7216747406018583361564261 1353140138628484380293299)
                      ·
                        rfl

theorem cell23_2635231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 2, 3, 2, 4].length) (baseStart_2635231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2635231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2635231 prefixEnd_2635231 := by exact prefixLift 2635231
  have htrace : WordTrace (prefixWord ++ tailWord_2635231) baseStart_2635231 baseEnd_2635231 := by
    simpa [prefixWord, tailWord_2635231, baseEnd_2635231] using wordTrace_append hprefix tailTrace_2635231
  have hstable : (prefixWord ++ tailWord_2635231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2635231).length < 2 ^ (prefixWord ++ tailWord_2635231).sum := by decide
  have hdescent : baseEnd_2635231 < baseStart_2635231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2635231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2635245 : List Nat := [1, 5, 1, 3, 2, 1, 2, 1, 1, 6]
def baseStart_2635245 : Nat := 118140960795 + 2635245 * 2 ^ 59
def prefixEnd_2635245 : Nat := 4983230072969 + 3 ^ 40 * 2635245 * 2
def baseEnd_2635245 : Nat := 451049109119215775172745

theorem tailTrace_2635245 : CollatzResearch.WordTrace tailWord_2635245 prefixEnd_2635245 451049109119215775172745 := by
  unfold tailWord_2635245
  simp only [CollatzResearch.WordTrace]
  refine ⟨96115281337964903859683189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64076854225309935906455459 96115281337964903859683189)
  ·
    refine ⟨9010807625434209736845299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 96115281337964903859683189 9010807625434209736845299)
    ·
      refine ⟨13516211438151314605267949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9010807625434209736845299 13516211438151314605267949)
      ·
        refine ⟨5068579289306742976975481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13516211438151314605267949 5068579289306742976975481)
        ·
          refine ⟨3801434466980057232731611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5068579289306742976975481 3801434466980057232731611)
          ·
            refine ⟨5702151700470085849097417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3801434466980057232731611 5702151700470085849097417)
            ·
              refine ⟨4276613775352564386823063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5702151700470085849097417 4276613775352564386823063)
              ·
                refine ⟨6414920663028846580234595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4276613775352564386823063 6414920663028846580234595)
                ·
                  refine ⟨9622380994543269870351893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6414920663028846580234595 9622380994543269870351893)
                  ·
                    refine ⟨451049109119215775172745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9622380994543269870351893 451049109119215775172745)
                    ·
                      rfl

theorem cell23_2635245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 2, 1, 1, 6].length) (baseStart_2635245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2635245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2635245 prefixEnd_2635245 := by exact prefixLift 2635245
  have htrace : WordTrace (prefixWord ++ tailWord_2635245) baseStart_2635245 baseEnd_2635245 := by
    simpa [prefixWord, tailWord_2635245, baseEnd_2635245] using wordTrace_append hprefix tailTrace_2635245
  have hstable : (prefixWord ++ tailWord_2635245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2635245).length < 2 ^ (prefixWord ++ tailWord_2635245).sum := by decide
  have hdescent : baseEnd_2635245 < baseStart_2635245 := by decide
  rcases family_descends (prefixWord ++ tailWord_2635245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2635248 : List Nat := [2, 1, 1, 1, 3, 5, 2, 1, 1, 2, 4]
def baseStart_2635248 : Nat := 118140960795 + 2635248 * 2 ^ 59
def prefixEnd_2635248 : Nat := 4983230072969 + 3 ^ 40 * 2635248 * 2
def baseEnd_2635248 : Nat := 1353148867799610813780721

theorem tailTrace_2635248 : CollatzResearch.WordTrace tailWord_2635248 prefixEnd_2635248 1353148867799610813780721 := by
  unfold tailWord_2635248
  simp only [CollatzResearch.WordTrace]
  refine ⟨48057695378477017686021199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64076927171302690248028265 48057695378477017686021199)
  ·
    refine ⟨72086543067715526529031799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48057695378477017686021199 72086543067715526529031799)
    ·
      refine ⟨108129814601573289793547699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72086543067715526529031799 108129814601573289793547699)
      ·
        refine ⟨162194721902359934690321549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108129814601573289793547699 162194721902359934690321549)
        ·
          refine ⟨60823020713384975508870581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 162194721902359934690321549 60823020713384975508870581)
          ·
            refine ⟨5702158191879841453956617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 60823020713384975508870581 5702158191879841453956617)
            ·
              refine ⟨4276618643909881090467463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5702158191879841453956617 4276618643909881090467463)
              ·
                refine ⟨6414927965864821635701195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4276618643909881090467463 6414927965864821635701195)
                ·
                  refine ⟨9622391948797232453551793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6414927965864821635701195 9622391948797232453551793)
                  ·
                    refine ⟨7216793961597924340163845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9622391948797232453551793 7216793961597924340163845)
                    ·
                      refine ⟨1353148867799610813780721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7216793961597924340163845 1353148867799610813780721)
                      ·
                        rfl

theorem cell23_2635248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2, 1, 1, 2, 4].length) (baseStart_2635248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2635248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2635248 prefixEnd_2635248 := by exact prefixLift 2635248
  have htrace : WordTrace (prefixWord ++ tailWord_2635248) baseStart_2635248 baseEnd_2635248 := by
    simpa [prefixWord, tailWord_2635248, baseEnd_2635248] using wordTrace_append hprefix tailTrace_2635248
  have hstable : (prefixWord ++ tailWord_2635248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2635248).length < 2 ^ (prefixWord ++ tailWord_2635248).sum := by decide
  have hdescent : baseEnd_2635248 < baseStart_2635248 := by decide
  rcases family_descends (prefixWord ++ tailWord_2635248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2635285 : List Nat := [1, 3, 2, 1, 3, 3, 1, 1, 4, 1, 3]
def baseStart_2635285 : Nat := 118140960795 + 2635285 * 2 ^ 59
def prefixEnd_2635285 : Nat := 4983230072969 + 3 ^ 40 * 2635285 * 2
def baseEnd_2635285 : Nat := 1353167866583827169018051

theorem tailTrace_2635285 : CollatzResearch.WordTrace tailWord_2635285 prefixEnd_2635285 1353167866583827169018051 := by
  unfold tailWord_2635285
  simp only [CollatzResearch.WordTrace]
  refine ⟨96116740257819990691139309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64077826838546660460759539 96116740257819990691139309)
  ·
    refine ⟨36043777596682496509177241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96116740257819990691139309 36043777596682496509177241)
    ·
      refine ⟨27032833197511872381882931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36043777596682496509177241 27032833197511872381882931)
      ·
        refine ⟨40549249796267808572824397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27032833197511872381882931 40549249796267808572824397)
        ·
          refine ⟨15205968673600428214809149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40549249796267808572824397 15205968673600428214809149)
          ·
            refine ⟨5702238252600160580553431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15205968673600428214809149 5702238252600160580553431)
            ·
              refine ⟨8553357378900240870830147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5702238252600160580553431 8553357378900240870830147)
              ·
                refine ⟨12830036068350361306245221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8553357378900240870830147 12830036068350361306245221)
                ·
                  refine ⟨2405631762815692744920979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12830036068350361306245221 2405631762815692744920979)
                  ·
                    refine ⟨3608447644223539117381469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2405631762815692744920979 3608447644223539117381469)
                    ·
                      refine ⟨1353167866583827169018051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3608447644223539117381469 1353167866583827169018051)
                      ·
                        rfl

theorem cell23_2635285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 1, 4, 1, 3].length) (baseStart_2635285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2635285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2635285 prefixEnd_2635285 := by exact prefixLift 2635285
  have htrace : WordTrace (prefixWord ++ tailWord_2635285) baseStart_2635285 baseEnd_2635285 := by
    simpa [prefixWord, tailWord_2635285, baseEnd_2635285] using wordTrace_append hprefix tailTrace_2635285
  have hstable : (prefixWord ++ tailWord_2635285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2635285).length < 2 ^ (prefixWord ++ tailWord_2635285).sum := by decide
  have hdescent : baseEnd_2635285 < baseStart_2635285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2635285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2635342 : List Nat := [4, 1, 1, 1, 1, 2, 1, 6, 2, 2, 2]
def baseStart_2635342 : Nat := 118140960795 + 2635342 * 2 ^ 59
def prefixEnd_2635342 : Nat := 4983230072969 + 3 ^ 40 * 2635342 * 2
def baseEnd_2635342 : Nat := 1353197134981133446005289

theorem tailTrace_2635342 : CollatzResearch.WordTrace tailWord_2635342 prefixEnd_2635342 1353197134981133446005289 := by
  unfold tailWord_2635342
  simp only [CollatzResearch.WordTrace]
  refine ⟨12014852402326686178245535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64079212812408992950642853 12014852402326686178245535)
  ·
    refine ⟨18022278603490029267368303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12014852402326686178245535 18022278603490029267368303)
    ·
      refine ⟨27033417905235043901052455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18022278603490029267368303 27033417905235043901052455)
      ·
        refine ⟨40550126857852565851578683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27033417905235043901052455 40550126857852565851578683)
        ·
          refine ⟨60825190286778848777368025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40550126857852565851578683 60825190286778848777368025)
          ·
            refine ⟨45618892715084136583026019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60825190286778848777368025 45618892715084136583026019)
            ·
              refine ⟨68428339072626204874539029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45618892715084136583026019 68428339072626204874539029)
              ·
                refine ⟨3207578394029353353494017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 68428339072626204874539029 3207578394029353353494017)
                ·
                  refine ⟨2405683795522015015120513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3207578394029353353494017 2405683795522015015120513)
                  ·
                    refine ⟨1804262846641511261340385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2405683795522015015120513 1804262846641511261340385)
                    ·
                      refine ⟨1353197134981133446005289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1804262846641511261340385 1353197134981133446005289)
                      ·
                        rfl

theorem cell23_2635342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 6, 2, 2, 2].length) (baseStart_2635342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2635342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2635342 prefixEnd_2635342 := by exact prefixLift 2635342
  have htrace : WordTrace (prefixWord ++ tailWord_2635342) baseStart_2635342 baseEnd_2635342 := by
    simpa [prefixWord, tailWord_2635342, baseEnd_2635342] using wordTrace_append hprefix tailTrace_2635342
  have hstable : (prefixWord ++ tailWord_2635342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2635342).length < 2 ^ (prefixWord ++ tailWord_2635342).sum := by decide
  have hdescent : baseEnd_2635342 < baseStart_2635342 := by decide
  rcases family_descends (prefixWord ++ tailWord_2635342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2635391 : List Nat := [1, 1, 2, 2, 1, 1, 1, 2, 4, 8]
def baseStart_2635391 : Nat := 118140960795 + 2635391 * 2 ^ 59
def prefixEnd_2635391 : Nat := 4983230072969 + 3 ^ 40 * 2635391 * 2
def baseEnd_2635391 : Nat := 451074098511067918097521

theorem tailTrace_2635391 : CollatzResearch.WordTrace tailWord_2635391 prefixEnd_2635391 451074098511067918097521 := by
  unfold tailWord_2635391
  simp only [CollatzResearch.WordTrace]
  refine ⟨96120606395435970794498027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64080404263623980529665351 96120606395435970794498027)
  ·
    refine ⟨144180909593153956191747041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96120606395435970794498027 144180909593153956191747041)
    ·
      refine ⟨108135682194865467143810281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144180909593153956191747041 108135682194865467143810281)
      ·
        refine ⟨81101761646149100357857711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108135682194865467143810281 81101761646149100357857711)
        ·
          refine ⟨121652642469223650536786567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81101761646149100357857711 121652642469223650536786567)
          ·
            refine ⟨182478963703835475805179851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121652642469223650536786567 182478963703835475805179851)
            ·
              refine ⟨273718445555753213707769777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 182478963703835475805179851 273718445555753213707769777)
              ·
                refine ⟨205288834166814910280827333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 273718445555753213707769777 205288834166814910280827333)
                ·
                  refine ⟨38491656406277795677655125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 205288834166814910280827333 38491656406277795677655125)
                  ·
                    refine ⟨451074098511067918097521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 38491656406277795677655125 451074098511067918097521)
                    ·
                      rfl

theorem cell23_2635391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 4, 8].length) (baseStart_2635391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2635391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2635391 prefixEnd_2635391 := by exact prefixLift 2635391
  have htrace : WordTrace (prefixWord ++ tailWord_2635391) baseStart_2635391 baseEnd_2635391 := by
    simpa [prefixWord, tailWord_2635391, baseEnd_2635391] using wordTrace_append hprefix tailTrace_2635391
  have hstable : (prefixWord ++ tailWord_2635391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2635391).length < 2 ^ (prefixWord ++ tailWord_2635391).sum := by decide
  have hdescent : baseEnd_2635391 < baseStart_2635391 := by decide
  rcases family_descends (prefixWord ++ tailWord_2635391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2635408 : List Nat := [2, 1, 1, 1, 1, 1, 3, 2, 7, 4]
def baseStart_2635408 : Nat := 118140960795 + 2635408 * 2 ^ 59
def prefixEnd_2635408 : Nat := 4983230072969 + 3 ^ 40 * 2635408 * 2
def baseEnd_2635408 : Nat := 451077008234776729259995

theorem tailTrace_2635408 : CollatzResearch.WordTrace tailWord_2635408 prefixEnd_2635408 451077008234776729259995 := by
  unfold tailWord_2635408
  simp only [CollatzResearch.WordTrace]
  refine ⟨48060613218187191348933439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64080817624249588465244585 48060613218187191348933439)
  ·
    refine ⟨72090919827280787023400159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48060613218187191348933439 72090919827280787023400159)
    ·
      refine ⟨108136379740921180535100239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72090919827280787023400159 108136379740921180535100239)
      ·
        refine ⟨162204569611381770802650359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108136379740921180535100239 162204569611381770802650359)
        ·
          refine ⟨243306854417072656203975539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162204569611381770802650359 243306854417072656203975539)
          ·
            refine ⟨364960281625608984305963309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 243306854417072656203975539 364960281625608984305963309)
            ·
              refine ⟨136860105609603369114736241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 364960281625608984305963309 136860105609603369114736241)
              ·
                refine ⟨102645079207202526836052181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 136860105609603369114736241 102645079207202526836052181)
                ·
                  refine ⟨2405744043918809222719973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 102645079207202526836052181 2405744043918809222719973)
                  ·
                    refine ⟨451077008234776729259995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2405744043918809222719973 451077008234776729259995)
                    ·
                      rfl

theorem cell23_2635408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 7, 4].length) (baseStart_2635408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2635408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2635408 prefixEnd_2635408 := by exact prefixLift 2635408
  have htrace : WordTrace (prefixWord ++ tailWord_2635408) baseStart_2635408 baseEnd_2635408 := by
    simpa [prefixWord, tailWord_2635408, baseEnd_2635408] using wordTrace_append hprefix tailTrace_2635408
  have hstable : (prefixWord ++ tailWord_2635408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2635408).length < 2 ^ (prefixWord ++ tailWord_2635408).sum := by decide
  have hdescent : baseEnd_2635408 < baseStart_2635408 := by decide
  rcases family_descends (prefixWord ++ tailWord_2635408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2635415 : List Nat := [1, 1, 3, 3, 2, 2, 1, 1, 1, 6, 2]
def baseStart_2635415 : Nat := 118140960795 + 2635415 * 2 ^ 59
def prefixEnd_2635415 : Nat := 4983230072969 + 3 ^ 40 * 2635415 * 2
def baseEnd_2635415 : Nat := 1353234619068911660392453

theorem tailTrace_2635415 : CollatzResearch.WordTrace tailWord_2635415 prefixEnd_2635415 1353234619068911660392453 := by
  unfold tailWord_2635415
  simp only [CollatzResearch.WordTrace]
  refine ⟨96121481747349022893371699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64080987831566015262247799 96121481747349022893371699)
  ·
    refine ⟨144182222621023534340057549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96121481747349022893371699 144182222621023534340057549)
    ·
      refine ⟨54068333482883825377521581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144182222621023534340057549 54068333482883825377521581)
      ·
        refine ⟨20275625056081434516570593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54068333482883825377521581 20275625056081434516570593)
        ·
          refine ⟨15206718792061075887427945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20275625056081434516570593 15206718792061075887427945)
          ·
            refine ⟨11405039094045806915570959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15206718792061075887427945 11405039094045806915570959)
            ·
              refine ⟨17107558641068710373356439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11405039094045806915570959 17107558641068710373356439)
              ·
                refine ⟨25661337961603065560034659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17107558641068710373356439 25661337961603065560034659)
                ·
                  refine ⟨38492006942404598340051989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25661337961603065560034659 38492006942404598340051989)
                  ·
                    refine ⟨1804312825425215547189937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 38492006942404598340051989 1804312825425215547189937)
                    ·
                      refine ⟨1353234619068911660392453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1804312825425215547189937 1353234619068911660392453)
                      ·
                        rfl

theorem cell23_2635415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 1, 1, 6, 2].length) (baseStart_2635415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2635415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2635415 prefixEnd_2635415 := by exact prefixLift 2635415
  have htrace : WordTrace (prefixWord ++ tailWord_2635415) baseStart_2635415 baseEnd_2635415 := by
    simpa [prefixWord, tailWord_2635415, baseEnd_2635415] using wordTrace_append hprefix tailTrace_2635415
  have hstable : (prefixWord ++ tailWord_2635415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2635415).length < 2 ^ (prefixWord ++ tailWord_2635415).sum := by decide
  have hdescent : baseEnd_2635415 < baseStart_2635415 := by decide
  rcases family_descends (prefixWord ++ tailWord_2635415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2635425 : List Nat := [1, 2, 3, 3, 2, 1, 1, 1, 5, 4]
def baseStart_2635425 : Nat := 118140960795 + 2635425 * 2 ^ 59
def prefixEnd_2635425 : Nat := 4983230072969 + 3 ^ 40 * 2635425 * 2
def baseEnd_2635425 : Nat := 451079917958485540422469

theorem tailTrace_2635425 : CollatzResearch.WordTrace tailWord_2635425 prefixEnd_2635425 451079917958485540422469 := by
  unfold tailWord_2635425
  simp only [CollatzResearch.WordTrace]
  refine ⟨96121846477312794601235729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64081230984875196400823819 96121846477312794601235729)
  ·
    refine ⟨72091384857984595950926797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96121846477312794601235729 72091384857984595950926797)
    ·
      refine ⟨27034269321744223481597549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72091384857984595950926797 27034269321744223481597549)
      ·
        refine ⟨10137850995654083805599081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27034269321744223481597549 10137850995654083805599081)
        ·
          refine ⟨7603388246740562854199311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10137850995654083805599081 7603388246740562854199311)
          ·
            refine ⟨11405082370110844281298967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7603388246740562854199311 11405082370110844281298967)
            ·
              refine ⟨17107623555166266421948451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11405082370110844281298967 17107623555166266421948451)
              ·
                refine ⟨25661435332749399632922677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17107623555166266421948451 25661435332749399632922677)
                ·
                  refine ⟨2405759562445256215586501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25661435332749399632922677 2405759562445256215586501)
                  ·
                    refine ⟨451079917958485540422469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2405759562445256215586501 451079917958485540422469)
                    ·
                      rfl

theorem cell23_2635425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 1, 5, 4].length) (baseStart_2635425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2635425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2635425 prefixEnd_2635425 := by exact prefixLift 2635425
  have htrace : WordTrace (prefixWord ++ tailWord_2635425) baseStart_2635425 baseEnd_2635425 := by
    simpa [prefixWord, tailWord_2635425, baseEnd_2635425] using wordTrace_append hprefix tailTrace_2635425
  have hstable : (prefixWord ++ tailWord_2635425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2635425).length < 2 ^ (prefixWord ++ tailWord_2635425).sum := by decide
  have hdescent : baseEnd_2635425 < baseStart_2635425 := by decide
  rcases family_descends (prefixWord ++ tailWord_2635425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2635442 : List Nat := [3, 2, 1, 1, 1, 2, 3, 5, 1, 4]
def baseStart_2635442 : Nat := 118140960795 + 2635442 * 2 ^ 59
def prefixEnd_2635442 : Nat := 4983230072969 + 3 ^ 40 * 2635442 * 2
def baseEnd_2635442 : Nat := 451082827682194351584943

theorem tailTrace_2635442 : CollatzResearch.WordTrace tailWord_2635442 prefixEnd_2635442 451082827682194351584943 := by
  unfold tailWord_2635442
  simp only [CollatzResearch.WordTrace]
  refine ⟨24030616629562801626151145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64081644345500804336403053 24030616629562801626151145)
  ·
    refine ⟨18022962472172101219613359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24030616629562801626151145 18022962472172101219613359)
    ·
      refine ⟨27034443708258151829420039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18022962472172101219613359 27034443708258151829420039)
      ·
        refine ⟨40551665562387227744130059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27034443708258151829420039 40551665562387227744130059)
        ·
          refine ⟨60827498343580841616195089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40551665562387227744130059 60827498343580841616195089)
          ·
            refine ⟨45620623757685631212146317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60827498343580841616195089 45620623757685631212146317)
            ·
              refine ⟨17107733909132111704554869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45620623757685631212146317 17107733909132111704554869)
              ·
                refine ⟨1603850053981135472302019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17107733909132111704554869 1603850053981135472302019)
                ·
                  refine ⟨2405775080971703208453029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1603850053981135472302019 2405775080971703208453029)
                  ·
                    refine ⟨451082827682194351584943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2405775080971703208453029 451082827682194351584943)
                    ·
                      rfl

theorem cell23_2635442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 5, 1, 4].length) (baseStart_2635442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2635442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2635442 prefixEnd_2635442 := by exact prefixLift 2635442
  have htrace : WordTrace (prefixWord ++ tailWord_2635442) baseStart_2635442 baseEnd_2635442 := by
    simpa [prefixWord, tailWord_2635442, baseEnd_2635442] using wordTrace_append hprefix tailTrace_2635442
  have hstable : (prefixWord ++ tailWord_2635442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2635442).length < 2 ^ (prefixWord ++ tailWord_2635442).sum := by decide
  have hdescent : baseEnd_2635442 < baseStart_2635442 := by decide
  rcases family_descends (prefixWord ++ tailWord_2635442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2635448 : List Nat := [2, 1, 2, 1, 2, 1, 1, 2, 1, 7, 3]
def baseStart_2635448 : Nat := 118140960795 + 2635448 * 2 ^ 59
def prefixEnd_2635448 : Nat := 4983230072969 + 3 ^ 40 * 2635448 * 2
def baseEnd_2635448 : Nat := 1353251563930510031279801

theorem tailTrace_2635448 : CollatzResearch.WordTrace tailWord_2635448 prefixEnd_2635448 1353251563930510031279801 := by
  unfold tailWord_2635448
  simp only [CollatzResearch.WordTrace]
  refine ⟨48061342678114734764661499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64081790237486313019548665 48061342678114734764661499)
  ·
    refine ⟨72092014017172102146992249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48061342678114734764661499 72092014017172102146992249)
    ·
      refine ⟨54069010512879076610244187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72092014017172102146992249 54069010512879076610244187)
      ·
        refine ⟨81103515769318614915366281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54069010512879076610244187 81103515769318614915366281)
        ·
          refine ⟨60827636826988961186524711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81103515769318614915366281 60827636826988961186524711)
          ·
            refine ⟨91241455240483441779787067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60827636826988961186524711 91241455240483441779787067)
            ·
              refine ⟨136862182860725162669680601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91241455240483441779787067 136862182860725162669680601)
              ·
                refine ⟨102646637145543872002260451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 136862182860725162669680601 102646637145543872002260451)
                ·
                  refine ⟨153969955718315808003390677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 102646637145543872002260451 153969955718315808003390677)
                  ·
                    refine ⟨3608670837148026750079469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 153969955718315808003390677 3608670837148026750079469)
                    ·
                      refine ⟨1353251563930510031279801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3608670837148026750079469 1353251563930510031279801)
                      ·
                        rfl

theorem cell23_2635448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 1, 7, 3].length) (baseStart_2635448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2635448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2635448 prefixEnd_2635448 := by exact prefixLift 2635448
  have htrace : WordTrace (prefixWord ++ tailWord_2635448) baseStart_2635448 baseEnd_2635448 := by
    simpa [prefixWord, tailWord_2635448, baseEnd_2635448] using wordTrace_append hprefix tailTrace_2635448
  have hstable : (prefixWord ++ tailWord_2635448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2635448).length < 2 ^ (prefixWord ++ tailWord_2635448).sum := by decide
  have hdescent : baseEnd_2635448 < baseStart_2635448 := by decide
  rcases family_descends (prefixWord ++ tailWord_2635448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2635482 : List Nat := [3, 1, 1, 2, 2, 3, 2, 2, 3, 1, 3]
def baseStart_2635482 : Nat := 118140960795 + 2635482 * 2 ^ 59
def prefixEnd_2635482 : Nat := 4983230072969 + 3 ^ 40 * 2635482 * 2
def baseEnd_2635482 : Nat := 1353269022272762898254645

theorem tailTrace_2635482 : CollatzResearch.WordTrace tailWord_2635482 prefixEnd_2635482 1353269022272762898254645 := by
  unfold tailWord_2635482
  simp only [CollatzResearch.WordTrace]
  refine ⟨24030981359526573334015175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64082616958737528890707133 24030981359526573334015175)
  ·
    refine ⟨36046472039289860001022763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24030981359526573334015175 36046472039289860001022763)
    ·
      refine ⟨54069708058934790001534145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36046472039289860001022763 54069708058934790001534145)
      ·
        refine ⟨40552281044201092501150609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54069708058934790001534145 40552281044201092501150609)
        ·
          refine ⟨30414210783150819375862957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40552281044201092501150609 30414210783150819375862957)
          ·
            refine ⟨11405329043681557265948609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30414210783150819375862957 11405329043681557265948609)
            ·
              refine ⟨8553996782761167949461457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11405329043681557265948609 8553996782761167949461457)
              ·
                refine ⟨6415497587070875962096093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8553996782761167949461457 6415497587070875962096093)
                ·
                  refine ⟨2405811595151578485786035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6415497587070875962096093 2405811595151578485786035)
                  ·
                    refine ⟨3608717392727367728679053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2405811595151578485786035 3608717392727367728679053)
                    ·
                      refine ⟨1353269022272762898254645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3608717392727367728679053 1353269022272762898254645)
                      ·
                        rfl

theorem cell23_2635482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 2, 3, 1, 3].length) (baseStart_2635482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2635482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2635482 prefixEnd_2635482 := by exact prefixLift 2635482
  have htrace : WordTrace (prefixWord ++ tailWord_2635482) baseStart_2635482 baseEnd_2635482 := by
    simpa [prefixWord, tailWord_2635482, baseEnd_2635482] using wordTrace_append hprefix tailTrace_2635482
  have hstable : (prefixWord ++ tailWord_2635482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2635482).length < 2 ^ (prefixWord ++ tailWord_2635482).sum := by decide
  have hdescent : baseEnd_2635482 < baseStart_2635482 := by decide
  rcases family_descends (prefixWord ++ tailWord_2635482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2635492 : List Nat := [2, 3, 1, 1, 1, 3, 2, 3, 2, 3, 2]
def baseStart_2635492 : Nat := 118140960795 + 2635492 * 2 ^ 59
def prefixEnd_2635492 : Nat := 4983230072969 + 3 ^ 40 * 2635492 * 2
def baseEnd_2635492 : Nat := 1353274157079307859129599

theorem tailTrace_2635492 : CollatzResearch.WordTrace tailWord_2635492 prefixEnd_2635492 1353274157079307859129599 := by
  unfold tailWord_2635492
  simp only [CollatzResearch.WordTrace]
  refine ⟨48062145084035032521962365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64082860112046710029283153 48062145084035032521962365)
  ·
    refine ⟨18023304406513137195735887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48062145084035032521962365 18023304406513137195735887)
    ·
      refine ⟨27034956609769705793603831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18023304406513137195735887 27034956609769705793603831)
      ·
        refine ⟨40552434914654558690405747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27034956609769705793603831 40552434914654558690405747)
        ·
          refine ⟨60828652371981838035608621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40552434914654558690405747 60828652371981838035608621)
          ·
            refine ⟨22810744639493189263353233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60828652371981838035608621 22810744639493189263353233)
            ·
              refine ⟨17108058479619891947514925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22810744639493189263353233 17108058479619891947514925)
              ·
                refine ⟨6415521929857459480318097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17108058479619891947514925 6415521929857459480318097)
                ·
                  refine ⟨4811641447393094610238573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6415521929857459480318097 4811641447393094610238573)
                  ·
                    refine ⟨1804365542772410478839465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4811641447393094610238573 1804365542772410478839465)
                    ·
                      refine ⟨1353274157079307859129599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1804365542772410478839465 1353274157079307859129599)
                      ·
                        rfl

theorem cell23_2635492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 3, 2, 3, 2].length) (baseStart_2635492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2635492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2635492 prefixEnd_2635492 := by exact prefixLift 2635492
  have htrace : WordTrace (prefixWord ++ tailWord_2635492) baseStart_2635492 baseEnd_2635492 := by
    simpa [prefixWord, tailWord_2635492, baseEnd_2635492] using wordTrace_append hprefix tailTrace_2635492
  have hstable : (prefixWord ++ tailWord_2635492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2635492).length < 2 ^ (prefixWord ++ tailWord_2635492).sum := by decide
  have hdescent : baseEnd_2635492 < baseStart_2635492 := by decide
  rcases family_descends (prefixWord ++ tailWord_2635492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2635499 : List Nat := [1, 1, 1, 1, 2, 4, 5, 3, 1, 1, 3]
def baseStart_2635499 : Nat := 118140960795 + 2635499 * 2 ^ 59
def prefixEnd_2635499 : Nat := 4983230072969 + 3 ^ 40 * 2635499 * 2
def baseEnd_2635499 : Nat := 1353277751443889331742067

theorem tailTrace_2635499 : CollatzResearch.WordTrace tailWord_2635499 prefixEnd_2635499 1353277751443889331742067 := by
  unfold tailWord_2635499
  simp only [CollatzResearch.WordTrace]
  refine ⟨96124545479044705239429551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64083030319363136826286367 96124545479044705239429551)
  ·
    refine ⟨144186818218567057859144327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96124545479044705239429551 144186818218567057859144327)
    ·
      refine ⟨216280227327850586788716491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144186818218567057859144327 216280227327850586788716491)
      ·
        refine ⟨324420340991775880183074737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216280227327850586788716491 324420340991775880183074737)
        ·
          refine ⟨243315255743831910137306053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 324420340991775880183074737 243315255743831910137306053)
          ·
            refine ⟨45621610451968483150744885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 243315255743831910137306053 45621610451968483150744885)
            ·
              refine ⟨4277025979872045295382333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45621610451968483150744885 4277025979872045295382333)
              ·
                refine ⟨1603884742452016985768375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4277025979872045295382333 1603884742452016985768375)
                ·
                  refine ⟨2405827113678025478652563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1603884742452016985768375 2405827113678025478652563)
                  ·
                    refine ⟨3608740670517038217978845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2405827113678025478652563 3608740670517038217978845)
                    ·
                      refine ⟨1353277751443889331742067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3608740670517038217978845 1353277751443889331742067)
                      ·
                        rfl

theorem cell23_2635499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5, 3, 1, 1, 3].length) (baseStart_2635499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2635499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2635499 prefixEnd_2635499 := by exact prefixLift 2635499
  have htrace : WordTrace (prefixWord ++ tailWord_2635499) baseStart_2635499 baseEnd_2635499 := by
    simpa [prefixWord, tailWord_2635499, baseEnd_2635499] using wordTrace_append hprefix tailTrace_2635499
  have hstable : (prefixWord ++ tailWord_2635499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2635499).length < 2 ^ (prefixWord ++ tailWord_2635499).sum := by decide
  have hdescent : baseEnd_2635499 < baseStart_2635499 := by decide
  rcases family_descends (prefixWord ++ tailWord_2635499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2635516 : List Nat := [2, 2, 2, 1, 3, 1, 5, 2, 1, 1, 3]
def baseStart_2635516 : Nat := 118140960795 + 2635516 * 2 ^ 59
def prefixEnd_2635516 : Nat := 4983230072969 + 3 ^ 40 * 2635516 * 2
def baseEnd_2635516 : Nat := 1353286480615015765229489

theorem tailTrace_2635516 : CollatzResearch.WordTrace tailWord_2635516 prefixEnd_2635516 1353286480615015765229489 := by
  unfold tailWord_2635516
  simp only [CollatzResearch.WordTrace]
  refine ⟨48062582759991558571399201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64083443679988744761865601 48062582759991558571399201)
  ·
    refine ⟨36046937069993668928549401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48062582759991558571399201 36046937069993668928549401)
    ·
      refine ⟨27035202802495251696412051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36046937069993668928549401 27035202802495251696412051)
      ·
        refine ⟨40552804203742877544618077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27035202802495251696412051 40552804203742877544618077)
        ·
          refine ⟨15207301576403579079231779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40552804203742877544618077 15207301576403579079231779)
          ·
            refine ⟨22810952364605368618847669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15207301576403579079231779 22810952364605368618847669)
            ·
              refine ⟨2138526784181753308016969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22810952364605368618847669 2138526784181753308016969)
              ·
                refine ⟨1603895088136314981012727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2138526784181753308016969 1603895088136314981012727)
                ·
                  refine ⟨2405842632204472471519091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1603895088136314981012727 2405842632204472471519091)
                  ·
                    refine ⟨3608763948306708707278637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2405842632204472471519091 3608763948306708707278637)
                    ·
                      refine ⟨1353286480615015765229489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3608763948306708707278637 1353286480615015765229489)
                      ·
                        rfl

theorem cell23_2635516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 5, 2, 1, 1, 3].length) (baseStart_2635516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2635516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2635516 prefixEnd_2635516 := by exact prefixLift 2635516
  have htrace : WordTrace (prefixWord ++ tailWord_2635516) baseStart_2635516 baseEnd_2635516 := by
    simpa [prefixWord, tailWord_2635516, baseEnd_2635516] using wordTrace_append hprefix tailTrace_2635516
  have hstable : (prefixWord ++ tailWord_2635516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2635516).length < 2 ^ (prefixWord ++ tailWord_2635516).sum := by decide
  have hdescent : baseEnd_2635516 < baseStart_2635516 := by decide
  rcases family_descends (prefixWord ++ tailWord_2635516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2635522 : List Nat := [3, 4, 1, 1, 1, 1, 2, 2, 3, 1, 4]
def baseStart_2635522 : Nat := 118140960795 + 2635522 * 2 ^ 59
def prefixEnd_2635522 : Nat := 4983230072969 + 3 ^ 40 * 2635522 * 2
def baseEnd_2635522 : Nat := 1353289561498942741754461

theorem tailTrace_2635522 : CollatzResearch.WordTrace tailWord_2635522 prefixEnd_2635522 1353289561498942741754461 := by
  unfold tailWord_2635522
  simp only [CollatzResearch.WordTrace]
  refine ⟨24031346089490345041879205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64083589571974253445011213 24031346089490345041879205)
  ·
    refine ⟨4505877391779439695352351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24031346089490345041879205 4505877391779439695352351)
    ·
      refine ⟨6758816087669159543028527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4505877391779439695352351 6758816087669159543028527)
      ·
        refine ⟨10138224131503739314542791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6758816087669159543028527 10138224131503739314542791)
        ·
          refine ⟨15207336197255608971814187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10138224131503739314542791 15207336197255608971814187)
          ·
            refine ⟨22811004295883413457721281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15207336197255608971814187 22811004295883413457721281)
            ·
              refine ⟨17108253221912560093290961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22811004295883413457721281 17108253221912560093290961)
              ·
                refine ⟨12831189916434420069968221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17108253221912560093290961 12831189916434420069968221)
                ·
                  refine ⟨4811696218662907526238083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12831189916434420069968221 4811696218662907526238083)
                  ·
                    refine ⟨7217544327994361289357125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4811696218662907526238083 7217544327994361289357125)
                    ·
                      refine ⟨1353289561498942741754461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7217544327994361289357125 1353289561498942741754461)
                      ·
                        rfl

theorem cell23_2635522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_2635522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2635522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2635522 prefixEnd_2635522 := by exact prefixLift 2635522
  have htrace : WordTrace (prefixWord ++ tailWord_2635522) baseStart_2635522 baseEnd_2635522 := by
    simpa [prefixWord, tailWord_2635522, baseEnd_2635522] using wordTrace_append hprefix tailTrace_2635522
  have hstable : (prefixWord ++ tailWord_2635522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2635522).length < 2 ^ (prefixWord ++ tailWord_2635522).sum := by decide
  have hdescent : baseEnd_2635522 < baseStart_2635522 := by decide
  rcases family_descends (prefixWord ++ tailWord_2635522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2635555 : List Nat := [1, 1, 1, 4, 2, 1, 3, 1, 3, 3, 3]
def baseStart_2635555 : Nat := 118140960795 + 2635555 * 2 ^ 59
def prefixEnd_2635555 : Nat := 4983230072969 + 3 ^ 40 * 2635555 * 2
def baseEnd_2635555 : Nat := 1353306506360541112641809

theorem tailTrace_2635555 : CollatzResearch.WordTrace tailWord_2635555 prefixEnd_2635555 1353306506360541112641809 := by
  unfold tailWord_2635555
  simp only [CollatzResearch.WordTrace]
  refine ⟨96126587966841826803468119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64084391977894551202312079 96126587966841826803468119)
  ·
    refine ⟨144189881950262740205202179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96126587966841826803468119 144189881950262740205202179)
    ·
      refine ⟨216284822925394110307803269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144189881950262740205202179 216284822925394110307803269)
      ·
        refine ⟨40553404298511395682713113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 216284822925394110307803269 40553404298511395682713113)
        ·
          refine ⟨30415053223883546762034835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40553404298511395682713113 30415053223883546762034835)
          ·
            refine ⟨45622579835825320143052253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30415053223883546762034835 45622579835825320143052253)
            ·
              refine ⟨17108467438434495053644595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45622579835825320143052253 17108467438434495053644595)
              ·
                refine ⟨25662701157651742580466893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17108467438434495053644595 25662701157651742580466893)
                ·
                  refine ⟨9623512934119403467675085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25662701157651742580466893 9623512934119403467675085)
                  ·
                    refine ⟨3608817350294776300378157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9623512934119403467675085 3608817350294776300378157)
                    ·
                      refine ⟨1353306506360541112641809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3608817350294776300378157 1353306506360541112641809)
                      ·
                        rfl

theorem cell23_2635555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 1, 3, 3, 3].length) (baseStart_2635555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2635555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2635555 prefixEnd_2635555 := by exact prefixLift 2635555
  have htrace : WordTrace (prefixWord ++ tailWord_2635555) baseStart_2635555 baseEnd_2635555 := by
    simpa [prefixWord, tailWord_2635555, baseEnd_2635555] using wordTrace_append hprefix tailTrace_2635555
  have hstable : (prefixWord ++ tailWord_2635555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2635555).length < 2 ^ (prefixWord ++ tailWord_2635555).sum := by decide
  have hdescent : baseEnd_2635555 < baseStart_2635555 := by decide
  rcases family_descends (prefixWord ++ tailWord_2635555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2635566 : List Nat := [4, 1, 3, 2, 2, 1, 2, 2, 2, 4]
def baseStart_2635566 : Nat := 118140960795 + 2635566 * 2 ^ 59
def prefixEnd_2635566 : Nat := 4983230072969 + 3 ^ 40 * 2635566 * 2
def baseEnd_2635566 : Nat := 451104051549246856534753

theorem tailTrace_2635566 : CollatzResearch.WordTrace tailWord_2635566 prefixEnd_2635566 451104051549246856534753 := by
  unfold tailWord_2635566
  simp only [CollatzResearch.WordTrace]
  refine ⟨12015873646225246960264819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64084659446534650454745701 12015873646225246960264819)
  ·
    refine ⟨18023810469337870440397229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12015873646225246960264819 18023810469337870440397229)
    ·
      refine ⟨6758928926001701415148961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18023810469337870440397229 6758928926001701415148961)
      ·
        refine ⟨5069196694501276061361721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6758928926001701415148961 5069196694501276061361721)
        ·
          refine ⟨3801897520875957046021291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5069196694501276061361721 3801897520875957046021291)
          ·
            refine ⟨5702846281313935569031937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3801897520875957046021291 5702846281313935569031937)
            ·
              refine ⟨4277134710985451676773953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5702846281313935569031937 4277134710985451676773953)
              ·
                refine ⟨3207851033239088757580465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4277134710985451676773953 3207851033239088757580465)
                ·
                  refine ⟨2405888274929316568185349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3207851033239088757580465 2405888274929316568185349)
                  ·
                    refine ⟨451104051549246856534753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2405888274929316568185349 451104051549246856534753)
                    ·
                      rfl

theorem cell23_2635566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 2, 2, 2, 4].length) (baseStart_2635566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2635566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2635566 prefixEnd_2635566 := by exact prefixLift 2635566
  have htrace : WordTrace (prefixWord ++ tailWord_2635566) baseStart_2635566 baseEnd_2635566 := by
    simpa [prefixWord, tailWord_2635566, baseEnd_2635566] using wordTrace_append hprefix tailTrace_2635566
  have hstable : (prefixWord ++ tailWord_2635566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2635566).length < 2 ^ (prefixWord ++ tailWord_2635566).sum := by decide
  have hdescent : baseEnd_2635566 < baseStart_2635566 := by decide
  rcases family_descends (prefixWord ++ tailWord_2635566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2635568 : List Nat := [2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 7]
def baseStart_2635568 : Nat := 118140960795 + 2635568 * 2 ^ 59
def prefixEnd_2635568 : Nat := 4983230072969 + 3 ^ 40 * 2635568 * 2
def baseEnd_2635568 : Nat := 1353313181609049561779249

theorem tailTrace_2635568 : CollatzResearch.WordTrace tailWord_2635568 prefixEnd_2635568 1353313181609049561779249 := by
  unfold tailWord_2635568
  simp only [CollatzResearch.WordTrace]
  refine ⟨48063531057897365011845679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64084708077196486682460905 48063531057897365011845679)
  ·
    refine ⟨72095296586846047517768519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48063531057897365011845679 72095296586846047517768519)
    ·
      refine ⟨108142944880269071276652779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72095296586846047517768519 108142944880269071276652779)
      ·
        refine ⟨162214417320403606914979169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108142944880269071276652779 162214417320403606914979169)
        ·
          refine ⟨121660812990302705186234377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162214417320403606914979169 121660812990302705186234377)
          ·
            refine ⟨91245609742727028889675783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121660812990302705186234377 91245609742727028889675783)
            ·
              refine ⟨136868414614090543334513675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91245609742727028889675783 136868414614090543334513675)
              ·
                refine ⟨205302621921135815001770513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 136868414614090543334513675 205302621921135815001770513)
                ·
                  refine ⟨153976966440851861251327885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 205302621921135815001770513 153976966440851861251327885)
                  ·
                    refine ⟨57741362415319447969247957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 153976966440851861251327885 57741362415319447969247957)
                    ·
                      refine ⟨1353313181609049561779249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 57741362415319447969247957 1353313181609049561779249)
                      ·
                        rfl

theorem cell23_2635568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 7].length) (baseStart_2635568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2635568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2635568 prefixEnd_2635568 := by exact prefixLift 2635568
  have htrace : WordTrace (prefixWord ++ tailWord_2635568) baseStart_2635568 baseEnd_2635568 := by
    simpa [prefixWord, tailWord_2635568, baseEnd_2635568] using wordTrace_append hprefix tailTrace_2635568
  have hstable : (prefixWord ++ tailWord_2635568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2635568).length < 2 ^ (prefixWord ++ tailWord_2635568).sum := by decide
  have hdescent : baseEnd_2635568 < baseStart_2635568 := by decide
  rcases family_descends (prefixWord ++ tailWord_2635568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2635573 : List Nat := [1, 3, 3, 1, 4, 1, 1, 4, 1, 2, 2]
def baseStart_2635573 : Nat := 118140960795 + 2635573 * 2 ^ 59
def prefixEnd_2635573 : Nat := 4983230072969 + 3 ^ 40 * 2635573 * 2
def baseEnd_2635573 : Nat := 1353315749012322042216727

theorem tailTrace_2635573 : CollatzResearch.WordTrace tailWord_2635573 prefixEnd_2635573 1353315749012322042216727 := by
  unfold tailWord_2635573
  simp only [CollatzResearch.WordTrace]
  refine ⟨96127244480776615877623373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64084829653851077251748915 96127244480776615877623373)
  ·
    refine ⟨36047716680291230954108765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96127244480776615877623373 36047716680291230954108765)
    ·
      refine ⟨13517893755109211607790787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36047716680291230954108765 13517893755109211607790787)
      ·
        refine ⟨20276840632663817411686181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13517893755109211607790787 20276840632663817411686181)
        ·
          refine ⟨3801907618624465764691159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20276840632663817411686181 3801907618624465764691159)
          ·
            refine ⟨5702861427936698647036739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3801907618624465764691159 5702861427936698647036739)
            ·
              refine ⟨8554292141905047970555109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5702861427936698647036739 8554292141905047970555109)
              ·
                refine ⟨1603929776607196494479083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8554292141905047970555109 1603929776607196494479083)
                ·
                  refine ⟨2405894664910794741718625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1603929776607196494479083 2405894664910794741718625)
                  ·
                    refine ⟨1804420998683096056288969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2405894664910794741718625 1804420998683096056288969)
                    ·
                      refine ⟨1353315749012322042216727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1804420998683096056288969 1353315749012322042216727)
                      ·
                        rfl

theorem cell23_2635573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 4, 1, 2, 2].length) (baseStart_2635573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2635573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2635573 prefixEnd_2635573 := by exact prefixLift 2635573
  have htrace : WordTrace (prefixWord ++ tailWord_2635573) baseStart_2635573 baseEnd_2635573 := by
    simpa [prefixWord, tailWord_2635573, baseEnd_2635573] using wordTrace_append hprefix tailTrace_2635573
  have hstable : (prefixWord ++ tailWord_2635573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2635573).length < 2 ^ (prefixWord ++ tailWord_2635573).sum := by decide
  have hdescent : baseEnd_2635573 < baseStart_2635573 := by decide
  rcases family_descends (prefixWord ++ tailWord_2635573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2635616 : List Nat := [2, 1, 1, 3, 3, 2, 4, 1, 1, 3, 2]
def baseStart_2635616 : Nat := 118140960795 + 2635616 * 2 ^ 59
def prefixEnd_2635616 : Nat := 4983230072969 + 3 ^ 40 * 2635616 * 2
def baseEnd_2635616 : Nat := 1353337828680465373979029

theorem tailTrace_2635616 : CollatzResearch.WordTrace tailWord_2635616 prefixEnd_2635616 1353337828680465373979029 := by
  unfold tailWord_2635616
  simp only [CollatzResearch.WordTrace]
  refine ⟨48064406409810417110719351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64085875213080556147625801 48064406409810417110719351)
  ·
    refine ⟨72096609614715625666079027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48064406409810417110719351 72096609614715625666079027)
    ·
      refine ⟨108144914422073438499118541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72096609614715625666079027 108144914422073438499118541)
      ·
        refine ⟨40554342908277539437169453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108144914422073438499118541 40554342908277539437169453)
        ·
          refine ⟨15207878590604077288938545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40554342908277539437169453 15207878590604077288938545)
          ·
            refine ⟨11405908942953057966703909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15207878590604077288938545 11405908942953057966703909)
            ·
              refine ⟨2138607926803698368756983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11405908942953057966703909 2138607926803698368756983)
              ·
                refine ⟨3207911890205547553135475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2138607926803698368756983 3207911890205547553135475)
                ·
                  refine ⟨4811867835308321329703213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3207911890205547553135475 4811867835308321329703213)
                  ·
                    refine ⟨1804450438240620498638705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4811867835308321329703213 1804450438240620498638705)
                    ·
                      refine ⟨1353337828680465373979029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1804450438240620498638705 1353337828680465373979029)
                      ·
                        rfl

theorem cell23_2635616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 4, 1, 1, 3, 2].length) (baseStart_2635616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2635616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2635616 prefixEnd_2635616 := by exact prefixLift 2635616
  have htrace : WordTrace (prefixWord ++ tailWord_2635616) baseStart_2635616 baseEnd_2635616 := by
    simpa [prefixWord, tailWord_2635616, baseEnd_2635616] using wordTrace_append hprefix tailTrace_2635616
  have hstable : (prefixWord ++ tailWord_2635616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2635616).length < 2 ^ (prefixWord ++ tailWord_2635616).sum := by decide
  have hdescent : baseEnd_2635616 < baseStart_2635616 := by decide
  rcases family_descends (prefixWord ++ tailWord_2635616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2635665 : List Nat := [1, 2, 2, 1, 1, 1, 6, 1, 1, 7]
def baseStart_2635665 : Nat := 118140960795 + 2635665 * 2 ^ 59
def prefixEnd_2635665 : Nat := 4983230072969 + 3 ^ 40 * 2635665 * 2
def baseEnd_2635665 : Nat := 451120996410845227422101

theorem tailTrace_2635665 : CollatzResearch.WordTrace tailWord_2635665 prefixEnd_2635665 451120996410845227422101 := by
  unfold tailWord_2635665
  simp only [CollatzResearch.WordTrace]
  refine ⟨96130599996443315589972449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64087066664295543726648299 96130599996443315589972449)
  ·
    refine ⟨72097949997332486692479337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96130599996443315589972449 72097949997332486692479337)
    ·
      refine ⟨54073462497999365019359503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72097949997332486692479337 54073462497999365019359503)
      ·
        refine ⟨81110193746999047529039255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54073462497999365019359503 81110193746999047529039255)
        ·
          refine ⟨121665290620498571293558883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81110193746999047529039255 121665290620498571293558883)
          ·
            refine ⟨182497935930747856940338325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121665290620498571293558883 182497935930747856940338325)
            ·
              refine ⟨8554590746753805794078359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 182497935930747856940338325 8554590746753805794078359)
              ·
                refine ⟨12831886120130708691117539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8554590746753805794078359 12831886120130708691117539)
                ·
                  refine ⟨19247829180196063036676309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12831886120130708691117539 19247829180196063036676309)
                  ·
                    refine ⟨451120996410845227422101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19247829180196063036676309 451120996410845227422101)
                    ·
                      rfl

theorem cell23_2635665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 7].length) (baseStart_2635665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2635665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2635665 prefixEnd_2635665 := by exact prefixLift 2635665
  have htrace : WordTrace (prefixWord ++ tailWord_2635665) baseStart_2635665 baseEnd_2635665 := by
    simpa [prefixWord, tailWord_2635665, baseEnd_2635665] using wordTrace_append hprefix tailTrace_2635665
  have hstable : (prefixWord ++ tailWord_2635665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2635665).length < 2 ^ (prefixWord ++ tailWord_2635665).sum := by decide
  have hdescent : baseEnd_2635665 < baseStart_2635665 := by decide
  rcases family_descends (prefixWord ++ tailWord_2635665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2635712 : List Nat := [2, 1, 1, 2, 3, 2, 2, 1, 5, 4]
def baseStart_2635712 : Nat := 118140960795 + 2635712 * 2 ^ 59
def prefixEnd_2635712 : Nat := 4983230072969 + 3 ^ 40 * 2635712 * 2
def baseEnd_2635712 : Nat := 451129040941098999459529

theorem tailTrace_2635712 : CollatzResearch.WordTrace tailWord_2635712 prefixEnd_2635712 451129040941098999459529 := by
  unfold tailWord_2635712
  simp only [CollatzResearch.WordTrace]
  refine ⟨48066157113636521308466695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64088209484848695077955593 48066157113636521308466695)
  ·
    refine ⟨72099235670454781962700043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48066157113636521308466695 72099235670454781962700043)
    ·
      refine ⟨108148853505682172944050065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72099235670454781962700043 108148853505682172944050065)
      ·
        refine ⟨81111640129261629708037549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108148853505682172944050065 81111640129261629708037549)
        ·
          refine ⟨30416865048473111140514081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81111640129261629708037549 30416865048473111140514081)
          ·
            refine ⟨22812648786354833355385561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30416865048473111140514081 22812648786354833355385561)
            ·
              refine ⟨17109486589766125016539171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22812648786354833355385561 17109486589766125016539171)
              ·
                refine ⟨25664229884649187524808757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17109486589766125016539171 25664229884649187524808757)
                ·
                  refine ⟨2406021551685861330450821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25664229884649187524808757 2406021551685861330450821)
                  ·
                    refine ⟨451129040941098999459529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2406021551685861330450821 451129040941098999459529)
                    ·
                      rfl

theorem cell23_2635712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 1, 5, 4].length) (baseStart_2635712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2635712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2635712 prefixEnd_2635712 := by exact prefixLift 2635712
  have htrace : WordTrace (prefixWord ++ tailWord_2635712) baseStart_2635712 baseEnd_2635712 := by
    simpa [prefixWord, tailWord_2635712, baseEnd_2635712] using wordTrace_append hprefix tailTrace_2635712
  have hstable : (prefixWord ++ tailWord_2635712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2635712).length < 2 ^ (prefixWord ++ tailWord_2635712).sum := by decide
  have hdescent : baseEnd_2635712 < baseStart_2635712 := by decide
  rcases family_descends (prefixWord ++ tailWord_2635712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2635722 : List Nat := [3, 1, 2, 1, 2, 1, 2, 3, 1, 4, 3]
def baseStart_2635722 : Nat := 118140960795 + 2635722 * 2 ^ 59
def prefixEnd_2635722 : Nat := 4983230072969 + 3 ^ 40 * 2635722 * 2
def baseEnd_2635722 : Nat := 1353392257629841959253541

theorem tailTrace_2635722 : CollatzResearch.WordTrace tailWord_2635722 prefixEnd_2635722 1353392257629841959253541 := by
  unfold tailWord_2635722
  simp only [CollatzResearch.WordTrace]
  refine ⟨24033169739309203581199355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64088452638157876216531613 24033169739309203581199355)
  ·
    refine ⟨36049754608963805371799033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24033169739309203581199355 36049754608963805371799033)
    ·
      refine ⟨27037315956722854028849275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36049754608963805371799033 27037315956722854028849275)
      ·
        refine ⟨40555973935084281043273913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27037315956722854028849275 40555973935084281043273913)
        ·
          refine ⟨30416980451313210782455435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40555973935084281043273913 30416980451313210782455435)
          ·
            refine ⟨45625470676969816173683153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30416980451313210782455435 45625470676969816173683153)
            ·
              refine ⟨34219103007727362130262365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45625470676969816173683153 34219103007727362130262365)
              ·
                refine ⟨12832163627897760798848387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34219103007727362130262365 12832163627897760798848387)
                ·
                  refine ⟨19248245441846641198272581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12832163627897760798848387 19248245441846641198272581)
                  ·
                    refine ⟨3609046020346245224676109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19248245441846641198272581 3609046020346245224676109)
                    ·
                      refine ⟨1353392257629841959253541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3609046020346245224676109 1353392257629841959253541)
                      ·
                        rfl

theorem cell23_2635722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 3, 1, 4, 3].length) (baseStart_2635722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2635722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2635722 prefixEnd_2635722 := by exact prefixLift 2635722
  have htrace : WordTrace (prefixWord ++ tailWord_2635722) baseStart_2635722 baseEnd_2635722 := by
    simpa [prefixWord, tailWord_2635722, baseEnd_2635722] using wordTrace_append hprefix tailTrace_2635722
  have hstable : (prefixWord ++ tailWord_2635722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2635722).length < 2 ^ (prefixWord ++ tailWord_2635722).sum := by decide
  have hdescent : baseEnd_2635722 < baseStart_2635722 := by decide
  rcases family_descends (prefixWord ++ tailWord_2635722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2635732 : List Nat := [2, 4, 1, 2, 1, 1, 2, 1, 2, 1, 6]
def baseStart_2635732 : Nat := 118140960795 + 2635732 * 2 ^ 59
def prefixEnd_2635732 : Nat := 4983230072969 + 3 ^ 40 * 2635732 * 2
def baseEnd_2635732 : Nat := 1353397392436386920128495

theorem tailTrace_2635732 : CollatzResearch.WordTrace tailWord_2635732 prefixEnd_2635732 1353397392436386920128495 := by
  unfold tailWord_2635732
  simp only [CollatzResearch.WordTrace]
  refine ⟨48066521843600293016330725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64088695791467057355107633 48066521843600293016330725)
  ·
    refine ⟨9012472845675054940562011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48066521843600293016330725 9012472845675054940562011)
    ·
      refine ⟨13518709268512582410843017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9012472845675054940562011 13518709268512582410843017)
      ·
        refine ⟨10139031951384436808132263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13518709268512582410843017 10139031951384436808132263)
        ·
          refine ⟨15208547927076655212198395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10139031951384436808132263 15208547927076655212198395)
          ·
            refine ⟨22812821890614982818297593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15208547927076655212198395 22812821890614982818297593)
            ·
              refine ⟨17109616417961237113723195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22812821890614982818297593 17109616417961237113723195)
              ·
                refine ⟨25664424626941855670584793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17109616417961237113723195 25664424626941855670584793)
                ·
                  refine ⟨19248318470206391752938595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25664424626941855670584793 19248318470206391752938595)
                  ·
                    refine ⟨28872477705309587629407893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19248318470206391752938595 28872477705309587629407893)
                    ·
                      refine ⟨1353397392436386920128495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28872477705309587629407893 1353397392436386920128495)
                      ·
                        rfl

theorem cell23_2635732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_2635732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2635732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2635732 prefixEnd_2635732 := by exact prefixLift 2635732
  have htrace : WordTrace (prefixWord ++ tailWord_2635732) baseStart_2635732 baseEnd_2635732 := by
    simpa [prefixWord, tailWord_2635732, baseEnd_2635732] using wordTrace_append hprefix tailTrace_2635732
  have hstable : (prefixWord ++ tailWord_2635732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2635732).length < 2 ^ (prefixWord ++ tailWord_2635732).sum := by decide
  have hdescent : baseEnd_2635732 < baseStart_2635732 := by decide
  rcases family_descends (prefixWord ++ tailWord_2635732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2635752 : List Nat := [2, 1, 4, 1, 1, 1, 1, 2, 2, 5, 3]
def baseStart_2635752 : Nat := 118140960795 + 2635752 * 2 ^ 59
def prefixEnd_2635752 : Nat := 4983230072969 + 3 ^ 40 * 2635752 * 2
def baseEnd_2635752 : Nat := 1353407662049476841878403

theorem tailTrace_2635752 : CollatzResearch.WordTrace tailWord_2635752 prefixEnd_2635752 1353407662049476841878403 := by
  unfold tailWord_2635752
  simp only [CollatzResearch.WordTrace]
  refine ⟨48066886573564064724194755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64089182098085419632259673 48066886573564064724194755)
  ·
    refine ⟨72100329860346097086292133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48066886573564064724194755 72100329860346097086292133)
    ·
      refine ⟨13518811848814893203679775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72100329860346097086292133 13518811848814893203679775)
      ·
        refine ⟨20278217773222339805519663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13518811848814893203679775 20278217773222339805519663)
        ·
          refine ⟨30417326659833509708279495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20278217773222339805519663 30417326659833509708279495)
          ·
            refine ⟨45625989989750264562419243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30417326659833509708279495 45625989989750264562419243)
            ·
              refine ⟨68438984984625396843628865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45625989989750264562419243 68438984984625396843628865)
              ·
                refine ⟨51329238738469047632721649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68438984984625396843628865 51329238738469047632721649)
                ·
                  refine ⟨38496929053851785724541237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51329238738469047632721649 38496929053851785724541237)
                  ·
                    refine ⟨3609087098798604911675741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38496929053851785724541237 3609087098798604911675741)
                    ·
                      refine ⟨1353407662049476841878403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3609087098798604911675741 1353407662049476841878403)
                      ·
                        rfl

theorem cell23_2635752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 2, 5, 3].length) (baseStart_2635752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2635752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2635752 prefixEnd_2635752 := by exact prefixLift 2635752
  have htrace : WordTrace (prefixWord ++ tailWord_2635752) baseStart_2635752 baseEnd_2635752 := by
    simpa [prefixWord, tailWord_2635752, baseEnd_2635752] using wordTrace_append hprefix tailTrace_2635752
  have hstable : (prefixWord ++ tailWord_2635752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2635752).length < 2 ^ (prefixWord ++ tailWord_2635752).sum := by decide
  have hdescent : baseEnd_2635752 < baseStart_2635752 := by decide
  rcases family_descends (prefixWord ++ tailWord_2635752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2635769 : List Nat := [1, 2, 1, 3, 1, 4, 1, 1, 5, 1, 3]
def baseStart_2635769 : Nat := 118140960795 + 2635769 * 2 ^ 59
def prefixEnd_2635769 : Nat := 4983230072969 + 3 ^ 40 * 2635769 * 2
def baseEnd_2635769 : Nat := 1353416391220603275365825

theorem tailTrace_2635769 : CollatzResearch.WordTrace tailWord_2635769 prefixEnd_2635769 1353416391220603275365825 := by
  unfold tailWord_2635769
  simp only [CollatzResearch.WordTrace]
  refine ⟨96134393188066541351758361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64089595458711027567838907 96134393188066541351758361)
  ·
    refine ⟨72100794891049906013818771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96134393188066541351758361 72100794891049906013818771)
    ·
      refine ⟨108151192336574859020728157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72100794891049906013818771 108151192336574859020728157)
      ·
        refine ⟨40556697126215572132773059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108151192336574859020728157 40556697126215572132773059)
        ·
          refine ⟨60835045689323358199159589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40556697126215572132773059 60835045689323358199159589)
          ·
            refine ⟨11406571066748129662342423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60835045689323358199159589 11406571066748129662342423)
            ·
              refine ⟨17109856600122194493513635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11406571066748129662342423 17109856600122194493513635)
              ·
                refine ⟨25664784900183291740270453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17109856600122194493513635 25664784900183291740270453)
                ·
                  refine ⟨2406073584392183600650355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25664784900183291740270453 2406073584392183600650355)
                  ·
                    refine ⟨3609110376588275400975533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2406073584392183600650355 3609110376588275400975533)
                    ·
                      refine ⟨1353416391220603275365825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3609110376588275400975533 1353416391220603275365825)
                      ·
                        rfl

theorem cell23_2635769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 1, 5, 1, 3].length) (baseStart_2635769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2635769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2635769 prefixEnd_2635769 := by exact prefixLift 2635769
  have htrace : WordTrace (prefixWord ++ tailWord_2635769) baseStart_2635769 baseEnd_2635769 := by
    simpa [prefixWord, tailWord_2635769, baseEnd_2635769] using wordTrace_append hprefix tailTrace_2635769
  have hstable : (prefixWord ++ tailWord_2635769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2635769).length < 2 ^ (prefixWord ++ tailWord_2635769).sum := by decide
  have hdescent : baseEnd_2635769 < baseStart_2635769 := by decide
  rcases family_descends (prefixWord ++ tailWord_2635769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2635772 : List Nat := [2, 2, 2, 1, 2, 2, 1, 3, 3, 5]
def baseStart_2635772 : Nat := 118140960795 + 2635772 * 2 ^ 59
def prefixEnd_2635772 : Nat := 4983230072969 + 3 ^ 40 * 2635772 * 2
def baseEnd_2635772 : Nat := 451139310554188921209437

theorem tailTrace_2635772 : CollatzResearch.WordTrace tailWord_2635772 prefixEnd_2635772 451139310554188921209437 := by
  unfold tailWord_2635772
  simp only [CollatzResearch.WordTrace]
  refine ⟨48067251303527836432058785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64089668404703781909411713 48067251303527836432058785)
  ·
    refine ⟨36050438477645877324044089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48067251303527836432058785 36050438477645877324044089)
    ·
      refine ⟨27037828858234407993033067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36050438477645877324044089 27037828858234407993033067)
      ·
        refine ⟨40556743287351611989549601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27037828858234407993033067 40556743287351611989549601)
        ·
          refine ⟨30417557465513708992162201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40556743287351611989549601 30417557465513708992162201)
          ·
            refine ⟨22813168099135281744121651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30417557465513708992162201 22813168099135281744121651)
            ·
              refine ⟨34219752148702922616182477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22813168099135281744121651 34219752148702922616182477)
              ·
                refine ⟨12832407055763595981068429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34219752148702922616182477 12832407055763595981068429)
                ·
                  refine ⟨4812152645911348492900661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12832407055763595981068429 4812152645911348492900661)
                  ·
                    refine ⟨451139310554188921209437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4812152645911348492900661 451139310554188921209437)
                    ·
                      rfl

theorem cell23_2635772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 3, 3, 5].length) (baseStart_2635772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2635772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2635772 prefixEnd_2635772 := by exact prefixLift 2635772
  have htrace : WordTrace (prefixWord ++ tailWord_2635772) baseStart_2635772 baseEnd_2635772 := by
    simpa [prefixWord, tailWord_2635772, baseEnd_2635772] using wordTrace_append hprefix tailTrace_2635772
  have hstable : (prefixWord ++ tailWord_2635772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2635772).length < 2 ^ (prefixWord ++ tailWord_2635772).sum := by decide
  have hdescent : baseEnd_2635772 < baseStart_2635772 := by decide
  rcases family_descends (prefixWord ++ tailWord_2635772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2635780 : List Nat := [2, 3, 2, 4, 1, 1, 2, 3, 1, 4]
def baseStart_2635780 : Nat := 118140960795 + 2635780 * 2 ^ 59
def prefixEnd_2635780 : Nat := 4983230072969 + 3 ^ 40 * 2635780 * 2
def baseEnd_2635780 : Nat := 451140679835934244109425

theorem tailTrace_2635780 : CollatzResearch.WordTrace tailWord_2635780 prefixEnd_2635780 451140679835934244109425 := by
  unfold tailWord_2635780
  simp only [CollatzResearch.WordTrace]
  refine ⟨48067397195513345115204397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64089862927351126820272529 48067397195513345115204397)
  ·
    refine ⟨18025273948317504418201649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48067397195513345115204397 18025273948317504418201649)
    ·
      refine ⟨13518955461238128313651237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18025273948317504418201649 13518955461238128313651237)
      ·
        refine ⟨2534804148982149058809607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13518955461238128313651237 2534804148982149058809607)
        ·
          refine ⟨3802206223473223588214411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2534804148982149058809607 3802206223473223588214411)
          ·
            refine ⟨5703309335209835382321617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3802206223473223588214411 5703309335209835382321617)
            ·
              refine ⟨4277482001407376536741213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5703309335209835382321617 4277482001407376536741213)
              ·
                refine ⟨1604055750527766201277955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4277482001407376536741213 1604055750527766201277955)
                ·
                  refine ⟨2406083625791649301916933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1604055750527766201277955 2406083625791649301916933)
                  ·
                    refine ⟨451140679835934244109425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2406083625791649301916933 451140679835934244109425)
                    ·
                      rfl

theorem cell23_2635780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 2, 3, 1, 4].length) (baseStart_2635780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2635780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2635780 prefixEnd_2635780 := by exact prefixLift 2635780
  have htrace : WordTrace (prefixWord ++ tailWord_2635780) baseStart_2635780 baseEnd_2635780 := by
    simpa [prefixWord, tailWord_2635780, baseEnd_2635780] using wordTrace_append hprefix tailTrace_2635780
  have hstable : (prefixWord ++ tailWord_2635780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2635780).length < 2 ^ (prefixWord ++ tailWord_2635780).sum := by decide
  have hdescent : baseEnd_2635780 < baseStart_2635780 := by decide
  rcases family_descends (prefixWord ++ tailWord_2635780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2635826 : List Nat := [3, 2, 1, 1, 2, 4, 2, 2, 1, 1, 4]
def baseStart_2635826 : Nat := 118140960795 + 2635826 * 2 ^ 59
def prefixEnd_2635826 : Nat := 4983230072969 + 3 ^ 40 * 2635826 * 2
def baseEnd_2635826 : Nat := 1353445659617909552353063

theorem tailTrace_2635826 : CollatzResearch.WordTrace tailWord_2635826 prefixEnd_2635826 1353445659617909552353063 := by
  unfold tailWord_2635826
  simp only [CollatzResearch.WordTrace]
  refine ⟨24034118037215010021645833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64090981432573360057722221 24034118037215010021645833)
  ·
    refine ⟨18025588527911257516234375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24034118037215010021645833 18025588527911257516234375)
    ·
      refine ⟨27038382791866886274351563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18025588527911257516234375 27038382791866886274351563)
      ·
        refine ⟨40557574187800329411527345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27038382791866886274351563 40557574187800329411527345)
        ·
          refine ⟨30418180640850247058645509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40557574187800329411527345 30418180640850247058645509)
          ·
            refine ⟨5703408870159421323496033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30418180640850247058645509 5703408870159421323496033)
            ·
              refine ⟨4277556652619565992622025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5703408870159421323496033 4277556652619565992622025)
              ·
                refine ⟨3208167489464674494466519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4277556652619565992622025 3208167489464674494466519)
                ·
                  refine ⟨4812251234197011741699779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3208167489464674494466519 4812251234197011741699779)
                  ·
                    refine ⟨7218376851295517612549669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4812251234197011741699779 7218376851295517612549669)
                    ·
                      refine ⟨1353445659617909552353063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7218376851295517612549669 1353445659617909552353063)
                      ·
                        rfl

theorem cell23_2635826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2, 2, 1, 1, 4].length) (baseStart_2635826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2635826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2635826 prefixEnd_2635826 := by exact prefixLift 2635826
  have htrace : WordTrace (prefixWord ++ tailWord_2635826) baseStart_2635826 baseEnd_2635826 := by
    simpa [prefixWord, tailWord_2635826, baseEnd_2635826] using wordTrace_append hprefix tailTrace_2635826
  have hstable : (prefixWord ++ tailWord_2635826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2635826).length < 2 ^ (prefixWord ++ tailWord_2635826).sum := by decide
  have hdescent : baseEnd_2635826 < baseStart_2635826 := by decide
  rcases family_descends (prefixWord ++ tailWord_2635826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2635829 : List Nat := [1, 3, 3, 1, 1, 1, 2, 3, 3, 2, 3]
def baseStart_2635829 : Nat := 118140960795 + 2635829 * 2 ^ 59
def prefixEnd_2635829 : Nat := 4983230072969 + 3 ^ 40 * 2635829 * 2
def baseEnd_2635829 : Nat := 1353447200059873040615549

theorem tailTrace_2635829 : CollatzResearch.WordTrace tailWord_2635829 prefixEnd_2635829 1353447200059873040615549 := by
  unfold tailWord_2635829
  simp only [CollatzResearch.WordTrace]
  refine ⟨96136581567849171598942541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64091054378566114399295027 96136581567849171598942541)
  ·
    refine ⟨36051218087943439349603453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96136581567849171598942541 36051218087943439349603453)
    ·
      refine ⟨13519206782978789756101295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36051218087943439349603453 13519206782978789756101295)
      ·
        refine ⟨20278810174468184634151943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13519206782978789756101295 20278810174468184634151943)
        ·
          refine ⟨30418215261702276951227915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20278810174468184634151943 30418215261702276951227915)
          ·
            refine ⟨45627322892553415426841873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30418215261702276951227915 45627322892553415426841873)
            ·
              refine ⟨34220492169415061570131405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45627322892553415426841873 34220492169415061570131405)
              ·
                refine ⟨12832684563530648088799277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34220492169415061570131405 12832684563530648088799277)
                ·
                  refine ⟨4812256711323993033299729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12832684563530648088799277 4812256711323993033299729)
                  ·
                    refine ⟨3609192533492994774974797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4812256711323993033299729 3609192533492994774974797)
                    ·
                      refine ⟨1353447200059873040615549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3609192533492994774974797 1353447200059873040615549)
                      ·
                        rfl

theorem cell23_2635829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 3, 3, 2, 3].length) (baseStart_2635829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2635829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2635829 prefixEnd_2635829 := by exact prefixLift 2635829
  have htrace : WordTrace (prefixWord ++ tailWord_2635829) baseStart_2635829 baseEnd_2635829 := by
    simpa [prefixWord, tailWord_2635829, baseEnd_2635829] using wordTrace_append hprefix tailTrace_2635829
  have hstable : (prefixWord ++ tailWord_2635829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2635829).length < 2 ^ (prefixWord ++ tailWord_2635829).sum := by decide
  have hdescent : baseEnd_2635829 < baseStart_2635829 := by decide
  rcases family_descends (prefixWord ++ tailWord_2635829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2635843 : List Nat := [1, 1, 1, 3, 1, 2, 2, 7, 1, 2, 2]
def baseStart_2635843 : Nat := 118140960795 + 2635843 * 2 ^ 59
def prefixEnd_2635843 : Nat := 4983230072969 + 3 ^ 40 * 2635843 * 2
def baseEnd_2635843 : Nat := 1353454388789035985840485

theorem tailTrace_2635843 : CollatzResearch.WordTrace tailWord_2635843 prefixEnd_2635843 1353454388789035985840485 := by
  unfold tailWord_2635843
  simp only [CollatzResearch.WordTrace]
  refine ⟨96137092189798451989952183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64091394793198967993301455 96137092189798451989952183)
  ·
    refine ⟨144205638284697677984928275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96137092189798451989952183 144205638284697677984928275)
    ·
      refine ⟨216308457427046516977392413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144205638284697677984928275 216308457427046516977392413)
      ·
        refine ⟨81115671535142443866522155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 216308457427046516977392413 81115671535142443866522155)
        ·
          refine ⟨121673507302713665799783233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81115671535142443866522155 121673507302713665799783233)
          ·
            refine ⟨91255130477035249349837425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121673507302713665799783233 91255130477035249349837425)
            ·
              refine ⟨68441347857776437012378069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91255130477035249349837425 68441347857776437012378069)
              ·
                refine ⟨1604094090416635242477611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 68441347857776437012378069 1604094090416635242477611)
                ·
                  refine ⟨2406141135624952863716417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1604094090416635242477611 2406141135624952863716417)
                  ·
                    refine ⟨1804605851718714647787313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2406141135624952863716417 1804605851718714647787313)
                    ·
                      refine ⟨1353454388789035985840485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1804605851718714647787313 1353454388789035985840485)
                      ·
                        rfl

theorem cell23_2635843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 7, 1, 2, 2].length) (baseStart_2635843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2635843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2635843 prefixEnd_2635843 := by exact prefixLift 2635843
  have htrace : WordTrace (prefixWord ++ tailWord_2635843) baseStart_2635843 baseEnd_2635843 := by
    simpa [prefixWord, tailWord_2635843, baseEnd_2635843] using wordTrace_append hprefix tailTrace_2635843
  have hstable : (prefixWord ++ tailWord_2635843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2635843).length < 2 ^ (prefixWord ++ tailWord_2635843).sum := by decide
  have hdescent : baseEnd_2635843 < baseStart_2635843 := by decide
  rcases family_descends (prefixWord ++ tailWord_2635843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2635859 : List Nat := [1, 1, 1, 2, 1, 1, 2, 2, 8, 1, 3]
def baseStart_2635859 : Nat := 118140960795 + 2635859 * 2 ^ 59
def prefixEnd_2635859 : Nat := 4983230072969 + 3 ^ 40 * 2635859 * 2
def baseEnd_2635859 : Nat := 1353462604479507923240411

theorem tailTrace_2635859 : CollatzResearch.WordTrace tailWord_2635859 prefixEnd_2635859 1353462604479507923240411 := by
  unfold tailWord_2635859
  simp only [CollatzResearch.WordTrace]
  refine ⟨96137675757740486722534631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64091783838493657815023087 96137675757740486722534631)
  ·
    refine ⟨144206513636610730083801947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96137675757740486722534631 144206513636610730083801947)
    ·
      refine ⟨216309770454916095125702921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144206513636610730083801947 216309770454916095125702921)
      ·
        refine ⟨162232327841187071344277191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 216309770454916095125702921 162232327841187071344277191)
        ·
          refine ⟨243348491761780607016415787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162232327841187071344277191 243348491761780607016415787)
          ·
            refine ⟨365022737642670910524623681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 243348491761780607016415787 365022737642670910524623681)
            ·
              refine ⟨273767053232003182893467761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 365022737642670910524623681 273767053232003182893467761)
              ·
                refine ⟨205325289924002387170100821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 273767053232003182893467761 205325289924002387170100821)
                ·
                  refine ⟨2406155741296902974649619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 205325289924002387170100821 2406155741296902974649619)
                  ·
                    refine ⟨3609233611945354461974429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2406155741296902974649619 3609233611945354461974429)
                    ·
                      refine ⟨1353462604479507923240411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3609233611945354461974429 1353462604479507923240411)
                      ·
                        rfl

theorem cell23_2635859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 8, 1, 3].length) (baseStart_2635859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2635859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2635859 prefixEnd_2635859 := by exact prefixLift 2635859
  have htrace : WordTrace (prefixWord ++ tailWord_2635859) baseStart_2635859 baseEnd_2635859 := by
    simpa [prefixWord, tailWord_2635859, baseEnd_2635859] using wordTrace_append hprefix tailTrace_2635859
  have hstable : (prefixWord ++ tailWord_2635859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2635859).length < 2 ^ (prefixWord ++ tailWord_2635859).sum := by decide
  have hdescent : baseEnd_2635859 < baseStart_2635859 := by decide
  rcases family_descends (prefixWord ++ tailWord_2635859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2635933 : List Nat := [1, 4, 2, 1, 1, 4, 2, 1, 1, 4, 2]
def baseStart_2635933 : Nat := 118140960795 + 2635933 * 2 ^ 59
def prefixEnd_2635933 : Nat := 4983230072969 + 3 ^ 40 * 2635933 * 2
def baseEnd_2635933 : Nat := 1353500602047940633715071

theorem tailTrace_2635933 : CollatzResearch.WordTrace tailWord_2635933 prefixEnd_2635933 1353500602047940633715071 := by
  unfold tailWord_2635933
  simp only [CollatzResearch.WordTrace]
  refine ⟨96140374759472397360728453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64093583172981598240485635 96140374759472397360728453)
  ·
    refine ⟨18026320267401074505136585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96140374759472397360728453 18026320267401074505136585)
    ·
      refine ⟨13519740200550805878852439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18026320267401074505136585 13519740200550805878852439)
      ·
        refine ⟨20279610300826208818278659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13519740200550805878852439 20279610300826208818278659)
        ·
          refine ⟨30419415451239313227417989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20279610300826208818278659 30419415451239313227417989)
          ·
            refine ⟨5703640397107371230140873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30419415451239313227417989 5703640397107371230140873)
            ·
              refine ⟨4277730297830528422605655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5703640397107371230140873 4277730297830528422605655)
              ·
                refine ⟨6416595446745792633908483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4277730297830528422605655 6416595446745792633908483)
                ·
                  refine ⟨9624893170118688950862725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6416595446745792633908483 9624893170118688950862725)
                  ·
                    refine ⟨1804667469397254178286761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9624893170118688950862725 1804667469397254178286761)
                    ·
                      refine ⟨1353500602047940633715071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1804667469397254178286761 1353500602047940633715071)
                      ·
                        rfl

theorem cell23_2635933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2, 1, 1, 4, 2].length) (baseStart_2635933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2635933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2635933 prefixEnd_2635933 := by exact prefixLift 2635933
  have htrace : WordTrace (prefixWord ++ tailWord_2635933) baseStart_2635933 baseEnd_2635933 := by
    simpa [prefixWord, tailWord_2635933, baseEnd_2635933] using wordTrace_append hprefix tailTrace_2635933
  have hstable : (prefixWord ++ tailWord_2635933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2635933).length < 2 ^ (prefixWord ++ tailWord_2635933).sum := by decide
  have hdescent : baseEnd_2635933 < baseStart_2635933 := by decide
  rcases family_descends (prefixWord ++ tailWord_2635933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2636026 : List Nat := [3, 1, 1, 1, 1, 5, 1, 1, 4, 2, 3]
def baseStart_2636026 : Nat := 118140960795 + 2636026 * 2 ^ 59
def prefixEnd_2636026 : Nat := 4983230072969 + 3 ^ 40 * 2636026 * 2
def baseEnd_2636026 : Nat := 1353548355748808769852143

theorem tailTrace_2636026 : CollatzResearch.WordTrace tailWord_2636026 prefixEnd_2636026 1353548355748808769852143 := by
  unfold tailWord_2636026
  simp only [CollatzResearch.WordTrace]
  refine ⟨24035941687033868560965983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64095844498756982829242621 24035941687033868560965983)
  ·
    refine ⟨36053912530550802841448975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24035941687033868560965983 36053912530550802841448975)
    ·
      refine ⟨54080868795826204262173463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36053912530550802841448975 54080868795826204262173463)
      ·
        refine ⟨81121303193739306393260195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54080868795826204262173463 81121303193739306393260195)
        ·
          refine ⟨121681954790608959589890293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81121303193739306393260195 121681954790608959589890293)
          ·
            refine ⟨11407683261619589961552215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 121681954790608959589890293 11407683261619589961552215)
            ·
              refine ⟨17111524892429384942328323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11407683261619589961552215 17111524892429384942328323)
              ·
                refine ⟨25667287338644077413492485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17111524892429384942328323 25667287338644077413492485)
                ·
                  refine ⟨4812616375995764515029841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25667287338644077413492485 4812616375995764515029841)
                  ·
                    refine ⟨3609462281996823386272381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4812616375995764515029841 3609462281996823386272381)
                    ·
                      refine ⟨1353548355748808769852143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3609462281996823386272381 1353548355748808769852143)
                      ·
                        rfl

theorem cell23_2636026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 1, 4, 2, 3].length) (baseStart_2636026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2636026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2636026 prefixEnd_2636026 := by exact prefixLift 2636026
  have htrace : WordTrace (prefixWord ++ tailWord_2636026) baseStart_2636026 baseEnd_2636026 := by
    simpa [prefixWord, tailWord_2636026, baseEnd_2636026] using wordTrace_append hprefix tailTrace_2636026
  have hstable : (prefixWord ++ tailWord_2636026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2636026).length < 2 ^ (prefixWord ++ tailWord_2636026).sum := by decide
  have hdescent : baseEnd_2636026 < baseStart_2636026 := by decide
  rcases family_descends (prefixWord ++ tailWord_2636026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2636046 : List Nat := [4, 1, 1, 2, 1, 2, 3, 3, 6]
def baseStart_2636046 : Nat := 118140960795 + 2636046 * 2 ^ 59
def prefixEnd_2636046 : Nat := 4983230072969 + 3 ^ 40 * 2636046 * 2
def baseEnd_2636046 : Nat := 150395402817988743511339

theorem tailTrace_2636046 : CollatzResearch.WordTrace tailWord_2636046 prefixEnd_2636046 150395402817988743511339 := by
  unfold tailWord_2636046
  simp only [CollatzResearch.WordTrace]
  refine ⟨12018062026007877207448999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64096330805375345106394661 12018062026007877207448999)
  ·
    refine ⟨18027093039011815811173499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12018062026007877207448999 18027093039011815811173499)
    ·
      refine ⟨27040639558517723716760249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18027093039011815811173499 27040639558517723716760249)
      ·
        refine ⟨20280479668888292787570187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27040639558517723716760249 20280479668888292787570187)
        ·
          refine ⟨30420719503332439181355281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20280479668888292787570187 30420719503332439181355281)
          ·
            refine ⟨22815539627499329386016461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30420719503332439181355281 22815539627499329386016461)
            ·
              refine ⟨8555827360312248519756173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22815539627499329386016461 8555827360312248519756173)
              ·
                refine ⟨3208435260117093194908565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8555827360312248519756173 3208435260117093194908565)
                ·
                  refine ⟨150395402817988743511339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3208435260117093194908565 150395402817988743511339)
                  ·
                    rfl

theorem cell23_2636046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 3, 6].length) (baseStart_2636046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2636046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2636046 prefixEnd_2636046 := by exact prefixLift 2636046
  have htrace : WordTrace (prefixWord ++ tailWord_2636046) baseStart_2636046 baseEnd_2636046 := by
    simpa [prefixWord, tailWord_2636046, baseEnd_2636046] using wordTrace_append hprefix tailTrace_2636046
  have hstable : (prefixWord ++ tailWord_2636046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2636046).length < 2 ^ (prefixWord ++ tailWord_2636046).sum := by decide
  have hdescent : baseEnd_2636046 < baseStart_2636046 := by decide
  rcases family_descends (prefixWord ++ tailWord_2636046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2636076 : List Nat := [2, 2, 1, 1, 1, 3, 2, 5, 1, 5]
def baseStart_2636076 : Nat := 118140960795 + 2636076 * 2 ^ 59
def prefixEnd_2636076 : Nat := 4983230072969 + 3 ^ 40 * 2636076 * 2
def baseEnd_2636076 : Nat := 451191343260511191408971

theorem tailTrace_2636076 : CollatzResearch.WordTrace tailWord_2636076 prefixEnd_2636076 451191343260511191408971 := by
  unfold tailWord_2636076
  simp only [CollatzResearch.WordTrace]
  refine ⟨48072795198977166391592041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64097060265302888522122721 48072795198977166391592041)
  ·
    refine ⟨36054596399232874793694031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48072795198977166391592041 36054596399232874793694031)
    ·
      refine ⟨54081894598849312190541047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36054596399232874793694031 54081894598849312190541047)
      ·
        refine ⟨81122841898273968285811571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54081894598849312190541047 81122841898273968285811571)
        ·
          refine ⟨121684262847410952428717357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81122841898273968285811571 121684262847410952428717357)
          ·
            refine ⟨45631598567779107160769009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 121684262847410952428717357 45631598567779107160769009)
            ·
              refine ⟨34223698925834330370576757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45631598567779107160769009 34223698925834330370576757)
              ·
                refine ⟨3208471774296968472241571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34223698925834330370576757 3208471774296968472241571)
                ·
                  refine ⟨4812707661445452708362357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3208471774296968472241571 4812707661445452708362357)
                  ·
                    refine ⟨451191343260511191408971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4812707661445452708362357 451191343260511191408971)
                    ·
                      rfl

theorem cell23_2636076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 5].length) (baseStart_2636076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2636076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2636076 prefixEnd_2636076 := by exact prefixLift 2636076
  have htrace : WordTrace (prefixWord ++ tailWord_2636076) baseStart_2636076 baseEnd_2636076 := by
    simpa [prefixWord, tailWord_2636076, baseEnd_2636076] using wordTrace_append hprefix tailTrace_2636076
  have hstable : (prefixWord ++ tailWord_2636076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2636076).length < 2 ^ (prefixWord ++ tailWord_2636076).sum := by decide
  have hdescent : baseEnd_2636076 < baseStart_2636076 := by decide
  rcases family_descends (prefixWord ++ tailWord_2636076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2636083 : List Nat := [1, 1, 1, 2, 5, 1, 1, 4, 2, 3, 2]
def baseStart_2636083 : Nat := 118140960795 + 2636083 * 2 ^ 59
def prefixEnd_2636083 : Nat := 4983230072969 + 3 ^ 40 * 2636083 * 2
def baseEnd_2636083 : Nat := 1353577624146115046839381

theorem tailTrace_2636083 : CollatzResearch.WordTrace tailWord_2636083 prefixEnd_2636083 1353577624146115046839381 := by
  unfold tailWord_2636083
  simp only [CollatzResearch.WordTrace]
  refine ⟨96145845708928972978688903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64097230472619315319125935 96145845708928972978688903)
  ·
    refine ⟨144218768563393459468033355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96145845708928972978688903 144218768563393459468033355)
    ·
      refine ⟨216328152845090189202050033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144218768563393459468033355 216328152845090189202050033)
      ·
        refine ⟨162246114633817641901537525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 216328152845090189202050033 162246114633817641901537525)
        ·
          refine ⟨15210573246920403928269143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 162246114633817641901537525 15210573246920403928269143)
          ·
            refine ⟨22815859870380605892403715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15210573246920403928269143 22815859870380605892403715)
            ·
              refine ⟨34223789805570908838605573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22815859870380605892403715 34223789805570908838605573)
              ·
                refine ⟨6416960588544545407238545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34223789805570908838605573 6416960588544545407238545)
                ·
                  refine ⟨4812720441408409055428909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6416960588544545407238545 4812720441408409055428909)
                  ·
                    refine ⟨1804770165528153395785841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4812720441408409055428909 1804770165528153395785841)
                    ·
                      refine ⟨1353577624146115046839381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1804770165528153395785841 1353577624146115046839381)
                      ·
                        rfl

theorem cell23_2636083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 4, 2, 3, 2].length) (baseStart_2636083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2636083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2636083 prefixEnd_2636083 := by exact prefixLift 2636083
  have htrace : WordTrace (prefixWord ++ tailWord_2636083) baseStart_2636083 baseEnd_2636083 := by
    simpa [prefixWord, tailWord_2636083, baseEnd_2636083] using wordTrace_append hprefix tailTrace_2636083
  have hstable : (prefixWord ++ tailWord_2636083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2636083).length < 2 ^ (prefixWord ++ tailWord_2636083).sum := by decide
  have hdescent : baseEnd_2636083 < baseStart_2636083 := by decide
  rcases family_descends (prefixWord ++ tailWord_2636083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2636084 : List Nat := [2, 5, 1, 1, 1, 4, 2, 2, 1, 4]
def baseStart_2636084 : Nat := 118140960795 + 2636084 * 2 ^ 59
def prefixEnd_2636084 : Nat := 4983230072969 + 3 ^ 40 * 2636084 * 2
def baseEnd_2636084 : Nat := 451192712542256514308959

theorem tailTrace_2636084 : CollatzResearch.WordTrace tailWord_2636084 prefixEnd_2636084 451192712542256514308959 := by
  unfold tailWord_2636084
  simp only [CollatzResearch.WordTrace]
  refine ⟨48072941090962675074737653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64097254787950233432983537 48072941090962675074737653)
  ·
    refine ⟨4506838227277750788256655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 48072941090962675074737653 4506838227277750788256655)
    ·
      refine ⟨6760257340916626182384983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4506838227277750788256655 6760257340916626182384983)
      ·
        refine ⟨10140386011374939273577475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6760257340916626182384983 10140386011374939273577475)
        ·
          refine ⟨15210579017062408910366213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10140386011374939273577475 15210579017062408910366213)
          ·
            refine ⟨2851983565699201670693665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15210579017062408910366213 2851983565699201670693665)
            ·
              refine ⟨2138987674274401253020249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2851983565699201670693665 2138987674274401253020249)
              ·
                refine ⟨1604240755705800939765187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2138987674274401253020249 1604240755705800939765187)
                ·
                  refine ⟨2406361133558701409647781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1604240755705800939765187 2406361133558701409647781)
                  ·
                    refine ⟨451192712542256514308959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2406361133558701409647781 451192712542256514308959)
                    ·
                      rfl

theorem cell23_2636084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 2, 2, 1, 4].length) (baseStart_2636084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2636084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2636084 prefixEnd_2636084 := by exact prefixLift 2636084
  have htrace : WordTrace (prefixWord ++ tailWord_2636084) baseStart_2636084 baseEnd_2636084 := by
    simpa [prefixWord, tailWord_2636084, baseEnd_2636084] using wordTrace_append hprefix tailTrace_2636084
  have hstable : (prefixWord ++ tailWord_2636084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2636084).length < 2 ^ (prefixWord ++ tailWord_2636084).sum := by decide
  have hdescent : baseEnd_2636084 < baseStart_2636084 := by decide
  rcases family_descends (prefixWord ++ tailWord_2636084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2636106 : List Nat := [3, 1, 2, 1, 1, 1, 1, 1, 8, 4]
def baseStart_2636106 : Nat := 118140960795 + 2636106 * 2 ^ 59
def prefixEnd_2636106 : Nat := 4983230072969 + 3 ^ 40 * 2636106 * 2
def baseEnd_2636106 : Nat := 451196478067056152283925

theorem tailTrace_2636106 : CollatzResearch.WordTrace tailWord_2636106 prefixEnd_2636106 451196478067056152283925 := by
  unfold tailWord_2636106
  simp only [CollatzResearch.WordTrace]
  refine ⟨24036671146961411976694043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64097789725230431937850781 24036671146961411976694043)
  ·
    refine ⟨36055006720442117965041065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24036671146961411976694043 36055006720442117965041065)
    ·
      refine ⟨27041255040331588473780799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36055006720442117965041065 27041255040331588473780799)
      ·
        refine ⟨40561882560497382710671199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27041255040331588473780799 40561882560497382710671199)
        ·
          refine ⟨60842823840746074066006799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40561882560497382710671199 60842823840746074066006799)
          ·
            refine ⟨91264235761119111099010199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60842823840746074066006799 91264235761119111099010199)
            ·
              refine ⟨136896353641678666648515299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91264235761119111099010199 136896353641678666648515299)
              ·
                refine ⟨205344530462517999972772949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 136896353641678666648515299 205344530462517999972772949)
                ·
                  refine ⟨2406381216357632812180933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 205344530462517999972772949 2406381216357632812180933)
                  ·
                    refine ⟨451196478067056152283925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2406381216357632812180933 451196478067056152283925)
                    ·
                      rfl

theorem cell23_2636106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 8, 4].length) (baseStart_2636106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2636106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2636106 prefixEnd_2636106 := by exact prefixLift 2636106
  have htrace : WordTrace (prefixWord ++ tailWord_2636106) baseStart_2636106 baseEnd_2636106 := by
    simpa [prefixWord, tailWord_2636106, baseEnd_2636106] using wordTrace_append hprefix tailTrace_2636106
  have hstable : (prefixWord ++ tailWord_2636106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2636106).length < 2 ^ (prefixWord ++ tailWord_2636106).sum := by decide
  have hdescent : baseEnd_2636106 < baseStart_2636106 := by decide
  rcases family_descends (prefixWord ++ tailWord_2636106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2636117 : List Nat := [1, 3, 2, 2, 4, 2, 1, 1, 2, 3, 2]
def baseStart_2636117 : Nat := 118140960795 + 2636117 * 2 ^ 59
def prefixEnd_2636117 : Nat := 4983230072969 + 3 ^ 40 * 2636117 * 2
def baseEnd_2636117 : Nat := 1353595082488367913814225

theorem tailTrace_2636117 : CollatzResearch.WordTrace tailWord_2636117 prefixEnd_2636117 1353595082488367913814225 := by
  unfold tailWord_2636117
  simp only [CollatzResearch.WordTrace]
  refine ⟨96147085790805796785426605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64098057193870531190284403 96147085790805796785426605)
  ·
    refine ⟨36055157171552173794534977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96147085790805796785426605 36055157171552173794534977)
    ·
      refine ⟨27041367878664130345901233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36055157171552173794534977 27041367878664130345901233)
      ·
        refine ⟨20281025908998097759425925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27041367878664130345901233 20281025908998097759425925)
        ·
          refine ⟨3802692357937143329892361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20281025908998097759425925 3802692357937143329892361)
          ·
            refine ⟨2852019268452857497419271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3802692357937143329892361 2852019268452857497419271)
            ·
              refine ⟨4278028902679286246128907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2852019268452857497419271 4278028902679286246128907)
              ·
                refine ⟨6417043354018929369193361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4278028902679286246128907 6417043354018929369193361)
                ·
                  refine ⟨4812782515514197026895021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6417043354018929369193361 4812782515514197026895021)
                  ·
                    refine ⟨1804793443317823885085633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4812782515514197026895021 1804793443317823885085633)
                    ·
                      refine ⟨1353595082488367913814225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1804793443317823885085633 1353595082488367913814225)
                      ·
                        rfl

theorem cell23_2636117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 1, 1, 2, 3, 2].length) (baseStart_2636117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2636117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2636117 prefixEnd_2636117 := by exact prefixLift 2636117
  have htrace : WordTrace (prefixWord ++ tailWord_2636117) baseStart_2636117 baseEnd_2636117 := by
    simpa [prefixWord, tailWord_2636117, baseEnd_2636117] using wordTrace_append hprefix tailTrace_2636117
  have hstable : (prefixWord ++ tailWord_2636117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2636117).length < 2 ^ (prefixWord ++ tailWord_2636117).sum := by decide
  have hdescent : baseEnd_2636117 < baseStart_2636117 := by decide
  rcases family_descends (prefixWord ++ tailWord_2636117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2636130 : List Nat := [3, 3, 2, 1, 1, 3, 1, 3, 1, 1, 4]
def baseStart_2636130 : Nat := 118140960795 + 2636130 * 2 ^ 59
def prefixEnd_2636130 : Nat := 4983230072969 + 3 ^ 40 * 2636130 * 2
def baseEnd_2636130 : Nat := 1353601757736876362951665

theorem tailTrace_2636130 : CollatzResearch.WordTrace tailWord_2636130 prefixEnd_2636130 1353601757736876362951665 := by
  unfold tailWord_2636130
  simp only [CollatzResearch.WordTrace]
  refine ⟨24036889984939675001412461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64098373293172466670433229 24036889984939675001412461)
  ·
    refine ⟨9013833744352378125529673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24036889984939675001412461 9013833744352378125529673)
    ·
      refine ⟨6760375308264283594147255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9013833744352378125529673 6760375308264283594147255)
      ·
        refine ⟨10140562962396425391220883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6760375308264283594147255 10140562962396425391220883)
        ·
          refine ⟨15210844443594638086831325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10140562962396425391220883 15210844443594638086831325)
          ·
            refine ⟨5704066666347989282561747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15210844443594638086831325 5704066666347989282561747)
            ·
              refine ⟨8556099999521983923842621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5704066666347989282561747 8556099999521983923842621)
              ·
                refine ⟨3208537499820743971440983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8556099999521983923842621 3208537499820743971440983)
                ·
                  refine ⟨4812806249731115957161475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3208537499820743971440983 4812806249731115957161475)
                  ·
                    refine ⟨7219209374596673935742213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4812806249731115957161475 7219209374596673935742213)
                    ·
                      refine ⟨1353601757736876362951665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7219209374596673935742213 1353601757736876362951665)
                      ·
                        rfl

theorem cell23_2636130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 3, 1, 1, 4].length) (baseStart_2636130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2636130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2636130 prefixEnd_2636130 := by exact prefixLift 2636130
  have htrace : WordTrace (prefixWord ++ tailWord_2636130) baseStart_2636130 baseEnd_2636130 := by
    simpa [prefixWord, tailWord_2636130, baseEnd_2636130] using wordTrace_append hprefix tailTrace_2636130
  have hstable : (prefixWord ++ tailWord_2636130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2636130).length < 2 ^ (prefixWord ++ tailWord_2636130).sum := by decide
  have hdescent : baseEnd_2636130 < baseStart_2636130 := by decide
  rcases family_descends (prefixWord ++ tailWord_2636130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2636136 : List Nat := [2, 1, 4, 2, 2, 2, 10]
def baseStart_2636136 : Nat := 118140960795 + 2636136 * 2 ^ 59
def prefixEnd_2636136 : Nat := 4983230072969 + 3 ^ 40 * 2636136 * 2
def baseEnd_2636136 : Nat := 16711170847170411598477

theorem tailTrace_2636136 : CollatzResearch.WordTrace tailWord_2636136 prefixEnd_2636136 16711170847170411598477 := by
  unfold tailWord_2636136
  simp only [CollatzResearch.WordTrace]
  refine ⟨48073889388868481515184131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64098519185157975353578841 48073889388868481515184131)
  ·
    refine ⟨72110834083302722272776197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48073889388868481515184131 72110834083302722272776197)
    ·
      refine ⟨13520781390619260426145537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72110834083302722272776197 13520781390619260426145537)
      ·
        refine ⟨10140586042964445319609153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13520781390619260426145537 10140586042964445319609153)
        ·
          refine ⟨7605439532223333989706865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10140586042964445319609153 7605439532223333989706865)
          ·
            refine ⟨5704079649167500492280149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7605439532223333989706865 5704079649167500492280149)
            ·
              refine ⟨16711170847170411598477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5704079649167500492280149 16711170847170411598477)
              ·
                rfl

theorem cell23_2636136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 10].length) (baseStart_2636136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2636136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2636136 prefixEnd_2636136 := by exact prefixLift 2636136
  have htrace : WordTrace (prefixWord ++ tailWord_2636136) baseStart_2636136 baseEnd_2636136 := by
    simpa [prefixWord, tailWord_2636136, baseEnd_2636136] using wordTrace_append hprefix tailTrace_2636136
  have hstable : (prefixWord ++ tailWord_2636136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2636136).length < 2 ^ (prefixWord ++ tailWord_2636136).sum := by decide
  have hdescent : baseEnd_2636136 < baseStart_2636136 := by decide
  rcases family_descends (prefixWord ++ tailWord_2636136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2636196 : List Nat := [2, 3, 1, 2, 1, 1, 2, 1, 4, 6]
def baseStart_2636196 : Nat := 118140960795 + 2636196 * 2 ^ 59
def prefixEnd_2636196 : Nat := 4983230072969 + 3 ^ 40 * 2636196 * 2
def baseEnd_2636196 : Nat := 451211882486691034908787

theorem tailTrace_2636196 : CollatzResearch.WordTrace tailWord_2636196 prefixEnd_2636196 451211882486691034908787 := by
  unfold tailWord_2636196
  simp only [CollatzResearch.WordTrace]
  refine ⟨48074983578759796638776221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64099978105013062185034961 48074983578759796638776221)
  ·
    refine ⟨18028118842034923739541083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48074983578759796638776221 18028118842034923739541083)
    ·
      refine ⟨27042178263052385609311625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18028118842034923739541083 27042178263052385609311625)
      ·
        refine ⟨20281633697289289206983719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27042178263052385609311625 20281633697289289206983719)
        ·
          refine ⟨30422450545933933810475579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20281633697289289206983719 30422450545933933810475579)
          ·
            refine ⟨45633675818900900715713369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30422450545933933810475579 45633675818900900715713369)
            ·
              refine ⟨34225256864175675536785027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45633675818900900715713369 34225256864175675536785027)
              ·
                refine ⟨51337885296263513305177541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34225256864175675536785027 51337885296263513305177541)
                ·
                  refine ⟨9625853493049408744720789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51337885296263513305177541 9625853493049408744720789)
                  ·
                    refine ⟨451211882486691034908787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9625853493049408744720789 451211882486691034908787)
                    ·
                      rfl

theorem cell23_2636196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 4, 6].length) (baseStart_2636196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2636196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2636196 prefixEnd_2636196 := by exact prefixLift 2636196
  have htrace : WordTrace (prefixWord ++ tailWord_2636196) baseStart_2636196 baseEnd_2636196 := by
    simpa [prefixWord, tailWord_2636196, baseEnd_2636196] using wordTrace_append hprefix tailTrace_2636196
  have hstable : (prefixWord ++ tailWord_2636196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2636196).length < 2 ^ (prefixWord ++ tailWord_2636196).sum := by decide
  have hdescent : baseEnd_2636196 < baseStart_2636196 := by decide
  rcases family_descends (prefixWord ++ tailWord_2636196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2636216 : List Nat := [2, 1, 2, 1, 2, 2, 1, 3, 1, 4, 4]
def baseStart_2636216 : Nat := 118140960795 + 2636216 * 2 ^ 59
def prefixEnd_2636216 : Nat := 4983230072969 + 3 ^ 40 * 2636216 * 2
def baseEnd_2636216 : Nat := 1353645917073163026476269

theorem tailTrace_2636216 : CollatzResearch.WordTrace tailWord_2636216 prefixEnd_2636216 1353645917073163026476269 := by
  unfold tailWord_2636216
  simp only [CollatzResearch.WordTrace]
  refine ⟨48075348308723568346640251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64100464411631424462187001 48075348308723568346640251)
  ·
    refine ⟨72113022463085352519960377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48075348308723568346640251 72113022463085352519960377)
    ·
      refine ⟨54084766847314014389970283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72113022463085352519960377 54084766847314014389970283)
      ·
        refine ⟨81127150270971021584955425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54084766847314014389970283 81127150270971021584955425)
        ·
          refine ⟨60845362703228266188716569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81127150270971021584955425 60845362703228266188716569)
          ·
            refine ⟨45634022027421199641537427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60845362703228266188716569 45634022027421199641537427)
            ·
              refine ⟨68451033041131799462306141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45634022027421199641537427 68451033041131799462306141)
              ·
                refine ⟨25669137390424424798364803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68451033041131799462306141 25669137390424424798364803)
                ·
                  refine ⟨38503706085636637197547205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25669137390424424798364803 38503706085636637197547205)
                  ·
                    refine ⟨7219444891056869474540101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38503706085636637197547205 7219444891056869474540101)
                    ·
                      refine ⟨1353645917073163026476269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7219444891056869474540101 1353645917073163026476269)
                      ·
                        rfl

theorem cell23_2636216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 3, 1, 4, 4].length) (baseStart_2636216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2636216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2636216 prefixEnd_2636216 := by exact prefixLift 2636216
  have htrace : WordTrace (prefixWord ++ tailWord_2636216) baseStart_2636216 baseEnd_2636216 := by
    simpa [prefixWord, tailWord_2636216, baseEnd_2636216] using wordTrace_append hprefix tailTrace_2636216
  have hstable : (prefixWord ++ tailWord_2636216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2636216).length < 2 ^ (prefixWord ++ tailWord_2636216).sum := by decide
  have hdescent : baseEnd_2636216 < baseStart_2636216 := by decide
  rcases family_descends (prefixWord ++ tailWord_2636216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2636270 : List Nat := [4, 1, 2, 1, 2, 3, 1, 1, 2, 3, 3]
def baseStart_2636270 : Nat := 118140960795 + 2636270 * 2 ^ 59
def prefixEnd_2636270 : Nat := 4983230072969 + 3 ^ 40 * 2636270 * 2
def baseEnd_2636270 : Nat := 1353673645028505815201021

theorem tailTrace_2636270 : CollatzResearch.WordTrace tailWord_2636270 prefixEnd_2636270 1353673645028505815201021 := by
  unfold tailWord_2636270
  simp only [CollatzResearch.WordTrace]
  refine ⟨12019083269906437989468283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64101777439501002610497509 12019083269906437989468283)
  ·
    refine ⟨18028624904859656984202425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12019083269906437989468283 18028624904859656984202425)
    ·
      refine ⟨13521468678644742738151819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18028624904859656984202425 13521468678644742738151819)
      ·
        refine ⟨20282203017967114107227729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13521468678644742738151819 20282203017967114107227729)
        ·
          refine ⟨15211652263475335580420797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20282203017967114107227729 15211652263475335580420797)
          ·
            refine ⟨5704369598803250842657799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15211652263475335580420797 5704369598803250842657799)
            ·
              refine ⟨8556554398204876263986699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5704369598803250842657799 8556554398204876263986699)
              ·
                refine ⟨12834831597307314395980049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8556554398204876263986699 12834831597307314395980049)
                ·
                  refine ⟨9626123697980485796985037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12834831597307314395980049 9626123697980485796985037)
                  ·
                    refine ⟨3609796386742682173869389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9626123697980485796985037 3609796386742682173869389)
                    ·
                      refine ⟨1353673645028505815201021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3609796386742682173869389 1353673645028505815201021)
                      ·
                        rfl

theorem cell23_2636270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 1, 2, 3, 3].length) (baseStart_2636270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2636270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2636270 prefixEnd_2636270 := by exact prefixLift 2636270
  have htrace : WordTrace (prefixWord ++ tailWord_2636270) baseStart_2636270 baseEnd_2636270 := by
    simpa [prefixWord, tailWord_2636270, baseEnd_2636270] using wordTrace_append hprefix tailTrace_2636270
  have hstable : (prefixWord ++ tailWord_2636270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2636270).length < 2 ^ (prefixWord ++ tailWord_2636270).sum := by decide
  have hdescent : baseEnd_2636270 < baseStart_2636270 := by decide
  rcases family_descends (prefixWord ++ tailWord_2636270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2636330 : List Nat := [3, 1, 4, 1, 1, 2, 1, 2, 1, 4, 3]
def baseStart_2636330 : Nat := 118140960795 + 2636330 * 2 ^ 59
def prefixEnd_2636330 : Nat := 4983230072969 + 3 ^ 40 * 2636330 * 2
def baseEnd_2636330 : Nat := 1353704453867775580450745

theorem tailTrace_2636330 : CollatzResearch.WordTrace tailWord_2636330 prefixEnd_2636330 1353704453867775580450745 := by
  unfold tailWord_2636330
  simp only [CollatzResearch.WordTrace]
  refine ⟨24038713634758533540732611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64103236359356089441953629 24038713634758533540732611)
  ·
    refine ⟨36058070452137800311098917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24038713634758533540732611 36058070452137800311098917)
    ·
      refine ⟨6760888209775837558331047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36058070452137800311098917 6760888209775837558331047)
      ·
        refine ⟨10141332314663756337496571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6760888209775837558331047 10141332314663756337496571)
        ·
          refine ⟨15211998471995634506244857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10141332314663756337496571 15211998471995634506244857)
          ·
            refine ⟨11408998853996725879683643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15211998471995634506244857 11408998853996725879683643)
            ·
              refine ⟨17113498280995088819525465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11408998853996725879683643 17113498280995088819525465)
              ·
                refine ⟨12835123710746316614644099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17113498280995088819525465 12835123710746316614644099)
                ·
                  refine ⟨19252685566119474921966149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12835123710746316614644099 19252685566119474921966149)
                  ·
                    refine ⟨3609878543647401547868653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19252685566119474921966149 3609878543647401547868653)
                    ·
                      refine ⟨1353704453867775580450745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3609878543647401547868653 1353704453867775580450745)
                      ·
                        rfl

theorem cell23_2636330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 2, 1, 4, 3].length) (baseStart_2636330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2636330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2636330 prefixEnd_2636330 := by exact prefixLift 2636330
  have htrace : WordTrace (prefixWord ++ tailWord_2636330) baseStart_2636330 baseEnd_2636330 := by
    simpa [prefixWord, tailWord_2636330, baseEnd_2636330] using wordTrace_append hprefix tailTrace_2636330
  have hstable : (prefixWord ++ tailWord_2636330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2636330).length < 2 ^ (prefixWord ++ tailWord_2636330).sum := by decide
  have hdescent : baseEnd_2636330 < baseStart_2636330 := by decide
  rcases family_descends (prefixWord ++ tailWord_2636330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2636343 : List Nat := [1, 1, 3, 1, 2, 3, 1, 1, 2, 5, 3]
def baseStart_2636343 : Nat := 118140960795 + 2636343 * 2 ^ 59
def prefixEnd_2636343 : Nat := 4983230072969 + 3 ^ 40 * 2636343 * 2
def baseEnd_2636343 : Nat := 1353711129116284029588185

theorem tailTrace_2636343 : CollatzResearch.WordTrace tailWord_2636343 prefixEnd_2636343 1353711129116284029588185 := by
  unfold tailWord_2636343
  simp only [CollatzResearch.WordTrace]
  refine ⟨96155328687987037383153683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64103552458658024922102455 96155328687987037383153683)
  ·
    refine ⟨144232993031980556074730525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96155328687987037383153683 144232993031980556074730525)
    ·
      refine ⟨54087372386992708528023947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144232993031980556074730525 54087372386992708528023947)
      ·
        refine ⟨81131058580489062792035921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54087372386992708528023947 81131058580489062792035921)
        ·
          refine ⟨60848293935366797094026941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81131058580489062792035921 60848293935366797094026941)
          ·
            refine ⟨22818110225762548910260103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60848293935366797094026941 22818110225762548910260103)
            ·
              refine ⟨34227165338643823365390155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22818110225762548910260103 34227165338643823365390155)
              ·
                refine ⟨51340748007965735048085233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34227165338643823365390155 51340748007965735048085233)
                ·
                  refine ⟨38505561005974301286063925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51340748007965735048085233 38505561005974301286063925)
                  ·
                    refine ⟨3609896344310090745568493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38505561005974301286063925 3609896344310090745568493)
                    ·
                      refine ⟨1353711129116284029588185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3609896344310090745568493 1353711129116284029588185)
                      ·
                        rfl

theorem cell23_2636343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 2, 5, 3].length) (baseStart_2636343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2636343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2636343 prefixEnd_2636343 := by exact prefixLift 2636343
  have htrace : WordTrace (prefixWord ++ tailWord_2636343) baseStart_2636343 baseEnd_2636343 := by
    simpa [prefixWord, tailWord_2636343, baseEnd_2636343] using wordTrace_append hprefix tailTrace_2636343
  have hstable : (prefixWord ++ tailWord_2636343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2636343).length < 2 ^ (prefixWord ++ tailWord_2636343).sum := by decide
  have hdescent : baseEnd_2636343 < baseStart_2636343 := by decide
  rcases family_descends (prefixWord ++ tailWord_2636343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2636360 : List Nat := [2, 1, 3, 1, 1, 1, 1, 4, 5, 1, 3]
def baseStart_2636360 : Nat := 118140960795 + 2636360 * 2 ^ 59
def prefixEnd_2636360 : Nat := 4983230072969 + 3 ^ 40 * 2636360 * 2
def baseEnd_2636360 : Nat := 1353719858287410463075607

theorem tailTrace_2636360 : CollatzResearch.WordTrace tailWord_2636360 prefixEnd_2636360 1353719858287410463075607 := by
  unfold tailWord_2636360
  simp only [CollatzResearch.WordTrace]
  refine ⟨48077974364462724643261267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64103965819283632857681689 48077974364462724643261267)
  ·
    refine ⟨72116961546694086964891901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48077974364462724643261267 72116961546694086964891901)
    ·
      refine ⟨27043860580010282611834463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72116961546694086964891901 27043860580010282611834463)
      ·
        refine ⟨40565790870015423917751695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27043860580010282611834463 40565790870015423917751695)
        ·
          refine ⟨60848686305023135876627543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40565790870015423917751695 60848686305023135876627543)
          ·
            refine ⟨91273029457534703814941315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60848686305023135876627543 91273029457534703814941315)
            ·
              refine ⟨136909544186302055722411973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91273029457534703814941315 136909544186302055722411973)
              ·
                refine ⟨25670539534931635447952245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 136909544186302055722411973 25670539534931635447952245)
                ·
                  refine ⟨2406613081399840823245523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25670539534931635447952245 2406613081399840823245523)
                  ·
                    refine ⟨3609919622099761234868285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2406613081399840823245523 3609919622099761234868285)
                    ·
                      refine ⟨1353719858287410463075607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3609919622099761234868285 1353719858287410463075607)
                      ·
                        rfl

theorem cell23_2636360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 4, 5, 1, 3].length) (baseStart_2636360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2636360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2636360 prefixEnd_2636360 := by exact prefixLift 2636360
  have htrace : WordTrace (prefixWord ++ tailWord_2636360) baseStart_2636360 baseEnd_2636360 := by
    simpa [prefixWord, tailWord_2636360, baseEnd_2636360] using wordTrace_append hprefix tailTrace_2636360
  have hstable : (prefixWord ++ tailWord_2636360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2636360).length < 2 ^ (prefixWord ++ tailWord_2636360).sum := by decide
  have hdescent : baseEnd_2636360 < baseStart_2636360 := by decide
  rcases family_descends (prefixWord ++ tailWord_2636360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2636393 : List Nat := [1, 2, 1, 1, 1, 4, 1, 5, 1, 6]
def baseStart_2636393 : Nat := 118140960795 + 2636393 * 2 ^ 59
def prefixEnd_2636393 : Nat := 4983230072969 + 3 ^ 40 * 2636393 * 2
def baseEnd_2636393 : Nat := 451245601049669611320985

theorem tailTrace_2636393 : CollatzResearch.WordTrace tailWord_2636393 prefixEnd_2636393 451245601049669611320985 := by
  unfold tailWord_2636393
  simp only [CollatzResearch.WordTrace]
  refine ⟨96157152337805895922473833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64104768225203930614982555 96157152337805895922473833)
  ·
    refine ⟨72117864253354421941855375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96157152337805895922473833 72117864253354421941855375)
    ·
      refine ⟨108176796380031632912783063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72117864253354421941855375 108176796380031632912783063)
      ·
        refine ⟨162265194570047449369174595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108176796380031632912783063 162265194570047449369174595)
        ·
          refine ⟨243397791855071174053761893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162265194570047449369174595 243397791855071174053761893)
          ·
            refine ⟨45637085972825845135080355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 243397791855071174053761893 45637085972825845135080355)
            ·
              refine ⟨68455628959238767702620533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45637085972825845135080355 68455628959238767702620533)
              ·
                refine ⟨6417715214928634472120675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 68455628959238767702620533 6417715214928634472120675)
                ·
                  refine ⟨9626572822392951708181013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6417715214928634472120675 9626572822392951708181013)
                  ·
                    refine ⟨451245601049669611320985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9626572822392951708181013 451245601049669611320985)
                    ·
                      rfl

theorem cell23_2636393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 5, 1, 6].length) (baseStart_2636393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2636393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2636393 prefixEnd_2636393 := by exact prefixLift 2636393
  have htrace : WordTrace (prefixWord ++ tailWord_2636393) baseStart_2636393 baseEnd_2636393 := by
    simpa [prefixWord, tailWord_2636393, baseEnd_2636393] using wordTrace_append hprefix tailTrace_2636393
  have hstable : (prefixWord ++ tailWord_2636393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2636393).length < 2 ^ (prefixWord ++ tailWord_2636393).sum := by decide
  have hdescent : baseEnd_2636393 < baseStart_2636393 := by decide
  rcases family_descends (prefixWord ++ tailWord_2636393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2636397 : List Nat := [1, 5, 1, 1, 3, 1, 3, 2, 1, 5]
def baseStart_2636397 : Nat := 118140960795 + 2636397 * 2 ^ 59
def prefixEnd_2636397 : Nat := 4983230072969 + 3 ^ 40 * 2636397 * 2
def baseEnd_2636397 : Nat := 451246285690542272770979

theorem tailTrace_2636397 : CollatzResearch.WordTrace tailWord_2636397 prefixEnd_2636397 451246285690542272770979 := by
  unfold tailWord_2636397
  simp only [CollatzResearch.WordTrace]
  refine ⟨96157298229791404605619445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64104865486527603070412963 96157298229791404605619445)
  ·
    refine ⟨9014746709042944181776823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 96157298229791404605619445 9014746709042944181776823)
    ·
      refine ⟨13522120063564416272665235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9014746709042944181776823 13522120063564416272665235)
      ·
        refine ⟨20283180095346624408997853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13522120063564416272665235 20283180095346624408997853)
        ·
          refine ⟨7606192535754984153374195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20283180095346624408997853 7606192535754984153374195)
          ·
            refine ⟨11409288803632476230061293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7606192535754984153374195 11409288803632476230061293)
            ·
              refine ⟨4278483301362178586272985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11409288803632476230061293 4278483301362178586272985)
              ·
                refine ⟨3208862476021633939704739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4278483301362178586272985 3208862476021633939704739)
                ·
                  refine ⟨4813293714032450909557109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3208862476021633939704739 4813293714032450909557109)
                  ·
                    refine ⟨451246285690542272770979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4813293714032450909557109 451246285690542272770979)
                    ·
                      rfl

theorem cell23_2636397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3, 2, 1, 5].length) (baseStart_2636397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2636397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2636397 prefixEnd_2636397 := by exact prefixLift 2636397
  have htrace : WordTrace (prefixWord ++ tailWord_2636397) baseStart_2636397 baseEnd_2636397 := by
    simpa [prefixWord, tailWord_2636397, baseEnd_2636397] using wordTrace_append hprefix tailTrace_2636397
  have hstable : (prefixWord ++ tailWord_2636397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2636397).length < 2 ^ (prefixWord ++ tailWord_2636397).sum := by decide
  have hdescent : baseEnd_2636397 < baseStart_2636397 := by decide
  rcases family_descends (prefixWord ++ tailWord_2636397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2636430 : List Nat := [4, 1, 1, 3, 1, 1, 1, 2, 3, 2, 4]
def baseStart_2636430 : Nat := 118140960795 + 2636430 * 2 ^ 59
def prefixEnd_2636430 : Nat := 4983230072969 + 3 ^ 40 * 2636430 * 2
def baseEnd_2636430 : Nat := 1353755801933225189200285

theorem tailTrace_2636430 : CollatzResearch.WordTrace tailWord_2636430 prefixEnd_2636430 1353755801933225189200285 := by
  unfold tailWord_2636430
  simp only [CollatzResearch.WordTrace]
  refine ⟨12019812729833981405196343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64105667892447900827713829 12019812729833981405196343)
  ·
    refine ⟨18029719094750972107794515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12019812729833981405196343 18029719094750972107794515)
    ·
      refine ⟨27044578642126458161691773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18029719094750972107794515 27044578642126458161691773)
      ·
        refine ⟨10141716990797421810634415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27044578642126458161691773 10141716990797421810634415)
        ·
          refine ⟨15212575486196132715951623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10141716990797421810634415 15212575486196132715951623)
          ·
            refine ⟨22818863229294199073927435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15212575486196132715951623 22818863229294199073927435)
            ·
              refine ⟨34228294843941298610891153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22818863229294199073927435 34228294843941298610891153)
              ·
                refine ⟨25671221132955973958168365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34228294843941298610891153 25671221132955973958168365)
                ·
                  refine ⟨9626707924858490234313137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25671221132955973958168365 9626707924858490234313137)
                  ·
                    refine ⟨7220030943643867675734853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9626707924858490234313137 7220030943643867675734853)
                    ·
                      refine ⟨1353755801933225189200285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7220030943643867675734853 1353755801933225189200285)
                      ·
                        rfl

theorem cell23_2636430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_2636430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2636430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2636430 prefixEnd_2636430 := by exact prefixLift 2636430
  have htrace : WordTrace (prefixWord ++ tailWord_2636430) baseStart_2636430 baseEnd_2636430 := by
    simpa [prefixWord, tailWord_2636430, baseEnd_2636430] using wordTrace_append hprefix tailTrace_2636430
  have hstable : (prefixWord ++ tailWord_2636430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2636430).length < 2 ^ (prefixWord ++ tailWord_2636430).sum := by decide
  have hdescent : baseEnd_2636430 < baseStart_2636430 := by decide
  rcases family_descends (prefixWord ++ tailWord_2636430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2636453 : List Nat := [1, 3, 1, 2, 1, 2, 1, 1, 4, 7]
def baseStart_2636453 : Nat := 118140960795 + 2636453 * 2 ^ 59
def prefixEnd_2636453 : Nat := 4983230072969 + 3 ^ 40 * 2636453 * 2
def baseEnd_2636453 : Nat := 451255870662759533070893

theorem tailTrace_2636453 : CollatzResearch.WordTrace tailWord_2636453 prefixEnd_2636453 451255870662759533070893 := by
  unfold tailWord_2636453
  simp only [CollatzResearch.WordTrace]
  refine ⟨96159340717588526169658013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64106227145059017446438675 96159340717588526169658013)
  ·
    refine ⟨36059752769095697313621755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96159340717588526169658013 36059752769095697313621755)
    ·
      refine ⟨54089629153643545970432633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36059752769095697313621755 54089629153643545970432633)
      ·
        refine ⟨40567221865232659477824475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54089629153643545970432633 40567221865232659477824475)
        ·
          refine ⟨60850832797848989216736713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40567221865232659477824475 60850832797848989216736713)
          ·
            refine ⟨45638124598386741912552535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60850832797848989216736713 45638124598386741912552535)
            ·
              refine ⟨68457186897580112868828803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45638124598386741912552535 68457186897580112868828803)
              ·
                refine ⟨102685780346370169303243205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68457186897580112868828803 102685780346370169303243205)
                ·
                  refine ⟨19253583814944406744358101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 102685780346370169303243205 19253583814944406744358101)
                  ·
                    refine ⟨451255870662759533070893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19253583814944406744358101 451255870662759533070893)
                    ·
                      rfl

theorem cell23_2636453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 4, 7].length) (baseStart_2636453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2636453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2636453 prefixEnd_2636453 := by exact prefixLift 2636453
  have htrace : WordTrace (prefixWord ++ tailWord_2636453) baseStart_2636453 baseEnd_2636453 := by
    simpa [prefixWord, tailWord_2636453, baseEnd_2636453] using wordTrace_append hprefix tailTrace_2636453
  have hstable : (prefixWord ++ tailWord_2636453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2636453).length < 2 ^ (prefixWord ++ tailWord_2636453).sum := by decide
  have hdescent : baseEnd_2636453 < baseStart_2636453 := by decide
  rcases family_descends (prefixWord ++ tailWord_2636453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2636471 : List Nat := [1, 1, 3, 1, 6, 2, 2, 1, 1, 2, 3]
def baseStart_2636471 : Nat := 118140960795 + 2636471 * 2 ^ 59
def prefixEnd_2636471 : Nat := 4983230072969 + 3 ^ 40 * 2636471 * 2
def baseEnd_2636471 : Nat := 1353776854640059528787597

theorem tailTrace_2636471 : CollatzResearch.WordTrace tailWord_2636471 prefixEnd_2636471 1353776854640059528787597 := by
  unfold tailWord_2636471
  simp only [CollatzResearch.WordTrace]
  refine ⟨96159997231523315243813267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64106664821015543495875511 96159997231523315243813267)
  ·
    refine ⟨144239995847284972865719901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96159997231523315243813267 144239995847284972865719901)
    ·
      refine ⟨54089998442731864824644963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144239995847284972865719901 54089998442731864824644963)
      ·
        refine ⟨81134997664097797236967445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54089998442731864824644963 81134997664097797236967445)
        ·
          refine ⟨3803203015504584245482849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 81134997664097797236967445 3803203015504584245482849)
          ·
            refine ⟨2852402261628438184112137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3803203015504584245482849 2852402261628438184112137)
            ·
              refine ⟨2139301696221328638084103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2852402261628438184112137 2139301696221328638084103)
              ·
                refine ⟨3208952544331992957126155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2139301696221328638084103 3208952544331992957126155)
                ·
                  refine ⟨4813428816497989435689233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3208952544331992957126155 4813428816497989435689233)
                  ·
                    refine ⟨3610071612373492076766925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4813428816497989435689233 3610071612373492076766925)
                    ·
                      refine ⟨1353776854640059528787597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3610071612373492076766925 1353776854640059528787597)
                      ·
                        rfl

theorem cell23_2636471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 2, 1, 1, 2, 3].length) (baseStart_2636471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2636471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2636471 prefixEnd_2636471 := by exact prefixLift 2636471
  have htrace : WordTrace (prefixWord ++ tailWord_2636471) baseStart_2636471 baseEnd_2636471 := by
    simpa [prefixWord, tailWord_2636471, baseEnd_2636471] using wordTrace_append hprefix tailTrace_2636471
  have hstable : (prefixWord ++ tailWord_2636471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2636471).length < 2 ^ (prefixWord ++ tailWord_2636471).sum := by decide
  have hdescent : baseEnd_2636471 < baseStart_2636471 := by decide
  rcases family_descends (prefixWord ++ tailWord_2636471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2636484 : List Nat := [2, 3, 3, 1, 1, 3, 1, 1, 4, 1, 3]
def baseStart_2636484 : Nat := 118140960795 + 2636484 * 2 ^ 59
def prefixEnd_2636484 : Nat := 4983230072969 + 3 ^ 40 * 2636484 * 2
def baseEnd_2636484 : Nat := 1353783529888567977925037

theorem tailTrace_2636484 : CollatzResearch.WordTrace tailWord_2636484 prefixEnd_2636484 1353783529888567977925037 := by
  unfold tailWord_2636484
  simp only [CollatzResearch.WordTrace]
  refine ⟨48080235690238109232018253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64106980920317478976024337 48080235690238109232018253)
  ·
    refine ⟨18030088383839290962006845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48080235690238109232018253 18030088383839290962006845)
    ·
      refine ⟨6761283143939734110752567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18030088383839290962006845 6761283143939734110752567)
      ·
        refine ⟨10141924715909601166128851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6761283143939734110752567 10141924715909601166128851)
        ·
          refine ⟨15212887073864401749193277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10141924715909601166128851 15212887073864401749193277)
          ·
            refine ⟨5704832652699150655947479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15212887073864401749193277 5704832652699150655947479)
            ·
              refine ⟨8557248979048725983921219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5704832652699150655947479 8557248979048725983921219)
              ·
                refine ⟨12835873468573088975881829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8557248979048725983921219 12835873468573088975881829)
                ·
                  refine ⟨2406726275357454182977843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12835873468573088975881829 2406726275357454182977843)
                  ·
                    refine ⟨3610089413036181274466765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2406726275357454182977843 3610089413036181274466765)
                    ·
                      refine ⟨1353783529888567977925037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3610089413036181274466765 1353783529888567977925037)
                      ·
                        rfl

theorem cell23_2636484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 1, 4, 1, 3].length) (baseStart_2636484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2636484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2636484 prefixEnd_2636484 := by exact prefixLift 2636484
  have htrace : WordTrace (prefixWord ++ tailWord_2636484) baseStart_2636484 baseEnd_2636484 := by
    simpa [prefixWord, tailWord_2636484, baseEnd_2636484] using wordTrace_append hprefix tailTrace_2636484
  have hstable : (prefixWord ++ tailWord_2636484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2636484).length < 2 ^ (prefixWord ++ tailWord_2636484).sum := by decide
  have hdescent : baseEnd_2636484 < baseStart_2636484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2636484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2636501 : List Nat := [1, 3, 2, 5, 1, 2, 1, 1, 1, 3, 3]
def baseStart_2636501 : Nat := 118140960795 + 2636501 * 2 ^ 59
def prefixEnd_2636501 : Nat := 4983230072969 + 3 ^ 40 * 2636501 * 2
def baseEnd_2636501 : Nat := 1353792259059694411412459

theorem tailTrace_2636501 : CollatzResearch.WordTrace tailWord_2636501 prefixEnd_2636501 1353792259059694411412459 := by
  unfold tailWord_2636501
  simp only [CollatzResearch.WordTrace]
  refine ⟨96161091421414630367405357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64107394280943086911603571 96161091421414630367405357)
  ·
    refine ⟨36060409283030486387777009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96161091421414630367405357 36060409283030486387777009)
    ·
      refine ⟨27045306962272864790832757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36060409283030486387777009 27045306962272864790832757)
      ·
        refine ⟨2535497527713081074140571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27045306962272864790832757 2535497527713081074140571)
        ·
          refine ⟨3803246291569621611210857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2535497527713081074140571 3803246291569621611210857)
          ·
            refine ⟨2852434718677216208408143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3803246291569621611210857 2852434718677216208408143)
            ·
              refine ⟨4278652078015824312612215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2852434718677216208408143 4278652078015824312612215)
              ·
                refine ⟨6417978117023736468918323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4278652078015824312612215 6417978117023736468918323)
                ·
                  refine ⟨9626967175535604703377485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6417978117023736468918323 9626967175535604703377485)
                  ·
                    refine ⟨3610112690825851763766557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9626967175535604703377485 3610112690825851763766557)
                    ·
                      refine ⟨1353792259059694411412459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3610112690825851763766557 1353792259059694411412459)
                      ·
                        rfl

theorem cell23_2636501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_2636501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2636501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2636501 prefixEnd_2636501 := by exact prefixLift 2636501
  have htrace : WordTrace (prefixWord ++ tailWord_2636501) baseStart_2636501 baseEnd_2636501 := by
    simpa [prefixWord, tailWord_2636501, baseEnd_2636501] using wordTrace_append hprefix tailTrace_2636501
  have hstable : (prefixWord ++ tailWord_2636501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2636501).length < 2 ^ (prefixWord ++ tailWord_2636501).sum := by decide
  have hdescent : baseEnd_2636501 < baseStart_2636501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2636501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2636570 : List Nat := [3, 1, 1, 3, 2, 1, 1, 2, 1, 1, 7]
def baseStart_2636570 : Nat := 118140960795 + 2636570 * 2 ^ 59
def prefixEnd_2636570 : Nat := 4983230072969 + 3 ^ 40 * 2636570 * 2
def baseEnd_2636570 : Nat := 1353827689224854641449641

theorem tailTrace_2636570 : CollatzResearch.WordTrace tailWord_2636570 prefixEnd_2636570 1353827689224854641449641 := by
  unfold tailWord_2636570
  simp only [CollatzResearch.WordTrace]
  refine ⟨24040902014541163787916791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64109072038776436767778109 24040902014541163787916791)
  ·
    refine ⟨36061353021811745681875187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24040902014541163787916791 36061353021811745681875187)
    ·
      refine ⟨54092029532717618522812781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36061353021811745681875187 54092029532717618522812781)
      ·
        refine ⟨20284511074769106946054793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54092029532717618522812781 20284511074769106946054793)
        ·
          refine ⟨15213383306076830209541095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20284511074769106946054793 15213383306076830209541095)
          ·
            refine ⟨22820074959115245314311643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15213383306076830209541095 22820074959115245314311643)
            ·
              refine ⟨34230112438672867971467465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22820074959115245314311643 34230112438672867971467465)
              ·
                refine ⟨25672584329004650978600599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34230112438672867971467465 25672584329004650978600599)
                ·
                  refine ⟨38508876493506976467900899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25672584329004650978600599 38508876493506976467900899)
                  ·
                    refine ⟨57763314740260464701851349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38508876493506976467900899 57763314740260464701851349)
                    ·
                      refine ⟨1353827689224854641449641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 57763314740260464701851349 1353827689224854641449641)
                      ·
                        rfl

theorem cell23_2636570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_2636570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2636570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2636570 prefixEnd_2636570 := by exact prefixLift 2636570
  have htrace : WordTrace (prefixWord ++ tailWord_2636570) baseStart_2636570 baseEnd_2636570 := by
    simpa [prefixWord, tailWord_2636570, baseEnd_2636570] using wordTrace_append hprefix tailTrace_2636570
  have hstable : (prefixWord ++ tailWord_2636570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2636570).length < 2 ^ (prefixWord ++ tailWord_2636570).sum := by decide
  have hdescent : baseEnd_2636570 < baseStart_2636570 := by decide
  rcases family_descends (prefixWord ++ tailWord_2636570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2636577 : List Nat := [1, 2, 3, 2, 1, 2, 4, 1, 2, 5]
def baseStart_2636577 : Nat := 118140960795 + 2636577 * 2 ^ 59
def prefixEnd_2636577 : Nat := 4983230072969 + 3 ^ 40 * 2636577 * 2
def baseEnd_2636577 : Nat := 451277094529812038020703

theorem tailTrace_2636577 : CollatzResearch.WordTrace tailWord_2636577 prefixEnd_2636577 451277094529812038020703 := by
  unfold tailWord_2636577
  simp only [CollatzResearch.WordTrace]
  refine ⟨96163863369139295347171985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64109242246092863564781323 96163863369139295347171985)
  ·
    refine ⟨72122897526854471510378989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96163863369139295347171985 72122897526854471510378989)
    ·
      refine ⟨27046086572570426816392121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72122897526854471510378989 27046086572570426816392121)
      ·
        refine ⟨20284564929427820112294091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27046086572570426816392121 20284564929427820112294091)
        ·
          refine ⟨30426847394141730168441137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20284564929427820112294091 30426847394141730168441137)
          ·
            refine ⟨22820135545606297626330853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30426847394141730168441137 22820135545606297626330853)
            ·
              refine ⟨4278775414801180804937035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22820135545606297626330853 4278775414801180804937035)
              ·
                refine ⟨6418163122201771207405553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4278775414801180804937035 6418163122201771207405553)
                ·
                  refine ⟨4813622341651328405554165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6418163122201771207405553 4813622341651328405554165)
                  ·
                    refine ⟨451277094529812038020703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4813622341651328405554165 451277094529812038020703)
                    ·
                      rfl

theorem cell23_2636577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4, 1, 2, 5].length) (baseStart_2636577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2636577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2636577 prefixEnd_2636577 := by exact prefixLift 2636577
  have htrace : WordTrace (prefixWord ++ tailWord_2636577) baseStart_2636577 baseEnd_2636577 := by
    simpa [prefixWord, tailWord_2636577, baseEnd_2636577] using wordTrace_append hprefix tailTrace_2636577
  have hstable : (prefixWord ++ tailWord_2636577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2636577).length < 2 ^ (prefixWord ++ tailWord_2636577).sum := by decide
  have hdescent : baseEnd_2636577 < baseStart_2636577 := by decide
  rcases family_descends (prefixWord ++ tailWord_2636577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2636600 : List Nat := [2, 1, 2, 1, 3, 2, 1, 1, 2, 3, 5]
def baseStart_2636600 : Nat := 118140960795 + 2636600 * 2 ^ 59
def prefixEnd_2636600 : Nat := 4983230072969 + 3 ^ 40 * 2636600 * 2
def baseEnd_2636600 : Nat := 1353843093644489524074503

theorem tailTrace_2636600 : CollatzResearch.WordTrace tailWord_2636600 prefixEnd_2636600 1353843093644489524074503 := by
  unfold tailWord_2636600
  simp only [CollatzResearch.WordTrace]
  refine ⟨48082351124027985137629627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64109801498703980183506169 48082351124027985137629627)
  ·
    refine ⟨72123526686041977706444441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48082351124027985137629627 72123526686041977706444441)
    ·
      refine ⟨54092645014531483279833331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72123526686041977706444441 54092645014531483279833331)
      ·
        refine ⟨81138967521797224919749997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54092645014531483279833331 81138967521797224919749997)
        ·
          refine ⟨30427112820673959344906249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81138967521797224919749997 30427112820673959344906249)
          ·
            refine ⟨22820334615505469508679687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30427112820673959344906249 22820334615505469508679687)
            ·
              refine ⟨34230501923258204263019531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22820334615505469508679687 34230501923258204263019531)
              ·
                refine ⟨51345752884887306394529297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34230501923258204263019531 51345752884887306394529297)
                ·
                  refine ⟨38509314663665479795896973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51345752884887306394529297 38509314663665479795896973)
                  ·
                    refine ⟨14440992998874554923461365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38509314663665479795896973 14440992998874554923461365)
                    ·
                      refine ⟨1353843093644489524074503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14440992998874554923461365 1353843093644489524074503)
                      ·
                        rfl

theorem cell23_2636600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 2, 3, 5].length) (baseStart_2636600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2636600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2636600 prefixEnd_2636600 := by exact prefixLift 2636600
  have htrace : WordTrace (prefixWord ++ tailWord_2636600) baseStart_2636600 baseEnd_2636600 := by
    simpa [prefixWord, tailWord_2636600, baseEnd_2636600] using wordTrace_append hprefix tailTrace_2636600
  have hstable : (prefixWord ++ tailWord_2636600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2636600).length < 2 ^ (prefixWord ++ tailWord_2636600).sum := by decide
  have hdescent : baseEnd_2636600 < baseStart_2636600 := by decide
  rcases family_descends (prefixWord ++ tailWord_2636600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2636634 : List Nat := [3, 1, 1, 2, 1, 4, 3, 1, 2, 2, 3]
def baseStart_2636634 : Nat := 118140960795 + 2636634 * 2 ^ 59
def prefixEnd_2636634 : Nat := 4983230072969 + 3 ^ 40 * 2636634 * 2
def baseEnd_2636634 : Nat := 1353860551986742391049347

theorem tailTrace_2636634 : CollatzResearch.WordTrace tailWord_2636634 prefixEnd_2636634 1353860551986742391049347 := by
  unfold tailWord_2636634
  simp only [CollatzResearch.WordTrace]
  refine ⟨24041485582483198520499239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64110628219955196054664637 24041485582483198520499239)
  ·
    refine ⟨36062228373724797780748859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24041485582483198520499239 36062228373724797780748859)
    ·
      refine ⟨54093342560587196671123289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36062228373724797780748859 54093342560587196671123289)
      ·
        refine ⟨40570006920440397503342467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54093342560587196671123289 40570006920440397503342467)
        ·
          refine ⟨60855010380660596255013701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40570006920440397503342467 60855010380660596255013701)
          ·
            refine ⟨11410314446373861797815069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60855010380660596255013701 11410314446373861797815069)
            ·
              refine ⟨4278867917390198174180651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11410314446373861797815069 4278867917390198174180651)
              ·
                refine ⟨6418301876085297261270977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4278867917390198174180651 6418301876085297261270977)
                ·
                  refine ⟨4813726407063972945953233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6418301876085297261270977 4813726407063972945953233)
                  ·
                    refine ⟨3610294805297979709464925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4813726407063972945953233 3610294805297979709464925)
                    ·
                      refine ⟨1353860551986742391049347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3610294805297979709464925 1353860551986742391049347)
                      ·
                        rfl

theorem cell23_2636634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3, 1, 2, 2, 3].length) (baseStart_2636634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2636634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2636634 prefixEnd_2636634 := by exact prefixLift 2636634
  have htrace : WordTrace (prefixWord ++ tailWord_2636634) baseStart_2636634 baseEnd_2636634 := by
    simpa [prefixWord, tailWord_2636634, baseEnd_2636634] using wordTrace_append hprefix tailTrace_2636634
  have hstable : (prefixWord ++ tailWord_2636634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2636634).length < 2 ^ (prefixWord ++ tailWord_2636634).sum := by decide
  have hdescent : baseEnd_2636634 < baseStart_2636634 := by decide
  rcases family_descends (prefixWord ++ tailWord_2636634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2636654 : List Nat := [4, 1, 2, 3, 2, 1, 1, 1, 8]
def baseStart_2636654 : Nat := 118140960795 + 2636654 * 2 ^ 59
def prefixEnd_2636654 : Nat := 4983230072969 + 3 ^ 40 * 2636654 * 2
def baseEnd_2636654 : Nat := 150430091288870256977695

theorem tailTrace_2636654 : CollatzResearch.WordTrace tailWord_2636654 prefixEnd_2636654 150430091288870256977695 := by
  unfold tailWord_2636654
  simp only [CollatzResearch.WordTrace]
  refine ⟨12020833973732542187215627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64111114526573558331816677 12020833973732542187215627)
  ·
    refine ⟨18031250960598813280823441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12020833973732542187215627 18031250960598813280823441)
    ·
      refine ⟨13523438220449109960617581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18031250960598813280823441 13523438220449109960617581)
      ·
        refine ⟨5071289332668416235231593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13523438220449109960617581 5071289332668416235231593)
        ·
          refine ⟨3803466999501312176423695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5071289332668416235231593 3803466999501312176423695)
          ·
            refine ⟨5705200499251968264635543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3803466999501312176423695 5705200499251968264635543)
            ·
              refine ⟨8557800748877952396953315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5705200499251968264635543 8557800748877952396953315)
              ·
                refine ⟨12836701123316928595429973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8557800748877952396953315 12836701123316928595429973)
                ·
                  refine ⟨150430091288870256977695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12836701123316928595429973 150430091288870256977695)
                  ·
                    rfl

theorem cell23_2636654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 1, 8].length) (baseStart_2636654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2636654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2636654 prefixEnd_2636654 := by exact prefixLift 2636654
  have htrace : WordTrace (prefixWord ++ tailWord_2636654) baseStart_2636654 baseEnd_2636654 := by
    simpa [prefixWord, tailWord_2636654, baseEnd_2636654] using wordTrace_append hprefix tailTrace_2636654
  have hstable : (prefixWord ++ tailWord_2636654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2636654).length < 2 ^ (prefixWord ++ tailWord_2636654).sum := by decide
  have hdescent : baseEnd_2636654 < baseStart_2636654 := by decide
  rcases family_descends (prefixWord ++ tailWord_2636654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2636704 : List Nat := [2, 1, 1, 4, 1, 1, 4, 3, 1, 1, 4]
def baseStart_2636704 : Nat := 118140960795 + 2636704 * 2 ^ 59
def prefixEnd_2636704 : Nat := 4983230072969 + 3 ^ 40 * 2636704 * 2
def baseEnd_2636704 : Nat := 1353896495632557117174025

theorem tailTrace_2636704 : CollatzResearch.WordTrace tailWord_2636704 prefixEnd_2636704 1353896495632557117174025 := by
  unfold tailWord_2636704
  simp only [CollatzResearch.WordTrace]
  refine ⟨48084247719839598018522583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64112330293119464024696777 48084247719839598018522583)
  ·
    refine ⟨72126371579759397027783875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48084247719839598018522583 72126371579759397027783875)
    ·
      refine ⟨108189557369639095541675813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72126371579759397027783875 108189557369639095541675813)
      ·
        refine ⟨20285542006807330414064215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 108189557369639095541675813 20285542006807330414064215)
        ·
          refine ⟨30428313010210995621096323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20285542006807330414064215 30428313010210995621096323)
          ·
            refine ⟨45642469515316493431644485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30428313010210995621096323 45642469515316493431644485)
            ·
              refine ⟨8557963034121842518433341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45642469515316493431644485 8557963034121842518433341)
              ·
                refine ⟨3209236137795690944412503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8557963034121842518433341 3209236137795690944412503)
                ·
                  refine ⟨4813854206693536416618755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3209236137795690944412503 4813854206693536416618755)
                  ·
                    refine ⟨7220781310040304624928133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4813854206693536416618755 7220781310040304624928133)
                    ·
                      refine ⟨1353896495632557117174025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7220781310040304624928133 1353896495632557117174025)
                      ·
                        rfl

theorem cell23_2636704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 3, 1, 1, 4].length) (baseStart_2636704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2636704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2636704 prefixEnd_2636704 := by exact prefixLift 2636704
  have htrace : WordTrace (prefixWord ++ tailWord_2636704) baseStart_2636704 baseEnd_2636704 := by
    simpa [prefixWord, tailWord_2636704, baseEnd_2636704] using wordTrace_append hprefix tailTrace_2636704
  have hstable : (prefixWord ++ tailWord_2636704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2636704).length < 2 ^ (prefixWord ++ tailWord_2636704).sum := by decide
  have hdescent : baseEnd_2636704 < baseStart_2636704 := by decide
  rcases family_descends (prefixWord ++ tailWord_2636704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2636707 : List Nat := [1, 1, 1, 4, 1, 2, 3, 3, 1, 1, 5]
def baseStart_2636707 : Nat := 118140960795 + 2636707 * 2 ^ 59
def prefixEnd_2636707 : Nat := 4983230072969 + 3 ^ 40 * 2636707 * 2
def baseEnd_2636707 : Nat := 1353898036074520605436511

theorem tailTrace_2636707 : CollatzResearch.WordTrace tailWord_2636707 prefixEnd_2636707 1353898036074520605436511 := by
  unfold tailWord_2636707
  simp only [CollatzResearch.WordTrace]
  refine ⟨96168604858668327549404375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64112403239112218366269583 96168604858668327549404375)
  ·
    refine ⟨144252907288002491324106563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96168604858668327549404375 144252907288002491324106563)
    ·
      refine ⟨216379360932003736986159845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144252907288002491324106563 216379360932003736986159845)
      ·
        refine ⟨40571130174750700684904971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 216379360932003736986159845 40571130174750700684904971)
        ·
          refine ⟨60856695262126051027357457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40571130174750700684904971 60856695262126051027357457)
          ·
            refine ⟨45642521446594538270518093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60856695262126051027357457 45642521446594538270518093)
            ·
              refine ⟨17115945542472951851444285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45642521446594538270518093 17115945542472951851444285)
              ·
                refine ⟨6418479578427356944291607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17115945542472951851444285 6418479578427356944291607)
                ·
                  refine ⟨9627719367641035416437411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6418479578427356944291607 9627719367641035416437411)
                  ·
                    refine ⟨14441579051461553124656117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9627719367641035416437411 14441579051461553124656117)
                    ·
                      refine ⟨1353898036074520605436511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14441579051461553124656117 1353898036074520605436511)
                      ·
                        rfl

theorem cell23_2636707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 3, 1, 1, 5].length) (baseStart_2636707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2636707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2636707 prefixEnd_2636707 := by exact prefixLift 2636707
  have htrace : WordTrace (prefixWord ++ tailWord_2636707) baseStart_2636707 baseEnd_2636707 := by
    simpa [prefixWord, tailWord_2636707, baseEnd_2636707] using wordTrace_append hprefix tailTrace_2636707
  have hstable : (prefixWord ++ tailWord_2636707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2636707).length < 2 ^ (prefixWord ++ tailWord_2636707).sum := by decide
  have hdescent : baseEnd_2636707 < baseStart_2636707 := by decide
  rcases family_descends (prefixWord ++ tailWord_2636707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2636734 : List Nat := [4, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4]
def baseStart_2636734 : Nat := 118140960795 + 2636734 * 2 ^ 59
def prefixEnd_2636734 : Nat := 4983230072969 + 3 ^ 40 * 2636734 * 2
def baseEnd_2636734 : Nat := 1353911900052191999798887

theorem tailTrace_2636734 : CollatzResearch.WordTrace tailWord_2636734 prefixEnd_2636734 1353911900052191999798887 := by
  unfold tailWord_2636734
  simp only [CollatzResearch.WordTrace]
  refine ⟨12021198703696313895079657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64113059753047007440424837 12021198703696313895079657)
  ·
    refine ⟨9015899027772235421309743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12021198703696313895079657 9015899027772235421309743)
    ·
      refine ⟨13523848541658353131964615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9015899027772235421309743 13523848541658353131964615)
      ·
        refine ⟨20285772812487529697946923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13523848541658353131964615 20285772812487529697946923)
        ·
          refine ⟨30428659218731294546920385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20285772812487529697946923 30428659218731294546920385)
          ·
            refine ⟨22821494414048470910190289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30428659218731294546920385 22821494414048470910190289)
            ·
              refine ⟨17116120810536353182642717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22821494414048470910190289 17116120810536353182642717)
              ·
                refine ⟨6418545303951132443491019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17116120810536353182642717 6418545303951132443491019)
                ·
                  refine ⟨9627817955926698665236529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6418545303951132443491019 9627817955926698665236529)
                  ·
                    refine ⟨7220863466945023998927397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9627817955926698665236529 7220863466945023998927397)
                    ·
                      refine ⟨1353911900052191999798887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7220863466945023998927397 1353911900052191999798887)
                      ·
                        rfl

theorem cell23_2636734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4].length) (baseStart_2636734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2636734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2636734 prefixEnd_2636734 := by exact prefixLift 2636734
  have htrace : WordTrace (prefixWord ++ tailWord_2636734) baseStart_2636734 baseEnd_2636734 := by
    simpa [prefixWord, tailWord_2636734, baseEnd_2636734] using wordTrace_append hprefix tailTrace_2636734
  have hstable : (prefixWord ++ tailWord_2636734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2636734).length < 2 ^ (prefixWord ++ tailWord_2636734).sum := by decide
  have hdescent : baseEnd_2636734 < baseStart_2636734 := by decide
  rcases family_descends (prefixWord ++ tailWord_2636734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2636758 : List Nat := [5, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5]
def baseStart_2636758 : Nat := 118140960795 + 2636758 * 2 ^ 59
def prefixEnd_2636758 : Nat := 4983230072969 + 3 ^ 40 * 2636758 * 2
def baseEnd_2636758 : Nat := 1353924223587899905898777

theorem tailTrace_2636758 : CollatzResearch.WordTrace tailWord_2636758 prefixEnd_2636758 1353924223587899905898777 := by
  unfold tailWord_2636758
  simp only [CollatzResearch.WordTrace]
  refine ⟨6010654061342722703719433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 64113643320989042173007285 6010654061342722703719433)
  ·
    refine ⟨4507990546007042027789575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6010654061342722703719433 4507990546007042027789575)
    ·
      refine ⟨6761985819010563041684363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4507990546007042027789575 6761985819010563041684363)
      ·
        refine ⟨10142978728515844562526545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6761985819010563041684363 10142978728515844562526545)
        ·
          refine ⟨7607234046386883421894909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10142978728515844562526545 7607234046386883421894909)
          ·
            refine ⟨2852712767395081283210591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7607234046386883421894909 2852712767395081283210591)
            ·
              refine ⟨4279069151092621924815887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2852712767395081283210591 4279069151092621924815887)
              ·
                refine ⟨6418603726638932887223831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4279069151092621924815887 6418603726638932887223831)
                ·
                  refine ⟨9627905589958399330835747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6418603726638932887223831 9627905589958399330835747)
                  ·
                    refine ⟨14441858384937598996253621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9627905589958399330835747 14441858384937598996253621)
                    ·
                      refine ⟨1353924223587899905898777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14441858384937598996253621 1353924223587899905898777)
                      ·
                        rfl

theorem cell23_2636758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5].length) (baseStart_2636758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2636758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2636758 prefixEnd_2636758 := by exact prefixLift 2636758
  have htrace : WordTrace (prefixWord ++ tailWord_2636758) baseStart_2636758 baseEnd_2636758 := by
    simpa [prefixWord, tailWord_2636758, baseEnd_2636758] using wordTrace_append hprefix tailTrace_2636758
  have hstable : (prefixWord ++ tailWord_2636758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2636758).length < 2 ^ (prefixWord ++ tailWord_2636758).sum := by decide
  have hdescent : baseEnd_2636758 < baseStart_2636758 := by decide
  rcases family_descends (prefixWord ++ tailWord_2636758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2636811 : List Nat := [1, 1, 1, 1, 6, 2, 2, 2, 1, 4, 2]
def baseStart_2636811 : Nat := 118140960795 + 2636811 * 2 ^ 59
def prefixEnd_2636811 : Nat := 4983230072969 + 3 ^ 40 * 2636811 * 2
def baseEnd_2636811 : Nat := 1353951438062588198536033

theorem tailTrace_2636811 : CollatzResearch.WordTrace tailWord_2636811 prefixEnd_2636811 1353951438062588198536033 := by
  unfold tailWord_2636811
  simp only [CollatzResearch.WordTrace]
  refine ⟨96172398050291553311190287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64114932033527702207460191 96172398050291553311190287)
  ·
    refine ⟨144258597075437329966785431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96172398050291553311190287 144258597075437329966785431)
    ·
      refine ⟨216387895613155994950178147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144258597075437329966785431 216387895613155994950178147)
      ·
        refine ⟨324581843419733992425267221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216387895613155994950178147 324581843419733992425267221)
        ·
          refine ⟨15214773910300030894934401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 324581843419733992425267221 15214773910300030894934401)
          ·
            refine ⟨11411080432725023171200801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15214773910300030894934401 11411080432725023171200801)
            ·
              refine ⟨8558310324543767378400601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11411080432725023171200801 8558310324543767378400601)
              ·
                refine ⟨6418732743407825533800451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8558310324543767378400601 6418732743407825533800451)
                ·
                  refine ⟨9628099115111738300700677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6418732743407825533800451 9628099115111738300700677)
                  ·
                    refine ⟨1805268584083450931381377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9628099115111738300700677 1805268584083450931381377)
                    ·
                      refine ⟨1353951438062588198536033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1805268584083450931381377 1353951438062588198536033)
                      ·
                        rfl

theorem cell23_2636811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 2, 1, 4, 2].length) (baseStart_2636811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2636811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2636811 prefixEnd_2636811 := by exact prefixLift 2636811
  have htrace : WordTrace (prefixWord ++ tailWord_2636811) baseStart_2636811 baseEnd_2636811 := by
    simpa [prefixWord, tailWord_2636811, baseEnd_2636811] using wordTrace_append hprefix tailTrace_2636811
  have hstable : (prefixWord ++ tailWord_2636811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2636811).length < 2 ^ (prefixWord ++ tailWord_2636811).sum := by decide
  have hdescent : baseEnd_2636811 < baseStart_2636811 := by decide
  rcases family_descends (prefixWord ++ tailWord_2636811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2636824 : List Nat := [2, 1, 2, 3, 2, 2, 1, 2, 2, 2, 4]
def baseStart_2636824 : Nat := 118140960795 + 2636824 * 2 ^ 59
def prefixEnd_2636824 : Nat := 4983230072969 + 3 ^ 40 * 2636824 * 2
def baseEnd_2636824 : Nat := 1353958113311096647673473

theorem tailTrace_2636824 : CollatzResearch.WordTrace tailWord_2636824 prefixEnd_2636824 1353958113311096647673473 := by
  unfold tailWord_2636824
  simp only [CollatzResearch.WordTrace]
  refine ⟨48086436099622228265706763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64115248132829637687609017 48086436099622228265706763)
  ·
    refine ⟨72129654149433342398560145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48086436099622228265706763 72129654149433342398560145)
    ·
      refine ⟨54097240612075006798920109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72129654149433342398560145 54097240612075006798920109)
      ·
        refine ⟨20286465229528127549595041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54097240612075006798920109 20286465229528127549595041)
        ·
          refine ⟨15214848922146095662196281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20286465229528127549595041 15214848922146095662196281)
          ·
            refine ⟨11411136691609571746647211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15214848922146095662196281 11411136691609571746647211)
            ·
              refine ⟨17116705037414357619970817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11411136691609571746647211 17116705037414357619970817)
              ·
                refine ⟨12837528778060768214978113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17116705037414357619970817 12837528778060768214978113)
                ·
                  refine ⟨9628146583545576161233585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12837528778060768214978113 9628146583545576161233585)
                  ·
                    refine ⟨7221109937659182120925189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9628146583545576161233585 7221109937659182120925189)
                    ·
                      refine ⟨1353958113311096647673473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7221109937659182120925189 1353958113311096647673473)
                      ·
                        rfl

theorem cell23_2636824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 2, 2, 2, 4].length) (baseStart_2636824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2636824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2636824 prefixEnd_2636824 := by exact prefixLift 2636824
  have htrace : WordTrace (prefixWord ++ tailWord_2636824) baseStart_2636824 baseEnd_2636824 := by
    simpa [prefixWord, tailWord_2636824, baseEnd_2636824] using wordTrace_append hprefix tailTrace_2636824
  have hstable : (prefixWord ++ tailWord_2636824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2636824).length < 2 ^ (prefixWord ++ tailWord_2636824).sum := by decide
  have hdescent : baseEnd_2636824 < baseStart_2636824 := by decide
  rcases family_descends (prefixWord ++ tailWord_2636824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2636834 : List Nat := [3, 3, 1, 1, 1, 3, 1, 3, 7]
def baseStart_2636834 : Nat := 118140960795 + 2636834 * 2 ^ 59
def prefixEnd_2636834 : Nat := 4983230072969 + 3 ^ 40 * 2636834 * 2
def baseEnd_2636834 : Nat := 150440360901960178727603

theorem tailTrace_2636834 : CollatzResearch.WordTrace tailWord_2636834 prefixEnd_2636834 150440360901960178727603 := by
  unfold tailWord_2636834
  simp only [CollatzResearch.WordTrace]
  refine ⟨24043309232302057059819389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64115491286138818826185037 24043309232302057059819389)
  ·
    refine ⟨9016240962113271397432271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24043309232302057059819389 9016240962113271397432271)
    ·
      refine ⟨13524361443169907096148407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9016240962113271397432271 13524361443169907096148407)
      ·
        refine ⟨20286542164754860644222611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13524361443169907096148407 20286542164754860644222611)
        ·
          refine ⟨30429813247132290966333917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20286542164754860644222611 30429813247132290966333917)
          ·
            refine ⟨11411179967674609112375219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30429813247132290966333917 11411179967674609112375219)
            ·
              refine ⟨17116769951511913668562829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11411179967674609112375219 17116769951511913668562829)
              ·
                refine ⟨6418788731816967625711061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17116769951511913668562829 6418788731816967625711061)
                ·
                  refine ⟨150440360901960178727603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6418788731816967625711061 150440360901960178727603)
                  ·
                    rfl

theorem cell23_2636834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 3, 7].length) (baseStart_2636834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2636834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2636834 prefixEnd_2636834 := by exact prefixLift 2636834
  have htrace : WordTrace (prefixWord ++ tailWord_2636834) baseStart_2636834 baseEnd_2636834 := by
    simpa [prefixWord, tailWord_2636834, baseEnd_2636834] using wordTrace_append hprefix tailTrace_2636834
  have hstable : (prefixWord ++ tailWord_2636834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2636834).length < 2 ^ (prefixWord ++ tailWord_2636834).sum := by decide
  have hdescent : baseEnd_2636834 < baseStart_2636834 := by decide
  rcases family_descends (prefixWord ++ tailWord_2636834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2636844 : List Nat := [2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 3]
def baseStart_2636844 : Nat := 118140960795 + 2636844 * 2 ^ 59
def prefixEnd_2636844 : Nat := 4983230072969 + 3 ^ 40 * 2636844 * 2
def baseEnd_2636844 : Nat := 1353968382924186569423381

theorem tailTrace_2636844 : CollatzResearch.WordTrace tailWord_2636844 prefixEnd_2636844 1353968382924186569423381 := by
  unfold tailWord_2636844
  simp only [CollatzResearch.WordTrace]
  refine ⟨48086800829585999973570793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64115734439447999964761057 48086800829585999973570793)
  ·
    refine ⟨36065100622189499980178095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48086800829585999973570793 36065100622189499980178095)
    ·
      refine ⟨54097650933284249970267143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36065100622189499980178095 54097650933284249970267143)
      ·
        refine ⟨81146476399926374955400715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54097650933284249970267143 81146476399926374955400715)
        ·
          refine ⟨121719714599889562433101073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81146476399926374955400715 121719714599889562433101073)
          ·
            refine ⟨91289785949917171824825805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121719714599889562433101073 91289785949917171824825805)
            ·
              refine ⟨34233669731218939434309677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91289785949917171824825805 34233669731218939434309677)
              ·
                refine ⟨12837626149207102287866129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34233669731218939434309677 12837626149207102287866129)
                ·
                  refine ⟨9628219611905326715899597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12837626149207102287866129 9628219611905326715899597)
                  ·
                    refine ⟨3610582354464497518462349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9628219611905326715899597 3610582354464497518462349)
                    ·
                      refine ⟨1353968382924186569423381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3610582354464497518462349 1353968382924186569423381)
                      ·
                        rfl

theorem cell23_2636844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 3].length) (baseStart_2636844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2636844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2636844 prefixEnd_2636844 := by exact prefixLift 2636844
  have htrace : WordTrace (prefixWord ++ tailWord_2636844) baseStart_2636844 baseEnd_2636844 := by
    simpa [prefixWord, tailWord_2636844, baseEnd_2636844] using wordTrace_append hprefix tailTrace_2636844
  have hstable : (prefixWord ++ tailWord_2636844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2636844).length < 2 ^ (prefixWord ++ tailWord_2636844).sum := by decide
  have hdescent : baseEnd_2636844 < baseStart_2636844 := by decide
  rcases family_descends (prefixWord ++ tailWord_2636844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2636864 : List Nat := [2, 1, 1, 2, 2, 3, 2, 3, 2, 5]
def baseStart_2636864 : Nat := 118140960795 + 2636864 * 2 ^ 59
def prefixEnd_2636864 : Nat := 4983230072969 + 3 ^ 40 * 2636864 * 2
def baseEnd_2636864 : Nat := 451326217512425497057763

theorem tailTrace_2636864 : CollatzResearch.WordTrace tailWord_2636864 prefixEnd_2636864 451326217512425497057763 := by
  unfold tailWord_2636864
  simp only [CollatzResearch.WordTrace]
  refine ⟨48087165559549771681434823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64116220746066362241913097 48087165559549771681434823)
  ·
    refine ⟨72130748339324657522152235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48087165559549771681434823 72130748339324657522152235)
    ·
      refine ⟨108196122508986986283228353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72130748339324657522152235 108196122508986986283228353)
      ·
        refine ⟨81147091881740239712421265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108196122508986986283228353 81147091881740239712421265)
        ·
          refine ⟨60860318911305179784315949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81147091881740239712421265 60860318911305179784315949)
          ·
            refine ⟨22822619591739442419118481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60860318911305179784315949 22822619591739442419118481)
            ·
              refine ⟨17116964693804581814338861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22822619591739442419118481 17116964693804581814338861)
              ·
                refine ⟨6418861760176718180377073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17116964693804581814338861 6418861760176718180377073)
                ·
                  refine ⟨4814146320132538635282805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6418861760176718180377073 4814146320132538635282805)
                  ·
                    refine ⟨451326217512425497057763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4814146320132538635282805 451326217512425497057763)
                    ·
                      rfl

theorem cell23_2636864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 3, 2, 5].length) (baseStart_2636864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2636864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2636864 prefixEnd_2636864 := by exact prefixLift 2636864
  have htrace : WordTrace (prefixWord ++ tailWord_2636864) baseStart_2636864 baseEnd_2636864 := by
    simpa [prefixWord, tailWord_2636864, baseEnd_2636864] using wordTrace_append hprefix tailTrace_2636864
  have hstable : (prefixWord ++ tailWord_2636864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2636864).length < 2 ^ (prefixWord ++ tailWord_2636864).sum := by decide
  have hdescent : baseEnd_2636864 < baseStart_2636864 := by decide
  rcases family_descends (prefixWord ++ tailWord_2636864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2636901 : List Nat := [1, 3, 1, 3, 2, 1, 2, 1, 1, 6, 2]
def baseStart_2636901 : Nat := 118140960795 + 2636901 * 2 ^ 59
def prefixEnd_2636901 : Nat := 4983230072969 + 3 ^ 40 * 2636901 * 2
def baseEnd_2636901 : Nat := 1353997651321492846410619

theorem tailTrace_2636901 : CollatzResearch.WordTrace tailWord_2636901 prefixEnd_2636901 1353997651321492846410619 := by
  unfold tailWord_2636901
  simp only [CollatzResearch.WordTrace]
  refine ⟨96175680619965498681966557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64117120413310332454644371 96175680619965498681966557)
  ·
    refine ⟨36065880232487062005737459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96175680619965498681966557 36065880232487062005737459)
    ·
      refine ⟨54098820348730593008606189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36065880232487062005737459 54098820348730593008606189)
      ·
        refine ⟨20287057630773972378227321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54098820348730593008606189 20287057630773972378227321)
        ·
          refine ⟨15215293223080479283670491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20287057630773972378227321 15215293223080479283670491)
          ·
            refine ⟨22822939834620718925505737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15215293223080479283670491 22822939834620718925505737)
            ·
              refine ⟨17117204875965539194129303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22822939834620718925505737 17117204875965539194129303)
              ·
                refine ⟨25675807313948308791193955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17117204875965539194129303 25675807313948308791193955)
                ·
                  refine ⟨38513710970922463186790933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25675807313948308791193955 38513710970922463186790933)
                  ·
                    refine ⟨1805330201761990461880825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 38513710970922463186790933 1805330201761990461880825)
                    ·
                      refine ⟨1353997651321492846410619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1805330201761990461880825 1353997651321492846410619)
                      ·
                        rfl

theorem cell23_2636901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 1, 1, 6, 2].length) (baseStart_2636901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2636901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2636901 prefixEnd_2636901 := by exact prefixLift 2636901
  have htrace : WordTrace (prefixWord ++ tailWord_2636901) baseStart_2636901 baseEnd_2636901 := by
    simpa [prefixWord, tailWord_2636901, baseEnd_2636901] using wordTrace_append hprefix tailTrace_2636901
  have hstable : (prefixWord ++ tailWord_2636901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2636901).length < 2 ^ (prefixWord ++ tailWord_2636901).sum := by decide
  have hdescent : baseEnd_2636901 < baseStart_2636901 := by decide
  rcases family_descends (prefixWord ++ tailWord_2636901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
