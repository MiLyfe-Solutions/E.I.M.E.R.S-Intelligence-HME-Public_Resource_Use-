import V185TrunkScan23Chunk0035

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_214253 : List Nat := [1, 5, 1, 2, 2, 3, 2, 1, 1, 3, 2]
def baseStart_214253 : Nat := 118140960795 + 214253 * 2 ^ 59
def prefixEnd_214253 : Nat := 4983230072969 + 3 ^ 40 * 214253 * 2
def baseEnd_214253 : Nat := 110014770667855467852175

theorem tailTrace_214253 : CollatzResearch.WordTrace tailWord_214253 prefixEnd_214253 110014770667855467852175 := by
  unfold tailWord_214253
  simp only [CollatzResearch.WordTrace]
  refine ⟨7814448892805447344311413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5209632595203631562874275 7814448892805447344311413)
  ·
    refine ⟨732604583700510688529195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7814448892805447344311413 732604583700510688529195)
    ·
      refine ⟨1098906875550766032793793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 732604583700510688529195 1098906875550766032793793)
      ·
        refine ⟨824180156663074524595345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1098906875550766032793793 824180156663074524595345)
        ·
          refine ⟨618135117497305893446509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 824180156663074524595345 618135117497305893446509)
          ·
            refine ⟨231800669061489710042441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 618135117497305893446509 231800669061489710042441)
            ·
              refine ⟨173850501796117282531831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 231800669061489710042441 173850501796117282531831)
              ·
                refine ⟨260775752694175923797747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 173850501796117282531831 260775752694175923797747)
                ·
                  refine ⟨391163629041263885696621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 260775752694175923797747 391163629041263885696621)
                  ·
                    refine ⟨146686360890473957136233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 391163629041263885696621 146686360890473957136233)
                    ·
                      refine ⟨110014770667855467852175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 146686360890473957136233 110014770667855467852175)
                      ·
                        rfl

theorem cell23_214253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 2, 1, 1, 3, 2].length) (baseStart_214253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_214253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_214253 prefixEnd_214253 := by exact prefixLift 214253
  have htrace : WordTrace (prefixWord ++ tailWord_214253) baseStart_214253 baseEnd_214253 := by
    simpa [prefixWord, tailWord_214253, baseEnd_214253] using wordTrace_append hprefix tailTrace_214253
  have hstable : (prefixWord ++ tailWord_214253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214253).length < 2 ^ (prefixWord ++ tailWord_214253).sum := by decide
  have hdescent : baseEnd_214253 < baseStart_214253 := by decide
  rcases family_descends (prefixWord ++ tailWord_214253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214265 : List Nat := [1, 2, 1, 3, 1, 1, 3, 1, 4, 3, 3]
def baseStart_214265 : Nat := 118140960795 + 214265 * 2 ^ 59
def prefixEnd_214265 : Nat := 4983230072969 + 3 ^ 40 * 214265 * 2
def baseEnd_214265 : Nat := 110020932435709420902119

theorem tailTrace_214265 : CollatzResearch.WordTrace tailWord_214265 prefixEnd_214265 110020932435709420902119 := by
  unfold tailWord_214265
  simp only [CollatzResearch.WordTrace]
  refine ⟨7814886568761973393748249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5209924379174648929165499 7814886568761973393748249)
  ·
    refine ⟨5861164926571480045311187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7814886568761973393748249 5861164926571480045311187)
    ·
      refine ⟨8791747389857220067966781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5861164926571480045311187 8791747389857220067966781)
      ·
        refine ⟨3296905271196457525487543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8791747389857220067966781 3296905271196457525487543)
        ·
          refine ⟨4945357906794686288231315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3296905271196457525487543 4945357906794686288231315)
          ·
            refine ⟨7418036860192029432346973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4945357906794686288231315 7418036860192029432346973)
            ·
              refine ⟨2781763822572011037130115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7418036860192029432346973 2781763822572011037130115)
              ·
                refine ⟨4172645733858016555695173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2781763822572011037130115 4172645733858016555695173)
                ·
                  refine ⟨782371075098378104192845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4172645733858016555695173 782371075098378104192845)
                  ·
                    refine ⟨293389153161891789072317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 782371075098378104192845 293389153161891789072317)
                    ·
                      refine ⟨110020932435709420902119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 293389153161891789072317 110020932435709420902119)
                      ·
                        rfl

theorem cell23_214265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 4, 3, 3].length) (baseStart_214265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_214265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_214265 prefixEnd_214265 := by exact prefixLift 214265
  have htrace : WordTrace (prefixWord ++ tailWord_214265) baseStart_214265 baseEnd_214265 := by
    simpa [prefixWord, tailWord_214265, baseEnd_214265] using wordTrace_append hprefix tailTrace_214265
  have hstable : (prefixWord ++ tailWord_214265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214265).length < 2 ^ (prefixWord ++ tailWord_214265).sum := by decide
  have hdescent : baseEnd_214265 < baseStart_214265 := by decide
  rcases family_descends (prefixWord ++ tailWord_214265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214306 : List Nat := [3, 3, 1, 1, 4, 2, 1, 3, 5]
def baseStart_214306 : Nat := 118140960795 + 214306 * 2 ^ 59
def prefixEnd_214306 : Nat := 4983230072969 + 3 ^ 40 * 214306 * 2
def baseEnd_214306 : Nat := 12226887238060417832159

theorem tailTrace_214306 : CollatzResearch.WordTrace tailWord_214306 prefixEnd_214306 12226887238060417832159 := by
  unfold tailWord_214306
  simp only [CollatzResearch.WordTrace]
  refine ⟨1954095490403359348997693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5210921307742291597327181 1954095490403359348997693)
  ·
    refine ⟨732785808901259755874135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1954095490403359348997693 732785808901259755874135)
    ·
      refine ⟨1099178713351889633811203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 732785808901259755874135 1099178713351889633811203)
      ·
        refine ⟨1648768070027834450716805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1099178713351889633811203 1648768070027834450716805)
        ·
          refine ⟨309144013130218959509401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1648768070027834450716805 309144013130218959509401)
          ·
            refine ⟨231858009847664219632051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 309144013130218959509401 231858009847664219632051)
            ·
              refine ⟨347787014771496329448077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 231858009847664219632051 347787014771496329448077)
              ·
                refine ⟨130420130539311123543029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 347787014771496329448077 130420130539311123543029)
                ·
                  refine ⟨12226887238060417832159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 130420130539311123543029 12226887238060417832159)
                  ·
                    rfl

theorem cell23_214306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 1, 3, 5].length) (baseStart_214306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_214306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_214306 prefixEnd_214306 := by exact prefixLift 214306
  have htrace : WordTrace (prefixWord ++ tailWord_214306) baseStart_214306 baseEnd_214306 := by
    simpa [prefixWord, tailWord_214306, baseEnd_214306] using wordTrace_append hprefix tailTrace_214306
  have hstable : (prefixWord ++ tailWord_214306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214306).length < 2 ^ (prefixWord ++ tailWord_214306).sum := by decide
  have hdescent : baseEnd_214306 < baseStart_214306 := by decide
  rcases family_descends (prefixWord ++ tailWord_214306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214322 : List Nat := [3, 2, 1, 1, 4, 1, 1, 1, 4, 1, 4]
def baseStart_214322 : Nat := 118140960795 + 214322 * 2 ^ 59
def prefixEnd_214322 : Nat := 4983230072969 + 3 ^ 40 * 214322 * 2
def baseEnd_214322 : Nat := 110050200833015697889357

theorem tailTrace_214322 : CollatzResearch.WordTrace tailWord_214322 prefixEnd_214322 110050200833015697889357 := by
  unfold tailWord_214322
  simp only [CollatzResearch.WordTrace]
  refine ⟨1954241382388868032143305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5211310353036981419048813 1954241382388868032143305)
  ·
    refine ⟨1465681036791651024107479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1954241382388868032143305 1465681036791651024107479)
    ·
      refine ⟨2198521555187476536161219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1465681036791651024107479 2198521555187476536161219)
      ·
        refine ⟨3297782332781214804241829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2198521555187476536161219 3297782332781214804241829)
        ·
          refine ⟨618334187396477775795343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3297782332781214804241829 618334187396477775795343)
          ·
            refine ⟨927501281094716663693015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 618334187396477775795343 927501281094716663693015)
            ·
              refine ⟨1391251921642074995539523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 927501281094716663693015 1391251921642074995539523)
              ·
                refine ⟨2086877882463112493309285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1391251921642074995539523 2086877882463112493309285)
                ·
                  refine ⟨391289602961833592495491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2086877882463112493309285 391289602961833592495491)
                  ·
                    refine ⟨586934404442750388743237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 391289602961833592495491 586934404442750388743237)
                    ·
                      refine ⟨110050200833015697889357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 586934404442750388743237 110050200833015697889357)
                      ·
                        rfl

theorem cell23_214322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 1, 4, 1, 4].length) (baseStart_214322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_214322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_214322 prefixEnd_214322 := by exact prefixLift 214322
  have htrace : WordTrace (prefixWord ++ tailWord_214322) baseStart_214322 baseEnd_214322 := by
    simpa [prefixWord, tailWord_214322, baseEnd_214322] using wordTrace_append hprefix tailTrace_214322
  have hstable : (prefixWord ++ tailWord_214322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214322).length < 2 ^ (prefixWord ++ tailWord_214322).sum := by decide
  have hdescent : baseEnd_214322 < baseStart_214322 := by decide
  rcases family_descends (prefixWord ++ tailWord_214322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214359 : List Nat := [1, 1, 3, 2, 3, 3, 2, 1, 2, 2, 3]
def baseStart_214359 : Nat := 118140960795 + 214359 * 2 ^ 59
def prefixEnd_214359 : Nat := 4983230072969 + 3 ^ 40 * 214359 * 2
def baseEnd_214359 : Nat := 110069199617232053126687

theorem tailTrace_214359 : CollatzResearch.WordTrace tailWord_214359 prefixEnd_214359 110069199617232053126687 := by
  unfold tailWord_214359
  simp only [CollatzResearch.WordTrace]
  refine ⟨7818315030421427447670131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5212210020280951631780087 7818315030421427447670131)
  ·
    refine ⟨11727472545632141171505197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7818315030421427447670131 11727472545632141171505197)
    ·
      refine ⟨4397802204612052939314449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11727472545632141171505197 4397802204612052939314449)
      ·
        refine ⟨3298351653459039704485837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4397802204612052939314449 3298351653459039704485837)
        ·
          refine ⟨1236881870047139889182189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3298351653459039704485837 1236881870047139889182189)
          ·
            refine ⟨463830701267677458443321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1236881870047139889182189 463830701267677458443321)
            ·
              refine ⟨347873025950758093832491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 463830701267677458443321 347873025950758093832491)
              ·
                refine ⟨521809538926137140748737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 347873025950758093832491 521809538926137140748737)
                ·
                  refine ⟨391357154194602855561553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 521809538926137140748737 391357154194602855561553)
                  ·
                    refine ⟨293517865645952141671165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 391357154194602855561553 293517865645952141671165)
                    ·
                      refine ⟨110069199617232053126687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 293517865645952141671165 110069199617232053126687)
                      ·
                        rfl

theorem cell23_214359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2, 1, 2, 2, 3].length) (baseStart_214359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_214359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_214359 prefixEnd_214359 := by exact prefixLift 214359
  have htrace : WordTrace (prefixWord ++ tailWord_214359) baseStart_214359 baseEnd_214359 := by
    simpa [prefixWord, tailWord_214359, baseEnd_214359] using wordTrace_append hprefix tailTrace_214359
  have hstable : (prefixWord ++ tailWord_214359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214359).length < 2 ^ (prefixWord ++ tailWord_214359).sum := by decide
  have hdescent : baseEnd_214359 < baseStart_214359 := by decide
  rcases family_descends (prefixWord ++ tailWord_214359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214412 : List Nat := [2, 2, 1, 2, 1, 3, 1, 3, 3, 1, 4]
def baseStart_214412 : Nat := 118140960795 + 214412 * 2 ^ 59
def prefixEnd_214412 : Nat := 4983230072969 + 3 ^ 40 * 214412 * 2
def baseEnd_214412 : Nat := 110096414091920345763943

theorem tailTrace_214412 : CollatzResearch.WordTrace tailWord_214412 prefixEnd_214412 110096414091920345763943 := by
  unfold tailWord_214412
  simp only [CollatzResearch.WordTrace]
  refine ⟨3910124049614708749674745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5213498732819611666232993 3910124049614708749674745)
  ·
    refine ⟨2932593037211031562256059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3910124049614708749674745 2932593037211031562256059)
    ·
      refine ⟨4398889555816547343384089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2932593037211031562256059 4398889555816547343384089)
      ·
        refine ⟨3299167166862410507538067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4398889555816547343384089 3299167166862410507538067)
        ·
          refine ⟨4948750750293615761307101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3299167166862410507538067 4948750750293615761307101)
          ·
            refine ⟨1855781531360105910490163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4948750750293615761307101 1855781531360105910490163)
            ·
              refine ⟨2783672297040158865735245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1855781531360105910490163 2783672297040158865735245)
              ·
                refine ⟨1043877111390059574650717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2783672297040158865735245 1043877111390059574650717)
                ·
                  refine ⟨391453916771272340494019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1043877111390059574650717 391453916771272340494019)
                  ·
                    refine ⟨587180875156908510741029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 391453916771272340494019 587180875156908510741029)
                    ·
                      refine ⟨110096414091920345763943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 587180875156908510741029 110096414091920345763943)
                      ·
                        rfl

theorem cell23_214412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 3, 3, 1, 4].length) (baseStart_214412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_214412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_214412 prefixEnd_214412 := by exact prefixLift 214412
  have htrace : WordTrace (prefixWord ++ tailWord_214412) baseStart_214412 baseEnd_214412 := by
    simpa [prefixWord, tailWord_214412, baseEnd_214412] using wordTrace_append hprefix tailTrace_214412
  have hstable : (prefixWord ++ tailWord_214412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214412).length < 2 ^ (prefixWord ++ tailWord_214412).sum := by decide
  have hdescent : baseEnd_214412 < baseStart_214412 := by decide
  rcases family_descends (prefixWord ++ tailWord_214412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214432 : List Nat := [2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 5]
def baseStart_214432 : Nat := 118140960795 + 214432 * 2 ^ 59
def prefixEnd_214432 : Nat := 4983230072969 + 3 ^ 40 * 214432 * 2
def baseEnd_214432 : Nat := 110106683705010267513851

theorem tailTrace_214432 : CollatzResearch.WordTrace tailWord_214432 prefixEnd_214432 110106683705010267513851 := by
  unfold tailWord_214432
  simp only [CollatzResearch.WordTrace]
  refine ⟨3910488779578480457538775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5213985039437973943385033 3910488779578480457538775)
  ·
    refine ⟨5865733169367720686308163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3910488779578480457538775 5865733169367720686308163)
    ·
      refine ⟨8798599754051581029462245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5865733169367720686308163 8798599754051581029462245)
      ·
        refine ⟨1649737453884671443024171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8798599754051581029462245 1649737453884671443024171)
        ·
          refine ⟨2474606180827007164536257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1649737453884671443024171 2474606180827007164536257)
          ·
            refine ⟨1855954635620255373402193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2474606180827007164536257 1855954635620255373402193)
            ·
              refine ⟨1391965976715191530051645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1855954635620255373402193 1391965976715191530051645)
              ·
                refine ⟨521987241268196823769367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1391965976715191530051645 521987241268196823769367)
                ·
                  refine ⟨782980861902295235654051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 521987241268196823769367 782980861902295235654051)
                  ·
                    refine ⟨1174471292853442853481077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 782980861902295235654051 1174471292853442853481077)
                    ·
                      refine ⟨110106683705010267513851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1174471292853442853481077 110106683705010267513851)
                      ·
                        rfl

theorem cell23_214432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 5].length) (baseStart_214432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_214432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_214432 prefixEnd_214432 := by exact prefixLift 214432
  have htrace : WordTrace (prefixWord ++ tailWord_214432) baseStart_214432 baseEnd_214432 := by
    simpa [prefixWord, tailWord_214432, baseEnd_214432] using wordTrace_append hprefix tailTrace_214432
  have hstable : (prefixWord ++ tailWord_214432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214432).length < 2 ^ (prefixWord ++ tailWord_214432).sum := by decide
  have hdescent : baseEnd_214432 < baseStart_214432 := by decide
  rcases family_descends (prefixWord ++ tailWord_214432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214435 : List Nat := [1, 1, 1, 4, 1, 3, 12]
def baseStart_214435 : Nat := 118140960795 + 214435 * 2 ^ 59
def prefixEnd_214435 : Nat := 4983230072969 + 3 ^ 40 * 214435 * 2
def baseEnd_214435 : Nat := 1359360791937947602177

theorem tailTrace_214435 : CollatzResearch.WordTrace tailWord_214435 prefixEnd_214435 1359360791937947602177 := by
  unfold tailWord_214435
  simp only [CollatzResearch.WordTrace]
  refine ⟨7821086978146092427436759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5214057985430728284957839 7821086978146092427436759)
  ·
    refine ⟨11731630467219138641155139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7821086978146092427436759 11731630467219138641155139)
    ·
      refine ⟨17597445700828707961732709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11731630467219138641155139 17597445700828707961732709)
      ·
        refine ⟨3299521068905382742824883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17597445700828707961732709 3299521068905382742824883)
        ·
          refine ⟨4949281603358074114237325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3299521068905382742824883 4949281603358074114237325)
          ·
            refine ⟨1855980601259277792838997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4949281603358074114237325 1855980601259277792838997)
            ·
              refine ⟨1359360791937947602177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 1855980601259277792838997 1359360791937947602177)
              ·
                rfl

theorem cell23_214435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 12].length) (baseStart_214435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_214435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_214435 prefixEnd_214435 := by exact prefixLift 214435
  have htrace : WordTrace (prefixWord ++ tailWord_214435) baseStart_214435 baseEnd_214435 := by
    simpa [prefixWord, tailWord_214435, baseEnd_214435] using wordTrace_append hprefix tailTrace_214435
  have hstable : (prefixWord ++ tailWord_214435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214435).length < 2 ^ (prefixWord ++ tailWord_214435).sum := by decide
  have hdescent : baseEnd_214435 < baseStart_214435 := by decide
  rcases family_descends (prefixWord ++ tailWord_214435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214439 : List Nat := [1, 1, 6, 1, 1, 1, 3, 1, 4, 4]
def baseStart_214439 : Nat := 118140960795 + 214439 * 2 ^ 59
def prefixEnd_214439 : Nat := 4983230072969 + 3 ^ 40 * 214439 * 2
def baseEnd_214439 : Nat := 36703426023197246708773

theorem tailTrace_214439 : CollatzResearch.WordTrace tailWord_214439 prefixEnd_214439 36703426023197246708773 := by
  unfold tailWord_214439
  simp only [CollatzResearch.WordTrace]
  refine ⟨7821232870131601110582371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5214155246754400740388247 7821232870131601110582371)
  ·
    refine ⟨11731849305197401665873557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7821232870131601110582371 11731849305197401665873557)
    ·
      refine ⟨549930436181128203087823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 11731849305197401665873557 549930436181128203087823)
      ·
        refine ⟨824895654271692304631735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 549930436181128203087823 824895654271692304631735)
        ·
          refine ⟨1237343481407538456947603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 824895654271692304631735 1237343481407538456947603)
          ·
            refine ⟨1856015222111307685421405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1237343481407538456947603 1856015222111307685421405)
            ·
              refine ⟨696005708291740382033027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1856015222111307685421405 696005708291740382033027)
              ·
                refine ⟨1044008562437610573049541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 696005708291740382033027 1044008562437610573049541)
                ·
                  refine ⟨195751605457051982446789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1044008562437610573049541 195751605457051982446789)
                  ·
                    refine ⟨36703426023197246708773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 195751605457051982446789 36703426023197246708773)
                    ·
                      rfl

theorem cell23_214439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 1, 4, 4].length) (baseStart_214439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_214439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_214439 prefixEnd_214439 := by exact prefixLift 214439
  have htrace : WordTrace (prefixWord ++ tailWord_214439) baseStart_214439 baseEnd_214439 := by
    simpa [prefixWord, tailWord_214439, baseEnd_214439] using wordTrace_append hprefix tailTrace_214439
  have hstable : (prefixWord ++ tailWord_214439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214439).length < 2 ^ (prefixWord ++ tailWord_214439).sum := by decide
  have hdescent : baseEnd_214439 < baseStart_214439 := by decide
  rcases family_descends (prefixWord ++ tailWord_214439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214479 : List Nat := [1, 1, 2, 1, 1, 4, 3, 2, 4, 1, 3]
def baseStart_214479 : Nat := 118140960795 + 214479 * 2 ^ 59
def prefixEnd_214479 : Nat := 4983230072969 + 3 ^ 40 * 214479 * 2
def baseEnd_214479 : Nat := 110130817295771583626135

theorem tailTrace_214479 : CollatzResearch.WordTrace tailWord_214479 prefixEnd_214479 110130817295771583626135 := by
  unfold tailWord_214479
  simp only [CollatzResearch.WordTrace]
  refine ⟨7822691789986687942038491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5215127859991125294692327 7822691789986687942038491)
  ·
    refine ⟨11734037684980031913057737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7822691789986687942038491 11734037684980031913057737)
    ·
      refine ⟨8800528263735023934793303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11734037684980031913057737 8800528263735023934793303)
      ·
        refine ⟨13200792395602535902189955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8800528263735023934793303 13200792395602535902189955)
        ·
          refine ⟨19801188593403803853284933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13200792395602535902189955 19801188593403803853284933)
          ·
            refine ⟨3712722861263213222490925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19801188593403803853284933 3712722861263213222490925)
            ·
              refine ⟨1392271072973704958434097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3712722861263213222490925 1392271072973704958434097)
              ·
                refine ⟨1044203304730278718825573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1392271072973704958434097 1044203304730278718825573)
                ·
                  refine ⟨195788119636927259779795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1044203304730278718825573 195788119636927259779795)
                  ·
                    refine ⟨293682179455390889669693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 195788119636927259779795 293682179455390889669693)
                    ·
                      refine ⟨110130817295771583626135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 293682179455390889669693 110130817295771583626135)
                      ·
                        rfl

theorem cell23_214479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 2, 4, 1, 3].length) (baseStart_214479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_214479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_214479 prefixEnd_214479 := by exact prefixLift 214479
  have htrace : WordTrace (prefixWord ++ tailWord_214479) baseStart_214479 baseEnd_214479 := by
    simpa [prefixWord, tailWord_214479, baseEnd_214479] using wordTrace_append hprefix tailTrace_214479
  have hstable : (prefixWord ++ tailWord_214479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214479).length < 2 ^ (prefixWord ++ tailWord_214479).sum := by decide
  have hdescent : baseEnd_214479 < baseStart_214479 := by decide
  rcases family_descends (prefixWord ++ tailWord_214479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214513 : List Nat := [1, 2, 2, 2, 3, 2, 4, 1, 2, 1, 3]
def baseStart_214513 : Nat := 118140960795 + 214513 * 2 ^ 59
def prefixEnd_214513 : Nat := 4983230072969 + 3 ^ 40 * 214513 * 2
def baseEnd_214513 : Nat := 110148275638024450600979

theorem tailTrace_214513 : CollatzResearch.WordTrace tailWord_214513 prefixEnd_214513 110148275638024450600979 := by
  unfold tailWord_214513
  simp only [CollatzResearch.WordTrace]
  refine ⟨7823931871863511748776193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5215954581242341165850795 7823931871863511748776193)
  ·
    refine ⟨5867948903897633811582145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7823931871863511748776193 5867948903897633811582145)
    ·
      refine ⟨4400961677923225358686609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5867948903897633811582145 4400961677923225358686609)
      ·
        refine ⟨3300721258442419019014957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4400961677923225358686609 3300721258442419019014957)
        ·
          refine ⟨1237770471915907132130609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3300721258442419019014957 1237770471915907132130609)
          ·
            refine ⟨928327853936930349097957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1237770471915907132130609 928327853936930349097957)
            ·
              refine ⟨174061472613174440455867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 928327853936930349097957 174061472613174440455867)
              ·
                refine ⟨261092208919761660683801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 174061472613174440455867 261092208919761660683801)
                ·
                  refine ⟨195819156689821245512851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 261092208919761660683801 195819156689821245512851)
                  ·
                    refine ⟨293728735034731868269277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 195819156689821245512851 293728735034731868269277)
                    ·
                      refine ⟨110148275638024450600979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 293728735034731868269277 110148275638024450600979)
                      ·
                        rfl

theorem cell23_214513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 4, 1, 2, 1, 3].length) (baseStart_214513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_214513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_214513 prefixEnd_214513 := by exact prefixLift 214513
  have htrace : WordTrace (prefixWord ++ tailWord_214513) baseStart_214513 baseEnd_214513 := by
    simpa [prefixWord, tailWord_214513, baseEnd_214513] using wordTrace_append hprefix tailTrace_214513
  have hstable : (prefixWord ++ tailWord_214513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214513).length < 2 ^ (prefixWord ++ tailWord_214513).sum := by decide
  have hdescent : baseEnd_214513 < baseStart_214513 := by decide
  rcases family_descends (prefixWord ++ tailWord_214513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214522 : List Nat := [3, 1, 1, 1, 1, 2, 3, 1, 4, 1, 5]
def baseStart_214522 : Nat := 118140960795 + 214522 * 2 ^ 59
def prefixEnd_214522 : Nat := 4983230072969 + 3 ^ 40 * 214522 * 2
def baseEnd_214522 : Nat := 110152896963914915388437

theorem tailTrace_214522 : CollatzResearch.WordTrace tailWord_214522 prefixEnd_214522 110152896963914915388437 := by
  unfold tailWord_214522
  simp only [CollatzResearch.WordTrace]
  refine ⟨1956065032207726571463455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5216173419220604190569213 1956065032207726571463455)
  ·
    refine ⟨2934097548311589857195183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1956065032207726571463455 2934097548311589857195183)
    ·
      refine ⟨4401146322467384785792775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2934097548311589857195183 4401146322467384785792775)
      ·
        refine ⟨6601719483701077178689163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4401146322467384785792775 6601719483701077178689163)
        ·
          refine ⟨9902579225551615768033745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6601719483701077178689163 9902579225551615768033745)
          ·
            refine ⟨7426934419163711826025309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9902579225551615768033745 7426934419163711826025309)
            ·
              refine ⟨2785100407186391934759491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7426934419163711826025309 2785100407186391934759491)
              ·
                refine ⟨4177650610779587902139237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2785100407186391934759491 4177650610779587902139237)
                ·
                  refine ⟨783309489521172731651107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4177650610779587902139237 783309489521172731651107)
                  ·
                    refine ⟨1174964234281759097476661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 783309489521172731651107 1174964234281759097476661)
                    ·
                      refine ⟨110152896963914915388437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1174964234281759097476661 110152896963914915388437)
                      ·
                        rfl

theorem cell23_214522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 4, 1, 5].length) (baseStart_214522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_214522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_214522 prefixEnd_214522 := by exact prefixLift 214522
  have htrace : WordTrace (prefixWord ++ tailWord_214522) baseStart_214522 baseEnd_214522 := by
    simpa [prefixWord, tailWord_214522, baseEnd_214522] using wordTrace_append hprefix tailTrace_214522
  have hstable : (prefixWord ++ tailWord_214522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214522).length < 2 ^ (prefixWord ++ tailWord_214522).sum := by decide
  have hdescent : baseEnd_214522 < baseStart_214522 := by decide
  rcases family_descends (prefixWord ++ tailWord_214522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214534 : List Nat := [6, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3]
def baseStart_214534 : Nat := 118140960795 + 214534 * 2 ^ 59
def prefixEnd_214534 : Nat := 4983230072969 + 3 ^ 40 * 214534 * 2
def baseEnd_214534 : Nat := 110159058731768868438383

theorem tailTrace_214534 : CollatzResearch.WordTrace tailWord_214534 prefixEnd_214534 110159058731768868438383 := by
  unfold tailWord_214534
  simp only [CollatzResearch.WordTrace]
  refine ⟨244521806399607260477833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 5216465203191621556860437 244521806399607260477833)
  ·
    refine ⟨183391354799705445358375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244521806399607260477833 183391354799705445358375)
    ·
      refine ⟨275087032199558168037563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183391354799705445358375 275087032199558168037563)
      ·
        refine ⟨412630548299337252056345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275087032199558168037563 412630548299337252056345)
        ·
          refine ⟨309472911224502939042259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 412630548299337252056345 309472911224502939042259)
          ·
            refine ⟨464209366836754408563389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 309472911224502939042259 464209366836754408563389)
            ·
              refine ⟨174078512563782903211271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 464209366836754408563389 174078512563782903211271)
              ·
                refine ⟨261117768845674354816907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 174078512563782903211271 261117768845674354816907)
                ·
                  refine ⟨391676653268511532225361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 261117768845674354816907 391676653268511532225361)
                  ·
                    refine ⟨293757489951383649169021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 391676653268511532225361 293757489951383649169021)
                    ·
                      refine ⟨110159058731768868438383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 293757489951383649169021 110159058731768868438383)
                      ·
                        rfl

theorem cell23_214534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3].length) (baseStart_214534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_214534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_214534 prefixEnd_214534 := by exact prefixLift 214534
  have htrace : WordTrace (prefixWord ++ tailWord_214534) baseStart_214534 baseEnd_214534 := by
    simpa [prefixWord, tailWord_214534, baseEnd_214534] using wordTrace_append hprefix tailTrace_214534
  have hstable : (prefixWord ++ tailWord_214534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214534).length < 2 ^ (prefixWord ++ tailWord_214534).sum := by decide
  have hdescent : baseEnd_214534 < baseStart_214534 := by decide
  rcases family_descends (prefixWord ++ tailWord_214534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214536 : List Nat := [2, 1, 3, 2, 1, 1, 2, 1, 6, 2, 2]
def baseStart_214536 : Nat := 118140960795 + 214536 * 2 ^ 59
def prefixEnd_214536 : Nat := 4983230072969 + 3 ^ 40 * 214536 * 2
def baseEnd_214536 : Nat := 110160085693077860613373

theorem tailTrace_214536 : CollatzResearch.WordTrace tailWord_214536 prefixEnd_214536 110160085693077860613373 := by
  unfold tailWord_214536
  simp only [CollatzResearch.WordTrace]
  refine ⟨3912385375390093338431731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5216513833853457784575641 3912385375390093338431731)
  ·
    refine ⟨5868578063085140007647597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3912385375390093338431731 5868578063085140007647597)
    ·
      refine ⟨2200716773656927502867849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5868578063085140007647597 2200716773656927502867849)
      ·
        refine ⟨1650537580242695627150887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2200716773656927502867849 1650537580242695627150887)
        ·
          refine ⟨2475806370364043440726331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1650537580242695627150887 2475806370364043440726331)
          ·
            refine ⟨3713709555546065161089497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2475806370364043440726331 3713709555546065161089497)
            ·
              refine ⟨2785282166659548870817123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3713709555546065161089497 2785282166659548870817123)
              ·
                refine ⟨4177923249989323306225685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2785282166659548870817123 4177923249989323306225685)
                ·
                  refine ⟨195840152343249529979329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4177923249989323306225685 195840152343249529979329)
                  ·
                    refine ⟨146880114257437147484497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 195840152343249529979329 146880114257437147484497)
                    ·
                      refine ⟨110160085693077860613373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 146880114257437147484497 110160085693077860613373)
                      ·
                        rfl

theorem cell23_214536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 6, 2, 2].length) (baseStart_214536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_214536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_214536 prefixEnd_214536 := by exact prefixLift 214536
  have htrace : WordTrace (prefixWord ++ tailWord_214536) baseStart_214536 baseEnd_214536 := by
    simpa [prefixWord, tailWord_214536, baseEnd_214536] using wordTrace_append hprefix tailTrace_214536
  have hstable : (prefixWord ++ tailWord_214536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214536).length < 2 ^ (prefixWord ++ tailWord_214536).sum := by decide
  have hdescent : baseEnd_214536 < baseStart_214536 := by decide
  rcases family_descends (prefixWord ++ tailWord_214536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214540 : List Nat := [2, 2, 1, 2, 5, 1, 3, 1, 1, 3, 2]
def baseStart_214540 : Nat := 118140960795 + 214540 * 2 ^ 59
def prefixEnd_214540 : Nat := 4983230072969 + 3 ^ 40 * 214540 * 2
def baseEnd_214540 : Nat := 110162139615695844963355

theorem tailTrace_214540 : CollatzResearch.WordTrace tailWord_214540 prefixEnd_214540 110162139615695844963355 := by
  unfold tailWord_214540
  simp only [CollatzResearch.WordTrace]
  refine ⟨3912458321382847680004537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5216611095177130240006049 3912458321382847680004537)
  ·
    refine ⟨2934343741037135760003403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3912458321382847680004537 2934343741037135760003403)
    ·
      refine ⟨4401515611555703640005105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2934343741037135760003403 4401515611555703640005105)
      ·
        refine ⟨3301136708666777730003829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4401515611555703640005105 3301136708666777730003829)
        ·
          refine ⟨309481566437510412187859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3301136708666777730003829 309481566437510412187859)
          ·
            refine ⟨464222349656265618281789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 309481566437510412187859 464222349656265618281789)
            ·
              refine ⟨174083381121099606855671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 464222349656265618281789 174083381121099606855671)
              ·
                refine ⟨261125071681649410283507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 174083381121099606855671 261125071681649410283507)
                ·
                  refine ⟨391687607522474115425261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 261125071681649410283507 391687607522474115425261)
                  ·
                    refine ⟨146882852820927793284473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 391687607522474115425261 146882852820927793284473)
                    ·
                      refine ⟨110162139615695844963355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 146882852820927793284473 110162139615695844963355)
                      ·
                        rfl

theorem cell23_214540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 3, 1, 1, 3, 2].length) (baseStart_214540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_214540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_214540 prefixEnd_214540 := by exact prefixLift 214540
  have htrace : WordTrace (prefixWord ++ tailWord_214540) baseStart_214540 baseEnd_214540 := by
    simpa [prefixWord, tailWord_214540, baseEnd_214540] using wordTrace_append hprefix tailTrace_214540
  have hstable : (prefixWord ++ tailWord_214540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214540).length < 2 ^ (prefixWord ++ tailWord_214540).sum := by decide
  have hdescent : baseEnd_214540 < baseStart_214540 := by decide
  rcases family_descends (prefixWord ++ tailWord_214540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214609 : List Nat := [1, 2, 2, 1, 3, 2, 2, 1, 4, 1, 4]
def baseStart_214609 : Nat := 118140960795 + 214609 * 2 ^ 59
def prefixEnd_214609 : Nat := 4983230072969 + 3 ^ 40 * 214609 * 2
def baseEnd_214609 : Nat := 110197569780856075000537

theorem tailTrace_214609 : CollatzResearch.WordTrace tailWord_214609 prefixEnd_214609 110197569780856075000537 := by
  unfold tailWord_214609
  simp only [CollatzResearch.WordTrace]
  refine ⟨7827433279515720144270881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5218288853010480096180587 7827433279515720144270881)
  ·
    refine ⟨5870574959636790108203161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7827433279515720144270881 5870574959636790108203161)
    ·
      refine ⟨4402931219727592581152371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5870574959636790108203161 4402931219727592581152371)
      ·
        refine ⟨6604396829591388871728557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4402931219727592581152371 6604396829591388871728557)
        ·
          refine ⟨2476648811096770826898209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6604396829591388871728557 2476648811096770826898209)
          ·
            refine ⟨1857486608322578120173657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2476648811096770826898209 1857486608322578120173657)
            ·
              refine ⟨1393114956241933590130243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1857486608322578120173657 1393114956241933590130243)
              ·
                refine ⟨2089672434362900385195365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1393114956241933590130243 2089672434362900385195365)
                ·
                  refine ⟨391813581443043822224131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2089672434362900385195365 391813581443043822224131)
                  ·
                    refine ⟨587720372164565733336197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 391813581443043822224131 587720372164565733336197)
                    ·
                      refine ⟨110197569780856075000537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 587720372164565733336197 110197569780856075000537)
                      ·
                        rfl

theorem cell23_214609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 1, 4, 1, 4].length) (baseStart_214609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_214609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_214609 prefixEnd_214609 := by exact prefixLift 214609
  have htrace : WordTrace (prefixWord ++ tailWord_214609) baseStart_214609 baseEnd_214609 := by
    simpa [prefixWord, tailWord_214609, baseEnd_214609] using wordTrace_append hprefix tailTrace_214609
  have hstable : (prefixWord ++ tailWord_214609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214609).length < 2 ^ (prefixWord ++ tailWord_214609).sum := by decide
  have hdescent : baseEnd_214609 < baseStart_214609 := by decide
  rcases family_descends (prefixWord ++ tailWord_214609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214703 : List Nat := [1, 1, 2, 1, 2, 4, 4, 1, 2, 3, 2]
def baseStart_214703 : Nat := 118140960795 + 214703 * 2 ^ 59
def prefixEnd_214703 : Nat := 4983230072969 + 3 ^ 40 * 214703 * 2
def baseEnd_214703 : Nat := 110245836962378707225105

theorem tailTrace_214703 : CollatzResearch.WordTrace tailWord_214703 prefixEnd_214703 110245836962378707225105 := by
  unfold tailWord_214703
  simp only [CollatzResearch.WordTrace]
  refine ⟨7830861741175174198192763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5220574494116782798795175 7830861741175174198192763)
  ·
    refine ⟨11746292611762761297289145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7830861741175174198192763 11746292611762761297289145)
    ·
      refine ⟨8809719458822070972966859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11746292611762761297289145 8809719458822070972966859)
      ·
        refine ⟨13214579188233106459450289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8809719458822070972966859 13214579188233106459450289)
        ·
          refine ⟨9910934391174829844587717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13214579188233106459450289 9910934391174829844587717)
          ·
            refine ⟨1858300198345280595860197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9910934391174829844587717 1858300198345280595860197)
            ·
              refine ⟨348431287189740111723787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1858300198345280595860197 348431287189740111723787)
              ·
                refine ⟨522646930784610167585681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 348431287189740111723787 522646930784610167585681)
                ·
                  refine ⟨391985198088457625689261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 522646930784610167585681 391985198088457625689261)
                  ·
                    refine ⟨146994449283171609633473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 391985198088457625689261 146994449283171609633473)
                    ·
                      refine ⟨110245836962378707225105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 146994449283171609633473 110245836962378707225105)
                      ·
                        rfl

theorem cell23_214703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4, 1, 2, 3, 2].length) (baseStart_214703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_214703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_214703 prefixEnd_214703 := by exact prefixLift 214703
  have htrace : WordTrace (prefixWord ++ tailWord_214703) baseStart_214703 baseEnd_214703 := by
    simpa [prefixWord, tailWord_214703, baseEnd_214703] using wordTrace_append hprefix tailTrace_214703
  have hstable : (prefixWord ++ tailWord_214703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214703).length < 2 ^ (prefixWord ++ tailWord_214703).sum := by decide
  have hdescent : baseEnd_214703 < baseStart_214703 := by decide
  rcases family_descends (prefixWord ++ tailWord_214703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214746 : List Nat := [3, 1, 1, 2, 2, 3, 1, 3, 1, 2, 4]
def baseStart_214746 : Nat := 118140960795 + 214746 * 2 ^ 59
def prefixEnd_214746 : Nat := 4983230072969 + 3 ^ 40 * 214746 * 2
def baseEnd_214746 : Nat := 110267916630522038987407

theorem tailTrace_214746 : CollatzResearch.WordTrace tailWord_214746 prefixEnd_214746 110267916630522038987407 := by
  unfold tailWord_214746
  simp only [CollatzResearch.WordTrace]
  refine ⟨1958107520004848135502023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5221620053346261694672061 1958107520004848135502023)
  ·
    refine ⟨2937161280007272203253035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1958107520004848135502023 2937161280007272203253035)
    ·
      refine ⟨4405741920010908304879553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2937161280007272203253035 4405741920010908304879553)
      ·
        refine ⟨3304306440008181228659665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4405741920010908304879553 3304306440008181228659665)
        ·
          refine ⟨2478229830006135921494749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3304306440008181228659665 2478229830006135921494749)
          ·
            refine ⟨929336186252300970560531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2478229830006135921494749 929336186252300970560531)
            ·
              refine ⟨1394004279378451455840797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 929336186252300970560531 1394004279378451455840797)
              ·
                refine ⟨522751604766919295940299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1394004279378451455840797 522751604766919295940299)
                ·
                  refine ⟨784127407150378943910449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 522751604766919295940299 784127407150378943910449)
                  ·
                    refine ⟨588095555362784207932837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 784127407150378943910449 588095555362784207932837)
                    ·
                      refine ⟨110267916630522038987407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 588095555362784207932837 110267916630522038987407)
                      ·
                        rfl

theorem cell23_214746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 3, 1, 2, 4].length) (baseStart_214746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_214746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_214746 prefixEnd_214746 := by exact prefixLift 214746
  have htrace : WordTrace (prefixWord ++ tailWord_214746) baseStart_214746 baseEnd_214746 := by
    simpa [prefixWord, tailWord_214746, baseEnd_214746] using wordTrace_append hprefix tailTrace_214746
  have hstable : (prefixWord ++ tailWord_214746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214746).length < 2 ^ (prefixWord ++ tailWord_214746).sum := by decide
  have hdescent : baseEnd_214746 < baseStart_214746 := by decide
  rcases family_descends (prefixWord ++ tailWord_214746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214756 : List Nat := [2, 3, 1, 1, 1, 3, 5, 7]
def baseStart_214756 : Nat := 118140960795 + 214756 * 2 ^ 59
def prefixEnd_214756 : Nat := 4983230072969 + 3 ^ 40 * 214756 * 2
def baseEnd_214756 : Nat := 4084187090261740735643

theorem tailTrace_214756 : CollatzResearch.WordTrace tailWord_214756 prefixEnd_214756 4084187090261740735643 := by
  unfold tailWord_214756
  simp only [CollatzResearch.WordTrace]
  refine ⟨3916397404991582124936061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5221863206655442833248081 3916397404991582124936061)
  ·
    refine ⟨1468649026871843296851023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3916397404991582124936061 1468649026871843296851023)
    ·
      refine ⟨2202973540307764945276535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1468649026871843296851023 2202973540307764945276535)
      ·
        refine ⟨3304460310461647417914803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2202973540307764945276535 3304460310461647417914803)
        ·
          refine ⟨4956690465692471126872205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3304460310461647417914803 4956690465692471126872205)
          ·
            refine ⟨1858758924634676672577077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4956690465692471126872205 1858758924634676672577077)
            ·
              refine ⟨174258649184500938054101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1858758924634676672577077 174258649184500938054101)
              ·
                refine ⟨4084187090261740735643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 174258649184500938054101 4084187090261740735643)
                ·
                  rfl

theorem cell23_214756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 5, 7].length) (baseStart_214756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_214756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_214756 prefixEnd_214756 := by exact prefixLift 214756
  have htrace : WordTrace (prefixWord ++ tailWord_214756) baseStart_214756 baseEnd_214756 := by
    simpa [prefixWord, tailWord_214756, baseEnd_214756] using wordTrace_append hprefix tailTrace_214756
  have hstable : (prefixWord ++ tailWord_214756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214756).length < 2 ^ (prefixWord ++ tailWord_214756).sum := by decide
  have hdescent : baseEnd_214756 < baseStart_214756 := by decide
  rcases family_descends (prefixWord ++ tailWord_214756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214767 : List Nat := [1, 1, 2, 1, 5, 1, 4, 3, 1, 2, 2]
def baseStart_214767 : Nat := 118140960795 + 214767 * 2 ^ 59
def prefixEnd_214767 : Nat := 4983230072969 + 3 ^ 40 * 214767 * 2
def baseEnd_214767 : Nat := 110278699724266456824811

theorem tailTrace_214767 : CollatzResearch.WordTrace tailWord_214767 prefixEnd_214767 110278699724266456824811 := by
  unfold tailWord_214767
  simp only [CollatzResearch.WordTrace]
  refine ⟨7833196012943313128522555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5222130675295542085681703 7833196012943313128522555)
  ·
    refine ⟨11749794019414969692783833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7833196012943313128522555 11749794019414969692783833)
    ·
      refine ⟨8812345514561227269587875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11749794019414969692783833 8812345514561227269587875)
      ·
        refine ⟨13218518271841840904381813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8812345514561227269587875 13218518271841840904381813)
        ·
          refine ⟨1239236087985172584785795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13218518271841840904381813 1239236087985172584785795)
          ·
            refine ⟨1858854131977758877178693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1239236087985172584785795 1858854131977758877178693)
            ·
              refine ⟨348535149745829789471005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1858854131977758877178693 348535149745829789471005)
              ·
                refine ⟨130700681154686171051627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 348535149745829789471005 130700681154686171051627)
                ·
                  refine ⟨196051021732029256577441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 130700681154686171051627 196051021732029256577441)
                  ·
                    refine ⟨147038266299021942433081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 196051021732029256577441 147038266299021942433081)
                    ·
                      refine ⟨110278699724266456824811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 147038266299021942433081 110278699724266456824811)
                      ·
                        rfl

theorem cell23_214767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4, 3, 1, 2, 2].length) (baseStart_214767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_214767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_214767 prefixEnd_214767 := by exact prefixLift 214767
  have htrace : WordTrace (prefixWord ++ tailWord_214767) baseStart_214767 baseEnd_214767 := by
    simpa [prefixWord, tailWord_214767, baseEnd_214767] using wordTrace_append hprefix tailTrace_214767
  have hstable : (prefixWord ++ tailWord_214767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214767).length < 2 ^ (prefixWord ++ tailWord_214767).sum := by decide
  have hdescent : baseEnd_214767 < baseStart_214767 := by decide
  rcases family_descends (prefixWord ++ tailWord_214767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214779 : List Nat := [1, 1, 1, 1, 1, 3, 1, 3, 4, 2, 5]
def baseStart_214779 : Nat := 118140960795 + 214779 * 2 ^ 59
def prefixEnd_214779 : Nat := 4983230072969 + 3 ^ 40 * 214779 * 2
def baseEnd_214779 : Nat := 110284861492120409874755

theorem tailTrace_214779 : CollatzResearch.WordTrace tailWord_214779 prefixEnd_214779 110284861492120409874755 := by
  unfold tailWord_214779
  simp only [CollatzResearch.WordTrace]
  refine ⟨7833633688899839177959391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5222422459266559451972927 7833633688899839177959391)
  ·
    refine ⟨11750450533349758766939087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7833633688899839177959391 11750450533349758766939087)
    ·
      refine ⟨17625675800024638150408631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11750450533349758766939087 17625675800024638150408631)
      ·
        refine ⟨26438513700036957225612947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17625675800024638150408631 26438513700036957225612947)
        ·
          refine ⟨39657770550055435838419421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26438513700036957225612947 39657770550055435838419421)
          ·
            refine ⟨14871663956270788439407283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39657770550055435838419421 14871663956270788439407283)
            ·
              refine ⟨22307495934406182659110925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14871663956270788439407283 22307495934406182659110925)
              ·
                refine ⟨8365310975402318497166597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22307495934406182659110925 8365310975402318497166597)
                ·
                  refine ⟨1568495807887934718218737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8365310975402318497166597 1568495807887934718218737)
                  ·
                    refine ⟨1176371855915951038664053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1568495807887934718218737 1176371855915951038664053)
                    ·
                      refine ⟨110284861492120409874755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1176371855915951038664053 110284861492120409874755)
                      ·
                        rfl

theorem cell23_214779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 4, 2, 5].length) (baseStart_214779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_214779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_214779 prefixEnd_214779 := by exact prefixLift 214779
  have htrace : WordTrace (prefixWord ++ tailWord_214779) baseStart_214779 baseEnd_214779 := by
    simpa [prefixWord, tailWord_214779, baseEnd_214779] using wordTrace_append hprefix tailTrace_214779
  have hstable : (prefixWord ++ tailWord_214779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214779).length < 2 ^ (prefixWord ++ tailWord_214779).sum := by decide
  have hdescent : baseEnd_214779 < baseStart_214779 := by decide
  rcases family_descends (prefixWord ++ tailWord_214779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214799 : List Nat := [1, 1, 2, 1, 1, 1, 4, 3, 1, 8]
def baseStart_214799 : Nat := 118140960795 + 214799 * 2 ^ 59
def prefixEnd_214799 : Nat := 4983230072969 + 3 ^ 40 * 214799 * 2
def baseEnd_214799 : Nat := 36765043701736777208221

theorem tailTrace_214799 : CollatzResearch.WordTrace tailWord_214799 prefixEnd_214799 36765043701736777208221 := by
  unfold tailWord_214799
  simp only [CollatzResearch.WordTrace]
  refine ⟨7834363148827382593687451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5222908765884921729124967 7834363148827382593687451)
  ·
    refine ⟨11751544723241073890531177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7834363148827382593687451 11751544723241073890531177)
    ·
      refine ⟨8813658542430805417898383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11751544723241073890531177 8813658542430805417898383)
      ·
        refine ⟨13220487813646208126847575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8813658542430805417898383 13220487813646208126847575)
        ·
          refine ⟨19830731720469312190271363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13220487813646208126847575 19830731720469312190271363)
          ·
            refine ⟨29746097580703968285407045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19830731720469312190271363 29746097580703968285407045)
            ·
              refine ⟨5577393296381994053513821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29746097580703968285407045 5577393296381994053513821)
              ·
                refine ⟨2091522486143247770067683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5577393296381994053513821 2091522486143247770067683)
                ·
                  refine ⟨3137283729214871655101525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2091522486143247770067683 3137283729214871655101525)
                  ·
                    refine ⟨36765043701736777208221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 3137283729214871655101525 36765043701736777208221)
                    ·
                      rfl

theorem cell23_214799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 3, 1, 8].length) (baseStart_214799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_214799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_214799 prefixEnd_214799 := by exact prefixLift 214799
  have htrace : WordTrace (prefixWord ++ tailWord_214799) baseStart_214799 baseEnd_214799 := by
    simpa [prefixWord, tailWord_214799, baseEnd_214799] using wordTrace_append hprefix tailTrace_214799
  have hstable : (prefixWord ++ tailWord_214799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214799).length < 2 ^ (prefixWord ++ tailWord_214799).sum := by decide
  have hdescent : baseEnd_214799 < baseStart_214799 := by decide
  rcases family_descends (prefixWord ++ tailWord_214799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214810 : List Nat := [3, 1, 1, 3, 2, 2, 1, 4, 1, 3, 2]
def baseStart_214810 : Nat := 118140960795 + 214810 * 2 ^ 59
def prefixEnd_214810 : Nat := 4983230072969 + 3 ^ 40 * 214810 * 2
def baseEnd_214810 : Nat := 110300779392409788587113

theorem tailTrace_214810 : CollatzResearch.WordTrace tailWord_214810 prefixEnd_214810 110300779392409788587113 := by
  unfold tailWord_214810
  simp only [CollatzResearch.WordTrace]
  refine ⟨1958691087946882868084471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5223176234525020981558589 1958691087946882868084471)
  ·
    refine ⟨2938036631920324302126707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1958691087946882868084471 2938036631920324302126707)
    ·
      refine ⟨4407054947880486453190061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2938036631920324302126707 4407054947880486453190061)
      ·
        refine ⟨1652645605455182419946273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4407054947880486453190061 1652645605455182419946273)
        ·
          refine ⟨1239484204091386814959705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1652645605455182419946273 1239484204091386814959705)
          ·
            refine ⟨929613153068540111219779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1239484204091386814959705 929613153068540111219779)
            ·
              refine ⟨1394419729602810166829669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 929613153068540111219779 1394419729602810166829669)
              ·
                refine ⟨261453699300526906280563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1394419729602810166829669 261453699300526906280563)
                ·
                  refine ⟨392180548950790359420845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 261453699300526906280563 392180548950790359420845)
                  ·
                    refine ⟨147067705856546384782817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 392180548950790359420845 147067705856546384782817)
                    ·
                      refine ⟨110300779392409788587113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 147067705856546384782817 110300779392409788587113)
                      ·
                        rfl

theorem cell23_214810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 4, 1, 3, 2].length) (baseStart_214810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_214810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_214810 prefixEnd_214810 := by exact prefixLift 214810
  have htrace : WordTrace (prefixWord ++ tailWord_214810) baseStart_214810 baseEnd_214810 := by
    simpa [prefixWord, tailWord_214810, baseEnd_214810] using wordTrace_append hprefix tailTrace_214810
  have hstable : (prefixWord ++ tailWord_214810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214810).length < 2 ^ (prefixWord ++ tailWord_214810).sum := by decide
  have hdescent : baseEnd_214810 < baseStart_214810 := by decide
  rcases family_descends (prefixWord ++ tailWord_214810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214840 : List Nat := [2, 1, 2, 1, 3, 3, 2, 1, 4, 2, 2]
def baseStart_214840 : Nat := 118140960795 + 214840 * 2 ^ 59
def prefixEnd_214840 : Nat := 4983230072969 + 3 ^ 40 * 214840 * 2
def baseEnd_214840 : Nat := 110316183812044671211975

theorem tailTrace_214840 : CollatzResearch.WordTrace tailWord_214840 prefixEnd_214840 110316183812044671211975 := by
  unfold tailWord_214840
  simp only [CollatzResearch.WordTrace]
  refine ⟨3917929270839423297964987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5223905694452564397286649 3917929270839423297964987)
  ·
    refine ⟨5876893906259134946947481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3917929270839423297964987 5876893906259134946947481)
    ·
      refine ⟨4407670429694351210210611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5876893906259134946947481 4407670429694351210210611)
      ·
        refine ⟨6611505644541526815315917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4407670429694351210210611 6611505644541526815315917)
        ·
          refine ⟨2479314616703072555743469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6611505644541526815315917 2479314616703072555743469)
          ·
            refine ⟨929742981263652208403801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2479314616703072555743469 929742981263652208403801)
            ·
              refine ⟨697307235947739156302851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 929742981263652208403801 697307235947739156302851)
              ·
                refine ⟨1045960853921608734454277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 697307235947739156302851 1045960853921608734454277)
                ·
                  refine ⟨196117660110301637710177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1045960853921608734454277 196117660110301637710177)
                  ·
                    refine ⟨147088245082726228282633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 196117660110301637710177 147088245082726228282633)
                    ·
                      refine ⟨110316183812044671211975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 147088245082726228282633 110316183812044671211975)
                      ·
                        rfl

theorem cell23_214840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 1, 4, 2, 2].length) (baseStart_214840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_214840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_214840 prefixEnd_214840 := by exact prefixLift 214840
  have htrace : WordTrace (prefixWord ++ tailWord_214840) baseStart_214840 baseEnd_214840 := by
    simpa [prefixWord, tailWord_214840, baseEnd_214840] using wordTrace_append hprefix tailTrace_214840
  have hstable : (prefixWord ++ tailWord_214840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214840).length < 2 ^ (prefixWord ++ tailWord_214840).sum := by decide
  have hdescent : baseEnd_214840 < baseStart_214840 := by decide
  rcases family_descends (prefixWord ++ tailWord_214840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214893 : List Nat := [1, 5, 1, 1, 1, 1, 4, 2, 2, 5]
def baseStart_214893 : Nat := 118140960795 + 214893 * 2 ^ 59
def prefixEnd_214893 : Nat := 4983230072969 + 3 ^ 40 * 214893 * 2
def baseEnd_214893 : Nat := 36781132762244321283077

theorem tailTrace_214893 : CollatzResearch.WordTrace tailWord_214893 prefixEnd_214893 36781132762244321283077 := by
  unfold tailWord_214893
  simp only [CollatzResearch.WordTrace]
  refine ⟨7837791610486836647609333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5225194406991224431739555 7837791610486836647609333)
  ·
    refine ⟨734792963483140935713375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7837791610486836647609333 734792963483140935713375)
    ·
      refine ⟨1102189445224711403570063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 734792963483140935713375 1102189445224711403570063)
      ·
        refine ⟨1653284167837067105355095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1102189445224711403570063 1653284167837067105355095)
        ·
          refine ⟨2479926251755600658032643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1653284167837067105355095 2479926251755600658032643)
          ·
            refine ⟨3719889377633400987048965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2479926251755600658032643 3719889377633400987048965)
            ·
              refine ⟨697479258306262685071681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3719889377633400987048965 697479258306262685071681)
              ·
                refine ⟨523109443729697013803761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 697479258306262685071681 523109443729697013803761)
                ·
                  refine ⟨392332082797272760352821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 523109443729697013803761 392332082797272760352821)
                  ·
                    refine ⟨36781132762244321283077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 392332082797272760352821 36781132762244321283077)
                    ·
                      rfl

theorem cell23_214893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 2, 2, 5].length) (baseStart_214893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_214893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_214893 prefixEnd_214893 := by exact prefixLift 214893
  have htrace : WordTrace (prefixWord ++ tailWord_214893) baseStart_214893 baseEnd_214893 := by
    simpa [prefixWord, tailWord_214893, baseEnd_214893] using wordTrace_append hprefix tailTrace_214893
  have hstable : (prefixWord ++ tailWord_214893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214893).length < 2 ^ (prefixWord ++ tailWord_214893).sum := by decide
  have hdescent : baseEnd_214893 < baseStart_214893 := by decide
  rcases family_descends (prefixWord ++ tailWord_214893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214896 : List Nat := [2, 1, 1, 1, 4, 1, 1, 2, 3, 3, 4]
def baseStart_214896 : Nat := 118140960795 + 214896 * 2 ^ 59
def prefixEnd_214896 : Nat := 4983230072969 + 3 ^ 40 * 214896 * 2
def baseEnd_214896 : Nat := 110344938728696452111717

theorem tailTrace_214896 : CollatzResearch.WordTrace tailWord_214896 prefixEnd_214896 110344938728696452111717 := by
  unfold tailWord_214896
  simp only [CollatzResearch.WordTrace]
  refine ⟨3918950514737984079984271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5225267352983978773312361 3918950514737984079984271)
  ·
    refine ⟨5878425772106976119976407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3918950514737984079984271 5878425772106976119976407)
    ·
      refine ⟨8817638658160464179964611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5878425772106976119976407 8817638658160464179964611)
      ·
        refine ⟨13226457987240696269946917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8817638658160464179964611 13226457987240696269946917)
        ·
          refine ⟨2479960872607630550615047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13226457987240696269946917 2479960872607630550615047)
          ·
            refine ⟨3719941308911445825922571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2479960872607630550615047 3719941308911445825922571)
            ·
              refine ⟨5579911963367168738883857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3719941308911445825922571 5579911963367168738883857)
              ·
                refine ⟨4184933972525376554162893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5579911963367168738883857 4184933972525376554162893)
                ·
                  refine ⟨1569350239697016207811085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4184933972525376554162893 1569350239697016207811085)
                  ·
                    refine ⟨588506339886381077929157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1569350239697016207811085 588506339886381077929157)
                    ·
                      refine ⟨110344938728696452111717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 588506339886381077929157 110344938728696452111717)
                      ·
                        rfl

theorem cell23_214896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3, 4].length) (baseStart_214896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_214896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_214896 prefixEnd_214896 := by exact prefixLift 214896
  have htrace : WordTrace (prefixWord ++ tailWord_214896) baseStart_214896 baseEnd_214896 := by
    simpa [prefixWord, tailWord_214896, baseEnd_214896] using wordTrace_append hprefix tailTrace_214896
  have hstable : (prefixWord ++ tailWord_214896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214896).length < 2 ^ (prefixWord ++ tailWord_214896).sum := by decide
  have hdescent : baseEnd_214896 < baseStart_214896 := by decide
  rcases family_descends (prefixWord ++ tailWord_214896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214930 : List Nat := [3, 2, 3, 2, 1, 2, 1, 1, 1, 3, 4]
def baseStart_214930 : Nat := 118140960795 + 214930 * 2 ^ 59
def prefixEnd_214930 : Nat := 4983230072969 + 3 ^ 40 * 214930 * 2
def baseEnd_214930 : Nat := 110362397070949319086561

theorem tailTrace_214930 : CollatzResearch.WordTrace tailWord_214930 prefixEnd_214930 110362397070949319086561 := by
  unfold tailWord_214930
  simp only [CollatzResearch.WordTrace]
  refine ⟨1959785277838197991676561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5226094074235194644470829 1959785277838197991676561)
  ·
    refine ⟨1469838958378648493757421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1959785277838197991676561 1469838958378648493757421)
    ·
      refine ⟨551189609391993185159033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1469838958378648493757421 551189609391993185159033)
      ·
        refine ⟨413392207043994888869275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 551189609391993185159033 413392207043994888869275)
        ·
          refine ⟨620088310565992333303913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 413392207043994888869275 620088310565992333303913)
          ·
            refine ⟨465066232924494249977935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 620088310565992333303913 465066232924494249977935)
            ·
              refine ⟨697599349386741374966903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 465066232924494249977935 697599349386741374966903)
              ·
                refine ⟨1046399024080112062450355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 697599349386741374966903 1046399024080112062450355)
                ·
                  refine ⟨1569598536120168093675533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1046399024080112062450355 1569598536120168093675533)
                  ·
                    refine ⟨588599451045063035128325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1569598536120168093675533 588599451045063035128325)
                    ·
                      refine ⟨110362397070949319086561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 588599451045063035128325 110362397070949319086561)
                      ·
                        rfl

theorem cell23_214930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_214930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_214930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_214930 prefixEnd_214930 := by exact prefixLift 214930
  have htrace : WordTrace (prefixWord ++ tailWord_214930) baseStart_214930 baseEnd_214930 := by
    simpa [prefixWord, tailWord_214930, baseEnd_214930] using wordTrace_append hprefix tailTrace_214930
  have hstable : (prefixWord ++ tailWord_214930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214930).length < 2 ^ (prefixWord ++ tailWord_214930).sum := by decide
  have hdescent : baseEnd_214930 < baseStart_214930 := by decide
  rcases family_descends (prefixWord ++ tailWord_214930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214933 : List Nat := [1, 3, 2, 1, 1, 3, 3, 1, 1, 4, 3]
def baseStart_214933 : Nat := 118140960795 + 214933 * 2 ^ 59
def prefixEnd_214933 : Nat := 4983230072969 + 3 ^ 40 * 214933 * 2
def baseEnd_214933 : Nat := 110363937512912807349047

theorem tailTrace_214933 : CollatzResearch.WordTrace tailWord_214933 prefixEnd_214933 110363937512912807349047 := by
  unfold tailWord_214933
  simp only [CollatzResearch.WordTrace]
  refine ⟨7839250530341923479065453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5226167020227948986043635 7839250530341923479065453)
  ·
    refine ⟨2939718948878221304649545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7839250530341923479065453 2939718948878221304649545)
    ·
      refine ⟨2204789211658665978487159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2939718948878221304649545 2204789211658665978487159)
      ·
        refine ⟨3307183817487998967730739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2204789211658665978487159 3307183817487998967730739)
        ·
          refine ⟨4960775726231998451596109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3307183817487998967730739 4960775726231998451596109)
          ·
            refine ⟨1860290897336999419348541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4960775726231998451596109 1860290897336999419348541)
            ·
              refine ⟨697609086501374782255703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1860290897336999419348541 697609086501374782255703)
              ·
                refine ⟨1046413629752062173383555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 697609086501374782255703 1046413629752062173383555)
                ·
                  refine ⟨1569620444628093260075333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1046413629752062173383555 1569620444628093260075333)
                  ·
                    refine ⟨294303833367767486264125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1569620444628093260075333 294303833367767486264125)
                    ·
                      refine ⟨110363937512912807349047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 294303833367767486264125 110363937512912807349047)
                      ·
                        rfl

theorem cell23_214933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 1, 1, 4, 3].length) (baseStart_214933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_214933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_214933 prefixEnd_214933 := by exact prefixLift 214933
  have htrace : WordTrace (prefixWord ++ tailWord_214933) baseStart_214933 baseEnd_214933 := by
    simpa [prefixWord, tailWord_214933, baseEnd_214933] using wordTrace_append hprefix tailTrace_214933
  have hstable : (prefixWord ++ tailWord_214933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214933).length < 2 ^ (prefixWord ++ tailWord_214933).sum := by decide
  have hdescent : baseEnd_214933 < baseStart_214933 := by decide
  rcases family_descends (prefixWord ++ tailWord_214933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214990 : List Nat := [4, 1, 1, 1, 2, 2, 1, 3, 1, 5, 2]
def baseStart_214990 : Nat := 118140960795 + 214990 * 2 ^ 59
def prefixEnd_214990 : Nat := 4983230072969 + 3 ^ 40 * 214990 * 2
def baseEnd_214990 : Nat := 110393205910219084336285

theorem tailTrace_214990 : CollatzResearch.WordTrace tailWord_214990 prefixEnd_214990 110393205910219084336285 := by
  unfold tailWord_214990
  simp only [CollatzResearch.WordTrace]
  refine ⟨980166186391927776736303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5227552994090281475926949 980166186391927776736303)
  ·
    refine ⟨1470249279587891665104455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 980166186391927776736303 1470249279587891665104455)
    ·
      refine ⟨2205373919381837497656683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1470249279587891665104455 2205373919381837497656683)
      ·
        refine ⟨3308060879072756246485025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2205373919381837497656683 3308060879072756246485025)
        ·
          refine ⟨2481045659304567184863769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3308060879072756246485025 2481045659304567184863769)
          ·
            refine ⟨1860784244478425388647827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2481045659304567184863769 1860784244478425388647827)
            ·
              refine ⟨2791176366717638082971741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1860784244478425388647827 2791176366717638082971741)
              ·
                refine ⟨1046691137519114281114403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2791176366717638082971741 1046691137519114281114403)
                ·
                  refine ⟨1570036706278671421671605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1046691137519114281114403 1570036706278671421671605)
                  ·
                    refine ⟨147190941213625445781713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1570036706278671421671605 147190941213625445781713)
                    ·
                      refine ⟨110393205910219084336285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 147190941213625445781713 110393205910219084336285)
                      ·
                        rfl

theorem cell23_214990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 3, 1, 5, 2].length) (baseStart_214990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_214990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_214990 prefixEnd_214990 := by exact prefixLift 214990
  have htrace : WordTrace (prefixWord ++ tailWord_214990) baseStart_214990 baseEnd_214990 := by
    simpa [prefixWord, tailWord_214990, baseEnd_214990] using wordTrace_append hprefix tailTrace_214990
  have hstable : (prefixWord ++ tailWord_214990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214990).length < 2 ^ (prefixWord ++ tailWord_214990).sum := by decide
  have hdescent : baseEnd_214990 < baseStart_214990 := by decide
  rcases family_descends (prefixWord ++ tailWord_214990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215007 : List Nat := [1, 1, 2, 3, 4, 2, 1, 2, 2, 3, 2]
def baseStart_215007 : Nat := 118140960795 + 215007 * 2 ^ 59
def prefixEnd_215007 : Nat := 4983230072969 + 3 ^ 40 * 215007 * 2
def baseEnd_215007 : Nat := 110401935081345517823707

theorem tailTrace_215007 : CollatzResearch.WordTrace tailWord_215007 prefixEnd_215007 110401935081345517823707 := by
  unfold tailWord_215007
  simp only [CollatzResearch.WordTrace]
  refine ⟨7841949532073834117259275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5227966354715889411506183 7841949532073834117259275)
  ·
    refine ⟨11762924298110751175888913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7841949532073834117259275 11762924298110751175888913)
    ·
      refine ⟨8822193223583063381916685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11762924298110751175888913 8822193223583063381916685)
      ·
        refine ⟨3308322458843648768218757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8822193223583063381916685 3308322458843648768218757)
        ·
          refine ⟨620310461033184144041017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3308322458843648768218757 620310461033184144041017)
          ·
            refine ⟨465232845774888108030763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 620310461033184144041017 465232845774888108030763)
            ·
              refine ⟨697849268662332162046145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 465232845774888108030763 697849268662332162046145)
              ·
                refine ⟨523386951496749121534609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 697849268662332162046145 523386951496749121534609)
                ·
                  refine ⟨392540213622561841150957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 523386951496749121534609 392540213622561841150957)
                  ·
                    refine ⟨147202580108460690431609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 392540213622561841150957 147202580108460690431609)
                    ·
                      refine ⟨110401935081345517823707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 147202580108460690431609 110401935081345517823707)
                      ·
                        rfl

theorem cell23_215007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 2, 2, 3, 2].length) (baseStart_215007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_215007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_215007 prefixEnd_215007 := by exact prefixLift 215007
  have htrace : WordTrace (prefixWord ++ tailWord_215007) baseStart_215007 baseEnd_215007 := by
    simpa [prefixWord, tailWord_215007, baseEnd_215007] using wordTrace_append hprefix tailTrace_215007
  have hstable : (prefixWord ++ tailWord_215007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215007).length < 2 ^ (prefixWord ++ tailWord_215007).sum := by decide
  have hdescent : baseEnd_215007 < baseStart_215007 := by decide
  rcases family_descends (prefixWord ++ tailWord_215007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215021 : List Nat := [1, 5, 1, 4, 2, 1, 2, 1, 6]
def baseStart_215021 : Nat := 118140960795 + 215021 * 2 ^ 59
def prefixEnd_215021 : Nat := 4983230072969 + 3 ^ 40 * 215021 * 2
def baseEnd_215021 : Nat := 12267680423389829227627

theorem tailTrace_215021 : CollatzResearch.WordTrace tailWord_215021 prefixEnd_215021 12267680423389829227627 := by
  unfold tailWord_215021
  simp only [CollatzResearch.WordTrace]
  refine ⟨7842460154023114508268917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5228306769348743005512611 7842460154023114508268917)
  ·
    refine ⟨735230639439666985150211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7842460154023114508268917 735230639439666985150211)
    ·
      refine ⟨1102845959159500477725317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 735230639439666985150211 1102845959159500477725317)
      ·
        refine ⟨206783617342406339573497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1102845959159500477725317 206783617342406339573497)
        ·
          refine ⟨155087713006804754680123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206783617342406339573497 155087713006804754680123)
          ·
            refine ⟨232631569510207132020185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155087713006804754680123 232631569510207132020185)
            ·
              refine ⟨174473677132655349015139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 232631569510207132020185 174473677132655349015139)
              ·
                refine ⟨261710515698983023522709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 174473677132655349015139 261710515698983023522709)
                ·
                  refine ⟨12267680423389829227627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 261710515698983023522709 12267680423389829227627)
                  ·
                    rfl

theorem cell23_215021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 2, 1, 6].length) (baseStart_215021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_215021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_215021 prefixEnd_215021 := by exact prefixLift 215021
  have htrace : WordTrace (prefixWord ++ tailWord_215021) baseStart_215021 baseEnd_215021 := by
    simpa [prefixWord, tailWord_215021, baseEnd_215021] using wordTrace_append hprefix tailTrace_215021
  have hstable : (prefixWord ++ tailWord_215021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215021).length < 2 ^ (prefixWord ++ tailWord_215021).sum := by decide
  have hdescent : baseEnd_215021 < baseStart_215021 := by decide
  rcases family_descends (prefixWord ++ tailWord_215021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215023 : List Nat := [1, 1, 2, 1, 4, 2, 1, 4, 1, 1, 5]
def baseStart_215023 : Nat := 118140960795 + 215023 * 2 ^ 59
def prefixEnd_215023 : Nat := 4983230072969 + 3 ^ 40 * 215023 * 2
def baseEnd_215023 : Nat := 110410150771817455223633

theorem tailTrace_215023 : CollatzResearch.WordTrace tailWord_215023 prefixEnd_215023 110410150771817455223633 := by
  unfold tailWord_215023
  simp only [CollatzResearch.WordTrace]
  refine ⟨7842533100015868849841723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5228355400010579233227815 7842533100015868849841723)
  ·
    refine ⟨11763799650023803274762585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7842533100015868849841723 11763799650023803274762585)
    ·
      refine ⟨8822849737517852456071939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11763799650023803274762585 8822849737517852456071939)
      ·
        refine ⟨13234274606276778684107909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8822849737517852456071939 13234274606276778684107909)
        ·
          refine ⟨2481426488676896003270233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13234274606276778684107909 2481426488676896003270233)
          ·
            refine ⟨1861069866507672002452675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2481426488676896003270233 1861069866507672002452675)
            ·
              refine ⟨2791604799761508003679013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1861069866507672002452675 2791604799761508003679013)
              ·
                refine ⟨523425899955282750689815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2791604799761508003679013 523425899955282750689815)
                ·
                  refine ⟨785138849932924126034723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 523425899955282750689815 785138849932924126034723)
                  ·
                    refine ⟨1177708274899386189052085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 785138849932924126034723 1177708274899386189052085)
                    ·
                      refine ⟨110410150771817455223633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1177708274899386189052085 110410150771817455223633)
                      ·
                        rfl

theorem cell23_215023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 4, 1, 1, 5].length) (baseStart_215023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_215023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_215023 prefixEnd_215023 := by exact prefixLift 215023
  have htrace : WordTrace (prefixWord ++ tailWord_215023) baseStart_215023 baseEnd_215023 := by
    simpa [prefixWord, tailWord_215023, baseEnd_215023] using wordTrace_append hprefix tailTrace_215023
  have hstable : (prefixWord ++ tailWord_215023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215023).length < 2 ^ (prefixWord ++ tailWord_215023).sum := by decide
  have hdescent : baseEnd_215023 < baseStart_215023 := by decide
  rcases family_descends (prefixWord ++ tailWord_215023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215033 : List Nat := [1, 2, 1, 3, 1, 4, 2, 1, 1, 1, 6]
def baseStart_215033 : Nat := 118140960795 + 215033 * 2 ^ 59
def prefixEnd_215033 : Nat := 4983230072969 + 3 ^ 40 * 215033 * 2
def baseEnd_215033 : Nat := 110415285578362416098587

theorem tailTrace_215033 : CollatzResearch.WordTrace tailWord_215033 prefixEnd_215033 110415285578362416098587 := by
  unfold tailWord_215033
  simp only [CollatzResearch.WordTrace]
  refine ⟨7842897829979640557705753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5228598553319760371803835 7842897829979640557705753)
  ·
    refine ⟨5882173372484730418279315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7842897829979640557705753 5882173372484730418279315)
    ·
      refine ⟨8823260058727095627418973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5882173372484730418279315 8823260058727095627418973)
      ·
        refine ⟨3308722522022660860282115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8823260058727095627418973 3308722522022660860282115)
        ·
          refine ⟨4963083783033991290423173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3308722522022660860282115 4963083783033991290423173)
          ·
            refine ⟨930578209318873366954345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4963083783033991290423173 930578209318873366954345)
            ·
              refine ⟨697933656989155025215759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 930578209318873366954345 697933656989155025215759)
              ·
                refine ⟨1046900485483732537823639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 697933656989155025215759 1046900485483732537823639)
                ·
                  refine ⟨1570350728225598806735459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1046900485483732537823639 1570350728225598806735459)
                  ·
                    refine ⟨2355526092338398210103189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1570350728225598806735459 2355526092338398210103189)
                    ·
                      refine ⟨110415285578362416098587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2355526092338398210103189 110415285578362416098587)
                      ·
                        rfl

theorem cell23_215033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 1, 1, 1, 6].length) (baseStart_215033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_215033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_215033 prefixEnd_215033 := by exact prefixLift 215033
  have htrace : WordTrace (prefixWord ++ tailWord_215033) baseStart_215033 baseEnd_215033 := by
    simpa [prefixWord, tailWord_215033, baseEnd_215033] using wordTrace_append hprefix tailTrace_215033
  have hstable : (prefixWord ++ tailWord_215033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215033).length < 2 ^ (prefixWord ++ tailWord_215033).sum := by decide
  have hdescent : baseEnd_215033 < baseStart_215033 := by decide
  rcases family_descends (prefixWord ++ tailWord_215033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215037 : List Nat := [1, 4, 1, 1, 1, 2, 2, 4, 3, 2, 2]
def baseStart_215037 : Nat := 118140960795 + 215037 * 2 ^ 59
def prefixEnd_215037 : Nat := 4983230072969 + 3 ^ 40 * 215037 * 2
def baseEnd_215037 : Nat := 110417339500980400448569

theorem tailTrace_215037 : CollatzResearch.WordTrace tailWord_215037 prefixEnd_215037 110417339500980400448569 := by
  unfold tailWord_215037
  simp only [CollatzResearch.WordTrace]
  refine ⟨7843043721965149240851365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5228695814643432827234243 7843043721965149240851365)
  ·
    refine ⟨1470570697868465482659631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7843043721965149240851365 1470570697868465482659631)
    ·
      refine ⟨2205856046802698223989447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1470570697868465482659631 2205856046802698223989447)
      ·
        refine ⟨3308784070204047335984171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2205856046802698223989447 3308784070204047335984171)
        ·
          refine ⟨4963176105306071003976257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3308784070204047335984171 4963176105306071003976257)
          ·
            refine ⟨3722382078979553252982193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4963176105306071003976257 3722382078979553252982193)
            ·
              refine ⟨2791786559234664939736645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3722382078979553252982193 2791786559234664939736645)
              ·
                refine ⟨523459979856499676200621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2791786559234664939736645 523459979856499676200621)
                ·
                  refine ⟨196297492446187378575233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 523459979856499676200621 196297492446187378575233)
                  ·
                    refine ⟨147223119334640533931425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 196297492446187378575233 147223119334640533931425)
                    ·
                      refine ⟨110417339500980400448569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 147223119334640533931425 110417339500980400448569)
                      ·
                        rfl

theorem cell23_215037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 4, 3, 2, 2].length) (baseStart_215037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_215037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_215037 prefixEnd_215037 := by exact prefixLift 215037
  have htrace : WordTrace (prefixWord ++ tailWord_215037) baseStart_215037 baseEnd_215037 := by
    simpa [prefixWord, tailWord_215037, baseEnd_215037] using wordTrace_append hprefix tailTrace_215037
  have hstable : (prefixWord ++ tailWord_215037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215037).length < 2 ^ (prefixWord ++ tailWord_215037).sum := by decide
  have hdescent : baseEnd_215037 < baseStart_215037 := by decide
  rcases family_descends (prefixWord ++ tailWord_215037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215040 : List Nat := [2, 1, 1, 2, 1, 1, 1, 8, 1, 2, 3]
def baseStart_215040 : Nat := 118140960795 + 215040 * 2 ^ 59
def prefixEnd_215040 : Nat := 4983230072969 + 3 ^ 40 * 215040 * 2
def baseEnd_215040 : Nat := 110418879942943888711055

theorem tailTrace_215040 : CollatzResearch.WordTrace tailWord_215040 prefixEnd_215040 110418879942943888711055 := by
  unfold tailWord_215040
  simp only [CollatzResearch.WordTrace]
  refine ⟨3921576570477140376605287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5228768760636187168807049 3921576570477140376605287)
  ·
    refine ⟨5882364855715710564907931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3921576570477140376605287 5882364855715710564907931)
    ·
      refine ⟨8823547283573565847361897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5882364855715710564907931 8823547283573565847361897)
      ·
        refine ⟨6617660462680174385521423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8823547283573565847361897 6617660462680174385521423)
        ·
          refine ⟨9926490694020261578282135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6617660462680174385521423 9926490694020261578282135)
          ·
            refine ⟨14889736041030392367423203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9926490694020261578282135 14889736041030392367423203)
            ·
              refine ⟨22334604061545588551134805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14889736041030392367423203 22334604061545588551134805)
              ·
                refine ⟨261733641346237365833611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 22334604061545588551134805 261733641346237365833611)
                ·
                  refine ⟨392600462019356048750417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 261733641346237365833611 392600462019356048750417)
                  ·
                    refine ⟨294450346514517036562813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 392600462019356048750417 294450346514517036562813)
                    ·
                      refine ⟨110418879942943888711055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 294450346514517036562813 110418879942943888711055)
                      ·
                        rfl

theorem cell23_215040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 8, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 8, 1, 2, 3].length) (baseStart_215040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_215040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_215040 prefixEnd_215040 := by exact prefixLift 215040
  have htrace : WordTrace (prefixWord ++ tailWord_215040) baseStart_215040 baseEnd_215040 := by
    simpa [prefixWord, tailWord_215040, baseEnd_215040] using wordTrace_append hprefix tailTrace_215040
  have hstable : (prefixWord ++ tailWord_215040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215040).length < 2 ^ (prefixWord ++ tailWord_215040).sum := by decide
  have hdescent : baseEnd_215040 < baseStart_215040 := by decide
  rcases family_descends (prefixWord ++ tailWord_215040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215060 : List Nat := [2, 4, 3, 2, 12]
def baseStart_215060 : Nat := 118140960795 + 215060 * 2 ^ 59
def prefixEnd_215060 : Nat := 4983230072969 + 3 ^ 40 * 215060 * 2
def baseEnd_215060 : Nat := 151480314891678752347

theorem tailTrace_215060 : CollatzResearch.WordTrace tailWord_215060 prefixEnd_215060 151480314891678752347 := by
  unfold tailWord_215060
  simp only [CollatzResearch.WordTrace]
  refine ⟨3921941300440912084469317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5229255067254549445959089 3921941300440912084469317)
  ·
    refine ⟨735363993832671015837997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3921941300440912084469317 735363993832671015837997)
    ·
      refine ⟨275761497687251630939249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 735363993832671015837997 275761497687251630939249)
      ·
        refine ⟨206821123265438723204437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 275761497687251630939249 206821123265438723204437)
        ·
          refine ⟨151480314891678752347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 206821123265438723204437 151480314891678752347)
          ·
            rfl

theorem cell23_215060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 12].length) (baseStart_215060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_215060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_215060 prefixEnd_215060 := by exact prefixLift 215060
  have htrace : WordTrace (prefixWord ++ tailWord_215060) baseStart_215060 baseEnd_215060 := by
    simpa [prefixWord, tailWord_215060, baseEnd_215060] using wordTrace_append hprefix tailTrace_215060
  have hstable : (prefixWord ++ tailWord_215060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215060).length < 2 ^ (prefixWord ++ tailWord_215060).sum := by decide
  have hdescent : baseEnd_215060 < baseStart_215060 := by decide
  rcases family_descends (prefixWord ++ tailWord_215060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215113 : List Nat := [1, 2, 1, 1, 2, 2, 4, 1, 1, 3, 5]
def baseStart_215113 : Nat := 118140960795 + 215113 * 2 ^ 59
def prefixEnd_215113 : Nat := 4983230072969 + 3 ^ 40 * 215113 * 2
def baseEnd_215113 : Nat := 110456364030722103098219

theorem tailTrace_215113 : CollatzResearch.WordTrace tailWord_215113 prefixEnd_215113 110456364030722103098219 := by
  unfold tailWord_215113
  simp only [CollatzResearch.WordTrace]
  refine ⟨7845815669689814220617993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5230543779793209480411995 7845815669689814220617993)
  ·
    refine ⟨5884361752267360665463495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7845815669689814220617993 5884361752267360665463495)
    ·
      refine ⟨8826542628401040998195243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5884361752267360665463495 8826542628401040998195243)
      ·
        refine ⟨13239813942601561497292865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8826542628401040998195243 13239813942601561497292865)
        ·
          refine ⟨9929860456951171122969649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13239813942601561497292865 9929860456951171122969649)
          ·
            refine ⟨7447395342713378342227237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9929860456951171122969649 7447395342713378342227237)
            ·
              refine ⟨1396386626758758439167607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7447395342713378342227237 1396386626758758439167607)
              ·
                refine ⟨2094579940138137658751411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1396386626758758439167607 2094579940138137658751411)
                ·
                  refine ⟨3141869910207206488127117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2094579940138137658751411 3141869910207206488127117)
                  ·
                    refine ⟨1178201216327702433047669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3141869910207206488127117 1178201216327702433047669)
                    ·
                      refine ⟨110456364030722103098219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1178201216327702433047669 110456364030722103098219)
                      ·
                        rfl

theorem cell23_215113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 1, 1, 3, 5].length) (baseStart_215113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_215113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_215113 prefixEnd_215113 := by exact prefixLift 215113
  have htrace : WordTrace (prefixWord ++ tailWord_215113) baseStart_215113 baseEnd_215113 := by
    simpa [prefixWord, tailWord_215113, baseEnd_215113] using wordTrace_append hprefix tailTrace_215113
  have hstable : (prefixWord ++ tailWord_215113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215113).length < 2 ^ (prefixWord ++ tailWord_215113).sum := by decide
  have hdescent : baseEnd_215113 < baseStart_215113 := by decide
  rcases family_descends (prefixWord ++ tailWord_215113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215138 : List Nat := [3, 3, 2, 2, 2, 1, 3, 1, 2, 1, 3]
def baseStart_215138 : Nat := 118140960795 + 215138 * 2 ^ 59
def prefixEnd_215138 : Nat := 4983230072969 + 3 ^ 40 * 215138 * 2
def baseEnd_215138 : Nat := 110469201047084505285605

theorem tailTrace_215138 : CollatzResearch.WordTrace tailWord_215138 prefixEnd_215138 110469201047084505285605 := by
  unfold tailWord_215138
  simp only [CollatzResearch.WordTrace]
  refine ⟨1961681873649810872569517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5231151663066162326852045 1961681873649810872569517)
  ·
    refine ⟨735630702618679077213569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1961681873649810872569517 735630702618679077213569)
    ·
      refine ⟨551723026964009307910177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 735630702618679077213569 551723026964009307910177)
      ·
        refine ⟨413792270223006980932633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 551723026964009307910177 413792270223006980932633)
        ·
          refine ⟨310344202667255235699475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 413792270223006980932633 310344202667255235699475)
          ·
            refine ⟨465516304000882853549213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 310344202667255235699475 465516304000882853549213)
            ·
              refine ⟨174568614000331070080955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 465516304000882853549213 174568614000331070080955)
              ·
                refine ⟨261852921000496605121433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 174568614000331070080955 261852921000496605121433)
                ·
                  refine ⟨196389690750372453841075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 261852921000496605121433 196389690750372453841075)
                  ·
                    refine ⟨294584536125558680761613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 196389690750372453841075 294584536125558680761613)
                    ·
                      refine ⟨110469201047084505285605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 294584536125558680761613 110469201047084505285605)
                      ·
                        rfl

theorem cell23_215138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 3, 1, 2, 1, 3].length) (baseStart_215138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_215138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_215138 prefixEnd_215138 := by exact prefixLift 215138
  have htrace : WordTrace (prefixWord ++ tailWord_215138) baseStart_215138 baseEnd_215138 := by
    simpa [prefixWord, tailWord_215138, baseEnd_215138] using wordTrace_append hprefix tailTrace_215138
  have hstable : (prefixWord ++ tailWord_215138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215138).length < 2 ^ (prefixWord ++ tailWord_215138).sum := by decide
  have hdescent : baseEnd_215138 < baseStart_215138 := by decide
  rcases family_descends (prefixWord ++ tailWord_215138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215140 : List Nat := [2, 3, 1, 1, 2, 1, 4, 1, 2, 2, 4]
def baseStart_215140 : Nat := 118140960795 + 215140 * 2 ^ 59
def prefixEnd_215140 : Nat := 4983230072969 + 3 ^ 40 * 215140 * 2
def baseEnd_215140 : Nat := 110470228008393497460595

theorem tailTrace_215140 : CollatzResearch.WordTrace tailWord_215140 prefixEnd_215140 110470228008393497460595 := by
  unfold tailWord_215140
  simp only [CollatzResearch.WordTrace]
  refine ⟨3923400220295998915925437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5231200293727998554567249 3923400220295998915925437)
  ·
    refine ⟨1471275082610999593472039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3923400220295998915925437 1471275082610999593472039)
    ·
      refine ⟨2206912623916499390208059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1471275082610999593472039 2206912623916499390208059)
      ·
        refine ⟨3310368935874749085312089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2206912623916499390208059 3310368935874749085312089)
        ·
          refine ⟨2482776701906061813984067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3310368935874749085312089 2482776701906061813984067)
          ·
            refine ⟨3724165052859092720976101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2482776701906061813984067 3724165052859092720976101)
            ·
              refine ⟨698280947411079885183019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3724165052859092720976101 698280947411079885183019)
              ·
                refine ⟨1047421421116619827774529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 698280947411079885183019 1047421421116619827774529)
                ·
                  refine ⟨785566065837464870830897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1047421421116619827774529 785566065837464870830897)
                  ·
                    refine ⟨589174549378098653123173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 785566065837464870830897 589174549378098653123173)
                    ·
                      refine ⟨110470228008393497460595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 589174549378098653123173 110470228008393497460595)
                      ·
                        rfl

theorem cell23_215140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 1, 2, 2, 4].length) (baseStart_215140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_215140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_215140 prefixEnd_215140 := by exact prefixLift 215140
  have htrace : WordTrace (prefixWord ++ tailWord_215140) baseStart_215140 baseEnd_215140 := by
    simpa [prefixWord, tailWord_215140, baseEnd_215140] using wordTrace_append hprefix tailTrace_215140
  have hstable : (prefixWord ++ tailWord_215140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215140).length < 2 ^ (prefixWord ++ tailWord_215140).sum := by decide
  have hdescent : baseEnd_215140 < baseStart_215140 := by decide
  rcases family_descends (prefixWord ++ tailWord_215140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215150 : List Nat := [4, 1, 2, 2, 1, 1, 1, 4, 7]
def baseStart_215150 : Nat := 118140960795 + 215150 * 2 ^ 59
def prefixEnd_215150 : Nat := 4983230072969 + 3 ^ 40 * 215150 * 2
def baseEnd_215150 : Nat := 12275040312770939815061

theorem tailTrace_215150 : CollatzResearch.WordTrace tailWord_215150 prefixEnd_215150 12275040312770939815061 := by
  unfold tailWord_215150
  simp only [CollatzResearch.WordTrace]
  refine ⟨980895646319471192464363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5231443447037179693143269 980895646319471192464363)
  ·
    refine ⟨1471343469479206788696545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 980895646319471192464363 1471343469479206788696545)
    ·
      refine ⟨1103507602109405091522409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1471343469479206788696545 1103507602109405091522409)
      ·
        refine ⟨827630701582053818641807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1103507602109405091522409 827630701582053818641807)
        ·
          refine ⟨1241446052373080727962711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 827630701582053818641807 1241446052373080727962711)
          ·
            refine ⟨1862169078559621091944067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1241446052373080727962711 1862169078559621091944067)
            ·
              refine ⟨2793253617839431637916101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1862169078559621091944067 2793253617839431637916101)
              ·
                refine ⟨523735053344893432109269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2793253617839431637916101 523735053344893432109269)
                ·
                  refine ⟨12275040312770939815061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 523735053344893432109269 12275040312770939815061)
                  ·
                    rfl

theorem cell23_215150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 4, 7].length) (baseStart_215150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_215150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_215150 prefixEnd_215150 := by exact prefixLift 215150
  have htrace : WordTrace (prefixWord ++ tailWord_215150) baseStart_215150 baseEnd_215150 := by
    simpa [prefixWord, tailWord_215150, baseEnd_215150] using wordTrace_append hprefix tailTrace_215150
  have hstable : (prefixWord ++ tailWord_215150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215150).length < 2 ^ (prefixWord ++ tailWord_215150).sum := by decide
  have hdescent : baseEnd_215150 < baseStart_215150 := by decide
  rcases family_descends (prefixWord ++ tailWord_215150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215237 : List Nat := [1, 3, 1, 1, 1, 1, 6, 2, 2, 2, 3]
def baseStart_215237 : Nat := 118140960795 + 215237 * 2 ^ 59
def prefixEnd_215237 : Nat := 4983230072969 + 3 ^ 40 * 215237 * 2
def baseEnd_215237 : Nat := 110520035631879617947649

theorem tailTrace_215237 : CollatzResearch.WordTrace tailWord_215237 prefixEnd_215237 110520035631879617947649 := by
  unfold tailWord_215237
  simp only [CollatzResearch.WordTrace]
  refine ⟨7850338321240583398131965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5233558880827055598754643 7850338321240583398131965)
  ·
    refine ⟨2943876870465218774299487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7850338321240583398131965 2943876870465218774299487)
    ·
      refine ⟨4415815305697828161449231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2943876870465218774299487 4415815305697828161449231)
      ·
        refine ⟨6623722958546742242173847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4415815305697828161449231 6623722958546742242173847)
        ·
          refine ⟨9935584437820113363260771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6623722958546742242173847 9935584437820113363260771)
          ·
            refine ⟨14903376656730170044891157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9935584437820113363260771 14903376656730170044891157)
            ·
              refine ⟨698595780784226720854273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 14903376656730170044891157 698595780784226720854273)
              ·
                refine ⟨523946835588170040640705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 698595780784226720854273 523946835588170040640705)
                ·
                  refine ⟨392960126691127530480529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 523946835588170040640705 392960126691127530480529)
                  ·
                    refine ⟨294720095018345647860397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 392960126691127530480529 294720095018345647860397)
                    ·
                      refine ⟨110520035631879617947649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 294720095018345647860397 110520035631879617947649)
                      ·
                        rfl

theorem cell23_215237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 2, 2, 2, 3].length) (baseStart_215237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_215237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_215237 prefixEnd_215237 := by exact prefixLift 215237
  have htrace : WordTrace (prefixWord ++ tailWord_215237) baseStart_215237 baseEnd_215237 := by
    simpa [prefixWord, tailWord_215237, baseEnd_215237] using wordTrace_append hprefix tailTrace_215237
  have hstable : (prefixWord ++ tailWord_215237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215237).length < 2 ^ (prefixWord ++ tailWord_215237).sum := by decide
  have hdescent : baseEnd_215237 < baseStart_215237 := by decide
  rcases family_descends (prefixWord ++ tailWord_215237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215271 : List Nat := [1, 1, 5, 3, 1, 3, 1, 1, 2, 2, 3]
def baseStart_215271 : Nat := 118140960795 + 215271 * 2 ^ 59
def prefixEnd_215271 : Nat := 4983230072969 + 3 ^ 40 * 215271 * 2
def baseEnd_215271 : Nat := 110537493974132484922493

theorem tailTrace_215271 : CollatzResearch.WordTrace tailWord_215271 prefixEnd_215271 110537493974132484922493 := by
  unfold tailWord_215271
  simp only [CollatzResearch.WordTrace]
  refine ⟨7851578403117407204869667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5234385602078271469913111 7851578403117407204869667)
  ·
    refine ⟨11777367604676110807304501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7851578403117407204869667 11777367604676110807304501)
    ·
      refine ⟨1104128212938385388184797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11777367604676110807304501 1104128212938385388184797)
      ·
        refine ⟨414048079851894520569299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1104128212938385388184797 414048079851894520569299)
        ·
          refine ⟨621072119777841780853949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 414048079851894520569299 621072119777841780853949)
          ·
            refine ⟨232902044916690667820231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 621072119777841780853949 232902044916690667820231)
            ·
              refine ⟨349353067375036001730347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 232902044916690667820231 349353067375036001730347)
              ·
                refine ⟨524029601062554002595521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 349353067375036001730347 524029601062554002595521)
                ·
                  refine ⟨393022200796915501946641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 524029601062554002595521 393022200796915501946641)
                  ·
                    refine ⟨294766650597686626459981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 393022200796915501946641 294766650597686626459981)
                    ·
                      refine ⟨110537493974132484922493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 294766650597686626459981 110537493974132484922493)
                      ·
                        rfl

theorem cell23_215271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_215271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_215271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_215271 prefixEnd_215271 := by exact prefixLift 215271
  have htrace : WordTrace (prefixWord ++ tailWord_215271) baseStart_215271 baseEnd_215271 := by
    simpa [prefixWord, tailWord_215271, baseEnd_215271] using wordTrace_append hprefix tailTrace_215271
  have hstable : (prefixWord ++ tailWord_215271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215271).length < 2 ^ (prefixWord ++ tailWord_215271).sum := by decide
  have hdescent : baseEnd_215271 < baseStart_215271 := by decide
  rcases family_descends (prefixWord ++ tailWord_215271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215317 : List Nat := [1, 3, 2, 1, 2, 1, 5, 1, 1, 6]
def baseStart_215317 : Nat := 118140960795 + 215317 * 2 ^ 59
def prefixEnd_215317 : Nat := 4983230072969 + 3 ^ 40 * 215317 * 2
def baseEnd_215317 : Nat := 36853704694746434982427

theorem tailTrace_215317 : CollatzResearch.WordTrace tailWord_215317 prefixEnd_215317 36853704694746434982427 := by
  unfold tailWord_215317
  simp only [CollatzResearch.WordTrace]
  refine ⟨7853256160950757061044205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5235504107300504707362803 7853256160950757061044205)
  ·
    refine ⟨2944971060356533897891577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7853256160950757061044205 2944971060356533897891577)
    ·
      refine ⟨2208728295267400423418683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2944971060356533897891577 2208728295267400423418683)
      ·
        refine ⟨3313092442901100635128025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2208728295267400423418683 3313092442901100635128025)
        ·
          refine ⟨2484819332175825476346019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3313092442901100635128025 2484819332175825476346019)
          ·
            refine ⟨3727228998263738214519029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2484819332175825476346019 3727228998263738214519029)
            ·
              refine ⟨349427718587225457611159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3727228998263738214519029 349427718587225457611159)
              ·
                refine ⟨524141577880838186416739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 349427718587225457611159 524141577880838186416739)
                ·
                  refine ⟨786212366821257279625109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 524141577880838186416739 786212366821257279625109)
                  ·
                    refine ⟨36853704694746434982427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 786212366821257279625109 36853704694746434982427)
                    ·
                      rfl

theorem cell23_215317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5, 1, 1, 6].length) (baseStart_215317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_215317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_215317 prefixEnd_215317 := by exact prefixLift 215317
  have htrace : WordTrace (prefixWord ++ tailWord_215317) baseStart_215317 baseEnd_215317 := by
    simpa [prefixWord, tailWord_215317, baseEnd_215317] using wordTrace_append hprefix tailTrace_215317
  have hstable : (prefixWord ++ tailWord_215317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215317).length < 2 ^ (prefixWord ++ tailWord_215317).sum := by decide
  have hdescent : baseEnd_215317 < baseStart_215317 := by decide
  rcases family_descends (prefixWord ++ tailWord_215317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215358 : List Nat := [4, 2, 1, 2, 1, 2, 3, 1, 3, 2, 2]
def baseStart_215358 : Nat := 118140960795 + 215358 * 2 ^ 59
def prefixEnd_215358 : Nat := 4983230072969 + 3 ^ 40 * 215358 * 2
def baseEnd_215358 : Nat := 110582166791073644534593

theorem tailTrace_215358 : CollatzResearch.WordTrace tailWord_215358 prefixEnd_215358 110582166791073644534593 := by
  unfold tailWord_215358
  simp only [CollatzResearch.WordTrace]
  refine ⟨981843944225277632910841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5236501035868147375524485 981843944225277632910841)
  ·
    refine ⟨736382958168958224683131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 981843944225277632910841 736382958168958224683131)
    ·
      refine ⟨1104574437253437337024697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 736382958168958224683131 1104574437253437337024697)
      ·
        refine ⟨828430827940078002768523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1104574437253437337024697 828430827940078002768523)
        ·
          refine ⟨1242646241910117004152785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 828430827940078002768523 1242646241910117004152785)
          ·
            refine ⟨931984681432587753114589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1242646241910117004152785 931984681432587753114589)
            ·
              refine ⟨349494255537220407417971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 931984681432587753114589 349494255537220407417971)
              ·
                refine ⟨524241383305830611126957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 349494255537220407417971 524241383305830611126957)
                ·
                  refine ⟨196590518739686479172609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 524241383305830611126957 196590518739686479172609)
                  ·
                    refine ⟨147442889054764859379457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 196590518739686479172609 147442889054764859379457)
                    ·
                      refine ⟨110582166791073644534593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 147442889054764859379457 110582166791073644534593)
                      ·
                        rfl

theorem cell23_215358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3, 1, 3, 2, 2].length) (baseStart_215358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_215358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_215358 prefixEnd_215358 := by exact prefixLift 215358
  have htrace : WordTrace (prefixWord ++ tailWord_215358) baseStart_215358 baseEnd_215358 := by
    simpa [prefixWord, tailWord_215358, baseEnd_215358] using wordTrace_append hprefix tailTrace_215358
  have hstable : (prefixWord ++ tailWord_215358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215358).length < 2 ^ (prefixWord ++ tailWord_215358).sum := by decide
  have hdescent : baseEnd_215358 < baseStart_215358 := by decide
  rcases family_descends (prefixWord ++ tailWord_215358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215374 : List Nat := [4, 1, 1, 1, 1, 1, 2, 2, 6, 1, 3]
def baseStart_215374 : Nat := 118140960795 + 215374 * 2 ^ 59
def prefixEnd_215374 : Nat := 4983230072969 + 3 ^ 40 * 215374 * 2
def baseEnd_215374 : Nat := 110590382481545581934519

theorem tailTrace_215374 : CollatzResearch.WordTrace tailWord_215374 prefixEnd_215374 110590382481545581934519 := by
  unfold tailWord_215374
  simp only [CollatzResearch.WordTrace]
  refine ⟨981916890218031974483647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5236890081162837197246117 981916890218031974483647)
  ·
    refine ⟨1472875335327047961725471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 981916890218031974483647 1472875335327047961725471)
    ·
      refine ⟨2209313002990571942588207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1472875335327047961725471 2209313002990571942588207)
      ·
        refine ⟨3313969504485857913882311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2209313002990571942588207 3313969504485857913882311)
        ·
          refine ⟨4970954256728786870823467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3313969504485857913882311 4970954256728786870823467)
          ·
            refine ⟨7456431385093180306235201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4970954256728786870823467 7456431385093180306235201)
            ·
              refine ⟨5592323538819885229676401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7456431385093180306235201 5592323538819885229676401)
              ·
                refine ⟨4194242654114913922257301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5592323538819885229676401 4194242654114913922257301)
                ·
                  refine ⟨196605124411636590105811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4194242654114913922257301 196605124411636590105811)
                  ·
                    refine ⟨294907686617454885158717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 196605124411636590105811 294907686617454885158717)
                    ·
                      refine ⟨110590382481545581934519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 294907686617454885158717 110590382481545581934519)
                      ·
                        rfl

theorem cell23_215374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 6, 1, 3].length) (baseStart_215374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_215374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_215374 prefixEnd_215374 := by exact prefixLift 215374
  have htrace : WordTrace (prefixWord ++ tailWord_215374) baseStart_215374 baseEnd_215374 := by
    simpa [prefixWord, tailWord_215374, baseEnd_215374] using wordTrace_append hprefix tailTrace_215374
  have hstable : (prefixWord ++ tailWord_215374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215374).length < 2 ^ (prefixWord ++ tailWord_215374).sum := by decide
  have hdescent : baseEnd_215374 < baseStart_215374 := by decide
  rcases family_descends (prefixWord ++ tailWord_215374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215431 : List Nat := [1, 1, 4, 2, 2, 1, 4, 1, 1, 4, 2]
def baseStart_215431 : Nat := 118140960795 + 215431 * 2 ^ 59
def prefixEnd_215431 : Nat := 4983230072969 + 3 ^ 40 * 215431 * 2
def baseEnd_215431 : Nat := 110619650878851858921757

theorem tailTrace_215431 : CollatzResearch.WordTrace tailWord_215431 prefixEnd_215431 110619650878851858921757 := by
  unfold tailWord_215431
  simp only [CollatzResearch.WordTrace]
  refine ⟨7857414082537754530694147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5238276055025169687129431 7857414082537754530694147)
  ·
    refine ⟨11786121123806631796041221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7857414082537754530694147 11786121123806631796041221)
    ·
      refine ⟨2209897710713743461757729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11786121123806631796041221 2209897710713743461757729)
      ·
        refine ⟨1657423283035307596318297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2209897710713743461757729 1657423283035307596318297)
        ·
          refine ⟨1243067462276480697238723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1657423283035307596318297 1243067462276480697238723)
          ·
            refine ⟨1864601193414721045858085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1243067462276480697238723 1864601193414721045858085)
            ·
              refine ⟨349612723765260196098391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1864601193414721045858085 349612723765260196098391)
              ·
                refine ⟨524419085647890294147587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 349612723765260196098391 524419085647890294147587)
                ·
                  refine ⟨786628628471835441221381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 524419085647890294147587 786628628471835441221381)
                  ·
                    refine ⟨147492867838469145229009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 786628628471835441221381 147492867838469145229009)
                    ·
                      refine ⟨110619650878851858921757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 147492867838469145229009 110619650878851858921757)
                      ·
                        rfl

theorem cell23_215431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4, 1, 1, 4, 2].length) (baseStart_215431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_215431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_215431 prefixEnd_215431 := by exact prefixLift 215431
  have htrace : WordTrace (prefixWord ++ tailWord_215431) baseStart_215431 baseEnd_215431 := by
    simpa [prefixWord, tailWord_215431, baseEnd_215431] using wordTrace_append hprefix tailTrace_215431
  have hstable : (prefixWord ++ tailWord_215431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215431).length < 2 ^ (prefixWord ++ tailWord_215431).sum := by decide
  have hdescent : baseEnd_215431 < baseStart_215431 := by decide
  rcases family_descends (prefixWord ++ tailWord_215431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215446 : List Nat := [5, 3, 1, 2, 2, 1, 2, 1, 1, 2, 3]
def baseStart_215446 : Nat := 118140960795 + 215446 * 2 ^ 59
def prefixEnd_215446 : Nat := 4983230072969 + 3 ^ 40 * 215446 * 2
def baseEnd_215446 : Nat := 110627353088669300234189

theorem tailTrace_215446 : CollatzResearch.WordTrace tailWord_215446 prefixEnd_215446 110627353088669300234189 := by
  unfold tailWord_215446
  simp only [CollatzResearch.WordTrace]
  refine ⟨491122573592713255780637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5238640784988941394993461 491122573592713255780637)
  ·
    refine ⟨184170965097267470917739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 491122573592713255780637 184170965097267470917739)
    ·
      refine ⟨276256447645901206376609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184170965097267470917739 276256447645901206376609)
      ·
        refine ⟨207192335734425904782457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 276256447645901206376609 207192335734425904782457)
        ·
          refine ⟨155394251800819428586843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207192335734425904782457 155394251800819428586843)
          ·
            refine ⟨233091377701229142880265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155394251800819428586843 233091377701229142880265)
            ·
              refine ⟨174818533275921857160199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 233091377701229142880265 174818533275921857160199)
              ·
                refine ⟨262227799913882785740299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 174818533275921857160199 262227799913882785740299)
                ·
                  refine ⟨393341699870824178610449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 262227799913882785740299 393341699870824178610449)
                  ·
                    refine ⟨295006274903118133957837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 393341699870824178610449 295006274903118133957837)
                    ·
                      refine ⟨110627353088669300234189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 295006274903118133957837 110627353088669300234189)
                      ·
                        rfl

theorem cell23_215446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_215446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_215446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_215446 prefixEnd_215446 := by exact prefixLift 215446
  have htrace : WordTrace (prefixWord ++ tailWord_215446) baseStart_215446 baseEnd_215446 := by
    simpa [prefixWord, tailWord_215446, baseEnd_215446] using wordTrace_append hprefix tailTrace_215446
  have hstable : (prefixWord ++ tailWord_215446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215446).length < 2 ^ (prefixWord ++ tailWord_215446).sum := by decide
  have hdescent : baseEnd_215446 < baseStart_215446 := by decide
  rcases family_descends (prefixWord ++ tailWord_215446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215484 : List Nat := [2, 2, 2, 4, 1, 1, 1, 2, 1, 7]
def baseStart_215484 : Nat := 118140960795 + 215484 * 2 ^ 59
def prefixEnd_215484 : Nat := 4983230072969 + 3 ^ 40 * 215484 * 2
def baseEnd_215484 : Nat := 36882288451180050519671

theorem tailTrace_215484 : CollatzResearch.WordTrace tailWord_215484 prefixEnd_215484 36882288451180050519671 := by
  unfold tailWord_215484
  simp only [CollatzResearch.WordTrace]
  refine ⟨3929673575672872291186753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5239564767563829721582337 3929673575672872291186753)
  ·
    refine ⟨2947255181754654218390065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3929673575672872291186753 2947255181754654218390065)
    ·
      refine ⟨2210441386315990663792549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2947255181754654218390065 2210441386315990663792549)
      ·
        refine ⟨414457759934248249461103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2210441386315990663792549 414457759934248249461103)
        ·
          refine ⟨621686639901372374191655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 414457759934248249461103 621686639901372374191655)
          ·
            refine ⟨932529959852058561287483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 621686639901372374191655 932529959852058561287483)
            ·
              refine ⟨1398794939778087841931225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 932529959852058561287483 1398794939778087841931225)
              ·
                refine ⟨1049096204833565881448419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1398794939778087841931225 1049096204833565881448419)
                ·
                  refine ⟨1573644307250348822172629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1049096204833565881448419 1573644307250348822172629)
                  ·
                    refine ⟨36882288451180050519671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1573644307250348822172629 36882288451180050519671)
                    ·
                      rfl

theorem cell23_215484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 2, 1, 7].length) (baseStart_215484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_215484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_215484 prefixEnd_215484 := by exact prefixLift 215484
  have htrace : WordTrace (prefixWord ++ tailWord_215484) baseStart_215484 baseEnd_215484 := by
    simpa [prefixWord, tailWord_215484, baseEnd_215484] using wordTrace_append hprefix tailTrace_215484
  have hstable : (prefixWord ++ tailWord_215484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215484).length < 2 ^ (prefixWord ++ tailWord_215484).sum := by decide
  have hdescent : baseEnd_215484 < baseStart_215484 := by decide
  rcases family_descends (prefixWord ++ tailWord_215484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215522 : List Nat := [3, 3, 3, 2, 1, 1, 3, 2, 5]
def baseStart_215522 : Nat := 118140960795 + 215522 * 2 ^ 59
def prefixEnd_215522 : Nat := 4983230072969 + 3 ^ 40 * 215522 * 2
def baseEnd_215522 : Nat := 12296264179823444764871

theorem tailTrace_215522 : CollatzResearch.WordTrace tailWord_215522 prefixEnd_215522 12296264179823444764871 := by
  unfold tailWord_215522
  simp only [CollatzResearch.WordTrace]
  refine ⟨1965183281302019268064205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5240488750138718048171213 1965183281302019268064205)
  ·
    refine ⟨736943730488257225524077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1965183281302019268064205 736943730488257225524077)
    ·
      refine ⟨276353898933096459571529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 736943730488257225524077 276353898933096459571529)
      ·
        refine ⟨207265424199822344678647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 276353898933096459571529 207265424199822344678647)
        ·
          refine ⟨310898136299733517017971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207265424199822344678647 310898136299733517017971)
          ·
            refine ⟨466347204449600275526957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 310898136299733517017971 466347204449600275526957)
            ·
              refine ⟨174880201668600103322609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 466347204449600275526957 174880201668600103322609)
              ·
                refine ⟨131160151251450077491957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 174880201668600103322609 131160151251450077491957)
                ·
                  refine ⟨12296264179823444764871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 131160151251450077491957 12296264179823444764871)
                  ·
                    rfl

theorem cell23_215522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 3, 2, 5].length) (baseStart_215522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_215522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_215522 prefixEnd_215522 := by exact prefixLift 215522
  have htrace : WordTrace (prefixWord ++ tailWord_215522) baseStart_215522 baseEnd_215522 := by
    simpa [prefixWord, tailWord_215522, baseEnd_215522] using wordTrace_append hprefix tailTrace_215522
  have hstable : (prefixWord ++ tailWord_215522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215522).length < 2 ^ (prefixWord ++ tailWord_215522).sum := by decide
  have hdescent : baseEnd_215522 < baseStart_215522 := by decide
  rcases family_descends (prefixWord ++ tailWord_215522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215544 : List Nat := [2, 1, 2, 1, 1, 4, 3, 3, 6]
def baseStart_215544 : Nat := 118140960795 + 215544 * 2 ^ 59
def prefixEnd_215544 : Nat := 4983230072969 + 3 ^ 40 * 215544 * 2
def baseEnd_215544 : Nat := 12297519354756657423193

theorem tailTrace_215544 : CollatzResearch.WordTrace tailWord_215544 prefixEnd_215544 12297519354756657423193 := by
  unfold tailWord_215544
  simp only [CollatzResearch.WordTrace]
  refine ⟨3930767765564187414778843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5241023687418916553038457 3930767765564187414778843)
  ·
    refine ⟨5896151648346281122168265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3930767765564187414778843 5896151648346281122168265)
    ·
      refine ⟨4422113736259710841626199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5896151648346281122168265 4422113736259710841626199)
      ·
        refine ⟨6633170604389566262439299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4422113736259710841626199 6633170604389566262439299)
        ·
          refine ⟨9949755906584349393658949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6633170604389566262439299 9949755906584349393658949)
          ·
            refine ⟨1865579232484565511311053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9949755906584349393658949 1865579232484565511311053)
            ·
              refine ⟨699592212181712066741645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1865579232484565511311053 699592212181712066741645)
              ·
                refine ⟨262347079568142025028117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 699592212181712066741645 262347079568142025028117)
                ·
                  refine ⟨12297519354756657423193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 262347079568142025028117 12297519354756657423193)
                  ·
                    rfl

theorem cell23_215544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 3, 6].length) (baseStart_215544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_215544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_215544 prefixEnd_215544 := by exact prefixLift 215544
  have htrace : WordTrace (prefixWord ++ tailWord_215544) baseStart_215544 baseEnd_215544 := by
    simpa [prefixWord, tailWord_215544, baseEnd_215544] using wordTrace_append hprefix tailTrace_215544
  have hstable : (prefixWord ++ tailWord_215544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215544).length < 2 ^ (prefixWord ++ tailWord_215544).sum := by decide
  have hdescent : baseEnd_215544 < baseStart_215544 := by decide
  rcases family_descends (prefixWord ++ tailWord_215544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215628 : List Nat := [2, 2, 1, 3, 1, 2, 1, 2, 5, 2, 2]
def baseStart_215628 : Nat := 118140960795 + 215628 * 2 ^ 59
def prefixEnd_215628 : Nat := 4983230072969 + 3 ^ 40 * 215628 * 2
def baseEnd_215628 : Nat := 110720806567787588158351

theorem tailTrace_215628 : CollatzResearch.WordTrace tailWord_215628 prefixEnd_215628 110720806567787588158351 := by
  unfold tailWord_215628
  simp only [CollatzResearch.WordTrace]
  refine ⟨3932299631412028587807769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5243066175216038117077025 3932299631412028587807769)
  ·
    refine ⟨2949224723559021440855827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3932299631412028587807769 2949224723559021440855827)
    ·
      refine ⟨4423837085338532161283741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2949224723559021440855827 4423837085338532161283741)
      ·
        refine ⟨1658938907001949560481403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4423837085338532161283741 1658938907001949560481403)
        ·
          refine ⟨2488408360502924340722105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1658938907001949560481403 2488408360502924340722105)
          ·
            refine ⟨1866306270377193255541579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2488408360502924340722105 1866306270377193255541579)
            ·
              refine ⟨2799459405565789883312369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1866306270377193255541579 2799459405565789883312369)
              ·
                refine ⟨2099594554174342412484277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2799459405565789883312369 2099594554174342412484277)
                ·
                  refine ⟨196836989453844601170401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2099594554174342412484277 196836989453844601170401)
                  ·
                    refine ⟨147627742090383450877801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 196836989453844601170401 147627742090383450877801)
                    ·
                      refine ⟨110720806567787588158351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 147627742090383450877801 110720806567787588158351)
                      ·
                        rfl

theorem cell23_215628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 2, 5, 2, 2].length) (baseStart_215628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_215628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_215628 prefixEnd_215628 := by exact prefixLift 215628
  have htrace : WordTrace (prefixWord ++ tailWord_215628) baseStart_215628 baseEnd_215628 := by
    simpa [prefixWord, tailWord_215628, baseEnd_215628] using wordTrace_append hprefix tailTrace_215628
  have hstable : (prefixWord ++ tailWord_215628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215628).length < 2 ^ (prefixWord ++ tailWord_215628).sum := by decide
  have hdescent : baseEnd_215628 < baseStart_215628 := by decide
  rcases family_descends (prefixWord ++ tailWord_215628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215634 : List Nat := [3, 2, 2, 1, 2, 1, 12]
def baseStart_215634 : Nat := 118140960795 + 215634 * 2 ^ 59
def prefixEnd_215634 : Nat := 4983230072969 + 3 ^ 40 * 215634 * 2
def baseEnd_215634 : Nat := 1366961573477957588683

theorem tailTrace_215634 : CollatzResearch.WordTrace tailWord_215634 prefixEnd_215634 1366961573477957588683 := by
  unfold tailWord_215634
  simp only [CollatzResearch.WordTrace]
  refine ⟨1966204525200580050083489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5243212067201546800222637 1966204525200580050083489)
  ·
    refine ⟨1474653393900435037562617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1966204525200580050083489 1474653393900435037562617)
    ·
      refine ⟨1105990045425326278171963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1474653393900435037562617 1105990045425326278171963)
      ·
        refine ⟨1658985068137989417257945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1105990045425326278171963 1658985068137989417257945)
        ·
          refine ⟨1244238801103492062943459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1658985068137989417257945 1244238801103492062943459)
          ·
            refine ⟨1866358201655238094415189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1244238801103492062943459 1866358201655238094415189)
            ·
              refine ⟨1366961573477957588683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 1866358201655238094415189 1366961573477957588683)
              ·
                rfl

theorem cell23_215634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 12].length) (baseStart_215634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_215634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_215634 prefixEnd_215634 := by exact prefixLift 215634
  have htrace : WordTrace (prefixWord ++ tailWord_215634) baseStart_215634 baseEnd_215634 := by
    simpa [prefixWord, tailWord_215634, baseEnd_215634] using wordTrace_append hprefix tailTrace_215634
  have hstable : (prefixWord ++ tailWord_215634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215634).length < 2 ^ (prefixWord ++ tailWord_215634).sum := by decide
  have hdescent : baseEnd_215634 < baseStart_215634 := by decide
  rcases family_descends (prefixWord ++ tailWord_215634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215735 : List Nat := [1, 1, 3, 1, 6, 1, 1, 2, 1, 4, 2]
def baseStart_215735 : Nat := 118140960795 + 215735 * 2 ^ 59
def prefixEnd_215735 : Nat := 4983230072969 + 3 ^ 40 * 215735 * 2
def baseEnd_215735 : Nat := 110775748997818669520359

theorem tailTrace_215735 : CollatzResearch.WordTrace tailWord_215735 prefixEnd_215735 110775748997818669520359 := by
  unfold tailWord_215735
  simp only [CollatzResearch.WordTrace]
  refine ⟨7868501873436414449760659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5245667915624276299840439 7868501873436414449760659)
  ·
    refine ⟨11802752810154621674640989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7868501873436414449760659 11802752810154621674640989)
    ·
      refine ⟨4426032303807983127990371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11802752810154621674640989 4426032303807983127990371)
      ·
        refine ⟨6639048455711974691985557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4426032303807983127990371 6639048455711974691985557)
        ·
          refine ⟨311205396361498813686823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 6639048455711974691985557 311205396361498813686823)
          ·
            refine ⟨466808094542248220530235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 311205396361498813686823 466808094542248220530235)
            ·
              refine ⟨700212141813372330795353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 466808094542248220530235 700212141813372330795353)
              ·
                refine ⟨525159106360029248096515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 700212141813372330795353 525159106360029248096515)
                ·
                  refine ⟨787738659540043872144773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 525159106360029248096515 787738659540043872144773)
                  ·
                    refine ⟨147700998663758226027145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 787738659540043872144773 147700998663758226027145)
                    ·
                      refine ⟨110775748997818669520359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 147700998663758226027145 110775748997818669520359)
                      ·
                        rfl

theorem cell23_215735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 2, 1, 4, 2].length) (baseStart_215735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_215735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_215735 prefixEnd_215735 := by exact prefixLift 215735
  have htrace : WordTrace (prefixWord ++ tailWord_215735) baseStart_215735 baseEnd_215735 := by
    simpa [prefixWord, tailWord_215735, baseEnd_215735] using wordTrace_append hprefix tailTrace_215735
  have hstable : (prefixWord ++ tailWord_215735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215735).length < 2 ^ (prefixWord ++ tailWord_215735).sum := by decide
  have hdescent : baseEnd_215735 < baseStart_215735 := by decide
  rcases family_descends (prefixWord ++ tailWord_215735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215752 : List Nat := [2, 1, 3, 1, 2, 4, 2, 2, 2, 2, 2]
def baseStart_215752 : Nat := 118140960795 + 215752 * 2 ^ 59
def prefixEnd_215752 : Nat := 4983230072969 + 3 ^ 40 * 215752 * 2
def baseEnd_215752 : Nat := 110784478168945103007781

theorem tailTrace_215752 : CollatzResearch.WordTrace tailWord_215752 prefixEnd_215752 110784478168945103007781 := by
  unfold tailWord_215752
  simp only [CollatzResearch.WordTrace]
  refine ⟨3934560957187413176564755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5246081276249884235419673 3934560957187413176564755)
  ·
    refine ⟨5901841435781119764847133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3934560957187413176564755 5901841435781119764847133)
    ·
      refine ⟨2213190538417919911817675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5901841435781119764847133 2213190538417919911817675)
      ·
        refine ⟨3319785807626879867726513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2213190538417919911817675 3319785807626879867726513)
        ·
          refine ⟨2489839355720159900794885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3319785807626879867726513 2489839355720159900794885)
          ·
            refine ⟨466844879197529981399041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2489839355720159900794885 466844879197529981399041)
            ·
              refine ⟨350133659398147486049281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 466844879197529981399041 350133659398147486049281)
              ·
                refine ⟨262600244548610614536961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 350133659398147486049281 262600244548610614536961)
                ·
                  refine ⟨196950183411457960902721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 262600244548610614536961 196950183411457960902721)
                  ·
                    refine ⟨147712637558593470677041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 196950183411457960902721 147712637558593470677041)
                    ·
                      refine ⟨110784478168945103007781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 147712637558593470677041 110784478168945103007781)
                      ·
                        rfl

theorem cell23_215752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2, 2, 2, 2, 2].length) (baseStart_215752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_215752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_215752 prefixEnd_215752 := by exact prefixLift 215752
  have htrace : WordTrace (prefixWord ++ tailWord_215752) baseStart_215752 baseEnd_215752 := by
    simpa [prefixWord, tailWord_215752, baseEnd_215752] using wordTrace_append hprefix tailTrace_215752
  have hstable : (prefixWord ++ tailWord_215752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215752).length < 2 ^ (prefixWord ++ tailWord_215752).sum := by decide
  have hdescent : baseEnd_215752 < baseStart_215752 := by decide
  rcases family_descends (prefixWord ++ tailWord_215752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215765 : List Nat := [1, 3, 2, 5, 1, 1, 1, 1, 2, 2, 4]
def baseStart_215765 : Nat := 118140960795 + 215765 * 2 ^ 59
def prefixEnd_215765 : Nat := 4983230072969 + 3 ^ 40 * 215765 * 2
def baseEnd_215765 : Nat := 110791153417453552145221

theorem tailTrace_215765 : CollatzResearch.WordTrace tailWord_215765 prefixEnd_215765 110791153417453552145221 := by
  unfold tailWord_215765
  simp only [CollatzResearch.WordTrace]
  refine ⟨7869596063327729573352749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5246397375551819715568499 7869596063327729573352749)
  ·
    refine ⟨2951098523747898590007281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7869596063327729573352749 2951098523747898590007281)
    ·
      refine ⟨2213323892810923942505461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2951098523747898590007281 2213323892810923942505461)
      ·
        refine ⟨207499114951024119609887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2213323892810923942505461 207499114951024119609887)
        ·
          refine ⟨311248672426536179414831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207499114951024119609887 311248672426536179414831)
          ·
            refine ⟨466873008639804269122247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 311248672426536179414831 466873008639804269122247)
            ·
              refine ⟨700309512959706403683371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 466873008639804269122247 700309512959706403683371)
              ·
                refine ⟨1050464269439559605525057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 700309512959706403683371 1050464269439559605525057)
                ·
                  refine ⟨787848202079669704143793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1050464269439559605525057 787848202079669704143793)
                  ·
                    refine ⟨590886151559752278107845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 787848202079669704143793 590886151559752278107845)
                    ·
                      refine ⟨110791153417453552145221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 590886151559752278107845 110791153417453552145221)
                      ·
                        rfl

theorem cell23_215765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_215765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_215765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_215765 prefixEnd_215765 := by exact prefixLift 215765
  have htrace : WordTrace (prefixWord ++ tailWord_215765) baseStart_215765 baseEnd_215765 := by
    simpa [prefixWord, tailWord_215765, baseEnd_215765] using wordTrace_append hprefix tailTrace_215765
  have hstable : (prefixWord ++ tailWord_215765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215765).length < 2 ^ (prefixWord ++ tailWord_215765).sum := by decide
  have hdescent : baseEnd_215765 < baseStart_215765 := by decide
  rcases family_descends (prefixWord ++ tailWord_215765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215768 : List Nat := [2, 1, 2, 2, 3, 3, 1, 1, 2, 3, 3]
def baseStart_215768 : Nat := 118140960795 + 215768 * 2 ^ 59
def prefixEnd_215768 : Nat := 4983230072969 + 3 ^ 40 * 215768 * 2
def baseEnd_215768 : Nat := 110792693859417040407707

theorem tailTrace_215768 : CollatzResearch.WordTrace tailWord_215768 prefixEnd_215768 110792693859417040407707 := by
  unfold tailWord_215768
  simp only [CollatzResearch.WordTrace]
  refine ⟨3934852741158430542855979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5246470321544574057141305 3934852741158430542855979)
  ·
    refine ⟨5902279111737645814283969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3934852741158430542855979 5902279111737645814283969)
    ·
      refine ⟨4426709333803234360712977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5902279111737645814283969 4426709333803234360712977)
      ·
        refine ⟨3320032000352425770534733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4426709333803234360712977 3320032000352425770534733)
        ·
          refine ⟨1245012000132159663950525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3320032000352425770534733 1245012000132159663950525)
          ·
            refine ⟨466879500049559873981447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1245012000132159663950525 466879500049559873981447)
            ·
              refine ⟨700319250074339810972171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 466879500049559873981447 700319250074339810972171)
              ·
                refine ⟨1050478875111509716458257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 700319250074339810972171 1050478875111509716458257)
                ·
                  refine ⟨787859156333632287343693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1050478875111509716458257 787859156333632287343693)
                  ·
                    refine ⟨295447183625112107753885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 787859156333632287343693 295447183625112107753885)
                    ·
                      refine ⟨110792693859417040407707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 295447183625112107753885 110792693859417040407707)
                      ·
                        rfl

theorem cell23_215768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 1, 2, 3, 3].length) (baseStart_215768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_215768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_215768 prefixEnd_215768 := by exact prefixLift 215768
  have htrace : WordTrace (prefixWord ++ tailWord_215768) baseStart_215768 baseEnd_215768 := by
    simpa [prefixWord, tailWord_215768, baseEnd_215768] using wordTrace_append hprefix tailTrace_215768
  have hstable : (prefixWord ++ tailWord_215768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215768).length < 2 ^ (prefixWord ++ tailWord_215768).sum := by decide
  have hdescent : baseEnd_215768 < baseStart_215768 := by decide
  rcases family_descends (prefixWord ++ tailWord_215768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215869 : List Nat := [1, 4, 1, 4, 3, 1, 1, 1, 3, 4]
def baseStart_215869 : Nat := 118140960795 + 215869 * 2 ^ 59
def prefixEnd_215869 : Nat := 4983230072969 + 3 ^ 40 * 215869 * 2
def baseEnd_215869 : Nat := 36948185135173715081581

theorem tailTrace_215869 : CollatzResearch.WordTrace tailWord_215869 prefixEnd_215869 36948185135173715081581 := by
  unfold tailWord_215869
  simp only [CollatzResearch.WordTrace]
  refine ⟨7873389254950955335138661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5248926169967303556759107 7873389254950955335138661)
  ·
    refine ⟨1476260485303304125338499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7873389254950955335138661 1476260485303304125338499)
    ·
      refine ⟨2214390727954956188007749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1476260485303304125338499 2214390727954956188007749)
      ·
        refine ⟨415198261491554285251453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2214390727954956188007749 415198261491554285251453)
        ·
          refine ⟨155699348059332856969295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 415198261491554285251453 155699348059332856969295)
          ·
            refine ⟨233549022088999285453943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155699348059332856969295 233549022088999285453943)
            ·
              refine ⟨350323533133498928180915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 233549022088999285453943 350323533133498928180915)
              ·
                refine ⟨525485299700248392271373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 350323533133498928180915 525485299700248392271373)
                ·
                  refine ⟨197056987387593147101765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 525485299700248392271373 197056987387593147101765)
                  ·
                    refine ⟨36948185135173715081581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 197056987387593147101765 36948185135173715081581)
                    ·
                      rfl

theorem cell23_215869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 1, 1, 3, 4].length) (baseStart_215869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_215869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_215869 prefixEnd_215869 := by exact prefixLift 215869
  have htrace : WordTrace (prefixWord ++ tailWord_215869) baseStart_215869 baseEnd_215869 := by
    simpa [prefixWord, tailWord_215869, baseEnd_215869] using wordTrace_append hprefix tailTrace_215869
  have hstable : (prefixWord ++ tailWord_215869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215869).length < 2 ^ (prefixWord ++ tailWord_215869).sum := by decide
  have hdescent : baseEnd_215869 < baseStart_215869 := by decide
  rcases family_descends (prefixWord ++ tailWord_215869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215891 : List Nat := [1, 1, 1, 2, 1, 1, 3, 2, 5, 6]
def baseStart_215891 : Nat := 118140960795 + 215891 * 2 ^ 59
def prefixEnd_215891 : Nat := 4983230072969 + 3 ^ 40 * 215891 * 2
def baseEnd_215891 : Nat := 36951950659973353056547

theorem tailTrace_215891 : CollatzResearch.WordTrace tailWord_215891 prefixEnd_215891 36951950659973353056547 := by
  unfold tailWord_215891
  simp only [CollatzResearch.WordTrace]
  refine ⟨7874191660871253092439527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5249461107247502061626351 7874191660871253092439527)
  ·
    refine ⟨11811287491306879638659291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7874191660871253092439527 11811287491306879638659291)
    ·
      refine ⟨17716931236960319457988937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11811287491306879638659291 17716931236960319457988937)
      ·
        refine ⟨13287698427720239593491703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17716931236960319457988937 13287698427720239593491703)
        ·
          refine ⟨19931547641580359390237555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13287698427720239593491703 19931547641580359390237555)
          ·
            refine ⟨29897321462370539085356333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19931547641580359390237555 29897321462370539085356333)
            ·
              refine ⟨11211495548388952157008625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29897321462370539085356333 11211495548388952157008625)
              ·
                refine ⟨8408621661291714117756469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11211495548388952157008625 8408621661291714117756469)
                ·
                  refine ⟨788308280746098198539669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8408621661291714117756469 788308280746098198539669)
                  ·
                    refine ⟨36951950659973353056547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 788308280746098198539669 36951950659973353056547)
                    ·
                      rfl

theorem cell23_215891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 5, 6].length) (baseStart_215891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_215891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_215891 prefixEnd_215891 := by exact prefixLift 215891
  have htrace : WordTrace (prefixWord ++ tailWord_215891) baseStart_215891 baseEnd_215891 := by
    simpa [prefixWord, tailWord_215891, baseEnd_215891] using wordTrace_append hprefix tailTrace_215891
  have hstable : (prefixWord ++ tailWord_215891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215891).length < 2 ^ (prefixWord ++ tailWord_215891).sum := by decide
  have hdescent : baseEnd_215891 < baseStart_215891 := by decide
  rcases family_descends (prefixWord ++ tailWord_215891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215895 : List Nat := [1, 1, 3, 2, 4, 1, 3, 2, 1, 5]
def baseStart_215895 : Nat := 118140960795 + 215895 * 2 ^ 59
def prefixEnd_215895 : Nat := 4983230072969 + 3 ^ 40 * 215895 * 2
def baseEnd_215895 : Nat := 36952635300846014506541

theorem tailTrace_215895 : CollatzResearch.WordTrace tailWord_215895 prefixEnd_215895 36952635300846014506541 := by
  unfold tailWord_215895
  simp only [CollatzResearch.WordTrace]
  refine ⟨7874337552856761775585139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5249558368571174517056759 7874337552856761775585139)
  ·
    refine ⟨11811506329285142663377709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7874337552856761775585139 11811506329285142663377709)
    ·
      refine ⟨4429314873481928498766641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11811506329285142663377709 4429314873481928498766641)
      ·
        refine ⟨3321986155111446374074981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4429314873481928498766641 3321986155111446374074981)
        ·
          refine ⟨622872404083396195139059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3321986155111446374074981 622872404083396195139059)
          ·
            refine ⟨934308606125094292708589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 622872404083396195139059 934308606125094292708589)
            ·
              refine ⟨350365727296910359765721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 934308606125094292708589 350365727296910359765721)
              ·
                refine ⟨262774295472682769824291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 350365727296910359765721 262774295472682769824291)
                ·
                  refine ⟨394161443209024154736437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 262774295472682769824291 394161443209024154736437)
                  ·
                    refine ⟨36952635300846014506541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 394161443209024154736437 36952635300846014506541)
                    ·
                      rfl

theorem cell23_215895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3, 2, 1, 5].length) (baseStart_215895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_215895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_215895 prefixEnd_215895 := by exact prefixLift 215895
  have htrace : WordTrace (prefixWord ++ tailWord_215895) baseStart_215895 baseEnd_215895 := by
    simpa [prefixWord, tailWord_215895, baseEnd_215895] using wordTrace_append hprefix tailTrace_215895
  have hstable : (prefixWord ++ tailWord_215895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215895).length < 2 ^ (prefixWord ++ tailWord_215895).sum := by decide
  have hdescent : baseEnd_215895 < baseStart_215895 := by decide
  rcases family_descends (prefixWord ++ tailWord_215895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215908 : List Nat := [2, 3, 1, 1, 4, 1, 1, 1, 3, 6]
def baseStart_215908 : Nat := 118140960795 + 215908 * 2 ^ 59
def prefixEnd_215908 : Nat := 4983230072969 + 3 ^ 40 * 215908 * 2
def baseEnd_215908 : Nat := 36954860383682164219021

theorem tailTrace_215908 : CollatzResearch.WordTrace tailWord_215908 prefixEnd_215908 36954860383682164219021 := by
  unfold tailWord_215908
  simp only [CollatzResearch.WordTrace]
  refine ⟨3937405850904832497904189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5249874467873109997205585 3937405850904832497904189)
  ·
    refine ⟨1476527194089312186714071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3937405850904832497904189 1476527194089312186714071)
    ·
      refine ⟨2214790791133968280071107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1476527194089312186714071 2214790791133968280071107)
      ·
        refine ⟨3322186186700952420106661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2214790791133968280071107 3322186186700952420106661)
        ·
          refine ⟨622909910006428578769999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3322186186700952420106661 622909910006428578769999)
          ·
            refine ⟨934364865009642868154999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 622909910006428578769999 934364865009642868154999)
            ·
              refine ⟨1401547297514464302232499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 934364865009642868154999 1401547297514464302232499)
              ·
                refine ⟨2102320946271696453348749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1401547297514464302232499 2102320946271696453348749)
                ·
                  refine ⟨788370354851886170005781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2102320946271696453348749 788370354851886170005781)
                  ·
                    refine ⟨36954860383682164219021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 788370354851886170005781 36954860383682164219021)
                    ·
                      rfl

theorem cell23_215908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 1, 3, 6].length) (baseStart_215908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_215908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_215908 prefixEnd_215908 := by exact prefixLift 215908
  have htrace : WordTrace (prefixWord ++ tailWord_215908) baseStart_215908 baseEnd_215908 := by
    simpa [prefixWord, tailWord_215908, baseEnd_215908] using wordTrace_append hprefix tailTrace_215908
  have hstable : (prefixWord ++ tailWord_215908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215908).length < 2 ^ (prefixWord ++ tailWord_215908).sum := by decide
  have hdescent : baseEnd_215908 < baseStart_215908 := by decide
  rcases family_descends (prefixWord ++ tailWord_215908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215912 : List Nat := [2, 1, 4, 2, 1, 3, 3, 1, 1, 5]
def baseStart_215912 : Nat := 118140960795 + 215912 * 2 ^ 59
def prefixEnd_215912 : Nat := 4983230072969 + 3 ^ 40 * 215912 * 2
def baseEnd_215912 : Nat := 36955545024554825669015

theorem tailTrace_215912 : CollatzResearch.WordTrace tailWord_215912 prefixEnd_215912 36955545024554825669015 := by
  unfold tailWord_215912
  simp only [CollatzResearch.WordTrace]
  refine ⟨3937478796897586839476995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5249971729196782452635993 3937478796897586839476995)
  ·
    refine ⟨5906218195346380259215493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3937478796897586839476995 5906218195346380259215493)
    ·
      refine ⟨1107415911627446298602905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5906218195346380259215493 1107415911627446298602905)
      ·
        refine ⟨830561933720584723952179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1107415911627446298602905 830561933720584723952179)
        ·
          refine ⟨1245842900580877085928269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 830561933720584723952179 1245842900580877085928269)
          ·
            refine ⟨467191087717828907223101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1245842900580877085928269 467191087717828907223101)
            ·
              refine ⟨175196657894185840208663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 467191087717828907223101 175196657894185840208663)
              ·
                refine ⟨262794986841278760312995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 175196657894185840208663 262794986841278760312995)
                ·
                  refine ⟨394192480261918140469493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 262794986841278760312995 394192480261918140469493)
                  ·
                    refine ⟨36955545024554825669015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 394192480261918140469493 36955545024554825669015)
                    ·
                      rfl

theorem cell23_215912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 3, 1, 1, 5].length) (baseStart_215912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_215912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_215912 prefixEnd_215912 := by exact prefixLift 215912
  have htrace : WordTrace (prefixWord ++ tailWord_215912) baseStart_215912 baseEnd_215912 := by
    simpa [prefixWord, tailWord_215912, baseEnd_215912] using wordTrace_append hprefix tailTrace_215912
  have hstable : (prefixWord ++ tailWord_215912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215912).length < 2 ^ (prefixWord ++ tailWord_215912).sum := by decide
  have hdescent : baseEnd_215912 < baseStart_215912 := by decide
  rcases family_descends (prefixWord ++ tailWord_215912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215921 : List Nat := [1, 2, 2, 2, 1, 15]
def baseStart_215921 : Nat := 118140960795 + 215921 * 2 ^ 59
def prefixEnd_215921 : Nat := 4983230072969 + 3 ^ 40 * 215921 * 2
def baseEnd_215921 : Nat := 456260314401460665821

theorem tailTrace_215921 : CollatzResearch.WordTrace tailWord_215921 prefixEnd_215921 456260314401460665821 := by
  unfold tailWord_215921
  simp only [CollatzResearch.WordTrace]
  refine ⟨7875285850762568216031617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5250190567175045477354411 7875285850762568216031617)
  ·
    refine ⟨5906464388071926162023713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7875285850762568216031617 5906464388071926162023713)
    ·
      refine ⟨4429848291053944621517785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5906464388071926162023713 4429848291053944621517785)
      ·
        refine ⟨3322386218290458466138339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4429848291053944621517785 3322386218290458466138339)
        ·
          refine ⟨4983579327435687699207509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3322386218290458466138339 4983579327435687699207509)
          ·
            refine ⟨456260314401460665821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 15 4983579327435687699207509 456260314401460665821)
            ·
              rfl

theorem cell23_215921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 15].length) (baseStart_215921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_215921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_215921 prefixEnd_215921 := by exact prefixLift 215921
  have htrace : WordTrace (prefixWord ++ tailWord_215921) baseStart_215921 baseEnd_215921 := by
    simpa [prefixWord, tailWord_215921, baseEnd_215921] using wordTrace_append hprefix tailTrace_215921
  have hstable : (prefixWord ++ tailWord_215921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215921).length < 2 ^ (prefixWord ++ tailWord_215921).sum := by decide
  have hdescent : baseEnd_215921 < baseStart_215921 := by decide
  rcases family_descends (prefixWord ++ tailWord_215921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215926 : List Nat := [5, 1, 1, 3, 1, 2, 1, 4, 1, 1, 3]
def baseStart_215926 : Nat := 118140960795 + 215926 * 2 ^ 59
def prefixEnd_215926 : Nat := 4983230072969 + 3 ^ 40 * 215926 * 2
def baseEnd_215926 : Nat := 110873823802827422231981

theorem tailTrace_215926 : CollatzResearch.WordTrace tailWord_215926 prefixEnd_215926 110873823802827422231981 := by
  unfold tailWord_215926
  simp only [CollatzResearch.WordTrace]
  refine ⟨492216763484028379372727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5250312143829636046642421 492216763484028379372727)
  ·
    refine ⟨738325145226042569059091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 492216763484028379372727 738325145226042569059091)
    ·
      refine ⟨1107487717839063853588637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 738325145226042569059091 1107487717839063853588637)
      ·
        refine ⟨415307894189648945095739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1107487717839063853588637 415307894189648945095739)
        ·
          refine ⟨622961841284473417643609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 415307894189648945095739 622961841284473417643609)
          ·
            refine ⟨467221380963355063232707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 622961841284473417643609 467221380963355063232707)
            ·
              refine ⟨700832071445032594849061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 467221380963355063232707 700832071445032594849061)
              ·
                refine ⟨131406013395943611534199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 700832071445032594849061 131406013395943611534199)
                ·
                  refine ⟨197109020093915417301299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 131406013395943611534199 197109020093915417301299)
                  ·
                    refine ⟨295663530140873125951949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 197109020093915417301299 295663530140873125951949)
                    ·
                      refine ⟨110873823802827422231981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 295663530140873125951949 110873823802827422231981)
                      ·
                        rfl

theorem cell23_215926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 4, 1, 1, 3].length) (baseStart_215926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_215926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_215926 prefixEnd_215926 := by exact prefixLift 215926
  have htrace : WordTrace (prefixWord ++ tailWord_215926) baseStart_215926 baseEnd_215926 := by
    simpa [prefixWord, tailWord_215926, baseEnd_215926] using wordTrace_append hprefix tailTrace_215926
  have hstable : (prefixWord ++ tailWord_215926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215926).length < 2 ^ (prefixWord ++ tailWord_215926).sum := by decide
  have hdescent : baseEnd_215926 < baseStart_215926 := by decide
  rcases family_descends (prefixWord ++ tailWord_215926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215945 : List Nat := [1, 2, 1, 1, 5, 3, 2, 1, 1, 2, 4]
def baseStart_215945 : Nat := 118140960795 + 215945 * 2 ^ 59
def prefixEnd_215945 : Nat := 4983230072969 + 3 ^ 40 * 215945 * 2
def baseEnd_215945 : Nat := 110883579935262847894393

theorem tailTrace_215945 : CollatzResearch.WordTrace tailWord_215945 prefixEnd_215945 110883579935262847894393 := by
  unfold tailWord_215945
  simp only [CollatzResearch.WordTrace]
  refine ⟨7876161202675620314905289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5250774135117080209936859 7876161202675620314905289)
  ·
    refine ⟨5907120902006715236178967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7876161202675620314905289 5907120902006715236178967)
    ·
      refine ⟨8860681353010072854268451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5907120902006715236178967 8860681353010072854268451)
      ·
        refine ⟨13291022029515109281402677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8860681353010072854268451 13291022029515109281402677)
        ·
          refine ⟨1246033315267041495131501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13291022029515109281402677 1246033315267041495131501)
          ·
            refine ⟨467262493225140560674313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1246033315267041495131501 467262493225140560674313)
            ·
              refine ⟨350446869918855420505735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 467262493225140560674313 350446869918855420505735)
              ·
                refine ⟨525670304878283130758603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 350446869918855420505735 525670304878283130758603)
                ·
                  refine ⟨788505457317424696137905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 525670304878283130758603 788505457317424696137905)
                  ·
                    refine ⟨591379092988068522103429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 788505457317424696137905 591379092988068522103429)
                    ·
                      refine ⟨110883579935262847894393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 591379092988068522103429 110883579935262847894393)
                      ·
                        rfl

theorem cell23_215945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2, 1, 1, 2, 4].length) (baseStart_215945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_215945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_215945 prefixEnd_215945 := by exact prefixLift 215945
  have htrace : WordTrace (prefixWord ++ tailWord_215945) baseStart_215945 baseEnd_215945 := by
    simpa [prefixWord, tailWord_215945, baseEnd_215945] using wordTrace_append hprefix tailTrace_215945
  have hstable : (prefixWord ++ tailWord_215945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215945).length < 2 ^ (prefixWord ++ tailWord_215945).sum := by decide
  have hdescent : baseEnd_215945 < baseStart_215945 := by decide
  rcases family_descends (prefixWord ++ tailWord_215945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215965 : List Nat := [1, 4, 2, 1, 2, 1, 1, 4, 1, 3, 3]
def baseStart_215965 : Nat := 118140960795 + 215965 * 2 ^ 59
def prefixEnd_215965 : Nat := 4983230072969 + 3 ^ 40 * 215965 * 2
def baseEnd_215965 : Nat := 110893849548352769644301

theorem tailTrace_215965 : CollatzResearch.WordTrace tailWord_215965 prefixEnd_215965 110893849548352769644301 := by
  unfold tailWord_215965
  simp only [CollatzResearch.WordTrace]
  refine ⟨7876890662603163730633349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5251260441735442487088899 7876890662603163730633349)
  ·
    refine ⟨1476916999238093199493753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7876890662603163730633349 1476916999238093199493753)
    ·
      refine ⟨1107687749428569899620315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1476916999238093199493753 1107687749428569899620315)
      ·
        refine ⟨1661531624142854849430473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1107687749428569899620315 1661531624142854849430473)
        ·
          refine ⟨1246148718107141137072855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1661531624142854849430473 1246148718107141137072855)
          ·
            refine ⟨1869223077160711705609283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1246148718107141137072855 1869223077160711705609283)
            ·
              refine ⟨2803834615741067558413925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1869223077160711705609283 2803834615741067558413925)
              ·
                refine ⟨525718990451450167202611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2803834615741067558413925 525718990451450167202611)
                ·
                  refine ⟨788578485677175250803917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 525718990451450167202611 788578485677175250803917)
                  ·
                    refine ⟨295716932128940719051469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 788578485677175250803917 295716932128940719051469)
                    ·
                      refine ⟨110893849548352769644301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 295716932128940719051469 110893849548352769644301)
                      ·
                        rfl

theorem cell23_215965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 4, 1, 3, 3].length) (baseStart_215965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_215965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_215965 prefixEnd_215965 := by exact prefixLift 215965
  have htrace : WordTrace (prefixWord ++ tailWord_215965) baseStart_215965 baseEnd_215965 := by
    simpa [prefixWord, tailWord_215965, baseEnd_215965] using wordTrace_append hprefix tailTrace_215965
  have hstable : (prefixWord ++ tailWord_215965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215965).length < 2 ^ (prefixWord ++ tailWord_215965).sum := by decide
  have hdescent : baseEnd_215965 < baseStart_215965 := by decide
  rcases family_descends (prefixWord ++ tailWord_215965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215969 : List Nat := [1, 2, 3, 4, 1, 1, 4, 1, 1, 2, 3]
def baseStart_215969 : Nat := 118140960795 + 215969 * 2 ^ 59
def prefixEnd_215969 : Nat := 4983230072969 + 3 ^ 40 * 215969 * 2
def baseEnd_215969 : Nat := 110895903470970753994283

theorem tailTrace_215969 : CollatzResearch.WordTrace tailWord_215969 prefixEnd_215969 110895903470970753994283 := by
  unfold tailWord_215969
  simp only [CollatzResearch.WordTrace]
  refine ⟨7877036554588672413778961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5251357703059114942519307 7877036554588672413778961)
  ·
    refine ⟨5907777415941504310334221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7877036554588672413778961 5907777415941504310334221)
    ·
      refine ⟨2215416530978064116375333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5907777415941504310334221 2215416530978064116375333)
      ·
        refine ⟨415390599558387021820375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2215416530978064116375333 415390599558387021820375)
        ·
          refine ⟨623085899337580532730563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 415390599558387021820375 623085899337580532730563)
          ·
            refine ⟨934628849006370799095845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 623085899337580532730563 934628849006370799095845)
            ·
              refine ⟨175242909188694524830471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 934628849006370799095845 175242909188694524830471)
              ·
                refine ⟨262864363783041787245707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 175242909188694524830471 262864363783041787245707)
                ·
                  refine ⟨394296545674562680868561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 262864363783041787245707 394296545674562680868561)
                  ·
                    refine ⟨295722409255922010651421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 394296545674562680868561 295722409255922010651421)
                    ·
                      refine ⟨110895903470970753994283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 295722409255922010651421 110895903470970753994283)
                      ·
                        rfl

theorem cell23_215969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 4, 1, 1, 2, 3].length) (baseStart_215969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_215969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_215969 prefixEnd_215969 := by exact prefixLift 215969
  have htrace : WordTrace (prefixWord ++ tailWord_215969) baseStart_215969 baseEnd_215969 := by
    simpa [prefixWord, tailWord_215969, baseEnd_215969] using wordTrace_append hprefix tailTrace_215969
  have hstable : (prefixWord ++ tailWord_215969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215969).length < 2 ^ (prefixWord ++ tailWord_215969).sum := by decide
  have hdescent : baseEnd_215969 < baseStart_215969 := by decide
  rcases family_descends (prefixWord ++ tailWord_215969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216006 : List Nat := [6, 1, 3, 1, 1, 1, 1, 9]
def baseStart_216006 : Nat := 118140960795 + 216006 * 2 ^ 59
def prefixEnd_216006 : Nat := 4983230072969 + 3 ^ 40 * 216006 * 2
def baseEnd_216006 : Nat := 4107959342784707749319

theorem tailTrace_216006 : CollatzResearch.WordTrace tailWord_216006 prefixEnd_216006 4107959342784707749319 := by
  unfold tailWord_216006
  simp only [CollatzResearch.WordTrace]
  refine ⟨246199564232957116652371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 5252257370303085155250581 246199564232957116652371)
  ·
    refine ⟨369299346349435674978557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246199564232957116652371 369299346349435674978557)
    ·
      refine ⟨138487254881038378116959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 369299346349435674978557 138487254881038378116959)
      ·
        refine ⟨207730882321557567175439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138487254881038378116959 207730882321557567175439)
        ·
          refine ⟨311596323482336350763159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207730882321557567175439 311596323482336350763159)
          ·
            refine ⟨467394485223504526144739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 311596323482336350763159 467394485223504526144739)
            ·
              refine ⟨701091727835256789217109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 467394485223504526144739 701091727835256789217109)
              ·
                refine ⟨4107959342784707749319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 701091727835256789217109 4107959342784707749319)
                ·
                  rfl

theorem cell23_216006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 9].length) (baseStart_216006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_216006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_216006 prefixEnd_216006 := by exact prefixLift 216006
  have htrace : WordTrace (prefixWord ++ tailWord_216006) baseStart_216006 baseEnd_216006 := by
    simpa [prefixWord, tailWord_216006, baseEnd_216006] using wordTrace_append hprefix tailTrace_216006
  have hstable : (prefixWord ++ tailWord_216006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216006).length < 2 ^ (prefixWord ++ tailWord_216006).sum := by decide
  have hdescent : baseEnd_216006 < baseStart_216006 := by decide
  rcases family_descends (prefixWord ++ tailWord_216006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216025 : List Nat := [1, 2, 1, 2, 5, 2, 1, 1, 2, 1, 5]
def baseStart_216025 : Nat := 118140960795 + 216025 * 2 ^ 59
def prefixEnd_216025 : Nat := 4983230072969 + 3 ^ 40 * 216025 * 2
def baseEnd_216025 : Nat := 110924658387622534894025

theorem tailTrace_216025 : CollatzResearch.WordTrace tailWord_216025 prefixEnd_216025 110924658387622534894025 := by
  unfold tailWord_216025
  simp only [CollatzResearch.WordTrace]
  refine ⟨7879079042385793977817529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5252719361590529318545019 7879079042385793977817529)
  ·
    refine ⟨5909309281789345483363147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7879079042385793977817529 5909309281789345483363147)
    ·
      refine ⟨8863963922684018225044721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5909309281789345483363147 8863963922684018225044721)
      ·
        refine ⟨6647972942013013668783541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8863963922684018225044721 6647972942013013668783541)
        ·
          refine ⟨623247463313720031448457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6647972942013013668783541 623247463313720031448457)
          ·
            refine ⟨467435597485290023586343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 623247463313720031448457 467435597485290023586343)
            ·
              refine ⟨701153396227935035379515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 467435597485290023586343 701153396227935035379515)
              ·
                refine ⟨1051730094341902553069273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 701153396227935035379515 1051730094341902553069273)
                ·
                  refine ⟨788797570756426914801955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1051730094341902553069273 788797570756426914801955)
                  ·
                    refine ⟨1183196356134640372202933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 788797570756426914801955 1183196356134640372202933)
                    ·
                      refine ⟨110924658387622534894025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1183196356134640372202933 110924658387622534894025)
                      ·
                        rfl

theorem cell23_216025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 1, 2, 1, 5].length) (baseStart_216025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_216025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_216025 prefixEnd_216025 := by exact prefixLift 216025
  have htrace : WordTrace (prefixWord ++ tailWord_216025) baseStart_216025 baseEnd_216025 := by
    simpa [prefixWord, tailWord_216025, baseEnd_216025] using wordTrace_append hprefix tailTrace_216025
  have hstable : (prefixWord ++ tailWord_216025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216025).length < 2 ^ (prefixWord ++ tailWord_216025).sum := by decide
  have hdescent : baseEnd_216025 < baseStart_216025 := by decide
  rcases family_descends (prefixWord ++ tailWord_216025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216039 : List Nat := [1, 1, 5, 2, 2, 1, 2, 1, 4, 2, 2]
def baseStart_216039 : Nat := 118140960795 + 216039 * 2 ^ 59
def prefixEnd_216039 : Nat := 4983230072969 + 3 ^ 40 * 216039 * 2
def baseEnd_216039 : Nat := 110931847116785480118961

theorem tailTrace_216039 : CollatzResearch.WordTrace tailWord_216039 prefixEnd_216039 110931847116785480118961 := by
  unfold tailWord_216039
  simp only [CollatzResearch.WordTrace]
  refine ⟨7879589664335074368827171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5253059776223382912551447 7879589664335074368827171)
  ·
    refine ⟨11819384496502611553240757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7879589664335074368827171 11819384496502611553240757)
    ·
      refine ⟨1108067296547119833116321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11819384496502611553240757 1108067296547119833116321)
      ·
        refine ⟨831050472410339874837241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1108067296547119833116321 831050472410339874837241)
        ·
          refine ⟨623287854307754906127931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 831050472410339874837241 623287854307754906127931)
          ·
            refine ⟨934931781461632359191897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 623287854307754906127931 934931781461632359191897)
            ·
              refine ⟨701198836096224269393923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 934931781461632359191897 701198836096224269393923)
              ·
                refine ⟨1051798254144336404090885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 701198836096224269393923 1051798254144336404090885)
                ·
                  refine ⟨197212172652063075767041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1051798254144336404090885 197212172652063075767041)
                  ·
                    refine ⟨147909129489047306825281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 197212172652063075767041 147909129489047306825281)
                    ·
                      refine ⟨110931847116785480118961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 147909129489047306825281 110931847116785480118961)
                      ·
                        rfl

theorem cell23_216039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 1, 4, 2, 2].length) (baseStart_216039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_216039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_216039 prefixEnd_216039 := by exact prefixLift 216039
  have htrace : WordTrace (prefixWord ++ tailWord_216039) baseStart_216039 baseEnd_216039 := by
    simpa [prefixWord, tailWord_216039, baseEnd_216039] using wordTrace_append hprefix tailTrace_216039
  have hstable : (prefixWord ++ tailWord_216039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216039).length < 2 ^ (prefixWord ++ tailWord_216039).sum := by decide
  have hdescent : baseEnd_216039 < baseStart_216039 := by decide
  rcases family_descends (prefixWord ++ tailWord_216039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216050 : List Nat := [3, 2, 1, 5, 2, 1, 2, 1, 2, 1, 3]
def baseStart_216050 : Nat := 118140960795 + 216050 * 2 ^ 59
def prefixEnd_216050 : Nat := 4983230072969 + 3 ^ 40 * 216050 * 2
def baseEnd_216050 : Nat := 110937495403984937081411

theorem tailTrace_216050 : CollatzResearch.WordTrace tailWord_216050 prefixEnd_216050 110937495403984937081411 := by
  unfold tailWord_216050
  simp only [CollatzResearch.WordTrace]
  refine ⟨1969997716823805811869401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5253327244863482164985069 1969997716823805811869401)
  ·
    refine ⟨1477498287617854358902051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1969997716823805811869401 1477498287617854358902051)
    ·
      refine ⟨2216247431426781538353077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1477498287617854358902051 2216247431426781538353077)
      ·
        refine ⟨207773196696260769220601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2216247431426781538353077 207773196696260769220601)
        ·
          refine ⟨155829897522195576915451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207773196696260769220601 155829897522195576915451)
          ·
            refine ⟨233744846283293365373177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155829897522195576915451 233744846283293365373177)
            ·
              refine ⟨175308634712470024029883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 233744846283293365373177 175308634712470024029883)
              ·
                refine ⟨262962952068705036044825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 175308634712470024029883 262962952068705036044825)
                ·
                  refine ⟨197222214051528777033619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 262962952068705036044825 197222214051528777033619)
                  ·
                    refine ⟨295833321077293165550429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 197222214051528777033619 295833321077293165550429)
                    ·
                      refine ⟨110937495403984937081411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 295833321077293165550429 110937495403984937081411)
                      ·
                        rfl

theorem cell23_216050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_216050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_216050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_216050 prefixEnd_216050 := by exact prefixLift 216050
  have htrace : WordTrace (prefixWord ++ tailWord_216050) baseStart_216050 baseEnd_216050 := by
    simpa [prefixWord, tailWord_216050, baseEnd_216050] using wordTrace_append hprefix tailTrace_216050
  have hstable : (prefixWord ++ tailWord_216050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216050).length < 2 ^ (prefixWord ++ tailWord_216050).sum := by decide
  have hdescent : baseEnd_216050 < baseStart_216050 := by decide
  rcases family_descends (prefixWord ++ tailWord_216050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216058 : List Nat := [3, 1, 1, 1, 1, 2, 1, 3, 3, 7]
def baseStart_216058 : Nat := 118140960795 + 216058 * 2 ^ 59
def prefixEnd_216058 : Nat := 4983230072969 + 3 ^ 40 * 216058 * 2
def baseEnd_216058 : Nat := 36980534416406968593791

theorem tailTrace_216058 : CollatzResearch.WordTrace tailWord_216058 prefixEnd_216058 36980534416406968593791 := by
  unfold tailWord_216058
  simp only [CollatzResearch.WordTrace]
  refine ⟨1970070662816560153442207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5253521767510827075845885 1970070662816560153442207)
  ·
    refine ⟨2955105994224840230163311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1970070662816560153442207 2955105994224840230163311)
    ·
      refine ⟨4432658991337260345244967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2955105994224840230163311 4432658991337260345244967)
      ·
        refine ⟨6648988487005890517867451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4432658991337260345244967 6648988487005890517867451)
        ·
          refine ⟨9973482730508835776801177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6648988487005890517867451 9973482730508835776801177)
          ·
            refine ⟨7480112047881626832600883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9973482730508835776801177 7480112047881626832600883)
            ·
              refine ⟨11220168071822440248901325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7480112047881626832600883 11220168071822440248901325)
              ·
                refine ⟨4207563026933415093337997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11220168071822440248901325 4207563026933415093337997)
                ·
                  refine ⟨1577836135100030660001749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4207563026933415093337997 1577836135100030660001749)
                  ·
                    refine ⟨36980534416406968593791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1577836135100030660001749 36980534416406968593791)
                    ·
                      rfl

theorem cell23_216058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 3, 7].length) (baseStart_216058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_216058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_216058 prefixEnd_216058 := by exact prefixLift 216058
  have htrace : WordTrace (prefixWord ++ tailWord_216058) baseStart_216058 baseEnd_216058 := by
    simpa [prefixWord, tailWord_216058, baseEnd_216058] using wordTrace_append hprefix tailTrace_216058
  have hstable : (prefixWord ++ tailWord_216058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216058).length < 2 ^ (prefixWord ++ tailWord_216058).sum := by decide
  have hdescent : baseEnd_216058 < baseStart_216058 := by decide
  rcases family_descends (prefixWord ++ tailWord_216058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216075 : List Nat := [1, 1, 1, 1, 6, 2, 1, 3, 2, 5]
def baseStart_216075 : Nat := 118140960795 + 216075 * 2 ^ 59
def prefixEnd_216075 : Nat := 4983230072969 + 3 ^ 40 * 216075 * 2
def baseEnd_216075 : Nat := 36983444140115779756265

theorem tailTrace_216075 : CollatzResearch.WordTrace tailWord_216075 prefixEnd_216075 36983444140115779756265 := by
  unfold tailWord_216075
  simp only [CollatzResearch.WordTrace]
  refine ⟨7880902692204652517137679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5253935128136435011425119 7880902692204652517137679)
  ·
    refine ⟨11821354038306978775706519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7880902692204652517137679 11821354038306978775706519)
    ·
      refine ⟨17732031057460468163559779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11821354038306978775706519 17732031057460468163559779)
      ·
        refine ⟨26598046586190702245339669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17732031057460468163559779 26598046586190702245339669)
        ·
          refine ⟨1246783433727689167750297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 26598046586190702245339669 1246783433727689167750297)
          ·
            refine ⟨935087575295766875812723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1246783433727689167750297 935087575295766875812723)
            ·
              refine ⟨1402631362943650313719085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 935087575295766875812723 1402631362943650313719085)
              ·
                refine ⟨525986761103868867644657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1402631362943650313719085 525986761103868867644657)
                ·
                  refine ⟨394490070827901650733493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 525986761103868867644657 394490070827901650733493)
                  ·
                    refine ⟨36983444140115779756265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 394490070827901650733493 36983444140115779756265)
                    ·
                      rfl

theorem cell23_216075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 3, 2, 5].length) (baseStart_216075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_216075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_216075 prefixEnd_216075 := by exact prefixLift 216075
  have htrace : WordTrace (prefixWord ++ tailWord_216075) baseStart_216075 baseEnd_216075 := by
    simpa [prefixWord, tailWord_216075, baseEnd_216075] using wordTrace_append hprefix tailTrace_216075
  have hstable : (prefixWord ++ tailWord_216075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216075).length < 2 ^ (prefixWord ++ tailWord_216075).sum := by decide
  have hdescent : baseEnd_216075 < baseStart_216075 := by decide
  rcases family_descends (prefixWord ++ tailWord_216075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216085 : List Nat := [1, 3, 2, 1, 4, 1, 1, 2, 1, 2, 5]
def baseStart_216085 : Nat := 118140960795 + 216085 * 2 ^ 59
def prefixEnd_216085 : Nat := 4983230072969 + 3 ^ 40 * 216085 * 2
def baseEnd_216085 : Nat := 110955467226892300143749

theorem tailTrace_216085 : CollatzResearch.WordTrace tailWord_216085 prefixEnd_216085 110955467226892300143749 := by
  unfold tailWord_216085
  simp only [CollatzResearch.WordTrace]
  refine ⟨7881267422168424225001709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5254178281445616150001139 7881267422168424225001709)
  ·
    refine ⟨2955475283313159084375641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7881267422168424225001709 2955475283313159084375641)
    ·
      refine ⟨2216606462484869313281731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2955475283313159084375641 2216606462484869313281731)
      ·
        refine ⟨3324909693727303969922597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2216606462484869313281731 3324909693727303969922597)
        ·
          refine ⟨623420567573869494360487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3324909693727303969922597 623420567573869494360487)
          ·
            refine ⟨935130851360804241540731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 623420567573869494360487 935130851360804241540731)
            ·
              refine ⟨1402696277041206362311097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 935130851360804241540731 1402696277041206362311097)
              ·
                refine ⟨1052022207780904771733323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1402696277041206362311097 1052022207780904771733323)
                ·
                  refine ⟨1578033311671357157599985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1052022207780904771733323 1578033311671357157599985)
                  ·
                    refine ⟨1183524983753517868199989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1578033311671357157599985 1183524983753517868199989)
                    ·
                      refine ⟨110955467226892300143749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1183524983753517868199989 110955467226892300143749)
                      ·
                        rfl

theorem cell23_216085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 2, 1, 2, 5].length) (baseStart_216085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_216085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_216085 prefixEnd_216085 := by exact prefixLift 216085
  have htrace : WordTrace (prefixWord ++ tailWord_216085) baseStart_216085 baseEnd_216085 := by
    simpa [prefixWord, tailWord_216085, baseEnd_216085] using wordTrace_append hprefix tailTrace_216085
  have hstable : (prefixWord ++ tailWord_216085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216085).length < 2 ^ (prefixWord ++ tailWord_216085).sum := by decide
  have hdescent : baseEnd_216085 < baseStart_216085 := by decide
  rcases family_descends (prefixWord ++ tailWord_216085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216112 : List Nat := [2, 1, 1, 1, 2, 4, 3, 1, 2, 4, 2]
def baseStart_216112 : Nat := 118140960795 + 216112 * 2 ^ 59
def prefixEnd_216112 : Nat := 4983230072969 + 3 ^ 40 * 216112 * 2
def baseEnd_216112 : Nat := 110969331204563694506125

theorem tailTrace_216112 : CollatzResearch.WordTrace tailWord_216112 prefixEnd_216112 110969331204563694506125 := by
  unfold tailWord_216112
  simp only [CollatzResearch.WordTrace]
  refine ⟨3941126096535303918117295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5254834795380405224156393 3941126096535303918117295)
  ·
    refine ⟨5911689144802955877175943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3941126096535303918117295 5911689144802955877175943)
    ·
      refine ⟨8867533717204433815763915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5911689144802955877175943 8867533717204433815763915)
      ·
        refine ⟨13301300575806650723645873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8867533717204433815763915 13301300575806650723645873)
        ·
          refine ⟨9975975431854988042734405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13301300575806650723645873 9975975431854988042734405)
          ·
            refine ⟨1870495393472810258012701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9975975431854988042734405 1870495393472810258012701)
            ·
              refine ⟨701435772552303846754763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1870495393472810258012701 701435772552303846754763)
              ·
                refine ⟨1052153658828455770132145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 701435772552303846754763 1052153658828455770132145)
                ·
                  refine ⟨789115244121341827599109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1052153658828455770132145 789115244121341827599109)
                  ·
                    refine ⟨147959108272751592674833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 789115244121341827599109 147959108272751592674833)
                    ·
                      refine ⟨110969331204563694506125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 147959108272751592674833 110969331204563694506125)
                      ·
                        rfl

theorem cell23_216112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 1, 2, 4, 2].length) (baseStart_216112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_216112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_216112 prefixEnd_216112 := by exact prefixLift 216112
  have htrace : WordTrace (prefixWord ++ tailWord_216112) baseStart_216112 baseEnd_216112 := by
    simpa [prefixWord, tailWord_216112, baseEnd_216112] using wordTrace_append hprefix tailTrace_216112
  have hstable : (prefixWord ++ tailWord_216112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216112).length < 2 ^ (prefixWord ++ tailWord_216112).sum := by decide
  have hdescent : baseEnd_216112 < baseStart_216112 := by decide
  rcases family_descends (prefixWord ++ tailWord_216112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216115 : List Nat := [1, 1, 1, 2, 4, 1, 1, 4, 1, 4, 3]
def baseStart_216115 : Nat := 118140960795 + 216115 * 2 ^ 59
def prefixEnd_216115 : Nat := 4983230072969 + 3 ^ 40 * 216115 * 2
def baseEnd_216115 : Nat := 110970871646527182768611

theorem tailTrace_216115 : CollatzResearch.WordTrace tailWord_216115 prefixEnd_216115 110970871646527182768611 := by
  unfold tailWord_216115
  simp only [CollatzResearch.WordTrace]
  refine ⟨7882361612059739348593799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5254907741373159565729199 7882361612059739348593799)
  ·
    refine ⟨11823542418089609022890699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7882361612059739348593799 11823542418089609022890699)
    ·
      refine ⟨17735313627134413534336049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11823542418089609022890699 17735313627134413534336049)
      ·
        refine ⟨13301485220350810150752037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17735313627134413534336049 13301485220350810150752037)
        ·
          refine ⟨2494028478815776903266007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13301485220350810150752037 2494028478815776903266007)
          ·
            refine ⟨3741042718223665354899011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2494028478815776903266007 3741042718223665354899011)
            ·
              refine ⟨5611564077335498032348517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3741042718223665354899011 5611564077335498032348517)
              ·
                refine ⟨1052168264500405881065347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5611564077335498032348517 1052168264500405881065347)
                ·
                  refine ⟨1578252396750608821598021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1052168264500405881065347 1578252396750608821598021)
                  ·
                    refine ⟨295922324390739154049629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1578252396750608821598021 295922324390739154049629)
                    ·
                      refine ⟨110970871646527182768611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 295922324390739154049629 110970871646527182768611)
                      ·
                        rfl

theorem cell23_216115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 4, 1, 4, 3].length) (baseStart_216115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_216115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_216115 prefixEnd_216115 := by exact prefixLift 216115
  have htrace : WordTrace (prefixWord ++ tailWord_216115) baseStart_216115 baseEnd_216115 := by
    simpa [prefixWord, tailWord_216115, baseEnd_216115] using wordTrace_append hprefix tailTrace_216115
  have hstable : (prefixWord ++ tailWord_216115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216115).length < 2 ^ (prefixWord ++ tailWord_216115).sum := by decide
  have hdescent : baseEnd_216115 < baseStart_216115 := by decide
  rcases family_descends (prefixWord ++ tailWord_216115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216172 : List Nat := [2, 2, 1, 1, 3, 2, 1, 1, 3, 5, 2]
def baseStart_216172 : Nat := 118140960795 + 216172 * 2 ^ 59
def prefixEnd_216172 : Nat := 4983230072969 + 3 ^ 40 * 216172 * 2
def baseEnd_216172 : Nat := 111000140043833459755849

theorem tailTrace_216172 : CollatzResearch.WordTrace tailWord_216172 prefixEnd_216172 111000140043833459755849 := by
  unfold tailWord_216172
  simp only [CollatzResearch.WordTrace]
  refine ⟨3942220286426619041709385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5256293715235492055612513 3942220286426619041709385)
  ·
    refine ⟨2956665214819964281282039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3942220286426619041709385 2956665214819964281282039)
    ·
      refine ⟨4434997822229946421923059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2956665214819964281282039 4434997822229946421923059)
      ·
        refine ⟨6652496733344919632884589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4434997822229946421923059 6652496733344919632884589)
        ·
          refine ⟨2494686275004344862331721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6652496733344919632884589 2494686275004344862331721)
          ·
            refine ⟨1871014706253258646748791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2494686275004344862331721 1871014706253258646748791)
            ·
              refine ⟨2806522059379887970123187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1871014706253258646748791 2806522059379887970123187)
              ·
                refine ⟨4209783089069831955184781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2806522059379887970123187 4209783089069831955184781)
                ·
                  refine ⟨1578668658401186983194293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4209783089069831955184781 1578668658401186983194293)
                  ·
                    refine ⟨148000186725111279674465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1578668658401186983194293 148000186725111279674465)
                    ·
                      refine ⟨111000140043833459755849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 148000186725111279674465 111000140043833459755849)
                      ·
                        rfl

theorem cell23_216172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 5, 2].length) (baseStart_216172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_216172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_216172 prefixEnd_216172 := by exact prefixLift 216172
  have htrace : WordTrace (prefixWord ++ tailWord_216172) baseStart_216172 baseEnd_216172 := by
    simpa [prefixWord, tailWord_216172, baseEnd_216172] using wordTrace_append hprefix tailTrace_216172
  have hstable : (prefixWord ++ tailWord_216172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216172).length < 2 ^ (prefixWord ++ tailWord_216172).sum := by decide
  have hdescent : baseEnd_216172 < baseStart_216172 := by decide
  rcases family_descends (prefixWord ++ tailWord_216172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216189 : List Nat := [1, 4, 1, 1, 3, 1, 2, 3, 2, 3, 2]
def baseStart_216189 : Nat := 118140960795 + 216189 * 2 ^ 59
def prefixEnd_216189 : Nat := 4983230072969 + 3 ^ 40 * 216189 * 2
def baseEnd_216189 : Nat := 111008869214959893243271

theorem tailTrace_216189 : CollatzResearch.WordTrace tailWord_216189 prefixEnd_216189 111008869214959893243271 := by
  unfold tailWord_216189
  simp only [CollatzResearch.WordTrace]
  refine ⟨7885060613791649986787621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5256707075861099991191747 7885060613791649986787621)
  ·
    refine ⟨1478448865085934372522679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7885060613791649986787621 1478448865085934372522679)
    ·
      refine ⟨2217673297628901558784019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1478448865085934372522679 2217673297628901558784019)
      ·
        refine ⟨3326509946443352338176029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2217673297628901558784019 3326509946443352338176029)
        ·
          refine ⟨1247441229916257126816011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3326509946443352338176029 1247441229916257126816011)
          ·
            refine ⟨1871161844874385690224017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1247441229916257126816011 1871161844874385690224017)
            ·
              refine ⟨1403371383655789267668013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1871161844874385690224017 1403371383655789267668013)
              ·
                refine ⟨526264268870920975375505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1403371383655789267668013 526264268870920975375505)
                ·
                  refine ⟨394698201653190731531629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 526264268870920975375505 394698201653190731531629)
                  ·
                    refine ⟨148011825619946524324361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 394698201653190731531629 148011825619946524324361)
                    ·
                      refine ⟨111008869214959893243271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 148011825619946524324361 111008869214959893243271)
                      ·
                        rfl

theorem cell23_216189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 3, 2, 3, 2].length) (baseStart_216189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_216189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_216189 prefixEnd_216189 := by exact prefixLift 216189
  have htrace : WordTrace (prefixWord ++ tailWord_216189) baseStart_216189 baseEnd_216189 := by
    simpa [prefixWord, tailWord_216189, baseEnd_216189] using wordTrace_append hprefix tailTrace_216189
  have hstable : (prefixWord ++ tailWord_216189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216189).length < 2 ^ (prefixWord ++ tailWord_216189).sum := by decide
  have hdescent : baseEnd_216189 < baseStart_216189 := by decide
  rcases family_descends (prefixWord ++ tailWord_216189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216195 : List Nat := [1, 1, 1, 3, 3, 2, 2, 1, 3, 6]
def baseStart_216195 : Nat := 118140960795 + 216195 * 2 ^ 59
def prefixEnd_216195 : Nat := 4983230072969 + 3 ^ 40 * 216195 * 2
def baseEnd_216195 : Nat := 37003983366295623256081

theorem tailTrace_216195 : CollatzResearch.WordTrace tailWord_216195 prefixEnd_216195 37003983366295623256081 := by
  unfold tailWord_216195
  simp only [CollatzResearch.WordTrace]
  refine ⟨7885279451769913011506039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5256852967846608674337359 7885279451769913011506039)
  ·
    refine ⟨11827919177654869517259059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7885279451769913011506039 11827919177654869517259059)
    ·
      refine ⟨17741878766482304275888589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11827919177654869517259059 17741878766482304275888589)
      ·
        refine ⟨6653204537430864103458221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17741878766482304275888589 6653204537430864103458221)
        ·
          refine ⟨2494951701536574038796833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6653204537430864103458221 2494951701536574038796833)
          ·
            refine ⟨1871213776152430529097625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2494951701536574038796833 1871213776152430529097625)
            ·
              refine ⟨1403410332114322896823219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1871213776152430529097625 1403410332114322896823219)
              ·
                refine ⟨2105115498171484345234829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1403410332114322896823219 2105115498171484345234829)
                ·
                  refine ⟨789418311814306629463061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2105115498171484345234829 789418311814306629463061)
                  ·
                    refine ⟨37003983366295623256081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 789418311814306629463061 37003983366295623256081)
                    ·
                      rfl

theorem cell23_216195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 1, 3, 6].length) (baseStart_216195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_216195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_216195 prefixEnd_216195 := by exact prefixLift 216195
  have htrace : WordTrace (prefixWord ++ tailWord_216195) baseStart_216195 baseEnd_216195 := by
    simpa [prefixWord, tailWord_216195, baseEnd_216195] using wordTrace_append hprefix tailTrace_216195
  have hstable : (prefixWord ++ tailWord_216195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216195).length < 2 ^ (prefixWord ++ tailWord_216195).sum := by decide
  have hdescent : baseEnd_216195 < baseStart_216195 := by decide
  rcases family_descends (prefixWord ++ tailWord_216195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216206 : List Nat := [4, 1, 1, 3, 2, 2, 1, 2, 2, 3, 2]
def baseStart_216206 : Nat := 118140960795 + 216206 * 2 ^ 59
def prefixEnd_216206 : Nat := 4983230072969 + 3 ^ 40 * 216206 * 2
def baseEnd_216206 : Nat := 111017598386086326730693

theorem tailTrace_216206 : CollatzResearch.WordTrace tailWord_216206 prefixEnd_216206 111017598386086326730693 := by
  unfold tailWord_216206
  simp only [CollatzResearch.WordTrace]
  refine ⟨985710081841257736269559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5257120436486707926770981 985710081841257736269559)
  ·
    refine ⟨1478565122761886604404339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 985710081841257736269559 1478565122761886604404339)
    ·
      refine ⟨2217847684142829906606509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1478565122761886604404339 2217847684142829906606509)
      ·
        refine ⟨831692881553561214977441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2217847684142829906606509 831692881553561214977441)
        ·
          refine ⟨623769661165170911233081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 831692881553561214977441 623769661165170911233081)
          ·
            refine ⟨467827245873878183424811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 623769661165170911233081 467827245873878183424811)
            ·
              refine ⟨701740868810817275137217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 467827245873878183424811 701740868810817275137217)
              ·
                refine ⟨526305651608112956352913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 701740868810817275137217 526305651608112956352913)
                ·
                  refine ⟨394729238706084717264685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 526305651608112956352913 394729238706084717264685)
                  ·
                    refine ⟨148023464514781768974257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 394729238706084717264685 148023464514781768974257)
                    ·
                      refine ⟨111017598386086326730693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 148023464514781768974257 111017598386086326730693)
                      ·
                        rfl

theorem cell23_216206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 2, 2, 3, 2].length) (baseStart_216206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_216206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_216206 prefixEnd_216206 := by exact prefixLift 216206
  have htrace : WordTrace (prefixWord ++ tailWord_216206) baseStart_216206 baseEnd_216206 := by
    simpa [prefixWord, tailWord_216206, baseEnd_216206] using wordTrace_append hprefix tailTrace_216206
  have hstable : (prefixWord ++ tailWord_216206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216206).length < 2 ^ (prefixWord ++ tailWord_216206).sum := by decide
  have hdescent : baseEnd_216206 < baseStart_216206 := by decide
  rcases family_descends (prefixWord ++ tailWord_216206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216229 : List Nat := [1, 3, 1, 2, 1, 5, 1, 3, 2, 4]
def baseStart_216229 : Nat := 118140960795 + 216229 * 2 ^ 59
def prefixEnd_216229 : Nat := 4983230072969 + 3 ^ 40 * 216229 * 2
def baseEnd_216229 : Nat := 37009802813713245581029

theorem tailTrace_216229 : CollatzResearch.WordTrace tailWord_216229 prefixEnd_216229 37009802813713245581029 := by
  unfold tailWord_216229
  simp only [CollatzResearch.WordTrace]
  refine ⟨7886519533646736818243741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5257679689097824545495827 7886519533646736818243741)
  ·
    refine ⟨2957444825117526306841403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7886519533646736818243741 2957444825117526306841403)
    ·
      refine ⟨4436167237676289460262105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2957444825117526306841403 4436167237676289460262105)
      ·
        refine ⟨3327125428257217095196579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4436167237676289460262105 3327125428257217095196579)
        ·
          refine ⟨4990688142385825642794869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3327125428257217095196579 4990688142385825642794869)
          ·
            refine ⟨467877013348671154012019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4990688142385825642794869 467877013348671154012019)
            ·
              refine ⟨701815520023006731018029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 467877013348671154012019 701815520023006731018029)
              ·
                refine ⟨263180820008627524131761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 701815520023006731018029 263180820008627524131761)
                ·
                  refine ⟨197385615006470643098821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 263180820008627524131761 197385615006470643098821)
                  ·
                    refine ⟨37009802813713245581029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 197385615006470643098821 37009802813713245581029)
                    ·
                      rfl

theorem cell23_216229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 3, 2, 4].length) (baseStart_216229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_216229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_216229 prefixEnd_216229 := by exact prefixLift 216229
  have htrace : WordTrace (prefixWord ++ tailWord_216229) baseStart_216229 baseEnd_216229 := by
    simpa [prefixWord, tailWord_216229, baseEnd_216229] using wordTrace_append hprefix tailTrace_216229
  have hstable : (prefixWord ++ tailWord_216229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216229).length < 2 ^ (prefixWord ++ tailWord_216229).sum := by decide
  have hdescent : baseEnd_216229 < baseStart_216229 := by decide
  rcases family_descends (prefixWord ++ tailWord_216229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216239 : List Nat := [1, 1, 2, 1, 2, 3, 5, 2, 1, 2, 3]
def baseStart_216239 : Nat := 118140960795 + 216239 * 2 ^ 59
def prefixEnd_216239 : Nat := 4983230072969 + 3 ^ 40 * 216239 * 2
def baseEnd_216239 : Nat := 111034543247684697618041

theorem tailTrace_216239 : CollatzResearch.WordTrace tailWord_216239 prefixEnd_216239 111034543247684697618041 := by
  unfold tailWord_216239
  simp only [CollatzResearch.WordTrace]
  refine ⟨7886884263610508526107771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5257922842407005684071847 7886884263610508526107771)
  ·
    refine ⟨11830326395415762789161657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7886884263610508526107771 11830326395415762789161657)
    ·
      refine ⟨8872744796561822091871243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11830326395415762789161657 8872744796561822091871243)
      ·
        refine ⟨13309117194842733137806865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8872744796561822091871243 13309117194842733137806865)
        ·
          refine ⟨9981837896132049853355149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13309117194842733137806865 9981837896132049853355149)
          ·
            refine ⟨3743189211049518695008181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9981837896132049853355149 3743189211049518695008181)
            ·
              refine ⟨350923988535892377657017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3743189211049518695008181 350923988535892377657017)
              ·
                refine ⟨263192991401919283242763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 350923988535892377657017 263192991401919283242763)
                ·
                  refine ⟨394789487102878924864145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 263192991401919283242763 394789487102878924864145)
                  ·
                    refine ⟨296092115327159193648109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 394789487102878924864145 296092115327159193648109)
                    ·
                      refine ⟨111034543247684697618041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 296092115327159193648109 111034543247684697618041)
                      ·
                        rfl

theorem cell23_216239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5, 2, 1, 2, 3].length) (baseStart_216239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_216239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_216239 prefixEnd_216239 := by exact prefixLift 216239
  have htrace : WordTrace (prefixWord ++ tailWord_216239) baseStart_216239 baseEnd_216239 := by
    simpa [prefixWord, tailWord_216239, baseEnd_216239] using wordTrace_append hprefix tailTrace_216239
  have hstable : (prefixWord ++ tailWord_216239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216239).length < 2 ^ (prefixWord ++ tailWord_216239).sum := by decide
  have hdescent : baseEnd_216239 < baseStart_216239 := by decide
  rcases family_descends (prefixWord ++ tailWord_216239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216256 : List Nat := [2, 1, 1, 2, 7, 1, 1, 1, 1, 1, 5]
def baseStart_216256 : Nat := 118140960795 + 216256 * 2 ^ 59
def prefixEnd_216256 : Nat := 4983230072969 + 3 ^ 40 * 216256 * 2
def baseEnd_216256 : Nat := 111043272418811131105463

theorem tailTrace_216256 : CollatzResearch.WordTrace tailWord_216256 prefixEnd_216256 111043272418811131105463 := by
  unfold tailWord_216256
  simp only [CollatzResearch.WordTrace]
  refine ⟨3943752152274460214738311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5258336203032613619651081 3943752152274460214738311)
  ·
    refine ⟨5915628228411690322107467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3943752152274460214738311 5915628228411690322107467)
    ·
      refine ⟨8873442342617535483161201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5915628228411690322107467 8873442342617535483161201)
      ·
        refine ⟨6655081756963151612370901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8873442342617535483161201 6655081756963151612370901)
        ·
          refine ⟨155978478678823865914943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 6655081756963151612370901 155978478678823865914943)
          ·
            refine ⟨233967718018235798872415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155978478678823865914943 233967718018235798872415)
            ·
              refine ⟨350951577027353698308623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 233967718018235798872415 350951577027353698308623)
              ·
                refine ⟨526427365541030547462935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 350951577027353698308623 526427365541030547462935)
                ·
                  refine ⟨789641048311545821194403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 526427365541030547462935 789641048311545821194403)
                  ·
                    refine ⟨1184461572467318731791605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 789641048311545821194403 1184461572467318731791605)
                    ·
                      refine ⟨111043272418811131105463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1184461572467318731791605 111043272418811131105463)
                      ·
                        rfl

theorem cell23_216256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 1, 1, 1, 1, 5].length) (baseStart_216256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_216256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_216256 prefixEnd_216256 := by exact prefixLift 216256
  have htrace : WordTrace (prefixWord ++ tailWord_216256) baseStart_216256 baseEnd_216256 := by
    simpa [prefixWord, tailWord_216256, baseEnd_216256] using wordTrace_append hprefix tailTrace_216256
  have hstable : (prefixWord ++ tailWord_216256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216256).length < 2 ^ (prefixWord ++ tailWord_216256).sum := by decide
  have hdescent : baseEnd_216256 < baseStart_216256 := by decide
  rcases family_descends (prefixWord ++ tailWord_216256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216265 : List Nat := [1, 2, 1, 1, 2, 1, 1, 2, 3, 4, 5]
def baseStart_216265 : Nat := 118140960795 + 216265 * 2 ^ 59
def prefixEnd_216265 : Nat := 4983230072969 + 3 ^ 40 * 216265 * 2
def baseEnd_216265 : Nat := 111047893744701595892921

theorem tailTrace_216265 : CollatzResearch.WordTrace tailWord_216265 prefixEnd_216265 111047893744701595892921 := by
  unfold tailWord_216265
  simp only [CollatzResearch.WordTrace]
  refine ⟨7887832561516314966554249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5258555041010876644369499 7887832561516314966554249)
  ·
    refine ⟨5915874421137236224915687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7887832561516314966554249 5915874421137236224915687)
    ·
      refine ⟨8873811631705854337373531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5915874421137236224915687 8873811631705854337373531)
      ·
        refine ⟨13310717447558781506060297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8873811631705854337373531 13310717447558781506060297)
        ·
          refine ⟨9983038085669086129545223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13310717447558781506060297 9983038085669086129545223)
          ·
            refine ⟨14974557128503629194317835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9983038085669086129545223 14974557128503629194317835)
            ·
              refine ⟨22461835692755443791476753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14974557128503629194317835 22461835692755443791476753)
              ·
                refine ⟨16846376769566582843607565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22461835692755443791476753 16846376769566582843607565)
                ·
                  refine ⟨6317391288587468566352837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16846376769566582843607565 6317391288587468566352837)
                  ·
                    refine ⟨1184510866610150356191157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6317391288587468566352837 1184510866610150356191157)
                    ·
                      refine ⟨111047893744701595892921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1184510866610150356191157 111047893744701595892921)
                      ·
                        rfl

theorem cell23_216265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 4, 5].length) (baseStart_216265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_216265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_216265 prefixEnd_216265 := by exact prefixLift 216265
  have htrace : WordTrace (prefixWord ++ tailWord_216265) baseStart_216265 baseEnd_216265 := by
    simpa [prefixWord, tailWord_216265, baseEnd_216265] using wordTrace_append hprefix tailTrace_216265
  have hstable : (prefixWord ++ tailWord_216265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216265).length < 2 ^ (prefixWord ++ tailWord_216265).sum := by decide
  have hdescent : baseEnd_216265 < baseStart_216265 := by decide
  rcases family_descends (prefixWord ++ tailWord_216265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216270 : List Nat := [4, 1, 1, 1, 5, 1, 1, 4, 1, 2, 2]
def baseStart_216270 : Nat := 118140960795 + 216270 * 2 ^ 59
def prefixEnd_216270 : Nat := 4983230072969 + 3 ^ 40 * 216270 * 2
def baseEnd_216270 : Nat := 111050461147974076330399

theorem tailTrace_216270 : CollatzResearch.WordTrace tailWord_216270 prefixEnd_216270 111050461147974076330399 := by
  unfold tailWord_216270
  simp only [CollatzResearch.WordTrace]
  refine ⟨986001865812275102560783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5258676617665467213657509 986001865812275102560783)
  ·
    refine ⟨1479002798718412653841175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 986001865812275102560783 1479002798718412653841175)
    ·
      refine ⟨2218504198077618980761763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1479002798718412653841175 2218504198077618980761763)
      ·
        refine ⟨3327756297116428471142645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2218504198077618980761763 3327756297116428471142645)
        ·
          refine ⟨311977152854665169169623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3327756297116428471142645 311977152854665169169623)
          ·
            refine ⟨467965729281997753754435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 311977152854665169169623 467965729281997753754435)
            ·
              refine ⟨701948593922996630631653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 467965729281997753754435 701948593922996630631653)
              ·
                refine ⟨131615361360561868243435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 701948593922996630631653 131615361360561868243435)
                ·
                  refine ⟨197423042040842802365153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 131615361360561868243435 197423042040842802365153)
                  ·
                    refine ⟨148067281530632101773865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 197423042040842802365153 148067281530632101773865)
                    ·
                      refine ⟨111050461147974076330399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 148067281530632101773865 111050461147974076330399)
                      ·
                        rfl

theorem cell23_216270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 4, 1, 2, 2].length) (baseStart_216270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_216270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_216270 prefixEnd_216270 := by exact prefixLift 216270
  have htrace : WordTrace (prefixWord ++ tailWord_216270) baseStart_216270 baseEnd_216270 := by
    simpa [prefixWord, tailWord_216270, baseEnd_216270] using wordTrace_append hprefix tailTrace_216270
  have hstable : (prefixWord ++ tailWord_216270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216270).length < 2 ^ (prefixWord ++ tailWord_216270).sum := by decide
  have hdescent : baseEnd_216270 < baseStart_216270 := by decide
  rcases family_descends (prefixWord ++ tailWord_216270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216276 : List Nat := [2, 4, 1, 4, 1, 2, 1, 8]
def baseStart_216276 : Nat := 118140960795 + 216276 * 2 ^ 59
def prefixEnd_216276 : Nat := 4983230072969 + 3 ^ 40 * 216276 * 2
def baseEnd_216276 : Nat := 4113094149329668624273

theorem tailTrace_216276 : CollatzResearch.WordTrace tailWord_216276 prefixEnd_216276 4113094149329668624273 := by
  unfold tailWord_216276
  simp only [CollatzResearch.WordTrace]
  refine ⟨3944116882238231922602341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5258822509650975896803121 3944116882238231922602341)
  ·
    refine ⟨739521915419668485487939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3944116882238231922602341 739521915419668485487939)
    ·
      refine ⟨1109282873129502728231909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 739521915419668485487939 1109282873129502728231909)
      ·
        refine ⟨207990538711781761543483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1109282873129502728231909 207990538711781761543483)
        ·
          refine ⟨311985808067672642315225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207990538711781761543483 311985808067672642315225)
          ·
            refine ⟨233989356050754481736419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 311985808067672642315225 233989356050754481736419)
            ·
              refine ⟨350984034076131722604629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 233989356050754481736419 350984034076131722604629)
              ·
                refine ⟨4113094149329668624273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 350984034076131722604629 4113094149329668624273)
                ·
                  rfl

theorem cell23_216276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 1, 8].length) (baseStart_216276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_216276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_216276 prefixEnd_216276 := by exact prefixLift 216276
  have htrace : WordTrace (prefixWord ++ tailWord_216276) baseStart_216276 baseEnd_216276 := by
    simpa [prefixWord, tailWord_216276, baseEnd_216276] using wordTrace_append hprefix tailTrace_216276
  have hstable : (prefixWord ++ tailWord_216276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216276).length < 2 ^ (prefixWord ++ tailWord_216276).sum := by decide
  have hdescent : baseEnd_216276 < baseStart_216276 := by decide
  rcases family_descends (prefixWord ++ tailWord_216276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216279 : List Nat := [1, 1, 3, 2, 1, 2, 3, 2, 3, 3, 2]
def baseStart_216279 : Nat := 118140960795 + 216279 * 2 ^ 59
def prefixEnd_216279 : Nat := 4983230072969 + 3 ^ 40 * 216279 * 2
def baseEnd_216279 : Nat := 111055082473864541117857

theorem tailTrace_216279 : CollatzResearch.WordTrace tailWord_216279 prefixEnd_216279 111055082473864541117857 := by
  unfold tailWord_216279
  simp only [CollatzResearch.WordTrace]
  refine ⟨7888343183465595357563891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5258895455643730238375927 7888343183465595357563891)
  ·
    refine ⟨11832514775198393036345837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7888343183465595357563891 11832514775198393036345837)
    ·
      refine ⟨4437193040699397388629689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11832514775198393036345837 4437193040699397388629689)
      ·
        refine ⟨3327894780524548041472267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4437193040699397388629689 3327894780524548041472267)
        ·
          refine ⟨4991842170786822062208401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3327894780524548041472267 4991842170786822062208401)
          ·
            refine ⟨3743881628090116546656301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4991842170786822062208401 3743881628090116546656301)
            ·
              refine ⟨1403955610533793704996113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3743881628090116546656301 1403955610533793704996113)
              ·
                refine ⟨1052966707900345278747085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1403955610533793704996113 1052966707900345278747085)
                ·
                  refine ⟨394862515462629479530157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1052966707900345278747085 394862515462629479530157)
                  ·
                    refine ⟨148073443298486054823809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 394862515462629479530157 148073443298486054823809)
                    ·
                      refine ⟨111055082473864541117857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 148073443298486054823809 111055082473864541117857)
                      ·
                        rfl

theorem cell23_216279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 2, 3, 3, 2].length) (baseStart_216279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_216279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_216279 prefixEnd_216279 := by exact prefixLift 216279
  have htrace : WordTrace (prefixWord ++ tailWord_216279) baseStart_216279 baseEnd_216279 := by
    simpa [prefixWord, tailWord_216279, baseEnd_216279] using wordTrace_append hprefix tailTrace_216279
  have hstable : (prefixWord ++ tailWord_216279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216279).length < 2 ^ (prefixWord ++ tailWord_216279).sum := by decide
  have hdescent : baseEnd_216279 < baseStart_216279 := by decide
  rcases family_descends (prefixWord ++ tailWord_216279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216296 : List Nat := [2, 1, 4, 1, 2, 1, 2, 4, 1, 3, 2]
def baseStart_216296 : Nat := 118140960795 + 216296 * 2 ^ 59
def prefixEnd_216296 : Nat := 4983230072969 + 3 ^ 40 * 216296 * 2
def baseEnd_216296 : Nat := 111063811644990974605279

theorem tailTrace_216296 : CollatzResearch.WordTrace tailWord_216296 prefixEnd_216296 111063811644990974605279 := by
  unfold tailWord_216296
  simp only [CollatzResearch.WordTrace]
  refine ⟨3944481612202003630466371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5259308816269338173955161 3944481612202003630466371)
  ·
    refine ⟨5916722418303005445699557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3944481612202003630466371 5916722418303005445699557)
    ·
      refine ⟨1109385453431813521068667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5916722418303005445699557 1109385453431813521068667)
      ·
        refine ⟨1664078180147720281603001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1109385453431813521068667 1664078180147720281603001)
        ·
          refine ⟨1248058635110790211202251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1664078180147720281603001 1248058635110790211202251)
          ·
            refine ⟨1872087952666185316803377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1248058635110790211202251 1872087952666185316803377)
            ·
              refine ⟨1404065964499638987602533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1872087952666185316803377 1404065964499638987602533)
              ·
                refine ⟨263262368343682310175475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1404065964499638987602533 263262368343682310175475)
                ·
                  refine ⟨394893552515523465263213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 263262368343682310175475 394893552515523465263213)
                  ·
                    refine ⟨148085082193321299473705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 394893552515523465263213 148085082193321299473705)
                    ·
                      refine ⟨111063811644990974605279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 148085082193321299473705 111063811644990974605279)
                      ·
                        rfl

theorem cell23_216296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 4, 1, 3, 2].length) (baseStart_216296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_216296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_216296 prefixEnd_216296 := by exact prefixLift 216296
  have htrace : WordTrace (prefixWord ++ tailWord_216296) baseStart_216296 baseEnd_216296 := by
    simpa [prefixWord, tailWord_216296, baseEnd_216296] using wordTrace_append hprefix tailTrace_216296
  have hstable : (prefixWord ++ tailWord_216296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216296).length < 2 ^ (prefixWord ++ tailWord_216296).sum := by decide
  have hdescent : baseEnd_216296 < baseStart_216296 := by decide
  rcases family_descends (prefixWord ++ tailWord_216296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216332 : List Nat := [2, 2, 1, 2, 2, 3, 1, 3, 7]
def baseStart_216332 : Nat := 118140960795 + 216332 * 2 ^ 59
def prefixEnd_216332 : Nat := 4983230072969 + 3 ^ 40 * 216332 * 2
def baseEnd_216332 : Nat := 12342477438728092639457

theorem tailTrace_216332 : CollatzResearch.WordTrace tailWord_216332 prefixEnd_216332 12342477438728092639457 := by
  unfold tailWord_216332
  simp only [CollatzResearch.WordTrace]
  refine ⟨3945138126136792704621625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5260184168182390272828833 3945138126136792704621625)
  ·
    refine ⟨2958853594602594528466219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3945138126136792704621625 2958853594602594528466219)
    ·
      refine ⟨4438280391903891792699329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2958853594602594528466219 4438280391903891792699329)
      ·
        refine ⟨3328710293927918844524497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4438280391903891792699329 3328710293927918844524497)
        ·
          refine ⟨2496532720445939133393373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3328710293927918844524497 2496532720445939133393373)
          ·
            refine ⟨936199770167227175022515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2496532720445939133393373 936199770167227175022515)
            ·
              refine ⟨1404299655250840762533773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 936199770167227175022515 1404299655250840762533773)
              ·
                refine ⟨526612370719065285950165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1404299655250840762533773 526612370719065285950165)
                ·
                  refine ⟨12342477438728092639457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 526612370719065285950165 12342477438728092639457)
                  ·
                    rfl

theorem cell23_216332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 3, 7].length) (baseStart_216332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_216332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_216332 prefixEnd_216332 := by exact prefixLift 216332
  have htrace : WordTrace (prefixWord ++ tailWord_216332) baseStart_216332 baseEnd_216332 := by
    simpa [prefixWord, tailWord_216332, baseEnd_216332] using wordTrace_append hprefix tailTrace_216332
  have hstable : (prefixWord ++ tailWord_216332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216332).length < 2 ^ (prefixWord ++ tailWord_216332).sum := by decide
  have hdescent : baseEnd_216332 < baseStart_216332 := by decide
  rcases family_descends (prefixWord ++ tailWord_216332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216349 : List Nat := [1, 4, 2, 3, 1, 1, 2, 2, 7]
def baseStart_216349 : Nat := 118140960795 + 216349 * 2 ^ 59
def prefixEnd_216349 : Nat := 4983230072969 + 3 ^ 40 * 216349 * 2
def baseEnd_216349 : Nat := 12343447346631029693615

theorem tailTrace_216349 : CollatzResearch.WordTrace tailWord_216349 prefixEnd_216349 12343447346631029693615 := by
  unfold tailWord_216349
  simp only [CollatzResearch.WordTrace]
  refine ⟨7890896293211997312612101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5260597528807998208408067 7890896293211997312612101)
  ·
    refine ⟨1479543054977249496114769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7890896293211997312612101 1479543054977249496114769)
    ·
      refine ⟨1109657291232937122086077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1479543054977249496114769 1109657291232937122086077)
      ·
        refine ⟨416121484212351420782279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1109657291232937122086077 416121484212351420782279)
        ·
          refine ⟨624182226318527131173419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 416121484212351420782279 624182226318527131173419)
          ·
            refine ⟨936273339477790696760129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 624182226318527131173419 936273339477790696760129)
            ·
              refine ⟨702205004608343022570097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 936273339477790696760129 702205004608343022570097)
              ·
                refine ⟨526653753456257266927573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 702205004608343022570097 526653753456257266927573)
                ·
                  refine ⟨12343447346631029693615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 526653753456257266927573 12343447346631029693615)
                  ·
                    rfl

theorem cell23_216349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 2, 7].length) (baseStart_216349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_216349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_216349 prefixEnd_216349 := by exact prefixLift 216349
  have htrace : WordTrace (prefixWord ++ tailWord_216349) baseStart_216349 baseEnd_216349 := by
    simpa [prefixWord, tailWord_216349, baseEnd_216349] using wordTrace_append hprefix tailTrace_216349
  have hstable : (prefixWord ++ tailWord_216349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216349).length < 2 ^ (prefixWord ++ tailWord_216349).sum := by decide
  have hdescent : baseEnd_216349 < baseStart_216349 := by decide
  rcases family_descends (prefixWord ++ tailWord_216349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216399 : List Nat := [1, 1, 2, 1, 1, 2, 1, 2, 6, 4, 2]
def baseStart_216399 : Nat := 118140960795 + 216399 * 2 ^ 59
def prefixEnd_216399 : Nat := 4983230072969 + 3 ^ 40 * 216399 * 2
def baseEnd_216399 : Nat := 111116700152404071617305

theorem tailTrace_216399 : CollatzResearch.WordTrace tailWord_216399 prefixEnd_216399 111116700152404071617305 := by
  unfold tailWord_216399
  simp only [CollatzResearch.WordTrace]
  refine ⟨7892719943030855851932251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5261813295353903901288167 7892719943030855851932251)
  ·
    refine ⟨11839079914546283777898377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7892719943030855851932251 11839079914546283777898377)
    ·
      refine ⟨8879309935909712833423783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11839079914546283777898377 8879309935909712833423783)
      ·
        refine ⟨13318964903864569250135675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8879309935909712833423783 13318964903864569250135675)
        ·
          refine ⟨19978447355796853875203513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13318964903864569250135675 19978447355796853875203513)
          ·
            refine ⟨14983835516847640406402635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19978447355796853875203513 14983835516847640406402635)
            ·
              refine ⟨22475753275271460609603953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14983835516847640406402635 22475753275271460609603953)
              ·
                refine ⟨16856814956453595457202965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22475753275271460609603953 16856814956453595457202965)
                ·
                  refine ⟨790163201083762287056389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 16856814956453595457202965 790163201083762287056389)
                  ·
                    refine ⟨148155600203205428823073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 790163201083762287056389 148155600203205428823073)
                    ·
                      refine ⟨111116700152404071617305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 148155600203205428823073 111116700152404071617305)
                      ·
                        rfl

theorem cell23_216399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 6, 4, 2].length) (baseStart_216399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_216399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_216399 prefixEnd_216399 := by exact prefixLift 216399
  have htrace : WordTrace (prefixWord ++ tailWord_216399) baseStart_216399 baseEnd_216399 := by
    simpa [prefixWord, tailWord_216399, baseEnd_216399] using wordTrace_append hprefix tailTrace_216399
  have hstable : (prefixWord ++ tailWord_216399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216399).length < 2 ^ (prefixWord ++ tailWord_216399).sum := by decide
  have hdescent : baseEnd_216399 < baseStart_216399 := by decide
  rcases family_descends (prefixWord ++ tailWord_216399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216409 : List Nat := [1, 2, 1, 2, 2, 2, 2, 4, 3, 4]
def baseStart_216409 : Nat := 118140960795 + 216409 * 2 ^ 59
def prefixEnd_216409 : Nat := 4983230072969 + 3 ^ 40 * 216409 * 2
def baseEnd_216409 : Nat := 37040611652983010830753

theorem tailTrace_216409 : CollatzResearch.WordTrace tailWord_216409 prefixEnd_216409 37040611652983010830753 := by
  unfold tailWord_216409
  simp only [CollatzResearch.WordTrace]
  refine ⟨7893084672994627559796281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5262056448663085039864187 7893084672994627559796281)
  ·
    refine ⟨5919813504745970669847211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7893084672994627559796281 5919813504745970669847211)
    ·
      refine ⟨8879720257118956004770817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5919813504745970669847211 8879720257118956004770817)
      ·
        refine ⟨6659790192839217003578113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8879720257118956004770817 6659790192839217003578113)
        ·
          refine ⟨4994842644629412752683585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6659790192839217003578113 4994842644629412752683585)
          ·
            refine ⟨3746131983472059564512689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4994842644629412752683585 3746131983472059564512689)
            ·
              refine ⟨2809598987604044673384517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3746131983472059564512689 2809598987604044673384517)
              ·
                refine ⟨526799810175758376259597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2809598987604044673384517 526799810175758376259597)
                ·
                  refine ⟨197549928815909391097349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 526799810175758376259597 197549928815909391097349)
                  ·
                    refine ⟨37040611652983010830753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 197549928815909391097349 37040611652983010830753)
                    ·
                      rfl

theorem cell23_216409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 4, 3, 4].length) (baseStart_216409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_216409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_216409 prefixEnd_216409 := by exact prefixLift 216409
  have htrace : WordTrace (prefixWord ++ tailWord_216409) baseStart_216409 baseEnd_216409 := by
    simpa [prefixWord, tailWord_216409, baseEnd_216409] using wordTrace_append hprefix tailTrace_216409
  have hstable : (prefixWord ++ tailWord_216409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216409).length < 2 ^ (prefixWord ++ tailWord_216409).sum := by decide
  have hdescent : baseEnd_216409 < baseStart_216409 := by decide
  rcases family_descends (prefixWord ++ tailWord_216409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216416 : List Nat := [2, 1, 1, 3, 4, 2, 2, 1, 2, 1, 4]
def baseStart_216416 : Nat := 118140960795 + 216416 * 2 ^ 59
def prefixEnd_216416 : Nat := 4983230072969 + 3 ^ 40 * 216416 * 2
def baseEnd_216416 : Nat := 111125429323530505104727

theorem tailTrace_216416 : CollatzResearch.WordTrace tailWord_216416 prefixEnd_216416 111125429323530505104727 := by
  unfold tailWord_216416
  simp only [CollatzResearch.WordTrace]
  refine ⟨3946669991984633877650551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5262226655979511836867401 3946669991984633877650551)
  ·
    refine ⟨5920004987976950816475827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3946669991984633877650551 5920004987976950816475827)
    ·
      refine ⟨8880007481965426224713741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5920004987976950816475827 8880007481965426224713741)
      ·
        refine ⟨3330002805737034834267653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8880007481965426224713741 3330002805737034834267653)
        ·
          refine ⟨624375526075694031425185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3330002805737034834267653 624375526075694031425185)
          ·
            refine ⟨468281644556770523568889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 624375526075694031425185 468281644556770523568889)
            ·
              refine ⟨351211233417577892676667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 468281644556770523568889 351211233417577892676667)
              ·
                refine ⟨526816850126366839015001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 351211233417577892676667 526816850126366839015001)
                ·
                  refine ⟨395112637594775129261251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 526816850126366839015001 395112637594775129261251)
                  ·
                    refine ⟨592668956392162693891877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 395112637594775129261251 592668956392162693891877)
                    ·
                      refine ⟨111125429323530505104727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 592668956392162693891877 111125429323530505104727)
                      ·
                        rfl

theorem cell23_216416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2, 1, 2, 1, 4].length) (baseStart_216416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_216416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_216416 prefixEnd_216416 := by exact prefixLift 216416
  have htrace : WordTrace (prefixWord ++ tailWord_216416) baseStart_216416 baseEnd_216416 := by
    simpa [prefixWord, tailWord_216416, baseEnd_216416] using wordTrace_append hprefix tailTrace_216416
  have hstable : (prefixWord ++ tailWord_216416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216416).length < 2 ^ (prefixWord ++ tailWord_216416).sum := by decide
  have hdescent : baseEnd_216416 < baseStart_216416 := by decide
  rcases family_descends (prefixWord ++ tailWord_216416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216439 : List Nat := [1, 1, 3, 1, 1, 2, 6, 2, 6]
def baseStart_216439 : Nat := 118140960795 + 216439 * 2 ^ 59
def prefixEnd_216439 : Nat := 4983230072969 + 3 ^ 40 * 216439 * 2
def baseEnd_216439 : Nat := 12348582153175990568569

theorem tailTrace_216439 : CollatzResearch.WordTrace tailWord_216439 prefixEnd_216439 12348582153175990568569 := by
  unfold tailWord_216439
  simp only [CollatzResearch.WordTrace]
  refine ⟨7894178862885942683388371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5262785908590628455592247 7894178862885942683388371)
  ·
    refine ⟨11841268294328914025082557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7894178862885942683388371 11841268294328914025082557)
    ·
      refine ⟨4440475610373342759405959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11841268294328914025082557 4440475610373342759405959)
      ·
        refine ⟨6660713415560014139108939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4440475610373342759405959 6660713415560014139108939)
        ·
          refine ⟨9991070123340021208663409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6660713415560014139108939 9991070123340021208663409)
          ·
            refine ⟨7493302592505015906497557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9991070123340021208663409 7493302592505015906497557)
            ·
              refine ⟨351248559023672620617073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7493302592505015906497557 351248559023672620617073)
              ·
                refine ⟨263436419267754465462805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 351248559023672620617073 263436419267754465462805)
                ·
                  refine ⟨12348582153175990568569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 263436419267754465462805 12348582153175990568569)
                  ·
                    rfl

theorem cell23_216439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6, 2, 6].length) (baseStart_216439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_216439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_216439 prefixEnd_216439 := by exact prefixLift 216439
  have htrace : WordTrace (prefixWord ++ tailWord_216439) baseStart_216439 baseEnd_216439 := by
    simpa [prefixWord, tailWord_216439, baseEnd_216439] using wordTrace_append hprefix tailTrace_216439
  have hstable : (prefixWord ++ tailWord_216439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216439).length < 2 ^ (prefixWord ++ tailWord_216439).sum := by decide
  have hdescent : baseEnd_216439 < baseStart_216439 := by decide
  rcases family_descends (prefixWord ++ tailWord_216439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216442 : List Nat := [3, 1, 1, 1, 1, 1, 2, 3, 1, 1, 8]
def baseStart_216442 : Nat := 118140960795 + 216442 * 2 ^ 59
def prefixEnd_216442 : Nat := 4983230072969 + 3 ^ 40 * 216442 * 2
def baseEnd_216442 : Nat := 111138779820547403379607

theorem tailTrace_216442 : CollatzResearch.WordTrace tailWord_216442 prefixEnd_216442 111138779820547403379607 := by
  unfold tailWord_216442
  simp only [CollatzResearch.WordTrace]
  refine ⟨1973572070468768548936895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5262858854583382797165053 1973572070468768548936895)
  ·
    refine ⟨2960358105703152823405343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1973572070468768548936895 2960358105703152823405343)
    ·
      refine ⟨4440537158554729235108015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2960358105703152823405343 4440537158554729235108015)
      ·
        refine ⟨6660805737832093852662023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4440537158554729235108015 6660805737832093852662023)
        ·
          refine ⟨9991208606748140778993035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6660805737832093852662023 9991208606748140778993035)
          ·
            refine ⟨14986812910122211168489553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9991208606748140778993035 14986812910122211168489553)
            ·
              refine ⟨11240109682591658376367165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14986812910122211168489553 11240109682591658376367165)
              ·
                refine ⟨4215041130971871891137687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11240109682591658376367165 4215041130971871891137687)
                ·
                  refine ⟨6322561696457807836706531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4215041130971871891137687 6322561696457807836706531)
                  ·
                    refine ⟨9483842544686711755059797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6322561696457807836706531 9483842544686711755059797)
                    ·
                      refine ⟨111138779820547403379607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 9483842544686711755059797 111138779820547403379607)
                      ·
                        rfl

theorem cell23_216442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 1, 1, 8].length) (baseStart_216442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_216442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_216442 prefixEnd_216442 := by exact prefixLift 216442
  have htrace : WordTrace (prefixWord ++ tailWord_216442) baseStart_216442 baseEnd_216442 := by
    simpa [prefixWord, tailWord_216442, baseEnd_216442] using wordTrace_append hprefix tailTrace_216442
  have hstable : (prefixWord ++ tailWord_216442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216442).length < 2 ^ (prefixWord ++ tailWord_216442).sum := by decide
  have hdescent : baseEnd_216442 < baseStart_216442 := by decide
  rcases family_descends (prefixWord ++ tailWord_216442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216450 : List Nat := [3, 4, 2, 1, 1, 2, 1, 1, 2, 4, 2]
def baseStart_216450 : Nat := 118140960795 + 216450 * 2 ^ 59
def prefixEnd_216450 : Nat := 4983230072969 + 3 ^ 40 * 216450 * 2
def baseEnd_216450 : Nat := 111142887665783372079571

theorem tailTrace_216450 : CollatzResearch.WordTrace tailWord_216450 prefixEnd_216450 111142887665783372079571 := by
  unfold tailWord_216450
  simp only [CollatzResearch.WordTrace]
  refine ⟨1973645016461522890509701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5263053377230727708025869 1973645016461522890509701)
  ·
    refine ⟨370058440586535541970569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1973645016461522890509701 370058440586535541970569)
    ·
      refine ⟨277543830439901656477927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 370058440586535541970569 277543830439901656477927)
      ·
        refine ⟨416315745659852484716891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277543830439901656477927 416315745659852484716891)
        ·
          refine ⟨624473618489778727075337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 416315745659852484716891 624473618489778727075337)
          ·
            refine ⟨468355213867334045306503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 624473618489778727075337 468355213867334045306503)
            ·
              refine ⟨702532820801001067959755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 468355213867334045306503 702532820801001067959755)
              ·
                refine ⟨1053799231201501601939633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 702532820801001067959755 1053799231201501601939633)
                ·
                  refine ⟨790349423401126201454725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1053799231201501601939633 790349423401126201454725)
                  ·
                    refine ⟨148190516887711162772761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 790349423401126201454725 148190516887711162772761)
                    ·
                      refine ⟨111142887665783372079571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 148190516887711162772761 111142887665783372079571)
                      ·
                        rfl

theorem cell23_216450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 1, 2, 4, 2].length) (baseStart_216450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_216450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_216450 prefixEnd_216450 := by exact prefixLift 216450
  have htrace : WordTrace (prefixWord ++ tailWord_216450) baseStart_216450 baseEnd_216450 := by
    simpa [prefixWord, tailWord_216450, baseEnd_216450] using wordTrace_append hprefix tailTrace_216450
  have hstable : (prefixWord ++ tailWord_216450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216450).length < 2 ^ (prefixWord ++ tailWord_216450).sum := by decide
  have hdescent : baseEnd_216450 < baseStart_216450 := by decide
  rcases family_descends (prefixWord ++ tailWord_216450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216469 : List Nat := [1, 3, 2, 1, 1, 2, 4, 1, 3, 5]
def baseStart_216469 : Nat := 118140960795 + 216469 * 2 ^ 59
def prefixEnd_216469 : Nat := 4983230072969 + 3 ^ 40 * 216469 * 2
def baseEnd_216469 : Nat := 37050881266072932580661

theorem tailTrace_216469 : CollatzResearch.WordTrace tailWord_216469 prefixEnd_216469 37050881266072932580661 := by
  unfold tailWord_216469
  simp only [CollatzResearch.WordTrace]
  refine ⟨7895273052777257806980461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5263515368518171871320307 7895273052777257806980461)
  ·
    refine ⟨2960727394791471677617673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7895273052777257806980461 2960727394791471677617673)
    ·
      refine ⟨2220545546093603758213255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2960727394791471677617673 2220545546093603758213255)
      ·
        refine ⟨3330818319140405637319883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2220545546093603758213255 3330818319140405637319883)
        ·
          refine ⟨4996227478710608455979825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3330818319140405637319883 4996227478710608455979825)
          ·
            refine ⟨3747170609032956341984869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4996227478710608455979825 3747170609032956341984869)
            ·
              refine ⟨702594489193679314122163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3747170609032956341984869 702594489193679314122163)
              ·
                refine ⟨1053891733790518971183245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 702594489193679314122163 1053891733790518971183245)
                ·
                  refine ⟨395209400171444614193717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1053891733790518971183245 395209400171444614193717)
                  ·
                    refine ⟨37050881266072932580661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 395209400171444614193717 37050881266072932580661)
                    ·
                      rfl

theorem cell23_216469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 1, 3, 5].length) (baseStart_216469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_216469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_216469 prefixEnd_216469 := by exact prefixLift 216469
  have htrace : WordTrace (prefixWord ++ tailWord_216469) baseStart_216469 baseEnd_216469 := by
    simpa [prefixWord, tailWord_216469, baseEnd_216469] using wordTrace_append hprefix tailTrace_216469
  have hstable : (prefixWord ++ tailWord_216469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216469).length < 2 ^ (prefixWord ++ tailWord_216469).sum := by decide
  have hdescent : baseEnd_216469 < baseStart_216469 := by decide
  rcases family_descends (prefixWord ++ tailWord_216469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216519 : List Nat := [1, 1, 4, 1, 1, 3, 3, 1, 1, 1, 6]
def baseStart_216519 : Nat := 118140960795 + 216519 * 2 ^ 59
def prefixEnd_216519 : Nat := 4983230072969 + 3 ^ 40 * 216519 * 2
def baseEnd_216519 : Nat := 111178317830943602116753

theorem tailTrace_216519 : CollatzResearch.WordTrace tailWord_216519 prefixEnd_216519 111178317830943602116753 := by
  unfold tailWord_216519
  simp only [CollatzResearch.WordTrace]
  refine ⟨7897096702596116346300611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5264731135064077564200407 7897096702596116346300611)
  ·
    refine ⟨11845645053894174519450917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7897096702596116346300611 11845645053894174519450917)
    ·
      refine ⟨2221058447605157722397047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11845645053894174519450917 2221058447605157722397047)
      ·
        refine ⟨3331587671407736583595571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2221058447605157722397047 3331587671407736583595571)
        ·
          refine ⟨4997381507111604875393357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3331587671407736583595571 4997381507111604875393357)
          ·
            refine ⟨1874018065166851828272509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4997381507111604875393357 1874018065166851828272509)
            ·
              refine ⟨702756774437569435602191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1874018065166851828272509 702756774437569435602191)
              ·
                refine ⟨1054135161656354153403287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 702756774437569435602191 1054135161656354153403287)
                ·
                  refine ⟨1581202742484531230104931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1054135161656354153403287 1581202742484531230104931)
                  ·
                    refine ⟨2371804113726796845157397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1581202742484531230104931 2371804113726796845157397)
                    ·
                      refine ⟨111178317830943602116753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2371804113726796845157397 111178317830943602116753)
                      ·
                        rfl

theorem cell23_216519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 1, 1, 1, 6].length) (baseStart_216519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_216519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_216519 prefixEnd_216519 := by exact prefixLift 216519
  have htrace : WordTrace (prefixWord ++ tailWord_216519) baseStart_216519 baseEnd_216519 := by
    simpa [prefixWord, tailWord_216519, baseEnd_216519] using wordTrace_append hprefix tailTrace_216519
  have hstable : (prefixWord ++ tailWord_216519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216519).length < 2 ^ (prefixWord ++ tailWord_216519).sum := by decide
  have hdescent : baseEnd_216519 < baseStart_216519 := by decide
  rcases family_descends (prefixWord ++ tailWord_216519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216523 : List Nat := [1, 1, 1, 1, 3, 3, 4, 2, 3, 2, 2]
def baseStart_216523 : Nat := 118140960795 + 216523 * 2 ^ 59
def prefixEnd_216523 : Nat := 4983230072969 + 3 ^ 40 * 216523 * 2
def baseEnd_216523 : Nat := 111180371753561586466735

theorem tailTrace_216523 : CollatzResearch.WordTrace tailWord_216523 prefixEnd_216523 111180371753561586466735 := by
  unfold tailWord_216523
  simp only [CollatzResearch.WordTrace]
  refine ⟨7897242594581625029446223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5264828396387750019630815 7897242594581625029446223)
  ·
    refine ⟨11845863891872437544169335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7897242594581625029446223 11845863891872437544169335)
    ·
      refine ⟨17768795837808656316254003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11845863891872437544169335 17768795837808656316254003)
      ·
        refine ⟨26653193756712984474381005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17768795837808656316254003 26653193756712984474381005)
        ·
          refine ⟨9994947658767369177892877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26653193756712984474381005 9994947658767369177892877)
          ·
            refine ⟨3748105372037763441709829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9994947658767369177892877 3748105372037763441709829)
            ·
              refine ⟨702769757257080645320593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3748105372037763441709829 702769757257080645320593)
              ·
                refine ⟨527077317942810483990445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 702769757257080645320593 527077317942810483990445)
                ·
                  refine ⟨197653994228553931496417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 527077317942810483990445 197653994228553931496417)
                  ·
                    refine ⟨148240495671415448622313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 197653994228553931496417 148240495671415448622313)
                    ·
                      refine ⟨111180371753561586466735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 148240495671415448622313 111180371753561586466735)
                      ·
                        rfl

theorem cell23_216523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 2, 3, 2, 2].length) (baseStart_216523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_216523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_216523 prefixEnd_216523 := by exact prefixLift 216523
  have htrace : WordTrace (prefixWord ++ tailWord_216523) baseStart_216523 baseEnd_216523 := by
    simpa [prefixWord, tailWord_216523, baseEnd_216523] using wordTrace_append hprefix tailTrace_216523
  have hstable : (prefixWord ++ tailWord_216523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216523).length < 2 ^ (prefixWord ++ tailWord_216523).sum := by decide
  have hdescent : baseEnd_216523 < baseStart_216523 := by decide
  rcases family_descends (prefixWord ++ tailWord_216523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216526 : List Nat := [4, 1, 1, 1, 2, 1, 2, 3, 3, 2, 3]
def baseStart_216526 : Nat := 118140960795 + 216526 * 2 ^ 59
def prefixEnd_216526 : Nat := 4983230072969 + 3 ^ 40 * 216526 * 2
def baseEnd_216526 : Nat := 111181912195525074729221

theorem tailTrace_216526 : CollatzResearch.WordTrace tailWord_216526 prefixEnd_216526 111181912195525074729221 := by
  unfold tailWord_216526
  simp only [CollatzResearch.WordTrace]
  refine ⟨987169001696344567725679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5264901342380504361203621 987169001696344567725679)
  ·
    refine ⟨1480753502544516851588519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 987169001696344567725679 1480753502544516851588519)
    ·
      refine ⟨2221130253816775277382779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1480753502544516851588519 2221130253816775277382779)
      ·
        refine ⟨3331695380725162916074169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2221130253816775277382779 3331695380725162916074169)
        ·
          refine ⟨2498771535543872187055627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3331695380725162916074169 2498771535543872187055627)
          ·
            refine ⟨3748157303315808280583441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2498771535543872187055627 3748157303315808280583441)
            ·
              refine ⟨2811117977486856210437581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3748157303315808280583441 2811117977486856210437581)
              ·
                refine ⟨1054169241557571078914093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2811117977486856210437581 1054169241557571078914093)
                ·
                  refine ⟨395313465584089154592785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1054169241557571078914093 395313465584089154592785)
                  ·
                    refine ⟨296485099188066865944589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 395313465584089154592785 296485099188066865944589)
                    ·
                      refine ⟨111181912195525074729221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 296485099188066865944589 111181912195525074729221)
                      ·
                        rfl

theorem cell23_216526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 3, 3, 2, 3].length) (baseStart_216526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_216526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_216526 prefixEnd_216526 := by exact prefixLift 216526
  have htrace : WordTrace (prefixWord ++ tailWord_216526) baseStart_216526 baseEnd_216526 := by
    simpa [prefixWord, tailWord_216526, baseEnd_216526] using wordTrace_append hprefix tailTrace_216526
  have hstable : (prefixWord ++ tailWord_216526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216526).length < 2 ^ (prefixWord ++ tailWord_216526).sum := by decide
  have hdescent : baseEnd_216526 < baseStart_216526 := by decide
  rcases family_descends (prefixWord ++ tailWord_216526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216534 : List Nat := [5, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3]
def baseStart_216534 : Nat := 118140960795 + 216534 * 2 ^ 59
def prefixEnd_216534 : Nat := 4983230072969 + 3 ^ 40 * 216534 * 2
def baseEnd_216534 : Nat := 111186020040761043429185

theorem tailTrace_216534 : CollatzResearch.WordTrace tailWord_216534 prefixEnd_216534 111186020040761043429185 := by
  unfold tailWord_216534
  simp only [CollatzResearch.WordTrace]
  refine ⟨493602737346360869256041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5265095865027849272064437 493602737346360869256041)
  ·
    refine ⟨370202053009770651942031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 493602737346360869256041 370202053009770651942031)
    ·
      refine ⟨555303079514655977913047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 370202053009770651942031 555303079514655977913047)
      ·
        refine ⟨832954619271983966869571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 555303079514655977913047 832954619271983966869571)
        ·
          refine ⟨1249431928907975950304357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 832954619271983966869571 1249431928907975950304357)
          ·
            refine ⟨234268486670245490682067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1249431928907975950304357 234268486670245490682067)
            ·
              refine ⟨351402730005368236023101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 234268486670245490682067 351402730005368236023101)
              ·
                refine ⟨131776023752013088508663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 351402730005368236023101 131776023752013088508663)
                ·
                  refine ⟨197664035628019632762995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 131776023752013088508663 197664035628019632762995)
                  ·
                    refine ⟨296496053442029449144493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 197664035628019632762995 296496053442029449144493)
                    ·
                      refine ⟨111186020040761043429185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 296496053442029449144493 111186020040761043429185)
                      ·
                        rfl

theorem cell23_216534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3].length) (baseStart_216534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_216534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_216534 prefixEnd_216534 := by exact prefixLift 216534
  have htrace : WordTrace (prefixWord ++ tailWord_216534) baseStart_216534 baseEnd_216534 := by
    simpa [prefixWord, tailWord_216534, baseEnd_216534] using wordTrace_append hprefix tailTrace_216534
  have hstable : (prefixWord ++ tailWord_216534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216534).length < 2 ^ (prefixWord ++ tailWord_216534).sum := by decide
  have hdescent : baseEnd_216534 < baseStart_216534 := by decide
  rcases family_descends (prefixWord ++ tailWord_216534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216574 : List Nat := [4, 2, 2, 3, 2, 1, 1, 2, 1, 1, 4]
def baseStart_216574 : Nat := 118140960795 + 216574 * 2 ^ 59
def prefixEnd_216574 : Nat := 4983230072969 + 3 ^ 40 * 216574 * 2
def baseEnd_216574 : Nat := 111206559266940886929001

theorem tailTrace_216574 : CollatzResearch.WordTrace tailWord_216574 prefixEnd_216574 111206559266940886929001 := by
  unfold tailWord_216574
  simp only [CollatzResearch.WordTrace]
  refine ⟨987387839674607592444097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5266068478264573826368517 987387839674607592444097)
  ·
    refine ⟨740540879755955694333073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 987387839674607592444097 740540879755955694333073)
    ·
      refine ⟨555405659816966770749805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 740540879755955694333073 555405659816966770749805)
      ·
        refine ⟨208277122431362539031177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 555405659816966770749805 208277122431362539031177)
        ·
          refine ⟨156207841823521904273383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208277122431362539031177 156207841823521904273383)
          ·
            refine ⟨234311762735282856410075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156207841823521904273383 234311762735282856410075)
            ·
              refine ⟨351467644102924284615113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 234311762735282856410075 351467644102924284615113)
              ·
                refine ⟨263600733077193213461335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 351467644102924284615113 263600733077193213461335)
                ·
                  refine ⟨395401099615789820192003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 263600733077193213461335 395401099615789820192003)
                  ·
                    refine ⟨593101649423684730288005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 395401099615789820192003 593101649423684730288005)
                    ·
                      refine ⟨111206559266940886929001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 593101649423684730288005 111206559266940886929001)
                      ·
                        rfl

theorem cell23_216574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_216574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_216574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_216574 prefixEnd_216574 := by exact prefixLift 216574
  have htrace : WordTrace (prefixWord ++ tailWord_216574) baseStart_216574 baseEnd_216574 := by
    simpa [prefixWord, tailWord_216574, baseEnd_216574] using wordTrace_append hprefix tailTrace_216574
  have hstable : (prefixWord ++ tailWord_216574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216574).length < 2 ^ (prefixWord ++ tailWord_216574).sum := by decide
  have hdescent : baseEnd_216574 < baseStart_216574 := by decide
  rcases family_descends (prefixWord ++ tailWord_216574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216577 : List Nat := [1, 2, 4, 1, 5, 1, 1, 2, 1, 2, 3]
def baseStart_216577 : Nat := 118140960795 + 216577 * 2 ^ 59
def prefixEnd_216577 : Nat := 4983230072969 + 3 ^ 40 * 216577 * 2
def baseEnd_216577 : Nat := 111208099708904375191487

theorem tailTrace_216577 : CollatzResearch.WordTrace tailWord_216577 prefixEnd_216577 111208099708904375191487 := by
  unfold tailWord_216577
  simp only [CollatzResearch.WordTrace]
  refine ⟨7899212136385992251911985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5266141424257328167941323 7899212136385992251911985)
  ·
    refine ⟨5924409102289494188933989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7899212136385992251911985 5924409102289494188933989)
    ·
      refine ⟨1110826706679280160425123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5924409102289494188933989 1110826706679280160425123)
      ·
        refine ⟨1666240060018920240637685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1110826706679280160425123 1666240060018920240637685)
        ·
          refine ⟨156210005626773772559783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1666240060018920240637685 156210005626773772559783)
          ·
            refine ⟨234315008440160658839675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156210005626773772559783 234315008440160658839675)
            ·
              refine ⟨351472512660240988259513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 234315008440160658839675 351472512660240988259513)
              ·
                refine ⟨263604384495180741194635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 351472512660240988259513 263604384495180741194635)
                ·
                  refine ⟨395406576742771111791953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 263604384495180741194635 395406576742771111791953)
                  ·
                    refine ⟨296554932557078333843965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 395406576742771111791953 296554932557078333843965)
                    ·
                      refine ⟨111208099708904375191487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 296554932557078333843965 111208099708904375191487)
                      ·
                        rfl

theorem cell23_216577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 1, 2, 1, 2, 3].length) (baseStart_216577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_216577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_216577 prefixEnd_216577 := by exact prefixLift 216577
  have htrace : WordTrace (prefixWord ++ tailWord_216577) baseStart_216577 baseEnd_216577 := by
    simpa [prefixWord, tailWord_216577, baseEnd_216577] using wordTrace_append hprefix tailTrace_216577
  have hstable : (prefixWord ++ tailWord_216577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216577).length < 2 ^ (prefixWord ++ tailWord_216577).sum := by decide
  have hdescent : baseEnd_216577 < baseStart_216577 := by decide
  rcases family_descends (prefixWord ++ tailWord_216577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216579 : List Nat := [1, 1, 1, 3, 2, 1, 2, 1, 4, 3, 4]
def baseStart_216579 : Nat := 118140960795 + 216579 * 2 ^ 59
def prefixEnd_216579 : Nat := 4983230072969 + 3 ^ 40 * 216579 * 2
def baseEnd_216579 : Nat := 111209126670213367366477

theorem tailTrace_216579 : CollatzResearch.WordTrace tailWord_216579 prefixEnd_216579 111209126670213367366477 := by
  unfold tailWord_216579
  simp only [CollatzResearch.WordTrace]
  refine ⟨7899285082378746593484791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5266190054919164395656527 7899285082378746593484791)
  ·
    refine ⟨11848927623568119890227187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7899285082378746593484791 11848927623568119890227187)
    ·
      refine ⟨17773391435352179835340781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11848927623568119890227187 17773391435352179835340781)
      ·
        refine ⟨6665021788257067438252793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17773391435352179835340781 6665021788257067438252793)
        ·
          refine ⟨4998766341192800578689595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6665021788257067438252793 4998766341192800578689595)
          ·
            refine ⟨7498149511789200868034393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4998766341192800578689595 7498149511789200868034393)
            ·
              refine ⟨5623612133841900651025795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7498149511789200868034393 5623612133841900651025795)
              ·
                refine ⟨8435418200762850976538693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5623612133841900651025795 8435418200762850976538693)
                ·
                  refine ⟨1581640912643034558101005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8435418200762850976538693 1581640912643034558101005)
                  ·
                    refine ⟨593115342241137959287877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1581640912643034558101005 593115342241137959287877)
                    ·
                      refine ⟨111209126670213367366477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 593115342241137959287877 111209126670213367366477)
                      ·
                        rfl

theorem cell23_216579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 4, 3, 4].length) (baseStart_216579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_216579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_216579 prefixEnd_216579 := by exact prefixLift 216579
  have htrace : WordTrace (prefixWord ++ tailWord_216579) baseStart_216579 baseEnd_216579 := by
    simpa [prefixWord, tailWord_216579, baseEnd_216579] using wordTrace_append hprefix tailTrace_216579
  have hstable : (prefixWord ++ tailWord_216579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216579).length < 2 ^ (prefixWord ++ tailWord_216579).sum := by decide
  have hdescent : baseEnd_216579 < baseStart_216579 := by decide
  rcases family_descends (prefixWord ++ tailWord_216579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216659 : List Nat := [1, 1, 1, 2, 1, 1, 2, 1, 5, 1, 7]
def baseStart_216659 : Nat := 118140960795 + 216659 * 2 ^ 59
def prefixEnd_216659 : Nat := 4983230072969 + 3 ^ 40 * 216659 * 2
def baseEnd_216659 : Nat := 111250205122573054366109

theorem tailTrace_216659 : CollatzResearch.WordTrace tailWord_216659 prefixEnd_216659 111250205122573054366109 := by
  unfold tailWord_216659
  simp only [CollatzResearch.WordTrace]
  refine ⟨7902202922088920256397031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5268135281392613504264687 7902202922088920256397031)
  ·
    refine ⟨11853304383133380384595547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7902202922088920256397031 11853304383133380384595547)
    ·
      refine ⟨17779956574700070576893321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11853304383133380384595547 17779956574700070576893321)
      ·
        refine ⟨13334967431025052932669991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17779956574700070576893321 13334967431025052932669991)
        ·
          refine ⟨20002451146537579399004987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13334967431025052932669991 20002451146537579399004987)
          ·
            refine ⟨30003676719806369098507481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20002451146537579399004987 30003676719806369098507481)
            ·
              refine ⟨22502757539854776823880611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30003676719806369098507481 22502757539854776823880611)
              ·
                refine ⟨33754136309782165235820917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22502757539854776823880611 33754136309782165235820917)
                ·
                  refine ⟨3164450279042077990858211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33754136309782165235820917 3164450279042077990858211)
                  ·
                    refine ⟨4746675418563116986287317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3164450279042077990858211 4746675418563116986287317)
                    ·
                      refine ⟨111250205122573054366109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 4746675418563116986287317 111250205122573054366109)
                      ·
                        rfl

theorem cell23_216659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 5, 1, 7].length) (baseStart_216659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_216659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_216659 prefixEnd_216659 := by exact prefixLift 216659
  have htrace : WordTrace (prefixWord ++ tailWord_216659) baseStart_216659 baseEnd_216659 := by
    simpa [prefixWord, tailWord_216659, baseEnd_216659] using wordTrace_append hprefix tailTrace_216659
  have hstable : (prefixWord ++ tailWord_216659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216659).length < 2 ^ (prefixWord ++ tailWord_216659).sum := by decide
  have hdescent : baseEnd_216659 < baseStart_216659 := by decide
  rcases family_descends (prefixWord ++ tailWord_216659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216666 : List Nat := [3, 1, 1, 2, 1, 1, 1, 6, 2, 5]
def baseStart_216666 : Nat := 118140960795 + 216666 * 2 ^ 59
def prefixEnd_216666 : Nat := 4983230072969 + 3 ^ 40 * 216666 * 2
def baseEnd_216666 : Nat := 37084599829051508992859

theorem tailTrace_216666 : CollatzResearch.WordTrace tailWord_216666 prefixEnd_216666 37084599829051508992859 := by
  unfold tailWord_216666
  simp only [CollatzResearch.WordTrace]
  refine ⟨1975614558265890112975463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5268305488709040301267901 1975614558265890112975463)
  ·
    refine ⟨2963421837398835169463195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1975614558265890112975463 2963421837398835169463195)
    ·
      refine ⟨4445132756098252754194793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2963421837398835169463195 4445132756098252754194793)
      ·
        refine ⟨3333849567073689565646095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4445132756098252754194793 3333849567073689565646095)
        ·
          refine ⟨5000774350610534348469143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3333849567073689565646095 5000774350610534348469143)
          ·
            refine ⟨7501161525915801522703715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5000774350610534348469143 7501161525915801522703715)
            ·
              refine ⟨11251742288873702284055573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7501161525915801522703715 11251742288873702284055573)
              ·
                refine ⟨527425419790954794565105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11251742288873702284055573 527425419790954794565105)
                ·
                  refine ⟨395569064843216095923829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 527425419790954794565105 395569064843216095923829)
                  ·
                    refine ⟨37084599829051508992859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 395569064843216095923829 37084599829051508992859)
                    ·
                      rfl

theorem cell23_216666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 6, 2, 5].length) (baseStart_216666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_216666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_216666 prefixEnd_216666 := by exact prefixLift 216666
  have htrace : WordTrace (prefixWord ++ tailWord_216666) baseStart_216666 baseEnd_216666 := by
    simpa [prefixWord, tailWord_216666, baseEnd_216666] using wordTrace_append hprefix tailTrace_216666
  have hstable : (prefixWord ++ tailWord_216666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216666).length < 2 ^ (prefixWord ++ tailWord_216666).sum := by decide
  have hdescent : baseEnd_216666 < baseStart_216666 := by decide
  rcases family_descends (prefixWord ++ tailWord_216666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216757 : List Nat := [1, 3, 3, 3, 2, 1, 2, 1, 2, 2, 3]
def baseStart_216757 : Nat := 118140960795 + 216757 * 2 ^ 59
def prefixEnd_216757 : Nat := 4983230072969 + 3 ^ 40 * 216757 * 2
def baseEnd_216757 : Nat := 111300526226713670940659

theorem tailTrace_216757 : CollatzResearch.WordTrace tailWord_216757 prefixEnd_216757 111300526226713670940659 := by
  unfold tailWord_216757
  simp only [CollatzResearch.WordTrace]
  refine ⟨7905777275733882993464525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5270518183822588662309683 7905777275733882993464525)
  ·
    refine ⟨2964666478400206122549197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7905777275733882993464525 2964666478400206122549197)
    ·
      refine ⟨1111749929400077295955949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2964666478400206122549197 1111749929400077295955949)
      ·
        refine ⟨416906223525028985983481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1111749929400077295955949 416906223525028985983481)
        ·
          refine ⟨312679667643771739487611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 416906223525028985983481 312679667643771739487611)
          ·
            refine ⟨469019501465657609231417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 312679667643771739487611 469019501465657609231417)
            ·
              refine ⟨351764626099243206923563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 469019501465657609231417 351764626099243206923563)
              ·
                refine ⟨527646939148864810385345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 351764626099243206923563 527646939148864810385345)
                ·
                  refine ⟨395735204361648607789009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 527646939148864810385345 395735204361648607789009)
                  ·
                    refine ⟨296801403271236455841757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 395735204361648607789009 296801403271236455841757)
                    ·
                      refine ⟨111300526226713670940659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 296801403271236455841757 111300526226713670940659)
                      ·
                        rfl

theorem cell23_216757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_216757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_216757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_216757 prefixEnd_216757 := by exact prefixLift 216757
  have htrace : WordTrace (prefixWord ++ tailWord_216757) baseStart_216757 baseEnd_216757 := by
    simpa [prefixWord, tailWord_216757, baseEnd_216757] using wordTrace_append hprefix tailTrace_216757
  have hstable : (prefixWord ++ tailWord_216757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216757).length < 2 ^ (prefixWord ++ tailWord_216757).sum := by decide
  have hdescent : baseEnd_216757 < baseStart_216757 := by decide
  rcases family_descends (prefixWord ++ tailWord_216757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216763 : List Nat := [1, 1, 1, 1, 1, 2, 3, 5, 1, 5, 2]
def baseStart_216763 : Nat := 118140960795 + 216763 * 2 ^ 59
def prefixEnd_216763 : Nat := 4983230072969 + 3 ^ 40 * 216763 * 2
def baseEnd_216763 : Nat := 111303607110640647465631

theorem tailTrace_216763 : CollatzResearch.WordTrace tailWord_216763 prefixEnd_216763 111303607110640647465631 := by
  unfold tailWord_216763
  simp only [CollatzResearch.WordTrace]
  refine ⟨7905996113712146018182943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5270664075808097345455295 7905996113712146018182943)
  ·
    refine ⟨11858994170568219027274415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7905996113712146018182943 11858994170568219027274415)
    ·
      refine ⟨17788491255852328540911623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11858994170568219027274415 17788491255852328540911623)
      ·
        refine ⟨26682736883778492811367435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17788491255852328540911623 26682736883778492811367435)
        ·
          refine ⟨40024105325667739217051153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26682736883778492811367435 40024105325667739217051153)
          ·
            refine ⟨30018078994250804412788365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40024105325667739217051153 30018078994250804412788365)
            ·
              refine ⟨11256779622844051654795637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30018078994250804412788365 11256779622844051654795637)
              ·
                refine ⟨1055323089641629842637091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11256779622844051654795637 1055323089641629842637091)
                ·
                  refine ⟨1582984634462444763955637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1055323089641629842637091 1582984634462444763955637)
                  ·
                    refine ⟨148404809480854196620841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1582984634462444763955637 148404809480854196620841)
                    ·
                      refine ⟨111303607110640647465631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 148404809480854196620841 111303607110640647465631)
                      ·
                        rfl

theorem cell23_216763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 5, 1, 5, 2].length) (baseStart_216763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_216763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_216763 prefixEnd_216763 := by exact prefixLift 216763
  have htrace : WordTrace (prefixWord ++ tailWord_216763) baseStart_216763 baseEnd_216763 := by
    simpa [prefixWord, tailWord_216763, baseEnd_216763] using wordTrace_append hprefix tailTrace_216763
  have hstable : (prefixWord ++ tailWord_216763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216763).length < 2 ^ (prefixWord ++ tailWord_216763).sum := by decide
  have hdescent : baseEnd_216763 < baseStart_216763 := by decide
  rcases family_descends (prefixWord ++ tailWord_216763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216774 : List Nat := [6, 1, 2, 1, 1, 1, 2, 2, 2, 2, 3]
def baseStart_216774 : Nat := 118140960795 + 216774 * 2 ^ 59
def prefixEnd_216774 : Nat := 4983230072969 + 3 ^ 40 * 216774 * 2
def baseEnd_216774 : Nat := 111309255397840104428081

theorem tailTrace_216774 : CollatzResearch.WordTrace tailWord_216774 prefixEnd_216774 111309255397840104428081 := by
  unfold tailWord_216774
  simp only [CollatzResearch.WordTrace]
  refine ⟨247074916146009215526043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 5270931544448196597888917 247074916146009215526043)
  ·
    refine ⟨370612374219013823289065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247074916146009215526043 370612374219013823289065)
    ·
      refine ⟨277959280664260367466799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 370612374219013823289065 277959280664260367466799)
      ·
        refine ⟨416938920996390551200199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277959280664260367466799 416938920996390551200199)
        ·
          refine ⟨625408381494585826800299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 416938920996390551200199 625408381494585826800299)
          ·
            refine ⟨938112572241878740200449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 625408381494585826800299 938112572241878740200449)
            ·
              refine ⟨703584429181409055150337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 938112572241878740200449 703584429181409055150337)
              ·
                refine ⟨527688321886056791362753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 703584429181409055150337 527688321886056791362753)
                ·
                  refine ⟨395766241414542593522065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 527688321886056791362753 395766241414542593522065)
                  ·
                    refine ⟨296824681060906945141549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 395766241414542593522065 296824681060906945141549)
                    ·
                      refine ⟨111309255397840104428081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 296824681060906945141549 111309255397840104428081)
                      ·
                        rfl

theorem cell23_216774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_216774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_216774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_216774 prefixEnd_216774 := by exact prefixLift 216774
  have htrace : WordTrace (prefixWord ++ tailWord_216774) baseStart_216774 baseEnd_216774 := by
    simpa [prefixWord, tailWord_216774, baseEnd_216774] using wordTrace_append hprefix tailTrace_216774
  have hstable : (prefixWord ++ tailWord_216774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216774).length < 2 ^ (prefixWord ++ tailWord_216774).sum := by decide
  have hdescent : baseEnd_216774 < baseStart_216774 := by decide
  rcases family_descends (prefixWord ++ tailWord_216774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216781 : List Nat := [1, 6, 2, 1, 1, 1, 4, 2, 1, 4]
def baseStart_216781 : Nat := 118140960795 + 216781 * 2 ^ 59
def prefixEnd_216781 : Nat := 4983230072969 + 3 ^ 40 * 216781 * 2
def baseEnd_216781 : Nat := 37104283254140525680183

theorem tailTrace_216781 : CollatzResearch.WordTrace tailWord_216781 prefixEnd_216781 37104283254140525680183 := by
  unfold tailWord_216781
  simp only [CollatzResearch.WordTrace]
  refine ⟨7906652627646935092338197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5271101751764623394892131 7906652627646935092338197)
  ·
    refine ⟨370624341920950082453353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 7906652627646935092338197 370624341920950082453353)
    ·
      refine ⟨277968256440712561840015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 370624341920950082453353 277968256440712561840015)
      ·
        refine ⟨416952384661068842760023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277968256440712561840015 416952384661068842760023)
        ·
          refine ⟨625428576991603264140035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 416952384661068842760023 625428576991603264140035)
          ·
            refine ⟨938142865487404896210053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 625428576991603264140035 938142865487404896210053)
            ·
              refine ⟨175901787278888418039385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 938142865487404896210053 175901787278888418039385)
              ·
                refine ⟨131926340459166313529539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 175901787278888418039385 131926340459166313529539)
                ·
                  refine ⟨197889510688749470294309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 131926340459166313529539 197889510688749470294309)
                  ·
                    refine ⟨37104283254140525680183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 197889510688749470294309 37104283254140525680183)
                    ·
                      rfl

theorem cell23_216781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_216781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_216781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_216781 prefixEnd_216781 := by exact prefixLift 216781
  have htrace : WordTrace (prefixWord ++ tailWord_216781) baseStart_216781 baseEnd_216781 := by
    simpa [prefixWord, tailWord_216781, baseEnd_216781] using wordTrace_append hprefix tailTrace_216781
  have hstable : (prefixWord ++ tailWord_216781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216781).length < 2 ^ (prefixWord ++ tailWord_216781).sum := by decide
  have hdescent : baseEnd_216781 < baseStart_216781 := by decide
  rcases family_descends (prefixWord ++ tailWord_216781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216793 : List Nat := [1, 2, 1, 2, 3, 3, 1, 2, 3, 1, 4]
def baseStart_216793 : Nat := 118140960795 + 216793 * 2 ^ 59
def prefixEnd_216793 : Nat := 4983230072969 + 3 ^ 40 * 216793 * 2
def baseEnd_216793 : Nat := 111319011530275530090493

theorem tailTrace_216793 : CollatzResearch.WordTrace tailWord_216793 prefixEnd_216793 111319011530275530090493 := by
  unfold tailWord_216793
  simp only [CollatzResearch.WordTrace]
  refine ⟨7907090303603461141775033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5271393535735640761183355 7907090303603461141775033)
  ·
    refine ⟨5930317727702595856331275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7907090303603461141775033 5930317727702595856331275)
    ·
      refine ⟨8895476591553893784496913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5930317727702595856331275 8895476591553893784496913)
      ·
        refine ⟨6671607443665420338372685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8895476591553893784496913 6671607443665420338372685)
        ·
          refine ⟨2501852791374532626889757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6671607443665420338372685 2501852791374532626889757)
          ·
            refine ⟨938194796765449735083659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2501852791374532626889757 938194796765449735083659)
            ·
              refine ⟨1407292195148174602625489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 938194796765449735083659 1407292195148174602625489)
              ·
                refine ⟨1055469146361130951969117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1407292195148174602625489 1055469146361130951969117)
                ·
                  refine ⟨395800929885424106988419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1055469146361130951969117 395800929885424106988419)
                  ·
                    refine ⟨593701394828136160482629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 395800929885424106988419 593701394828136160482629)
                    ·
                      refine ⟨111319011530275530090493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 593701394828136160482629 111319011530275530090493)
                      ·
                        rfl

theorem cell23_216793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 2, 3, 1, 4].length) (baseStart_216793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_216793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_216793 prefixEnd_216793 := by exact prefixLift 216793
  have htrace : WordTrace (prefixWord ++ tailWord_216793) baseStart_216793 baseEnd_216793 := by
    simpa [prefixWord, tailWord_216793, baseEnd_216793] using wordTrace_append hprefix tailTrace_216793
  have hstable : (prefixWord ++ tailWord_216793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216793).length < 2 ^ (prefixWord ++ tailWord_216793).sum := by decide
  have hdescent : baseEnd_216793 < baseStart_216793 := by decide
  rcases family_descends (prefixWord ++ tailWord_216793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216823 : List Nat := [1, 1, 3, 1, 1, 1, 6, 2, 1, 2, 4]
def baseStart_216823 : Nat := 118140960795 + 216823 * 2 ^ 59
def prefixEnd_216823 : Nat := 4983230072969 + 3 ^ 40 * 216823 * 2
def baseEnd_216823 : Nat := 111334415949910412715355

theorem tailTrace_216823 : CollatzResearch.WordTrace tailWord_216823 prefixEnd_216823 111334415949910412715355 := by
  unfold tailWord_216823
  simp only [CollatzResearch.WordTrace]
  refine ⟨7908184493494776265367123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5272122995663184176911415 7908184493494776265367123)
  ·
    refine ⟨11862276740242164398050685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7908184493494776265367123 11862276740242164398050685)
    ·
      refine ⟨4448353777590811649269007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11862276740242164398050685 4448353777590811649269007)
      ·
        refine ⟨6672530666386217473903511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4448353777590811649269007 6672530666386217473903511)
        ·
          refine ⟨10008795999579326210855267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6672530666386217473903511 10008795999579326210855267)
          ·
            refine ⟨15013193999368989316282901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10008795999579326210855267 15013193999368989316282901)
            ·
              refine ⟨703743468720421374200761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15013193999368989316282901 703743468720421374200761)
              ·
                refine ⟨527807601540316030650571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 703743468720421374200761 527807601540316030650571)
                ·
                  refine ⟨791711402310474045975857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 527807601540316030650571 791711402310474045975857)
                  ·
                    refine ⟨593783551732855534481893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 791711402310474045975857 593783551732855534481893)
                    ·
                      refine ⟨111334415949910412715355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 593783551732855534481893 111334415949910412715355)
                      ·
                        rfl

theorem cell23_216823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 2, 1, 2, 4].length) (baseStart_216823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_216823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_216823 prefixEnd_216823 := by exact prefixLift 216823
  have htrace : WordTrace (prefixWord ++ tailWord_216823) baseStart_216823 baseEnd_216823 := by
    simpa [prefixWord, tailWord_216823, baseEnd_216823] using wordTrace_append hprefix tailTrace_216823
  have hstable : (prefixWord ++ tailWord_216823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216823).length < 2 ^ (prefixWord ++ tailWord_216823).sum := by decide
  have hdescent : baseEnd_216823 < baseStart_216823 := by decide
  rcases family_descends (prefixWord ++ tailWord_216823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216843 : List Nat := [1, 1, 1, 1, 5, 1, 2, 2, 3, 3, 3]
def baseStart_216843 : Nat := 118140960795 + 216843 * 2 ^ 59
def prefixEnd_216843 : Nat := 4983230072969 + 3 ^ 40 * 216843 * 2
def baseEnd_216843 : Nat := 111344685563000334465263

theorem tailTrace_216843 : CollatzResearch.WordTrace tailWord_216843 prefixEnd_216843 111344685563000334465263 := by
  unfold tailWord_216843
  simp only [CollatzResearch.WordTrace]
  refine ⟨7908913953422319681095183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5272609302281546454063455 7908913953422319681095183)
  ·
    refine ⟨11863370930133479521642775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7908913953422319681095183 11863370930133479521642775)
    ·
      refine ⟨17795056395200219282464163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11863370930133479521642775 17795056395200219282464163)
      ·
        refine ⟨26692584592800328923696245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17795056395200219282464163 26692584592800328923696245)
        ·
          refine ⟨2502429805575030836596523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26692584592800328923696245 2502429805575030836596523)
          ·
            refine ⟨3753644708362546254894785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2502429805575030836596523 3753644708362546254894785)
            ·
              refine ⟨2815233531271909691171089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3753644708362546254894785 2815233531271909691171089)
              ·
                refine ⟨2111425148453932268378317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2815233531271909691171089 2111425148453932268378317)
                ·
                  refine ⟨791784430670224600641869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2111425148453932268378317 791784430670224600641869)
                  ·
                    refine ⟨296919161501334225240701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 791784430670224600641869 296919161501334225240701)
                    ·
                      refine ⟨111344685563000334465263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 296919161501334225240701 111344685563000334465263)
                      ·
                        rfl

theorem cell23_216843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 2, 3, 3, 3].length) (baseStart_216843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_216843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_216843 prefixEnd_216843 := by exact prefixLift 216843
  have htrace : WordTrace (prefixWord ++ tailWord_216843) baseStart_216843 baseEnd_216843 := by
    simpa [prefixWord, tailWord_216843, baseEnd_216843] using wordTrace_append hprefix tailTrace_216843
  have hstable : (prefixWord ++ tailWord_216843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216843).length < 2 ^ (prefixWord ++ tailWord_216843).sum := by decide
  have hdescent : baseEnd_216843 < baseStart_216843 := by decide
  rcases family_descends (prefixWord ++ tailWord_216843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216844 : List Nat := [2, 2, 1, 2, 2, 1, 4, 4, 1, 2, 2]
def baseStart_216844 : Nat := 118140960795 + 216844 * 2 ^ 59
def prefixEnd_216844 : Nat := 4983230072969 + 3 ^ 40 * 216844 * 2
def baseEnd_216844 : Nat := 111345199043654830552759

theorem tailTrace_216844 : CollatzResearch.WordTrace tailWord_216844 prefixEnd_216844 111345199043654830552759 := by
  unfold tailWord_216844
  simp only [CollatzResearch.WordTrace]
  refine ⟨3954475213209348425940793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5272633617612464567921057 3954475213209348425940793)
  ·
    refine ⟨2965856409907011319455595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3954475213209348425940793 2965856409907011319455595)
    ·
      refine ⟨4448784614860516979183393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2965856409907011319455595 4448784614860516979183393)
      ·
        refine ⟨3336588461145387734387545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4448784614860516979183393 3336588461145387734387545)
        ·
          refine ⟨2502441345859040800790659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3336588461145387734387545 2502441345859040800790659)
          ·
            refine ⟨3753662018788561201185989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2502441345859040800790659 3753662018788561201185989)
            ·
              refine ⟨703811628522855225222373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3753662018788561201185989 703811628522855225222373)
              ·
                refine ⟨131964680348035354729195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 703811628522855225222373 131964680348035354729195)
                ·
                  refine ⟨197947020522053032093793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 131964680348035354729195 197947020522053032093793)
                  ·
                    refine ⟨148460265391539774070345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 197947020522053032093793 148460265391539774070345)
                    ·
                      refine ⟨111345199043654830552759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 148460265391539774070345 111345199043654830552759)
                      ·
                        rfl

theorem cell23_216844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 4, 1, 2, 2].length) (baseStart_216844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_216844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_216844 prefixEnd_216844 := by exact prefixLift 216844
  have htrace : WordTrace (prefixWord ++ tailWord_216844) baseStart_216844 baseEnd_216844 := by
    simpa [prefixWord, tailWord_216844, baseEnd_216844] using wordTrace_append hprefix tailTrace_216844
  have hstable : (prefixWord ++ tailWord_216844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216844).length < 2 ^ (prefixWord ++ tailWord_216844).sum := by decide
  have hdescent : baseEnd_216844 < baseStart_216844 := by decide
  rcases family_descends (prefixWord ++ tailWord_216844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216938 : List Nat := [3, 1, 3, 4, 1, 1, 3, 1, 1, 3, 2]
def baseStart_216938 : Nat := 118140960795 + 216938 * 2 ^ 59
def prefixEnd_216938 : Nat := 4983230072969 + 3 ^ 40 * 216938 * 2
def baseEnd_216938 : Nat := 111393466225177462777327

theorem tailTrace_216938 : CollatzResearch.WordTrace tailWord_216938 prefixEnd_216938 111393466225177462777327 := by
  unfold tailWord_216938
  simp only [CollatzResearch.WordTrace]
  refine ⟨1978094722019537726450867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5274919258718767270535645 1978094722019537726450867)
  ·
    refine ⟨2967142083029306589676301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1978094722019537726450867 2967142083029306589676301)
    ·
      refine ⟨1112678281135989971128613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2967142083029306589676301 1112678281135989971128613)
      ·
        refine ⟨208627177712998119586615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1112678281135989971128613 208627177712998119586615)
        ·
          refine ⟨312940766569497179379923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208627177712998119586615 312940766569497179379923)
          ·
            refine ⟨469411149854245769069885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 312940766569497179379923 469411149854245769069885)
            ·
              refine ⟨176029181195342163401207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 469411149854245769069885 176029181195342163401207)
              ·
                refine ⟨264043771793013245101811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 176029181195342163401207 264043771793013245101811)
                ·
                  refine ⟨396065657689519867652717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 264043771793013245101811 396065657689519867652717)
                  ·
                    refine ⟨148524621633569950369769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 396065657689519867652717 148524621633569950369769)
                    ·
                      refine ⟨111393466225177462777327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 148524621633569950369769 111393466225177462777327)
                      ·
                        rfl

theorem cell23_216938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_216938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_216938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_216938 prefixEnd_216938 := by exact prefixLift 216938
  have htrace : WordTrace (prefixWord ++ tailWord_216938) baseStart_216938 baseEnd_216938 := by
    simpa [prefixWord, tailWord_216938, baseEnd_216938] using wordTrace_append hprefix tailTrace_216938
  have hstable : (prefixWord ++ tailWord_216938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216938).length < 2 ^ (prefixWord ++ tailWord_216938).sum := by decide
  have hdescent : baseEnd_216938 < baseStart_216938 := by decide
  rcases family_descends (prefixWord ++ tailWord_216938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216960 : List Nat := [2, 1, 1, 2, 1, 2, 3, 1, 1, 7, 2]
def baseStart_216960 : Nat := 118140960795 + 216960 * 2 ^ 59
def prefixEnd_216960 : Nat := 4983230072969 + 3 ^ 40 * 216960 * 2
def baseEnd_216960 : Nat := 111404762799576376702225

theorem tailTrace_216960 : CollatzResearch.WordTrace tailWord_216960 prefixEnd_216960 111404762799576376702225 := by
  unfold tailWord_216960
  simp only [CollatzResearch.WordTrace]
  refine ⟨3956590646999224331552167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5275454195998965775402889 3956590646999224331552167)
  ·
    refine ⟨5934885970498836497328251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3956590646999224331552167 5934885970498836497328251)
    ·
      refine ⟨8902328955748254745992377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5934885970498836497328251 8902328955748254745992377)
      ·
        refine ⟨6676746716811191059494283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8902328955748254745992377 6676746716811191059494283)
        ·
          refine ⟨10015120075216786589241425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6676746716811191059494283 10015120075216786589241425)
          ·
            refine ⟨7511340056412589941931069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10015120075216786589241425 7511340056412589941931069)
            ·
              refine ⟨2816752521154721228224151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7511340056412589941931069 2816752521154721228224151)
              ·
                refine ⟨4225128781732081842336227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2816752521154721228224151 4225128781732081842336227)
                ·
                  refine ⟨6337693172598122763504341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4225128781732081842336227 6337693172598122763504341)
                  ·
                    refine ⟨148539683732768502269633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6337693172598122763504341 148539683732768502269633)
                    ·
                      refine ⟨111404762799576376702225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 148539683732768502269633 111404762799576376702225)
                      ·
                        rfl

theorem cell23_216960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 1, 7, 2].length) (baseStart_216960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_216960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_216960 prefixEnd_216960 := by exact prefixLift 216960
  have htrace : WordTrace (prefixWord ++ tailWord_216960) baseStart_216960 baseEnd_216960 := by
    simpa [prefixWord, tailWord_216960, baseEnd_216960] using wordTrace_append hprefix tailTrace_216960
  have hstable : (prefixWord ++ tailWord_216960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216960).length < 2 ^ (prefixWord ++ tailWord_216960).sum := by decide
  have hdescent : baseEnd_216960 < baseStart_216960 := by decide
  rcases family_descends (prefixWord ++ tailWord_216960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216967 : List Nat := [1, 1, 4, 2, 4, 1, 1, 1, 2, 3, 3]
def baseStart_216967 : Nat := 118140960795 + 216967 * 2 ^ 59
def prefixEnd_216967 : Nat := 4983230072969 + 3 ^ 40 * 216967 * 2
def baseEnd_216967 : Nat := 111408357164157849314693

theorem tailTrace_216967 : CollatzResearch.WordTrace tailWord_216967 prefixEnd_216967 111408357164157849314693 := by
  unfold tailWord_216967
  simp only [CollatzResearch.WordTrace]
  refine ⟨7913436604973088858609155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5275624403315392572406103 7913436604973088858609155)
  ·
    refine ⟨11870154907459633287913733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7913436604973088858609155 11870154907459633287913733)
    ·
      refine ⟨2225654045148681241483825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11870154907459633287913733 2225654045148681241483825)
      ·
        refine ⟨1669240533861510931112869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2225654045148681241483825 1669240533861510931112869)
        ·
          refine ⟨312982600099033299583663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1669240533861510931112869 312982600099033299583663)
          ·
            refine ⟨469473900148549949375495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 312982600099033299583663 469473900148549949375495)
            ·
              refine ⟨704210850222824924063243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 469473900148549949375495 704210850222824924063243)
              ·
                refine ⟨1056316275334237386094865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 704210850222824924063243 1056316275334237386094865)
                ·
                  refine ⟨792237206500678039571149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1056316275334237386094865 792237206500678039571149)
                  ·
                    refine ⟨297088952437754264839181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 792237206500678039571149 297088952437754264839181)
                    ·
                      refine ⟨111408357164157849314693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 297088952437754264839181 111408357164157849314693)
                      ·
                        rfl

theorem cell23_216967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 1, 2, 3, 3].length) (baseStart_216967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_216967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_216967 prefixEnd_216967 := by exact prefixLift 216967
  have htrace : WordTrace (prefixWord ++ tailWord_216967) baseStart_216967 baseEnd_216967 := by
    simpa [prefixWord, tailWord_216967, baseEnd_216967] using wordTrace_append hprefix tailTrace_216967
  have hstable : (prefixWord ++ tailWord_216967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216967).length < 2 ^ (prefixWord ++ tailWord_216967).sum := by decide
  have hdescent : baseEnd_216967 < baseStart_216967 := by decide
  rcases family_descends (prefixWord ++ tailWord_216967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217017 : List Nat := [1, 2, 1, 4, 2, 1, 4, 1, 3, 4]
def baseStart_217017 : Nat := 118140960795 + 217017 * 2 ^ 59
def prefixEnd_217017 : Nat := 4983230072969 + 3 ^ 40 * 217017 * 2
def baseEnd_217017 : Nat := 37144677065627551229821

theorem tailTrace_217017 : CollatzResearch.WordTrace tailWord_217017 prefixEnd_217017 37144677065627551229821 := by
  unfold tailWord_217017
  simp only [CollatzResearch.WordTrace]
  refine ⟨7915260254791947397929305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5276840169861298265286203 7915260254791947397929305)
  ·
    refine ⟨5936445191093960548446979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7915260254791947397929305 5936445191093960548446979)
    ·
      refine ⟨8904667786640940822670469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5936445191093960548446979 8904667786640940822670469)
      ·
        refine ⟨1669625209995176404250713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8904667786640940822670469 1669625209995176404250713)
        ·
          refine ⟨1252218907496382303188035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1669625209995176404250713 1252218907496382303188035)
          ·
            refine ⟨1878328361244573454782053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1252218907496382303188035 1878328361244573454782053)
            ·
              refine ⟨352186567733357522771635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1878328361244573454782053 352186567733357522771635)
              ·
                refine ⟨528279851600036284157453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 352186567733357522771635 528279851600036284157453)
                ·
                  refine ⟨198104944350013606559045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 528279851600036284157453 198104944350013606559045)
                  ·
                    refine ⟨37144677065627551229821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 198104944350013606559045 37144677065627551229821)
                    ·
                      rfl

theorem cell23_217017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4, 1, 3, 4].length) (baseStart_217017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_217017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_217017 prefixEnd_217017 := by exact prefixLift 217017
  have htrace : WordTrace (prefixWord ++ tailWord_217017) baseStart_217017 baseEnd_217017 := by
    simpa [prefixWord, tailWord_217017, baseEnd_217017] using wordTrace_append hprefix tailTrace_217017
  have hstable : (prefixWord ++ tailWord_217017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217017).length < 2 ^ (prefixWord ++ tailWord_217017).sum := by decide
  have hdescent : baseEnd_217017 < baseStart_217017 := by decide
  rcases family_descends (prefixWord ++ tailWord_217017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217057 : List Nat := [1, 2, 3, 1, 2, 1, 2, 2, 5, 1, 3]
def baseStart_217057 : Nat := 118140960795 + 217057 * 2 ^ 59
def prefixEnd_217057 : Nat := 4983230072969 + 3 ^ 40 * 217057 * 2
def baseEnd_217057 : Nat := 111454570423062497189279

theorem tailTrace_217057 : CollatzResearch.WordTrace tailWord_217057 prefixEnd_217057 111454570423062497189279 := by
  unfold tailWord_217057
  simp only [CollatzResearch.WordTrace]
  refine ⟨7916719174647034229385425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5277812783098022819590283 7916719174647034229385425)
  ·
    refine ⟨5937539380985275672039069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7916719174647034229385425 5937539380985275672039069)
    ·
      refine ⟨2226577267869478377014651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5937539380985275672039069 2226577267869478377014651)
      ·
        refine ⟨3339865901804217565521977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2226577267869478377014651 3339865901804217565521977)
        ·
          refine ⟨2504899426353163174141483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3339865901804217565521977 2504899426353163174141483)
          ·
            refine ⟨3757349139529744761212225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2504899426353163174141483 3757349139529744761212225)
            ·
              refine ⟨2818011854647308570909169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3757349139529744761212225 2818011854647308570909169)
              ·
                refine ⟨2113508890985481428181877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2818011854647308570909169 2113508890985481428181877)
                ·
                  refine ⟨198141458529888883892051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2113508890985481428181877 198141458529888883892051)
                  ·
                    refine ⟨297212187794833325838077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 198141458529888883892051 297212187794833325838077)
                    ·
                      refine ⟨111454570423062497189279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 297212187794833325838077 111454570423062497189279)
                      ·
                        rfl

theorem cell23_217057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 2, 5, 1, 3].length) (baseStart_217057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_217057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_217057 prefixEnd_217057 := by exact prefixLift 217057
  have htrace : WordTrace (prefixWord ++ tailWord_217057) baseStart_217057 baseEnd_217057 := by
    simpa [prefixWord, tailWord_217057, baseEnd_217057] using wordTrace_append hprefix tailTrace_217057
  have hstable : (prefixWord ++ tailWord_217057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217057).length < 2 ^ (prefixWord ++ tailWord_217057).sum := by decide
  have hdescent : baseEnd_217057 < baseStart_217057 := by decide
  rcases family_descends (prefixWord ++ tailWord_217057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217111 : List Nat := [1, 1, 3, 5, 2, 1, 3, 1, 1, 5]
def baseStart_217111 : Nat := 118140960795 + 217111 * 2 ^ 59
def prefixEnd_217111 : Nat := 4983230072969 + 3 ^ 40 * 217111 * 2
def baseEnd_217111 : Nat := 37160766126135095304677

theorem tailTrace_217111 : CollatzResearch.WordTrace tailWord_217111 prefixEnd_217111 37160766126135095304677 := by
  unfold tailWord_217111
  simp only [CollatzResearch.WordTrace]
  refine ⟨7918688716451401451851187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5279125810967600967900791 7918688716451401451851187)
  ·
    refine ⟨11878033074677102177776781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7918688716451401451851187 11878033074677102177776781)
    ·
      refine ⟨4454262403003913316666293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11878033074677102177776781 4454262403003913316666293)
      ·
        refine ⟨417587100281616873437465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4454262403003913316666293 417587100281616873437465)
        ·
          refine ⟨313190325211212655078099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 417587100281616873437465 313190325211212655078099)
          ·
            refine ⟨469785487816818982617149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 313190325211212655078099 469785487816818982617149)
            ·
              refine ⟨176169557931307118481431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 469785487816818982617149 176169557931307118481431)
              ·
                refine ⟨264254336896960677722147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 176169557931307118481431 264254336896960677722147)
                ·
                  refine ⟨396381505345441016583221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 264254336896960677722147 396381505345441016583221)
                  ·
                    refine ⟨37160766126135095304677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 396381505345441016583221 37160766126135095304677)
                    ·
                      rfl

theorem cell23_217111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 3, 1, 1, 5].length) (baseStart_217111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_217111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_217111 prefixEnd_217111 := by exact prefixLift 217111
  have htrace : WordTrace (prefixWord ++ tailWord_217111) baseStart_217111 baseEnd_217111 := by
    simpa [prefixWord, tailWord_217111, baseEnd_217111] using wordTrace_append hprefix tailTrace_217111
  have hstable : (prefixWord ++ tailWord_217111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217111).length < 2 ^ (prefixWord ++ tailWord_217111).sum := by decide
  have hdescent : baseEnd_217111 < baseStart_217111 := by decide
  rcases family_descends (prefixWord ++ tailWord_217111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217134 : List Nat := [4, 1, 3, 1, 1, 2, 1, 2, 3, 2, 3]
def baseStart_217134 : Nat := 118140960795 + 217134 * 2 ^ 59
def prefixEnd_217134 : Nat := 4983230072969 + 3 ^ 40 * 217134 * 2
def baseEnd_217134 : Nat := 111494108433458695926425

theorem tailTrace_217134 : CollatzResearch.WordTrace tailWord_217134 prefixEnd_217134 111494108433458695926425 := by
  unfold tailWord_217134
  simp only [CollatzResearch.WordTrace]
  refine ⟨989940949421009547492307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5279685063578717586625637 989940949421009547492307)
  ·
    refine ⟨1484911424131514321238461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 989940949421009547492307 1484911424131514321238461)
    ·
      refine ⟨556841784049317870464423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1484911424131514321238461 556841784049317870464423)
      ·
        refine ⟨835262676073976805696635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 556841784049317870464423 835262676073976805696635)
        ·
          refine ⟨1252894014110965208544953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 835262676073976805696635 1252894014110965208544953)
          ·
            refine ⟨939670510583223906408715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1252894014110965208544953 939670510583223906408715)
            ·
              refine ⟨1409505765874835859613073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 939670510583223906408715 1409505765874835859613073)
              ·
                refine ⟨1057129324406126894709805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1409505765874835859613073 1057129324406126894709805)
                ·
                  refine ⟨396423496652297585516177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1057129324406126894709805 396423496652297585516177)
                  ·
                    refine ⟨297317622489223189137133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 396423496652297585516177 297317622489223189137133)
                    ·
                      refine ⟨111494108433458695926425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 297317622489223189137133 111494108433458695926425)
                      ·
                        rfl

theorem cell23_217134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 2, 3, 2, 3].length) (baseStart_217134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_217134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_217134 prefixEnd_217134 := by exact prefixLift 217134
  have htrace : WordTrace (prefixWord ++ tailWord_217134) baseStart_217134 baseEnd_217134 := by
    simpa [prefixWord, tailWord_217134, baseEnd_217134] using wordTrace_append hprefix tailTrace_217134
  have hstable : (prefixWord ++ tailWord_217134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217134).length < 2 ^ (prefixWord ++ tailWord_217134).sum := by decide
  have hdescent : baseEnd_217134 < baseStart_217134 := by decide
  rcases family_descends (prefixWord ++ tailWord_217134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217137 : List Nat := [1, 2, 2, 3, 1, 5, 1, 8]
def baseStart_217137 : Nat := 118140960795 + 217137 * 2 ^ 59
def prefixEnd_217137 : Nat := 4983230072969 + 3 ^ 40 * 217137 * 2
def baseEnd_217137 : Nat := 4129468476867488303293

theorem tailTrace_217137 : CollatzResearch.WordTrace tailWord_217137 prefixEnd_217137 4129468476867488303293 := by
  unfold tailWord_217137
  simp only [CollatzResearch.WordTrace]
  refine ⟨7919637014357207892297665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5279758009571471928198443 7919637014357207892297665)
  ·
    refine ⟨5939727760767905919223249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7919637014357207892297665 5939727760767905919223249)
    ·
      refine ⟨4454795820575929439417437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5939727760767905919223249 4454795820575929439417437)
      ·
        refine ⟨1670548432715973539781539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4454795820575929439417437 1670548432715973539781539)
        ·
          refine ⟨2505822649073960309672309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1670548432715973539781539 2505822649073960309672309)
          ·
            refine ⟨234920873350683779031779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2505822649073960309672309 234920873350683779031779)
            ·
              refine ⟨352381310026025668547669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 234920873350683779031779 352381310026025668547669)
              ·
                refine ⟨4129468476867488303293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 352381310026025668547669 4129468476867488303293)
                ·
                  rfl

theorem cell23_217137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 1, 8].length) (baseStart_217137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_217137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_217137 prefixEnd_217137 := by exact prefixLift 217137
  have htrace : WordTrace (prefixWord ++ tailWord_217137) baseStart_217137 baseEnd_217137 := by
    simpa [prefixWord, tailWord_217137, baseEnd_217137] using wordTrace_append hprefix tailTrace_217137
  have hstable : (prefixWord ++ tailWord_217137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217137).length < 2 ^ (prefixWord ++ tailWord_217137).sum := by decide
  have hdescent : baseEnd_217137 < baseStart_217137 := by decide
  rcases family_descends (prefixWord ++ tailWord_217137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217144 : List Nat := [2, 1, 2, 1, 6, 1, 2, 1, 1, 2, 4]
def baseStart_217144 : Nat := 118140960795 + 217144 * 2 ^ 59
def prefixEnd_217144 : Nat := 4983230072969 + 3 ^ 40 * 217144 * 2
def baseEnd_217144 : Nat := 111499243240003656801379

theorem tailTrace_217144 : CollatzResearch.WordTrace tailWord_217144 prefixEnd_217144 111499243240003656801379 := by
  unfold tailWord_217144
  simp only [CollatzResearch.WordTrace]
  refine ⟨3959946162665924043901243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5279928216887898725201657 3959946162665924043901243)
  ·
    refine ⟨5939919243998886065851865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3959946162665924043901243 5939919243998886065851865)
    ·
      refine ⟨4454939432999164549388899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5939919243998886065851865 4454939432999164549388899)
      ·
        refine ⟨6682409149498746824083349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4454939432999164549388899 6682409149498746824083349)
        ·
          refine ⟨313237928882753757378907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 6682409149498746824083349 313237928882753757378907)
          ·
            refine ⟨469856893324130636068361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 313237928882753757378907 469856893324130636068361)
            ·
              refine ⟨352392669993097977051271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 469856893324130636068361 352392669993097977051271)
              ·
                refine ⟨528589004989646965576907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 352392669993097977051271 528589004989646965576907)
                ·
                  refine ⟨792883507484470448365361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 528589004989646965576907 792883507484470448365361)
                  ·
                    refine ⟨594662630613352836274021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 792883507484470448365361 594662630613352836274021)
                    ·
                      refine ⟨111499243240003656801379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 594662630613352836274021 111499243240003656801379)
                      ·
                        rfl

theorem cell23_217144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 2, 1, 1, 2, 4].length) (baseStart_217144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_217144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_217144 prefixEnd_217144 := by exact prefixLift 217144
  have htrace : WordTrace (prefixWord ++ tailWord_217144) baseStart_217144 baseEnd_217144 := by
    simpa [prefixWord, tailWord_217144, baseEnd_217144] using wordTrace_append hprefix tailTrace_217144
  have hstable : (prefixWord ++ tailWord_217144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217144).length < 2 ^ (prefixWord ++ tailWord_217144).sum := by decide
  have hdescent : baseEnd_217144 < baseStart_217144 := by decide
  rcases family_descends (prefixWord ++ tailWord_217144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217165 : List Nat := [1, 6, 1, 1, 1, 1, 4, 3, 1, 2, 2]
def baseStart_217165 : Nat := 118140960795 + 217165 * 2 ^ 59
def prefixEnd_217165 : Nat := 4983230072969 + 3 ^ 40 * 217165 * 2
def baseEnd_217165 : Nat := 111510026333748074638783

theorem tailTrace_217165 : CollatzResearch.WordTrace tailWord_217165 prefixEnd_217165 111510026333748074638783 := by
  unfold tailWord_217165
  simp only [CollatzResearch.WordTrace]
  refine ⟨7920658258255768674316949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5280438838837179116211299 7920658258255768674316949)
  ·
    refine ⟨371280855855739156608607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 7920658258255768674316949 371280855855739156608607)
    ·
      refine ⟨556921283783608734912911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371280855855739156608607 556921283783608734912911)
      ·
        refine ⟨835381925675413102369367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 556921283783608734912911 835381925675413102369367)
        ·
          refine ⟨1253072888513119653554051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 835381925675413102369367 1253072888513119653554051)
          ·
            refine ⟨1879609332769679480331077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1253072888513119653554051 1879609332769679480331077)
            ·
              refine ⟨352426749894314902562077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1879609332769679480331077 352426749894314902562077)
              ·
                refine ⟨132160031210368088460779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 352426749894314902562077 132160031210368088460779)
                ·
                  refine ⟨198240046815552132691169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 132160031210368088460779 198240046815552132691169)
                  ·
                    refine ⟨148680035111664099518377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 198240046815552132691169 148680035111664099518377)
                    ·
                      refine ⟨111510026333748074638783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 148680035111664099518377 111510026333748074638783)
                      ·
                        rfl

theorem cell23_217165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 4, 3, 1, 2, 2].length) (baseStart_217165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_217165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_217165 prefixEnd_217165 := by exact prefixLift 217165
  have htrace : WordTrace (prefixWord ++ tailWord_217165) baseStart_217165 baseEnd_217165 := by
    simpa [prefixWord, tailWord_217165, baseEnd_217165] using wordTrace_append hprefix tailTrace_217165
  have hstable : (prefixWord ++ tailWord_217165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217165).length < 2 ^ (prefixWord ++ tailWord_217165).sum := by decide
  have hdescent : baseEnd_217165 < baseStart_217165 := by decide
  rcases family_descends (prefixWord ++ tailWord_217165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217182 : List Nat := [4, 4, 1, 1, 2, 1, 2, 1, 3, 2, 2]
def baseStart_217182 : Nat := 118140960795 + 217182 * 2 ^ 59
def prefixEnd_217182 : Nat := 4983230072969 + 3 ^ 40 * 217182 * 2
def baseEnd_217182 : Nat := 111518755504874508126205

theorem tailTrace_217182 : CollatzResearch.WordTrace tailWord_217182 prefixEnd_217182 111518755504874508126205 := by
  unfold tailWord_217182
  simp only [CollatzResearch.WordTrace]
  refine ⟨990159787399272572210725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5280852199462787051790533 990159787399272572210725)
  ·
    refine ⟨185654960137363607289511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 990159787399272572210725 185654960137363607289511)
    ·
      refine ⟨278482440206045410934267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185654960137363607289511 278482440206045410934267)
      ·
        refine ⟨417723660309068116401401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278482440206045410934267 417723660309068116401401)
        ·
          refine ⟨313292745231801087301051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 417723660309068116401401 313292745231801087301051)
          ·
            refine ⟨469939117847701630951577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 313292745231801087301051 469939117847701630951577)
            ·
              refine ⟨352454338385776223213683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 469939117847701630951577 352454338385776223213683)
              ·
                refine ⟨528681507578664334820525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 352454338385776223213683 528681507578664334820525)
                ·
                  refine ⟨198255565341999125557697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 528681507578664334820525 198255565341999125557697)
                  ·
                    refine ⟨148691674006499344168273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 198255565341999125557697 148691674006499344168273)
                    ·
                      refine ⟨111518755504874508126205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 148691674006499344168273 111518755504874508126205)
                      ·
                        rfl

theorem cell23_217182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 2, 1, 3, 2, 2].length) (baseStart_217182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_217182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_217182 prefixEnd_217182 := by exact prefixLift 217182
  have htrace : WordTrace (prefixWord ++ tailWord_217182) baseStart_217182 baseEnd_217182 := by
    simpa [prefixWord, tailWord_217182, baseEnd_217182] using wordTrace_append hprefix tailTrace_217182
  have hstable : (prefixWord ++ tailWord_217182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217182).length < 2 ^ (prefixWord ++ tailWord_217182).sum := by decide
  have hdescent : baseEnd_217182 < baseStart_217182 := by decide
  rcases family_descends (prefixWord ++ tailWord_217182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217197 : List Nat := [1, 5, 1, 1, 2, 1, 1, 3, 2, 6]
def baseStart_217197 : Nat := 118140960795 + 217197 * 2 ^ 59
def prefixEnd_217197 : Nat := 4983230072969 + 3 ^ 40 * 217197 * 2
def baseEnd_217197 : Nat := 37175485904897316479545

theorem tailTrace_217197 : CollatzResearch.WordTrace tailWord_217197 prefixEnd_217197 37175485904897316479545 := by
  unfold tailWord_217197
  simp only [CollatzResearch.WordTrace]
  refine ⟨7921825394139838139481845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5281216929426558759654563 7921825394139838139481845)
  ·
    refine ⟨742671130700609825576423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7921825394139838139481845 742671130700609825576423)
    ·
      refine ⟨1114006696050914738364635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 742671130700609825576423 1114006696050914738364635)
      ·
        refine ⟨1671010044076372107546953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1114006696050914738364635 1671010044076372107546953)
        ·
          refine ⟨1253257533057279080660215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1671010044076372107546953 1253257533057279080660215)
          ·
            refine ⟨1879886299585918620990323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1253257533057279080660215 1879886299585918620990323)
            ·
              refine ⟨2819829449378877931485485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1879886299585918620990323 2819829449378877931485485)
              ·
                refine ⟨1057436043517079224307057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2819829449378877931485485 1057436043517079224307057)
                ·
                  refine ⟨793077032637809418230293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1057436043517079224307057 793077032637809418230293)
                  ·
                    refine ⟨37175485904897316479545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 793077032637809418230293 37175485904897316479545)
                    ·
                      rfl

theorem cell23_217197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 3, 2, 6].length) (baseStart_217197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_217197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_217197 prefixEnd_217197 := by exact prefixLift 217197
  have htrace : WordTrace (prefixWord ++ tailWord_217197) baseStart_217197 baseEnd_217197 := by
    simpa [prefixWord, tailWord_217197, baseEnd_217197] using wordTrace_append hprefix tailTrace_217197
  have hstable : (prefixWord ++ tailWord_217197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217197).length < 2 ^ (prefixWord ++ tailWord_217197).sum := by decide
  have hdescent : baseEnd_217197 < baseStart_217197 := by decide
  rcases family_descends (prefixWord ++ tailWord_217197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217198 : List Nat := [4, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3]
def baseStart_217198 : Nat := 118140960795 + 217198 * 2 ^ 59
def prefixEnd_217198 : Nat := 4983230072969 + 3 ^ 40 * 217198 * 2
def baseEnd_217198 : Nat := 111526971195346445526131

theorem tailTrace_217198 : CollatzResearch.WordTrace tailWord_217198 prefixEnd_217198 111526971195346445526131 := by
  unfold tailWord_217198
  simp only [CollatzResearch.WordTrace]
  refine ⟨990232733392026913783531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5281241244757476873512165 990232733392026913783531)
  ·
    refine ⟨1485349100088040370675297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 990232733392026913783531 1485349100088040370675297)
    ·
      refine ⟨1114011825066030278006473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1485349100088040370675297 1114011825066030278006473)
      ·
        refine ⟨835508868799522708504855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1114011825066030278006473 835508868799522708504855)
        ·
          refine ⟨1253263303199284062757283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 835508868799522708504855 1253263303199284062757283)
          ·
            refine ⟨1879894954798926094135925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1253263303199284062757283 1879894954798926094135925)
            ·
              refine ⟨176240152012399321325243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1879894954798926094135925 176240152012399321325243)
              ·
                refine ⟨264360228018598981987865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 176240152012399321325243 264360228018598981987865)
                ·
                  refine ⟨198270171013949236490899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 264360228018598981987865 198270171013949236490899)
                  ·
                    refine ⟨297405256520923854736349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 198270171013949236490899 297405256520923854736349)
                    ·
                      refine ⟨111526971195346445526131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 297405256520923854736349 111526971195346445526131)
                      ·
                        rfl

theorem cell23_217198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3].length) (baseStart_217198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_217198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_217198 prefixEnd_217198 := by exact prefixLift 217198
  have htrace : WordTrace (prefixWord ++ tailWord_217198) baseStart_217198 baseEnd_217198 := by
    simpa [prefixWord, tailWord_217198, baseEnd_217198] using wordTrace_append hprefix tailTrace_217198
  have hstable : (prefixWord ++ tailWord_217198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217198).length < 2 ^ (prefixWord ++ tailWord_217198).sum := by decide
  have hdescent : baseEnd_217198 < baseStart_217198 := by decide
  rcases family_descends (prefixWord ++ tailWord_217198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217221 : List Nat := [1, 3, 1, 1, 5, 1, 1, 2, 4, 2, 2]
def baseStart_217221 : Nat := 118140960795 + 217221 * 2 ^ 59
def prefixEnd_217221 : Nat := 4983230072969 + 3 ^ 40 * 217221 * 2
def baseEnd_217221 : Nat := 111538781250399855538525

theorem tailTrace_217221 : CollatzResearch.WordTrace tailWord_217221 prefixEnd_217221 111538781250399855538525 := by
  unfold tailWord_217221
  simp only [CollatzResearch.WordTrace]
  refine ⟨7922700746052890238355517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5281800497368593492237011 7922700746052890238355517)
  ·
    refine ⟨2971012779769833839383319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7922700746052890238355517 2971012779769833839383319)
    ·
      refine ⟨4456519169654750759074979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2971012779769833839383319 4456519169654750759074979)
      ·
        refine ⟨6684778754482126138612469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4456519169654750759074979 6684778754482126138612469)
        ·
          refine ⟨626698008232699325494919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6684778754482126138612469 626698008232699325494919)
          ·
            refine ⟨940047012349048988242379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 626698008232699325494919 940047012349048988242379)
            ·
              refine ⟨1410070518523573482363569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 940047012349048988242379 1410070518523573482363569)
              ·
                refine ⟨1057552888892680111772677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1410070518523573482363569 1057552888892680111772677)
                ·
                  refine ⟨198291166667377520957377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1057552888892680111772677 198291166667377520957377)
                  ·
                    refine ⟨148718375000533140718033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 198291166667377520957377 148718375000533140718033)
                    ·
                      refine ⟨111538781250399855538525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 148718375000533140718033 111538781250399855538525)
                      ·
                        rfl

theorem cell23_217221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 2, 4, 2, 2].length) (baseStart_217221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_217221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_217221 prefixEnd_217221 := by exact prefixLift 217221
  have htrace : WordTrace (prefixWord ++ tailWord_217221) baseStart_217221 baseEnd_217221 := by
    simpa [prefixWord, tailWord_217221, baseEnd_217221] using wordTrace_append hprefix tailTrace_217221
  have hstable : (prefixWord ++ tailWord_217221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217221).length < 2 ^ (prefixWord ++ tailWord_217221).sum := by decide
  have hdescent : baseEnd_217221 < baseStart_217221 := by decide
  rcases family_descends (prefixWord ++ tailWord_217221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217224 : List Nat := [2, 1, 3, 4, 1, 2, 1, 1, 2, 1, 5]
def baseStart_217224 : Nat := 118140960795 + 217224 * 2 ^ 59
def prefixEnd_217224 : Nat := 4983230072969 + 3 ^ 40 * 217224 * 2
def baseEnd_217224 : Nat := 111540321692363343801011

theorem tailTrace_217224 : CollatzResearch.WordTrace tailWord_217224 prefixEnd_217224 111540321692363343801011 := by
  unfold tailWord_217224
  simp only [CollatzResearch.WordTrace]
  refine ⟨3961405082521010875357363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5281873443361347833809817 3961405082521010875357363)
  ·
    refine ⟨5942107623781516313036045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3961405082521010875357363 5942107623781516313036045)
    ·
      refine ⟨2228290358918068617388517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5942107623781516313036045 2228290358918068617388517)
      ·
        refine ⟨417804442297137865760347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2228290358918068617388517 417804442297137865760347)
        ·
          refine ⟨626706663445706798640521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 417804442297137865760347 626706663445706798640521)
          ·
            refine ⟨470029997584280098980391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 626706663445706798640521 470029997584280098980391)
            ·
              refine ⟨705044996376420148470587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 470029997584280098980391 705044996376420148470587)
              ·
                refine ⟨1057567494564630222705881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 705044996376420148470587 1057567494564630222705881)
                ·
                  refine ⟨793175620923472667029411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1057567494564630222705881 793175620923472667029411)
                  ·
                    refine ⟨1189763431385209000544117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 793175620923472667029411 1189763431385209000544117)
                    ·
                      refine ⟨111540321692363343801011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1189763431385209000544117 111540321692363343801011)
                      ·
                        rfl

theorem cell23_217224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_217224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_217224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_217224 prefixEnd_217224 := by exact prefixLift 217224
  have htrace : WordTrace (prefixWord ++ tailWord_217224) baseStart_217224 baseEnd_217224 := by
    simpa [prefixWord, tailWord_217224, baseEnd_217224] using wordTrace_append hprefix tailTrace_217224
  have hstable : (prefixWord ++ tailWord_217224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217224).length < 2 ^ (prefixWord ++ tailWord_217224).sum := by decide
  have hdescent : baseEnd_217224 < baseStart_217224 := by decide
  rcases family_descends (prefixWord ++ tailWord_217224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217255 : List Nat := [1, 1, 6, 2, 2, 1, 1, 3, 2, 2, 2]
def baseStart_217255 : Nat := 118140960795 + 217255 * 2 ^ 59
def prefixEnd_217255 : Nat := 4983230072969 + 3 ^ 40 * 217255 * 2
def baseEnd_217255 : Nat := 111556239592652722513369

theorem tailTrace_217255 : CollatzResearch.WordTrace tailWord_217255 prefixEnd_217255 111556239592652722513369 := by
  unfold tailWord_217255
  simp only [CollatzResearch.WordTrace]
  refine ⟨7923940827929714045093219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5282627218619809363395479 7923940827929714045093219)
  ·
    refine ⟨11885911241894571067639829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7923940827929714045093219 11885911241894571067639829)
    ·
      refine ⟨557152089463808018795617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 11885911241894571067639829 557152089463808018795617)
      ·
        refine ⟨417864067097856014096713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 557152089463808018795617 417864067097856014096713)
        ·
          refine ⟨313398050323392010572535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 417864067097856014096713 313398050323392010572535)
          ·
            refine ⟨470097075485088015858803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 313398050323392010572535 470097075485088015858803)
            ·
              refine ⟨705145613227632023788205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 470097075485088015858803 705145613227632023788205)
              ·
                refine ⟨264429604960362008920577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 705145613227632023788205 264429604960362008920577)
                ·
                  refine ⟨198322203720271506690433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 264429604960362008920577 198322203720271506690433)
                  ·
                    refine ⟨148741652790203630017825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 198322203720271506690433 148741652790203630017825)
                    ·
                      refine ⟨111556239592652722513369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 148741652790203630017825 111556239592652722513369)
                      ·
                        rfl

theorem cell23_217255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 3, 2, 2, 2].length) (baseStart_217255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_217255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_217255 prefixEnd_217255 := by exact prefixLift 217255
  have htrace : WordTrace (prefixWord ++ tailWord_217255) baseStart_217255 baseEnd_217255 := by
    simpa [prefixWord, tailWord_217255, baseEnd_217255] using wordTrace_append hprefix tailTrace_217255
  have hstable : (prefixWord ++ tailWord_217255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217255).length < 2 ^ (prefixWord ++ tailWord_217255).sum := by decide
  have hdescent : baseEnd_217255 < baseStart_217255 := by decide
  rcases family_descends (prefixWord ++ tailWord_217255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217284 : List Nat := [2, 3, 3, 1, 2, 1, 1, 2, 1, 2, 5]
def baseStart_217284 : Nat := 118140960795 + 217284 * 2 ^ 59
def prefixEnd_217284 : Nat := 4983230072969 + 3 ^ 40 * 217284 * 2
def baseEnd_217284 : Nat := 111571130531633109050735

theorem tailTrace_217284 : CollatzResearch.WordTrace tailWord_217284 prefixEnd_217284 111571130531633109050735 := by
  unfold tailWord_217284
  simp only [CollatzResearch.WordTrace]
  refine ⟨3962499272412325998949453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5283332363216434665265937 3962499272412325998949453)
  ·
    refine ⟨1485937227154622249606045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3962499272412325998949453 1485937227154622249606045)
    ·
      refine ⟨557226460182983343602267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1485937227154622249606045 557226460182983343602267)
      ·
        refine ⟨835839690274475015403401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 557226460182983343602267 835839690274475015403401)
        ·
          refine ⟨626879767705856261552551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 835839690274475015403401 626879767705856261552551)
          ·
            refine ⟨940319651558784392328827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 626879767705856261552551 940319651558784392328827)
            ·
              refine ⟨1410479477338176588493241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 940319651558784392328827 1410479477338176588493241)
              ·
                refine ⟨1057859608003632441369931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1410479477338176588493241 1057859608003632441369931)
                ·
                  refine ⟨1586789412005448662054897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1057859608003632441369931 1586789412005448662054897)
                  ·
                    refine ⟨1190092059004086496541173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1586789412005448662054897 1190092059004086496541173)
                    ·
                      refine ⟨111571130531633109050735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1190092059004086496541173 111571130531633109050735)
                      ·
                        rfl

theorem cell23_217284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_217284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_217284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_217284 prefixEnd_217284 := by exact prefixLift 217284
  have htrace : WordTrace (prefixWord ++ tailWord_217284) baseStart_217284 baseEnd_217284 := by
    simpa [prefixWord, tailWord_217284, baseEnd_217284] using wordTrace_append hprefix tailTrace_217284
  have hstable : (prefixWord ++ tailWord_217284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217284).length < 2 ^ (prefixWord ++ tailWord_217284).sum := by decide
  have hdescent : baseEnd_217284 < baseStart_217284 := by decide
  rcases family_descends (prefixWord ++ tailWord_217284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217338 : List Nat := [3, 1, 1, 1, 1, 6, 2, 3, 1, 4]
def baseStart_217338 : Nat := 118140960795 + 217338 * 2 ^ 59
def prefixEnd_217338 : Nat := 4983230072969 + 3 ^ 40 * 217338 * 2
def baseEnd_217338 : Nat := 37199619495658632591829

theorem tailTrace_217338 : CollatzResearch.WordTrace tailWord_217338 prefixEnd_217338 37199619495658632591829 := by
  unfold tailWord_217338
  simp only [CollatzResearch.WordTrace]
  refine ⟨1981742021657254805091167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5284645391086012813576445 1981742021657254805091167)
  ·
    refine ⟨2972613032485882207636751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1981742021657254805091167 2972613032485882207636751)
    ·
      refine ⟨4458919548728823311455127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2972613032485882207636751 4458919548728823311455127)
      ·
        refine ⟨6688379323093234967182691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4458919548728823311455127 6688379323093234967182691)
        ·
          refine ⟨10032568984639852450774037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6688379323093234967182691 10032568984639852450774037)
          ·
            refine ⟨470276671154993083630033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 10032568984639852450774037 470276671154993083630033)
            ·
              refine ⟨352707503366244812722525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 470276671154993083630033 352707503366244812722525)
              ·
                refine ⟨132265313762341804770947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 352707503366244812722525 132265313762341804770947)
                ·
                  refine ⟨198397970643512707156421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 132265313762341804770947 198397970643512707156421)
                  ·
                    refine ⟨37199619495658632591829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 198397970643512707156421 37199619495658632591829)
                    ·
                      rfl

theorem cell23_217338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2, 3, 1, 4].length) (baseStart_217338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_217338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_217338 prefixEnd_217338 := by exact prefixLift 217338
  have htrace : WordTrace (prefixWord ++ tailWord_217338) baseStart_217338 baseEnd_217338 := by
    simpa [prefixWord, tailWord_217338, baseEnd_217338] using wordTrace_append hprefix tailTrace_217338
  have hstable : (prefixWord ++ tailWord_217338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217338).length < 2 ^ (prefixWord ++ tailWord_217338).sum := by decide
  have hdescent : baseEnd_217338 < baseStart_217338 := by decide
  rcases family_descends (prefixWord ++ tailWord_217338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217351 : List Nat := [1, 1, 4, 5, 1, 1, 1, 1, 8]
def baseStart_217351 : Nat := 118140960795 + 217351 * 2 ^ 59
def prefixEnd_217351 : Nat := 4983230072969 + 3 ^ 40 * 217351 * 2
def baseEnd_217351 : Nat := 12400614859498260768103

theorem tailTrace_217351 : CollatzResearch.WordTrace tailWord_217351 prefixEnd_217351 12400614859498260768103 := by
  unfold tailWord_217351
  simp only [CollatzResearch.WordTrace]
  refine ⟨7927442235581922440587907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5284961490387948293725271 7927442235581922440587907)
  ·
    refine ⟨11891163353372883660881861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7927442235581922440587907 11891163353372883660881861)
    ·
      refine ⟨2229593128757415686415349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11891163353372883660881861 2229593128757415686415349)
      ·
        refine ⟨209024355821007720601439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2229593128757415686415349 209024355821007720601439)
        ·
          refine ⟨313536533731511580902159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209024355821007720601439 313536533731511580902159)
          ·
            refine ⟨470304800597267371353239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 313536533731511580902159 470304800597267371353239)
            ·
              refine ⟨705457200895901057029859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 470304800597267371353239 705457200895901057029859)
              ·
                refine ⟨1058185801343851585544789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 705457200895901057029859 1058185801343851585544789)
                ·
                  refine ⟨12400614859498260768103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1058185801343851585544789 12400614859498260768103)
                  ·
                    rfl

theorem cell23_217351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 1, 8].length) (baseStart_217351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_217351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_217351 prefixEnd_217351 := by exact prefixLift 217351
  have htrace : WordTrace (prefixWord ++ tailWord_217351) baseStart_217351 baseEnd_217351 := by
    simpa [prefixWord, tailWord_217351, baseEnd_217351] using wordTrace_append hprefix tailTrace_217351
  have hstable : (prefixWord ++ tailWord_217351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217351).length < 2 ^ (prefixWord ++ tailWord_217351).sum := by decide
  have hdescent : baseEnd_217351 < baseStart_217351 := by decide
  rcases family_descends (prefixWord ++ tailWord_217351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217361 : List Nat := [1, 2, 2, 1, 1, 5, 1, 3, 3, 1, 3]
def baseStart_217361 : Nat := 118140960795 + 217361 * 2 ^ 59
def prefixEnd_217361 : Nat := 4983230072969 + 3 ^ 40 * 217361 * 2
def baseEnd_217361 : Nat := 111610668542029307787881

theorem tailTrace_217361 : CollatzResearch.WordTrace tailWord_217361 prefixEnd_217361 111610668542029307787881 := by
  unfold tailWord_217361
  simp only [CollatzResearch.WordTrace]
  refine ⟨7927806965545694148451937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5285204643697129432301291 7927806965545694148451937)
  ·
    refine ⟨5945855224159270611338953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7927806965545694148451937 5945855224159270611338953)
    ·
      refine ⟨4459391418119452958504215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5945855224159270611338953 4459391418119452958504215)
      ·
        refine ⟨6689087127179179437756323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4459391418119452958504215 6689087127179179437756323)
        ·
          refine ⟨10033630690768769156634485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6689087127179179437756323 10033630690768769156634485)
          ·
            refine ⟨940652877259572108434483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10033630690768769156634485 940652877259572108434483)
            ·
              refine ⟨1410979315889358162651725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 940652877259572108434483 1410979315889358162651725)
              ·
                refine ⟨529117243458509310994397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1410979315889358162651725 529117243458509310994397)
                ·
                  refine ⟨198418966296940991622899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 529117243458509310994397 198418966296940991622899)
                  ·
                    refine ⟨297628449445411487434349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 198418966296940991622899 297628449445411487434349)
                    ·
                      refine ⟨111610668542029307787881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 297628449445411487434349 111610668542029307787881)
                      ·
                        rfl

theorem cell23_217361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 3, 3, 1, 3].length) (baseStart_217361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_217361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_217361 prefixEnd_217361 := by exact prefixLift 217361
  have htrace : WordTrace (prefixWord ++ tailWord_217361) baseStart_217361 baseEnd_217361 := by
    simpa [prefixWord, tailWord_217361, baseEnd_217361] using wordTrace_append hprefix tailTrace_217361
  have hstable : (prefixWord ++ tailWord_217361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217361).length < 2 ^ (prefixWord ++ tailWord_217361).sum := by decide
  have hdescent : baseEnd_217361 < baseStart_217361 := by decide
  rcases family_descends (prefixWord ++ tailWord_217361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217378 : List Nat := [3, 3, 1, 1, 3, 1, 2, 2, 3, 1, 3]
def baseStart_217378 : Nat := 118140960795 + 217378 * 2 ^ 59
def prefixEnd_217378 : Nat := 4983230072969 + 3 ^ 40 * 217378 * 2
def baseEnd_217378 : Nat := 111619397713155741275303

theorem tailTrace_217378 : CollatzResearch.WordTrace tailWord_217378 prefixEnd_217378 111619397713155741275303 := by
  unfold tailWord_217378
  simp only [CollatzResearch.WordTrace]
  refine ⟨1982106751621026512955197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5285618004322737367880525 1982106751621026512955197)
  ·
    refine ⟨743290031857884942358199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1982106751621026512955197 743290031857884942358199)
    ·
      refine ⟨1114935047786827413537299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 743290031857884942358199 1114935047786827413537299)
      ·
        refine ⟨1672402571680241120305949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1114935047786827413537299 1672402571680241120305949)
        ·
          refine ⟨627150964380090420114731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1672402571680241120305949 627150964380090420114731)
          ·
            refine ⟨940726446570135630172097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 627150964380090420114731 940726446570135630172097)
            ·
              refine ⟨705544834927601722629073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 940726446570135630172097 705544834927601722629073)
              ·
                refine ⟨529158626195701291971805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 705544834927601722629073 529158626195701291971805)
                ·
                  refine ⟨198434484823387984489427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 529158626195701291971805 198434484823387984489427)
                  ·
                    refine ⟨297651727235081976734141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 198434484823387984489427 297651727235081976734141)
                    ·
                      refine ⟨111619397713155741275303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 297651727235081976734141 111619397713155741275303)
                      ·
                        rfl

theorem cell23_217378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 2, 3, 1, 3].length) (baseStart_217378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_217378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_217378 prefixEnd_217378 := by exact prefixLift 217378
  have htrace : WordTrace (prefixWord ++ tailWord_217378) baseStart_217378 baseEnd_217378 := by
    simpa [prefixWord, tailWord_217378, baseEnd_217378] using wordTrace_append hprefix tailTrace_217378
  have hstable : (prefixWord ++ tailWord_217378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217378).length < 2 ^ (prefixWord ++ tailWord_217378).sum := by decide
  have hdescent : baseEnd_217378 < baseStart_217378 := by decide
  rcases family_descends (prefixWord ++ tailWord_217378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217387 : List Nat := [1, 1, 1, 1, 2, 1, 2, 1, 1, 7, 5]
def baseStart_217387 : Nat := 118140960795 + 217387 * 2 ^ 59
def prefixEnd_217387 : Nat := 4983230072969 + 3 ^ 40 * 217387 * 2
def baseEnd_217387 : Nat := 111624019039046206062761

theorem tailTrace_217387 : CollatzResearch.WordTrace tailWord_217387 prefixEnd_217387 111624019039046206062761 := by
  unfold tailWord_217387
  simp only [CollatzResearch.WordTrace]
  refine ⟨7928755263451500588898415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5285836842301000392598943 7928755263451500588898415)
  ·
    refine ⟨11893132895177250883347623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7928755263451500588898415 11893132895177250883347623)
    ·
      refine ⟨17839699342765876325021435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11893132895177250883347623 17839699342765876325021435)
      ·
        refine ⟨26759549014148814487532153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17839699342765876325021435 26759549014148814487532153)
        ·
          refine ⟨20069661760611610865649115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26759549014148814487532153 20069661760611610865649115)
          ·
            refine ⟨30104492640917416298473673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20069661760611610865649115 30104492640917416298473673)
            ·
              refine ⟨22578369480688062223855255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30104492640917416298473673 22578369480688062223855255)
              ·
                refine ⟨33867554221032093335782883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22578369480688062223855255 33867554221032093335782883)
                ·
                  refine ⟨50801331331548140003674325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33867554221032093335782883 50801331331548140003674325)
                  ·
                    refine ⟨1190656203083159531336117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50801331331548140003674325 1190656203083159531336117)
                    ·
                      refine ⟨111624019039046206062761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1190656203083159531336117 111624019039046206062761)
                      ·
                        rfl

theorem cell23_217387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 7, 5].length) (baseStart_217387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_217387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_217387 prefixEnd_217387 := by exact prefixLift 217387
  have htrace : WordTrace (prefixWord ++ tailWord_217387) baseStart_217387 baseEnd_217387 := by
    simpa [prefixWord, tailWord_217387, baseEnd_217387] using wordTrace_append hprefix tailTrace_217387
  have hstable : (prefixWord ++ tailWord_217387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217387).length < 2 ^ (prefixWord ++ tailWord_217387).sum := by decide
  have hdescent : baseEnd_217387 < baseStart_217387 := by decide
  rcases family_descends (prefixWord ++ tailWord_217387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217389 : List Nat := [1, 5, 3, 1, 3, 1, 1, 3, 1, 4]
def baseStart_217389 : Nat := 118140960795 + 217389 * 2 ^ 59
def prefixEnd_217389 : Nat := 4983230072969 + 3 ^ 40 * 217389 * 2
def baseEnd_217389 : Nat := 37208348666785066079251

theorem tailTrace_217389 : CollatzResearch.WordTrace tailWord_217389 prefixEnd_217389 37208348666785066079251 := by
  unfold tailWord_217389
  simp only [CollatzResearch.WordTrace]
  refine ⟨7928828209444254930471221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5285885472962836620314147 7928828209444254930471221)
  ·
    refine ⟨743327644635398899731677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7928828209444254930471221 743327644635398899731677)
    ·
      refine ⟨278747866738274587399379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 743327644635398899731677 278747866738274587399379)
      ·
        refine ⟨418121800107411881099069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278747866738274587399379 418121800107411881099069)
        ·
          refine ⟨156795675040279455412151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 418121800107411881099069 156795675040279455412151)
          ·
            refine ⟨235193512560419183118227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156795675040279455412151 235193512560419183118227)
            ·
              refine ⟨352790268840628774677341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 235193512560419183118227 352790268840628774677341)
              ·
                refine ⟨132296350815235790504003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 352790268840628774677341 132296350815235790504003)
                ·
                  refine ⟨198444526222853685756005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 132296350815235790504003 198444526222853685756005)
                  ·
                    refine ⟨37208348666785066079251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 198444526222853685756005 37208348666785066079251)
                    ·
                      rfl

theorem cell23_217389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_217389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_217389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_217389 prefixEnd_217389 := by exact prefixLift 217389
  have htrace : WordTrace (prefixWord ++ tailWord_217389) baseStart_217389 baseEnd_217389 := by
    simpa [prefixWord, tailWord_217389, baseEnd_217389] using wordTrace_append hprefix tailTrace_217389
  have hstable : (prefixWord ++ tailWord_217389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217389).length < 2 ^ (prefixWord ++ tailWord_217389).sum := by decide
  have hdescent : baseEnd_217389 < baseStart_217389 := by decide
  rcases family_descends (prefixWord ++ tailWord_217389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217412 : List Nat := [2, 3, 4, 1, 2, 2, 1, 1, 3, 1, 3]
def baseStart_217412 : Nat := 118140960795 + 217412 * 2 ^ 59
def prefixEnd_217412 : Nat := 4983230072969 + 3 ^ 40 * 217412 * 2
def baseEnd_217412 : Nat := 111636856055408608250147

theorem tailTrace_217412 : CollatzResearch.WordTrace tailWord_217412 prefixEnd_217412 111636856055408608250147 := by
  unfold tailWord_217412
  simp only [CollatzResearch.WordTrace]
  refine ⟨3964833544180464929279245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5286444725573953239038993 3964833544180464929279245)
  ·
    refine ⟨1486812579067674348479717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3964833544180464929279245 1486812579067674348479717)
    ·
      refine ⟨278777358575188940339947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1486812579067674348479717 278777358575188940339947)
      ·
        refine ⟨418166037862783410509921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278777358575188940339947 418166037862783410509921)
        ·
          refine ⟨313624528397087557882441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 418166037862783410509921 313624528397087557882441)
          ·
            refine ⟨235218396297815668411831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 313624528397087557882441 235218396297815668411831)
            ·
              refine ⟨352827594446723502617747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 235218396297815668411831 352827594446723502617747)
              ·
                refine ⟨529241391670085253926621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 352827594446723502617747 529241391670085253926621)
                ·
                  refine ⟨198465521876281970222483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 529241391670085253926621 198465521876281970222483)
                  ·
                    refine ⟨297698282814422955333725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 198465521876281970222483 297698282814422955333725)
                    ·
                      refine ⟨111636856055408608250147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 297698282814422955333725 111636856055408608250147)
                      ·
                        rfl

theorem cell23_217412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_217412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_217412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_217412 prefixEnd_217412 := by exact prefixLift 217412
  have htrace : WordTrace (prefixWord ++ tailWord_217412) baseStart_217412 baseEnd_217412 := by
    simpa [prefixWord, tailWord_217412, baseEnd_217412] using wordTrace_append hprefix tailTrace_217412
  have hstable : (prefixWord ++ tailWord_217412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217412).length < 2 ^ (prefixWord ++ tailWord_217412).sum := by decide
  have hdescent : baseEnd_217412 < baseStart_217412 := by decide
  rcases family_descends (prefixWord ++ tailWord_217412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217424 : List Nat := [2, 1, 1, 1, 1, 7, 2, 8]
def baseStart_217424 : Nat := 118140960795 + 217424 * 2 ^ 59
def prefixEnd_217424 : Nat := 4983230072969 + 3 ^ 40 * 217424 * 2
def baseEnd_217424 : Nat := 4134926586046761529633

theorem tailTrace_217424 : CollatzResearch.WordTrace tailWord_217424 prefixEnd_217424 4134926586046761529633 := by
  unfold tailWord_217424
  simp only [CollatzResearch.WordTrace]
  refine ⟨3965052382158727953997663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5286736509544970605330217 3965052382158727953997663)
  ·
    refine ⟨5947578573238091930996495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3965052382158727953997663 5947578573238091930996495)
    ·
      refine ⟨8921367859857137896494743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5947578573238091930996495 8921367859857137896494743)
      ·
        refine ⟨13382051789785706844742115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8921367859857137896494743 13382051789785706844742115)
        ·
          refine ⟨20073077684678560267113173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13382051789785706844742115 20073077684678560267113173)
          ·
            refine ⟨470462758234653756260465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 20073077684678560267113173 470462758234653756260465)
            ·
              refine ⟨352847068675990317195349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 470462758234653756260465 352847068675990317195349)
              ·
                refine ⟨4134926586046761529633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 352847068675990317195349 4134926586046761529633)
                ·
                  rfl

theorem cell23_217424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2, 8].length) (baseStart_217424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_217424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_217424 prefixEnd_217424 := by exact prefixLift 217424
  have htrace : WordTrace (prefixWord ++ tailWord_217424) baseStart_217424 baseEnd_217424 := by
    simpa [prefixWord, tailWord_217424, baseEnd_217424] using wordTrace_append hprefix tailTrace_217424
  have hstable : (prefixWord ++ tailWord_217424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217424).length < 2 ^ (prefixWord ++ tailWord_217424).sum := by decide
  have hdescent : baseEnd_217424 < baseStart_217424 := by decide
  rcases family_descends (prefixWord ++ tailWord_217424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217428 : List Nat := [2, 4, 1, 1, 2, 3, 1, 3, 2, 4]
def baseStart_217428 : Nat := 118140960795 + 217428 * 2 ^ 59
def prefixEnd_217428 : Nat := 4983230072969 + 3 ^ 40 * 217428 * 2
def baseEnd_217428 : Nat := 37215023915293515216691

theorem tailTrace_217428 : CollatzResearch.WordTrace tailWord_217428 prefixEnd_217428 37215023915293515216691 := by
  unfold tailWord_217428
  simp only [CollatzResearch.WordTrace]
  refine ⟨3965125328151482295570469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5286833770868643060760625 3965125328151482295570469)
  ·
    refine ⟨743460999028402930419463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3965125328151482295570469 743460999028402930419463)
    ·
      refine ⟨1115191498542604395629195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 743460999028402930419463 1115191498542604395629195)
      ·
        refine ⟨1672787247813906593443793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1115191498542604395629195 1672787247813906593443793)
        ·
          refine ⟨1254590435860429945082845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1672787247813906593443793 1254590435860429945082845)
          ·
            refine ⟨470471413447661229406067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1254590435860429945082845 470471413447661229406067)
            ·
              refine ⟨705707120171491844109101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 470471413447661229406067 705707120171491844109101)
              ·
                refine ⟨264640170064309441540913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 705707120171491844109101 264640170064309441540913)
                ·
                  refine ⟨198480127548232081155685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 264640170064309441540913 198480127548232081155685)
                  ·
                    refine ⟨37215023915293515216691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 198480127548232081155685 37215023915293515216691)
                    ·
                      rfl

theorem cell23_217428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 3, 2, 4].length) (baseStart_217428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_217428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_217428 prefixEnd_217428 := by exact prefixLift 217428
  have htrace : WordTrace (prefixWord ++ tailWord_217428) baseStart_217428 baseEnd_217428 := by
    simpa [prefixWord, tailWord_217428, baseEnd_217428] using wordTrace_append hprefix tailTrace_217428
  have hstable : (prefixWord ++ tailWord_217428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217428).length < 2 ^ (prefixWord ++ tailWord_217428).sum := by decide
  have hdescent : baseEnd_217428 < baseStart_217428 := by decide
  rcases family_descends (prefixWord ++ tailWord_217428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217462 : List Nat := [5, 1, 1, 4, 1, 1, 2, 2, 2, 4]
def baseStart_217462 : Nat := 118140960795 + 217462 * 2 ^ 59
def prefixEnd_217462 : Nat := 4983230072969 + 3 ^ 40 * 217462 * 2
def baseEnd_217462 : Nat := 37220843362711137541639

theorem tailTrace_217462 : CollatzResearch.WordTrace tailWord_217462 prefixEnd_217462 37220843362711137541639 := by
  unfold tailWord_217462
  simp only [CollatzResearch.WordTrace]
  refine ⟨495718171136236774867415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5287660492119858931919093 495718171136236774867415)
  ·
    refine ⟨743577256704355162301123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 495718171136236774867415 743577256704355162301123)
    ·
      refine ⟨1115365885056532743451685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 743577256704355162301123 1115365885056532743451685)
      ·
        refine ⟨209131103448099889397191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1115365885056532743451685 209131103448099889397191)
        ·
          refine ⟨313696655172149834095787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209131103448099889397191 313696655172149834095787)
          ·
            refine ⟨470544982758224751143681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 313696655172149834095787 470544982758224751143681)
            ·
              refine ⟨352908737068668563357761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 470544982758224751143681 352908737068668563357761)
              ·
                refine ⟨264681552801501422518321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 352908737068668563357761 264681552801501422518321)
                ·
                  refine ⟨198511164601126066888741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 264681552801501422518321 198511164601126066888741)
                  ·
                    refine ⟨37220843362711137541639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 198511164601126066888741 37220843362711137541639)
                    ·
                      rfl

theorem cell23_217462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 2, 2, 2, 4].length) (baseStart_217462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_217462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_217462 prefixEnd_217462 := by exact prefixLift 217462
  have htrace : WordTrace (prefixWord ++ tailWord_217462) baseStart_217462 baseEnd_217462 := by
    simpa [prefixWord, tailWord_217462, baseEnd_217462] using wordTrace_append hprefix tailTrace_217462
  have hstable : (prefixWord ++ tailWord_217462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217462).length < 2 ^ (prefixWord ++ tailWord_217462).sum := by decide
  have hdescent : baseEnd_217462 < baseStart_217462 := by decide
  rcases family_descends (prefixWord ++ tailWord_217462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217469 : List Nat := [1, 4, 1, 1, 2, 5, 2, 2, 1, 2, 2]
def baseStart_217469 : Nat := 118140960795 + 217469 * 2 ^ 59
def prefixEnd_217469 : Nat := 4983230072969 + 3 ^ 40 * 217469 * 2
def baseEnd_217469 : Nat := 111666124452714885237385

theorem tailTrace_217469 : CollatzResearch.WordTrace tailWord_217469 prefixEnd_217469 111666124452714885237385 := by
  unfold tailWord_217469
  simp only [CollatzResearch.WordTrace]
  refine ⟨7931746049154428593383461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5287830699436285728922307 7931746049154428593383461)
  ·
    refine ⟨1487202384216455361259399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7931746049154428593383461 1487202384216455361259399)
    ·
      refine ⟨2230803576324683041889099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1487202384216455361259399 2230803576324683041889099)
      ·
        refine ⟨3346205364487024562833649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2230803576324683041889099 3346205364487024562833649)
        ·
          refine ⟨2509654023365268422125237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3346205364487024562833649 2509654023365268422125237)
          ·
            refine ⟨235280064690493914574241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2509654023365268422125237 235280064690493914574241)
            ·
              refine ⟨176460048517870435930681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 235280064690493914574241 176460048517870435930681)
              ·
                refine ⟨132345036388402826948011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 176460048517870435930681 132345036388402826948011)
                ·
                  refine ⟨198517554582604240422017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 132345036388402826948011 198517554582604240422017)
                  ·
                    refine ⟨148888165936953180316513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 198517554582604240422017 148888165936953180316513)
                    ·
                      refine ⟨111666124452714885237385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 148888165936953180316513 111666124452714885237385)
                      ·
                        rfl

theorem cell23_217469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 2, 2, 1, 2, 2].length) (baseStart_217469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_217469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_217469 prefixEnd_217469 := by exact prefixLift 217469
  have htrace : WordTrace (prefixWord ++ tailWord_217469) baseStart_217469 baseEnd_217469 := by
    simpa [prefixWord, tailWord_217469, baseEnd_217469] using wordTrace_append hprefix tailTrace_217469
  have hstable : (prefixWord ++ tailWord_217469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217469).length < 2 ^ (prefixWord ++ tailWord_217469).sum := by decide
  have hdescent : baseEnd_217469 < baseStart_217469 := by decide
  rcases family_descends (prefixWord ++ tailWord_217469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217484 : List Nat := [2, 2, 1, 2, 1, 4, 1, 1, 1, 8]
def baseStart_217484 : Nat := 118140960795 + 217484 * 2 ^ 59
def prefixEnd_217484 : Nat := 4983230072969 + 3 ^ 40 * 217484 * 2
def baseEnd_217484 : Nat := 37224608887510775516605

theorem tailTrace_217484 : CollatzResearch.WordTrace tailWord_217484 prefixEnd_217484 37224608887510775516605 := by
  unfold tailWord_217484
  simp only [CollatzResearch.WordTrace]
  refine ⟨3966146572050043077589753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5288195429400057436786337 3966146572050043077589753)
  ·
    refine ⟨2974609929037532308192315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3966146572050043077589753 2974609929037532308192315)
    ·
      refine ⟨4461914893556298462288473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2974609929037532308192315 4461914893556298462288473)
      ·
        refine ⟨3346436170167223846716355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4461914893556298462288473 3346436170167223846716355)
        ·
          refine ⟨5019654255250835770074533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3346436170167223846716355 5019654255250835770074533)
          ·
            refine ⟨941185172859531706888975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5019654255250835770074533 941185172859531706888975)
            ·
              refine ⟨1411777759289297560333463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 941185172859531706888975 1411777759289297560333463)
              ·
                refine ⟨2117666638933946340500195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1411777759289297560333463 2117666638933946340500195)
                ·
                  refine ⟨3176499958400919510750293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2117666638933946340500195 3176499958400919510750293)
                  ·
                    refine ⟨37224608887510775516605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 3176499958400919510750293 37224608887510775516605)
                    ·
                      rfl

theorem cell23_217484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 1, 1, 8].length) (baseStart_217484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_217484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_217484 prefixEnd_217484 := by exact prefixLift 217484
  have htrace : WordTrace (prefixWord ++ tailWord_217484) baseStart_217484 baseEnd_217484 := by
    simpa [prefixWord, tailWord_217484, baseEnd_217484] using wordTrace_append hprefix tailTrace_217484
  have hstable : (prefixWord ++ tailWord_217484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217484).length < 2 ^ (prefixWord ++ tailWord_217484).sum := by decide
  have hdescent : baseEnd_217484 < baseStart_217484 := by decide
  rcases family_descends (prefixWord ++ tailWord_217484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217508 : List Nat := [2, 3, 1, 2, 1, 1, 4, 2, 1, 4, 2]
def baseStart_217508 : Nat := 118140960795 + 217508 * 2 ^ 59
def prefixEnd_217508 : Nat := 4983230072969 + 3 ^ 40 * 217508 * 2
def baseEnd_217508 : Nat := 111686150198240232649705

theorem tailTrace_217508 : CollatzResearch.WordTrace tailWord_217508 prefixEnd_217508 111686150198240232649705 := by
  unfold tailWord_217508
  simp only [CollatzResearch.WordTrace]
  refine ⟨3966584248006569127026589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5288778997342092169368785 3966584248006569127026589)
  ·
    refine ⟨1487469093002463422634971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3966584248006569127026589 1487469093002463422634971)
    ·
      refine ⟨2231203639503695133952457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1487469093002463422634971 2231203639503695133952457)
      ·
        refine ⟨1673402729627771350464343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2231203639503695133952457 1673402729627771350464343)
        ·
          refine ⟨2510104094441657025696515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1673402729627771350464343 2510104094441657025696515)
          ·
            refine ⟨3765156141662485538544773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2510104094441657025696515 3765156141662485538544773)
            ·
              refine ⟨705966776561716038477145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3765156141662485538544773 705966776561716038477145)
              ·
                refine ⟨529475082421287028857859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 705966776561716038477145 529475082421287028857859)
                ·
                  refine ⟨794212623631930543286789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 529475082421287028857859 794212623631930543286789)
                  ·
                    refine ⟨148914866930986976866273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 794212623631930543286789 148914866930986976866273)
                    ·
                      refine ⟨111686150198240232649705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 148914866930986976866273 111686150198240232649705)
                      ·
                        rfl

theorem cell23_217508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 2, 1, 4, 2].length) (baseStart_217508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_217508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_217508 prefixEnd_217508 := by exact prefixLift 217508
  have htrace : WordTrace (prefixWord ++ tailWord_217508) baseStart_217508 baseEnd_217508 := by
    simpa [prefixWord, tailWord_217508, baseEnd_217508] using wordTrace_append hprefix tailTrace_217508
  have hstable : (prefixWord ++ tailWord_217508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217508).length < 2 ^ (prefixWord ++ tailWord_217508).sum := by decide
  have hdescent : baseEnd_217508 < baseStart_217508 := by decide
  rcases family_descends (prefixWord ++ tailWord_217508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217512 : List Nat := [2, 1, 6, 1, 1, 2, 1, 3, 1, 3, 2]
def baseStart_217512 : Nat := 118140960795 + 217512 * 2 ^ 59
def prefixEnd_217512 : Nat := 4983230072969 + 3 ^ 40 * 217512 * 2
def baseEnd_217512 : Nat := 111688204120858216999687

theorem tailTrace_217512 : CollatzResearch.WordTrace tailWord_217512 prefixEnd_217512 111688204120858216999687 := by
  unfold tailWord_217512
  simp only [CollatzResearch.WordTrace]
  refine ⟨3966657193999323468599395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5288876258665764624799193 3966657193999323468599395)
  ·
    refine ⟨5949985790998985202899093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3966657193999323468599395 5949985790998985202899093)
    ·
      refine ⟨278905583953077431385895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 5949985790998985202899093 278905583953077431385895)
      ·
        refine ⟨418358375929616147078843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278905583953077431385895 418358375929616147078843)
        ·
          refine ⟨627537563894424220618265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 418358375929616147078843 627537563894424220618265)
          ·
            refine ⟨470653172920818165463699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 627537563894424220618265 470653172920818165463699)
            ·
              refine ⟨705979759381227248195549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 470653172920818165463699 705979759381227248195549)
              ·
                refine ⟨264742409767960218073331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 705979759381227248195549 264742409767960218073331)
                ·
                  refine ⟨397113614651940327109997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 264742409767960218073331 397113614651940327109997)
                  ·
                    refine ⟨148917605494477622666249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 397113614651940327109997 148917605494477622666249)
                    ·
                      refine ⟨111688204120858216999687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 148917605494477622666249 111688204120858216999687)
                      ·
                        rfl

theorem cell23_217512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 3, 1, 3, 2].length) (baseStart_217512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_217512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_217512 prefixEnd_217512 := by exact prefixLift 217512
  have htrace : WordTrace (prefixWord ++ tailWord_217512) baseStart_217512 baseEnd_217512 := by
    simpa [prefixWord, tailWord_217512, baseEnd_217512] using wordTrace_append hprefix tailTrace_217512
  have hstable : (prefixWord ++ tailWord_217512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217512).length < 2 ^ (prefixWord ++ tailWord_217512).sum := by decide
  have hdescent : baseEnd_217512 < baseStart_217512 := by decide
  rcases family_descends (prefixWord ++ tailWord_217512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217521 : List Nat := [1, 2, 2, 4, 1, 2, 1, 2, 2, 2, 4]
def baseStart_217521 : Nat := 118140960795 + 217521 * 2 ^ 59
def prefixEnd_217521 : Nat := 4983230072969 + 3 ^ 40 * 217521 * 2
def baseEnd_217521 : Nat := 111692825446748681787145

theorem tailTrace_217521 : CollatzResearch.WordTrace tailWord_217521 prefixEnd_217521 111692825446748681787145 := by
  unfold tailWord_217521
  simp only [CollatzResearch.WordTrace]
  refine ⟨7933642644966041474276417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5289095096644027649517611 7933642644966041474276417)
  ·
    refine ⟨5950231983724531105707313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7933642644966041474276417 5950231983724531105707313)
    ·
      refine ⟨4462673987793398329280485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5950231983724531105707313 4462673987793398329280485)
      ·
        refine ⟨836751372711262186740091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4462673987793398329280485 836751372711262186740091)
        ·
          refine ⟨1255127059066893280110137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 836751372711262186740091 1255127059066893280110137)
          ·
            refine ⟨941345294300169960082603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1255127059066893280110137 941345294300169960082603)
            ·
              refine ⟨1412017941450254940123905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 941345294300169960082603 1412017941450254940123905)
              ·
                refine ⟨1059013456087691205092929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1412017941450254940123905 1059013456087691205092929)
                ·
                  refine ⟨794260092065768403819697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1059013456087691205092929 794260092065768403819697)
                  ·
                    refine ⟨595695069049326302864773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 794260092065768403819697 595695069049326302864773)
                    ·
                      refine ⟨111692825446748681787145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 595695069049326302864773 111692825446748681787145)
                      ·
                        rfl

theorem cell23_217521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_217521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_217521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_217521 prefixEnd_217521 := by exact prefixLift 217521
  have htrace : WordTrace (prefixWord ++ tailWord_217521) baseStart_217521 baseEnd_217521 := by
    simpa [prefixWord, tailWord_217521, baseEnd_217521] using wordTrace_append hprefix tailTrace_217521
  have hstable : (prefixWord ++ tailWord_217521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217521).length < 2 ^ (prefixWord ++ tailWord_217521).sum := by decide
  have hdescent : baseEnd_217521 < baseStart_217521 := by decide
  rcases family_descends (prefixWord ++ tailWord_217521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217561 : List Nat := [1, 2, 1, 2, 4, 1, 2, 3, 2, 5]
def baseStart_217561 : Nat := 118140960795 + 217561 * 2 ^ 59
def prefixEnd_217561 : Nat := 4983230072969 + 3 ^ 40 * 217561 * 2
def baseEnd_217561 : Nat := 37237788224309508428987

theorem tailTrace_217561 : CollatzResearch.WordTrace tailWord_217561 prefixEnd_217561 37237788224309508428987 := by
  unfold tailWord_217561
  simp only [CollatzResearch.WordTrace]
  refine ⟨7935101564821128305732537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5290067709880752203821691 7935101564821128305732537)
  ·
    refine ⟨5951326173615846229299403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7935101564821128305732537 5951326173615846229299403)
    ·
      refine ⟨8926989260423769343949105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5951326173615846229299403 8926989260423769343949105)
      ·
        refine ⟨6695241945317827007961829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8926989260423769343949105 6695241945317827007961829)
        ·
          refine ⟨1255357864747092563992843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6695241945317827007961829 1255357864747092563992843)
          ·
            refine ⟨1883036797120638845989265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1255357864747092563992843 1883036797120638845989265)
            ·
              refine ⟨1412277597840479134491949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1883036797120638845989265 1412277597840479134491949)
              ·
                refine ⟨529604099190179675434481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1412277597840479134491949 529604099190179675434481)
                ·
                  refine ⟨397203074392634756575861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 529604099190179675434481 397203074392634756575861)
                  ·
                    refine ⟨37237788224309508428987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 397203074392634756575861 37237788224309508428987)
                    ·
                      rfl

theorem cell23_217561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 3, 2, 5].length) (baseStart_217561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_217561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_217561 prefixEnd_217561 := by exact prefixLift 217561
  have htrace : WordTrace (prefixWord ++ tailWord_217561) baseStart_217561 baseEnd_217561 := by
    simpa [prefixWord, tailWord_217561, baseEnd_217561] using wordTrace_append hprefix tailTrace_217561
  have hstable : (prefixWord ++ tailWord_217561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217561).length < 2 ^ (prefixWord ++ tailWord_217561).sum := by decide
  have hdescent : baseEnd_217561 < baseStart_217561 := by decide
  rcases family_descends (prefixWord ++ tailWord_217561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217578 : List Nat := [3, 1, 3, 1, 3, 2, 1, 2, 2, 5]
def baseStart_217578 : Nat := 118140960795 + 217578 * 2 ^ 59
def prefixEnd_217578 : Nat := 4983230072969 + 3 ^ 40 * 217578 * 2
def baseEnd_217578 : Nat := 37240697948018319591461

theorem tailTrace_217578 : CollatzResearch.WordTrace tailWord_217578 prefixEnd_217578 37240697948018319591461 := by
  unfold tailWord_217578
  simp only [CollatzResearch.WordTrace]
  refine ⟨1983930401439885052275347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5290481070506360139400925 1983930401439885052275347)
  ·
    refine ⟨2975895602159827578413021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1983930401439885052275347 2975895602159827578413021)
    ·
      refine ⟨1115960850809935341904883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2975895602159827578413021 1115960850809935341904883)
      ·
        refine ⟨1673941276214903012857325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1115960850809935341904883 1673941276214903012857325)
        ·
          refine ⟨627727978580588629821497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1673941276214903012857325 627727978580588629821497)
          ·
            refine ⟨470795983935441472366123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 627727978580588629821497 470795983935441472366123)
            ·
              refine ⟨706193975903162208549185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 470795983935441472366123 706193975903162208549185)
              ·
                refine ⟨529645481927371656411889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 706193975903162208549185 529645481927371656411889)
                ·
                  refine ⟨397234111445528742308917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 529645481927371656411889 397234111445528742308917)
                  ·
                    refine ⟨37240697948018319591461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 397234111445528742308917 37240697948018319591461)
                    ·
                      rfl

theorem cell23_217578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 2, 2, 5].length) (baseStart_217578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_217578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_217578 prefixEnd_217578 := by exact prefixLift 217578
  have htrace : WordTrace (prefixWord ++ tailWord_217578) baseStart_217578 baseEnd_217578 := by
    simpa [prefixWord, tailWord_217578, baseEnd_217578] using wordTrace_append hprefix tailTrace_217578
  have hstable : (prefixWord ++ tailWord_217578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217578).length < 2 ^ (prefixWord ++ tailWord_217578).sum := by decide
  have hdescent : baseEnd_217578 < baseStart_217578 := by decide
  rcases family_descends (prefixWord ++ tailWord_217578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217642 : List Nat := [3, 1, 4, 1, 1, 3, 1, 4, 1, 4]
def baseStart_217642 : Nat := 118140960795 + 217642 * 2 ^ 59
def prefixEnd_217642 : Nat := 4983230072969 + 3 ^ 40 * 217642 * 2
def baseEnd_217642 : Nat := 37251652201980902791363

theorem tailTrace_217642 : CollatzResearch.WordTrace tailWord_217642 prefixEnd_217642 37251652201980902791363 := by
  unfold tailWord_217642
  simp only [CollatzResearch.WordTrace]
  refine ⟨1984513969381919784857795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5292037251685119426287453 1984513969381919784857795)
  ·
    refine ⟨2976770954072879677286693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1984513969381919784857795 2976770954072879677286693)
    ·
      refine ⟨558144553888664939491255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2976770954072879677286693 558144553888664939491255)
      ·
        refine ⟨837216830832997409236883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 558144553888664939491255 837216830832997409236883)
        ·
          refine ⟨1255825246249496113855325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 837216830832997409236883 1255825246249496113855325)
          ·
            refine ⟨470934467343561042695747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1255825246249496113855325 470934467343561042695747)
            ·
              refine ⟨706401701015341564043621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 470934467343561042695747 706401701015341564043621)
              ·
                refine ⟨132450318940376543258179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 706401701015341564043621 132450318940376543258179)
                ·
                  refine ⟨198675478410564814887269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 132450318940376543258179 198675478410564814887269)
                  ·
                    refine ⟨37251652201980902791363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 198675478410564814887269 37251652201980902791363)
                    ·
                      rfl

theorem cell23_217642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 4, 1, 4].length) (baseStart_217642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_217642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_217642 prefixEnd_217642 := by exact prefixLift 217642
  have htrace : WordTrace (prefixWord ++ tailWord_217642) baseStart_217642 baseEnd_217642 := by
    simpa [prefixWord, tailWord_217642, baseEnd_217642] using wordTrace_append hprefix tailTrace_217642
  have hstable : (prefixWord ++ tailWord_217642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217642).length < 2 ^ (prefixWord ++ tailWord_217642).sum := by decide
  have hdescent : baseEnd_217642 < baseStart_217642 := by decide
  rcases family_descends (prefixWord ++ tailWord_217642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217651 : List Nat := [1, 1, 1, 2, 4, 2, 1, 1, 5, 5]
def baseStart_217651 : Nat := 118140960795 + 217651 * 2 ^ 59
def prefixEnd_217651 : Nat := 4983230072969 + 3 ^ 40 * 217651 * 2
def baseEnd_217651 : Nat := 37253192643944391053849

theorem tailTrace_217651 : CollatzResearch.WordTrace tailWord_217651 prefixEnd_217651 37253192643944391053849 := by
  unfold tailWord_217651
  simp only [CollatzResearch.WordTrace]
  refine ⟨7938384134495073676508807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5292256089663382451005871 7938384134495073676508807)
  ·
    refine ⟨11907576201742610514763211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7938384134495073676508807 11907576201742610514763211)
    ·
      refine ⟨17861364302613915772144817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11907576201742610514763211 17861364302613915772144817)
      ·
        refine ⟨13396023226960436829108613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17861364302613915772144817 13396023226960436829108613)
        ·
          refine ⟨2511754355055081905457865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13396023226960436829108613 2511754355055081905457865)
          ·
            refine ⟨1883815766291311429093399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2511754355055081905457865 1883815766291311429093399)
            ·
              refine ⟨2825723649436967143640099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1883815766291311429093399 2825723649436967143640099)
              ·
                refine ⟨4238585474155450715460149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2825723649436967143640099 4238585474155450715460149)
                ·
                  refine ⟨397367388202073504574389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4238585474155450715460149 397367388202073504574389)
                  ·
                    refine ⟨37253192643944391053849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 397367388202073504574389 37253192643944391053849)
                    ·
                      rfl

theorem cell23_217651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 5, 5].length) (baseStart_217651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_217651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_217651 prefixEnd_217651 := by exact prefixLift 217651
  have htrace : WordTrace (prefixWord ++ tailWord_217651) baseStart_217651 baseEnd_217651 := by
    simpa [prefixWord, tailWord_217651, baseEnd_217651] using wordTrace_append hprefix tailTrace_217651
  have hstable : (prefixWord ++ tailWord_217651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217651).length < 2 ^ (prefixWord ++ tailWord_217651).sum := by decide
  have hdescent : baseEnd_217651 < baseStart_217651 := by decide
  rcases family_descends (prefixWord ++ tailWord_217651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217665 : List Nat := [1, 2, 5, 1, 1, 2, 1, 1, 5, 1, 3]
def baseStart_217665 : Nat := 118140960795 + 217665 * 2 ^ 59
def prefixEnd_217665 : Nat := 4983230072969 + 3 ^ 40 * 217665 * 2
def baseEnd_217665 : Nat := 111766766660996118386483

theorem tailTrace_217665 : CollatzResearch.WordTrace tailWord_217665 prefixEnd_217665 111766766660996118386483 := by
  unfold tailWord_217665
  simp only [CollatzResearch.WordTrace]
  refine ⟨7938894756444354067518449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5292596504296236045012299 7938894756444354067518449)
  ·
    refine ⟨5954171067333265550638837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7938894756444354067518449 5954171067333265550638837)
    ·
      refine ⟨558203537562493645372391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5954171067333265550638837 558203537562493645372391)
      ·
        refine ⟨837305306343740468058587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 558203537562493645372391 837305306343740468058587)
        ·
          refine ⟨1255957959515610702087881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 837305306343740468058587 1255957959515610702087881)
          ·
            refine ⟨941968469636708026565911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1255957959515610702087881 941968469636708026565911)
            ·
              refine ⟨1412952704455062039848867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 941968469636708026565911 1412952704455062039848867)
              ·
                refine ⟨2119429056682593059773301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1412952704455062039848867 2119429056682593059773301)
                ·
                  refine ⟨198696474063993099353747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2119429056682593059773301 198696474063993099353747)
                  ·
                    refine ⟨298044711095989649030621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 198696474063993099353747 298044711095989649030621)
                    ·
                      refine ⟨111766766660996118386483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 298044711095989649030621 111766766660996118386483)
                      ·
                        rfl

theorem cell23_217665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 1, 5, 1, 3].length) (baseStart_217665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_217665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_217665 prefixEnd_217665 := by exact prefixLift 217665
  have htrace : WordTrace (prefixWord ++ tailWord_217665) baseStart_217665 baseEnd_217665 := by
    simpa [prefixWord, tailWord_217665, baseEnd_217665] using wordTrace_append hprefix tailTrace_217665
  have hstable : (prefixWord ++ tailWord_217665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217665).length < 2 ^ (prefixWord ++ tailWord_217665).sum := by decide
  have hdescent : baseEnd_217665 < baseStart_217665 := by decide
  rcases family_descends (prefixWord ++ tailWord_217665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217675 : List Nat := [1, 1, 1, 1, 3, 1, 7, 1, 2, 3, 2]
def baseStart_217675 : Nat := 118140960795 + 217675 * 2 ^ 59
def prefixEnd_217675 : Nat := 4983230072969 + 3 ^ 40 * 217675 * 2
def baseEnd_217675 : Nat := 111771901467541079261437

theorem tailTrace_217675 : CollatzResearch.WordTrace tailWord_217675 prefixEnd_217675 111771901467541079261437 := by
  unfold tailWord_217675
  simp only [CollatzResearch.WordTrace]
  refine ⟨7939259486408125775382479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5292839657605417183588319 7939259486408125775382479)
  ·
    refine ⟨11908889229612188663073719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7939259486408125775382479 11908889229612188663073719)
    ·
      refine ⟨17863333844418282994610579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11908889229612188663073719 17863333844418282994610579)
      ·
        refine ⟨26795000766627424491915869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17863333844418282994610579 26795000766627424491915869)
        ·
          refine ⟨10048125287485284184468451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26795000766627424491915869 10048125287485284184468451)
          ·
            refine ⟨15072187931227926276702677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10048125287485284184468451 15072187931227926276702677)
            ·
              refine ⟨353254404638154522110219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 15072187931227926276702677 353254404638154522110219)
              ·
                refine ⟨529881606957231783165329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 353254404638154522110219 529881606957231783165329)
                ·
                  refine ⟨397411205217923837373997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 529881606957231783165329 397411205217923837373997)
                  ·
                    refine ⟨149029201956721439015249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 397411205217923837373997 149029201956721439015249)
                    ·
                      refine ⟨111771901467541079261437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 149029201956721439015249 111771901467541079261437)
                      ·
                        rfl

theorem cell23_217675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7, 1, 2, 3, 2].length) (baseStart_217675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_217675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_217675 prefixEnd_217675 := by exact prefixLift 217675
  have htrace : WordTrace (prefixWord ++ tailWord_217675) baseStart_217675 baseEnd_217675 := by
    simpa [prefixWord, tailWord_217675, baseEnd_217675] using wordTrace_append hprefix tailTrace_217675
  have hstable : (prefixWord ++ tailWord_217675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217675).length < 2 ^ (prefixWord ++ tailWord_217675).sum := by decide
  have hdescent : baseEnd_217675 < baseStart_217675 := by decide
  rcases family_descends (prefixWord ++ tailWord_217675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217685 : List Nat := [1, 3, 2, 2, 1, 1, 6, 1, 1, 5]
def baseStart_217685 : Nat := 118140960795 + 217685 * 2 ^ 59
def prefixEnd_217685 : Nat := 4983230072969 + 3 ^ 40 * 217685 * 2
def baseEnd_217685 : Nat := 37259012091362013378797

theorem tailTrace_217685 : CollatzResearch.WordTrace tailWord_217685 prefixEnd_217685 37259012091362013378797 := by
  unfold tailWord_217685
  simp only [CollatzResearch.WordTrace]
  refine ⟨7939624216371897483246509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5293082810914598322164339 7939624216371897483246509)
  ·
    refine ⟨2977359081139461556217441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7939624216371897483246509 2977359081139461556217441)
    ·
      refine ⟨2233019310854596167163081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2977359081139461556217441 2233019310854596167163081)
      ·
        refine ⟨1674764483140947125372311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2233019310854596167163081 1674764483140947125372311)
        ·
          refine ⟨2512146724711420688058467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1674764483140947125372311 2512146724711420688058467)
          ·
            refine ⟨3768220087067131032087701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2512146724711420688058467 3768220087067131032087701)
            ·
              refine ⟨176635316581271767129111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3768220087067131032087701 176635316581271767129111)
              ·
                refine ⟨264952974871907650693667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 176635316581271767129111 264952974871907650693667)
                ·
                  refine ⟨397429462307861476040501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 264952974871907650693667 397429462307861476040501)
                  ·
                    refine ⟨37259012091362013378797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 397429462307861476040501 37259012091362013378797)
                    ·
                      rfl

theorem cell23_217685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 6, 1, 1, 5].length) (baseStart_217685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_217685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_217685 prefixEnd_217685 := by exact prefixLift 217685
  have htrace : WordTrace (prefixWord ++ tailWord_217685) baseStart_217685 baseEnd_217685 := by
    simpa [prefixWord, tailWord_217685, baseEnd_217685] using wordTrace_append hprefix tailTrace_217685
  have hstable : (prefixWord ++ tailWord_217685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217685).length < 2 ^ (prefixWord ++ tailWord_217685).sum := by decide
  have hdescent : baseEnd_217685 < baseStart_217685 := by decide
  rcases family_descends (prefixWord ++ tailWord_217685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217708 : List Nat := [2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 3]
def baseStart_217708 : Nat := 118140960795 + 217708 * 2 ^ 59
def prefixEnd_217708 : Nat := 4983230072969 + 3 ^ 40 * 217708 * 2
def baseEnd_217708 : Nat := 111788846329139450148785

theorem tailTrace_217708 : CollatzResearch.WordTrace tailWord_217708 prefixEnd_217708 111788846329139450148785 := by
  unfold tailWord_217708
  simp only [CollatzResearch.WordTrace]
  refine ⟨3970231547644286205666889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5293642063525714940889185 3970231547644286205666889)
  ·
    refine ⟨2977673660733214654250167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3970231547644286205666889 2977673660733214654250167)
    ·
      refine ⟨4466510491099821981375251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2977673660733214654250167 4466510491099821981375251)
      ·
        refine ⟨6699765736649732972062877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4466510491099821981375251 6699765736649732972062877)
        ·
          refine ⟨2512412151243649864523579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6699765736649732972062877 2512412151243649864523579)
          ·
            refine ⟨3768618226865474796785369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2512412151243649864523579 3768618226865474796785369)
            ·
              refine ⟨2826463670149106097589027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3768618226865474796785369 2826463670149106097589027)
              ·
                refine ⟨4239695505223659146383541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2826463670149106097589027 4239695505223659146383541)
                ·
                  refine ⟨397471453614718044973457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4239695505223659146383541 397471453614718044973457)
                  ·
                    refine ⟨298103590211038533730093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 397471453614718044973457 298103590211038533730093)
                    ·
                      refine ⟨111788846329139450148785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 298103590211038533730093 111788846329139450148785)
                      ·
                        rfl

theorem cell23_217708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 3].length) (baseStart_217708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_217708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_217708 prefixEnd_217708 := by exact prefixLift 217708
  have htrace : WordTrace (prefixWord ++ tailWord_217708) baseStart_217708 baseEnd_217708 := by
    simpa [prefixWord, tailWord_217708, baseEnd_217708] using wordTrace_append hprefix tailTrace_217708
  have hstable : (prefixWord ++ tailWord_217708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217708).length < 2 ^ (prefixWord ++ tailWord_217708).sum := by decide
  have hdescent : baseEnd_217708 < baseStart_217708 := by decide
  rcases family_descends (prefixWord ++ tailWord_217708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217728 : List Nat := [2, 1, 1, 2, 1, 5, 4, 7]
def baseStart_217728 : Nat := 118140960795 + 217728 * 2 ^ 59
def prefixEnd_217728 : Nat := 4983230072969 + 3 ^ 40 * 217728 * 2
def baseEnd_217728 : Nat := 4140707997860347107359

theorem tailTrace_217728 : CollatzResearch.WordTrace tailWord_217728 prefixEnd_217728 4140707997860347107359 := by
  unfold tailWord_217728
  simp only [CollatzResearch.WordTrace]
  refine ⟨3970596277608057913530919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5294128370144077218041225 3970596277608057913530919)
  ·
    refine ⟨5955894416412086870296379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3970596277608057913530919 5955894416412086870296379)
    ·
      refine ⟨8933841624618130305444569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5955894416412086870296379 8933841624618130305444569)
      ·
        refine ⟨6700381218463597729083427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8933841624618130305444569 6700381218463597729083427)
        ·
          refine ⟨10050571827695396593625141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6700381218463597729083427 10050571827695396593625141)
          ·
            refine ⟨942241108846443430652357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10050571827695396593625141 942241108846443430652357)
            ·
              refine ⟨176670207908708143247317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 942241108846443430652357 176670207908708143247317)
              ·
                refine ⟨4140707997860347107359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 176670207908708143247317 4140707997860347107359)
                ·
                  rfl

theorem cell23_217728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 4, 7].length) (baseStart_217728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_217728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_217728 prefixEnd_217728 := by exact prefixLift 217728
  have htrace : WordTrace (prefixWord ++ tailWord_217728) baseStart_217728 baseEnd_217728 := by
    simpa [prefixWord, tailWord_217728, baseEnd_217728] using wordTrace_append hprefix tailTrace_217728
  have hstable : (prefixWord ++ tailWord_217728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217728).length < 2 ^ (prefixWord ++ tailWord_217728).sum := by decide
  have hdescent : baseEnd_217728 < baseStart_217728 := by decide
  rcases family_descends (prefixWord ++ tailWord_217728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217765 : List Nat := [1, 3, 1, 2, 1, 2, 1, 4, 3, 3, 2]
def baseStart_217765 : Nat := 118140960795 + 217765 * 2 ^ 59
def prefixEnd_217765 : Nat := 4983230072969 + 3 ^ 40 * 217765 * 2
def baseEnd_217765 : Nat := 111818114726445727136023

theorem tailTrace_217765 : CollatzResearch.WordTrace tailWord_217765 prefixEnd_217765 111818114726445727136023 := by
  unfold tailWord_217765
  simp only [CollatzResearch.WordTrace]
  refine ⟨7942542056082071146158749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5295028037388047430772499 7942542056082071146158749)
  ·
    refine ⟨2978453271030776679809531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7942542056082071146158749 2978453271030776679809531)
    ·
      refine ⟨4467679906546165019714297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2978453271030776679809531 4467679906546165019714297)
      ·
        refine ⟨3350759929909623764785723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4467679906546165019714297 3350759929909623764785723)
        ·
          refine ⟨5026139894864435647178585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3350759929909623764785723 5026139894864435647178585)
          ·
            refine ⟨3769604921148326735383939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5026139894864435647178585 3769604921148326735383939)
            ·
              refine ⟨5654407381722490103075909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3769604921148326735383939 5654407381722490103075909)
              ·
                refine ⟨1060201384072966894326733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5654407381722490103075909 1060201384072966894326733)
                ·
                  refine ⟨397575519027362585372525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1060201384072966894326733 397575519027362585372525)
                  ·
                    refine ⟨149090819635260969514697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 397575519027362585372525 149090819635260969514697)
                    ·
                      refine ⟨111818114726445727136023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 149090819635260969514697 111818114726445727136023)
                      ·
                        rfl

theorem cell23_217765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 4, 3, 3, 2].length) (baseStart_217765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_217765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_217765 prefixEnd_217765 := by exact prefixLift 217765
  have htrace : WordTrace (prefixWord ++ tailWord_217765) baseStart_217765 baseEnd_217765 := by
    simpa [prefixWord, tailWord_217765, baseEnd_217765] using wordTrace_append hprefix tailTrace_217765
  have hstable : (prefixWord ++ tailWord_217765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217765).length < 2 ^ (prefixWord ++ tailWord_217765).sum := by decide
  have hdescent : baseEnd_217765 < baseStart_217765 := by decide
  rcases family_descends (prefixWord ++ tailWord_217765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217818 : List Nat := [3, 1, 1, 2, 2, 2, 2, 3, 7]
def baseStart_217818 : Nat := 118140960795 + 217818 * 2 ^ 59
def prefixEnd_217818 : Nat := 4983230072969 + 3 ^ 40 * 217818 * 2
def baseEnd_217818 : Nat := 12427258800126002197031

theorem tailTrace_217818 : CollatzResearch.WordTrace tailWord_217818 prefixEnd_217818 12427258800126002197031 := by
  unfold tailWord_217818
  simp only [CollatzResearch.WordTrace]
  refine ⟨1986118781222515299459527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5296316749926707465225405 1986118781222515299459527)
  ·
    refine ⟨2979178171833772949189291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1986118781222515299459527 2979178171833772949189291)
    ·
      refine ⟨4468767257750659423783937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2979178171833772949189291 4468767257750659423783937)
      ·
        refine ⟨3351575443312994567837953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4468767257750659423783937 3351575443312994567837953)
        ·
          refine ⟨2513681582484745925878465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3351575443312994567837953 2513681582484745925878465)
          ·
            refine ⟨1885261186863559444408849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2513681582484745925878465 1885261186863559444408849)
            ·
              refine ⟨1413945890147669583306637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1885261186863559444408849 1413945890147669583306637)
              ·
                refine ⟨530229708805376093739989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1413945890147669583306637 530229708805376093739989)
                ·
                  refine ⟨12427258800126002197031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 530229708805376093739989 12427258800126002197031)
                  ·
                    rfl

theorem cell23_217818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 3, 7].length) (baseStart_217818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_217818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_217818 prefixEnd_217818 := by exact prefixLift 217818
  have htrace : WordTrace (prefixWord ++ tailWord_217818) baseStart_217818 baseEnd_217818 := by
    simpa [prefixWord, tailWord_217818, baseEnd_217818] using wordTrace_append hprefix tailTrace_217818
  have hstable : (prefixWord ++ tailWord_217818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217818).length < 2 ^ (prefixWord ++ tailWord_217818).sum := by decide
  have hdescent : baseEnd_217818 < baseStart_217818 := by decide
  rcases family_descends (prefixWord ++ tailWord_217818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217825 : List Nat := [1, 2, 3, 1, 4, 2, 1, 1, 2, 2, 4]
def baseStart_217825 : Nat := 118140960795 + 217825 * 2 ^ 59
def prefixEnd_217825 : Nat := 4983230072969 + 3 ^ 40 * 217825 * 2
def baseEnd_217825 : Nat := 111848923565715492385747

theorem tailTrace_217825 : CollatzResearch.WordTrace tailWord_217825 prefixEnd_217825 111848923565715492385747 := by
  unfold tailWord_217825
  simp only [CollatzResearch.WordTrace]
  refine ⟨7944730435864701393342929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5296486957243134262228619 7944730435864701393342929)
  ·
    refine ⟨5958547826898526045007197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7944730435864701393342929 5958547826898526045007197)
    ·
      refine ⟨2234455435086947266877699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5958547826898526045007197 2234455435086947266877699)
      ·
        refine ⟨3351683152630420900316549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2234455435086947266877699 3351683152630420900316549)
        ·
          refine ⟨628440591118203918809353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3351683152630420900316549 628440591118203918809353)
          ·
            refine ⟨471330443338652939107015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 628440591118203918809353 471330443338652939107015)
            ·
              refine ⟨706995665007979408660523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 471330443338652939107015 706995665007979408660523)
              ·
                refine ⟨1060493497511969112990785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 706995665007979408660523 1060493497511969112990785)
                ·
                  refine ⟨795370123133976834743089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1060493497511969112990785 795370123133976834743089)
                  ·
                    refine ⟨596527592350482626057317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 795370123133976834743089 596527592350482626057317)
                    ·
                      refine ⟨111848923565715492385747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 596527592350482626057317 111848923565715492385747)
                      ·
                        rfl

theorem cell23_217825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 1, 2, 2, 4].length) (baseStart_217825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_217825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_217825 prefixEnd_217825 := by exact prefixLift 217825
  have htrace : WordTrace (prefixWord ++ tailWord_217825) baseStart_217825 baseEnd_217825 := by
    simpa [prefixWord, tailWord_217825, baseEnd_217825] using wordTrace_append hprefix tailTrace_217825
  have hstable : (prefixWord ++ tailWord_217825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217825).length < 2 ^ (prefixWord ++ tailWord_217825).sum := by decide
  have hdescent : baseEnd_217825 < baseStart_217825 := by decide
  rcases family_descends (prefixWord ++ tailWord_217825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217829 : List Nat := [1, 3, 1, 4, 1, 2, 2, 3, 2, 2, 2]
def baseStart_217829 : Nat := 118140960795 + 217829 * 2 ^ 59
def prefixEnd_217829 : Nat := 4983230072969 + 3 ^ 40 * 217829 * 2
def baseEnd_217829 : Nat := 111850977488333476735729

theorem tailTrace_217829 : CollatzResearch.WordTrace tailWord_217829 prefixEnd_217829 111850977488333476735729 := by
  unfold tailWord_217829
  simp only [CollatzResearch.WordTrace]
  refine ⟨7944876327850210076488541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5296584218566806717659027 7944876327850210076488541)
  ·
    refine ⟨2979328622943828778683203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7944876327850210076488541 2979328622943828778683203)
    ·
      refine ⟨4468992934415743168024805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2979328622943828778683203 4468992934415743168024805)
      ·
        refine ⟨837936175202951844004651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4468992934415743168024805 837936175202951844004651)
        ·
          refine ⟨1256904262804427766006977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 837936175202951844004651 1256904262804427766006977)
          ·
            refine ⟨942678197103320824505233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1256904262804427766006977 942678197103320824505233)
            ·
              refine ⟨707008647827490618378925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 942678197103320824505233 707008647827490618378925)
              ·
                refine ⟨265128242935308981892097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 707008647827490618378925 265128242935308981892097)
                ·
                  refine ⟨198846182201481736419073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 265128242935308981892097 198846182201481736419073)
                  ·
                    refine ⟨149134636651111302314305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 198846182201481736419073 149134636651111302314305)
                    ·
                      refine ⟨111850977488333476735729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 149134636651111302314305 111850977488333476735729)
                      ·
                        rfl

theorem cell23_217829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 3, 2, 2, 2].length) (baseStart_217829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_217829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_217829 prefixEnd_217829 := by exact prefixLift 217829
  have htrace : WordTrace (prefixWord ++ tailWord_217829) baseStart_217829 baseEnd_217829 := by
    simpa [prefixWord, tailWord_217829, baseEnd_217829] using wordTrace_append hprefix tailTrace_217829
  have hstable : (prefixWord ++ tailWord_217829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217829).length < 2 ^ (prefixWord ++ tailWord_217829).sum := by decide
  have hdescent : baseEnd_217829 < baseStart_217829 := by decide
  rcases family_descends (prefixWord ++ tailWord_217829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217848 : List Nat := [2, 1, 2, 1, 1, 2, 5, 1, 1, 7]
def baseStart_217848 : Nat := 118140960795 + 217848 * 2 ^ 59
def prefixEnd_217848 : Nat := 4983230072969 + 3 ^ 40 * 217848 * 2
def baseEnd_217848 : Nat := 37286911206922967466047

theorem tailTrace_217848 : CollatzResearch.WordTrace tailWord_217848 prefixEnd_217848 37286911206922967466047 := by
  unfold tailWord_217848
  simp only [CollatzResearch.WordTrace]
  refine ⟨3972784657390688160715099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5297046209854250880953465 3972784657390688160715099)
  ·
    refine ⟨5959176986086032241072649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3972784657390688160715099 5959176986086032241072649)
    ·
      refine ⟨4469382739564524180804487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5959176986086032241072649 4469382739564524180804487)
      ·
        refine ⟨6704074109346786271206731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4469382739564524180804487 6704074109346786271206731)
        ·
          refine ⟨10056111164020179406810097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6704074109346786271206731 10056111164020179406810097)
          ·
            refine ⟨7542083373015134555107573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10056111164020179406810097 7542083373015134555107573)
            ·
              refine ⟨707070316220168864541335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7542083373015134555107573 707070316220168864541335)
              ·
                refine ⟨1060605474330253296812003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 707070316220168864541335 1060605474330253296812003)
                ·
                  refine ⟨1590908211495379945218005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1060605474330253296812003 1590908211495379945218005)
                  ·
                    refine ⟨37286911206922967466047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1590908211495379945218005 37286911206922967466047)
                    ·
                      rfl

theorem cell23_217848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 1, 1, 7].length) (baseStart_217848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_217848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_217848 prefixEnd_217848 := by exact prefixLift 217848
  have htrace : WordTrace (prefixWord ++ tailWord_217848) baseStart_217848 baseEnd_217848 := by
    simpa [prefixWord, tailWord_217848, baseEnd_217848] using wordTrace_append hprefix tailTrace_217848
  have hstable : (prefixWord ++ tailWord_217848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217848).length < 2 ^ (prefixWord ++ tailWord_217848).sum := by decide
  have hdescent : baseEnd_217848 < baseStart_217848 := by decide
  rcases family_descends (prefixWord ++ tailWord_217848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217852 : List Nat := [2, 2, 2, 1, 3, 3, 2, 3, 5]
def baseStart_217852 : Nat := 118140960795 + 217852 * 2 ^ 59
def prefixEnd_217852 : Nat := 4983230072969 + 3 ^ 40 * 217852 * 2
def baseEnd_217852 : Nat := 12429198615931876305347

theorem tailTrace_217852 : CollatzResearch.WordTrace tailWord_217852 prefixEnd_217852 12429198615931876305347 := by
  unfold tailWord_217852
  simp only [CollatzResearch.WordTrace]
  refine ⟨3972857603383442502287905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5297143471177923336383873 3972857603383442502287905)
  ·
    refine ⟨2979643202537581876715929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3972857603383442502287905 2979643202537581876715929)
    ·
      refine ⟨2234732401903186407536947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2979643202537581876715929 2234732401903186407536947)
      ·
        refine ⟨3352098602854779611305421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2234732401903186407536947 3352098602854779611305421)
        ·
          refine ⟨1257036976070542354239533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3352098602854779611305421 1257036976070542354239533)
          ·
            refine ⟨471388866026453382839825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1257036976070542354239533 471388866026453382839825)
            ·
              refine ⟨353541649519840037129869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 471388866026453382839825 353541649519840037129869)
              ·
                refine ⟨132578118569940013923701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 353541649519840037129869 132578118569940013923701)
                ·
                  refine ⟨12429198615931876305347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 132578118569940013923701 12429198615931876305347)
                  ·
                    rfl

theorem cell23_217852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2, 3, 5].length) (baseStart_217852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_217852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_217852 prefixEnd_217852 := by exact prefixLift 217852
  have htrace : WordTrace (prefixWord ++ tailWord_217852) baseStart_217852 baseEnd_217852 := by
    simpa [prefixWord, tailWord_217852, baseEnd_217852] using wordTrace_append hprefix tailTrace_217852
  have hstable : (prefixWord ++ tailWord_217852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217852).length < 2 ^ (prefixWord ++ tailWord_217852).sum := by decide
  have hdescent : baseEnd_217852 < baseStart_217852 := by decide
  rcases family_descends (prefixWord ++ tailWord_217852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217902 : List Nat := [4, 1, 3, 2, 1, 1, 2, 1, 1, 3, 4]
def baseStart_217902 : Nat := 118140960795 + 217902 * 2 ^ 59
def prefixEnd_217902 : Nat := 4983230072969 + 3 ^ 40 * 217902 * 2
def baseEnd_217902 : Nat := 111888461576111691122893

theorem tailTrace_217902 : CollatzResearch.WordTrace tailWord_217902 prefixEnd_217902 111888461576111691122893 := by
  unfold tailWord_217902
  simp only [CollatzResearch.WordTrace]
  refine ⟨993442357073217942986995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5298359237723829029263973 993442357073217942986995)
  ·
    refine ⟨1490163535609826914480493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 993442357073217942986995 1490163535609826914480493)
    ·
      refine ⟨558811325853685092930185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1490163535609826914480493 558811325853685092930185)
      ·
        refine ⟨419108494390263819697639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 558811325853685092930185 419108494390263819697639)
        ·
          refine ⟨628662741585395729546459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 419108494390263819697639 628662741585395729546459)
          ·
            refine ⟨942994112378093594319689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 628662741585395729546459 942994112378093594319689)
            ·
              refine ⟨707245584283570195739767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 942994112378093594319689 707245584283570195739767)
              ·
                refine ⟨1060868376425355293609651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 707245584283570195739767 1060868376425355293609651)
                ·
                  refine ⟨1591302564638032940414477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1060868376425355293609651 1591302564638032940414477)
                  ·
                    refine ⟨596738461739262352655429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1591302564638032940414477 596738461739262352655429)
                    ·
                      refine ⟨111888461576111691122893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 596738461739262352655429 111888461576111691122893)
                      ·
                        rfl

theorem cell23_217902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_217902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_217902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_217902 prefixEnd_217902 := by exact prefixLift 217902
  have htrace : WordTrace (prefixWord ++ tailWord_217902) baseStart_217902 baseEnd_217902 := by
    simpa [prefixWord, tailWord_217902, baseEnd_217902] using wordTrace_append hprefix tailTrace_217902
  have hstable : (prefixWord ++ tailWord_217902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217902).length < 2 ^ (prefixWord ++ tailWord_217902).sum := by decide
  have hdescent : baseEnd_217902 < baseStart_217902 := by decide
  rcases family_descends (prefixWord ++ tailWord_217902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217905 : List Nat := [1, 2, 2, 3, 2, 1, 1, 3, 1, 4, 3]
def baseStart_217905 : Nat := 118140960795 + 217905 * 2 ^ 59
def prefixEnd_217905 : Nat := 4983230072969 + 3 ^ 40 * 217905 * 2
def baseEnd_217905 : Nat := 111890002018075179385379

theorem tailTrace_217905 : CollatzResearch.WordTrace tailWord_217905 prefixEnd_217905 111890002018075179385379 := by
  unfold tailWord_217905
  simp only [CollatzResearch.WordTrace]
  refine ⟨7947648275574875056255169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5298432183716583370836779 7947648275574875056255169)
  ·
    refine ⟨5960736206681156292191377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7947648275574875056255169 5960736206681156292191377)
    ·
      refine ⟨4470552155010867219143533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5960736206681156292191377 4470552155010867219143533)
      ·
        refine ⟨1676457058129075207178825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4470552155010867219143533 1676457058129075207178825)
        ·
          refine ⟨1257342793596806405384119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1676457058129075207178825 1257342793596806405384119)
          ·
            refine ⟨1886014190395209608076179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1257342793596806405384119 1886014190395209608076179)
            ·
              refine ⟨2829021285592814412114269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1886014190395209608076179 2829021285592814412114269)
              ·
                refine ⟨1060882982097305404542851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2829021285592814412114269 1060882982097305404542851)
                ·
                  refine ⟨1591324473145958106814277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1060882982097305404542851 1591324473145958106814277)
                  ·
                    refine ⟨298373338714867145027677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1591324473145958106814277 298373338714867145027677)
                    ·
                      refine ⟨111890002018075179385379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 298373338714867145027677 111890002018075179385379)
                      ·
                        rfl

theorem cell23_217905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 3, 1, 4, 3].length) (baseStart_217905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_217905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_217905 prefixEnd_217905 := by exact prefixLift 217905
  have htrace : WordTrace (prefixWord ++ tailWord_217905) baseStart_217905 baseEnd_217905 := by
    simpa [prefixWord, tailWord_217905, baseEnd_217905] using wordTrace_append hprefix tailTrace_217905
  have hstable : (prefixWord ++ tailWord_217905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217905).length < 2 ^ (prefixWord ++ tailWord_217905).sum := by decide
  have hdescent : baseEnd_217905 < baseStart_217905 := by decide
  rcases family_descends (prefixWord ++ tailWord_217905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217952 : List Nat := [2, 1, 1, 3, 3, 1, 2, 1, 5, 1, 3]
def baseStart_217952 : Nat := 118140960795 + 217952 * 2 ^ 59
def prefixEnd_217952 : Nat := 4983230072969 + 3 ^ 40 * 217952 * 2
def baseEnd_217952 : Nat := 111914135608836495497663

theorem tailTrace_217952 : CollatzResearch.WordTrace tailWord_217952 prefixEnd_217952 111914135608836495497663 := by
  unfold tailWord_217952
  simp only [CollatzResearch.WordTrace]
  refine ⟨3974681253202301041608055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5299575004269734722144073 3974681253202301041608055)
  ·
    refine ⟨5962021879803451562412083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3974681253202301041608055 5962021879803451562412083)
    ·
      refine ⟨8943032819705177343618125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5962021879803451562412083 8943032819705177343618125)
      ·
        refine ⟨3353637307389441503856797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8943032819705177343618125 3353637307389441503856797)
        ·
          refine ⟨1257613990271040563946299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3353637307389441503856797 1257613990271040563946299)
          ·
            refine ⟨1886420985406560845919449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1257613990271040563946299 1886420985406560845919449)
            ·
              refine ⟨1414815739054920634439587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1886420985406560845919449 1414815739054920634439587)
              ·
                refine ⟨2122223608582380951659381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1414815739054920634439587 2122223608582380951659381)
                ·
                  refine ⟨198958463304598214218067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2122223608582380951659381 198958463304598214218067)
                  ·
                    refine ⟨298437694956897321327101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 198958463304598214218067 298437694956897321327101)
                    ·
                      refine ⟨111914135608836495497663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 298437694956897321327101 111914135608836495497663)
                      ·
                        rfl

theorem cell23_217952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 1, 5, 1, 3].length) (baseStart_217952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_217952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_217952 prefixEnd_217952 := by exact prefixLift 217952
  have htrace : WordTrace (prefixWord ++ tailWord_217952) baseStart_217952 baseEnd_217952 := by
    simpa [prefixWord, tailWord_217952, baseEnd_217952] using wordTrace_append hprefix tailTrace_217952
  have hstable : (prefixWord ++ tailWord_217952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217952).length < 2 ^ (prefixWord ++ tailWord_217952).sum := by decide
  have hdescent : baseEnd_217952 < baseStart_217952 := by decide
  rcases family_descends (prefixWord ++ tailWord_217952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217992 : List Nat := [2, 1, 3, 3, 2, 1, 1, 2, 3, 1, 4]
def baseStart_217992 : Nat := 118140960795 + 217992 * 2 ^ 59
def prefixEnd_217992 : Nat := 4983230072969 + 3 ^ 40 * 217992 * 2
def baseEnd_217992 : Nat := 111934674835016338997479

theorem tailTrace_217992 : CollatzResearch.WordTrace tailWord_217992 prefixEnd_217992 111934674835016338997479 := by
  unfold tailWord_217992
  simp only [CollatzResearch.WordTrace]
  refine ⟨3975410713129844457336115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5300547617506459276448153 3975410713129844457336115)
  ·
    refine ⟨5963116069694766686004173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3975410713129844457336115 5963116069694766686004173)
    ·
      refine ⟨2236168526135537507251565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5963116069694766686004173 2236168526135537507251565)
      ·
        refine ⟨838563197300826565219337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2236168526135537507251565 838563197300826565219337)
        ·
          refine ⟨628922397975619923914503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 838563197300826565219337 628922397975619923914503)
          ·
            refine ⟨943383596963429885871755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 628922397975619923914503 943383596963429885871755)
            ·
              refine ⟨1415075395445144828807633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 943383596963429885871755 1415075395445144828807633)
              ·
                refine ⟨1061306546583858621605725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1415075395445144828807633 1061306546583858621605725)
                ·
                  refine ⟨397989954968946983102147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1061306546583858621605725 397989954968946983102147)
                  ·
                    refine ⟨596984932453420474653221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 397989954968946983102147 596984932453420474653221)
                    ·
                      refine ⟨111934674835016338997479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 596984932453420474653221 111934674835016338997479)
                      ·
                        rfl

theorem cell23_217992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_217992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_217992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_217992 prefixEnd_217992 := by exact prefixLift 217992
  have htrace : WordTrace (prefixWord ++ tailWord_217992) baseStart_217992 baseEnd_217992 := by
    simpa [prefixWord, tailWord_217992, baseEnd_217992] using wordTrace_append hprefix tailTrace_217992
  have hstable : (prefixWord ++ tailWord_217992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217992).length < 2 ^ (prefixWord ++ tailWord_217992).sum := by decide
  have hdescent : baseEnd_217992 < baseStart_217992 := by decide
  rcases family_descends (prefixWord ++ tailWord_217992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217995 : List Nat := [1, 1, 1, 1, 4, 2, 2, 4, 1, 1, 5]
def baseStart_217995 : Nat := 118140960795 + 217995 * 2 ^ 59
def prefixEnd_217995 : Nat := 4983230072969 + 3 ^ 40 * 217995 * 2
def baseEnd_217995 : Nat := 111936215276979827259965

theorem tailTrace_217995 : CollatzResearch.WordTrace tailWord_217995 prefixEnd_217995 111936215276979827259965 := by
  unfold tailWord_217995
  simp only [CollatzResearch.WordTrace]
  refine ⟨7950930845248820427031439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5300620563499213618020959 7950930845248820427031439)
  ·
    refine ⟨11926396267873230640547159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7950930845248820427031439 11926396267873230640547159)
    ·
      refine ⟨17889594401809845960820739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11926396267873230640547159 17889594401809845960820739)
      ·
        refine ⟨26834391602714768941231109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17889594401809845960820739 26834391602714768941231109)
        ·
          refine ⟨5031448425509019176480833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26834391602714768941231109 5031448425509019176480833)
          ·
            refine ⟨3773586319131764382360625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5031448425509019176480833 3773586319131764382360625)
            ·
              refine ⟨2830189739348823286770469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3773586319131764382360625 2830189739348823286770469)
              ·
                refine ⟨530660576127904366269463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2830189739348823286770469 530660576127904366269463)
                ·
                  refine ⟨795990864191856549404195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 530660576127904366269463 795990864191856549404195)
                  ·
                    refine ⟨1193986296287784824106293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 795990864191856549404195 1193986296287784824106293)
                    ·
                      refine ⟨111936215276979827259965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1193986296287784824106293 111936215276979827259965)
                      ·
                        rfl

theorem cell23_217995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 4, 1, 1, 5].length) (baseStart_217995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_217995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_217995 prefixEnd_217995 := by exact prefixLift 217995
  have htrace : WordTrace (prefixWord ++ tailWord_217995) baseStart_217995 baseEnd_217995 := by
    simpa [prefixWord, tailWord_217995, baseEnd_217995] using wordTrace_append hprefix tailTrace_217995
  have hstable : (prefixWord ++ tailWord_217995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217995).length < 2 ^ (prefixWord ++ tailWord_217995).sum := by decide
  have hdescent : baseEnd_217995 < baseStart_217995 := by decide
  rcases family_descends (prefixWord ++ tailWord_217995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218006 : List Nat := [5, 3, 1, 1, 1, 1, 2, 1, 3, 5]
def baseStart_218006 : Nat := 118140960795 + 218006 * 2 ^ 59
def prefixEnd_218006 : Nat := 4983230072969 + 3 ^ 40 * 218006 * 2
def baseEnd_218006 : Nat := 37313954521393094740805

theorem tailTrace_218006 : CollatzResearch.WordTrace tailWord_218006 prefixEnd_218006 37313954521393094740805 := by
  unfold tailWord_218006
  simp only [CollatzResearch.WordTrace]
  refine ⟨496958253013060581605117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5300888032139312870454581 496958253013060581605117)
  ·
    refine ⟨186359344879897718101919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 496958253013060581605117 186359344879897718101919)
    ·
      refine ⟨279539017319846577152879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186359344879897718101919 279539017319846577152879)
      ·
        refine ⟨419308525979769865729319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279539017319846577152879 419308525979769865729319)
        ·
          refine ⟨628962788969654798593979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 419308525979769865729319 628962788969654798593979)
          ·
            refine ⟨943444183454482197890969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 628962788969654798593979 943444183454482197890969)
            ·
              refine ⟨707583137590861648418227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 943444183454482197890969 707583137590861648418227)
              ·
                refine ⟨1061374706386292472627341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 707583137590861648418227 1061374706386292472627341)
                ·
                  refine ⟨398015514894859677235253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1061374706386292472627341 398015514894859677235253)
                  ·
                    refine ⟨37313954521393094740805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 398015514894859677235253 37313954521393094740805)
                    ·
                      rfl

theorem cell23_218006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_218006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_218006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_218006 prefixEnd_218006 := by exact prefixLift 218006
  have htrace : WordTrace (prefixWord ++ tailWord_218006) baseStart_218006 baseEnd_218006 := by
    simpa [prefixWord, tailWord_218006, baseEnd_218006] using wordTrace_append hprefix tailTrace_218006
  have hstable : (prefixWord ++ tailWord_218006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218006).length < 2 ^ (prefixWord ++ tailWord_218006).sum := by decide
  have hdescent : baseEnd_218006 < baseStart_218006 := by decide
  rcases family_descends (prefixWord ++ tailWord_218006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218023 : List Nat := [1, 1, 6, 1, 4, 1, 2, 1, 1, 5]
def baseStart_218023 : Nat := 118140960795 + 218023 * 2 ^ 59
def prefixEnd_218023 : Nat := 4983230072969 + 3 ^ 40 * 218023 * 2
def baseEnd_218023 : Nat := 37316864245101905903279

theorem tailTrace_218023 : CollatzResearch.WordTrace tailWord_218023 prefixEnd_218023 37316864245101905903279 := by
  unfold tailWord_218023
  simp only [CollatzResearch.WordTrace]
  refine ⟨7951952089147381209050723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5301301392764920806033815 7951952089147381209050723)
  ·
    refine ⟨11927928133721071813576085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7951952089147381209050723 11927928133721071813576085)
    ·
      refine ⟨559121631268175241261379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 11927928133721071813576085 559121631268175241261379)
      ·
        refine ⟨838682446902262861892069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 559121631268175241261379 838682446902262861892069)
        ·
          refine ⟨157252958794174286604763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 838682446902262861892069 157252958794174286604763)
          ·
            refine ⟨235879438191261429907145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157252958794174286604763 235879438191261429907145)
            ·
              refine ⟨176909578643446072430359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 235879438191261429907145 176909578643446072430359)
              ·
                refine ⟨265364367965169108645539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 176909578643446072430359 265364367965169108645539)
                ·
                  refine ⟨398046551947753662968309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 265364367965169108645539 398046551947753662968309)
                  ·
                    refine ⟨37316864245101905903279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 398046551947753662968309 37316864245101905903279)
                    ·
                      rfl

theorem cell23_218023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 2, 1, 1, 5].length) (baseStart_218023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_218023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_218023 prefixEnd_218023 := by exact prefixLift 218023
  have htrace : WordTrace (prefixWord ++ tailWord_218023) baseStart_218023 baseEnd_218023 := by
    simpa [prefixWord, tailWord_218023, baseEnd_218023] using wordTrace_append hprefix tailTrace_218023
  have hstable : (prefixWord ++ tailWord_218023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218023).length < 2 ^ (prefixWord ++ tailWord_218023).sum := by decide
  have hdescent : baseEnd_218023 < baseStart_218023 := by decide
  rcases family_descends (prefixWord ++ tailWord_218023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218036 : List Nat := [2, 5, 2, 1, 1, 2, 1, 1, 4, 4]
def baseStart_218036 : Nat := 118140960795 + 218036 * 2 ^ 59
def prefixEnd_218036 : Nat := 4983230072969 + 3 ^ 40 * 218036 * 2
def baseEnd_218036 : Nat := 37319089327938055615759

theorem tailTrace_218036 : CollatzResearch.WordTrace tailWord_218036 prefixEnd_218036 37319089327938055615759 := by
  unfold tailWord_218036
  simp only [CollatzResearch.WordTrace]
  refine ⟨3976213119050142214636981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5301617492066856286182641 3976213119050142214636981)
  ·
    refine ⟨372769979910950832622217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3976213119050142214636981 372769979910950832622217)
    ·
      refine ⟨279577484933213124466663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 372769979910950832622217 279577484933213124466663)
      ·
        refine ⟨419366227399819686699995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279577484933213124466663 419366227399819686699995)
        ·
          refine ⟨629049341099729530049993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 419366227399819686699995 629049341099729530049993)
          ·
            refine ⟨471787005824797147537495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 629049341099729530049993 471787005824797147537495)
            ·
              refine ⟨707680508737195721306243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 471787005824797147537495 707680508737195721306243)
              ·
                refine ⟨1061520763105793581959365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 707680508737195721306243 1061520763105793581959365)
                ·
                  refine ⟨199035143082336296617381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1061520763105793581959365 199035143082336296617381)
                  ·
                    refine ⟨37319089327938055615759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 199035143082336296617381 37319089327938055615759)
                    ·
                      rfl

theorem cell23_218036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_218036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_218036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_218036 prefixEnd_218036 := by exact prefixLift 218036
  have htrace : WordTrace (prefixWord ++ tailWord_218036) baseStart_218036 baseEnd_218036 := by
    simpa [prefixWord, tailWord_218036, baseEnd_218036] using wordTrace_append hprefix tailTrace_218036
  have hstable : (prefixWord ++ tailWord_218036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218036).length < 2 ^ (prefixWord ++ tailWord_218036).sum := by decide
  have hdescent : baseEnd_218036 < baseStart_218036 := by decide
  rcases family_descends (prefixWord ++ tailWord_218036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218056 : List Nat := [2, 1, 3, 1, 6, 1, 1, 1, 1, 2, 4]
def baseStart_218056 : Nat := 118140960795 + 218056 * 2 ^ 59
def prefixEnd_218056 : Nat := 4983230072969 + 3 ^ 40 * 218056 * 2
def baseEnd_218056 : Nat := 111967537596904088597185

theorem tailTrace_218056 : CollatzResearch.WordTrace tailWord_218056 prefixEnd_218056 111967537596904088597185 := by
  unfold tailWord_218056
  simp only [CollatzResearch.WordTrace]
  refine ⟨3976577849013913922501011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5302103798685218563334681 3976577849013913922501011)
  ·
    refine ⟨5964866773520870883751517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3976577849013913922501011 5964866773520870883751517)
    ·
      refine ⟨2236825040070326581406819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5964866773520870883751517 2236825040070326581406819)
      ·
        refine ⟨3355237560105489872110229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2236825040070326581406819 3355237560105489872110229)
        ·
          refine ⟨157276760629944837755167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 3355237560105489872110229 157276760629944837755167)
          ·
            refine ⟨235915140944917256632751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157276760629944837755167 235915140944917256632751)
            ·
              refine ⟨353872711417375884949127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 235915140944917256632751 353872711417375884949127)
              ·
                refine ⟨530809067126063827423691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 353872711417375884949127 530809067126063827423691)
                ·
                  refine ⟨796213600689095741135537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 530809067126063827423691 796213600689095741135537)
                  ·
                    refine ⟨597160200516821805851653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 796213600689095741135537 597160200516821805851653)
                    ·
                      refine ⟨111967537596904088597185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 597160200516821805851653 111967537596904088597185)
                      ·
                        rfl

theorem cell23_218056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 1, 1, 1, 2, 4].length) (baseStart_218056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_218056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_218056 prefixEnd_218056 := by exact prefixLift 218056
  have htrace : WordTrace (prefixWord ++ tailWord_218056) baseStart_218056 baseEnd_218056 := by
    simpa [prefixWord, tailWord_218056, baseEnd_218056] using wordTrace_append hprefix tailTrace_218056
  have hstable : (prefixWord ++ tailWord_218056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218056).length < 2 ^ (prefixWord ++ tailWord_218056).sum := by decide
  have hdescent : baseEnd_218056 < baseStart_218056 := by decide
  rcases family_descends (prefixWord ++ tailWord_218056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218059 : List Nat := [1, 1, 1, 1, 3, 7, 1, 1, 1, 3, 3]
def baseStart_218059 : Nat := 118140960795 + 218059 * 2 ^ 59
def prefixEnd_218059 : Nat := 4983230072969 + 3 ^ 40 * 218059 * 2
def baseEnd_218059 : Nat := 111969078038867576859671

theorem tailTrace_218059 : CollatzResearch.WordTrace tailWord_218059 prefixEnd_218059 111969078038867576859671 := by
  unfold tailWord_218059
  simp only [CollatzResearch.WordTrace]
  refine ⟨7953265117016959357361231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5302176744677972904907487 7953265117016959357361231)
  ·
    refine ⟨11929897675525439036041847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7953265117016959357361231 11929897675525439036041847)
    ·
      refine ⟨17894846513288158554062771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11929897675525439036041847 17894846513288158554062771)
      ·
        refine ⟨26842269769932237831094157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17894846513288158554062771 26842269769932237831094157)
        ·
          refine ⟨10065851163724589186660309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26842269769932237831094157 10065851163724589186660309)
          ·
            refine ⟨235918386649795059062351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 10065851163724589186660309 235918386649795059062351)
            ·
              refine ⟨353877579974692588593527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 235918386649795059062351 353877579974692588593527)
              ·
                refine ⟨530816369962038882890291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 353877579974692588593527 530816369962038882890291)
                ·
                  refine ⟨796224554943058324335437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 530816369962038882890291 796224554943058324335437)
                  ·
                    refine ⟨298584208103646871625789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 796224554943058324335437 298584208103646871625789)
                    ·
                      refine ⟨111969078038867576859671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 298584208103646871625789 111969078038867576859671)
                      ·
                        rfl

theorem cell23_218059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 1, 1, 1, 3, 3].length) (baseStart_218059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_218059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_218059 prefixEnd_218059 := by exact prefixLift 218059
  have htrace : WordTrace (prefixWord ++ tailWord_218059) baseStart_218059 baseEnd_218059 := by
    simpa [prefixWord, tailWord_218059, baseEnd_218059] using wordTrace_append hprefix tailTrace_218059
  have hstable : (prefixWord ++ tailWord_218059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218059).length < 2 ^ (prefixWord ++ tailWord_218059).sum := by decide
  have hdescent : baseEnd_218059 < baseStart_218059 := by decide
  rcases family_descends (prefixWord ++ tailWord_218059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218162 : List Nat := [3, 2, 1, 1, 2, 2, 1, 3, 1, 2, 5]
def baseStart_218162 : Nat := 118140960795 + 218162 * 2 ^ 59
def prefixEnd_218162 : Nat := 4983230072969 + 3 ^ 40 * 218162 * 2
def baseEnd_218162 : Nat := 112021966546280673871697

theorem tailTrace_218162 : CollatzResearch.WordTrace tailWord_218162 prefixEnd_218162 112021966546280673871697 := by
  unfold tailWord_218162
  simp only [CollatzResearch.WordTrace]
  refine ⟨1989255458910951987090185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5304681223762538632240493 1989255458910951987090185)
  ·
    refine ⟨1491941594183213990317639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1989255458910951987090185 1491941594183213990317639)
    ·
      refine ⟨2237912391274820985476459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1491941594183213990317639 2237912391274820985476459)
      ·
        refine ⟨3356868586912231478214689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2237912391274820985476459 3356868586912231478214689)
        ·
          refine ⟨2517651440184173608661017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3356868586912231478214689 2517651440184173608661017)
          ·
            refine ⟨1888238580138130206495763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2517651440184173608661017 1888238580138130206495763)
            ·
              refine ⟨2832357870207195309743645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1888238580138130206495763 2832357870207195309743645)
              ·
                refine ⟨1062134201327698241153867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2832357870207195309743645 1062134201327698241153867)
                ·
                  refine ⟨1593201301991547361730801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1062134201327698241153867 1593201301991547361730801)
                  ·
                    refine ⟨1194900976493660521298101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1593201301991547361730801 1194900976493660521298101)
                    ·
                      refine ⟨112021966546280673871697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1194900976493660521298101 112021966546280673871697)
                      ·
                        rfl

theorem cell23_218162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 3, 1, 2, 5].length) (baseStart_218162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_218162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_218162 prefixEnd_218162 := by exact prefixLift 218162
  have htrace : WordTrace (prefixWord ++ tailWord_218162) baseStart_218162 baseEnd_218162 := by
    simpa [prefixWord, tailWord_218162, baseEnd_218162] using wordTrace_append hprefix tailTrace_218162
  have hstable : (prefixWord ++ tailWord_218162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218162).length < 2 ^ (prefixWord ++ tailWord_218162).sum := by decide
  have hdescent : baseEnd_218162 < baseStart_218162 := by decide
  rcases family_descends (prefixWord ++ tailWord_218162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218166 : List Nat := [5, 1, 2, 1, 1, 3, 1, 1, 2, 3, 3]
def baseStart_218166 : Nat := 118140960795 + 218166 * 2 ^ 59
def prefixEnd_218166 : Nat := 4983230072969 + 3 ^ 40 * 218166 * 2
def baseEnd_218166 : Nat := 112024020468898658221679

theorem tailTrace_218166 : CollatzResearch.WordTrace tailWord_218166 prefixEnd_218166 112024020468898658221679 := by
  unfold tailWord_218166
  simp only [CollatzResearch.WordTrace]
  refine ⟨497322982976832289469147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5304778485086211087670901 497322982976832289469147)
  ·
    refine ⟨745984474465248434203721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 497322982976832289469147 745984474465248434203721)
    ·
      refine ⟨559488355848936325652791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 745984474465248434203721 559488355848936325652791)
      ·
        refine ⟨839232533773404488479187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 559488355848936325652791 839232533773404488479187)
        ·
          refine ⟨1258848800660106732718781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 839232533773404488479187 1258848800660106732718781)
          ·
            refine ⟨472068300247540024769543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1258848800660106732718781 472068300247540024769543)
            ·
              refine ⟨708102450371310037154315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 472068300247540024769543 708102450371310037154315)
              ·
                refine ⟨1062153675556965055731473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 708102450371310037154315 1062153675556965055731473)
                ·
                  refine ⟨796615256667723791798605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1062153675556965055731473 796615256667723791798605)
                  ·
                    refine ⟨298730721250396421924477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 796615256667723791798605 298730721250396421924477)
                    ·
                      refine ⟨112024020468898658221679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 298730721250396421924477 112024020468898658221679)
                      ·
                        rfl

theorem cell23_218166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 1, 2, 3, 3].length) (baseStart_218166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_218166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_218166 prefixEnd_218166 := by exact prefixLift 218166
  have htrace : WordTrace (prefixWord ++ tailWord_218166) baseStart_218166 baseEnd_218166 := by
    simpa [prefixWord, tailWord_218166, baseEnd_218166] using wordTrace_append hprefix tailTrace_218166
  have hstable : (prefixWord ++ tailWord_218166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218166).length < 2 ^ (prefixWord ++ tailWord_218166).sum := by decide
  have hdescent : baseEnd_218166 < baseStart_218166 := by decide
  rcases family_descends (prefixWord ++ tailWord_218166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218209 : List Nat := [1, 2, 3, 1, 1, 2, 2, 4, 2, 2, 3]
def baseStart_218209 : Nat := 118140960795 + 218209 * 2 ^ 59
def prefixEnd_218209 : Nat := 4983230072969 + 3 ^ 40 * 218209 * 2
def baseEnd_218209 : Nat := 112046100137041989983981

theorem tailTrace_218209 : CollatzResearch.WordTrace tailWord_218209 prefixEnd_218209 112046100137041989983981 := by
  unfold tailWord_218209
  simp only [CollatzResearch.WordTrace]
  refine ⟨7958736066473534975321681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5305824044315689983547787 7958736066473534975321681)
  ·
    refine ⟨5969052049855151231491261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7958736066473534975321681 5969052049855151231491261)
    ·
      refine ⟨2238394518695681711809223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5969052049855151231491261 2238394518695681711809223)
      ·
        refine ⟨3357591778043522567713835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2238394518695681711809223 3357591778043522567713835)
        ·
          refine ⟨5036387667065283851570753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3357591778043522567713835 5036387667065283851570753)
          ·
            refine ⟨3777290750298962888678065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5036387667065283851570753 3777290750298962888678065)
            ·
              refine ⟨2832968062724222166508549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3777290750298962888678065 2832968062724222166508549)
              ·
                refine ⟨531181511760791656220353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2832968062724222166508549 531181511760791656220353)
                ·
                  refine ⟨398386133820593742165265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 531181511760791656220353 398386133820593742165265)
                  ·
                    refine ⟨298789600365445306623949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 398386133820593742165265 298789600365445306623949)
                    ·
                      refine ⟨112046100137041989983981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 298789600365445306623949 112046100137041989983981)
                      ·
                        rfl

theorem cell23_218209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 4, 2, 2, 3].length) (baseStart_218209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_218209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_218209 prefixEnd_218209 := by exact prefixLift 218209
  have htrace : WordTrace (prefixWord ++ tailWord_218209) baseStart_218209 baseEnd_218209 := by
    simpa [prefixWord, tailWord_218209, baseEnd_218209] using wordTrace_append hprefix tailTrace_218209
  have hstable : (prefixWord ++ tailWord_218209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218209).length < 2 ^ (prefixWord ++ tailWord_218209).sum := by decide
  have hdescent : baseEnd_218209 < baseStart_218209 := by decide
  rcases family_descends (prefixWord ++ tailWord_218209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218259 : List Nat := [1, 1, 1, 2, 1, 2, 6, 3, 1, 5]
def baseStart_218259 : Nat := 118140960795 + 218259 * 2 ^ 59
def prefixEnd_218259 : Nat := 4983230072969 + 3 ^ 40 * 218259 * 2
def baseEnd_218259 : Nat := 37357258056588931452917

theorem tailTrace_218259 : CollatzResearch.WordTrace tailWord_218259 prefixEnd_218259 37357258056588931452917 := by
  unfold tailWord_218259
  simp only [CollatzResearch.WordTrace]
  refine ⟨7960559716292393514641831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5307039810861595676427887 7960559716292393514641831)
  ·
    refine ⟨11940839574438590271962747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7960559716292393514641831 11940839574438590271962747)
    ·
      refine ⟨17911259361657885407944121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11940839574438590271962747 17911259361657885407944121)
      ·
        refine ⟨13433444521243414055958091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17911259361657885407944121 13433444521243414055958091)
        ·
          refine ⟨20150166781865121083937137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13433444521243414055958091 20150166781865121083937137)
          ·
            refine ⟨15112625086398840812952853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20150166781865121083937137 15112625086398840812952853)
            ·
              refine ⟨708404300924945663107165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15112625086398840812952853 708404300924945663107165)
              ·
                refine ⟨265651612846854623665187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 708404300924945663107165 265651612846854623665187)
                ·
                  refine ⟨398477419270281935497781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 265651612846854623665187 398477419270281935497781)
                  ·
                    refine ⟨37357258056588931452917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 398477419270281935497781 37357258056588931452917)
                    ·
                      rfl

theorem cell23_218259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 3, 1, 5].length) (baseStart_218259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_218259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_218259 prefixEnd_218259 := by exact prefixLift 218259
  have htrace : WordTrace (prefixWord ++ tailWord_218259) baseStart_218259 baseEnd_218259 := by
    simpa [prefixWord, tailWord_218259, baseEnd_218259] using wordTrace_append hprefix tailTrace_218259
  have hstable : (prefixWord ++ tailWord_218259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218259).length < 2 ^ (prefixWord ++ tailWord_218259).sum := by decide
  have hdescent : baseEnd_218259 < baseStart_218259 := by decide
  rcases family_descends (prefixWord ++ tailWord_218259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218329 : List Nat := [1, 2, 1, 2, 3, 1, 1, 1, 5, 3, 3]
def baseStart_218329 : Nat := 118140960795 + 218329 * 2 ^ 59
def prefixEnd_218329 : Nat := 4983230072969 + 3 ^ 40 * 218329 * 2
def baseEnd_218329 : Nat := 112107717815581520483429

theorem tailTrace_218329 : CollatzResearch.WordTrace tailWord_218329 prefixEnd_218329 112107717815581520483429 := by
  unfold tailWord_218329
  simp only [CollatzResearch.WordTrace]
  refine ⟨7963112826038795469690041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5308741884025863646460027 7963112826038795469690041)
  ·
    refine ⟨5972334619529096602267531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7963112826038795469690041 5972334619529096602267531)
    ·
      refine ⟨8958501929293644903401297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5972334619529096602267531 8958501929293644903401297)
      ·
        refine ⟨6718876446970233677550973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8958501929293644903401297 6718876446970233677550973)
        ·
          refine ⟨2519578667613837629081615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6718876446970233677550973 2519578667613837629081615)
          ·
            refine ⟨3779368001420756443622423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2519578667613837629081615 3779368001420756443622423)
            ·
              refine ⟨5669052002131134665433635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3779368001420756443622423 5669052002131134665433635)
              ·
                refine ⟨8503578003196701998150453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5669052002131134665433635 8503578003196701998150453)
                ·
                  refine ⟨797210437799690812326605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8503578003196701998150453 797210437799690812326605)
                  ·
                    refine ⟨298953914174884054622477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 797210437799690812326605 298953914174884054622477)
                    ·
                      refine ⟨112107717815581520483429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 298953914174884054622477 112107717815581520483429)
                      ·
                        rfl

theorem cell23_218329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 5, 3, 3].length) (baseStart_218329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_218329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_218329 prefixEnd_218329 := by exact prefixLift 218329
  have htrace : WordTrace (prefixWord ++ tailWord_218329) baseStart_218329 baseEnd_218329 := by
    simpa [prefixWord, tailWord_218329, baseEnd_218329] using wordTrace_append hprefix tailTrace_218329
  have hstable : (prefixWord ++ tailWord_218329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218329).length < 2 ^ (prefixWord ++ tailWord_218329).sum := by decide
  have hdescent : baseEnd_218329 < baseStart_218329 := by decide
  rcases family_descends (prefixWord ++ tailWord_218329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218343 : List Nat := [1, 1, 5, 3, 2, 1, 2, 1, 1, 2, 4]
def baseStart_218343 : Nat := 118140960795 + 218343 * 2 ^ 59
def prefixEnd_218343 : Nat := 4983230072969 + 3 ^ 40 * 218343 * 2
def baseEnd_218343 : Nat := 112114906544744465708365

theorem tailTrace_218343 : CollatzResearch.WordTrace tailWord_218343 prefixEnd_218343 112114906544744465708365 := by
  unfold tailWord_218343
  simp only [CollatzResearch.WordTrace]
  refine ⟨7963623447988075860699683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5309082298658717240466455 7963623447988075860699683)
  ·
    refine ⟨11945435171982113791049525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7963623447988075860699683 11945435171982113791049525)
    ·
      refine ⟨1119884547373323167910893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11945435171982113791049525 1119884547373323167910893)
      ·
        refine ⟨419956705264996187966585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1119884547373323167910893 419956705264996187966585)
        ·
          refine ⟨314967528948747140974939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 419956705264996187966585 314967528948747140974939)
          ·
            refine ⟨472451293423120711462409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 314967528948747140974939 472451293423120711462409)
            ·
              refine ⟨354338470067340533596807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 472451293423120711462409 354338470067340533596807)
              ·
                refine ⟨531507705101010800395211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 354338470067340533596807 531507705101010800395211)
                ·
                  refine ⟨797261557651516200592817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 531507705101010800395211 797261557651516200592817)
                  ·
                    refine ⟨597946168238637150444613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 797261557651516200592817 597946168238637150444613)
                    ·
                      refine ⟨112114906544744465708365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 597946168238637150444613 112114906544744465708365)
                      ·
                        rfl

theorem cell23_218343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_218343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_218343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_218343 prefixEnd_218343 := by exact prefixLift 218343
  have htrace : WordTrace (prefixWord ++ tailWord_218343) baseStart_218343 baseEnd_218343 := by
    simpa [prefixWord, tailWord_218343, baseEnd_218343] using wordTrace_append hprefix tailTrace_218343
  have hstable : (prefixWord ++ tailWord_218343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218343).length < 2 ^ (prefixWord ++ tailWord_218343).sum := by decide
  have hdescent : baseEnd_218343 < baseStart_218343 := by decide
  rcases family_descends (prefixWord ++ tailWord_218343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218346 : List Nat := [3, 1, 3, 1, 1, 3, 1, 3, 1, 3, 3]
def baseStart_218346 : Nat := 118140960795 + 218346 * 2 ^ 59
def prefixEnd_218346 : Nat := 4983230072969 + 3 ^ 40 * 218346 * 2
def baseEnd_218346 : Nat := 112116446986707953970851

theorem tailTrace_218346 : CollatzResearch.WordTrace tailWord_218346 prefixEnd_218346 112116446986707953970851 := by
  unfold tailWord_218346
  simp only [CollatzResearch.WordTrace]
  refine ⟨1990933216744301843264723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5309155244651471582039261 1990933216744301843264723)
  ·
    refine ⟨2986399825116452764897085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1990933216744301843264723 2986399825116452764897085)
    ·
      refine ⟨1119899934418669786836407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2986399825116452764897085 1119899934418669786836407)
      ·
        refine ⟨1679849901628004680254611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1119899934418669786836407 1679849901628004680254611)
        ·
          refine ⟨2519774852442007020381917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1679849901628004680254611 2519774852442007020381917)
          ·
            refine ⟨944915569665752632643219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2519774852442007020381917 944915569665752632643219)
            ·
              refine ⟨1417373354498628948964829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 944915569665752632643219 1417373354498628948964829)
              ·
                refine ⟨531515007936985855861811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1417373354498628948964829 531515007936985855861811)
                ·
                  refine ⟨797272511905478783792717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 531515007936985855861811 797272511905478783792717)
                  ·
                    refine ⟨298977191964554543922269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 797272511905478783792717 298977191964554543922269)
                    ·
                      refine ⟨112116446986707953970851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 298977191964554543922269 112116446986707953970851)
                      ·
                        rfl

theorem cell23_218346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 3, 1, 3, 3].length) (baseStart_218346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_218346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_218346 prefixEnd_218346 := by exact prefixLift 218346
  have htrace : WordTrace (prefixWord ++ tailWord_218346) baseStart_218346 baseEnd_218346 := by
    simpa [prefixWord, tailWord_218346, baseEnd_218346] using wordTrace_append hprefix tailTrace_218346
  have hstable : (prefixWord ++ tailWord_218346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218346).length < 2 ^ (prefixWord ++ tailWord_218346).sum := by decide
  have hdescent : baseEnd_218346 < baseStart_218346 := by decide
  rcases family_descends (prefixWord ++ tailWord_218346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218373 : List Nat := [1, 3, 1, 1, 2, 1, 5, 3, 1, 3, 2]
def baseStart_218373 : Nat := 118140960795 + 218373 * 2 ^ 59
def prefixEnd_218373 : Nat := 4983230072969 + 3 ^ 40 * 218373 * 2
def baseEnd_218373 : Nat := 112130310964379348333227

theorem tailTrace_218373 : CollatzResearch.WordTrace tailWord_218373 prefixEnd_218373 112130310964379348333227 := by
  unfold tailWord_218373
  simp only [CollatzResearch.WordTrace]
  refine ⟨7964717637879390984291773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5309811758586260656194515 7964717637879390984291773)
  ·
    refine ⟨2986769114204771619109415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7964717637879390984291773 2986769114204771619109415)
    ·
      refine ⟨4480153671307157428664123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2986769114204771619109415 4480153671307157428664123)
      ·
        refine ⟨6720230506960736142996185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4480153671307157428664123 6720230506960736142996185)
        ·
          refine ⟨5040172880220552107247139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6720230506960736142996185 5040172880220552107247139)
          ·
            refine ⟨7560259320330828160870709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5040172880220552107247139 7560259320330828160870709)
            ·
              refine ⟨708774311281015140081629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7560259320330828160870709 708774311281015140081629)
              ·
                refine ⟨265790366730380677530611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 708774311281015140081629 265790366730380677530611)
                ·
                  refine ⟨398685550095571016295917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 265790366730380677530611 398685550095571016295917)
                  ·
                    refine ⟨149507081285839131110969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 398685550095571016295917 149507081285839131110969)
                    ·
                      refine ⟨112130310964379348333227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 149507081285839131110969 112130310964379348333227)
                      ·
                        rfl

theorem cell23_218373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 3, 1, 3, 2].length) (baseStart_218373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_218373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_218373 prefixEnd_218373 := by exact prefixLift 218373
  have htrace : WordTrace (prefixWord ++ tailWord_218373) baseStart_218373 baseEnd_218373 := by
    simpa [prefixWord, tailWord_218373, baseEnd_218373] using wordTrace_append hprefix tailTrace_218373
  have hstable : (prefixWord ++ tailWord_218373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218373).length < 2 ^ (prefixWord ++ tailWord_218373).sum := by decide
  have hdescent : baseEnd_218373 < baseStart_218373 := by decide
  rcases family_descends (prefixWord ++ tailWord_218373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218379 : List Nat := [1, 1, 1, 1, 5, 3, 1, 2, 2, 6]
def baseStart_218379 : Nat := 118140960795 + 218379 * 2 ^ 59
def prefixEnd_218379 : Nat := 4983230072969 + 3 ^ 40 * 218379 * 2
def baseEnd_218379 : Nat := 37377797282768774952733

theorem tailTrace_218379 : CollatzResearch.WordTrace tailWord_218379 prefixEnd_218379 37377797282768774952733 := by
  unfold tailWord_218379
  simp only [CollatzResearch.WordTrace]
  refine ⟨7964936475857654009010191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5309957650571769339340127 7964936475857654009010191)
  ·
    refine ⟨11947404713786481013515287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7964936475857654009010191 11947404713786481013515287)
    ·
      refine ⟨17921107070679721520272931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11947404713786481013515287 17921107070679721520272931)
      ·
        refine ⟨26881660606019582280409397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17921107070679721520272931 26881660606019582280409397)
        ·
          refine ⟨2520155681814335838788381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26881660606019582280409397 2520155681814335838788381)
          ·
            refine ⟨945058380680375939545643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2520155681814335838788381 945058380680375939545643)
            ·
              refine ⟨1417587571020563909318465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 945058380680375939545643 1417587571020563909318465)
              ·
                refine ⟨1063190678265422931988849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1417587571020563909318465 1063190678265422931988849)
                ·
                  refine ⟨797393008699067198991637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1063190678265422931988849 797393008699067198991637)
                  ·
                    refine ⟨37377797282768774952733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 797393008699067198991637 37377797282768774952733)
                    ·
                      rfl

theorem cell23_218379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 2, 2, 6].length) (baseStart_218379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_218379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_218379 prefixEnd_218379 := by exact prefixLift 218379
  have htrace : WordTrace (prefixWord ++ tailWord_218379) baseStart_218379 baseEnd_218379 := by
    simpa [prefixWord, tailWord_218379, baseEnd_218379] using wordTrace_append hprefix tailTrace_218379
  have hstable : (prefixWord ++ tailWord_218379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218379).length < 2 ^ (prefixWord ++ tailWord_218379).sum := by decide
  have hdescent : baseEnd_218379 < baseStart_218379 := by decide
  rcases family_descends (prefixWord ++ tailWord_218379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218380 : List Nat := [2, 2, 1, 2, 2, 5, 1, 2, 2, 1, 3]
def baseStart_218380 : Nat := 118140960795 + 218380 * 2 ^ 59
def prefixEnd_218380 : Nat := 4983230072969 + 3 ^ 40 * 218380 * 2
def baseEnd_218380 : Nat := 112133905328960820945695

theorem tailTrace_218380 : CollatzResearch.WordTrace tailWord_218380 prefixEnd_218380 112133905328960820945695 := by
  unfold tailWord_218380
  simp only [CollatzResearch.WordTrace]
  refine ⟨3982486474427015589898297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5309981965902687453197729 3982486474427015589898297)
  ·
    refine ⟨2986864855820261692423723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3982486474427015589898297 2986864855820261692423723)
    ·
      refine ⟨4480297283730392538635585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2986864855820261692423723 4480297283730392538635585)
      ·
        refine ⟨3360222962797794403976689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4480297283730392538635585 3360222962797794403976689)
        ·
          refine ⟨2520167222098345802982517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3360222962797794403976689 2520167222098345802982517)
          ·
            refine ⟨236265677071719919029611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2520167222098345802982517 236265677071719919029611)
            ·
              refine ⟨354398515607579878544417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 236265677071719919029611 354398515607579878544417)
              ·
                refine ⟨265798886705684908908313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 354398515607579878544417 265798886705684908908313)
                ·
                  refine ⟨199349165029263681681235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 265798886705684908908313 199349165029263681681235)
                  ·
                    refine ⟨299023747543895522521853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 199349165029263681681235 299023747543895522521853)
                    ·
                      refine ⟨112133905328960820945695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 299023747543895522521853 112133905328960820945695)
                      ·
                        rfl

theorem cell23_218380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 1, 2, 2, 1, 3].length) (baseStart_218380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_218380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_218380 prefixEnd_218380 := by exact prefixLift 218380
  have htrace : WordTrace (prefixWord ++ tailWord_218380) baseStart_218380 baseEnd_218380 := by
    simpa [prefixWord, tailWord_218380, baseEnd_218380] using wordTrace_append hprefix tailTrace_218380
  have hstable : (prefixWord ++ tailWord_218380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218380).length < 2 ^ (prefixWord ++ tailWord_218380).sum := by decide
  have hdescent : baseEnd_218380 < baseStart_218380 := by decide
  rcases family_descends (prefixWord ++ tailWord_218380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218389 : List Nat := [1, 3, 2, 1, 2, 1, 1, 2, 4, 1, 5]
def baseStart_218389 : Nat := 118140960795 + 218389 * 2 ^ 59
def prefixEnd_218389 : Nat := 4983230072969 + 3 ^ 40 * 218389 * 2
def baseEnd_218389 : Nat := 112138526654851285733153

theorem tailTrace_218389 : CollatzResearch.WordTrace tailWord_218389 prefixEnd_218389 112138526654851285733153 := by
  unfold tailWord_218389
  simp only [CollatzResearch.WordTrace]
  refine ⟨7965301205821425716874221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5310200803880950477916147 7965301205821425716874221)
  ·
    refine ⟨2986987952183034643827833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7965301205821425716874221 2986987952183034643827833)
    ·
      refine ⟨2240240964137275982870875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2986987952183034643827833 2240240964137275982870875)
      ·
        refine ⟨3360361446205913974306313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2240240964137275982870875 3360361446205913974306313)
        ·
          refine ⟨2520271084654435480729735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3360361446205913974306313 2520271084654435480729735)
          ·
            refine ⟨3780406626981653221094603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2520271084654435480729735 3780406626981653221094603)
            ·
              refine ⟨5670609940472479831641905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3780406626981653221094603 5670609940472479831641905)
              ·
                refine ⟨4252957455354359873731429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5670609940472479831641905 4252957455354359873731429)
                ·
                  refine ⟨797429522878942476324643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4252957455354359873731429 797429522878942476324643)
                  ·
                    refine ⟨1196144284318413714486965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 797429522878942476324643 1196144284318413714486965)
                    ·
                      refine ⟨112138526654851285733153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1196144284318413714486965 112138526654851285733153)
                      ·
                        rfl

theorem cell23_218389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 4, 1, 5].length) (baseStart_218389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_218389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_218389 prefixEnd_218389 := by exact prefixLift 218389
  have htrace : WordTrace (prefixWord ++ tailWord_218389) baseStart_218389 baseEnd_218389 := by
    simpa [prefixWord, tailWord_218389, baseEnd_218389] using wordTrace_append hprefix tailTrace_218389
  have hstable : (prefixWord ++ tailWord_218389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218389).length < 2 ^ (prefixWord ++ tailWord_218389).sum := by decide
  have hdescent : baseEnd_218389 < baseStart_218389 := by decide
  rcases family_descends (prefixWord ++ tailWord_218389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218397 : List Nat := [1, 4, 2, 3, 1, 2, 3, 1, 2, 1, 3]
def baseStart_218397 : Nat := 118140960795 + 218397 * 2 ^ 59
def prefixEnd_218397 : Nat := 4983230072969 + 3 ^ 40 * 218397 * 2
def baseEnd_218397 : Nat := 112142634500087254433117

theorem tailTrace_218397 : CollatzResearch.WordTrace tailWord_218397 prefixEnd_218397 112142634500087254433117 := by
  unfold tailWord_218397
  simp only [CollatzResearch.WordTrace]
  refine ⟨7965592989792443083165445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5310395326528295388776963 7965592989792443083165445)
  ·
    refine ⟨1493548685586083078093521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7965592989792443083165445 1493548685586083078093521)
    ·
      refine ⟨1120161514189562308570141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1493548685586083078093521 1120161514189562308570141)
      ·
        refine ⟨420060567821085865713803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1120161514189562308570141 420060567821085865713803)
        ·
          refine ⟨630090851731628798570705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 420060567821085865713803 630090851731628798570705)
          ·
            refine ⟨472568138798721598928029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 630090851731628798570705 472568138798721598928029)
            ·
              refine ⟨177213052049520599598011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 472568138798721598928029 177213052049520599598011)
              ·
                refine ⟨265819578074280899397017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177213052049520599598011 265819578074280899397017)
                ·
                  refine ⟨199364683555710674547763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 265819578074280899397017 199364683555710674547763)
                  ·
                    refine ⟨299047025333566011821645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 199364683555710674547763 299047025333566011821645)
                    ·
                      refine ⟨112142634500087254433117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 299047025333566011821645 112142634500087254433117)
                      ·
                        rfl

theorem cell23_218397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 3, 1, 2, 1, 3].length) (baseStart_218397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_218397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_218397 prefixEnd_218397 := by exact prefixLift 218397
  have htrace : WordTrace (prefixWord ++ tailWord_218397) baseStart_218397 baseEnd_218397 := by
    simpa [prefixWord, tailWord_218397, baseEnd_218397] using wordTrace_append hprefix tailTrace_218397
  have hstable : (prefixWord ++ tailWord_218397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218397).length < 2 ^ (prefixWord ++ tailWord_218397).sum := by decide
  have hdescent : baseEnd_218397 < baseStart_218397 := by decide
  rcases family_descends (prefixWord ++ tailWord_218397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218403 : List Nat := [1, 1, 1, 4, 2, 3, 3, 1, 1, 4, 2]
def baseStart_218403 : Nat := 118140960795 + 218403 * 2 ^ 59
def prefixEnd_218403 : Nat := 4983230072969 + 3 ^ 40 * 218403 * 2
def baseEnd_218403 : Nat := 112145715384014230958089

theorem tailTrace_218403 : CollatzResearch.WordTrace tailWord_218403 prefixEnd_218403 112145715384014230958089 := by
  unfold tailWord_218403
  simp only [CollatzResearch.WordTrace]
  refine ⟨7965811827770706107883863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5310541218513804071922575 7965811827770706107883863)
  ·
    refine ⟨11948717741656059161825795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7965811827770706107883863 11948717741656059161825795)
    ·
      refine ⟨17923076612484088742738693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11948717741656059161825795 17923076612484088742738693)
      ·
        refine ⟨3360576864840766639263505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17923076612484088742738693 3360576864840766639263505)
        ·
          refine ⟨2520432648630574979447629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3360576864840766639263505 2520432648630574979447629)
          ·
            refine ⟨945162243236465617292861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2520432648630574979447629 945162243236465617292861)
            ·
              refine ⟨354435841213674606484823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 945162243236465617292861 354435841213674606484823)
              ·
                refine ⟨531653761820511909727235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 354435841213674606484823 531653761820511909727235)
                ·
                  refine ⟨797480642730767864590853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 531653761820511909727235 797480642730767864590853)
                  ·
                    refine ⟨149527620512018974610785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 797480642730767864590853 149527620512018974610785)
                    ·
                      refine ⟨112145715384014230958089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 149527620512018974610785 112145715384014230958089)
                      ·
                        rfl

theorem cell23_218403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3, 1, 1, 4, 2].length) (baseStart_218403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_218403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_218403 prefixEnd_218403 := by exact prefixLift 218403
  have htrace : WordTrace (prefixWord ++ tailWord_218403) baseStart_218403 baseEnd_218403 := by
    simpa [prefixWord, tailWord_218403, baseEnd_218403] using wordTrace_append hprefix tailTrace_218403
  have hstable : (prefixWord ++ tailWord_218403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218403).length < 2 ^ (prefixWord ++ tailWord_218403).sum := by decide
  have hdescent : baseEnd_218403 < baseStart_218403 := by decide
  rcases family_descends (prefixWord ++ tailWord_218403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218420 : List Nat := [2, 5, 1, 1, 1, 1, 1, 1, 6, 2, 2]
def baseStart_218420 : Nat := 118140960795 + 218420 * 2 ^ 59
def prefixEnd_218420 : Nat := 4983230072969 + 3 ^ 40 * 218420 * 2
def baseEnd_218420 : Nat := 112154444555140664445511

theorem tailTrace_218420 : CollatzResearch.WordTrace tailWord_218420 prefixEnd_218420 112154444555140664445511 := by
  unfold tailWord_218420
  simp only [CollatzResearch.WordTrace]
  refine ⟨3983215934354559005626357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5310954579139412007501809 3983215934354559005626357)
  ·
    refine ⟨373426493845739906777471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3983215934354559005626357 373426493845739906777471)
    ·
      refine ⟨560139740768609860166207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373426493845739906777471 560139740768609860166207)
      ·
        refine ⟨840209611152914790249311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 560139740768609860166207 840209611152914790249311)
        ·
          refine ⟨1260314416729372185373967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 840209611152914790249311 1260314416729372185373967)
          ·
            refine ⟨1890471625094058278060951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1260314416729372185373967 1890471625094058278060951)
            ·
              refine ⟨2835707437641087417091427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1890471625094058278060951 2835707437641087417091427)
              ·
                refine ⟨4253561156461631125637141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2835707437641087417091427 4253561156461631125637141)
                ·
                  refine ⟨199385679209138959014241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4253561156461631125637141 199385679209138959014241)
                  ·
                    refine ⟨149539259406854219260681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 199385679209138959014241 149539259406854219260681)
                    ·
                      refine ⟨112154444555140664445511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 149539259406854219260681 112154444555140664445511)
                      ·
                        rfl

theorem cell23_218420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 6, 2, 2].length) (baseStart_218420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_218420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_218420 prefixEnd_218420 := by exact prefixLift 218420
  have htrace : WordTrace (prefixWord ++ tailWord_218420) baseStart_218420 baseEnd_218420 := by
    simpa [prefixWord, tailWord_218420, baseEnd_218420] using wordTrace_append hprefix tailTrace_218420
  have hstable : (prefixWord ++ tailWord_218420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218420).length < 2 ^ (prefixWord ++ tailWord_218420).sum := by decide
  have hdescent : baseEnd_218420 < baseStart_218420 := by decide
  rcases family_descends (prefixWord ++ tailWord_218420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218466 : List Nat := [3, 3, 2, 1, 1, 1, 1, 2, 1, 1, 7]
def baseStart_218466 : Nat := 118140960795 + 218466 * 2 ^ 59
def prefixEnd_218466 : Nat := 4983230072969 + 3 ^ 40 * 218466 * 2
def baseEnd_218466 : Nat := 112178064665247484470299

theorem tailTrace_218466 : CollatzResearch.WordTrace tailWord_218466 prefixEnd_218466 112178064665247484470299 := by
  unfold tailWord_218466
  simp only [CollatzResearch.WordTrace]
  refine ⟨1992027406635616966856813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5312073084361645244951501 1992027406635616966856813)
  ·
    refine ⟨747010277488356362571305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1992027406635616966856813 747010277488356362571305)
    ·
      refine ⟨560257708116267271928479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 747010277488356362571305 560257708116267271928479)
      ·
        refine ⟨840386562174400907892719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 560257708116267271928479 840386562174400907892719)
        ·
          refine ⟨1260579843261601361839079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 840386562174400907892719 1260579843261601361839079)
          ·
            refine ⟨1890869764892402042758619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1260579843261601361839079 1890869764892402042758619)
            ·
              refine ⟨2836304647338603064137929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1890869764892402042758619 2836304647338603064137929)
              ·
                refine ⟨2127228485503952298103447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2836304647338603064137929 2127228485503952298103447)
                ·
                  refine ⟨3190842728255928447155171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2127228485503952298103447 3190842728255928447155171)
                  ·
                    refine ⟨4786264092383892670732757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3190842728255928447155171 4786264092383892670732757)
                    ·
                      refine ⟨112178064665247484470299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 4786264092383892670732757 112178064665247484470299)
                      ·
                        rfl

theorem cell23_218466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_218466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_218466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_218466 prefixEnd_218466 := by exact prefixLift 218466
  have htrace : WordTrace (prefixWord ++ tailWord_218466) baseStart_218466 baseEnd_218466 := by
    simpa [prefixWord, tailWord_218466, baseEnd_218466] using wordTrace_append hprefix tailTrace_218466
  have hstable : (prefixWord ++ tailWord_218466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218466).length < 2 ^ (prefixWord ++ tailWord_218466).sum := by decide
  have hdescent : baseEnd_218466 < baseStart_218466 := by decide
  rcases family_descends (prefixWord ++ tailWord_218466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218493 : List Nat := [1, 4, 1, 1, 2, 2, 2, 2, 2, 4, 2]
def baseStart_218493 : Nat := 118140960795 + 218493 * 2 ^ 59
def prefixEnd_218493 : Nat := 4983230072969 + 3 ^ 40 * 218493 * 2
def baseEnd_218493 : Nat := 112191928642918878832675

theorem tailTrace_218493 : CollatzResearch.WordTrace tailWord_218493 prefixEnd_218493 112191928642918878832675 := by
  unfold tailWord_218493
  simp only [CollatzResearch.WordTrace]
  refine ⟨7969094397444651478660133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5312729598296434319106755 7969094397444651478660133)
  ·
    refine ⟨1494205199520872152248775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7969094397444651478660133 1494205199520872152248775)
    ·
      refine ⟨2241307799281308228373163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1494205199520872152248775 2241307799281308228373163)
      ·
        refine ⟨3361961698921962342559745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2241307799281308228373163 3361961698921962342559745)
        ·
          refine ⟨2521471274191471756919809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3361961698921962342559745 2521471274191471756919809)
          ·
            refine ⟨1891103455643603817689857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2521471274191471756919809 1891103455643603817689857)
            ·
              refine ⟨1418327591732702863267393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1891103455643603817689857 1418327591732702863267393)
              ·
                refine ⟨1063745693799527147450545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1418327591732702863267393 1063745693799527147450545)
                ·
                  refine ⟨797809270349645360587909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1063745693799527147450545 797809270349645360587909)
                  ·
                    refine ⟨149589238190558505110233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 797809270349645360587909 149589238190558505110233)
                    ·
                      refine ⟨112191928642918878832675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 149589238190558505110233 112191928642918878832675)
                      ·
                        rfl

theorem cell23_218493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 2, 2, 4, 2].length) (baseStart_218493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_218493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_218493 prefixEnd_218493 := by exact prefixLift 218493
  have htrace : WordTrace (prefixWord ++ tailWord_218493) baseStart_218493 baseEnd_218493 := by
    simpa [prefixWord, tailWord_218493, baseEnd_218493] using wordTrace_append hprefix tailTrace_218493
  have hstable : (prefixWord ++ tailWord_218493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218493).length < 2 ^ (prefixWord ++ tailWord_218493).sum := by decide
  have hdescent : baseEnd_218493 < baseStart_218493 := by decide
  rcases family_descends (prefixWord ++ tailWord_218493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218520 : List Nat := [2, 1, 2, 5, 2, 1, 1, 2, 3, 4]
def baseStart_218520 : Nat := 118140960795 + 218520 * 2 ^ 59
def prefixEnd_218520 : Nat := 4983230072969 + 3 ^ 40 * 218520 * 2
def baseEnd_218520 : Nat := 37401930873530091065017

theorem tailTrace_218520 : CollatzResearch.WordTrace tailWord_218520 prefixEnd_218520 37401930873530091065017 := by
  unfold tailWord_218520
  simp only [CollatzResearch.WordTrace]
  refine ⟨3985039584173417544946507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5313386112231223393262009 3985039584173417544946507)
  ·
    refine ⟨5977559376260126317419761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3985039584173417544946507 5977559376260126317419761)
    ·
      refine ⟨4483169532195094738064821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5977559376260126317419761 4483169532195094738064821)
      ·
        refine ⟨420297143643290131693577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4483169532195094738064821 420297143643290131693577)
        ·
          refine ⟨315222857732467598770183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 420297143643290131693577 315222857732467598770183)
          ·
            refine ⟨472834286598701398155275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 315222857732467598770183 472834286598701398155275)
            ·
              refine ⟨709251429898052097232913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 472834286598701398155275 709251429898052097232913)
              ·
                refine ⟨531938572423539072924685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 709251429898052097232913 531938572423539072924685)
                ·
                  refine ⟨199476964658827152346757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 531938572423539072924685 199476964658827152346757)
                  ·
                    refine ⟨37401930873530091065017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 199476964658827152346757 37401930873530091065017)
                    ·
                      rfl

theorem cell23_218520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 2, 3, 4].length) (baseStart_218520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_218520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_218520 prefixEnd_218520 := by exact prefixLift 218520
  have htrace : WordTrace (prefixWord ++ tailWord_218520) baseStart_218520 baseEnd_218520 := by
    simpa [prefixWord, tailWord_218520, baseEnd_218520] using wordTrace_append hprefix tailTrace_218520
  have hstable : (prefixWord ++ tailWord_218520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218520).length < 2 ^ (prefixWord ++ tailWord_218520).sum := by decide
  have hdescent : baseEnd_218520 < baseStart_218520 := by decide
  rcases family_descends (prefixWord ++ tailWord_218520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218530 : List Nat := [3, 3, 1, 2, 1, 2, 3, 1, 2, 2, 3]
def baseStart_218530 : Nat := 118140960795 + 218530 * 2 ^ 59
def prefixEnd_218530 : Nat := 4983230072969 + 3 ^ 40 * 218530 * 2
def baseEnd_218530 : Nat := 112210927427135234070005

theorem tailTrace_218530 : CollatzResearch.WordTrace tailWord_218530 prefixEnd_218530 112210927427135234070005 := by
  unfold tailWord_218530
  simp only [CollatzResearch.WordTrace]
  refine ⟨1992610974577651699439261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5313629265540404531838029 1992610974577651699439261)
  ·
    refine ⟨747229115466619387289723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1992610974577651699439261 747229115466619387289723)
    ·
      refine ⟨1120843673199929080934585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 747229115466619387289723 1120843673199929080934585)
      ·
        refine ⟨840632754899946810700939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1120843673199929080934585 840632754899946810700939)
        ·
          refine ⟨1260949132349920216051409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 840632754899946810700939 1260949132349920216051409)
          ·
            refine ⟨945711849262440162038557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1260949132349920216051409 945711849262440162038557)
            ·
              refine ⟨354641943473415060764459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 945711849262440162038557 354641943473415060764459)
              ·
                refine ⟨531962915210122591146689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 354641943473415060764459 531962915210122591146689)
                ·
                  refine ⟨398972186407591943360017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 531962915210122591146689 398972186407591943360017)
                  ·
                    refine ⟨299229139805693957520013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 398972186407591943360017 299229139805693957520013)
                    ·
                      refine ⟨112210927427135234070005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 299229139805693957520013 112210927427135234070005)
                      ·
                        rfl

theorem cell23_218530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3, 1, 2, 2, 3].length) (baseStart_218530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_218530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_218530 prefixEnd_218530 := by exact prefixLift 218530
  have htrace : WordTrace (prefixWord ++ tailWord_218530) baseStart_218530 baseEnd_218530 := by
    simpa [prefixWord, tailWord_218530, baseEnd_218530] using wordTrace_append hprefix tailTrace_218530
  have hstable : (prefixWord ++ tailWord_218530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218530).length < 2 ^ (prefixWord ++ tailWord_218530).sum := by decide
  have hdescent : baseEnd_218530 < baseStart_218530 := by decide
  rcases family_descends (prefixWord ++ tailWord_218530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218546 : List Nat := [3, 2, 1, 1, 1, 1, 2, 2, 5, 5]
def baseStart_218546 : Nat := 118140960795 + 218546 * 2 ^ 59
def prefixEnd_218546 : Nat := 4983230072969 + 3 ^ 40 * 218546 * 2
def baseEnd_218546 : Nat := 37406381039202390489977

theorem tailTrace_218546 : CollatzResearch.WordTrace tailWord_218546 prefixEnd_218546 37406381039202390489977 := by
  unfold tailWord_218546
  simp only [CollatzResearch.WordTrace]
  refine ⟨1992756866563160382584873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5314018310835094353559661 1992756866563160382584873)
  ·
    refine ⟨1494567649922370286938655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1992756866563160382584873 1494567649922370286938655)
    ·
      refine ⟨2241851474883555430407983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1494567649922370286938655 2241851474883555430407983)
      ·
        refine ⟨3362777212325333145611975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2241851474883555430407983 3362777212325333145611975)
        ·
          refine ⟨5044165818487999718417963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3362777212325333145611975 5044165818487999718417963)
          ·
            refine ⟨7566248727731999577626945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5044165818487999718417963 7566248727731999577626945)
            ·
              refine ⟨5674686545798999683220209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7566248727731999577626945 5674686545798999683220209)
              ·
                refine ⟨4256014909349249762415157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5674686545798999683220209 4256014909349249762415157)
                ·
                  refine ⟨399001397751492165226421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4256014909349249762415157 399001397751492165226421)
                  ·
                    refine ⟨37406381039202390489977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 399001397751492165226421 37406381039202390489977)
                    ·
                      rfl

theorem cell23_218546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 5, 5].length) (baseStart_218546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_218546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_218546 prefixEnd_218546 := by exact prefixLift 218546
  have htrace : WordTrace (prefixWord ++ tailWord_218546) baseStart_218546 baseEnd_218546 := by
    simpa [prefixWord, tailWord_218546, baseEnd_218546] using wordTrace_append hprefix tailTrace_218546
  have hstable : (prefixWord ++ tailWord_218546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218546).length < 2 ^ (prefixWord ++ tailWord_218546).sum := by decide
  have hdescent : baseEnd_218546 < baseStart_218546 := by decide
  rcases family_descends (prefixWord ++ tailWord_218546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218593 : List Nat := [1, 2, 3, 1, 2, 3, 1, 2, 4, 4]
def baseStart_218593 : Nat := 118140960795 + 218593 * 2 ^ 59
def prefixEnd_218593 : Nat := 4983230072969 + 3 ^ 40 * 218593 * 2
def baseEnd_218593 : Nat := 37414425569456162527405

theorem tailTrace_218593 : CollatzResearch.WordTrace tailWord_218593 prefixEnd_218593 37414425569456162527405 := by
  unfold tailWord_218593
  simp only [CollatzResearch.WordTrace]
  refine ⟨7972741697082368557300433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5315161131388245704866955 7972741697082368557300433)
  ·
    refine ⟨5979556272811776417975325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7972741697082368557300433 5979556272811776417975325)
    ·
      refine ⟨2242333602304416156740747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5979556272811776417975325 2242333602304416156740747)
      ·
        refine ⟨3363500403456624235111121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2242333602304416156740747 3363500403456624235111121)
        ·
          refine ⟨2522625302592468176333341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3363500403456624235111121 2522625302592468176333341)
          ·
            refine ⟨945984488472175566125003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2522625302592468176333341 945984488472175566125003)
            ·
              refine ⟨1418976732708263349187505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 945984488472175566125003 1418976732708263349187505)
              ·
                refine ⟨1064232549531197511890629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1418976732708263349187505 1064232549531197511890629)
                ·
                  refine ⟨199543603037099533479493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1064232549531197511890629 199543603037099533479493)
                  ·
                    refine ⟨37414425569456162527405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 199543603037099533479493 37414425569456162527405)
                    ·
                      rfl

theorem cell23_218593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 2, 4, 4].length) (baseStart_218593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_218593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_218593 prefixEnd_218593 := by exact prefixLift 218593
  have htrace : WordTrace (prefixWord ++ tailWord_218593) baseStart_218593 baseEnd_218593 := by
    simpa [prefixWord, tailWord_218593, baseEnd_218593] using wordTrace_append hprefix tailTrace_218593
  have hstable : (prefixWord ++ tailWord_218593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218593).length < 2 ^ (prefixWord ++ tailWord_218593).sum := by decide
  have hdescent : baseEnd_218593 < baseStart_218593 := by decide
  rcases family_descends (prefixWord ++ tailWord_218593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218610 : List Nat := [3, 2, 1, 4, 1, 1, 2, 1, 4, 4]
def baseStart_218610 : Nat := 118140960795 + 218610 * 2 ^ 59
def prefixEnd_218610 : Nat := 4983230072969 + 3 ^ 40 * 218610 * 2
def baseEnd_218610 : Nat := 37417335293164973689879

theorem tailTrace_218610 : CollatzResearch.WordTrace tailWord_218610 prefixEnd_218610 37417335293164973689879 := by
  unfold tailWord_218610
  simp only [CollatzResearch.WordTrace]
  refine ⟨1993340434505195115167321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5315574492013853640446189 1993340434505195115167321)
  ·
    refine ⟨1495005325878896336375491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1993340434505195115167321 1495005325878896336375491)
    ·
      refine ⟨2242507988818344504563237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1495005325878896336375491 2242507988818344504563237)
      ·
        refine ⟨420470247903439594605607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2242507988818344504563237 420470247903439594605607)
        ·
          refine ⟨630705371855159391908411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 420470247903439594605607 630705371855159391908411)
          ·
            refine ⟨946058057782739087862617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 630705371855159391908411 946058057782739087862617)
            ·
              refine ⟨709543543337054315896963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 946058057782739087862617 709543543337054315896963)
              ·
                refine ⟨1064315315005581473845445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 709543543337054315896963 1064315315005581473845445)
                ·
                  refine ⟨199559121563546526346021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1064315315005581473845445 199559121563546526346021)
                  ·
                    refine ⟨37417335293164973689879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 199559121563546526346021 37417335293164973689879)
                    ·
                      rfl

theorem cell23_218610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 1, 4, 4].length) (baseStart_218610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_218610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_218610 prefixEnd_218610 := by exact prefixLift 218610
  have htrace : WordTrace (prefixWord ++ tailWord_218610) baseStart_218610 baseEnd_218610 := by
    simpa [prefixWord, tailWord_218610, baseEnd_218610] using wordTrace_append hprefix tailTrace_218610
  have hstable : (prefixWord ++ tailWord_218610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218610).length < 2 ^ (prefixWord ++ tailWord_218610).sum := by decide
  have hdescent : baseEnd_218610 < baseStart_218610 := by decide
  rcases family_descends (prefixWord ++ tailWord_218610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218633 : List Nat := [1, 2, 1, 1, 3, 1, 4, 3, 1, 3, 3]
def baseStart_218633 : Nat := 118140960795 + 218633 * 2 ^ 59
def prefixEnd_218633 : Nat := 4983230072969 + 3 ^ 40 * 218633 * 2
def baseEnd_218633 : Nat := 112263815934548331082031

theorem tailTrace_218633 : CollatzResearch.WordTrace tailWord_218633 prefixEnd_218633 112263815934548331082031 := by
  unfold tailWord_218633
  simp only [CollatzResearch.WordTrace]
  refine ⟨7974200616937455388756553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5316133744624970259171035 7974200616937455388756553)
  ·
    refine ⟨5980650462703091541567415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7974200616937455388756553 5980650462703091541567415)
    ·
      refine ⟨8970975694054637312351123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5980650462703091541567415 8970975694054637312351123)
      ·
        refine ⟨13456463541081955968526685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8970975694054637312351123 13456463541081955968526685)
        ·
          refine ⟨5046173827905733488197507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13456463541081955968526685 5046173827905733488197507)
          ·
            refine ⟨7569260741858600232296261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5046173827905733488197507 7569260741858600232296261)
            ·
              refine ⟨1419236389098487543555549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7569260741858600232296261 1419236389098487543555549)
              ·
                refine ⟨532213645911932828833331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1419236389098487543555549 532213645911932828833331)
                ·
                  refine ⟨798320468867899243249997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 532213645911932828833331 798320468867899243249997)
                  ·
                    refine ⟨299370175825462216218749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 798320468867899243249997 299370175825462216218749)
                    ·
                      refine ⟨112263815934548331082031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 299370175825462216218749 112263815934548331082031)
                      ·
                        rfl

theorem cell23_218633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 3, 1, 3, 3].length) (baseStart_218633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_218633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_218633 prefixEnd_218633 := by exact prefixLift 218633
  have htrace : WordTrace (prefixWord ++ tailWord_218633) baseStart_218633 baseEnd_218633 := by
    simpa [prefixWord, tailWord_218633, baseEnd_218633] using wordTrace_append hprefix tailTrace_218633
  have hstable : (prefixWord ++ tailWord_218633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218633).length < 2 ^ (prefixWord ++ tailWord_218633).sum := by decide
  have hdescent : baseEnd_218633 < baseStart_218633 := by decide
  rcases family_descends (prefixWord ++ tailWord_218633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218693 : List Nat := [1, 3, 1, 1, 1, 4, 1, 2, 2, 4, 3]
def baseStart_218693 : Nat := 118140960795 + 218693 * 2 ^ 59
def prefixEnd_218693 : Nat := 4983230072969 + 3 ^ 40 * 218693 * 2
def baseEnd_218693 : Nat := 112294624773818096331755

theorem tailTrace_218693 : CollatzResearch.WordTrace tailWord_218693 prefixEnd_218693 112294624773818096331755 := by
  unfold tailWord_218693
  simp only [CollatzResearch.WordTrace]
  refine ⟨7976388996720085635940733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5317592664480057090627155 7976388996720085635940733)
  ·
    refine ⟨2991145873770032113477775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7976388996720085635940733 2991145873770032113477775)
    ·
      refine ⟨4486718810655048170216663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2991145873770032113477775 4486718810655048170216663)
      ·
        refine ⟨6730078215982572255324995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4486718810655048170216663 6730078215982572255324995)
        ·
          refine ⟨10095117323973858382987493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6730078215982572255324995 10095117323973858382987493)
          ·
            refine ⟨1892834498245098446810155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10095117323973858382987493 1892834498245098446810155)
            ·
              refine ⟨2839251747367647670215233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1892834498245098446810155 2839251747367647670215233)
              ·
                refine ⟨2129438810525735752661425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2839251747367647670215233 2129438810525735752661425)
                ·
                  refine ⟨1597079107894301814496069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2129438810525735752661425 1597079107894301814496069)
                  ·
                    refine ⟨299452332730181590218013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1597079107894301814496069 299452332730181590218013)
                    ·
                      refine ⟨112294624773818096331755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 299452332730181590218013 112294624773818096331755)
                      ·
                        rfl

theorem cell23_218693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 2, 2, 4, 3].length) (baseStart_218693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_218693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_218693 prefixEnd_218693 := by exact prefixLift 218693
  have htrace : WordTrace (prefixWord ++ tailWord_218693) baseStart_218693 baseEnd_218693 := by
    simpa [prefixWord, tailWord_218693, baseEnd_218693] using wordTrace_append hprefix tailTrace_218693
  have hstable : (prefixWord ++ tailWord_218693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218693).length < 2 ^ (prefixWord ++ tailWord_218693).sum := by decide
  have hdescent : baseEnd_218693 < baseStart_218693 := by decide
  rcases family_descends (prefixWord ++ tailWord_218693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218724 : List Nat := [2, 3, 1, 1, 2, 3, 3, 2, 2, 2, 2]
def baseStart_218724 : Nat := 118140960795 + 218724 * 2 ^ 59
def prefixEnd_218724 : Nat := 4983230072969 + 3 ^ 40 * 218724 * 2
def baseEnd_218724 : Nat := 112310542674107475044113

theorem tailTrace_218724 : CollatzResearch.WordTrace tailWord_218724 prefixEnd_218724 112310542674107475044113 := by
  unfold tailWord_218724
  simp only [CollatzResearch.WordTrace]
  refine ⟨3988759829803888965159613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5318346439738518620212817 3988759829803888965159613)
  ·
    refine ⟨1495784936176458361934855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3988759829803888965159613 1495784936176458361934855)
    ·
      refine ⟨2243677404264687542902283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1495784936176458361934855 2243677404264687542902283)
      ·
        refine ⟨3365516106397031314353425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2243677404264687542902283 3365516106397031314353425)
        ·
          refine ⟨2524137079797773485765069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3365516106397031314353425 2524137079797773485765069)
          ·
            refine ⟨946551404924165057161901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2524137079797773485765069 946551404924165057161901)
            ·
              refine ⟨354956776846561896435713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 946551404924165057161901 354956776846561896435713)
              ·
                refine ⟨266217582634921422326785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 354956776846561896435713 266217582634921422326785)
                ·
                  refine ⟨199663186976191066745089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 266217582634921422326785 199663186976191066745089)
                  ·
                    refine ⟨149747390232143300058817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 199663186976191066745089 149747390232143300058817)
                    ·
                      refine ⟨112310542674107475044113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 149747390232143300058817 112310542674107475044113)
                      ·
                        rfl

theorem cell23_218724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3, 2, 2, 2, 2].length) (baseStart_218724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_218724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_218724 prefixEnd_218724 := by exact prefixLift 218724
  have htrace : WordTrace (prefixWord ++ tailWord_218724) baseStart_218724 baseEnd_218724 := by
    simpa [prefixWord, tailWord_218724, baseEnd_218724] using wordTrace_append hprefix tailTrace_218724
  have hstable : (prefixWord ++ tailWord_218724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218724).length < 2 ^ (prefixWord ++ tailWord_218724).sum := by decide
  have hdescent : baseEnd_218724 < baseStart_218724 := by decide
  rcases family_descends (prefixWord ++ tailWord_218724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218730 : List Nat := [3, 1, 3, 2, 1, 3, 2, 1, 7]
def baseStart_218730 : Nat := 118140960795 + 218730 * 2 ^ 59
def prefixEnd_218730 : Nat := 4983230072969 + 3 ^ 40 * 218730 * 2
def baseEnd_218730 : Nat := 12479291506448272396565

theorem tailTrace_218730 : CollatzResearch.WordTrace tailWord_218730 prefixEnd_218730 12479291506448272396565 := by
  unfold tailWord_218730
  simp only [CollatzResearch.WordTrace]
  refine ⟨1994434624396510238759411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5318492331724027303358429 1994434624396510238759411)
  ·
    refine ⟨2991651936594765358139117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1994434624396510238759411 2991651936594765358139117)
    ·
      refine ⟨1121869476223037009302169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2991651936594765358139117 1121869476223037009302169)
      ·
        refine ⟨841402107167277756976627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1121869476223037009302169 841402107167277756976627)
        ·
          refine ⟨1262103160750916635464941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 841402107167277756976627 1262103160750916635464941)
          ·
            refine ⟨473288685281593738299353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1262103160750916635464941 473288685281593738299353)
            ·
              refine ⟨354966513961195303724515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 473288685281593738299353 354966513961195303724515)
              ·
                refine ⟨532449770941792955586773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 354966513961195303724515 532449770941792955586773)
                ·
                  refine ⟨12479291506448272396565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 532449770941792955586773 12479291506448272396565)
                  ·
                    rfl

theorem cell23_218730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2, 1, 7].length) (baseStart_218730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_218730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_218730 prefixEnd_218730 := by exact prefixLift 218730
  have htrace : WordTrace (prefixWord ++ tailWord_218730) baseStart_218730 baseEnd_218730 := by
    simpa [prefixWord, tailWord_218730, baseEnd_218730] using wordTrace_append hprefix tailTrace_218730
  have hstable : (prefixWord ++ tailWord_218730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218730).length < 2 ^ (prefixWord ++ tailWord_218730).sum := by decide
  have hdescent : baseEnd_218730 < baseStart_218730 := by decide
  rcases family_descends (prefixWord ++ tailWord_218730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218763 : List Nat := [1, 1, 1, 1, 4, 1, 3, 3, 1, 3, 4]
def baseStart_218763 : Nat := 118140960795 + 218763 * 2 ^ 59
def prefixEnd_218763 : Nat := 4983230072969 + 3 ^ 40 * 218763 * 2
def baseEnd_218763 : Nat := 112330568419632822456433

theorem tailTrace_218763 : CollatzResearch.WordTrace tailWord_218763 prefixEnd_218763 112330568419632822456433 := by
  unfold tailWord_218763
  simp only [CollatzResearch.WordTrace]
  refine ⟨7978942106466487590988943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5319294737644325060659295 7978942106466487590988943)
  ·
    refine ⟨11968413159699731386483415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7978942106466487590988943 11968413159699731386483415)
    ·
      refine ⟨17952619739549597079725123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11968413159699731386483415 17952619739549597079725123)
      ·
        refine ⟨26928929609324395619587685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17952619739549597079725123 26928929609324395619587685)
        ·
          refine ⟨5049174301748324178672691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26928929609324395619587685 5049174301748324178672691)
          ·
            refine ⟨7573761452622486268009037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5049174301748324178672691 7573761452622486268009037)
            ·
              refine ⟨2840160544733432350503389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7573761452622486268009037 2840160544733432350503389)
              ·
                refine ⟨1065060204275037131438771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2840160544733432350503389 1065060204275037131438771)
                ·
                  refine ⟨1597590306412555697158157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1065060204275037131438771 1597590306412555697158157)
                  ·
                    refine ⟨599096364904708386434309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1597590306412555697158157 599096364904708386434309)
                    ·
                      refine ⟨112330568419632822456433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 599096364904708386434309 112330568419632822456433)
                      ·
                        rfl

theorem cell23_218763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 3, 1, 3, 4].length) (baseStart_218763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_218763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_218763 prefixEnd_218763 := by exact prefixLift 218763
  have htrace : WordTrace (prefixWord ++ tailWord_218763) baseStart_218763 baseEnd_218763 := by
    simpa [prefixWord, tailWord_218763, baseEnd_218763] using wordTrace_append hprefix tailTrace_218763
  have hstable : (prefixWord ++ tailWord_218763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218763).length < 2 ^ (prefixWord ++ tailWord_218763).sum := by decide
  have hdescent : baseEnd_218763 < baseStart_218763 := by decide
  rcases family_descends (prefixWord ++ tailWord_218763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218792 : List Nat := [2, 1, 7, 1, 1, 2, 2, 1, 2, 2, 2]
def baseStart_218792 : Nat := 118140960795 + 218792 * 2 ^ 59
def prefixEnd_218792 : Nat := 4983230072969 + 3 ^ 40 * 218792 * 2
def baseEnd_218792 : Nat := 112345459358613208993801

theorem tailTrace_218792 : CollatzResearch.WordTrace tailWord_218792 prefixEnd_218792 112345459358613208993801 := by
  unfold tailWord_218792
  simp only [CollatzResearch.WordTrace]
  refine ⟨3989999911680712771897315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5319999882240950362529753 3989999911680712771897315)
  ·
    refine ⟨5984999867521069157845973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3989999911680712771897315 5984999867521069157845973)
    ·
      refine ⟨140273434395025058387015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 5984999867521069157845973 140273434395025058387015)
      ·
        refine ⟨210410151592537587580523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140273434395025058387015 210410151592537587580523)
        ·
          refine ⟨315615227388806381370785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210410151592537587580523 315615227388806381370785)
          ·
            refine ⟨236711420541604786028089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 315615227388806381370785 236711420541604786028089)
            ·
              refine ⟨177533565406203589521067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 236711420541604786028089 177533565406203589521067)
              ·
                refine ⟨266300348109305384281601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177533565406203589521067 266300348109305384281601)
                ·
                  refine ⟨199725261081979038211201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 266300348109305384281601 199725261081979038211201)
                  ·
                    refine ⟨149793945811484278658401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 199725261081979038211201 149793945811484278658401)
                    ·
                      refine ⟨112345459358613208993801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 149793945811484278658401 112345459358613208993801)
                      ·
                        rfl

theorem cell23_218792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_218792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_218792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_218792 prefixEnd_218792 := by exact prefixLift 218792
  have htrace : WordTrace (prefixWord ++ tailWord_218792) baseStart_218792 baseEnd_218792 := by
    simpa [prefixWord, tailWord_218792, baseEnd_218792] using wordTrace_append hprefix tailTrace_218792
  have hstable : (prefixWord ++ tailWord_218792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218792).length < 2 ^ (prefixWord ++ tailWord_218792).sum := by decide
  have hdescent : baseEnd_218792 < baseStart_218792 := by decide
  rcases family_descends (prefixWord ++ tailWord_218792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218797 : List Nat := [1, 5, 2, 1, 1, 1, 2, 1, 1, 6, 2]
def baseStart_218797 : Nat := 118140960795 + 218797 * 2 ^ 59
def prefixEnd_218797 : Nat := 4983230072969 + 3 ^ 40 * 218797 * 2
def baseEnd_218797 : Nat := 112348026761885689431277

theorem tailTrace_218797 : CollatzResearch.WordTrace tailWord_218797 prefixEnd_218797 112348026761885689431277 := by
  unfold tailWord_218797
  simp only [CollatzResearch.WordTrace]
  refine ⟨7980182188343311397726645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5320121458895540931817763 7980182188343311397726645)
  ·
    refine ⟨748142080157185443536873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7980182188343311397726645 748142080157185443536873)
    ·
      refine ⟨561106560117889082652655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 748142080157185443536873 561106560117889082652655)
      ·
        refine ⟨841659840176833623978983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 561106560117889082652655 841659840176833623978983)
        ·
          refine ⟨1262489760265250435968475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 841659840176833623978983 1262489760265250435968475)
          ·
            refine ⟨1893734640397875653952713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1262489760265250435968475 1893734640397875653952713)
            ·
              refine ⟨1420300980298406740464535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1893734640397875653952713 1420300980298406740464535)
              ·
                refine ⟨2130451470447610110696803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1420300980298406740464535 2130451470447610110696803)
                ·
                  refine ⟨3195677205671415166045205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2130451470447610110696803 3195677205671415166045205)
                  ·
                    refine ⟨149797369015847585908369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3195677205671415166045205 149797369015847585908369)
                    ·
                      refine ⟨112348026761885689431277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 149797369015847585908369 112348026761885689431277)
                      ·
                        rfl

theorem cell23_218797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 1, 1, 6, 2].length) (baseStart_218797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_218797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_218797 prefixEnd_218797 := by exact prefixLift 218797
  have htrace : WordTrace (prefixWord ++ tailWord_218797) baseStart_218797 baseEnd_218797 := by
    simpa [prefixWord, tailWord_218797, baseEnd_218797] using wordTrace_append hprefix tailTrace_218797
  have hstable : (prefixWord ++ tailWord_218797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218797).length < 2 ^ (prefixWord ++ tailWord_218797).sum := by decide
  have hdescent : baseEnd_218797 < baseStart_218797 := by decide
  rcases family_descends (prefixWord ++ tailWord_218797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218841 : List Nat := [1, 2, 1, 2, 3, 5, 2, 2, 1, 4]
def baseStart_218841 : Nat := 118140960795 + 218841 * 2 ^ 59
def prefixEnd_218841 : Nat := 4983230072969 + 3 ^ 40 * 218841 * 2
def baseEnd_218841 : Nat := 37456873303561172427025

theorem tailTrace_218841 : CollatzResearch.WordTrace tailWord_218841 prefixEnd_218841 37456873303561172427025 := by
  unfold tailWord_218841
  simp only [CollatzResearch.WordTrace]
  refine ⟨7981787000183906912328377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5321191333455937941552251 7981787000183906912328377)
  ·
    refine ⟨5986340250137930184246283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7981787000183906912328377 5986340250137930184246283)
    ·
      refine ⟨8979510375206895276369425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5986340250137930184246283 8979510375206895276369425)
      ·
        refine ⟨6734632781405171457277069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8979510375206895276369425 6734632781405171457277069)
        ·
          refine ⟨2525487293026939296478901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6734632781405171457277069 2525487293026939296478901)
          ·
            refine ⟨236764433721275559044897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2525487293026939296478901 236764433721275559044897)
            ·
              refine ⟨177573325290956669283673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 236764433721275559044897 177573325290956669283673)
              ·
                refine ⟨133179993968217501962755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 177573325290956669283673 133179993968217501962755)
                ·
                  refine ⟨199769990952326252944133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 133179993968217501962755 199769990952326252944133)
                  ·
                    refine ⟨37456873303561172427025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 199769990952326252944133 37456873303561172427025)
                    ·
                      rfl

theorem cell23_218841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 2, 2, 1, 4].length) (baseStart_218841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_218841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_218841 prefixEnd_218841 := by exact prefixLift 218841
  have htrace : WordTrace (prefixWord ++ tailWord_218841) baseStart_218841 baseEnd_218841 := by
    simpa [prefixWord, tailWord_218841, baseEnd_218841] using wordTrace_append hprefix tailTrace_218841
  have hstable : (prefixWord ++ tailWord_218841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218841).length < 2 ^ (prefixWord ++ tailWord_218841).sum := by decide
  have hdescent : baseEnd_218841 < baseStart_218841 := by decide
  rcases family_descends (prefixWord ++ tailWord_218841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218847 : List Nat := [1, 1, 2, 3, 2, 2, 2, 3, 3, 1, 3]
def baseStart_218847 : Nat := 118140960795 + 218847 * 2 ^ 59
def prefixEnd_218847 : Nat := 4983230072969 + 3 ^ 40 * 218847 * 2
def baseEnd_218847 : Nat := 112373700794610493806047

theorem tailTrace_218847 : CollatzResearch.WordTrace tailWord_218847 prefixEnd_218847 112373700794610493806047 := by
  unfold tailWord_218847
  simp only [CollatzResearch.WordTrace]
  refine ⟨7982005838162169937046795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5321337225441446624697863 7982005838162169937046795)
  ·
    refine ⟨11973008757243254905570193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7982005838162169937046795 11973008757243254905570193)
    ·
      refine ⟨8979756567932441179177645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11973008757243254905570193 8979756567932441179177645)
      ·
        refine ⟨3367408712974665442191617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8979756567932441179177645 3367408712974665442191617)
        ·
          refine ⟨2525556534730999081643713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3367408712974665442191617 2525556534730999081643713)
          ·
            refine ⟨1894167401048249311232785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2525556534730999081643713 1894167401048249311232785)
            ·
              refine ⟨1420625550786186983424589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1894167401048249311232785 1420625550786186983424589)
              ·
                refine ⟨532734581544820118784221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1420625550786186983424589 532734581544820118784221)
                ·
                  refine ⟨199775468079307544544083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 532734581544820118784221 199775468079307544544083)
                  ·
                    refine ⟨299663202118961316816125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 199775468079307544544083 299663202118961316816125)
                    ·
                      refine ⟨112373700794610493806047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 299663202118961316816125 112373700794610493806047)
                      ·
                        rfl

theorem cell23_218847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 3, 3, 1, 3].length) (baseStart_218847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_218847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_218847 prefixEnd_218847 := by exact prefixLift 218847
  have htrace : WordTrace (prefixWord ++ tailWord_218847) baseStart_218847 baseEnd_218847 := by
    simpa [prefixWord, tailWord_218847, baseEnd_218847] using wordTrace_append hprefix tailTrace_218847
  have hstable : (prefixWord ++ tailWord_218847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218847).length < 2 ^ (prefixWord ++ tailWord_218847).sum := by decide
  have hdescent : baseEnd_218847 < baseStart_218847 := by decide
  rcases family_descends (prefixWord ++ tailWord_218847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218868 : List Nat := [2, 6, 1, 1, 1, 3, 1, 1, 2, 2, 3]
def baseStart_218868 : Nat := 118140960795 + 218868 * 2 ^ 59
def prefixEnd_218868 : Nat := 4983230072969 + 3 ^ 40 * 218868 * 2
def baseEnd_218868 : Nat := 112384483888354911643451

theorem tailTrace_218868 : CollatzResearch.WordTrace tailWord_218868 prefixEnd_218868 112384483888354911643451 := by
  unfold tailWord_218868
  simp only [CollatzResearch.WordTrace]
  refine ⟨3991385885543045261780629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5321847847390727015707505 3991385885543045261780629)
  ·
    refine ⟨187096213384830246645967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 3991385885543045261780629 187096213384830246645967)
    ·
      refine ⟨280644320077245369968951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187096213384830246645967 280644320077245369968951)
      ·
        refine ⟨420966480115868054953427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280644320077245369968951 420966480115868054953427)
        ·
          refine ⟨631449720173802082430141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 420966480115868054953427 631449720173802082430141)
          ·
            refine ⟨236793645065175780911303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 631449720173802082430141 236793645065175780911303)
            ·
              refine ⟨355190467597763671366955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 236793645065175780911303 355190467597763671366955)
              ·
                refine ⟨532785701396645507050433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 355190467597763671366955 532785701396645507050433)
                ·
                  refine ⟨399589276047484130287825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 532785701396645507050433 399589276047484130287825)
                  ·
                    refine ⟨299691957035613097715869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 399589276047484130287825 299691957035613097715869)
                    ·
                      refine ⟨112384483888354911643451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 299691957035613097715869 112384483888354911643451)
                      ·
                        rfl

theorem cell23_218868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_218868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_218868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_218868 prefixEnd_218868 := by exact prefixLift 218868
  have htrace : WordTrace (prefixWord ++ tailWord_218868) baseStart_218868 baseEnd_218868 := by
    simpa [prefixWord, tailWord_218868, baseEnd_218868] using wordTrace_append hprefix tailTrace_218868
  have hstable : (prefixWord ++ tailWord_218868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218868).length < 2 ^ (prefixWord ++ tailWord_218868).sum := by decide
  have hdescent : baseEnd_218868 < baseStart_218868 := by decide
  rcases family_descends (prefixWord ++ tailWord_218868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218880 : List Nat := [2, 1, 1, 2, 1, 1, 2, 3, 6, 4]
def baseStart_218880 : Nat := 118140960795 + 218880 * 2 ^ 59
def prefixEnd_218880 : Nat := 4983230072969 + 3 ^ 40 * 218880 * 2
def baseEnd_218880 : Nat := 37463548552069621564465

theorem tailTrace_218880 : CollatzResearch.WordTrace tailWord_218880 prefixEnd_218880 37463548552069621564465 := by
  unfold tailWord_218880
  simp only [CollatzResearch.WordTrace]
  refine ⟨3991604723521308286499047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5322139631361744381998729 3991604723521308286499047)
  ·
    refine ⟨5987407085281962429748571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3991604723521308286499047 5987407085281962429748571)
    ·
      refine ⟨8981110627922943644622857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5987407085281962429748571 8981110627922943644622857)
      ·
        refine ⟨6735832970942207733467143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8981110627922943644622857 6735832970942207733467143)
        ·
          refine ⟨10103749456413311600200715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6735832970942207733467143 10103749456413311600200715)
          ·
            refine ⟨15155624184619967400301073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10103749456413311600200715 15155624184619967400301073)
            ·
              refine ⟨11366718138464975550225805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15155624184619967400301073 11366718138464975550225805)
              ·
                refine ⟨4262519301924365831334677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11366718138464975550225805 4262519301924365831334677)
                ·
                  refine ⟨199805592277704648343813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4262519301924365831334677 199805592277704648343813)
                  ·
                    refine ⟨37463548552069621564465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 199805592277704648343813 37463548552069621564465)
                    ·
                      rfl

theorem cell23_218880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 6, 4].length) (baseStart_218880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_218880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_218880 prefixEnd_218880 := by exact prefixLift 218880
  have htrace : WordTrace (prefixWord ++ tailWord_218880) baseStart_218880 baseEnd_218880 := by
    simpa [prefixWord, tailWord_218880, baseEnd_218880] using wordTrace_append hprefix tailTrace_218880
  have hstable : (prefixWord ++ tailWord_218880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218880).length < 2 ^ (prefixWord ++ tailWord_218880).sum := by decide
  have hdescent : baseEnd_218880 < baseStart_218880 := by decide
  rcases family_descends (prefixWord ++ tailWord_218880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218884 : List Nat := [2, 3, 2, 2, 1, 2, 4, 1, 1, 5]
def baseStart_218884 : Nat := 118140960795 + 218884 * 2 ^ 59
def prefixEnd_218884 : Nat := 4983230072969 + 3 ^ 40 * 218884 * 2
def baseEnd_218884 : Nat := 37464233192942283014459

theorem tailTrace_218884 : CollatzResearch.WordTrace tailWord_218884 prefixEnd_218884 37464233192942283014459 := by
  unfold tailWord_218884
  simp only [CollatzResearch.WordTrace]
  refine ⟨3991677669514062628071853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5322236892685416837429137 3991677669514062628071853)
  ·
    refine ⟨1496879126067773485526945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3991677669514062628071853 1496879126067773485526945)
    ·
      refine ⟨1122659344550830114145209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1496879126067773485526945 1122659344550830114145209)
      ·
        refine ⟨841994508413122585608907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1122659344550830114145209 841994508413122585608907)
        ·
          refine ⟨1262991762619683878413361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 841994508413122585608907 1262991762619683878413361)
          ·
            refine ⟨947243821964762908810021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1262991762619683878413361 947243821964762908810021)
            ·
              refine ⟨177608216618393045401879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 947243821964762908810021 177608216618393045401879)
              ·
                refine ⟨266412324927589568102819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177608216618393045401879 266412324927589568102819)
                ·
                  refine ⟨399618487391384352154229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 266412324927589568102819 399618487391384352154229)
                  ·
                    refine ⟨37464233192942283014459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 399618487391384352154229 37464233192942283014459)
                    ·
                      rfl

theorem cell23_218884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 4, 1, 1, 5].length) (baseStart_218884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_218884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_218884 prefixEnd_218884 := by exact prefixLift 218884
  have htrace : WordTrace (prefixWord ++ tailWord_218884) baseStart_218884 baseEnd_218884 := by
    simpa [prefixWord, tailWord_218884, baseEnd_218884] using wordTrace_append hprefix tailTrace_218884
  have hstable : (prefixWord ++ tailWord_218884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218884).length < 2 ^ (prefixWord ++ tailWord_218884).sum := by decide
  have hdescent : baseEnd_218884 < baseStart_218884 := by decide
  rcases family_descends (prefixWord ++ tailWord_218884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218898 : List Nat := [3, 2, 4, 1, 1, 1, 2, 4, 1, 1, 3]
def baseStart_218898 : Nat := 118140960795 + 218898 * 2 ^ 59
def prefixEnd_218898 : Nat := 4983230072969 + 3 ^ 40 * 218898 * 2
def baseEnd_218898 : Nat := 112399888307989794268313

theorem tailTrace_218898 : CollatzResearch.WordTrace tailWord_218898 prefixEnd_218898 112399888307989794268313 := by
  unfold tailWord_218898
  simp only [CollatzResearch.WordTrace]
  refine ⟨1995966490244351411788337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5322577307318270431435565 1995966490244351411788337)
  ·
    refine ⟨1496974867683263558841253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1995966490244351411788337 1496974867683263558841253)
    ·
      refine ⟨280682787690611917282735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1496974867683263558841253 280682787690611917282735)
      ·
        refine ⟨421024181535917875924103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280682787690611917282735 421024181535917875924103)
        ·
          refine ⟨631536272303876813886155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 421024181535917875924103 631536272303876813886155)
          ·
            refine ⟨947304408455815220829233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 631536272303876813886155 947304408455815220829233)
            ·
              refine ⟨710478306341861415621925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 947304408455815220829233 710478306341861415621925)
              ·
                refine ⟨133214682439099015429111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 710478306341861415621925 133214682439099015429111)
                ·
                  refine ⟨199822023658648523143667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 133214682439099015429111 199822023658648523143667)
                  ·
                    refine ⟨299733035487972784715501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 199822023658648523143667 299733035487972784715501)
                    ·
                      refine ⟨112399888307989794268313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 299733035487972784715501 112399888307989794268313)
                      ·
                        rfl

theorem cell23_218898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 4, 1, 1, 3].length) (baseStart_218898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_218898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_218898 prefixEnd_218898 := by exact prefixLift 218898
  have htrace : WordTrace (prefixWord ++ tailWord_218898) baseStart_218898 baseEnd_218898 := by
    simpa [prefixWord, tailWord_218898, baseEnd_218898] using wordTrace_append hprefix tailTrace_218898
  have hstable : (prefixWord ++ tailWord_218898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218898).length < 2 ^ (prefixWord ++ tailWord_218898).sum := by decide
  have hdescent : baseEnd_218898 < baseStart_218898 := by decide
  rcases family_descends (prefixWord ++ tailWord_218898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218904 : List Nat := [2, 1, 2, 3, 1, 1, 3, 3, 3, 2, 2]
def baseStart_218904 : Nat := 118140960795 + 218904 * 2 ^ 59
def prefixEnd_218904 : Nat := 4983230072969 + 3 ^ 40 * 218904 * 2
def baseEnd_218904 : Nat := 112402969191916770793285

theorem tailTrace_218904 : CollatzResearch.WordTrace tailWord_218904 prefixEnd_218904 112402969191916770793285 := by
  unfold tailWord_218904
  simp only [CollatzResearch.WordTrace]
  refine ⟨3992042399477834335935883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5322723199303779114581177 3992042399477834335935883)
  ·
    refine ⟨5988063599216751503903825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3992042399477834335935883 5988063599216751503903825)
    ·
      refine ⟨4491047699412563627927869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5988063599216751503903825 4491047699412563627927869)
      ·
        refine ⟨1684142887279711360472951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4491047699412563627927869 1684142887279711360472951)
        ·
          refine ⟨2526214330919567040709427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1684142887279711360472951 2526214330919567040709427)
          ·
            refine ⟨3789321496379350561064141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2526214330919567040709427 3789321496379350561064141)
            ·
              refine ⟨1420995561142256460399053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3789321496379350561064141 1420995561142256460399053)
              ·
                refine ⟨532873335428346172649645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1420995561142256460399053 532873335428346172649645)
                ·
                  refine ⟨199827500785629814743617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 532873335428346172649645 199827500785629814743617)
                  ·
                    refine ⟨149870625589222361057713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 199827500785629814743617 149870625589222361057713)
                    ·
                      refine ⟨112402969191916770793285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 149870625589222361057713 112402969191916770793285)
                      ·
                        rfl

theorem cell23_218904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 3, 3, 2, 2].length) (baseStart_218904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_218904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_218904 prefixEnd_218904 := by exact prefixLift 218904
  have htrace : WordTrace (prefixWord ++ tailWord_218904) baseStart_218904 baseEnd_218904 := by
    simpa [prefixWord, tailWord_218904, baseEnd_218904] using wordTrace_append hprefix tailTrace_218904
  have hstable : (prefixWord ++ tailWord_218904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218904).length < 2 ^ (prefixWord ++ tailWord_218904).sum := by decide
  have hdescent : baseEnd_218904 < baseStart_218904 := by decide
  rcases family_descends (prefixWord ++ tailWord_218904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218917 : List Nat := [1, 3, 1, 2, 3, 2, 3, 1, 1, 2, 4]
def baseStart_218917 : Nat := 118140960795 + 218917 * 2 ^ 59
def prefixEnd_218917 : Nat := 4983230072969 + 3 ^ 40 * 218917 * 2
def baseEnd_218917 : Nat := 112409644440425219930725

theorem tailTrace_218917 : CollatzResearch.WordTrace tailWord_218917 prefixEnd_218917 112409644440425219930725 := by
  unfold tailWord_218917
  simp only [CollatzResearch.WordTrace]
  refine ⟨7984558947908571892095005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5323039298605714594730003 7984558947908571892095005)
  ·
    refine ⟨2994209605465714459535627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7984558947908571892095005 2994209605465714459535627)
    ·
      refine ⟨4491314408198571689303441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2994209605465714459535627 4491314408198571689303441)
      ·
        refine ⟨3368485806148928766977581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4491314408198571689303441 3368485806148928766977581)
        ·
          refine ⟨1263182177305848287616593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3368485806148928766977581 1263182177305848287616593)
          ·
            refine ⟨947386632979386215712445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1263182177305848287616593 947386632979386215712445)
            ·
              refine ⟨355269987367269830892167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 947386632979386215712445 355269987367269830892167)
              ·
                refine ⟨532904981050904746338251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 355269987367269830892167 532904981050904746338251)
                ·
                  refine ⟨799357471576357119507377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 532904981050904746338251 799357471576357119507377)
                  ·
                    refine ⟨599518103682267839630533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 799357471576357119507377 599518103682267839630533)
                    ·
                      refine ⟨112409644440425219930725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 599518103682267839630533 112409644440425219930725)
                      ·
                        rfl

theorem cell23_218917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 1, 1, 2, 4].length) (baseStart_218917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_218917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_218917 prefixEnd_218917 := by exact prefixLift 218917
  have htrace : WordTrace (prefixWord ++ tailWord_218917) baseStart_218917 baseEnd_218917 := by
    simpa [prefixWord, tailWord_218917, baseEnd_218917] using wordTrace_append hprefix tailTrace_218917
  have hstable : (prefixWord ++ tailWord_218917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218917).length < 2 ^ (prefixWord ++ tailWord_218917).sum := by decide
  have hdescent : baseEnd_218917 < baseStart_218917 := by decide
  rcases family_descends (prefixWord ++ tailWord_218917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218924 : List Nat := [2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 3]
def baseStart_218924 : Nat := 118140960795 + 218924 * 2 ^ 59
def prefixEnd_218924 : Nat := 4983230072969 + 3 ^ 40 * 218924 * 2
def baseEnd_218924 : Nat := 112413238805006692543193

theorem tailTrace_218924 : CollatzResearch.WordTrace tailWord_218924 prefixEnd_218924 112413238805006692543193 := by
  unfold tailWord_218924
  simp only [CollatzResearch.WordTrace]
  refine ⟨3992407129441606043799913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5323209505922141391733217 3992407129441606043799913)
  ·
    refine ⟨2994305347081204532849935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3992407129441606043799913 2994305347081204532849935)
    ·
      refine ⟨4491458020621806799274903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2994305347081204532849935 4491458020621806799274903)
      ·
        refine ⟨6737187030932710198912355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4491458020621806799274903 6737187030932710198912355)
        ·
          refine ⟨10105780546399065298368533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6737187030932710198912355 10105780546399065298368533)
          ·
            refine ⟨473708463112456185861025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 10105780546399065298368533 473708463112456185861025)
            ·
              refine ⟨355281347334342139395769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 473708463112456185861025 355281347334342139395769)
              ·
                refine ⟨266461010500756604546827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 355281347334342139395769 266461010500756604546827)
                ·
                  refine ⟨399691515751134906820241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 266461010500756604546827 399691515751134906820241)
                  ·
                    refine ⟨299768636813351180115181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 399691515751134906820241 299768636813351180115181)
                    ·
                      refine ⟨112413238805006692543193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 299768636813351180115181 112413238805006692543193)
                      ·
                        rfl

theorem cell23_218924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 3].length) (baseStart_218924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_218924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_218924 prefixEnd_218924 := by exact prefixLift 218924
  have htrace : WordTrace (prefixWord ++ tailWord_218924) baseStart_218924 baseEnd_218924 := by
    simpa [prefixWord, tailWord_218924, baseEnd_218924] using wordTrace_append hprefix tailTrace_218924
  have hstable : (prefixWord ++ tailWord_218924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218924).length < 2 ^ (prefixWord ++ tailWord_218924).sum := by decide
  have hdescent : baseEnd_218924 < baseStart_218924 := by decide
  rcases family_descends (prefixWord ++ tailWord_218924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218938 : List Nat := [3, 1, 1, 1, 5, 1, 3, 3, 1, 2, 2]
def baseStart_218938 : Nat := 118140960795 + 218938 * 2 ^ 59
def prefixEnd_218938 : Nat := 4983230072969 + 3 ^ 40 * 218938 * 2
def baseEnd_218938 : Nat := 112420427534169637768129

theorem tailTrace_218938 : CollatzResearch.WordTrace tailWord_218938 prefixEnd_218938 112420427534169637768129 := by
  unfold tailWord_218938
  simp only [CollatzResearch.WordTrace]
  refine ⟨1996331220208123119652367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5323549920554994985739645 1996331220208123119652367)
  ·
    refine ⟨2994496830312184679478551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1996331220208123119652367 2994496830312184679478551)
    ·
      refine ⟨4491745245468277019217827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2994496830312184679478551 4491745245468277019217827)
      ·
        refine ⟨6737617868202415528826741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4491745245468277019217827 6737617868202415528826741)
        ·
          refine ⟨631651675143976455827507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6737617868202415528826741 631651675143976455827507)
          ·
            refine ⟨947477512715964683741261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 631651675143976455827507 947477512715964683741261)
            ·
              refine ⟨355304067268486756402973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 947477512715964683741261 355304067268486756402973)
              ·
                refine ⟨133239025225682533651115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 355304067268486756402973 133239025225682533651115)
                ·
                  refine ⟨199858537838523800476673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 133239025225682533651115 199858537838523800476673)
                  ·
                    refine ⟨149893903378892850357505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 199858537838523800476673 149893903378892850357505)
                    ·
                      refine ⟨112420427534169637768129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 149893903378892850357505 112420427534169637768129)
                      ·
                        rfl

theorem cell23_218938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3, 3, 1, 2, 2].length) (baseStart_218938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_218938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_218938 prefixEnd_218938 := by exact prefixLift 218938
  have htrace : WordTrace (prefixWord ++ tailWord_218938) baseStart_218938 baseEnd_218938 := by
    simpa [prefixWord, tailWord_218938, baseEnd_218938] using wordTrace_append hprefix tailTrace_218938
  have hstable : (prefixWord ++ tailWord_218938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218938).length < 2 ^ (prefixWord ++ tailWord_218938).sum := by decide
  have hdescent : baseEnd_218938 < baseStart_218938 := by decide
  rcases family_descends (prefixWord ++ tailWord_218938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218954 : List Nat := [3, 1, 2, 1, 1, 1, 4, 4, 2, 1, 3]
def baseStart_218954 : Nat := 118140960795 + 218954 * 2 ^ 59
def prefixEnd_218954 : Nat := 4983230072969 + 3 ^ 40 * 218954 * 2
def baseEnd_218954 : Nat := 112428643224641575168055

theorem tailTrace_218954 : CollatzResearch.WordTrace tailWord_218954 prefixEnd_218954 112428643224641575168055 := by
  unfold tailWord_218954
  simp only [CollatzResearch.WordTrace]
  refine ⟨1996477112193631802797979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5323938965849684807461277 1996477112193631802797979)
  ·
    refine ⟨2994715668290447704196969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1996477112193631802797979 2994715668290447704196969)
    ·
      refine ⟨2246036751217835778147727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2994715668290447704196969 2246036751217835778147727)
      ·
        refine ⟨3369055126826753667221591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2246036751217835778147727 3369055126826753667221591)
        ·
          refine ⟨5053582690240130500832387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3369055126826753667221591 5053582690240130500832387)
          ·
            refine ⟨7580374035360195751248581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5053582690240130500832387 7580374035360195751248581)
            ·
              refine ⟨1421320131630036703359109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7580374035360195751248581 1421320131630036703359109)
              ·
                refine ⟨266497524680631881879833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1421320131630036703359109 266497524680631881879833)
                ·
                  refine ⟨199873143510473911409875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 266497524680631881879833 199873143510473911409875)
                  ·
                    refine ⟨299809715265710867114813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 199873143510473911409875 299809715265710867114813)
                    ·
                      refine ⟨112428643224641575168055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 299809715265710867114813 112428643224641575168055)
                      ·
                        rfl

theorem cell23_218954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 4, 2, 1, 3].length) (baseStart_218954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_218954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_218954 prefixEnd_218954 := by exact prefixLift 218954
  have htrace : WordTrace (prefixWord ++ tailWord_218954) baseStart_218954 baseEnd_218954 := by
    simpa [prefixWord, tailWord_218954, baseEnd_218954] using wordTrace_append hprefix tailTrace_218954
  have hstable : (prefixWord ++ tailWord_218954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218954).length < 2 ^ (prefixWord ++ tailWord_218954).sum := by decide
  have hdescent : baseEnd_218954 < baseStart_218954 := by decide
  rcases family_descends (prefixWord ++ tailWord_218954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218960 : List Nat := [2, 1, 1, 1, 1, 4, 1, 3, 2, 3, 4]
def baseStart_218960 : Nat := 118140960795 + 218960 * 2 ^ 59
def prefixEnd_218960 : Nat := 4983230072969 + 3 ^ 40 * 218960 * 2
def baseEnd_218960 : Nat := 112431724108568551693027

theorem tailTrace_218960 : CollatzResearch.WordTrace tailWord_218960 prefixEnd_218960 112431724108568551693027 := by
  unfold tailWord_218960
  simp only [CollatzResearch.WordTrace]
  refine ⟨3993063643376395117955167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5324084857835193490606889 3993063643376395117955167)
  ·
    refine ⟨5989595465064592676932751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3993063643376395117955167 5989595465064592676932751)
    ·
      refine ⟨8984393197596889015399127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5989595465064592676932751 8984393197596889015399127)
      ·
        refine ⟨13476589796395333523098691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8984393197596889015399127 13476589796395333523098691)
        ·
          refine ⟨20214884694593000284648037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13476589796395333523098691 20214884694593000284648037)
          ·
            refine ⟨3790290880236187553371507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20214884694593000284648037 3790290880236187553371507)
            ·
              refine ⟨5685436320354281330057261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3790290880236187553371507 5685436320354281330057261)
              ·
                refine ⟨2132038620132855498771473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5685436320354281330057261 2132038620132855498771473)
                ·
                  refine ⟨1599028965099641624078605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2132038620132855498771473 1599028965099641624078605)
                  ·
                    refine ⟨599635861912365609029477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1599028965099641624078605 599635861912365609029477)
                    ·
                      refine ⟨112431724108568551693027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 599635861912365609029477 112431724108568551693027)
                      ·
                        rfl

theorem cell23_218960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3, 4].length) (baseStart_218960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_218960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_218960 prefixEnd_218960 := by exact prefixLift 218960
  have htrace : WordTrace (prefixWord ++ tailWord_218960) baseStart_218960 baseEnd_218960 := by
    simpa [prefixWord, tailWord_218960, baseEnd_218960] using wordTrace_append hprefix tailTrace_218960
  have hstable : (prefixWord ++ tailWord_218960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218960).length < 2 ^ (prefixWord ++ tailWord_218960).sum := by decide
  have hdescent : baseEnd_218960 < baseStart_218960 := by decide
  rcases family_descends (prefixWord ++ tailWord_218960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218970 : List Nat := [3, 1, 1, 2, 1, 3, 2, 1, 1, 8]
def baseStart_218970 : Nat := 118140960795 + 218970 * 2 ^ 59
def prefixEnd_218970 : Nat := 4983230072969 + 3 ^ 40 * 218970 * 2
def baseEnd_218970 : Nat := 37478952971704504189327

theorem tailTrace_218970 : CollatzResearch.WordTrace tailWord_218970 prefixEnd_218970 37478952971704504189327 := by
  unfold tailWord_218970
  simp only [CollatzResearch.WordTrace]
  refine ⟨1996623004179140485943591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5324328011144374629182909 1996623004179140485943591)
  ·
    refine ⟨2994934506268710728915387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1996623004179140485943591 2994934506268710728915387)
    ·
      refine ⟨4492401759403066093373081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2994934506268710728915387 4492401759403066093373081)
      ·
        refine ⟨3369301319552299570029811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4492401759403066093373081 3369301319552299570029811)
        ·
          refine ⟨5053951979328449355044717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3369301319552299570029811 5053951979328449355044717)
          ·
            refine ⟨1895231992248168508141769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5053951979328449355044717 1895231992248168508141769)
            ·
              refine ⟨1421423994186126381106327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1895231992248168508141769 1421423994186126381106327)
              ·
                refine ⟨2132135991279189571659491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1421423994186126381106327 2132135991279189571659491)
                ·
                  refine ⟨3198203986918784357489237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2132135991279189571659491 3198203986918784357489237)
                  ·
                    refine ⟨37478952971704504189327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 3198203986918784357489237 37478952971704504189327)
                    ·
                      rfl

theorem cell23_218970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 1, 1, 8].length) (baseStart_218970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_218970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_218970 prefixEnd_218970 := by exact prefixLift 218970
  have htrace : WordTrace (prefixWord ++ tailWord_218970) baseStart_218970 baseEnd_218970 := by
    simpa [prefixWord, tailWord_218970, baseEnd_218970] using wordTrace_append hprefix tailTrace_218970
  have hstable : (prefixWord ++ tailWord_218970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218970).length < 2 ^ (prefixWord ++ tailWord_218970).sum := by decide
  have hdescent : baseEnd_218970 < baseStart_218970 := by decide
  rcases family_descends (prefixWord ++ tailWord_218970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218997 : List Nat := [1, 3, 4, 1, 1, 1, 1, 3, 2, 1, 5]
def baseStart_218997 : Nat := 118140960795 + 218997 * 2 ^ 59
def prefixEnd_218997 : Nat := 4983230072969 + 3 ^ 40 * 218997 * 2
def baseEnd_218997 : Nat := 112450722892784906930357

theorem tailTrace_218997 : CollatzResearch.WordTrace tailWord_218997 prefixEnd_218997 112450722892784906930357 := by
  unfold tailWord_218997
  simp only [CollatzResearch.WordTrace]
  refine ⟨7987476787618745555007245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5324984525079163703338163 7987476787618745555007245)
  ·
    refine ⟨2995303795357029583127717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7987476787618745555007245 2995303795357029583127717)
    ·
      refine ⟨561619461629443046836447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2995303795357029583127717 561619461629443046836447)
      ·
        refine ⟨842429192444164570254671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 561619461629443046836447 842429192444164570254671)
        ·
          refine ⟨1263643788666246855382007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 842429192444164570254671 1263643788666246855382007)
          ·
            refine ⟨1895465682999370283073011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1263643788666246855382007 1895465682999370283073011)
            ·
              refine ⟨2843198524499055424609517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1895465682999370283073011 2843198524499055424609517)
              ·
                refine ⟨1066199446687145784228569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2843198524499055424609517 1066199446687145784228569)
                ·
                  refine ⟨799649585015359338171427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1066199446687145784228569 799649585015359338171427)
                  ·
                    refine ⟨1199474377523039007257141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 799649585015359338171427 1199474377523039007257141)
                    ·
                      refine ⟨112450722892784906930357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1199474377523039007257141 112450722892784906930357)
                      ·
                        rfl

theorem cell23_218997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_218997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_218997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_218997 prefixEnd_218997 := by exact prefixLift 218997
  have htrace : WordTrace (prefixWord ++ tailWord_218997) baseStart_218997 baseEnd_218997 := by
    simpa [prefixWord, tailWord_218997, baseEnd_218997] using wordTrace_append hprefix tailTrace_218997
  have hstable : (prefixWord ++ tailWord_218997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218997).length < 2 ^ (prefixWord ++ tailWord_218997).sum := by decide
  have hdescent : baseEnd_218997 < baseStart_218997 := by decide
  rcases family_descends (prefixWord ++ tailWord_218997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219011 : List Nat := [1, 1, 1, 3, 4, 2, 1, 4, 2, 2, 2]
def baseStart_219011 : Nat := 118140960795 + 219011 * 2 ^ 59
def prefixEnd_219011 : Nat := 4983230072969 + 3 ^ 40 * 219011 * 2
def baseEnd_219011 : Nat := 112457911621947852155293

theorem tailTrace_219011 : CollatzResearch.WordTrace tailWord_219011 prefixEnd_219011 112457911621947852155293 := by
  unfold tailWord_219011
  simp only [CollatzResearch.WordTrace]
  refine ⟨7987987409568025946016887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5325324939712017297344591 7987987409568025946016887)
  ·
    refine ⟨11981981114352038919025331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7987987409568025946016887 11981981114352038919025331)
    ·
      refine ⟨17972971671528058378537997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11981981114352038919025331 17972971671528058378537997)
      ·
        refine ⟨6739864376823021891951749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17972971671528058378537997 6739864376823021891951749)
        ·
          refine ⟨1263724570654316604740953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6739864376823021891951749 1263724570654316604740953)
          ·
            refine ⟨947793427990737453555715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1263724570654316604740953 947793427990737453555715)
            ·
              refine ⟨1421690141986106180333573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 947793427990737453555715 1421690141986106180333573)
              ·
                refine ⟨266566901622394908812545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1421690141986106180333573 266566901622394908812545)
                ·
                  refine ⟨199925176216796181609409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 266566901622394908812545 199925176216796181609409)
                  ·
                    refine ⟨149943882162597136207057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 199925176216796181609409 149943882162597136207057)
                    ·
                      refine ⟨112457911621947852155293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 149943882162597136207057 112457911621947852155293)
                      ·
                        rfl

theorem cell23_219011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 4, 2, 2, 2].length) (baseStart_219011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_219011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_219011 prefixEnd_219011 := by exact prefixLift 219011
  have htrace : WordTrace (prefixWord ++ tailWord_219011) baseStart_219011 baseEnd_219011 := by
    simpa [prefixWord, tailWord_219011, baseEnd_219011] using wordTrace_append hprefix tailTrace_219011
  have hstable : (prefixWord ++ tailWord_219011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219011).length < 2 ^ (prefixWord ++ tailWord_219011).sum := by decide
  have hdescent : baseEnd_219011 < baseStart_219011 := by decide
  rcases family_descends (prefixWord ++ tailWord_219011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219020 : List Nat := [2, 2, 1, 2, 1, 2, 1, 1, 2, 1, 8]
def baseStart_219020 : Nat := 118140960795 + 219020 * 2 ^ 59
def prefixEnd_219020 : Nat := 4983230072969 + 3 ^ 40 * 219020 * 2
def baseEnd_219020 : Nat := 112462532947838316942751

theorem tailTrace_219020 : CollatzResearch.WordTrace tailWord_219020 prefixEnd_219020 112462532947838316942751 := by
  unfold tailWord_219020
  simp only [CollatzResearch.WordTrace]
  refine ⟨3994157833267710241547257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5325543777690280322063009 3994157833267710241547257)
  ·
    refine ⟨2995618374950782681160443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3994157833267710241547257 2995618374950782681160443)
    ·
      refine ⟨4493427562426174021740665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2995618374950782681160443 4493427562426174021740665)
      ·
        refine ⟨3370070671819630516305499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4493427562426174021740665 3370070671819630516305499)
        ·
          refine ⟨5055106007729445774458249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3370070671819630516305499 5055106007729445774458249)
          ·
            refine ⟨3791329505797084330843687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5055106007729445774458249 3791329505797084330843687)
            ·
              refine ⟨5686994258695626496265531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3791329505797084330843687 5686994258695626496265531)
              ·
                refine ⟨8530491388043439744398297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5686994258695626496265531 8530491388043439744398297)
                ·
                  refine ⟨6397868541032579808298723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8530491388043439744398297 6397868541032579808298723)
                  ·
                    refine ⟨9596802811548869712448085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6397868541032579808298723 9596802811548869712448085)
                    ·
                      refine ⟨112462532947838316942751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 9596802811548869712448085 112462532947838316942751)
                      ·
                        rfl

theorem cell23_219020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 2, 1, 8].length) (baseStart_219020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_219020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_219020 prefixEnd_219020 := by exact prefixLift 219020
  have htrace : WordTrace (prefixWord ++ tailWord_219020) baseStart_219020 baseEnd_219020 := by
    simpa [prefixWord, tailWord_219020, baseEnd_219020] using wordTrace_append hprefix tailTrace_219020
  have hstable : (prefixWord ++ tailWord_219020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219020).length < 2 ^ (prefixWord ++ tailWord_219020).sum := by decide
  have hdescent : baseEnd_219020 < baseStart_219020 := by decide
  rcases family_descends (prefixWord ++ tailWord_219020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219028 : List Nat := [2, 4, 2, 1, 1, 2, 2, 3, 2, 2, 2]
def baseStart_219028 : Nat := 118140960795 + 219028 * 2 ^ 59
def prefixEnd_219028 : Nat := 4983230072969 + 3 ^ 40 * 219028 * 2
def baseEnd_219028 : Nat := 112466640793074285642715

theorem tailTrace_219028 : CollatzResearch.WordTrace tailWord_219028 prefixEnd_219028 112466640793074285642715 := by
  unfold tailWord_219028
  simp only [CollatzResearch.WordTrace]
  refine ⟨3994303725253218924692869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5325738300337625232923825 3994303725253218924692869)
  ·
    refine ⟨748931948484978548379913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3994303725253218924692869 748931948484978548379913)
    ·
      refine ⟨561698961363733911284935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 748931948484978548379913 561698961363733911284935)
      ·
        refine ⟨842548442045600866927403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 561698961363733911284935 842548442045600866927403)
        ·
          refine ⟨1263822663068401300391105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 842548442045600866927403 1263822663068401300391105)
          ·
            refine ⟨947866997301300975293329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1263822663068401300391105 947866997301300975293329)
            ·
              refine ⟨710900247975975731469997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 947866997301300975293329 710900247975975731469997)
              ·
                refine ⟨266587592990990899301249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 710900247975975731469997 266587592990990899301249)
                ·
                  refine ⟨199940694743243174475937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 266587592990990899301249 199940694743243174475937)
                  ·
                    refine ⟨149955521057432380856953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 199940694743243174475937 149955521057432380856953)
                    ·
                      refine ⟨112466640793074285642715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 149955521057432380856953 112466640793074285642715)
                      ·
                        rfl

theorem cell23_219028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 3, 2, 2, 2].length) (baseStart_219028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_219028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_219028 prefixEnd_219028 := by exact prefixLift 219028
  have htrace : WordTrace (prefixWord ++ tailWord_219028) baseStart_219028 baseEnd_219028 := by
    simpa [prefixWord, tailWord_219028, baseEnd_219028] using wordTrace_append hprefix tailTrace_219028
  have hstable : (prefixWord ++ tailWord_219028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219028).length < 2 ^ (prefixWord ++ tailWord_219028).sum := by decide
  have hdescent : baseEnd_219028 < baseStart_219028 := by decide
  rcases family_descends (prefixWord ++ tailWord_219028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219087 : List Nat := [1, 1, 2, 1, 1, 5, 1, 1, 3, 4, 3]
def baseStart_219087 : Nat := 118140960795 + 219087 * 2 ^ 59
def prefixEnd_219087 : Nat := 4983230072969 + 3 ^ 40 * 219087 * 2
def baseEnd_219087 : Nat := 112496936151689554804943

theorem tailTrace_219087 : CollatzResearch.WordTrace tailWord_219087 prefixEnd_219087 112496936151689554804943 := by
  unfold tailWord_219087
  simp only [CollatzResearch.WordTrace]
  refine ⟨7990759357292690925783515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5327172904861793950522343 7990759357292690925783515)
  ·
    refine ⟨11986139035939036388675273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7990759357292690925783515 11986139035939036388675273)
    ·
      refine ⟨8989604276954277291506455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11986139035939036388675273 8989604276954277291506455)
      ·
        refine ⟨13484406415431415937259683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8989604276954277291506455 13484406415431415937259683)
        ·
          refine ⟨20226609623147123905889525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13484406415431415937259683 20226609623147123905889525)
          ·
            refine ⟨1896244652170042866177143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20226609623147123905889525 1896244652170042866177143)
            ·
              refine ⟨2844366978255064299265715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1896244652170042866177143 2844366978255064299265715)
              ·
                refine ⟨4266550467382596448898573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2844366978255064299265715 4266550467382596448898573)
                ·
                  refine ⟨1599956425268473668336965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4266550467382596448898573 1599956425268473668336965)
                  ·
                    refine ⟨299991829737838812813181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1599956425268473668336965 299991829737838812813181)
                    ·
                      refine ⟨112496936151689554804943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 299991829737838812813181 112496936151689554804943)
                      ·
                        rfl

theorem cell23_219087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 3, 4, 3].length) (baseStart_219087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_219087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_219087 prefixEnd_219087 := by exact prefixLift 219087
  have htrace : WordTrace (prefixWord ++ tailWord_219087) baseStart_219087 baseEnd_219087 := by
    simpa [prefixWord, tailWord_219087, baseEnd_219087] using wordTrace_append hprefix tailTrace_219087
  have hstable : (prefixWord ++ tailWord_219087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219087).length < 2 ^ (prefixWord ++ tailWord_219087).sum := by decide
  have hdescent : baseEnd_219087 < baseStart_219087 := by decide
  rcases family_descends (prefixWord ++ tailWord_219087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219107 : List Nat := [1, 1, 1, 6, 1, 2, 1, 2, 8]
def baseStart_219107 : Nat := 118140960795 + 219107 * 2 ^ 59
def prefixEnd_219107 : Nat := 4983230072969 + 3 ^ 40 * 219107 * 2
def baseEnd_219107 : Nat := 12500800640531052950539

theorem tailTrace_219107 : CollatzResearch.WordTrace tailWord_219107 prefixEnd_219107 12500800640531052950539 := by
  unfold tailWord_219107
  simp only [CollatzResearch.WordTrace]
  refine ⟨7991488817220234341511575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5327659211480156227674383 7991488817220234341511575)
  ·
    refine ⟨11987233225830351512267363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7991488817220234341511575 11987233225830351512267363)
    ·
      refine ⟨17980849838745527268401045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11987233225830351512267363 17980849838745527268401045)
      ·
        refine ⟨842852336191196590706299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 17980849838745527268401045 842852336191196590706299)
        ·
          refine ⟨1264278504286794886059449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 842852336191196590706299 1264278504286794886059449)
          ·
            refine ⟨948208878215096164544587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1264278504286794886059449 948208878215096164544587)
            ·
              refine ⟨1422313317322644246816881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 948208878215096164544587 1422313317322644246816881)
              ·
                refine ⟨1066734987991983185112661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1422313317322644246816881 1066734987991983185112661)
                ·
                  refine ⟨12500800640531052950539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1066734987991983185112661 12500800640531052950539)
                  ·
                    rfl

theorem cell23_219107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 2, 8].length) (baseStart_219107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_219107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_219107 prefixEnd_219107 := by exact prefixLift 219107
  have htrace : WordTrace (prefixWord ++ tailWord_219107) baseStart_219107 baseEnd_219107 := by
    simpa [prefixWord, tailWord_219107, baseEnd_219107] using wordTrace_append hprefix tailTrace_219107
  have hstable : (prefixWord ++ tailWord_219107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219107).length < 2 ^ (prefixWord ++ tailWord_219107).sum := by decide
  have hdescent : baseEnd_219107 < baseStart_219107 := by decide
  rcases family_descends (prefixWord ++ tailWord_219107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219121 : List Nat := [1, 2, 2, 2, 5, 1, 1, 2, 2, 2, 3]
def baseStart_219121 : Nat := 118140960795 + 219121 * 2 ^ 59
def prefixEnd_219121 : Nat := 4983230072969 + 3 ^ 40 * 219121 * 2
def baseEnd_219121 : Nat := 112514394493942421779787

theorem tailTrace_219121 : CollatzResearch.WordTrace tailWord_219121 prefixEnd_219121 112514394493942421779787 := by
  unfold tailWord_219121
  simp only [CollatzResearch.WordTrace]
  refine ⟨7991999439169514732521217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5327999626113009821680811 7991999439169514732521217)
  ·
    refine ⟨5993999579377136049390913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7991999439169514732521217 5993999579377136049390913)
    ·
      refine ⟨4495499684532852037043185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5993999579377136049390913 4495499684532852037043185)
      ·
        refine ⟨3371624763399639027782389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4495499684532852037043185 3371624763399639027782389)
        ·
          refine ⟨316089821568716158854599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3371624763399639027782389 316089821568716158854599)
          ·
            refine ⟨474134732353074238281899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 316089821568716158854599 474134732353074238281899)
            ·
              refine ⟨711202098529611357422849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 474134732353074238281899 711202098529611357422849)
              ·
                refine ⟨533401573897208518067137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 711202098529611357422849 533401573897208518067137)
                ·
                  refine ⟨400051180422906388550353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 533401573897208518067137 400051180422906388550353)
                  ·
                    refine ⟨300038385317179791412765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 400051180422906388550353 300038385317179791412765)
                    ·
                      refine ⟨112514394493942421779787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 300038385317179791412765 112514394493942421779787)
                      ·
                        rfl

theorem cell23_219121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 2, 2, 2, 3].length) (baseStart_219121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_219121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_219121 prefixEnd_219121 := by exact prefixLift 219121
  have htrace : WordTrace (prefixWord ++ tailWord_219121) baseStart_219121 baseEnd_219121 := by
    simpa [prefixWord, tailWord_219121, baseEnd_219121] using wordTrace_append hprefix tailTrace_219121
  have hstable : (prefixWord ++ tailWord_219121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219121).length < 2 ^ (prefixWord ++ tailWord_219121).sum := by decide
  have hdescent : baseEnd_219121 < baseStart_219121 := by decide
  rcases family_descends (prefixWord ++ tailWord_219121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219141 : List Nat := [1, 3, 1, 1, 2, 6, 2, 1, 6]
def baseStart_219141 : Nat := 118140960795 + 219141 * 2 ^ 59
def prefixEnd_219141 : Nat := 4983230072969 + 3 ^ 40 * 219141 * 2
def baseEnd_219141 : Nat := 12502740456336927058855

theorem tailTrace_219141 : CollatzResearch.WordTrace tailWord_219141 prefixEnd_219141 12502740456336927058855 := by
  unfold tailWord_219141
  simp only [CollatzResearch.WordTrace]
  refine ⟨7992728899097058148249277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5328485932731372098832851 7992728899097058148249277)
  ·
    refine ⟨2997273337161396805593479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7992728899097058148249277 2997273337161396805593479)
    ·
      refine ⟨4495910005742095208390219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2997273337161396805593479 4495910005742095208390219)
      ·
        refine ⟨6743865008613142812585329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4495910005742095208390219 6743865008613142812585329)
        ·
          refine ⟨5057898756459857109438997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6743865008613142812585329 5057898756459857109438997)
          ·
            refine ⟨237089004209055802004953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 5057898756459857109438997 237089004209055802004953)
            ·
              refine ⟨177816753156791851503715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 237089004209055802004953 177816753156791851503715)
              ·
                refine ⟨266725129735187777255573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177816753156791851503715 266725129735187777255573)
                ·
                  refine ⟨12502740456336927058855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 266725129735187777255573 12502740456336927058855)
                  ·
                    rfl

theorem cell23_219141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 2, 1, 6].length) (baseStart_219141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_219141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_219141 prefixEnd_219141 := by exact prefixLift 219141
  have htrace : WordTrace (prefixWord ++ tailWord_219141) baseStart_219141 baseEnd_219141 := by
    simpa [prefixWord, tailWord_219141, baseEnd_219141] using wordTrace_append hprefix tailTrace_219141
  have hstable : (prefixWord ++ tailWord_219141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219141).length < 2 ^ (prefixWord ++ tailWord_219141).sum := by decide
  have hdescent : baseEnd_219141 < baseStart_219141 := by decide
  rcases family_descends (prefixWord ++ tailWord_219141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219171 : List Nat := [1, 1, 1, 4, 3, 1, 5, 1, 1, 5]
def baseStart_219171 : Nat := 118140960795 + 219171 * 2 ^ 59
def prefixEnd_219171 : Nat := 4983230072969 + 3 ^ 40 * 219171 * 2
def baseEnd_219171 : Nat := 37513356175555742051519

theorem tailTrace_219171 : CollatzResearch.WordTrace tailWord_219171 prefixEnd_219171 37513356175555742051519 := by
  unfold tailWord_219171
  simp only [CollatzResearch.WordTrace]
  refine ⟨7993823088988373271841367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5329215392658915514560911 7993823088988373271841367)
  ·
    refine ⟨11990734633482559907762051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7993823088988373271841367 11990734633482559907762051)
    ·
      refine ⟨17986101950223839861643077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11990734633482559907762051 17986101950223839861643077)
      ·
        refine ⟨3372394115666969974058077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17986101950223839861643077 3372394115666969974058077)
        ·
          refine ⟨1264647793375113740271779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3372394115666969974058077 1264647793375113740271779)
          ·
            refine ⟨1896971690062670610407669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1264647793375113740271779 1896971690062670610407669)
            ·
              refine ⟨177841095943375369725719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1896971690062670610407669 177841095943375369725719)
              ·
                refine ⟨266761643915063054588579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177841095943375369725719 266761643915063054588579)
                ·
                  refine ⟨400142465872594581882869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 266761643915063054588579 400142465872594581882869)
                  ·
                    refine ⟨37513356175555742051519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 400142465872594581882869 37513356175555742051519)
                    ·
                      rfl

theorem cell23_219171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 5, 1, 1, 5].length) (baseStart_219171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_219171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_219171 prefixEnd_219171 := by exact prefixLift 219171
  have htrace : WordTrace (prefixWord ++ tailWord_219171) baseStart_219171 baseEnd_219171 := by
    simpa [prefixWord, tailWord_219171, baseEnd_219171] using wordTrace_append hprefix tailTrace_219171
  have hstable : (prefixWord ++ tailWord_219171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219171).length < 2 ^ (prefixWord ++ tailWord_219171).sum := by decide
  have hdescent : baseEnd_219171 < baseStart_219171 := by decide
  rcases family_descends (prefixWord ++ tailWord_219171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219178 : List Nat := [3, 1, 4, 1, 2, 1, 2, 2, 2, 3, 2]
def baseStart_219178 : Nat := 118140960795 + 219178 * 2 ^ 59
def prefixEnd_219178 : Nat := 4983230072969 + 3 ^ 40 * 219178 * 2
def baseEnd_219178 : Nat := 112543662891248698767025

theorem tailTrace_219178 : CollatzResearch.WordTrace tailWord_219178 prefixEnd_219178 112543662891248698767025 := by
  unfold tailWord_219178
  simp only [CollatzResearch.WordTrace]
  refine ⟨1998519599990753366836547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5329385599975342311564125 1998519599990753366836547)
  ·
    refine ⟨2997779399986130050254821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1998519599990753366836547 2997779399986130050254821)
    ·
      refine ⟨562083637497399384422779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2997779399986130050254821 562083637497399384422779)
      ·
        refine ⟨843125456246099076634169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 562083637497399384422779 843125456246099076634169)
        ·
          refine ⟨632344092184574307475627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 843125456246099076634169 632344092184574307475627)
          ·
            refine ⟨948516138276861461213441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 632344092184574307475627 948516138276861461213441)
            ·
              refine ⟨711387103707646095910081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 948516138276861461213441 711387103707646095910081)
              ·
                refine ⟨533540327780734571932561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 711387103707646095910081 533540327780734571932561)
                ·
                  refine ⟨400155245835550928949421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 533540327780734571932561 400155245835550928949421)
                  ·
                    refine ⟨150058217188331598356033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 400155245835550928949421 150058217188331598356033)
                    ·
                      refine ⟨112543662891248698767025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 150058217188331598356033 112543662891248698767025)
                      ·
                        rfl

theorem cell23_219178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 2, 2, 3, 2].length) (baseStart_219178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_219178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_219178 prefixEnd_219178 := by exact prefixLift 219178
  have htrace : WordTrace (prefixWord ++ tailWord_219178) baseStart_219178 baseEnd_219178 := by
    simpa [prefixWord, tailWord_219178, baseEnd_219178] using wordTrace_append hprefix tailTrace_219178
  have hstable : (prefixWord ++ tailWord_219178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219178).length < 2 ^ (prefixWord ++ tailWord_219178).sum := by decide
  have hdescent : baseEnd_219178 < baseStart_219178 := by decide
  rcases family_descends (prefixWord ++ tailWord_219178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219185 : List Nat := [1, 2, 2, 3, 1, 3, 4, 2, 1, 1, 3]
def baseStart_219185 : Nat := 118140960795 + 219185 * 2 ^ 59
def prefixEnd_219185 : Nat := 4983230072969 + 3 ^ 40 * 219185 * 2
def baseEnd_219185 : Nat := 112547257255830171379493

theorem tailTrace_219185 : CollatzResearch.WordTrace tailWord_219185 prefixEnd_219185 112547257255830171379493 := by
  unfold tailWord_219185
  simp only [CollatzResearch.WordTrace]
  refine ⟨7994333710937653662851009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5329555807291769108567339 7994333710937653662851009)
  ·
    refine ⟨5995750283203240247138257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7994333710937653662851009 5995750283203240247138257)
    ·
      refine ⟨4496812712402430185353693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5995750283203240247138257 4496812712402430185353693)
      ·
        refine ⟨1686304767150911319507635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4496812712402430185353693 1686304767150911319507635)
        ·
          refine ⟨2529457150726366979261453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1686304767150911319507635 2529457150726366979261453)
          ·
            refine ⟨948546431522387617223045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2529457150726366979261453 948546431522387617223045)
            ·
              refine ⟨177852455910447678229321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 948546431522387617223045 177852455910447678229321)
              ·
                refine ⟨133389341932835758671991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 177852455910447678229321 133389341932835758671991)
                ·
                  refine ⟨200084012899253638007987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 133389341932835758671991 200084012899253638007987)
                  ·
                    refine ⟨300126019348880457011981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 200084012899253638007987 300126019348880457011981)
                    ·
                      refine ⟨112547257255830171379493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 300126019348880457011981 112547257255830171379493)
                      ·
                        rfl

theorem cell23_219185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 4, 2, 1, 1, 3].length) (baseStart_219185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_219185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_219185 prefixEnd_219185 := by exact prefixLift 219185
  have htrace : WordTrace (prefixWord ++ tailWord_219185) baseStart_219185 baseEnd_219185 := by
    simpa [prefixWord, tailWord_219185, baseEnd_219185] using wordTrace_append hprefix tailTrace_219185
  have hstable : (prefixWord ++ tailWord_219185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219185).length < 2 ^ (prefixWord ++ tailWord_219185).sum := by decide
  have hdescent : baseEnd_219185 < baseStart_219185 := by decide
  rcases family_descends (prefixWord ++ tailWord_219185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219187 : List Nat := [1, 1, 1, 2, 4, 1, 2, 1, 3, 1, 6]
def baseStart_219187 : Nat := 118140960795 + 219187 * 2 ^ 59
def prefixEnd_219187 : Nat := 4983230072969 + 3 ^ 40 * 219187 * 2
def baseEnd_219187 : Nat := 112548284217139163554483

theorem tailTrace_219187 : CollatzResearch.WordTrace tailWord_219187 prefixEnd_219187 112548284217139163554483 := by
  unfold tailWord_219187
  simp only [CollatzResearch.WordTrace]
  refine ⟨7994406656930408004423815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5329604437953605336282543 7994406656930408004423815)
  ·
    refine ⟨11991609985395612006635723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7994406656930408004423815 11991609985395612006635723)
    ·
      refine ⟨17987414978093418009953585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11991609985395612006635723 17987414978093418009953585)
      ·
        refine ⟨13490561233570063507465189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17987414978093418009953585 13490561233570063507465189)
        ·
          refine ⟨2529480231294386907649723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13490561233570063507465189 2529480231294386907649723)
          ·
            refine ⟨3794220346941580361474585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2529480231294386907649723 3794220346941580361474585)
            ·
              refine ⟨2845665260206185271105939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3794220346941580361474585 2845665260206185271105939)
              ·
                refine ⟨4268497890309277906658909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2845665260206185271105939 4268497890309277906658909)
                ·
                  refine ⟨1600686708865979214997091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4268497890309277906658909 1600686708865979214997091)
                  ·
                    refine ⟨2401030063298968822495637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1600686708865979214997091 2401030063298968822495637)
                    ·
                      refine ⟨112548284217139163554483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2401030063298968822495637 112548284217139163554483)
                      ·
                        rfl

theorem cell23_219187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 3, 1, 6].length) (baseStart_219187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_219187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_219187 prefixEnd_219187 := by exact prefixLift 219187
  have htrace : WordTrace (prefixWord ++ tailWord_219187) baseStart_219187 baseEnd_219187 := by
    simpa [prefixWord, tailWord_219187, baseEnd_219187] using wordTrace_append hprefix tailTrace_219187
  have hstable : (prefixWord ++ tailWord_219187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219187).length < 2 ^ (prefixWord ++ tailWord_219187).sum := by decide
  have hdescent : baseEnd_219187 < baseStart_219187 := by decide
  rcases family_descends (prefixWord ++ tailWord_219187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219201 : List Nat := [1, 2, 5, 1, 2, 2, 2, 1, 1, 6]
def baseStart_219201 : Nat := 118140960795 + 219201 * 2 ^ 59
def prefixEnd_219201 : Nat := 4983230072969 + 3 ^ 40 * 219201 * 2
def baseEnd_219201 : Nat := 37518490982100702926473

theorem tailTrace_219201 : CollatzResearch.WordTrace tailWord_219201 prefixEnd_219201 37518490982100702926473 := by
  unfold tailWord_219201
  simp only [CollatzResearch.WordTrace]
  refine ⟨7994917278879688395433457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5329944852586458930288971 7994917278879688395433457)
  ·
    refine ⟨5996187959159766296575093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7994917278879688395433457 5996187959159766296575093)
    ·
      refine ⟨562142621171228090303915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5996187959159766296575093 562142621171228090303915)
      ·
        refine ⟨843213931756842135455873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 562142621171228090303915 843213931756842135455873)
        ·
          refine ⟨632410448817631601591905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 843213931756842135455873 632410448817631601591905)
          ·
            refine ⟨474307836613223701193929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 632410448817631601591905 474307836613223701193929)
            ·
              refine ⟨355730877459917775895447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 474307836613223701193929 355730877459917775895447)
              ·
                refine ⟨533596316189876663843171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 355730877459917775895447 533596316189876663843171)
                ·
                  refine ⟨800394474284814995764757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 533596316189876663843171 800394474284814995764757)
                  ·
                    refine ⟨37518490982100702926473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 800394474284814995764757 37518490982100702926473)
                    ·
                      rfl

theorem cell23_219201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2, 1, 1, 6].length) (baseStart_219201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_219201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_219201 prefixEnd_219201 := by exact prefixLift 219201
  have htrace : WordTrace (prefixWord ++ tailWord_219201) baseStart_219201 baseEnd_219201 := by
    simpa [prefixWord, tailWord_219201, baseEnd_219201] using wordTrace_append hprefix tailTrace_219201
  have hstable : (prefixWord ++ tailWord_219201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219201).length < 2 ^ (prefixWord ++ tailWord_219201).sum := by decide
  have hdescent : baseEnd_219201 < baseStart_219201 := by decide
  rcases family_descends (prefixWord ++ tailWord_219201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219222 : List Nat := [5, 2, 2, 1, 1, 3, 2, 1, 1, 5]
def baseStart_219222 : Nat := 118140960795 + 219222 * 2 ^ 59
def prefixEnd_219222 : Nat := 4983230072969 + 3 ^ 40 * 219222 * 2
def baseEnd_219222 : Nat := 37522085346682175538941

theorem tailTrace_219222 : CollatzResearch.WordTrace tailWord_219222 prefixEnd_219222 37522085346682175538941 := by
  unfold tailWord_219222
  simp only [CollatzResearch.WordTrace]
  refine ⟨499730200737725561371745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5330455474535739321298613 499730200737725561371745)
  ·
    refine ⟨374797650553294171028809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 499730200737725561371745 374797650553294171028809)
    ·
      refine ⟨281098237914970628271607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 374797650553294171028809 281098237914970628271607)
      ·
        refine ⟨421647356872455942407411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281098237914970628271607 421647356872455942407411)
        ·
          refine ⟨632471035308683913611117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 421647356872455942407411 632471035308683913611117)
          ·
            refine ⟨237176638240756467604169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 632471035308683913611117 237176638240756467604169)
            ·
              refine ⟨177882478680567350703127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 237176638240756467604169 177882478680567350703127)
              ·
                refine ⟨266823718020851026054691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177882478680567350703127 266823718020851026054691)
                ·
                  refine ⟨400235577031276539082037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 266823718020851026054691 400235577031276539082037)
                  ·
                    refine ⟨37522085346682175538941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 400235577031276539082037 37522085346682175538941)
                    ·
                      rfl

theorem cell23_219222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_219222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_219222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_219222 prefixEnd_219222 := by exact prefixLift 219222
  have htrace : WordTrace (prefixWord ++ tailWord_219222) baseStart_219222 baseEnd_219222 := by
    simpa [prefixWord, tailWord_219222, baseEnd_219222] using wordTrace_append hprefix tailTrace_219222
  have hstable : (prefixWord ++ tailWord_219222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219222).length < 2 ^ (prefixWord ++ tailWord_219222).sum := by decide
  have hdescent : baseEnd_219222 < baseStart_219222 := by decide
  rcases family_descends (prefixWord ++ tailWord_219222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219225 : List Nat := [1, 2, 1, 2, 2, 1, 6, 3, 1, 2, 2]
def baseStart_219225 : Nat := 118140960795 + 219225 * 2 ^ 59
def prefixEnd_219225 : Nat := 4983230072969 + 3 ^ 40 * 219225 * 2
def baseEnd_219225 : Nat := 112567796482010014879309

theorem tailTrace_219225 : CollatzResearch.WordTrace tailWord_219225 prefixEnd_219225 112567796482010014879309 := by
  unfold tailWord_219225
  simp only [CollatzResearch.WordTrace]
  refine ⟨7995792630792740494307129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5330528420528493662871419 7995792630792740494307129)
  ·
    refine ⟨5996844473094555370730347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7995792630792740494307129 5996844473094555370730347)
    ·
      refine ⟨8995266709641833056095521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5996844473094555370730347 8995266709641833056095521)
      ·
        refine ⟨6746450032231374792071641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8995266709641833056095521 6746450032231374792071641)
        ·
          refine ⟨5059837524173531094053731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6746450032231374792071641 5059837524173531094053731)
          ·
            refine ⟨7589756286260296641080597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5059837524173531094053731 7589756286260296641080597)
            ·
              refine ⟨355769825918451405050653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7589756286260296641080597 355769825918451405050653)
              ·
                refine ⟨133413684719419276893995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 355769825918451405050653 133413684719419276893995)
                ·
                  refine ⟨200120527079128915340993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 133413684719419276893995 200120527079128915340993)
                  ·
                    refine ⟨150090395309346686505745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 200120527079128915340993 150090395309346686505745)
                    ·
                      refine ⟨112567796482010014879309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 150090395309346686505745 112567796482010014879309)
                      ·
                        rfl

theorem cell23_219225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6, 3, 1, 2, 2].length) (baseStart_219225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_219225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_219225 prefixEnd_219225 := by exact prefixLift 219225
  have htrace : WordTrace (prefixWord ++ tailWord_219225) baseStart_219225 baseEnd_219225 := by
    simpa [prefixWord, tailWord_219225, baseEnd_219225] using wordTrace_append hprefix tailTrace_219225
  have hstable : (prefixWord ++ tailWord_219225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219225).length < 2 ^ (prefixWord ++ tailWord_219225).sum := by decide
  have hdescent : baseEnd_219225 < baseStart_219225 := by decide
  rcases family_descends (prefixWord ++ tailWord_219225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219228 : List Nat := [2, 2, 4, 1, 1, 3, 1, 3, 1, 2, 3]
def baseStart_219228 : Nat := 118140960795 + 219228 * 2 ^ 59
def prefixEnd_219228 : Nat := 4983230072969 + 3 ^ 40 * 219228 * 2
def baseEnd_219228 : Nat := 112569336923973503141795

theorem tailTrace_219228 : CollatzResearch.WordTrace tailWord_219228 prefixEnd_219228 112569336923973503141795 := by
  unfold tailWord_219228
  simp only [CollatzResearch.WordTrace]
  refine ⟨3997951024890936003333169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5330601366521248004444225 3997951024890936003333169)
  ·
    refine ⟨2998463268668202002499877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3997951024890936003333169 2998463268668202002499877)
    ·
      refine ⟨562211862875287875468727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2998463268668202002499877 562211862875287875468727)
      ·
        refine ⟨843317794312931813203091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 562211862875287875468727 843317794312931813203091)
        ·
          refine ⟨1264976691469397719804637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 843317794312931813203091 1264976691469397719804637)
          ·
            refine ⟨474366259301024144926739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1264976691469397719804637 474366259301024144926739)
            ·
              refine ⟨711549388951536217390109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 474366259301024144926739 711549388951536217390109)
              ·
                refine ⟨266831020856826081521291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 711549388951536217390109 266831020856826081521291)
                ·
                  refine ⟨400246531285239122281937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 266831020856826081521291 400246531285239122281937)
                  ·
                    refine ⟨300184898463929341711453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 400246531285239122281937 300184898463929341711453)
                    ·
                      refine ⟨112569336923973503141795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 300184898463929341711453 112569336923973503141795)
                      ·
                        rfl

theorem cell23_219228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 3, 1, 2, 3].length) (baseStart_219228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_219228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_219228 prefixEnd_219228 := by exact prefixLift 219228
  have htrace : WordTrace (prefixWord ++ tailWord_219228) baseStart_219228 baseEnd_219228 := by
    simpa [prefixWord, tailWord_219228, baseEnd_219228] using wordTrace_append hprefix tailTrace_219228
  have hstable : (prefixWord ++ tailWord_219228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219228).length < 2 ^ (prefixWord ++ tailWord_219228).sum := by decide
  have hdescent : baseEnd_219228 < baseStart_219228 := by decide
  rcases family_descends (prefixWord ++ tailWord_219228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219241 : List Nat := [1, 2, 1, 1, 1, 5, 3, 1, 4, 1, 3]
def baseStart_219241 : Nat := 118140960795 + 219241 * 2 ^ 59
def prefixEnd_219241 : Nat := 4983230072969 + 3 ^ 40 * 219241 * 2
def baseEnd_219241 : Nat := 112576012172481952279235

theorem tailTrace_219241 : CollatzResearch.WordTrace tailWord_219241 prefixEnd_219241 112576012172481952279235 := by
  unfold tailWord_219241
  simp only [CollatzResearch.WordTrace]
  refine ⟨7996376198734775226889577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5330917465823183484593051 7996376198734775226889577)
  ·
    refine ⟨5997282149051081420167183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7996376198734775226889577 5997282149051081420167183)
    ·
      refine ⟨8995923223576622130250775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5997282149051081420167183 8995923223576622130250775)
      ·
        refine ⟨13493884835364933195376163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8995923223576622130250775 13493884835364933195376163)
        ·
          refine ⟨20240827253047399793064245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13493884835364933195376163 20240827253047399793064245)
          ·
            refine ⟨1897577554973193730599773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20240827253047399793064245 1897577554973193730599773)
            ·
              refine ⟨711591583114947648974915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1897577554973193730599773 711591583114947648974915)
              ·
                refine ⟨1067387374672421473462373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 711591583114947648974915 1067387374672421473462373)
                ·
                  refine ⟨200135132751079026274195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1067387374672421473462373 200135132751079026274195)
                  ·
                    refine ⟨300202699126618539411293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 200135132751079026274195 300202699126618539411293)
                    ·
                      refine ⟨112576012172481952279235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 300202699126618539411293 112576012172481952279235)
                      ·
                        rfl

theorem cell23_219241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 1, 4, 1, 3].length) (baseStart_219241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_219241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_219241 prefixEnd_219241 := by exact prefixLift 219241
  have htrace : WordTrace (prefixWord ++ tailWord_219241) baseStart_219241 baseEnd_219241 := by
    simpa [prefixWord, tailWord_219241, baseEnd_219241] using wordTrace_append hprefix tailTrace_219241
  have hstable : (prefixWord ++ tailWord_219241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219241).length < 2 ^ (prefixWord ++ tailWord_219241).sum := by decide
  have hdescent : baseEnd_219241 < baseStart_219241 := by decide
  rcases family_descends (prefixWord ++ tailWord_219241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219362 : List Nat := [3, 3, 4, 1, 1, 1, 1, 1, 2, 2, 4]
def baseStart_219362 : Nat := 118140960795 + 219362 * 2 ^ 59
def prefixEnd_219362 : Nat := 4983230072969 + 3 ^ 40 * 219362 * 2
def baseEnd_219362 : Nat := 112638143331675978866179

theorem tailTrace_219362 : CollatzResearch.WordTrace tailWord_219362 prefixEnd_219362 112638143331675978866179 := by
  unfold tailWord_219362
  simp only [CollatzResearch.WordTrace]
  refine ⟨2000197357824103223011085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5333859620864275261362893 2000197357824103223011085)
  ·
    refine ⟨750074009184038708629157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2000197357824103223011085 750074009184038708629157)
    ·
      refine ⟨140638876722007257867967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 750074009184038708629157 140638876722007257867967)
      ·
        refine ⟨210958315083010886801951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140638876722007257867967 210958315083010886801951)
        ·
          refine ⟨316437472624516330202927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210958315083010886801951 316437472624516330202927)
          ·
            refine ⟨474656208936774495304391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 316437472624516330202927 474656208936774495304391)
            ·
              refine ⟨711984313405161742956587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 474656208936774495304391 711984313405161742956587)
              ·
                refine ⟨1067976470107742614434881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 711984313405161742956587 1067976470107742614434881)
                ·
                  refine ⟨800982352580806960826161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1067976470107742614434881 800982352580806960826161)
                  ·
                    refine ⟨600736764435605220619621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 800982352580806960826161 600736764435605220619621)
                    ·
                      refine ⟨112638143331675978866179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 600736764435605220619621 112638143331675978866179)
                      ·
                        rfl

theorem cell23_219362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_219362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_219362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_219362 prefixEnd_219362 := by exact prefixLift 219362
  have htrace : WordTrace (prefixWord ++ tailWord_219362) baseStart_219362 baseEnd_219362 := by
    simpa [prefixWord, tailWord_219362, baseEnd_219362] using wordTrace_append hprefix tailTrace_219362
  have hstable : (prefixWord ++ tailWord_219362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219362).length < 2 ^ (prefixWord ++ tailWord_219362).sum := by decide
  have hdescent : baseEnd_219362 < baseStart_219362 := by decide
  rcases family_descends (prefixWord ++ tailWord_219362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219364 : List Nat := [2, 3, 1, 1, 1, 2, 1, 2, 2, 8]
def baseStart_219364 : Nat := 118140960795 + 219364 * 2 ^ 59
def prefixEnd_219364 : Nat := 4983230072969 + 3 ^ 40 * 219364 * 2
def baseEnd_219364 : Nat := 37546390097661657013723

theorem tailTrace_219364 : CollatzResearch.WordTrace tailWord_219364 prefixEnd_219364 37546390097661657013723 := by
  unfold tailWord_219364
  simp only [CollatzResearch.WordTrace]
  refine ⟨4000431188644583616808573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5333908251526111489078097 4000431188644583616808573)
  ·
    refine ⟨1500161695741718856303215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4000431188644583616808573 1500161695741718856303215)
    ·
      refine ⟨2250242543612578284454823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1500161695741718856303215 2250242543612578284454823)
      ·
        refine ⟨3375363815418867426682235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2250242543612578284454823 3375363815418867426682235)
        ·
          refine ⟨5063045723128301140023353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3375363815418867426682235 5063045723128301140023353)
          ·
            refine ⟨3797284292346225855017515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5063045723128301140023353 3797284292346225855017515)
            ·
              refine ⟨5695926438519338782526273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3797284292346225855017515 5695926438519338782526273)
              ·
                refine ⟨4271944828889504086894705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5695926438519338782526273 4271944828889504086894705)
                ·
                  refine ⟨3203958621667128065171029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4271944828889504086894705 3203958621667128065171029)
                  ·
                    refine ⟨37546390097661657013723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 3203958621667128065171029 37546390097661657013723)
                    ·
                      rfl

theorem cell23_219364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 2, 8].length) (baseStart_219364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_219364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_219364 prefixEnd_219364 := by exact prefixLift 219364
  have htrace : WordTrace (prefixWord ++ tailWord_219364) baseStart_219364 baseEnd_219364 := by
    simpa [prefixWord, tailWord_219364, baseEnd_219364] using wordTrace_append hprefix tailTrace_219364
  have hstable : (prefixWord ++ tailWord_219364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219364).length < 2 ^ (prefixWord ++ tailWord_219364).sum := by decide
  have hdescent : baseEnd_219364 < baseStart_219364 := by decide
  rcases family_descends (prefixWord ++ tailWord_219364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219384 : List Nat := [2, 1, 2, 1, 1, 2, 1, 2, 4, 1, 6]
def baseStart_219384 : Nat := 118140960795 + 219384 * 2 ^ 59
def prefixEnd_219384 : Nat := 4983230072969 + 3 ^ 40 * 219384 * 2
def baseEnd_219384 : Nat := 112649439906074892791077

theorem tailTrace_219384 : CollatzResearch.WordTrace tailWord_219384 prefixEnd_219384 112649439906074892791077 := by
  unfold tailWord_219384
  simp only [CollatzResearch.WordTrace]
  refine ⟨4000795918608355324672603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5334394558144473766230137 4000795918608355324672603)
  ·
    refine ⟨6001193877912532987008905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4000795918608355324672603 6001193877912532987008905)
    ·
      refine ⟨4500895408434399740256679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6001193877912532987008905 4500895408434399740256679)
      ·
        refine ⟨6751343112651599610385019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4500895408434399740256679 6751343112651599610385019)
        ·
          refine ⟨10127014668977399415577529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6751343112651599610385019 10127014668977399415577529)
          ·
            refine ⟨7595261001733049561683147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10127014668977399415577529 7595261001733049561683147)
            ·
              refine ⟨11392891502599574342524721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7595261001733049561683147 11392891502599574342524721)
              ·
                refine ⟨8544668626949680756893541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11392891502599574342524721 8544668626949680756893541)
                ·
                  refine ⟨1602125367553065141917539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8544668626949680756893541 1602125367553065141917539)
                  ·
                    refine ⟨2403188051329597712876309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1602125367553065141917539 2403188051329597712876309)
                    ·
                      refine ⟨112649439906074892791077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2403188051329597712876309 112649439906074892791077)
                      ·
                        rfl

theorem cell23_219384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 4, 1, 6].length) (baseStart_219384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_219384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_219384 prefixEnd_219384 := by exact prefixLift 219384
  have htrace : WordTrace (prefixWord ++ tailWord_219384) baseStart_219384 baseEnd_219384 := by
    simpa [prefixWord, tailWord_219384, baseEnd_219384] using wordTrace_append hprefix tailTrace_219384
  have hstable : (prefixWord ++ tailWord_219384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219384).length < 2 ^ (prefixWord ++ tailWord_219384).sum := by decide
  have hdescent : baseEnd_219384 < baseStart_219384 := by decide
  rcases family_descends (prefixWord ++ tailWord_219384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219388 : List Nat := [2, 2, 2, 1, 4, 1, 3, 1, 2, 1, 4]
def baseStart_219388 : Nat := 118140960795 + 219388 * 2 ^ 59
def prefixEnd_219388 : Nat := 4983230072969 + 3 ^ 40 * 219388 * 2
def baseEnd_219388 : Nat := 112651493828692877141059

theorem tailTrace_219388 : CollatzResearch.WordTrace tailWord_219388 prefixEnd_219388 112651493828692877141059 := by
  unfold tailWord_219388
  simp only [CollatzResearch.WordTrace]
  refine ⟨4000868864601109666245409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5334491819468146221660545 4000868864601109666245409)
  ·
    refine ⟨3000651648450832249684057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4000868864601109666245409 3000651648450832249684057)
    ·
      refine ⟨2250488736338124187263043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3000651648450832249684057 2250488736338124187263043)
      ·
        refine ⟨3375733104507186280894565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2250488736338124187263043 3375733104507186280894565)
        ·
          refine ⟨632949957095097427667731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3375733104507186280894565 632949957095097427667731)
          ·
            refine ⟨949424935642646141501597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 632949957095097427667731 949424935642646141501597)
            ·
              refine ⟨356034350865992303063099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 949424935642646141501597 356034350865992303063099)
              ·
                refine ⟨534051526298988454594649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 356034350865992303063099 534051526298988454594649)
                ·
                  refine ⟨400538644724241340945987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 534051526298988454594649 400538644724241340945987)
                  ·
                    refine ⟨600807967086362011418981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 400538644724241340945987 600807967086362011418981)
                    ·
                      refine ⟨112651493828692877141059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 600807967086362011418981 112651493828692877141059)
                      ·
                        rfl

theorem cell23_219388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3, 1, 2, 1, 4].length) (baseStart_219388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_219388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_219388 prefixEnd_219388 := by exact prefixLift 219388
  have htrace : WordTrace (prefixWord ++ tailWord_219388) baseStart_219388 baseEnd_219388 := by
    simpa [prefixWord, tailWord_219388, baseEnd_219388] using wordTrace_append hprefix tailTrace_219388
  have hstable : (prefixWord ++ tailWord_219388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219388).length < 2 ^ (prefixWord ++ tailWord_219388).sum := by decide
  have hdescent : baseEnd_219388 < baseStart_219388 := by decide
  rcases family_descends (prefixWord ++ tailWord_219388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219391 : List Nat := [1, 1, 2, 2, 1, 4, 3, 1, 1, 4, 3]
def baseStart_219391 : Nat := 118140960795 + 219391 * 2 ^ 59
def prefixEnd_219391 : Nat := 4983230072969 + 3 ^ 40 * 219391 * 2
def baseEnd_219391 : Nat := 112653034270656365403545

theorem tailTrace_219391 : CollatzResearch.WordTrace tailWord_219391 prefixEnd_219391 112653034270656365403545 := by
  unfold tailWord_219391
  simp only [CollatzResearch.WordTrace]
  refine ⟨8001847148191350844850027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5334564765460900563233351 8001847148191350844850027)
  ·
    refine ⟨12002770722287026267275041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8001847148191350844850027 12002770722287026267275041)
    ·
      refine ⟨9002078041715269700456281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12002770722287026267275041 9002078041715269700456281)
      ·
        refine ⟨6751558531286452275342211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9002078041715269700456281 6751558531286452275342211)
        ·
          refine ⟨10127337796929678413013317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6751558531286452275342211 10127337796929678413013317)
          ·
            refine ⟨1898875836924314702439997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10127337796929678413013317 1898875836924314702439997)
            ·
              refine ⟨712078438846618013414999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1898875836924314702439997 712078438846618013414999)
              ·
                refine ⟨1068117658269927020122499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 712078438846618013414999 1068117658269927020122499)
                ·
                  refine ⟨1602176487404890530183749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1068117658269927020122499 1602176487404890530183749)
                  ·
                    refine ⟨300408091388416974409453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1602176487404890530183749 300408091388416974409453)
                    ·
                      refine ⟨112653034270656365403545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 300408091388416974409453 112653034270656365403545)
                      ·
                        rfl

theorem cell23_219391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 1, 1, 4, 3].length) (baseStart_219391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_219391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_219391 prefixEnd_219391 := by exact prefixLift 219391
  have htrace : WordTrace (prefixWord ++ tailWord_219391) baseStart_219391 baseEnd_219391 := by
    simpa [prefixWord, tailWord_219391, baseEnd_219391] using wordTrace_append hprefix tailTrace_219391
  have hstable : (prefixWord ++ tailWord_219391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219391).length < 2 ^ (prefixWord ++ tailWord_219391).sum := by decide
  have hdescent : baseEnd_219391 < baseStart_219391 := by decide
  rcases family_descends (prefixWord ++ tailWord_219391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219415 : List Nat := [1, 1, 3, 4, 1, 2, 2, 4, 1, 4]
def baseStart_219415 : Nat := 118140960795 + 219415 * 2 ^ 59
def prefixEnd_219415 : Nat := 4983230072969 + 3 ^ 40 * 219415 * 2
def baseEnd_219415 : Nat := 37555119268788090501145

theorem tailTrace_219415 : CollatzResearch.WordTrace tailWord_219415 prefixEnd_219415 37555119268788090501145 := by
  unfold tailWord_219415
  simp only [CollatzResearch.WordTrace]
  refine ⟨8002722500104402943723699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5335148333402935295815799 8002722500104402943723699)
  ·
    refine ⟨12004083750156604415585549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8002722500104402943723699 12004083750156604415585549)
    ·
      refine ⟨4501531406308726655844581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12004083750156604415585549 4501531406308726655844581)
      ·
        refine ⟨844037138682886247970859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4501531406308726655844581 844037138682886247970859)
        ·
          refine ⟨1266055708024329371956289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 844037138682886247970859 1266055708024329371956289)
          ·
            refine ⟨949541781018247028967217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1266055708024329371956289 949541781018247028967217)
            ·
              refine ⟨712156335763685271725413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 949541781018247028967217 712156335763685271725413)
              ·
                refine ⟨133529312955690988448515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 712156335763685271725413 133529312955690988448515)
                ·
                  refine ⟨200293969433536482672773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 133529312955690988448515 200293969433536482672773)
                  ·
                    refine ⟨37555119268788090501145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 200293969433536482672773 37555119268788090501145)
                    ·
                      rfl

theorem cell23_219415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 4, 1, 4].length) (baseStart_219415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_219415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_219415 prefixEnd_219415 := by exact prefixLift 219415
  have htrace : WordTrace (prefixWord ++ tailWord_219415) baseStart_219415 baseEnd_219415 := by
    simpa [prefixWord, tailWord_219415, baseEnd_219415] using wordTrace_append hprefix tailTrace_219415
  have hstable : (prefixWord ++ tailWord_219415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219415).length < 2 ^ (prefixWord ++ tailWord_219415).sum := by decide
  have hdescent : baseEnd_219415 < baseStart_219415 := by decide
  rcases family_descends (prefixWord ++ tailWord_219415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219422 : List Nat := [4, 3, 2, 1, 1, 1, 2, 1, 2, 4, 2]
def baseStart_219422 : Nat := 118140960795 + 219422 * 2 ^ 59
def prefixEnd_219422 : Nat := 4983230072969 + 3 ^ 40 * 219422 * 2
def baseEnd_219422 : Nat := 112668952170945744115903

theorem tailTrace_219422 : CollatzResearch.WordTrace tailWord_219422 prefixEnd_219422 112668952170945744115903 := by
  unfold tailWord_219422
  simp only [CollatzResearch.WordTrace]
  refine ⟨1000372226384880392403565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5335318540719362092819013 1000372226384880392403565)
  ·
    refine ⟨375139584894330147151337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1000372226384880392403565 375139584894330147151337)
    ·
      refine ⟨281354688670747610363503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 375139584894330147151337 281354688670747610363503)
      ·
        refine ⟨422032033006121415545255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281354688670747610363503 422032033006121415545255)
        ·
          refine ⟨633048049509182123317883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 422032033006121415545255 633048049509182123317883)
          ·
            refine ⟨949572074263773184976825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 633048049509182123317883 949572074263773184976825)
            ·
              refine ⟨712179055697829888732619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 949572074263773184976825 712179055697829888732619)
              ·
                refine ⟨1068268583546744833098929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 712179055697829888732619 1068268583546744833098929)
                ·
                  refine ⟨801201437660058624824197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1068268583546744833098929 801201437660058624824197)
                  ·
                    refine ⟨150225269561260992154537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 801201437660058624824197 150225269561260992154537)
                    ·
                      refine ⟨112668952170945744115903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 150225269561260992154537 112668952170945744115903)
                      ·
                        rfl

theorem cell23_219422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 1, 2, 4, 2].length) (baseStart_219422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_219422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_219422 prefixEnd_219422 := by exact prefixLift 219422
  have htrace : WordTrace (prefixWord ++ tailWord_219422) baseStart_219422 baseEnd_219422 := by
    simpa [prefixWord, tailWord_219422, baseEnd_219422] using wordTrace_append hprefix tailTrace_219422
  have hstable : (prefixWord ++ tailWord_219422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219422).length < 2 ^ (prefixWord ++ tailWord_219422).sum := by decide
  have hdescent : baseEnd_219422 < baseStart_219422 := by decide
  rcases family_descends (prefixWord ++ tailWord_219422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219448 : List Nat := [2, 1, 2, 1, 3, 1, 4, 1, 1, 5, 2]
def baseStart_219448 : Nat := 118140960795 + 219448 * 2 ^ 59
def prefixEnd_219448 : Nat := 4983230072969 + 3 ^ 40 * 219448 * 2
def baseEnd_219448 : Nat := 112682302667962642390783

theorem tailTrace_219448 : CollatzResearch.WordTrace tailWord_219448 prefixEnd_219448 112682302667962642390783 := by
  unfold tailWord_219448
  simp only [CollatzResearch.WordTrace]
  refine ⟨4001963054492424789837499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5335950739323233053116665 4001963054492424789837499)
  ·
    refine ⟨6002944581738637184756249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4001963054492424789837499 6002944581738637184756249)
    ·
      refine ⟨4502208436303977888567187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6002944581738637184756249 4502208436303977888567187)
      ·
        refine ⟨6753312654455966832850781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4502208436303977888567187 6753312654455966832850781)
        ·
          refine ⟨2532492245420987562319043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6753312654455966832850781 2532492245420987562319043)
          ·
            refine ⟨3798738368131481343478565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2532492245420987562319043 3798738368131481343478565)
            ·
              refine ⟨712263444024652751902231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3798738368131481343478565 712263444024652751902231)
              ·
                refine ⟨1068395166036979127853347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 712263444024652751902231 1068395166036979127853347)
                ·
                  refine ⟨1602592749055468691780021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1068395166036979127853347 1602592749055468691780021)
                  ·
                    refine ⟨150243070223950189854377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1602592749055468691780021 150243070223950189854377)
                    ·
                      refine ⟨112682302667962642390783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 150243070223950189854377 112682302667962642390783)
                      ·
                        rfl

theorem cell23_219448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 1, 1, 5, 2].length) (baseStart_219448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_219448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_219448 prefixEnd_219448 := by exact prefixLift 219448
  have htrace : WordTrace (prefixWord ++ tailWord_219448) baseStart_219448 baseEnd_219448 := by
    simpa [prefixWord, tailWord_219448, baseEnd_219448] using wordTrace_append hprefix tailTrace_219448
  have hstable : (prefixWord ++ tailWord_219448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219448).length < 2 ^ (prefixWord ++ tailWord_219448).sum := by decide
  have hdescent : baseEnd_219448 < baseStart_219448 := by decide
  rcases family_descends (prefixWord ++ tailWord_219448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219461 : List Nat := [1, 3, 1, 1, 1, 2, 1, 1, 7, 1, 4]
def baseStart_219461 : Nat := 118140960795 + 219461 * 2 ^ 59
def prefixEnd_219461 : Nat := 4983230072969 + 3 ^ 40 * 219461 * 2
def baseEnd_219461 : Nat := 112688977916471091528223

theorem tailTrace_219461 : CollatzResearch.WordTrace tailWord_219461 prefixEnd_219461 112688977916471091528223 := by
  unfold tailWord_219461
  simp only [CollatzResearch.WordTrace]
  refine ⟨8004400257937752799898237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5336266838625168533265491 8004400257937752799898237)
  ·
    refine ⟨3001650096726657299961839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8004400257937752799898237 3001650096726657299961839)
    ·
      refine ⟨4502475145089985949942759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3001650096726657299961839 4502475145089985949942759)
      ·
        refine ⟨6753712717634978924914139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4502475145089985949942759 6753712717634978924914139)
        ·
          refine ⟨10130569076452468387371209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6753712717634978924914139 10130569076452468387371209)
          ·
            refine ⟨7597926807339351290528407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10130569076452468387371209 7597926807339351290528407)
            ·
              refine ⟨11396890211009026935792611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7597926807339351290528407 11396890211009026935792611)
              ·
                refine ⟨17095335316513540403688917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11396890211009026935792611 17095335316513540403688917)
                ·
                  refine ⟨400671921480786103211459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17095335316513540403688917 400671921480786103211459)
                  ·
                    refine ⟨601007882221179154817189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 400671921480786103211459 601007882221179154817189)
                    ·
                      refine ⟨112688977916471091528223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 601007882221179154817189 112688977916471091528223)
                      ·
                        rfl

theorem cell23_219461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 7, 1, 4].length) (baseStart_219461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_219461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_219461 prefixEnd_219461 := by exact prefixLift 219461
  have htrace : WordTrace (prefixWord ++ tailWord_219461) baseStart_219461 baseEnd_219461 := by
    simpa [prefixWord, tailWord_219461, baseEnd_219461] using wordTrace_append hprefix tailTrace_219461
  have hstable : (prefixWord ++ tailWord_219461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219461).length < 2 ^ (prefixWord ++ tailWord_219461).sum := by decide
  have hdescent : baseEnd_219461 < baseStart_219461 := by decide
  rcases family_descends (prefixWord ++ tailWord_219461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219481 : List Nat := [1, 2, 1, 2, 2, 2, 1, 1, 2, 6, 3]
def baseStart_219481 : Nat := 118140960795 + 219481 * 2 ^ 59
def prefixEnd_219481 : Nat := 4983230072969 + 3 ^ 40 * 219481 * 2
def baseEnd_219481 : Nat := 112699247529561013278131

theorem tailTrace_219481 : CollatzResearch.WordTrace tailWord_219481 prefixEnd_219481 112699247529561013278131 := by
  unfold tailWord_219481
  simp only [CollatzResearch.WordTrace]
  refine ⟨8005129717865296215626297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5336753145243530810417531 8005129717865296215626297)
  ·
    refine ⟨6003847288398972161719723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8005129717865296215626297 6003847288398972161719723)
    ·
      refine ⟨9005770932598458242579585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6003847288398972161719723 9005770932598458242579585)
      ·
        refine ⟨6754328199448843681934689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9005770932598458242579585 6754328199448843681934689)
        ·
          refine ⟨5065746149586632761451017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6754328199448843681934689 5065746149586632761451017)
          ·
            refine ⟨3799309612189974571088263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5065746149586632761451017 3799309612189974571088263)
            ·
              refine ⟨5698964418284961856632395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3799309612189974571088263 5698964418284961856632395)
              ·
                refine ⟨8548446627427442784948593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5698964418284961856632395 8548446627427442784948593)
                ·
                  refine ⟨6411334970570582088711445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8548446627427442784948593 6411334970570582088711445)
                  ·
                    refine ⟨300531326745496035408349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6411334970570582088711445 300531326745496035408349)
                    ·
                      refine ⟨112699247529561013278131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 300531326745496035408349 112699247529561013278131)
                      ·
                        rfl

theorem cell23_219481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 6, 3].length) (baseStart_219481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_219481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_219481 prefixEnd_219481 := by exact prefixLift 219481
  have htrace : WordTrace (prefixWord ++ tailWord_219481) baseStart_219481 baseEnd_219481 := by
    simpa [prefixWord, tailWord_219481, baseEnd_219481] using wordTrace_append hprefix tailTrace_219481
  have hstable : (prefixWord ++ tailWord_219481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219481).length < 2 ^ (prefixWord ++ tailWord_219481).sum := by decide
  have hdescent : baseEnd_219481 < baseStart_219481 := by decide
  rcases family_descends (prefixWord ++ tailWord_219481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219491 : List Nat := [1, 1, 1, 5, 2, 1, 1, 3, 1, 1, 6]
def baseStart_219491 : Nat := 118140960795 + 219491 * 2 ^ 59
def prefixEnd_219491 : Nat := 4983230072969 + 3 ^ 40 * 219491 * 2
def baseEnd_219491 : Nat := 112704382336105974153085

theorem tailTrace_219491 : CollatzResearch.WordTrace tailWord_219491 prefixEnd_219491 112704382336105974153085 := by
  unfold tailWord_219491
  simp only [CollatzResearch.WordTrace]
  refine ⟨8005494447829067923490327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5336996298552711948993551 8005494447829067923490327)
  ·
    refine ⟨12008241671743601885235491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8005494447829067923490327 12008241671743601885235491)
    ·
      refine ⟨18012362507615402827853237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12008241671743601885235491 18012362507615402827853237)
      ·
        refine ⟨1688658985088944015111241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18012362507615402827853237 1688658985088944015111241)
        ·
          refine ⟨1266494238816708011333431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1688658985088944015111241 1266494238816708011333431)
          ·
            refine ⟨1899741358225062017000147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1266494238816708011333431 1899741358225062017000147)
            ·
              refine ⟨2849612037337593025500221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1899741358225062017000147 2849612037337593025500221)
              ·
                refine ⟨1068604514001597384562583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2849612037337593025500221 1068604514001597384562583)
                ·
                  refine ⟨1602906771002396076843875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1068604514001597384562583 1602906771002396076843875)
                  ·
                    refine ⟨2404360156503594115265813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1602906771002396076843875 2404360156503594115265813)
                    ·
                      refine ⟨112704382336105974153085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2404360156503594115265813 112704382336105974153085)
                      ·
                        rfl

theorem cell23_219491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 3, 1, 1, 6].length) (baseStart_219491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_219491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_219491 prefixEnd_219491 := by exact prefixLift 219491
  have htrace : WordTrace (prefixWord ++ tailWord_219491) baseStart_219491 baseEnd_219491 := by
    simpa [prefixWord, tailWord_219491, baseEnd_219491] using wordTrace_append hprefix tailTrace_219491
  have hstable : (prefixWord ++ tailWord_219491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219491).length < 2 ^ (prefixWord ++ tailWord_219491).sum := by decide
  have hdescent : baseEnd_219491 < baseStart_219491 := by decide
  rcases family_descends (prefixWord ++ tailWord_219491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219495 : List Nat := [1, 1, 5, 1, 3, 1, 3, 2, 1, 1, 4]
def baseStart_219495 : Nat := 118140960795 + 219495 * 2 ^ 59
def prefixEnd_219495 : Nat := 4983230072969 + 3 ^ 40 * 219495 * 2
def baseEnd_219495 : Nat := 112706436258723958503067

theorem tailTrace_219495 : CollatzResearch.WordTrace tailWord_219495 prefixEnd_219495 112706436258723958503067 := by
  unfold tailWord_219495
  simp only [CollatzResearch.WordTrace]
  refine ⟨8005640339814576606635939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5337093559876384404423959 8005640339814576606635939)
  ·
    refine ⟨12008460509721864909953909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8005640339814576606635939 12008460509721864909953909)
    ·
      refine ⟨1125793172786424835308179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12008460509721864909953909 1125793172786424835308179)
      ·
        refine ⟨1688689759179637252962269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1125793172786424835308179 1688689759179637252962269)
        ·
          refine ⟨633258659692363969860851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1688689759179637252962269 633258659692363969860851)
          ·
            refine ⟨949887989538545954791277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 633258659692363969860851 949887989538545954791277)
            ·
              refine ⟨356207996076954733046729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 949887989538545954791277 356207996076954733046729)
              ·
                refine ⟨267155997057716049785047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 356207996076954733046729 267155997057716049785047)
                ·
                  refine ⟨400733995586574074677571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 267155997057716049785047 400733995586574074677571)
                  ·
                    refine ⟨601100993379861112016357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 400733995586574074677571 601100993379861112016357)
                    ·
                      refine ⟨112706436258723958503067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 601100993379861112016357 112706436258723958503067)
                      ·
                        rfl

theorem cell23_219495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3, 2, 1, 1, 4].length) (baseStart_219495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_219495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_219495 prefixEnd_219495 := by exact prefixLift 219495
  have htrace : WordTrace (prefixWord ++ tailWord_219495) baseStart_219495 baseEnd_219495 := by
    simpa [prefixWord, tailWord_219495, baseEnd_219495] using wordTrace_append hprefix tailTrace_219495
  have hstable : (prefixWord ++ tailWord_219495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219495).length < 2 ^ (prefixWord ++ tailWord_219495).sum := by decide
  have hdescent : baseEnd_219495 < baseStart_219495 := by decide
  rcases family_descends (prefixWord ++ tailWord_219495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219501 : List Nat := [1, 5, 1, 1, 1, 2, 1, 11]
def baseStart_219501 : Nat := 118140960795 + 219501 * 2 ^ 59
def prefixEnd_219501 : Nat := 4983230072969 + 3 ^ 40 * 219501 * 2
def baseEnd_219501 : Nat := 4174426560838923519557

theorem tailTrace_219501 : CollatzResearch.WordTrace tailWord_219501 prefixEnd_219501 4174426560838923519557 := by
  unfold tailWord_219501
  simp only [CollatzResearch.WordTrace]
  refine ⟨8005859177792839631354357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5337239451861893087569571 8005859177792839631354357)
  ·
    refine ⟨750549297918078715439471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8005859177792839631354357 750549297918078715439471)
    ·
      refine ⟨1125823946877118073159207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 750549297918078715439471 1125823946877118073159207)
      ·
        refine ⟨1688735920315677109738811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1125823946877118073159207 1688735920315677109738811)
        ·
          refine ⟨2533103880473515664608217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1688735920315677109738811 2533103880473515664608217)
          ·
            refine ⟨1899827910355136748456163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2533103880473515664608217 1899827910355136748456163)
            ·
              refine ⟨2849741865532705122684245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1899827910355136748456163 2849741865532705122684245)
              ·
                refine ⟨4174426560838923519557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 2849741865532705122684245 4174426560838923519557)
                ·
                  rfl

theorem cell23_219501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 11].length) (baseStart_219501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_219501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_219501 prefixEnd_219501 := by exact prefixLift 219501
  have htrace : WordTrace (prefixWord ++ tailWord_219501) baseStart_219501 baseEnd_219501 := by
    simpa [prefixWord, tailWord_219501, baseEnd_219501] using wordTrace_append hprefix tailTrace_219501
  have hstable : (prefixWord ++ tailWord_219501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219501).length < 2 ^ (prefixWord ++ tailWord_219501).sum := by decide
  have hdescent : baseEnd_219501 < baseStart_219501 := by decide
  rcases family_descends (prefixWord ++ tailWord_219501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219528 : List Nat := [2, 1, 3, 3, 1, 1, 1, 2, 3, 3, 3]
def baseStart_219528 : Nat := 118140960795 + 219528 * 2 ^ 59
def prefixEnd_219528 : Nat := 4983230072969 + 3 ^ 40 * 219528 * 2
def baseEnd_219528 : Nat := 112723381120322329390415

theorem tailTrace_219528 : CollatzResearch.WordTrace tailWord_219528 prefixEnd_219528 112723381120322329390415 := by
  unfold tailWord_219528
  simp only [CollatzResearch.WordTrace]
  refine ⟨4003421974347511621293619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5337895965796682161724825 4003421974347511621293619)
  ·
    refine ⟨6005132961521267431940429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4003421974347511621293619 6005132961521267431940429)
    ·
      refine ⟨2251924860570475286977661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6005132961521267431940429 2251924860570475286977661)
      ·
        refine ⟨844471822713928232616623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2251924860570475286977661 844471822713928232616623)
        ·
          refine ⟨1266707734070892348924935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 844471822713928232616623 1266707734070892348924935)
          ·
            refine ⟨1900061601106338523387403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1266707734070892348924935 1900061601106338523387403)
            ·
              refine ⟨2850092401659507785081105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1900061601106338523387403 2850092401659507785081105)
              ·
                refine ⟨2137569301244630838810829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2850092401659507785081105 2137569301244630838810829)
                ·
                  refine ⟨801588487966736564554061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2137569301244630838810829 801588487966736564554061)
                  ·
                    refine ⟨300595682987526211707773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 801588487966736564554061 300595682987526211707773)
                    ·
                      refine ⟨112723381120322329390415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 300595682987526211707773 112723381120322329390415)
                      ·
                        rfl

theorem cell23_219528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 2, 3, 3, 3].length) (baseStart_219528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_219528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_219528 prefixEnd_219528 := by exact prefixLift 219528
  have htrace : WordTrace (prefixWord ++ tailWord_219528) baseStart_219528 baseEnd_219528 := by
    simpa [prefixWord, tailWord_219528, baseEnd_219528] using wordTrace_append hprefix tailTrace_219528
  have hstable : (prefixWord ++ tailWord_219528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219528).length < 2 ^ (prefixWord ++ tailWord_219528).sum := by decide
  have hdescent : baseEnd_219528 < baseStart_219528 := by decide
  rcases family_descends (prefixWord ++ tailWord_219528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219529 : List Nat := [1, 2, 1, 1, 6, 2, 1, 4, 1, 2, 2]
def baseStart_219529 : Nat := 118140960795 + 219529 * 2 ^ 59
def prefixEnd_219529 : Nat := 4983230072969 + 3 ^ 40 * 219529 * 2
def baseEnd_219529 : Nat := 112723894600976825477911

theorem tailTrace_219529 : CollatzResearch.WordTrace tailWord_219529 prefixEnd_219529 112723894600976825477911 := by
  unfold tailWord_219529
  simp only [CollatzResearch.WordTrace]
  refine ⟨8006880421691400413373641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5337920281127600275582427 8006880421691400413373641)
  ·
    refine ⟨6005160316268550310030231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8006880421691400413373641 6005160316268550310030231)
    ·
      refine ⟨9007740474402825465045347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6005160316268550310030231 9007740474402825465045347)
      ·
        refine ⟨13511610711604238197568021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9007740474402825465045347 13511610711604238197568021)
        ·
          refine ⟨633356752106448665511001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 13511610711604238197568021 633356752106448665511001)
          ·
            refine ⟨475017564079836499133251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 633356752106448665511001 475017564079836499133251)
            ·
              refine ⟨712526346119754748699877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 475017564079836499133251 712526346119754748699877)
              ·
                refine ⟨133598689897454015381227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 712526346119754748699877 133598689897454015381227)
                ·
                  refine ⟨200398034846181023071841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 133598689897454015381227 200398034846181023071841)
                  ·
                    refine ⟨150298526134635767303881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 200398034846181023071841 150298526134635767303881)
                    ·
                      refine ⟨112723894600976825477911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 150298526134635767303881 112723894600976825477911)
                      ·
                        rfl

theorem cell23_219529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 4, 1, 2, 2].length) (baseStart_219529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_219529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_219529 prefixEnd_219529 := by exact prefixLift 219529
  have htrace : WordTrace (prefixWord ++ tailWord_219529) baseStart_219529 baseEnd_219529 := by
    simpa [prefixWord, tailWord_219529, baseEnd_219529] using wordTrace_append hprefix tailTrace_219529
  have hstable : (prefixWord ++ tailWord_219529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219529).length < 2 ^ (prefixWord ++ tailWord_219529).sum := by decide
  have hdescent : baseEnd_219529 < baseStart_219529 := by decide
  rcases family_descends (prefixWord ++ tailWord_219529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219531 : List Nat := [1, 1, 1, 1, 4, 4, 1, 1, 2, 7]
def baseStart_219531 : Nat := 118140960795 + 219531 * 2 ^ 59
def prefixEnd_219531 : Nat := 4983230072969 + 3 ^ 40 * 219531 * 2
def baseEnd_219531 : Nat := 37574973854095272550967

theorem tailTrace_219531 : CollatzResearch.WordTrace tailWord_219531 prefixEnd_219531 37574973854095272550967 := by
  unfold tailWord_219531
  simp only [CollatzResearch.WordTrace]
  refine ⟨8006953367684154754946447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5337968911789436503297631 8006953367684154754946447)
  ·
    refine ⟨12010430051526232132419671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8006953367684154754946447 12010430051526232132419671)
    ·
      refine ⟨18015645077289348198629507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12010430051526232132419671 18015645077289348198629507)
      ·
        refine ⟨27023467615934022297944261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18015645077289348198629507 27023467615934022297944261)
        ·
          refine ⟨5066900177987629180864549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27023467615934022297944261 5066900177987629180864549)
          ·
            refine ⟨950043783372680471412103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5066900177987629180864549 950043783372680471412103)
            ·
              refine ⟨1425065675059020707118155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 950043783372680471412103 1425065675059020707118155)
              ·
                refine ⟨2137598512588531060677233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1425065675059020707118155 2137598512588531060677233)
                ·
                  refine ⟨1603198884441398295507925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2137598512588531060677233 1603198884441398295507925)
                  ·
                    refine ⟨37574973854095272550967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1603198884441398295507925 37574973854095272550967)
                    ·
                      rfl

theorem cell23_219531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 1, 2, 7].length) (baseStart_219531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_219531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_219531 prefixEnd_219531 := by exact prefixLift 219531
  have htrace : WordTrace (prefixWord ++ tailWord_219531) baseStart_219531 baseEnd_219531 := by
    simpa [prefixWord, tailWord_219531, baseEnd_219531] using wordTrace_append hprefix tailTrace_219531
  have hstable : (prefixWord ++ tailWord_219531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219531).length < 2 ^ (prefixWord ++ tailWord_219531).sum := by decide
  have hdescent : baseEnd_219531 < baseStart_219531 := by decide
  rcases family_descends (prefixWord ++ tailWord_219531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219541 : List Nat := [1, 3, 2, 1, 1, 2, 1, 2, 1, 4, 5]
def baseStart_219541 : Nat := 118140960795 + 219541 * 2 ^ 59
def prefixEnd_219541 : Nat := 4983230072969 + 3 ^ 40 * 219541 * 2
def baseEnd_219541 : Nat := 112730056368830778527855

theorem tailTrace_219541 : CollatzResearch.WordTrace tailWord_219541 prefixEnd_219541 112730056368830778527855 := by
  unfold tailWord_219541
  simp only [CollatzResearch.WordTrace]
  refine ⟨8007318097647926462810477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5338212065098617641873651 8007318097647926462810477)
  ·
    refine ⟨3002744286617972423553929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8007318097647926462810477 3002744286617972423553929)
    ·
      refine ⟨2252058214963479317665447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3002744286617972423553929 2252058214963479317665447)
      ·
        refine ⟨3378087322445218976498171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2252058214963479317665447 3378087322445218976498171)
        ·
          refine ⟨5067130983667828464747257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3378087322445218976498171 5067130983667828464747257)
          ·
            refine ⟨3800348237750871348560443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5067130983667828464747257 3800348237750871348560443)
            ·
              refine ⟨5700522356626307022840665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3800348237750871348560443 5700522356626307022840665)
              ·
                refine ⟨4275391767469730267130499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5700522356626307022840665 4275391767469730267130499)
                ·
                  refine ⟨6413087651204595400695749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4275391767469730267130499 6413087651204595400695749)
                  ·
                    refine ⟨1202453934600861637630453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6413087651204595400695749 1202453934600861637630453)
                    ·
                      refine ⟨112730056368830778527855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1202453934600861637630453 112730056368830778527855)
                      ·
                        rfl

theorem cell23_219541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 4, 5].length) (baseStart_219541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_219541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_219541 prefixEnd_219541 := by exact prefixLift 219541
  have htrace : WordTrace (prefixWord ++ tailWord_219541) baseStart_219541 baseEnd_219541 := by
    simpa [prefixWord, tailWord_219541, baseEnd_219541] using wordTrace_append hprefix tailTrace_219541
  have hstable : (prefixWord ++ tailWord_219541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219541).length < 2 ^ (prefixWord ++ tailWord_219541).sum := by decide
  have hdescent : baseEnd_219541 < baseStart_219541 := by decide
  rcases family_descends (prefixWord ++ tailWord_219541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219545 : List Nat := [1, 2, 1, 2, 1, 4, 1, 5, 2, 1, 3]
def baseStart_219545 : Nat := 118140960795 + 219545 * 2 ^ 59
def prefixEnd_219545 : Nat := 4983230072969 + 3 ^ 40 * 219545 * 2
def baseEnd_219545 : Nat := 112732110291448762877837

theorem tailTrace_219545 : CollatzResearch.WordTrace tailWord_219545 prefixEnd_219545 112732110291448762877837 := by
  unfold tailWord_219545
  simp only [CollatzResearch.WordTrace]
  refine ⟨8007463989633435145956089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5338309326422290097304059 8007463989633435145956089)
  ·
    refine ⟨6005597992225076359467067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8007463989633435145956089 6005597992225076359467067)
    ·
      refine ⟨9008396988337614539200601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6005597992225076359467067 9008396988337614539200601)
      ·
        refine ⟨6756297741253210904400451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9008396988337614539200601 6756297741253210904400451)
        ·
          refine ⟨10134446611879816356600677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6756297741253210904400451 10134446611879816356600677)
          ·
            refine ⟨1900208739727465566862627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10134446611879816356600677 1900208739727465566862627)
            ·
              refine ⟨2850313109591198350293941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1900208739727465566862627 2850313109591198350293941)
              ·
                refine ⟨267216854024174845340057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2850313109591198350293941 267216854024174845340057)
                ·
                  refine ⟨200412640518131134005043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 267216854024174845340057 200412640518131134005043)
                  ·
                    refine ⟨300618960777196701007565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 200412640518131134005043 300618960777196701007565)
                    ·
                      refine ⟨112732110291448762877837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 300618960777196701007565 112732110291448762877837)
                      ·
                        rfl

theorem cell23_219545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 5, 2, 1, 3].length) (baseStart_219545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_219545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_219545 prefixEnd_219545 := by exact prefixLift 219545
  have htrace : WordTrace (prefixWord ++ tailWord_219545) baseStart_219545 baseEnd_219545 := by
    simpa [prefixWord, tailWord_219545, baseEnd_219545] using wordTrace_append hprefix tailTrace_219545
  have hstable : (prefixWord ++ tailWord_219545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219545).length < 2 ^ (prefixWord ++ tailWord_219545).sum := by decide
  have hdescent : baseEnd_219545 < baseStart_219545 := by decide
  rcases family_descends (prefixWord ++ tailWord_219545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219555 : List Nat := [1, 1, 1, 4, 1, 4, 2, 1, 3, 3, 2]
def baseStart_219555 : Nat := 118140960795 + 219555 * 2 ^ 59
def prefixEnd_219555 : Nat := 4983230072969 + 3 ^ 40 * 219555 * 2
def baseEnd_219555 : Nat := 112737245097993723752791

theorem tailTrace_219555 : CollatzResearch.WordTrace tailWord_219555 prefixEnd_219555 112737245097993723752791 := by
  unfold tailWord_219555
  simp only [CollatzResearch.WordTrace]
  refine ⟨8007828719597206853820119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5338552479731471235880079 8007828719597206853820119)
  ·
    refine ⟨12011743079395810280730179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8007828719597206853820119 12011743079395810280730179)
    ·
      refine ⟨18017614619093715421095269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12011743079395810280730179 18017614619093715421095269)
      ·
        refine ⟨3378302741080071641455363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18017614619093715421095269 3378302741080071641455363)
        ·
          refine ⟨5067454111620107462183045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3378302741080071641455363 5067454111620107462183045)
          ·
            refine ⟨950147645928770149159321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5067454111620107462183045 950147645928770149159321)
            ·
              refine ⟨712610734446577611869491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 950147645928770149159321 712610734446577611869491)
              ·
                refine ⟨1068916101669866417804237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 712610734446577611869491 1068916101669866417804237)
                ·
                  refine ⟨400843538126199906676589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1068916101669866417804237 400843538126199906676589)
                  ·
                    refine ⟨150316326797324965003721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 400843538126199906676589 150316326797324965003721)
                    ·
                      refine ⟨112737245097993723752791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 150316326797324965003721 112737245097993723752791)
                      ·
                        rfl

theorem cell23_219555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 1, 3, 3, 2].length) (baseStart_219555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_219555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_219555 prefixEnd_219555 := by exact prefixLift 219555
  have htrace : WordTrace (prefixWord ++ tailWord_219555) baseStart_219555 baseEnd_219555 := by
    simpa [prefixWord, tailWord_219555, baseEnd_219555] using wordTrace_append hprefix tailTrace_219555
  have hstable : (prefixWord ++ tailWord_219555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219555).length < 2 ^ (prefixWord ++ tailWord_219555).sum := by decide
  have hdescent : baseEnd_219555 < baseStart_219555 := by decide
  rcases family_descends (prefixWord ++ tailWord_219555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219568 : List Nat := [2, 1, 1, 1, 2, 1, 1, 2, 2, 8, 2]
def baseStart_219568 : Nat := 118140960795 + 219568 * 2 ^ 59
def prefixEnd_219568 : Nat := 4983230072969 + 3 ^ 40 * 219568 * 2
def baseEnd_219568 : Nat := 112743920346502172890231

theorem tailTrace_219568 : CollatzResearch.WordTrace tailWord_219568 prefixEnd_219568 112743920346502172890231 := by
  unfold tailWord_219568
  simp only [CollatzResearch.WordTrace]
  refine ⟨4004151434275055037021679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5338868579033406716028905 4004151434275055037021679)
  ·
    refine ⟨6006227151412582555532519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4004151434275055037021679 6006227151412582555532519)
    ·
      refine ⟨9009340727118873833298779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6006227151412582555532519 9009340727118873833298779)
      ·
        refine ⟨13514011090678310749948169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9009340727118873833298779 13514011090678310749948169)
        ·
          refine ⟨10135508318008733062461127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13514011090678310749948169 10135508318008733062461127)
          ·
            refine ⟨15203262477013099593691691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10135508318008733062461127 15203262477013099593691691)
            ·
              refine ⟨22804893715519649390537537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15203262477013099593691691 22804893715519649390537537)
              ·
                refine ⟨17103670286639737042903153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22804893715519649390537537 17103670286639737042903153)
                ·
                  refine ⟨12827752714979802782177365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17103670286639737042903153 12827752714979802782177365)
                  ·
                    refine ⟨150325227128669563853641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 12827752714979802782177365 150325227128669563853641)
                    ·
                      refine ⟨112743920346502172890231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 150325227128669563853641 112743920346502172890231)
                      ·
                        rfl

theorem cell23_219568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 2, 8, 2].length) (baseStart_219568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_219568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_219568 prefixEnd_219568 := by exact prefixLift 219568
  have htrace : WordTrace (prefixWord ++ tailWord_219568) baseStart_219568 baseEnd_219568 := by
    simpa [prefixWord, tailWord_219568, baseEnd_219568] using wordTrace_append hprefix tailTrace_219568
  have hstable : (prefixWord ++ tailWord_219568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219568).length < 2 ^ (prefixWord ++ tailWord_219568).sum := by decide
  have hdescent : baseEnd_219568 < baseStart_219568 := by decide
  rcases family_descends (prefixWord ++ tailWord_219568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219601 : List Nat := [1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 9]
def baseStart_219601 : Nat := 118140960795 + 219601 * 2 ^ 59
def prefixEnd_219601 : Nat := 4983230072969 + 3 ^ 40 * 219601 * 2
def baseEnd_219601 : Nat := 112760865208100543777579

theorem tailTrace_219601 : CollatzResearch.WordTrace tailWord_219601 prefixEnd_219601 112760865208100543777579 := by
  unfold tailWord_219601
  simp only [CollatzResearch.WordTrace]
  refine ⟨8009506477430556709994657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5339670984953704473329771 8009506477430556709994657)
  ·
    refine ⟨6007129858072917532495993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8009506477430556709994657 6007129858072917532495993)
    ·
      refine ⟨4505347393554688149371995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6007129858072917532495993 4505347393554688149371995)
      ·
        refine ⟨6758021090332032224057993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4505347393554688149371995 6758021090332032224057993)
        ·
          refine ⟨5068515817749024168043495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6758021090332032224057993 5068515817749024168043495)
          ·
            refine ⟨7602773726623536252065243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5068515817749024168043495 7602773726623536252065243)
            ·
              refine ⟨11404160589935304378097865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7602773726623536252065243 11404160589935304378097865)
              ·
                refine ⟨8553120442451478283573399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11404160589935304378097865 8553120442451478283573399)
                ·
                  refine ⟨12829680663677217425360099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8553120442451478283573399 12829680663677217425360099)
                  ·
                    refine ⟨19244520995515826138040149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12829680663677217425360099 19244520995515826138040149)
                    ·
                      refine ⟨112760865208100543777579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 19244520995515826138040149 112760865208100543777579)
                      ·
                        rfl

theorem cell23_219601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 9].length) (baseStart_219601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_219601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_219601 prefixEnd_219601 := by exact prefixLift 219601
  have htrace : WordTrace (prefixWord ++ tailWord_219601) baseStart_219601 baseEnd_219601 := by
    simpa [prefixWord, tailWord_219601, baseEnd_219601] using wordTrace_append hprefix tailTrace_219601
  have hstable : (prefixWord ++ tailWord_219601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219601).length < 2 ^ (prefixWord ++ tailWord_219601).sum := by decide
  have hdescent : baseEnd_219601 < baseStart_219601 := by decide
  rcases family_descends (prefixWord ++ tailWord_219601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219645 : List Nat := [1, 4, 1, 1, 1, 3, 2, 1, 2, 5, 2]
def baseStart_219645 : Nat := 118140960795 + 219645 * 2 ^ 59
def prefixEnd_219645 : Nat := 4983230072969 + 3 ^ 40 * 219645 * 2
def baseEnd_219645 : Nat := 112783458356898371627377

theorem tailTrace_219645 : CollatzResearch.WordTrace tailWord_219645 prefixEnd_219645 112783458356898371627377 := by
  unfold tailWord_219645
  simp only [CollatzResearch.WordTrace]
  refine ⟨8011111289271152224596389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5340740859514101483064259 8011111289271152224596389)
  ·
    refine ⟨1502083366738341042111823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8011111289271152224596389 1502083366738341042111823)
    ·
      refine ⟨2253125050107511563167735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1502083366738341042111823 2253125050107511563167735)
      ·
        refine ⟨3379687575161267344751603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2253125050107511563167735 3379687575161267344751603)
        ·
          refine ⟨5069531362741901017127405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3379687575161267344751603 5069531362741901017127405)
          ·
            refine ⟨1901074261028212881422777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5069531362741901017127405 1901074261028212881422777)
            ·
              refine ⟨1425805695771159661067083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1901074261028212881422777 1425805695771159661067083)
              ·
                refine ⟨2138708543656739491600625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1425805695771159661067083 2138708543656739491600625)
                ·
                  refine ⟨1604031407742554618700469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2138708543656739491600625 1604031407742554618700469)
                  ·
                    refine ⟨150377944475864495503169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1604031407742554618700469 150377944475864495503169)
                    ·
                      refine ⟨112783458356898371627377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 150377944475864495503169 112783458356898371627377)
                      ·
                        rfl

theorem cell23_219645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 1, 2, 5, 2].length) (baseStart_219645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_219645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_219645 prefixEnd_219645 := by exact prefixLift 219645
  have htrace : WordTrace (prefixWord ++ tailWord_219645) baseStart_219645 baseEnd_219645 := by
    simpa [prefixWord, tailWord_219645, baseEnd_219645] using wordTrace_append hprefix tailTrace_219645
  have hstable : (prefixWord ++ tailWord_219645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219645).length < 2 ^ (prefixWord ++ tailWord_219645).sum := by decide
  have hdescent : baseEnd_219645 < baseStart_219645 := by decide
  rcases family_descends (prefixWord ++ tailWord_219645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219698 : List Nat := [3, 2, 1, 1, 2, 1, 2, 3, 8]
def baseStart_219698 : Nat := 118140960795 + 219698 * 2 ^ 59
def prefixEnd_219698 : Nat := 4983230072969 + 3 ^ 40 * 219698 * 2
def baseEnd_219698 : Nat := 12534519203509629362737

theorem tailTrace_219698 : CollatzResearch.WordTrace tailWord_219698 prefixEnd_219698 12534519203509629362737 := by
  unfold tailWord_219698
  simp only [CollatzResearch.WordTrace]
  refine ⟨2003261089519785569068937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5342029572052761517517165 2003261089519785569068937)
  ·
    refine ⟨1502445817139839176801703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2003261089519785569068937 1502445817139839176801703)
    ·
      refine ⟨2253668725709758765202555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1502445817139839176801703 2253668725709758765202555)
      ·
        refine ⟨3380503088564638147803833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2253668725709758765202555 3380503088564638147803833)
        ·
          refine ⟨2535377316423478610852875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3380503088564638147803833 2535377316423478610852875)
          ·
            refine ⟨3803065974635217916279313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2535377316423478610852875 3803065974635217916279313)
            ·
              refine ⟨2852299480976413437209485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3803065974635217916279313 2852299480976413437209485)
              ·
                refine ⟨1069612305366155038953557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2852299480976413437209485 1069612305366155038953557)
                ·
                  refine ⟨12534519203509629362737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1069612305366155038953557 12534519203509629362737)
                  ·
                    rfl

theorem cell23_219698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 3, 8].length) (baseStart_219698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_219698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_219698 prefixEnd_219698 := by exact prefixLift 219698
  have htrace : WordTrace (prefixWord ++ tailWord_219698) baseStart_219698 baseEnd_219698 := by
    simpa [prefixWord, tailWord_219698, baseEnd_219698] using wordTrace_append hprefix tailTrace_219698
  have hstable : (prefixWord ++ tailWord_219698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219698).length < 2 ^ (prefixWord ++ tailWord_219698).sum := by decide
  have hdescent : baseEnd_219698 < baseStart_219698 := by decide
  rcases family_descends (prefixWord ++ tailWord_219698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219738 : List Nat := [3, 1, 1, 2, 1, 1, 1, 1, 1, 6, 5]
def baseStart_219738 : Nat := 118140960795 + 219738 * 2 ^ 59
def prefixEnd_219738 : Nat := 4983230072969 + 3 ^ 40 * 219738 * 2
def baseEnd_219738 : Nat := 112831212057766507764449

theorem tailTrace_219738 : CollatzResearch.WordTrace tailWord_219738 prefixEnd_219738 112831212057766507764449 := by
  unfold tailWord_219738
  simp only [CollatzResearch.WordTrace]
  refine ⟨2003625819483557276932967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5343002185289486071821245 2003625819483557276932967)
  ·
    refine ⟨3005438729225335915399451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2003625819483557276932967 3005438729225335915399451)
    ·
      refine ⟨4508158093838003873099177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3005438729225335915399451 4508158093838003873099177)
      ·
        refine ⟨3381118570378502904824383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4508158093838003873099177 3381118570378502904824383)
        ·
          refine ⟨5071677855567754357236575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3381118570378502904824383 5071677855567754357236575)
          ·
            refine ⟨7607516783351631535854863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5071677855567754357236575 7607516783351631535854863)
            ·
              refine ⟨11411275175027447303782295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7607516783351631535854863 11411275175027447303782295)
              ·
                refine ⟨17116912762541170955673443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11411275175027447303782295 17116912762541170955673443)
                ·
                  refine ⟨25675369143811756433510165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17116912762541170955673443 25675369143811756433510165)
                  ·
                    refine ⟨1203532928616176082820789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25675369143811756433510165 1203532928616176082820789)
                    ·
                      refine ⟨112831212057766507764449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1203532928616176082820789 112831212057766507764449)
                      ·
                        rfl

theorem cell23_219738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 1, 6, 5].length) (baseStart_219738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_219738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_219738 prefixEnd_219738 := by exact prefixLift 219738
  have htrace : WordTrace (prefixWord ++ tailWord_219738) baseStart_219738 baseEnd_219738 := by
    simpa [prefixWord, tailWord_219738, baseEnd_219738] using wordTrace_append hprefix tailTrace_219738
  have hstable : (prefixWord ++ tailWord_219738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219738).length < 2 ^ (prefixWord ++ tailWord_219738).sum := by decide
  have hdescent : baseEnd_219738 < baseStart_219738 := by decide
  rcases family_descends (prefixWord ++ tailWord_219738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219749 : List Nat := [1, 3, 1, 3, 5, 1, 1, 2, 6]
def baseStart_219749 : Nat := 118140960795 + 219749 * 2 ^ 59
def prefixEnd_219749 : Nat := 4983230072969 + 3 ^ 40 * 219749 * 2
def baseEnd_219749 : Nat := 12537428927218440525211

theorem tailTrace_219749 : CollatzResearch.WordTrace tailWord_219749 prefixEnd_219749 12537428927218440525211 := by
  unfold tailWord_219749
  simp only [CollatzResearch.WordTrace]
  refine ⟨8014904480894377986382301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5343269653929585324254867 8014904480894377986382301)
  ·
    refine ⟨3005589180335391744893363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8014904480894377986382301 3005589180335391744893363)
    ·
      refine ⟨4508383770503087617340045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3005589180335391744893363 4508383770503087617340045)
      ·
        refine ⟨1690643913938657856502517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4508383770503087617340045 1690643913938657856502517)
        ·
          refine ⟨158497866931749174047111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1690643913938657856502517 158497866931749174047111)
          ·
            refine ⟨237746800397623761070667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158497866931749174047111 237746800397623761070667)
            ·
              refine ⟨356620200596435641606001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 237746800397623761070667 356620200596435641606001)
              ·
                refine ⟨267465150447326731204501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 356620200596435641606001 267465150447326731204501)
                ·
                  refine ⟨12537428927218440525211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 267465150447326731204501 12537428927218440525211)
                  ·
                    rfl

theorem cell23_219749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 1, 2, 6].length) (baseStart_219749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_219749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_219749 prefixEnd_219749 := by exact prefixLift 219749
  have htrace : WordTrace (prefixWord ++ tailWord_219749) baseStart_219749 baseEnd_219749 := by
    simpa [prefixWord, tailWord_219749, baseEnd_219749] using wordTrace_append hprefix tailTrace_219749
  have hstable : (prefixWord ++ tailWord_219749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219749).length < 2 ^ (prefixWord ++ tailWord_219749).sum := by decide
  have hdescent : baseEnd_219749 < baseStart_219749 := by decide
  rcases family_descends (prefixWord ++ tailWord_219749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219759 : List Nat := [1, 1, 2, 1, 3, 2, 4, 4, 1, 1, 3]
def baseStart_219759 : Nat := 118140960795 + 219759 * 2 ^ 59
def prefixEnd_219759 : Nat := 4983230072969 + 3 ^ 40 * 219759 * 2
def baseEnd_219759 : Nat := 112841995151510925601853

theorem tailTrace_219759 : CollatzResearch.WordTrace tailWord_219759 prefixEnd_219759 112841995151510925601853 := by
  unfold tailWord_219759
  simp only [CollatzResearch.WordTrace]
  refine ⟨8015269210858149694246331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5343512807238766462830887 8015269210858149694246331)
  ·
    refine ⟨12022903816287224541369497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8015269210858149694246331 12022903816287224541369497)
    ·
      refine ⟨9017177862215418406027123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12022903816287224541369497 9017177862215418406027123)
      ·
        refine ⟨13525766793323127609040685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9017177862215418406027123 13525766793323127609040685)
        ·
          refine ⟨5072162547496172853390257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13525766793323127609040685 5072162547496172853390257)
          ·
            refine ⟨3804121910622129640042693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5072162547496172853390257 3804121910622129640042693)
            ·
              refine ⟨713272858241649307508005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3804121910622129640042693 713272858241649307508005)
              ·
                refine ⟨133738660920309245157751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 713272858241649307508005 133738660920309245157751)
                ·
                  refine ⟨200607991380463867736627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 133738660920309245157751 200607991380463867736627)
                  ·
                    refine ⟨300911987070695801604941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 200607991380463867736627 300911987070695801604941)
                    ·
                      refine ⟨112841995151510925601853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 300911987070695801604941 112841995151510925601853)
                      ·
                        rfl

theorem cell23_219759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 4, 1, 1, 3].length) (baseStart_219759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_219759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_219759 prefixEnd_219759 := by exact prefixLift 219759
  have htrace : WordTrace (prefixWord ++ tailWord_219759) baseStart_219759 baseEnd_219759 := by
    simpa [prefixWord, tailWord_219759, baseEnd_219759] using wordTrace_append hprefix tailTrace_219759
  have hstable : (prefixWord ++ tailWord_219759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219759).length < 2 ^ (prefixWord ++ tailWord_219759).sum := by decide
  have hdescent : baseEnd_219759 < baseStart_219759 := by decide
  rcases family_descends (prefixWord ++ tailWord_219759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219822 : List Nat := [4, 1, 4, 1, 1, 1, 1, 10]
def baseStart_219822 : Nat := 118140960795 + 219822 * 2 ^ 59
def prefixEnd_219822 : Nat := 4983230072969 + 3 ^ 40 * 219822 * 2
def baseEnd_219822 : Nat := 4180531275286821448669

theorem tailTrace_219822 : CollatzResearch.WordTrace tailWord_219822 prefixEnd_219822 4180531275286821448669 := by
  unfold tailWord_219822
  simp only [CollatzResearch.WordTrace]
  refine ⟨1002195876203738931723715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5345044673086607635859813 1002195876203738931723715)
  ·
    refine ⟨1503293814305608397585573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1002195876203738931723715 1503293814305608397585573)
    ·
      refine ⟨281867590182301574547295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1503293814305608397585573 281867590182301574547295)
      ·
        refine ⟨422801385273452361820943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281867590182301574547295 422801385273452361820943)
        ·
          refine ⟨634202077910178542731415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 422801385273452361820943 634202077910178542731415)
          ·
            refine ⟨951303116865267814097123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 634202077910178542731415 951303116865267814097123)
            ·
              refine ⟨1426954675297901721145685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 951303116865267814097123 1426954675297901721145685)
              ·
                refine ⟨4180531275286821448669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 1426954675297901721145685 4180531275286821448669)
                ·
                  rfl

theorem cell23_219822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 10].length) (baseStart_219822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_219822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_219822 prefixEnd_219822 := by exact prefixLift 219822
  have htrace : WordTrace (prefixWord ++ tailWord_219822) baseStart_219822 baseEnd_219822 := by
    simpa [prefixWord, tailWord_219822, baseEnd_219822] using wordTrace_append hprefix tailTrace_219822
  have hstable : (prefixWord ++ tailWord_219822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219822).length < 2 ^ (prefixWord ++ tailWord_219822).sum := by decide
  have hdescent : baseEnd_219822 < baseStart_219822 := by decide
  rcases family_descends (prefixWord ++ tailWord_219822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219853 : List Nat := [1, 6, 2, 1, 3, 1, 1, 1, 1, 1, 5]
def baseStart_219853 : Nat := 118140960795 + 219853 * 2 ^ 59
def prefixEnd_219853 : Nat := 4983230072969 + 3 ^ 40 * 219853 * 2
def baseEnd_219853 : Nat := 112890262333033557826421

theorem tailTrace_219853 : CollatzResearch.WordTrace tailWord_219853 prefixEnd_219853 112890262333033557826421 := by
  unfold tailWord_219853
  simp only [CollatzResearch.WordTrace]
  refine ⟨8018697672517603748168213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5345798448345069165445475 8018697672517603748168213)
  ·
    refine ⟨375876453399262675695385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 8018697672517603748168213 375876453399262675695385)
    ·
      refine ⟨281907340049447006771539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 375876453399262675695385 281907340049447006771539)
      ·
        refine ⟨422861010074170510157309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281907340049447006771539 422861010074170510157309)
        ·
          refine ⟨158572878777813941308991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 422861010074170510157309 158572878777813941308991)
          ·
            refine ⟨237859318166720911963487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158572878777813941308991 237859318166720911963487)
            ·
              refine ⟨356788977250081367945231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 237859318166720911963487 356788977250081367945231)
              ·
                refine ⟨535183465875122051917847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 356788977250081367945231 535183465875122051917847)
                ·
                  refine ⟨802775198812683077876771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 535183465875122051917847 802775198812683077876771)
                  ·
                    refine ⟨1204162798219024616815157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 802775198812683077876771 1204162798219024616815157)
                    ·
                      refine ⟨112890262333033557826421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1204162798219024616815157 112890262333033557826421)
                      ·
                        rfl

theorem cell23_219853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 1, 1, 1, 1, 5].length) (baseStart_219853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_219853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_219853 prefixEnd_219853 := by exact prefixLift 219853
  have htrace : WordTrace (prefixWord ++ tailWord_219853) baseStart_219853 baseEnd_219853 := by
    simpa [prefixWord, tailWord_219853, baseEnd_219853] using wordTrace_append hprefix tailTrace_219853
  have hstable : (prefixWord ++ tailWord_219853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219853).length < 2 ^ (prefixWord ++ tailWord_219853).sum := by decide
  have hdescent : baseEnd_219853 < baseStart_219853 := by decide
  rcases family_descends (prefixWord ++ tailWord_219853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
