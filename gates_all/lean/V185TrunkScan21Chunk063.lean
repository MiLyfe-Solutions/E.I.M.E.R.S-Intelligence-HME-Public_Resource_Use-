import V185TrunkScan21Chunk062

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_762165 : List Nat := [1, 3, 3, 1, 2, 1, 2, 3, 5]
def baseStart_762165 : Nat := 118140960795 + 762165 * 2 ^ 59
def prefixEnd_762165 : Nat := 4983230072969 + 3 ^ 40 * 762165 * 2
def baseEnd_762165 : Nat := 173936436904051448725499

theorem tailTrace_762165 : CollatzResearch.WordTrace tailWord_762165 prefixEnd_762165 173936436904051448725499 := by
  unfold tailWord_762165
  simp only [CollatzResearch.WordTrace]
  refine ⟨27798441283813847263951949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18532294189209231509301299 27798441283813847263951949)
  ·
    refine ⟨10424415481430192723981981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27798441283813847263951949 10424415481430192723981981)
    ·
      refine ⟨3909155805536322271493243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10424415481430192723981981 3909155805536322271493243)
      ·
        refine ⟨5863733708304483407239865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3909155805536322271493243 5863733708304483407239865)
        ·
          refine ⟨4397800281228362555429899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5863733708304483407239865 4397800281228362555429899)
          ·
            refine ⟨6596700421842543833144849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4397800281228362555429899 6596700421842543833144849)
            ·
              refine ⟨4947525316381907874858637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6596700421842543833144849 4947525316381907874858637)
              ·
                refine ⟨1855321993643215453071989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4947525316381907874858637 1855321993643215453071989)
                ·
                  refine ⟨173936436904051448725499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1855321993643215453071989 173936436904051448725499)
                  ·
                    rfl

theorem cell21_762165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 3, 5].length) (baseStart_762165 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_762165 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_762165 prefixEnd_762165 := by exact prefixLift 762165
  have htrace : WordTrace (prefixWord ++ tailWord_762165) baseStart_762165 baseEnd_762165 := by
    simpa [prefixWord, tailWord_762165, baseEnd_762165] using wordTrace_append hprefix tailTrace_762165
  have hstable : (prefixWord ++ tailWord_762165).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762165).length < 2 ^ (prefixWord ++ tailWord_762165).sum := by decide
  have hdescent : baseEnd_762165 < baseStart_762165 := by decide
  rcases family_descends (prefixWord ++ tailWord_762165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762213 : List Nat := [1, 3, 1, 3, 1, 5, 1, 2, 4]
def baseStart_762213 : Nat := 118140960795 + 762213 * 2 ^ 59
def prefixEnd_762213 : Nat := 4983230072969 + 3 ^ 40 * 762213 * 2
def baseEnd_762213 : Nat := 173947391158014031925401

theorem tailTrace_762213 : CollatzResearch.WordTrace tailWord_762213 prefixEnd_762213 173947391158014031925401 := by
  unfold tailWord_762213
  simp only [CollatzResearch.WordTrace]
  refine ⟨27800191987639951461699293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18533461325093300974466195 27800191987639951461699293)
  ·
    refine ⟨10425071995364981798137235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27800191987639951461699293 10425071995364981798137235)
    ·
      refine ⟨15637607993047472697205853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10425071995364981798137235 15637607993047472697205853)
      ·
        refine ⟨5864102997392802261452195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15637607993047472697205853 5864102997392802261452195)
        ·
          refine ⟨8796154496089203392178293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5864102997392802261452195 8796154496089203392178293)
          ·
            refine ⟨824639484008362818016715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8796154496089203392178293 824639484008362818016715)
            ·
              refine ⟨1236959226012544227025073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 824639484008362818016715 1236959226012544227025073)
              ·
                refine ⟨927719419509408170268805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1236959226012544227025073 927719419509408170268805)
                ·
                  refine ⟨173947391158014031925401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 927719419509408170268805 173947391158014031925401)
                  ·
                    rfl

theorem cell21_762213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 1, 2, 4].length) (baseStart_762213 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_762213 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_762213 prefixEnd_762213 := by exact prefixLift 762213
  have htrace : WordTrace (prefixWord ++ tailWord_762213) baseStart_762213 baseEnd_762213 := by
    simpa [prefixWord, tailWord_762213, baseEnd_762213] using wordTrace_append hprefix tailTrace_762213
  have hstable : (prefixWord ++ tailWord_762213).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762213).length < 2 ^ (prefixWord ++ tailWord_762213).sum := by decide
  have hdescent : baseEnd_762213 < baseStart_762213 := by decide
  rcases family_descends (prefixWord ++ tailWord_762213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762275 : List Nat := [1, 1, 1, 4, 1, 5, 3, 2, 3]
def baseStart_762275 : Nat := 118140960795 + 762275 * 2 ^ 59
def prefixEnd_762275 : Nat := 4983230072969 + 3 ^ 40 * 762275 * 2
def baseEnd_762275 : Nat := 173961540402715701891941

theorem tailTrace_762275 : CollatzResearch.WordTrace tailWord_762275 prefixEnd_762275 173961540402715701891941 := by
  unfold tailWord_762275
  simp only [CollatzResearch.WordTrace]
  refine ⟨27802453313415336050456279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18534968875610224033637519 27802453313415336050456279)
  ·
    refine ⟨41703679970123004075684419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27802453313415336050456279 41703679970123004075684419)
    ·
      refine ⟨62555519955184506113526629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41703679970123004075684419 62555519955184506113526629)
      ·
        refine ⟨11729159991597094896286243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62555519955184506113526629 11729159991597094896286243)
        ·
          refine ⟨17593739987395642344429365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11729159991597094896286243 17593739987395642344429365)
          ·
            refine ⟨1649413123818341469790253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17593739987395642344429365 1649413123818341469790253)
            ·
              refine ⟨618529921431878051171345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1649413123818341469790253 618529921431878051171345)
              ·
                refine ⟨463897441073908538378509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 618529921431878051171345 463897441073908538378509)
                ·
                  refine ⟨173961540402715701891941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 463897441073908538378509 173961540402715701891941)
                  ·
                    rfl

theorem cell21_762275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 3, 2, 3].length) (baseStart_762275 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_762275 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_762275 prefixEnd_762275 := by exact prefixLift 762275
  have htrace : WordTrace (prefixWord ++ tailWord_762275) baseStart_762275 baseEnd_762275 := by
    simpa [prefixWord, tailWord_762275, baseEnd_762275] using wordTrace_append hprefix tailTrace_762275
  have hstable : (prefixWord ++ tailWord_762275).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762275).length < 2 ^ (prefixWord ++ tailWord_762275).sum := by decide
  have hdescent : baseEnd_762275 < baseStart_762275 := by decide
  rcases family_descends (prefixWord ++ tailWord_762275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762289 : List Nat := [1, 2, 2, 4, 1, 2, 4, 1, 4]
def baseStart_762289 : Nat := 118140960795 + 762289 * 2 ^ 59
def prefixEnd_762289 : Nat := 4983230072969 + 3 ^ 40 * 762289 * 2
def baseEnd_762289 : Nat := 173964735393454788658579

theorem tailTrace_762289 : CollatzResearch.WordTrace tailWord_762289 prefixEnd_762289 173964735393454788658579 := by
  unfold tailWord_762289
  simp only [CollatzResearch.WordTrace]
  refine ⟨27802963935364616441465921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18535309290243077627643947 27802963935364616441465921)
  ·
    refine ⟨20852222951523462331099441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27802963935364616441465921 20852222951523462331099441)
    ·
      refine ⟨15639167213642596748324581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20852222951523462331099441 15639167213642596748324581)
      ·
        refine ⟨2932343852557986890310859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15639167213642596748324581 2932343852557986890310859)
        ·
          refine ⟨4398515778836980335466289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2932343852557986890310859 4398515778836980335466289)
          ·
            refine ⟨3298886834127735251599717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4398515778836980335466289 3298886834127735251599717)
            ·
              refine ⟨618541281398950359674947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3298886834127735251599717 618541281398950359674947)
              ·
                refine ⟨927811922098425539512421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 618541281398950359674947 927811922098425539512421)
                ·
                  refine ⟨173964735393454788658579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 927811922098425539512421 173964735393454788658579)
                  ·
                    rfl

theorem cell21_762289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 4, 1, 4].length) (baseStart_762289 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_762289 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_762289 prefixEnd_762289 := by exact prefixLift 762289
  have htrace : WordTrace (prefixWord ++ tailWord_762289) baseStart_762289 baseEnd_762289 := by
    simpa [prefixWord, tailWord_762289, baseEnd_762289] using wordTrace_append hprefix tailTrace_762289
  have hstable : (prefixWord ++ tailWord_762289).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762289).length < 2 ^ (prefixWord ++ tailWord_762289).sum := by decide
  have hdescent : baseEnd_762289 < baseStart_762289 := by decide
  rcases family_descends (prefixWord ++ tailWord_762289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762345 : List Nat := [1, 2, 1, 1, 1, 2, 1, 12]
def baseStart_762345 : Nat := 118140960795 + 762345 * 2 ^ 59
def prefixEnd_762345 : Nat := 4983230072969 + 3 ^ 40 * 762345 * 2
def baseEnd_762345 : Nat := 57992505118803711908377

theorem tailTrace_762345 : CollatzResearch.WordTrace tailWord_762345 prefixEnd_762345 57992505118803711908377 := by
  unfold tailWord_762345
  simp only [CollatzResearch.WordTrace]
  refine ⟨27805006423161738005504489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18536670948774492003669659 27805006423161738005504489)
  ·
    refine ⟨20853754817371303504128367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27805006423161738005504489 20853754817371303504128367)
    ·
      refine ⟨31280632226056955256192551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20853754817371303504128367 31280632226056955256192551)
      ·
        refine ⟨46920948339085432884288827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31280632226056955256192551 46920948339085432884288827)
        ·
          refine ⟨70381422508628149326433241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46920948339085432884288827 70381422508628149326433241)
          ·
            refine ⟨52786066881471111994824931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70381422508628149326433241 52786066881471111994824931)
            ·
              refine ⟨79179100322206667992237397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52786066881471111994824931 79179100322206667992237397)
              ·
                refine ⟨57992505118803711908377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 79179100322206667992237397 57992505118803711908377)
                ·
                  rfl

theorem cell21_762345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 12].length) (baseStart_762345 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_762345 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_762345 prefixEnd_762345 := by exact prefixLift 762345
  have htrace : WordTrace (prefixWord ++ tailWord_762345) baseStart_762345 baseEnd_762345 := by
    simpa [prefixWord, tailWord_762345, baseEnd_762345] using wordTrace_append hprefix tailTrace_762345
  have hstable : (prefixWord ++ tailWord_762345).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762345).length < 2 ^ (prefixWord ++ tailWord_762345).sum := by decide
  have hdescent : baseEnd_762345 < baseStart_762345 := by decide
  rcases family_descends (prefixWord ++ tailWord_762345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762376 : List Nat := [2, 1, 3, 2, 1, 1, 1, 1, 9]
def baseStart_762376 : Nat := 118140960795 + 762376 * 2 ^ 59
def prefixEnd_762376 : Nat := 4983230072969 + 3 ^ 40 * 762376 * 2
def baseEnd_762376 : Nat := 173984589978761970708401

theorem tailTrace_762376 : CollatzResearch.WordTrace tailWord_762376 prefixEnd_762376 173984589978761970708401 := by
  unfold tailWord_762376
  simp only [CollatzResearch.WordTrace]
  refine ⟨13903068543024715149941491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18537424724032953533255321 13903068543024715149941491)
  ·
    refine ⟨20854602814537072724912237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13903068543024715149941491 20854602814537072724912237)
    ·
      refine ⟨7820476055451402271842089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20854602814537072724912237 7820476055451402271842089)
      ·
        refine ⟨5865357041588551703881567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7820476055451402271842089 5865357041588551703881567)
        ·
          refine ⟨8798035562382827555822351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5865357041588551703881567 8798035562382827555822351)
          ·
            refine ⟨13197053343574241333733527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8798035562382827555822351 13197053343574241333733527)
            ·
              refine ⟨19795580015361362000600291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13197053343574241333733527 19795580015361362000600291)
              ·
                refine ⟨29693370023042043000900437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19795580015361362000600291 29693370023042043000900437)
                ·
                  refine ⟨173984589978761970708401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 29693370023042043000900437 173984589978761970708401)
                  ·
                    rfl

theorem cell21_762376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 9].length) (baseStart_762376 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_762376 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_762376 prefixEnd_762376 := by exact prefixLift 762376
  have htrace : WordTrace (prefixWord ++ tailWord_762376) baseStart_762376 baseEnd_762376 := by
    simpa [prefixWord, tailWord_762376, baseEnd_762376] using wordTrace_append hprefix tailTrace_762376
  have hstable : (prefixWord ++ tailWord_762376).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762376).length < 2 ^ (prefixWord ++ tailWord_762376).sum := by decide
  have hdescent : baseEnd_762376 < baseStart_762376 := by decide
  rcases family_descends (prefixWord ++ tailWord_762376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762413 : List Nat := [1, 5, 4, 1, 1, 1, 1, 7]
def baseStart_762413 : Nat := 118140960795 + 762413 * 2 ^ 59
def prefixEnd_762413 : Nat := 4983230072969 + 3 ^ 40 * 762413 * 2
def baseEnd_762413 : Nat := 57997677960952709530553

theorem tailTrace_762413 : CollatzResearch.WordTrace tailWord_762413 prefixEnd_762413 57997677960952709530553 := by
  unfold tailWord_762413
  simp only [CollatzResearch.WordTrace]
  refine ⟨27807486586915385618979893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18538324391276923745986595 27807486586915385618979893)
  ·
    refine ⟨2606951867523317401779365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27807486586915385618979893 2606951867523317401779365)
    ·
      refine ⟨488803475160622012833631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2606951867523317401779365 488803475160622012833631)
      ·
        refine ⟨733205212740933019250447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 488803475160622012833631 733205212740933019250447)
        ·
          refine ⟨1099807819111399528875671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 733205212740933019250447 1099807819111399528875671)
          ·
            refine ⟨1649711728667099293313507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1099807819111399528875671 1649711728667099293313507)
            ·
              refine ⟨2474567593000648939970261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1649711728667099293313507 2474567593000648939970261)
              ·
                refine ⟨57997677960952709530553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2474567593000648939970261 57997677960952709530553)
                ·
                  rfl

theorem cell21_762413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 7].length) (baseStart_762413 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_762413 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_762413 prefixEnd_762413 := by exact prefixLift 762413
  have htrace : WordTrace (prefixWord ++ tailWord_762413) baseStart_762413 baseEnd_762413 := by
    simpa [prefixWord, tailWord_762413, baseEnd_762413] using wordTrace_append hprefix tailTrace_762413
  have hstable : (prefixWord ++ tailWord_762413).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762413).length < 2 ^ (prefixWord ++ tailWord_762413).sum := by decide
  have hdescent : baseEnd_762413 < baseStart_762413 := by decide
  rcases family_descends (prefixWord ++ tailWord_762413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762500 : List Nat := [2, 3, 2, 1, 3, 1, 1, 4, 4]
def baseStart_762500 : Nat := 118140960795 + 762500 * 2 ^ 59
def prefixEnd_762500 : Nat := 4983230072969 + 3 ^ 40 * 762500 * 2
def baseEnd_762500 : Nat := 174012888468165310641481

theorem tailTrace_762500 : CollatzResearch.WordTrace tailWord_762500 prefixEnd_762500 174012888468165310641481 := by
  unfold tailWord_762500
  simp only [CollatzResearch.WordTrace]
  refine ⟨13905329868800099738698477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18540439825066799651597969 13905329868800099738698477)
  ·
    refine ⟨5214498700800037402011929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13905329868800099738698477 5214498700800037402011929)
    ·
      refine ⟨3910874025600028051508947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5214498700800037402011929 3910874025600028051508947)
      ·
        refine ⟨5866311038400042077263421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3910874025600028051508947 5866311038400042077263421)
        ·
          refine ⟨2199866639400015778973783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5866311038400042077263421 2199866639400015778973783)
          ·
            refine ⟨3299799959100023668460675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2199866639400015778973783 3299799959100023668460675)
            ·
              refine ⟨4949699938650035502691013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3299799959100023668460675 4949699938650035502691013)
              ·
                refine ⟨928068738496881656754565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4949699938650035502691013 928068738496881656754565)
                ·
                  refine ⟨174012888468165310641481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 928068738496881656754565 174012888468165310641481)
                  ·
                    rfl

theorem cell21_762500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 4, 4].length) (baseStart_762500 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_762500 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_762500 prefixEnd_762500 := by exact prefixLift 762500
  have htrace : WordTrace (prefixWord ++ tailWord_762500) baseStart_762500 baseEnd_762500 := by
    simpa [prefixWord, tailWord_762500, baseEnd_762500] using wordTrace_append hprefix tailTrace_762500
  have hstable : (prefixWord ++ tailWord_762500).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762500).length < 2 ^ (prefixWord ++ tailWord_762500).sum := by decide
  have hdescent : baseEnd_762500 < baseStart_762500 := by decide
  rcases family_descends (prefixWord ++ tailWord_762500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762559 : List Nat := [1, 1, 2, 2, 2, 5, 1, 1, 6]
def baseStart_762559 : Nat := 118140960795 + 762559 * 2 ^ 59
def prefixEnd_762559 : Nat := 4983230072969 + 3 ^ 40 * 762559 * 2
def baseEnd_762559 : Nat := 174026353071994319158027

theorem tailTrace_762559 : CollatzResearch.WordTrace tailWord_762559 prefixEnd_762559 174026353071994319158027 := by
  unfold tailWord_762559
  simp only [CollatzResearch.WordTrace]
  refine ⟨27812811644386452553794731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18541874429590968369196487 27812811644386452553794731)
  ·
    refine ⟨41719217466579678830692097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27812811644386452553794731 41719217466579678830692097)
    ·
      refine ⟨31289413099934759123019073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41719217466579678830692097 31289413099934759123019073)
      ·
        refine ⟨23467059824951069342264305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31289413099934759123019073 23467059824951069342264305)
        ·
          refine ⟨17600294868713302006698229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23467059824951069342264305 17600294868713302006698229)
          ·
            refine ⟨1650027643941872063127959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17600294868713302006698229 1650027643941872063127959)
            ·
              refine ⟨2475041465912808094691939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1650027643941872063127959 2475041465912808094691939)
              ·
                refine ⟨3712562198869212142037909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2475041465912808094691939 3712562198869212142037909)
                ·
                  refine ⟨174026353071994319158027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3712562198869212142037909 174026353071994319158027)
                  ·
                    rfl

theorem cell21_762559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 1, 6].length) (baseStart_762559 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_762559 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_762559 prefixEnd_762559 := by exact prefixLift 762559
  have htrace : WordTrace (prefixWord ++ tailWord_762559) baseStart_762559 baseEnd_762559 := by
    simpa [prefixWord, tailWord_762559, baseEnd_762559] using wordTrace_append hprefix tailTrace_762559
  have hstable : (prefixWord ++ tailWord_762559).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762559).length < 2 ^ (prefixWord ++ tailWord_762559).sum := by decide
  have hdescent : baseEnd_762559 < baseStart_762559 := by decide
  rcases family_descends (prefixWord ++ tailWord_762559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762613 : List Nat := [1, 3, 6, 1, 2, 1, 1, 1, 5]
def baseStart_762613 : Nat := 118140960795 + 762613 * 2 ^ 59
def prefixEnd_762613 : Nat := 4983230072969 + 3 ^ 40 * 762613 * 2
def baseEnd_762613 : Nat := 174038676607702225257917

theorem tailTrace_762613 : CollatzResearch.WordTrace tailWord_762613 prefixEnd_762613 174038676607702225257917 := by
  unfold tailWord_762613
  simp only [CollatzResearch.WordTrace]
  refine ⟨27814781186190819776260493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18543187457460546517506995 27814781186190819776260493)
  ·
    refine ⟨10430542944821557416097685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27814781186190819776260493 10430542944821557416097685)
    ·
      refine ⟨488931700538510503879579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 10430542944821557416097685 488931700538510503879579)
      ·
        refine ⟨733397550807765755819369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 488931700538510503879579 733397550807765755819369)
        ·
          refine ⟨550048163105824316864527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 733397550807765755819369 550048163105824316864527)
          ·
            refine ⟨825072244658736475296791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 550048163105824316864527 825072244658736475296791)
            ·
              refine ⟨1237608366988104712945187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 825072244658736475296791 1237608366988104712945187)
              ·
                refine ⟨1856412550482157069417781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1237608366988104712945187 1856412550482157069417781)
                ·
                  refine ⟨174038676607702225257917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1856412550482157069417781 174038676607702225257917)
                  ·
                    rfl

theorem cell21_762613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 1, 1, 5].length) (baseStart_762613 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_762613 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_762613 prefixEnd_762613 := by exact prefixLift 762613
  have htrace : WordTrace (prefixWord ++ tailWord_762613) baseStart_762613 baseEnd_762613 := by
    simpa [prefixWord, tailWord_762613, baseEnd_762613] using wordTrace_append hprefix tailTrace_762613
  have hstable : (prefixWord ++ tailWord_762613).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762613).length < 2 ^ (prefixWord ++ tailWord_762613).sum := by decide
  have hdescent : baseEnd_762613 < baseStart_762613 := by decide
  rcases family_descends (prefixWord ++ tailWord_762613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762666 : List Nat := [3, 1, 4, 3, 10]
def baseStart_762666 : Nat := 118140960795 + 762666 * 2 ^ 59
def prefixEnd_762666 : Nat := 4983230072969 + 3 ^ 40 * 762666 * 2
def baseEnd_762666 : Nat := 2148774962096122356475

theorem tailTrace_762666 : CollatzResearch.WordTrace tailWord_762666 prefixEnd_762666 2148774962096122356475 := by
  unfold tailWord_762666
  simp only [CollatzResearch.WordTrace]
  refine ⟨6954178563749702456984963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18544476169999206551959901 6954178563749702456984963)
  ·
    refine ⟨10431267845624553685477445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6954178563749702456984963 10431267845624553685477445)
    ·
      refine ⟨1955862721054603816027021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10431267845624553685477445 1955862721054603816027021)
      ·
        refine ⟨733448520395476431010133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1955862721054603816027021 733448520395476431010133)
        ·
          refine ⟨2148774962096122356475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 733448520395476431010133 2148774962096122356475)
          ·
            rfl

theorem cell21_762666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 10].length) (baseStart_762666 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_762666 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_762666 prefixEnd_762666 := by exact prefixLift 762666
  have htrace : WordTrace (prefixWord ++ tailWord_762666) baseStart_762666 baseEnd_762666 := by
    simpa [prefixWord, tailWord_762666, baseEnd_762666] using wordTrace_append hprefix tailTrace_762666
  have hstable : (prefixWord ++ tailWord_762666).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762666).length < 2 ^ (prefixWord ++ tailWord_762666).sum := by decide
  have hdescent : baseEnd_762666 < baseStart_762666 := by decide
  rcases family_descends (prefixWord ++ tailWord_762666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762680 : List Nat := [2, 1, 2, 1, 3, 2, 2, 3, 5]
def baseStart_762680 : Nat := 118140960795 + 762680 * 2 ^ 59
def prefixEnd_762680 : Nat := 4983230072969 + 3 ^ 40 * 762680 * 2
def baseEnd_762680 : Nat := 174053966920524997641113

theorem tailTrace_762680 : CollatzResearch.WordTrace tailWord_762680 prefixEnd_762680 174053966920524997641113 := by
  unfold tailWord_762680
  simp only [CollatzResearch.WordTrace]
  refine ⟨13908612438474045109474747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18544816584632060145966329 13908612438474045109474747)
  ·
    refine ⟨20862918657711067664212121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13908612438474045109474747 20862918657711067664212121)
    ·
      refine ⟨15647188993283300748159091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20862918657711067664212121 15647188993283300748159091)
      ·
        refine ⟨23470783489924951122238637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15647188993283300748159091 23470783489924951122238637)
        ·
          refine ⟨8801543808721856670839489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23470783489924951122238637 8801543808721856670839489)
          ·
            refine ⟨6601157856541392503129617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8801543808721856670839489 6601157856541392503129617)
            ·
              refine ⟨4950868392406044377347213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6601157856541392503129617 4950868392406044377347213)
              ·
                refine ⟨1856575647152266641505205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4950868392406044377347213 1856575647152266641505205)
                ·
                  refine ⟨174053966920524997641113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1856575647152266641505205 174053966920524997641113)
                  ·
                    rfl

theorem cell21_762680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 3, 5].length) (baseStart_762680 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_762680 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_762680 prefixEnd_762680 := by exact prefixLift 762680
  have htrace : WordTrace (prefixWord ++ tailWord_762680) baseStart_762680 baseEnd_762680 := by
    simpa [prefixWord, tailWord_762680, baseEnd_762680] using wordTrace_append hprefix tailTrace_762680
  have hstable : (prefixWord ++ tailWord_762680).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762680).length < 2 ^ (prefixWord ++ tailWord_762680).sum := by decide
  have hdescent : baseEnd_762680 < baseStart_762680 := by decide
  rcases family_descends (prefixWord ++ tailWord_762680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762714 : List Nat := [3, 1, 1, 2, 1, 5, 2, 3, 3]
def baseStart_762714 : Nat := 118140960795 + 762714 * 2 ^ 59
def prefixEnd_762714 : Nat := 4983230072969 + 3 ^ 40 * 762714 * 2
def baseEnd_762714 : Nat := 174061726183748494074377

theorem tailTrace_762714 : CollatzResearch.WordTrace tailWord_762714 prefixEnd_762714 174061726183748494074377 := by
  unfold tailWord_762714
  simp only [CollatzResearch.WordTrace]
  refine ⟨6954616239706228506421799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18545643305883276017124797 6954616239706228506421799)
  ·
    refine ⟨10431924359559342759632699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6954616239706228506421799 10431924359559342759632699)
    ·
      refine ⟨15647886539339014139449049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10431924359559342759632699 15647886539339014139449049)
      ·
        refine ⟨11735914904504260604586787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15647886539339014139449049 11735914904504260604586787)
        ·
          refine ⟨17603872356756390906880181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11735914904504260604586787 17603872356756390906880181)
          ·
            refine ⟨1650363033445911647520017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17603872356756390906880181 1650363033445911647520017)
            ·
              refine ⟨1237772275084433735640013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1650363033445911647520017 1237772275084433735640013)
              ·
                refine ⟨464164603156662650865005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1237772275084433735640013 464164603156662650865005)
                ·
                  refine ⟨174061726183748494074377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 464164603156662650865005 174061726183748494074377)
                  ·
                    rfl

theorem cell21_762714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2, 3, 3].length) (baseStart_762714 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_762714 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_762714 prefixEnd_762714 := by exact prefixLift 762714
  have htrace : WordTrace (prefixWord ++ tailWord_762714) baseStart_762714 baseEnd_762714 := by
    simpa [prefixWord, tailWord_762714, baseEnd_762714] using wordTrace_append hprefix tailTrace_762714
  have hstable : (prefixWord ++ tailWord_762714).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762714).length < 2 ^ (prefixWord ++ tailWord_762714).sum := by decide
  have hdescent : baseEnd_762714 < baseStart_762714 := by decide
  rcases family_descends (prefixWord ++ tailWord_762714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762728 : List Nat := [2, 1, 4, 2, 1, 2, 3, 2, 4]
def baseStart_762728 : Nat := 118140960795 + 762728 * 2 ^ 59
def prefixEnd_762728 : Nat := 4983230072969 + 3 ^ 40 * 762728 * 2
def baseEnd_762728 : Nat := 174064921174487580841015

theorem tailTrace_762728 : CollatzResearch.WordTrace tailWord_762728 prefixEnd_762728 174064921174487580841015 := by
  unfold tailWord_762728
  simp only [CollatzResearch.WordTrace]
  refine ⟨13909487790387097208348419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18545983720516129611131225 13909487790387097208348419)
  ·
    refine ⟨20864231685580645812522629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13909487790387097208348419 20864231685580645812522629)
    ·
      refine ⟨3912043441046371089847993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20864231685580645812522629 3912043441046371089847993)
      ·
        refine ⟨2934032580784778317385995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3912043441046371089847993 2934032580784778317385995)
        ·
          refine ⟨4401048871177167476078993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2934032580784778317385995 4401048871177167476078993)
          ·
            refine ⟨3300786653382875607059245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4401048871177167476078993 3300786653382875607059245)
            ·
              refine ⟨1237794995018578352647217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3300786653382875607059245 1237794995018578352647217)
              ·
                refine ⟨928346246263933764485413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1237794995018578352647217 928346246263933764485413)
                ·
                  refine ⟨174064921174487580841015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 928346246263933764485413 174064921174487580841015)
                  ·
                    rfl

theorem cell21_762728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3, 2, 4].length) (baseStart_762728 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_762728 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_762728 prefixEnd_762728 := by exact prefixLift 762728
  have htrace : WordTrace (prefixWord ++ tailWord_762728) baseStart_762728 baseEnd_762728 := by
    simpa [prefixWord, tailWord_762728, baseEnd_762728] using wordTrace_append hprefix tailTrace_762728
  have hstable : (prefixWord ++ tailWord_762728).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762728).length < 2 ^ (prefixWord ++ tailWord_762728).sum := by decide
  have hdescent : baseEnd_762728 < baseStart_762728 := by decide
  rcases family_descends (prefixWord ++ tailWord_762728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762759 : List Nat := [1, 1, 4, 2, 3, 3, 2, 5]
def baseStart_762759 : Nat := 118140960795 + 762759 * 2 ^ 59
def prefixEnd_762759 : Nat := 4983230072969 + 3 ^ 40 * 762759 * 2
def baseEnd_762759 : Nat := 58023998598946138608095

theorem tailTrace_762759 : CollatzResearch.WordTrace tailWord_762759 prefixEnd_762759 58023998598946138608095 := by
  unfold tailWord_762759
  simp only [CollatzResearch.WordTrace]
  refine ⟨27820106243661886711075331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18546737495774591140716887 27820106243661886711075331)
  ·
    refine ⟨41730159365492830066612997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27820106243661886711075331 41730159365492830066612997)
    ·
      refine ⟨7824404881029905637489937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41730159365492830066612997 7824404881029905637489937)
      ·
        refine ⟨5868303660772429228117453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7824404881029905637489937 5868303660772429228117453)
        ·
          refine ⟨2200613872789660960544045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5868303660772429228117453 2200613872789660960544045)
          ·
            refine ⟨825230202296122860204017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2200613872789660960544045 825230202296122860204017)
            ·
              refine ⟨618922651722092145153013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 825230202296122860204017 618922651722092145153013)
              ·
                refine ⟨58023998598946138608095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 618922651722092145153013 58023998598946138608095)
                ·
                  rfl

theorem cell21_762759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 2, 5].length) (baseStart_762759 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_762759 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_762759 prefixEnd_762759 := by exact prefixLift 762759
  have htrace : WordTrace (prefixWord ++ tailWord_762759) baseStart_762759 baseEnd_762759 := by
    simpa [prefixWord, tailWord_762759, baseEnd_762759] using wordTrace_append hprefix tailTrace_762759
  have hstable : (prefixWord ++ tailWord_762759).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762759).length < 2 ^ (prefixWord ++ tailWord_762759).sum := by decide
  have hdescent : baseEnd_762759 < baseStart_762759 := by decide
  rcases family_descends (prefixWord ++ tailWord_762759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762863 : List Nat := [1, 1, 2, 1, 4, 3, 2, 3, 4]
def baseStart_762863 : Nat := 118140960795 + 762863 * 2 ^ 59
def prefixEnd_762863 : Nat := 4983230072969 + 3 ^ 40 * 762863 * 2
def baseEnd_762863 : Nat := 174095730013757346090739

theorem tailTrace_762863 : CollatzResearch.WordTrace tailWord_762863 prefixEnd_762863 174095730013757346090739 := by
  unfold tailWord_762863
  simp only [CollatzResearch.WordTrace]
  refine ⟨27823899435285112472861243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18549266290190074981907495 27823899435285112472861243)
  ·
    refine ⟨41735849152927668709291865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27823899435285112472861243 41735849152927668709291865)
    ·
      refine ⟨31301886864695751531968899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41735849152927668709291865 31301886864695751531968899)
      ·
        refine ⟨46952830297043627297953349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31301886864695751531968899 46952830297043627297953349)
        ·
          refine ⟨8803655680695680118366253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46952830297043627297953349 8803655680695680118366253)
          ·
            refine ⟨3301370880260880044387345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8803655680695680118366253 3301370880260880044387345)
            ·
              refine ⟨2476028160195660033290509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3301370880260880044387345 2476028160195660033290509)
              ·
                refine ⟨928510560073372512483941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2476028160195660033290509 928510560073372512483941)
                ·
                  refine ⟨174095730013757346090739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 928510560073372512483941 174095730013757346090739)
                  ·
                    rfl

theorem cell21_762863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 3, 4].length) (baseStart_762863 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_762863 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_762863 prefixEnd_762863 := by exact prefixLift 762863
  have htrace : WordTrace (prefixWord ++ tailWord_762863) baseStart_762863 baseEnd_762863 := by
    simpa [prefixWord, tailWord_762863, baseEnd_762863] using wordTrace_append hprefix tailTrace_762863
  have hstable : (prefixWord ++ tailWord_762863).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762863).length < 2 ^ (prefixWord ++ tailWord_762863).sum := by decide
  have hdescent : baseEnd_762863 < baseStart_762863 := by decide
  rcases family_descends (prefixWord ++ tailWord_762863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762866 : List Nat := [3, 2, 1, 5, 1, 1, 1, 2, 5]
def baseStart_762866 : Nat := 118140960795 + 762866 * 2 ^ 59
def prefixEnd_762866 : Nat := 4983230072969 + 3 ^ 40 * 762866 * 2
def baseEnd_762866 : Nat := 174096414654630007540733

theorem tailTrace_762866 : CollatzResearch.WordTrace tailWord_762866 prefixEnd_762866 174096414654630007540733 := by
  unfold tailWord_762866
  simp only [CollatzResearch.WordTrace]
  refine ⟨6956002213568560996305113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18549339236182829323480301 6956002213568560996305113)
  ·
    refine ⟨5217001660176420747228835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6956002213568560996305113 5217001660176420747228835)
    ·
      refine ⟨7825502490264631120843253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5217001660176420747228835 7825502490264631120843253)
      ·
        refine ⟨733640858462309167579055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7825502490264631120843253 733640858462309167579055)
        ·
          refine ⟨1100461287693463751368583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 733640858462309167579055 1100461287693463751368583)
          ·
            refine ⟨1650691931540195627052875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1100461287693463751368583 1650691931540195627052875)
            ·
              refine ⟨2476037897310293440579313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1650691931540195627052875 2476037897310293440579313)
              ·
                refine ⟨1857028422982720080434485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2476037897310293440579313 1857028422982720080434485)
                ·
                  refine ⟨174096414654630007540733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1857028422982720080434485 174096414654630007540733)
                  ·
                    rfl

theorem cell21_762866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 2, 5].length) (baseStart_762866 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_762866 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_762866 prefixEnd_762866 := by exact prefixLift 762866
  have htrace : WordTrace (prefixWord ++ tailWord_762866) baseStart_762866 baseEnd_762866 := by
    simpa [prefixWord, tailWord_762866, baseEnd_762866] using wordTrace_append hprefix tailTrace_762866
  have hstable : (prefixWord ++ tailWord_762866).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762866).length < 2 ^ (prefixWord ++ tailWord_762866).sum := by decide
  have hdescent : baseEnd_762866 < baseStart_762866 := by decide
  rcases family_descends (prefixWord ++ tailWord_762866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762973 : List Nat := [1, 4, 4, 1, 2, 1, 1, 3, 4]
def baseStart_762973 : Nat := 118140960795 + 762973 * 2 ^ 59
def prefixEnd_762973 : Nat := 4983230072969 + 3 ^ 40 * 762973 * 2
def baseEnd_762973 : Nat := 174120833512421599257181

theorem tailTrace_762973 : CollatzResearch.WordTrace tailWord_762973 prefixEnd_762973 174120833512421599257181 := by
  unfold tailWord_762973
  simp only [CollatzResearch.WordTrace]
  refine ⟨27827911464886601259365573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18551940976591067506243715 27827911464886601259365573)
  ·
    refine ⟨5217733399666237736131045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27827911464886601259365573 5217733399666237736131045)
    ·
      refine ⟨978325012437419575524571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5217733399666237736131045 978325012437419575524571)
      ·
        refine ⟨1467487518656129363286857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 978325012437419575524571 1467487518656129363286857)
        ·
          refine ⟨1100615638992097022465143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1467487518656129363286857 1100615638992097022465143)
          ·
            refine ⟨1650923458488145533697715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1100615638992097022465143 1650923458488145533697715)
            ·
              refine ⟨2476385187732218300546573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1650923458488145533697715 2476385187732218300546573)
              ·
                refine ⟨928644445399581862704965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2476385187732218300546573 928644445399581862704965)
                ·
                  refine ⟨174120833512421599257181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 928644445399581862704965 174120833512421599257181)
                  ·
                    rfl

theorem cell21_762973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 3, 4].length) (baseStart_762973 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_762973 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_762973 prefixEnd_762973 := by exact prefixLift 762973
  have htrace : WordTrace (prefixWord ++ tailWord_762973) baseStart_762973 baseEnd_762973 := by
    simpa [prefixWord, tailWord_762973, baseEnd_762973] using wordTrace_append hprefix tailTrace_762973
  have hstable : (prefixWord ++ tailWord_762973).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762973).length < 2 ^ (prefixWord ++ tailWord_762973).sum := by decide
  have hdescent : baseEnd_762973 < baseStart_762973 := by decide
  rcases family_descends (prefixWord ++ tailWord_762973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763105 : List Nat := [1, 2, 3, 1, 3, 3, 1, 7]
def baseStart_763105 : Nat := 118140960795 + 763105 * 2 ^ 59
def prefixEnd_763105 : Nat := 4983230072969 + 3 ^ 40 * 763105 * 2
def baseEnd_763105 : Nat := 58050319236939567685637

theorem tailTrace_763105 : CollatzResearch.WordTrace tailWord_763105 prefixEnd_763105 58050319236939567685637 := by
  unfold tailWord_763105
  simp only [CollatzResearch.WordTrace]
  refine ⟨27832725900408387803170769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18555150600272258535447179 27832725900408387803170769)
  ·
    refine ⟨20874544425306290852378077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27832725900408387803170769 20874544425306290852378077)
    ·
      refine ⟨7827954159489859069641779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20874544425306290852378077 7827954159489859069641779)
      ·
        refine ⟨11741931239234788604462669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7827954159489859069641779 11741931239234788604462669)
        ·
          refine ⟨4403224214713045726673501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11741931239234788604462669 4403224214713045726673501)
          ·
            refine ⟨1651209080517392147502563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4403224214713045726673501 1651209080517392147502563)
            ·
              refine ⟨2476813620776088221253845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1651209080517392147502563 2476813620776088221253845)
              ·
                refine ⟨58050319236939567685637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2476813620776088221253845 58050319236939567685637)
                ·
                  rfl

theorem cell21_763105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 7].length) (baseStart_763105 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_763105 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_763105 prefixEnd_763105 := by exact prefixLift 763105
  have htrace : WordTrace (prefixWord ++ tailWord_763105) baseStart_763105 baseEnd_763105 := by
    simpa [prefixWord, tailWord_763105, baseEnd_763105] using wordTrace_append hprefix tailTrace_763105
  have hstable : (prefixWord ++ tailWord_763105).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763105).length < 2 ^ (prefixWord ++ tailWord_763105).sum := by decide
  have hdescent : baseEnd_763105 < baseStart_763105 := by decide
  rcases family_descends (prefixWord ++ tailWord_763105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763111 : List Nat := [1, 1, 5, 3, 2, 2, 1, 3, 3]
def baseStart_763111 : Nat := 118140960795 + 763111 * 2 ^ 59
def prefixEnd_763111 : Nat := 4983230072969 + 3 ^ 40 * 763111 * 2
def baseEnd_763111 : Nat := 174152326992564025956899

theorem tailTrace_763111 : CollatzResearch.WordTrace tailWord_763111 prefixEnd_763111 174152326992564025956899 := by
  unfold tailWord_763111
  simp only [CollatzResearch.WordTrace]
  refine ⟨27832944738386650827889187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18555296492257767218592791 27832944738386650827889187)
  ·
    refine ⟨41749417107579976241833781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27832944738386650827889187 41749417107579976241833781)
    ·
      refine ⟨3914007853835622772671917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41749417107579976241833781 3914007853835622772671917)
      ·
        refine ⟨1467752945188358539751969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3914007853835622772671917 1467752945188358539751969)
        ·
          refine ⟨1100814708891268904813977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1467752945188358539751969 1100814708891268904813977)
          ·
            refine ⟨825611031668451678610483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1100814708891268904813977 825611031668451678610483)
            ·
              refine ⟨1238416547502677517915725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 825611031668451678610483 1238416547502677517915725)
              ·
                refine ⟨464406205313504069218397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1238416547502677517915725 464406205313504069218397)
                ·
                  refine ⟨174152326992564025956899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 464406205313504069218397 174152326992564025956899)
                  ·
                    rfl

theorem cell21_763111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 1, 3, 3].length) (baseStart_763111 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_763111 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_763111 prefixEnd_763111 := by exact prefixLift 763111
  have htrace : WordTrace (prefixWord ++ tailWord_763111) baseStart_763111 baseEnd_763111 := by
    simpa [prefixWord, tailWord_763111, baseEnd_763111] using wordTrace_append hprefix tailTrace_763111
  have hstable : (prefixWord ++ tailWord_763111).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763111).length < 2 ^ (prefixWord ++ tailWord_763111).sum := by decide
  have hdescent : baseEnd_763111 < baseStart_763111 := by decide
  rcases family_descends (prefixWord ++ tailWord_763111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763122 : List Nat := [3, 2, 1, 3, 3, 2, 7]
def baseStart_763122 : Nat := 118140960795 + 763122 * 2 ^ 59
def prefixEnd_763122 : Nat := 4983230072969 + 3 ^ 40 * 763122 * 2
def baseEnd_763122 : Nat := 19350537482492272363727

theorem tailTrace_763122 : CollatzResearch.WordTrace tailWord_763122 prefixEnd_763122 19350537482492272363727 := by
  unfold tailWord_763122
  simp only [CollatzResearch.WordTrace]
  refine ⟨6958336485336699926634905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18555563960897866471026413 6958336485336699926634905)
  ·
    refine ⟨5218752364002524944976179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6958336485336699926634905 5218752364002524944976179)
    ·
      refine ⟨7828128546003787417464269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5218752364002524944976179 7828128546003787417464269)
      ·
        refine ⟨2935548204751420281549101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7828128546003787417464269 2935548204751420281549101)
        ·
          refine ⟨1100830576781782605580913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2935548204751420281549101 1100830576781782605580913)
          ·
            refine ⟨825622932586336954185685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1100830576781782605580913 825622932586336954185685)
            ·
              refine ⟨19350537482492272363727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 825622932586336954185685 19350537482492272363727)
              ·
                rfl

theorem cell21_763122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 7].length) (baseStart_763122 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_763122 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_763122 prefixEnd_763122 := by exact prefixLift 763122
  have htrace : WordTrace (prefixWord ++ tailWord_763122) baseStart_763122 baseEnd_763122 := by
    simpa [prefixWord, tailWord_763122, baseEnd_763122] using wordTrace_append hprefix tailTrace_763122
  have hstable : (prefixWord ++ tailWord_763122).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763122).length < 2 ^ (prefixWord ++ tailWord_763122).sum := by decide
  have hdescent : baseEnd_763122 < baseStart_763122 := by decide
  rcases family_descends (prefixWord ++ tailWord_763122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763212 : List Nat := [2, 2, 1, 3, 2, 3, 1, 2, 5]
def baseStart_763212 : Nat := 118140960795 + 763212 * 2 ^ 59
def prefixEnd_763212 : Nat := 4983230072969 + 3 ^ 40 * 763212 * 2
def baseEnd_763212 : Nat := 174175376568610294773359

theorem tailTrace_763212 : CollatzResearch.WordTrace tailWord_763212 prefixEnd_763212 174175376568610294773359 := by
  unfold tailWord_763212
  simp only [CollatzResearch.WordTrace]
  refine ⟨13918314255510372538657945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18557752340680496718210593 13918314255510372538657945)
  ·
    refine ⟨10438735691632779403993459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13918314255510372538657945 10438735691632779403993459)
    ·
      refine ⟨15658103537449169105990189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10438735691632779403993459 15658103537449169105990189)
      ·
        refine ⟨5871788826543438414746321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15658103537449169105990189 5871788826543438414746321)
        ·
          refine ⟨4403841619907578811059741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5871788826543438414746321 4403841619907578811059741)
          ·
            refine ⟨1651440607465342054147403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4403841619907578811059741 1651440607465342054147403)
            ·
              refine ⟨2477160911198013081221105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1651440607465342054147403 2477160911198013081221105)
              ·
                refine ⟨1857870683398509810915829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2477160911198013081221105 1857870683398509810915829)
                ·
                  refine ⟨174175376568610294773359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1857870683398509810915829 174175376568610294773359)
                  ·
                    rfl

theorem cell21_763212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 2, 5].length) (baseStart_763212 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_763212 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_763212 prefixEnd_763212 := by exact prefixLift 763212
  have htrace : WordTrace (prefixWord ++ tailWord_763212) baseStart_763212 baseEnd_763212 := by
    simpa [prefixWord, tailWord_763212, baseEnd_763212] using wordTrace_append hprefix tailTrace_763212
  have hstable : (prefixWord ++ tailWord_763212).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763212).length < 2 ^ (prefixWord ++ tailWord_763212).sum := by decide
  have hdescent : baseEnd_763212 < baseStart_763212 := by decide
  rcases family_descends (prefixWord ++ tailWord_763212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763246 : List Nat := [4, 1, 2, 4, 1, 1, 2, 1, 5]
def baseStart_763246 : Nat := 118140960795 + 763246 * 2 ^ 59
def prefixEnd_763246 : Nat := 4983230072969 + 3 ^ 40 * 763246 * 2
def baseEnd_763246 : Nat := 174183135831833791206623

theorem tailTrace_763246 : CollatzResearch.WordTrace tailWord_763246 prefixEnd_763246 174183135831833791206623 := by
  unfold tailWord_763246
  simp only [CollatzResearch.WordTrace]
  refine ⟨3479733574112196110506699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18558579061931712589369061 3479733574112196110506699)
  ·
    refine ⟨5219600361168294165760049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3479733574112196110506699 5219600361168294165760049)
    ·
      refine ⟨3914700270876220624320037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5219600361168294165760049 3914700270876220624320037)
      ·
        refine ⟨734006300789291367060007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3914700270876220624320037 734006300789291367060007)
        ·
          refine ⟨1101009451183937050590011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 734006300789291367060007 1101009451183937050590011)
          ·
            refine ⟨1651514176775905575885017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1101009451183937050590011 1651514176775905575885017)
            ·
              refine ⟨1238635632581929181913763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1651514176775905575885017 1238635632581929181913763)
              ·
                refine ⟨1857953448872893772870645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1238635632581929181913763 1857953448872893772870645)
                ·
                  refine ⟨174183135831833791206623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1857953448872893772870645 174183135831833791206623)
                  ·
                    rfl

theorem cell21_763246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 2, 1, 5].length) (baseStart_763246 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_763246 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_763246 prefixEnd_763246 := by exact prefixLift 763246
  have htrace : WordTrace (prefixWord ++ tailWord_763246) baseStart_763246 baseEnd_763246 := by
    simpa [prefixWord, tailWord_763246, baseEnd_763246] using wordTrace_append hprefix tailTrace_763246
  have hstable : (prefixWord ++ tailWord_763246).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763246).length < 2 ^ (prefixWord ++ tailWord_763246).sum := by decide
  have hdescent : baseEnd_763246 < baseStart_763246 := by decide
  rcases family_descends (prefixWord ++ tailWord_763246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763381 : List Nat := [1, 3, 5, 1, 1, 2, 1, 2, 5]
def baseStart_763381 : Nat := 118140960795 + 763381 * 2 ^ 59
def prefixEnd_763381 : Nat := 4983230072969 + 3 ^ 40 * 763381 * 2
def baseEnd_763381 : Nat := 174213944671103556456347

theorem tailTrace_763381 : CollatzResearch.WordTrace tailWord_763381 prefixEnd_763381 174213944671103556456347 := by
  unfold tailWord_763381
  simp only [CollatzResearch.WordTrace]
  refine ⟨27842792447408486940217997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18561861631605657960145331 27842792447408486940217997)
  ·
    refine ⟨10441047167778182602581749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27842792447408486940217997 10441047167778182602581749)
    ·
      refine ⟨978848171979204618992039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10441047167778182602581749 978848171979204618992039)
      ·
        refine ⟨1468272257968806928488059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 978848171979204618992039 1468272257968806928488059)
        ·
          refine ⟨2202408386953210392732089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1468272257968806928488059 2202408386953210392732089)
          ·
            refine ⟨1651806290214907794549067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2202408386953210392732089 1651806290214907794549067)
            ·
              refine ⟨2477709435322361691823601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1651806290214907794549067 2477709435322361691823601)
              ·
                refine ⟨1858282076491771268867701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2477709435322361691823601 1858282076491771268867701)
                ·
                  refine ⟨174213944671103556456347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1858282076491771268867701 174213944671103556456347)
                  ·
                    rfl

theorem cell21_763381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 2, 5].length) (baseStart_763381 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_763381 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_763381 prefixEnd_763381 := by exact prefixLift 763381
  have htrace : WordTrace (prefixWord ++ tailWord_763381) baseStart_763381 baseEnd_763381 := by
    simpa [prefixWord, tailWord_763381, baseEnd_763381] using wordTrace_append hprefix tailTrace_763381
  have hstable : (prefixWord ++ tailWord_763381).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763381).length < 2 ^ (prefixWord ++ tailWord_763381).sum := by decide
  have hdescent : baseEnd_763381 < baseStart_763381 := by decide
  rcases family_descends (prefixWord ++ tailWord_763381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763412 : List Nat := [2, 4, 3, 1, 2, 1, 1, 1, 6]
def baseStart_763412 : Nat := 118140960795 + 763412 * 2 ^ 59
def prefixEnd_763412 : Nat := 4983230072969 + 3 ^ 40 * 763412 * 2
def baseEnd_763412 : Nat := 174221019293454391439617

theorem tailTrace_763412 : CollatzResearch.WordTrace tailWord_763412 prefixEnd_763412 174221019293454391439617 := by
  unfold tailWord_763412
  simp only [CollatzResearch.WordTrace]
  refine ⟨13921961555148089617298245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18562615406864119489730993 13921961555148089617298245)
  ·
    refine ⟨2610367791590266803243421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13921961555148089617298245 2610367791590266803243421)
    ·
      refine ⟨978887921846350051216283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2610367791590266803243421 978887921846350051216283)
      ·
        refine ⟨1468331882769525076824425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 978887921846350051216283 1468331882769525076824425)
        ·
          refine ⟨1101248912077143807618319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1468331882769525076824425 1101248912077143807618319)
          ·
            refine ⟨1651873368115715711427479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1101248912077143807618319 1651873368115715711427479)
            ·
              refine ⟨2477810052173573567141219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1651873368115715711427479 2477810052173573567141219)
              ·
                refine ⟨3716715078260360350711829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2477810052173573567141219 3716715078260360350711829)
                ·
                  refine ⟨174221019293454391439617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3716715078260360350711829 174221019293454391439617)
                  ·
                    rfl

theorem cell21_763412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 1, 6].length) (baseStart_763412 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_763412 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_763412 prefixEnd_763412 := by exact prefixLift 763412
  have htrace : WordTrace (prefixWord ++ tailWord_763412) baseStart_763412 baseEnd_763412 := by
    simpa [prefixWord, tailWord_763412, baseEnd_763412] using wordTrace_append hprefix tailTrace_763412
  have hstable : (prefixWord ++ tailWord_763412).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763412).length < 2 ^ (prefixWord ++ tailWord_763412).sum := by decide
  have hdescent : baseEnd_763412 < baseStart_763412 := by decide
  rcases family_descends (prefixWord ++ tailWord_763412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763423 : List Nat := [1, 1, 2, 4, 1, 1, 3, 3, 5]
def baseStart_763423 : Nat := 118140960795 + 763423 * 2 ^ 59
def prefixEnd_763423 : Nat := 4983230072969 + 3 ^ 40 * 763423 * 2
def baseEnd_763423 : Nat := 174223529643320816756261

theorem tailTrace_763423 : CollatzResearch.WordTrace tailWord_763423 prefixEnd_763423 174223529643320816756261 := by
  unfold tailWord_763423
  simp only [CollatzResearch.WordTrace]
  refine ⟨27844324313256328113246923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18562882875504218742164615 27844324313256328113246923)
  ·
    refine ⟨41766486469884492169870385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27844324313256328113246923 41766486469884492169870385)
    ·
      refine ⟨31324864852413369127402789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41766486469884492169870385 31324864852413369127402789)
      ·
        refine ⟨5873412159827506711388023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31324864852413369127402789 5873412159827506711388023)
        ·
          refine ⟨8810118239741260067082035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5873412159827506711388023 8810118239741260067082035)
          ·
            refine ⟨13215177359611890100623053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8810118239741260067082035 13215177359611890100623053)
            ·
              refine ⟨4955691509854458787733645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13215177359611890100623053 4955691509854458787733645)
              ·
                refine ⟨1858384316195422045400117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4955691509854458787733645 1858384316195422045400117)
                ·
                  refine ⟨174223529643320816756261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1858384316195422045400117 174223529643320816756261)
                  ·
                    rfl

theorem cell21_763423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 3, 5].length) (baseStart_763423 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_763423 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_763423 prefixEnd_763423 := by exact prefixLift 763423
  have htrace : WordTrace (prefixWord ++ tailWord_763423) baseStart_763423 baseEnd_763423 := by
    simpa [prefixWord, tailWord_763423, baseEnd_763423] using wordTrace_append hprefix tailTrace_763423
  have hstable : (prefixWord ++ tailWord_763423).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763423).length < 2 ^ (prefixWord ++ tailWord_763423).sum := by decide
  have hdescent : baseEnd_763423 < baseStart_763423 := by decide
  rcases family_descends (prefixWord ++ tailWord_763423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763468 : List Nat := [2, 2, 1, 3, 1, 3, 9]
def baseStart_763468 : Nat := 118140960795 + 763468 * 2 ^ 59
def prefixEnd_763468 : Nat := 4983230072969 + 3 ^ 40 * 763468 * 2
def baseEnd_763468 : Nat := 19359311028490082056241

theorem tailTrace_763468 : CollatzResearch.WordTrace tailWord_763468 prefixEnd_763468 19359311028490082056241 := by
  unfold tailWord_763468
  simp only [CollatzResearch.WordTrace]
  refine ⟨13922982799046650399317529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18563977065395533865756705 13922982799046650399317529)
  ·
    refine ⟨10442237099284987799488147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13922982799046650399317529 10442237099284987799488147)
    ·
      refine ⟨15663355648927481699232221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10442237099284987799488147 15663355648927481699232221)
      ·
        refine ⟨5873758368347805637212083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15663355648927481699232221 5873758368347805637212083)
        ·
          refine ⟨8810637552521708455818125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5873758368347805637212083 8810637552521708455818125)
          ·
            refine ⟨3303989082195640670931797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8810637552521708455818125 3303989082195640670931797)
            ·
              refine ⟨19359311028490082056241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3303989082195640670931797 19359311028490082056241)
              ·
                rfl

theorem cell21_763468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 9].length) (baseStart_763468 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_763468 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_763468 prefixEnd_763468 := by exact prefixLift 763468
  have htrace : WordTrace (prefixWord ++ tailWord_763468) baseStart_763468 baseEnd_763468 := by
    simpa [prefixWord, tailWord_763468, baseEnd_763468] using wordTrace_append hprefix tailTrace_763468
  have hstable : (prefixWord ++ tailWord_763468).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763468).length < 2 ^ (prefixWord ++ tailWord_763468).sum := by decide
  have hdescent : baseEnd_763468 < baseStart_763468 := by decide
  rcases family_descends (prefixWord ++ tailWord_763468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763474 : List Nat := [3, 2, 2, 1, 2, 3, 3, 2, 3]
def baseStart_763474 : Nat := 118140960795 + 763474 * 2 ^ 59
def prefixEnd_763474 : Nat := 4983230072969 + 3 ^ 40 * 763474 * 2
def baseEnd_763474 : Nat := 174235168538156061406157

theorem tailTrace_763474 : CollatzResearch.WordTrace tailWord_763474 prefixEnd_763474 174235168538156061406157 := by
  unfold tailWord_763474
  simp only [CollatzResearch.WordTrace]
  refine ⟨6961546109017890955838369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18564122957381042548902317 6961546109017890955838369)
  ·
    refine ⟨5221159581763418216878777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6961546109017890955838369 5221159581763418216878777)
    ·
      refine ⟨3915869686322563662659083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5221159581763418216878777 3915869686322563662659083)
      ·
        refine ⟨5873804529483845493988625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3915869686322563662659083 5873804529483845493988625)
        ·
          refine ⟨4405353397112884120491469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5873804529483845493988625 4405353397112884120491469)
          ·
            refine ⟨1652007523917331545184301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4405353397112884120491469 1652007523917331545184301)
            ·
              refine ⟨619502821468999329444113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1652007523917331545184301 619502821468999329444113)
              ·
                refine ⟨464627116101749497083085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 619502821468999329444113 464627116101749497083085)
                ·
                  refine ⟨174235168538156061406157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 464627116101749497083085 174235168538156061406157)
                  ·
                    rfl

theorem cell21_763474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 3, 2, 3].length) (baseStart_763474 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_763474 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_763474 prefixEnd_763474 := by exact prefixLift 763474
  have htrace : WordTrace (prefixWord ++ tailWord_763474) baseStart_763474 baseEnd_763474 := by
    simpa [prefixWord, tailWord_763474, baseEnd_763474] using wordTrace_append hprefix tailTrace_763474
  have hstable : (prefixWord ++ tailWord_763474).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763474).length < 2 ^ (prefixWord ++ tailWord_763474).sum := by decide
  have hdescent : baseEnd_763474 < baseStart_763474 := by decide
  rcases family_descends (prefixWord ++ tailWord_763474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763516 : List Nat := [2, 2, 2, 1, 1, 2, 1, 7, 3]
def baseStart_763516 : Nat := 118140960795 + 763516 * 2 ^ 59
def prefixEnd_763516 : Nat := 4983230072969 + 3 ^ 40 * 763516 * 2
def baseEnd_763516 : Nat := 174244753510373321706071

theorem tailTrace_763516 : CollatzResearch.WordTrace tailWord_763516 prefixEnd_763516 174244753510373321706071 := by
  unfold tailWord_763516
  simp only [CollatzResearch.WordTrace]
  refine ⟨13923858150959702498191201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18565144201279603330921601 13923858150959702498191201)
  ·
    refine ⟨10442893613219776873643401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13923858150959702498191201 10442893613219776873643401)
    ·
      refine ⟨7832170209914832655232551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10442893613219776873643401 7832170209914832655232551)
      ·
        refine ⟨11748255314872248982848827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7832170209914832655232551 11748255314872248982848827)
        ·
          refine ⟨17622382972308373474273241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11748255314872248982848827 17622382972308373474273241)
          ·
            refine ⟨13216787229231280105704931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17622382972308373474273241 13216787229231280105704931)
            ·
              refine ⟨19825180843846920158557397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13216787229231280105704931 19825180843846920158557397)
              ·
                refine ⟨464652676027662191216189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 19825180843846920158557397 464652676027662191216189)
                ·
                  refine ⟨174244753510373321706071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 464652676027662191216189 174244753510373321706071)
                  ·
                    rfl

theorem cell21_763516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 7, 3].length) (baseStart_763516 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_763516 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_763516 prefixEnd_763516 := by exact prefixLift 763516
  have htrace : WordTrace (prefixWord ++ tailWord_763516) baseStart_763516 baseEnd_763516 := by
    simpa [prefixWord, tailWord_763516, baseEnd_763516] using wordTrace_append hprefix tailTrace_763516
  have hstable : (prefixWord ++ tailWord_763516).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763516).length < 2 ^ (prefixWord ++ tailWord_763516).sum := by decide
  have hdescent : baseEnd_763516 < baseStart_763516 := by decide
  rcases family_descends (prefixWord ++ tailWord_763516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763589 : List Nat := [1, 3, 1, 1, 1, 1, 2, 5, 6]
def baseStart_763589 : Nat := 118140960795 + 763589 * 2 ^ 59
def prefixEnd_763589 : Nat := 4983230072969 + 3 ^ 40 * 763589 * 2
def baseEnd_763589 : Nat := 174261413104941416989255

theorem tailTrace_763589 : CollatzResearch.WordTrace tailWord_763589 prefixEnd_763589 174261413104941416989255 := by
  unfold tailWord_763589
  simp only [CollatzResearch.WordTrace]
  refine ⟨27850378830654938463789821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18566919220436625642526547 27850378830654938463789821)
  ·
    refine ⟨10443892061495601923921183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27850378830654938463789821 10443892061495601923921183)
    ·
      refine ⟨15665838092243402885881775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10443892061495601923921183 15665838092243402885881775)
      ·
        refine ⟨23498757138365104328822663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15665838092243402885881775 23498757138365104328822663)
        ·
          refine ⟨35248135707547656493233995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23498757138365104328822663 35248135707547656493233995)
          ·
            refine ⟨52872203561321484739850993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35248135707547656493233995 52872203561321484739850993)
            ·
              refine ⟨39654152670991113554888245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52872203561321484739850993 39654152670991113554888245)
              ·
                refine ⟨3717576812905416895770773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39654152670991113554888245 3717576812905416895770773)
                ·
                  refine ⟨174261413104941416989255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3717576812905416895770773 174261413104941416989255)
                  ·
                    rfl

theorem cell21_763589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 5, 6].length) (baseStart_763589 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_763589 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_763589 prefixEnd_763589 := by exact prefixLift 763589
  have htrace : WordTrace (prefixWord ++ tailWord_763589) baseStart_763589 baseEnd_763589 := by
    simpa [prefixWord, tailWord_763589, baseEnd_763589] using wordTrace_append hprefix tailTrace_763589
  have hstable : (prefixWord ++ tailWord_763589).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763589).length < 2 ^ (prefixWord ++ tailWord_763589).sum := by decide
  have hdescent : baseEnd_763589 < baseStart_763589 := by decide
  rcases family_descends (prefixWord ++ tailWord_763589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763592 : List Nat := [2, 1, 3, 1, 2, 2, 1, 6, 3]
def baseStart_763592 : Nat := 118140960795 + 763592 * 2 ^ 59
def prefixEnd_763592 : Nat := 4983230072969 + 3 ^ 40 * 763592 * 2
def baseEnd_763592 : Nat := 174262097745814078439249

theorem tailTrace_763592 : CollatzResearch.WordTrace tailWord_763592 prefixEnd_763592 174262097745814078439249 := by
  unfold tailWord_763592
  simp only [CollatzResearch.WordTrace]
  refine ⟨13925244124822034988074515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18566992166429379984099353 13925244124822034988074515)
  ·
    refine ⟨20887866187233052482111773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13925244124822034988074515 20887866187233052482111773)
    ·
      refine ⟨7832949820212394680791915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20887866187233052482111773 7832949820212394680791915)
      ·
        refine ⟨11749424730318592021187873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7832949820212394680791915 11749424730318592021187873)
        ·
          refine ⟨8812068547738944015890905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11749424730318592021187873 8812068547738944015890905)
          ·
            refine ⟨6609051410804208011918179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8812068547738944015890905 6609051410804208011918179)
            ·
              refine ⟨9913577116206312017877269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6609051410804208011918179 9913577116206312017877269)
              ·
                refine ⟨464698927322170875837997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9913577116206312017877269 464698927322170875837997)
                ·
                  refine ⟨174262097745814078439249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 464698927322170875837997 174262097745814078439249)
                  ·
                    rfl

theorem cell21_763592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 6, 3].length) (baseStart_763592 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_763592 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_763592 prefixEnd_763592 := by exact prefixLift 763592
  have htrace : WordTrace (prefixWord ++ tailWord_763592) baseStart_763592 baseEnd_763592 := by
    simpa [prefixWord, tailWord_763592, baseEnd_763592] using wordTrace_append hprefix tailTrace_763592
  have hstable : (prefixWord ++ tailWord_763592).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763592).length < 2 ^ (prefixWord ++ tailWord_763592).sum := by decide
  have hdescent : baseEnd_763592 < baseStart_763592 := by decide
  rcases family_descends (prefixWord ++ tailWord_763592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763612 : List Nat := [2, 2, 5, 1, 3, 1, 2, 5]
def baseStart_763612 : Nat := 118140960795 + 763612 * 2 ^ 59
def prefixEnd_763612 : Nat := 4983230072969 + 3 ^ 40 * 763612 * 2
def baseEnd_763612 : Nat := 58088887339432829368625

theorem tailTrace_763612 : CollatzResearch.WordTrace tailWord_763612 prefixEnd_763612 58088887339432829368625 := by
  unfold tailWord_763612
  simp only [CollatzResearch.WordTrace]
  refine ⟨13925608854785806695938545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18567478473047742261251393 13925608854785806695938545)
  ·
    refine ⟨10444206641089355021953909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13925608854785806695938545 10444206641089355021953909)
    ·
      refine ⟨979144372602127033308179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10444206641089355021953909 979144372602127033308179)
      ·
        refine ⟨1468716558903190549962269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 979144372602127033308179 1468716558903190549962269)
        ·
          refine ⟨550768709588696456235851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1468716558903190549962269 550768709588696456235851)
          ·
            refine ⟨826153064383044684353777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 550768709588696456235851 826153064383044684353777)
            ·
              refine ⟨619614798287283513265333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 826153064383044684353777 619614798287283513265333)
              ·
                refine ⟨58088887339432829368625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 619614798287283513265333 58088887339432829368625)
                ·
                  rfl

theorem cell21_763612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 2, 5].length) (baseStart_763612 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_763612 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_763612 prefixEnd_763612 := by exact prefixLift 763612
  have htrace : WordTrace (prefixWord ++ tailWord_763612) baseStart_763612 baseEnd_763612 := by
    simpa [prefixWord, tailWord_763612, baseEnd_763612] using wordTrace_append hprefix tailTrace_763612
  have hstable : (prefixWord ++ tailWord_763612).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763612).length < 2 ^ (prefixWord ++ tailWord_763612).sum := by decide
  have hdescent : baseEnd_763612 < baseStart_763612 := by decide
  rcases family_descends (prefixWord ++ tailWord_763612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763620 : List Nat := [2, 3, 1, 1, 1, 3, 3, 7]
def baseStart_763620 : Nat := 118140960795 + 763620 * 2 ^ 59
def prefixEnd_763620 : Nat := 4983230072969 + 3 ^ 40 * 763620 * 2
def baseEnd_763620 : Nat := 58089495909097417324175

theorem tailTrace_763620 : CollatzResearch.WordTrace tailWord_763620 prefixEnd_763620 58089495909097417324175 := by
  unfold tailWord_763620
  simp only [CollatzResearch.WordTrace]
  refine ⟨13925754746771315379084157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18567672995695087172112209 13925754746771315379084157)
  ·
    refine ⟨5222158030039243267156559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13925754746771315379084157 5222158030039243267156559)
    ·
      refine ⟨7833237045058864900734839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5222158030039243267156559 7833237045058864900734839)
      ·
        refine ⟨11749855567588297351102259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7833237045058864900734839 11749855567588297351102259)
        ·
          refine ⟨17624783351382446026653389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11749855567588297351102259 17624783351382446026653389)
          ·
            refine ⟨6609293756768417259995021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17624783351382446026653389 6609293756768417259995021)
            ·
              refine ⟨2478485158788156472498133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6609293756768417259995021 2478485158788156472498133)
              ·
                refine ⟨58089495909097417324175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2478485158788156472498133 58089495909097417324175)
                ·
                  rfl

theorem cell21_763620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 7].length) (baseStart_763620 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_763620 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_763620 prefixEnd_763620 := by exact prefixLift 763620
  have htrace : WordTrace (prefixWord ++ tailWord_763620) baseStart_763620 baseEnd_763620 := by
    simpa [prefixWord, tailWord_763620, baseEnd_763620] using wordTrace_append hprefix tailTrace_763620
  have hstable : (prefixWord ++ tailWord_763620).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763620).length < 2 ^ (prefixWord ++ tailWord_763620).sum := by decide
  have hdescent : baseEnd_763620 < baseStart_763620 := by decide
  rcases family_descends (prefixWord ++ tailWord_763620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763651 : List Nat := [1, 1, 1, 3, 2, 2, 5, 1, 5]
def baseStart_763651 : Nat := 118140960795 + 763651 * 2 ^ 59
def prefixEnd_763651 : Nat := 4983230072969 + 3 ^ 40 * 763651 * 2
def baseEnd_763651 : Nat := 174275562349643086955795

theorem tailTrace_763651 : CollatzResearch.WordTrace tailWord_763651 prefixEnd_763651 174275562349643086955795 := by
  unfold tailWord_763651
  simp only [CollatzResearch.WordTrace]
  refine ⟨27852640156430323052546807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18568426770953548701697871 27852640156430323052546807)
  ·
    refine ⟨41778960234645484578820211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27852640156430323052546807 41778960234645484578820211)
    ·
      refine ⟨62668440351968226868230317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41778960234645484578820211 62668440351968226868230317)
      ·
        refine ⟨23500665131988085075586369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62668440351968226868230317 23500665131988085075586369)
        ·
          refine ⟨17625498848991063806689777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23500665131988085075586369 17625498848991063806689777)
          ·
            refine ⟨13219124136743297855017333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17625498848991063806689777 13219124136743297855017333)
            ·
              refine ⟨1239292887819684173907875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13219124136743297855017333 1239292887819684173907875)
              ·
                refine ⟨1858939331729526260861813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1239292887819684173907875 1858939331729526260861813)
                ·
                  refine ⟨174275562349643086955795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1858939331729526260861813 174275562349643086955795)
                  ·
                    rfl

theorem cell21_763651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5, 1, 5].length) (baseStart_763651 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_763651 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_763651 prefixEnd_763651 := by exact prefixLift 763651
  have htrace : WordTrace (prefixWord ++ tailWord_763651) baseStart_763651 baseEnd_763651 := by
    simpa [prefixWord, tailWord_763651, baseEnd_763651] using wordTrace_append hprefix tailTrace_763651
  have hstable : (prefixWord ++ tailWord_763651).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763651).length < 2 ^ (prefixWord ++ tailWord_763651).sum := by decide
  have hdescent : baseEnd_763651 < baseStart_763651 := by decide
  rcases family_descends (prefixWord ++ tailWord_763651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763699 : List Nat := [1, 1, 1, 2, 7, 1, 2, 2, 4]
def baseStart_763699 : Nat := 118140960795 + 763699 * 2 ^ 59
def prefixEnd_763699 : Nat := 4983230072969 + 3 ^ 40 * 763699 * 2
def baseEnd_763699 : Nat := 174286516603605670155697

theorem tailTrace_763699 : CollatzResearch.WordTrace tailWord_763699 prefixEnd_763699 174286516603605670155697 := by
  unfold tailWord_763699
  simp only [CollatzResearch.WordTrace]
  refine ⟨27854390860256427250294151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18569593906837618166862767 27854390860256427250294151)
  ·
    refine ⟨41781586290384640875441227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27854390860256427250294151 41781586290384640875441227)
    ·
      refine ⟨62672379435576961313161841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41781586290384640875441227 62672379435576961313161841)
      ·
        refine ⟨47004284576682720984871381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62672379435576961313161841 47004284576682720984871381)
        ·
          refine ⟨1101662919766001273082923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 47004284576682720984871381 1101662919766001273082923)
          ·
            refine ⟨1652494379649001909624385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1101662919766001273082923 1652494379649001909624385)
            ·
              refine ⟨1239370784736751432218289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1652494379649001909624385 1239370784736751432218289)
              ·
                refine ⟨929528088552563574163717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1239370784736751432218289 929528088552563574163717)
                ·
                  refine ⟨174286516603605670155697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 929528088552563574163717 174286516603605670155697)
                  ·
                    rfl

theorem cell21_763699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 2, 2, 4].length) (baseStart_763699 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_763699 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_763699 prefixEnd_763699 := by exact prefixLift 763699
  have htrace : WordTrace (prefixWord ++ tailWord_763699) baseStart_763699 baseEnd_763699 := by
    simpa [prefixWord, tailWord_763699, baseEnd_763699] using wordTrace_append hprefix tailTrace_763699
  have hstable : (prefixWord ++ tailWord_763699).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763699).length < 2 ^ (prefixWord ++ tailWord_763699).sum := by decide
  have hdescent : baseEnd_763699 < baseStart_763699 := by decide
  rcases family_descends (prefixWord ++ tailWord_763699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763702 : List Nat := [5, 1, 2, 2, 1, 2, 1, 4, 3]
def baseStart_763702 : Nat := 118140960795 + 763702 * 2 ^ 59
def prefixEnd_763702 : Nat := 4983230072969 + 3 ^ 40 * 763702 * 2
def baseEnd_763702 : Nat := 174287201244478331605691

theorem tailTrace_763702 : CollatzResearch.WordTrace tailWord_763702 prefixEnd_763702 174287201244478331605691 := by
  unfold tailWord_763702
  simp only [CollatzResearch.WordTrace]
  refine ⟨1740906267452847422665835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18569666852830372508435573 1740906267452847422665835)
  ·
    refine ⟨2611359401179271133998753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1740906267452847422665835 2611359401179271133998753)
    ·
      refine ⟨1958519550884453350499065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2611359401179271133998753 1958519550884453350499065)
      ·
        refine ⟨1468889663163340012874299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1958519550884453350499065 1468889663163340012874299)
        ·
          refine ⟨2203334494745010019311449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1468889663163340012874299 2203334494745010019311449)
          ·
            refine ⟨1652500871058757514483587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2203334494745010019311449 1652500871058757514483587)
            ·
              refine ⟨2478751306588136271725381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1652500871058757514483587 2478751306588136271725381)
              ·
                refine ⟨464765869985275550948509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2478751306588136271725381 464765869985275550948509)
                ·
                  refine ⟨174287201244478331605691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 464765869985275550948509 174287201244478331605691)
                  ·
                    rfl

theorem cell21_763702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 4, 3].length) (baseStart_763702 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_763702 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_763702 prefixEnd_763702 := by exact prefixLift 763702
  have htrace : WordTrace (prefixWord ++ tailWord_763702) baseStart_763702 baseEnd_763702 := by
    simpa [prefixWord, tailWord_763702, baseEnd_763702] using wordTrace_append hprefix tailTrace_763702
  have hstable : (prefixWord ++ tailWord_763702).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763702).length < 2 ^ (prefixWord ++ tailWord_763702).sum := by decide
  have hdescent : baseEnd_763702 < baseStart_763702 := by decide
  rcases family_descends (prefixWord ++ tailWord_763702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763744 : List Nat := [2, 1, 1, 3, 3, 2, 1, 5, 3]
def baseStart_763744 : Nat := 118140960795 + 763744 * 2 ^ 59
def prefixEnd_763744 : Nat := 4983230072969 + 3 ^ 40 * 763744 * 2
def baseEnd_763744 : Nat := 174296786216695591905605

theorem tailTrace_763744 : CollatzResearch.WordTrace tailWord_763744 prefixEnd_763744 174296786216695591905605 := by
  unfold tailWord_763744
  simp only [CollatzResearch.WordTrace]
  refine ⟨13928016072546699967841143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18570688096728933290454857 13928016072546699967841143)
  ·
    refine ⟨20892024108820049951761715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13928016072546699967841143 20892024108820049951761715)
    ·
      refine ⟨31338036163230074927642573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20892024108820049951761715 31338036163230074927642573)
      ·
        refine ⟨11751763561211278097865965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31338036163230074927642573 11751763561211278097865965)
        ·
          refine ⟨4406911335454229286699737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11751763561211278097865965 4406911335454229286699737)
          ·
            refine ⟨3305183501590671965024803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4406911335454229286699737 3305183501590671965024803)
            ·
              refine ⟨4957775252386007947537205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3305183501590671965024803 4957775252386007947537205)
              ·
                refine ⟨464791429911188245081613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4957775252386007947537205 464791429911188245081613)
                ·
                  refine ⟨174296786216695591905605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 464791429911188245081613 174296786216695591905605)
                  ·
                    rfl

theorem cell21_763744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 5, 3].length) (baseStart_763744 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_763744 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_763744 prefixEnd_763744 := by exact prefixLift 763744
  have htrace : WordTrace (prefixWord ++ tailWord_763744) baseStart_763744 baseEnd_763744 := by
    simpa [prefixWord, tailWord_763744, baseEnd_763744] using wordTrace_append hprefix tailTrace_763744
  have hstable : (prefixWord ++ tailWord_763744).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763744).length < 2 ^ (prefixWord ++ tailWord_763744).sum := by decide
  have hdescent : baseEnd_763744 < baseStart_763744 := by decide
  rcases family_descends (prefixWord ++ tailWord_763744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763848 : List Nat := [2, 1, 3, 1, 4, 1, 2, 7]
def baseStart_763848 : Nat := 118140960795 + 763848 * 2 ^ 59
def prefixEnd_763848 : Nat := 4983230072969 + 3 ^ 40 * 763848 * 2
def baseEnd_763848 : Nat := 58106840144538174057353

theorem tailTrace_763848 : CollatzResearch.WordTrace tailWord_763848 prefixEnd_763848 58106840144538174057353 := by
  unfold tailWord_763848
  simp only [CollatzResearch.WordTrace]
  refine ⟨13929912668358312848734099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18573216891144417131645465 13929912668358312848734099)
  ·
    refine ⟨20894869002537469273101149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13929912668358312848734099 20894869002537469273101149)
    ·
      refine ⟨7835575875951550977412931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20894869002537469273101149 7835575875951550977412931)
      ·
        refine ⟨11753363813927326466119397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7835575875951550977412931 11753363813927326466119397)
        ·
          refine ⟨2203755715111373712397387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11753363813927326466119397 2203755715111373712397387)
          ·
            refine ⟨3305633572667060568596081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2203755715111373712397387 3305633572667060568596081)
            ·
              refine ⟨2479225179500295426447061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3305633572667060568596081 2479225179500295426447061)
              ·
                refine ⟨58106840144538174057353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2479225179500295426447061 58106840144538174057353)
                ·
                  rfl

theorem cell21_763848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 7].length) (baseStart_763848 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_763848 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_763848 prefixEnd_763848 := by exact prefixLift 763848
  have htrace : WordTrace (prefixWord ++ tailWord_763848) baseStart_763848 baseEnd_763848 := by
    simpa [prefixWord, tailWord_763848, baseEnd_763848] using wordTrace_append hprefix tailTrace_763848
  have hstable : (prefixWord ++ tailWord_763848).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763848).length < 2 ^ (prefixWord ++ tailWord_763848).sum := by decide
  have hdescent : baseEnd_763848 < baseStart_763848 := by decide
  rcases family_descends (prefixWord ++ tailWord_763848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763907 : List Nat := [1, 1, 1, 3, 2, 1, 1, 11]
def baseStart_763907 : Nat := 118140960795 + 763907 * 2 ^ 59
def prefixEnd_763907 : Nat := 4983230072969 + 3 ^ 40 * 763907 * 2
def baseEnd_763907 : Nat := 58111328345814510229535

theorem tailTrace_763907 : CollatzResearch.WordTrace tailWord_763907 prefixEnd_763907 58111328345814510229535 := by
  unfold tailWord_763907
  simp only [CollatzResearch.WordTrace]
  refine ⟨27861977243502878773865975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18574651495668585849243983 27861977243502878773865975)
  ·
    refine ⟨41792965865254318160798963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27861977243502878773865975 41792965865254318160798963)
    ·
      refine ⟨62689448797881477241198445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41792965865254318160798963 62689448797881477241198445)
      ·
        refine ⟨23508543299205553965449417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62689448797881477241198445 23508543299205553965449417)
        ·
          refine ⟨17631407474404165474087063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23508543299205553965449417 17631407474404165474087063)
          ·
            refine ⟨26447111211606248211130595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17631407474404165474087063 26447111211606248211130595)
            ·
              refine ⟨39670666817409372316695893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26447111211606248211130595 39670666817409372316695893)
              ·
                refine ⟨58111328345814510229535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 39670666817409372316695893 58111328345814510229535)
                ·
                  rfl

theorem cell21_763907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 11].length) (baseStart_763907 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_763907 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_763907 prefixEnd_763907 := by exact prefixLift 763907
  have htrace : WordTrace (prefixWord ++ tailWord_763907) baseStart_763907 baseEnd_763907 := by
    simpa [prefixWord, tailWord_763907, baseEnd_763907] using wordTrace_append hprefix tailTrace_763907
  have hstable : (prefixWord ++ tailWord_763907).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763907).length < 2 ^ (prefixWord ++ tailWord_763907).sum := by decide
  have hdescent : baseEnd_763907 < baseStart_763907 := by decide
  rcases family_descends (prefixWord ++ tailWord_763907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763989 : List Nat := [1, 3, 2, 2, 1, 4, 3, 2, 3]
def baseStart_763989 : Nat := 118140960795 + 763989 * 2 ^ 59
def prefixEnd_763989 : Nat := 4983230072969 + 3 ^ 40 * 763989 * 2
def baseEnd_763989 : Nat := 174352698554629610321771

theorem tailTrace_763989 : CollatzResearch.WordTrace tailWord_763989 prefixEnd_763989 174352698554629610321771 := by
  unfold tailWord_763989
  simp only [CollatzResearch.WordTrace]
  refine ⟨27864968029205806778351021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18576645352803871185567347 27864968029205806778351021)
  ·
    refine ⟨10449363010952177541881633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27864968029205806778351021 10449363010952177541881633)
    ·
      refine ⟨7837022258214133156411225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10449363010952177541881633 7837022258214133156411225)
      ·
        refine ⟨5877766693660599867308419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7837022258214133156411225 5877766693660599867308419)
        ·
          refine ⟨8816650040490899800962629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5877766693660599867308419 8816650040490899800962629)
          ·
            refine ⟨1653121882592043712680493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8816650040490899800962629 1653121882592043712680493)
            ·
              refine ⟨619920705972016392255185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1653121882592043712680493 619920705972016392255185)
              ·
                refine ⟨464940529479012294191389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 619920705972016392255185 464940529479012294191389)
                ·
                  refine ⟨174352698554629610321771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 464940529479012294191389 174352698554629610321771)
                  ·
                    rfl

theorem cell21_763989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 3, 2, 3].length) (baseStart_763989 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_763989 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_763989 prefixEnd_763989 := by exact prefixLift 763989
  have htrace : WordTrace (prefixWord ++ tailWord_763989) baseStart_763989 baseEnd_763989 := by
    simpa [prefixWord, tailWord_763989, baseEnd_763989] using wordTrace_append hprefix tailTrace_763989
  have hstable : (prefixWord ++ tailWord_763989).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763989).length < 2 ^ (prefixWord ++ tailWord_763989).sum := by decide
  have hdescent : baseEnd_763989 < baseStart_763989 := by decide
  rcases family_descends (prefixWord ++ tailWord_763989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764000 : List Nat := [2, 1, 1, 3, 2, 4, 2, 6]
def baseStart_764000 : Nat := 118140960795 + 764000 * 2 ^ 59
def prefixEnd_764000 : Nat := 4983230072969 + 3 ^ 40 * 764000 * 2
def baseEnd_764000 : Nat := 58118402968165345212805

theorem tailTrace_764000 : CollatzResearch.WordTrace tailWord_764000 prefixEnd_764000 58118402968165345212805 := by
  unfold tailWord_764000
  simp only [CollatzResearch.WordTrace]
  refine ⟨13932684616082977828500727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18576912821443970438000969 13932684616082977828500727)
  ·
    refine ⟨20899026924124466742751091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13932684616082977828500727 20899026924124466742751091)
    ·
      refine ⟨31348540386186700114126637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20899026924124466742751091 31348540386186700114126637)
      ·
        refine ⟨11755702644820012542797489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31348540386186700114126637 11755702644820012542797489)
        ·
          refine ⟨8816776983615009407098117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11755702644820012542797489 8816776983615009407098117)
          ·
            refine ⟨1653145684427814263830897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8816776983615009407098117 1653145684427814263830897)
            ·
              refine ⟨1239859263320860697873173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1653145684427814263830897 1239859263320860697873173)
              ·
                refine ⟨58118402968165345212805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1239859263320860697873173 58118402968165345212805)
                ·
                  rfl

theorem cell21_764000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2, 6].length) (baseStart_764000 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_764000 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_764000 prefixEnd_764000 := by exact prefixLift 764000
  have htrace : WordTrace (prefixWord ++ tailWord_764000) baseStart_764000 baseEnd_764000 := by
    simpa [prefixWord, tailWord_764000, baseEnd_764000] using wordTrace_append hprefix tailTrace_764000
  have hstable : (prefixWord ++ tailWord_764000).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764000).length < 2 ^ (prefixWord ++ tailWord_764000).sum := by decide
  have hdescent : baseEnd_764000 < baseStart_764000 := by decide
  rcases family_descends (prefixWord ++ tailWord_764000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764107 : List Nat := [1, 1, 1, 1, 3, 2, 3, 6, 3]
def baseStart_764107 : Nat := 118140960795 + 764107 * 2 ^ 59
def prefixEnd_764107 : Nat := 4983230072969 + 3 ^ 40 * 764107 * 2
def baseEnd_764107 : Nat := 174379627762287627354863

theorem tailTrace_764107 : CollatzResearch.WordTrace tailWord_764107 prefixEnd_764107 174379627762287627354863 := by
  unfold tailWord_764107
  simp only [CollatzResearch.WordTrace]
  refine ⟨27869271842778312931146575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18579514561852208620764383 27869271842778312931146575)
  ·
    refine ⟨41803907764167469396719863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27869271842778312931146575 41803907764167469396719863)
    ·
      refine ⟨62705861646251204095079795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41803907764167469396719863 62705861646251204095079795)
      ·
        refine ⟨94058792469376806142619693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62705861646251204095079795 94058792469376806142619693)
        ·
          refine ⟨35272047176016302303482385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94058792469376806142619693 35272047176016302303482385)
          ·
            refine ⟨26454035382012226727611789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35272047176016302303482385 26454035382012226727611789)
            ·
              refine ⟨9920263268254585022854421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26454035382012226727611789 9920263268254585022854421)
              ·
                refine ⟨465012340699433672946301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9920263268254585022854421 465012340699433672946301)
                ·
                  refine ⟨174379627762287627354863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 465012340699433672946301 174379627762287627354863)
                  ·
                    rfl

theorem cell21_764107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 6, 3].length) (baseStart_764107 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_764107 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_764107 prefixEnd_764107 := by exact prefixLift 764107
  have htrace : WordTrace (prefixWord ++ tailWord_764107) baseStart_764107 baseEnd_764107 := by
    simpa [prefixWord, tailWord_764107, baseEnd_764107] using wordTrace_append hprefix tailTrace_764107
  have hstable : (prefixWord ++ tailWord_764107).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764107).length < 2 ^ (prefixWord ++ tailWord_764107).sum := by decide
  have hdescent : baseEnd_764107 < baseStart_764107 := by decide
  rcases family_descends (prefixWord ++ tailWord_764107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764121 : List Nat := [1, 2, 1, 2, 3, 1, 2, 5, 4]
def baseStart_764121 : Nat := 118140960795 + 764121 * 2 ^ 59
def prefixEnd_764121 : Nat := 4983230072969 + 3 ^ 40 * 764121 * 2
def baseEnd_764121 : Nat := 174382822753026714121501

theorem tailTrace_764121 : CollatzResearch.WordTrace tailWord_764121 prefixEnd_764121 174382822753026714121501 := by
  unfold tailWord_764121
  simp only [CollatzResearch.WordTrace]
  refine ⟨27869782464727593322156217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18579854976485062214770811 27869782464727593322156217)
  ·
    refine ⟨20902336848545694991617163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27869782464727593322156217 20902336848545694991617163)
    ·
      refine ⟨31353505272818542487425745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20902336848545694991617163 31353505272818542487425745)
      ·
        refine ⟨23515128954613906865569309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31353505272818542487425745 23515128954613906865569309)
        ·
          refine ⟨8818173357980215074588491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23515128954613906865569309 8818173357980215074588491)
          ·
            refine ⟨13227260036970322611882737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8818173357980215074588491 13227260036970322611882737)
            ·
              refine ⟨9920445027727741958912053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13227260036970322611882737 9920445027727741958912053)
              ·
                refine ⟨930041721349475808648005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9920445027727741958912053 930041721349475808648005)
                ·
                  refine ⟨174382822753026714121501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 930041721349475808648005 174382822753026714121501)
                  ·
                    rfl

theorem cell21_764121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 5, 4].length) (baseStart_764121 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_764121 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_764121 prefixEnd_764121 := by exact prefixLift 764121
  have htrace : WordTrace (prefixWord ++ tailWord_764121) baseStart_764121 baseEnd_764121 := by
    simpa [prefixWord, tailWord_764121, baseEnd_764121] using wordTrace_append hprefix tailTrace_764121
  have hstable : (prefixWord ++ tailWord_764121).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764121).length < 2 ^ (prefixWord ++ tailWord_764121).sum := by decide
  have hdescent : baseEnd_764121 < baseStart_764121 := by decide
  rcases family_descends (prefixWord ++ tailWord_764121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764217 : List Nat := [1, 2, 1, 6, 1, 1, 4, 2, 3]
def baseStart_764217 : Nat := 118140960795 + 764217 * 2 ^ 59
def prefixEnd_764217 : Nat := 4983230072969 + 3 ^ 40 * 764217 * 2
def baseEnd_764217 : Nat := 174404731260951880521305

theorem tailTrace_764217 : CollatzResearch.WordTrace tailWord_764217 prefixEnd_764217 174404731260951880521305 := by
  unfold tailWord_764217
  simp only [CollatzResearch.WordTrace]
  refine ⟨27873283872379801717650905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18582189248253201145100603 27873283872379801717650905)
  ·
    refine ⟨20904962904284851288238179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27873283872379801717650905 20904962904284851288238179)
    ·
      refine ⟨31357444356427276932357269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20904962904284851288238179 31357444356427276932357269)
      ·
        refine ⟨1469880204207528606204247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 31357444356427276932357269 1469880204207528606204247)
        ·
          refine ⟨2204820306311292909306371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1469880204207528606204247 2204820306311292909306371)
          ·
            refine ⟨3307230459466939363959557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2204820306311292909306371 3307230459466939363959557)
            ·
              refine ⟨620105711150051130742417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3307230459466939363959557 620105711150051130742417)
              ·
                refine ⟨465079283362538348056813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 620105711150051130742417 465079283362538348056813)
                ·
                  refine ⟨174404731260951880521305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 465079283362538348056813 174404731260951880521305)
                  ·
                    rfl

theorem cell21_764217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 4, 2, 3].length) (baseStart_764217 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_764217 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_764217 prefixEnd_764217 := by exact prefixLift 764217
  have htrace : WordTrace (prefixWord ++ tailWord_764217) baseStart_764217 baseEnd_764217 := by
    simpa [prefixWord, tailWord_764217, baseEnd_764217] using wordTrace_append hprefix tailTrace_764217
  have hstable : (prefixWord ++ tailWord_764217).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764217).length < 2 ^ (prefixWord ++ tailWord_764217).sum := by decide
  have hdescent : baseEnd_764217 < baseStart_764217 := by decide
  rcases family_descends (prefixWord ++ tailWord_764217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764242 : List Nat := [3, 2, 2, 1, 1, 1, 3, 1, 7]
def baseStart_764242 : Nat := 118140960795 + 764242 * 2 ^ 59
def prefixEnd_764242 : Nat := 4983230072969 + 3 ^ 40 * 764242 * 2
def baseEnd_764242 : Nat := 174410436601557392604587

theorem tailTrace_764242 : CollatzResearch.WordTrace tailWord_764242 prefixEnd_764242 174410436601557392604587 := by
  unfold tailWord_764242
  simp only [CollatzResearch.WordTrace]
  refine ⟨6968548924322307746827745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18582797131526153991540653 6968548924322307746827745)
  ·
    refine ⟨5226411693241730810120809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6968548924322307746827745 5226411693241730810120809)
    ·
      refine ⟨3919808769931298107590607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5226411693241730810120809 3919808769931298107590607)
      ·
        refine ⟨5879713154896947161385911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3919808769931298107590607 5879713154896947161385911)
        ·
          refine ⟨8819569732345420742078867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5879713154896947161385911 8819569732345420742078867)
          ·
            refine ⟨13229354598518131113118301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8819569732345420742078867 13229354598518131113118301)
            ·
              refine ⟨4961007974444299167419363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13229354598518131113118301 4961007974444299167419363)
              ·
                refine ⟨7441511961666448751129045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4961007974444299167419363 7441511961666448751129045)
                ·
                  refine ⟨174410436601557392604587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7441511961666448751129045 174410436601557392604587)
                  ·
                    rfl

theorem cell21_764242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 1, 7].length) (baseStart_764242 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_764242 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_764242 prefixEnd_764242 := by exact prefixLift 764242
  have htrace : WordTrace (prefixWord ++ tailWord_764242) baseStart_764242 baseEnd_764242 := by
    simpa [prefixWord, tailWord_764242, baseEnd_764242] using wordTrace_append hprefix tailTrace_764242
  have hstable : (prefixWord ++ tailWord_764242).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764242).length < 2 ^ (prefixWord ++ tailWord_764242).sum := by decide
  have hdescent : baseEnd_764242 < baseStart_764242 := by decide
  rcases family_descends (prefixWord ++ tailWord_764242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764245 : List Nat := [1, 3, 2, 2, 4, 1, 3, 5]
def baseStart_764245 : Nat := 118140960795 + 764245 * 2 ^ 59
def prefixEnd_764245 : Nat := 4983230072969 + 3 ^ 40 * 764245 * 2
def baseEnd_764245 : Nat := 58137040414143351351527

theorem tailTrace_764245 : CollatzResearch.WordTrace tailWord_764245 prefixEnd_764245 58137040414143351351527 := by
  unfold tailWord_764245
  simp only [CollatzResearch.WordTrace]
  refine ⟨27874305116278362499670189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18582870077518908333113459 27874305116278362499670189)
  ·
    refine ⟨10452864418604385937376321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27874305116278362499670189 10452864418604385937376321)
    ·
      refine ⟨7839648313953289453032241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10452864418604385937376321 7839648313953289453032241)
      ·
        refine ⟨5879736235464967089774181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7839648313953289453032241 5879736235464967089774181)
        ·
          refine ⟨1102450544149681329332659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5879736235464967089774181 1102450544149681329332659)
          ·
            refine ⟨1653675816224521993998989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1102450544149681329332659 1653675816224521993998989)
            ·
              refine ⟨620128431084195747749621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1653675816224521993998989 620128431084195747749621)
              ·
                refine ⟨58137040414143351351527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 620128431084195747749621 58137040414143351351527)
                ·
                  rfl

theorem cell21_764245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 3, 5].length) (baseStart_764245 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_764245 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_764245 prefixEnd_764245 := by exact prefixLift 764245
  have htrace : WordTrace (prefixWord ++ tailWord_764245) baseStart_764245 baseEnd_764245 := by
    simpa [prefixWord, tailWord_764245, baseEnd_764245] using wordTrace_append hprefix tailTrace_764245
  have hstable : (prefixWord ++ tailWord_764245).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764245).length < 2 ^ (prefixWord ++ tailWord_764245).sum := by decide
  have hdescent : baseEnd_764245 < baseStart_764245 := by decide
  rcases family_descends (prefixWord ++ tailWord_764245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764321 : List Nat := [1, 2, 3, 5, 1, 2, 7]
def baseStart_764321 : Nat := 118140960795 + 764321 * 2 ^ 59
def prefixEnd_764321 : Nat := 4983230072969 + 3 ^ 40 * 764321 * 2
def baseEnd_764321 : Nat := 19380940608652312309751

theorem tailTrace_764321 : CollatzResearch.WordTrace tailWord_764321 prefixEnd_764321 19380940608652312309751 := by
  unfold tailWord_764321
  simp only [CollatzResearch.WordTrace]
  refine ⟨27877077064003027479436817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18584718042668684986291211 27877077064003027479436817)
  ·
    refine ⟨20907807798002270609577613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27877077064003027479436817 20907807798002270609577613)
    ·
      refine ⟨7840427924250851478591605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20907807798002270609577613 7840427924250851478591605)
      ·
        refine ⟨735040117898517326117963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7840427924250851478591605 735040117898517326117963)
        ·
          refine ⟨1102560176847775989176945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 735040117898517326117963 1102560176847775989176945)
          ·
            refine ⟨826920132635831991882709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1102560176847775989176945 826920132635831991882709)
            ·
              refine ⟨19380940608652312309751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 826920132635831991882709 19380940608652312309751)
              ·
                rfl

theorem cell21_764321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 7].length) (baseStart_764321 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_764321 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_764321 prefixEnd_764321 := by exact prefixLift 764321
  have htrace : WordTrace (prefixWord ++ tailWord_764321) baseStart_764321 baseEnd_764321 := by
    simpa [prefixWord, tailWord_764321, baseEnd_764321] using wordTrace_append hprefix tailTrace_764321
  have hstable : (prefixWord ++ tailWord_764321).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764321).length < 2 ^ (prefixWord ++ tailWord_764321).sum := by decide
  have hdescent : baseEnd_764321 < baseStart_764321 := by decide
  rcases family_descends (prefixWord ++ tailWord_764321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764386 : List Nat := [3, 3, 3, 2, 1, 1, 1, 4, 3]
def baseStart_764386 : Nat := 118140960795 + 764386 * 2 ^ 59
def prefixEnd_764386 : Nat := 4983230072969 + 3 ^ 40 * 764386 * 2
def baseEnd_764386 : Nat := 174443299363445142204293

theorem tailTrace_764386 : CollatzResearch.WordTrace tailWord_764386 prefixEnd_764386 174443299363445142204293 := by
  unfold tailWord_764386
  simp only [CollatzResearch.WordTrace]
  refine ⟨6969861952191885895138253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18586298539178362387035341 6969861952191885895138253)
  ·
    refine ⟨2613698232071957210676845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6969861952191885895138253 2613698232071957210676845)
    ·
      refine ⟨980136837026983954003817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2613698232071957210676845 980136837026983954003817)
      ·
        refine ⟨735102627770237965502863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 980136837026983954003817 735102627770237965502863)
        ·
          refine ⟨1102653941655356948254295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 735102627770237965502863 1102653941655356948254295)
          ·
            refine ⟨1653980912483035422381443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1102653941655356948254295 1653980912483035422381443)
            ·
              refine ⟨2480971368724553133572165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1653980912483035422381443 2480971368724553133572165)
              ·
                refine ⟨465182131635853712544781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2480971368724553133572165 465182131635853712544781)
                ·
                  refine ⟨174443299363445142204293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 465182131635853712544781 174443299363445142204293)
                  ·
                    rfl

theorem cell21_764386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 4, 3].length) (baseStart_764386 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_764386 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_764386 prefixEnd_764386 := by exact prefixLift 764386
  have htrace : WordTrace (prefixWord ++ tailWord_764386) baseStart_764386 baseEnd_764386 := by
    simpa [prefixWord, tailWord_764386, baseEnd_764386] using wordTrace_append hprefix tailTrace_764386
  have hstable : (prefixWord ++ tailWord_764386).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764386).length < 2 ^ (prefixWord ++ tailWord_764386).sum := by decide
  have hdescent : baseEnd_764386 < baseStart_764386 := by decide
  rcases family_descends (prefixWord ++ tailWord_764386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764397 : List Nat := [1, 5, 1, 3, 1, 3, 1, 6]
def baseStart_764397 : Nat := 118140960795 + 764397 * 2 ^ 59
def prefixEnd_764397 : Nat := 4983230072969 + 3 ^ 40 * 764397 * 2
def baseEnd_764397 : Nat := 58148603237770522506979

theorem tailTrace_764397 : CollatzResearch.WordTrace tailWord_764397 prefixEnd_764397 58148603237770522506979 := by
  unfold tailWord_764397
  simp only [CollatzResearch.WordTrace]
  refine ⟨27879849011727692459203445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18586566007818461639468963 27879849011727692459203445)
  ·
    refine ⟨2613735844849471168050323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27879849011727692459203445 2613735844849471168050323)
    ·
      refine ⟨3920603767274206752075485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2613735844849471168050323 3920603767274206752075485)
      ·
        refine ⟨1470226412727827532028307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3920603767274206752075485 1470226412727827532028307)
        ·
          refine ⟨2205339619091741298042461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1470226412727827532028307 2205339619091741298042461)
          ·
            refine ⟨827002357159402986765923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2205339619091741298042461 827002357159402986765923)
            ·
              refine ⟨1240503535739104480148885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 827002357159402986765923 1240503535739104480148885)
              ·
                refine ⟨58148603237770522506979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1240503535739104480148885 58148603237770522506979)
                ·
                  rfl

theorem cell21_764397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 1, 6].length) (baseStart_764397 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_764397 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_764397 prefixEnd_764397 := by exact prefixLift 764397
  have htrace : WordTrace (prefixWord ++ tailWord_764397) baseStart_764397 baseEnd_764397 := by
    simpa [prefixWord, tailWord_764397, baseEnd_764397] using wordTrace_append hprefix tailTrace_764397
  have hstable : (prefixWord ++ tailWord_764397).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764397).length < 2 ^ (prefixWord ++ tailWord_764397).sum := by decide
  have hdescent : baseEnd_764397 < baseStart_764397 := by decide
  rcases family_descends (prefixWord ++ tailWord_764397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764428 : List Nat := [2, 2, 1, 2, 4, 2, 2, 3, 3]
def baseStart_764428 : Nat := 118140960795 + 764428 * 2 ^ 59
def prefixEnd_764428 : Nat := 4983230072969 + 3 ^ 40 * 764428 * 2
def baseEnd_764428 : Nat := 174452884335662402504207

theorem tailTrace_764428 : CollatzResearch.WordTrace tailWord_764428 prefixEnd_764428 174452884335662402504207 := by
  unfold tailWord_764428
  simp only [CollatzResearch.WordTrace]
  refine ⟨13940489837307692376790969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18587319783076923169054625 13940489837307692376790969)
  ·
    refine ⟨10455367377980769282593227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13940489837307692376790969 10455367377980769282593227)
    ·
      refine ⟨15683051066971153923889841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10455367377980769282593227 15683051066971153923889841)
      ·
        refine ⟨11762288300228365442917381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15683051066971153923889841 11762288300228365442917381)
        ·
          refine ⟨2205429056292818520547009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11762288300228365442917381 2205429056292818520547009)
          ·
            refine ⟨1654071792219613890410257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2205429056292818520547009 1654071792219613890410257)
            ·
              refine ⟨1240553844164710417807693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1654071792219613890410257 1240553844164710417807693)
              ·
                refine ⟨465207691561766406677885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1240553844164710417807693 465207691561766406677885)
                ·
                  refine ⟨174452884335662402504207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 465207691561766406677885 174452884335662402504207)
                  ·
                    rfl

theorem cell21_764428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2, 3, 3].length) (baseStart_764428 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_764428 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_764428 prefixEnd_764428 := by exact prefixLift 764428
  have htrace : WordTrace (prefixWord ++ tailWord_764428) baseStart_764428 baseEnd_764428 := by
    simpa [prefixWord, tailWord_764428, baseEnd_764428] using wordTrace_append hprefix tailTrace_764428
  have hstable : (prefixWord ++ tailWord_764428).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764428).length < 2 ^ (prefixWord ++ tailWord_764428).sum := by decide
  have hdescent : baseEnd_764428 < baseStart_764428 := by decide
  rcases family_descends (prefixWord ++ tailWord_764428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764510 : List Nat := [4, 4, 1, 2, 1, 2, 2, 1, 4]
def baseStart_764510 : Nat := 118140960795 + 764510 * 2 ^ 59
def prefixEnd_764510 : Nat := 4983230072969 + 3 ^ 40 * 764510 * 2
def baseEnd_764510 : Nat := 174471597852848482137373

theorem tailTrace_764510 : CollatzResearch.WordTrace tailWord_764510 prefixEnd_764510 174471597852848482137373 := by
  unfold tailWord_764510
  simp only [CollatzResearch.WordTrace]
  refine ⟨3485496307539789094758373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18589313640212208505377989 3485496307539789094758373)
  ·
    refine ⟨653530557663710455267195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3485496307539789094758373 653530557663710455267195)
    ·
      refine ⟨980295836495565682900793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 653530557663710455267195 980295836495565682900793)
      ·
        refine ⟨735221877371674262175595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 980295836495565682900793 735221877371674262175595)
        ·
          refine ⟨1102832816057511393263393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 735221877371674262175595 1102832816057511393263393)
          ·
            refine ⟨827124612043133544947545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1102832816057511393263393 827124612043133544947545)
            ·
              refine ⟨620343459032350158710659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 827124612043133544947545 620343459032350158710659)
              ·
                refine ⟨930515188548525238065989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 620343459032350158710659 930515188548525238065989)
                ·
                  refine ⟨174471597852848482137373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 930515188548525238065989 174471597852848482137373)
                  ·
                    rfl

theorem cell21_764510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_764510 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_764510 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_764510 prefixEnd_764510 := by exact prefixLift 764510
  have htrace : WordTrace (prefixWord ++ tailWord_764510) baseStart_764510 baseEnd_764510 := by
    simpa [prefixWord, tailWord_764510, baseEnd_764510] using wordTrace_append hprefix tailTrace_764510
  have hstable : (prefixWord ++ tailWord_764510).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764510).length < 2 ^ (prefixWord ++ tailWord_764510).sum := by decide
  have hdescent : baseEnd_764510 < baseStart_764510 := by decide
  rcases family_descends (prefixWord ++ tailWord_764510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764515 : List Nat := [1, 1, 1, 5, 1, 2, 4, 6]
def baseStart_764515 : Nat := 118140960795 + 764515 * 2 ^ 59
def prefixEnd_764515 : Nat := 4983230072969 + 3 ^ 40 * 764515 * 2
def baseEnd_764515 : Nat := 58157579640323194851343

theorem tailTrace_764515 : CollatzResearch.WordTrace tailWord_764515 prefixEnd_764515 58157579640323194851343 := by
  unfold tailWord_764515
  simp only [CollatzResearch.WordTrace]
  refine ⟨27884152825300198611998999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18589435216866799074665999 27884152825300198611998999)
  ·
    refine ⟨41826229237950297917998499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27884152825300198611998999 41826229237950297917998499)
    ·
      refine ⟨62739343856925446876997749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41826229237950297917998499 62739343856925446876997749)
      ·
        refine ⟨5881813486586760644718539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 62739343856925446876997749 5881813486586760644718539)
        ·
          refine ⟨8822720229880140967077809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5881813486586760644718539 8822720229880140967077809)
          ·
            refine ⟨6617040172410105725308357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8822720229880140967077809 6617040172410105725308357)
            ·
              refine ⟨1240695032326894823495317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6617040172410105725308357 1240695032326894823495317)
              ·
                refine ⟨58157579640323194851343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1240695032326894823495317 58157579640323194851343)
                ·
                  rfl

theorem cell21_764515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4, 6].length) (baseStart_764515 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_764515 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_764515 prefixEnd_764515 := by exact prefixLift 764515
  have htrace : WordTrace (prefixWord ++ tailWord_764515) baseStart_764515 baseEnd_764515 := by
    simpa [prefixWord, tailWord_764515, baseEnd_764515] using wordTrace_append hprefix tailTrace_764515
  have hstable : (prefixWord ++ tailWord_764515).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764515).length < 2 ^ (prefixWord ++ tailWord_764515).sum := by decide
  have hdescent : baseEnd_764515 < baseStart_764515 := by decide
  rcases family_descends (prefixWord ++ tailWord_764515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764622 : List Nat := [4, 1, 1, 1, 3, 2, 1, 3, 5]
def baseStart_764622 : Nat := 118140960795 + 764622 * 2 ^ 59
def prefixEnd_764622 : Nat := 4983230072969 + 3 ^ 40 * 764622 * 2
def baseEnd_764622 : Nat := 174497157778761176270477

theorem tailTrace_764622 : CollatzResearch.WordTrace tailWord_764622 prefixEnd_764622 174497157778761176270477 := by
  unfold tailWord_764622
  simp only [CollatzResearch.WordTrace]
  refine ⟨3486006929489069485768015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18592036957275037257429413 3486006929489069485768015)
  ·
    refine ⟨5229010394233604228652023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3486006929489069485768015 5229010394233604228652023)
    ·
      refine ⟨7843515591350406342978035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5229010394233604228652023 7843515591350406342978035)
      ·
        refine ⟨11765273387025609514467053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7843515591350406342978035 11765273387025609514467053)
        ·
          refine ⟨4411977520134603567925145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11765273387025609514467053 4411977520134603567925145)
          ·
            refine ⟨3308983140100952675943859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4411977520134603567925145 3308983140100952675943859)
            ·
              refine ⟨4963474710151429013915789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3308983140100952675943859 4963474710151429013915789)
              ·
                refine ⟨1861303016306785880218421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4963474710151429013915789 1861303016306785880218421)
                ·
                  refine ⟨174497157778761176270477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1861303016306785880218421 174497157778761176270477)
                  ·
                    rfl

theorem cell21_764622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 3, 5].length) (baseStart_764622 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_764622 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_764622 prefixEnd_764622 := by exact prefixLift 764622
  have htrace : WordTrace (prefixWord ++ tailWord_764622) baseStart_764622 baseEnd_764622 := by
    simpa [prefixWord, tailWord_764622, baseEnd_764622] using wordTrace_append hprefix tailTrace_764622
  have hstable : (prefixWord ++ tailWord_764622).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764622).length < 2 ^ (prefixWord ++ tailWord_764622).sum := by decide
  have hdescent : baseEnd_764622 < baseStart_764622 := by decide
  rcases family_descends (prefixWord ++ tailWord_764622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764895 : List Nat := [1, 1, 2, 3, 6, 8]
def baseStart_764895 : Nat := 118140960795 + 764895 * 2 ^ 59
def prefixEnd_764895 : Nat := 4983230072969 + 3 ^ 40 * 764895 * 2
def baseEnd_764895 : Nat := 6465165188821235859997

theorem tailTrace_764895 : CollatzResearch.WordTrace tailWord_764895 prefixEnd_764895 6465165188821235859997 := by
  unfold tailWord_764895
  simp only [CollatzResearch.WordTrace]
  refine ⟨27898012563923523510832139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18598675042615682340554759 27898012563923523510832139)
  ·
    refine ⟨41847018845885285266248209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27898012563923523510832139 41847018845885285266248209)
    ·
      refine ⟨31385264134413963949686157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41847018845885285266248209 31385264134413963949686157)
      ·
        refine ⟨11769474050405236481132309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31385264134413963949686157 11769474050405236481132309)
        ·
          refine ⟨551694096112745460053077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 11769474050405236481132309 551694096112745460053077)
          ·
            refine ⟨6465165188821235859997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 551694096112745460053077 6465165188821235859997)
            ·
              rfl

theorem cell21_764895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 8].length) (baseStart_764895 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_764895 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_764895 prefixEnd_764895 := by exact prefixLift 764895
  have htrace : WordTrace (prefixWord ++ tailWord_764895) baseStart_764895 baseEnd_764895 := by
    simpa [prefixWord, tailWord_764895, baseEnd_764895] using wordTrace_append hprefix tailTrace_764895
  have hstable : (prefixWord ++ tailWord_764895).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764895).length < 2 ^ (prefixWord ++ tailWord_764895).sum := by decide
  have hdescent : baseEnd_764895 < baseStart_764895 := by decide
  rcases family_descends (prefixWord ++ tailWord_764895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764898 : List Nat := [3, 3, 3, 1, 1, 1, 1, 4, 4]
def baseStart_764898 : Nat := 118140960795 + 764898 * 2 ^ 59
def prefixEnd_764898 : Nat := 4983230072969 + 3 ^ 40 * 764898 * 2
def baseEnd_764898 : Nat := 174560144739046029669913

theorem tailTrace_764898 : CollatzResearch.WordTrace tailWord_764898 prefixEnd_764898 174560144739046029669913 := by
  unfold tailWord_764898
  simp only [CollatzResearch.WordTrace]
  refine ⟨6974530495728163755797837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18598747988608436682127565 6974530495728163755797837)
  ·
    refine ⟨2615448935898061408424189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6974530495728163755797837 2615448935898061408424189)
    ·
      refine ⟨980793350961773028159071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2615448935898061408424189 980793350961773028159071)
      ·
        refine ⟨1471190026442659542238607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 980793350961773028159071 1471190026442659542238607)
        ·
          refine ⟨2206785039663989313357911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1471190026442659542238607 2206785039663989313357911)
          ·
            refine ⟨3310177559495983970036867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2206785039663989313357911 3310177559495983970036867)
            ·
              refine ⟨4965266339243975955055301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3310177559495983970036867 4965266339243975955055301)
              ·
                refine ⟨930987438608245491572869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4965266339243975955055301 930987438608245491572869)
                ·
                  refine ⟨174560144739046029669913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 930987438608245491572869 174560144739046029669913)
                  ·
                    rfl

theorem cell21_764898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 4, 4].length) (baseStart_764898 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_764898 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_764898 prefixEnd_764898 := by exact prefixLift 764898
  have htrace : WordTrace (prefixWord ++ tailWord_764898) baseStart_764898 baseEnd_764898 := by
    simpa [prefixWord, tailWord_764898, baseEnd_764898] using wordTrace_append hprefix tailTrace_764898
  have hstable : (prefixWord ++ tailWord_764898).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764898).length < 2 ^ (prefixWord ++ tailWord_764898).sum := by decide
  have hdescent : baseEnd_764898 < baseStart_764898 := by decide
  rcases family_descends (prefixWord ++ tailWord_764898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764923 : List Nat := [1, 1, 1, 1, 1, 3, 3, 2, 8]
def baseStart_764923 : Nat := 118140960795 + 764923 * 2 ^ 59
def prefixEnd_764923 : Nat := 4983230072969 + 3 ^ 40 * 764923 * 2
def baseEnd_764923 : Nat := 174565850079651541753195

theorem tailTrace_764923 : CollatzResearch.WordTrace tailWord_764923 prefixEnd_764923 174565850079651541753195 := by
  unfold tailWord_764923
  simp only [CollatzResearch.WordTrace]
  refine ⟨27899033807822084292851423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18599355871881389528567615 27899033807822084292851423)
  ·
    refine ⟨41848550711733126439277135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27899033807822084292851423 41848550711733126439277135)
    ·
      refine ⟨62772826067599689658915703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41848550711733126439277135 62772826067599689658915703)
      ·
        refine ⟨94159239101399534488373555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62772826067599689658915703 94159239101399534488373555)
        ·
          refine ⟨141238858652099301732560333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94159239101399534488373555 141238858652099301732560333)
          ·
            refine ⟨52964571994537238149710125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 141238858652099301732560333 52964571994537238149710125)
            ·
              refine ⟨19861714497951464306141297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52964571994537238149710125 19861714497951464306141297)
              ·
                refine ⟨14896285873463598229605973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19861714497951464306141297 14896285873463598229605973)
                ·
                  refine ⟨174565850079651541753195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14896285873463598229605973 174565850079651541753195)
                  ·
                    rfl

theorem cell21_764923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 8].length) (baseStart_764923 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_764923 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_764923 prefixEnd_764923 := by exact prefixLift 764923
  have htrace : WordTrace (prefixWord ++ tailWord_764923) baseStart_764923 baseEnd_764923 := by
    simpa [prefixWord, tailWord_764923, baseEnd_764923] using wordTrace_append hprefix tailTrace_764923
  have hstable : (prefixWord ++ tailWord_764923).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764923).length < 2 ^ (prefixWord ++ tailWord_764923).sum := by decide
  have hdescent : baseEnd_764923 < baseStart_764923 := by decide
  rcases family_descends (prefixWord ++ tailWord_764923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764954 : List Nat := [3, 1, 1, 3, 1, 2, 10]
def baseStart_764954 : Nat := 118140960795 + 764954 * 2 ^ 59
def prefixEnd_764954 : Nat := 4983230072969 + 3 ^ 40 * 764954 * 2
def baseEnd_764954 : Nat := 19396991633555819637385

theorem tailTrace_764954 : CollatzResearch.WordTrace tailWord_764954 prefixEnd_764954 19396991633555819637385 := by
  unfold tailWord_764954
  simp only [CollatzResearch.WordTrace]
  refine ⟨6975041117677444146807479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18600109647139851058153277 6975041117677444146807479)
  ·
    refine ⟨10462561676516166220211219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6975041117677444146807479 10462561676516166220211219)
    ·
      refine ⟨15693842514774249330316829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10462561676516166220211219 15693842514774249330316829)
      ·
        refine ⟨5885190943040343498868811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15693842514774249330316829 5885190943040343498868811)
        ·
          refine ⟨8827786414560515248303217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5885190943040343498868811 8827786414560515248303217)
          ·
            refine ⟨6620839810920386436227413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8827786414560515248303217 6620839810920386436227413)
            ·
              refine ⟨19396991633555819637385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 6620839810920386436227413 19396991633555819637385)
              ·
                rfl

theorem cell21_764954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 10].length) (baseStart_764954 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_764954 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_764954 prefixEnd_764954 := by exact prefixLift 764954
  have htrace : WordTrace (prefixWord ++ tailWord_764954) baseStart_764954 baseEnd_764954 := by
    simpa [prefixWord, tailWord_764954, baseEnd_764954] using wordTrace_append hprefix tailTrace_764954
  have hstable : (prefixWord ++ tailWord_764954).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764954).length < 2 ^ (prefixWord ++ tailWord_764954).sum := by decide
  have hdescent : baseEnd_764954 < baseStart_764954 := by decide
  rcases family_descends (prefixWord ++ tailWord_764954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764957 : List Nat := [1, 4, 2, 2, 3, 1, 1, 1, 6]
def baseStart_764957 : Nat := 118140960795 + 764957 * 2 ^ 59
def prefixEnd_764957 : Nat := 4983230072969 + 3 ^ 40 * 764957 * 2
def baseEnd_764957 : Nat := 174573609342875038186459

theorem tailTrace_764957 : CollatzResearch.WordTrace tailWord_764957 prefixEnd_764957 174573609342875038186459 := by
  unfold tailWord_764957
  simp only [CollatzResearch.WordTrace]
  refine ⟨27900273889698908099589125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18600182593132605399726083 27900273889698908099589125)
  ·
    refine ⟨5231301354318545268672961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27900273889698908099589125 5231301354318545268672961)
    ·
      refine ⟨3923476015738908951504721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5231301354318545268672961 3923476015738908951504721)
      ·
        refine ⟨2942607011804181713628541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3923476015738908951504721 2942607011804181713628541)
        ·
          refine ⟨1103477629426568142610703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2942607011804181713628541 1103477629426568142610703)
          ·
            refine ⟨1655216444139852213916055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1103477629426568142610703 1655216444139852213916055)
            ·
              refine ⟨2482824666209778320874083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1655216444139852213916055 2482824666209778320874083)
              ·
                refine ⟨3724236999314667481311125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2482824666209778320874083 3724236999314667481311125)
                ·
                  refine ⟨174573609342875038186459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3724236999314667481311125 174573609342875038186459)
                  ·
                    rfl

theorem cell21_764957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 1, 6].length) (baseStart_764957 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_764957 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_764957 prefixEnd_764957 := by exact prefixLift 764957
  have htrace : WordTrace (prefixWord ++ tailWord_764957) baseStart_764957 baseEnd_764957 := by
    simpa [prefixWord, tailWord_764957, baseEnd_764957] using wordTrace_append hprefix tailTrace_764957
  have hstable : (prefixWord ++ tailWord_764957).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764957).length < 2 ^ (prefixWord ++ tailWord_764957).sum := by decide
  have hdescent : baseEnd_764957 < baseStart_764957 := by decide
  rcases family_descends (prefixWord ++ tailWord_764957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764974 : List Nat := [4, 1, 3, 1, 1, 1, 5, 1, 4]
def baseStart_764974 : Nat := 118140960795 + 764974 * 2 ^ 59
def prefixEnd_764974 : Nat := 4983230072969 + 3 ^ 40 * 764974 * 2
def baseEnd_764974 : Nat := 174577488974486786403091

theorem tailTrace_764974 : CollatzResearch.WordTrace tailWord_764974 prefixEnd_764974 174577488974486786403091 := by
  unfold tailWord_764974
  simp only [CollatzResearch.WordTrace]
  refine ⟨3487611741329665000369747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18600595953758213335305317 3487611741329665000369747)
  ·
    refine ⟨5231417611994497500554621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3487611741329665000369747 5231417611994497500554621)
    ·
      refine ⟨1961781604497936562707983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5231417611994497500554621 1961781604497936562707983)
      ·
        refine ⟨2942672406746904844061975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1961781604497936562707983 2942672406746904844061975)
        ·
          refine ⟨4414008610120357266092963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2942672406746904844061975 4414008610120357266092963)
          ·
            refine ⟨6621012915180535899139445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4414008610120357266092963 6621012915180535899139445)
            ·
              refine ⟨620719960798175240544323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6621012915180535899139445 620719960798175240544323)
              ·
                refine ⟨931079941197262860816485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 620719960798175240544323 931079941197262860816485)
                ·
                  refine ⟨174577488974486786403091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 931079941197262860816485 174577488974486786403091)
                  ·
                    rfl

theorem cell21_764974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 5, 1, 4].length) (baseStart_764974 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_764974 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_764974 prefixEnd_764974 := by exact prefixLift 764974
  have htrace : WordTrace (prefixWord ++ tailWord_764974) baseStart_764974 baseEnd_764974 := by
    simpa [prefixWord, tailWord_764974, baseEnd_764974] using wordTrace_append hprefix tailTrace_764974
  have hstable : (prefixWord ++ tailWord_764974).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764974).length < 2 ^ (prefixWord ++ tailWord_764974).sum := by decide
  have hdescent : baseEnd_764974 < baseStart_764974 := by decide
  rcases family_descends (prefixWord ++ tailWord_764974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764988 : List Nat := [2, 2, 2, 2, 2, 4, 2, 5]
def baseStart_764988 : Nat := 118140960795 + 764988 * 2 ^ 59
def prefixEnd_764988 : Nat := 4983230072969 + 3 ^ 40 * 764988 * 2
def baseEnd_764988 : Nat := 58193561321741957723243

theorem tailTrace_764988 : CollatzResearch.WordTrace tailWord_764988 prefixEnd_764988 58193561321741957723243 := by
  unfold tailWord_764988
  simp only [CollatzResearch.WordTrace]
  refine ⟨13950702276293300196983809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18600936368391066929311745 13950702276293300196983809)
  ·
    refine ⟨10463026707219975147737857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13950702276293300196983809 10463026707219975147737857)
    ·
      refine ⟨7847270030414981360803393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10463026707219975147737857 7847270030414981360803393)
      ·
        refine ⟨5885452522811236020602545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7847270030414981360803393 5885452522811236020602545)
        ·
          refine ⟨4414089392108427015451909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5885452522811236020602545 4414089392108427015451909)
          ·
            refine ⟨827641761020330065397233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4414089392108427015451909 827641761020330065397233)
            ·
              refine ⟨620731320765247549047925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 827641761020330065397233 620731320765247549047925)
              ·
                refine ⟨58193561321741957723243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 620731320765247549047925 58193561321741957723243)
                ·
                  rfl

theorem cell21_764988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 2, 5].length) (baseStart_764988 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_764988 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_764988 prefixEnd_764988 := by exact prefixLift 764988
  have htrace : WordTrace (prefixWord ++ tailWord_764988) baseStart_764988 baseEnd_764988 := by
    simpa [prefixWord, tailWord_764988, baseEnd_764988] using wordTrace_append hprefix tailTrace_764988
  have hstable : (prefixWord ++ tailWord_764988).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764988).length < 2 ^ (prefixWord ++ tailWord_764988).sum := by decide
  have hdescent : baseEnd_764988 < baseStart_764988 := by decide
  rcases family_descends (prefixWord ++ tailWord_764988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765016 : List Nat := [2, 1, 2, 2, 1, 3, 2, 4, 4]
def baseStart_765016 : Nat := 118140960795 + 765016 * 2 ^ 59
def prefixEnd_765016 : Nat := 4983230072969 + 3 ^ 40 * 765016 * 2
def baseEnd_765016 : Nat := 174587073946704046703005

theorem tailTrace_765016 : CollatzResearch.WordTrace tailWord_765016 prefixEnd_765016 174587073946704046703005 := by
  unfold tailWord_765016
  simp only [CollatzResearch.WordTrace]
  refine ⟨13951212898242580587993451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18601617197656774117324601 13951212898242580587993451)
  ·
    refine ⟨20926819347363870881990177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13951212898242580587993451 20926819347363870881990177)
    ·
      refine ⟨15695114510522903161492633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20926819347363870881990177 15695114510522903161492633)
      ·
        refine ⟨11771335882892177371119475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15695114510522903161492633 11771335882892177371119475)
        ·
          refine ⟨17657003824338266056679213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11771335882892177371119475 17657003824338266056679213)
          ·
            refine ⟨6621376434126849771254705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17657003824338266056679213 6621376434126849771254705)
            ·
              refine ⟨4966032325595137328441029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6621376434126849771254705 4966032325595137328441029)
              ·
                refine ⟨931131061049088249082693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4966032325595137328441029 931131061049088249082693)
                ·
                  refine ⟨174587073946704046703005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 931131061049088249082693 174587073946704046703005)
                  ·
                    rfl

theorem cell21_765016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 4, 4].length) (baseStart_765016 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_765016 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_765016 prefixEnd_765016 := by exact prefixLift 765016
  have htrace : WordTrace (prefixWord ++ tailWord_765016) baseStart_765016 baseEnd_765016 := by
    simpa [prefixWord, tailWord_765016, baseEnd_765016] using wordTrace_append hprefix tailTrace_765016
  have hstable : (prefixWord ++ tailWord_765016).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765016).length < 2 ^ (prefixWord ++ tailWord_765016).sum := by decide
  have hdescent : baseEnd_765016 < baseStart_765016 := by decide
  rcases family_descends (prefixWord ++ tailWord_765016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765033 : List Nat := [1, 2, 1, 1, 1, 6, 4, 1, 4]
def baseStart_765033 : Nat := 118140960795 + 765033 * 2 ^ 59
def prefixEnd_765033 : Nat := 4983230072969 + 3 ^ 40 * 765033 * 2
def baseEnd_765033 : Nat := 174590953578315794919637

theorem tailTrace_765033 : CollatzResearch.WordTrace tailWord_765033 prefixEnd_765033 174590953578315794919637 := by
  unfold tailWord_765033
  simp only [CollatzResearch.WordTrace]
  refine ⟨27903045837423573079355753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18602030558282382052903835 27903045837423573079355753)
  ·
    refine ⟨20927284378067679809516815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27903045837423573079355753 20927284378067679809516815)
    ·
      refine ⟨31390926567101519714275223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20927284378067679809516815 31390926567101519714275223)
      ·
        refine ⟨47086389850652279571412835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31390926567101519714275223 47086389850652279571412835)
        ·
          refine ⟨70629584775978419357119253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47086389850652279571412835 70629584775978419357119253)
          ·
            refine ⟨3310761786373988407364965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 70629584775978419357119253 3310761786373988407364965)
            ·
              refine ⟨620767834945122826380931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3310761786373988407364965 620767834945122826380931)
              ·
                refine ⟨931151752417684239571397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 620767834945122826380931 931151752417684239571397)
                ·
                  refine ⟨174590953578315794919637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 931151752417684239571397 174590953578315794919637)
                  ·
                    rfl

theorem cell21_765033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 4, 1, 4].length) (baseStart_765033 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_765033 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_765033 prefixEnd_765033 := by exact prefixLift 765033
  have htrace : WordTrace (prefixWord ++ tailWord_765033) baseStart_765033 baseEnd_765033 := by
    simpa [prefixWord, tailWord_765033, baseEnd_765033] using wordTrace_append hprefix tailTrace_765033
  have hstable : (prefixWord ++ tailWord_765033).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765033).length < 2 ^ (prefixWord ++ tailWord_765033).sum := by decide
  have hdescent : baseEnd_765033 < baseStart_765033 := by decide
  rcases family_descends (prefixWord ++ tailWord_765033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765075 : List Nat := [1, 1, 1, 2, 1, 2, 4, 3, 6]
def baseStart_765075 : Nat := 118140960795 + 765075 * 2 ^ 59
def prefixEnd_765075 : Nat := 4983230072969 + 3 ^ 40 * 765075 * 2
def baseEnd_765075 : Nat := 174600538550533055219551

theorem tailTrace_765075 : CollatzResearch.WordTrace tailWord_765075 prefixEnd_765075 174600538550533055219551 := by
  unfold tailWord_765075
  simp only [CollatzResearch.WordTrace]
  refine ⟨27904577703271414252384679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18603051802180942834923119 27904577703271414252384679)
  ·
    refine ⟨41856866554907121378577019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27904577703271414252384679 41856866554907121378577019)
    ·
      refine ⟨62785299832360682067865529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41856866554907121378577019 62785299832360682067865529)
      ·
        refine ⟨47088974874270511550899147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62785299832360682067865529 47088974874270511550899147)
        ·
          refine ⟨70633462311405767326348721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47088974874270511550899147 70633462311405767326348721)
          ·
            refine ⟨52975096733554325494761541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70633462311405767326348721 52975096733554325494761541)
            ·
              refine ⟨9932830637541436030267789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52975096733554325494761541 9932830637541436030267789)
              ·
                refine ⟨3724811489078038511350421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9932830637541436030267789 3724811489078038511350421)
                ·
                  refine ⟨174600538550533055219551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3724811489078038511350421 174600538550533055219551)
                  ·
                    rfl

theorem cell21_765075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 3, 6].length) (baseStart_765075 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_765075 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_765075 prefixEnd_765075 := by exact prefixLift 765075
  have htrace : WordTrace (prefixWord ++ tailWord_765075) baseStart_765075 baseEnd_765075 := by
    simpa [prefixWord, tailWord_765075, baseEnd_765075] using wordTrace_append hprefix tailTrace_765075
  have hstable : (prefixWord ++ tailWord_765075).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765075).length < 2 ^ (prefixWord ++ tailWord_765075).sum := by decide
  have hdescent : baseEnd_765075 < baseStart_765075 := by decide
  rcases family_descends (prefixWord ++ tailWord_765075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765157 : List Nat := [1, 3, 1, 4, 4, 1, 2, 5]
def baseStart_765157 : Nat := 118140960795 + 765157 * 2 ^ 59
def prefixEnd_765157 : Nat := 4983230072969 + 3 ^ 40 * 765157 * 2
def baseEnd_765157 : Nat := 58206417355906378284239

theorem tailTrace_765157 : CollatzResearch.WordTrace tailWord_765157 prefixEnd_765157 58206417355906378284239 := by
  unfold tailWord_765157
  simp only [CollatzResearch.WordTrace]
  refine ⟨27907568488974342256869725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18605045659316228171246483 27907568488974342256869725)
  ·
    refine ⟨10465338183365378346326147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27907568488974342256869725 10465338183365378346326147)
    ·
      refine ⟨15698007275048067519489221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10465338183365378346326147 15698007275048067519489221)
      ·
        refine ⟨2943376364071512659904229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15698007275048067519489221 2943376364071512659904229)
        ·
          refine ⟨551883068263408623732043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2943376364071512659904229 551883068263408623732043)
          ·
            refine ⟨827824602395112935598065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 551883068263408623732043 827824602395112935598065)
            ·
              refine ⟨620868451796334701698549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 827824602395112935598065 620868451796334701698549)
              ·
                refine ⟨58206417355906378284239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 620868451796334701698549 58206417355906378284239)
                ·
                  rfl

theorem cell21_765157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 2, 5].length) (baseStart_765157 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_765157 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_765157 prefixEnd_765157 := by exact prefixLift 765157
  have htrace : WordTrace (prefixWord ++ tailWord_765157) baseStart_765157 baseEnd_765157 := by
    simpa [prefixWord, tailWord_765157, baseEnd_765157] using wordTrace_append hprefix tailTrace_765157
  have hstable : (prefixWord ++ tailWord_765157).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765157).length < 2 ^ (prefixWord ++ tailWord_765157).sum := by decide
  have hdescent : baseEnd_765157 < baseStart_765157 := by decide
  rcases family_descends (prefixWord ++ tailWord_765157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765171 : List Nat := [1, 1, 1, 2, 2, 7, 1, 3, 3]
def baseStart_765171 : Nat := 118140960795 + 765171 * 2 ^ 59
def prefixEnd_765171 : Nat := 4983230072969 + 3 ^ 40 * 765171 * 2
def baseEnd_765171 : Nat := 174622447058458221619355

theorem tailTrace_765171 : CollatzResearch.WordTrace tailWord_765171 prefixEnd_765171 174622447058458221619355 := by
  unfold tailWord_765171
  simp only [CollatzResearch.WordTrace]
  refine ⟨27908079110923622647879367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18605386073949081765252911 27908079110923622647879367)
  ·
    refine ⟨41862118666385433971819051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27908079110923622647879367 41862118666385433971819051)
    ·
      refine ⟨62793177999578150957728577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41862118666385433971819051 62793177999578150957728577)
      ·
        refine ⟨47094883499683613218296433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62793177999578150957728577 47094883499683613218296433)
        ·
          refine ⟨35321162624762709913722325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47094883499683613218296433 35321162624762709913722325)
          ·
            refine ⟨827839749017876013602867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 35321162624762709913722325 827839749017876013602867)
            ·
              refine ⟨1241759623526814020404301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 827839749017876013602867 1241759623526814020404301)
              ·
                refine ⟨465659858822555257651613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1241759623526814020404301 465659858822555257651613)
                ·
                  refine ⟨174622447058458221619355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 465659858822555257651613 174622447058458221619355)
                  ·
                    rfl

theorem cell21_765171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 1, 3, 3].length) (baseStart_765171 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_765171 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_765171 prefixEnd_765171 := by exact prefixLift 765171
  have htrace : WordTrace (prefixWord ++ tailWord_765171) baseStart_765171 baseEnd_765171 := by
    simpa [prefixWord, tailWord_765171, baseEnd_765171] using wordTrace_append hprefix tailTrace_765171
  have hstable : (prefixWord ++ tailWord_765171).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765171).length < 2 ^ (prefixWord ++ tailWord_765171).sum := by decide
  have hdescent : baseEnd_765171 < baseStart_765171 := by decide
  rcases family_descends (prefixWord ++ tailWord_765171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765188 : List Nat := [2, 3, 2, 2, 2, 2, 3, 2, 3]
def baseStart_765188 : Nat := 118140960795 + 765188 * 2 ^ 59
def prefixEnd_765188 : Nat := 4983230072969 + 3 ^ 40 * 765188 * 2
def baseEnd_765188 : Nat := 174626326690069969835987

theorem tailTrace_765188 : CollatzResearch.WordTrace tailWord_765188 prefixEnd_765188 174626326690069969835987 := by
  unfold tailWord_765188
  simp only [CollatzResearch.WordTrace]
  refine ⟨13954349575931017275624109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18605799434574689700832145 13954349575931017275624109)
  ·
    refine ⟨5232881090974131478359041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13954349575931017275624109 5232881090974131478359041)
    ·
      refine ⟨3924660818230598608769281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5232881090974131478359041 3924660818230598608769281)
      ·
        refine ⟨2943495613672948956576961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3924660818230598608769281 2943495613672948956576961)
        ·
          refine ⟨2207621710254711717432721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2943495613672948956576961 2207621710254711717432721)
          ·
            refine ⟨1655716282691033788074541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2207621710254711717432721 1655716282691033788074541)
            ·
              refine ⟨620893606009137670527953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1655716282691033788074541 620893606009137670527953)
              ·
                refine ⟨465670204506853252895965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 620893606009137670527953 465670204506853252895965)
                ·
                  refine ⟨174626326690069969835987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 465670204506853252895965 174626326690069969835987)
                  ·
                    rfl

theorem cell21_765188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 3, 2, 3].length) (baseStart_765188 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_765188 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_765188 prefixEnd_765188 := by exact prefixLift 765188
  have htrace : WordTrace (prefixWord ++ tailWord_765188) baseStart_765188 baseEnd_765188 := by
    simpa [prefixWord, tailWord_765188, baseEnd_765188] using wordTrace_append hprefix tailTrace_765188
  have hstable : (prefixWord ++ tailWord_765188).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765188).length < 2 ^ (prefixWord ++ tailWord_765188).sum := by decide
  have hdescent : baseEnd_765188 < baseStart_765188 := by decide
  rcases family_descends (prefixWord ++ tailWord_765188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765244 : List Nat := [2, 2, 2, 2, 1, 3, 1, 4, 4]
def baseStart_765244 : Nat := 118140960795 + 765244 * 2 ^ 59
def prefixEnd_765244 : Nat := 4983230072969 + 3 ^ 40 * 765244 * 2
def baseEnd_765244 : Nat := 174639106653026316902539

theorem tailTrace_765244 : CollatzResearch.WordTrace tailWord_765244 prefixEnd_765244 174639106653026316902539 := by
  unfold tailWord_765244
  simp only [CollatzResearch.WordTrace]
  refine ⟨13955370819829578057643393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18607161093106104076857857 13955370819829578057643393)
  ·
    refine ⟨10466528114872183543232545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13955370819829578057643393 10466528114872183543232545)
    ·
      refine ⟨7849896086154137657424409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10466528114872183543232545 7849896086154137657424409)
      ·
        refine ⟨5887422064615603243068307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7849896086154137657424409 5887422064615603243068307)
        ·
          refine ⟨8831133096923404864602461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5887422064615603243068307 8831133096923404864602461)
          ·
            refine ⟨3311674911346276824225923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8831133096923404864602461 3311674911346276824225923)
            ·
              refine ⟨4967512367019415236338885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3311674911346276824225923 4967512367019415236338885)
              ·
                refine ⟨931408568816140356813541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4967512367019415236338885 931408568816140356813541)
                ·
                  refine ⟨174639106653026316902539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 931408568816140356813541 174639106653026316902539)
                  ·
                    rfl

theorem cell21_765244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 4, 4].length) (baseStart_765244 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_765244 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_765244 prefixEnd_765244 := by exact prefixLift 765244
  have htrace : WordTrace (prefixWord ++ tailWord_765244) baseStart_765244 baseEnd_765244 := by
    simpa [prefixWord, tailWord_765244, baseEnd_765244] using wordTrace_append hprefix tailTrace_765244
  have hstable : (prefixWord ++ tailWord_765244).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765244).length < 2 ^ (prefixWord ++ tailWord_765244).sum := by decide
  have hdescent : baseEnd_765244 < baseStart_765244 := by decide
  rcases family_descends (prefixWord ++ tailWord_765244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765247 : List Nat := [1, 1, 2, 2, 4, 2, 4, 2, 3]
def baseStart_765247 : Nat := 118140960795 + 765247 * 2 ^ 59
def prefixEnd_765247 : Nat := 4983230072969 + 3 ^ 40 * 765247 * 2
def baseEnd_765247 : Nat := 174639791293898978352533

theorem tailTrace_765247 : CollatzResearch.WordTrace tailWord_765247 prefixEnd_765247 174639791293898978352533 := by
  unfold tailWord_765247
  simp only [CollatzResearch.WordTrace]
  refine ⟨27910851058648287627645995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18607234039098858418430663 27910851058648287627645995)
  ·
    refine ⟨41866276587972431441468993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27910851058648287627645995 41866276587972431441468993)
    ·
      refine ⟨31399707440979323581101745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41866276587972431441468993 31399707440979323581101745)
      ·
        refine ⟨23549780580734492685826309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31399707440979323581101745 23549780580734492685826309)
        ·
          refine ⟨4415583858887717378592433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23549780580734492685826309 4415583858887717378592433)
          ·
            refine ⟨3311687894165788033944325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4415583858887717378592433 3311687894165788033944325)
            ·
              refine ⟨620941480156085256364561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3311687894165788033944325 620941480156085256364561)
              ·
                refine ⟨465706110117063942273421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 620941480156085256364561 465706110117063942273421)
                ·
                  refine ⟨174639791293898978352533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 465706110117063942273421 174639791293898978352533)
                  ·
                    rfl

theorem cell21_765247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 4, 2, 3].length) (baseStart_765247 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_765247 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_765247 prefixEnd_765247 := by exact prefixLift 765247
  have htrace : WordTrace (prefixWord ++ tailWord_765247) baseStart_765247 baseEnd_765247 := by
    simpa [prefixWord, tailWord_765247, baseEnd_765247] using wordTrace_append hprefix tailTrace_765247
  have hstable : (prefixWord ++ tailWord_765247).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765247).length < 2 ^ (prefixWord ++ tailWord_765247).sum := by decide
  have hdescent : baseEnd_765247 < baseStart_765247 := by decide
  rcases family_descends (prefixWord ++ tailWord_765247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765303 : List Nat := [1, 1, 3, 1, 1, 2, 5, 1, 6]
def baseStart_765303 : Nat := 118140960795 + 765303 * 2 ^ 59
def prefixEnd_765303 : Nat := 4983230072969 + 3 ^ 40 * 765303 * 2
def baseEnd_765303 : Nat := 174652571256855325419085

theorem tailTrace_765303 : CollatzResearch.WordTrace tailWord_765303 prefixEnd_765303 174652571256855325419085 := by
  unfold tailWord_765303
  simp only [CollatzResearch.WordTrace]
  refine ⟨27912893546445409191684563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18608595697630272794456375 27912893546445409191684563)
  ·
    refine ⟨41869340319668113787526845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27912893546445409191684563 41869340319668113787526845)
    ·
      refine ⟨15701002619875542670322567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41869340319668113787526845 15701002619875542670322567)
      ·
        refine ⟨23551503929813314005483851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15701002619875542670322567 23551503929813314005483851)
        ·
          refine ⟨35327255894719971008225777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23551503929813314005483851 35327255894719971008225777)
          ·
            refine ⟨26495441921039978256169333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35327255894719971008225777 26495441921039978256169333)
            ·
              refine ⟨2483947680097497961515875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26495441921039978256169333 2483947680097497961515875)
              ·
                refine ⟨3725921520146246942273813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2483947680097497961515875 3725921520146246942273813)
                ·
                  refine ⟨174652571256855325419085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3725921520146246942273813 174652571256855325419085)
                  ·
                    rfl

theorem cell21_765303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 1, 6].length) (baseStart_765303 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_765303 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_765303 prefixEnd_765303 := by exact prefixLift 765303
  have htrace : WordTrace (prefixWord ++ tailWord_765303) baseStart_765303 baseEnd_765303 := by
    simpa [prefixWord, tailWord_765303, baseEnd_765303] using wordTrace_append hprefix tailTrace_765303
  have hstable : (prefixWord ++ tailWord_765303).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765303).length < 2 ^ (prefixWord ++ tailWord_765303).sum := by decide
  have hdescent : baseEnd_765303 < baseStart_765303 := by decide
  rcases family_descends (prefixWord ++ tailWord_765303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765410 : List Nat := [3, 3, 3, 12]
def baseStart_765410 : Nat := 118140960795 + 765410 * 2 ^ 59
def prefixEnd_765410 : Nat := 4983230072969 + 3 ^ 40 * 765410 * 2
def baseEnd_765410 : Nat := 718835350266036696031

theorem tailTrace_765410 : CollatzResearch.WordTrace tailWord_765410 prefixEnd_765410 718835350266036696031 := by
  unfold tailWord_765410
  simp only [CollatzResearch.WordTrace]
  refine ⟨6979199039264441616457421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18611197438038510977219789 6979199039264441616457421)
  ·
    refine ⟨2617199639724165606171533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6979199039264441616457421 2617199639724165606171533)
    ·
      refine ⟨981449864896562102314325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2617199639724165606171533 981449864896562102314325)
      ·
        refine ⟨718835350266036696031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 12 981449864896562102314325 718835350266036696031)
        ·
          rfl

theorem cell21_765410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 12].length) (baseStart_765410 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_765410 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_765410 prefixEnd_765410 := by exact prefixLift 765410
  have htrace : WordTrace (prefixWord ++ tailWord_765410) baseStart_765410 baseEnd_765410 := by
    simpa [prefixWord, tailWord_765410, baseEnd_765410] using wordTrace_append hprefix tailTrace_765410
  have hstable : (prefixWord ++ tailWord_765410).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765410).length < 2 ^ (prefixWord ++ tailWord_765410).sum := by decide
  have hdescent : baseEnd_765410 < baseStart_765410 := by decide
  rcases family_descends (prefixWord ++ tailWord_765410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765413 : List Nat := [1, 3, 1, 5, 1, 2, 2, 2, 4]
def baseStart_765413 : Nat := 118140960795 + 765413 * 2 ^ 59
def prefixEnd_765413 : Nat := 4983230072969 + 3 ^ 40 * 765413 * 2
def baseEnd_765413 : Nat := 174677674755519578585527

theorem tailTrace_765413 : CollatzResearch.WordTrace tailWord_765413 prefixEnd_765413 174677674755519578585527 := by
  unfold tailWord_765413
  simp only [CollatzResearch.WordTrace]
  refine ⟨27916905576046897978188893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18611270384031265318792595 27916905576046897978188893)
  ·
    refine ⟨10468839591017586741820835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27916905576046897978188893 10468839591017586741820835)
    ·
      refine ⟨15703259386526380112731253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10468839591017586741820835 15703259386526380112731253)
      ·
        refine ⟨1472180567486848135568555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15703259386526380112731253 1472180567486848135568555)
        ·
          refine ⟨2208270851230272203352833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1472180567486848135568555 2208270851230272203352833)
          ·
            refine ⟨1656203138422704152514625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2208270851230272203352833 1656203138422704152514625)
            ·
              refine ⟨1242152353817028114385969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1656203138422704152514625 1242152353817028114385969)
              ·
                refine ⟨931614265362771085789477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1242152353817028114385969 931614265362771085789477)
                ·
                  refine ⟨174677674755519578585527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 931614265362771085789477 174677674755519578585527)
                  ·
                    rfl

theorem cell21_765413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2, 2, 4].length) (baseStart_765413 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_765413 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_765413 prefixEnd_765413 := by exact prefixLift 765413
  have htrace : WordTrace (prefixWord ++ tailWord_765413) baseStart_765413 baseEnd_765413 := by
    simpa [prefixWord, tailWord_765413, baseEnd_765413] using wordTrace_append hprefix tailTrace_765413
  have hstable : (prefixWord ++ tailWord_765413).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765413).length < 2 ^ (prefixWord ++ tailWord_765413).sum := by decide
  have hdescent : baseEnd_765413 < baseStart_765413 := by decide
  rcases family_descends (prefixWord ++ tailWord_765413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765444 : List Nat := [2, 3, 2, 3, 2, 1, 3, 5]
def baseStart_765444 : Nat := 118140960795 + 765444 * 2 ^ 59
def prefixEnd_765444 : Nat := 4983230072969 + 3 ^ 40 * 765444 * 2
def baseEnd_765444 : Nat := 58228249792623471189599

theorem tailTrace_765444 : CollatzResearch.WordTrace tailWord_765444 prefixEnd_765444 58228249792623471189599 := by
  unfold tailWord_765444
  simp only [CollatzResearch.WordTrace]
  refine ⟨13959018119467295136283693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18612024159289726848378257 13959018119467295136283693)
  ·
    refine ⟨5234631794800235676106385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13959018119467295136283693 5234631794800235676106385)
    ·
      refine ⟨3925973846100176757079789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5234631794800235676106385 3925973846100176757079789)
      ·
        refine ⟨1472240192287566283904921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3925973846100176757079789 1472240192287566283904921)
        ·
          refine ⟨1104180144215674712928691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1472240192287566283904921 1104180144215674712928691)
          ·
            refine ⟨1656270216323512069393037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1104180144215674712928691 1656270216323512069393037)
            ·
              refine ⟨621101331121317026022389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1656270216323512069393037 621101331121317026022389)
              ·
                refine ⟨58228249792623471189599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 621101331121317026022389 58228249792623471189599)
                ·
                  rfl

theorem cell21_765444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 3, 5].length) (baseStart_765444 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_765444 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_765444 prefixEnd_765444 := by exact prefixLift 765444
  have htrace : WordTrace (prefixWord ++ tailWord_765444) baseStart_765444 baseEnd_765444 := by
    simpa [prefixWord, tailWord_765444, baseEnd_765444] using wordTrace_append hprefix tailTrace_765444
  have hstable : (prefixWord ++ tailWord_765444).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765444).length < 2 ^ (prefixWord ++ tailWord_765444).sum := by decide
  have hdescent : baseEnd_765444 < baseStart_765444 := by decide
  rcases family_descends (prefixWord ++ tailWord_765444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765472 : List Nat := [2, 1, 1, 6, 1, 2, 1, 1, 6]
def baseStart_765472 : Nat := 118140960795 + 765472 * 2 ^ 59
def prefixEnd_765472 : Nat := 4983230072969 + 3 ^ 40 * 765472 * 2
def baseEnd_765472 : Nat := 174691139359348587102073

theorem tailTrace_765472 : CollatzResearch.WordTrace tailWord_765472 prefixEnd_765472 174691139359348587102073 := by
  unfold tailWord_765472
  simp only [CollatzResearch.WordTrace]
  refine ⟨13959528741416575527293335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18612704988555434036391113 13959528741416575527293335)
  ·
    refine ⟨20939293112124863290940003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13959528741416575527293335 20939293112124863290940003)
    ·
      refine ⟨31408939668187294936410005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20939293112124863290940003 31408939668187294936410005)
      ·
        refine ⟨1472294046946279450144219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 31408939668187294936410005 1472294046946279450144219)
        ·
          refine ⟨2208441070419419175216329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1472294046946279450144219 2208441070419419175216329)
          ·
            refine ⟨1656330802814564381412247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2208441070419419175216329 1656330802814564381412247)
            ·
              refine ⟨2484496204221846572118371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1656330802814564381412247 2484496204221846572118371)
              ·
                refine ⟨3726744306332769858177557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2484496204221846572118371 3726744306332769858177557)
                ·
                  refine ⟨174691139359348587102073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3726744306332769858177557 174691139359348587102073)
                  ·
                    rfl

theorem cell21_765472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 1, 6].length) (baseStart_765472 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_765472 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_765472 prefixEnd_765472 := by exact prefixLift 765472
  have htrace : WordTrace (prefixWord ++ tailWord_765472) baseStart_765472 baseEnd_765472 := by
    simpa [prefixWord, tailWord_765472, baseEnd_765472] using wordTrace_append hprefix tailTrace_765472
  have hstable : (prefixWord ++ tailWord_765472).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765472).length < 2 ^ (prefixWord ++ tailWord_765472).sum := by decide
  have hdescent : baseEnd_765472 < baseStart_765472 := by decide
  rcases family_descends (prefixWord ++ tailWord_765472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765503 : List Nat := [1, 1, 2, 2, 3, 5, 2, 5]
def baseStart_765503 : Nat := 118140960795 + 765503 * 2 ^ 59
def prefixEnd_765503 : Nat := 4983230072969 + 3 ^ 40 * 765503 * 2
def baseEnd_765503 : Nat := 58232737993899807361781

theorem tailTrace_765503 : CollatzResearch.WordTrace tailWord_765503 prefixEnd_765503 58232737993899807361781 := by
  unfold tailWord_765503
  simp only [CollatzResearch.WordTrace]
  refine ⟨27920188145720843348965163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18613458763813895565976775 27920188145720843348965163)
  ·
    refine ⟨41880282218581265023447745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27920188145720843348965163 41880282218581265023447745)
    ·
      refine ⟨31410211663935948767585809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41880282218581265023447745 31410211663935948767585809)
      ·
        refine ⟨23557658747951961575689357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31410211663935948767585809 23557658747951961575689357)
        ·
          refine ⟨8834122030481985590883509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23557658747951961575689357 8834122030481985590883509)
          ·
            refine ⟨828198940357686149145329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8834122030481985590883509 828198940357686149145329)
            ·
              refine ⟨621149205268264611858997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 828198940357686149145329 621149205268264611858997)
              ·
                refine ⟨58232737993899807361781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 621149205268264611858997 58232737993899807361781)
                ·
                  rfl

theorem cell21_765503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 2, 5].length) (baseStart_765503 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_765503 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_765503 prefixEnd_765503 := by exact prefixLift 765503
  have htrace : WordTrace (prefixWord ++ tailWord_765503) baseStart_765503 baseEnd_765503 := by
    simpa [prefixWord, tailWord_765503, baseEnd_765503] using wordTrace_append hprefix tailTrace_765503
  have hstable : (prefixWord ++ tailWord_765503).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765503).length < 2 ^ (prefixWord ++ tailWord_765503).sum := by decide
  have hdescent : baseEnd_765503 < baseStart_765503 := by decide
  rcases family_descends (prefixWord ++ tailWord_765503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765526 : List Nat := [5, 2, 2, 2, 1, 1, 3, 2, 3]
def baseStart_765526 : Nat := 118140960795 + 765526 * 2 ^ 59
def prefixEnd_765526 : Nat := 4983230072969 + 3 ^ 40 * 765526 * 2
def baseEnd_765526 : Nat := 174703462895056493201963

theorem tailTrace_765526 : CollatzResearch.WordTrace tailWord_765526 prefixEnd_765526 174703462895056493201963 := by
  unfold tailWord_765526
  simp only [CollatzResearch.WordTrace]
  refine ⟨1745064189039844892315777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18614018016425012184701621 1745064189039844892315777)
  ·
    refine ⟨1308798141779883669236833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1745064189039844892315777 1308798141779883669236833)
    ·
      refine ⟨981598606334912751927625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1308798141779883669236833 981598606334912751927625)
      ·
        refine ⟨736198954751184563945719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 981598606334912751927625 736198954751184563945719)
        ·
          refine ⟨1104298432126776845918579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 736198954751184563945719 1104298432126776845918579)
          ·
            refine ⟨1656447648190165268877869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1104298432126776845918579 1656447648190165268877869)
            ·
              refine ⟨621167868071311975829201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1656447648190165268877869 621167868071311975829201)
              ·
                refine ⟨465875901053483981871901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 621167868071311975829201 465875901053483981871901)
                ·
                  refine ⟨174703462895056493201963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 465875901053483981871901 174703462895056493201963)
                  ·
                    rfl

theorem cell21_765526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 3, 2, 3].length) (baseStart_765526 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_765526 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_765526 prefixEnd_765526 := by exact prefixLift 765526
  have htrace : WordTrace (prefixWord ++ tailWord_765526) baseStart_765526 baseEnd_765526 := by
    simpa [prefixWord, tailWord_765526, baseEnd_765526] using wordTrace_append hprefix tailTrace_765526
  have hstable : (prefixWord ++ tailWord_765526).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765526).length < 2 ^ (prefixWord ++ tailWord_765526).sum := by decide
  have hdescent : baseEnd_765526 < baseStart_765526 := by decide
  rcases family_descends (prefixWord ++ tailWord_765526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765545 : List Nat := [1, 2, 1, 1, 1, 4, 3, 8]
def baseStart_765545 : Nat := 118140960795 + 765545 * 2 ^ 59
def prefixEnd_765545 : Nat := 4983230072969 + 3 ^ 40 * 765545 * 2
def baseEnd_765545 : Nat := 58235932984638894128419

theorem tailTrace_765545 : CollatzResearch.WordTrace tailWord_765545 prefixEnd_765545 58235932984638894128419 := by
  unfold tailWord_765545
  simp only [CollatzResearch.WordTrace]
  refine ⟨27921720011568684521994089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18614480007712456347996059 27921720011568684521994089)
  ·
    refine ⟨20941290008676513391495567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27921720011568684521994089 20941290008676513391495567)
    ·
      refine ⟨31411935013014770087243351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20941290008676513391495567 31411935013014770087243351)
      ·
        refine ⟨47117902519522155130865027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31411935013014770087243351 47117902519522155130865027)
        ·
          refine ⟨70676853779283232696297541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47117902519522155130865027 70676853779283232696297541)
          ·
            refine ⟨13251910083615606130555789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70676853779283232696297541 13251910083615606130555789)
            ·
              refine ⟨4969466281355852298958421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13251910083615606130555789 4969466281355852298958421)
              ·
                refine ⟨58235932984638894128419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4969466281355852298958421 58235932984638894128419)
                ·
                  rfl

theorem cell21_765545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 8].length) (baseStart_765545 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_765545 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_765545 prefixEnd_765545 := by exact prefixLift 765545
  have htrace : WordTrace (prefixWord ++ tailWord_765545) baseStart_765545 baseEnd_765545 := by
    simpa [prefixWord, tailWord_765545, baseEnd_765545] using wordTrace_append hprefix tailTrace_765545
  have hstable : (prefixWord ++ tailWord_765545).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765545).length < 2 ^ (prefixWord ++ tailWord_765545).sum := by decide
  have hdescent : baseEnd_765545 < baseStart_765545 := by decide
  rcases family_descends (prefixWord ++ tailWord_765545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765596 : List Nat := [2, 2, 3, 2, 4, 1, 1, 6]
def baseStart_765596 : Nat := 118140960795 + 765596 * 2 ^ 59
def prefixEnd_765596 : Nat := 4983230072969 + 3 ^ 40 * 765596 * 2
def baseEnd_765596 : Nat := 58239812616250642345051

theorem tailTrace_765596 : CollatzResearch.WordTrace tailWord_765596 prefixEnd_765596 58239812616250642345051 := by
  unfold tailWord_765596
  simp only [CollatzResearch.WordTrace]
  refine ⟨13961790067191960116050321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18615720089589280154733761 13961790067191960116050321)
  ·
    refine ⟨10471342550393970087037741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13961790067191960116050321 10471342550393970087037741)
    ·
      refine ⟨3926753456397738782639153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10471342550393970087037741 3926753456397738782639153)
      ·
        refine ⟨2945065092298304086979365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3926753456397738782639153 2945065092298304086979365)
        ·
          refine ⟨552199704805932016308631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2945065092298304086979365 552199704805932016308631)
          ·
            refine ⟨828299557208898024462947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 552199704805932016308631 828299557208898024462947)
            ·
              refine ⟨1242449335813347036694421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 828299557208898024462947 1242449335813347036694421)
              ·
                refine ⟨58239812616250642345051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1242449335813347036694421 58239812616250642345051)
                ·
                  rfl

theorem cell21_765596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 1, 6].length) (baseStart_765596 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_765596 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_765596 prefixEnd_765596 := by exact prefixLift 765596
  have htrace : WordTrace (prefixWord ++ tailWord_765596) baseStart_765596 baseEnd_765596 := by
    simpa [prefixWord, tailWord_765596, baseEnd_765596] using wordTrace_append hprefix tailTrace_765596
  have hstable : (prefixWord ++ tailWord_765596).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765596).length < 2 ^ (prefixWord ++ tailWord_765596).sum := by decide
  have hdescent : baseEnd_765596 < baseStart_765596 := by decide
  rcases family_descends (prefixWord ++ tailWord_765596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765697 : List Nat := [1, 2, 4, 1, 1, 1, 11]
def baseStart_765697 : Nat := 118140960795 + 765697 * 2 ^ 59
def prefixEnd_765697 : Nat := 4983230072969 + 3 ^ 40 * 765697 * 2
def baseEnd_765697 : Nat := 19415831936088688427957

theorem tailTrace_765697 : CollatzResearch.WordTrace tailWord_765697 prefixEnd_765697 19415831936088688427957 := by
  unfold tailWord_765697
  simp only [CollatzResearch.WordTrace]
  refine ⟨27927263907018014481527345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18618175938012009654351563 27927263907018014481527345)
  ·
    refine ⟨20945447930263510861145509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27927263907018014481527345 20945447930263510861145509)
    ·
      refine ⟨3927271486924408286464783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20945447930263510861145509 3927271486924408286464783)
      ·
        refine ⟨5890907230386612429697175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3927271486924408286464783 5890907230386612429697175)
        ·
          refine ⟨8836360845579918644545763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5890907230386612429697175 8836360845579918644545763)
          ·
            refine ⟨13254541268369877966818645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8836360845579918644545763 13254541268369877966818645)
            ·
              refine ⟨19415831936088688427957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 13254541268369877966818645 19415831936088688427957)
              ·
                rfl

theorem cell21_765697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 11].length) (baseStart_765697 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_765697 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_765697 prefixEnd_765697 := by exact prefixLift 765697
  have htrace : WordTrace (prefixWord ++ tailWord_765697) baseStart_765697 baseEnd_765697 := by
    simpa [prefixWord, tailWord_765697, baseEnd_765697] using wordTrace_append hprefix tailTrace_765697
  have hstable : (prefixWord ++ tailWord_765697).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765697).length < 2 ^ (prefixWord ++ tailWord_765697).sum := by decide
  have hdescent : baseEnd_765697 < baseStart_765697 := by decide
  rcases family_descends (prefixWord ++ tailWord_765697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765703 : List Nat := [1, 1, 4, 4, 3, 1, 1, 1, 5]
def baseStart_765703 : Nat := 118140960795 + 765703 * 2 ^ 59
def prefixEnd_765703 : Nat := 4983230072969 + 3 ^ 40 * 765703 * 2
def baseEnd_765703 : Nat := 174743856706543518751601

theorem tailTrace_765703 : CollatzResearch.WordTrace tailWord_765703 prefixEnd_765703 174743856706543518751601 := by
  unfold tailWord_765703
  simp only [CollatzResearch.WordTrace]
  refine ⟨27927482744996277506245763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18618321829997518337497175 27927482744996277506245763)
  ·
    refine ⟨41891224117494416259368645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27927482744996277506245763 41891224117494416259368645)
    ·
      refine ⟨7854604522030203048631621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41891224117494416259368645 7854604522030203048631621)
      ·
        refine ⟨1472738347880663071618429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7854604522030203048631621 1472738347880663071618429)
        ·
          refine ⟨552276880455248651856911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1472738347880663071618429 552276880455248651856911)
          ·
            refine ⟨828415320682872977785367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 552276880455248651856911 828415320682872977785367)
            ·
              refine ⟨1242622981024309466678051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 828415320682872977785367 1242622981024309466678051)
              ·
                refine ⟨1863934471536464200017077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1242622981024309466678051 1863934471536464200017077)
                ·
                  refine ⟨174743856706543518751601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1863934471536464200017077 174743856706543518751601)
                  ·
                    rfl

theorem cell21_765703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 1, 5].length) (baseStart_765703 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_765703 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_765703 prefixEnd_765703 := by exact prefixLift 765703
  have htrace : WordTrace (prefixWord ++ tailWord_765703) baseStart_765703 baseEnd_765703 := by
    simpa [prefixWord, tailWord_765703, baseEnd_765703] using wordTrace_append hprefix tailTrace_765703
  have hstable : (prefixWord ++ tailWord_765703).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765703).length < 2 ^ (prefixWord ++ tailWord_765703).sum := by decide
  have hdescent : baseEnd_765703 < baseStart_765703 := by decide
  rcases family_descends (prefixWord ++ tailWord_765703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765709 : List Nat := [1, 7, 2, 1, 1, 2, 2, 1, 4]
def baseStart_765709 : Nat := 118140960795 + 765709 * 2 ^ 59
def prefixEnd_765709 : Nat := 4983230072969 + 3 ^ 40 * 765709 * 2
def baseEnd_765709 : Nat := 174745225988288841651589

theorem tailTrace_765709 : CollatzResearch.WordTrace tailWord_765709 prefixEnd_765709 174745225988288841651589 := by
  unfold tailWord_765709
  simp only [CollatzResearch.WordTrace]
  refine ⟨27927701582974540530964181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18618467721983027020642787 27927701582974540530964181)
  ·
    refine ⟨654555505850965793694473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 27927701582974540530964181 654555505850965793694473)
    ·
      refine ⟨490916629388224345270855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 654555505850965793694473 490916629388224345270855)
      ·
        refine ⟨736374944082336517906283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 490916629388224345270855 736374944082336517906283)
        ·
          refine ⟨1104562416123504776859425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 736374944082336517906283 1104562416123504776859425)
          ·
            refine ⟨828421812092628582644569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1104562416123504776859425 828421812092628582644569)
            ·
              refine ⟨621316359069471436983427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 828421812092628582644569 621316359069471436983427)
              ·
                refine ⟨931974538604207155475141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 621316359069471436983427 931974538604207155475141)
                ·
                  refine ⟨174745225988288841651589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 931974538604207155475141 174745225988288841651589)
                  ·
                    rfl

theorem cell21_765709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_765709 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_765709 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_765709 prefixEnd_765709 := by exact prefixLift 765709
  have htrace : WordTrace (prefixWord ++ tailWord_765709) baseStart_765709 baseEnd_765709 := by
    simpa [prefixWord, tailWord_765709, baseEnd_765709] using wordTrace_append hprefix tailTrace_765709
  have hstable : (prefixWord ++ tailWord_765709).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765709).length < 2 ^ (prefixWord ++ tailWord_765709).sum := by decide
  have hdescent : baseEnd_765709 < baseStart_765709 := by decide
  rcases family_descends (prefixWord ++ tailWord_765709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765717 : List Nat := [1, 3, 2, 1, 2, 5, 2, 1, 4]
def baseStart_765717 : Nat := 118140960795 + 765717 * 2 ^ 59
def prefixEnd_765717 : Nat := 4983230072969 + 3 ^ 40 * 765717 * 2
def baseEnd_765717 : Nat := 174747051697282605518239

theorem tailTrace_765717 : CollatzResearch.WordTrace tailWord_765717 prefixEnd_765717 174747051697282605518239 := by
  unfold tailWord_765717
  simp only [CollatzResearch.WordTrace]
  refine ⟨27927993366945557897255405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18618662244630371931503603 27927993366945557897255405)
  ·
    refine ⟨10472997512604584211470777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27927993366945557897255405 10472997512604584211470777)
    ·
      refine ⟨7854748134453438158603083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10472997512604584211470777 7854748134453438158603083)
      ·
        refine ⟨11782122201680157237904625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7854748134453438158603083 11782122201680157237904625)
        ·
          refine ⟨8836591651260117928428469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11782122201680157237904625 8836591651260117928428469)
          ·
            refine ⟨828430467305636055790169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8836591651260117928428469 828430467305636055790169)
            ·
              refine ⟨621322850479227041842627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 828430467305636055790169 621322850479227041842627)
              ·
                refine ⟨931984275718840562763941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 621322850479227041842627 931984275718840562763941)
                ·
                  refine ⟨174747051697282605518239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 931984275718840562763941 174747051697282605518239)
                  ·
                    rfl

theorem cell21_765717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 2, 1, 4].length) (baseStart_765717 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_765717 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_765717 prefixEnd_765717 := by exact prefixLift 765717
  have htrace : WordTrace (prefixWord ++ tailWord_765717) baseStart_765717 baseEnd_765717 := by
    simpa [prefixWord, tailWord_765717, baseEnd_765717] using wordTrace_append hprefix tailTrace_765717
  have hstable : (prefixWord ++ tailWord_765717).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765717).length < 2 ^ (prefixWord ++ tailWord_765717).sum := by decide
  have hdescent : baseEnd_765717 < baseStart_765717 := by decide
  rcases family_descends (prefixWord ++ tailWord_765717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765728 : List Nat := [2, 1, 1, 5, 1, 1, 2, 1, 7]
def baseStart_765728 : Nat := 118140960795 + 765728 * 2 ^ 59
def prefixEnd_765728 : Nat := 4983230072969 + 3 ^ 40 * 765728 * 2
def baseEnd_765728 : Nat := 174749562047149030834883

theorem tailTrace_765728 : CollatzResearch.WordTrace tailWord_765728 prefixEnd_765728 174749562047149030834883 := by
  unfold tailWord_765728
  simp only [CollatzResearch.WordTrace]
  refine ⟨13964197284952853387952919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18618929713270471183937225 13964197284952853387952919)
  ·
    refine ⟨20946295927429280081929379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13964197284952853387952919 20946295927429280081929379)
    ·
      refine ⟨31419443891143920122894069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20946295927429280081929379 31419443891143920122894069)
      ·
        refine ⟨2945572864794742511521319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31419443891143920122894069 2945572864794742511521319)
        ·
          refine ⟨4418359297192113767281979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2945572864794742511521319 4418359297192113767281979)
          ·
            refine ⟨6627538945788170650922969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4418359297192113767281979 6627538945788170650922969)
            ·
              refine ⟨4970654209341127988192227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6627538945788170650922969 4970654209341127988192227)
              ·
                refine ⟨7455981314011691982288341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4970654209341127988192227 7455981314011691982288341)
                ·
                  refine ⟨174749562047149030834883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7455981314011691982288341 174749562047149030834883)
                  ·
                    rfl

theorem cell21_765728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 1, 7].length) (baseStart_765728 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_765728 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_765728 prefixEnd_765728 := by exact prefixLift 765728
  have htrace : WordTrace (prefixWord ++ tailWord_765728) baseStart_765728 baseEnd_765728 := by
    simpa [prefixWord, tailWord_765728, baseEnd_765728] using wordTrace_append hprefix tailTrace_765728
  have hstable : (prefixWord ++ tailWord_765728).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765728).length < 2 ^ (prefixWord ++ tailWord_765728).sum := by decide
  have hdescent : baseEnd_765728 < baseStart_765728 := by decide
  rcases family_descends (prefixWord ++ tailWord_765728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765855 : List Nat := [1, 1, 2, 5, 3, 2, 1, 3, 3]
def baseStart_765855 : Nat := 118140960795 + 765855 * 2 ^ 59
def prefixEnd_765855 : Nat := 4983230072969 + 3 ^ 40 * 765855 * 2
def baseEnd_765855 : Nat := 174778545177425032217957

theorem tailTrace_765855 : CollatzResearch.WordTrace tailWord_765855 prefixEnd_765855 174778545177425032217957 := by
  unfold tailWord_765855
  simp only [CollatzResearch.WordTrace]
  refine ⟨27933026640445607465779019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18622017760297071643852679 27933026640445607465779019)
  ·
    refine ⟨41899539960668411198668529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27933026640445607465779019 41899539960668411198668529)
    ·
      refine ⟨31424654970501308399001397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41899539960668411198668529 31424654970501308399001397)
      ·
        refine ⟨2946061403484497662406381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31424654970501308399001397 2946061403484497662406381)
        ·
          refine ⟨1104773026306686623402393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2946061403484497662406381 1104773026306686623402393)
          ·
            refine ⟨828579769730014967551795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1104773026306686623402393 828579769730014967551795)
            ·
              refine ⟨1242869654595022451327693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 828579769730014967551795 1242869654595022451327693)
              ·
                refine ⟨466076120473133419247885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1242869654595022451327693 466076120473133419247885)
                ·
                  refine ⟨174778545177425032217957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 466076120473133419247885 174778545177425032217957)
                  ·
                    rfl

theorem cell21_765855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 1, 3, 3].length) (baseStart_765855 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_765855 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_765855 prefixEnd_765855 := by exact prefixLift 765855
  have htrace : WordTrace (prefixWord ++ tailWord_765855) baseStart_765855 baseEnd_765855 := by
    simpa [prefixWord, tailWord_765855, baseEnd_765855] using wordTrace_append hprefix tailTrace_765855
  have hstable : (prefixWord ++ tailWord_765855).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765855).length < 2 ^ (prefixWord ++ tailWord_765855).sum := by decide
  have hdescent : baseEnd_765855 < baseStart_765855 := by decide
  rcases family_descends (prefixWord ++ tailWord_765855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765939 : List Nat := [1, 1, 1, 2, 2, 2, 1, 2, 9]
def baseStart_765939 : Nat := 118140960795 + 765939 * 2 ^ 59
def prefixEnd_765939 : Nat := 4983230072969 + 3 ^ 40 * 765939 * 2
def baseEnd_765939 : Nat := 174797715121859552817785

theorem tailTrace_765939 : CollatzResearch.WordTrace tailWord_765939 prefixEnd_765939 174797715121859552817785 := by
  unfold tailWord_765939
  simp only [CollatzResearch.WordTrace]
  refine ⟨27936090372141289811836871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18624060248094193207891247 27936090372141289811836871)
  ·
    refine ⟨41904135558211934717755307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27936090372141289811836871 41904135558211934717755307)
    ·
      refine ⟨62856203337317902076632961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41904135558211934717755307 62856203337317902076632961)
      ·
        refine ⟨47142152502988426557474721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62856203337317902076632961 47142152502988426557474721)
        ·
          refine ⟨35356614377241319918106041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47142152502988426557474721 35356614377241319918106041)
          ·
            refine ⟨26517460782930989938579531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35356614377241319918106041 26517460782930989938579531)
            ·
              refine ⟨39776191174396484907869297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26517460782930989938579531 39776191174396484907869297)
              ·
                refine ⟨29832143380797363680901973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39776191174396484907869297 29832143380797363680901973)
                ·
                  refine ⟨174797715121859552817785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 29832143380797363680901973 174797715121859552817785)
                  ·
                    rfl

theorem cell21_765939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 9].length) (baseStart_765939 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_765939 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_765939 prefixEnd_765939 := by exact prefixLift 765939
  have htrace : WordTrace (prefixWord ++ tailWord_765939) baseStart_765939 baseEnd_765939 := by
    simpa [prefixWord, tailWord_765939, baseEnd_765939] using wordTrace_append hprefix tailTrace_765939
  have hstable : (prefixWord ++ tailWord_765939).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765939).length < 2 ^ (prefixWord ++ tailWord_765939).sum := by decide
  have hdescent : baseEnd_765939 < baseStart_765939 := by decide
  rcases family_descends (prefixWord ++ tailWord_765939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765965 : List Nat := [1, 7, 1, 2, 1, 1, 2, 3, 3]
def baseStart_765965 : Nat := 118140960795 + 765965 * 2 ^ 59
def prefixEnd_765965 : Nat := 4983230072969 + 3 ^ 40 * 765965 * 2
def baseEnd_765965 : Nat := 174803648676089285384399

theorem tailTrace_765965 : CollatzResearch.WordTrace tailWord_765965 prefixEnd_765965 174803648676089285384399 := by
  unfold tailWord_765965
  simp only [CollatzResearch.WordTrace]
  refine ⟨27937038670047096252283349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18624692446698064168188899 27937038670047096252283349)
  ·
    refine ⟨654774343829228818412891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 27937038670047096252283349 654774343829228818412891)
    ·
      refine ⟨982161515743843227619337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 654774343829228818412891 982161515743843227619337)
      ·
        refine ⟨736621136807882420714503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 982161515743843227619337 736621136807882420714503)
        ·
          refine ⟨1104931705211823631071755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 736621136807882420714503 1104931705211823631071755)
          ·
            refine ⟨1657397557817735446607633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1104931705211823631071755 1657397557817735446607633)
            ·
              refine ⟨1243048168363301584955725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1657397557817735446607633 1243048168363301584955725)
              ·
                refine ⟨466143063136238094358397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1243048168363301584955725 466143063136238094358397)
                ·
                  refine ⟨174803648676089285384399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 466143063136238094358397 174803648676089285384399)
                  ·
                    rfl

theorem cell21_765965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_765965 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_765965 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_765965 prefixEnd_765965 := by exact prefixLift 765965
  have htrace : WordTrace (prefixWord ++ tailWord_765965) baseStart_765965 baseEnd_765965 := by
    simpa [prefixWord, tailWord_765965, baseEnd_765965] using wordTrace_append hprefix tailTrace_765965
  have hstable : (prefixWord ++ tailWord_765965).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765965).length < 2 ^ (prefixWord ++ tailWord_765965).sum := by decide
  have hdescent : baseEnd_765965 < baseStart_765965 := by decide
  rcases family_descends (prefixWord ++ tailWord_765965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766063 : List Nat := [1, 1, 2, 1, 3, 5, 1, 3, 4]
def baseStart_766063 : Nat := 118140960795 + 766063 * 2 ^ 59
def prefixEnd_766063 : Nat := 4983230072969 + 3 ^ 40 * 766063 * 2
def baseEnd_766063 : Nat := 174826013611262892750865

theorem tailTrace_766063 : CollatzResearch.WordTrace tailWord_766063 prefixEnd_766063 174826013611262892750865 := by
  unfold tailWord_766063
  simp only [CollatzResearch.WordTrace]
  refine ⟨27940613023692058989350843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18627075349128039326233895 27940613023692058989350843)
  ·
    refine ⟨41910919535538088484026265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27940613023692058989350843 41910919535538088484026265)
    ·
      refine ⟨31433189651653566363019699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41910919535538088484026265 31433189651653566363019699)
      ·
        refine ⟨47149784477480349544529549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31433189651653566363019699 47149784477480349544529549)
        ·
          refine ⟨17681169179055131079198581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47149784477480349544529549 17681169179055131079198581)
          ·
            refine ⟨1657609610536418538674867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17681169179055131079198581 1657609610536418538674867)
            ·
              refine ⟨2486414415804627808012301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1657609610536418538674867 2486414415804627808012301)
              ·
                refine ⟨932405405926735428004613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2486414415804627808012301 932405405926735428004613)
                ·
                  refine ⟨174826013611262892750865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 932405405926735428004613 174826013611262892750865)
                  ·
                    rfl

theorem cell21_766063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 3, 4].length) (baseStart_766063 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_766063 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_766063 prefixEnd_766063 := by exact prefixLift 766063
  have htrace : WordTrace (prefixWord ++ tailWord_766063) baseStart_766063 baseEnd_766063 := by
    simpa [prefixWord, tailWord_766063, baseEnd_766063] using wordTrace_append hprefix tailTrace_766063
  have hstable : (prefixWord ++ tailWord_766063).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766063).length < 2 ^ (prefixWord ++ tailWord_766063).sum := by decide
  have hdescent : baseEnd_766063 < baseStart_766063 := by decide
  rcases family_descends (prefixWord ++ tailWord_766063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766077 : List Nat := [1, 4, 1, 1, 3, 2, 2, 7]
def baseStart_766077 : Nat := 118140960795 + 766077 * 2 ^ 59
def prefixEnd_766077 : Nat := 4983230072969 + 3 ^ 40 * 766077 * 2
def baseEnd_766077 : Nat := 58276402867333993172501

theorem tailTrace_766077 : CollatzResearch.WordTrace tailWord_766077 prefixEnd_766077 58276402867333993172501 := by
  unfold tailWord_766077
  simp only [CollatzResearch.WordTrace]
  refine ⟨27941123645641339380360485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18627415763760892920240323 27941123645641339380360485)
  ·
    refine ⟨5238960683557751133817591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27941123645641339380360485 5238960683557751133817591)
    ·
      refine ⟨7858441025336626700726387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5238960683557751133817591 7858441025336626700726387)
      ·
        refine ⟨11787661538004940051089581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7858441025336626700726387 11787661538004940051089581)
        ·
          refine ⟨4420373076751852519158593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11787661538004940051089581 4420373076751852519158593)
          ·
            refine ⟨3315279807563889389368945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4420373076751852519158593 3315279807563889389368945)
            ·
              refine ⟨2486459855672917042026709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3315279807563889389368945 2486459855672917042026709)
              ·
                refine ⟨58276402867333993172501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2486459855672917042026709 58276402867333993172501)
                ·
                  rfl

theorem cell21_766077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 7].length) (baseStart_766077 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_766077 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_766077 prefixEnd_766077 := by exact prefixLift 766077
  have htrace : WordTrace (prefixWord ++ tailWord_766077) baseStart_766077 baseEnd_766077 := by
    simpa [prefixWord, tailWord_766077, baseEnd_766077] using wordTrace_append hprefix tailTrace_766077
  have hstable : (prefixWord ++ tailWord_766077).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766077).length < 2 ^ (prefixWord ++ tailWord_766077).sum := by decide
  have hdescent : baseEnd_766077 < baseStart_766077 := by decide
  rcases family_descends (prefixWord ++ tailWord_766077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766094 : List Nat := [4, 1, 1, 3, 4, 8]
def baseStart_766094 : Nat := 118140960795 + 766094 * 2 ^ 59
def prefixEnd_766094 : Nat := 4983230072969 + 3 ^ 40 * 766094 * 2
def baseEnd_766094 : Nat := 6475299564207915842005

theorem tailTrace_766094 : CollatzResearch.WordTrace tailWord_766094 prefixEnd_766094 6475299564207915842005 := by
  unfold tailWord_766094
  simp only [CollatzResearch.WordTrace]
  refine ⟨3492717960822468910466167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18627829124386500855819557 3492717960822468910466167)
  ·
    refine ⟨5239076941233703365699251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3492717960822468910466167 5239076941233703365699251)
    ·
      refine ⟨7858615411850555048548877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5239076941233703365699251 7858615411850555048548877)
      ·
        refine ⟨2946980779443958143205829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7858615411850555048548877 2946980779443958143205829)
        ·
          refine ⟨552558896145742151851093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2946980779443958143205829 552558896145742151851093)
          ·
            refine ⟨6475299564207915842005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 552558896145742151851093 6475299564207915842005)
            ·
              rfl

theorem cell21_766094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 8].length) (baseStart_766094 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_766094 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_766094 prefixEnd_766094 := by exact prefixLift 766094
  have htrace : WordTrace (prefixWord ++ tailWord_766094) baseStart_766094 baseEnd_766094 := by
    simpa [prefixWord, tailWord_766094, baseEnd_766094] using wordTrace_append hprefix tailTrace_766094
  have hstable : (prefixWord ++ tailWord_766094).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766094).length < 2 ^ (prefixWord ++ tailWord_766094).sum := by decide
  have hdescent : baseEnd_766094 < baseStart_766094 := by decide
  rcases family_descends (prefixWord ++ tailWord_766094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766108 : List Nat := [2, 2, 3, 2, 1, 1, 2, 3, 5]
def baseStart_766108 : Nat := 118140960795 + 766108 * 2 ^ 59
def prefixEnd_766108 : Nat := 4983230072969 + 3 ^ 40 * 766108 * 2
def baseEnd_766108 : Nat := 174836283224352814500773

theorem tailTrace_766108 : CollatzResearch.WordTrace tailWord_766108 prefixEnd_766108 174836283224352814500773 := by
  unfold tailWord_766108
  simp only [CollatzResearch.WordTrace]
  refine ⟨13971127154264515837369489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18628169539019354449825985 13971127154264515837369489)
  ·
    refine ⟨10478345365698386878027117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13971127154264515837369489 10478345365698386878027117)
    ·
      refine ⟨3929379512136895079260169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10478345365698386878027117 3929379512136895079260169)
      ·
        refine ⟨2947034634102671309445127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3929379512136895079260169 2947034634102671309445127)
        ·
          refine ⟨4420551951154006964167691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2947034634102671309445127 4420551951154006964167691)
          ·
            refine ⟨6630827926731010446251537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4420551951154006964167691 6630827926731010446251537)
            ·
              refine ⟨4973120945048257834688653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6630827926731010446251537 4973120945048257834688653)
              ·
                refine ⟨1864920354393096688008245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4973120945048257834688653 1864920354393096688008245)
                ·
                  refine ⟨174836283224352814500773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1864920354393096688008245 174836283224352814500773)
                  ·
                    rfl

theorem cell21_766108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 3, 5].length) (baseStart_766108 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_766108 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_766108 prefixEnd_766108 := by exact prefixLift 766108
  have htrace : WordTrace (prefixWord ++ tailWord_766108) baseStart_766108 baseEnd_766108 := by
    simpa [prefixWord, tailWord_766108, baseEnd_766108] using wordTrace_append hprefix tailTrace_766108
  have hstable : (prefixWord ++ tailWord_766108).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766108).length < 2 ^ (prefixWord ++ tailWord_766108).sum := by decide
  have hdescent : baseEnd_766108 < baseStart_766108 := by decide
  rcases family_descends (prefixWord ++ tailWord_766108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766125 : List Nat := [1, 5, 2, 1, 2, 2, 1, 2, 5]
def baseStart_766125 : Nat := 118140960795 + 766125 * 2 ^ 59
def prefixEnd_766125 : Nat := 4983230072969 + 3 ^ 40 * 766125 * 2
def baseEnd_766125 : Nat := 174840162855964562717405

theorem tailTrace_766125 : CollatzResearch.WordTrace tailWord_766125 prefixEnd_766125 174840162855964562717405 := by
  unfold tailWord_766125
  simp only [CollatzResearch.WordTrace]
  refine ⟨27942874349467443578107829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18628582899644962385405219 27942874349467443578107829)
  ·
    refine ⟨2619644470262572835447609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27942874349467443578107829 2619644470262572835447609)
    ·
      refine ⟨1964733352696929626585707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2619644470262572835447609 1964733352696929626585707)
      ·
        refine ⟨2947100029045394439878561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1964733352696929626585707 2947100029045394439878561)
        ·
          refine ⟨2210325021784045829908921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2947100029045394439878561 2210325021784045829908921)
          ·
            refine ⟨1657743766338034372431691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2210325021784045829908921 1657743766338034372431691)
            ·
              refine ⟨2486615649507051558647537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1657743766338034372431691 2486615649507051558647537)
              ·
                refine ⟨1864961737130288668985653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2486615649507051558647537 1864961737130288668985653)
                ·
                  refine ⟨174840162855964562717405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1864961737130288668985653 174840162855964562717405)
                  ·
                    rfl

theorem cell21_766125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 2, 5].length) (baseStart_766125 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_766125 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_766125 prefixEnd_766125 := by exact prefixLift 766125
  have htrace : WordTrace (prefixWord ++ tailWord_766125) baseStart_766125 baseEnd_766125 := by
    simpa [prefixWord, tailWord_766125, baseEnd_766125] using wordTrace_append hprefix tailTrace_766125
  have hstable : (prefixWord ++ tailWord_766125).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766125).length < 2 ^ (prefixWord ++ tailWord_766125).sum := by decide
  have hdescent : baseEnd_766125 < baseStart_766125 := by decide
  rcases family_descends (prefixWord ++ tailWord_766125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766156 : List Nat := [2, 2, 1, 6, 1, 1, 1, 1, 6]
def baseStart_766156 : Nat := 118140960795 + 766156 * 2 ^ 59
def prefixEnd_766156 : Nat := 4983230072969 + 3 ^ 40 * 766156 * 2
def baseEnd_766156 : Nat := 174847237478315397700675

theorem tailTrace_766156 : CollatzResearch.WordTrace tailWord_766156 prefixEnd_766156 174847237478315397700675 := by
  unfold tailWord_766156
  simp only [CollatzResearch.WordTrace]
  refine ⟨13972002506177567936243161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18629336674903423914990881 13972002506177567936243161)
  ·
    refine ⟨10479001879633175952182371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13972002506177567936243161 10479001879633175952182371)
    ·
      refine ⟨15718502819449763928273557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10479001879633175952182371 15718502819449763928273557)
      ·
        refine ⟨736804819661707684137823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 15718502819449763928273557 736804819661707684137823)
        ·
          refine ⟨1105207229492561526206735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 736804819661707684137823 1105207229492561526206735)
          ·
            refine ⟨1657810844238842289310103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1105207229492561526206735 1657810844238842289310103)
            ·
              refine ⟨2486716266358263433965155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1657810844238842289310103 2486716266358263433965155)
              ·
                refine ⟨3730074399537395150947733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2486716266358263433965155 3730074399537395150947733)
                ·
                  refine ⟨174847237478315397700675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3730074399537395150947733 174847237478315397700675)
                  ·
                    rfl

theorem cell21_766156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 1, 6].length) (baseStart_766156 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_766156 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_766156 prefixEnd_766156 := by exact prefixLift 766156
  have htrace : WordTrace (prefixWord ++ tailWord_766156) baseStart_766156 baseEnd_766156 := by
    simpa [prefixWord, tailWord_766156, baseEnd_766156] using wordTrace_append hprefix tailTrace_766156
  have hstable : (prefixWord ++ tailWord_766156).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766156).length < 2 ^ (prefixWord ++ tailWord_766156).sum := by decide
  have hdescent : baseEnd_766156 < baseStart_766156 := by decide
  rcases family_descends (prefixWord ++ tailWord_766156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766173 : List Nat := [1, 4, 3, 2, 1, 2, 3, 1, 4]
def baseStart_766173 : Nat := 118140960795 + 766173 * 2 ^ 59
def prefixEnd_766173 : Nat := 4983230072969 + 3 ^ 40 * 766173 * 2
def baseEnd_766173 : Nat := 174851117109927145917307

theorem tailTrace_766173 : CollatzResearch.WordTrace tailWord_766173 prefixEnd_766173 174851117109927145917307 := by
  unfold tailWord_766173
  simp only [CollatzResearch.WordTrace]
  refine ⟨27944625053293547775855173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18629750035529031850570115 27944625053293547775855173)
  ·
    refine ⟨5239617197492540207972845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27944625053293547775855173 5239617197492540207972845)
    ·
      refine ⟨1964856449059702577989817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5239617197492540207972845 1964856449059702577989817)
      ·
        refine ⟨1473642336794776933492363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1964856449059702577989817 1473642336794776933492363)
        ·
          refine ⟨2210463505192165400238545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1473642336794776933492363 2210463505192165400238545)
          ·
            refine ⟨1657847628894124050178909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2210463505192165400238545 1657847628894124050178909)
            ·
              refine ⟨621692860835296518817091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1657847628894124050178909 621692860835296518817091)
              ·
                refine ⟨932539291252944778225637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 621692860835296518817091 932539291252944778225637)
                ·
                  refine ⟨174851117109927145917307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 932539291252944778225637 174851117109927145917307)
                  ·
                    rfl

theorem cell21_766173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 3, 1, 4].length) (baseStart_766173 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_766173 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_766173 prefixEnd_766173 := by exact prefixLift 766173
  have htrace : WordTrace (prefixWord ++ tailWord_766173) baseStart_766173 baseEnd_766173 := by
    simpa [prefixWord, tailWord_766173, baseEnd_766173] using wordTrace_append hprefix tailTrace_766173
  have hstable : (prefixWord ++ tailWord_766173).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766173).length < 2 ^ (prefixWord ++ tailWord_766173).sum := by decide
  have hdescent : baseEnd_766173 < baseStart_766173 := by decide
  rcases family_descends (prefixWord ++ tailWord_766173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766184 : List Nat := [2, 1, 4, 1, 2, 2, 2, 2, 5]
def baseStart_766184 : Nat := 118140960795 + 766184 * 2 ^ 59
def prefixEnd_766184 : Nat := 4983230072969 + 3 ^ 40 * 766184 * 2
def baseEnd_766184 : Nat := 174853627459793571233951

theorem tailTrace_766184 : CollatzResearch.WordTrace tailWord_766184 prefixEnd_766184 174853627459793571233951 := by
  unfold tailWord_766184
  simp only [CollatzResearch.WordTrace]
  refine ⟨13972513128126848327252803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18630017504169131103003737 13972513128126848327252803)
  ·
    refine ⟨20958769692190272490879205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13972513128126848327252803 20958769692190272490879205)
    ·
      refine ⟨3929769317285676092039851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20958769692190272490879205 3929769317285676092039851)
      ·
        refine ⟨5894653975928514138059777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3929769317285676092039851 5894653975928514138059777)
        ·
          refine ⟨4420990481946385603544833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5894653975928514138059777 4420990481946385603544833)
          ·
            refine ⟨3315742861459789202658625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4420990481946385603544833 3315742861459789202658625)
            ·
              refine ⟨2486807146094841901993969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3315742861459789202658625 2486807146094841901993969)
              ·
                refine ⟨1865105359571131426495477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2486807146094841901993969 1865105359571131426495477)
                ·
                  refine ⟨174853627459793571233951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1865105359571131426495477 174853627459793571233951)
                  ·
                    rfl

theorem cell21_766184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 2, 5].length) (baseStart_766184 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_766184 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_766184 prefixEnd_766184 := by exact prefixLift 766184
  have htrace : WordTrace (prefixWord ++ tailWord_766184) baseStart_766184 baseEnd_766184 := by
    simpa [prefixWord, tailWord_766184, baseEnd_766184] using wordTrace_append hprefix tailTrace_766184
  have hstable : (prefixWord ++ tailWord_766184).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766184).length < 2 ^ (prefixWord ++ tailWord_766184).sum := by decide
  have hdescent : baseEnd_766184 < baseStart_766184 := by decide
  rcases family_descends (prefixWord ++ tailWord_766184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766243 : List Nat := [1, 1, 1, 4, 2, 2, 2, 1, 7]
def baseStart_766243 : Nat := 118140960795 + 766243 * 2 ^ 59
def prefixEnd_766243 : Nat := 4983230072969 + 3 ^ 40 * 766243 * 2
def baseEnd_766243 : Nat := 174867092063622579750497

theorem tailTrace_766243 : CollatzResearch.WordTrace tailWord_766243 prefixEnd_766243 174867092063622579750497 := by
  unfold tailWord_766243
  simp only [CollatzResearch.WordTrace]
  refine ⟨27947178163039949730903383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18631452108693299820602255 27947178163039949730903383)
  ·
    refine ⟨41920767244559924596355075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27947178163039949730903383 41920767244559924596355075)
    ·
      refine ⟨62881150866839886894532613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41920767244559924596355075 62881150866839886894532613)
      ·
        refine ⟨11790215787532478792724865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62881150866839886894532613 11790215787532478792724865)
        ·
          refine ⟨8842661840649359094543649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11790215787532478792724865 8842661840649359094543649)
          ·
            refine ⟨6631996380487019320907737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8842661840649359094543649 6631996380487019320907737)
            ·
              refine ⟨4973997285365264490680803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6631996380487019320907737 4973997285365264490680803)
              ·
                refine ⟨7460995928047896736021205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4973997285365264490680803 7460995928047896736021205)
                ·
                  refine ⟨174867092063622579750497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7460995928047896736021205 174867092063622579750497)
                  ·
                    rfl

theorem cell21_766243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 1, 7].length) (baseStart_766243 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_766243 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_766243 prefixEnd_766243 := by exact prefixLift 766243
  have htrace : WordTrace (prefixWord ++ tailWord_766243) baseStart_766243 baseEnd_766243 := by
    simpa [prefixWord, tailWord_766243, baseEnd_766243] using wordTrace_append hprefix tailTrace_766243
  have hstable : (prefixWord ++ tailWord_766243).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766243).length < 2 ^ (prefixWord ++ tailWord_766243).sum := by decide
  have hdescent : baseEnd_766243 < baseStart_766243 := by decide
  rcases family_descends (prefixWord ++ tailWord_766243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766356 : List Nat := [2, 4, 2, 1, 4, 1, 2, 5]
def baseStart_766356 : Nat := 118140960795 + 766356 * 2 ^ 59
def prefixEnd_766356 : Nat := 4983230072969 + 3 ^ 40 * 766356 * 2
def baseEnd_766356 : Nat := 58297626734386498122311

theorem tailTrace_766356 : CollatzResearch.WordTrace tailWord_766356 prefixEnd_766356 58297626734386498122311 := by
  unfold tailWord_766356
  simp only [CollatzResearch.WordTrace]
  refine ⟨13975649805815285014883461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18634199741087046686511281 13975649805815285014883461)
  ·
    refine ⟨2620434338590365940290649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13975649805815285014883461 2620434338590365940290649)
    ·
      refine ⟨1965325753942774455217987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2620434338590365940290649 1965325753942774455217987)
      ·
        refine ⟨2947988630914161682826981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1965325753942774455217987 2947988630914161682826981)
        ·
          refine ⟨552747868296405315530059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2947988630914161682826981 552747868296405315530059)
          ·
            refine ⟨829121802444607973295089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 552747868296405315530059 829121802444607973295089)
            ·
              refine ⟨621841351833455979971317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 829121802444607973295089 621841351833455979971317)
              ·
                refine ⟨58297626734386498122311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 621841351833455979971317 58297626734386498122311)
                ·
                  rfl

theorem cell21_766356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 2, 5].length) (baseStart_766356 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_766356 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_766356 prefixEnd_766356 := by exact prefixLift 766356
  have htrace : WordTrace (prefixWord ++ tailWord_766356) baseStart_766356 baseEnd_766356 := by
    simpa [prefixWord, tailWord_766356, baseEnd_766356] using wordTrace_append hprefix tailTrace_766356
  have hstable : (prefixWord ++ tailWord_766356).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766356).length < 2 ^ (prefixWord ++ tailWord_766356).sum := by decide
  have hdescent : baseEnd_766356 < baseStart_766356 := by decide
  rcases family_descends (prefixWord ++ tailWord_766356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766429 : List Nat := [1, 4, 3, 1, 1, 1, 2, 5, 3]
def baseStart_766429 : Nat := 118140960795 + 766429 * 2 ^ 59
def prefixEnd_766429 : Nat := 4983230072969 + 3 ^ 40 * 766429 * 2
def baseEnd_766429 : Nat := 174909539797727589650117

theorem tailTrace_766429 : CollatzResearch.WordTrace tailWord_766429 prefixEnd_766429 174909539797727589650117 := by
  unfold tailWord_766429
  simp only [CollatzResearch.WordTrace]
  refine ⟨27953962140366103497174341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18635974760244068998116227 27953962140366103497174341)
  ·
    refine ⟨5241367901318644405720189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27953962140366103497174341 5241367901318644405720189)
    ·
      refine ⟨1965512962994491652145071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5241367901318644405720189 1965512962994491652145071)
      ·
        refine ⟨2948269444491737478217607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1965512962994491652145071 2948269444491737478217607)
        ·
          refine ⟨4422404166737606217326411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2948269444491737478217607 4422404166737606217326411)
          ·
            refine ⟨6633606250106409325989617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4422404166737606217326411 6633606250106409325989617)
            ·
              refine ⟨4975204687579806994492213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6633606250106409325989617 4975204687579806994492213)
              ·
                refine ⟨466425439460606905733645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4975204687579806994492213 466425439460606905733645)
                ·
                  refine ⟨174909539797727589650117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 466425439460606905733645 174909539797727589650117)
                  ·
                    rfl

theorem cell21_766429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 5, 3].length) (baseStart_766429 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_766429 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_766429 prefixEnd_766429 := by exact prefixLift 766429
  have htrace : WordTrace (prefixWord ++ tailWord_766429) baseStart_766429 baseEnd_766429 := by
    simpa [prefixWord, tailWord_766429, baseEnd_766429] using wordTrace_append hprefix tailTrace_766429
  have hstable : (prefixWord ++ tailWord_766429).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766429).length < 2 ^ (prefixWord ++ tailWord_766429).sum := by decide
  have hdescent : baseEnd_766429 < baseStart_766429 := by decide
  rcases family_descends (prefixWord ++ tailWord_766429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766440 : List Nat := [2, 1, 4, 1, 1, 12]
def baseStart_766440 : Nat := 118140960795 + 766440 * 2 ^ 59
def prefixEnd_766440 : Nat := 4983230072969 + 3 ^ 40 * 766440 * 2
def baseEnd_766440 : Nat := 6478224079540519072843

theorem tailTrace_766440 : CollatzResearch.WordTrace tailWord_766440 prefixEnd_766440 6478224079540519072843 := by
  unfold tailWord_766440
  simp only [CollatzResearch.WordTrace]
  refine ⟨13977181671663126187912387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18636242228884168250549849 13977181671663126187912387)
  ·
    refine ⟨20965772507494689281868581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13977181671663126187912387 20965772507494689281868581)
    ·
      refine ⟨3931082345155254240350359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20965772507494689281868581 3931082345155254240350359)
      ·
        refine ⟨5896623517732881360525539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3931082345155254240350359 5896623517732881360525539)
        ·
          refine ⟨8844935276599322040788309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5896623517732881360525539 8844935276599322040788309)
          ·
            refine ⟨6478224079540519072843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 8844935276599322040788309 6478224079540519072843)
            ·
              rfl

theorem cell21_766440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 12].length) (baseStart_766440 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_766440 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_766440 prefixEnd_766440 := by exact prefixLift 766440
  have htrace : WordTrace (prefixWord ++ tailWord_766440) baseStart_766440 baseEnd_766440 := by
    simpa [prefixWord, tailWord_766440, baseEnd_766440] using wordTrace_append hprefix tailTrace_766440
  have hstable : (prefixWord ++ tailWord_766440).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766440).length < 2 ^ (prefixWord ++ tailWord_766440).sum := by decide
  have hdescent : baseEnd_766440 < baseStart_766440 := by decide
  rcases family_descends (prefixWord ++ tailWord_766440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766446 : List Nat := [4, 1, 2, 1, 2, 2, 4, 2, 3]
def baseStart_766446 : Nat := 118140960795 + 766446 * 2 ^ 59
def prefixEnd_766446 : Nat := 4983230072969 + 3 ^ 40 * 766446 * 2
def baseEnd_766446 : Nat := 174913419429339337866749

theorem tailTrace_766446 : CollatzResearch.WordTrace tailWord_766446 prefixEnd_766446 174913419429339337866749 := by
  unfold tailWord_766446
  simp only [CollatzResearch.WordTrace]
  refine ⟨3494322772663064425067899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18636388120869676933695461 3494322772663064425067899)
  ·
    refine ⟨5241484158994596637601849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3494322772663064425067899 5241484158994596637601849)
    ·
      refine ⟨3931113119245947478201387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5241484158994596637601849 3931113119245947478201387)
      ·
        refine ⟨5896669678868921217302081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3931113119245947478201387 5896669678868921217302081)
        ·
          refine ⟨4422502259151690912976561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5896669678868921217302081 4422502259151690912976561)
          ·
            refine ⟨3316876694363768184732421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4422502259151690912976561 3316876694363768184732421)
            ·
              refine ⟨621914380193206534637329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3316876694363768184732421 621914380193206534637329)
              ·
                refine ⟨466435785144904900977997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 621914380193206534637329 466435785144904900977997)
                ·
                  refine ⟨174913419429339337866749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 466435785144904900977997 174913419429339337866749)
                  ·
                    rfl

theorem cell21_766446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 4, 2, 3].length) (baseStart_766446 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_766446 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_766446 prefixEnd_766446 := by exact prefixLift 766446
  have htrace : WordTrace (prefixWord ++ tailWord_766446) baseStart_766446 baseEnd_766446 := by
    simpa [prefixWord, tailWord_766446, baseEnd_766446] using wordTrace_append hprefix tailTrace_766446
  have hstable : (prefixWord ++ tailWord_766446).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766446).length < 2 ^ (prefixWord ++ tailWord_766446).sum := by decide
  have hdescent : baseEnd_766446 < baseStart_766446 := by decide
  rcases family_descends (prefixWord ++ tailWord_766446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766519 : List Nat := [1, 1, 3, 1, 2, 3, 5, 1, 4]
def baseStart_766519 : Nat := 118140960795 + 766519 * 2 ^ 59
def prefixEnd_766519 : Nat := 4983230072969 + 3 ^ 40 * 766519 * 2
def baseEnd_766519 : Nat := 174930079023907433149933

theorem tailTrace_766519 : CollatzResearch.WordTrace tailWord_766519 prefixEnd_766519 174930079023907433149933 := by
  unfold tailWord_766519
  simp only [CollatzResearch.WordTrace]
  refine ⟨27957244710040048867950611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18638163140026699245300407 27957244710040048867950611)
  ·
    refine ⟨41935867065060073301925917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27957244710040048867950611 41935867065060073301925917)
    ·
      refine ⟨15725950149397527488222219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41935867065060073301925917 15725950149397527488222219)
      ·
        refine ⟨23588925224096291232333329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15725950149397527488222219 23588925224096291232333329)
        ·
          refine ⟨17691693918072218424249997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23588925224096291232333329 17691693918072218424249997)
          ·
            refine ⟨6634385219277081909093749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17691693918072218424249997 6634385219277081909093749)
            ·
              refine ⟨621973614307226428977539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6634385219277081909093749 621973614307226428977539)
              ·
                refine ⟨932960421460839643466309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 621973614307226428977539 932960421460839643466309)
                ·
                  refine ⟨174930079023907433149933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 932960421460839643466309 174930079023907433149933)
                  ·
                    rfl

theorem cell21_766519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 5, 1, 4].length) (baseStart_766519 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_766519 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_766519 prefixEnd_766519 := by exact prefixLift 766519
  have htrace : WordTrace (prefixWord ++ tailWord_766519) baseStart_766519 baseEnd_766519 := by
    simpa [prefixWord, tailWord_766519, baseEnd_766519] using wordTrace_append hprefix tailTrace_766519
  have hstable : (prefixWord ++ tailWord_766519).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766519).length < 2 ^ (prefixWord ++ tailWord_766519).sum := by decide
  have hdescent : baseEnd_766519 < baseStart_766519 := by decide
  rcases family_descends (prefixWord ++ tailWord_766519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766533 : List Nat := [1, 3, 1, 1, 1, 5, 4, 5]
def baseStart_766533 : Nat := 118140960795 + 766533 * 2 ^ 59
def prefixEnd_766533 : Nat := 4983230072969 + 3 ^ 40 * 766533 * 2
def baseEnd_766533 : Nat := 58311091338215506638857

theorem tailTrace_766533 : CollatzResearch.WordTrace tailWord_766533 prefixEnd_766533 58311091338215506638857 := by
  unfold tailWord_766533
  simp only [CollatzResearch.WordTrace]
  refine ⟨27957755331989329258960253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18638503554659552839306835 27957755331989329258960253)
  ·
    refine ⟨10484158249495998472110095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27957755331989329258960253 10484158249495998472110095)
    ·
      refine ⟨15726237374243997708165143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10484158249495998472110095 15726237374243997708165143)
      ·
        refine ⟨23589356061365996562247715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15726237374243997708165143 23589356061365996562247715)
        ·
          refine ⟨35384034092048994843371573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23589356061365996562247715 35384034092048994843371573)
          ·
            refine ⟨3317253196129593266566085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35384034092048994843371573 3317253196129593266566085)
            ·
              refine ⟨621984974274298737481141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3317253196129593266566085 621984974274298737481141)
              ·
                refine ⟨58311091338215506638857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 621984974274298737481141 58311091338215506638857)
                ·
                  rfl

theorem cell21_766533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 4, 5].length) (baseStart_766533 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_766533 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_766533 prefixEnd_766533 := by exact prefixLift 766533
  have htrace : WordTrace (prefixWord ++ tailWord_766533) baseStart_766533 baseEnd_766533 := by
    simpa [prefixWord, tailWord_766533, baseEnd_766533] using wordTrace_append hprefix tailTrace_766533
  have hstable : (prefixWord ++ tailWord_766533).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766533).length < 2 ^ (prefixWord ++ tailWord_766533).sum := by decide
  have hdescent : baseEnd_766533 < baseStart_766533 := by decide
  rcases family_descends (prefixWord ++ tailWord_766533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766592 : List Nat := [2, 1, 1, 2, 1, 5, 2, 7]
def baseStart_766592 : Nat := 118140960795 + 766592 * 2 ^ 59
def prefixEnd_766592 : Nat := 4983230072969 + 3 ^ 40 * 766592 * 2
def baseEnd_766592 : Nat := 58315579539491842811039

theorem tailTrace_766592 : CollatzResearch.WordTrace tailWord_766592 prefixEnd_766592 58315579539491842811039 := by
  unfold tailWord_766592
  simp only [CollatzResearch.WordTrace]
  refine ⟨13979953619387791167679015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18639938159183721556905353 13979953619387791167679015)
  ·
    refine ⟨20969930429081686751518523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13979953619387791167679015 20969930429081686751518523)
    ·
      refine ⟨31454895643622530127277785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20969930429081686751518523 31454895643622530127277785)
      ·
        refine ⟨23591171732716897595458339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31454895643622530127277785 23591171732716897595458339)
        ·
          refine ⟨35386757599075346393187509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23591171732716897595458339 35386757599075346393187509)
          ·
            refine ⟨3317508524913313724361329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35386757599075346393187509 3317508524913313724361329)
            ·
              refine ⟨2488131393684985293270997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3317508524913313724361329 2488131393684985293270997)
              ·
                refine ⟨58315579539491842811039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2488131393684985293270997 58315579539491842811039)
                ·
                  rfl

theorem cell21_766592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 7].length) (baseStart_766592 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_766592 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_766592 prefixEnd_766592 := by exact prefixLift 766592
  have htrace : WordTrace (prefixWord ++ tailWord_766592) baseStart_766592 baseEnd_766592 := by
    simpa [prefixWord, tailWord_766592, baseEnd_766592] using wordTrace_append hprefix tailTrace_766592
  have hstable : (prefixWord ++ tailWord_766592).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766592).length < 2 ^ (prefixWord ++ tailWord_766592).sum := by decide
  have hdescent : baseEnd_766592 < baseStart_766592 := by decide
  rcases family_descends (prefixWord ++ tailWord_766592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766612 : List Nat := [2, 4, 2, 2, 1, 2, 2, 2, 4]
def baseStart_766612 : Nat := 118140960795 + 766612 * 2 ^ 59
def prefixEnd_766612 : Nat := 4983230072969 + 3 ^ 40 * 766612 * 2
def baseEnd_766612 : Nat := 174951302890959938099743

theorem tailTrace_766612 : CollatzResearch.WordTrace tailWord_766612 prefixEnd_766612 174951302890959938099743 := by
  unfold tailWord_766612
  simp only [CollatzResearch.WordTrace]
  refine ⟨13980318349351562875543045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18640424465802083834057393 13980318349351562875543045)
  ·
    refine ⟨2621309690503418039164321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13980318349351562875543045 2621309690503418039164321)
    ·
      refine ⟨1965982267877563529373241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2621309690503418039164321 1965982267877563529373241)
      ·
        refine ⟨1474486700908172647029931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1965982267877563529373241 1474486700908172647029931)
        ·
          refine ⟨2211730051362258970544897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1474486700908172647029931 2211730051362258970544897)
          ·
            refine ⟨1658797538521694227908673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2211730051362258970544897 1658797538521694227908673)
            ·
              refine ⟨1244098153891270670931505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1658797538521694227908673 1244098153891270670931505)
              ·
                refine ⟨933073615418453003198629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1244098153891270670931505 933073615418453003198629)
                ·
                  refine ⟨174951302890959938099743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 933073615418453003198629 174951302890959938099743)
                  ·
                    rfl

theorem cell21_766612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 2, 4].length) (baseStart_766612 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_766612 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_766612 prefixEnd_766612 := by exact prefixLift 766612
  have htrace : WordTrace (prefixWord ++ tailWord_766612) baseStart_766612 baseEnd_766612 := by
    simpa [prefixWord, tailWord_766612, baseEnd_766612] using wordTrace_append hprefix tailTrace_766612
  have hstable : (prefixWord ++ tailWord_766612).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766612).length < 2 ^ (prefixWord ++ tailWord_766612).sum := by decide
  have hdescent : baseEnd_766612 < baseStart_766612 := by decide
  rcases family_descends (prefixWord ++ tailWord_766612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766654 : List Nat := [4, 2, 1, 1, 2, 1, 2, 2, 6]
def baseStart_766654 : Nat := 118140960795 + 766654 * 2 ^ 59
def prefixEnd_766654 : Nat := 4983230072969 + 3 ^ 40 * 766654 * 2
def baseEnd_766654 : Nat := 174960887863177198399657

theorem tailTrace_766654 : CollatzResearch.WordTrace tailWord_766654 prefixEnd_766654 174960887863177198399657 := by
  unfold tailWord_766654
  simp only [CollatzResearch.WordTrace]
  refine ⟨3495271070568870865514377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18641445709700644616076677 3495271070568870865514377)
  ·
    refine ⟨2621453302926653149135783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3495271070568870865514377 2621453302926653149135783)
    ·
      refine ⟨3932179954389979723703675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2621453302926653149135783 3932179954389979723703675)
      ·
        refine ⟨5898269931584969585555513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3932179954389979723703675 5898269931584969585555513)
        ·
          refine ⟨4423702448688727189166635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5898269931584969585555513 4423702448688727189166635)
          ·
            refine ⟨6635553673033090783749953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4423702448688727189166635 6635553673033090783749953)
            ·
              refine ⟨4976665254774818087812465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6635553673033090783749953 4976665254774818087812465)
              ·
                refine ⟨3732498941081113565859349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4976665254774818087812465 3732498941081113565859349)
                ·
                  refine ⟨174960887863177198399657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3732498941081113565859349 174960887863177198399657)
                  ·
                    rfl

theorem cell21_766654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_766654 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_766654 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_766654 prefixEnd_766654 := by exact prefixLift 766654
  have htrace : WordTrace (prefixWord ++ tailWord_766654) baseStart_766654 baseEnd_766654 := by
    simpa [prefixWord, tailWord_766654, baseEnd_766654] using wordTrace_append hprefix tailTrace_766654
  have hstable : (prefixWord ++ tailWord_766654).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766654).length < 2 ^ (prefixWord ++ tailWord_766654).sum := by decide
  have hdescent : baseEnd_766654 < baseStart_766654 := by decide
  rcases family_descends (prefixWord ++ tailWord_766654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766702 : List Nat := [4, 1, 2, 1, 1, 5, 2, 5]
def baseStart_766702 : Nat := 118140960795 + 766702 * 2 ^ 59
def prefixEnd_766702 : Nat := 4983230072969 + 3 ^ 40 * 766702 * 2
def baseEnd_766702 : Nat := 58323947372379927199853

theorem tailTrace_766702 : CollatzResearch.WordTrace tailWord_766702 prefixEnd_766702 58323947372379927199853 := by
  unfold tailWord_766702
  simp only [CollatzResearch.WordTrace]
  refine ⟨3495489908547133890232795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18642612845584714081241573 3495489908547133890232795)
  ·
    refine ⟨5243234862820700835349193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3495489908547133890232795 5243234862820700835349193)
    ·
      refine ⟨3932426147115525626511895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5243234862820700835349193 3932426147115525626511895)
      ·
        refine ⟨5898639220673288439767843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3932426147115525626511895 5898639220673288439767843)
        ·
          refine ⟨8847958831009932659651765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5898639220673288439767843 8847958831009932659651765)
          ·
            refine ⟨829496140407181186842353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8847958831009932659651765 829496140407181186842353)
            ·
              refine ⟨622122105305385890131765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 829496140407181186842353 622122105305385890131765)
              ·
                refine ⟨58323947372379927199853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 622122105305385890131765 58323947372379927199853)
                ·
                  rfl

theorem cell21_766702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 2, 5].length) (baseStart_766702 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_766702 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_766702 prefixEnd_766702 := by exact prefixLift 766702
  have htrace : WordTrace (prefixWord ++ tailWord_766702) baseStart_766702 baseEnd_766702 := by
    simpa [prefixWord, tailWord_766702, baseEnd_766702] using wordTrace_append hprefix tailTrace_766702
  have hstable : (prefixWord ++ tailWord_766702).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766702).length < 2 ^ (prefixWord ++ tailWord_766702).sum := by decide
  have hdescent : baseEnd_766702 < baseStart_766702 := by decide
  rcases family_descends (prefixWord ++ tailWord_766702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766708 : List Nat := [2, 6, 1, 1, 2, 2, 1, 3, 3]
def baseStart_766708 : Nat := 118140960795 + 766708 * 2 ^ 59
def prefixEnd_766708 : Nat := 4983230072969 + 3 ^ 40 * 766708 * 2
def baseEnd_766708 : Nat := 174973211398885104499547

theorem tailTrace_766708 : CollatzResearch.WordTrace tailWord_766708 prefixEnd_766708 174973211398885104499547 := by
  unfold tailWord_766708
  simp only [CollatzResearch.WordTrace]
  refine ⟨13982069053177667073290389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18642758737570222764387185 13982069053177667073290389)
  ·
    refine ⟨655409486867703144060487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 13982069053177667073290389 655409486867703144060487)
    ·
      refine ⟨983114230301554716090731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 655409486867703144060487 983114230301554716090731)
      ·
        refine ⟨1474671345452332074136097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 983114230301554716090731 1474671345452332074136097)
        ·
          refine ⟨1106003509089249055602073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1474671345452332074136097 1106003509089249055602073)
          ·
            refine ⟨829502631816936791701555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1106003509089249055602073 829502631816936791701555)
            ·
              refine ⟨1244253947725405187552333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 829502631816936791701555 1244253947725405187552333)
              ·
                refine ⟨466595230397026945332125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1244253947725405187552333 466595230397026945332125)
                ·
                  refine ⟨174973211398885104499547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 466595230397026945332125 174973211398885104499547)
                  ·
                    rfl

theorem cell21_766708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_766708 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_766708 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_766708 prefixEnd_766708 := by exact prefixLift 766708
  have htrace : WordTrace (prefixWord ++ tailWord_766708) baseStart_766708 baseEnd_766708 := by
    simpa [prefixWord, tailWord_766708, baseEnd_766708] using wordTrace_append hprefix tailTrace_766708
  have hstable : (prefixWord ++ tailWord_766708).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766708).length < 2 ^ (prefixWord ++ tailWord_766708).sum := by decide
  have hdescent : baseEnd_766708 < baseStart_766708 := by decide
  rcases family_descends (prefixWord ++ tailWord_766708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766730 : List Nat := [3, 1, 2, 2, 1, 2, 2, 4, 4]
def baseStart_766730 : Nat := 118140960795 + 766730 * 2 ^ 59
def prefixEnd_766730 : Nat := 4983230072969 + 3 ^ 40 * 766730 * 2
def baseEnd_766730 : Nat := 174978232098617955132835

theorem tailTrace_766730 : CollatzResearch.WordTrace tailWord_766730 prefixEnd_766730 174978232098617955132835 := by
  unfold tailWord_766730
  simp only [CollatzResearch.WordTrace]
  refine ⟨6991235128068907975970411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18643293674850421269254429 6991235128068907975970411)
  ·
    refine ⟨10486852692103361963955617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6991235128068907975970411 10486852692103361963955617)
    ·
      refine ⟨7865139519077521472966713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10486852692103361963955617 7865139519077521472966713)
      ·
        refine ⟨5898854639308141104725035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7865139519077521472966713 5898854639308141104725035)
        ·
          refine ⟨8848281958962211657087553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5898854639308141104725035 8848281958962211657087553)
          ·
            refine ⟨6636211469221658742815665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8848281958962211657087553 6636211469221658742815665)
            ·
              refine ⟨4977158601916244057111749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6636211469221658742815665 4977158601916244057111749)
              ·
                refine ⟨933217237859295760708453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4977158601916244057111749 933217237859295760708453)
                ·
                  refine ⟨174978232098617955132835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 933217237859295760708453 174978232098617955132835)
                  ·
                    rfl

theorem cell21_766730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 4, 4].length) (baseStart_766730 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_766730 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_766730 prefixEnd_766730 := by exact prefixLift 766730
  have htrace : WordTrace (prefixWord ++ tailWord_766730) baseStart_766730 baseEnd_766730 := by
    simpa [prefixWord, tailWord_766730, baseEnd_766730] using wordTrace_append hprefix tailTrace_766730
  have hstable : (prefixWord ++ tailWord_766730).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766730).length < 2 ^ (prefixWord ++ tailWord_766730).sum := by decide
  have hdescent : baseEnd_766730 < baseStart_766730 := by decide
  rcases family_descends (prefixWord ++ tailWord_766730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766792 : List Nat := [2, 1, 3, 1, 1, 3, 3, 4, 3]
def baseStart_766792 : Nat := 118140960795 + 766792 * 2 ^ 59
def prefixEnd_766792 : Nat := 4983230072969 + 3 ^ 40 * 766792 * 2
def baseEnd_766792 : Nat := 174992381343319625099375

theorem tailTrace_766792 : CollatzResearch.WordTrace tailWord_766792 prefixEnd_766792 174992381343319625099375 := by
  unfold tailWord_766792
  simp only [CollatzResearch.WordTrace]
  refine ⟨13983600919025508246319315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18644801225367344328425753 13983600919025508246319315)
  ·
    refine ⟨20975401378538262369478973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13983600919025508246319315 20975401378538262369478973)
    ·
      refine ⟨7865775516951848388554615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20975401378538262369478973 7865775516951848388554615)
      ·
        refine ⟨11798663275427772582831923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7865775516951848388554615 11798663275427772582831923)
        ·
          refine ⟨17697994913141658874247885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11798663275427772582831923 17697994913141658874247885)
          ·
            refine ⟨6636748092428122077842957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17697994913141658874247885 6636748092428122077842957)
            ·
              refine ⟨2488780534660545779191109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6636748092428122077842957 2488780534660545779191109)
              ·
                refine ⟨466646350248852333598333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2488780534660545779191109 466646350248852333598333)
                ·
                  refine ⟨174992381343319625099375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 466646350248852333598333 174992381343319625099375)
                  ·
                    rfl

theorem cell21_766792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 4, 3].length) (baseStart_766792 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_766792 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_766792 prefixEnd_766792 := by exact prefixLift 766792
  have htrace : WordTrace (prefixWord ++ tailWord_766792) baseStart_766792 baseEnd_766792 := by
    simpa [prefixWord, tailWord_766792, baseEnd_766792] using wordTrace_append hprefix tailTrace_766792
  have hstable : (prefixWord ++ tailWord_766792).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766792).length < 2 ^ (prefixWord ++ tailWord_766792).sum := by decide
  have hdescent : baseEnd_766792 < baseStart_766792 := by decide
  rcases family_descends (prefixWord ++ tailWord_766792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766851 : List Nat := [1, 1, 1, 3, 4, 1, 4, 1, 5]
def baseStart_766851 : Nat := 118140960795 + 766851 * 2 ^ 59
def prefixEnd_766851 : Nat := 4983230072969 + 3 ^ 40 * 766851 * 2
def baseEnd_766851 : Nat := 175005845947148633615921

theorem tailTrace_766851 : CollatzResearch.WordTrace tailWord_766851 prefixEnd_766851 175005845947148633615921 := by
  unfold tailWord_766851
  simp only [CollatzResearch.WordTrace]
  refine ⟨27969353744837269569036407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18646235829891513046024271 27969353744837269569036407)
  ·
    refine ⟨41954030617255904353554611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27969353744837269569036407 41954030617255904353554611)
    ·
      refine ⟨62931045925883856530331917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41954030617255904353554611 62931045925883856530331917)
      ·
        refine ⟨23599142222206446198874469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62931045925883856530331917 23599142222206446198874469)
        ·
          refine ⟨4424839166663708662288963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23599142222206446198874469 4424839166663708662288963)
          ·
            refine ⟨6637258749995562993433445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4424839166663708662288963 6637258749995562993433445)
            ·
              refine ⟨1244486015624168061268771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6637258749995562993433445 1244486015624168061268771)
              ·
                refine ⟨1866729023436252091903157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1244486015624168061268771 1866729023436252091903157)
                ·
                  refine ⟨175005845947148633615921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1866729023436252091903157 175005845947148633615921)
                  ·
                    rfl

theorem cell21_766851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4, 1, 5].length) (baseStart_766851 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_766851 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_766851 prefixEnd_766851 := by exact prefixLift 766851
  have htrace : WordTrace (prefixWord ++ tailWord_766851) baseStart_766851 baseEnd_766851 := by
    simpa [prefixWord, tailWord_766851, baseEnd_766851] using wordTrace_append hprefix tailTrace_766851
  have hstable : (prefixWord ++ tailWord_766851).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766851).length < 2 ^ (prefixWord ++ tailWord_766851).sum := by decide
  have hdescent : baseEnd_766851 < baseStart_766851 := by decide
  rcases family_descends (prefixWord ++ tailWord_766851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766882 : List Nat := [3, 3, 1, 2, 2, 1, 1, 2, 6]
def baseStart_766882 : Nat := 118140960795 + 766882 * 2 ^ 59
def prefixEnd_766882 : Nat := 4983230072969 + 3 ^ 40 * 766882 * 2
def baseEnd_766882 : Nat := 175012920569499468599191

theorem tailTrace_766882 : CollatzResearch.WordTrace tailWord_766882 prefixEnd_766882 175012920569499468599191 := by
  unfold tailWord_766882
  simp only [CollatzResearch.WordTrace]
  refine ⟨6992621101931240465853725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18646989605149974575609933 6992621101931240465853725)
  ·
    refine ⟨2622232913224215174695147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6992621101931240465853725 2622232913224215174695147)
    ·
      refine ⟨3933349369836322762042721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2622232913224215174695147 3933349369836322762042721)
      ·
        refine ⟨2950012027377242071532041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3933349369836322762042721 2950012027377242071532041)
        ·
          refine ⟨2212509020532931553649031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2950012027377242071532041 2212509020532931553649031)
          ·
            refine ⟨3318763530799397330473547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2212509020532931553649031 3318763530799397330473547)
            ·
              refine ⟨4978145296199095995710321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3318763530799397330473547 4978145296199095995710321)
              ·
                refine ⟨3733608972149321996782741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4978145296199095995710321 3733608972149321996782741)
                ·
                  refine ⟨175012920569499468599191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3733608972149321996782741 175012920569499468599191)
                  ·
                    rfl

theorem cell21_766882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_766882 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_766882 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_766882 prefixEnd_766882 := by exact prefixLift 766882
  have htrace : WordTrace (prefixWord ++ tailWord_766882) baseStart_766882 baseEnd_766882 := by
    simpa [prefixWord, tailWord_766882, baseEnd_766882] using wordTrace_append hprefix tailTrace_766882
  have hstable : (prefixWord ++ tailWord_766882).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766882).length < 2 ^ (prefixWord ++ tailWord_766882).sum := by decide
  have hdescent : baseEnd_766882 < baseStart_766882 := by decide
  rcases family_descends (prefixWord ++ tailWord_766882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766916 : List Nat := [2, 3, 3, 3, 1, 1, 1, 3, 4]
def baseStart_766916 : Nat := 118140960795 + 766916 * 2 ^ 59
def prefixEnd_766916 : Nat := 4983230072969 + 3 ^ 40 * 766916 * 2
def baseEnd_766916 : Nat := 175020679832722965032455

theorem tailTrace_766916 : CollatzResearch.WordTrace tailWord_766916 prefixEnd_766916 175020679832722965032455 := by
  unfold tailWord_766916
  simp only [CollatzResearch.WordTrace]
  refine ⟨13985862244800892835076301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18647816326401190446768401 13985862244800892835076301)
  ·
    refine ⟨5244698341800334813153613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13985862244800892835076301 5244698341800334813153613)
    ·
      refine ⟨1966761878175125554932605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5244698341800334813153613 1966761878175125554932605)
      ·
        refine ⟨737535704315672083099727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1966761878175125554932605 737535704315672083099727)
        ·
          refine ⟨1106303556473508124649591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 737535704315672083099727 1106303556473508124649591)
          ·
            refine ⟨1659455334710262186974387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1106303556473508124649591 1659455334710262186974387)
            ·
              refine ⟨2489183002065393280461581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1659455334710262186974387 2489183002065393280461581)
              ·
                refine ⟨933443625774522480173093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2489183002065393280461581 933443625774522480173093)
                ·
                  refine ⟨175020679832722965032455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 933443625774522480173093 175020679832722965032455)
                  ·
                    rfl

theorem cell21_766916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 3, 4].length) (baseStart_766916 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_766916 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_766916 prefixEnd_766916 := by exact prefixLift 766916
  have htrace : WordTrace (prefixWord ++ tailWord_766916) baseStart_766916 baseEnd_766916 := by
    simpa [prefixWord, tailWord_766916, baseEnd_766916] using wordTrace_append hprefix tailTrace_766916
  have hstable : (prefixWord ++ tailWord_766916).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766916).length < 2 ^ (prefixWord ++ tailWord_766916).sum := by decide
  have hdescent : baseEnd_766916 < baseStart_766916 := by decide
  rcases family_descends (prefixWord ++ tailWord_766916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766961 : List Nat := [1, 2, 2, 2, 4, 1, 4, 2, 3]
def baseStart_766961 : Nat := 118140960795 + 766961 * 2 ^ 59
def prefixEnd_766961 : Nat := 4983230072969 + 3 ^ 40 * 766961 * 2
def baseEnd_766961 : Nat := 175030949445812886782363

theorem tailTrace_766961 : CollatzResearch.WordTrace tailWord_766961 prefixEnd_766961 175030949445812886782363 := by
  unfold tailWord_766961
  simp only [CollatzResearch.WordTrace]
  refine ⟨27973365774438758355540737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18648910516292505570360491 27973365774438758355540737)
  ·
    refine ⟨20980024330829068766655553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27973365774438758355540737 20980024330829068766655553)
    ·
      refine ⟨15735018248121801574991665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20980024330829068766655553 15735018248121801574991665)
      ·
        refine ⟨11801263686091351181243749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15735018248121801574991665 11801263686091351181243749)
        ·
          refine ⟨2212736941142128346483203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11801263686091351181243749 2212736941142128346483203)
          ·
            refine ⟨3319105411713192519724805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2212736941142128346483203 3319105411713192519724805)
            ·
              refine ⟨622332264696223597448401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3319105411713192519724805 622332264696223597448401)
              ·
                refine ⟨466749198522167698086301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 622332264696223597448401 466749198522167698086301)
                ·
                  refine ⟨175030949445812886782363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 466749198522167698086301 175030949445812886782363)
                  ·
                    rfl

theorem cell21_766961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 4, 2, 3].length) (baseStart_766961 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_766961 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_766961 prefixEnd_766961 := by exact prefixLift 766961
  have htrace : WordTrace (prefixWord ++ tailWord_766961) baseStart_766961 baseEnd_766961 := by
    simpa [prefixWord, tailWord_766961, baseEnd_766961] using wordTrace_append hprefix tailTrace_766961
  have hstable : (prefixWord ++ tailWord_766961).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766961).length < 2 ^ (prefixWord ++ tailWord_766961).sum := by decide
  have hdescent : baseEnd_766961 < baseStart_766961 := by decide
  rcases family_descends (prefixWord ++ tailWord_766961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766972 : List Nat := [2, 2, 2, 1, 2, 3, 3, 6]
def baseStart_766972 : Nat := 118140960795 + 766972 * 2 ^ 59
def prefixEnd_766972 : Nat := 4983230072969 + 3 ^ 40 * 766972 * 2
def baseEnd_766972 : Nat := 58344486598559770699669

theorem tailTrace_766972 : CollatzResearch.WordTrace tailWord_766972 prefixEnd_766972 58344486598559770699669 := by
  unfold tailWord_766972
  simp only [CollatzResearch.WordTrace]
  refine ⟨13986883488699453617095585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18649177984932604822794113 13986883488699453617095585)
  ·
    refine ⟨10490162616524590212821689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13986883488699453617095585 10490162616524590212821689)
    ·
      refine ⟨7867621962393442659616267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10490162616524590212821689 7867621962393442659616267)
      ·
        refine ⟨11801432943590163989424401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7867621962393442659616267 11801432943590163989424401)
        ·
          refine ⟨8851074707692622992068301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11801432943590163989424401 8851074707692622992068301)
          ·
            refine ⟨3319153015384733622025613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8851074707692622992068301 3319153015384733622025613)
            ·
              refine ⟨1244682380769275108259605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3319153015384733622025613 1244682380769275108259605)
              ·
                refine ⟨58344486598559770699669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1244682380769275108259605 58344486598559770699669)
                ·
                  rfl

theorem cell21_766972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 6].length) (baseStart_766972 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_766972 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_766972 prefixEnd_766972 := by exact prefixLift 766972
  have htrace : WordTrace (prefixWord ++ tailWord_766972) baseStart_766972 baseEnd_766972 := by
    simpa [prefixWord, tailWord_766972, baseEnd_766972] using wordTrace_append hprefix tailTrace_766972
  have hstable : (prefixWord ++ tailWord_766972).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766972).length < 2 ^ (prefixWord ++ tailWord_766972).sum := by decide
  have hdescent : baseEnd_766972 < baseStart_766972 := by decide
  rcases family_descends (prefixWord ++ tailWord_766972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767031 : List Nat := [1, 1, 3, 1, 2, 2, 1, 10]
def baseStart_767031 : Nat := 118140960795 + 767031 * 2 ^ 59
def prefixEnd_767031 : Nat := 4983230072969 + 3 ^ 40 * 767031 * 2
def baseEnd_767031 : Nat := 58348974799836106871851

theorem tailTrace_767031 : CollatzResearch.WordTrace tailWord_767031 prefixEnd_767031 58348974799836106871851 := by
  unfold tailWord_767031
  simp only [CollatzResearch.WordTrace]
  refine ⟨27975918884185160310588947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18650612589456773540392631 27975918884185160310588947)
  ·
    refine ⟨41963878326277740465883421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27975918884185160310588947 41963878326277740465883421)
    ·
      refine ⟨15736454372354152674706283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41963878326277740465883421 15736454372354152674706283)
      ·
        refine ⟨23604681558531229012059425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15736454372354152674706283 23604681558531229012059425)
        ·
          refine ⟨17703511168898421759044569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23604681558531229012059425 17703511168898421759044569)
          ·
            refine ⟨13277633376673816319283427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17703511168898421759044569 13277633376673816319283427)
            ·
              refine ⟨19916450065010724478925141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13277633376673816319283427 19916450065010724478925141)
              ·
                refine ⟨58348974799836106871851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 19916450065010724478925141 58348974799836106871851)
                ·
                  rfl

theorem cell21_767031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 10].length) (baseStart_767031 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_767031 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_767031 prefixEnd_767031 := by exact prefixLift 767031
  have htrace : WordTrace (prefixWord ++ tailWord_767031) baseStart_767031 baseEnd_767031 := by
    simpa [prefixWord, tailWord_767031, baseEnd_767031] using wordTrace_append hprefix tailTrace_767031
  have hstable : (prefixWord ++ tailWord_767031).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767031).length < 2 ^ (prefixWord ++ tailWord_767031).sum := by decide
  have hdescent : baseEnd_767031 < baseStart_767031 := by decide
  rcases family_descends (prefixWord ++ tailWord_767031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767079 : List Nat := [1, 1, 5, 1, 1, 3, 3, 1, 5]
def baseStart_767079 : Nat := 118140960795 + 767079 * 2 ^ 59
def prefixEnd_767079 : Nat := 4983230072969 + 3 ^ 40 * 767079 * 2
def baseEnd_767079 : Nat := 175057878653470903815455

theorem tailTrace_767079 : CollatzResearch.WordTrace tailWord_767079 prefixEnd_767079 175057878653470903815455 := by
  unfold tailWord_767079
  simp only [CollatzResearch.WordTrace]
  refine ⟨27977669588011264508336291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18651779725340843005557527 27977669588011264508336291)
  ·
    refine ⟨41966504382016896762504437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27977669588011264508336291 41966504382016896762504437)
    ·
      refine ⟨3934359785814084071484791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41966504382016896762504437 3934359785814084071484791)
      ·
        refine ⟨5901539678721126107227187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3934359785814084071484791 5901539678721126107227187)
        ·
          refine ⟨8852309518081689160840781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5901539678721126107227187 8852309518081689160840781)
          ·
            refine ⟨3319616069280633435315293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8852309518081689160840781 3319616069280633435315293)
            ·
              refine ⟨1244856025980237538243235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3319616069280633435315293 1244856025980237538243235)
              ·
                refine ⟨1867284038970356307364853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1244856025980237538243235 1867284038970356307364853)
                ·
                  refine ⟨175057878653470903815455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1867284038970356307364853 175057878653470903815455)
                  ·
                    rfl

theorem cell21_767079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3, 1, 5].length) (baseStart_767079 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_767079 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_767079 prefixEnd_767079 := by exact prefixLift 767079
  have htrace : WordTrace (prefixWord ++ tailWord_767079) baseStart_767079 baseEnd_767079 := by
    simpa [prefixWord, tailWord_767079, baseEnd_767079] using wordTrace_append hprefix tailTrace_767079
  have hstable : (prefixWord ++ tailWord_767079).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767079).length < 2 ^ (prefixWord ++ tailWord_767079).sum := by decide
  have hdescent : baseEnd_767079 < baseStart_767079 := by decide
  rcases family_descends (prefixWord ++ tailWord_767079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767107 : List Nat := [1, 1, 1, 3, 3, 2, 1, 9]
def baseStart_767107 : Nat := 118140960795 + 767107 * 2 ^ 59
def prefixEnd_767107 : Nat := 4983230072969 + 3 ^ 40 * 767107 * 2
def baseEnd_767107 : Nat := 58354756211649692449577

theorem tailTrace_767107 : CollatzResearch.WordTrace tailWord_767107 prefixEnd_767107 58354756211649692449577 := by
  unfold tailWord_767107
  simp only [CollatzResearch.WordTrace]
  refine ⟨27978690831909825290355575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18652460554606550193570383 27978690831909825290355575)
  ·
    refine ⟨41968036247864737935533363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27978690831909825290355575 41968036247864737935533363)
    ·
      refine ⟨62952054371797106903300045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41968036247864737935533363 62952054371797106903300045)
      ·
        refine ⟨23607020389423915088737517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62952054371797106903300045 23607020389423915088737517)
        ·
          refine ⟨8852632646033968158276569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23607020389423915088737517 8852632646033968158276569)
          ·
            refine ⟨6639474484525476118707427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8852632646033968158276569 6639474484525476118707427)
            ·
              refine ⟨9959211726788214178061141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6639474484525476118707427 9959211726788214178061141)
              ·
                refine ⟨58354756211649692449577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9959211726788214178061141 58354756211649692449577)
                ·
                  rfl

theorem cell21_767107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 9].length) (baseStart_767107 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_767107 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_767107 prefixEnd_767107 := by exact prefixLift 767107
  have htrace : WordTrace (prefixWord ++ tailWord_767107) baseStart_767107 baseEnd_767107 := by
    simpa [prefixWord, tailWord_767107, baseEnd_767107] using wordTrace_append hprefix tailTrace_767107
  have hstable : (prefixWord ++ tailWord_767107).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767107).length < 2 ^ (prefixWord ++ tailWord_767107).sum := by decide
  have hdescent : baseEnd_767107 < baseStart_767107 := by decide
  rcases family_descends (prefixWord ++ tailWord_767107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767130 : List Nat := [3, 1, 1, 5, 1, 3, 2, 2, 3]
def baseStart_767130 : Nat := 118140960795 + 767130 * 2 ^ 59
def prefixEnd_767130 : Nat := 4983230072969 + 3 ^ 40 * 767130 * 2
def baseEnd_767130 : Nat := 175069517548306148465351

theorem tailTrace_767130 : CollatzResearch.WordTrace tailWord_767130 prefixEnd_767130 175069517548306148465351 := by
  unfold tailWord_767130
  simp only [CollatzResearch.WordTrace]
  refine ⟨6994882427706625054610711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18653019807217666812295229 6994882427706625054610711)
  ·
    refine ⟨10492323641559937581916067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6994882427706625054610711 10492323641559937581916067)
    ·
      refine ⟨15738485462339906372874101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10492323641559937581916067 15738485462339906372874101)
      ·
        refine ⟨1475483012094366222456947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15738485462339906372874101 1475483012094366222456947)
        ·
          refine ⟨2213224518141549333685421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1475483012094366222456947 2213224518141549333685421)
          ·
            refine ⟨829959194303081000132033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2213224518141549333685421 829959194303081000132033)
            ·
              refine ⟨622469395727310750099025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 829959194303081000132033 622469395727310750099025)
              ·
                refine ⟨466852046795483062574269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 622469395727310750099025 466852046795483062574269)
                ·
                  refine ⟨175069517548306148465351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 466852046795483062574269 175069517548306148465351)
                  ·
                    rfl

theorem cell21_767130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 2, 2, 3].length) (baseStart_767130 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_767130 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_767130 prefixEnd_767130 := by exact prefixLift 767130
  have htrace : WordTrace (prefixWord ++ tailWord_767130) baseStart_767130 baseEnd_767130 := by
    simpa [prefixWord, tailWord_767130, baseEnd_767130] using wordTrace_append hprefix tailTrace_767130
  have hstable : (prefixWord ++ tailWord_767130).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767130).length < 2 ^ (prefixWord ++ tailWord_767130).sum := by decide
  have hdescent : baseEnd_767130 < baseStart_767130 := by decide
  rcases family_descends (prefixWord ++ tailWord_767130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767234 : List Nat := [3, 4, 1, 1, 4, 1, 7]
def baseStart_767234 : Nat := 118140960795 + 767234 * 2 ^ 59
def prefixEnd_767234 : Nat := 4983230072969 + 3 ^ 40 * 767234 * 2
def baseEnd_767234 : Nat := 19454805751691675414645

theorem tailTrace_767234 : CollatzResearch.WordTrace tailWord_767234 prefixEnd_767234 19454805751691675414645 := by
  unfold tailWord_767234
  simp only [CollatzResearch.WordTrace]
  refine ⟨6995830725612431495057189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18655548601633150653485837 6995830725612431495057189)
  ·
    refine ⟨1311718261052330905323223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6995830725612431495057189 1311718261052330905323223)
    ·
      refine ⟨1967577391578496357984835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1311718261052330905323223 1967577391578496357984835)
      ·
        refine ⟨2951366087367744536977253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1967577391578496357984835 2951366087367744536977253)
        ·
          refine ⟨553381141381452100683235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2951366087367744536977253 553381141381452100683235)
          ·
            refine ⟨830071712072178151024853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 553381141381452100683235 830071712072178151024853)
            ·
              refine ⟨19454805751691675414645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 830071712072178151024853 19454805751691675414645)
              ·
                rfl

theorem cell21_767234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 7].length) (baseStart_767234 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_767234 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_767234 prefixEnd_767234 := by exact prefixLift 767234
  have htrace : WordTrace (prefixWord ++ tailWord_767234) baseStart_767234 baseEnd_767234 := by
    simpa [prefixWord, tailWord_767234, baseEnd_767234] using wordTrace_append hprefix tailTrace_767234
  have hstable : (prefixWord ++ tailWord_767234).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767234).length < 2 ^ (prefixWord ++ tailWord_767234).sum := by decide
  have hdescent : baseEnd_767234 < baseStart_767234 := by decide
  rcases family_descends (prefixWord ++ tailWord_767234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767293 : List Nat := [1, 4, 1, 5, 2, 8]
def baseStart_767293 : Nat := 118140960795 + 767293 * 2 ^ 59
def prefixEnd_767293 : Nat := 4983230072969 + 3 ^ 40 * 767293 * 2
def baseEnd_767293 : Nat := 6485433939594595824013

theorem tailTrace_767293 : CollatzResearch.WordTrace tailWord_767293 prefixEnd_767293 6485433939594595824013 := by
  unfold tailWord_767293
  simp only [CollatzResearch.WordTrace]
  refine ⟨27985474809235979056626533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18656983206157319371084355 27985474809235979056626533)
  ·
    refine ⟨5247276526731746073117475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27985474809235979056626533 5247276526731746073117475)
    ·
      refine ⟨7870914790097619109676213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5247276526731746073117475 7870914790097619109676213)
      ·
        refine ⟨737898261571651791532145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7870914790097619109676213 737898261571651791532145)
        ·
          refine ⟨553423696178738843649109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 737898261571651791532145 553423696178738843649109)
          ·
            refine ⟨6485433939594595824013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 553423696178738843649109 6485433939594595824013)
            ·
              rfl

theorem cell21_767293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 8].length) (baseStart_767293 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_767293 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_767293 prefixEnd_767293 := by exact prefixLift 767293
  have htrace : WordTrace (prefixWord ++ tailWord_767293) baseStart_767293 baseEnd_767293 := by
    simpa [prefixWord, tailWord_767293, baseEnd_767293] using wordTrace_append hprefix tailTrace_767293
  have hstable : (prefixWord ++ tailWord_767293).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767293).length < 2 ^ (prefixWord ++ tailWord_767293).sum := by decide
  have hdescent : baseEnd_767293 < baseStart_767293 := by decide
  rcases family_descends (prefixWord ++ tailWord_767293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767321 : List Nat := [1, 2, 1, 2, 2, 2, 4, 3, 4]
def baseStart_767321 : Nat := 118140960795 + 767321 * 2 ^ 59
def prefixEnd_767321 : Nat := 4983230072969 + 3 ^ 40 * 767321 * 2
def baseEnd_767321 : Nat := 175113106350532260781627

theorem tailTrace_767321 : CollatzResearch.WordTrace tailWord_767321 prefixEnd_767321 175113106350532260781627 := by
  unfold tailWord_767321
  simp only [CollatzResearch.WordTrace]
  refine ⟨27986496053134539838645817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18657664035423026559097211 27986496053134539838645817)
  ·
    refine ⟨20989872039850904878984363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27986496053134539838645817 20989872039850904878984363)
    ·
      refine ⟨31484808059776357318476545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20989872039850904878984363 31484808059776357318476545)
      ·
        refine ⟨23613606044832267988857409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31484808059776357318476545 23613606044832267988857409)
        ·
          refine ⟨17710204533624200991643057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23613606044832267988857409 17710204533624200991643057)
          ·
            refine ⟨13282653400218150743732293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17710204533624200991643057 13282653400218150743732293)
            ·
              refine ⟨2490497512540903264449805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13282653400218150743732293 2490497512540903264449805)
              ·
                refine ⟨933936567202838724168677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2490497512540903264449805 933936567202838724168677)
                ·
                  refine ⟨175113106350532260781627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 933936567202838724168677 175113106350532260781627)
                  ·
                    rfl

theorem cell21_767321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 3, 4].length) (baseStart_767321 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_767321 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_767321 prefixEnd_767321 := by exact prefixLift 767321
  have htrace : WordTrace (prefixWord ++ tailWord_767321) baseStart_767321 baseEnd_767321 := by
    simpa [prefixWord, tailWord_767321, baseEnd_767321] using wordTrace_append hprefix tailTrace_767321
  have hstable : (prefixWord ++ tailWord_767321).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767321).length < 2 ^ (prefixWord ++ tailWord_767321).sum := by decide
  have hdescent : baseEnd_767321 < baseStart_767321 := by decide
  rcases family_descends (prefixWord ++ tailWord_767321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767417 : List Nat := [1, 2, 1, 4, 4, 1, 3, 2, 3]
def baseStart_767417 : Nat := 118140960795 + 767417 * 2 ^ 59
def prefixEnd_767417 : Nat := 4983230072969 + 3 ^ 40 * 767417 * 2
def baseEnd_767417 : Nat := 175135014858457427181431

theorem tailTrace_767417 : CollatzResearch.WordTrace tailWord_767417 prefixEnd_767417 175135014858457427181431 := by
  unfold tailWord_767417
  simp only [CollatzResearch.WordTrace]
  refine ⟨27989997460786748234140505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18659998307191165489427003 27989997460786748234140505)
  ·
    refine ⟨20992498095590061175605379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27989997460786748234140505 20992498095590061175605379)
    ·
      refine ⟨31488747143385091763408069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20992498095590061175605379 31488747143385091763408069)
      ·
        refine ⟨5904140089384704705639013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31488747143385091763408069 5904140089384704705639013)
        ·
          refine ⟨1107026266759632132307315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5904140089384704705639013 1107026266759632132307315)
          ·
            refine ⟨1660539400139448198460973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1107026266759632132307315 1660539400139448198460973)
            ·
              refine ⟨622702275052293074422865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1660539400139448198460973 622702275052293074422865)
              ·
                refine ⟨467026706289219805817149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 622702275052293074422865 467026706289219805817149)
                ·
                  refine ⟨175135014858457427181431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 467026706289219805817149 175135014858457427181431)
                  ·
                    rfl

theorem cell21_767417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 3, 2, 3].length) (baseStart_767417 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_767417 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_767417 prefixEnd_767417 := by exact prefixLift 767417
  have htrace : WordTrace (prefixWord ++ tailWord_767417) baseStart_767417 baseEnd_767417 := by
    simpa [prefixWord, tailWord_767417, baseEnd_767417] using wordTrace_append hprefix tailTrace_767417
  have hstable : (prefixWord ++ tailWord_767417).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767417).length < 2 ^ (prefixWord ++ tailWord_767417).sum := by decide
  have hdescent : baseEnd_767417 < baseStart_767417 := by decide
  rcases family_descends (prefixWord ++ tailWord_767417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767428 : List Nat := [2, 3, 3, 2, 1, 1, 1, 8]
def baseStart_767428 : Nat := 118140960795 + 767428 * 2 ^ 59
def prefixEnd_767428 : Nat := 4983230072969 + 3 ^ 40 * 767428 * 2
def baseEnd_767428 : Nat := 58379175069441284166025

theorem tailTrace_767428 : CollatzResearch.WordTrace tailWord_767428 prefixEnd_767428 58379175069441284166025 := by
  unfold tailWord_767428
  simp only [CollatzResearch.WordTrace]
  refine ⟨13995199331873448556395469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18660265775831264741860625 13995199331873448556395469)
  ·
    refine ⟨5248199749452543208648301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13995199331873448556395469 5248199749452543208648301)
    ·
      refine ⟨1968074906044703703243113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5248199749452543208648301 1968074906044703703243113)
      ·
        refine ⟨1476056179533527777432335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1968074906044703703243113 1476056179533527777432335)
        ·
          refine ⟨2214084269300291666148503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1476056179533527777432335 2214084269300291666148503)
          ·
            refine ⟨3321126403950437499222755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2214084269300291666148503 3321126403950437499222755)
            ·
              refine ⟨4981689605925656248834133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3321126403950437499222755 4981689605925656248834133)
              ·
                refine ⟨58379175069441284166025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4981689605925656248834133 58379175069441284166025)
                ·
                  rfl

theorem cell21_767428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 8].length) (baseStart_767428 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_767428 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_767428 prefixEnd_767428 := by exact prefixLift 767428
  have htrace : WordTrace (prefixWord ++ tailWord_767428) baseStart_767428 baseEnd_767428 := by
    simpa [prefixWord, tailWord_767428, baseEnd_767428] using wordTrace_append hprefix tailTrace_767428
  have hstable : (prefixWord ++ tailWord_767428).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767428).length < 2 ^ (prefixWord ++ tailWord_767428).sum := by decide
  have hdescent : baseEnd_767428 < baseStart_767428 := by decide
  rcases family_descends (prefixWord ++ tailWord_767428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767456 : List Nat := [2, 1, 1, 3, 1, 1, 2, 4, 6]
def baseStart_767456 : Nat := 118140960795 + 767456 * 2 ^ 59
def prefixEnd_767456 : Nat := 4983230072969 + 3 ^ 40 * 767456 * 2
def baseEnd_767456 : Nat := 175143915189802026031351

theorem tailTrace_767456 : CollatzResearch.WordTrace tailWord_767456 prefixEnd_767456 175143915189802026031351 := by
  unfold tailWord_767456
  simp only [CollatzResearch.WordTrace]
  refine ⟨13995709953822728947405111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18660946605096971929873481 13995709953822728947405111)
  ·
    refine ⟨20993564930734093421107667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13995709953822728947405111 20993564930734093421107667)
    ·
      refine ⟨31490347396101140131661501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20993564930734093421107667 31490347396101140131661501)
      ·
        refine ⟨11808880273537927549373063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31490347396101140131661501 11808880273537927549373063)
        ·
          refine ⟨17713320410306891324059595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11808880273537927549373063 17713320410306891324059595)
          ·
            refine ⟨26569980615460336986089393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17713320410306891324059595 26569980615460336986089393)
            ·
              refine ⟨19927485461595252739567045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26569980615460336986089393 19927485461595252739567045)
              ·
                refine ⟨3736403524049109888668821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19927485461595252739567045 3736403524049109888668821)
                ·
                  refine ⟨175143915189802026031351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3736403524049109888668821 175143915189802026031351)
                  ·
                    rfl

theorem cell21_767456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 4, 6].length) (baseStart_767456 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_767456 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_767456 prefixEnd_767456 := by exact prefixLift 767456
  have htrace : WordTrace (prefixWord ++ tailWord_767456) baseStart_767456 baseEnd_767456 := by
    simpa [prefixWord, tailWord_767456, baseEnd_767456] using wordTrace_append hprefix tailTrace_767456
  have hstable : (prefixWord ++ tailWord_767456).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767456).length < 2 ^ (prefixWord ++ tailWord_767456).sum := by decide
  have hdescent : baseEnd_767456 < baseStart_767456 := by decide
  rcases family_descends (prefixWord ++ tailWord_767456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767473 : List Nat := [1, 2, 2, 2, 3, 2, 1, 4, 4]
def baseStart_767473 : Nat := 118140960795 + 767473 * 2 ^ 59
def prefixEnd_767473 : Nat := 4983230072969 + 3 ^ 40 * 767473 * 2
def baseEnd_767473 : Nat := 175147794821413774247983

theorem tailTrace_767473 : CollatzResearch.WordTrace tailWord_767473 prefixEnd_767473 175147794821413774247983 := by
  unfold tailWord_767473
  simp only [CollatzResearch.WordTrace]
  refine ⟨27992039948583869798179073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18661359965722579865452715 27992039948583869798179073)
  ·
    refine ⟨20994029961437902348634305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27992039948583869798179073 20994029961437902348634305)
    ·
      refine ⟨15745522471078426761475729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20994029961437902348634305 15745522471078426761475729)
      ·
        refine ⟨11809141853308820071106797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15745522471078426761475729 11809141853308820071106797)
        ·
          refine ⟨4428428194990807526665049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11809141853308820071106797 4428428194990807526665049)
          ·
            refine ⟨3321321146243105644998787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4428428194990807526665049 3321321146243105644998787)
            ·
              refine ⟨4981981719364658467498181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3321321146243105644998787 4981981719364658467498181)
              ·
                refine ⟨934121572380873462655909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4981981719364658467498181 934121572380873462655909)
                ·
                  refine ⟨175147794821413774247983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 934121572380873462655909 175147794821413774247983)
                  ·
                    rfl

theorem cell21_767473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 4, 4].length) (baseStart_767473 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_767473 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_767473 prefixEnd_767473 := by exact prefixLift 767473
  have htrace : WordTrace (prefixWord ++ tailWord_767473) baseStart_767473 baseEnd_767473 := by
    simpa [prefixWord, tailWord_767473, baseEnd_767473] using wordTrace_append hprefix tailTrace_767473
  have hstable : (prefixWord ++ tailWord_767473).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767473).length < 2 ^ (prefixWord ++ tailWord_767473).sum := by decide
  have hdescent : baseEnd_767473 < baseStart_767473 := by decide
  rcases family_descends (prefixWord ++ tailWord_767473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767577 : List Nat := [1, 2, 1, 2, 2, 1, 1, 4, 7]
def baseStart_767577 : Nat := 118140960795 + 767577 * 2 ^ 59
def prefixEnd_767577 : Nat := 4983230072969 + 3 ^ 40 * 767577 * 2
def baseEnd_767577 : Nat := 175171529038332704514437

theorem tailTrace_767577 : CollatzResearch.WordTrace tailWord_767577 prefixEnd_767577 175171529038332704514437 := by
  unfold tailWord_767577
  simp only [CollatzResearch.WordTrace]
  refine ⟨27995833140207095559964985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18663888760138063706643323 27995833140207095559964985)
  ·
    refine ⟨20996874855155321669973739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27995833140207095559964985 20996874855155321669973739)
    ·
      refine ⟨31495312282732982504960609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20996874855155321669973739 31495312282732982504960609)
      ·
        refine ⟨23621484212049736878720457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31495312282732982504960609 23621484212049736878720457)
        ·
          refine ⟨17716113159037302659040343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23621484212049736878720457 17716113159037302659040343)
          ·
            refine ⟨26574169738555953988560515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17716113159037302659040343 26574169738555953988560515)
            ·
              refine ⟨39861254607833930982840773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26574169738555953988560515 39861254607833930982840773)
              ·
                refine ⟨7473985238968862059282645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39861254607833930982840773 7473985238968862059282645)
                ·
                  refine ⟨175171529038332704514437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7473985238968862059282645 175171529038332704514437)
                  ·
                    rfl

theorem cell21_767577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 4, 7].length) (baseStart_767577 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_767577 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_767577 prefixEnd_767577 := by exact prefixLift 767577
  have htrace : WordTrace (prefixWord ++ tailWord_767577) baseStart_767577 baseEnd_767577 := by
    simpa [prefixWord, tailWord_767577, baseEnd_767577] using wordTrace_append hprefix tailTrace_767577
  have hstable : (prefixWord ++ tailWord_767577).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767577).length < 2 ^ (prefixWord ++ tailWord_767577).sum := by decide
  have hdescent : baseEnd_767577 < baseStart_767577 := by decide
  rcases family_descends (prefixWord ++ tailWord_767577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767580 : List Nat := [2, 2, 4, 1, 2, 3, 7]
def baseStart_767580 : Nat := 118140960795 + 767580 * 2 ^ 59
def prefixEnd_767580 : Nat := 4983230072969 + 3 ^ 40 * 767580 * 2
def baseEnd_767580 : Nat := 19463579297689485107159

theorem tailTrace_767580 : CollatzResearch.WordTrace tailWord_767580 prefixEnd_767580 19463579297689485107159 := by
  unfold tailWord_767580
  simp only [CollatzResearch.WordTrace]
  refine ⟨13997971279598113536162097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18663961706130818048216129 13997971279598113536162097)
  ·
    refine ⟨10498478459698585152121573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13997971279598113536162097 10498478459698585152121573)
    ·
      refine ⟨1968464711193484716022795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10498478459698585152121573 1968464711193484716022795)
      ·
        refine ⟨2952697066790227074034193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1968464711193484716022795 2952697066790227074034193)
        ·
          refine ⟨2214522800092670305525645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2952697066790227074034193 2214522800092670305525645)
          ·
            refine ⟨830446050034751364572117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2214522800092670305525645 830446050034751364572117)
            ·
              refine ⟨19463579297689485107159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 830446050034751364572117 19463579297689485107159)
              ·
                rfl

theorem cell21_767580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 7].length) (baseStart_767580 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_767580 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_767580 prefixEnd_767580 := by exact prefixLift 767580
  have htrace : WordTrace (prefixWord ++ tailWord_767580) baseStart_767580 baseEnd_767580 := by
    simpa [prefixWord, tailWord_767580, baseEnd_767580] using wordTrace_append hprefix tailTrace_767580
  have hstable : (prefixWord ++ tailWord_767580).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767580).length < 2 ^ (prefixWord ++ tailWord_767580).sum := by decide
  have hdescent : baseEnd_767580 < baseStart_767580 := by decide
  rcases family_descends (prefixWord ++ tailWord_767580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767687 : List Nat := [1, 1, 4, 1, 1, 1, 6, 3, 3]
def baseStart_767687 : Nat := 118140960795 + 767687 * 2 ^ 59
def prefixEnd_767687 : Nat := 4983230072969 + 3 ^ 40 * 767687 * 2
def baseEnd_767687 : Nat := 175196632536996957680879

theorem tailTrace_767687 : CollatzResearch.WordTrace tailWord_767687 prefixEnd_767687 175196632536996957680879 := by
  unfold tailWord_767687
  simp only [CollatzResearch.WordTrace]
  refine ⟨27999845169808584346469315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18666563446539056230979543 27999845169808584346469315)
  ·
    refine ⟨41999767754712876519703973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27999845169808584346469315 41999767754712876519703973)
    ·
      refine ⟨7874956454008664347444495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41999767754712876519703973 7874956454008664347444495)
      ·
        refine ⟨11812434681012996521166743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7874956454008664347444495 11812434681012996521166743)
        ·
          refine ⟨17718652021519494781750115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11812434681012996521166743 17718652021519494781750115)
          ·
            refine ⟨26577978032279242172625173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17718652021519494781750115 26577978032279242172625173)
            ·
              refine ⟨1245842720263089476841805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 26577978032279242172625173 1245842720263089476841805)
              ·
                refine ⟨467191020098658553815677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1245842720263089476841805 467191020098658553815677)
                ·
                  refine ⟨175196632536996957680879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 467191020098658553815677 175196632536996957680879)
                  ·
                    rfl

theorem cell21_767687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6, 3, 3].length) (baseStart_767687 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_767687 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_767687 prefixEnd_767687 := by exact prefixLift 767687
  have htrace : WordTrace (prefixWord ++ tailWord_767687) baseStart_767687 baseEnd_767687 := by
    simpa [prefixWord, tailWord_767687, baseEnd_767687] using wordTrace_append hprefix tailTrace_767687
  have hstable : (prefixWord ++ tailWord_767687).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767687).length < 2 ^ (prefixWord ++ tailWord_767687).sum := by decide
  have hdescent : baseEnd_767687 < baseStart_767687 := by decide
  rcases family_descends (prefixWord ++ tailWord_767687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767777 : List Nat := [1, 2, 3, 2, 1, 4, 1, 3, 4]
def baseStart_767777 : Nat := 118140960795 + 767777 * 2 ^ 59
def prefixEnd_767777 : Nat := 4983230072969 + 3 ^ 40 * 767777 * 2
def baseEnd_767777 : Nat := 175217171763176801180695

theorem tailTrace_767777 : CollatzResearch.WordTrace tailWord_767777 prefixEnd_767777 175217171763176801180695 := by
  unfold tailWord_767777
  simp only [CollatzResearch.WordTrace]
  refine ⟨28003127739482529717245585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18668751826321686478163723 28003127739482529717245585)
  ·
    refine ⟨21002345804611897287934189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28003127739482529717245585 21002345804611897287934189)
    ·
      refine ⟨7875879676729461482975321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21002345804611897287934189 7875879676729461482975321)
      ·
        refine ⟨5906909757547096112231491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7875879676729461482975321 5906909757547096112231491)
        ·
          refine ⟨8860364636320644168347237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5906909757547096112231491 8860364636320644168347237)
          ·
            refine ⟨1661318369310120781565107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8860364636320644168347237 1661318369310120781565107)
            ·
              refine ⟨2491977553965181172347661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1661318369310120781565107 2491977553965181172347661)
              ·
                refine ⟨934491582736942939630373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2491977553965181172347661 934491582736942939630373)
                ·
                  refine ⟨175217171763176801180695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 934491582736942939630373 175217171763176801180695)
                  ·
                    rfl

theorem cell21_767777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 3, 4].length) (baseStart_767777 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_767777 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_767777 prefixEnd_767777 := by exact prefixLift 767777
  have htrace : WordTrace (prefixWord ++ tailWord_767777) baseStart_767777 baseEnd_767777 := by
    simpa [prefixWord, tailWord_767777, baseEnd_767777] using wordTrace_append hprefix tailTrace_767777
  have hstable : (prefixWord ++ tailWord_767777).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767777).length < 2 ^ (prefixWord ++ tailWord_767777).sum := by decide
  have hdescent : baseEnd_767777 < baseStart_767777 := by decide
  rcases family_descends (prefixWord ++ tailWord_767777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767814 : List Nat := [6, 1, 1, 2, 1, 1, 4, 2, 3]
def baseStart_767814 : Nat := 118140960795 + 767814 * 2 ^ 59
def prefixEnd_767814 : Nat := 4983230072969 + 3 ^ 40 * 767814 * 2
def baseEnd_767814 : Nat := 175225615667272959063953

theorem tailTrace_767814 : CollatzResearch.WordTrace tailWord_767814 prefixEnd_767814 175225615667272959063953 := by
  unfold tailWord_767814
  simp only [CollatzResearch.WordTrace]
  refine ⟨875139913760890157385703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 18669651493565656690894997 875139913760890157385703)
  ·
    refine ⟨1312709870641335236078555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 875139913760890157385703 1312709870641335236078555)
    ·
      refine ⟨1969064805962002854117833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1312709870641335236078555 1969064805962002854117833)
      ·
        refine ⟨1476798604471502140588375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1969064805962002854117833 1476798604471502140588375)
        ·
          refine ⟨2215197906707253210882563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1476798604471502140588375 2215197906707253210882563)
          ·
            refine ⟨3322796860060879816323845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2215197906707253210882563 3322796860060879816323845)
            ·
              refine ⟨623024411261414965560721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3322796860060879816323845 623024411261414965560721)
              ·
                refine ⟨467268308446061224170541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 623024411261414965560721 467268308446061224170541)
                ·
                  refine ⟨175225615667272959063953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 467268308446061224170541 175225615667272959063953)
                  ·
                    rfl

theorem cell21_767814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 4, 2, 3].length) (baseStart_767814 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_767814 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_767814 prefixEnd_767814 := by exact prefixLift 767814
  have htrace : WordTrace (prefixWord ++ tailWord_767814) baseStart_767814 baseEnd_767814 := by
    simpa [prefixWord, tailWord_767814, baseEnd_767814] using wordTrace_append hprefix tailTrace_767814
  have hstable : (prefixWord ++ tailWord_767814).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767814).length < 2 ^ (prefixWord ++ tailWord_767814).sum := by decide
  have hdescent : baseEnd_767814 < baseStart_767814 := by decide
  rcases family_descends (prefixWord ++ tailWord_767814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767870 : List Nat := [4, 2, 3, 1, 1, 2, 1, 1, 6]
def baseStart_767870 : Nat := 118140960795 + 767870 * 2 ^ 59
def prefixEnd_767870 : Nat := 4983230072969 + 3 ^ 40 * 767870 * 2
def baseEnd_767870 : Nat := 175238395630229306130505

theorem tailTrace_767870 : CollatzResearch.WordTrace tailWord_767870 prefixEnd_767870 175238395630229306130505 := by
  unfold tailWord_767870
  simp only [CollatzResearch.WordTrace]
  refine ⟨3500814966018200825047633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18671013152097071066920709 3500814966018200825047633)
  ·
    refine ⟨2625611224513650618785725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3500814966018200825047633 2625611224513650618785725)
    ·
      refine ⟨984604209192618982044647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2625611224513650618785725 984604209192618982044647)
      ·
        refine ⟨1476906313788928473066971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 984604209192618982044647 1476906313788928473066971)
        ·
          refine ⟨2215359470683392709600457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1476906313788928473066971 2215359470683392709600457)
          ·
            refine ⟨1661519603012544532200343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2215359470683392709600457 1661519603012544532200343)
            ·
              refine ⟨2492279404518816798300515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1661519603012544532200343 2492279404518816798300515)
              ·
                refine ⟨3738419106778225197450773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2492279404518816798300515 3738419106778225197450773)
                ·
                  refine ⟨175238395630229306130505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3738419106778225197450773 175238395630229306130505)
                  ·
                    rfl

theorem cell21_767870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 1, 6].length) (baseStart_767870 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_767870 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_767870 prefixEnd_767870 := by exact prefixLift 767870
  have htrace : WordTrace (prefixWord ++ tailWord_767870) baseStart_767870 baseEnd_767870 := by
    simpa [prefixWord, tailWord_767870, baseEnd_767870] using wordTrace_append hprefix tailTrace_767870
  have hstable : (prefixWord ++ tailWord_767870).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767870).length < 2 ^ (prefixWord ++ tailWord_767870).sum := by decide
  have hdescent : baseEnd_767870 < baseStart_767870 := by decide
  rcases family_descends (prefixWord ++ tailWord_767870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767898 : List Nat := [3, 1, 1, 4, 2, 1, 2, 2, 5]
def baseStart_767898 : Nat := 118140960795 + 767898 * 2 ^ 59
def prefixEnd_767898 : Nat := 4983230072969 + 3 ^ 40 * 767898 * 2
def baseEnd_767898 : Nat := 175244785611707479663781

theorem tailTrace_767898 : CollatzResearch.WordTrace tailWord_767898 prefixEnd_767898 175244785611707479663781 := by
  unfold tailWord_767898
  simp only [CollatzResearch.WordTrace]
  refine ⟨7001885243011041845600087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18671693981362778254933565 7001885243011041845600087)
  ·
    refine ⟨10502827864516562768400131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7001885243011041845600087 10502827864516562768400131)
    ·
      refine ⟨15754241796774844152600197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10502827864516562768400131 15754241796774844152600197)
      ·
        refine ⟨2953920336895283278612537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15754241796774844152600197 2953920336895283278612537)
        ·
          refine ⟨2215440252671462458959403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2953920336895283278612537 2215440252671462458959403)
          ·
            refine ⟨3323160379007193688439105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2215440252671462458959403 3323160379007193688439105)
            ·
              refine ⟨2492370284255395266329329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3323160379007193688439105 2492370284255395266329329)
              ·
                refine ⟨1869277713191546449746997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2492370284255395266329329 1869277713191546449746997)
                ·
                  refine ⟨175244785611707479663781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1869277713191546449746997 175244785611707479663781)
                  ·
                    rfl

theorem cell21_767898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 2, 5].length) (baseStart_767898 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_767898 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_767898 prefixEnd_767898 := by exact prefixLift 767898
  have htrace : WordTrace (prefixWord ++ tailWord_767898) baseStart_767898 baseEnd_767898 := by
    simpa [prefixWord, tailWord_767898, baseEnd_767898] using wordTrace_append hprefix tailTrace_767898
  have hstable : (prefixWord ++ tailWord_767898).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767898).length < 2 ^ (prefixWord ++ tailWord_767898).sum := by decide
  have hdescent : baseEnd_767898 < baseStart_767898 := by decide
  rcases family_descends (prefixWord ++ tailWord_767898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767918 : List Nat := [4, 1, 5, 1, 1, 2, 7]
def baseStart_767918 : Nat := 118140960795 + 767918 * 2 ^ 59
def prefixEnd_767918 : Nat := 4983230072969 + 3 ^ 40 * 767918 * 2
def baseEnd_767918 : Nat := 19472149987132432147823

theorem tailTrace_767918 : CollatzResearch.WordTrace tailWord_767918 prefixEnd_767918 19472149987132432147823 := by
  unfold tailWord_767918
  simp only [CollatzResearch.WordTrace]
  refine ⟨3501033803996463849766051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18672180287981140532085605 3501033803996463849766051)
  ·
    refine ⟨5251550705994695774649077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3501033803996463849766051 5251550705994695774649077)
    ·
      refine ⟨492332878687002728873351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5251550705994695774649077 492332878687002728873351)
      ·
        refine ⟨738499318030504093310027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 492332878687002728873351 738499318030504093310027)
        ·
          refine ⟨1107748977045756139965041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 738499318030504093310027 1107748977045756139965041)
          ·
            refine ⟨830811732784317104973781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1107748977045756139965041 830811732784317104973781)
            ·
              refine ⟨19472149987132432147823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 830811732784317104973781 19472149987132432147823)
              ·
                rfl

theorem cell21_767918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 7].length) (baseStart_767918 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_767918 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_767918 prefixEnd_767918 := by exact prefixLift 767918
  have htrace : WordTrace (prefixWord ++ tailWord_767918) baseStart_767918 baseEnd_767918 := by
    simpa [prefixWord, tailWord_767918, baseEnd_767918] using wordTrace_append hprefix tailTrace_767918
  have hstable : (prefixWord ++ tailWord_767918).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767918).length < 2 ^ (prefixWord ++ tailWord_767918).sum := by decide
  have hdescent : baseEnd_767918 < baseStart_767918 := by decide
  rcases family_descends (prefixWord ++ tailWord_767918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767932 : List Nat := [2, 2, 2, 5, 1, 2, 1, 1, 5]
def baseStart_767932 : Nat := 118140960795 + 767932 * 2 ^ 59
def prefixEnd_767932 : Nat := 4983230072969 + 3 ^ 40 * 767932 * 2
def baseEnd_767932 : Nat := 175252544874930976097045

theorem tailTrace_767932 : CollatzResearch.WordTrace tailWord_767932 prefixEnd_767932 175252544874930976097045 := by
  unfold tailWord_767932
  simp only [CollatzResearch.WordTrace]
  refine ⟨14004390526960495594569025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18672520702613994126092033 14004390526960495594569025)
  ·
    refine ⟨10503292895220371695926769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14004390526960495594569025 10503292895220371695926769)
    ·
      refine ⟨7877469671415278771945077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10503292895220371695926769 7877469671415278771945077)
      ·
        refine ⟨738512781695182384869851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7877469671415278771945077 738512781695182384869851)
        ·
          refine ⟨1107769172542773577304777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 738512781695182384869851 1107769172542773577304777)
          ·
            refine ⟨830826879407080182978583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1107769172542773577304777 830826879407080182978583)
            ·
              refine ⟨1246240319110620274467875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 830826879407080182978583 1246240319110620274467875)
              ·
                refine ⟨1869360478665930411701813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1246240319110620274467875 1869360478665930411701813)
                ·
                  refine ⟨175252544874930976097045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1869360478665930411701813 175252544874930976097045)
                  ·
                    rfl

theorem cell21_767932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 1, 1, 5].length) (baseStart_767932 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_767932 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_767932 prefixEnd_767932 := by exact prefixLift 767932
  have htrace : WordTrace (prefixWord ++ tailWord_767932) baseStart_767932 baseEnd_767932 := by
    simpa [prefixWord, tailWord_767932, baseEnd_767932] using wordTrace_append hprefix tailTrace_767932
  have hstable : (prefixWord ++ tailWord_767932).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767932).length < 2 ^ (prefixWord ++ tailWord_767932).sum := by decide
  have hdescent : baseEnd_767932 < baseStart_767932 := by decide
  rcases family_descends (prefixWord ++ tailWord_767932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768039 : List Nat := [1, 1, 7, 1, 2, 2, 1, 2, 4]
def baseStart_768039 : Nat := 118140960795 + 768039 * 2 ^ 59
def prefixEnd_768039 : Nat := 4983230072969 + 3 ^ 40 * 768039 * 2
def baseEnd_768039 : Nat := 175276963732722567813493

theorem tailTrace_768039 : CollatzResearch.WordTrace tailWord_768039 prefixEnd_768039 175276963732722567813493 := by
  unfold tailWord_768039
  simp only [CollatzResearch.WordTrace]
  refine ⟨28012683664533348463283171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18675122443022232308855447 28012683664533348463283171)
  ·
    refine ⟨42019025496800022694924757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28012683664533348463283171 42019025496800022694924757)
    ·
      refine ⟨984820910081250531912299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 42019025496800022694924757 984820910081250531912299)
      ·
        refine ⟨1477231365121875797868449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 984820910081250531912299 1477231365121875797868449)
        ·
          refine ⟨1107923523841406848401337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1477231365121875797868449 1107923523841406848401337)
          ·
            refine ⟨830942642881055136301003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1107923523841406848401337 830942642881055136301003)
            ·
              refine ⟨1246413964321582704451505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 830942642881055136301003 1246413964321582704451505)
              ·
                refine ⟨934810473241187028338629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1246413964321582704451505 934810473241187028338629)
                ·
                  refine ⟨175276963732722567813493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 934810473241187028338629 175276963732722567813493)
                  ·
                    rfl

theorem cell21_768039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 1, 2, 4].length) (baseStart_768039 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_768039 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_768039 prefixEnd_768039 := by exact prefixLift 768039
  have htrace : WordTrace (prefixWord ++ tailWord_768039) baseStart_768039 baseEnd_768039 := by
    simpa [prefixWord, tailWord_768039, baseEnd_768039] using wordTrace_append hprefix tailTrace_768039
  have hstable : (prefixWord ++ tailWord_768039).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768039).length < 2 ^ (prefixWord ++ tailWord_768039).sum := by decide
  have hdescent : baseEnd_768039 < baseStart_768039 := by decide
  rcases family_descends (prefixWord ++ tailWord_768039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768050 : List Nat := [3, 2, 1, 1, 2, 4, 2, 1, 5]
def baseStart_768050 : Nat := 118140960795 + 768050 * 2 ^ 59
def prefixEnd_768050 : Nat := 4983230072969 + 3 ^ 40 * 768050 * 2
def baseEnd_768050 : Nat := 175279474082588993130137

theorem tailTrace_768050 : CollatzResearch.WordTrace tailWord_768050 prefixEnd_768050 175279474082588993130137 := by
  unfold tailWord_768050
  simp only [CollatzResearch.WordTrace]
  refine ⟨7003271216873374335483401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18675389911662331561289069 7003271216873374335483401)
  ·
    refine ⟨5252453412655030751612551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7003271216873374335483401 5252453412655030751612551)
    ·
      refine ⟨7878680118982546127418827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5252453412655030751612551 7878680118982546127418827)
      ·
        refine ⟨11818020178473819191128241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7878680118982546127418827 11818020178473819191128241)
        ·
          refine ⟨8863515133855364393346181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11818020178473819191128241 8863515133855364393346181)
          ·
            refine ⟨1661909087597880823752409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8863515133855364393346181 1661909087597880823752409)
            ·
              refine ⟨1246431815698410617814307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1661909087597880823752409 1246431815698410617814307)
              ·
                refine ⟨1869647723547615926721461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1246431815698410617814307 1869647723547615926721461)
                ·
                  refine ⟨175279474082588993130137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1869647723547615926721461 175279474082588993130137)
                  ·
                    rfl

theorem cell21_768050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2, 1, 5].length) (baseStart_768050 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_768050 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_768050 prefixEnd_768050 := by exact prefixLift 768050
  have htrace : WordTrace (prefixWord ++ tailWord_768050) baseStart_768050 baseEnd_768050 := by
    simpa [prefixWord, tailWord_768050, baseEnd_768050] using wordTrace_append hprefix tailTrace_768050
  have hstable : (prefixWord ++ tailWord_768050).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768050).length < 2 ^ (prefixWord ++ tailWord_768050).sum := by decide
  have hdescent : baseEnd_768050 < baseStart_768050 := by decide
  rcases family_descends (prefixWord ++ tailWord_768050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768154 : List Nat := [3, 1, 1, 5, 11]
def baseStart_768154 : Nat := 118140960795 + 768154 * 2 ^ 59
def prefixEnd_768154 : Nat := 4983230072969 + 3 ^ 40 * 768154 * 2
def baseEnd_768154 : Nat := 2164237139500097819711

theorem tailTrace_768154 : CollatzResearch.WordTrace tailWord_768154 prefixEnd_768154 2164237139500097819711 := by
  unfold tailWord_768154
  simp only [CollatzResearch.WordTrace]
  refine ⟨7004219514779180775929879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18677918706077815402479677 7004219514779180775929879)
  ·
    refine ⟨10506329272168771163894819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7004219514779180775929879 10506329272168771163894819)
    ·
      refine ⟨15759493908253156745842229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10506329272168771163894819 15759493908253156745842229)
      ·
        refine ⟨1477452553898733444922709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15759493908253156745842229 1477452553898733444922709)
        ·
          refine ⟨2164237139500097819711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 1477452553898733444922709 2164237139500097819711)
          ·
            rfl

theorem cell21_768154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 11].length) (baseStart_768154 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_768154 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_768154 prefixEnd_768154 := by exact prefixLift 768154
  have htrace : WordTrace (prefixWord ++ tailWord_768154) baseStart_768154 baseEnd_768154 := by
    simpa [prefixWord, tailWord_768154, baseEnd_768154] using wordTrace_append hprefix tailTrace_768154
  have hstable : (prefixWord ++ tailWord_768154).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768154).length < 2 ^ (prefixWord ++ tailWord_768154).sum := by decide
  have hdescent : baseEnd_768154 < baseStart_768154 := by decide
  rcases family_descends (prefixWord ++ tailWord_768154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768157 : List Nat := [1, 4, 2, 1, 1, 4, 2, 2, 4]
def baseStart_768157 : Nat := 118140960795 + 768157 * 2 ^ 59
def prefixEnd_768157 : Nat := 4983230072969 + 3 ^ 40 * 768157 * 2
def baseEnd_768157 : Nat := 175303892940380584846585

theorem tailTrace_768157 : CollatzResearch.WordTrace tailWord_768157 prefixEnd_768157 175303892940380584846585 := by
  unfold tailWord_768157
  simp only [CollatzResearch.WordTrace]
  refine ⟨28016987478105854616078725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18677991652070569744052483 28016987478105854616078725)
  ·
    refine ⟨5253185152144847740514761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28016987478105854616078725 5253185152144847740514761)
    ·
      refine ⟨3939888864108635805386071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5253185152144847740514761 3939888864108635805386071)
      ·
        refine ⟨5909833296162953708079107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3939888864108635805386071 5909833296162953708079107)
        ·
          refine ⟨8864749944244430562118661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5909833296162953708079107 8864749944244430562118661)
          ·
            refine ⟨1662140614545830730397249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8864749944244430562118661 1662140614545830730397249)
            ·
              refine ⟨1246605460909373047797937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1662140614545830730397249 1246605460909373047797937)
              ·
                refine ⟨934954095682029785848453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1246605460909373047797937 934954095682029785848453)
                ·
                  refine ⟨175303892940380584846585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 934954095682029785848453 175303892940380584846585)
                  ·
                    rfl

theorem cell21_768157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2, 2, 4].length) (baseStart_768157 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_768157 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_768157 prefixEnd_768157 := by exact prefixLift 768157
  have htrace : WordTrace (prefixWord ++ tailWord_768157) baseStart_768157 baseEnd_768157 := by
    simpa [prefixWord, tailWord_768157, baseEnd_768157] using wordTrace_append hprefix tailTrace_768157
  have hstable : (prefixWord ++ tailWord_768157).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768157).length < 2 ^ (prefixWord ++ tailWord_768157).sum := by decide
  have hdescent : baseEnd_768157 < baseStart_768157 := by decide
  rcases family_descends (prefixWord ++ tailWord_768157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768160 : List Nat := [2, 1, 1, 4, 2, 4, 2, 2, 3]
def baseStart_768160 : Nat := 118140960795 + 768160 * 2 ^ 59
def prefixEnd_768160 : Nat := 4983230072969 + 3 ^ 40 * 768160 * 2
def baseEnd_768160 : Nat := 175304577581253246296579

theorem tailTrace_768160 : CollatzResearch.WordTrace tailWord_768160 prefixEnd_768160 175304577581253246296579 := by
  unfold tailWord_768160
  simp only [CollatzResearch.WordTrace]
  refine ⟨14008548448547493064218967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18678064598063324085625289 14008548448547493064218967)
  ·
    refine ⟨21012822672821239596328451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14008548448547493064218967 21012822672821239596328451)
    ·
      refine ⟨31519234009231859394492677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21012822672821239596328451 31519234009231859394492677)
      ·
        refine ⟨5909856376730973636467377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31519234009231859394492677 5909856376730973636467377)
        ·
          refine ⟨4432392282548230227350533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5909856376730973636467377 4432392282548230227350533)
          ·
            refine ⟨831073552977793167628225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4432392282548230227350533 831073552977793167628225)
            ·
              refine ⟨623305164733344875721169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 831073552977793167628225 623305164733344875721169)
              ·
                refine ⟨467478873550008656790877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 623305164733344875721169 467478873550008656790877)
                ·
                  refine ⟨175304577581253246296579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 467478873550008656790877 175304577581253246296579)
                  ·
                    rfl

theorem cell21_768160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 2, 2, 3].length) (baseStart_768160 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_768160 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_768160 prefixEnd_768160 := by exact prefixLift 768160
  have htrace : WordTrace (prefixWord ++ tailWord_768160) baseStart_768160 baseEnd_768160 := by
    simpa [prefixWord, tailWord_768160, baseEnd_768160] using wordTrace_append hprefix tailTrace_768160
  have hstable : (prefixWord ++ tailWord_768160).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768160).length < 2 ^ (prefixWord ++ tailWord_768160).sum := by decide
  have hdescent : baseEnd_768160 < baseStart_768160 := by decide
  rcases family_descends (prefixWord ++ tailWord_768160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768185 : List Nat := [1, 2, 1, 4, 1, 2, 3, 2, 5]
def baseStart_768185 : Nat := 118140960795 + 768185 * 2 ^ 59
def prefixEnd_768185 : Nat := 4983230072969 + 3 ^ 40 * 768185 * 2
def baseEnd_768185 : Nat := 175310282921858758379861

theorem tailTrace_768185 : CollatzResearch.WordTrace tailWord_768185 prefixEnd_768185 175310282921858758379861 := by
  unfold tailWord_768185
  simp only [CollatzResearch.WordTrace]
  refine ⟨28018008722004415398098009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18678672481336276932065339 28018008722004415398098009)
  ·
    refine ⟨21013506541503311548573507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28018008722004415398098009 21013506541503311548573507)
    ·
      refine ⟨31520259812254967322860261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21013506541503311548573507 31520259812254967322860261)
      ·
        refine ⟨5910048714797806373036299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31520259812254967322860261 5910048714797806373036299)
        ·
          refine ⟨8865073072196709559554449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5910048714797806373036299 8865073072196709559554449)
          ·
            refine ⟨6648804804147532169665837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8865073072196709559554449 6648804804147532169665837)
            ·
              refine ⟨2493301801555324563624689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6648804804147532169665837 2493301801555324563624689)
              ·
                refine ⟨1869976351166493422718517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2493301801555324563624689 1869976351166493422718517)
                ·
                  refine ⟨175310282921858758379861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1869976351166493422718517 175310282921858758379861)
                  ·
                    rfl

theorem cell21_768185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 2, 5].length) (baseStart_768185 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_768185 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_768185 prefixEnd_768185 := by exact prefixLift 768185
  have htrace : WordTrace (prefixWord ++ tailWord_768185) baseStart_768185 baseEnd_768185 := by
    simpa [prefixWord, tailWord_768185, baseEnd_768185] using wordTrace_append hprefix tailTrace_768185
  have hstable : (prefixWord ++ tailWord_768185).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768185).length < 2 ^ (prefixWord ++ tailWord_768185).sum := by decide
  have hdescent : baseEnd_768185 < baseStart_768185 := by decide
  rcases family_descends (prefixWord ++ tailWord_768185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768188 : List Nat := [2, 2, 2, 3, 3, 1, 3, 5]
def baseStart_768188 : Nat := 118140960795 + 768188 * 2 ^ 59
def prefixEnd_768188 : Nat := 4983230072969 + 3 ^ 40 * 768188 * 2
def baseEnd_768188 : Nat := 58436989187577139943285

theorem tailTrace_768188 : CollatzResearch.WordTrace tailWord_768188 prefixEnd_768188 58436989187577139943285 := by
  unfold tailWord_768188
  simp only [CollatzResearch.WordTrace]
  refine ⟨14009059070496773455228609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18678745427329031273638145 14009059070496773455228609)
  ·
    refine ⟨10506794302872580091421457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14009059070496773455228609 10506794302872580091421457)
    ·
      refine ⟨7880095727154435068566093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10506794302872580091421457 7880095727154435068566093)
      ·
        refine ⟨2955035897682913150712285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7880095727154435068566093 2955035897682913150712285)
        ·
          refine ⟨1108138461631092431517107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2955035897682913150712285 1108138461631092431517107)
          ·
            refine ⟨1662207692446638647275661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1108138461631092431517107 1662207692446638647275661)
            ·
              refine ⟨623327884667489492728373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1662207692446638647275661 623327884667489492728373)
              ·
                refine ⟨58436989187577139943285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 623327884667489492728373 58436989187577139943285)
                ·
                  rfl

theorem cell21_768188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 3, 5].length) (baseStart_768188 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_768188 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_768188 prefixEnd_768188 := by exact prefixLift 768188
  have htrace : WordTrace (prefixWord ++ tailWord_768188) baseStart_768188 baseEnd_768188 := by
    simpa [prefixWord, tailWord_768188, baseEnd_768188] using wordTrace_append hprefix tailTrace_768188
  have hstable : (prefixWord ++ tailWord_768188).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768188).length < 2 ^ (prefixWord ++ tailWord_768188).sum := by decide
  have hdescent : baseEnd_768188 < baseStart_768188 := by decide
  rcases family_descends (prefixWord ++ tailWord_768188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768216 : List Nat := [2, 1, 2, 2, 4, 2, 1, 1, 6]
def baseStart_768216 : Nat := 118140960795 + 768216 * 2 ^ 59
def prefixEnd_768216 : Nat := 4983230072969 + 3 ^ 40 * 768216 * 2
def baseEnd_768216 : Nat := 175317357544209593363131

theorem tailTrace_768216 : CollatzResearch.WordTrace tailWord_768216 prefixEnd_768216 175317357544209593363131 := by
  unfold tailWord_768216
  simp only [CollatzResearch.WordTrace]
  refine ⟨14009569692446053846238251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18679426256594738461651001 14009569692446053846238251)
  ·
    refine ⟨21014354538669080769357377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14009569692446053846238251 21014354538669080769357377)
    ·
      refine ⟨15760765904001810577018033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21014354538669080769357377 15760765904001810577018033)
      ·
        refine ⟨11820574428001357932763525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15760765904001810577018033 11820574428001357932763525)
        ·
          refine ⟨2216357705250254612393161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11820574428001357932763525 2216357705250254612393161)
          ·
            refine ⟨1662268278937690959294871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2216357705250254612393161 1662268278937690959294871)
            ·
              refine ⟨2493402418406536438942307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1662268278937690959294871 2493402418406536438942307)
              ·
                refine ⟨3740103627609804658413461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2493402418406536438942307 3740103627609804658413461)
                ·
                  refine ⟨175317357544209593363131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3740103627609804658413461 175317357544209593363131)
                  ·
                    rfl

theorem cell21_768216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 1, 6].length) (baseStart_768216 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_768216 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_768216 prefixEnd_768216 := by exact prefixLift 768216
  have htrace : WordTrace (prefixWord ++ tailWord_768216) baseStart_768216 baseEnd_768216 := by
    simpa [prefixWord, tailWord_768216, baseEnd_768216] using wordTrace_append hprefix tailTrace_768216
  have hstable : (prefixWord ++ tailWord_768216).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768216).length < 2 ^ (prefixWord ++ tailWord_768216).sum := by decide
  have hdescent : baseEnd_768216 < baseStart_768216 := by decide
  rcases family_descends (prefixWord ++ tailWord_768216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768320 : List Nat := [2, 1, 1, 2, 2, 1, 2, 1, 9]
def baseStart_768320 : Nat := 118140960795 + 768320 * 2 ^ 59
def prefixEnd_768320 : Nat := 4983230072969 + 3 ^ 40 * 768320 * 2
def baseEnd_768320 : Nat := 175341091761128523629585

theorem tailTrace_768320 : CollatzResearch.WordTrace tailWord_768320 prefixEnd_768320 175341091761128523629585 := by
  unfold tailWord_768320
  simp only [CollatzResearch.WordTrace]
  refine ⟨14011466288257666727131207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18681955051010222302841609 14011466288257666727131207)
  ·
    refine ⟨21017199432386500090696811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14011466288257666727131207 21017199432386500090696811)
    ·
      refine ⟨31525799148579750136045217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21017199432386500090696811 31525799148579750136045217)
      ·
        refine ⟨23644349361434812602033913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31525799148579750136045217 23644349361434812602033913)
        ·
          refine ⟨17733262021076109451525435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23644349361434812602033913 17733262021076109451525435)
          ·
            refine ⟨26599893031614164177288153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17733262021076109451525435 26599893031614164177288153)
            ·
              refine ⟨19949919773710623132966115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26599893031614164177288153 19949919773710623132966115)
              ·
                refine ⟨29924879660565934699449173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19949919773710623132966115 29924879660565934699449173)
                ·
                  refine ⟨175341091761128523629585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 29924879660565934699449173 175341091761128523629585)
                  ·
                    rfl

theorem cell21_768320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 9].length) (baseStart_768320 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_768320 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_768320 prefixEnd_768320 := by exact prefixLift 768320
  have htrace : WordTrace (prefixWord ++ tailWord_768320) baseStart_768320 baseEnd_768320 := by
    simpa [prefixWord, tailWord_768320, baseEnd_768320] using wordTrace_append hprefix tailTrace_768320
  have hstable : (prefixWord ++ tailWord_768320).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768320).length < 2 ^ (prefixWord ++ tailWord_768320).sum := by decide
  have hdescent : baseEnd_768320 < baseStart_768320 := by decide
  rcases family_descends (prefixWord ++ tailWord_768320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768354 : List Nat := [3, 3, 2, 1, 1, 3, 1, 2, 5]
def baseStart_768354 : Nat := 118140960795 + 768354 * 2 ^ 59
def prefixEnd_768354 : Nat := 4983230072969 + 3 ^ 40 * 768354 * 2
def baseEnd_768354 : Nat := 175348851024352020062849

theorem tailTrace_768354 : CollatzResearch.WordTrace tailWord_768354 prefixEnd_768354 175348851024352020062849 := by
  unfold tailWord_768354
  simp only [CollatzResearch.WordTrace]
  refine ⟨7006043164598039315250029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18682781772261438174000077 7006043164598039315250029)
  ·
    refine ⟨2627266186724264743218761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7006043164598039315250029 2627266186724264743218761)
    ·
      refine ⟨1970449640043198557414071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2627266186724264743218761 1970449640043198557414071)
      ·
        refine ⟨2955674460064797836121107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1970449640043198557414071 2955674460064797836121107)
        ·
          refine ⟨4433511690097196754181661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2955674460064797836121107 4433511690097196754181661)
          ·
            refine ⟨1662566883786448782818123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4433511690097196754181661 1662566883786448782818123)
            ·
              refine ⟨2493850325679673174227185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1662566883786448782818123 2493850325679673174227185)
              ·
                refine ⟨1870387744259754880670389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2493850325679673174227185 1870387744259754880670389)
                ·
                  refine ⟨175348851024352020062849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1870387744259754880670389 175348851024352020062849)
                  ·
                    rfl

theorem cell21_768354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 2, 5].length) (baseStart_768354 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_768354 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_768354 prefixEnd_768354 := by exact prefixLift 768354
  have htrace : WordTrace (prefixWord ++ tailWord_768354) baseStart_768354 baseEnd_768354 := by
    simpa [prefixWord, tailWord_768354, baseEnd_768354] using wordTrace_append hprefix tailTrace_768354
  have hstable : (prefixWord ++ tailWord_768354).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768354).length < 2 ^ (prefixWord ++ tailWord_768354).sum := by decide
  have hdescent : baseEnd_768354 < baseStart_768354 := by decide
  rcases family_descends (prefixWord ++ tailWord_768354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768385 : List Nat := [1, 2, 4, 3, 1, 1, 3, 2, 4]
def baseStart_768385 : Nat := 118140960795 + 768385 * 2 ^ 59
def prefixEnd_768385 : Nat := 4983230072969 + 3 ^ 40 * 768385 * 2
def baseEnd_768385 : Nat := 175355925646702855046119

theorem tailTrace_768385 : CollatzResearch.WordTrace tailWord_768385 prefixEnd_768385 175355925646702855046119 := by
  unfold tailWord_768385
  simp only [CollatzResearch.WordTrace]
  refine ⟨28025303321279849555378609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18683535547519899703585739 28025303321279849555378609)
  ·
    refine ⟨21018977490959887166533957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28025303321279849555378609 21018977490959887166533957)
    ·
      refine ⟨3941058279554978843725117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21018977490959887166533957 3941058279554978843725117)
      ·
        refine ⟨1477896854833117066396919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3941058279554978843725117 1477896854833117066396919)
        ·
          refine ⟨2216845282249675599595379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1477896854833117066396919 2216845282249675599595379)
          ·
            refine ⟨3325267923374513399393069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2216845282249675599595379 3325267923374513399393069)
            ·
              refine ⟨1246975471265442524772401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3325267923374513399393069 1246975471265442524772401)
              ·
                refine ⟨935231603449081893579301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1246975471265442524772401 935231603449081893579301)
                ·
                  refine ⟨175355925646702855046119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 935231603449081893579301 175355925646702855046119)
                  ·
                    rfl

theorem cell21_768385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3, 2, 4].length) (baseStart_768385 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_768385 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_768385 prefixEnd_768385 := by exact prefixLift 768385
  have htrace : WordTrace (prefixWord ++ tailWord_768385) baseStart_768385 baseEnd_768385 := by
    simpa [prefixWord, tailWord_768385, baseEnd_768385] using wordTrace_append hprefix tailTrace_768385
  have hstable : (prefixWord ++ tailWord_768385).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768385).length < 2 ^ (prefixWord ++ tailWord_768385).sum := by decide
  have hdescent : baseEnd_768385 < baseStart_768385 := by decide
  rcases family_descends (prefixWord ++ tailWord_768385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768444 : List Nat := [2, 2, 2, 4, 1, 1, 2, 1, 6]
def baseStart_768444 : Nat := 118140960795 + 768444 * 2 ^ 59
def prefixEnd_768444 : Nat := 4983230072969 + 3 ^ 40 * 768444 * 2
def baseEnd_768444 : Nat := 175369390250531863562665

theorem tailTrace_768444 : CollatzResearch.WordTrace tailWord_768444 prefixEnd_768444 175369390250531863562665 := by
  unfold tailWord_768444
  simp only [CollatzResearch.WordTrace]
  refine ⟨14013727614033051315888193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18684970152044068421184257 14013727614033051315888193)
  ·
    refine ⟨10510295710524788486916145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14013727614033051315888193 10510295710524788486916145)
    ·
      refine ⟨7882721782893591365187109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10510295710524788486916145 7882721782893591365187109)
      ·
        refine ⟨1478010334292548380972583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7882721782893591365187109 1478010334292548380972583)
        ·
          refine ⟨2217015501438822571458875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1478010334292548380972583 2217015501438822571458875)
          ·
            refine ⟨3325523252158233857188313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2217015501438822571458875 3325523252158233857188313)
            ·
              refine ⟨2494142439118675392891235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3325523252158233857188313 2494142439118675392891235)
              ·
                refine ⟨3741213658678013089336853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2494142439118675392891235 3741213658678013089336853)
                ·
                  refine ⟨175369390250531863562665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3741213658678013089336853 175369390250531863562665)
                  ·
                    rfl

theorem cell21_768444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 1, 6].length) (baseStart_768444 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_768444 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_768444 prefixEnd_768444 := by exact prefixLift 768444
  have htrace : WordTrace (prefixWord ++ tailWord_768444) baseStart_768444 baseEnd_768444 := by
    simpa [prefixWord, tailWord_768444, baseEnd_768444] using wordTrace_append hprefix tailTrace_768444
  have hstable : (prefixWord ++ tailWord_768444).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768444).length < 2 ^ (prefixWord ++ tailWord_768444).sum := by decide
  have hdescent : baseEnd_768444 < baseStart_768444 := by decide
  rcases family_descends (prefixWord ++ tailWord_768444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768458 : List Nat := [3, 1, 2, 1, 2, 2, 4, 6]
def baseStart_768458 : Nat := 118140960795 + 768458 * 2 ^ 59
def prefixEnd_768458 : Nat := 4983230072969 + 3 ^ 40 * 768458 * 2
def baseEnd_768458 : Nat := 58457528413756983443101

theorem tailTrace_768458 : CollatzResearch.WordTrace tailWord_768458 prefixEnd_768458 58457528413756983443101 := by
  unfold tailWord_768458
  simp only [CollatzResearch.WordTrace]
  refine ⟨7006991462503845755696507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18685310566676922015190685 7006991462503845755696507)
  ·
    refine ⟨10510487193755768633544761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7006991462503845755696507 10510487193755768633544761)
    ·
      refine ⟨7882865395316826475158571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10510487193755768633544761 7882865395316826475158571)
      ·
        refine ⟨11824298092975239712737857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7882865395316826475158571 11824298092975239712737857)
        ·
          refine ⟨8868223569731429784553393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11824298092975239712737857 8868223569731429784553393)
          ·
            refine ⟨6651167677298572338415045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8868223569731429784553393 6651167677298572338415045)
            ·
              refine ⟨1247093939493482313452821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6651167677298572338415045 1247093939493482313452821)
              ·
                refine ⟨58457528413756983443101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1247093939493482313452821 58457528413756983443101)
                ·
                  rfl

theorem cell21_768458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4, 6].length) (baseStart_768458 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_768458 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_768458 prefixEnd_768458 := by exact prefixLift 768458
  have htrace : WordTrace (prefixWord ++ tailWord_768458) baseStart_768458 baseEnd_768458 := by
    simpa [prefixWord, tailWord_768458, baseEnd_768458] using wordTrace_append hprefix tailTrace_768458
  have hstable : (prefixWord ++ tailWord_768458).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768458).length < 2 ^ (prefixWord ++ tailWord_768458).sum := by decide
  have hdescent : baseEnd_768458 < baseStart_768458 := by decide
  rcases family_descends (prefixWord ++ tailWord_768458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768472 : List Nat := [2, 1, 2, 2, 2, 1, 1, 3, 7]
def baseStart_768472 : Nat := 118140960795 + 768472 * 2 ^ 59
def prefixEnd_768472 : Nat := 4983230072969 + 3 ^ 40 * 768472 * 2
def baseEnd_768472 : Nat := 175375780232010037095941

theorem tailTrace_768472 : CollatzResearch.WordTrace tailWord_768472 prefixEnd_768472 175375780232010037095941 := by
  unfold tailWord_768472
  simp only [CollatzResearch.WordTrace]
  refine ⟨14014238235982331706897835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18685650981309775609197113 14014238235982331706897835)
  ·
    refine ⟨21021357353973497560346753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14014238235982331706897835 21021357353973497560346753)
    ·
      refine ⟨15766018015480123170260065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21021357353973497560346753 15766018015480123170260065)
      ·
        refine ⟨11824513511610092377695049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15766018015480123170260065 11824513511610092377695049)
        ·
          refine ⟨8868385133707569283271287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11824513511610092377695049 8868385133707569283271287)
          ·
            refine ⟨13302577700561353924906931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8868385133707569283271287 13302577700561353924906931)
            ·
              refine ⟨19953866550842030887360397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13302577700561353924906931 19953866550842030887360397)
              ·
                refine ⟨7482699956565761582760149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19953866550842030887360397 7482699956565761582760149)
                ·
                  refine ⟨175375780232010037095941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7482699956565761582760149 175375780232010037095941)
                  ·
                    rfl

theorem cell21_768472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 3, 7].length) (baseStart_768472 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_768472 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_768472 prefixEnd_768472 := by exact prefixLift 768472
  have htrace : WordTrace (prefixWord ++ tailWord_768472) baseStart_768472 baseEnd_768472 := by
    simpa [prefixWord, tailWord_768472, baseEnd_768472] using wordTrace_append hprefix tailTrace_768472
  have hstable : (prefixWord ++ tailWord_768472).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768472).length < 2 ^ (prefixWord ++ tailWord_768472).sum := by decide
  have hdescent : baseEnd_768472 < baseStart_768472 := by decide
  rcases family_descends (prefixWord ++ tailWord_768472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768565 : List Nat := [1, 3, 3, 1, 1, 2, 4, 1, 5]
def baseStart_768565 : Nat := 118140960795 + 768565 * 2 ^ 59
def prefixEnd_768565 : Nat := 4983230072969 + 3 ^ 40 * 768565 * 2
def baseEnd_768565 : Nat := 175397004099062542045751

theorem tailTrace_768565 : CollatzResearch.WordTrace tailWord_768565 prefixEnd_768565 175397004099062542045751 := by
  unfold tailWord_768565
  simp only [CollatzResearch.WordTrace]
  refine ⟨28031868460627740296931149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18687912307085160197954099 28031868460627740296931149)
  ·
    refine ⟨10511950672735402611349181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28031868460627740296931149 10511950672735402611349181)
    ·
      refine ⟨3941981502275775979255943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10511950672735402611349181 3941981502275775979255943)
      ·
        refine ⟨5912972253413663968883915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3941981502275775979255943 5912972253413663968883915)
        ·
          refine ⟨8869458380120495953325873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5912972253413663968883915 8869458380120495953325873)
          ·
            refine ⟨6652093785090371964994405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8869458380120495953325873 6652093785090371964994405)
            ·
              refine ⟨1247267584704444743436451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6652093785090371964994405 1247267584704444743436451)
              ·
                refine ⟨1870901377056667115154677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1247267584704444743436451 1870901377056667115154677)
                ·
                  refine ⟨175397004099062542045751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1870901377056667115154677 175397004099062542045751)
                  ·
                    rfl

theorem cell21_768565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4, 1, 5].length) (baseStart_768565 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_768565 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_768565 prefixEnd_768565 := by exact prefixLift 768565
  have htrace : WordTrace (prefixWord ++ tailWord_768565) baseStart_768565 baseEnd_768565 := by
    simpa [prefixWord, tailWord_768565, baseEnd_768565] using wordTrace_append hprefix tailTrace_768565
  have hstable : (prefixWord ++ tailWord_768565).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768565).length < 2 ^ (prefixWord ++ tailWord_768565).sum := by decide
  have hdescent : baseEnd_768565 < baseStart_768565 := by decide
  rcases family_descends (prefixWord ++ tailWord_768565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768579 : List Nat := [1, 1, 1, 3, 1, 2, 1, 7, 4]
def baseStart_768579 : Nat := 118140960795 + 768579 * 2 ^ 59
def prefixEnd_768579 : Nat := 4983230072969 + 3 ^ 40 * 768579 * 2
def baseEnd_768579 : Nat := 175400199089801628812389

theorem tailTrace_768579 : CollatzResearch.WordTrace tailWord_768579 prefixEnd_768579 175400199089801628812389 := by
  unfold tailWord_768579
  simp only [CollatzResearch.WordTrace]
  refine ⟨28032379082577020687940791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18688252721718013791960527 28032379082577020687940791)
  ·
    refine ⟨42048568623865531031911187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28032379082577020687940791 42048568623865531031911187)
    ·
      refine ⟨63072852935798296547866781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42048568623865531031911187 63072852935798296547866781)
      ·
        refine ⟨23652319850924361205450043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63072852935798296547866781 23652319850924361205450043)
        ·
          refine ⟨35478479776386541808175065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23652319850924361205450043 35478479776386541808175065)
          ·
            refine ⟨26608859832289906356131299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35478479776386541808175065 26608859832289906356131299)
            ·
              refine ⟨39913289748434859534196949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26608859832289906356131299 39913289748434859534196949)
              ·
                refine ⟨935467728478942020332741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 39913289748434859534196949 935467728478942020332741)
                ·
                  refine ⟨175400199089801628812389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 935467728478942020332741 175400199089801628812389)
                  ·
                    rfl

theorem cell21_768579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 7, 4].length) (baseStart_768579 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_768579 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_768579 prefixEnd_768579 := by exact prefixLift 768579
  have htrace : WordTrace (prefixWord ++ tailWord_768579) baseStart_768579 baseEnd_768579 := by
    simpa [prefixWord, tailWord_768579, baseEnd_768579] using wordTrace_append hprefix tailTrace_768579
  have hstable : (prefixWord ++ tailWord_768579).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768579).length < 2 ^ (prefixWord ++ tailWord_768579).sum := by decide
  have hdescent : baseEnd_768579 < baseStart_768579 := by decide
  rcases family_descends (prefixWord ++ tailWord_768579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768616 : List Nat := [2, 1, 4, 3, 2, 1, 3, 2, 3]
def baseStart_768616 : Nat := 118140960795 + 768616 * 2 ^ 59
def prefixEnd_768616 : Nat := 4983230072969 + 3 ^ 40 * 768616 * 2
def baseEnd_768616 : Nat := 175408642993897786695647

theorem tailTrace_768616 : CollatzResearch.WordTrace tailWord_768616 prefixEnd_768616 175408642993897786695647 := by
  unfold tailWord_768616
  simp only [CollatzResearch.WordTrace]
  refine ⟨14016864291721488003518851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18689152388961984004691801 14016864291721488003518851)
  ·
    refine ⟨21025296437582232005278277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14016864291721488003518851 21025296437582232005278277)
    ·
      refine ⟨3942243082046668500989677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21025296437582232005278277 3942243082046668500989677)
      ·
        refine ⟨1478341155767500687871129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3942243082046668500989677 1478341155767500687871129)
        ·
          refine ⟨1108755866825625515903347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1478341155767500687871129 1108755866825625515903347)
          ·
            refine ⟨1663133800238438273855021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1108755866825625515903347 1663133800238438273855021)
            ·
              refine ⟨623675175089414352695633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1663133800238438273855021 623675175089414352695633)
              ·
                refine ⟨467756381317060764521725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 623675175089414352695633 467756381317060764521725)
                ·
                  refine ⟨175408642993897786695647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 467756381317060764521725 175408642993897786695647)
                  ·
                    rfl

theorem cell21_768616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 3, 2, 3].length) (baseStart_768616 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_768616 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_768616 prefixEnd_768616 := by exact prefixLift 768616
  have htrace : WordTrace (prefixWord ++ tailWord_768616) baseStart_768616 baseEnd_768616 := by
    simpa [prefixWord, tailWord_768616, baseEnd_768616] using wordTrace_append hprefix tailTrace_768616
  have hstable : (prefixWord ++ tailWord_768616).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768616).length < 2 ^ (prefixWord ++ tailWord_768616).sum := by decide
  have hdescent : baseEnd_768616 < baseStart_768616 := by decide
  rcases family_descends (prefixWord ++ tailWord_768616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768762 : List Nat := [3, 1, 1, 1, 1, 3, 6, 5]
def baseStart_768762 : Nat := 118140960795 + 768762 * 2 ^ 59
def prefixEnd_768762 : Nat := 4983230072969 + 3 ^ 40 * 768762 * 2
def baseEnd_768762 : Nat := 58480654061011325754005

theorem tailTrace_768762 : CollatzResearch.WordTrace tailWord_768762 prefixEnd_768762 58480654061011325754005 := by
  unfold tailWord_768762
  simp only [CollatzResearch.WordTrace]
  refine ⟨7009763410228510735463135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18692702427276028627901693 7009763410228510735463135)
  ·
    refine ⟨10514645115342766103194703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7009763410228510735463135 10514645115342766103194703)
    ·
      refine ⟨15771967673014149154792055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10514645115342766103194703 15771967673014149154792055)
      ·
        refine ⟨23657951509521223732188083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15771967673014149154792055 23657951509521223732188083)
        ·
          refine ⟨35486927264281835598282125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23657951509521223732188083 35486927264281835598282125)
          ·
            refine ⟨13307597724105688349355797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35486927264281835598282125 13307597724105688349355797)
            ·
              refine ⟨623793643317454141376053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 13307597724105688349355797 623793643317454141376053)
              ·
                refine ⟨58480654061011325754005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 623793643317454141376053 58480654061011325754005)
                ·
                  rfl

theorem cell21_768762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 6, 5].length) (baseStart_768762 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_768762 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_768762 prefixEnd_768762 := by exact prefixLift 768762
  have htrace : WordTrace (prefixWord ++ tailWord_768762) baseStart_768762 baseEnd_768762 := by
    simpa [prefixWord, tailWord_768762, baseEnd_768762] using wordTrace_append hprefix tailTrace_768762
  have hstable : (prefixWord ++ tailWord_768762).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768762).length < 2 ^ (prefixWord ++ tailWord_768762).sum := by decide
  have hdescent : baseEnd_768762 < baseStart_768762 := by decide
  rcases family_descends (prefixWord ++ tailWord_768762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768928 : List Nat := [2, 1, 1, 4, 1, 1, 4, 2, 5]
def baseStart_768928 : Nat := 118140960795 + 768928 * 2 ^ 59
def prefixEnd_768928 : Nat := 4983230072969 + 3 ^ 40 * 768928 * 2
def baseEnd_768928 : Nat := 175479845644654577495009

theorem tailTrace_768928 : CollatzResearch.WordTrace tailWord_768928 prefixEnd_768928 175479845644654577495009 := by
  unfold tailWord_768928
  simp only [CollatzResearch.WordTrace]
  refine ⟨14022554079156326646197719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18696738772208435528263625 14022554079156326646197719)
  ·
    refine ⟨21033831118734489969296579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14022554079156326646197719 21033831118734489969296579)
    ·
      refine ⟨31550746678101734953944869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21033831118734489969296579 31550746678101734953944869)
      ·
        refine ⟨5915765002144075303864663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31550746678101734953944869 5915765002144075303864663)
        ·
          refine ⟨8873647503216112955796995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5915765002144075303864663 8873647503216112955796995)
          ·
            refine ⟨13310471254824169433695493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8873647503216112955796995 13310471254824169433695493)
            ·
              refine ⟨2495713360279531768817905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13310471254824169433695493 2495713360279531768817905)
              ·
                refine ⟨1871785020209648826613429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2495713360279531768817905 1871785020209648826613429)
                ·
                  refine ⟨175479845644654577495009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1871785020209648826613429 175479845644654577495009)
                  ·
                    rfl

theorem cell21_768928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 2, 5].length) (baseStart_768928 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_768928 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_768928 prefixEnd_768928 := by exact prefixLift 768928
  have htrace : WordTrace (prefixWord ++ tailWord_768928) baseStart_768928 baseEnd_768928 := by
    simpa [prefixWord, tailWord_768928, baseEnd_768928] using wordTrace_append hprefix tailTrace_768928
  have hstable : (prefixWord ++ tailWord_768928).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768928).length < 2 ^ (prefixWord ++ tailWord_768928).sum := by decide
  have hdescent : baseEnd_768928 < baseStart_768928 := by decide
  rcases family_descends (prefixWord ++ tailWord_768928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769013 : List Nat := [1, 3, 5, 2, 1, 2, 2, 2, 3]
def baseStart_769013 : Nat := 118140960795 + 769013 * 2 ^ 59
def prefixEnd_769013 : Nat := 4983230072969 + 3 ^ 40 * 769013 * 2
def baseEnd_769013 : Nat := 175499243802713318578169

theorem tailTrace_769013 : CollatzResearch.WordTrace tailWord_769013 prefixEnd_769013 175499243802713318578169 := by
  unfold tailWord_769013
  simp only [CollatzResearch.WordTrace]
  refine ⟨28048208363004712809239693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18698805575336475206159795 28048208363004712809239693)
  ·
    refine ⟨10518078136126767303464885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28048208363004712809239693 10518078136126767303464885)
    ·
      refine ⟨986069825261884434699833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10518078136126767303464885 986069825261884434699833)
      ·
        refine ⟨739552368946413326024875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 986069825261884434699833 739552368946413326024875)
        ·
          refine ⟨1109328553419619989037313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 739552368946413326024875 1109328553419619989037313)
          ·
            refine ⟨831996415064714991777985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1109328553419619989037313 831996415064714991777985)
            ·
              refine ⟨623997311298536243833489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 831996415064714991777985 623997311298536243833489)
              ·
                refine ⟨467997983473902182875117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 623997311298536243833489 467997983473902182875117)
                ·
                  refine ⟨175499243802713318578169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 467997983473902182875117 175499243802713318578169)
                  ·
                    rfl

theorem cell21_769013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 2, 2, 3].length) (baseStart_769013 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_769013 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_769013 prefixEnd_769013 := by exact prefixLift 769013
  have htrace : WordTrace (prefixWord ++ tailWord_769013) baseStart_769013 baseEnd_769013 := by
    simpa [prefixWord, tailWord_769013, baseEnd_769013] using wordTrace_append hprefix tailTrace_769013
  have hstable : (prefixWord ++ tailWord_769013).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769013).length < 2 ^ (prefixWord ++ tailWord_769013).sum := by decide
  have hdescent : baseEnd_769013 < baseStart_769013 := by decide
  rcases family_descends (prefixWord ++ tailWord_769013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769018 : List Nat := [3, 1, 1, 1, 1, 2, 1, 5, 6]
def baseStart_769018 : Nat := 118140960795 + 769018 * 2 ^ 59
def prefixEnd_769018 : Nat := 4983230072969 + 3 ^ 40 * 769018 * 2
def baseEnd_769018 : Nat := 175500384870834420994825

theorem tailTrace_769018 : CollatzResearch.WordTrace tailWord_769018 prefixEnd_769018 175500384870834420994825 := by
  unfold tailWord_769018
  simp only [CollatzResearch.WordTrace]
  refine ⟨7012097681996649665792927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18698927151991065775447805 7012097681996649665792927)
  ·
    refine ⟨10518146522994974498689391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7012097681996649665792927 10518146522994974498689391)
    ·
      refine ⟨15777219784492461748034087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10518146522994974498689391 15777219784492461748034087)
      ·
        refine ⟨23665829676738692622051131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15777219784492461748034087 23665829676738692622051131)
        ·
          refine ⟨35498744515108038933076697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23665829676738692622051131 35498744515108038933076697)
          ·
            refine ⟨26624058386331029199807523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35498744515108038933076697 26624058386331029199807523)
            ·
              refine ⟨39936087579496543799711285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26624058386331029199807523 39936087579496543799711285)
              ·
                refine ⟨3744008210577800981222933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39936087579496543799711285 3744008210577800981222933)
                ·
                  refine ⟨175500384870834420994825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3744008210577800981222933 175500384870834420994825)
                  ·
                    rfl

theorem cell21_769018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 5, 6].length) (baseStart_769018 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_769018 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_769018 prefixEnd_769018 := by exact prefixLift 769018
  have htrace : WordTrace (prefixWord ++ tailWord_769018) baseStart_769018 baseEnd_769018 := by
    simpa [prefixWord, tailWord_769018, baseEnd_769018] using wordTrace_append hprefix tailTrace_769018
  have hstable : (prefixWord ++ tailWord_769018).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769018).length < 2 ^ (prefixWord ++ tailWord_769018).sum := by decide
  have hdescent : baseEnd_769018 < baseStart_769018 := by decide
  rcases family_descends (prefixWord ++ tailWord_769018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769035 : List Nat := [1, 1, 1, 1, 6, 2, 2, 3, 4]
def baseStart_769035 : Nat := 118140960795 + 769035 * 2 ^ 59
def prefixEnd_769035 : Nat := 4983230072969 + 3 ^ 40 * 769035 * 2
def baseEnd_769035 : Nat := 175504264502446169211457

theorem tailTrace_769035 : CollatzResearch.WordTrace tailWord_769035 prefixEnd_769035 175504264502446169211457 := by
  unfold tailWord_769035
  simp only [CollatzResearch.WordTrace]
  refine ⟨28049010768925010566540559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18699340512616673711027039 28049010768925010566540559)
  ·
    refine ⟨42073516153387515849810839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28049010768925010566540559 42073516153387515849810839)
    ·
      refine ⟨63110274230081273774716259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42073516153387515849810839 63110274230081273774716259)
      ·
        refine ⟨94665411345121910662074389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63110274230081273774716259 94665411345121910662074389)
        ·
          refine ⟨4437441156802589562284737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 94665411345121910662074389 4437441156802589562284737)
          ·
            refine ⟨3328080867601942171713553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4437441156802589562284737 3328080867601942171713553)
            ·
              refine ⟨2496060650701456628785165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3328080867601942171713553 2496060650701456628785165)
              ·
                refine ⟨936022744013046235794437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2496060650701456628785165 936022744013046235794437)
                ·
                  refine ⟨175504264502446169211457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 936022744013046235794437 175504264502446169211457)
                  ·
                    rfl

theorem cell21_769035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 3, 4].length) (baseStart_769035 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_769035 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_769035 prefixEnd_769035 := by exact prefixLift 769035
  have htrace : WordTrace (prefixWord ++ tailWord_769035) baseStart_769035 baseEnd_769035 := by
    simpa [prefixWord, tailWord_769035, baseEnd_769035] using wordTrace_append hprefix tailTrace_769035
  have hstable : (prefixWord ++ tailWord_769035).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769035).length < 2 ^ (prefixWord ++ tailWord_769035).sum := by decide
  have hdescent : baseEnd_769035 < baseStart_769035 := by decide
  rcases family_descends (prefixWord ++ tailWord_769035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769066 : List Nat := [3, 1, 4, 1, 3, 1, 8]
def baseStart_769066 : Nat := 118140960795 + 769066 * 2 ^ 59
def prefixEnd_769066 : Nat := 4983230072969 + 3 ^ 40 * 769066 * 2
def baseEnd_769066 : Nat := 19501259902755222688303

theorem tailTrace_769066 : CollatzResearch.WordTrace tailWord_769066 prefixEnd_769066 19501259902755222688303 := by
  unfold tailWord_769066
  simp only [CollatzResearch.WordTrace]
  refine ⟨7012535357953175715229763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18700094287875135240612701 7012535357953175715229763)
  ·
    refine ⟨10518803036929763572844645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7012535357953175715229763 10518803036929763572844645)
    ·
      refine ⟨1972275569424330669908371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10518803036929763572844645 1972275569424330669908371)
      ·
        refine ⟨2958413354136496004862557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1972275569424330669908371 2958413354136496004862557)
        ·
          refine ⟨1109405007801186001823459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2958413354136496004862557 1109405007801186001823459)
          ·
            refine ⟨1664107511701779002735189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1109405007801186001823459 1664107511701779002735189)
            ·
              refine ⟨19501259902755222688303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1664107511701779002735189 19501259902755222688303)
              ·
                rfl

theorem cell21_769066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 8].length) (baseStart_769066 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_769066 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_769066 prefixEnd_769066 := by exact prefixLift 769066
  have htrace : WordTrace (prefixWord ++ tailWord_769066) baseStart_769066 baseEnd_769066 := by
    simpa [prefixWord, tailWord_769066, baseEnd_769066] using wordTrace_append hprefix tailTrace_769066
  have hstable : (prefixWord ++ tailWord_769066).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769066).length < 2 ^ (prefixWord ++ tailWord_769066).sum := by decide
  have hdescent : baseEnd_769066 < baseStart_769066 := by decide
  rcases family_descends (prefixWord ++ tailWord_769066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769080 : List Nat := [2, 1, 2, 1, 5, 1, 1, 3, 5]
def baseStart_769080 : Nat := 118140960795 + 769080 * 2 ^ 59
def prefixEnd_769080 : Nat := 4983230072969 + 3 ^ 40 * 769080 * 2
def baseEnd_769080 : Nat := 175514534115536090961365

theorem tailTrace_769080 : CollatzResearch.WordTrace tailWord_769080 prefixEnd_769080 175514534115536090961365 := by
  unfold tailWord_769080
  simp only [CollatzResearch.WordTrace]
  refine ⟨14025326026880991625964347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18700434702507988834619129 14025326026880991625964347)
  ·
    refine ⟨21037989040321487438946521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14025326026880991625964347 21037989040321487438946521)
    ·
      refine ⟨15778491780241115579209891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21037989040321487438946521 15778491780241115579209891)
      ·
        refine ⟨23667737670361673368814837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15778491780241115579209891 23667737670361673368814837)
        ·
          refine ⟨2218850406596406878326391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23667737670361673368814837 2218850406596406878326391)
          ·
            refine ⟨3328275609894610317489587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2218850406596406878326391 3328275609894610317489587)
            ·
              refine ⟨4992413414841915476234381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3328275609894610317489587 4992413414841915476234381)
              ·
                refine ⟨1872155030565718303587893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4992413414841915476234381 1872155030565718303587893)
                ·
                  refine ⟨175514534115536090961365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1872155030565718303587893 175514534115536090961365)
                  ·
                    rfl

theorem cell21_769080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 3, 5].length) (baseStart_769080 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_769080 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_769080 prefixEnd_769080 := by exact prefixLift 769080
  have htrace : WordTrace (prefixWord ++ tailWord_769080) baseStart_769080 baseEnd_769080 := by
    simpa [prefixWord, tailWord_769080, baseEnd_769080] using wordTrace_append hprefix tailTrace_769080
  have hstable : (prefixWord ++ tailWord_769080).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769080).length < 2 ^ (prefixWord ++ tailWord_769080).sum := by decide
  have hdescent : baseEnd_769080 < baseStart_769080 := by decide
  rcases family_descends (prefixWord ++ tailWord_769080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769142 : List Nat := [5, 1, 1, 2, 1, 1, 4, 6]
def baseStart_769142 : Nat := 118140960795 + 769142 * 2 ^ 59
def prefixEnd_769142 : Nat := 4983230072969 + 3 ^ 40 * 769142 * 2
def baseEnd_769142 : Nat := 58509561120079253642635

theorem tailTrace_769142 : CollatzResearch.WordTrace tailWord_769142 prefixEnd_769142 58509561120079253642635 := by
  unfold tailWord_769142
  simp only [CollatzResearch.WordTrace]
  refine ⟨1753307086221085490042855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18701942253024911893790453 1753307086221085490042855)
  ·
    refine ⟨2629960629331628235064283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1753307086221085490042855 2629960629331628235064283)
    ·
      refine ⟨3944940943997442352596425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2629960629331628235064283 3944940943997442352596425)
      ·
        refine ⟨2958705707998081764447319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3944940943997442352596425 2958705707998081764447319)
        ·
          refine ⟨4438058561997122646670979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2958705707998081764447319 4438058561997122646670979)
          ·
            refine ⟨6657087842995683970006469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4438058561997122646670979 6657087842995683970006469)
            ·
              refine ⟨1248203970561690744376213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6657087842995683970006469 1248203970561690744376213)
              ·
                refine ⟨58509561120079253642635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1248203970561690744376213 58509561120079253642635)
                ·
                  rfl

theorem cell21_769142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4, 6].length) (baseStart_769142 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_769142 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_769142 prefixEnd_769142 := by exact prefixLift 769142
  have htrace : WordTrace (prefixWord ++ tailWord_769142) baseStart_769142 baseEnd_769142 := by
    simpa [prefixWord, tailWord_769142, baseEnd_769142] using wordTrace_append hprefix tailTrace_769142
  have hstable : (prefixWord ++ tailWord_769142).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769142).length < 2 ^ (prefixWord ++ tailWord_769142).sum := by decide
  have hdescent : baseEnd_769142 < baseStart_769142 := by decide
  rcases family_descends (prefixWord ++ tailWord_769142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769145 : List Nat := [1, 2, 1, 3, 5, 2, 2, 1, 4]
def baseStart_769145 : Nat := 118140960795 + 769145 * 2 ^ 59
def prefixEnd_769145 : Nat := 4983230072969 + 3 ^ 40 * 769145 * 2
def baseEnd_769145 : Nat := 175529368001110422377899

theorem tailTrace_769145 : CollatzResearch.WordTrace tailWord_769145 prefixEnd_769145 175529368001110422377899 := by
  unfold tailWord_769145
  simp only [CollatzResearch.WordTrace]
  refine ⟨28053022798526499353044889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18702015199017666235363259 28053022798526499353044889)
  ·
    refine ⟨21039767098894874514783667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28053022798526499353044889 21039767098894874514783667)
    ·
      refine ⟨31559650648342311772175501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21039767098894874514783667 31559650648342311772175501)
      ·
        refine ⟨11834868993128366914565813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31559650648342311772175501 11834868993128366914565813)
        ·
          refine ⟨1109518968105784398240545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11834868993128366914565813 1109518968105784398240545)
          ·
            refine ⟨832139226079338298680409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1109518968105784398240545 832139226079338298680409)
            ·
              refine ⟨624104419559503724010307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 832139226079338298680409 624104419559503724010307)
              ·
                refine ⟨936156629339255586015461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 624104419559503724010307 936156629339255586015461)
                ·
                  refine ⟨175529368001110422377899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 936156629339255586015461 175529368001110422377899)
                  ·
                    rfl

theorem cell21_769145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 2, 1, 4].length) (baseStart_769145 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_769145 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_769145 prefixEnd_769145 := by exact prefixLift 769145
  have htrace : WordTrace (prefixWord ++ tailWord_769145) baseStart_769145 baseEnd_769145 := by
    simpa [prefixWord, tailWord_769145, baseEnd_769145] using wordTrace_append hprefix tailTrace_769145
  have hstable : (prefixWord ++ tailWord_769145).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769145).length < 2 ^ (prefixWord ++ tailWord_769145).sum := by decide
  have hdescent : baseEnd_769145 < baseStart_769145 := by decide
  rcases family_descends (prefixWord ++ tailWord_769145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769215 : List Nat := [1, 1, 2, 2, 2, 2, 3, 1, 7]
def baseStart_769215 : Nat := 118140960795 + 769215 * 2 ^ 59
def prefixEnd_769215 : Nat := 4983230072969 + 3 ^ 40 * 769215 * 2
def baseEnd_769215 : Nat := 175545342954805856211089

theorem tailTrace_769215 : CollatzResearch.WordTrace tailWord_769215 prefixEnd_769215 175545342954805856211089 := by
  unfold tailWord_769215
  simp only [CollatzResearch.WordTrace]
  refine ⟨28055575908272901308093099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18703717272181934205395399 28055575908272901308093099)
  ·
    refine ⟨42083363862409351962139649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28055575908272901308093099 42083363862409351962139649)
    ·
      refine ⟨31562522896807013971604737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42083363862409351962139649 31562522896807013971604737)
      ·
        refine ⟨23671892172605260478703553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31562522896807013971604737 23671892172605260478703553)
        ·
          refine ⟨17753919129453945359027665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23671892172605260478703553 17753919129453945359027665)
          ·
            refine ⟨13315439347090459019270749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17753919129453945359027665 13315439347090459019270749)
            ·
              refine ⟨4993289755158922132226531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13315439347090459019270749 4993289755158922132226531)
              ·
                refine ⟨7489934632738383198339797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4993289755158922132226531 7489934632738383198339797)
                ·
                  refine ⟨175545342954805856211089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7489934632738383198339797 175545342954805856211089)
                  ·
                    rfl

theorem cell21_769215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 1, 7].length) (baseStart_769215 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_769215 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_769215 prefixEnd_769215 := by exact prefixLift 769215
  have htrace : WordTrace (prefixWord ++ tailWord_769215) baseStart_769215 baseEnd_769215 := by
    simpa [prefixWord, tailWord_769215, baseEnd_769215] using wordTrace_append hprefix tailTrace_769215
  have hstable : (prefixWord ++ tailWord_769215).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769215).length < 2 ^ (prefixWord ++ tailWord_769215).sum := by decide
  have hdescent : baseEnd_769215 < baseStart_769215 := by decide
  rcases family_descends (prefixWord ++ tailWord_769215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769238 : List Nat := [5, 2, 1, 2, 2, 2, 1, 2, 4]
def baseStart_769238 : Nat := 118140960795 + 769238 * 2 ^ 59
def prefixEnd_769238 : Nat := 4983230072969 + 3 ^ 40 * 769238 * 2
def baseEnd_769238 : Nat := 175550591868162927327709

theorem tailTrace_769238 : CollatzResearch.WordTrace tailWord_769238 prefixEnd_769238 175550591868162927327709 := by
  unfold tailWord_769238
  simp only [CollatzResearch.WordTrace]
  refine ⟨1753525924199348514761273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18704276524793050824120245 1753525924199348514761273)
  ·
    refine ⟨1315144443149511386070955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1753525924199348514761273 1315144443149511386070955)
    ·
      refine ⟨1972716664724267079106433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1315144443149511386070955 1972716664724267079106433)
      ·
        refine ⟨1479537498543200309329825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1972716664724267079106433 1479537498543200309329825)
        ·
          refine ⟨1109653123907400231997369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1479537498543200309329825 1109653123907400231997369)
          ·
            refine ⟨832239842930550173998027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1109653123907400231997369 832239842930550173998027)
            ·
              refine ⟨1248359764395825260997041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 832239842930550173998027 1248359764395825260997041)
              ·
                refine ⟨936269823296868945747781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1248359764395825260997041 936269823296868945747781)
                ·
                  refine ⟨175550591868162927327709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 936269823296868945747781 175550591868162927327709)
                  ·
                    rfl

theorem cell21_769238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_769238 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_769238 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_769238 prefixEnd_769238 := by exact prefixLift 769238
  have htrace : WordTrace (prefixWord ++ tailWord_769238) baseStart_769238 baseEnd_769238 := by
    simpa [prefixWord, tailWord_769238, baseEnd_769238] using wordTrace_append hprefix tailTrace_769238
  have hstable : (prefixWord ++ tailWord_769238).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769238).length < 2 ^ (prefixWord ++ tailWord_769238).sum := by decide
  have hdescent : baseEnd_769238 < baseStart_769238 := by decide
  rcases family_descends (prefixWord ++ tailWord_769238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769249 : List Nat := [1, 2, 3, 1, 3, 2, 2, 4, 3]
def baseStart_769249 : Nat := 118140960795 + 769249 * 2 ^ 59
def prefixEnd_769249 : Nat := 4983230072969 + 3 ^ 40 * 769249 * 2
def baseEnd_769249 : Nat := 175553102218029352644353

theorem tailTrace_769249 : CollatzResearch.WordTrace tailWord_769249 prefixEnd_769249 175553102218029352644353 := by
  unfold tailWord_769249
  simp only [CollatzResearch.WordTrace]
  refine ⟨28056815990149725114830801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18704543993433150076553867 28056815990149725114830801)
  ·
    refine ⟨21042611992612293836123101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28056815990149725114830801 21042611992612293836123101)
    ·
      refine ⟨7890979497229610188546163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21042611992612293836123101 7890979497229610188546163)
      ·
        refine ⟨11836469245844415282819245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7890979497229610188546163 11836469245844415282819245)
        ·
          refine ⟨4438675967191655731057217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11836469245844415282819245 4438675967191655731057217)
          ·
            refine ⟨3329006975393741798292913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4438675967191655731057217 3329006975393741798292913)
            ·
              refine ⟨2496755231545306348719685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3329006975393741798292913 2496755231545306348719685)
              ·
                refine ⟨468141605914744940384941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2496755231545306348719685 468141605914744940384941)
                ·
                  refine ⟨175553102218029352644353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 468141605914744940384941 175553102218029352644353)
                  ·
                    rfl

theorem cell21_769249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 4, 3].length) (baseStart_769249 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_769249 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_769249 prefixEnd_769249 := by exact prefixLift 769249
  have htrace : WordTrace (prefixWord ++ tailWord_769249) baseStart_769249 baseEnd_769249 := by
    simpa [prefixWord, tailWord_769249, baseEnd_769249] using wordTrace_append hprefix tailTrace_769249
  have hstable : (prefixWord ++ tailWord_769249).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769249).length < 2 ^ (prefixWord ++ tailWord_769249).sum := by decide
  have hdescent : baseEnd_769249 < baseStart_769249 := by decide
  rcases family_descends (prefixWord ++ tailWord_769249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769308 : List Nat := [2, 2, 3, 1, 1, 1, 5, 1, 5]
def baseStart_769308 : Nat := 118140960795 + 769308 * 2 ^ 59
def prefixEnd_769308 : Nat := 4983230072969 + 3 ^ 40 * 769308 * 2
def baseEnd_769308 : Nat := 175566566821858361160899

theorem tailTrace_769308 : CollatzResearch.WordTrace tailWord_769308 prefixEnd_769308 175566566821858361160899 := by
  unfold tailWord_769308
  simp only [CollatzResearch.WordTrace]
  refine ⟨14029483948467989095614289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18705978597957318794152385 14029483948467989095614289)
  ·
    refine ⟨10522112961350991821710717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14029483948467989095614289 10522112961350991821710717)
    ·
      refine ⟨3945792360506621933141519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10522112961350991821710717 3945792360506621933141519)
      ·
        refine ⟨5918688540759932899712279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3945792360506621933141519 5918688540759932899712279)
        ·
          refine ⟨8878032811139899349568419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5918688540759932899712279 8878032811139899349568419)
          ·
            refine ⟨13317049216709849024352629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8878032811139899349568419 13317049216709849024352629)
            ·
              refine ⟨1248473364066548346033059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13317049216709849024352629 1248473364066548346033059)
              ·
                refine ⟨1872710046099822519049589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1248473364066548346033059 1872710046099822519049589)
                ·
                  refine ⟨175566566821858361160899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1872710046099822519049589 175566566821858361160899)
                  ·
                    rfl

theorem cell21_769308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5, 1, 5].length) (baseStart_769308 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_769308 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_769308 prefixEnd_769308 := by exact prefixLift 769308
  have htrace : WordTrace (prefixWord ++ tailWord_769308) baseStart_769308 baseEnd_769308 := by
    simpa [prefixWord, tailWord_769308, baseEnd_769308] using wordTrace_append hprefix tailTrace_769308
  have hstable : (prefixWord ++ tailWord_769308).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769308).length < 2 ^ (prefixWord ++ tailWord_769308).sum := by decide
  have hdescent : baseEnd_769308 < baseStart_769308 := by decide
  rcases family_descends (prefixWord ++ tailWord_769308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769314 : List Nat := [3, 3, 1, 1, 5, 1, 2, 1, 4]
def baseStart_769314 : Nat := 118140960795 + 769314 * 2 ^ 59
def prefixEnd_769314 : Nat := 4983230072969 + 3 ^ 40 * 769314 * 2
def baseEnd_769314 : Nat := 175567936103603684060887

theorem tailTrace_769314 : CollatzResearch.WordTrace tailWord_769314 prefixEnd_769314 175567936103603684060887 := by
  unfold tailWord_769314
  simp only [CollatzResearch.WordTrace]
  refine ⟨7014796683728560303986749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18706124489942827477297997 7014796683728560303986749)
  ·
    refine ⟨2630548756398210113995031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7014796683728560303986749 2630548756398210113995031)
    ·
      refine ⟨3945823134597315170992547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2630548756398210113995031 3945823134597315170992547)
      ·
        refine ⟨5918734701895972756488821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3945823134597315170992547 5918734701895972756488821)
        ·
          refine ⟨554881378302747445920827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5918734701895972756488821 554881378302747445920827)
          ·
            refine ⟨832322067454121168881241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 554881378302747445920827 832322067454121168881241)
            ·
              refine ⟨624241550590590876660931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 832322067454121168881241 624241550590590876660931)
              ·
                refine ⟨936362325885886314991397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 624241550590590876660931 936362325885886314991397)
                ·
                  refine ⟨175567936103603684060887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 936362325885886314991397 175567936103603684060887)
                  ·
                    rfl

theorem cell21_769314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 2, 1, 4].length) (baseStart_769314 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_769314 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_769314 prefixEnd_769314 := by exact prefixLift 769314
  have htrace : WordTrace (prefixWord ++ tailWord_769314) baseStart_769314 baseEnd_769314 := by
    simpa [prefixWord, tailWord_769314, baseEnd_769314] using wordTrace_append hprefix tailTrace_769314
  have hstable : (prefixWord ++ tailWord_769314).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769314).length < 2 ^ (prefixWord ++ tailWord_769314).sum := by decide
  have hdescent : baseEnd_769314 < baseStart_769314 := by decide
  rcases family_descends (prefixWord ++ tailWord_769314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769415 : List Nat := [1, 1, 4, 2, 2, 2, 3, 2, 4]
def baseStart_769415 : Nat := 118140960795 + 769415 * 2 ^ 59
def prefixEnd_769415 : Nat := 4983230072969 + 3 ^ 40 * 769415 * 2
def baseEnd_769415 : Nat := 175590985679649952877347

theorem tailTrace_769415 : CollatzResearch.WordTrace tailWord_769415 prefixEnd_769415 175590985679649952877347 := by
  unfold tailWord_769415
  simp only [CollatzResearch.WordTrace]
  refine ⟨28062870507548335465373699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18708580338365556976915799 28062870507548335465373699)
  ·
    refine ⟨42094305761322503198060549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28062870507548335465373699 42094305761322503198060549)
    ·
      refine ⟨7892682330247969349636353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42094305761322503198060549 7892682330247969349636353)
      ·
        refine ⟨5919511747685977012227265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7892682330247969349636353 5919511747685977012227265)
        ·
          refine ⟨4439633810764482759170449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5919511747685977012227265 4439633810764482759170449)
          ·
            refine ⟨3329725358073362069377837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4439633810764482759170449 3329725358073362069377837)
            ·
              refine ⟨1248647009277510776016689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3329725358073362069377837 1248647009277510776016689)
              ·
                refine ⟨936485256958133082012517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1248647009277510776016689 936485256958133082012517)
                ·
                  refine ⟨175590985679649952877347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 936485256958133082012517 175590985679649952877347)
                  ·
                    rfl

theorem cell21_769415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3, 2, 4].length) (baseStart_769415 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_769415 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_769415 prefixEnd_769415 := by exact prefixLift 769415
  have htrace : WordTrace (prefixWord ++ tailWord_769415) baseStart_769415 baseEnd_769415 := by
    simpa [prefixWord, tailWord_769415, baseEnd_769415] using wordTrace_append hprefix tailTrace_769415
  have hstable : (prefixWord ++ tailWord_769415).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769415).length < 2 ^ (prefixWord ++ tailWord_769415).sum := by decide
  have hdescent : baseEnd_769415 < baseStart_769415 := by decide
  rcases family_descends (prefixWord ++ tailWord_769415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769443 : List Nat := [1, 1, 1, 4, 1, 3, 1, 4, 5]
def baseStart_769443 : Nat := 118140960795 + 769443 * 2 ^ 59
def prefixEnd_769443 : Nat := 4983230072969 + 3 ^ 40 * 769443 * 2
def baseEnd_769443 : Nat := 175597375661128126410623

theorem tailTrace_769443 : CollatzResearch.WordTrace tailWord_769443 prefixEnd_769443 175597375661128126410623 := by
  unfold tailWord_769443
  simp only [CollatzResearch.WordTrace]
  refine ⟨28063891751446896247392983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18709261167631264164928655 28063891751446896247392983)
  ·
    refine ⟨42095837627170344371089475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28063891751446896247392983 42095837627170344371089475)
    ·
      refine ⟨63143756440755516556634213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42095837627170344371089475 63143756440755516556634213)
      ·
        refine ⟨11839454332641659354368915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63143756440755516556634213 11839454332641659354368915)
        ·
          refine ⟨17759181498962489031553373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11839454332641659354368915 17759181498962489031553373)
          ·
            refine ⟨6659693062110933386832515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17759181498962489031553373 6659693062110933386832515)
            ·
              refine ⟨9989539593166400080248773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6659693062110933386832515 9989539593166400080248773)
              ·
                refine ⟨1873038673718700015046645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9989539593166400080248773 1873038673718700015046645)
                ·
                  refine ⟨175597375661128126410623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1873038673718700015046645 175597375661128126410623)
                  ·
                    rfl

theorem cell21_769443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 4, 5].length) (baseStart_769443 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_769443 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_769443 prefixEnd_769443 := by exact prefixLift 769443
  have htrace : WordTrace (prefixWord ++ tailWord_769443) baseStart_769443 baseEnd_769443 := by
    simpa [prefixWord, tailWord_769443, baseEnd_769443] using wordTrace_append hprefix tailTrace_769443
  have hstable : (prefixWord ++ tailWord_769443).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769443).length < 2 ^ (prefixWord ++ tailWord_769443).sum := by decide
  have hdescent : baseEnd_769443 < baseStart_769443 := by decide
  rcases family_descends (prefixWord ++ tailWord_769443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769646 : List Nat := [4, 1, 2, 2, 4, 1, 1, 1, 5]
def baseStart_769646 : Nat := 118140960795 + 769646 * 2 ^ 59
def prefixEnd_769646 : Nat := 4983230072969 + 3 ^ 40 * 769646 * 2
def baseEnd_769646 : Nat := 175643703026844884526875

theorem tailTrace_769646 : CollatzResearch.WordTrace tailWord_769646 prefixEnd_769646 175643703026844884526875 := by
  unfold tailWord_769646
  simp only [CollatzResearch.WordTrace]
  refine ⟨3508911971213932739629099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18714197179807641278021861 3508911971213932739629099)
  ·
    refine ⟨5263367956820899109443649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3508911971213932739629099 5263367956820899109443649)
    ·
      refine ⟨3947525967615674332082737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5263367956820899109443649 3947525967615674332082737)
      ·
        refine ⟨2960644475711755749062053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3947525967615674332082737 2960644475711755749062053)
        ·
          refine ⟨555120839195954202949135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2960644475711755749062053 555120839195954202949135)
          ·
            refine ⟨832681258793931304423703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 555120839195954202949135 832681258793931304423703)
            ·
              refine ⟨1249021888190896956635555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 832681258793931304423703 1249021888190896956635555)
              ·
                refine ⟨1873532832286345434953333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1249021888190896956635555 1873532832286345434953333)
                ·
                  refine ⟨175643703026844884526875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1873532832286345434953333 175643703026844884526875)
                  ·
                    rfl

theorem cell21_769646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 1, 1, 5].length) (baseStart_769646 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_769646 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_769646 prefixEnd_769646 := by exact prefixLift 769646
  have htrace : WordTrace (prefixWord ++ tailWord_769646) baseStart_769646 baseEnd_769646 := by
    simpa [prefixWord, tailWord_769646, baseEnd_769646] using wordTrace_append hprefix tailTrace_769646
  have hstable : (prefixWord ++ tailWord_769646).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769646).length < 2 ^ (prefixWord ++ tailWord_769646).sum := by decide
  have hdescent : baseEnd_769646 < baseStart_769646 := by decide
  rcases family_descends (prefixWord ++ tailWord_769646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769685 : List Nat := [1, 3, 2, 1, 1, 1, 1, 3, 8]
def baseStart_769685 : Nat := 118140960795 + 769685 * 2 ^ 59
def prefixEnd_769685 : Nat := 4983230072969 + 3 ^ 40 * 769685 * 2
def baseEnd_769685 : Nat := 175652603358189483376795

theorem tailTrace_769685 : CollatzResearch.WordTrace tailWord_769685 prefixEnd_769685 175652603358189483376795 := by
  unfold tailWord_769685
  simp only [CollatzResearch.WordTrace]
  refine ⟨28072718216570171577702509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18715145477713447718468339 28072718216570171577702509)
  ·
    refine ⟨10527269331213814341638441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28072718216570171577702509 10527269331213814341638441)
    ·
      refine ⟨7895451998410360756228831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10527269331213814341638441 7895451998410360756228831)
      ·
        refine ⟨11843177997615541134343247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7895451998410360756228831 11843177997615541134343247)
        ·
          refine ⟨17764766996423311701514871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11843177997615541134343247 17764766996423311701514871)
          ·
            refine ⟨26647150494634967552272307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17764766996423311701514871 26647150494634967552272307)
            ·
              refine ⟨39970725741952451328408461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26647150494634967552272307 39970725741952451328408461)
              ·
                refine ⟨14989022153232169248153173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39970725741952451328408461 14989022153232169248153173)
                ·
                  refine ⟨175652603358189483376795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14989022153232169248153173 175652603358189483376795)
                  ·
                    rfl

theorem cell21_769685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 8].length) (baseStart_769685 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_769685 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_769685 prefixEnd_769685 := by exact prefixLift 769685
  have htrace : WordTrace (prefixWord ++ tailWord_769685) baseStart_769685 baseEnd_769685 := by
    simpa [prefixWord, tailWord_769685, baseEnd_769685] using wordTrace_append hprefix tailTrace_769685
  have hstable : (prefixWord ++ tailWord_769685).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769685).length < 2 ^ (prefixWord ++ tailWord_769685).sum := by decide
  have hdescent : baseEnd_769685 < baseStart_769685 := by decide
  rcases family_descends (prefixWord ++ tailWord_769685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769764 : List Nat := [2, 3, 1, 1, 1, 3, 1, 6, 3]
def baseStart_769764 : Nat := 118140960795 + 769764 * 2 ^ 59
def prefixEnd_769764 : Nat := 4983230072969 + 3 ^ 40 * 769764 * 2
def baseEnd_769764 : Nat := 175670632234502901559967

theorem tailTrace_769764 : CollatzResearch.WordTrace tailWord_769764 prefixEnd_769764 175670632234502901559967 := by
  unfold tailWord_769764
  simp only [CollatzResearch.WordTrace]
  refine ⟨14037799791641984034914173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18717066388855978713218897 14037799791641984034914173)
  ·
    refine ⟨5264174921865744013092815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14037799791641984034914173 5264174921865744013092815)
    ·
      refine ⟨7896262382798616019639223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5264174921865744013092815 7896262382798616019639223)
      ·
        refine ⟨11844393574197924029458835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7896262382798616019639223 11844393574197924029458835)
        ·
          refine ⟨17766590361296886044188253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11844393574197924029458835 17766590361296886044188253)
          ·
            refine ⟨6662471385486332266570595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17766590361296886044188253 6662471385486332266570595)
            ·
              refine ⟨9993707078229498399855893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6662471385486332266570595 9993707078229498399855893)
              ·
                refine ⟨468455019292007737493245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9993707078229498399855893 468455019292007737493245)
                ·
                  refine ⟨175670632234502901559967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 468455019292007737493245 175670632234502901559967)
                  ·
                    rfl

theorem cell21_769764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 6, 3].length) (baseStart_769764 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_769764 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_769764 prefixEnd_769764 := by exact prefixLift 769764
  have htrace : WordTrace (prefixWord ++ tailWord_769764) baseStart_769764 baseEnd_769764 := by
    simpa [prefixWord, tailWord_769764, baseEnd_769764] using wordTrace_append hprefix tailTrace_769764
  have hstable : (prefixWord ++ tailWord_769764).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769764).length < 2 ^ (prefixWord ++ tailWord_769764).sum := by decide
  have hdescent : baseEnd_769764 < baseStart_769764 := by decide
  rcases family_descends (prefixWord ++ tailWord_769764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769868 : List Nat := [2, 2, 1, 3, 4, 9]
def baseStart_769868 : Nat := 118140960795 + 769868 * 2 ^ 59
def prefixEnd_769868 : Nat := 4983230072969 + 3 ^ 40 * 769868 * 2
def baseEnd_769868 : Nat := 6507198757460067845423

theorem tailTrace_769868 : CollatzResearch.WordTrace tailWord_769868 prefixEnd_769868 6507198757460067845423 := by
  unfold tailWord_769868
  simp only [CollatzResearch.WordTrace]
  refine ⟨14039696387453596915807129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18719595183271462554409505 14039696387453596915807129)
  ·
    refine ⟨10529772290590197686855347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14039696387453596915807129 10529772290590197686855347)
    ·
      refine ⟨15794658435885296530283021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10529772290590197686855347 15794658435885296530283021)
      ·
        refine ⟨5922996913456986198856133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15794658435885296530283021 5922996913456986198856133)
        ·
          refine ⟨1110561921273184912285525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5922996913456986198856133 1110561921273184912285525)
          ·
            refine ⟨6507198757460067845423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1110561921273184912285525 6507198757460067845423)
            ·
              rfl

theorem cell21_769868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 9].length) (baseStart_769868 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_769868 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_769868 prefixEnd_769868 := by exact prefixLift 769868
  have htrace : WordTrace (prefixWord ++ tailWord_769868) baseStart_769868 baseEnd_769868 := by
    simpa [prefixWord, tailWord_769868, baseEnd_769868] using wordTrace_append hprefix tailTrace_769868
  have hstable : (prefixWord ++ tailWord_769868).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769868).length < 2 ^ (prefixWord ++ tailWord_769868).sum := by decide
  have hdescent : baseEnd_769868 < baseStart_769868 := by decide
  rcases family_descends (prefixWord ++ tailWord_769868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769874 : List Nat := [3, 2, 2, 1, 1, 5, 2, 2, 3]
def baseStart_769874 : Nat := 118140960795 + 769874 * 2 ^ 59
def prefixEnd_769874 : Nat := 4983230072969 + 3 ^ 40 * 769874 * 2
def baseEnd_769874 : Nat := 175695735733167154726409

theorem tailTrace_769874 : CollatzResearch.WordTrace tailWord_769874 prefixEnd_769874 175695735733167154726409 := by
  unfold tailWord_769874
  simp only [CollatzResearch.WordTrace]
  refine ⟨7019902903221364214083169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18719741075256971237555117 7019902903221364214083169)
  ·
    refine ⟨5264927177416023160562377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7019902903221364214083169 5264927177416023160562377)
    ·
      refine ⟨3948695383062017370421783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5264927177416023160562377 3948695383062017370421783)
      ·
        refine ⟨5923043074593026055632675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3948695383062017370421783 5923043074593026055632675)
        ·
          refine ⟨8884564611889539083449013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5923043074593026055632675 8884564611889539083449013)
          ·
            refine ⟨832927932364644289073345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8884564611889539083449013 832927932364644289073345)
            ·
              refine ⟨624695949273483216805009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 832927932364644289073345 624695949273483216805009)
              ·
                refine ⟨468521961955112412603757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 624695949273483216805009 468521961955112412603757)
                ·
                  refine ⟨175695735733167154726409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 468521961955112412603757 175695735733167154726409)
                  ·
                    rfl

theorem cell21_769874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 2, 2, 3].length) (baseStart_769874 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_769874 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_769874 prefixEnd_769874 := by exact prefixLift 769874
  have htrace : WordTrace (prefixWord ++ tailWord_769874) baseStart_769874 baseEnd_769874 := by
    simpa [prefixWord, tailWord_769874, baseEnd_769874] using wordTrace_append hprefix tailTrace_769874
  have hstable : (prefixWord ++ tailWord_769874).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769874).length < 2 ^ (prefixWord ++ tailWord_769874).sum := by decide
  have hdescent : baseEnd_769874 < baseStart_769874 := by decide
  rcases family_descends (prefixWord ++ tailWord_769874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769902 : List Nat := [4, 1, 2, 3, 1, 2, 3, 5]
def baseStart_769902 : Nat := 118140960795 + 769902 * 2 ^ 59
def prefixEnd_769902 : Nat := 4983230072969 + 3 ^ 40 * 769902 * 2
def baseEnd_769902 : Nat := 58567375238215109419895

theorem tailTrace_769902 : CollatzResearch.WordTrace tailWord_769902 prefixEnd_769902 58567375238215109419895 := by
  unfold tailWord_769902
  simp only [CollatzResearch.WordTrace]
  refine ⟨3510079107098002204793995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18720421904522678425567973 3510079107098002204793995)
  ·
    refine ⟨5265118660647003307190993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3510079107098002204793995 5265118660647003307190993)
    ·
      refine ⟨3948838995485252480393245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5265118660647003307190993 3948838995485252480393245)
      ·
        refine ⟨1480814623306969680147467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3948838995485252480393245 1480814623306969680147467)
        ·
          refine ⟨2221221934960454520221201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1480814623306969680147467 2221221934960454520221201)
          ·
            refine ⟨1665916451220340890165901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2221221934960454520221201 1665916451220340890165901)
            ·
              refine ⟨624718669207627833812213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1665916451220340890165901 624718669207627833812213)
              ·
                refine ⟨58567375238215109419895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 624718669207627833812213 58567375238215109419895)
                ·
                  rfl

theorem cell21_769902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 3, 5].length) (baseStart_769902 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_769902 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_769902 prefixEnd_769902 := by exact prefixLift 769902
  have htrace : WordTrace (prefixWord ++ tailWord_769902) baseStart_769902 baseEnd_769902 := by
    simpa [prefixWord, tailWord_769902, baseEnd_769902] using wordTrace_append hprefix tailTrace_769902
  have hstable : (prefixWord ++ tailWord_769902).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769902).length < 2 ^ (prefixWord ++ tailWord_769902).sum := by decide
  have hdescent : baseEnd_769902 < baseStart_769902 := by decide
  rcases family_descends (prefixWord ++ tailWord_769902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769913 : List Nat := [1, 2, 1, 3, 2, 2, 2, 2, 6]
def baseStart_769913 : Nat := 118140960795 + 769913 * 2 ^ 59
def prefixEnd_769913 : Nat := 4983230072969 + 3 ^ 40 * 769913 * 2
def baseEnd_769913 : Nat := 175704636064511753576329

theorem tailTrace_769913 : CollatzResearch.WordTrace tailWord_769913 prefixEnd_769913 175704636064511753576329 := by
  unfold tailWord_769913
  simp only [CollatzResearch.WordTrace]
  refine ⟨28081034059744166517002393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18720689373162777678001595 28081034059744166517002393)
  ·
    refine ⟨21060775544808124887751795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28081034059744166517002393 21060775544808124887751795)
    ·
      refine ⟨31591163317212187331627693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21060775544808124887751795 31591163317212187331627693)
      ·
        refine ⟨11846686243954570249360385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31591163317212187331627693 11846686243954570249360385)
        ·
          refine ⟨8885014682965927687020289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11846686243954570249360385 8885014682965927687020289)
          ·
            refine ⟨6663761012224445765265217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8885014682965927687020289 6663761012224445765265217)
            ·
              refine ⟨4997820759168334323948913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6663761012224445765265217 4997820759168334323948913)
              ·
                refine ⟨3748365569376250742961685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4997820759168334323948913 3748365569376250742961685)
                ·
                  refine ⟨175704636064511753576329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3748365569376250742961685 175704636064511753576329)
                  ·
                    rfl

theorem cell21_769913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 2, 6].length) (baseStart_769913 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_769913 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_769913 prefixEnd_769913 := by exact prefixLift 769913
  have htrace : WordTrace (prefixWord ++ tailWord_769913) baseStart_769913 baseEnd_769913 := by
    simpa [prefixWord, tailWord_769913, baseEnd_769913] using wordTrace_append hprefix tailTrace_769913
  have hstable : (prefixWord ++ tailWord_769913).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769913).length < 2 ^ (prefixWord ++ tailWord_769913).sum := by decide
  have hdescent : baseEnd_769913 < baseStart_769913 := by decide
  rcases family_descends (prefixWord ++ tailWord_769913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769992 : List Nat := [2, 1, 3, 1, 4, 3, 1, 1, 5]
def baseStart_769992 : Nat := 118140960795 + 769992 * 2 ^ 59
def prefixEnd_769992 : Nat := 4983230072969 + 3 ^ 40 * 769992 * 2
def baseEnd_769992 : Nat := 175722664940825171759501

theorem tailTrace_769992 : CollatzResearch.WordTrace tailWord_769992 prefixEnd_769992 175722664940825171759501 := by
  unfold tailWord_769992
  simp only [CollatzResearch.WordTrace]
  refine ⟨14041957713228981504564115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18722610284305308672752153 14041957713228981504564115)
  ·
    refine ⟨21062936569843472256846173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14041957713228981504564115 21062936569843472256846173)
    ·
      refine ⟨7898601213691302096317315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21062936569843472256846173 7898601213691302096317315)
      ·
        refine ⟨11847901820536953144475973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7898601213691302096317315 11847901820536953144475973)
        ·
          refine ⟨2221481591350678714589245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11847901820536953144475973 2221481591350678714589245)
          ·
            refine ⟨833055596756504517970967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2221481591350678714589245 833055596756504517970967)
            ·
              refine ⟨1249583395134756776956451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 833055596756504517970967 1249583395134756776956451)
              ·
                refine ⟨1874375092702135165434677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1249583395134756776956451 1874375092702135165434677)
                ·
                  refine ⟨175722664940825171759501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1874375092702135165434677 175722664940825171759501)
                  ·
                    rfl

theorem cell21_769992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 1, 1, 5].length) (baseStart_769992 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_769992 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_769992 prefixEnd_769992 := by exact prefixLift 769992
  have htrace : WordTrace (prefixWord ++ tailWord_769992) baseStart_769992 baseEnd_769992 := by
    simpa [prefixWord, tailWord_769992, baseEnd_769992] using wordTrace_append hprefix tailTrace_769992
  have hstable : (prefixWord ++ tailWord_769992).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769992).length < 2 ^ (prefixWord ++ tailWord_769992).sum := by decide
  have hdescent : baseEnd_769992 < baseStart_769992 := by decide
  rcases family_descends (prefixWord ++ tailWord_769992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770130 : List Nat := [3, 2, 2, 1, 4, 2, 2, 5]
def baseStart_770130 : Nat := 118140960795 + 770130 * 2 ^ 59
def prefixEnd_770130 : Nat := 4983230072969 + 3 ^ 40 * 770130 * 2
def baseEnd_770130 : Nat := 58584719473655866153073

theorem tailTrace_770130 : CollatzResearch.WordTrace tailWord_770130 prefixEnd_770130 58584719473655866153073 := by
  unfold tailWord_770130
  simp only [CollatzResearch.WordTrace]
  refine ⟨7022237174989503144412961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18725965799972008385101229 7022237174989503144412961)
  ·
    refine ⟨5266677881242127358309721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7022237174989503144412961 5266677881242127358309721)
    ·
      refine ⟨3950008410931595518732291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5266677881242127358309721 3950008410931595518732291)
      ·
        refine ⟨5925012616397393278098437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3950008410931595518732291 5925012616397393278098437)
        ·
          refine ⟨1110939865574511239643457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5925012616397393278098437 1110939865574511239643457)
          ·
            refine ⟨833204899180883429732593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1110939865574511239643457 833204899180883429732593)
            ·
              refine ⟨624903674385662572299445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 833204899180883429732593 624903674385662572299445)
              ·
                refine ⟨58584719473655866153073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 624903674385662572299445 58584719473655866153073)
                ·
                  rfl

theorem cell21_770130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 2, 5].length) (baseStart_770130 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_770130 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_770130 prefixEnd_770130 := by exact prefixLift 770130
  have htrace : WordTrace (prefixWord ++ tailWord_770130) baseStart_770130 baseEnd_770130 := by
    simpa [prefixWord, tailWord_770130, baseEnd_770130] using wordTrace_append hprefix tailTrace_770130
  have hstable : (prefixWord ++ tailWord_770130).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770130).length < 2 ^ (prefixWord ++ tailWord_770130).sum := by decide
  have hdescent : baseEnd_770130 < baseStart_770130 := by decide
  rcases family_descends (prefixWord ++ tailWord_770130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770144 : List Nat := [2, 1, 1, 3, 2, 3, 3, 3, 3]
def baseStart_770144 : Nat := 118140960795 + 770144 * 2 ^ 59
def prefixEnd_770144 : Nat := 4983230072969 + 3 ^ 40 * 770144 * 2
def baseEnd_770144 : Nat := 175757353411706685225857

theorem tailTrace_770144 : CollatzResearch.WordTrace tailWord_770144 prefixEnd_770144 175757353411706685225857 := by
  unfold tailWord_770144
  simp only [CollatzResearch.WordTrace]
  refine ⟨14044729660953646484330743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18726306214604861979107657 14044729660953646484330743)
  ·
    refine ⟨21067094491430469726496115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14044729660953646484330743 21067094491430469726496115)
    ·
      refine ⟨31600641737145704589744173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21067094491430469726496115 31600641737145704589744173)
      ·
        refine ⟨11850240651429639221154065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31600641737145704589744173 11850240651429639221154065)
        ·
          refine ⟨8887680488572229415865549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11850240651429639221154065 8887680488572229415865549)
          ·
            refine ⟨3332880183214586030949581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8887680488572229415865549 3332880183214586030949581)
            ·
              refine ⟨1249830068705469761606093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3332880183214586030949581 1249830068705469761606093)
              ·
                refine ⟨468686275764551160602285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1249830068705469761606093 468686275764551160602285)
                ·
                  refine ⟨175757353411706685225857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 468686275764551160602285 175757353411706685225857)
                  ·
                    rfl

theorem cell21_770144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3, 3, 3].length) (baseStart_770144 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_770144 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_770144 prefixEnd_770144 := by exact prefixLift 770144
  have htrace : WordTrace (prefixWord ++ tailWord_770144) baseStart_770144 baseEnd_770144 := by
    simpa [prefixWord, tailWord_770144, baseEnd_770144] using wordTrace_append hprefix tailTrace_770144
  have hstable : (prefixWord ++ tailWord_770144).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770144).length < 2 ^ (prefixWord ++ tailWord_770144).sum := by decide
  have hdescent : baseEnd_770144 < baseStart_770144 := by decide
  rcases family_descends (prefixWord ++ tailWord_770144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770158 : List Nat := [4, 1, 2, 2, 1, 1, 2, 4, 4]
def baseStart_770158 : Nat := 118140960795 + 770158 * 2 ^ 59
def prefixEnd_770158 : Nat := 4983230072969 + 3 ^ 40 * 770158 * 2
def baseEnd_770158 : Nat := 175760548402445771992495

theorem tailTrace_770158 : CollatzResearch.WordTrace tailWord_770158 prefixEnd_770158 175760548402445771992495 := by
  unfold tailWord_770158
  simp only [CollatzResearch.WordTrace]
  refine ⟨3511246242982071669958891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18726646629237715573114085 3511246242982071669958891)
  ·
    refine ⟨5266869364473107504938337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3511246242982071669958891 5266869364473107504938337)
    ·
      refine ⟨3950152023354830628703753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5266869364473107504938337 3950152023354830628703753)
      ·
        refine ⟨2962614017516122971527815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3950152023354830628703753 2962614017516122971527815)
        ·
          refine ⟨4443921026274184457291723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2962614017516122971527815 4443921026274184457291723)
          ·
            refine ⟨6665881539411276685937585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4443921026274184457291723 6665881539411276685937585)
            ·
              refine ⟨4999411154558457514453189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6665881539411276685937585 4999411154558457514453189)
              ·
                refine ⟨937389591479710783959973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4999411154558457514453189 937389591479710783959973)
                ·
                  refine ⟨175760548402445771992495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 937389591479710783959973 175760548402445771992495)
                  ·
                    rfl

theorem cell21_770158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 4, 4].length) (baseStart_770158 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_770158 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_770158 prefixEnd_770158 := by exact prefixLift 770158
  have htrace : WordTrace (prefixWord ++ tailWord_770158) baseStart_770158 baseEnd_770158 := by
    simpa [prefixWord, tailWord_770158, baseEnd_770158] using wordTrace_append hprefix tailTrace_770158
  have hstable : (prefixWord ++ tailWord_770158).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770158).length < 2 ^ (prefixWord ++ tailWord_770158).sum := by decide
  have hdescent : baseEnd_770158 < baseStart_770158 := by decide
  rcases family_descends (prefixWord ++ tailWord_770158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770172 : List Nat := [2, 2, 2, 1, 1, 5, 2, 6]
def baseStart_770172 : Nat := 118140960795 + 770172 * 2 ^ 59
def prefixEnd_770172 : Nat := 4983230072969 + 3 ^ 40 * 770172 * 2
def baseEnd_770172 : Nat := 58587914464394952919711

theorem tailTrace_770172 : CollatzResearch.WordTrace tailWord_770172 prefixEnd_770172 58587914464394952919711 := by
  unfold tailWord_770172
  simp only [CollatzResearch.WordTrace]
  refine ⟨14045240282902926875340385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18726987043870569167120513 14045240282902926875340385)
  ·
    refine ⟨10533930212177195156505289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14045240282902926875340385 10533930212177195156505289)
    ·
      refine ⟨7900447659132896367378967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10533930212177195156505289 7900447659132896367378967)
      ·
        refine ⟨11850671488699344551068451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7900447659132896367378967 11850671488699344551068451)
        ·
          refine ⟨17776007233049016826602677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11850671488699344551068451 17776007233049016826602677)
          ·
            refine ⟨1666500678098345327494001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17776007233049016826602677 1666500678098345327494001)
            ·
              refine ⟨1249875508573758995620501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1666500678098345327494001 1249875508573758995620501)
              ·
                refine ⟨58587914464394952919711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1249875508573758995620501 58587914464394952919711)
                ·
                  rfl

theorem cell21_770172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2, 6].length) (baseStart_770172 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_770172 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_770172 prefixEnd_770172 := by exact prefixLift 770172
  have htrace : WordTrace (prefixWord ++ tailWord_770172) baseStart_770172 baseEnd_770172 := by
    simpa [prefixWord, tailWord_770172, baseEnd_770172] using wordTrace_append hprefix tailTrace_770172
  have hstable : (prefixWord ++ tailWord_770172).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770172).length < 2 ^ (prefixWord ++ tailWord_770172).sum := by decide
  have hdescent : baseEnd_770172 < baseStart_770172 := by decide
  rcases family_descends (prefixWord ++ tailWord_770172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770279 : List Nat := [1, 1, 5, 3, 1, 1, 1, 3, 5]
def baseStart_770279 : Nat := 118140960795 + 770279 * 2 ^ 59
def prefixEnd_770279 : Nat := 4983230072969 + 3 ^ 40 * 770279 * 2
def baseEnd_770279 : Nat := 175788162250976450475581

theorem tailTrace_770279 : CollatzResearch.WordTrace tailWord_770279 prefixEnd_770279 175788162250976450475581 := by
  unfold tailWord_770279
  simp only [CollatzResearch.WordTrace]
  refine ⟨28094383176418211024825891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18729588784278807349883927 28094383176418211024825891)
  ·
    refine ⟨42141574764627316537238837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28094383176418211024825891 42141574764627316537238837)
    ·
      refine ⟨3950772634183810925366141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42141574764627316537238837 3950772634183810925366141)
      ·
        refine ⟨1481539737818929097012303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3950772634183810925366141 1481539737818929097012303)
        ·
          refine ⟨2222309606728393645518455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1481539737818929097012303 2222309606728393645518455)
          ·
            refine ⟨3333464410092590468277683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2222309606728393645518455 3333464410092590468277683)
            ·
              refine ⟨5000196615138885702416525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3333464410092590468277683 5000196615138885702416525)
              ·
                refine ⟨1875073730677082138406197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5000196615138885702416525 1875073730677082138406197)
                ·
                  refine ⟨175788162250976450475581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1875073730677082138406197 175788162250976450475581)
                  ·
                    rfl

theorem cell21_770279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 3, 5].length) (baseStart_770279 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_770279 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_770279 prefixEnd_770279 := by exact prefixLift 770279
  have htrace : WordTrace (prefixWord ++ tailWord_770279) baseStart_770279 baseEnd_770279 := by
    simpa [prefixWord, tailWord_770279, baseEnd_770279] using wordTrace_append hprefix tailTrace_770279
  have hstable : (prefixWord ++ tailWord_770279).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770279).length < 2 ^ (prefixWord ++ tailWord_770279).sum := by decide
  have hdescent : baseEnd_770279 < baseStart_770279 := by decide
  rcases family_descends (prefixWord ++ tailWord_770279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770307 : List Nat := [1, 1, 1, 3, 2, 3, 3, 7]
def baseStart_770307 : Nat := 118140960795 + 770307 * 2 ^ 59
def prefixEnd_770307 : Nat := 4983230072969 + 3 ^ 40 * 770307 * 2
def baseEnd_770307 : Nat := 58598184077484874669619

theorem tailTrace_770307 : CollatzResearch.WordTrace tailWord_770307 prefixEnd_770307 58598184077484874669619 := by
  unfold tailWord_770307
  simp only [CollatzResearch.WordTrace]
  refine ⟨28095404420316771806845175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18730269613544514537896783 28095404420316771806845175)
  ·
    refine ⟨42143106630475157710267763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28095404420316771806845175 42143106630475157710267763)
    ·
      refine ⟨63214659945712736565401645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42143106630475157710267763 63214659945712736565401645)
      ·
        refine ⟨23705497479642276212025617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63214659945712736565401645 23705497479642276212025617)
        ·
          refine ⟨17779123109731707159019213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23705497479642276212025617 17779123109731707159019213)
          ·
            refine ⟨6667171166149390184632205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17779123109731707159019213 6667171166149390184632205)
            ·
              refine ⟨2500189187306021319237077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6667171166149390184632205 2500189187306021319237077)
              ·
                refine ⟨58598184077484874669619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2500189187306021319237077 58598184077484874669619)
                ·
                  rfl

theorem cell21_770307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 7].length) (baseStart_770307 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_770307 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_770307 prefixEnd_770307 := by exact prefixLift 770307
  have htrace : WordTrace (prefixWord ++ tailWord_770307) baseStart_770307 baseEnd_770307 := by
    simpa [prefixWord, tailWord_770307, baseEnd_770307] using wordTrace_append hprefix tailTrace_770307
  have hstable : (prefixWord ++ tailWord_770307).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770307).length < 2 ^ (prefixWord ++ tailWord_770307).sum := by decide
  have hdescent : baseEnd_770307 < baseStart_770307 := by decide
  rcases family_descends (prefixWord ++ tailWord_770307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770344 : List Nat := [2, 1, 5, 1, 3, 2, 2, 1, 4]
def baseStart_770344 : Nat := 118140960795 + 770344 * 2 ^ 59
def prefixEnd_770344 : Nat := 4983230072969 + 3 ^ 40 * 770344 * 2
def baseEnd_770344 : Nat := 175802996136550781892115

theorem tailTrace_770344 : CollatzResearch.WordTrace tailWord_770344 prefixEnd_770344 175802996136550781892115 := by
  unfold tailWord_770344
  simp only [CollatzResearch.WordTrace]
  refine ⟨14048376960591363562971043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18731169280788484750628057 14048376960591363562971043)
  ·
    refine ⟨21072565440887045344456565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14048376960591363562971043 21072565440887045344456565)
    ·
      refine ⟨1975553010083160501042803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21072565440887045344456565 1975553010083160501042803)
      ·
        refine ⟨2963329515124740751564205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1975553010083160501042803 2963329515124740751564205)
        ·
          refine ⟨1111248568171777781836577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2963329515124740751564205 1111248568171777781836577)
          ·
            refine ⟨833436426128833336377433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1111248568171777781836577 833436426128833336377433)
            ·
              refine ⟨625077319596625002283075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 833436426128833336377433 625077319596625002283075)
              ·
                refine ⟨937615979394937503424613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 625077319596625002283075 937615979394937503424613)
                ·
                  refine ⟨175802996136550781892115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 937615979394937503424613 175802996136550781892115)
                  ·
                    rfl

theorem cell21_770344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 2, 1, 4].length) (baseStart_770344 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_770344 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_770344 prefixEnd_770344 := by exact prefixLift 770344
  have htrace : WordTrace (prefixWord ++ tailWord_770344) baseStart_770344 baseEnd_770344 := by
    simpa [prefixWord, tailWord_770344, baseEnd_770344] using wordTrace_append hprefix tailTrace_770344
  have hstable : (prefixWord ++ tailWord_770344).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770344).length < 2 ^ (prefixWord ++ tailWord_770344).sum := by decide
  have hdescent : baseEnd_770344 < baseStart_770344 := by decide
  rcases family_descends (prefixWord ++ tailWord_770344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770352 : List Nat := [2, 1, 1, 1, 2, 2, 2, 2, 8]
def baseStart_770352 : Nat := 118140960795 + 770352 * 2 ^ 59
def prefixEnd_770352 : Nat := 4983230072969 + 3 ^ 40 * 770352 * 2
def baseEnd_770352 : Nat := 175804821845544545758765

theorem tailTrace_770352 : CollatzResearch.WordTrace tailWord_770352 prefixEnd_770352 175804821845544545758765 := by
  unfold tailWord_770352
  simp only [CollatzResearch.WordTrace]
  refine ⟨14048522852576872246116655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18731363803435829661488873 14048522852576872246116655)
  ·
    refine ⟨21072784278865308369174983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14048522852576872246116655 21072784278865308369174983)
    ·
      refine ⟨31609176418297962553762475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21072784278865308369174983 31609176418297962553762475)
      ·
        refine ⟨47413764627446943830643713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31609176418297962553762475 47413764627446943830643713)
        ·
          refine ⟨35560323470585207872982785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47413764627446943830643713 35560323470585207872982785)
          ·
            refine ⟨26670242602938905904737089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35560323470585207872982785 26670242602938905904737089)
            ·
              refine ⟨20002681952204179428552817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26670242602938905904737089 20002681952204179428552817)
              ·
                refine ⟨15002011464153134571414613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20002681952204179428552817 15002011464153134571414613)
                ·
                  refine ⟨175804821845544545758765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15002011464153134571414613 175804821845544545758765)
                  ·
                    rfl

theorem cell21_770352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 8].length) (baseStart_770352 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_770352 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_770352 prefixEnd_770352 := by exact prefixLift 770352
  have htrace : WordTrace (prefixWord ++ tailWord_770352) baseStart_770352 baseEnd_770352 := by
    simpa [prefixWord, tailWord_770352, baseEnd_770352] using wordTrace_append hprefix tailTrace_770352
  have hstable : (prefixWord ++ tailWord_770352).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770352).length < 2 ^ (prefixWord ++ tailWord_770352).sum := by decide
  have hdescent : baseEnd_770352 < baseStart_770352 := by decide
  rcases family_descends (prefixWord ++ tailWord_770352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770454 : List Nat := [5, 3, 1, 2, 1, 1, 3, 1, 4]
def baseStart_770454 : Nat := 118140960795 + 770454 * 2 ^ 59
def prefixEnd_770454 : Nat := 4983230072969 + 3 ^ 40 * 770454 * 2
def baseEnd_770454 : Nat := 175828099635215035058557

theorem tailTrace_770454 : CollatzResearch.WordTrace tailWord_770454 prefixEnd_770454 175828099635215035058557 := by
  unfold tailWord_770454
  simp only [CollatzResearch.WordTrace]
  refine ⟨1756297871924013494527901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18733843967189477274964277 1756297871924013494527901)
  ·
    refine ⟨658611701971505060447963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1756297871924013494527901 658611701971505060447963)
    ·
      refine ⟨987917552957257590671945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 658611701971505060447963 987917552957257590671945)
      ·
        refine ⟨740938164717943193003959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 987917552957257590671945 740938164717943193003959)
        ·
          refine ⟨1111407247076914789505939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 740938164717943193003959 1111407247076914789505939)
          ·
            refine ⟨1667110870615372184258909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1111407247076914789505939 1667110870615372184258909)
            ·
              refine ⟨625166576480764569097091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1667110870615372184258909 625166576480764569097091)
              ·
                refine ⟨937749864721146853645637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 625166576480764569097091 937749864721146853645637)
                ·
                  refine ⟨175828099635215035058557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 937749864721146853645637 175828099635215035058557)
                  ·
                    rfl

theorem cell21_770454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_770454 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_770454 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_770454 prefixEnd_770454 := by exact prefixLift 770454
  have htrace : WordTrace (prefixWord ++ tailWord_770454) baseStart_770454 baseEnd_770454 := by
    simpa [prefixWord, tailWord_770454, baseEnd_770454] using wordTrace_append hprefix tailTrace_770454
  have hstable : (prefixWord ++ tailWord_770454).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770454).length < 2 ^ (prefixWord ++ tailWord_770454).sum := by decide
  have hdescent : baseEnd_770454 < baseStart_770454 := by decide
  rcases family_descends (prefixWord ++ tailWord_770454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770521 : List Nat := [1, 2, 1, 2, 4, 1, 3, 3, 4]
def baseStart_770521 : Nat := 118140960795 + 770521 * 2 ^ 59
def prefixEnd_770521 : Nat := 4983230072969 + 3 ^ 40 * 770521 * 2
def baseEnd_770521 : Nat := 175843389948037807441753

theorem tailTrace_770521 : CollatzResearch.WordTrace tailWord_770521 prefixEnd_770521 175843389948037807441753 := by
  unfold tailWord_770521
  simp only [CollatzResearch.WordTrace]
  refine ⟨28103209641541486355135417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18735473094360990903423611 28103209641541486355135417)
  ·
    refine ⟨21077407231156114766351563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28103209641541486355135417 21077407231156114766351563)
    ·
      refine ⟨31616110846734172149527345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21077407231156114766351563 31616110846734172149527345)
      ·
        refine ⟨23712083135050629112145509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31616110846734172149527345 23712083135050629112145509)
        ·
          refine ⟨4446015587821992958527283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23712083135050629112145509 4446015587821992958527283)
          ·
            refine ⟨6669023381732989437790925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4446015587821992958527283 6669023381732989437790925)
            ·
              refine ⟨2500883768149871039171597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6669023381732989437790925 2500883768149871039171597)
              ·
                refine ⟨937831413056201639689349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2500883768149871039171597 937831413056201639689349)
                ·
                  refine ⟨175843389948037807441753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 937831413056201639689349 175843389948037807441753)
                  ·
                    rfl

theorem cell21_770521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 3, 4].length) (baseStart_770521 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_770521 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_770521 prefixEnd_770521 := by exact prefixLift 770521
  have htrace : WordTrace (prefixWord ++ tailWord_770521) baseStart_770521 baseEnd_770521 := by
    simpa [prefixWord, tailWord_770521, baseEnd_770521] using wordTrace_append hprefix tailTrace_770521
  have hstable : (prefixWord ++ tailWord_770521).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770521).length < 2 ^ (prefixWord ++ tailWord_770521).sum := by decide
  have hdescent : baseEnd_770521 < baseStart_770521 := by decide
  rcases family_descends (prefixWord ++ tailWord_770521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770535 : List Nat := [1, 1, 5, 2, 1, 1, 1, 9]
def baseStart_770535 : Nat := 118140960795 + 770535 * 2 ^ 59
def prefixEnd_770535 : Nat := 4983230072969 + 3 ^ 40 * 770535 * 2
def baseEnd_770535 : Nat := 58615528312925631402797

theorem tailTrace_770535 : CollatzResearch.WordTrace tailWord_770535 prefixEnd_770535 58615528312925631402797 := by
  unfold tailWord_770535
  simp only [CollatzResearch.WordTrace]
  refine ⟨28103720263490766746145059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18735813508993844497430039 28103720263490766746145059)
  ·
    refine ⟨42155580395236150119217589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28103720263490766746145059 42155580395236150119217589)
    ·
      refine ⟨3952085662053389073676649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42155580395236150119217589 3952085662053389073676649)
      ·
        refine ⟨2964064246540041805257487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3952085662053389073676649 2964064246540041805257487)
        ·
          refine ⟨4446096369810062707886231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2964064246540041805257487 4446096369810062707886231)
          ·
            refine ⟨6669144554715094061829347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4446096369810062707886231 6669144554715094061829347)
            ·
              refine ⟨10003716832072641092744021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6669144554715094061829347 10003716832072641092744021)
              ·
                refine ⟨58615528312925631402797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10003716832072641092744021 58615528312925631402797)
                ·
                  rfl

theorem cell21_770535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 9].length) (baseStart_770535 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_770535 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_770535 prefixEnd_770535 := by exact prefixLift 770535
  have htrace : WordTrace (prefixWord ++ tailWord_770535) baseStart_770535 baseEnd_770535 := by
    simpa [prefixWord, tailWord_770535, baseEnd_770535] using wordTrace_append hprefix tailTrace_770535
  have hstable : (prefixWord ++ tailWord_770535).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770535).length < 2 ^ (prefixWord ++ tailWord_770535).sum := by decide
  have hdescent : baseEnd_770535 < baseStart_770535 := by decide
  rcases family_descends (prefixWord ++ tailWord_770535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770600 : List Nat := [2, 1, 5, 2, 1, 1, 1, 5, 3]
def baseStart_770600 : Nat := 118140960795 + 770600 * 2 ^ 59
def prefixEnd_770600 : Nat := 4983230072969 + 3 ^ 40 * 770600 * 2
def baseEnd_770600 : Nat := 175861418824351225624925

theorem tailTrace_770600 : CollatzResearch.WordTrace tailWord_770600 prefixEnd_770600 175861418824351225624925 := by
  unfold tailWord_770600
  simp only [CollatzResearch.WordTrace]
  refine ⟨14053045504127641423630627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18737394005503521898174169 14053045504127641423630627)
  ·
    refine ⟨21079568256191462135445941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14053045504127641423630627 21079568256191462135445941)
    ·
      refine ⟨1976209524017949575198057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21079568256191462135445941 1976209524017949575198057)
      ·
        refine ⟨1482157143013462181398543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1976209524017949575198057 1482157143013462181398543)
        ·
          refine ⟨2223235714520193272097815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1482157143013462181398543 2223235714520193272097815)
          ·
            refine ⟨3334853571780289908146723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2223235714520193272097815 3334853571780289908146723)
            ·
              refine ⟨5002280357670434862220085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3334853571780289908146723 5002280357670434862220085)
              ·
                refine ⟨468963783531603268333133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5002280357670434862220085 468963783531603268333133)
                ·
                  refine ⟨175861418824351225624925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 468963783531603268333133 175861418824351225624925)
                  ·
                    rfl

theorem cell21_770600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 5, 3].length) (baseStart_770600 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_770600 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_770600 prefixEnd_770600 := by exact prefixLift 770600
  have htrace : WordTrace (prefixWord ++ tailWord_770600) baseStart_770600 baseEnd_770600 := by
    simpa [prefixWord, tailWord_770600, baseEnd_770600] using wordTrace_append hprefix tailTrace_770600
  have hstable : (prefixWord ++ tailWord_770600).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770600).length < 2 ^ (prefixWord ++ tailWord_770600).sum := by decide
  have hdescent : baseEnd_770600 < baseStart_770600 := by decide
  rcases family_descends (prefixWord ++ tailWord_770600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770614 : List Nat := [5, 1, 2, 1, 2, 2, 1, 1, 6]
def baseStart_770614 : Nat := 118140960795 + 770614 * 2 ^ 59
def prefixEnd_770614 : Nat := 4983230072969 + 3 ^ 40 * 770614 * 2
def baseEnd_770614 : Nat := 175864613815090312391563

theorem tailTrace_770614 : CollatzResearch.WordTrace tailWord_770614 prefixEnd_770614 175864613815090312391563 := by
  unfold tailWord_770614
  simp only [CollatzResearch.WordTrace]
  refine ⟨1756662601887785202391931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18737734420136375492180597 1756662601887785202391931)
  ·
    refine ⟨2634993902831677803587897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1756662601887785202391931 2634993902831677803587897)
    ·
      refine ⟨1976245427123758352690923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2634993902831677803587897 1976245427123758352690923)
      ·
        refine ⟨2964368140685637529036385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1976245427123758352690923 2964368140685637529036385)
        ·
          refine ⟨2223276105514228146777289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2964368140685637529036385 2223276105514228146777289)
          ·
            refine ⟨1667457079135671110082967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2223276105514228146777289 1667457079135671110082967)
            ·
              refine ⟨2501185618703506665124451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1667457079135671110082967 2501185618703506665124451)
              ·
                refine ⟨3751778428055259997686677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2501185618703506665124451 3751778428055259997686677)
                ·
                  refine ⟨175864613815090312391563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3751778428055259997686677 175864613815090312391563)
                  ·
                    rfl

theorem cell21_770614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 1, 6].length) (baseStart_770614 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_770614 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_770614 prefixEnd_770614 := by exact prefixLift 770614
  have htrace : WordTrace (prefixWord ++ tailWord_770614) baseStart_770614 baseEnd_770614 := by
    simpa [prefixWord, tailWord_770614, baseEnd_770614] using wordTrace_append hprefix tailTrace_770614
  have hstable : (prefixWord ++ tailWord_770614).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770614).length < 2 ^ (prefixWord ++ tailWord_770614).sum := by decide
  have hdescent : baseEnd_770614 < baseStart_770614 := by decide
  rcases family_descends (prefixWord ++ tailWord_770614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770642 : List Nat := [3, 2, 2, 1, 2, 1, 1, 4, 5]
def baseStart_770642 : Nat := 118140960795 + 770642 * 2 ^ 59
def prefixEnd_770642 : Nat := 4983230072969 + 3 ^ 40 * 770642 * 2
def baseEnd_770642 : Nat := 175871003796568485924839

theorem tailTrace_770642 : CollatzResearch.WordTrace tailWord_770642 prefixEnd_770642 175871003796568485924839 := by
  unfold tailWord_770642
  simp only [CollatzResearch.WordTrace]
  refine ⟨7026905718525781005072545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18738415249402082680193453 7026905718525781005072545)
  ·
    refine ⟨5270179288894335753804409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7026905718525781005072545 5270179288894335753804409)
    ·
      refine ⟨3952634466670751815353307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5270179288894335753804409 3952634466670751815353307)
      ·
        refine ⟨5928951700006127723029961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3952634466670751815353307 5928951700006127723029961)
        ·
          refine ⟨4446713775004595792272471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5928951700006127723029961 4446713775004595792272471)
          ·
            refine ⟨6670070662506893688408707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4446713775004595792272471 6670070662506893688408707)
            ·
              refine ⟨10005105993760340532613061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6670070662506893688408707 10005105993760340532613061)
              ·
                refine ⟨1875957373830063849864949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10005105993760340532613061 1875957373830063849864949)
                ·
                  refine ⟨175871003796568485924839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1875957373830063849864949 175871003796568485924839)
                  ·
                    rfl

theorem cell21_770642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 4, 5].length) (baseStart_770642 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_770642 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_770642 prefixEnd_770642 := by exact prefixLift 770642
  have htrace : WordTrace (prefixWord ++ tailWord_770642) baseStart_770642 baseEnd_770642 := by
    simpa [prefixWord, tailWord_770642, baseEnd_770642] using wordTrace_append hprefix tailTrace_770642
  have hstable : (prefixWord ++ tailWord_770642).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770642).length < 2 ^ (prefixWord ++ tailWord_770642).sum := by decide
  have hdescent : baseEnd_770642 < baseStart_770642 := by decide
  rcases family_descends (prefixWord ++ tailWord_770642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770656 : List Nat := [2, 1, 1, 3, 2, 1, 3, 2, 6]
def baseStart_770656 : Nat := 118140960795 + 770656 * 2 ^ 59
def prefixEnd_770656 : Nat := 4983230072969 + 3 ^ 40 * 770656 * 2
def baseEnd_770656 : Nat := 175874198787307572691477

theorem tailTrace_770656 : CollatzResearch.WordTrace tailWord_770656 prefixEnd_770656 175874198787307572691477 := by
  unfold tailWord_770656
  simp only [CollatzResearch.WordTrace]
  refine ⟨14054066748026202205649911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18738755664034936274199881 14054066748026202205649911)
  ·
    refine ⟨21081100122039303308474867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14054066748026202205649911 21081100122039303308474867)
    ·
      refine ⟨31621650183058954962712301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21081100122039303308474867 31621650183058954962712301)
      ·
        refine ⟨11858118818647108111017113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31621650183058954962712301 11858118818647108111017113)
        ·
          refine ⟨8893589113985331083262835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11858118818647108111017113 8893589113985331083262835)
          ·
            refine ⟨13340383670977996624894253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8893589113985331083262835 13340383670977996624894253)
            ·
              refine ⟨5002643876616748734335345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13340383670977996624894253 5002643876616748734335345)
              ·
                refine ⟨3751982907462561550751509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5002643876616748734335345 3751982907462561550751509)
                ·
                  refine ⟨175874198787307572691477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3751982907462561550751509 175874198787307572691477)
                  ·
                    rfl

theorem cell21_770656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 2, 6].length) (baseStart_770656 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_770656 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_770656 prefixEnd_770656 := by exact prefixLift 770656
  have htrace : WordTrace (prefixWord ++ tailWord_770656) baseStart_770656 baseEnd_770656 := by
    simpa [prefixWord, tailWord_770656, baseEnd_770656] using wordTrace_append hprefix tailTrace_770656
  have hstable : (prefixWord ++ tailWord_770656).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770656).length < 2 ^ (prefixWord ++ tailWord_770656).sum := by decide
  have hdescent : baseEnd_770656 < baseStart_770656 := by decide
  rcases family_descends (prefixWord ++ tailWord_770656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770727 : List Nat := [1, 1, 6, 3, 2, 1, 2, 2, 3]
def baseStart_770727 : Nat := 118140960795 + 770727 * 2 ^ 59
def prefixEnd_770727 : Nat := 4983230072969 + 3 ^ 40 * 770727 * 2
def baseEnd_770727 : Nat := 175890401954627227007999

theorem tailTrace_770727 : CollatzResearch.WordTrace tailWord_770727 prefixEnd_770727 175890401954627227007999 := by
  unfold tailWord_770727
  simp only [CollatzResearch.WordTrace]
  refine ⟨28110723078795183537134435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18740482052530122358089623 28110723078795183537134435)
  ·
    refine ⟨42166084618192775305701653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28110723078795183537134435 42166084618192775305701653)
    ·
      refine ⟨1976535216477786342454765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 42166084618192775305701653 1976535216477786342454765)
      ·
        refine ⟨741200706179169878420537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1976535216477786342454765 741200706179169878420537)
        ·
          refine ⟨555900529634377408815403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 741200706179169878420537 555900529634377408815403)
          ·
            refine ⟨833850794451566113223105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 555900529634377408815403 833850794451566113223105)
            ·
              refine ⟨625388095838674584917329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 833850794451566113223105 625388095838674584917329)
              ·
                refine ⟨469041071879005938687997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 625388095838674584917329 469041071879005938687997)
                ·
                  refine ⟨175890401954627227007999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 469041071879005938687997 175890401954627227007999)
                  ·
                    rfl

theorem cell21_770727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 2, 2, 3].length) (baseStart_770727 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_770727 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_770727 prefixEnd_770727 := by exact prefixLift 770727
  have htrace : WordTrace (prefixWord ++ tailWord_770727) baseStart_770727 baseEnd_770727 := by
    simpa [prefixWord, tailWord_770727, baseEnd_770727] using wordTrace_append hprefix tailTrace_770727
  have hstable : (prefixWord ++ tailWord_770727).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770727).length < 2 ^ (prefixWord ++ tailWord_770727).sum := by decide
  have hdescent : baseEnd_770727 < baseStart_770727 := by decide
  rcases family_descends (prefixWord ++ tailWord_770727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770735 : List Nat := [1, 1, 2, 1, 2, 6, 1, 4, 3]
def baseStart_770735 : Nat := 118140960795 + 770735 * 2 ^ 59
def prefixEnd_770735 : Nat := 4983230072969 + 3 ^ 40 * 770735 * 2
def baseEnd_770735 : Nat := 175892227663620990874649

theorem tailTrace_770735 : CollatzResearch.WordTrace tailWord_770735 prefixEnd_770735 175892227663620990874649 := by
  unfold tailWord_770735
  simp only [CollatzResearch.WordTrace]
  refine ⟨28111014862766200903425659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18740676575177467268950439 28111014862766200903425659)
  ·
    refine ⟨42166522294149301355138489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28111014862766200903425659 42166522294149301355138489)
    ·
      refine ⟨31624891720611976016353867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42166522294149301355138489 31624891720611976016353867)
      ·
        refine ⟨47437337580917964024530801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31624891720611976016353867 47437337580917964024530801)
        ·
          refine ⟨35578003185688473018398101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47437337580917964024530801 35578003185688473018398101)
          ·
            refine ⟨1667718899329147172737411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 35578003185688473018398101 1667718899329147172737411)
            ·
              refine ⟨2501578348993720759106117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1667718899329147172737411 2501578348993720759106117)
              ·
                refine ⟨469045940436322642332397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2501578348993720759106117 469045940436322642332397)
                ·
                  refine ⟨175892227663620990874649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 469045940436322642332397 175892227663620990874649)
                  ·
                    rfl

theorem cell21_770735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 4, 3].length) (baseStart_770735 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_770735 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_770735 prefixEnd_770735 := by exact prefixLift 770735
  have htrace : WordTrace (prefixWord ++ tailWord_770735) baseStart_770735 baseEnd_770735 := by
    simpa [prefixWord, tailWord_770735, baseEnd_770735] using wordTrace_append hprefix tailTrace_770735
  have hstable : (prefixWord ++ tailWord_770735).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770735).length < 2 ^ (prefixWord ++ tailWord_770735).sum := by decide
  have hdescent : baseEnd_770735 < baseStart_770735 := by decide
  rcases family_descends (prefixWord ++ tailWord_770735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770749 : List Nat := [1, 4, 1, 2, 1, 3, 2, 3, 4]
def baseStart_770749 : Nat := 118140960795 + 770749 * 2 ^ 59
def prefixEnd_770749 : Nat := 4983230072969 + 3 ^ 40 * 770749 * 2
def baseEnd_770749 : Nat := 175895422654360077641287

theorem tailTrace_770749 : CollatzResearch.WordTrace tailWord_770749 prefixEnd_770749 175895422654360077641287 := by
  unfold tailWord_770749
  simp only [CollatzResearch.WordTrace]
  refine ⟨28111525484715481294435301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18741016989810320862956867 28111525484715481294435301)
  ·
    refine ⟨5270911028384152742706619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28111525484715481294435301 5270911028384152742706619)
    ·
      refine ⟨7906366542576229114059929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5270911028384152742706619 7906366542576229114059929)
      ·
        refine ⟨5929774906932171835544947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7906366542576229114059929 5929774906932171835544947)
        ·
          refine ⟨8894662360398257753317421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5929774906932171835544947 8894662360398257753317421)
          ·
            refine ⟨3335498385149346657494033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8894662360398257753317421 3335498385149346657494033)
            ·
              refine ⟨2501623788862009993120525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3335498385149346657494033 2501623788862009993120525)
              ·
                refine ⟨938108920823253747420197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2501623788862009993120525 938108920823253747420197)
                ·
                  refine ⟨175895422654360077641287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 938108920823253747420197 175895422654360077641287)
                  ·
                    rfl

theorem cell21_770749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 3, 4].length) (baseStart_770749 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_770749 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_770749 prefixEnd_770749 := by exact prefixLift 770749
  have htrace : WordTrace (prefixWord ++ tailWord_770749) baseStart_770749 baseEnd_770749 := by
    simpa [prefixWord, tailWord_770749, baseEnd_770749] using wordTrace_append hprefix tailTrace_770749
  have hstable : (prefixWord ++ tailWord_770749).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770749).length < 2 ^ (prefixWord ++ tailWord_770749).sum := by decide
  have hdescent : baseEnd_770749 < baseStart_770749 := by decide
  rcases family_descends (prefixWord ++ tailWord_770749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770777 : List Nat := [1, 2, 1, 2, 3, 2, 1, 2, 7]
def baseStart_770777 : Nat := 118140960795 + 770777 * 2 ^ 59
def prefixEnd_770777 : Nat := 4983230072969 + 3 ^ 40 * 770777 * 2
def baseEnd_770777 : Nat := 175901812635838251174563

theorem tailTrace_770777 : CollatzResearch.WordTrace tailWord_770777 prefixEnd_770777 175901812635838251174563 := by
  unfold tailWord_770777
  simp only [CollatzResearch.WordTrace]
  refine ⟨28112546728614042076454585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18741697819076028050969723 28112546728614042076454585)
  ·
    refine ⟨21084410046460531557340939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28112546728614042076454585 21084410046460531557340939)
    ·
      refine ⟨31626615069690797336011409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21084410046460531557340939 31626615069690797336011409)
      ·
        refine ⟨23719961302268098002008557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31626615069690797336011409 23719961302268098002008557)
        ·
          refine ⟨8894985488350536750753209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23719961302268098002008557 8894985488350536750753209)
          ·
            refine ⟨6671239116262902563064907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8894985488350536750753209 6671239116262902563064907)
            ·
              refine ⟨10006858674394353844597361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6671239116262902563064907 10006858674394353844597361)
              ·
                refine ⟨7505144005795765383448021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10006858674394353844597361 7505144005795765383448021)
                ·
                  refine ⟨175901812635838251174563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7505144005795765383448021 175901812635838251174563)
                  ·
                    rfl

theorem cell21_770777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 2, 7].length) (baseStart_770777 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_770777 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_770777 prefixEnd_770777 := by exact prefixLift 770777
  have htrace : WordTrace (prefixWord ++ tailWord_770777) baseStart_770777 baseEnd_770777 := by
    simpa [prefixWord, tailWord_770777, baseEnd_770777] using wordTrace_append hprefix tailTrace_770777
  have hstable : (prefixWord ++ tailWord_770777).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770777).length < 2 ^ (prefixWord ++ tailWord_770777).sum := by decide
  have hdescent : baseEnd_770777 < baseStart_770777 := by decide
  rcases family_descends (prefixWord ++ tailWord_770777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770780 : List Nat := [2, 2, 5, 1, 1, 2, 8]
def baseStart_770780 : Nat := 118140960795 + 770780 * 2 ^ 59
def prefixEnd_770780 : Nat := 4983230072969 + 3 ^ 40 * 770780 * 2
def baseEnd_770780 : Nat := 19544721919634545847173

theorem tailTrace_770780 : CollatzResearch.WordTrace tailWord_770780 prefixEnd_770780 19544721919634545847173 := by
  unfold tailWord_770780
  simp only [CollatzResearch.WordTrace]
  refine ⟨14056328073801586794406897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18741770765068782392542529 14056328073801586794406897)
  ·
    refine ⟨10542246055351190095805173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14056328073801586794406897 10542246055351190095805173)
    ·
      refine ⟨988335567689174071481735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10542246055351190095805173 988335567689174071481735)
      ·
        refine ⟨1482503351533761107222603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 988335567689174071481735 1482503351533761107222603)
        ·
          refine ⟨2223755027300641660833905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1482503351533761107222603 2223755027300641660833905)
          ·
            refine ⟨1667816270475481245625429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2223755027300641660833905 1667816270475481245625429)
            ·
              refine ⟨19544721919634545847173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1667816270475481245625429 19544721919634545847173)
              ·
                rfl

theorem cell21_770780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 8].length) (baseStart_770780 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_770780 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_770780 prefixEnd_770780 := by exact prefixLift 770780
  have htrace : WordTrace (prefixWord ++ tailWord_770780) baseStart_770780 baseEnd_770780 := by
    simpa [prefixWord, tailWord_770780, baseEnd_770780] using wordTrace_append hprefix tailTrace_770780
  have hstable : (prefixWord ++ tailWord_770780).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770780).length < 2 ^ (prefixWord ++ tailWord_770780).sum := by decide
  have hdescent : baseEnd_770780 < baseStart_770780 := by decide
  rcases family_descends (prefixWord ++ tailWord_770780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770845 : List Nat := [1, 4, 2, 4, 2, 1, 1, 1, 5]
def baseStart_770845 : Nat := 118140960795 + 770845 * 2 ^ 59
def prefixEnd_770845 : Nat := 4983230072969 + 3 ^ 40 * 770845 * 2
def baseEnd_770845 : Nat := 175917331162285244041091

theorem tailTrace_770845 : CollatzResearch.WordTrace tailWord_770845 prefixEnd_770845 175917331162285244041091 := by
  unfold tailWord_770845
  simp only [CollatzResearch.WordTrace]
  refine ⟨28115026892367689689929989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18743351261578459793286659 28115026892367689689929989)
  ·
    refine ⟨5271567542318941816861873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28115026892367689689929989 5271567542318941816861873)
    ·
      refine ⟨3953675656739206362646405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5271567542318941816861873 3953675656739206362646405)
      ·
        refine ⟨741314185638601192996201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3953675656739206362646405 741314185638601192996201)
        ·
          refine ⟨555985639228950894747151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 741314185638601192996201 555985639228950894747151)
          ·
            refine ⟨833978458843426342120727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 555985639228950894747151 833978458843426342120727)
            ·
              refine ⟨1250967688265139513181091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 833978458843426342120727 1250967688265139513181091)
              ·
                refine ⟨1876451532397709269771637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1250967688265139513181091 1876451532397709269771637)
                ·
                  refine ⟨175917331162285244041091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1876451532397709269771637 175917331162285244041091)
                  ·
                    rfl

theorem cell21_770845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 1, 1, 5].length) (baseStart_770845 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_770845 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_770845 prefixEnd_770845 := by exact prefixLift 770845
  have htrace : WordTrace (prefixWord ++ tailWord_770845) baseStart_770845 baseEnd_770845 := by
    simpa [prefixWord, tailWord_770845, baseEnd_770845] using wordTrace_append hprefix tailTrace_770845
  have hstable : (prefixWord ++ tailWord_770845).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770845).length < 2 ^ (prefixWord ++ tailWord_770845).sum := by decide
  have hdescent : baseEnd_770845 < baseStart_770845 := by decide
  rcases family_descends (prefixWord ++ tailWord_770845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770901 : List Nat := [1, 3, 2, 2, 2, 1, 4, 2, 4]
def baseStart_770901 : Nat := 118140960795 + 770901 * 2 ^ 59
def prefixEnd_770901 : Nat := 4983230072969 + 3 ^ 40 * 770901 * 2
def baseEnd_770901 : Nat := 175930111125241591107643

theorem tailTrace_770901 : CollatzResearch.WordTrace tailWord_770901 prefixEnd_770901 175930111125241591107643 := by
  unfold tailWord_770901
  simp only [CollatzResearch.WordTrace]
  refine ⟨28117069380164811253968557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18744712920109874169312371 28117069380164811253968557)
  ·
    refine ⟨10543901017561804220238209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28117069380164811253968557 10543901017561804220238209)
    ·
      refine ⟨7907925763171353165178657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10543901017561804220238209 7907925763171353165178657)
      ·
        refine ⟨5930944322378514873883993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7907925763171353165178657 5930944322378514873883993)
        ·
          refine ⟨4448208241783886155412995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5930944322378514873883993 4448208241783886155412995)
          ·
            refine ⟨6672312362675829233119493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4448208241783886155412995 6672312362675829233119493)
            ·
              refine ⟨1251058568001717981209905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6672312362675829233119493 1251058568001717981209905)
              ·
                refine ⟨938293926001288485907429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1251058568001717981209905 938293926001288485907429)
                ·
                  refine ⟨175930111125241591107643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 938293926001288485907429 175930111125241591107643)
                  ·
                    rfl

theorem cell21_770901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4, 2, 4].length) (baseStart_770901 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_770901 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_770901 prefixEnd_770901 := by exact prefixLift 770901
  have htrace : WordTrace (prefixWord ++ tailWord_770901) baseStart_770901 baseEnd_770901 := by
    simpa [prefixWord, tailWord_770901, baseEnd_770901] using wordTrace_append hprefix tailTrace_770901
  have hstable : (prefixWord ++ tailWord_770901).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770901).length < 2 ^ (prefixWord ++ tailWord_770901).sum := by decide
  have hdescent : baseEnd_770901 < baseStart_770901 := by decide
  rcases family_descends (prefixWord ++ tailWord_770901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770915 : List Nat := [1, 1, 1, 5, 3, 1, 3, 6]
def baseStart_770915 : Nat := 118140960795 + 770915 * 2 ^ 59
def prefixEnd_770915 : Nat := 4983230072969 + 3 ^ 40 * 770915 * 2
def baseEnd_770915 : Nat := 58644435371993559291427

theorem tailTrace_770915 : CollatzResearch.WordTrace tailWord_770915 prefixEnd_770915 58644435371993559291427 := by
  unfold tailWord_770915
  simp only [CollatzResearch.WordTrace]
  refine ⟨28117580002114091644978199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18745053334742727763318799 28117580002114091644978199)
  ·
    refine ⟨42176370003171137467467299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28117580002114091644978199 42176370003171137467467299)
    ·
      refine ⟨63264555004756706201200949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42176370003171137467467299 63264555004756706201200949)
      ·
        refine ⟨5931052031695941206362589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 63264555004756706201200949 5931052031695941206362589)
        ·
          refine ⟨2224144511885977952385971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5931052031695941206362589 2224144511885977952385971)
          ·
            refine ⟨3336216767828966928578957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2224144511885977952385971 3336216767828966928578957)
            ·
              refine ⟨1251081287935862598217109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3336216767828966928578957 1251081287935862598217109)
              ·
                refine ⟨58644435371993559291427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1251081287935862598217109 58644435371993559291427)
                ·
                  rfl

theorem cell21_770915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3, 6].length) (baseStart_770915 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_770915 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_770915 prefixEnd_770915 := by exact prefixLift 770915
  have htrace : WordTrace (prefixWord ++ tailWord_770915) baseStart_770915 baseEnd_770915 := by
    simpa [prefixWord, tailWord_770915, baseEnd_770915] using wordTrace_append hprefix tailTrace_770915
  have hstable : (prefixWord ++ tailWord_770915).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770915).length < 2 ^ (prefixWord ++ tailWord_770915).sum := by decide
  have hdescent : baseEnd_770915 < baseStart_770915 := by decide
  rcases family_descends (prefixWord ++ tailWord_770915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770929 : List Nat := [1, 2, 2, 2, 1, 4, 1, 1, 7]
def baseStart_770929 : Nat := 118140960795 + 770929 * 2 ^ 59
def prefixEnd_770929 : Nat := 4983230072969 + 3 ^ 40 * 770929 * 2
def baseEnd_770929 : Nat := 175936501106719764640919

theorem tailTrace_770929 : CollatzResearch.WordTrace tailWord_770929 prefixEnd_770929 175936501106719764640919 := by
  unfold tailWord_770929
  simp only [CollatzResearch.WordTrace]
  refine ⟨28118090624063372035987841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18745393749375581357325227 28118090624063372035987841)
  ·
    refine ⟨21088567968047529026990881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28118090624063372035987841 21088567968047529026990881)
    ·
      refine ⟨15816425976035646770243161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21088567968047529026990881 15816425976035646770243161)
      ·
        refine ⟨11862319482026735077682371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15816425976035646770243161 11862319482026735077682371)
        ·
          refine ⟨17793479223040102616523557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11862319482026735077682371 17793479223040102616523557)
          ·
            refine ⟨3336277354320019240598167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17793479223040102616523557 3336277354320019240598167)
            ·
              refine ⟨5004416031480028860897251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3336277354320019240598167 5004416031480028860897251)
              ·
                refine ⟨7506624047220043291345877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5004416031480028860897251 7506624047220043291345877)
                ·
                  refine ⟨175936501106719764640919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7506624047220043291345877 175936501106719764640919)
                  ·
                    rfl

theorem cell21_770929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 1, 7].length) (baseStart_770929 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_770929 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_770929 prefixEnd_770929 := by exact prefixLift 770929
  have htrace : WordTrace (prefixWord ++ tailWord_770929) baseStart_770929 baseEnd_770929 := by
    simpa [prefixWord, tailWord_770929, baseEnd_770929] using wordTrace_append hprefix tailTrace_770929
  have hstable : (prefixWord ++ tailWord_770929).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770929).length < 2 ^ (prefixWord ++ tailWord_770929).sum := by decide
  have hdescent : baseEnd_770929 < baseStart_770929 := by decide
  rcases family_descends (prefixWord ++ tailWord_770929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771022 : List Nat := [4, 1, 1, 1, 2, 3, 3, 1, 5]
def baseStart_771022 : Nat := 118140960795 + 771022 * 2 ^ 59
def prefixEnd_771022 : Nat := 4983230072969 + 3 ^ 40 * 771022 * 2
def baseEnd_771022 : Nat := 175957724973772269590729

theorem tailTrace_771022 : CollatzResearch.WordTrace tailWord_771022 prefixEnd_771022 175957724973772269590729 := by
  unfold tailWord_771022
  simp only [CollatzResearch.WordTrace]
  refine ⟨3515185326590806114890415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18747655075150965946082213 3515185326590806114890415)
  ·
    refine ⟨5272777989886209172335623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3515185326590806114890415 5272777989886209172335623)
    ·
      refine ⟨7909166984829313758503435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5272777989886209172335623 7909166984829313758503435)
      ·
        refine ⟨11863750477243970637755153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7909166984829313758503435 11863750477243970637755153)
        ·
          refine ⟨8897812857932977978316365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11863750477243970637755153 8897812857932977978316365)
          ·
            refine ⟨3336679821724866741868637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8897812857932977978316365 3336679821724866741868637)
            ·
              refine ⟨1251254933146825028200739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3336679821724866741868637 1251254933146825028200739)
              ·
                refine ⟨1876882399720237542301109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1251254933146825028200739 1876882399720237542301109)
                ·
                  refine ⟨175957724973772269590729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1876882399720237542301109 175957724973772269590729)
                  ·
                    rfl

theorem cell21_771022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3, 1, 5].length) (baseStart_771022 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_771022 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_771022 prefixEnd_771022 := by exact prefixLift 771022
  have htrace : WordTrace (prefixWord ++ tailWord_771022) baseStart_771022 baseEnd_771022 := by
    simpa [prefixWord, tailWord_771022, baseEnd_771022] using wordTrace_append hprefix tailTrace_771022
  have hstable : (prefixWord ++ tailWord_771022).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771022).length < 2 ^ (prefixWord ++ tailWord_771022).sum := by decide
  have hdescent : baseEnd_771022 < baseStart_771022 := by decide
  rcases family_descends (prefixWord ++ tailWord_771022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771129 : List Nat := [1, 2, 1, 5, 2, 1, 3, 2, 4]
def baseStart_771129 : Nat := 118140960795 + 771129 * 2 ^ 59
def prefixEnd_771129 : Nat := 4983230072969 + 3 ^ 40 * 771129 * 2
def baseEnd_771129 : Nat := 175982143831563861307177

theorem tailTrace_771129 : CollatzResearch.WordTrace tailWord_771129 prefixEnd_771129 175982143831563861307177 := by
  unfold tailWord_771129
  simp only [CollatzResearch.WordTrace]
  refine ⟨28125385223338806193268441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18750256815559204128845627 28125385223338806193268441)
  ·
    refine ⟨21094038917504104644951331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28125385223338806193268441 21094038917504104644951331)
    ·
      refine ⟨31641058376256156967426997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21094038917504104644951331 31641058376256156967426997)
      ·
        refine ⟨2966349222774014715696281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31641058376256156967426997 2966349222774014715696281)
        ·
          refine ⟨2224761917080511036772211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2966349222774014715696281 2224761917080511036772211)
          ·
            refine ⟨3337142875620766555158317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2224761917080511036772211 3337142875620766555158317)
            ·
              refine ⟨1251428578357787458184369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3337142875620766555158317 1251428578357787458184369)
              ·
                refine ⟨938571433768340593638277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1251428578357787458184369 938571433768340593638277)
                ·
                  refine ⟨175982143831563861307177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 938571433768340593638277 175982143831563861307177)
                  ·
                    rfl

theorem cell21_771129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3, 2, 4].length) (baseStart_771129 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_771129 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_771129 prefixEnd_771129 := by exact prefixLift 771129
  have htrace : WordTrace (prefixWord ++ tailWord_771129) baseStart_771129 baseEnd_771129 := by
    simpa [prefixWord, tailWord_771129, baseEnd_771129] using wordTrace_append hprefix tailTrace_771129
  have hstable : (prefixWord ++ tailWord_771129).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771129).length < 2 ^ (prefixWord ++ tailWord_771129).sum := by decide
  have hdescent : baseEnd_771129 < baseStart_771129 := by decide
  rcases family_descends (prefixWord ++ tailWord_771129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771157 : List Nat := [1, 3, 2, 2, 1, 2, 1, 4, 5]
def baseStart_771157 : Nat := 118140960795 + 771157 * 2 ^ 59
def prefixEnd_771157 : Nat := 4983230072969 + 3 ^ 40 * 771157 * 2
def baseEnd_771157 : Nat := 175988533813042034840453

theorem tailTrace_771157 : CollatzResearch.WordTrace tailWord_771157 prefixEnd_771157 175988533813042034840453 := by
  unfold tailWord_771157
  simp only [CollatzResearch.WordTrace]
  refine ⟨28126406467237366975287725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18750937644824911316858483 28126406467237366975287725)
  ·
    refine ⟨10547402425214012615732897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28126406467237366975287725 10547402425214012615732897)
    ·
      refine ⟨7910551818910509461799673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10547402425214012615732897 7910551818910509461799673)
      ·
        refine ⟨5932913864182882096349755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7910551818910509461799673 5932913864182882096349755)
        ·
          refine ⟨8899370796274323144524633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5932913864182882096349755 8899370796274323144524633)
          ·
            refine ⟨6674528097205742358393475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8899370796274323144524633 6674528097205742358393475)
            ·
              refine ⟨10011792145808613537590213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6674528097205742358393475 10011792145808613537590213)
              ·
                refine ⟨1877211027339115038298165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10011792145808613537590213 1877211027339115038298165)
                ·
                  refine ⟨175988533813042034840453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1877211027339115038298165 175988533813042034840453)
                  ·
                    rfl

theorem cell21_771157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 4, 5].length) (baseStart_771157 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_771157 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_771157 prefixEnd_771157 := by exact prefixLift 771157
  have htrace : WordTrace (prefixWord ++ tailWord_771157) baseStart_771157 baseEnd_771157 := by
    simpa [prefixWord, tailWord_771157, baseEnd_771157] using wordTrace_append hprefix tailTrace_771157
  have hstable : (prefixWord ++ tailWord_771157).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771157).length < 2 ^ (prefixWord ++ tailWord_771157).sum := by decide
  have hdescent : baseEnd_771157 < baseStart_771157 := by decide
  rcases family_descends (prefixWord ++ tailWord_771157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771166 : List Nat := [4, 4, 1, 1, 1, 3, 1, 3, 3]
def baseStart_771166 : Nat := 118140960795 + 771166 * 2 ^ 59
def prefixEnd_771166 : Nat := 4983230072969 + 3 ^ 40 * 771166 * 2
def baseEnd_771166 : Nat := 175990587735660019190435

theorem tailTrace_771166 : CollatzResearch.WordTrace tailWord_771166 prefixEnd_771166 175990587735660019190435 := by
  unfold tailWord_771166
  simp only [CollatzResearch.WordTrace]
  refine ⟨3515841840525595189045669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18751156482803174341576901 3515841840525595189045669)
  ·
    refine ⟨659220345098549097946063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3515841840525595189045669 659220345098549097946063)
    ·
      refine ⟨988830517647823646919095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 659220345098549097946063 988830517647823646919095)
      ·
        refine ⟨1483245776471735470378643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 988830517647823646919095 1483245776471735470378643)
        ·
          refine ⟨2224868664707603205567965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1483245776471735470378643 2224868664707603205567965)
          ·
            refine ⟨834325749265351202087987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2224868664707603205567965 834325749265351202087987)
            ·
              refine ⟨1251488623898026803131981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 834325749265351202087987 1251488623898026803131981)
              ·
                refine ⟨469308233961760051174493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1251488623898026803131981 469308233961760051174493)
                ·
                  refine ⟨175990587735660019190435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 469308233961760051174493 175990587735660019190435)
                  ·
                    rfl

theorem cell21_771166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_771166 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_771166 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_771166 prefixEnd_771166 := by exact prefixLift 771166
  have htrace : WordTrace (prefixWord ++ tailWord_771166) baseStart_771166 baseEnd_771166 := by
    simpa [prefixWord, tailWord_771166, baseEnd_771166] using wordTrace_append hprefix tailTrace_771166
  have hstable : (prefixWord ++ tailWord_771166).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771166).length < 2 ^ (prefixWord ++ tailWord_771166).sum := by decide
  have hdescent : baseEnd_771166 < baseStart_771166 := by decide
  rcases family_descends (prefixWord ++ tailWord_771166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771191 : List Nat := [1, 1, 3, 1, 1, 4, 5, 2, 3]
def baseStart_771191 : Nat := 118140960795 + 771191 * 2 ^ 59
def prefixEnd_771191 : Nat := 4983230072969 + 3 ^ 40 * 771191 * 2
def baseEnd_771191 : Nat := 175996293076265531273717

theorem tailTrace_771191 : CollatzResearch.WordTrace tailWord_771191 prefixEnd_771191 175996293076265531273717 := by
  unfold tailWord_771191
  simp only [CollatzResearch.WordTrace]
  refine ⟨28127646549114190782025427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18751764366076127188016951 28127646549114190782025427)
  ·
    refine ⟨42191469823671286173038141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28127646549114190782025427 42191469823671286173038141)
    ·
      refine ⟨15821801183876732314889303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42191469823671286173038141 15821801183876732314889303)
      ·
        refine ⟨23732701775815098472333955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15821801183876732314889303 23732701775815098472333955)
        ·
          refine ⟨35599052663722647708500933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23732701775815098472333955 35599052663722647708500933)
          ·
            refine ⟨6674822374447996445343925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35599052663722647708500933 6674822374447996445343925)
            ·
              refine ⟨625764597604499666750993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6674822374447996445343925 625764597604499666750993)
              ·
                refine ⟨469323448203374750063245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 625764597604499666750993 469323448203374750063245)
                ·
                  refine ⟨175996293076265531273717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 469323448203374750063245 175996293076265531273717)
                  ·
                    rfl

theorem cell21_771191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 5, 2, 3].length) (baseStart_771191 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_771191 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_771191 prefixEnd_771191 := by exact prefixLift 771191
  have htrace : WordTrace (prefixWord ++ tailWord_771191) baseStart_771191 baseEnd_771191 := by
    simpa [prefixWord, tailWord_771191, baseEnd_771191] using wordTrace_append hprefix tailTrace_771191
  have hstable : (prefixWord ++ tailWord_771191).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771191).length < 2 ^ (prefixWord ++ tailWord_771191).sum := by decide
  have hdescent : baseEnd_771191 < baseStart_771191 := by decide
  rcases family_descends (prefixWord ++ tailWord_771191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771205 : List Nat := [1, 3, 1, 1, 6, 1, 1, 3, 4]
def baseStart_771205 : Nat := 118140960795 + 771205 * 2 ^ 59
def prefixEnd_771205 : Nat := 4983230072969 + 3 ^ 40 * 771205 * 2
def baseEnd_771205 : Nat := 175999488067004618040355

theorem tailTrace_771205 : CollatzResearch.WordTrace tailWord_771205 prefixEnd_771205 175999488067004618040355 := by
  unfold tailWord_771205
  simp only [CollatzResearch.WordTrace]
  refine ⟨28128157171063471173035069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18752104780708980782023379 28128157171063471173035069)
  ·
    refine ⟨10548058939148801689888151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28128157171063471173035069 10548058939148801689888151)
    ·
      refine ⟨15822088408723202534832227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10548058939148801689888151 15822088408723202534832227)
      ·
        refine ⟨23733132613084803802248341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15822088408723202534832227 23733132613084803802248341)
        ·
          refine ⟨1112490591238350178230391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 23733132613084803802248341 1112490591238350178230391)
          ·
            refine ⟨1668735886857525267345587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1112490591238350178230391 1668735886857525267345587)
            ·
              refine ⟨2503103830286287901018381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1668735886857525267345587 2503103830286287901018381)
              ·
                refine ⟨938663936357357962881893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2503103830286287901018381 938663936357357962881893)
                ·
                  refine ⟨175999488067004618040355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 938663936357357962881893 175999488067004618040355)
                  ·
                    rfl

theorem cell21_771205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 3, 4].length) (baseStart_771205 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_771205 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_771205 prefixEnd_771205 := by exact prefixLift 771205
  have htrace : WordTrace (prefixWord ++ tailWord_771205) baseStart_771205 baseEnd_771205 := by
    simpa [prefixWord, tailWord_771205, baseEnd_771205] using wordTrace_append hprefix tailTrace_771205
  have hstable : (prefixWord ++ tailWord_771205).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771205).length < 2 ^ (prefixWord ++ tailWord_771205).sum := by decide
  have hdescent : baseEnd_771205 < baseStart_771205 := by decide
  rcases family_descends (prefixWord ++ tailWord_771205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771247 : List Nat := [1, 1, 2, 1, 2, 3, 2, 3, 6]
def baseStart_771247 : Nat := 118140960795 + 771247 * 2 ^ 59
def prefixEnd_771247 : Nat := 4983230072969 + 3 ^ 40 * 771247 * 2
def baseEnd_771247 : Nat := 176009073039221878340269

theorem tailTrace_771247 : CollatzResearch.WordTrace tailWord_771247 prefixEnd_771247 176009073039221878340269 := by
  unfold tailWord_771247
  simp only [CollatzResearch.WordTrace]
  refine ⟨28129689036911312346063995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18753126024607541564042663 28129689036911312346063995)
  ·
    refine ⟨42194533555366968519095993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28129689036911312346063995 42194533555366968519095993)
    ·
      refine ⟨31645900166525226389321995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42194533555366968519095993 31645900166525226389321995)
      ·
        refine ⟨47468850249787839583982993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31645900166525226389321995 47468850249787839583982993)
        ·
          refine ⟨35601637687340879687987245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47468850249787839583982993 35601637687340879687987245)
          ·
            refine ⟨13350614132752829882995217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35601637687340879687987245 13350614132752829882995217)
            ·
              refine ⟨10012960599564622412246413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13350614132752829882995217 10012960599564622412246413)
              ·
                refine ⟨3754860224836733404592405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10012960599564622412246413 3754860224836733404592405)
                ·
                  refine ⟨176009073039221878340269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3754860224836733404592405 176009073039221878340269)
                  ·
                    rfl

theorem cell21_771247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 3, 6].length) (baseStart_771247 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_771247 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_771247 prefixEnd_771247 := by exact prefixLift 771247
  have htrace : WordTrace (prefixWord ++ tailWord_771247) baseStart_771247 baseEnd_771247 := by
    simpa [prefixWord, tailWord_771247, baseEnd_771247] using wordTrace_append hprefix tailTrace_771247
  have hstable : (prefixWord ++ tailWord_771247).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771247).length < 2 ^ (prefixWord ++ tailWord_771247).sum := by decide
  have hdescent : baseEnd_771247 < baseStart_771247 := by decide
  rcases family_descends (prefixWord ++ tailWord_771247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771326 : List Nat := [4, 2, 2, 1, 1, 2, 2, 2, 5]
def baseStart_771326 : Nat := 118140960795 + 771326 * 2 ^ 59
def prefixEnd_771326 : Nat := 4983230072969 + 3 ^ 40 * 771326 * 2
def baseEnd_771326 : Nat := 176027101915535296523441

theorem tailTrace_771326 : CollatzResearch.WordTrace tailWord_771326 prefixEnd_771326 176027101915535296523441 := by
  unfold tailWord_771326
  simp only [CollatzResearch.WordTrace]
  refine ⟨3516571300453138604773729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18755046935750072558793221 3516571300453138604773729)
  ·
    refine ⟨2637428475339853953580297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3516571300453138604773729 2637428475339853953580297)
    ·
      refine ⟨1978071356504890465185223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2637428475339853953580297 1978071356504890465185223)
      ·
        refine ⟨2967107034757335697777835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1978071356504890465185223 2967107034757335697777835)
        ·
          refine ⟨4450660552136003546666753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2967107034757335697777835 4450660552136003546666753)
          ·
            refine ⟨3337995414102002660000065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4450660552136003546666753 3337995414102002660000065)
            ·
              refine ⟨2503496560576501995000049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3337995414102002660000065 2503496560576501995000049)
              ·
                refine ⟨1877622420432376496250037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2503496560576501995000049 1877622420432376496250037)
                ·
                  refine ⟨176027101915535296523441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1877622420432376496250037 176027101915535296523441)
                  ·
                    rfl

theorem cell21_771326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_771326 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_771326 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_771326 prefixEnd_771326 := by exact prefixLift 771326
  have htrace : WordTrace (prefixWord ++ tailWord_771326) baseStart_771326 baseEnd_771326 := by
    simpa [prefixWord, tailWord_771326, baseEnd_771326] using wordTrace_append hprefix tailTrace_771326
  have hstable : (prefixWord ++ tailWord_771326).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771326).length < 2 ^ (prefixWord ++ tailWord_771326).sum := by decide
  have hdescent : baseEnd_771326 < baseStart_771326 := by decide
  rcases family_descends (prefixWord ++ tailWord_771326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771354 : List Nat := [3, 1, 1, 3, 3, 1, 9]
def baseStart_771354 : Nat := 118140960795 + 771354 * 2 ^ 59
def prefixEnd_771354 : Nat := 4983230072969 + 3 ^ 40 * 771354 * 2
def baseEnd_771354 : Nat := 19559276877445941117413

theorem tailTrace_771354 : CollatzResearch.WordTrace tailWord_771354 prefixEnd_771354 19559276877445941117413 := by
  unfold tailWord_771354
  simp only [CollatzResearch.WordTrace]
  refine ⟨7033397911880917405052279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18755727765015779746806077 7033397911880917405052279)
  ·
    refine ⟨10550096867821376107578419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7033397911880917405052279 10550096867821376107578419)
    ·
      refine ⟨15825145301732064161367629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10550096867821376107578419 15825145301732064161367629)
      ·
        refine ⟨5934429488149524060512861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15825145301732064161367629 5934429488149524060512861)
        ·
          refine ⟨2225411058056071522692323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5934429488149524060512861 2225411058056071522692323)
          ·
            refine ⟨3338116587084107284038485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2225411058056071522692323 3338116587084107284038485)
            ·
              refine ⟨19559276877445941117413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3338116587084107284038485 19559276877445941117413)
              ·
                rfl

theorem cell21_771354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 9].length) (baseStart_771354 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_771354 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_771354 prefixEnd_771354 := by exact prefixLift 771354
  have htrace : WordTrace (prefixWord ++ tailWord_771354) baseStart_771354 baseEnd_771354 := by
    simpa [prefixWord, tailWord_771354, baseEnd_771354] using wordTrace_append hprefix tailTrace_771354
  have hstable : (prefixWord ++ tailWord_771354).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771354).length < 2 ^ (prefixWord ++ tailWord_771354).sum := by decide
  have hdescent : baseEnd_771354 < baseStart_771354 := by decide
  rcases family_descends (prefixWord ++ tailWord_771354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771360 : List Nat := [2, 1, 1, 5, 3, 1, 3, 2, 3]
def baseStart_771360 : Nat := 118140960795 + 771360 * 2 ^ 59
def prefixEnd_771360 : Nat := 4983230072969 + 3 ^ 40 * 771360 * 2
def baseEnd_771360 : Nat := 176034861178758792956705

theorem tailTrace_771360 : CollatzResearch.WordTrace tailWord_771360 prefixEnd_771360 176034861178758792956705 := by
  unfold tailWord_771360
  simp only [CollatzResearch.WordTrace]
  refine ⟨14066905242750966322463767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18755873657001288429951689 14066905242750966322463767)
  ·
    refine ⟨21100357864126449483695651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14066905242750966322463767 21100357864126449483695651)
    ·
      refine ⟨31650536796189674225543477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21100357864126449483695651 31650536796189674225543477)
      ·
        refine ⟨2967237824642781958644701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31650536796189674225543477 2967237824642781958644701)
        ·
          refine ⟨1112714184241043234491763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2967237824642781958644701 1112714184241043234491763)
          ·
            refine ⟨1669071276361564851737645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1112714184241043234491763 1669071276361564851737645)
            ·
              refine ⟨625901728635586819401617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1669071276361564851737645 625901728635586819401617)
              ·
                refine ⟨469426296476690114551213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 625901728635586819401617 469426296476690114551213)
                ·
                  refine ⟨176034861178758792956705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 469426296476690114551213 176034861178758792956705)
                  ·
                    rfl

theorem cell21_771360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 3, 2, 3].length) (baseStart_771360 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_771360 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_771360 prefixEnd_771360 := by exact prefixLift 771360
  have htrace : WordTrace (prefixWord ++ tailWord_771360) baseStart_771360 baseEnd_771360 := by
    simpa [prefixWord, tailWord_771360, baseEnd_771360] using wordTrace_append hprefix tailTrace_771360
  have hstable : (prefixWord ++ tailWord_771360).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771360).length < 2 ^ (prefixWord ++ tailWord_771360).sum := by decide
  have hdescent : baseEnd_771360 < baseStart_771360 := by decide
  rcases family_descends (prefixWord ++ tailWord_771360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771416 : List Nat := [2, 1, 2, 2, 1, 1, 6, 2, 4]
def baseStart_771416 : Nat := 118140960795 + 771416 * 2 ^ 59
def prefixEnd_771416 : Nat := 4983230072969 + 3 ^ 40 * 771416 * 2
def baseEnd_771416 : Nat := 176047641141715140023257

theorem tailTrace_771416 : CollatzResearch.WordTrace tailWord_771416 prefixEnd_771416 176047641141715140023257 := by
  unfold tailWord_771416
  simp only [CollatzResearch.WordTrace]
  refine ⟨14067926486649527104483051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18757235315532702805977401 14067926486649527104483051)
  ·
    refine ⟨21101889729974290656724577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14067926486649527104483051 21101889729974290656724577)
    ·
      refine ⟨15826417297480717992543433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21101889729974290656724577 15826417297480717992543433)
      ·
        refine ⟨11869812973110538494407575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15826417297480717992543433 11869812973110538494407575)
        ·
          refine ⟨17804719459665807741611363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11869812973110538494407575 17804719459665807741611363)
          ·
            refine ⟨26707079189498711612417045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17804719459665807741611363 26707079189498711612417045)
            ·
              refine ⟨1251894337007752106832049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 26707079189498711612417045 1251894337007752106832049)
              ·
                refine ⟨938920752755814080124037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1251894337007752106832049 938920752755814080124037)
                ·
                  refine ⟨176047641141715140023257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 938920752755814080124037 176047641141715140023257)
                  ·
                    rfl

theorem cell21_771416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6, 2, 4].length) (baseStart_771416 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_771416 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_771416 prefixEnd_771416 := by exact prefixLift 771416
  have htrace : WordTrace (prefixWord ++ tailWord_771416) baseStart_771416 baseEnd_771416 := by
    simpa [prefixWord, tailWord_771416, baseEnd_771416] using wordTrace_append hprefix tailTrace_771416
  have hstable : (prefixWord ++ tailWord_771416).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771416).length < 2 ^ (prefixWord ++ tailWord_771416).sum := by decide
  have hdescent : baseEnd_771416 < baseStart_771416 := by decide
  rcases family_descends (prefixWord ++ tailWord_771416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771520 : List Nat := [2, 1, 1, 2, 3, 1, 2, 2, 7]
def baseStart_771520 : Nat := 118140960795 + 771520 * 2 ^ 59
def prefixEnd_771520 : Nat := 4983230072969 + 3 ^ 40 * 771520 * 2
def baseEnd_771520 : Nat := 176071375358634070289711

theorem tailTrace_771520 : CollatzResearch.WordTrace tailWord_771520 prefixEnd_771520 176071375358634070289711 := by
  unfold tailWord_771520
  simp only [CollatzResearch.WordTrace]
  refine ⟨14069823082461139985376007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18759764109948186647168009 14069823082461139985376007)
  ·
    refine ⟨21104734623691709978064011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14069823082461139985376007 21104734623691709978064011)
    ·
      refine ⟨31657101935537564967096017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21104734623691709978064011 31657101935537564967096017)
      ·
        refine ⟨23742826451653173725322013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31657101935537564967096017 23742826451653173725322013)
        ·
          refine ⟨8903559919369940146995755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23742826451653173725322013 8903559919369940146995755)
          ·
            refine ⟨13355339879054910220493633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8903559919369940146995755 13355339879054910220493633)
            ·
              refine ⟨10016504909291182665370225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13355339879054910220493633 10016504909291182665370225)
              ·
                refine ⟨7512378681968386999027669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10016504909291182665370225 7512378681968386999027669)
                ·
                  refine ⟨176071375358634070289711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7512378681968386999027669 176071375358634070289711)
                  ·
                    rfl

theorem cell21_771520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 2, 7].length) (baseStart_771520 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_771520 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_771520 prefixEnd_771520 := by exact prefixLift 771520
  have htrace : WordTrace (prefixWord ++ tailWord_771520) baseStart_771520 baseEnd_771520 := by
    simpa [prefixWord, tailWord_771520, baseEnd_771520] using wordTrace_append hprefix tailTrace_771520
  have hstable : (prefixWord ++ tailWord_771520).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771520).length < 2 ^ (prefixWord ++ tailWord_771520).sum := by decide
  have hdescent : baseEnd_771520 < baseStart_771520 := by decide
  rcases family_descends (prefixWord ++ tailWord_771520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771585 : List Nat := [1, 2, 4, 1, 4, 1, 2, 2, 4]
def baseStart_771585 : Nat := 118140960795 + 771585 * 2 ^ 59
def prefixEnd_771585 : Nat := 4983230072969 + 3 ^ 40 * 771585 * 2
def baseEnd_771585 : Nat := 176086209244208401706245

theorem tailTrace_771585 : CollatzResearch.WordTrace tailWord_771585 prefixEnd_771585 176086209244208401706245 := by
  unfold tailWord_771585
  simp only [CollatzResearch.WordTrace]
  refine ⟨28142016909686796071868209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18761344606457864047912139 28142016909686796071868209)
  ·
    refine ⟨21106512682265097053901157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28142016909686796071868209 21106512682265097053901157)
    ·
      refine ⟨3957471127924705697606467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21106512682265097053901157 3957471127924705697606467)
      ·
        refine ⟨5936206691887058546409701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3957471127924705697606467 5936206691887058546409701)
        ·
          refine ⟨1113038754728823477451819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5936206691887058546409701 1113038754728823477451819)
          ·
            refine ⟨1669558132093235216177729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1113038754728823477451819 1669558132093235216177729)
            ·
              refine ⟨1252168599069926412133297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1669558132093235216177729 1252168599069926412133297)
              ·
                refine ⟨939126449302444809099973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1252168599069926412133297 939126449302444809099973)
                ·
                  refine ⟨176086209244208401706245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 939126449302444809099973 176086209244208401706245)
                  ·
                    rfl

theorem cell21_771585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 2, 2, 4].length) (baseStart_771585 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_771585 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_771585 prefixEnd_771585 := by exact prefixLift 771585
  have htrace : WordTrace (prefixWord ++ tailWord_771585) baseStart_771585 baseEnd_771585 := by
    simpa [prefixWord, tailWord_771585, baseEnd_771585] using wordTrace_append hprefix tailTrace_771585
  have hstable : (prefixWord ++ tailWord_771585).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771585).length < 2 ^ (prefixWord ++ tailWord_771585).sum := by decide
  have hdescent : baseEnd_771585 < baseStart_771585 := by decide
  rcases family_descends (prefixWord ++ tailWord_771585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771613 : List Nat := [1, 4, 2, 2, 1, 1, 3, 2, 5]
def baseStart_771613 : Nat := 118140960795 + 771613 * 2 ^ 59
def prefixEnd_771613 : Nat := 4983230072969 + 3 ^ 40 * 771613 * 2
def baseEnd_771613 : Nat := 176092599225686575239521

theorem tailTrace_771613 : CollatzResearch.WordTrace tailWord_771613 prefixEnd_771613 176092599225686575239521 := by
  unfold tailWord_771613
  simp only [CollatzResearch.WordTrace]
  refine ⟨28143038153585356853887493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18762025435723571235924995 28143038153585356853887493)
  ·
    refine ⟨5276819653797254410103905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28143038153585356853887493 5276819653797254410103905)
    ·
      refine ⟨3957614740347940807577929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5276819653797254410103905 3957614740347940807577929)
      ·
        refine ⟨2968211055260955605683447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3957614740347940807577929 2968211055260955605683447)
        ·
          refine ⟨4452316582891433408525171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2968211055260955605683447 4452316582891433408525171)
          ·
            refine ⟨6678474874337150112787757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4452316582891433408525171 6678474874337150112787757)
            ·
              refine ⟨2504428077876431292295409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6678474874337150112787757 2504428077876431292295409)
              ·
                refine ⟨1878321058407323469221557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2504428077876431292295409 1878321058407323469221557)
                ·
                  refine ⟨176092599225686575239521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1878321058407323469221557 176092599225686575239521)
                  ·
                    rfl

theorem cell21_771613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 2, 5].length) (baseStart_771613 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_771613 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_771613 prefixEnd_771613 := by exact prefixLift 771613
  have htrace : WordTrace (prefixWord ++ tailWord_771613) baseStart_771613 baseEnd_771613 := by
    simpa [prefixWord, tailWord_771613, baseEnd_771613] using wordTrace_append hprefix tailTrace_771613
  have hstable : (prefixWord ++ tailWord_771613).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771613).length < 2 ^ (prefixWord ++ tailWord_771613).sum := by decide
  have hdescent : baseEnd_771613 < baseStart_771613 := by decide
  rcases family_descends (prefixWord ++ tailWord_771613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771644 : List Nat := [2, 2, 2, 2, 4, 1, 1, 1, 6]
def baseStart_771644 : Nat := 118140960795 + 771644 * 2 ^ 59
def prefixEnd_771644 : Nat := 4983230072969 + 3 ^ 40 * 771644 * 2
def baseEnd_771644 : Nat := 176099673848037410222791

theorem tailTrace_771644 : CollatzResearch.WordTrace tailWord_771644 prefixEnd_771644 176099673848037410222791 := by
  unfold tailWord_771644
  simp only [CollatzResearch.WordTrace]
  refine ⟨14072084408236524574132993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18762779210982032765510657 14072084408236524574132993)
  ·
    refine ⟨10554063306177393430599745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14072084408236524574132993 10554063306177393430599745)
    ·
      refine ⟨7915547479633045072949809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10554063306177393430599745 7915547479633045072949809)
      ·
        refine ⟨5936660609724783804712357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7915547479633045072949809 5936660609724783804712357)
        ·
          refine ⟨1113123864323396963383567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5936660609724783804712357 1113123864323396963383567)
          ·
            refine ⟨1669685796485095445075351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1113123864323396963383567 1669685796485095445075351)
            ·
              refine ⟨2504528694727643167613027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1669685796485095445075351 2504528694727643167613027)
              ·
                refine ⟨3756793042091464751419541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2504528694727643167613027 3756793042091464751419541)
                ·
                  refine ⟨176099673848037410222791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3756793042091464751419541 176099673848037410222791)
                  ·
                    rfl

theorem cell21_771644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 1, 6].length) (baseStart_771644 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_771644 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_771644 prefixEnd_771644 := by exact prefixLift 771644
  have htrace : WordTrace (prefixWord ++ tailWord_771644) baseStart_771644 baseEnd_771644 := by
    simpa [prefixWord, tailWord_771644, baseEnd_771644] using wordTrace_append hprefix tailTrace_771644
  have hstable : (prefixWord ++ tailWord_771644).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771644).length < 2 ^ (prefixWord ++ tailWord_771644).sum := by decide
  have hdescent : baseEnd_771644 < baseStart_771644 := by decide
  rcases family_descends (prefixWord ++ tailWord_771644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771703 : List Nat := [1, 1, 3, 1, 1, 3, 1, 6, 4]
def baseStart_771703 : Nat := 118140960795 + 771703 * 2 ^ 59
def prefixEnd_771703 : Nat := 4983230072969 + 3 ^ 40 * 771703 * 2
def baseEnd_771703 : Nat := 176113138451866418739337

theorem tailTrace_771703 : CollatzResearch.WordTrace tailWord_771703 prefixEnd_771703 176113138451866418739337 := by
  unfold tailWord_771703
  simp only [CollatzResearch.WordTrace]
  refine ⟨28146320723259302224663763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18764213815506201483109175 28146320723259302224663763)
  ·
    refine ⟨42219481084888953336995645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28146320723259302224663763 42219481084888953336995645)
    ·
      refine ⟨15832305406833357501373367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42219481084888953336995645 15832305406833357501373367)
      ·
        refine ⟨23748458110250036252060051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15832305406833357501373367 23748458110250036252060051)
        ·
          refine ⟨35622687165375054378090077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23748458110250036252060051 35622687165375054378090077)
          ·
            refine ⟨13358507687015645391783779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35622687165375054378090077 13358507687015645391783779)
            ·
              refine ⟨20037761530523468087675669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13358507687015645391783779 20037761530523468087675669)
              ·
                refine ⟨939270071743287566609797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 20037761530523468087675669 939270071743287566609797)
                ·
                  refine ⟨176113138451866418739337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 939270071743287566609797 176113138451866418739337)
                  ·
                    rfl

theorem cell21_771703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 6, 4].length) (baseStart_771703 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_771703 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_771703 prefixEnd_771703 := by exact prefixLift 771703
  have htrace : WordTrace (prefixWord ++ tailWord_771703) baseStart_771703 baseEnd_771703 := by
    simpa [prefixWord, tailWord_771703, baseEnd_771703] using wordTrace_append hprefix tailTrace_771703
  have hstable : (prefixWord ++ tailWord_771703).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771703).length < 2 ^ (prefixWord ++ tailWord_771703).sum := by decide
  have hdescent : baseEnd_771703 < baseStart_771703 := by decide
  rcases family_descends (prefixWord ++ tailWord_771703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771889 : List Nat := [1, 2, 2, 3, 2, 4, 2, 1, 4]
def baseStart_771889 : Nat := 118140960795 + 771889 * 2 ^ 59
def prefixEnd_771889 : Nat := 4983230072969 + 3 ^ 40 * 771889 * 2
def baseEnd_771889 : Nat := 176155586185971428638957

theorem tailTrace_771889 : CollatzResearch.WordTrace tailWord_771889 prefixEnd_771889 176155586185971428638957 := by
  unfold tailWord_771889
  simp only [CollatzResearch.WordTrace]
  refine ⟨28153104700585455990934721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18768736467056970660623147 28153104700585455990934721)
  ·
    refine ⟨21114828525439091993201041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28153104700585455990934721 21114828525439091993201041)
    ·
      refine ⟨15836121394079318994900781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21114828525439091993201041 15836121394079318994900781)
      ·
        refine ⟨5938545522779744623087793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15836121394079318994900781 5938545522779744623087793)
        ·
          refine ⟨4453909142084808467315845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5938545522779744623087793 4453909142084808467315845)
          ·
            refine ⟨835107964140901587621721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4453909142084808467315845 835107964140901587621721)
            ·
              refine ⟨626330973105676190716291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 835107964140901587621721 626330973105676190716291)
              ·
                refine ⟨939496459658514286074437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 626330973105676190716291 939496459658514286074437)
                ·
                  refine ⟨176155586185971428638957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 939496459658514286074437 176155586185971428638957)
                  ·
                    rfl

theorem cell21_771889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 2, 1, 4].length) (baseStart_771889 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_771889 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_771889 prefixEnd_771889 := by exact prefixLift 771889
  have htrace : WordTrace (prefixWord ++ tailWord_771889) baseStart_771889 baseEnd_771889 := by
    simpa [prefixWord, tailWord_771889, baseEnd_771889] using wordTrace_append hprefix tailTrace_771889
  have hstable : (prefixWord ++ tailWord_771889).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771889).length < 2 ^ (prefixWord ++ tailWord_771889).sum := by decide
  have hdescent : baseEnd_771889 < baseStart_771889 := by decide
  rcases family_descends (prefixWord ++ tailWord_771889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771900 : List Nat := [2, 2, 2, 2, 1, 1, 2, 4, 5]
def baseStart_771900 : Nat := 118140960795 + 771900 * 2 ^ 59
def prefixEnd_771900 : Nat := 4983230072969 + 3 ^ 40 * 771900 * 2
def baseEnd_771900 : Nat := 176158096535837853955601

theorem tailTrace_771900 : CollatzResearch.WordTrace tailWord_771900 prefixEnd_771900 176158096535837853955601 := by
  unfold tailWord_771900
  simp only [CollatzResearch.WordTrace]
  refine ⟨14076752951772802434792577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18769003935697069913056769 14076752951772802434792577)
  ·
    refine ⟨10557564713829601826094433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14076752951772802434792577 10557564713829601826094433)
    ·
      refine ⟨7918173535372201369570825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10557564713829601826094433 7918173535372201369570825)
      ·
        refine ⟨5938630151529151027178119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7918173535372201369570825 5938630151529151027178119)
        ·
          refine ⟨8907945227293726540767179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5938630151529151027178119 8907945227293726540767179)
          ·
            refine ⟨13361917840940589811150769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8907945227293726540767179 13361917840940589811150769)
            ·
              refine ⟨10021438380705442358363077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13361917840940589811150769 10021438380705442358363077)
              ·
                refine ⟨1879019696382270442193077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10021438380705442358363077 1879019696382270442193077)
                ·
                  refine ⟨176158096535837853955601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1879019696382270442193077 176158096535837853955601)
                  ·
                    rfl

theorem cell21_771900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 4, 5].length) (baseStart_771900 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_771900 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_771900 prefixEnd_771900 := by exact prefixLift 771900
  have htrace : WordTrace (prefixWord ++ tailWord_771900) baseStart_771900 baseEnd_771900 := by
    simpa [prefixWord, tailWord_771900, baseEnd_771900] using wordTrace_append hprefix tailTrace_771900
  have hstable : (prefixWord ++ tailWord_771900).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771900).length < 2 ^ (prefixWord ++ tailWord_771900).sum := by decide
  have hdescent : baseEnd_771900 < baseStart_771900 := by decide
  rcases family_descends (prefixWord ++ tailWord_771900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771982 : List Nat := [4, 1, 1, 5, 1, 2, 1, 2, 4]
def baseStart_771982 : Nat := 118140960795 + 771982 * 2 ^ 59
def prefixEnd_771982 : Nat := 4983230072969 + 3 ^ 40 * 771982 * 2
def baseEnd_771982 : Nat := 176176810053023933588767

theorem tailTrace_771982 : CollatzResearch.WordTrace tailWord_771982 prefixEnd_771982 176176810053023933588767 := by
  unfold tailWord_771982
  simp only [CollatzResearch.WordTrace]
  refine ⟨3519562086156066609258775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18770997792832355249380133 3519562086156066609258775)
  ·
    refine ⟨5279343129234099913888163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3519562086156066609258775 5279343129234099913888163)
    ·
      refine ⟨7919014693851149870832245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5279343129234099913888163 7919014693851149870832245)
      ·
        refine ⟨742407627548545300390523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7919014693851149870832245 742407627548545300390523)
        ·
          refine ⟨1113611441322817950585785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 742407627548545300390523 1113611441322817950585785)
          ·
            refine ⟨835208580992113462939339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1113611441322817950585785 835208580992113462939339)
            ·
              refine ⟨1252812871488170194409009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 835208580992113462939339 1252812871488170194409009)
              ·
                refine ⟨939609653616127645806757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1252812871488170194409009 939609653616127645806757)
                ·
                  refine ⟨176176810053023933588767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 939609653616127645806757 176176810053023933588767)
                  ·
                    rfl

theorem cell21_771982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 1, 2, 4].length) (baseStart_771982 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_771982 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_771982 prefixEnd_771982 := by exact prefixLift 771982
  have htrace : WordTrace (prefixWord ++ tailWord_771982) baseStart_771982 baseEnd_771982 := by
    simpa [prefixWord, tailWord_771982, baseEnd_771982] using wordTrace_append hprefix tailTrace_771982
  have hstable : (prefixWord ++ tailWord_771982).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771982).length < 2 ^ (prefixWord ++ tailWord_771982).sum := by decide
  have hdescent : baseEnd_771982 < baseStart_771982 := by decide
  rcases family_descends (prefixWord ++ tailWord_771982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771993 : List Nat := [1, 2, 1, 2, 1, 3, 4, 4, 3]
def baseStart_771993 : Nat := 118140960795 + 771993 * 2 ^ 59
def prefixEnd_771993 : Nat := 4983230072969 + 3 ^ 40 * 771993 * 2
def baseEnd_771993 : Nat := 176179320402890358905411

theorem tailTrace_771993 : CollatzResearch.WordTrace tailWord_771993 prefixEnd_771993 176179320402890358905411 := by
  unfold tailWord_771993
  simp only [CollatzResearch.WordTrace]
  refine ⟨28156897892208681752720633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18771265261472454501813755 28156897892208681752720633)
  ·
    refine ⟨21117673419156511314540475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28156897892208681752720633 21117673419156511314540475)
    ·
      refine ⟨31676510128734766971810713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21117673419156511314540475 31676510128734766971810713)
      ·
        refine ⟨23757382596551075228858035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31676510128734766971810713 23757382596551075228858035)
        ·
          refine ⟨35636073894826612843287053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23757382596551075228858035 35636073894826612843287053)
          ·
            refine ⟨13363527710559979816232645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35636073894826612843287053 13363527710559979816232645)
            ·
              refine ⟨2505661445729996215543621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13363527710559979816232645 2505661445729996215543621)
              ·
                refine ⟨469811521074374290414429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2505661445729996215543621 469811521074374290414429)
                ·
                  refine ⟨176179320402890358905411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 469811521074374290414429 176179320402890358905411)
                  ·
                    rfl

theorem cell21_771993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 4, 3].length) (baseStart_771993 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_771993 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_771993 prefixEnd_771993 := by exact prefixLift 771993
  have htrace : WordTrace (prefixWord ++ tailWord_771993) baseStart_771993 baseEnd_771993 := by
    simpa [prefixWord, tailWord_771993, baseEnd_771993] using wordTrace_append hprefix tailTrace_771993
  have hstable : (prefixWord ++ tailWord_771993).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771993).length < 2 ^ (prefixWord ++ tailWord_771993).sum := by decide
  have hdescent : baseEnd_771993 < baseStart_771993 := by decide
  rcases family_descends (prefixWord ++ tailWord_771993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772058 : List Nat := [3, 1, 1, 2, 6, 1, 2, 1, 4]
def baseStart_772058 : Nat := 118140960795 + 772058 * 2 ^ 59
def prefixEnd_772058 : Nat := 4983230072969 + 3 ^ 40 * 772058 * 2
def baseEnd_772058 : Nat := 176194154288464690321945

theorem tailTrace_772058 : CollatzResearch.WordTrace tailWord_772058 prefixEnd_772058 176194154288464690321945 := by
  unfold tailWord_772058
  simp only [CollatzResearch.WordTrace]
  refine ⟨7039817159243299463459207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18772845757982131902557885 7039817159243299463459207)
  ·
    refine ⟨10559725738864949195188811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7039817159243299463459207 10559725738864949195188811)
    ·
      refine ⟨15839588608297423792783217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10559725738864949195188811 15839588608297423792783217)
      ·
        refine ⟨11879691456223067844587413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15839588608297423792783217 11879691456223067844587413)
        ·
          refine ⟨556860537010456305215035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 11879691456223067844587413 556860537010456305215035)
          ·
            refine ⟨835290805515684457822553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 556860537010456305215035 835290805515684457822553)
            ·
              refine ⟨626468104136763343366915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 835290805515684457822553 626468104136763343366915)
              ·
                refine ⟨939702156205145015050373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 626468104136763343366915 939702156205145015050373)
                ·
                  refine ⟨176194154288464690321945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 939702156205145015050373 176194154288464690321945)
                  ·
                    rfl

theorem cell21_772058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 2, 1, 4].length) (baseStart_772058 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_772058 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_772058 prefixEnd_772058 := by exact prefixLift 772058
  have htrace : WordTrace (prefixWord ++ tailWord_772058) baseStart_772058 baseEnd_772058 := by
    simpa [prefixWord, tailWord_772058, baseEnd_772058] using wordTrace_append hprefix tailTrace_772058
  have hstable : (prefixWord ++ tailWord_772058).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772058).length < 2 ^ (prefixWord ++ tailWord_772058).sum := by decide
  have hdescent : baseEnd_772058 < baseStart_772058 := by decide
  rcases family_descends (prefixWord ++ tailWord_772058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772103 : List Nat := [1, 1, 4, 3, 1, 4, 2, 2, 3]
def baseStart_772103 : Nat := 118140960795 + 772103 * 2 ^ 59
def prefixEnd_772103 : Nat := 4983230072969 + 3 ^ 40 * 772103 * 2
def baseEnd_772103 : Nat := 176204423901554612071853

theorem tailTrace_772103 : CollatzResearch.WordTrace tailWord_772103 prefixEnd_772103 176204423901554612071853 := by
  unfold tailWord_772103
  simp only [CollatzResearch.WordTrace]
  refine ⟨28160909921810170539224963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18773939947873447026149975 28160909921810170539224963)
  ·
    refine ⟨42241364882715255808837445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28160909921810170539224963 42241364882715255808837445)
    ·
      refine ⟨7920255915509110464157021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42241364882715255808837445 7920255915509110464157021)
      ·
        refine ⟨2970095968315916424058883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7920255915509110464157021 2970095968315916424058883)
        ·
          refine ⟨4455143952473874636088325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2970095968315916424058883 4455143952473874636088325)
          ·
            refine ⟨835339491088851494266561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4455143952473874636088325 835339491088851494266561)
            ·
              refine ⟨626504618316638620699921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 835339491088851494266561 626504618316638620699921)
              ·
                refine ⟨469878463737478965524941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 626504618316638620699921 469878463737478965524941)
                ·
                  refine ⟨176204423901554612071853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 469878463737478965524941 176204423901554612071853)
                  ·
                    rfl

theorem cell21_772103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 2, 2, 3].length) (baseStart_772103 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_772103 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_772103 prefixEnd_772103 := by exact prefixLift 772103
  have htrace : WordTrace (prefixWord ++ tailWord_772103) baseStart_772103 baseEnd_772103 := by
    simpa [prefixWord, tailWord_772103, baseEnd_772103] using wordTrace_append hprefix tailTrace_772103
  have hstable : (prefixWord ++ tailWord_772103).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772103).length < 2 ^ (prefixWord ++ tailWord_772103).sum := by decide
  have hdescent : baseEnd_772103 < baseStart_772103 := by decide
  rcases family_descends (prefixWord ++ tailWord_772103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772145 : List Nat := [1, 2, 2, 3, 1, 3, 1, 5, 3]
def baseStart_772145 : Nat := 118140960795 + 772145 * 2 ^ 59
def prefixEnd_772145 : Nat := 4983230072969 + 3 ^ 40 * 772145 * 2
def baseEnd_772145 : Nat := 176214008873771872371767

theorem tailTrace_772145 : CollatzResearch.WordTrace tailWord_772145 prefixEnd_772145 176214008873771872371767 := by
  unfold tailWord_772145
  simp only [CollatzResearch.WordTrace]
  refine ⟨28162441787658011712253889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18774961191772007808169259 28162441787658011712253889)
  ·
    refine ⟨21121831340743508784190417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28162441787658011712253889 21121831340743508784190417)
    ·
      refine ⟨15841373505557631588142813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21121831340743508784190417 15841373505557631588142813)
      ·
        refine ⟨5940515064584111845553555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15841373505557631588142813 5940515064584111845553555)
        ·
          refine ⟨8910772596876167768330333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5940515064584111845553555 8910772596876167768330333)
          ·
            refine ⟨3341539723828562913123875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8910772596876167768330333 3341539723828562913123875)
            ·
              refine ⟨5012309585742844369685813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3341539723828562913123875 5012309585742844369685813)
              ·
                refine ⟨469904023663391659658045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5012309585742844369685813 469904023663391659658045)
                ·
                  refine ⟨176214008873771872371767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 469904023663391659658045 176214008873771872371767)
                  ·
                    rfl

theorem cell21_772145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 5, 3].length) (baseStart_772145 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_772145 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_772145 prefixEnd_772145 := by exact prefixLift 772145
  have htrace : WordTrace (prefixWord ++ tailWord_772145) baseStart_772145 baseEnd_772145 := by
    simpa [prefixWord, tailWord_772145, baseEnd_772145] using wordTrace_append hprefix tailTrace_772145
  have hstable : (prefixWord ++ tailWord_772145).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772145).length < 2 ^ (prefixWord ++ tailWord_772145).sum := by decide
  have hdescent : baseEnd_772145 < baseStart_772145 := by decide
  rcases family_descends (prefixWord ++ tailWord_772145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772159 : List Nat := [1, 1, 2, 2, 3, 1, 5, 2, 4]
def baseStart_772159 : Nat := 118140960795 + 772159 * 2 ^ 59
def prefixEnd_772159 : Nat := 4983230072969 + 3 ^ 40 * 772159 * 2
def baseEnd_772159 : Nat := 176217203864510959138405

theorem tailTrace_772159 : CollatzResearch.WordTrace tailWord_772159 prefixEnd_772159 176217203864510959138405 := by
  unfold tailWord_772159
  simp only [CollatzResearch.WordTrace]
  refine ⟨28162952409607292103263531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18775301606404861402175687 28162952409607292103263531)
  ·
    refine ⟨42244428614410938154895297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28162952409607292103263531 42244428614410938154895297)
    ·
      refine ⟨31683321460808203616171473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42244428614410938154895297 31683321460808203616171473)
      ·
        refine ⟨23762491095606152712128605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31683321460808203616171473 23762491095606152712128605)
        ·
          refine ⟨8910934160852307267048227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23762491095606152712128605 8910934160852307267048227)
          ·
            refine ⟨13366401241278460900572341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8910934160852307267048227 13366401241278460900572341)
            ·
              refine ⟨1253100116369855709428657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13366401241278460900572341 1253100116369855709428657)
              ·
                refine ⟨939825087277391782071493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1253100116369855709428657 939825087277391782071493)
                ·
                  refine ⟨176217203864510959138405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 939825087277391782071493 176217203864510959138405)
                  ·
                    rfl

theorem cell21_772159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5, 2, 4].length) (baseStart_772159 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_772159 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_772159 prefixEnd_772159 := by exact prefixLift 772159
  have htrace : WordTrace (prefixWord ++ tailWord_772159) baseStart_772159 baseEnd_772159 := by
    simpa [prefixWord, tailWord_772159, baseEnd_772159] using wordTrace_append hprefix tailTrace_772159
  have hstable : (prefixWord ++ tailWord_772159).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772159).length < 2 ^ (prefixWord ++ tailWord_772159).sum := by decide
  have hdescent : baseEnd_772159 < baseStart_772159 := by decide
  rcases family_descends (prefixWord ++ tailWord_772159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772221 : List Nat := [1, 4, 1, 1, 3, 4, 1, 1, 5]
def baseStart_772221 : Nat := 118140960795 + 772221 * 2 ^ 59
def prefixEnd_772221 : Nat := 4983230072969 + 3 ^ 40 * 772221 * 2
def baseEnd_772221 : Nat := 176231353109212629104945

theorem tailTrace_772221 : CollatzResearch.WordTrace tailWord_772221 prefixEnd_772221 176231353109212629104945 := by
  unfold tailWord_772221
  simp only [CollatzResearch.WordTrace]
  refine ⟨28165213735382676692020517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18776809156921784461347011 28165213735382676692020517)
  ·
    refine ⟨5280977575384251879753847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28165213735382676692020517 5280977575384251879753847)
    ·
      refine ⟨7921466363076377819630771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5280977575384251879753847 7921466363076377819630771)
      ·
        refine ⟨11882199544614566729446157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7921466363076377819630771 11882199544614566729446157)
        ·
          refine ⟨4455824829230462523542309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11882199544614566729446157 4455824829230462523542309)
          ·
            refine ⟨835467155480711723164183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4455824829230462523542309 835467155480711723164183)
            ·
              refine ⟨1253200733221067584746275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 835467155480711723164183 1253200733221067584746275)
              ·
                refine ⟨1879801099831601377119413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1253200733221067584746275 1879801099831601377119413)
                ·
                  refine ⟨176231353109212629104945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1879801099831601377119413 176231353109212629104945)
                  ·
                    rfl

theorem cell21_772221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 1, 1, 5].length) (baseStart_772221 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_772221 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_772221 prefixEnd_772221 := by exact prefixLift 772221
  have htrace : WordTrace (prefixWord ++ tailWord_772221) baseStart_772221 baseEnd_772221 := by
    simpa [prefixWord, tailWord_772221, baseEnd_772221] using wordTrace_append hprefix tailTrace_772221
  have hstable : (prefixWord ++ tailWord_772221).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772221).length < 2 ^ (prefixWord ++ tailWord_772221).sum := by decide
  have hdescent : baseEnd_772221 < baseStart_772221 := by decide
  rcases family_descends (prefixWord ++ tailWord_772221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772266 : List Nat := [3, 1, 5, 1, 2, 9]
def baseStart_772266 : Nat := 118140960795 + 772266 * 2 ^ 59
def prefixEnd_772266 : Nat := 4983230072969 + 3 ^ 40 * 772266 * 2
def baseEnd_772266 : Nat := 6527467508233427809439

theorem tailTrace_772266 : CollatzResearch.WordTrace tailWord_772266 prefixEnd_772266 6527467508233427809439 := by
  unfold tailWord_772266
  simp only [CollatzResearch.WordTrace]
  refine ⟨7041713755054912344352163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18777903346813099584939101 7041713755054912344352163)
  ·
    refine ⟨10562570632582368516528245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7041713755054912344352163 10562570632582368516528245)
    ·
      refine ⟨990240996804597048424523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10562570632582368516528245 990240996804597048424523)
      ·
        refine ⟨1485361495206895572636785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 990240996804597048424523 1485361495206895572636785)
        ·
          refine ⟨1114021121405171679477589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1485361495206895572636785 1114021121405171679477589)
          ·
            refine ⟨6527467508233427809439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1114021121405171679477589 6527467508233427809439)
            ·
              rfl

theorem cell21_772266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 9].length) (baseStart_772266 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_772266 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_772266 prefixEnd_772266 := by exact prefixLift 772266
  have htrace : WordTrace (prefixWord ++ tailWord_772266) baseStart_772266 baseEnd_772266 := by
    simpa [prefixWord, tailWord_772266, baseEnd_772266] using wordTrace_append hprefix tailTrace_772266
  have hstable : (prefixWord ++ tailWord_772266).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772266).length < 2 ^ (prefixWord ++ tailWord_772266).sum := by decide
  have hdescent : baseEnd_772266 < baseStart_772266 := by decide
  rcases family_descends (prefixWord ++ tailWord_772266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772325 : List Nat := [1, 3, 1, 4, 2, 2, 8]
def baseStart_772325 : Nat := 118140960795 + 772325 * 2 ^ 59
def prefixEnd_772325 : Nat := 4983230072969 + 3 ^ 40 * 772325 * 2
def baseEnd_772325 : Nat := 19583898591792395485711

theorem tailTrace_772325 : CollatzResearch.WordTrace tailWord_772325 prefixEnd_772325 19583898591792395485711 := by
  unfold tailWord_772325
  simp only [CollatzResearch.WordTrace]
  refine ⟨28169006927005902453806429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18779337951337268302537619 28169006927005902453806429)
  ·
    refine ⟨10563377597627213420177411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28169006927005902453806429 10563377597627213420177411)
    ·
      refine ⟨15845066396440820130266117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10563377597627213420177411 15845066396440820130266117)
      ·
        refine ⟨2970949949332653774424897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15845066396440820130266117 2970949949332653774424897)
        ·
          refine ⟨2228212461999490330818673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2970949949332653774424897 2228212461999490330818673)
          ·
            refine ⟨1671159346499617748114005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2228212461999490330818673 1671159346499617748114005)
            ·
              refine ⟨19583898591792395485711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1671159346499617748114005 19583898591792395485711)
              ·
                rfl

theorem cell21_772325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 8].length) (baseStart_772325 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_772325 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_772325 prefixEnd_772325 := by exact prefixLift 772325
  have htrace : WordTrace (prefixWord ++ tailWord_772325) baseStart_772325 baseEnd_772325 := by
    simpa [prefixWord, tailWord_772325, baseEnd_772325] using wordTrace_append hprefix tailTrace_772325
  have hstable : (prefixWord ++ tailWord_772325).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772325).length < 2 ^ (prefixWord ++ tailWord_772325).sum := by decide
  have hdescent : baseEnd_772325 < baseStart_772325 := by decide
  rcases family_descends (prefixWord ++ tailWord_772325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772328 : List Nat := [2, 1, 4, 1, 2, 4, 1, 2, 4]
def baseStart_772328 : Nat := 118140960795 + 772328 * 2 ^ 59
def prefixEnd_772328 : Nat := 4983230072969 + 3 ^ 40 * 772328 * 2
def baseEnd_772328 : Nat := 176255771967004220821393

theorem tailTrace_772328 : CollatzResearch.WordTrace tailWord_772328 prefixEnd_772328 176255771967004220821393 := by
  unfold tailWord_772328
  simp only [CollatzResearch.WordTrace]
  refine ⟨14084558172997516983082819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18779410897330022644110425 14084558172997516983082819)
  ·
    refine ⟨21126837259496275474624229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14084558172997516983082819 21126837259496275474624229)
    ·
      refine ⟨3961281986155551651492043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21126837259496275474624229 3961281986155551651492043)
      ·
        refine ⟨5941922979233327477238065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3961281986155551651492043 5941922979233327477238065)
        ·
          refine ⟨4456442234424995607928549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5941922979233327477238065 4456442234424995607928549)
          ·
            refine ⟨835582918954686676486603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4456442234424995607928549 835582918954686676486603)
            ·
              refine ⟨1253374378432030014729905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 835582918954686676486603 1253374378432030014729905)
              ·
                refine ⟨940030783824022511047429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1253374378432030014729905 940030783824022511047429)
                ·
                  refine ⟨176255771967004220821393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 940030783824022511047429 176255771967004220821393)
                  ·
                    rfl

theorem cell21_772328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 1, 2, 4].length) (baseStart_772328 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_772328 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_772328 prefixEnd_772328 := by exact prefixLift 772328
  have htrace : WordTrace (prefixWord ++ tailWord_772328) baseStart_772328 baseEnd_772328 := by
    simpa [prefixWord, tailWord_772328, baseEnd_772328] using wordTrace_append hprefix tailTrace_772328
  have hstable : (prefixWord ++ tailWord_772328).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772328).length < 2 ^ (prefixWord ++ tailWord_772328).sum := by decide
  have hdescent : baseEnd_772328 < baseStart_772328 := by decide
  rcases family_descends (prefixWord ++ tailWord_772328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772373 : List Nat := [1, 3, 2, 1, 2, 1, 5, 3, 3]
def baseStart_772373 : Nat := 118140960795 + 772373 * 2 ^ 59
def prefixEnd_772373 : Nat := 4983230072969 + 3 ^ 40 * 772373 * 2
def baseEnd_772373 : Nat := 176266041580094142571301

theorem tailTrace_772373 : CollatzResearch.WordTrace tailWord_772373 prefixEnd_772373 176266041580094142571301 := by
  unfold tailWord_772373
  simp only [CollatzResearch.WordTrace]
  refine ⟨28170757630832006651553773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18780505087221337767702515 28170757630832006651553773)
  ·
    refine ⟨10564034111562002494332665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28170757630832006651553773 10564034111562002494332665)
    ·
      refine ⟨7923025583671501870749499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10564034111562002494332665 7923025583671501870749499)
      ·
        refine ⟨11884538375507252806124249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7923025583671501870749499 11884538375507252806124249)
        ·
          refine ⟨8913403781630439604593187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11884538375507252806124249 8913403781630439604593187)
          ·
            refine ⟨13370105672445659406889781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8913403781630439604593187 13370105672445659406889781)
            ·
              refine ⟨1253447406791780569395917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13370105672445659406889781 1253447406791780569395917)
              ·
                refine ⟨470042777546917713523469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1253447406791780569395917 470042777546917713523469)
                ·
                  refine ⟨176266041580094142571301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 470042777546917713523469 176266041580094142571301)
                  ·
                    rfl

theorem cell21_772373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5, 3, 3].length) (baseStart_772373 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_772373 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_772373 prefixEnd_772373 := by exact prefixLift 772373
  have htrace : WordTrace (prefixWord ++ tailWord_772373) baseStart_772373 baseEnd_772373 := by
    simpa [prefixWord, tailWord_772373, baseEnd_772373] using wordTrace_append hprefix tailTrace_772373
  have hstable : (prefixWord ++ tailWord_772373).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772373).length < 2 ^ (prefixWord ++ tailWord_772373).sum := by decide
  have hdescent : baseEnd_772373 < baseStart_772373 := by decide
  rcases family_descends (prefixWord ++ tailWord_772373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772404 : List Nat := [2, 5, 1, 1, 1, 3, 1, 3, 4]
def baseStart_772404 : Nat := 118140960795 + 772404 * 2 ^ 59
def prefixEnd_772404 : Nat := 4983230072969 + 3 ^ 40 * 772404 * 2
def baseEnd_772404 : Nat := 176273116202444977554571

theorem tailTrace_772404 : CollatzResearch.WordTrace tailWord_772404 prefixEnd_772404 176273116202444977554571 := by
  unfold tailWord_772404
  simp only [CollatzResearch.WordTrace]
  refine ⟨14085944146859849472966133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18781258862479799297288177 14085944146859849472966133)
  ·
    refine ⟨1320557263768110888090575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14085944146859849472966133 1320557263768110888090575)
    ·
      refine ⟨1980835895652166332135863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1320557263768110888090575 1980835895652166332135863)
      ·
        refine ⟨2971253843478249498203795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1980835895652166332135863 2971253843478249498203795)
        ·
          refine ⟨4456880765217374247305693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2971253843478249498203795 4456880765217374247305693)
          ·
            refine ⟨1671330286956515342739635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4456880765217374247305693 1671330286956515342739635)
            ·
              refine ⟨2506995430434773014109453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1671330286956515342739635 2506995430434773014109453)
              ·
                refine ⟨940123286413039880291045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2506995430434773014109453 940123286413039880291045)
                ·
                  refine ⟨176273116202444977554571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 940123286413039880291045 176273116202444977554571)
                  ·
                    rfl

theorem cell21_772404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_772404 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_772404 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_772404 prefixEnd_772404 := by exact prefixLift 772404
  have htrace : WordTrace (prefixWord ++ tailWord_772404) baseStart_772404 baseEnd_772404 := by
    simpa [prefixWord, tailWord_772404, baseEnd_772404] using wordTrace_append hprefix tailTrace_772404
  have hstable : (prefixWord ++ tailWord_772404).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772404).length < 2 ^ (prefixWord ++ tailWord_772404).sum := by decide
  have hdescent : baseEnd_772404 < baseStart_772404 := by decide
  rcases family_descends (prefixWord ++ tailWord_772404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772415 : List Nat := [1, 1, 2, 2, 4, 1, 2, 1, 7]
def baseStart_772415 : Nat := 118140960795 + 772415 * 2 ^ 59
def prefixEnd_772415 : Nat := 4983230072969 + 3 ^ 40 * 772415 * 2
def baseEnd_772415 : Nat := 176275626552311402871215

theorem tailTrace_772415 : CollatzResearch.WordTrace tailWord_772415 prefixEnd_772415 176275626552311402871215 := by
  unfold tailWord_772415
  simp only [CollatzResearch.WordTrace]
  refine ⟨28172289496679847824582699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18781526331119898549721799 28172289496679847824582699)
  ·
    refine ⟨42258434245019771736874049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28172289496679847824582699 42258434245019771736874049)
    ·
      refine ⟨31693825683764828802655537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42258434245019771736874049 31693825683764828802655537)
      ·
        refine ⟨23770369262823621601991653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31693825683764828802655537 23770369262823621601991653)
        ·
          refine ⟨4456944236779429050373435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23770369262823621601991653 4456944236779429050373435)
          ·
            refine ⟨6685416355169143575560153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4456944236779429050373435 6685416355169143575560153)
            ·
              refine ⟨5014062266376857681670115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6685416355169143575560153 5014062266376857681670115)
              ·
                refine ⟨7521093399565286522505173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5014062266376857681670115 7521093399565286522505173)
                ·
                  refine ⟨176275626552311402871215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7521093399565286522505173 176275626552311402871215)
                  ·
                    rfl

theorem cell21_772415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 1, 7].length) (baseStart_772415 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_772415 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_772415 prefixEnd_772415 := by exact prefixLift 772415
  have htrace : WordTrace (prefixWord ++ tailWord_772415) baseStart_772415 baseEnd_772415 := by
    simpa [prefixWord, tailWord_772415, baseEnd_772415] using wordTrace_append hprefix tailTrace_772415
  have hstable : (prefixWord ++ tailWord_772415).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772415).length < 2 ^ (prefixWord ++ tailWord_772415).sum := by decide
  have hdescent : baseEnd_772415 < baseStart_772415 := by decide
  rcases family_descends (prefixWord ++ tailWord_772415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772643 : List Nat := [1, 1, 1, 4, 4, 1, 1, 1, 7]
def baseStart_772643 : Nat := 118140960795 + 772643 * 2 ^ 59
def prefixEnd_772643 : Nat := 4983230072969 + 3 ^ 40 * 772643 * 2
def baseEnd_772643 : Nat := 176327659258633673070749

theorem tailTrace_772643 : CollatzResearch.WordTrace tailWord_772643 prefixEnd_772643 176327659258633673070749 := by
  unfold tailWord_772643
  simp only [CollatzResearch.WordTrace]
  refine ⟨28180605339853842763882583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18787070226569228509255055 28180605339853842763882583)
  ·
    refine ⟨42270908009780764145823875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28180605339853842763882583 42270908009780764145823875)
    ·
      refine ⟨63406362014671146218735813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42270908009780764145823875 63406362014671146218735813)
      ·
        refine ⟨11888692877750839916012965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63406362014671146218735813 11888692877750839916012965)
        ·
          refine ⟨2229129914578282484252431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11888692877750839916012965 2229129914578282484252431)
          ·
            refine ⟨3343694871867423726378647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2229129914578282484252431 3343694871867423726378647)
            ·
              refine ⟨5015542307801135589567971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3343694871867423726378647 5015542307801135589567971)
              ·
                refine ⟨7523313461701703384351957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5015542307801135589567971 7523313461701703384351957)
                ·
                  refine ⟨176327659258633673070749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7523313461701703384351957 176327659258633673070749)
                  ·
                    rfl

theorem cell21_772643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 1, 7].length) (baseStart_772643 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_772643 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_772643 prefixEnd_772643 := by exact prefixLift 772643
  have htrace : WordTrace (prefixWord ++ tailWord_772643) baseStart_772643 baseEnd_772643 := by
    simpa [prefixWord, tailWord_772643, baseEnd_772643] using wordTrace_append hprefix tailTrace_772643
  have hstable : (prefixWord ++ tailWord_772643).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772643).length < 2 ^ (prefixWord ++ tailWord_772643).sum := by decide
  have hdescent : baseEnd_772643 < baseStart_772643 := by decide
  rcases family_descends (prefixWord ++ tailWord_772643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772705 : List Nat := [1, 2, 3, 1, 1, 4, 4, 5]
def baseStart_772705 : Nat := 118140960795 + 772705 * 2 ^ 59
def prefixEnd_772705 : Nat := 4983230072969 + 3 ^ 40 * 772705 * 2
def baseEnd_772705 : Nat := 58780602834445114345763

theorem tailTrace_772705 : CollatzResearch.WordTrace tailWord_772705 prefixEnd_772705 58780602834445114345763 := by
  unfold tailWord_772705
  simp only [CollatzResearch.WordTrace]
  refine ⟨28182866665629227352639569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18788577777086151568426379 28182866665629227352639569)
  ·
    refine ⟨21137149999221920514479677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28182866665629227352639569 21137149999221920514479677)
    ·
      refine ⟨7926431249708220192929879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21137149999221920514479677 7926431249708220192929879)
      ·
        refine ⟨11889646874562330289394819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7926431249708220192929879 11889646874562330289394819)
        ·
          refine ⟨17834470311843495434092229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11889646874562330289394819 17834470311843495434092229)
          ·
            refine ⟨3343963183470655393892293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17834470311843495434092229 3343963183470655393892293)
            ·
              refine ⟨626993096900747886354805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3343963183470655393892293 626993096900747886354805)
              ·
                refine ⟨58780602834445114345763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 626993096900747886354805 58780602834445114345763)
                ·
                  rfl

theorem cell21_772705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 4, 5].length) (baseStart_772705 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_772705 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_772705 prefixEnd_772705 := by exact prefixLift 772705
  have htrace : WordTrace (prefixWord ++ tailWord_772705) baseStart_772705 baseEnd_772705 := by
    simpa [prefixWord, tailWord_772705, baseEnd_772705] using wordTrace_append hprefix tailTrace_772705
  have hstable : (prefixWord ++ tailWord_772705).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772705).length < 2 ^ (prefixWord ++ tailWord_772705).sum := by decide
  have hdescent : baseEnd_772705 < baseStart_772705 := by decide
  rcases family_descends (prefixWord ++ tailWord_772705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772722 : List Nat := [3, 2, 1, 2, 5, 1, 7]
def baseStart_772722 : Nat := 118140960795 + 772722 * 2 ^ 59
def prefixEnd_772722 : Nat := 4983230072969 + 3 ^ 40 * 772722 * 2
def baseEnd_772722 : Nat := 19593965348327454583769

theorem tailTrace_772722 : CollatzResearch.WordTrace tailWord_772722 prefixEnd_772722 19593965348327454583769 := by
  unfold tailWord_772722
  simp only [CollatzResearch.WordTrace]
  refine ⟨7045871676641909814002105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18788991137711759504005613 7045871676641909814002105)
  ·
    refine ⟨5284403757481432360501579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7045871676641909814002105 5284403757481432360501579)
    ·
      refine ⟨7926605636222148540752369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5284403757481432360501579 7926605636222148540752369)
      ·
        refine ⟨5944954227166611405564277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7926605636222148540752369 5944954227166611405564277)
        ·
          refine ⟨557339458796869819271651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5944954227166611405564277 557339458796869819271651)
          ·
            refine ⟨836009188195304728907477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 557339458796869819271651 836009188195304728907477)
            ·
              refine ⟨19593965348327454583769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 836009188195304728907477 19593965348327454583769)
              ·
                rfl

theorem cell21_772722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 7].length) (baseStart_772722 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_772722 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_772722 prefixEnd_772722 := by exact prefixLift 772722
  have htrace : WordTrace (prefixWord ++ tailWord_772722) baseStart_772722 baseEnd_772722 := by
    simpa [prefixWord, tailWord_772722, baseEnd_772722] using wordTrace_append hprefix tailTrace_772722
  have hstable : (prefixWord ++ tailWord_772722).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772722).length < 2 ^ (prefixWord ++ tailWord_772722).sum := by decide
  have hdescent : baseEnd_772722 < baseStart_772722 := by decide
  rcases family_descends (prefixWord ++ tailWord_772722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772736 : List Nat := [2, 1, 1, 2, 1, 7, 1, 1, 5]
def baseStart_772736 : Nat := 118140960795 + 772736 * 2 ^ 59
def prefixEnd_772736 : Nat := 4983230072969 + 3 ^ 40 * 772736 * 2
def baseEnd_772736 : Nat := 176348883125686178020559

theorem tailTrace_772736 : CollatzResearch.WordTrace tailWord_772736 prefixEnd_772736 176348883125686178020559 := by
  unfold tailWord_772736
  simp only [CollatzResearch.WordTrace]
  refine ⟨14091998664258459823509031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18789331552344613098012041 14091998664258459823509031)
  ·
    refine ⟨21137997996387689735263547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14091998664258459823509031 21137997996387689735263547)
    ·
      refine ⟨31706996994581534602895321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21137997996387689735263547 31706996994581534602895321)
      ·
        refine ⟨23780247745936150952171491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31706996994581534602895321 23780247745936150952171491)
        ·
          refine ⟨35670371618904226428257237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23780247745936150952171491 35670371618904226428257237)
          ·
            refine ⟨836024334818067806912279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 35670371618904226428257237 836024334818067806912279)
            ·
              refine ⟨1254036502227101710368419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 836024334818067806912279 1254036502227101710368419)
              ·
                refine ⟨1881054753340652565552629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1254036502227101710368419 1881054753340652565552629)
                ·
                  refine ⟨176348883125686178020559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1881054753340652565552629 176348883125686178020559)
                  ·
                    rfl

theorem cell21_772736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 1, 1, 5].length) (baseStart_772736 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_772736 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_772736 prefixEnd_772736 := by exact prefixLift 772736
  have htrace : WordTrace (prefixWord ++ tailWord_772736) baseStart_772736 baseEnd_772736 := by
    simpa [prefixWord, tailWord_772736, baseEnd_772736] using wordTrace_append hprefix tailTrace_772736
  have hstable : (prefixWord ++ tailWord_772736).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772736).length < 2 ^ (prefixWord ++ tailWord_772736).sum := by decide
  have hdescent : baseEnd_772736 < baseStart_772736 := by decide
  rcases family_descends (prefixWord ++ tailWord_772736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772812 : List Nat := [2, 2, 1, 5, 1, 2, 1, 2, 5]
def baseStart_772812 : Nat := 118140960795 + 772812 * 2 ^ 59
def prefixEnd_772812 : Nat := 4983230072969 + 3 ^ 40 * 772812 * 2
def baseEnd_772812 : Nat := 176366227361126934753737

theorem tailTrace_772812 : CollatzResearch.WordTrace tailWord_772812 prefixEnd_772812 176366227361126934753737 := by
  unfold tailWord_772812
  simp only [CollatzResearch.WordTrace]
  refine ⟨14093384638120792313392345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18791179517494389751189793 14093384638120792313392345)
  ·
    refine ⟨10570038478590594235044259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14093384638120792313392345 10570038478590594235044259)
    ·
      refine ⟨15855057717885891352566389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10570038478590594235044259 15855057717885891352566389)
      ·
        refine ⟨1486411661051802314303099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15855057717885891352566389 1486411661051802314303099)
        ·
          refine ⟨2229617491577703471454649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1486411661051802314303099 2229617491577703471454649)
          ·
            refine ⟨1672213118683277603590987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2229617491577703471454649 1672213118683277603590987)
            ·
              refine ⟨2508319678024916405386481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1672213118683277603590987 2508319678024916405386481)
              ·
                refine ⟨1881239758518687304039861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2508319678024916405386481 1881239758518687304039861)
                ·
                  refine ⟨176366227361126934753737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1881239758518687304039861 176366227361126934753737)
                  ·
                    rfl

theorem cell21_772812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 2, 5].length) (baseStart_772812 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_772812 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_772812 prefixEnd_772812 := by exact prefixLift 772812
  have htrace : WordTrace (prefixWord ++ tailWord_772812) baseStart_772812 baseEnd_772812 := by
    simpa [prefixWord, tailWord_772812, baseEnd_772812] using wordTrace_append hprefix tailTrace_772812
  have hstable : (prefixWord ++ tailWord_772812).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772812).length < 2 ^ (prefixWord ++ tailWord_772812).sum := by decide
  have hdescent : baseEnd_772812 < baseStart_772812 := by decide
  rcases family_descends (prefixWord ++ tailWord_772812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772885 : List Nat := [1, 3, 2, 1, 2, 2, 1, 1, 8]
def baseStart_772885 : Nat := 118140960795 + 772885 * 2 ^ 59
def prefixEnd_772885 : Nat := 4983230072969 + 3 ^ 40 * 772885 * 2
def baseEnd_772885 : Nat := 176382886955695030036921

theorem tailTrace_772885 : CollatzResearch.WordTrace tailWord_772885 prefixEnd_772885 176382886955695030036921 := by
  unfold tailWord_772885
  simp only [CollatzResearch.WordTrace]
  refine ⟨28189431804977118094192109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18792954536651412062794739 28189431804977118094192109)
  ·
    refine ⟨10571036926866419285322041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28189431804977118094192109 10571036926866419285322041)
    ·
      refine ⟨7928277695149814463991531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10571036926866419285322041 7928277695149814463991531)
      ·
        refine ⟨11892416542724721695987297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7928277695149814463991531 11892416542724721695987297)
        ·
          refine ⟨8919312407043541271990473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11892416542724721695987297 8919312407043541271990473)
          ·
            refine ⟨6689484305282655953992855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8919312407043541271990473 6689484305282655953992855)
            ·
              refine ⟨10034226457923983930989283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6689484305282655953992855 10034226457923983930989283)
              ·
                refine ⟨15051339686885975896483925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10034226457923983930989283 15051339686885975896483925)
                ·
                  refine ⟨176382886955695030036921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15051339686885975896483925 176382886955695030036921)
                  ·
                    rfl

theorem cell21_772885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 8].length) (baseStart_772885 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_772885 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_772885 prefixEnd_772885 := by exact prefixLift 772885
  have htrace : WordTrace (prefixWord ++ tailWord_772885) baseStart_772885 baseEnd_772885 := by
    simpa [prefixWord, tailWord_772885, baseEnd_772885] using wordTrace_append hprefix tailTrace_772885
  have hstable : (prefixWord ++ tailWord_772885).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772885).length < 2 ^ (prefixWord ++ tailWord_772885).sum := by decide
  have hdescent : baseEnd_772885 < baseStart_772885 := by decide
  rcases family_descends (prefixWord ++ tailWord_772885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772978 : List Nat := [3, 2, 1, 2, 1, 1, 4, 3, 4]
def baseStart_772978 : Nat := 118140960795 + 772978 * 2 ^ 59
def prefixEnd_772978 : Nat := 4983230072969 + 3 ^ 40 * 772978 * 2
def baseEnd_772978 : Nat := 176404110822747534986731

theorem tailTrace_772978 : CollatzResearch.WordTrace tailWord_772978 prefixEnd_772978 176404110822747534986731 := by
  unfold tailWord_772978
  simp only [CollatzResearch.WordTrace]
  refine ⟨7048205948410048744331897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18795215862426796651551725 7048205948410048744331897)
  ·
    refine ⟨5286154461307536558248923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7048205948410048744331897 5286154461307536558248923)
    ·
      refine ⟨7929231691961304837373385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5286154461307536558248923 7929231691961304837373385)
      ·
        refine ⟨5946923768970978628030039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7929231691961304837373385 5946923768970978628030039)
        ·
          refine ⟨8920385653456467942045059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5946923768970978628030039 8920385653456467942045059)
          ·
            refine ⟨13380578480184701913067589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8920385653456467942045059 13380578480184701913067589)
            ·
              refine ⟨2508858465034631608700173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13380578480184701913067589 2508858465034631608700173)
              ·
                refine ⟨940821924387986853262565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2508858465034631608700173 940821924387986853262565)
                ·
                  refine ⟨176404110822747534986731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 940821924387986853262565 176404110822747534986731)
                  ·
                    rfl

theorem cell21_772978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 3, 4].length) (baseStart_772978 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_772978 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_772978 prefixEnd_772978 := by exact prefixLift 772978
  have htrace : WordTrace (prefixWord ++ tailWord_772978) baseStart_772978 baseEnd_772978 := by
    simpa [prefixWord, tailWord_772978, baseEnd_772978] using wordTrace_append hprefix tailTrace_772978
  have hstable : (prefixWord ++ tailWord_772978).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772978).length < 2 ^ (prefixWord ++ tailWord_772978).sum := by decide
  have hdescent : baseEnd_772978 < baseStart_772978 := by decide
  rcases family_descends (prefixWord ++ tailWord_772978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773023 : List Nat := [1, 1, 2, 5, 2, 1, 1, 3, 5]
def baseStart_773023 : Nat := 118140960795 + 773023 * 2 ^ 59
def prefixEnd_773023 : Nat := 4983230072969 + 3 ^ 40 * 773023 * 2
def baseEnd_773023 : Nat := 176414380435837456736639

theorem tailTrace_773023 : CollatzResearch.WordTrace tailWord_773023 prefixEnd_773023 176414380435837456736639 := by
  unfold tailWord_773023
  simp only [CollatzResearch.WordTrace]
  refine ⟨28194465078477167662715723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18796310052318111775143815 28194465078477167662715723)
  ·
    refine ⟨42291697617715751494073585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28194465078477167662715723 42291697617715751494073585)
    ·
      refine ⟨31718773213286813620555189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42291697617715751494073585 31718773213286813620555189)
      ·
        refine ⟨2973634988745638776927049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31718773213286813620555189 2973634988745638776927049)
        ·
          refine ⟨2230226241559229082695287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2973634988745638776927049 2230226241559229082695287)
          ·
            refine ⟨3345339362338843624042931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2230226241559229082695287 3345339362338843624042931)
            ·
              refine ⟨5018009043508265436064397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3345339362338843624042931 5018009043508265436064397)
              ·
                refine ⟨1881753391315599538524149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5018009043508265436064397 1881753391315599538524149)
                ·
                  refine ⟨176414380435837456736639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1881753391315599538524149 176414380435837456736639)
                  ·
                    rfl

theorem cell21_773023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 3, 5].length) (baseStart_773023 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_773023 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_773023 prefixEnd_773023 := by exact prefixLift 773023
  have htrace : WordTrace (prefixWord ++ tailWord_773023) baseStart_773023 baseEnd_773023 := by
    simpa [prefixWord, tailWord_773023, baseEnd_773023] using wordTrace_append hprefix tailTrace_773023
  have hstable : (prefixWord ++ tailWord_773023).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773023).length < 2 ^ (prefixWord ++ tailWord_773023).sum := by decide
  have hdescent : baseEnd_773023 < baseStart_773023 := by decide
  rcases family_descends (prefixWord ++ tailWord_773023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773074 : List Nat := [3, 2, 2, 3, 1, 2, 3, 2, 3]
def baseStart_773074 : Nat := 118140960795 + 773074 * 2 ^ 59
def prefixEnd_773074 : Nat := 4983230072969 + 3 ^ 40 * 773074 * 2
def baseEnd_773074 : Nat := 176426019330672701386535

theorem tailTrace_773074 : CollatzResearch.WordTrace tailWord_773074 prefixEnd_773074 176426019330672701386535 := by
  unfold tailWord_773074
  simp only [CollatzResearch.WordTrace]
  refine ⟨7049081300323100843205569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18797550134194935581881517 7049081300323100843205569)
  ·
    refine ⟨5286810975242325632404177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7049081300323100843205569 5286810975242325632404177)
    ·
      refine ⟨3965108231431744224303133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5286810975242325632404177 3965108231431744224303133)
      ·
        refine ⟨1486915586786904084113675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3965108231431744224303133 1486915586786904084113675)
        ·
          refine ⟨2230373380180356126170513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1486915586786904084113675 2230373380180356126170513)
          ·
            refine ⟨1672780035135267094627885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2230373380180356126170513 1672780035135267094627885)
            ·
              refine ⟨627292513175725160485457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1672780035135267094627885 627292513175725160485457)
              ·
                refine ⟨470469384881793870364093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 627292513175725160485457 470469384881793870364093)
                ·
                  refine ⟨176426019330672701386535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 470469384881793870364093 176426019330672701386535)
                  ·
                    rfl

theorem cell21_773074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 3, 2, 3].length) (baseStart_773074 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_773074 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_773074 prefixEnd_773074 := by exact prefixLift 773074
  have htrace : WordTrace (prefixWord ++ tailWord_773074) baseStart_773074 baseEnd_773074 := by
    simpa [prefixWord, tailWord_773074, baseEnd_773074] using wordTrace_append hprefix tailTrace_773074
  have hstable : (prefixWord ++ tailWord_773074).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773074).length < 2 ^ (prefixWord ++ tailWord_773074).sum := by decide
  have hdescent : baseEnd_773074 < baseStart_773074 := by decide
  rcases family_descends (prefixWord ++ tailWord_773074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773085 : List Nat := [1, 4, 3, 1, 2, 2, 2, 6]
def baseStart_773085 : Nat := 118140960795 + 773085 * 2 ^ 59
def prefixEnd_773085 : Nat := 4983230072969 + 3 ^ 40 * 773085 * 2
def baseEnd_773085 : Nat := 58809509893513042234393

theorem tailTrace_773085 : CollatzResearch.WordTrace tailWord_773085 prefixEnd_773085 58809509893513042234393 := by
  unfold tailWord_773085
  simp only [CollatzResearch.WordTrace]
  refine ⟨28196726404252552251472709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18797817602835034834315139 28196726404252552251472709)
  ·
    refine ⟨5286886200797353547151133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28196726404252552251472709 5286886200797353547151133)
    ·
      refine ⟨1982582325299007580181675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5286886200797353547151133 1982582325299007580181675)
      ·
        refine ⟨2973873487948511370272513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1982582325299007580181675 2973873487948511370272513)
        ·
          refine ⟨2230405115961383527704385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2973873487948511370272513 2230405115961383527704385)
          ·
            refine ⟨1672803836971037645778289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2230405115961383527704385 1672803836971037645778289)
            ·
              refine ⟨1254602877728278234333717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1672803836971037645778289 1254602877728278234333717)
              ·
                refine ⟨58809509893513042234393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1254602877728278234333717 58809509893513042234393)
                ·
                  rfl

theorem cell21_773085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2, 6].length) (baseStart_773085 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_773085 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_773085 prefixEnd_773085 := by exact prefixLift 773085
  have htrace : WordTrace (prefixWord ++ tailWord_773085) baseStart_773085 baseEnd_773085 := by
    simpa [prefixWord, tailWord_773085, baseEnd_773085] using wordTrace_append hprefix tailTrace_773085
  have hstable : (prefixWord ++ tailWord_773085).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773085).length < 2 ^ (prefixWord ++ tailWord_773085).sum := by decide
  have hdescent : baseEnd_773085 < baseStart_773085 := by decide
  rcases family_descends (prefixWord ++ tailWord_773085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773130 : List Nat := [3, 1, 2, 2, 3, 1, 1, 4, 4]
def baseStart_773130 : Nat := 118140960795 + 773130 * 2 ^ 59
def prefixEnd_773130 : Nat := 4983230072969 + 3 ^ 40 * 773130 * 2
def baseEnd_773130 : Nat := 176438799293629048453087

theorem tailTrace_773130 : CollatzResearch.WordTrace tailWord_773130 prefixEnd_773130 176438799293629048453087 := by
  unfold tailWord_773130
  simp only [CollatzResearch.WordTrace]
  refine ⟨7049591922272381234215211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18798911792726349957907229 7049591922272381234215211)
  ·
    refine ⟨10574387883408571851322817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7049591922272381234215211 10574387883408571851322817)
    ·
      refine ⟨7930790912556428888492113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10574387883408571851322817 7930790912556428888492113)
      ·
        refine ⟨5948093184417321666369085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7930790912556428888492113 5948093184417321666369085)
        ·
          refine ⟨2230534944156495624888407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5948093184417321666369085 2230534944156495624888407)
          ·
            refine ⟨3345802416234743437332611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2230534944156495624888407 3345802416234743437332611)
            ·
              refine ⟨5018703624352115155998917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3345802416234743437332611 5018703624352115155998917)
              ·
                refine ⟨941006929566021591749797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5018703624352115155998917 941006929566021591749797)
                ·
                  refine ⟨176438799293629048453087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 941006929566021591749797 176438799293629048453087)
                  ·
                    rfl

theorem cell21_773130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 4, 4].length) (baseStart_773130 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_773130 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_773130 prefixEnd_773130 := by exact prefixLift 773130
  have htrace : WordTrace (prefixWord ++ tailWord_773130) baseStart_773130 baseEnd_773130 := by
    simpa [prefixWord, tailWord_773130, baseEnd_773130] using wordTrace_append hprefix tailTrace_773130
  have hstable : (prefixWord ++ tailWord_773130).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773130).length < 2 ^ (prefixWord ++ tailWord_773130).sum := by decide
  have hdescent : baseEnd_773130 < baseStart_773130 := by decide
  rcases family_descends (prefixWord ++ tailWord_773130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773144 : List Nat := [2, 1, 2, 3, 2, 2, 3, 6]
def baseStart_773144 : Nat := 118140960795 + 773144 * 2 ^ 59
def prefixEnd_773144 : Nat := 4983230072969 + 3 ^ 40 * 773144 * 2
def baseEnd_773144 : Nat := 58813998094789378406575

theorem tailTrace_773144 : CollatzResearch.WordTrace tailWord_773144 prefixEnd_773144 58813998094789378406575 := by
  unfold tailWord_773144
  simp only [CollatzResearch.WordTrace]
  refine ⟨14099439155519402663935243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18799252207359203551913657 14099439155519402663935243)
  ·
    refine ⟨21149158733279103995902865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14099439155519402663935243 21149158733279103995902865)
    ·
      refine ⟨15861869049959327996927149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21149158733279103995902865 15861869049959327996927149)
      ·
        refine ⟨5948200893734747998847681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15861869049959327996927149 5948200893734747998847681)
        ·
          refine ⟨4461150670301060999135761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5948200893734747998847681 4461150670301060999135761)
          ·
            refine ⟨3345863002725795749351821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4461150670301060999135761 3345863002725795749351821)
            ·
              refine ⟨1254698626022173406006933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3345863002725795749351821 1254698626022173406006933)
              ·
                refine ⟨58813998094789378406575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1254698626022173406006933 58813998094789378406575)
                ·
                  rfl

theorem cell21_773144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3, 6].length) (baseStart_773144 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_773144 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_773144 prefixEnd_773144 := by exact prefixLift 773144
  have htrace : WordTrace (prefixWord ++ tailWord_773144) baseStart_773144 baseEnd_773144 := by
    simpa [prefixWord, tailWord_773144, baseEnd_773144] using wordTrace_append hprefix tailTrace_773144
  have hstable : (prefixWord ++ tailWord_773144).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773144).length < 2 ^ (prefixWord ++ tailWord_773144).sum := by decide
  have hdescent : baseEnd_773144 < baseStart_773144 := by decide
  rcases family_descends (prefixWord ++ tailWord_773144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773313 : List Nat := [1, 2, 6, 1, 1, 1, 3, 6]
def baseStart_773313 : Nat := 118140960795 + 773313 * 2 ^ 59
def prefixEnd_773313 : Nat := 4983230072969 + 3 ^ 40 * 773313 * 2
def baseEnd_773313 : Nat := 58826854128953798967571

theorem tailTrace_773313 : CollatzResearch.WordTrace tailWord_773313 prefixEnd_773313 58826854128953798967571 := by
  unfold tailWord_773313
  simp only [CollatzResearch.WordTrace]
  refine ⟨28205042247426547190772593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18803361498284364793848395 28205042247426547190772593)
  ·
    refine ⟨21153781685569910393079445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28205042247426547190772593 21153781685569910393079445)
    ·
      refine ⟨991583516511089549675599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 21153781685569910393079445 991583516511089549675599)
      ·
        refine ⟨1487375274766634324513399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 991583516511089549675599 1487375274766634324513399)
        ·
          refine ⟨2231062912149951486770099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1487375274766634324513399 2231062912149951486770099)
          ·
            refine ⟨3346594368224927230155149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2231062912149951486770099 3346594368224927230155149)
            ·
              refine ⟨1254972888084347711308181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3346594368224927230155149 1254972888084347711308181)
              ·
                refine ⟨58826854128953798967571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1254972888084347711308181 58826854128953798967571)
                ·
                  rfl

theorem cell21_773313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 3, 6].length) (baseStart_773313 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_773313 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_773313 prefixEnd_773313 := by exact prefixLift 773313
  have htrace : WordTrace (prefixWord ++ tailWord_773313) baseStart_773313 baseEnd_773313 := by
    simpa [prefixWord, tailWord_773313, baseEnd_773313] using wordTrace_append hprefix tailTrace_773313
  have hstable : (prefixWord ++ tailWord_773313).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773313).length < 2 ^ (prefixWord ++ tailWord_773313).sum := by decide
  have hdescent : baseEnd_773313 < baseStart_773313 := by decide
  rcases family_descends (prefixWord ++ tailWord_773313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773344 : List Nat := [2, 1, 1, 3, 1, 5, 2, 3, 3]
def baseStart_773344 : Nat := 118140960795 + 773344 * 2 ^ 59
def prefixEnd_773344 : Nat := 4983230072969 + 3 ^ 40 * 773344 * 2
def baseEnd_773344 : Nat := 176487637009212231885983

theorem tailTrace_773344 : CollatzResearch.WordTrace tailWord_773344 prefixEnd_773344 176487637009212231885983 := by
  unfold tailWord_773344
  simp only [CollatzResearch.WordTrace]
  refine ⟨14103086455157119742575543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18804115273542826323434057 14103086455157119742575543)
  ·
    refine ⟨21154629682735679613863315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14103086455157119742575543 21154629682735679613863315)
    ·
      refine ⟨31731944524103519420794973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21154629682735679613863315 31731944524103519420794973)
      ·
        refine ⟨11899479196538819782798115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31731944524103519420794973 11899479196538819782798115)
        ·
          refine ⟨17849218794808229674197173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11899479196538819782798115 17849218794808229674197173)
          ·
            refine ⟨1673364262013271531955985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17849218794808229674197173 1673364262013271531955985)
            ·
              refine ⟨1255023196509953648966989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1673364262013271531955985 1255023196509953648966989)
              ·
                refine ⟨470633698691232618362621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1255023196509953648966989 470633698691232618362621)
                ·
                  refine ⟨176487637009212231885983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 470633698691232618362621 176487637009212231885983)
                  ·
                    rfl

theorem cell21_773344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2, 3, 3].length) (baseStart_773344 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_773344 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_773344 prefixEnd_773344 := by exact prefixLift 773344
  have htrace : WordTrace (prefixWord ++ tailWord_773344) baseStart_773344 baseEnd_773344 := by
    simpa [prefixWord, tailWord_773344, baseEnd_773344] using wordTrace_append hprefix tailTrace_773344
  have hstable : (prefixWord ++ tailWord_773344).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773344).length < 2 ^ (prefixWord ++ tailWord_773344).sum := by decide
  have hdescent : baseEnd_773344 < baseStart_773344 := by decide
  rcases family_descends (prefixWord ++ tailWord_773344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773355 : List Nat := [1, 1, 1, 1, 2, 7, 8]
def baseStart_773355 : Nat := 118140960795 + 773355 * 2 ^ 59
def prefixEnd_773355 : Nat := 4983230072969 + 3 ^ 40 * 773355 * 2
def baseEnd_773355 : Nat := 19610016373230961911403

theorem tailTrace_773355 : CollatzResearch.WordTrace tailWord_773355 prefixEnd_773355 19610016373230961911403 := by
  unfold tailWord_773355
  simp only [CollatzResearch.WordTrace]
  refine ⟨28206574113274388363801519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18804382742182925575867679 28206574113274388363801519)
  ·
    refine ⟨42309861169911582545702279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28206574113274388363801519 42309861169911582545702279)
    ·
      refine ⟨63464791754867373818553419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42309861169911582545702279 63464791754867373818553419)
      ·
        refine ⟨95197187632301060727830129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63464791754867373818553419 95197187632301060727830129)
        ·
          refine ⟨71397890724225795545872597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95197187632301060727830129 71397890724225795545872597)
          ·
            refine ⟨1673388063849042083106389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 71397890724225795545872597 1673388063849042083106389)
            ·
              refine ⟨19610016373230961911403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1673388063849042083106389 19610016373230961911403)
              ·
                rfl

theorem cell21_773355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 8].length) (baseStart_773355 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_773355 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_773355 prefixEnd_773355 := by exact prefixLift 773355
  have htrace : WordTrace (prefixWord ++ tailWord_773355) baseStart_773355 baseEnd_773355 := by
    simpa [prefixWord, tailWord_773355, baseEnd_773355] using wordTrace_append hprefix tailTrace_773355
  have hstable : (prefixWord ++ tailWord_773355).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773355).length < 2 ^ (prefixWord ++ tailWord_773355).sum := by decide
  have hdescent : baseEnd_773355 < baseStart_773355 := by decide
  rcases family_descends (prefixWord ++ tailWord_773355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773358 : List Nat := [4, 1, 2, 1, 1, 1, 5, 2, 4]
def baseStart_773358 : Nat := 118140960795 + 773358 * 2 ^ 59
def prefixEnd_773358 : Nat := 4983230072969 + 3 ^ 40 * 773358 * 2
def baseEnd_773358 : Nat := 176490831999951318652621

theorem tailTrace_773358 : CollatzResearch.WordTrace tailWord_773358 prefixEnd_773358 176490831999951318652621 := by
  unfold tailWord_773358
  simp only [CollatzResearch.WordTrace]
  refine ⟨3525835441532939984520091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18804455688175679917440485 3525835441532939984520091)
  ·
    refine ⟨5288753162299409976780137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3525835441532939984520091 5288753162299409976780137)
    ·
      refine ⟨3966564871724557482585103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5288753162299409976780137 3966564871724557482585103)
      ·
        refine ⟨5949847307586836223877655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3966564871724557482585103 5949847307586836223877655)
        ·
          refine ⟨8924770961380254335816483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5949847307586836223877655 8924770961380254335816483)
          ·
            refine ⟨13387156442070381503724725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8924770961380254335816483 13387156442070381503724725)
            ·
              refine ⟨1255045916444098265974193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13387156442070381503724725 1255045916444098265974193)
              ·
                refine ⟨941284437333073699480645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1255045916444098265974193 941284437333073699480645)
                ·
                  refine ⟨176490831999951318652621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 941284437333073699480645 176490831999951318652621)
                  ·
                    rfl

theorem cell21_773358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5, 2, 4].length) (baseStart_773358 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_773358 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_773358 prefixEnd_773358 := by exact prefixLift 773358
  have htrace : WordTrace (prefixWord ++ tailWord_773358) baseStart_773358 baseEnd_773358 := by
    simpa [prefixWord, tailWord_773358, baseEnd_773358] using wordTrace_append hprefix tailTrace_773358
  have hstable : (prefixWord ++ tailWord_773358).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773358).length < 2 ^ (prefixWord ++ tailWord_773358).sum := by decide
  have hdescent : baseEnd_773358 < baseStart_773358 := by decide
  rcases family_descends (prefixWord ++ tailWord_773358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773406 : List Nat := [4, 3, 2, 1, 2, 2, 7]
def baseStart_773406 : Nat := 118140960795 + 773406 * 2 ^ 59
def prefixEnd_773406 : Nat := 4983230072969 + 3 ^ 40 * 773406 * 2
def baseEnd_773406 : Nat := 19611309583768211316947

theorem tailTrace_773406 : CollatzResearch.WordTrace tailWord_773406 prefixEnd_773406 19611309583768211316947 := by
  unfold tailWord_773406
  simp only [CollatzResearch.WordTrace]
  refine ⟨3526054279511203009238509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18805622824059749382605381 3526054279511203009238509)
  ·
    refine ⟨1322270354816701128464441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3526054279511203009238509 1322270354816701128464441)
    ·
      refine ⟨991702766112525846348331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1322270354816701128464441 991702766112525846348331)
      ·
        refine ⟨1487554149168788769522497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 991702766112525846348331 1487554149168788769522497)
        ·
          refine ⟨1115665611876591577141873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1487554149168788769522497 1115665611876591577141873)
          ·
            refine ⟨836749208907443682856405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1115665611876591577141873 836749208907443682856405)
            ·
              refine ⟨19611309583768211316947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 836749208907443682856405 19611309583768211316947)
              ·
                rfl

theorem cell21_773406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 7].length) (baseStart_773406 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_773406 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_773406 prefixEnd_773406 := by exact prefixLift 773406
  have htrace : WordTrace (prefixWord ++ tailWord_773406) baseStart_773406 baseEnd_773406 := by
    simpa [prefixWord, tailWord_773406, baseEnd_773406] using wordTrace_append hprefix tailTrace_773406
  have hstable : (prefixWord ++ tailWord_773406).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773406).length < 2 ^ (prefixWord ++ tailWord_773406).sum := by decide
  have hdescent : baseEnd_773406 < baseStart_773406 := by decide
  rcases family_descends (prefixWord ++ tailWord_773406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773482 : List Nat := [3, 1, 3, 3, 3, 1, 1, 6]
def baseStart_773482 : Nat := 118140960795 + 773482 * 2 ^ 59
def prefixEnd_773482 : Nat := 4983230072969 + 3 ^ 40 * 773482 * 2
def baseEnd_773482 : Nat := 58839710163118219528567

theorem tailTrace_773482 : CollatzResearch.WordTrace tailWord_773482 prefixEnd_773482 58839710163118219528567 := by
  unfold tailWord_773482
  simp only [CollatzResearch.WordTrace]
  refine ⟨7052801545953572263418675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18807470789209526035783133 7052801545953572263418675)
  ·
    refine ⟨10579202318930358395128013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7052801545953572263418675 10579202318930358395128013)
    ·
      refine ⟨3967200869598884398173005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10579202318930358395128013 3967200869598884398173005)
      ·
        refine ⟨1487700326099581649314877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3967200869598884398173005 1487700326099581649314877)
        ·
          refine ⟨557887622287343118493079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1487700326099581649314877 557887622287343118493079)
          ·
            refine ⟨836831433431014677739619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 557887622287343118493079 836831433431014677739619)
            ·
              refine ⟨1255247150146522016609429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 836831433431014677739619 1255247150146522016609429)
              ·
                refine ⟨58839710163118219528567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1255247150146522016609429 58839710163118219528567)
                ·
                  rfl

theorem cell21_773482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 1, 6].length) (baseStart_773482 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_773482 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_773482 prefixEnd_773482 := by exact prefixLift 773482
  have htrace : WordTrace (prefixWord ++ tailWord_773482) baseStart_773482 baseEnd_773482 := by
    simpa [prefixWord, tailWord_773482, baseEnd_773482] using wordTrace_append hprefix tailTrace_773482
  have hstable : (prefixWord ++ tailWord_773482).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773482).length < 2 ^ (prefixWord ++ tailWord_773482).sum := by decide
  have hdescent : baseEnd_773482 < baseStart_773482 := by decide
  rcases family_descends (prefixWord ++ tailWord_773482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773524 : List Nat := [2, 4, 2, 1, 2, 2, 8]
def baseStart_773524 : Nat := 118140960795 + 773524 * 2 ^ 59
def prefixEnd_773524 : Nat := 4983230072969 + 3 ^ 40 * 773524 * 2
def baseEnd_773524 : Nat := 19614301717952435431735

theorem tailTrace_773524 : CollatzResearch.WordTrace tailWord_773524 prefixEnd_773524 19614301717952435431735 := by
  unfold tailWord_773524
  simp only [CollatzResearch.WordTrace]
  refine ⟨14106369024831065113351813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18808492033108086817802417 14106369024831065113351813)
  ·
    refine ⟨2644944192155824708753465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14106369024831065113351813 2644944192155824708753465)
    ·
      refine ⟨1983708144116868531565099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2644944192155824708753465 1983708144116868531565099)
      ·
        refine ⟨2975562216175302797347649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1983708144116868531565099 2975562216175302797347649)
        ·
          refine ⟨2231671662131477098010737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2975562216175302797347649 2231671662131477098010737)
          ·
            refine ⟨1673753746598607823508053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2231671662131477098010737 1673753746598607823508053)
            ·
              refine ⟨19614301717952435431735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1673753746598607823508053 19614301717952435431735)
              ·
                rfl

theorem cell21_773524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 8].length) (baseStart_773524 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_773524 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_773524 prefixEnd_773524 := by exact prefixLift 773524
  have htrace : WordTrace (prefixWord ++ tailWord_773524) baseStart_773524 baseEnd_773524 := by
    simpa [prefixWord, tailWord_773524, baseEnd_773524] using wordTrace_append hprefix tailTrace_773524
  have hstable : (prefixWord ++ tailWord_773524).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773524).length < 2 ^ (prefixWord ++ tailWord_773524).sum := by decide
  have hdescent : baseEnd_773524 < baseStart_773524 := by decide
  rcases family_descends (prefixWord ++ tailWord_773524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773544 : List Nat := [2, 1, 6, 1, 2, 1, 3, 1, 4]
def baseStart_773544 : Nat := 118140960795 + 773544 * 2 ^ 59
def prefixEnd_773544 : Nat := 4983230072969 + 3 ^ 40 * 773544 * 2
def baseEnd_773544 : Nat := 176533279734056328552241

theorem tailTrace_773544 : CollatzResearch.WordTrace tailWord_773544 prefixEnd_773544 176533279734056328552241 := by
  unfold tailWord_773544
  simp only [CollatzResearch.WordTrace]
  refine ⟨14106733754794836821215843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18808978339726449094954457 14106733754794836821215843)
  ·
    refine ⟨21160100632192255231823765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14106733754794836821215843 21160100632192255231823765)
    ·
      refine ⟨991879717134011963991739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 21160100632192255231823765 991879717134011963991739)
      ·
        refine ⟨1487819575701017945987609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 991879717134011963991739 1487819575701017945987609)
        ·
          refine ⟨1115864681775763459490707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1487819575701017945987609 1115864681775763459490707)
          ·
            refine ⟨1673797022663645189236061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1115864681775763459490707 1673797022663645189236061)
            ·
              refine ⟨627673883498866945963523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1673797022663645189236061 627673883498866945963523)
              ·
                refine ⟨941510825248300418945285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 627673883498866945963523 941510825248300418945285)
                ·
                  refine ⟨176533279734056328552241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 941510825248300418945285 176533279734056328552241)
                  ·
                    rfl

theorem cell21_773544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 3, 1, 4].length) (baseStart_773544 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_773544 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_773544 prefixEnd_773544 := by exact prefixLift 773544
  have htrace : WordTrace (prefixWord ++ tailWord_773544) baseStart_773544 baseEnd_773544 := by
    simpa [prefixWord, tailWord_773544, baseEnd_773544] using wordTrace_append hprefix tailTrace_773544
  have hstable : (prefixWord ++ tailWord_773544).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773544).length < 2 ^ (prefixWord ++ tailWord_773544).sum := by decide
  have hdescent : baseEnd_773544 < baseStart_773544 := by decide
  rcases family_descends (prefixWord ++ tailWord_773544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773603 : List Nat := [1, 1, 1, 6, 2, 3, 2, 1, 4]
def baseStart_773603 : Nat := 118140960795 + 773603 * 2 ^ 59
def prefixEnd_773603 : Nat := 4983230072969 + 3 ^ 40 * 773603 * 2
def baseEnd_773603 : Nat := 176546744337885337068787

theorem tailTrace_773603 : CollatzResearch.WordTrace tailWord_773603 prefixEnd_773603 176546744337885337068787 := by
  unfold tailWord_773603
  simp only [CollatzResearch.WordTrace]
  refine ⟨28215619416375926718829463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18810412944250617812552975 28215619416375926718829463)
  ·
    refine ⟨42323429124563890078244195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28215619416375926718829463 42323429124563890078244195)
    ·
      refine ⟨63485143686845835117366293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42323429124563890078244195 63485143686845835117366293)
      ·
        refine ⟨2975866110320898521126545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 63485143686845835117366293 2975866110320898521126545)
        ·
          refine ⟨2231899582740673890844909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2975866110320898521126545 2231899582740673890844909)
          ·
            refine ⟨836962343527752709066841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2231899582740673890844909 836962343527752709066841)
            ·
              refine ⟨627721757645814531800131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 836962343527752709066841 627721757645814531800131)
              ·
                refine ⟨941582636468721797700197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 627721757645814531800131 941582636468721797700197)
                ·
                  refine ⟨176546744337885337068787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 941582636468721797700197 176546744337885337068787)
                  ·
                    rfl

theorem cell21_773603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 2, 1, 4].length) (baseStart_773603 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_773603 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_773603 prefixEnd_773603 := by exact prefixLift 773603
  have htrace : WordTrace (prefixWord ++ tailWord_773603) baseStart_773603 baseEnd_773603 := by
    simpa [prefixWord, tailWord_773603, baseEnd_773603] using wordTrace_append hprefix tailTrace_773603
  have hstable : (prefixWord ++ tailWord_773603).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773603).length < 2 ^ (prefixWord ++ tailWord_773603).sum := by decide
  have hdescent : baseEnd_773603 < baseStart_773603 := by decide
  rcases family_descends (prefixWord ++ tailWord_773603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773614 : List Nat := [4, 1, 2, 1, 2, 1, 2, 1, 7]
def baseStart_773614 : Nat := 118140960795 + 773614 * 2 ^ 59
def prefixEnd_773614 : Nat := 4983230072969 + 3 ^ 40 * 773614 * 2
def baseEnd_773614 : Nat := 176549254687751762385431

theorem tailTrace_773614 : CollatzResearch.WordTrace tailWord_773614 prefixEnd_773614 176549254687751762385431 := by
  unfold tailWord_773614
  simp only [CollatzResearch.WordTrace]
  refine ⟨3527002577417009449684987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18810680412890717064986597 3527002577417009449684987)
  ·
    refine ⟨5290503866125514174527481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3527002577417009449684987 5290503866125514174527481)
    ·
      refine ⟨3967877899594135630895611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5290503866125514174527481 3967877899594135630895611)
      ·
        refine ⟨5951816849391203446343417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3967877899594135630895611 5951816849391203446343417)
        ·
          refine ⟨4463862637043402584757563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5951816849391203446343417 4463862637043402584757563)
          ·
            refine ⟨6695793955565103877136345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4463862637043402584757563 6695793955565103877136345)
            ·
              refine ⟨5021845466673827907852259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6695793955565103877136345 5021845466673827907852259)
              ·
                refine ⟨7532768200010741861778389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5021845466673827907852259 7532768200010741861778389)
                ·
                  refine ⟨176549254687751762385431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7532768200010741861778389 176549254687751762385431)
                  ·
                    rfl

theorem cell21_773614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 1, 7].length) (baseStart_773614 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_773614 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_773614 prefixEnd_773614 := by exact prefixLift 773614
  have htrace : WordTrace (prefixWord ++ tailWord_773614) baseStart_773614 baseEnd_773614 := by
    simpa [prefixWord, tailWord_773614, baseEnd_773614] using wordTrace_append hprefix tailTrace_773614
  have hstable : (prefixWord ++ tailWord_773614).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773614).length < 2 ^ (prefixWord ++ tailWord_773614).sum := by decide
  have hdescent : baseEnd_773614 < baseStart_773614 := by decide
  rcases family_descends (prefixWord ++ tailWord_773614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773628 : List Nat := [2, 2, 2, 1, 2, 1, 2, 1, 8]
def baseStart_773628 : Nat := 118140960795 + 773628 * 2 ^ 59
def prefixEnd_773628 : Nat := 4983230072969 + 3 ^ 40 * 773628 * 2
def baseEnd_773628 : Nat := 176552449678490849152069

theorem tailTrace_773628 : CollatzResearch.WordTrace tailWord_773628 prefixEnd_773628 176552449678490849152069 := by
  unfold tailWord_773628
  simp only [CollatzResearch.WordTrace]
  refine ⟨14108265620642677994244769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18811020827523570658993025 14108265620642677994244769)
  ·
    refine ⟨10581199215482008495683577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14108265620642677994244769 10581199215482008495683577)
    ·
      refine ⟨7935899411611506371762683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10581199215482008495683577 7935899411611506371762683)
      ·
        refine ⟨11903849117417259557644025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7935899411611506371762683 11903849117417259557644025)
        ·
          refine ⟨8927886838062944668233019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11903849117417259557644025 8927886838062944668233019)
          ·
            refine ⟨13391830257094417002349529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8927886838062944668233019 13391830257094417002349529)
            ·
              refine ⟨10043872692820812751762147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13391830257094417002349529 10043872692820812751762147)
              ·
                refine ⟨15065809039231219127643221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10043872692820812751762147 15065809039231219127643221)
                ·
                  refine ⟨176552449678490849152069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15065809039231219127643221 176552449678490849152069)
                  ·
                    rfl

theorem cell21_773628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 8].length) (baseStart_773628 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_773628 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_773628 prefixEnd_773628 := by exact prefixLift 773628
  have htrace : WordTrace (prefixWord ++ tailWord_773628) baseStart_773628 baseEnd_773628 := by
    simpa [prefixWord, tailWord_773628, baseEnd_773628] using wordTrace_append hprefix tailTrace_773628
  have hstable : (prefixWord ++ tailWord_773628).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773628).length < 2 ^ (prefixWord ++ tailWord_773628).sum := by decide
  have hdescent : baseEnd_773628 < baseStart_773628 := by decide
  rcases family_descends (prefixWord ++ tailWord_773628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773741 : List Nat := [1, 5, 1, 1, 4, 2, 1, 3, 3]
def baseStart_773741 : Nat := 118140960795 + 773741 * 2 ^ 59
def prefixEnd_773741 : Nat := 4983230072969 + 3 ^ 40 * 773741 * 2
def baseEnd_773741 : Nat := 176578237818027763768505

theorem tailTrace_773741 : CollatzResearch.WordTrace tailWord_773741 prefixEnd_773741 176578237818027763768505 := by
  unfold tailWord_773741
  simp only [CollatzResearch.WordTrace]
  refine ⟨28220652689875976287353077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18813768459917317524902051 28220652689875976287353077)
  ·
    refine ⟨2645686189675872776939351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28220652689875976287353077 2645686189675872776939351)
    ·
      refine ⟨3968529284513809165409027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2645686189675872776939351 3968529284513809165409027)
      ·
        refine ⟨5952793926770713748113541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3968529284513809165409027 5952793926770713748113541)
        ·
          refine ⟨1116148861269508827771289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5952793926770713748113541 1116148861269508827771289)
          ·
            refine ⟨837111645952131620828467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1116148861269508827771289 837111645952131620828467)
            ·
              refine ⟨1255667468928197431242701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 837111645952131620828467 1255667468928197431242701)
              ·
                refine ⟨470875300848074036716013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1255667468928197431242701 470875300848074036716013)
                ·
                  refine ⟨176578237818027763768505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 470875300848074036716013 176578237818027763768505)
                  ·
                    rfl

theorem cell21_773741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 1, 3, 3].length) (baseStart_773741 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_773741 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_773741 prefixEnd_773741 := by exact prefixLift 773741
  have htrace : WordTrace (prefixWord ++ tailWord_773741) baseStart_773741 baseEnd_773741 := by
    simpa [prefixWord, tailWord_773741, baseEnd_773741] using wordTrace_append hprefix tailTrace_773741
  have hstable : (prefixWord ++ tailWord_773741).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773741).length < 2 ^ (prefixWord ++ tailWord_773741).sum := by decide
  have hdescent : baseEnd_773741 < baseStart_773741 := by decide
  rcases family_descends (prefixWord ++ tailWord_773741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773842 : List Nat := [3, 2, 2, 2, 2, 1, 1, 1, 7]
def baseStart_773842 : Nat := 118140960795 + 773842 * 2 ^ 59
def prefixEnd_773842 : Nat := 4983230072969 + 3 ^ 40 * 773842 * 2
def baseEnd_773842 : Nat := 176601287394074032584965

theorem tailTrace_773842 : CollatzResearch.WordTrace tailWord_773842 prefixEnd_773842 176601287394074032584965 := by
  unfold tailWord_773842
  simp only [CollatzResearch.WordTrace]
  refine ⟨7056084115627517634194945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18816224308340047024519853 7056084115627517634194945)
  ·
    refine ⟨5292063086720638225646209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7056084115627517634194945 5292063086720638225646209)
    ·
      refine ⟨3969047315040478669234657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5292063086720638225646209 3969047315040478669234657)
      ·
        refine ⟨2976785486280359001925993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3969047315040478669234657 2976785486280359001925993)
        ·
          refine ⟨2232589114710269251444495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2976785486280359001925993 2232589114710269251444495)
          ·
            refine ⟨3348883672065403877166743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2232589114710269251444495 3348883672065403877166743)
            ·
              refine ⟨5023325508098105815750115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3348883672065403877166743 5023325508098105815750115)
              ·
                refine ⟨7534988262147158723625173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5023325508098105815750115 7534988262147158723625173)
                ·
                  refine ⟨176601287394074032584965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7534988262147158723625173 176601287394074032584965)
                  ·
                    rfl

theorem cell21_773842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 1, 7].length) (baseStart_773842 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_773842 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_773842 prefixEnd_773842 := by exact prefixLift 773842
  have htrace : WordTrace (prefixWord ++ tailWord_773842) baseStart_773842 baseEnd_773842 := by
    simpa [prefixWord, tailWord_773842, baseEnd_773842] using wordTrace_append hprefix tailTrace_773842
  have hstable : (prefixWord ++ tailWord_773842).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773842).length < 2 ^ (prefixWord ++ tailWord_773842).sum := by decide
  have hdescent : baseEnd_773842 < baseStart_773842 := by decide
  rcases family_descends (prefixWord ++ tailWord_773842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773873 : List Nat := [1, 2, 2, 2, 2, 3, 3, 2, 4]
def baseStart_773873 : Nat := 118140960795 + 773873 * 2 ^ 59
def prefixEnd_773873 : Nat := 4983230072969 + 3 ^ 40 * 773873 * 2
def baseEnd_773873 : Nat := 176608362016424867568235

theorem tailTrace_773873 : CollatzResearch.WordTrace tailWord_773873 prefixEnd_773873 176608362016424867568235 := by
  unfold tailWord_773873
  simp only [CollatzResearch.WordTrace]
  refine ⟨28225467125397762831158273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18816978083598508554105515 28225467125397762831158273)
  ·
    refine ⟨21169100344048322123368705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28225467125397762831158273 21169100344048322123368705)
    ·
      refine ⟨15876825258036241592526529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21169100344048322123368705 15876825258036241592526529)
      ·
        refine ⟨11907618943527181194394897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15876825258036241592526529 11907618943527181194394897)
        ·
          refine ⟨8930714207645385895796173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11907618943527181194394897 8930714207645385895796173)
          ·
            refine ⟨3349017827867019710923565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8930714207645385895796173 3349017827867019710923565)
            ·
              refine ⟨1255881685450132391596337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3349017827867019710923565 1255881685450132391596337)
              ·
                refine ⟨941911264087599293697253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1255881685450132391596337 941911264087599293697253)
                ·
                  refine ⟨176608362016424867568235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 941911264087599293697253 176608362016424867568235)
                  ·
                    rfl

theorem cell21_773873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3, 2, 4].length) (baseStart_773873 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_773873 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_773873 prefixEnd_773873 := by exact prefixLift 773873
  have htrace : WordTrace (prefixWord ++ tailWord_773873) baseStart_773873 baseEnd_773873 := by
    simpa [prefixWord, tailWord_773873, baseEnd_773873] using wordTrace_append hprefix tailTrace_773873
  have hstable : (prefixWord ++ tailWord_773873).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773873).length < 2 ^ (prefixWord ++ tailWord_773873).sum := by decide
  have hdescent : baseEnd_773873 < baseStart_773873 := by decide
  rcases family_descends (prefixWord ++ tailWord_773873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773876 : List Nat := [2, 6, 1, 1, 1, 1, 1, 3, 5]
def baseStart_773876 : Nat := 118140960795 + 773876 * 2 ^ 59
def prefixEnd_773876 : Nat := 4983230072969 + 3 ^ 40 * 773876 * 2
def baseEnd_773876 : Nat := 176609046657297529018229

theorem tailTrace_773876 : CollatzResearch.WordTrace tailWord_773876 prefixEnd_773876 176609046657297529018229 := by
  unfold tailWord_773876
  simp only [CollatzResearch.WordTrace]
  refine ⟨14112788272193447171758741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18817051029591262895678321 14112788272193447171758741)
  ·
    refine ⟨661536950259067836176191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 14112788272193447171758741 661536950259067836176191)
    ·
      refine ⟨992305425388601754264287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 661536950259067836176191 992305425388601754264287)
      ·
        refine ⟨1488458138082902631396431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 992305425388601754264287 1488458138082902631396431)
        ·
          refine ⟨2232687207124353947094647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1488458138082902631396431 2232687207124353947094647)
          ·
            refine ⟨3349030810686530920641971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2232687207124353947094647 3349030810686530920641971)
            ·
              refine ⟨5023546216029796380962957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3349030810686530920641971 5023546216029796380962957)
              ·
                refine ⟨1883829831011173642861109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5023546216029796380962957 1883829831011173642861109)
                ·
                  refine ⟨176609046657297529018229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1883829831011173642861109 176609046657297529018229)
                  ·
                    rfl

theorem cell21_773876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_773876 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_773876 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_773876 prefixEnd_773876 := by exact prefixLift 773876
  have htrace : WordTrace (prefixWord ++ tailWord_773876) baseStart_773876 baseEnd_773876 := by
    simpa [prefixWord, tailWord_773876, baseEnd_773876] using wordTrace_append hprefix tailTrace_773876
  have hstable : (prefixWord ++ tailWord_773876).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773876).length < 2 ^ (prefixWord ++ tailWord_773876).sum := by decide
  have hdescent : baseEnd_773876 < baseStart_773876 := by decide
  rcases family_descends (prefixWord ++ tailWord_773876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773932 : List Nat := [2, 2, 1, 1, 1, 5, 2, 1, 6]
def baseStart_773932 : Nat := 118140960795 + 773932 * 2 ^ 59
def prefixEnd_773932 : Nat := 4983230072969 + 3 ^ 40 * 773932 * 2
def baseEnd_773932 : Nat := 176621826620253876084781

theorem tailTrace_773932 : CollatzResearch.WordTrace tailWord_773932 prefixEnd_773932 176621826620253876084781 := by
  unfold tailWord_773932
  simp only [CollatzResearch.WordTrace]
  refine ⟨14113809516092007953778025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18818412688122677271704033 14113809516092007953778025)
  ·
    refine ⟨10585357137069005965333519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14113809516092007953778025 10585357137069005965333519)
    ·
      refine ⟨15878035705603508948000279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10585357137069005965333519 15878035705603508948000279)
      ·
        refine ⟨23817053558405263422000419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15878035705603508948000279 23817053558405263422000419)
        ·
          refine ⟨35725580337607895133000629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23817053558405263422000419 35725580337607895133000629)
          ·
            refine ⟨3349273156650740168718809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35725580337607895133000629 3349273156650740168718809)
            ·
              refine ⟨2511954867488055126539107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3349273156650740168718809 2511954867488055126539107)
              ·
                refine ⟨3767932301232082689808661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2511954867488055126539107 3767932301232082689808661)
                ·
                  refine ⟨176621826620253876084781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3767932301232082689808661 176621826620253876084781)
                  ·
                    rfl

theorem cell21_773932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 6].length) (baseStart_773932 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_773932 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_773932 prefixEnd_773932 := by exact prefixLift 773932
  have htrace : WordTrace (prefixWord ++ tailWord_773932) baseStart_773932 baseEnd_773932 := by
    simpa [prefixWord, tailWord_773932, baseEnd_773932] using wordTrace_append hprefix tailTrace_773932
  have hstable : (prefixWord ++ tailWord_773932).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773932).length < 2 ^ (prefixWord ++ tailWord_773932).sum := by decide
  have hdescent : baseEnd_773932 < baseStart_773932 := by decide
  rcases family_descends (prefixWord ++ tailWord_773932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
