import V185TrunkScan23Chunk0944

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5593788 : List Nat := [2, 2, 2, 3, 1, 1, 1, 1, 4, 6]
def baseStart_5593788 : Nat := 118140960795 + 5593788 * 2 ^ 59
def prefixEnd_5593788 : Nat := 4983230072969 + 3 ^ 40 * 5593788 * 2
def baseEnd_5593788 : Nat := 957433974450821837474881

theorem tailTrace_5593788 : CollatzResearch.WordTrace tailWord_5593788 prefixEnd_5593788 957433974450821837474881 := by
  unfold tailWord_5593788
  simp only [CollatzResearch.WordTrace]
  refine ⟨102011104729334446888387009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136014806305779262517849345 102011104729334446888387009)
  ·
    refine ⟨76508328547000835166290257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102011104729334446888387009 76508328547000835166290257)
    ·
      refine ⟨57381246410250626374717693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76508328547000835166290257 57381246410250626374717693)
      ·
        refine ⟨21517967403843984890519135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57381246410250626374717693 21517967403843984890519135)
        ·
          refine ⟨32276951105765977335778703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21517967403843984890519135 32276951105765977335778703)
          ·
            refine ⟨48415426658648966003668055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32276951105765977335778703 48415426658648966003668055)
            ·
              refine ⟨72623139987973449005502083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48415426658648966003668055 72623139987973449005502083)
              ·
                refine ⟨108934709981960173508253125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72623139987973449005502083 108934709981960173508253125)
                ·
                  refine ⟨20425258121617532532797461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 108934709981960173508253125 20425258121617532532797461)
                  ·
                    refine ⟨957433974450821837474881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20425258121617532532797461 957433974450821837474881)
                    ·
                      rfl

theorem cell23_5593788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 4, 6].length) (baseStart_5593788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5593788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5593788 prefixEnd_5593788 := by exact prefixLift 5593788
  have htrace : WordTrace (prefixWord ++ tailWord_5593788) baseStart_5593788 baseEnd_5593788 := by
    simpa [prefixWord, tailWord_5593788, baseEnd_5593788] using wordTrace_append hprefix tailTrace_5593788
  have hstable : (prefixWord ++ tailWord_5593788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5593788).length < 2 ^ (prefixWord ++ tailWord_5593788).sum := by decide
  have hdescent : baseEnd_5593788 < baseStart_5593788 := by decide
  rcases family_descends (prefixWord ++ tailWord_5593788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5593789 : List Nat := [1, 4, 1, 2, 1, 5, 1, 2, 2, 1, 3]
def baseStart_5593789 : Nat := 118140960795 + 5593789 * 2 ^ 59
def prefixEnd_5593789 : Nat := 4983230072969 + 3 ^ 40 * 5593789 * 2
def baseEnd_5593789 : Nat := 2872302436833120008512139

theorem tailTrace_5593789 : CollatzResearch.WordTrace tailWord_5593789 prefixEnd_5593789 2872302436833120008512139 := by
  unfold tailWord_5593789
  simp only [CollatzResearch.WordTrace]
  refine ⟨204022245931665270947560421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136014830621110180631706947 204022245931665270947560421)
  ·
    refine ⟨38254171112187238302667579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 204022245931665270947560421 38254171112187238302667579)
    ·
      refine ⟨57381256668280857454001369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38254171112187238302667579 57381256668280857454001369)
      ·
        refine ⟨43035942501210643090501027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57381256668280857454001369 43035942501210643090501027)
        ·
          refine ⟨64553913751815964635751541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43035942501210643090501027 64553913751815964635751541)
          ·
            refine ⟨6051929414232746684601707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 64553913751815964635751541 6051929414232746684601707)
            ·
              refine ⟨9077894121349120026902561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6051929414232746684601707 9077894121349120026902561)
              ·
                refine ⟨6808420591011840020176921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9077894121349120026902561 6808420591011840020176921)
                ·
                  refine ⟨5106315443258880015132691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6808420591011840020176921 5106315443258880015132691)
                  ·
                    refine ⟨7659473164888320022699037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5106315443258880015132691 7659473164888320022699037)
                    ·
                      refine ⟨2872302436833120008512139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7659473164888320022699037 2872302436833120008512139)
                      ·
                        rfl

theorem cell23_5593789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 1, 2, 2, 1, 3].length) (baseStart_5593789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5593789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5593789 prefixEnd_5593789 := by exact prefixLift 5593789
  have htrace : WordTrace (prefixWord ++ tailWord_5593789) baseStart_5593789 baseEnd_5593789 := by
    simpa [prefixWord, tailWord_5593789, baseEnd_5593789] using wordTrace_append hprefix tailTrace_5593789
  have hstable : (prefixWord ++ tailWord_5593789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5593789).length < 2 ^ (prefixWord ++ tailWord_5593789).sum := by decide
  have hdescent : baseEnd_5593789 < baseStart_5593789 := by decide
  rcases family_descends (prefixWord ++ tailWord_5593789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5593818 : List Nat := [3, 1, 1, 2, 2, 2, 1, 4, 7]
def baseStart_5593818 : Nat := 118140960795 + 5593818 * 2 ^ 59
def prefixEnd_5593818 : Nat := 4983230072969 + 3 ^ 40 * 5593818 * 2
def baseEnd_5593818 : Nat := 319146369752455599449945

theorem tailTrace_5593818 : CollatzResearch.WordTrace tailWord_5593818 prefixEnd_5593818 319146369752455599449945 := by
  unfold tailWord_5593818
  simp only [CollatzResearch.WordTrace]
  refine ⟨51005825912140052225091527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136015535765706805933577405 51005825912140052225091527)
  ·
    refine ⟨76508738868210078337637291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51005825912140052225091527 76508738868210078337637291)
    ·
      refine ⟨114763108302315117506455937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76508738868210078337637291 114763108302315117506455937)
      ·
        refine ⟨86072331226736338129841953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114763108302315117506455937 86072331226736338129841953)
        ·
          refine ⟨64554248420052253597381465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86072331226736338129841953 64554248420052253597381465)
          ·
            refine ⟨48415686315039190198036099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64554248420052253597381465 48415686315039190198036099)
            ·
              refine ⟨72623529472558785297054149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48415686315039190198036099 72623529472558785297054149)
              ·
                refine ⟨13616911776104772243197653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72623529472558785297054149 13616911776104772243197653)
                ·
                  refine ⟨319146369752455599449945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13616911776104772243197653 319146369752455599449945)
                  ·
                    rfl

theorem cell23_5593818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 4, 7].length) (baseStart_5593818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5593818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5593818 prefixEnd_5593818 := by exact prefixLift 5593818
  have htrace : WordTrace (prefixWord ++ tailWord_5593818) baseStart_5593818 baseEnd_5593818 := by
    simpa [prefixWord, tailWord_5593818, baseEnd_5593818] using wordTrace_append hprefix tailTrace_5593818
  have hstable : (prefixWord ++ tailWord_5593818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5593818).length < 2 ^ (prefixWord ++ tailWord_5593818).sum := by decide
  have hdescent : baseEnd_5593818 < baseStart_5593818 := by decide
  rcases family_descends (prefixWord ++ tailWord_5593818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5593855 : List Nat := [1, 1, 2, 2, 1, 3, 1, 3, 2, 5, 2]
def baseStart_5593855 : Nat := 118140960795 + 5593855 * 2 ^ 59
def prefixEnd_5593855 : Nat := 4983230072969 + 3 ^ 40 * 5593855 * 2
def baseEnd_5593855 : Nat := 2872336326556316750286835

theorem tailTrace_5593855 : CollatzResearch.WordTrace tailWord_5593855 prefixEnd_5593855 2872336326556316750286835 := by
  unfold tailWord_5593855
  simp only [CollatzResearch.WordTrace]
  refine ⟨204024653149426164219463019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136016435432950776146308679 204024653149426164219463019)
  ·
    refine ⟨306036979724139246329194529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204024653149426164219463019 306036979724139246329194529)
    ·
      refine ⟨229527734793104434746895897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 306036979724139246329194529 229527734793104434746895897)
      ·
        refine ⟨172145801094828326060171923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 229527734793104434746895897 172145801094828326060171923)
        ·
          refine ⟨258218701642242489090257885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172145801094828326060171923 258218701642242489090257885)
          ·
            refine ⟨96832013115840933408846707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 258218701642242489090257885 96832013115840933408846707)
            ·
              refine ⟨145248019673761400113270061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96832013115840933408846707 145248019673761400113270061)
              ·
                refine ⟨54468007377660525042476273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 145248019673761400113270061 54468007377660525042476273)
                ·
                  refine ⟨40851005533245393781857205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54468007377660525042476273 40851005533245393781857205)
                  ·
                    refine ⟨3829781768741755667049113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40851005533245393781857205 3829781768741755667049113)
                    ·
                      refine ⟨2872336326556316750286835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3829781768741755667049113 2872336326556316750286835)
                      ·
                        rfl

theorem cell23_5593855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 3, 2, 5, 2].length) (baseStart_5593855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5593855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5593855 prefixEnd_5593855 := by exact prefixLift 5593855
  have htrace : WordTrace (prefixWord ++ tailWord_5593855) baseStart_5593855 baseEnd_5593855 := by
    simpa [prefixWord, tailWord_5593855, baseEnd_5593855] using wordTrace_append hprefix tailTrace_5593855
  have hstable : (prefixWord ++ tailWord_5593855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5593855).length < 2 ^ (prefixWord ++ tailWord_5593855).sum := by decide
  have hdescent : baseEnd_5593855 < baseStart_5593855 := by decide
  rcases family_descends (prefixWord ++ tailWord_5593855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5593863 : List Nat := [1, 1, 4, 4, 1, 3, 2, 1, 2, 2, 2]
def baseStart_5593863 : Nat := 118140960795 + 5593863 * 2 ^ 59
def prefixEnd_5593863 : Nat := 4983230072969 + 3 ^ 40 * 5593863 * 2
def baseEnd_5593863 : Nat := 2872340434401552718986799

theorem tailTrace_5593863 : CollatzResearch.WordTrace tailWord_5593863 prefixEnd_5593863 2872340434401552718986799 := by
  unfold tailWord_5593863
  simp only [CollatzResearch.WordTrace]
  refine ⟨204024944933397181585754243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136016629955598121057169495 204024944933397181585754243)
  ·
    refine ⟨306037417400095772378631365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204024944933397181585754243 306037417400095772378631365)
    ·
      refine ⟨57382015762517957320993381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 306037417400095772378631365 57382015762517957320993381)
      ·
        refine ⟨10759127955472116997686259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57382015762517957320993381 10759127955472116997686259)
        ·
          refine ⟨16138691933208175496529389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10759127955472116997686259 16138691933208175496529389)
          ·
            refine ⟨6052009474953065811198521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16138691933208175496529389 6052009474953065811198521)
            ·
              refine ⟨4539007106214799358398891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6052009474953065811198521 4539007106214799358398891)
              ·
                refine ⟨6808510659322199037598337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4539007106214799358398891 6808510659322199037598337)
                ·
                  refine ⟨5106382994491649278198753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6808510659322199037598337 5106382994491649278198753)
                  ·
                    refine ⟨3829787245868736958649065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5106382994491649278198753 3829787245868736958649065)
                    ·
                      refine ⟨2872340434401552718986799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3829787245868736958649065 2872340434401552718986799)
                      ·
                        rfl

theorem cell23_5593863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 2, 1, 2, 2, 2].length) (baseStart_5593863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5593863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5593863 prefixEnd_5593863 := by exact prefixLift 5593863
  have htrace : WordTrace (prefixWord ++ tailWord_5593863) baseStart_5593863 baseEnd_5593863 := by
    simpa [prefixWord, tailWord_5593863, baseEnd_5593863] using wordTrace_append hprefix tailTrace_5593863
  have hstable : (prefixWord ++ tailWord_5593863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5593863).length < 2 ^ (prefixWord ++ tailWord_5593863).sum := by decide
  have hdescent : baseEnd_5593863 < baseStart_5593863 := by decide
  rcases family_descends (prefixWord ++ tailWord_5593863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5593952 : List Nat := [2, 1, 1, 3, 3, 1, 1, 2, 5, 1, 3]
def baseStart_5593952 : Nat := 118140960795 + 5593952 * 2 ^ 59
def prefixEnd_5593952 : Nat := 4983230072969 + 3 ^ 40 * 5593952 * 2
def baseEnd_5593952 : Nat := 2872386134179802870773889

theorem tailTrace_5593952 : CollatzResearch.WordTrace tailWord_5593952 prefixEnd_5593952 2872386134179802870773889 := by
  unfold tailWord_5593952
  simp only [CollatzResearch.WordTrace]
  refine ⟨102014095515037374892872055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136018794020049833190496073 102014095515037374892872055)
  ·
    refine ⟨153021143272556062339308083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102014095515037374892872055 153021143272556062339308083)
    ·
      refine ⟨229531714908834093508962125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153021143272556062339308083 229531714908834093508962125)
      ·
        refine ⟨86074393090812785065860797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 229531714908834093508962125 86074393090812785065860797)
        ·
          refine ⟨32277897409054794399697799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86074393090812785065860797 32277897409054794399697799)
          ·
            refine ⟨48416846113582191599546699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32277897409054794399697799 48416846113582191599546699)
            ·
              refine ⟨72625269170373287399320049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48416846113582191599546699 72625269170373287399320049)
              ·
                refine ⟨54468951877779965549490037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72625269170373287399320049 54468951877779965549490037)
                ·
                  refine ⟨5106464238541871770264691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54468951877779965549490037 5106464238541871770264691)
                  ·
                    refine ⟨7659696357812807655397037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5106464238541871770264691 7659696357812807655397037)
                    ·
                      refine ⟨2872386134179802870773889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7659696357812807655397037 2872386134179802870773889)
                      ·
                        rfl

theorem cell23_5593952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 2, 5, 1, 3].length) (baseStart_5593952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5593952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5593952 prefixEnd_5593952 := by exact prefixLift 5593952
  have htrace : WordTrace (prefixWord ++ tailWord_5593952) baseStart_5593952 baseEnd_5593952 := by
    simpa [prefixWord, tailWord_5593952, baseEnd_5593952] using wordTrace_append hprefix tailTrace_5593952
  have hstable : (prefixWord ++ tailWord_5593952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5593952).length < 2 ^ (prefixWord ++ tailWord_5593952).sum := by decide
  have hdescent : baseEnd_5593952 < baseStart_5593952 := by decide
  rcases family_descends (prefixWord ++ tailWord_5593952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5593969 : List Nat := [1, 2, 2, 2, 1, 5, 2, 1, 3, 1, 3]
def baseStart_5593969 : Nat := 118140960795 + 5593969 * 2 ^ 59
def prefixEnd_5593969 : Nat := 4983230072969 + 3 ^ 40 * 5593969 * 2
def baseEnd_5593969 : Nat := 2872394863350929304261311

theorem tailTrace_5593969 : CollatzResearch.WordTrace tailWord_5593969 prefixEnd_5593969 2872394863350929304261311 := by
  unfold tailWord_5593969
  simp only [CollatzResearch.WordTrace]
  refine ⟨204028811071013161689112961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136019207380675441126075307 204028811071013161689112961)
  ·
    refine ⟨153021608303259871266834721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204028811071013161689112961 153021608303259871266834721)
    ·
      refine ⟨114766206227444903450126041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153021608303259871266834721 114766206227444903450126041)
      ·
        refine ⟨86074654670583677587594531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114766206227444903450126041 86074654670583677587594531)
        ·
          refine ⟨129111982005875516381391797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86074654670583677587594531 129111982005875516381391797)
          ·
            refine ⟨12104248313050829660755481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 129111982005875516381391797 12104248313050829660755481)
            ·
              refine ⟨9078186234788122245566611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12104248313050829660755481 9078186234788122245566611)
              ·
                refine ⟨13617279352182183368349917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9078186234788122245566611 13617279352182183368349917)
                ·
                  refine ⟨5106479757068318763131219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13617279352182183368349917 5106479757068318763131219)
                  ·
                    refine ⟨7659719635602478144696829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5106479757068318763131219 7659719635602478144696829)
                    ·
                      refine ⟨2872394863350929304261311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7659719635602478144696829 2872394863350929304261311)
                      ·
                        rfl

theorem cell23_5593969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2, 1, 3, 1, 3].length) (baseStart_5593969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5593969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5593969 prefixEnd_5593969 := by exact prefixLift 5593969
  have htrace : WordTrace (prefixWord ++ tailWord_5593969) baseStart_5593969 baseEnd_5593969 := by
    simpa [prefixWord, tailWord_5593969, baseEnd_5593969] using wordTrace_append hprefix tailTrace_5593969
  have hstable : (prefixWord ++ tailWord_5593969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5593969).length < 2 ^ (prefixWord ++ tailWord_5593969).sum := by decide
  have hdescent : baseEnd_5593969 < baseStart_5593969 := by decide
  rcases family_descends (prefixWord ++ tailWord_5593969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5593975 : List Nat := [1, 1, 3, 1, 1, 2, 1, 3, 5, 1, 4]
def baseStart_5593975 : Nat := 118140960795 + 5593975 * 2 ^ 59
def prefixEnd_5593975 : Nat := 4983230072969 + 3 ^ 40 * 5593975 * 2
def baseEnd_5593975 : Nat := 2872397944234856280786283

theorem tailTrace_5593975 : CollatzResearch.WordTrace tailWord_5593975 prefixEnd_5593975 2872397944234856280786283 := by
  unfold tailWord_5593975
  simp only [CollatzResearch.WordTrace]
  refine ⟨204029029908991424713831379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136019353272660949809220919 204029029908991424713831379)
  ·
    refine ⟨306043544863487137070747069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204029029908991424713831379 306043544863487137070747069)
    ·
      refine ⟨114766329323807676401530151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 306043544863487137070747069 114766329323807676401530151)
      ·
        refine ⟨172149493985711514602295227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114766329323807676401530151 172149493985711514602295227)
        ·
          refine ⟨258224240978567271903442841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172149493985711514602295227 258224240978567271903442841)
          ·
            refine ⟨193668180733925453927582131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 258224240978567271903442841 193668180733925453927582131)
            ·
              refine ⟨290502271100888180891373197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 193668180733925453927582131 290502271100888180891373197)
              ·
                refine ⟨108938351662833067834264949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 290502271100888180891373197 108938351662833067834264949)
                ·
                  refine ⟨10212970468390600109462339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 108938351662833067834264949 10212970468390600109462339)
                  ·
                    refine ⟨15319455702585900164193509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10212970468390600109462339 15319455702585900164193509)
                    ·
                      refine ⟨2872397944234856280786283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15319455702585900164193509 2872397944234856280786283)
                      ·
                        rfl

theorem cell23_5593975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 5, 1, 4].length) (baseStart_5593975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5593975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5593975 prefixEnd_5593975 := by exact prefixLift 5593975
  have htrace : WordTrace (prefixWord ++ tailWord_5593975) baseStart_5593975 baseEnd_5593975 := by
    simpa [prefixWord, tailWord_5593975, baseEnd_5593975] using wordTrace_append hprefix tailTrace_5593975
  have hstable : (prefixWord ++ tailWord_5593975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5593975).length < 2 ^ (prefixWord ++ tailWord_5593975).sum := by decide
  have hdescent : baseEnd_5593975 < baseStart_5593975 := by decide
  rcases family_descends (prefixWord ++ tailWord_5593975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5594015 : List Nat := [1, 1, 2, 5, 2, 1, 11]
def baseStart_5594015 : Nat := 118140960795 + 5594015 * 2 ^ 59
def prefixEnd_5594015 : Nat := 4983230072969 + 3 ^ 40 * 5594015 * 2
def baseEnd_5594015 : Nat := 35461956585938717583779

theorem tailTrace_5594015 : CollatzResearch.WordTrace tailWord_5594015 prefixEnd_5594015 35461956585938717583779 := by
  unfold tailWord_5594015
  simp only [CollatzResearch.WordTrace]
  refine ⟨204030488828846511545287499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136020325885897674363524999 204030488828846511545287499)
  ·
    refine ⟨306045733243269767317931249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204030488828846511545287499 306045733243269767317931249)
    ·
      refine ⟨229534299932452325488448437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 306045733243269767317931249 229534299932452325488448437)
      ·
        refine ⟨21518840618667405514542041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 229534299932452325488448437 21518840618667405514542041)
        ·
          refine ⟨16139130464000554135906531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21518840618667405514542041 16139130464000554135906531)
          ·
            refine ⟨24208695696000831203859797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16139130464000554135906531 24208695696000831203859797)
            ·
              refine ⟨35461956585938717583779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 24208695696000831203859797 35461956585938717583779)
              ·
                rfl

theorem cell23_5594015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 11].length) (baseStart_5594015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5594015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5594015 prefixEnd_5594015 := by exact prefixLift 5594015
  have htrace : WordTrace (prefixWord ++ tailWord_5594015) baseStart_5594015 baseEnd_5594015 := by
    simpa [prefixWord, tailWord_5594015, baseEnd_5594015] using wordTrace_append hprefix tailTrace_5594015
  have hstable : (prefixWord ++ tailWord_5594015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5594015).length < 2 ^ (prefixWord ++ tailWord_5594015).sum := by decide
  have hdescent : baseEnd_5594015 < baseStart_5594015 := by decide
  rcases family_descends (prefixWord ++ tailWord_5594015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5594042 : List Nat := [3, 1, 1, 1, 2, 1, 4, 3, 1, 3, 3]
def baseStart_5594042 : Nat := 118140960795 + 5594042 * 2 ^ 59
def prefixEnd_5594042 : Nat := 4983230072969 + 3 ^ 40 * 5594042 * 2
def baseEnd_5594042 : Nat := 2872432347438707518648475

theorem tailTrace_5594042 : CollatzResearch.WordTrace tailWord_5594042 prefixEnd_5594042 2872432347438707518648475 := by
  unfold tailWord_5594042
  simp only [CollatzResearch.WordTrace]
  refine ⟨51007868399937173789130095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136020982399832463437680253 51007868399937173789130095)
  ·
    refine ⟨76511802599905760683695143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51007868399937173789130095 76511802599905760683695143)
    ·
      refine ⟨114767703899858641025542715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76511802599905760683695143 114767703899858641025542715)
      ·
        refine ⟨172151555849787961538314073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114767703899858641025542715 172151555849787961538314073)
        ·
          refine ⟨129113666887340971153735555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172151555849787961538314073 129113666887340971153735555)
          ·
            refine ⟨193670500331011456730603333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129113666887340971153735555 193670500331011456730603333)
            ·
              refine ⟨36313218812064648136988125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 193670500331011456730603333 36313218812064648136988125)
              ·
                refine ⟨13617457054524243051370547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36313218812064648136988125 13617457054524243051370547)
                ·
                  refine ⟨20426185581786364577055821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13617457054524243051370547 20426185581786364577055821)
                  ·
                    refine ⟨7659819593169886716395933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20426185581786364577055821 7659819593169886716395933)
                    ·
                      refine ⟨2872432347438707518648475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7659819593169886716395933 2872432347438707518648475)
                      ·
                        rfl

theorem cell23_5594042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 3, 1, 3, 3].length) (baseStart_5594042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5594042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5594042 prefixEnd_5594042 := by exact prefixLift 5594042
  have htrace : WordTrace (prefixWord ++ tailWord_5594042) baseStart_5594042 baseEnd_5594042 := by
    simpa [prefixWord, tailWord_5594042, baseEnd_5594042] using wordTrace_append hprefix tailTrace_5594042
  have hstable : (prefixWord ++ tailWord_5594042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5594042).length < 2 ^ (prefixWord ++ tailWord_5594042).sum := by decide
  have hdescent : baseEnd_5594042 < baseStart_5594042 := by decide
  rcases family_descends (prefixWord ++ tailWord_5594042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5594055 : List Nat := [1, 1, 4, 1, 1, 2, 2, 1, 1, 4, 5]
def baseStart_5594055 : Nat := 118140960795 + 5594055 * 2 ^ 59
def prefixEnd_5594055 : Nat := 4983230072969 + 3 ^ 40 * 5594055 * 2
def baseEnd_5594055 : Nat := 2872439022687215967785915

theorem tailTrace_5594055 : CollatzResearch.WordTrace tailWord_5594055 prefixEnd_5594055 2872439022687215967785915 := by
  unfold tailWord_5594055
  simp only [CollatzResearch.WordTrace]
  refine ⟨204031947748701598376743619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136021298499134398917829079 204031947748701598376743619)
  ·
    refine ⟨306047921623052397565115429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204031947748701598376743619 306047921623052397565115429)
    ·
      refine ⟨57383985304322324543459143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 306047921623052397565115429 57383985304322324543459143)
      ·
        refine ⟨86075977956483486815188715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57383985304322324543459143 86075977956483486815188715)
        ·
          refine ⟨129113966934725230222783073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86075977956483486815188715 129113966934725230222783073)
          ·
            refine ⟨96835475201043922667087305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129113966934725230222783073 96835475201043922667087305)
            ·
              refine ⟨72626606400782942000315479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96835475201043922667087305 72626606400782942000315479)
              ·
                refine ⟨108939909601174413000473219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72626606400782942000315479 108939909601174413000473219)
                ·
                  refine ⟨163409864401761619500709829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 108939909601174413000473219 163409864401761619500709829)
                  ·
                    refine ⟨30639349575330303656383093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 163409864401761619500709829 30639349575330303656383093)
                    ·
                      refine ⟨2872439022687215967785915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30639349575330303656383093 2872439022687215967785915)
                      ·
                        rfl

theorem cell23_5594055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 4, 5].length) (baseStart_5594055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5594055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5594055 prefixEnd_5594055 := by exact prefixLift 5594055
  have htrace : WordTrace (prefixWord ++ tailWord_5594055) baseStart_5594055 baseEnd_5594055 := by
    simpa [prefixWord, tailWord_5594055, baseEnd_5594055] using wordTrace_append hprefix tailTrace_5594055
  have hstable : (prefixWord ++ tailWord_5594055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5594055).length < 2 ^ (prefixWord ++ tailWord_5594055).sum := by decide
  have hdescent : baseEnd_5594055 < baseStart_5594055 := by decide
  rcases family_descends (prefixWord ++ tailWord_5594055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5594077 : List Nat := [1, 4, 3, 1, 2, 3, 2, 2, 1, 2, 2]
def baseStart_5594077 : Nat := 118140960795 + 5594077 * 2 ^ 59
def prefixEnd_5594077 : Nat := 4983230072969 + 3 ^ 40 * 5594077 * 2
def baseEnd_5594077 : Nat := 2872450319261614881710815

theorem tailTrace_5594077 : CollatzResearch.WordTrace tailWord_5594077 prefixEnd_5594077 2872450319261614881710815 := by
  unfold tailWord_5594077
  simp only [CollatzResearch.WordTrace]
  refine ⟨204032750154621896134044485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136021833436414597422696323 204032750154621896134044485)
  ·
    refine ⟨38256140653991605525133341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 204032750154621896134044485 38256140653991605525133341)
    ·
      refine ⟨14346052745246852071925003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38256140653991605525133341 14346052745246852071925003)
      ·
        refine ⟨21519079117870278107887505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14346052745246852071925003 21519079117870278107887505)
        ·
          refine ⟨16139309338402708580915629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21519079117870278107887505 16139309338402708580915629)
          ·
            refine ⟨6052241001901015717843361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16139309338402708580915629 6052241001901015717843361)
            ·
              refine ⟨4539180751425761788382521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6052241001901015717843361 4539180751425761788382521)
              ·
                refine ⟨3404385563569321341286891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4539180751425761788382521 3404385563569321341286891)
                ·
                  refine ⟨5106578345353982011930337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3404385563569321341286891 5106578345353982011930337)
                  ·
                    refine ⟨3829933759015486508947753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5106578345353982011930337 3829933759015486508947753)
                    ·
                      refine ⟨2872450319261614881710815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3829933759015486508947753 2872450319261614881710815)
                      ·
                        rfl

theorem cell23_5594077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 2, 2, 1, 2, 2].length) (baseStart_5594077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5594077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5594077 prefixEnd_5594077 := by exact prefixLift 5594077
  have htrace : WordTrace (prefixWord ++ tailWord_5594077) baseStart_5594077 baseEnd_5594077 := by
    simpa [prefixWord, tailWord_5594077, baseEnd_5594077] using wordTrace_append hprefix tailTrace_5594077
  have hstable : (prefixWord ++ tailWord_5594077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5594077).length < 2 ^ (prefixWord ++ tailWord_5594077).sum := by decide
  have hdescent : baseEnd_5594077 < baseStart_5594077 := by decide
  rcases family_descends (prefixWord ++ tailWord_5594077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5594099 : List Nat := [1, 1, 1, 2, 2, 2, 1, 1, 8, 2, 2]
def baseStart_5594099 : Nat := 118140960795 + 5594099 * 2 ^ 59
def prefixEnd_5594099 : Nat := 4983230072969 + 3 ^ 40 * 5594099 * 2
def baseEnd_5594099 : Nat := 2872461615836013795635713

theorem tailTrace_5594099 : CollatzResearch.WordTrace tailWord_5594099 prefixEnd_5594099 2872461615836013795635713 := by
  unfold tailWord_5594099
  simp only [CollatzResearch.WordTrace]
  refine ⟨204033552560542193891345351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136022368373694795927563567 204033552560542193891345351)
  ·
    refine ⟨306050328840813290837018027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204033552560542193891345351 306050328840813290837018027)
    ·
      refine ⟨459075493261219936255527041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 306050328840813290837018027 459075493261219936255527041)
      ·
        refine ⟨344306619945914952191645281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 459075493261219936255527041 344306619945914952191645281)
        ·
          refine ⟨258229964959436214143733961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 344306619945914952191645281 258229964959436214143733961)
          ·
            refine ⟨193672473719577160607800471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 258229964959436214143733961 193672473719577160607800471)
            ·
              refine ⟨290508710579365740911700707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 193672473719577160607800471 290508710579365740911700707)
              ·
                refine ⟨435763065869048611367551061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 290508710579365740911700707 435763065869048611367551061)
                ·
                  refine ⟨5106598428152913414463489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 435763065869048611367551061 5106598428152913414463489)
                  ·
                    refine ⟨3829948821114685060847617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5106598428152913414463489 3829948821114685060847617)
                    ·
                      refine ⟨2872461615836013795635713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3829948821114685060847617 2872461615836013795635713)
                      ·
                        rfl

theorem cell23_5594099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 8, 2, 2].length) (baseStart_5594099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5594099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5594099 prefixEnd_5594099 := by exact prefixLift 5594099
  have htrace : WordTrace (prefixWord ++ tailWord_5594099) baseStart_5594099 baseEnd_5594099 := by
    simpa [prefixWord, tailWord_5594099, baseEnd_5594099] using wordTrace_append hprefix tailTrace_5594099
  have hstable : (prefixWord ++ tailWord_5594099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5594099).length < 2 ^ (prefixWord ++ tailWord_5594099).sum := by decide
  have hdescent : baseEnd_5594099 < baseStart_5594099 := by decide
  rcases family_descends (prefixWord ++ tailWord_5594099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5594100 : List Nat := [2, 6, 2, 1, 1, 1, 3, 7]
def baseStart_5594100 : Nat := 118140960795 + 5594100 * 2 ^ 59
def prefixEnd_5594100 : Nat := 4983230072969 + 3 ^ 40 * 5594100 * 2
def baseEnd_5594100 : Nat := 106387486270987714508267

theorem tailTrace_5594100 : CollatzResearch.WordTrace tailWord_5594100 prefixEnd_5594100 106387486270987714508267 := by
  unfold tailWord_5594100
  simp only [CollatzResearch.WordTrace]
  refine ⟨102016794516769285531065877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136022392689025714041421169 102016794516769285531065877)
  ·
    refine ⟨4782037242973560259268713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 102016794516769285531065877 4782037242973560259268713)
    ·
      refine ⟨3586527932230170194451535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4782037242973560259268713 3586527932230170194451535)
      ·
        refine ⟨5379791898345255291677303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3586527932230170194451535 5379791898345255291677303)
        ·
          refine ⟨8069687847517882937515955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5379791898345255291677303 8069687847517882937515955)
          ·
            refine ⟨12104531771276824406273933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8069687847517882937515955 12104531771276824406273933)
            ·
              refine ⟨4539199414228809152352725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12104531771276824406273933 4539199414228809152352725)
              ·
                refine ⟨106387486270987714508267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4539199414228809152352725 106387486270987714508267)
                ·
                  rfl

theorem cell23_5594100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 3, 7].length) (baseStart_5594100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5594100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5594100 prefixEnd_5594100 := by exact prefixLift 5594100
  have htrace : WordTrace (prefixWord ++ tailWord_5594100) baseStart_5594100 baseEnd_5594100 := by
    simpa [prefixWord, tailWord_5594100, baseEnd_5594100] using wordTrace_append hprefix tailTrace_5594100
  have hstable : (prefixWord ++ tailWord_5594100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5594100).length < 2 ^ (prefixWord ++ tailWord_5594100).sum := by decide
  have hdescent : baseEnd_5594100 < baseStart_5594100 := by decide
  rcases family_descends (prefixWord ++ tailWord_5594100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5594115 : List Nat := [1, 1, 1, 3, 2, 1, 1, 1, 3, 2, 7]
def baseStart_5594115 : Nat := 118140960795 + 5594115 * 2 ^ 59
def prefixEnd_5594115 : Nat := 4983230072969 + 3 ^ 40 * 5594115 * 2
def baseEnd_5594115 : Nat := 2872469831526485733035639

theorem tailTrace_5594115 : CollatzResearch.WordTrace tailWord_5594115 prefixEnd_5594115 2872469831526485733035639 := by
  unfold tailWord_5594115
  simp only [CollatzResearch.WordTrace]
  refine ⟨204034136128484228623927799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136022757418989485749285199 204034136128484228623927799)
  ·
    refine ⟨306051204192726342935891699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204034136128484228623927799 306051204192726342935891699)
    ·
      refine ⟨459076806289089514403837549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 306051204192726342935891699 459076806289089514403837549)
      ·
        refine ⟨172153802358408567901439081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 459076806289089514403837549 172153802358408567901439081)
        ·
          refine ⟨129115351768806425926079311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172153802358408567901439081 129115351768806425926079311)
          ·
            refine ⟨193673027653209638889118967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129115351768806425926079311 193673027653209638889118967)
            ·
              refine ⟨290509541479814458333678451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 193673027653209638889118967 290509541479814458333678451)
              ·
                refine ⟨435764312219721687500517677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 290509541479814458333678451 435764312219721687500517677)
                ·
                  refine ⟨163411617082395632812694129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 435764312219721687500517677 163411617082395632812694129)
                  ·
                    refine ⟨122558712811796724609520597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 163411617082395632812694129 122558712811796724609520597)
                    ·
                      refine ⟨2872469831526485733035639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 122558712811796724609520597 2872469831526485733035639)
                      ·
                        rfl

theorem cell23_5594115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 2, 7].length) (baseStart_5594115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5594115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5594115 prefixEnd_5594115 := by exact prefixLift 5594115
  have htrace : WordTrace (prefixWord ++ tailWord_5594115) baseStart_5594115 baseEnd_5594115 := by
    simpa [prefixWord, tailWord_5594115, baseEnd_5594115] using wordTrace_append hprefix tailTrace_5594115
  have hstable : (prefixWord ++ tailWord_5594115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5594115).length < 2 ^ (prefixWord ++ tailWord_5594115).sum := by decide
  have hdescent : baseEnd_5594115 < baseStart_5594115 := by decide
  rcases family_descends (prefixWord ++ tailWord_5594115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5594133 : List Nat := [1, 3, 2, 1, 4, 1, 3, 2, 2, 2, 2]
def baseStart_5594133 : Nat := 118140960795 + 5594133 * 2 ^ 59
def prefixEnd_5594133 : Nat := 4983230072969 + 3 ^ 40 * 5594133 * 2
def baseEnd_5594133 : Nat := 2872479074178266662610557

theorem tailTrace_5594133 : CollatzResearch.WordTrace tailWord_5594133 prefixEnd_5594133 2872479074178266662610557 := by
  unfold tailWord_5594133
  simp only [CollatzResearch.WordTrace]
  refine ⟨204034792642419017698083053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136023195094946011798722035 204034792642419017698083053)
  ·
    refine ⟨76513047240907131636781145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 204034792642419017698083053 76513047240907131636781145)
    ·
      refine ⟨57384785430680348727585859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76513047240907131636781145 57384785430680348727585859)
      ·
        refine ⟨86077178146020523091378789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57384785430680348727585859 86077178146020523091378789)
        ·
          refine ⟨16139470902378848079633523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 86077178146020523091378789 16139470902378848079633523)
          ·
            refine ⟨24209206353568272119450285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16139470902378848079633523 24209206353568272119450285)
            ·
              refine ⟨9078452382588102044793857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24209206353568272119450285 9078452382588102044793857)
              ·
                refine ⟨6808839286941076533595393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9078452382588102044793857 6808839286941076533595393)
                ·
                  refine ⟨5106629465205807400196545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6808839286941076533595393 5106629465205807400196545)
                  ·
                    refine ⟨3829972098904355550147409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5106629465205807400196545 3829972098904355550147409)
                    ·
                      refine ⟨2872479074178266662610557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3829972098904355550147409 2872479074178266662610557)
                      ·
                        rfl

theorem cell23_5594133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3, 2, 2, 2, 2].length) (baseStart_5594133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5594133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5594133 prefixEnd_5594133 := by exact prefixLift 5594133
  have htrace : WordTrace (prefixWord ++ tailWord_5594133) baseStart_5594133 baseEnd_5594133 := by
    simpa [prefixWord, tailWord_5594133, baseEnd_5594133] using wordTrace_append hprefix tailTrace_5594133
  have hstable : (prefixWord ++ tailWord_5594133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5594133).length < 2 ^ (prefixWord ++ tailWord_5594133).sum := by decide
  have hdescent : baseEnd_5594133 < baseStart_5594133 := by decide
  rcases family_descends (prefixWord ++ tailWord_5594133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5594202 : List Nat := [3, 1, 1, 2, 1, 1, 2, 2, 2, 4, 4]
def baseStart_5594202 : Nat := 118140960795 + 5594202 * 2 ^ 59
def prefixEnd_5594202 : Nat := 4983230072969 + 3 ^ 40 * 5594202 * 2
def baseEnd_5594202 : Nat := 2872514504343426892647739

theorem tailTrace_5594202 : CollatzResearch.WordTrace tailWord_5594202 prefixEnd_5594202 2872514504343426892647739 := by
  unfold tailWord_5594202
  simp only [CollatzResearch.WordTrace]
  refine ⟨51009327319792260620586215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136024872852779361654896573 51009327319792260620586215)
  ·
    refine ⟨76513990979688390930879323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51009327319792260620586215 76513990979688390930879323)
    ·
      refine ⟨114770986469532586396318985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76513990979688390930879323 114770986469532586396318985)
      ·
        refine ⟨86078239852149439797239239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114770986469532586396318985 86078239852149439797239239)
        ·
          refine ⟨129117359778224159695858859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86078239852149439797239239 129117359778224159695858859)
          ·
            refine ⟨193676039667336239543788289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129117359778224159695858859 193676039667336239543788289)
            ·
              refine ⟨145257029750502179657841217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 193676039667336239543788289 145257029750502179657841217)
              ·
                refine ⟨108942772312876634743380913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 145257029750502179657841217 108942772312876634743380913)
                ·
                  refine ⟨81707079234657476057535685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 108942772312876634743380913 81707079234657476057535685)
                  ·
                    refine ⟨15320077356498276760787941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 81707079234657476057535685 15320077356498276760787941)
                    ·
                      refine ⟨2872514504343426892647739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15320077356498276760787941 2872514504343426892647739)
                      ·
                        rfl

theorem cell23_5594202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 2, 4, 4].length) (baseStart_5594202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5594202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5594202 prefixEnd_5594202 := by exact prefixLift 5594202
  have htrace : WordTrace (prefixWord ++ tailWord_5594202) baseStart_5594202 baseEnd_5594202 := by
    simpa [prefixWord, tailWord_5594202, baseEnd_5594202] using wordTrace_append hprefix tailTrace_5594202
  have hstable : (prefixWord ++ tailWord_5594202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5594202).length < 2 ^ (prefixWord ++ tailWord_5594202).sum := by decide
  have hdescent : baseEnd_5594202 < baseStart_5594202 := by decide
  rcases family_descends (prefixWord ++ tailWord_5594202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5594226 : List Nat := [3, 2, 1, 2, 2, 1, 4, 1, 2, 2, 3]
def baseStart_5594226 : Nat := 118140960795 + 5594226 * 2 ^ 59
def prefixEnd_5594226 : Nat := 4983230072969 + 3 ^ 40 * 5594226 * 2
def baseEnd_5594226 : Nat := 2872526827879134798747629

theorem tailTrace_5594226 : CollatzResearch.WordTrace tailWord_5594226 prefixEnd_5594226 2872526827879134798747629 := by
  unfold tailWord_5594226
  simp only [CollatzResearch.WordTrace]
  refine ⟨51009546157770523645304633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136025456420721396387479021 51009546157770523645304633)
  ·
    refine ⟨38257159618327892733978475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51009546157770523645304633 38257159618327892733978475)
    ·
      refine ⟨57385739427491839100967713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38257159618327892733978475 57385739427491839100967713)
      ·
        refine ⟨43039304570618879325725785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57385739427491839100967713 43039304570618879325725785)
        ·
          refine ⟨32279478427964159494294339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43039304570618879325725785 32279478427964159494294339)
          ·
            refine ⟨48419217641946239241441509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32279478427964159494294339 48419217641946239241441509)
            ·
              refine ⟨9078603307864919857770283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48419217641946239241441509 9078603307864919857770283)
              ·
                refine ⟨13617904961797379786655425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9078603307864919857770283 13617904961797379786655425)
                ·
                  refine ⟨10213428721348034839991569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13617904961797379786655425 10213428721348034839991569)
                  ·
                    refine ⟨7660071541011026129993677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10213428721348034839991569 7660071541011026129993677)
                    ·
                      refine ⟨2872526827879134798747629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7660071541011026129993677 2872526827879134798747629)
                      ·
                        rfl

theorem cell23_5594226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4, 1, 2, 2, 3].length) (baseStart_5594226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5594226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5594226 prefixEnd_5594226 := by exact prefixLift 5594226
  have htrace : WordTrace (prefixWord ++ tailWord_5594226) baseStart_5594226 baseEnd_5594226 := by
    simpa [prefixWord, tailWord_5594226, baseEnd_5594226] using wordTrace_append hprefix tailTrace_5594226
  have hstable : (prefixWord ++ tailWord_5594226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5594226).length < 2 ^ (prefixWord ++ tailWord_5594226).sum := by decide
  have hdescent : baseEnd_5594226 < baseStart_5594226 := by decide
  rcases family_descends (prefixWord ++ tailWord_5594226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5594252 : List Nat := [2, 2, 1, 2, 1, 1, 1, 2, 2, 4, 5]
def baseStart_5594252 : Nat := 118140960795 + 5594252 * 2 ^ 59
def prefixEnd_5594252 : Nat := 4983230072969 + 3 ^ 40 * 5594252 * 2
def baseEnd_5594252 : Nat := 2872540178376151697022509

theorem tailTrace_5594252 : CollatzResearch.WordTrace tailWord_5594252 prefixEnd_5594252 2872540178376151697022509 := by
  unfold tailWord_5594252
  simp only [CollatzResearch.WordTrace]
  refine ⟨102019566464493950510832505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136026088619325267347776673 102019566464493950510832505)
  ·
    refine ⟨76514674848370462883124379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102019566464493950510832505 76514674848370462883124379)
    ·
      refine ⟨114772012272555694324686569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76514674848370462883124379 114772012272555694324686569)
      ·
        refine ⟨86079009204416770743514927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114772012272555694324686569 86079009204416770743514927)
        ·
          refine ⟨129118513806625156115272391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86079009204416770743514927 129118513806625156115272391)
          ·
            refine ⟨193677770709937734172908587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129118513806625156115272391 193677770709937734172908587)
            ·
              refine ⟨290516656064906601259362881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 193677770709937734172908587 290516656064906601259362881)
              ·
                refine ⟨217887492048679950944522161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 290516656064906601259362881 217887492048679950944522161)
                ·
                  refine ⟨163415619036509963208391621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 217887492048679950944522161 163415619036509963208391621)
                  ·
                    refine ⟨30640428569345618101573429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 163415619036509963208391621 30640428569345618101573429)
                    ·
                      refine ⟨2872540178376151697022509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30640428569345618101573429 2872540178376151697022509)
                      ·
                        rfl

theorem cell23_5594252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 4, 5].length) (baseStart_5594252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5594252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5594252 prefixEnd_5594252 := by exact prefixLift 5594252
  have htrace : WordTrace (prefixWord ++ tailWord_5594252) baseStart_5594252 baseEnd_5594252 := by
    simpa [prefixWord, tailWord_5594252, baseEnd_5594252] using wordTrace_append hprefix tailTrace_5594252
  have hstable : (prefixWord ++ tailWord_5594252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5594252).length < 2 ^ (prefixWord ++ tailWord_5594252).sum := by decide
  have hdescent : baseEnd_5594252 < baseStart_5594252 := by decide
  rcases family_descends (prefixWord ++ tailWord_5594252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5594290 : List Nat := [3, 2, 1, 1, 1, 5, 2, 3, 1, 1, 3]
def baseStart_5594290 : Nat := 118140960795 + 5594290 * 2 ^ 59
def prefixEnd_5594290 : Nat := 4983230072969 + 3 ^ 40 * 5594290 * 2
def baseEnd_5594290 : Nat := 2872559690641022548347335

theorem tailTrace_5594290 : CollatzResearch.WordTrace tailWord_5594290 prefixEnd_5594290 2872559690641022548347335 := by
  unfold tailWord_5594290
  simp only [CollatzResearch.WordTrace]
  refine ⟨51010129725712558377887081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136027012601900155674365549 51010129725712558377887081)
  ·
    refine ⟨38257597294284418783415311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51010129725712558377887081 38257597294284418783415311)
    ·
      refine ⟨57386395941426628175122967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38257597294284418783415311 57386395941426628175122967)
      ·
        refine ⟨86079593912139942262684451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57386395941426628175122967 86079593912139942262684451)
        ·
          refine ⟨129119390868209913394026677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86079593912139942262684451 129119390868209913394026677)
          ·
            refine ⟨12104942893894679380690001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 129119390868209913394026677 12104942893894679380690001)
            ·
              refine ⟨9078707170421009535517501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12104942893894679380690001 9078707170421009535517501)
              ·
                refine ⟨3404515188907878575819063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9078707170421009535517501 3404515188907878575819063)
                ·
                  refine ⟨5106772783361817863728595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3404515188907878575819063 5106772783361817863728595)
                  ·
                    refine ⟨7660159175042726795592893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5106772783361817863728595 7660159175042726795592893)
                    ·
                      refine ⟨2872559690641022548347335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7660159175042726795592893 2872559690641022548347335)
                      ·
                        rfl

theorem cell23_5594290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2, 3, 1, 1, 3].length) (baseStart_5594290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5594290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5594290 prefixEnd_5594290 := by exact prefixLift 5594290
  have htrace : WordTrace (prefixWord ++ tailWord_5594290) baseStart_5594290 baseEnd_5594290 := by
    simpa [prefixWord, tailWord_5594290, baseEnd_5594290] using wordTrace_append hprefix tailTrace_5594290
  have hstable : (prefixWord ++ tailWord_5594290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5594290).length < 2 ^ (prefixWord ++ tailWord_5594290).sum := by decide
  have hdescent : baseEnd_5594290 < baseStart_5594290 := by decide
  rcases family_descends (prefixWord ++ tailWord_5594290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5594299 : List Nat := [1, 1, 1, 1, 1, 2, 4, 2, 5, 2, 3]
def baseStart_5594299 : Nat := 118140960795 + 5594299 * 2 ^ 59
def prefixEnd_5594299 : Nat := 4983230072969 + 3 ^ 40 * 5594299 * 2
def baseEnd_5594299 : Nat := 2872564311966913013134793

theorem tailTrace_5594299 : CollatzResearch.WordTrace tailWord_5594299 prefixEnd_5594299 2872564311966913013134793 := by
  unfold tailWord_5594299
  simp only [CollatzResearch.WordTrace]
  refine ⟨204040847159817628048625951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136027231439878418699083967 204040847159817628048625951)
  ·
    refine ⟨306061270739726442072938927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204040847159817628048625951 306061270739726442072938927)
    ·
      refine ⟨459091906109589663109408391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 306061270739726442072938927 459091906109589663109408391)
      ·
        refine ⟨688637859164384494664112587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 459091906109589663109408391 688637859164384494664112587)
        ·
          refine ⟨1032956788746576741996168881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 688637859164384494664112587 1032956788746576741996168881)
          ·
            refine ⟨774717591559932556497126661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1032956788746576741996168881 774717591559932556497126661)
            ·
              refine ⟨145259548417487354343211249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 774717591559932556497126661 145259548417487354343211249)
              ·
                refine ⟨108944661313115515757408437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 145259548417487354343211249 108944661313115515757408437)
                ·
                  refine ⟨10213561998104579602257041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 108944661313115515757408437 10213561998104579602257041)
                  ·
                    refine ⟨7660171498578434701692781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10213561998104579602257041 7660171498578434701692781)
                    ·
                      refine ⟨2872564311966913013134793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7660171498578434701692781 2872564311966913013134793)
                      ·
                        rfl

theorem cell23_5594299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 5, 2, 3].length) (baseStart_5594299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5594299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5594299 prefixEnd_5594299 := by exact prefixLift 5594299
  have htrace : WordTrace (prefixWord ++ tailWord_5594299) baseStart_5594299 baseEnd_5594299 := by
    simpa [prefixWord, tailWord_5594299, baseEnd_5594299] using wordTrace_append hprefix tailTrace_5594299
  have hstable : (prefixWord ++ tailWord_5594299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5594299).length < 2 ^ (prefixWord ++ tailWord_5594299).sum := by decide
  have hdescent : baseEnd_5594299 < baseStart_5594299 := by decide
  rcases family_descends (prefixWord ++ tailWord_5594299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5594336 : List Nat := [2, 1, 1, 3, 1, 6, 2, 7]
def baseStart_5594336 : Nat := 118140960795 + 5594336 * 2 ^ 59
def prefixEnd_5594336 : Nat := 4983230072969 + 3 ^ 40 * 5594336 * 2
def baseEnd_5594336 : Nat := 106391974472264050680449

theorem tailTrace_5594336 : CollatzResearch.WordTrace tailWord_5594336 prefixEnd_5594336 106391974472264050680449 := by
  unfold tailWord_5594336
  simp only [CollatzResearch.WordTrace]
  refine ⟨102021098330341791683861431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136028131107122388911815241 102021098330341791683861431)
  ·
    refine ⟨153031647495512687525792147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102021098330341791683861431 153031647495512687525792147)
    ·
      refine ⟨229547471243269031288688221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153031647495512687525792147 229547471243269031288688221)
      ·
        refine ⟨86080301716225886733258083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 229547471243269031288688221 86080301716225886733258083)
        ·
          refine ⟨129120452574338830099887125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86080301716225886733258083 129120452574338830099887125)
          ·
            refine ⟨6052521214422132660932209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 129120452574338830099887125 6052521214422132660932209)
            ·
              refine ⟨4539390910816599495699157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6052521214422132660932209 4539390910816599495699157)
              ·
                refine ⟨106391974472264050680449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4539390910816599495699157 106391974472264050680449)
                ·
                  rfl

theorem cell23_5594336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 2, 7].length) (baseStart_5594336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5594336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5594336 prefixEnd_5594336 := by exact prefixLift 5594336
  have htrace : WordTrace (prefixWord ++ tailWord_5594336) baseStart_5594336 baseEnd_5594336 := by
    simpa [prefixWord, tailWord_5594336, baseEnd_5594336] using wordTrace_append hprefix tailTrace_5594336
  have hstable : (prefixWord ++ tailWord_5594336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5594336).length < 2 ^ (prefixWord ++ tailWord_5594336).sum := by decide
  have hdescent : baseEnd_5594336 < baseStart_5594336 := by decide
  rcases family_descends (prefixWord ++ tailWord_5594336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5594347 : List Nat := [1, 1, 1, 1, 2, 8, 1, 3, 1, 2, 2]
def baseStart_5594347 : Nat := 118140960795 + 5594347 * 2 ^ 59
def prefixEnd_5594347 : Nat := 4983230072969 + 3 ^ 40 * 5594347 * 2
def baseEnd_5594347 : Nat := 2872588959038328825334573

theorem tailTrace_5594347 : CollatzResearch.WordTrace tailWord_5594347 prefixEnd_5594347 2872588959038328825334573 := by
  unfold tailWord_5594347
  simp only [CollatzResearch.WordTrace]
  refine ⟨204042597863643732246373295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136028398575762488164248863 204042597863643732246373295)
  ·
    refine ⟨306063896795465598369559943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204042597863643732246373295 306063896795465598369559943)
    ·
      refine ⟨459095845193198397554339915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 306063896795465598369559943 459095845193198397554339915)
      ·
        refine ⟨688643767789797596331509873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 459095845193198397554339915 688643767789797596331509873)
        ·
          refine ⟨516482825842348197248632405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 688643767789797596331509873 516482825842348197248632405)
          ·
            refine ⟨6052533115340017936507411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 516482825842348197248632405 6052533115340017936507411)
            ·
              refine ⟨9078799673010026904761117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6052533115340017936507411 9078799673010026904761117)
              ·
                refine ⟨3404549877378760089285419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9078799673010026904761117 3404549877378760089285419)
                ·
                  refine ⟨5106824816068140133928129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3404549877378760089285419 5106824816068140133928129)
                  ·
                    refine ⟨3830118612051105100446097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5106824816068140133928129 3830118612051105100446097)
                    ·
                      refine ⟨2872588959038328825334573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3830118612051105100446097 2872588959038328825334573)
                      ·
                        rfl

theorem cell23_5594347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 1, 3, 1, 2, 2].length) (baseStart_5594347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5594347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5594347 prefixEnd_5594347 := by exact prefixLift 5594347
  have htrace : WordTrace (prefixWord ++ tailWord_5594347) baseStart_5594347 baseEnd_5594347 := by
    simpa [prefixWord, tailWord_5594347, baseEnd_5594347] using wordTrace_append hprefix tailTrace_5594347
  have hstable : (prefixWord ++ tailWord_5594347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5594347).length < 2 ^ (prefixWord ++ tailWord_5594347).sum := by decide
  have hdescent : baseEnd_5594347 < baseStart_5594347 := by decide
  rcases family_descends (prefixWord ++ tailWord_5594347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5594364 : List Nat := [2, 2, 2, 1, 5, 1, 3, 2, 1, 2, 2]
def baseStart_5594364 : Nat := 118140960795 + 5594364 * 2 ^ 59
def prefixEnd_5594364 : Nat := 4983230072969 + 3 ^ 40 * 5594364 * 2
def baseEnd_5594364 : Nat := 2872597688209455258821995

theorem tailTrace_5594364 : CollatzResearch.WordTrace tailWord_5594364 prefixEnd_5594364 2872597688209455258821995 := by
  unfold tailWord_5594364
  simp only [CollatzResearch.WordTrace]
  refine ⟨102021608952291072074871073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136028811936388096099828097 102021608952291072074871073)
  ·
    refine ⟨76516206714218304056153305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102021608952291072074871073 76516206714218304056153305)
    ·
      refine ⟨57387155035663728042114979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76516206714218304056153305 57387155035663728042114979)
      ·
        refine ⟨86080732553495592063172469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57387155035663728042114979 86080732553495592063172469)
        ·
          refine ⟨8070068676890211755922419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 86080732553495592063172469 8070068676890211755922419)
          ·
            refine ⟨12105103015335317633883629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8070068676890211755922419 12105103015335317633883629)
            ·
              refine ⟨4539413630750744112706361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12105103015335317633883629 4539413630750744112706361)
              ·
                refine ⟨3404560223063058084529771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4539413630750744112706361 3404560223063058084529771)
                ·
                  refine ⟨5106840334594587126794657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3404560223063058084529771 5106840334594587126794657)
                  ·
                    refine ⟨3830130250945940345095993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5106840334594587126794657 3830130250945940345095993)
                    ·
                      refine ⟨2872597688209455258821995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3830130250945940345095993 2872597688209455258821995)
                      ·
                        rfl

theorem cell23_5594364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 3, 2, 1, 2, 2].length) (baseStart_5594364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5594364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5594364 prefixEnd_5594364 := by exact prefixLift 5594364
  have htrace : WordTrace (prefixWord ++ tailWord_5594364) baseStart_5594364 baseEnd_5594364 := by
    simpa [prefixWord, tailWord_5594364, baseEnd_5594364] using wordTrace_append hprefix tailTrace_5594364
  have hstable : (prefixWord ++ tailWord_5594364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5594364).length < 2 ^ (prefixWord ++ tailWord_5594364).sum := by decide
  have hdescent : baseEnd_5594364 < baseStart_5594364 := by decide
  rcases family_descends (prefixWord ++ tailWord_5594364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5594380 : List Nat := [2, 2, 1, 2, 2, 3, 4, 1, 2, 1, 3]
def baseStart_5594380 : Nat := 118140960795 + 5594380 * 2 ^ 59
def prefixEnd_5594380 : Nat := 4983230072969 + 3 ^ 40 * 5594380 * 2
def baseEnd_5594380 : Nat := 2872605903899927196221921

theorem tailTrace_5594380 : CollatzResearch.WordTrace tailWord_5594380 prefixEnd_5594380 2872605903899927196221921 := by
  unfold tailWord_5594380
  simp only [CollatzResearch.WordTrace]
  refine ⟨102021900736262089441162297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136029200981682785921549729 102021900736262089441162297)
  ·
    refine ⟨76516425552196567080871723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102021900736262089441162297 76516425552196567080871723)
    ·
      refine ⟨114774638328294850621307585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76516425552196567080871723 114774638328294850621307585)
      ·
        refine ⟨86080978746221137965980689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114774638328294850621307585 86080978746221137965980689)
        ·
          refine ⟨64560734059665853474485517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86080978746221137965980689 64560734059665853474485517)
          ·
            refine ⟨24210275272374695052932069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64560734059665853474485517 24210275272374695052932069)
            ·
              refine ⟨4539426613570255322424763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24210275272374695052932069 4539426613570255322424763)
              ·
                refine ⟨6809139920355382983637145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4539426613570255322424763 6809139920355382983637145)
                ·
                  refine ⟨5106854940266537237727859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6809139920355382983637145 5106854940266537237727859)
                  ·
                    refine ⟨7660282410399805856591789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5106854940266537237727859 7660282410399805856591789)
                    ·
                      refine ⟨2872605903899927196221921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7660282410399805856591789 2872605903899927196221921)
                      ·
                        rfl

theorem cell23_5594380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 4, 1, 2, 1, 3].length) (baseStart_5594380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5594380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5594380 prefixEnd_5594380 := by exact prefixLift 5594380
  have htrace : WordTrace (prefixWord ++ tailWord_5594380) baseStart_5594380 baseEnd_5594380 := by
    simpa [prefixWord, tailWord_5594380, baseEnd_5594380] using wordTrace_append hprefix tailTrace_5594380
  have hstable : (prefixWord ++ tailWord_5594380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5594380).length < 2 ^ (prefixWord ++ tailWord_5594380).sum := by decide
  have hdescent : baseEnd_5594380 < baseStart_5594380 := by decide
  rcases family_descends (prefixWord ++ tailWord_5594380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5594403 : List Nat := [1, 1, 1, 4, 2, 4, 1, 2, 1, 4, 2]
def baseStart_5594403 : Nat := 118140960795 + 5594403 * 2 ^ 59
def prefixEnd_5594403 : Nat := 4983230072969 + 3 ^ 40 * 5594403 * 2
def baseEnd_5594403 : Nat := 2872617713954980606234315

theorem tailTrace_5594403 : CollatzResearch.WordTrace tailWord_5594403 prefixEnd_5594403 2872617713954980606234315 := by
  unfold tailWord_5594403
  simp only [CollatzResearch.WordTrace]
  refine ⟨204044640351440853810411863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136029760234293902540274575 204044640351440853810411863)
  ·
    refine ⟨306066960527161280715617795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204044640351440853810411863 306066960527161280715617795)
    ·
      refine ⟨459100440790741921073426693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 306066960527161280715617795 459100440790741921073426693)
      ·
        refine ⟨86081332648264110201267505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 459100440790741921073426693 86081332648264110201267505)
        ·
          refine ⟨64560999486198082650950629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86081332648264110201267505 64560999486198082650950629)
          ·
            refine ⟨12105187403662140497053243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64560999486198082650950629 12105187403662140497053243)
            ·
              refine ⟨18157781105493210745579865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12105187403662140497053243 18157781105493210745579865)
              ·
                refine ⟨13618335829119908059184899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18157781105493210745579865 13618335829119908059184899)
                ·
                  refine ⟨20427503743679862088777349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13618335829119908059184899 20427503743679862088777349)
                  ·
                    refine ⟨3830156951939974141645753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20427503743679862088777349 3830156951939974141645753)
                    ·
                      refine ⟨2872617713954980606234315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3830156951939974141645753 2872617713954980606234315)
                      ·
                        rfl

theorem cell23_5594403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 2, 1, 4, 2].length) (baseStart_5594403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5594403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5594403 prefixEnd_5594403 := by exact prefixLift 5594403
  have htrace : WordTrace (prefixWord ++ tailWord_5594403) baseStart_5594403 baseEnd_5594403 := by
    simpa [prefixWord, tailWord_5594403, baseEnd_5594403] using wordTrace_append hprefix tailTrace_5594403
  have hstable : (prefixWord ++ tailWord_5594403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5594403).length < 2 ^ (prefixWord ++ tailWord_5594403).sum := by decide
  have hdescent : baseEnd_5594403 < baseStart_5594403 := by decide
  rcases family_descends (prefixWord ++ tailWord_5594403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5594433 : List Nat := [1, 2, 5, 2, 1, 2, 1, 1, 2, 2, 4]
def baseStart_5594433 : Nat := 118140960795 + 5594433 * 2 ^ 59
def prefixEnd_5594433 : Nat := 4983230072969 + 3 ^ 40 * 5594433 * 2
def baseEnd_5594433 : Nat := 2872633118374615488859177

theorem tailTrace_5594433 : CollatzResearch.WordTrace tailWord_5594433 prefixEnd_5594433 2872633118374615488859177 := by
  unfold tailWord_5594433
  simp only [CollatzResearch.WordTrace]
  refine ⟨204045734541332168934003953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136030489694221445956002635 204045734541332168934003953)
  ·
    refine ⟨153034300905999126700502965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204045734541332168934003953 153034300905999126700502965)
    ·
      refine ⟨14346965709937418128172153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 153034300905999126700502965 14346965709937418128172153)
      ·
        refine ⟨10760224282453063596129115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14346965709937418128172153 10760224282453063596129115)
        ·
          refine ⟨16140336423679595394193673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10760224282453063596129115 16140336423679595394193673)
          ·
            refine ⟨12105252317759696545645255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16140336423679595394193673 12105252317759696545645255)
            ·
              refine ⟨18157878476639544818467883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12105252317759696545645255 18157878476639544818467883)
              ·
                refine ⟨27236817714959317227701825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18157878476639544818467883 27236817714959317227701825)
                ·
                  refine ⟨20427613286219487920776369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27236817714959317227701825 20427613286219487920776369)
                  ·
                    refine ⟨15320709964664615940582277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20427613286219487920776369 15320709964664615940582277)
                    ·
                      refine ⟨2872633118374615488859177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15320709964664615940582277 2872633118374615488859177)
                      ·
                        rfl

theorem cell23_5594433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_5594433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5594433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5594433 prefixEnd_5594433 := by exact prefixLift 5594433
  have htrace : WordTrace (prefixWord ++ tailWord_5594433) baseStart_5594433 baseEnd_5594433 := by
    simpa [prefixWord, tailWord_5594433, baseEnd_5594433] using wordTrace_append hprefix tailTrace_5594433
  have hstable : (prefixWord ++ tailWord_5594433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5594433).length < 2 ^ (prefixWord ++ tailWord_5594433).sum := by decide
  have hdescent : baseEnd_5594433 < baseStart_5594433 := by decide
  rcases family_descends (prefixWord ++ tailWord_5594433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5594493 : List Nat := [1, 4, 1, 1, 2, 2, 1, 3, 2, 4, 2]
def baseStart_5594493 : Nat := 118140960795 + 5594493 * 2 ^ 59
def prefixEnd_5594493 : Nat := 4983230072969 + 3 ^ 40 * 5594493 * 2
def baseEnd_5594493 : Nat := 2872663927213885254108901

theorem tailTrace_5594493 : CollatzResearch.WordTrace tailWord_5594493 prefixEnd_5594493 2872663927213885254108901 := by
  unfold tailWord_5594493
  simp only [CollatzResearch.WordTrace]
  refine ⟨204047922921114799181188133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136031948614076532787458755 204047922921114799181188133)
  ·
    refine ⟨38258985547709024846472775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 204047922921114799181188133 38258985547709024846472775)
    ·
      refine ⟨57388478321563537269709163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38258985547709024846472775 57388478321563537269709163)
      ·
        refine ⟨86082717482345305904563745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57388478321563537269709163 86082717482345305904563745)
        ·
          refine ⟨64562038111758979428422809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86082717482345305904563745 64562038111758979428422809)
          ·
            refine ⟨48421528583819234571317107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64562038111758979428422809 48421528583819234571317107)
            ·
              refine ⟨72632292875728851856975661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48421528583819234571317107 72632292875728851856975661)
              ·
                refine ⟨27237109828398319446365873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72632292875728851856975661 27237109828398319446365873)
                ·
                  refine ⟨20427832371298739584774405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27237109828398319446365873 20427832371298739584774405)
                  ·
                    refine ⟨3830218569618513672145201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20427832371298739584774405 3830218569618513672145201)
                    ·
                      refine ⟨2872663927213885254108901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3830218569618513672145201 2872663927213885254108901)
                      ·
                        rfl

theorem cell23_5594493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 3, 2, 4, 2].length) (baseStart_5594493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5594493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5594493 prefixEnd_5594493 := by exact prefixLift 5594493
  have htrace : WordTrace (prefixWord ++ tailWord_5594493) baseStart_5594493 baseEnd_5594493 := by
    simpa [prefixWord, tailWord_5594493, baseEnd_5594493] using wordTrace_append hprefix tailTrace_5594493
  have hstable : (prefixWord ++ tailWord_5594493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5594493).length < 2 ^ (prefixWord ++ tailWord_5594493).sum := by decide
  have hdescent : baseEnd_5594493 < baseStart_5594493 := by decide
  rcases family_descends (prefixWord ++ tailWord_5594493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5594503 : List Nat := [1, 1, 4, 2, 2, 2, 2, 2, 3, 4]
def baseStart_5594503 : Nat := 118140960795 + 5594503 * 2 ^ 59
def prefixEnd_5594503 : Nat := 4983230072969 + 3 ^ 40 * 5594503 * 2
def baseEnd_5594503 : Nat := 957556354006810071661285

theorem tailTrace_5594503 : CollatzResearch.WordTrace tailWord_5594503 prefixEnd_5594503 957556354006810071661285 := by
  unfold tailWord_5594503
  simp only [CollatzResearch.WordTrace]
  refine ⟨204048287651078570889052163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136032191767385713926034775 204048287651078570889052163)
  ·
    refine ⟨306072431476617856333578245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204048287651078570889052163 306072431476617856333578245)
    ·
      refine ⟨57388580901865848062545921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 306072431476617856333578245 57388580901865848062545921)
      ·
        refine ⟨43041435676399386046909441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57388580901865848062545921 43041435676399386046909441)
        ·
          refine ⟨32281076757299539535182081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43041435676399386046909441 32281076757299539535182081)
          ·
            refine ⟨24210807567974654651386561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32281076757299539535182081 24210807567974654651386561)
            ·
              refine ⟨18158105675980990988539921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24210807567974654651386561 18158105675980990988539921)
              ·
                refine ⟨13618579256985743241404941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18158105675980990988539921 13618579256985743241404941)
                ·
                  refine ⟨5106967221369653715526853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13618579256985743241404941 5106967221369653715526853)
                  ·
                    refine ⟨957556354006810071661285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5106967221369653715526853 957556354006810071661285)
                    ·
                      rfl

theorem cell23_5594503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 2, 3, 4].length) (baseStart_5594503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5594503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5594503 prefixEnd_5594503 := by exact prefixLift 5594503
  have htrace : WordTrace (prefixWord ++ tailWord_5594503) baseStart_5594503 baseEnd_5594503 := by
    simpa [prefixWord, tailWord_5594503, baseEnd_5594503] using wordTrace_append hprefix tailTrace_5594503
  have hstable : (prefixWord ++ tailWord_5594503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5594503).length < 2 ^ (prefixWord ++ tailWord_5594503).sum := by decide
  have hdescent : baseEnd_5594503 < baseStart_5594503 := by decide
  rcases family_descends (prefixWord ++ tailWord_5594503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5594530 : List Nat := [3, 3, 1, 2, 1, 3, 1, 2, 2, 2, 3]
def baseStart_5594530 : Nat := 118140960795 + 5594530 * 2 ^ 59
def prefixEnd_5594530 : Nat := 4983230072969 + 3 ^ 40 * 5594530 * 2
def baseEnd_5594530 : Nat := 2872682925998101609346231

theorem tailTrace_5594530 : CollatzResearch.WordTrace tailWord_5594530 prefixEnd_5594530 2872682925998101609346231 := by
  unfold tailWord_5594530
  simp only [CollatzResearch.WordTrace]
  refine ⟨51012318105495188625071261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136032848281320503000190029 51012318105495188625071261)
  ·
    refine ⟨19129619289560695734401723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51012318105495188625071261 19129619289560695734401723)
    ·
      refine ⟨28694428934341043601602585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19129619289560695734401723 28694428934341043601602585)
      ·
        refine ⟨21520821700755782701201939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28694428934341043601602585 21520821700755782701201939)
        ·
          refine ⟨32281232551133674051802909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21520821700755782701201939 32281232551133674051802909)
          ·
            refine ⟨12105462206675127769426091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32281232551133674051802909 12105462206675127769426091)
            ·
              refine ⟨18158193310012691654139137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12105462206675127769426091 18158193310012691654139137)
              ·
                refine ⟨13618644982509518740604353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18158193310012691654139137 13618644982509518740604353)
                ·
                  refine ⟨10213983736882139055453265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13618644982509518740604353 10213983736882139055453265)
                  ·
                    refine ⟨7660487802661604291589949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10213983736882139055453265 7660487802661604291589949)
                    ·
                      refine ⟨2872682925998101609346231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7660487802661604291589949 2872682925998101609346231)
                      ·
                        rfl

theorem cell23_5594530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 2, 2, 2, 3].length) (baseStart_5594530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5594530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5594530 prefixEnd_5594530 := by exact prefixLift 5594530
  have htrace : WordTrace (prefixWord ++ tailWord_5594530) baseStart_5594530 baseEnd_5594530 := by
    simpa [prefixWord, tailWord_5594530, baseEnd_5594530] using wordTrace_append hprefix tailTrace_5594530
  have hstable : (prefixWord ++ tailWord_5594530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5594530).length < 2 ^ (prefixWord ++ tailWord_5594530).sum := by decide
  have hdescent : baseEnd_5594530 < baseStart_5594530 := by decide
  rcases family_descends (prefixWord ++ tailWord_5594530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5594563 : List Nat := [1, 1, 1, 3, 1, 1, 7, 2, 1, 5]
def baseStart_5594563 : Nat := 118140960795 + 5594563 * 2 ^ 59
def prefixEnd_5594563 : Nat := 4983230072969 + 3 ^ 40 * 5594563 * 2
def baseEnd_5594563 : Nat := 957566623619899993411193

theorem tailTrace_5594563 : CollatzResearch.WordTrace tailWord_5594563 prefixEnd_5594563 957566623619899993411193 := by
  unfold tailWord_5594563
  simp only [CollatzResearch.WordTrace]
  refine ⟨204050476030861201136236343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136033650687240800757490895 204050476030861201136236343)
  ·
    refine ⟨306075714046291801704354515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204050476030861201136236343 306075714046291801704354515)
    ·
      refine ⟨459113571069437702556531773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 306075714046291801704354515 459113571069437702556531773)
      ·
        refine ⟨172167589151039138458699415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 459113571069437702556531773 172167589151039138458699415)
        ·
          refine ⟨258251383726558707688049123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172167589151039138458699415 258251383726558707688049123)
          ·
            refine ⟨387377075589838061532073685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 258251383726558707688049123 387377075589838061532073685)
            ·
              refine ⟨9079150209136829567157977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 387377075589838061532073685 9079150209136829567157977)
              ·
                refine ⟨6809362656852622175368483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9079150209136829567157977 6809362656852622175368483)
                ·
                  refine ⟨10214043985278933263052725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6809362656852622175368483 10214043985278933263052725)
                  ·
                    refine ⟨957566623619899993411193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10214043985278933263052725 957566623619899993411193)
                    ·
                      rfl

theorem cell23_5594563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7, 2, 1, 5].length) (baseStart_5594563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5594563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5594563 prefixEnd_5594563 := by exact prefixLift 5594563
  have htrace : WordTrace (prefixWord ++ tailWord_5594563) baseStart_5594563 baseEnd_5594563 := by
    simpa [prefixWord, tailWord_5594563, baseEnd_5594563] using wordTrace_append hprefix tailTrace_5594563
  have hstable : (prefixWord ++ tailWord_5594563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5594563).length < 2 ^ (prefixWord ++ tailWord_5594563).sum := by decide
  have hdescent : baseEnd_5594563 < baseStart_5594563 := by decide
  rcases family_descends (prefixWord ++ tailWord_5594563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5594570 : List Nat := [3, 1, 2, 1, 2, 3, 1, 3, 2, 3, 2]
def baseStart_5594570 : Nat := 118140960795 + 5594570 * 2 ^ 59
def prefixEnd_5594570 : Nat := 4983230072969 + 3 ^ 40 * 5594570 * 2
def baseEnd_5594570 : Nat := 2872703465224281452846047

theorem tailTrace_5594570 : CollatzResearch.WordTrace tailWord_5594570 prefixEnd_5594570 2872703465224281452846047 := by
  unfold tailWord_5594570
  simp only [CollatzResearch.WordTrace]
  refine ⟨51012682835458960332935291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136033820894557227554494109 51012682835458960332935291)
  ·
    refine ⟨76519024253188440499402937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51012682835458960332935291 76519024253188440499402937)
    ·
      refine ⟨57389268189891330374552203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76519024253188440499402937 57389268189891330374552203)
      ·
        refine ⟨86083902284836995561828305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57389268189891330374552203 86083902284836995561828305)
        ·
          refine ⟨64562926713627746671371229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86083902284836995561828305 64562926713627746671371229)
          ·
            refine ⟨24211097517610405001764211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64562926713627746671371229 24211097517610405001764211)
            ·
              refine ⟨36316646276415607502646317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24211097517610405001764211 36316646276415607502646317)
              ·
                refine ⟨13618742353655852813492369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36316646276415607502646317 13618742353655852813492369)
                ·
                  refine ⟨10214056765241889610119277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13618742353655852813492369 10214056765241889610119277)
                  ·
                    refine ⟨3830271286965708603794729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10214056765241889610119277 3830271286965708603794729)
                    ·
                      refine ⟨2872703465224281452846047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3830271286965708603794729 2872703465224281452846047)
                      ·
                        rfl

theorem cell23_5594570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 3, 2, 3, 2].length) (baseStart_5594570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5594570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5594570 prefixEnd_5594570 := by exact prefixLift 5594570
  have htrace : WordTrace (prefixWord ++ tailWord_5594570) baseStart_5594570 baseEnd_5594570 := by
    simpa [prefixWord, tailWord_5594570, baseEnd_5594570] using wordTrace_append hprefix tailTrace_5594570
  have hstable : (prefixWord ++ tailWord_5594570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5594570).length < 2 ^ (prefixWord ++ tailWord_5594570).sum := by decide
  have hdescent : baseEnd_5594570 < baseStart_5594570 := by decide
  rcases family_descends (prefixWord ++ tailWord_5594570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5594576 : List Nat := [2, 1, 1, 1, 1, 2, 2, 6, 1, 6]
def baseStart_5594576 : Nat := 118140960795 + 5594576 * 2 ^ 59
def prefixEnd_5594576 : Nat := 4983230072969 + 3 ^ 40 * 5594576 * 2
def baseEnd_5594576 : Nat := 957568848702736143123673

theorem tailTrace_5594576 : CollatzResearch.WordTrace tailWord_5594576 prefixEnd_5594576 957568848702736143123673 := by
  unfold tailWord_5594576
  simp only [CollatzResearch.WordTrace]
  refine ⟨102025475089907052178229791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136033966786542736237639721 102025475089907052178229791)
  ·
    refine ⟨153038212634860578267344687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102025475089907052178229791 153038212634860578267344687)
    ·
      refine ⟨229557318952290867401017031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153038212634860578267344687 229557318952290867401017031)
      ·
        refine ⟨344335978428436301101525547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229557318952290867401017031 344335978428436301101525547)
        ·
          refine ⟨516503967642654451652288321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 344335978428436301101525547 516503967642654451652288321)
          ·
            refine ⟨387377975731990838739216241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 516503967642654451652288321 387377975731990838739216241)
            ·
              refine ⟨290533481798993129054412181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 387377975731990838739216241 290533481798993129054412181)
              ·
                refine ⟨13618756959327802924425571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 290533481798993129054412181 13618756959327802924425571)
                ·
                  refine ⟨20428135438991704386638357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13618756959327802924425571 20428135438991704386638357)
                  ·
                    refine ⟨957568848702736143123673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20428135438991704386638357 957568848702736143123673)
                    ·
                      rfl

theorem cell23_5594576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 6, 1, 6].length) (baseStart_5594576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5594576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5594576 prefixEnd_5594576 := by exact prefixLift 5594576
  have htrace : WordTrace (prefixWord ++ tailWord_5594576) baseStart_5594576 baseEnd_5594576 := by
    simpa [prefixWord, tailWord_5594576, baseEnd_5594576] using wordTrace_append hprefix tailTrace_5594576
  have hstable : (prefixWord ++ tailWord_5594576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5594576).length < 2 ^ (prefixWord ++ tailWord_5594576).sum := by decide
  have hdescent : baseEnd_5594576 < baseStart_5594576 := by decide
  rcases family_descends (prefixWord ++ tailWord_5594576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5594583 : List Nat := [1, 1, 3, 2, 1, 1, 1, 7, 1, 1, 4]
def baseStart_5594583 : Nat := 118140960795 + 5594583 * 2 ^ 59
def prefixEnd_5594583 : Nat := 4983230072969 + 3 ^ 40 * 5594583 * 2
def baseEnd_5594583 : Nat := 2872710140472789901983487

theorem tailTrace_5594583 : CollatzResearch.WordTrace tailWord_5594583 prefixEnd_5594583 2872710140472789901983487 := by
  unfold tailWord_5594583
  simp only [CollatzResearch.WordTrace]
  refine ⟨204051205490788744551964403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136034136993859163034642935 204051205490788744551964403)
  ·
    refine ⟨306076808236183116827946605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204051205490788744551964403 306076808236183116827946605)
    ·
      refine ⟨114778803088568668810479977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 306076808236183116827946605 114778803088568668810479977)
      ·
        refine ⟨86084102316426501607859983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114778803088568668810479977 86084102316426501607859983)
        ·
          refine ⟨129126153474639752411789975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86084102316426501607859983 129126153474639752411789975)
          ·
            refine ⟨193689230211959628617684963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129126153474639752411789975 193689230211959628617684963)
            ·
              refine ⟨290533845317939442926527445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 193689230211959628617684963 290533845317939442926527445)
              ·
                refine ⟨6809386999639205693590487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 290533845317939442926527445 6809386999639205693590487)
                ·
                  refine ⟨10214080499458808540385731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6809386999639205693590487 10214080499458808540385731)
                  ·
                    refine ⟨15321120749188212810578597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10214080499458808540385731 15321120749188212810578597)
                    ·
                      refine ⟨2872710140472789901983487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15321120749188212810578597 2872710140472789901983487)
                      ·
                        rfl

theorem cell23_5594583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 7, 1, 1, 4].length) (baseStart_5594583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5594583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5594583 prefixEnd_5594583 := by exact prefixLift 5594583
  have htrace : WordTrace (prefixWord ++ tailWord_5594583) baseStart_5594583 baseEnd_5594583 := by
    simpa [prefixWord, tailWord_5594583, baseEnd_5594583] using wordTrace_append hprefix tailTrace_5594583
  have hstable : (prefixWord ++ tailWord_5594583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5594583).length < 2 ^ (prefixWord ++ tailWord_5594583).sum := by decide
  have hdescent : baseEnd_5594583 < baseStart_5594583 := by decide
  rcases family_descends (prefixWord ++ tailWord_5594583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5594596 : List Nat := [2, 3, 1, 1, 1, 1, 1, 3, 3, 1, 6]
def baseStart_5594596 : Nat := 118140960795 + 5594596 * 2 ^ 59
def prefixEnd_5594596 : Nat := 4983230072969 + 3 ^ 40 * 5594596 * 2
def baseEnd_5594596 : Nat := 2872716815721298351120927

theorem tailTrace_5594596 : CollatzResearch.WordTrace tailWord_5594596 prefixEnd_5594596 2872716815721298351120927 := by
  unfold tailWord_5594596
  simp only [CollatzResearch.WordTrace]
  refine ⟨102025839819870823886093821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136034453093161098514791761 102025839819870823886093821)
  ·
    refine ⟨38259689932451558957285183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102025839819870823886093821 38259689932451558957285183)
    ·
      refine ⟨57389534898677338435927775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38259689932451558957285183 57389534898677338435927775)
      ·
        refine ⟨86084302348016007653891663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57389534898677338435927775 86084302348016007653891663)
        ·
          refine ⟨129126453522024011480837495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86084302348016007653891663 129126453522024011480837495)
          ·
            refine ⟨193689680283036017221256243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129126453522024011480837495 193689680283036017221256243)
            ·
              refine ⟨290534520424554025831884365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 193689680283036017221256243 290534520424554025831884365)
              ·
                refine ⟨108950445159207759686956637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 290534520424554025831884365 108950445159207759686956637)
                ·
                  refine ⟨40856416934702909882608739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 108950445159207759686956637 40856416934702909882608739)
                  ·
                    refine ⟨61284625402054364823913109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40856416934702909882608739 61284625402054364823913109)
                    ·
                      refine ⟨2872716815721298351120927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61284625402054364823913109 2872716815721298351120927)
                      ·
                        rfl

theorem cell23_5594596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 3, 1, 6].length) (baseStart_5594596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5594596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5594596 prefixEnd_5594596 := by exact prefixLift 5594596
  have htrace : WordTrace (prefixWord ++ tailWord_5594596) baseStart_5594596 baseEnd_5594596 := by
    simpa [prefixWord, tailWord_5594596, baseEnd_5594596] using wordTrace_append hprefix tailTrace_5594596
  have hstable : (prefixWord ++ tailWord_5594596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5594596).length < 2 ^ (prefixWord ++ tailWord_5594596).sum := by decide
  have hdescent : baseEnd_5594596 < baseStart_5594596 := by decide
  rcases family_descends (prefixWord ++ tailWord_5594596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5594610 : List Nat := [3, 2, 1, 4, 1, 2, 2, 1, 1, 6]
def baseStart_5594610 : Nat := 118140960795 + 5594610 * 2 ^ 59
def prefixEnd_5594610 : Nat := 4983230072969 + 3 ^ 40 * 5594610 * 2
def baseEnd_5594610 : Nat := 957574668150153765448621

theorem tailTrace_5594610 : CollatzResearch.WordTrace tailWord_5594610 prefixEnd_5594610 957574668150153765448621 := by
  unfold tailWord_5594610
  simp only [CollatzResearch.WordTrace]
  refine ⟨51013047565422732040799321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136034793507793952108798189 51013047565422732040799321)
  ·
    refine ⟨38259785674067049030599491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51013047565422732040799321 38259785674067049030599491)
    ·
      refine ⟨57389678511100573545899237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38259785674067049030599491 57389678511100573545899237)
      ·
        refine ⟨10760564720831357539856107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57389678511100573545899237 10760564720831357539856107)
        ·
          refine ⟨16140847081247036309784161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10760564720831357539856107 16140847081247036309784161)
          ·
            refine ⟨12105635310935277232338121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16140847081247036309784161 12105635310935277232338121)
            ·
              refine ⟨9079226483201457924253591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12105635310935277232338121 9079226483201457924253591)
              ·
                refine ⟨13618839724802186886380387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9079226483201457924253591 13618839724802186886380387)
                ·
                  refine ⟨20428259587203280329570581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13618839724802186886380387 20428259587203280329570581)
                  ·
                    refine ⟨957574668150153765448621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20428259587203280329570581 957574668150153765448621)
                    ·
                      rfl

theorem cell23_5594610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2, 1, 1, 6].length) (baseStart_5594610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5594610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5594610 prefixEnd_5594610 := by exact prefixLift 5594610
  have htrace : WordTrace (prefixWord ++ tailWord_5594610) baseStart_5594610 baseEnd_5594610 := by
    simpa [prefixWord, tailWord_5594610, baseEnd_5594610] using wordTrace_append hprefix tailTrace_5594610
  have hstable : (prefixWord ++ tailWord_5594610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5594610).length < 2 ^ (prefixWord ++ tailWord_5594610).sum := by decide
  have hdescent : baseEnd_5594610 < baseStart_5594610 := by decide
  rcases family_descends (prefixWord ++ tailWord_5594610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5594633 : List Nat := [1, 2, 1, 1, 3, 1, 3, 4, 1, 3, 3]
def baseStart_5594633 : Nat := 118140960795 + 5594633 * 2 ^ 59
def prefixEnd_5594633 : Nat := 4983230072969 + 3 ^ 40 * 5594633 * 2
def baseEnd_5594633 : Nat := 2872735814505514706358257

theorem tailTrace_5594633 : CollatzResearch.WordTrace tailWord_5594633 prefixEnd_5594633 2872735814505514706358257 := by
  unfold tailWord_5594633
  simp only [CollatzResearch.WordTrace]
  refine ⟨204053029140607603091284553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136035352760405068727523035 204053029140607603091284553)
  ·
    refine ⟨153039771855455702318463415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204053029140607603091284553 153039771855455702318463415)
    ·
      refine ⟨229559657783183553477695123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153039771855455702318463415 229559657783183553477695123)
      ·
        refine ⟨344339486674775330216542685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229559657783183553477695123 344339486674775330216542685)
        ·
          refine ⟨129127307503040748831203507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 344339486674775330216542685 129127307503040748831203507)
          ·
            refine ⟨193690961254561123246805261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129127307503040748831203507 193690961254561123246805261)
            ·
              refine ⟨72634110470460421217551973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 193690961254561123246805261 72634110470460421217551973)
              ·
                refine ⟨13618895713211328978290995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72634110470460421217551973 13618895713211328978290995)
                ·
                  refine ⟨20428343569816993467436493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13618895713211328978290995 20428343569816993467436493)
                  ·
                    refine ⟨7660628838681372550288685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20428343569816993467436493 7660628838681372550288685)
                    ·
                      refine ⟨2872735814505514706358257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7660628838681372550288685 2872735814505514706358257)
                      ·
                        rfl

theorem cell23_5594633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 4, 1, 3, 3].length) (baseStart_5594633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5594633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5594633 prefixEnd_5594633 := by exact prefixLift 5594633
  have htrace : WordTrace (prefixWord ++ tailWord_5594633) baseStart_5594633 baseEnd_5594633 := by
    simpa [prefixWord, tailWord_5594633, baseEnd_5594633] using wordTrace_append hprefix tailTrace_5594633
  have hstable : (prefixWord ++ tailWord_5594633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5594633).length < 2 ^ (prefixWord ++ tailWord_5594633).sum := by decide
  have hdescent : baseEnd_5594633 < baseStart_5594633 := by decide
  rcases family_descends (prefixWord ++ tailWord_5594633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5594634 : List Nat := [3, 1, 2, 2, 2, 2, 1, 5, 1, 2, 2]
def baseStart_5594634 : Nat := 118140960795 + 5594634 * 2 ^ 59
def prefixEnd_5594634 : Nat := 4983230072969 + 3 ^ 40 * 5594634 * 2
def baseEnd_5594634 : Nat := 2872736327986169202445753

theorem tailTrace_5594634 : CollatzResearch.WordTrace tailWord_5594634 prefixEnd_5594634 2872736327986169202445753 := by
  unfold tailWord_5594634
  simp only [CollatzResearch.WordTrace]
  refine ⟨51013266403400995065517739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136035377075735986841380637 51013266403400995065517739)
  ·
    refine ⟨76519899605101492598276609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51013266403400995065517739 76519899605101492598276609)
    ·
      refine ⟨57389924703826119448707457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76519899605101492598276609 57389924703826119448707457)
      ·
        refine ⟨43042443527869589586530593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57389924703826119448707457 43042443527869589586530593)
        ·
          refine ⟨32281832645902192189897945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43042443527869589586530593 32281832645902192189897945)
          ·
            refine ⟨24211374484426644142423459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32281832645902192189897945 24211374484426644142423459)
            ·
              refine ⟨36317061726639966213635189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24211374484426644142423459 36317061726639966213635189)
              ·
                refine ⟨3404724536872496832528299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36317061726639966213635189 3404724536872496832528299)
                ·
                  refine ⟨5107086805308745248792449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3404724536872496832528299 5107086805308745248792449)
                  ·
                    refine ⟨3830315103981558936594337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5107086805308745248792449 3830315103981558936594337)
                    ·
                      refine ⟨2872736327986169202445753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3830315103981558936594337 2872736327986169202445753)
                      ·
                        rfl

theorem cell23_5594634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 5, 1, 2, 2].length) (baseStart_5594634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5594634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5594634 prefixEnd_5594634 := by exact prefixLift 5594634
  have htrace : WordTrace (prefixWord ++ tailWord_5594634) baseStart_5594634 baseEnd_5594634 := by
    simpa [prefixWord, tailWord_5594634, baseEnd_5594634] using wordTrace_append hprefix tailTrace_5594634
  have hstable : (prefixWord ++ tailWord_5594634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5594634).length < 2 ^ (prefixWord ++ tailWord_5594634).sum := by decide
  have hdescent : baseEnd_5594634 < baseStart_5594634 := by decide
  rcases family_descends (prefixWord ++ tailWord_5594634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5594664 : List Nat := [2, 1, 5, 2, 3, 1, 1, 1, 1, 2, 4]
def baseStart_5594664 : Nat := 118140960795 + 5594664 * 2 ^ 59
def prefixEnd_5594664 : Nat := 4983230072969 + 3 ^ 40 * 5594664 * 2
def baseEnd_5594664 : Nat := 2872751732405804085070615

theorem tailTrace_5594664 : CollatzResearch.WordTrace tailWord_5594664 prefixEnd_5594664 2872751732405804085070615 := by
  unfold tailWord_5594664
  simp only [CollatzResearch.WordTrace]
  refine ⟨102027079901747647692831523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136036106535663530257108697 102027079901747647692831523)
  ·
    refine ⟨153040619852621471539247285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102027079901747647692831523 153040619852621471539247285)
    ·
      refine ⟨14347558111183262956804433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 153040619852621471539247285 14347558111183262956804433)
      ·
        refine ⟨10760668583387447217603325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14347558111183262956804433 10760668583387447217603325)
        ·
          refine ⟨4035250718770292706601247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10760668583387447217603325 4035250718770292706601247)
          ·
            refine ⟨6052876078155439059901871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4035250718770292706601247 6052876078155439059901871)
            ·
              refine ⟨9079314117233158589852807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6052876078155439059901871 9079314117233158589852807)
              ·
                refine ⟨13618971175849737884779211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9079314117233158589852807 13618971175849737884779211)
                ·
                  refine ⟨20428456763774606827168817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13618971175849737884779211 20428456763774606827168817)
                  ·
                    refine ⟨15321342572830955120376613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20428456763774606827168817 15321342572830955120376613)
                    ·
                      refine ⟨2872751732405804085070615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15321342572830955120376613 2872751732405804085070615)
                      ·
                        rfl

theorem cell23_5594664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 1, 1, 1, 2, 4].length) (baseStart_5594664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5594664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5594664 prefixEnd_5594664 := by exact prefixLift 5594664
  have htrace : WordTrace (prefixWord ++ tailWord_5594664) baseStart_5594664 baseEnd_5594664 := by
    simpa [prefixWord, tailWord_5594664, baseEnd_5594664] using wordTrace_append hprefix tailTrace_5594664
  have hstable : (prefixWord ++ tailWord_5594664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5594664).length < 2 ^ (prefixWord ++ tailWord_5594664).sum := by decide
  have hdescent : baseEnd_5594664 < baseStart_5594664 := by decide
  rcases family_descends (prefixWord ++ tailWord_5594664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5594677 : List Nat := [1, 3, 3, 1, 1, 3, 1, 4, 1, 3, 2]
def baseStart_5594677 : Nat := 118140960795 + 5594677 * 2 ^ 59
def prefixEnd_5594677 : Nat := 4983230072969 + 3 ^ 40 * 5594677 * 2
def baseEnd_5594677 : Nat := 2872758407654312534208055

theorem tailTrace_5594677 : CollatzResearch.WordTrace tailWord_5594677 prefixEnd_5594677 2872758407654312534208055 := by
  unfold tailWord_5594677
  simp only [CollatzResearch.WordTrace]
  refine ⟨204054633952448198605886285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136036422634965465737257523 204054633952448198605886285)
  ·
    refine ⟨76520487732168074477207357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 204054633952448198605886285 76520487732168074477207357)
    ·
      refine ⟨28695182899563027928952759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76520487732168074477207357 28695182899563027928952759)
      ·
        refine ⟨43042774349344541893429139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28695182899563027928952759 43042774349344541893429139)
        ·
          refine ⟨64564161524016812840143709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43042774349344541893429139 64564161524016812840143709)
          ·
            refine ⟨24211560571506304815053891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64564161524016812840143709 24211560571506304815053891)
            ·
              refine ⟨36317340857259457222580837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24211560571506304815053891 36317340857259457222580837)
              ·
                refine ⟨6809501410736148229233907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36317340857259457222580837 6809501410736148229233907)
                ·
                  refine ⟨10214252116104222343850861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6809501410736148229233907 10214252116104222343850861)
                  ·
                    refine ⟨3830344543539083378944073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10214252116104222343850861 3830344543539083378944073)
                    ·
                      refine ⟨2872758407654312534208055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3830344543539083378944073 2872758407654312534208055)
                      ·
                        rfl

theorem cell23_5594677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 4, 1, 3, 2].length) (baseStart_5594677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5594677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5594677 prefixEnd_5594677 := by exact prefixLift 5594677
  have htrace : WordTrace (prefixWord ++ tailWord_5594677) baseStart_5594677 baseEnd_5594677 := by
    simpa [prefixWord, tailWord_5594677, baseEnd_5594677] using wordTrace_append hprefix tailTrace_5594677
  have hstable : (prefixWord ++ tailWord_5594677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5594677).length < 2 ^ (prefixWord ++ tailWord_5594677).sum := by decide
  have hdescent : baseEnd_5594677 < baseStart_5594677 := by decide
  rcases family_descends (prefixWord ++ tailWord_5594677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5594693 : List Nat := [1, 3, 1, 1, 1, 4, 3, 1, 2, 1, 5]
def baseStart_5594693 : Nat := 118140960795 + 5594693 * 2 ^ 59
def prefixEnd_5594693 : Nat := 4983230072969 + 3 ^ 40 * 5594693 * 2
def baseEnd_5594693 : Nat := 2872766623344784471607981

theorem tailTrace_5594693 : CollatzResearch.WordTrace tailWord_5594693 prefixEnd_5594693 2872766623344784471607981 := by
  unfold tailWord_5594693
  simp only [CollatzResearch.WordTrace]
  refine ⟨204055217520390233338468733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136036811680260155558979155 204055217520390233338468733)
  ·
    refine ⟨76520706570146337501925775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 204055217520390233338468733 76520706570146337501925775)
    ·
      refine ⟨114781059855219506252888663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76520706570146337501925775 114781059855219506252888663)
      ·
        refine ⟨172171589782829259379332995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114781059855219506252888663 172171589782829259379332995)
        ·
          refine ⟨258257384674243889068999493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172171589782829259379332995 258257384674243889068999493)
          ·
            refine ⟨48423259626420729200437405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 258257384674243889068999493 48423259626420729200437405)
            ·
              refine ⟨18158722359907773450164027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48423259626420729200437405 18158722359907773450164027)
              ·
                refine ⟨27238083539861660175246041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18158722359907773450164027 27238083539861660175246041)
                ·
                  refine ⟨20428562654896245131434531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27238083539861660175246041 20428562654896245131434531)
                  ·
                    refine ⟨30642843982344367697151797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20428562654896245131434531 30642843982344367697151797)
                    ·
                      refine ⟨2872766623344784471607981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30642843982344367697151797 2872766623344784471607981)
                      ·
                        rfl

theorem cell23_5594693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 1, 2, 1, 5].length) (baseStart_5594693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5594693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5594693 prefixEnd_5594693 := by exact prefixLift 5594693
  have htrace : WordTrace (prefixWord ++ tailWord_5594693) baseStart_5594693 baseEnd_5594693 := by
    simpa [prefixWord, tailWord_5594693, baseEnd_5594693] using wordTrace_append hprefix tailTrace_5594693
  have hstable : (prefixWord ++ tailWord_5594693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5594693).length < 2 ^ (prefixWord ++ tailWord_5594693).sum := by decide
  have hdescent : baseEnd_5594693 < baseStart_5594693 := by decide
  rcases family_descends (prefixWord ++ tailWord_5594693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5594724 : List Nat := [2, 3, 1, 1, 2, 4, 1, 3, 2, 2, 2]
def baseStart_5594724 : Nat := 118140960795 + 5594724 * 2 ^ 59
def prefixEnd_5594724 : Nat := 4983230072969 + 3 ^ 40 * 5594724 * 2
def baseEnd_5594724 : Nat := 2872782541245073850320339

theorem tailTrace_5594724 : CollatzResearch.WordTrace tailWord_5594724 prefixEnd_5594724 2872782541245073850320339 := by
  unfold tailWord_5594724
  simp only [CollatzResearch.WordTrace]
  refine ⟨102028174091638962816423613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136037565455518617088564817 102028174091638962816423613)
  ·
    refine ⟨38260565284364611056158855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102028174091638962816423613 38260565284364611056158855)
    ·
      refine ⟨57390847926546916584238283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38260565284364611056158855 57390847926546916584238283)
      ·
        refine ⟨86086271889820374876357425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57390847926546916584238283 86086271889820374876357425)
        ·
          refine ⟨64564703917365281157268069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86086271889820374876357425 64564703917365281157268069)
          ·
            refine ⟨12105881984505990216987763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64564703917365281157268069 12105881984505990216987763)
            ·
              refine ⟨18158822976758985325481645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12105881984505990216987763 18158822976758985325481645)
              ·
                refine ⟨6809558616284619497055617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18158822976758985325481645 6809558616284619497055617)
                ·
                  refine ⟨5107168962213464622791713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6809558616284619497055617 5107168962213464622791713)
                  ·
                    refine ⟨3830376721660098467093785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5107168962213464622791713 3830376721660098467093785)
                    ·
                      refine ⟨2872782541245073850320339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3830376721660098467093785 2872782541245073850320339)
                      ·
                        rfl

theorem cell23_5594724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 3, 2, 2, 2].length) (baseStart_5594724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5594724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5594724 prefixEnd_5594724 := by exact prefixLift 5594724
  have htrace : WordTrace (prefixWord ++ tailWord_5594724) baseStart_5594724 baseEnd_5594724 := by
    simpa [prefixWord, tailWord_5594724, baseEnd_5594724] using wordTrace_append hprefix tailTrace_5594724
  have hstable : (prefixWord ++ tailWord_5594724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5594724).length < 2 ^ (prefixWord ++ tailWord_5594724).sum := by decide
  have hdescent : baseEnd_5594724 < baseStart_5594724 := by decide
  rcases family_descends (prefixWord ++ tailWord_5594724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5594797 : List Nat := [1, 5, 2, 1, 1, 1, 1, 2, 1, 6, 2]
def baseStart_5594797 : Nat := 118140960795 + 5594797 * 2 ^ 59
def prefixEnd_5594797 : Nat := 4983230072969 + 3 ^ 40 * 5594797 * 2
def baseEnd_5594797 : Nat := 2872820025332852064707503

theorem tailTrace_5594797 : CollatzResearch.WordTrace tailWord_5594797 prefixEnd_5594797 2872820025332852064707503 := by
  unfold tailWord_5594797
  simp only [CollatzResearch.WordTrace]
  refine ⟨204059010712013459100254645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136039340474675639400169763 204059010712013459100254645)
  ·
    refine ⟨19130532254251261790648873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 204059010712013459100254645 19130532254251261790648873)
    ·
      refine ⟨14347899190688446342986655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19130532254251261790648873 14347899190688446342986655)
      ·
        refine ⟨21521848786032669514479983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14347899190688446342986655 21521848786032669514479983)
        ·
          refine ⟨32282773179049004271719975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21521848786032669514479983 32282773179049004271719975)
          ·
            refine ⟨48424159768573506407579963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32282773179049004271719975 48424159768573506407579963)
            ·
              refine ⟨72636239652860259611369945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48424159768573506407579963 72636239652860259611369945)
              ·
                refine ⟨54477179739645194708527459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72636239652860259611369945 54477179739645194708527459)
                ·
                  refine ⟨81715769609467792062791189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54477179739645194708527459 81715769609467792062791189)
                  ·
                    refine ⟨3830426700443802752943337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 81715769609467792062791189 3830426700443802752943337)
                    ·
                      refine ⟨2872820025332852064707503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3830426700443802752943337 2872820025332852064707503)
                      ·
                        rfl

theorem cell23_5594797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 2, 1, 6, 2].length) (baseStart_5594797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5594797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5594797 prefixEnd_5594797 := by exact prefixLift 5594797
  have htrace : WordTrace (prefixWord ++ tailWord_5594797) baseStart_5594797 baseEnd_5594797 := by
    simpa [prefixWord, tailWord_5594797, baseEnd_5594797] using wordTrace_append hprefix tailTrace_5594797
  have hstable : (prefixWord ++ tailWord_5594797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5594797).length < 2 ^ (prefixWord ++ tailWord_5594797).sum := by decide
  have hdescent : baseEnd_5594797 < baseStart_5594797 := by decide
  rcases family_descends (prefixWord ++ tailWord_5594797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5594803 : List Nat := [1, 1, 1, 2, 3, 3, 2, 2, 8]
def baseStart_5594803 : Nat := 118140960795 + 5594803 * 2 ^ 59
def prefixEnd_5594803 : Nat := 4983230072969 + 3 ^ 40 * 5594803 * 2
def baseEnd_5594803 : Nat := 319202567357419893470275

theorem tailTrace_5594803 : CollatzResearch.WordTrace tailWord_5594803 prefixEnd_5594803 319202567357419893470275 := by
  unfold tailWord_5594803
  simp only [CollatzResearch.WordTrace]
  refine ⟨204059229549991722124973063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136039486366661148083315375 204059229549991722124973063)
  ·
    refine ⟨306088844324987583187459595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204059229549991722124973063 306088844324987583187459595)
    ·
      refine ⟨459133266487481374781189393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 306088844324987583187459595 459133266487481374781189393)
      ·
        refine ⟨344349949865611031085892045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 459133266487481374781189393 344349949865611031085892045)
        ·
          refine ⟨129131231199604136657209517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 344349949865611031085892045 129131231199604136657209517)
          ·
            refine ⟨48424211699851551246453569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 129131231199604136657209517 48424211699851551246453569)
            ·
              refine ⟨36318158774888663434840177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48424211699851551246453569 36318158774888663434840177)
              ·
                refine ⟨27238619081166497576130133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36318158774888663434840177 27238619081166497576130133)
                ·
                  refine ⟨319202567357419893470275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27238619081166497576130133 319202567357419893470275)
                  ·
                    rfl

theorem cell23_5594803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 2, 8].length) (baseStart_5594803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5594803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5594803 prefixEnd_5594803 := by exact prefixLift 5594803
  have htrace : WordTrace (prefixWord ++ tailWord_5594803) baseStart_5594803 baseEnd_5594803 := by
    simpa [prefixWord, tailWord_5594803, baseEnd_5594803] using wordTrace_append hprefix tailTrace_5594803
  have hstable : (prefixWord ++ tailWord_5594803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5594803).length < 2 ^ (prefixWord ++ tailWord_5594803).sum := by decide
  have hdescent : baseEnd_5594803 < baseStart_5594803 := by decide
  rcases family_descends (prefixWord ++ tailWord_5594803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5594820 : List Nat := [2, 3, 3, 1, 1, 1, 3, 1, 8]
def baseStart_5594820 : Nat := 118140960795 + 5594820 * 2 ^ 59
def prefixEnd_5594820 : Nat := 4983230072969 + 3 ^ 40 * 5594820 * 2
def baseEnd_5594820 : Nat := 319203537265322830524433

theorem tailTrace_5594820 : CollatzResearch.WordTrace tailWord_5594820 prefixEnd_5594820 319203537265322830524433 := by
  unfold tailWord_5594820
  simp only [CollatzResearch.WordTrace]
  refine ⟨102029924795465067014170957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136039899727286756018894609 102029924795465067014170957)
  ·
    refine ⟨38261221798299400130314109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102029924795465067014170957 38261221798299400130314109)
    ·
      refine ⟨14347958174362275048867791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38261221798299400130314109 14347958174362275048867791)
      ·
        refine ⟨21521937261543412573301687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14347958174362275048867791 21521937261543412573301687)
        ·
          refine ⟨32282905892315118859952531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21521937261543412573301687 32282905892315118859952531)
          ·
            refine ⟨48424358838472678289928797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32282905892315118859952531 48424358838472678289928797)
            ·
              refine ⟨18159134564427254358723299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48424358838472678289928797 18159134564427254358723299)
              ·
                refine ⟨27238701846640881538084949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18159134564427254358723299 27238701846640881538084949)
                ·
                  refine ⟨319203537265322830524433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27238701846640881538084949 319203537265322830524433)
                  ·
                    rfl

theorem cell23_5594820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 1, 8].length) (baseStart_5594820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5594820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5594820 prefixEnd_5594820 := by exact prefixLift 5594820
  have htrace : WordTrace (prefixWord ++ tailWord_5594820) baseStart_5594820 baseEnd_5594820 := by
    simpa [prefixWord, tailWord_5594820, baseEnd_5594820] using wordTrace_append hprefix tailTrace_5594820
  have hstable : (prefixWord ++ tailWord_5594820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5594820).length < 2 ^ (prefixWord ++ tailWord_5594820).sum := by decide
  have hdescent : baseEnd_5594820 < baseStart_5594820 := by decide
  rcases family_descends (prefixWord ++ tailWord_5594820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5594823 : List Nat := [1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 8]
def baseStart_5594823 : Nat := 118140960795 + 5594823 * 2 ^ 59
def prefixEnd_5594823 : Nat := 4983230072969 + 3 ^ 40 * 5594823 * 2
def baseEnd_5594823 : Nat := 2872833375829868962982383

theorem tailTrace_5594823 : CollatzResearch.WordTrace tailWord_5594823 prefixEnd_5594823 2872833375829868962982383 := by
  unfold tailWord_5594823
  simp only [CollatzResearch.WordTrace]
  refine ⟨204059959009919265540701123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136039972673279510360467415 204059959009919265540701123)
  ·
    refine ⟨306089938514878898311051685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204059959009919265540701123 306089938514878898311051685)
    ·
      refine ⟨57391863471539793433322191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 306089938514878898311051685 57391863471539793433322191)
      ·
        refine ⟨86087795207309690149983287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57391863471539793433322191 86087795207309690149983287)
        ·
          refine ⟨129131692810964535224974931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86087795207309690149983287 129131692810964535224974931)
          ·
            refine ⟨193697539216446802837462397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129131692810964535224974931 193697539216446802837462397)
            ·
              refine ⟨72636577206167551064048399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 193697539216446802837462397 72636577206167551064048399)
              ·
                refine ⟨108954865809251326596072599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72636577206167551064048399 108954865809251326596072599)
                ·
                  refine ⟨163432298713876989894108899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 108954865809251326596072599 163432298713876989894108899)
                  ·
                    refine ⟨245148448070815484841163349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 163432298713876989894108899 245148448070815484841163349)
                    ·
                      refine ⟨2872833375829868962982383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 245148448070815484841163349 2872833375829868962982383)
                      ·
                        rfl

theorem cell23_5594823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 8].length) (baseStart_5594823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5594823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5594823 prefixEnd_5594823 := by exact prefixLift 5594823
  have htrace : WordTrace (prefixWord ++ tailWord_5594823) baseStart_5594823 baseEnd_5594823 := by
    simpa [prefixWord, tailWord_5594823, baseEnd_5594823] using wordTrace_append hprefix tailTrace_5594823
  have hstable : (prefixWord ++ tailWord_5594823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5594823).length < 2 ^ (prefixWord ++ tailWord_5594823).sum := by decide
  have hdescent : baseEnd_5594823 < baseStart_5594823 := by decide
  rcases family_descends (prefixWord ++ tailWord_5594823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5594847 : List Nat := [1, 1, 2, 3, 2, 2, 1, 4, 3, 1, 3]
def baseStart_5594847 : Nat := 118140960795 + 5594847 * 2 ^ 59
def prefixEnd_5594847 : Nat := 4983230072969 + 3 ^ 40 * 5594847 * 2
def baseEnd_5594847 : Nat := 2872845699365576869082273

theorem tailTrace_5594847 : CollatzResearch.WordTrace tailWord_5594847 prefixEnd_5594847 2872845699365576869082273 := by
  unfold tailWord_5594847
  simp only [CollatzResearch.WordTrace]
  refine ⟨204060834361832317639574795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136040556241221545093049863 204060834361832317639574795)
  ·
    refine ⟨306091251542748476459362193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204060834361832317639574795 306091251542748476459362193)
    ·
      refine ⟨229568438657061357344521645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 306091251542748476459362193 229568438657061357344521645)
      ·
        refine ⟨86088164496398009004195617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 229568438657061357344521645 86088164496398009004195617)
        ·
          refine ⟨64566123372298506753146713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86088164496398009004195617 64566123372298506753146713)
          ·
            refine ⟨48424592529223880064860035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64566123372298506753146713 48424592529223880064860035)
            ·
              refine ⟨72636888793835820097290053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48424592529223880064860035 72636888793835820097290053)
              ·
                refine ⟨13619416648844216268241885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72636888793835820097290053 13619416648844216268241885)
                ·
                  refine ⟨5107281243316581100590707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13619416648844216268241885 5107281243316581100590707)
                  ·
                    refine ⟨7660921864974871650886061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5107281243316581100590707 7660921864974871650886061)
                    ·
                      refine ⟨2872845699365576869082273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7660921864974871650886061 2872845699365576869082273)
                      ·
                        rfl

theorem cell23_5594847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 4, 3, 1, 3].length) (baseStart_5594847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5594847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5594847 prefixEnd_5594847 := by exact prefixLift 5594847
  have htrace : WordTrace (prefixWord ++ tailWord_5594847) baseStart_5594847 baseEnd_5594847 := by
    simpa [prefixWord, tailWord_5594847, baseEnd_5594847] using wordTrace_append hprefix tailTrace_5594847
  have hstable : (prefixWord ++ tailWord_5594847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5594847).length < 2 ^ (prefixWord ++ tailWord_5594847).sum := by decide
  have hdescent : baseEnd_5594847 < baseStart_5594847 := by decide
  rcases family_descends (prefixWord ++ tailWord_5594847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5594857 : List Nat := [1, 2, 1, 1, 1, 2, 3, 5, 2, 3, 2]
def baseStart_5594857 : Nat := 118140960795 + 5594857 * 2 ^ 59
def prefixEnd_5594857 : Nat := 4983230072969 + 3 ^ 40 * 5594857 * 2
def baseEnd_5594857 : Nat := 2872850834172121829957227

theorem tailTrace_5594857 : CollatzResearch.WordTrace tailWord_5594857 prefixEnd_5594857 2872850834172121829957227 := by
  unfold tailWord_5594857
  simp only [CollatzResearch.WordTrace]
  refine ⟨204061199091796089347438825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136040799394530726231625883 204061199091796089347438825)
  ·
    refine ⟨153045899318847067010579119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204061199091796089347438825 153045899318847067010579119)
    ·
      refine ⟨229568848978270600515868679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153045899318847067010579119 229568848978270600515868679)
      ·
        refine ⟨344353273467405900773803019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229568848978270600515868679 344353273467405900773803019)
        ·
          refine ⟨516529910201108851160704529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 344353273467405900773803019 516529910201108851160704529)
          ·
            refine ⟨387397432650831638370528397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 516529910201108851160704529 387397432650831638370528397)
            ·
              refine ⟨145274037244061864388948149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 387397432650831638370528397 145274037244061864388948149)
              ·
                refine ⟨13619440991630799786463889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 145274037244061864388948149 13619440991630799786463889)
                ·
                  refine ⟨10214580743723099839847917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13619440991630799786463889 10214580743723099839847917)
                  ·
                    refine ⟨3830467778896162439942969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10214580743723099839847917 3830467778896162439942969)
                    ·
                      refine ⟨2872850834172121829957227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3830467778896162439942969 2872850834172121829957227)
                      ·
                        rfl

theorem cell23_5594857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 5, 2, 3, 2].length) (baseStart_5594857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5594857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5594857 prefixEnd_5594857 := by exact prefixLift 5594857
  have htrace : WordTrace (prefixWord ++ tailWord_5594857) baseStart_5594857 baseEnd_5594857 := by
    simpa [prefixWord, tailWord_5594857, baseEnd_5594857] using wordTrace_append hprefix tailTrace_5594857
  have hstable : (prefixWord ++ tailWord_5594857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5594857).length < 2 ^ (prefixWord ++ tailWord_5594857).sum := by decide
  have hdescent : baseEnd_5594857 < baseStart_5594857 := by decide
  rcases family_descends (prefixWord ++ tailWord_5594857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5594864 : List Nat := [2, 1, 1, 1, 3, 1, 2, 7, 1, 1, 3]
def baseStart_5594864 : Nat := 118140960795 + 5594864 * 2 ^ 59
def prefixEnd_5594864 : Nat := 4983230072969 + 3 ^ 40 * 5594864 * 2
def baseEnd_5594864 : Nat := 2872854428536703302569695

theorem tailTrace_5594864 : CollatzResearch.WordTrace tailWord_5594864 prefixEnd_5594864 2872854428536703302569695 := by
  unfold tailWord_5594864
  simp only [CollatzResearch.WordTrace]
  refine ⟨102030727201385364771471823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136040969601847153028629097 102030727201385364771471823)
  ·
    refine ⟨153046090802078047157207735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102030727201385364771471823 153046090802078047157207735)
    ·
      refine ⟨229569136203117070735811603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153046090802078047157207735 229569136203117070735811603)
      ·
        refine ⟨344353704304675606103717405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229569136203117070735811603 344353704304675606103717405)
        ·
          refine ⟨129132639114253352288894027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 344353704304675606103717405 129132639114253352288894027)
          ·
            refine ⟨193698958671380028433341041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129132639114253352288894027 193698958671380028433341041)
            ·
              refine ⟨145274219003535021325005781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 193698958671380028433341041 145274219003535021325005781)
              ·
                refine ⟨3404864507895352062304823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 145274219003535021325005781 3404864507895352062304823)
                ·
                  refine ⟨5107296761843028093457235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3404864507895352062304823 5107296761843028093457235)
                  ·
                    refine ⟨7660945142764542140185853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5107296761843028093457235 7660945142764542140185853)
                    ·
                      refine ⟨2872854428536703302569695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7660945142764542140185853 2872854428536703302569695)
                      ·
                        rfl

theorem cell23_5594864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 7, 1, 1, 3].length) (baseStart_5594864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5594864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5594864 prefixEnd_5594864 := by exact prefixLift 5594864
  have htrace : WordTrace (prefixWord ++ tailWord_5594864) baseStart_5594864 baseEnd_5594864 := by
    simpa [prefixWord, tailWord_5594864, baseEnd_5594864] using wordTrace_append hprefix tailTrace_5594864
  have hstable : (prefixWord ++ tailWord_5594864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5594864).length < 2 ^ (prefixWord ++ tailWord_5594864).sum := by decide
  have hdescent : baseEnd_5594864 < baseStart_5594864 := by decide
  rcases family_descends (prefixWord ++ tailWord_5594864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5594904 : List Nat := [2, 1, 2, 3, 1, 1, 2, 4, 3, 2, 2]
def baseStart_5594904 : Nat := 118140960795 + 5594904 * 2 ^ 59
def prefixEnd_5594904 : Nat := 4983230072969 + 3 ^ 40 * 5594904 * 2
def baseEnd_5594904 : Nat := 2872874967762883146069511

theorem tailTrace_5594904 : CollatzResearch.WordTrace tailWord_5594904 prefixEnd_5594904 2872874967762883146069511 := by
  unfold tailWord_5594904
  simp only [CollatzResearch.WordTrace]
  refine ⟨102031456661312908187199883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136041942215083877582933177 102031456661312908187199883)
  ·
    refine ⟨153047184991969362280799825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102031456661312908187199883 153047184991969362280799825)
    ·
      refine ⟨114785388743977021710599869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153047184991969362280799825 114785388743977021710599869)
      ·
        refine ⟨43044520778991383141474951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114785388743977021710599869 43044520778991383141474951)
        ·
          refine ⟨64566781168487074712212427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43044520778991383141474951 64566781168487074712212427)
          ·
            refine ⟨96850171752730612068318641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64566781168487074712212427 96850171752730612068318641)
            ·
              refine ⟨72637628814547959051238981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96850171752730612068318641 72637628814547959051238981)
              ·
                refine ⟨13619555402727742322107309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72637628814547959051238981 13619555402727742322107309)
                ·
                  refine ⟨5107333276022903370790241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13619555402727742322107309 5107333276022903370790241)
                  ·
                    refine ⟨3830499957017177528092681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5107333276022903370790241 3830499957017177528092681)
                    ·
                      refine ⟨2872874967762883146069511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3830499957017177528092681 2872874967762883146069511)
                      ·
                        rfl

theorem cell23_5594904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 4, 3, 2, 2].length) (baseStart_5594904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5594904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5594904 prefixEnd_5594904 := by exact prefixLift 5594904
  have htrace : WordTrace (prefixWord ++ tailWord_5594904) baseStart_5594904 baseEnd_5594904 := by
    simpa [prefixWord, tailWord_5594904, baseEnd_5594904] using wordTrace_append hprefix tailTrace_5594904
  have hstable : (prefixWord ++ tailWord_5594904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5594904).length < 2 ^ (prefixWord ++ tailWord_5594904).sum := by decide
  have hdescent : baseEnd_5594904 < baseStart_5594904 := by decide
  rcases family_descends (prefixWord ++ tailWord_5594904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5594917 : List Nat := [1, 3, 1, 2, 3, 3, 1, 2, 1, 2, 4]
def baseStart_5594917 : Nat := 118140960795 + 5594917 * 2 ^ 59
def prefixEnd_5594917 : Nat := 4983230072969 + 3 ^ 40 * 5594917 * 2
def baseEnd_5594917 : Nat := 2872881643011391595206951

theorem tailTrace_5594917 : CollatzResearch.WordTrace tailWord_5594917 prefixEnd_5594917 2872881643011391595206951 := by
  unfold tailWord_5594917
  simp only [CollatzResearch.WordTrace]
  refine ⟨204063387471578719594623005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136042258314385813063082003 204063387471578719594623005)
  ·
    refine ⟨76523770301842019847983627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 204063387471578719594623005 76523770301842019847983627)
    ·
      refine ⟨114785655452763029771975441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76523770301842019847983627 114785655452763029771975441)
      ·
        refine ⟨86089241589572272328981581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114785655452763029771975441 86089241589572272328981581)
        ·
          refine ⟨32283465596089602123368093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86089241589572272328981581 32283465596089602123368093)
          ·
            refine ⟨12106299598533600796263035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32283465596089602123368093 12106299598533600796263035)
            ·
              refine ⟨18159449397800401194394553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12106299598533600796263035 18159449397800401194394553)
              ·
                refine ⟨13619587048350300895795915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18159449397800401194394553 13619587048350300895795915)
                ·
                  refine ⟨20429380572525451343693873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13619587048350300895795915 20429380572525451343693873)
                  ·
                    refine ⟨15322035429394088507770405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20429380572525451343693873 15322035429394088507770405)
                    ·
                      refine ⟨2872881643011391595206951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15322035429394088507770405 2872881643011391595206951)
                      ·
                        rfl

theorem cell23_5594917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 2, 1, 2, 4].length) (baseStart_5594917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5594917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5594917 prefixEnd_5594917 := by exact prefixLift 5594917
  have htrace : WordTrace (prefixWord ++ tailWord_5594917) baseStart_5594917 baseEnd_5594917 := by
    simpa [prefixWord, tailWord_5594917, baseEnd_5594917] using wordTrace_append hprefix tailTrace_5594917
  have hstable : (prefixWord ++ tailWord_5594917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5594917).length < 2 ^ (prefixWord ++ tailWord_5594917).sum := by decide
  have hdescent : baseEnd_5594917 < baseStart_5594917 := by decide
  rcases family_descends (prefixWord ++ tailWord_5594917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5594938 : List Nat := [3, 1, 1, 1, 5, 2, 1, 4, 1, 2, 2]
def baseStart_5594938 : Nat := 118140960795 + 5594938 * 2 ^ 59
def prefixEnd_5594938 : Nat := 4983230072969 + 3 ^ 40 * 5594938 * 2
def baseEnd_5594938 : Nat := 2872892426105136013044355

theorem tailTrace_5594938 : CollatzResearch.WordTrace tailWord_5594938 prefixEnd_5594938 2872892426105136013044355 := by
  unfold tailWord_5594938
  simp only [CollatzResearch.WordTrace]
  refine ⟨51016038351125660045284367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136042768936335093454091645 51016038351125660045284367)
  ·
    refine ⟨76524057526688490067926551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51016038351125660045284367 76524057526688490067926551)
    ·
      refine ⟨114786086290032735101889827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76524057526688490067926551 114786086290032735101889827)
      ·
        refine ⟨172179129435049102652834741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114786086290032735101889827 172179129435049102652834741)
        ·
          refine ⟨16141793384535853373703257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 172179129435049102652834741 16141793384535853373703257)
          ·
            refine ⟨12106345038401890030277443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16141793384535853373703257 12106345038401890030277443)
            ·
              refine ⟨18159517557602835045416165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12106345038401890030277443 18159517557602835045416165)
              ·
                refine ⟨3404909542050531571015531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18159517557602835045416165 3404909542050531571015531)
                ·
                  refine ⟨5107364313075797356523297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3404909542050531571015531 5107364313075797356523297)
                  ·
                    refine ⟨3830523234806848017392473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5107364313075797356523297 3830523234806848017392473)
                    ·
                      refine ⟨2872892426105136013044355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3830523234806848017392473 2872892426105136013044355)
                      ·
                        rfl

theorem cell23_5594938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 4, 1, 2, 2].length) (baseStart_5594938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5594938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5594938 prefixEnd_5594938 := by exact prefixLift 5594938
  have htrace : WordTrace (prefixWord ++ tailWord_5594938) baseStart_5594938 baseEnd_5594938 := by
    simpa [prefixWord, tailWord_5594938, baseEnd_5594938] using wordTrace_append hprefix tailTrace_5594938
  have hstable : (prefixWord ++ tailWord_5594938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5594938).length < 2 ^ (prefixWord ++ tailWord_5594938).sum := by decide
  have hdescent : baseEnd_5594938 < baseStart_5594938 := by decide
  rcases family_descends (prefixWord ++ tailWord_5594938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5594940 : List Nat := [2, 2, 2, 2, 1, 1, 3, 1, 2, 7]
def baseStart_5594940 : Nat := 118140960795 + 5594940 * 2 ^ 59
def prefixEnd_5594940 : Nat := 4983230072969 + 3 ^ 40 * 5594940 * 2
def baseEnd_5594940 : Nat := 957631151022148335073115

theorem tailTrace_5594940 : CollatzResearch.WordTrace tailWord_5594940 prefixEnd_5594940 957631151022148335073115 := by
  unfold tailWord_5594940
  simp only [CollatzResearch.WordTrace]
  refine ⟨102032113175247697261355137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136042817566996929681806849 102032113175247697261355137)
  ·
    refine ⟨76524084881435772946016353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102032113175247697261355137 76524084881435772946016353)
    ·
      refine ⟨57393063661076829709512265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76524084881435772946016353 57393063661076829709512265)
      ·
        refine ⟨43044797745807622282134199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57393063661076829709512265 43044797745807622282134199)
        ·
          refine ⟨64567196618711433423201299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43044797745807622282134199 64567196618711433423201299)
          ·
            refine ⟨96850794928067150134801949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64567196618711433423201299 96850794928067150134801949)
            ·
              refine ⟨36319048098025181300550731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96850794928067150134801949 36319048098025181300550731)
              ·
                refine ⟨54478572147037771950826097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36319048098025181300550731 54478572147037771950826097)
                ·
                  refine ⟨40858929110278328963119573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54478572147037771950826097 40858929110278328963119573)
                  ·
                    refine ⟨957631151022148335073115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40858929110278328963119573 957631151022148335073115)
                    ·
                      rfl

theorem cell23_5594940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 1, 2, 7].length) (baseStart_5594940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5594940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5594940 prefixEnd_5594940 := by exact prefixLift 5594940
  have htrace : WordTrace (prefixWord ++ tailWord_5594940) baseStart_5594940 baseEnd_5594940 := by
    simpa [prefixWord, tailWord_5594940, baseEnd_5594940] using wordTrace_append hprefix tailTrace_5594940
  have hstable : (prefixWord ++ tailWord_5594940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5594940).length < 2 ^ (prefixWord ++ tailWord_5594940).sum := by decide
  have hdescent : baseEnd_5594940 < baseStart_5594940 := by decide
  rcases family_descends (prefixWord ++ tailWord_5594940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5594954 : List Nat := [3, 1, 2, 1, 1, 1, 3, 5, 2, 1, 3]
def baseStart_5594954 : Nat := 118140960795 + 5594954 * 2 ^ 59
def prefixEnd_5594954 : Nat := 4983230072969 + 3 ^ 40 * 5594954 * 2
def baseEnd_5594954 : Nat := 2872900641795607950444281

theorem tailTrace_5594954 : CollatzResearch.WordTrace tailWord_5594954 prefixEnd_5594954 2872900641795607950444281 := by
  unfold tailWord_5594954
  simp only [CollatzResearch.WordTrace]
  refine ⟨51016184243111168728429979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136043157981629783275813277 51016184243111168728429979)
  ·
    refine ⟨76524276364666753092644969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51016184243111168728429979 76524276364666753092644969)
    ·
      refine ⟨57393207273500064819483727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76524276364666753092644969 57393207273500064819483727)
      ·
        refine ⟨86089810910250097229225591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57393207273500064819483727 86089810910250097229225591)
        ·
          refine ⟨129134716365375145843838387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86089810910250097229225591 129134716365375145843838387)
          ·
            refine ⟨193702074548062718765757581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129134716365375145843838387 193702074548062718765757581)
            ·
              refine ⟨72638277955523519537159093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 193702074548062718765757581 72638277955523519537159093)
              ·
                refine ⟨6809838558330329956608665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 72638277955523519537159093 6809838558330329956608665)
                ·
                  refine ⟨5107378918747747467456499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6809838558330329956608665 5107378918747747467456499)
                  ·
                    refine ⟨7661068378121621201184749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5107378918747747467456499 7661068378121621201184749)
                    ·
                      refine ⟨2872900641795607950444281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7661068378121621201184749 2872900641795607950444281)
                      ·
                        rfl

theorem cell23_5594954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 5, 2, 1, 3].length) (baseStart_5594954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5594954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5594954 prefixEnd_5594954 := by exact prefixLift 5594954
  have htrace : WordTrace (prefixWord ++ tailWord_5594954) baseStart_5594954 baseEnd_5594954 := by
    simpa [prefixWord, tailWord_5594954, baseEnd_5594954] using wordTrace_append hprefix tailTrace_5594954
  have hstable : (prefixWord ++ tailWord_5594954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5594954).length < 2 ^ (prefixWord ++ tailWord_5594954).sum := by decide
  have hdescent : baseEnd_5594954 < baseStart_5594954 := by decide
  rcases family_descends (prefixWord ++ tailWord_5594954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5594960 : List Nat := [2, 1, 1, 1, 1, 4, 1, 1, 4, 3, 4]
def baseStart_5594960 : Nat := 118140960795 + 5594960 * 2 ^ 59
def prefixEnd_5594960 : Nat := 4983230072969 + 3 ^ 40 * 5594960 * 2
def baseEnd_5594960 : Nat := 2872903722679534926969253

theorem tailTrace_5594960 : CollatzResearch.WordTrace tailWord_5594960 prefixEnd_5594960 2872903722679534926969253 := by
  unfold tailWord_5594960
  simp only [CollatzResearch.WordTrace]
  refine ⟨102032477905211468969219167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136043303873615291958958889 102032477905211468969219167)
  ·
    refine ⟨153048716857817203453828751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102032477905211468969219167 153048716857817203453828751)
    ·
      refine ⟨229573075286725805180743127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153048716857817203453828751 229573075286725805180743127)
      ·
        refine ⟨344359612930088707771114691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229573075286725805180743127 344359612930088707771114691)
        ·
          refine ⟨516539419395133061656672037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 344359612930088707771114691 516539419395133061656672037)
          ·
            refine ⟨96851141136587449060626007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 516539419395133061656672037 96851141136587449060626007)
            ·
              refine ⟨145276711704881173590939011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96851141136587449060626007 145276711704881173590939011)
              ·
                refine ⟨217915067557321760386408517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 145276711704881173590939011 217915067557321760386408517)
                ·
                  refine ⟨40859075166997830072451597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 217915067557321760386408517 40859075166997830072451597)
                  ·
                    refine ⟨15322153187624186277169349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40859075166997830072451597 15322153187624186277169349)
                    ·
                      refine ⟨2872903722679534926969253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15322153187624186277169349 2872903722679534926969253)
                      ·
                        rfl

theorem cell23_5594960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3, 4].length) (baseStart_5594960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5594960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5594960 prefixEnd_5594960 := by exact prefixLift 5594960
  have htrace : WordTrace (prefixWord ++ tailWord_5594960) baseStart_5594960 baseEnd_5594960 := by
    simpa [prefixWord, tailWord_5594960, baseEnd_5594960] using wordTrace_append hprefix tailTrace_5594960
  have hstable : (prefixWord ++ tailWord_5594960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5594960).length < 2 ^ (prefixWord ++ tailWord_5594960).sum := by decide
  have hdescent : baseEnd_5594960 < baseStart_5594960 := by decide
  rcases family_descends (prefixWord ++ tailWord_5594960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5594970 : List Nat := [3, 1, 1, 2, 1, 3, 1, 2, 1, 8]
def baseStart_5594970 : Nat := 118140960795 + 5594970 * 2 ^ 59
def prefixEnd_5594970 : Nat := 4983230072969 + 3 ^ 40 * 5594970 * 2
def baseEnd_5594970 : Nat := 957636285828693295948069

theorem tailTrace_5594970 : CollatzResearch.WordTrace tailWord_5594970 prefixEnd_5594970 957636285828693295948069 := by
  unfold tailWord_5594970
  simp only [CollatzResearch.WordTrace]
  refine ⟨51016330135096677411575591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136043547026924473097534909 51016330135096677411575591)
  ·
    refine ⟨76524495202645016117363387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51016330135096677411575591 76524495202645016117363387)
    ·
      refine ⟨114786742803967524176045081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76524495202645016117363387 114786742803967524176045081)
      ·
        refine ⟨86090057102975643132033811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114786742803967524176045081 86090057102975643132033811)
        ·
          refine ⟨129135085654463464698050717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86090057102975643132033811 129135085654463464698050717)
          ·
            refine ⟨48425657120423799261769019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 129135085654463464698050717 48425657120423799261769019)
            ·
              refine ⟨72638485680635698892653529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48425657120423799261769019 72638485680635698892653529)
              ·
                refine ⟨54478864260476774169490147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72638485680635698892653529 54478864260476774169490147)
                ·
                  refine ⟨81718296390715161254235221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54478864260476774169490147 81718296390715161254235221)
                  ·
                    refine ⟨957636285828693295948069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 81718296390715161254235221 957636285828693295948069)
                    ·
                      rfl

theorem cell23_5594970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 2, 1, 8].length) (baseStart_5594970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5594970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5594970 prefixEnd_5594970 := by exact prefixLift 5594970
  have htrace : WordTrace (prefixWord ++ tailWord_5594970) baseStart_5594970 baseEnd_5594970 := by
    simpa [prefixWord, tailWord_5594970, baseEnd_5594970] using wordTrace_append hprefix tailTrace_5594970
  have hstable : (prefixWord ++ tailWord_5594970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5594970).length < 2 ^ (prefixWord ++ tailWord_5594970).sum := by decide
  have hdescent : baseEnd_5594970 < baseStart_5594970 := by decide
  rcases family_descends (prefixWord ++ tailWord_5594970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5595011 : List Nat := [1, 1, 1, 3, 4, 4, 1, 1, 1, 4, 2]
def baseStart_5595011 : Nat := 118140960795 + 5595011 * 2 ^ 59
def prefixEnd_5595011 : Nat := 4983230072969 + 3 ^ 40 * 5595011 * 2
def baseEnd_5595011 : Nat := 2872929910192914227431519

theorem tailTrace_5595011 : CollatzResearch.WordTrace tailWord_5595011 prefixEnd_5595011 2872929910192914227431519 := by
  unfold tailWord_5595011
  simp only [CollatzResearch.WordTrace]
  refine ⟨204066815933238173648544887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136044543955492115765696591 204066815933238173648544887)
  ·
    refine ⟨306100223899857260472817331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204066815933238173648544887 306100223899857260472817331)
    ·
      refine ⟨459150335849785890709225997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 306100223899857260472817331 459150335849785890709225997)
      ·
        refine ⟨172181375943669709015959749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 459150335849785890709225997 172181375943669709015959749)
        ·
          refine ⟨32284007989438070440492453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 172181375943669709015959749 32284007989438070440492453)
          ·
            refine ⟨6053251498019638207592335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32284007989438070440492453 6053251498019638207592335)
            ·
              refine ⟨9079877247029457311388503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6053251498019638207592335 9079877247029457311388503)
              ·
                refine ⟨13619815870544185967082755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9079877247029457311388503 13619815870544185967082755)
                ·
                  refine ⟨20429723805816278950624133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13619815870544185967082755 20429723805816278950624133)
                  ·
                    refine ⟨3830573213590552303242025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20429723805816278950624133 3830573213590552303242025)
                    ·
                      refine ⟨2872929910192914227431519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3830573213590552303242025 2872929910192914227431519)
                      ·
                        rfl

theorem cell23_5595011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 1, 1, 1, 4, 2].length) (baseStart_5595011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5595011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5595011 prefixEnd_5595011 := by exact prefixLift 5595011
  have htrace : WordTrace (prefixWord ++ tailWord_5595011) baseStart_5595011 baseEnd_5595011 := by
    simpa [prefixWord, tailWord_5595011, baseEnd_5595011] using wordTrace_append hprefix tailTrace_5595011
  have hstable : (prefixWord ++ tailWord_5595011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5595011).length < 2 ^ (prefixWord ++ tailWord_5595011).sum := by decide
  have hdescent : baseEnd_5595011 < baseStart_5595011 := by decide
  rcases family_descends (prefixWord ++ tailWord_5595011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5595057 : List Nat := [1, 2, 2, 4, 2, 1, 1, 1, 1, 1, 7]
def baseStart_5595057 : Nat := 118140960795 + 5595057 * 2 ^ 59
def prefixEnd_5595057 : Nat := 4983230072969 + 3 ^ 40 * 5595057 * 2
def baseEnd_5595057 : Nat := 2872953530303021047456307

theorem tailTrace_5595057 : CollatzResearch.WordTrace tailWord_5595057 prefixEnd_5595057 2872953530303021047456307 := by
  unfold tailWord_5595057
  simp only [CollatzResearch.WordTrace]
  refine ⟨204068493691071523504719425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136045662460714349003146283 204068493691071523504719425)
  ·
    refine ⟨153051370268303642628539569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204068493691071523504719425 153051370268303642628539569)
    ·
      refine ⟨114788527701227731971404677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153051370268303642628539569 114788527701227731971404677)
      ·
        refine ⟨21522848943980199744638377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 114788527701227731971404677 21522848943980199744638377)
        ·
          refine ⟨16142136707985149808478783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21522848943980199744638377 16142136707985149808478783)
          ·
            refine ⟨24213205061977724712718175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16142136707985149808478783 24213205061977724712718175)
            ·
              refine ⟨36319807592966587069077263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24213205061977724712718175 36319807592966587069077263)
              ·
                refine ⟨54479711389449880603615895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36319807592966587069077263 54479711389449880603615895)
                ·
                  refine ⟨81719567084174820905423843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54479711389449880603615895 81719567084174820905423843)
                  ·
                    refine ⟨122579350626262231358135765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 81719567084174820905423843 122579350626262231358135765)
                    ·
                      refine ⟨2872953530303021047456307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 122579350626262231358135765 2872953530303021047456307)
                      ·
                        rfl

theorem cell23_5595057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_5595057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5595057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5595057 prefixEnd_5595057 := by exact prefixLift 5595057
  have htrace : WordTrace (prefixWord ++ tailWord_5595057) baseStart_5595057 baseEnd_5595057 := by
    simpa [prefixWord, tailWord_5595057, baseEnd_5595057] using wordTrace_append hprefix tailTrace_5595057
  have hstable : (prefixWord ++ tailWord_5595057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5595057).length < 2 ^ (prefixWord ++ tailWord_5595057).sum := by decide
  have hdescent : baseEnd_5595057 < baseStart_5595057 := by decide
  rcases family_descends (prefixWord ++ tailWord_5595057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5595084 : List Nat := [2, 2, 1, 4, 1, 2, 1, 3, 2, 1, 4]
def baseStart_5595084 : Nat := 118140960795 + 5595084 * 2 ^ 59
def prefixEnd_5595084 : Nat := 4983230072969 + 3 ^ 40 * 5595084 * 2
def baseEnd_5595084 : Nat := 2872967394280692441818683

theorem tailTrace_5595084 : CollatzResearch.WordTrace tailWord_5595084 prefixEnd_5595084 2872967394280692441818683 := by
  unfold tailWord_5595084
  simp only [CollatzResearch.WordTrace]
  refine ⟨102034739230986853557976153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136046318974649138077301537 102034739230986853557976153)
  ·
    refine ⟨76526054423240140168482115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102034739230986853557976153 76526054423240140168482115)
    ·
      refine ⟨114789081634860210252723173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76526054423240140168482115 114789081634860210252723173)
      ·
        refine ⟨21522952806536289422385595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 114789081634860210252723173 21522952806536289422385595)
        ·
          refine ⟨32284429209804434133578393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21522952806536289422385595 32284429209804434133578393)
          ·
            refine ⟨24213321907353325600183795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32284429209804434133578393 24213321907353325600183795)
            ·
              refine ⟨36319982861029988400275693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24213321907353325600183795 36319982861029988400275693)
              ·
                refine ⟨13619993572886245650103385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36319982861029988400275693 13619993572886245650103385)
                ·
                  refine ⟨10214995179664684237577539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13619993572886245650103385 10214995179664684237577539)
                  ·
                    refine ⟨15322492769497026356366309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10214995179664684237577539 15322492769497026356366309)
                    ·
                      refine ⟨2872967394280692441818683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15322492769497026356366309 2872967394280692441818683)
                      ·
                        rfl

theorem cell23_5595084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_5595084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5595084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5595084 prefixEnd_5595084 := by exact prefixLift 5595084
  have htrace : WordTrace (prefixWord ++ tailWord_5595084) baseStart_5595084 baseEnd_5595084 := by
    simpa [prefixWord, tailWord_5595084, baseEnd_5595084] using wordTrace_append hprefix tailTrace_5595084
  have hstable : (prefixWord ++ tailWord_5595084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5595084).length < 2 ^ (prefixWord ++ tailWord_5595084).sum := by decide
  have hdescent : baseEnd_5595084 < baseStart_5595084 := by decide
  rcases family_descends (prefixWord ++ tailWord_5595084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5595184 : List Nat := [2, 1, 1, 1, 2, 5, 3, 1, 1, 6]
def baseStart_5595184 : Nat := 118140960795 + 5595184 * 2 ^ 59
def prefixEnd_5595184 : Nat := 4983230072969 + 3 ^ 40 * 5595184 * 2
def baseEnd_5595184 : Nat := 957672914115380683522741

theorem tailTrace_5595184 : CollatzResearch.WordTrace tailWord_5595184 prefixEnd_5595184 957672914115380683522741 := by
  unfold tailWord_5595184
  simp only [CollatzResearch.WordTrace]
  refine ⟨102036562880805712097296303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136048750507740949463061737 102036562880805712097296303)
  ·
    refine ⟨153054844321208568145944455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102036562880805712097296303 153054844321208568145944455)
    ·
      refine ⟨229582266481812852218916683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153054844321208568145944455 229582266481812852218916683)
      ·
        refine ⟨344373399722719278328375025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229582266481812852218916683 344373399722719278328375025)
        ·
          refine ⟨258280049792039458746281269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 344373399722719278328375025 258280049792039458746281269)
          ·
            refine ⟨24213754668003699257463869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 258280049792039458746281269 24213754668003699257463869)
            ·
              refine ⟨9080158000501387221548951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24213754668003699257463869 9080158000501387221548951)
              ·
                refine ⟨13620237000752080832323427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9080158000501387221548951 13620237000752080832323427)
                ·
                  refine ⟨20430355501128121248485141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13620237000752080832323427 20430355501128121248485141)
                  ·
                    refine ⟨957672914115380683522741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20430355501128121248485141 957672914115380683522741)
                    ·
                      rfl

theorem cell23_5595184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3, 1, 1, 6].length) (baseStart_5595184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5595184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5595184 prefixEnd_5595184 := by exact prefixLift 5595184
  have htrace : WordTrace (prefixWord ++ tailWord_5595184) baseStart_5595184 baseEnd_5595184 := by
    simpa [prefixWord, tailWord_5595184, baseEnd_5595184] using wordTrace_append hprefix tailTrace_5595184
  have hstable : (prefixWord ++ tailWord_5595184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5595184).length < 2 ^ (prefixWord ++ tailWord_5595184).sum := by decide
  have hdescent : baseEnd_5595184 < baseStart_5595184 := by decide
  rcases family_descends (prefixWord ++ tailWord_5595184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5595201 : List Nat := [1, 2, 5, 1, 2, 1, 1, 2, 4, 4]
def baseStart_5595201 : Nat := 118140960795 + 5595201 * 2 ^ 59
def prefixEnd_5595201 : Nat := 4983230072969 + 3 ^ 40 * 5595201 * 2
def baseEnd_5595201 : Nat := 957675823839089494685215

theorem tailTrace_5595201 : CollatzResearch.WordTrace tailWord_5595201 prefixEnd_5595201 957675823839089494685215 := by
  unfold tailWord_5595201
  simp only [CollatzResearch.WordTrace]
  refine ⟨204073745802549836097961457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136049163868366557398640971 204073745802549836097961457)
  ·
    refine ⟨153055309351912377073471093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204073745802549836097961457 153055309351912377073471093)
    ·
      refine ⟨14348935251741785350637915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 153055309351912377073471093 14348935251741785350637915)
      ·
        refine ⟨21523402877612678025956873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14348935251741785350637915 21523402877612678025956873)
        ·
          refine ⟨16142552158209508519467655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21523402877612678025956873 16142552158209508519467655)
          ·
            refine ⟨24213828237314262779201483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16142552158209508519467655 24213828237314262779201483)
            ·
              refine ⟨36320742355971394168802225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24213828237314262779201483 36320742355971394168802225)
              ·
                refine ⟨27240556766978545626601669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36320742355971394168802225 27240556766978545626601669)
                ·
                  refine ⟨5107604393808477304987813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27240556766978545626601669 5107604393808477304987813)
                  ·
                    refine ⟨957675823839089494685215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5107604393808477304987813 957675823839089494685215)
                    ·
                      rfl

theorem cell23_5595201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 2, 4, 4].length) (baseStart_5595201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5595201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5595201 prefixEnd_5595201 := by exact prefixLift 5595201
  have htrace : WordTrace (prefixWord ++ tailWord_5595201) baseStart_5595201 baseEnd_5595201 := by
    simpa [prefixWord, tailWord_5595201, baseEnd_5595201] using wordTrace_append hprefix tailTrace_5595201
  have hstable : (prefixWord ++ tailWord_5595201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5595201).length < 2 ^ (prefixWord ++ tailWord_5595201).sum := by decide
  have hdescent : baseEnd_5595201 < baseStart_5595201 := by decide
  rcases family_descends (prefixWord ++ tailWord_5595201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5595214 : List Nat := [4, 1, 1, 1, 1, 6, 9]
def baseStart_5595214 : Nat := 118140960795 + 5595214 * 2 ^ 59
def prefixEnd_5595214 : Nat := 4983230072969 + 3 ^ 40 * 5595214 * 2
def baseEnd_5595214 : Nat := 35469557367478727570285

theorem tailTrace_5595214 : CollatzResearch.WordTrace tailWord_5595214 prefixEnd_5595214 35469557367478727570285 := by
  unfold tailWord_5595214
  simp only [CollatzResearch.WordTrace]
  refine ⟨25509277493937842414773087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136049479967668492878789797 25509277493937842414773087)
  ·
    refine ⟨38263916240906763622159631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25509277493937842414773087 38263916240906763622159631)
    ·
      refine ⟨57395874361360145433239447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38263916240906763622159631 57395874361360145433239447)
      ·
        refine ⟨86093811542040218149859171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57395874361360145433239447 86093811542040218149859171)
        ·
          refine ⟨129140717313060327224788757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86093811542040218149859171 129140717313060327224788757)
          ·
            refine ⟨6053471124049702838661973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 129140717313060327224788757 6053471124049702838661973)
            ·
              refine ⟨35469557367478727570285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6053471124049702838661973 35469557367478727570285)
              ·
                rfl

theorem cell23_5595214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 9].length) (baseStart_5595214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5595214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5595214 prefixEnd_5595214 := by exact prefixLift 5595214
  have htrace : WordTrace (prefixWord ++ tailWord_5595214) baseStart_5595214 baseEnd_5595214 := by
    simpa [prefixWord, tailWord_5595214, baseEnd_5595214] using wordTrace_append hprefix tailTrace_5595214
  have hstable : (prefixWord ++ tailWord_5595214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5595214).length < 2 ^ (prefixWord ++ tailWord_5595214).sum := by decide
  have hdescent : baseEnd_5595214 < baseStart_5595214 := by decide
  rcases family_descends (prefixWord ++ tailWord_5595214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5595332 : List Nat := [2, 3, 3, 1, 2, 1, 3, 2, 2, 2, 2]
def baseStart_5595332 : Nat := 118140960795 + 5595332 * 2 ^ 59
def prefixEnd_5595332 : Nat := 4983230072969 + 3 ^ 40 * 5595332 * 2
def baseEnd_5595332 : Nat := 2873094737483007471517543

theorem tailTrace_5595332 : CollatzResearch.WordTrace tailWord_5595332 prefixEnd_5595332 2873094737483007471517543 := by
  unfold tailWord_5595332
  simp only [CollatzResearch.WordTrace]
  refine ⟨102039261882537622735490125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136052349176716830313986833 102039261882537622735490125)
  ·
    refine ⟨38264723205951608525808797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102039261882537622735490125 38264723205951608525808797)
    ·
      refine ⟨14349271202231853197178299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38264723205951608525808797 14349271202231853197178299)
      ·
        refine ⟨21523906803347779795767449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14349271202231853197178299 21523906803347779795767449)
        ·
          refine ⟨16142930102510834846825587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21523906803347779795767449 16142930102510834846825587)
          ·
            refine ⟨24214395153766252270238381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16142930102510834846825587 24214395153766252270238381)
            ·
              refine ⟨9080398182662344601339393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24214395153766252270238381 9080398182662344601339393)
              ·
                refine ⟨6810298636996758451004545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9080398182662344601339393 6810298636996758451004545)
                ·
                  refine ⟨5107723977747568838253409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6810298636996758451004545 5107723977747568838253409)
                  ·
                    refine ⟨3830792983310676628690057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5107723977747568838253409 3830792983310676628690057)
                    ·
                      refine ⟨2873094737483007471517543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3830792983310676628690057 2873094737483007471517543)
                      ·
                        rfl

theorem cell23_5595332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3, 2, 2, 2, 2].length) (baseStart_5595332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5595332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5595332 prefixEnd_5595332 := by exact prefixLift 5595332
  have htrace : WordTrace (prefixWord ++ tailWord_5595332) baseStart_5595332 baseEnd_5595332 := by
    simpa [prefixWord, tailWord_5595332, baseEnd_5595332] using wordTrace_append hprefix tailTrace_5595332
  have hstable : (prefixWord ++ tailWord_5595332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5595332).length < 2 ^ (prefixWord ++ tailWord_5595332).sum := by decide
  have hdescent : baseEnd_5595332 < baseStart_5595332 := by decide
  rcases family_descends (prefixWord ++ tailWord_5595332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5595349 : List Nat := [1, 3, 2, 4, 2, 1, 3, 1, 2, 2, 2]
def baseStart_5595349 : Nat := 118140960795 + 5595349 * 2 ^ 59
def prefixEnd_5595349 : Nat := 4983230072969 + 3 ^ 40 * 5595349 * 2
def baseEnd_5595349 : Nat := 2873103466654133905004965

theorem tailTrace_5595349 : CollatzResearch.WordTrace tailWord_5595349 prefixEnd_5595349 2873103466654133905004965 := by
  unfold tailWord_5595349
  simp only [CollatzResearch.WordTrace]
  refine ⟨204079143806013657374349101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136052762537342438249566067 204079143806013657374349101)
  ·
    refine ⟨76529678927255121515380913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 204079143806013657374349101 76529678927255121515380913)
    ·
      refine ⟨57397259195441341136535685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76529678927255121515380913 57397259195441341136535685)
      ·
        refine ⟨10761986099145251463100441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57397259195441341136535685 10761986099145251463100441)
        ·
          refine ⟨8071489574358938597325331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10761986099145251463100441 8071489574358938597325331)
          ·
            refine ⟨12107234361538407895987997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8071489574358938597325331 12107234361538407895987997)
            ·
              refine ⟨4540212885576902960995499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12107234361538407895987997 4540212885576902960995499)
              ·
                refine ⟨6810319328365354441493249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4540212885576902960995499 6810319328365354441493249)
                ·
                  refine ⟨5107739496274015831119937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6810319328365354441493249 5107739496274015831119937)
                  ·
                    refine ⟨3830804622205511873339953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5107739496274015831119937 3830804622205511873339953)
                    ·
                      refine ⟨2873103466654133905004965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3830804622205511873339953 2873103466654133905004965)
                      ·
                        rfl

theorem cell23_5595349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 3, 1, 2, 2, 2].length) (baseStart_5595349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5595349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5595349 prefixEnd_5595349 := by exact prefixLift 5595349
  have htrace : WordTrace (prefixWord ++ tailWord_5595349) baseStart_5595349 baseEnd_5595349 := by
    simpa [prefixWord, tailWord_5595349, baseEnd_5595349] using wordTrace_append hprefix tailTrace_5595349
  have hstable : (prefixWord ++ tailWord_5595349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5595349).length < 2 ^ (prefixWord ++ tailWord_5595349).sum := by decide
  have hdescent : baseEnd_5595349 < baseStart_5595349 := by decide
  rcases family_descends (prefixWord ++ tailWord_5595349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5595364 : List Nat := [2, 3, 1, 1, 1, 2, 1, 1, 1, 10]
def baseStart_5595364 : Nat := 118140960795 + 5595364 * 2 ^ 59
def prefixEnd_5595364 : Nat := 4983230072969 + 3 ^ 40 * 5595364 * 2
def baseEnd_5595364 : Nat := 957703722954650448772465

theorem tailTrace_5595364 : CollatzResearch.WordTrace tailWord_5595364 prefixEnd_5595364 957703722954650448772465 := by
  unfold tailWord_5595364
  simp only [CollatzResearch.WordTrace]
  refine ⟨102039845450479657468072573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136053127267306209957430097 102039845450479657468072573)
  ·
    refine ⟨38264942043929871550527215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102039845450479657468072573 38264942043929871550527215)
    ·
      refine ⟨57397413065894807325790823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38264942043929871550527215 57397413065894807325790823)
      ·
        refine ⟨86096119598842210988686235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57397413065894807325790823 86096119598842210988686235)
        ·
          refine ⟨129144179398263316483029353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86096119598842210988686235 129144179398263316483029353)
          ·
            refine ⟨96858134548697487362272015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129144179398263316483029353 96858134548697487362272015)
            ·
              refine ⟨145287201823046231043408023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96858134548697487362272015 145287201823046231043408023)
              ·
                refine ⟨217930802734569346565112035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 145287201823046231043408023 217930802734569346565112035)
                ·
                  refine ⟨326896204101854019847668053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 217930802734569346565112035 326896204101854019847668053)
                  ·
                    refine ⟨957703722954650448772465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 326896204101854019847668053 957703722954650448772465)
                    ·
                      rfl

theorem cell23_5595364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 1, 10].length) (baseStart_5595364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5595364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5595364 prefixEnd_5595364 := by exact prefixLift 5595364
  have htrace : WordTrace (prefixWord ++ tailWord_5595364) baseStart_5595364 baseEnd_5595364 := by
    simpa [prefixWord, tailWord_5595364, baseEnd_5595364] using wordTrace_append hprefix tailTrace_5595364
  have hstable : (prefixWord ++ tailWord_5595364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5595364).length < 2 ^ (prefixWord ++ tailWord_5595364).sum := by decide
  have hdescent : baseEnd_5595364 < baseStart_5595364 := by decide
  rcases family_descends (prefixWord ++ tailWord_5595364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5595371 : List Nat := [1, 1, 1, 1, 2, 5, 2, 3, 2, 1, 4]
def baseStart_5595371 : Nat := 118140960795 + 5595371 * 2 ^ 59
def prefixEnd_5595371 : Nat := 4983230072969 + 3 ^ 40 * 5595371 * 2
def baseEnd_5595371 : Nat := 2873114763228532818929863

theorem tailTrace_5595371 : CollatzResearch.WordTrace tailWord_5595371 prefixEnd_5595371 2873114763228532818929863 := by
  unfold tailWord_5595371
  simp only [CollatzResearch.WordTrace]
  refine ⟨204079946211933955131649967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136053297474622636754433311 204079946211933955131649967)
  ·
    refine ⟨306119919317900932697474951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204079946211933955131649967 306119919317900932697474951)
    ·
      refine ⟨459179878976851399046212427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 306119919317900932697474951 459179878976851399046212427)
      ·
        refine ⟨688769818465277098569318641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 459179878976851399046212427 688769818465277098569318641)
        ·
          refine ⟨516577363848957823926988981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 688769818465277098569318641 516577363848957823926988981)
          ·
            refine ⟨48429127860839795993155217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 516577363848957823926988981 48429127860839795993155217)
            ·
              refine ⟨36321845895629846994866413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48429127860839795993155217 36321845895629846994866413)
              ·
                refine ⟨13620692210861192623074905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36321845895629846994866413 13620692210861192623074905)
                ·
                  refine ⟨10215519158145894467306179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13620692210861192623074905 10215519158145894467306179)
                  ·
                    refine ⟨15323278737218841700959269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10215519158145894467306179 15323278737218841700959269)
                    ·
                      refine ⟨2873114763228532818929863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15323278737218841700959269 2873114763228532818929863)
                      ·
                        rfl

theorem cell23_5595371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 3, 2, 1, 4].length) (baseStart_5595371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5595371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5595371 prefixEnd_5595371 := by exact prefixLift 5595371
  have htrace : WordTrace (prefixWord ++ tailWord_5595371) baseStart_5595371 baseEnd_5595371 := by
    simpa [prefixWord, tailWord_5595371, baseEnd_5595371] using wordTrace_append hprefix tailTrace_5595371
  have hstable : (prefixWord ++ tailWord_5595371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5595371).length < 2 ^ (prefixWord ++ tailWord_5595371).sum := by decide
  have hdescent : baseEnd_5595371 < baseStart_5595371 := by decide
  rcases family_descends (prefixWord ++ tailWord_5595371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5595384 : List Nat := [2, 1, 2, 1, 1, 2, 1, 3, 1, 3, 6]
def baseStart_5595384 : Nat := 118140960795 + 5595384 * 2 ^ 59
def prefixEnd_5595384 : Nat := 4983230072969 + 3 ^ 40 * 5595384 * 2
def baseEnd_5595384 : Nat := 2873121438477041268067303

theorem tailTrace_5595384 : CollatzResearch.WordTrace tailWord_5595384 prefixEnd_5595384 2873121438477041268067303 := by
  unfold tailWord_5595384
  simp only [CollatzResearch.WordTrace]
  refine ⟨102040210180443429175936603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136053613573924572234582137 102040210180443429175936603)
  ·
    refine ⟨153060315270665143763904905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102040210180443429175936603 153060315270665143763904905)
    ·
      refine ⟨114795236452998857822928679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153060315270665143763904905 114795236452998857822928679)
      ·
        refine ⟨172192854679498286734393019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114795236452998857822928679 172192854679498286734393019)
        ·
          refine ⟨258289282019247430101589529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172192854679498286734393019 258289282019247430101589529)
          ·
            refine ⟨193716961514435572576192147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 258289282019247430101589529 193716961514435572576192147)
            ·
              refine ⟨290575442271653358864288221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 193716961514435572576192147 290575442271653358864288221)
              ·
                refine ⟨108965790851870009574108083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 290575442271653358864288221 108965790851870009574108083)
                ·
                  refine ⟨163448686277805014361162125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 108965790851870009574108083 163448686277805014361162125)
                  ·
                    refine ⟨61293257354176880385435797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 163448686277805014361162125 61293257354176880385435797)
                    ·
                      refine ⟨2873121438477041268067303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61293257354176880385435797 2873121438477041268067303)
                      ·
                        rfl

theorem cell23_5595384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 1, 3, 6].length) (baseStart_5595384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5595384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5595384 prefixEnd_5595384 := by exact prefixLift 5595384
  have htrace : WordTrace (prefixWord ++ tailWord_5595384) baseStart_5595384 baseEnd_5595384 := by
    simpa [prefixWord, tailWord_5595384, baseEnd_5595384] using wordTrace_append hprefix tailTrace_5595384
  have hstable : (prefixWord ++ tailWord_5595384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5595384).length < 2 ^ (prefixWord ++ tailWord_5595384).sum := by decide
  have hdescent : baseEnd_5595384 < baseStart_5595384 := by decide
  rcases family_descends (prefixWord ++ tailWord_5595384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5595388 : List Nat := [2, 2, 2, 1, 4, 2, 1, 2, 2, 1, 4]
def baseStart_5595388 : Nat := 118140960795 + 5595388 * 2 ^ 59
def prefixEnd_5595388 : Nat := 4983230072969 + 3 ^ 40 * 5595388 * 2
def baseEnd_5595388 : Nat := 2873123492399659252417285

theorem tailTrace_5595388 : CollatzResearch.WordTrace tailWord_5595388 prefixEnd_5595388 2873123492399659252417285 := by
  unfold tailWord_5595388
  simp only [CollatzResearch.WordTrace]
  refine ⟨102040283126436183517509409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136053710835248244690012545 102040283126436183517509409)
  ·
    refine ⟨76530212344827137638132057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102040283126436183517509409 76530212344827137638132057)
    ·
      refine ⟨57397659258620353228599043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76530212344827137638132057 57397659258620353228599043)
      ·
        refine ⟨86096488887930529842898565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57397659258620353228599043 86096488887930529842898565)
        ·
          refine ⟨16143091666486974345543481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 86096488887930529842898565 16143091666486974345543481)
          ·
            refine ⟨12107318749865230759157611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16143091666486974345543481 12107318749865230759157611)
            ·
              refine ⟨18160978124797846138736417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12107318749865230759157611 18160978124797846138736417)
              ·
                refine ⟨13620733593598384604052313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18160978124797846138736417 13620733593598384604052313)
                ·
                  refine ⟨10215550195198788453039235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13620733593598384604052313 10215550195198788453039235)
                  ·
                    refine ⟨15323325292798182679558853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10215550195198788453039235 15323325292798182679558853)
                    ·
                      refine ⟨2873123492399659252417285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15323325292798182679558853 2873123492399659252417285)
                      ·
                        rfl

theorem cell23_5595388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 2, 2, 1, 4].length) (baseStart_5595388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5595388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5595388 prefixEnd_5595388 := by exact prefixLift 5595388
  have htrace : WordTrace (prefixWord ++ tailWord_5595388) baseStart_5595388 baseEnd_5595388 := by
    simpa [prefixWord, tailWord_5595388, baseEnd_5595388] using wordTrace_append hprefix tailTrace_5595388
  have hstable : (prefixWord ++ tailWord_5595388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5595388).length < 2 ^ (prefixWord ++ tailWord_5595388).sum := by decide
  have hdescent : baseEnd_5595388 < baseStart_5595388 := by decide
  rcases family_descends (prefixWord ++ tailWord_5595388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5595422 : List Nat := [4, 3, 2, 1, 1, 2, 2, 1, 2, 1, 4]
def baseStart_5595422 : Nat := 118140960795 + 5595422 * 2 ^ 59
def prefixEnd_5595422 : Nat := 4983230072969 + 3 ^ 40 * 5595422 * 2
def baseEnd_5595422 : Nat := 2873140950741912119392129

theorem tailTrace_5595422 : CollatzResearch.WordTrace tailWord_5595422 prefixEnd_5595422 2873140950741912119392129 := by
  unfold tailWord_5595422
  simp only [CollatzResearch.WordTrace]
  refine ⟨25510225791843648855219565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136054537556499460561171013 25510225791843648855219565)
  ·
    refine ⟨9566334671941368320707337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25510225791843648855219565 9566334671941368320707337)
    ·
      refine ⟨7174751003956026240530503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9566334671941368320707337 7174751003956026240530503)
      ·
        refine ⟨10762126505934039360795755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7174751003956026240530503 10762126505934039360795755)
        ·
          refine ⟨16143189758901059041193633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10762126505934039360795755 16143189758901059041193633)
          ·
            refine ⟨12107392319175794280895225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16143189758901059041193633 12107392319175794280895225)
            ·
              refine ⟨9080544239381845710671419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12107392319175794280895225 9080544239381845710671419)
              ·
                refine ⟨13620816359072768566007129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9080544239381845710671419 13620816359072768566007129)
                ·
                  refine ⟨10215612269304576424505347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13620816359072768566007129 10215612269304576424505347)
                  ·
                    refine ⟨15323418403956864636758021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10215612269304576424505347 15323418403956864636758021)
                    ·
                      refine ⟨2873140950741912119392129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15323418403956864636758021 2873140950741912119392129)
                      ·
                        rfl

theorem cell23_5595422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_5595422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5595422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5595422 prefixEnd_5595422 := by exact prefixLift 5595422
  have htrace : WordTrace (prefixWord ++ tailWord_5595422) baseStart_5595422 baseEnd_5595422 := by
    simpa [prefixWord, tailWord_5595422, baseEnd_5595422] using wordTrace_append hprefix tailTrace_5595422
  have hstable : (prefixWord ++ tailWord_5595422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5595422).length < 2 ^ (prefixWord ++ tailWord_5595422).sum := by decide
  have hdescent : baseEnd_5595422 < baseStart_5595422 := by decide
  rcases family_descends (prefixWord ++ tailWord_5595422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5595449 : List Nat := [1, 2, 1, 6, 1, 3, 2, 2, 1, 4]
def baseStart_5595449 : Nat := 118140960795 + 5595449 * 2 ^ 59
def prefixEnd_5595449 : Nat := 4983230072969 + 3 ^ 40 * 5595449 * 2
def baseEnd_5595449 : Nat := 957718271573194504584835

theorem tailTrace_5595449 : CollatzResearch.WordTrace tailWord_5595449 prefixEnd_5595449 957718271573194504584835 := by
  unfold tailWord_5595449
  simp only [CollatzResearch.WordTrace]
  refine ⟨204082791105651374452989401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136055194070434249635326267 204082791105651374452989401)
  ·
    refine ⟨153062093329238530839742051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204082791105651374452989401 153062093329238530839742051)
    ·
      refine ⟨229593139993857796259613077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153062093329238530839742051 229593139993857796259613077)
      ·
        refine ⟨10762178437212084199669363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 229593139993857796259613077 10762178437212084199669363)
        ·
          refine ⟨16143267655818126299504045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10762178437212084199669363 16143267655818126299504045)
          ·
            refine ⟨6053725370931797362314017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16143267655818126299504045 6053725370931797362314017)
            ·
              refine ⟨4540294028198848021735513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6053725370931797362314017 4540294028198848021735513)
              ·
                refine ⟨3405220521149136016301635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4540294028198848021735513 3405220521149136016301635)
                ·
                  refine ⟨5107830781723704024452453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3405220521149136016301635 5107830781723704024452453)
                  ·
                    refine ⟨957718271573194504584835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5107830781723704024452453 957718271573194504584835)
                    ·
                      rfl

theorem cell23_5595449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 2, 2, 1, 4].length) (baseStart_5595449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5595449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5595449 prefixEnd_5595449 := by exact prefixLift 5595449
  have htrace : WordTrace (prefixWord ++ tailWord_5595449) baseStart_5595449 baseEnd_5595449 := by
    simpa [prefixWord, tailWord_5595449, baseEnd_5595449] using wordTrace_append hprefix tailTrace_5595449
  have hstable : (prefixWord ++ tailWord_5595449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5595449).length < 2 ^ (prefixWord ++ tailWord_5595449).sum := by decide
  have hdescent : baseEnd_5595449 < baseStart_5595449 := by decide
  rcases family_descends (prefixWord ++ tailWord_5595449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5595495 : List Nat := [1, 1, 5, 1, 3, 2, 1, 3, 1, 1, 4]
def baseStart_5595495 : Nat := 118140960795 + 5595495 * 2 ^ 59
def prefixEnd_5595495 : Nat := 4983230072969 + 3 ^ 40 * 5595495 * 2
def baseEnd_5595495 : Nat := 2873178434829690333779293

theorem tailTrace_5595495 : CollatzResearch.WordTrace tailWord_5595495 prefixEnd_5595495 2873178434829690333779293 := by
  unfold tailWord_5595495
  simp only [CollatzResearch.WordTrace]
  refine ⟨204084468863484724309163939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136056312575656482872775959 204084468863484724309163939)
  ·
    refine ⟨306126703295227086463745909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204084468863484724309163939 306126703295227086463745909)
    ·
      refine ⟨28699378433927539355976179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 306126703295227086463745909 28699378433927539355976179)
      ·
        refine ⟨43049067650891309033964269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28699378433927539355976179 43049067650891309033964269)
        ·
          refine ⟨16143400369084240887736601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43049067650891309033964269 16143400369084240887736601)
          ·
            refine ⟨12107550276813180665802451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16143400369084240887736601 12107550276813180665802451)
            ·
              refine ⟨18161325415219770998703677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12107550276813180665802451 18161325415219770998703677)
              ·
                refine ⟨6810497030707414124513879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18161325415219770998703677 6810497030707414124513879)
                ·
                  refine ⟨10215745546061121186770819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6810497030707414124513879 10215745546061121186770819)
                  ·
                    refine ⟨15323618319091681780156229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10215745546061121186770819 15323618319091681780156229)
                    ·
                      refine ⟨2873178434829690333779293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15323618319091681780156229 2873178434829690333779293)
                      ·
                        rfl

theorem cell23_5595495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 3, 1, 1, 4].length) (baseStart_5595495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5595495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5595495 prefixEnd_5595495 := by exact prefixLift 5595495
  have htrace : WordTrace (prefixWord ++ tailWord_5595495) baseStart_5595495 baseEnd_5595495 := by
    simpa [prefixWord, tailWord_5595495, baseEnd_5595495] using wordTrace_append hprefix tailTrace_5595495
  have hstable : (prefixWord ++ tailWord_5595495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5595495).length < 2 ^ (prefixWord ++ tailWord_5595495).sum := by decide
  have hdescent : baseEnd_5595495 < baseStart_5595495 := by decide
  rcases family_descends (prefixWord ++ tailWord_5595495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5595501 : List Nat := [1, 5, 1, 1, 1, 2, 12]
def baseStart_5595501 : Nat := 118140960795 + 5595501 * 2 ^ 59
def prefixEnd_5595501 : Nat := 4983230072969 + 3 ^ 40 * 5595501 * 2
def baseEnd_5595501 : Nat := 35471376737205151979065

theorem tailTrace_5595501 : CollatzResearch.WordTrace tailWord_5595501 prefixEnd_5595501 35471376737205151979065 := by
  unfold tailWord_5595501
  simp only [CollatzResearch.WordTrace]
  refine ⟨204084687701462987333882357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136056458467641991555921571 204084687701462987333882357)
  ·
    refine ⟨19132939472012155062551471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 204084687701462987333882357 19132939472012155062551471)
    ·
      refine ⟨28699409208018232593827207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19132939472012155062551471 28699409208018232593827207)
      ·
        refine ⟨43049113812027348890740811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28699409208018232593827207 43049113812027348890740811)
        ·
          refine ⟨64573670718041023336111217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43049113812027348890740811 64573670718041023336111217)
          ·
            refine ⟨48430253038530767502083413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64573670718041023336111217 48430253038530767502083413)
            ·
              refine ⟨35471376737205151979065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 48430253038530767502083413 35471376737205151979065)
              ·
                rfl

theorem cell23_5595501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 12].length) (baseStart_5595501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5595501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5595501 prefixEnd_5595501 := by exact prefixLift 5595501
  have htrace : WordTrace (prefixWord ++ tailWord_5595501) baseStart_5595501 baseEnd_5595501 := by
    simpa [prefixWord, tailWord_5595501, baseEnd_5595501] using wordTrace_append hprefix tailTrace_5595501
  have hstable : (prefixWord ++ tailWord_5595501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5595501).length < 2 ^ (prefixWord ++ tailWord_5595501).sum := by decide
  have hdescent : baseEnd_5595501 < baseStart_5595501 := by decide
  rcases family_descends (prefixWord ++ tailWord_5595501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5595546 : List Nat := [3, 1, 1, 4, 1, 4, 1, 3, 1, 2, 2]
def baseStart_5595546 : Nat := 118140960795 + 5595546 * 2 ^ 59
def prefixEnd_5595546 : Nat := 4983230072969 + 3 ^ 40 * 5595546 * 2
def baseEnd_5595546 : Nat := 2873204622343069634241559

theorem tailTrace_5595546 : CollatzResearch.WordTrace tailWord_5595546 prefixEnd_5595546 2873204622343069634241559 := by
  unfold tailWord_5595546
  simp only [CollatzResearch.WordTrace]
  refine ⟨51021582246574990004817623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136057552657533306679513661 51021582246574990004817623)
  ·
    refine ⟨76532373369862485007226435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51021582246574990004817623 76532373369862485007226435)
    ·
      refine ⟨114798560054793727510839653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76532373369862485007226435 114798560054793727510839653)
      ·
        refine ⟨21524730010273823908282435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 114798560054793727510839653 21524730010273823908282435)
        ·
          refine ⟨32287095015410735862423653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21524730010273823908282435 32287095015410735862423653)
          ·
            refine ⟨6053830315389512974204435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32287095015410735862423653 6053830315389512974204435)
            ·
              refine ⟨9080745473084269461306653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6053830315389512974204435 9080745473084269461306653)
              ·
                refine ⟨3405279552406601047989995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9080745473084269461306653 3405279552406601047989995)
                ·
                  refine ⟨5107919328609901571984993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3405279552406601047989995 5107919328609901571984993)
                  ·
                    refine ⟨3830939496457426178988745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5107919328609901571984993 3830939496457426178988745)
                    ·
                      refine ⟨2873204622343069634241559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3830939496457426178988745 2873204622343069634241559)
                      ·
                        rfl

theorem cell23_5595546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 1, 3, 1, 2, 2].length) (baseStart_5595546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5595546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5595546 prefixEnd_5595546 := by exact prefixLift 5595546
  have htrace : WordTrace (prefixWord ++ tailWord_5595546) baseStart_5595546 baseEnd_5595546 := by
    simpa [prefixWord, tailWord_5595546, baseEnd_5595546] using wordTrace_append hprefix tailTrace_5595546
  have hstable : (prefixWord ++ tailWord_5595546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5595546).length < 2 ^ (prefixWord ++ tailWord_5595546).sum := by decide
  have hdescent : baseEnd_5595546 < baseStart_5595546 := by decide
  rcases family_descends (prefixWord ++ tailWord_5595546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5595561 : List Nat := [1, 2, 1, 1, 1, 1, 3, 3, 4, 6]
def baseStart_5595561 : Nat := 118140960795 + 5595561 * 2 ^ 59
def prefixEnd_5595561 : Nat := 4983230072969 + 3 ^ 40 * 5595561 * 2
def baseEnd_5595561 : Nat := 957737441517629025184663

theorem tailTrace_5595561 : CollatzResearch.WordTrace tailWord_5595561 prefixEnd_5595561 957737441517629025184663 := by
  unfold tailWord_5595561
  simp only [CollatzResearch.WordTrace]
  refine ⟨204086876081245617581066537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136057917387497078387377691 204086876081245617581066537)
  ·
    refine ⟨153065157060934213185799903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204086876081245617581066537 153065157060934213185799903)
    ·
      refine ⟨229597735591401319778699855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153065157060934213185799903 229597735591401319778699855)
      ·
        refine ⟨344396603387101979668049783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229597735591401319778699855 344396603387101979668049783)
        ·
          refine ⟨516594905080652969502074675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 344396603387101979668049783 516594905080652969502074675)
          ·
            refine ⟨774892357620979454253112013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 516594905080652969502074675 774892357620979454253112013)
            ·
              refine ⟨290584634107867295344917005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 774892357620979454253112013 290584634107867295344917005)
              ·
                refine ⟨108969237790450235754343877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 290584634107867295344917005 108969237790450235754343877)
                ·
                  refine ⟨20431732085709419203939477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 108969237790450235754343877 20431732085709419203939477)
                  ·
                    refine ⟨957737441517629025184663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20431732085709419203939477 957737441517629025184663)
                    ·
                      rfl

theorem cell23_5595561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 4, 6].length) (baseStart_5595561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5595561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5595561 prefixEnd_5595561 := by exact prefixLift 5595561
  have htrace : WordTrace (prefixWord ++ tailWord_5595561) baseStart_5595561 baseEnd_5595561 := by
    simpa [prefixWord, tailWord_5595561, baseEnd_5595561] using wordTrace_append hprefix tailTrace_5595561
  have hstable : (prefixWord ++ tailWord_5595561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5595561).length < 2 ^ (prefixWord ++ tailWord_5595561).sum := by decide
  have hdescent : baseEnd_5595561 < baseStart_5595561 := by decide
  rcases family_descends (prefixWord ++ tailWord_5595561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5595598 : List Nat := [4, 1, 1, 1, 2, 1, 1, 2, 4, 2, 4]
def baseStart_5595598 : Nat := 118140960795 + 5595598 * 2 ^ 59
def prefixEnd_5595598 : Nat := 4983230072969 + 3 ^ 40 * 5595598 * 2
def baseEnd_5595598 : Nat := 2873231323337103430791319

theorem tailTrace_5595598 : CollatzResearch.WordTrace tailWord_5595598 prefixEnd_5595598 2873231323337103430791319 := by
  unfold tailWord_5595598
  simp only [CollatzResearch.WordTrace]
  refine ⟨25511028197763946612520431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136058817054741048600108965 25511028197763946612520431)
  ·
    refine ⟨38266542296645919918780647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25511028197763946612520431 38266542296645919918780647)
    ·
      refine ⟨57399813444968879878170971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38266542296645919918780647 57399813444968879878170971)
      ·
        refine ⟨86099720167453319817256457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57399813444968879878170971 86099720167453319817256457)
        ·
          refine ⟨64574790125589989862942343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86099720167453319817256457 64574790125589989862942343)
          ·
            refine ⟨96862185188384984794413515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64574790125589989862942343 96862185188384984794413515)
            ·
              refine ⟨145293277782577477191620273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96862185188384984794413515 145293277782577477191620273)
              ·
                refine ⟨108969958336933107893715205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 145293277782577477191620273 108969958336933107893715205)
                ·
                  refine ⟨20431867188174957730071601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 108969958336933107893715205 20431867188174957730071601)
                  ·
                    refine ⟨15323900391131218297553701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20431867188174957730071601 15323900391131218297553701)
                    ·
                      refine ⟨2873231323337103430791319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15323900391131218297553701 2873231323337103430791319)
                      ·
                        rfl

theorem cell23_5595598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 4, 2, 4].length) (baseStart_5595598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5595598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5595598 prefixEnd_5595598 := by exact prefixLift 5595598
  have htrace : WordTrace (prefixWord ++ tailWord_5595598) baseStart_5595598 baseEnd_5595598 := by
    simpa [prefixWord, tailWord_5595598, baseEnd_5595598] using wordTrace_append hprefix tailTrace_5595598
  have hstable : (prefixWord ++ tailWord_5595598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5595598).length < 2 ^ (prefixWord ++ tailWord_5595598).sum := by decide
  have hdescent : baseEnd_5595598 < baseStart_5595598 := by decide
  rcases family_descends (prefixWord ++ tailWord_5595598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5595606 : List Nat := [5, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2]
def baseStart_5595606 : Nat := 118140960795 + 5595606 * 2 ^ 59
def prefixEnd_5595606 : Nat := 4983230072969 + 3 ^ 40 * 5595606 * 2
def baseEnd_5595606 : Nat := 2873235431182339399491283

theorem tailTrace_5595606 : CollatzResearch.WordTrace tailWord_5595606 prefixEnd_5595606 2873235431182339399491283 := by
  unfold tailWord_5595606
  simp only [CollatzResearch.WordTrace]
  refine ⟨12755532335380161891653417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 136059011577388393510969781 12755532335380161891653417)
  ·
    refine ⟨9566649251535121418740063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12755532335380161891653417 9566649251535121418740063)
    ·
      refine ⟨14349973877302682128110095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9566649251535121418740063 14349973877302682128110095)
      ·
        refine ⟨21524960815954023192165143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14349973877302682128110095 21524960815954023192165143)
        ·
          refine ⟨32287441223931034788247715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21524960815954023192165143 32287441223931034788247715)
          ·
            refine ⟨48431161835896552182371573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32287441223931034788247715 48431161835896552182371573)
            ·
              refine ⟨4540421422115301767097335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48431161835896552182371573 4540421422115301767097335)
              ·
                refine ⟨6810632133172952650646003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4540421422115301767097335 6810632133172952650646003)
                ·
                  refine ⟨10215948199759428975969005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6810632133172952650646003 10215948199759428975969005)
                  ·
                    refine ⟨3830980574909785865988377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10215948199759428975969005 3830980574909785865988377)
                    ·
                      refine ⟨2873235431182339399491283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3830980574909785865988377 2873235431182339399491283)
                      ·
                        rfl

theorem cell23_5595606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2].length) (baseStart_5595606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5595606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5595606 prefixEnd_5595606 := by exact prefixLift 5595606
  have htrace : WordTrace (prefixWord ++ tailWord_5595606) baseStart_5595606 baseEnd_5595606 := by
    simpa [prefixWord, tailWord_5595606, baseEnd_5595606] using wordTrace_append hprefix tailTrace_5595606
  have hstable : (prefixWord ++ tailWord_5595606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5595606).length < 2 ^ (prefixWord ++ tailWord_5595606).sum := by decide
  have hdescent : baseEnd_5595606 < baseStart_5595606 := by decide
  rcases family_descends (prefixWord ++ tailWord_5595606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5595645 : List Nat := [1, 4, 1, 1, 1, 3, 1, 2, 2, 5, 2]
def baseStart_5595645 : Nat := 118140960795 + 5595645 * 2 ^ 59
def prefixEnd_5595645 : Nat := 4983230072969 + 3 ^ 40 * 5595645 * 2
def baseEnd_5595645 : Nat := 2873255456927864746903603

theorem tailTrace_5595645 : CollatzResearch.WordTrace tailWord_5595645 prefixEnd_5595645 2873255456927864746903603 := by
  unfold tailWord_5595645
  simp only [CollatzResearch.WordTrace]
  refine ⟨204089939812941299927124389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136059959875294199951416259 204089939812941299927124389)
  ·
    refine ⟨38266863714926493736335823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 204089939812941299927124389 38266863714926493736335823)
    ·
      refine ⟨57400295572389740604503735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38266863714926493736335823 57400295572389740604503735)
      ·
        refine ⟨86100443358584610906755603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57400295572389740604503735 86100443358584610906755603)
        ·
          refine ⟨129150665037876916360133405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86100443358584610906755603 129150665037876916360133405)
          ·
            refine ⟨48431499389203843635050027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 129150665037876916360133405 48431499389203843635050027)
            ·
              refine ⟨72647249083805765452575041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48431499389203843635050027 72647249083805765452575041)
              ·
                refine ⟨54485436812854324089431281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72647249083805765452575041 54485436812854324089431281)
                ·
                  refine ⟨40864077609640743067073461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54485436812854324089431281 40864077609640743067073461)
                  ·
                    refine ⟨3831007275903819662538137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40864077609640743067073461 3831007275903819662538137)
                    ·
                      refine ⟨2873255456927864746903603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3831007275903819662538137 2873255456927864746903603)
                      ·
                        rfl

theorem cell23_5595645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 2, 2, 5, 2].length) (baseStart_5595645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5595645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5595645 prefixEnd_5595645 := by exact prefixLift 5595645
  have htrace : WordTrace (prefixWord ++ tailWord_5595645) baseStart_5595645 baseEnd_5595645 := by
    simpa [prefixWord, tailWord_5595645, baseEnd_5595645] using wordTrace_append hprefix tailTrace_5595645
  have hstable : (prefixWord ++ tailWord_5595645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5595645).length < 2 ^ (prefixWord ++ tailWord_5595645).sum := by decide
  have hdescent : baseEnd_5595645 < baseStart_5595645 := by decide
  rcases family_descends (prefixWord ++ tailWord_5595645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5595655 : List Nat := [1, 1, 4, 3, 3, 1, 1, 1, 1, 7]
def baseStart_5595655 : Nat := 118140960795 + 5595655 * 2 ^ 59
def prefixEnd_5595655 : Nat := 4983230072969 + 3 ^ 40 * 5595655 * 2
def baseEnd_5595655 : Nat := 957753530578136569259519

theorem tailTrace_5595655 : CollatzResearch.WordTrace tailWord_5595655 prefixEnd_5595655 957753530578136569259519 := by
  unfold tailWord_5595655
  simp only [CollatzResearch.WordTrace]
  refine ⟨204090304542905071634988419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136060203028603381089992279 204090304542905071634988419)
  ·
    refine ⟨306135456814357607452482629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204090304542905071634988419 306135456814357607452482629)
    ·
      refine ⟨57400398152692051397340493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 306135456814357607452482629 57400398152692051397340493)
      ·
        refine ⟨21525149307259519274002685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57400398152692051397340493 21525149307259519274002685)
        ·
          refine ⟨8071930990222319727751007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21525149307259519274002685 8071930990222319727751007)
          ·
            refine ⟨12107896485333479591626511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8071930990222319727751007 12107896485333479591626511)
            ·
              refine ⟨18161844728000219387439767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12107896485333479591626511 18161844728000219387439767)
              ·
                refine ⟨27242767092000329081159651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18161844728000219387439767 27242767092000329081159651)
                ·
                  refine ⟨40864150638000493621739477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27242767092000329081159651 40864150638000493621739477)
                  ·
                    refine ⟨957753530578136569259519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40864150638000493621739477 957753530578136569259519)
                    ·
                      rfl

theorem cell23_5595655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 1, 1, 7].length) (baseStart_5595655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5595655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5595655 prefixEnd_5595655 := by exact prefixLift 5595655
  have htrace : WordTrace (prefixWord ++ tailWord_5595655) baseStart_5595655 baseEnd_5595655 := by
    simpa [prefixWord, tailWord_5595655, baseEnd_5595655] using wordTrace_append hprefix tailTrace_5595655
  have hstable : (prefixWord ++ tailWord_5595655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5595655).length < 2 ^ (prefixWord ++ tailWord_5595655).sum := by decide
  have hdescent : baseEnd_5595655 < baseStart_5595655 := by decide
  rcases family_descends (prefixWord ++ tailWord_5595655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5595685 : List Nat := [1, 3, 1, 2, 2, 1, 3, 3, 3, 4]
def baseStart_5595685 : Nat := 118140960795 + 5595685 * 2 ^ 59
def prefixEnd_5595685 : Nat := 4983230072969 + 3 ^ 40 * 5595685 * 2
def baseEnd_5595685 : Nat := 957758665384681530134473

theorem tailTrace_5595685 : CollatzResearch.WordTrace tailWord_5595685 prefixEnd_5595685 957758665384681530134473 := by
  unfold tailWord_5595685
  simp only [CollatzResearch.WordTrace]
  refine ⟨204091398732796386758580509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136060932488530924505720339 204091398732796386758580509)
  ·
    refine ⟨76534274524798645034467691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 204091398732796386758580509 76534274524798645034467691)
    ·
      refine ⟨114801411787197967551701537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76534274524798645034467691 114801411787197967551701537)
      ·
        refine ⟨86101058840398475663776153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114801411787197967551701537 86101058840398475663776153)
        ·
          refine ⟨64575794130298856747832115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86101058840398475663776153 64575794130298856747832115)
          ·
            refine ⟨96863691195448285121748173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64575794130298856747832115 96863691195448285121748173)
            ·
              refine ⟨36323884198293106920655565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96863691195448285121748173 36323884198293106920655565)
              ·
                refine ⟨13621456574359915095245837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36323884198293106920655565 13621456574359915095245837)
                ·
                  refine ⟨5108046215384968160717189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13621456574359915095245837 5108046215384968160717189)
                  ·
                    refine ⟨957758665384681530134473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5108046215384968160717189 957758665384681530134473)
                    ·
                      rfl

theorem cell23_5595685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 3, 3, 4].length) (baseStart_5595685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5595685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5595685 prefixEnd_5595685 := by exact prefixLift 5595685
  have htrace : WordTrace (prefixWord ++ tailWord_5595685) baseStart_5595685 baseEnd_5595685 := by
    simpa [prefixWord, tailWord_5595685, baseEnd_5595685] using wordTrace_append hprefix tailTrace_5595685
  have hstable : (prefixWord ++ tailWord_5595685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5595685).length < 2 ^ (prefixWord ++ tailWord_5595685).sum := by decide
  have hdescent : baseEnd_5595685 < baseStart_5595685 := by decide
  rcases family_descends (prefixWord ++ tailWord_5595685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5595719 : List Nat := [1, 1, 4, 1, 4, 1, 3, 3, 1, 4]
def baseStart_5595719 : Nat := 118140960795 + 5595719 * 2 ^ 59
def prefixEnd_5595719 : Nat := 4983230072969 + 3 ^ 40 * 5595719 * 2
def baseEnd_5595719 : Nat := 957764484832099152459421

theorem tailTrace_5595719 : CollatzResearch.WordTrace tailWord_5595719 prefixEnd_5595719 957764484832099152459421 := by
  unfold tailWord_5595719
  simp only [CollatzResearch.WordTrace]
  refine ⟨204092638814673210565318211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136061759209782140376878807 204092638814673210565318211)
  ·
    refine ⟨306138958222009815847977317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204092638814673210565318211 306138958222009815847977317)
    ·
      refine ⟨57401054666626840471495747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 306138958222009815847977317 57401054666626840471495747)
      ·
        refine ⟨86101581999940260707243621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57401054666626840471495747 86101581999940260707243621)
        ·
          refine ⟨16144046624988798882608179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 86101581999940260707243621 16144046624988798882608179)
          ·
            refine ⟨24216069937483198323912269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16144046624988798882608179 24216069937483198323912269)
            ·
              refine ⟨9081026226556199371467101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24216069937483198323912269 9081026226556199371467101)
              ·
                refine ⟨3405384834958574764300163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9081026226556199371467101 3405384834958574764300163)
                ·
                  refine ⟨5108077252437862146450245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3405384834958574764300163 5108077252437862146450245)
                  ·
                    refine ⟨957764484832099152459421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5108077252437862146450245 957764484832099152459421)
                    ·
                      rfl

theorem cell23_5595719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3, 3, 1, 4].length) (baseStart_5595719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5595719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5595719 prefixEnd_5595719 := by exact prefixLift 5595719
  have htrace : WordTrace (prefixWord ++ tailWord_5595719) baseStart_5595719 baseEnd_5595719 := by
    simpa [prefixWord, tailWord_5595719, baseEnd_5595719] using wordTrace_append hprefix tailTrace_5595719
  have hstable : (prefixWord ++ tailWord_5595719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5595719).length < 2 ^ (prefixWord ++ tailWord_5595719).sum := by decide
  have hdescent : baseEnd_5595719 < baseStart_5595719 := by decide
  rcases family_descends (prefixWord ++ tailWord_5595719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5595738 : List Nat := [3, 1, 1, 2, 1, 1, 1, 1, 4, 1, 7]
def baseStart_5595738 : Nat := 118140960795 + 5595738 * 2 ^ 59
def prefixEnd_5595738 : Nat := 4983230072969 + 3 ^ 40 * 5595738 * 2
def baseEnd_5595738 : Nat := 2873303210628732883040675

theorem tailTrace_5595738 : CollatzResearch.WordTrace tailWord_5595738 prefixEnd_5595738 2873303210628732883040675 := by
  unfold tailWord_5595738
  simp only [CollatzResearch.WordTrace]
  refine ⟨51023332950401094202564967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136062221201069584540173245 51023332950401094202564967)
  ·
    refine ⟨76534999425601641303847451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51023332950401094202564967 76534999425601641303847451)
    ·
      refine ⟨114802499138402461955771177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76534999425601641303847451 114802499138402461955771177)
      ·
        refine ⟨86101874353801846466828383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114802499138402461955771177 86101874353801846466828383)
        ·
          refine ⟨129152811530702769700242575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86101874353801846466828383 129152811530702769700242575)
          ·
            refine ⟨193729217296054154550363863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129152811530702769700242575 193729217296054154550363863)
            ·
              refine ⟨290593825944081231825545795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 193729217296054154550363863 290593825944081231825545795)
              ·
                refine ⟨435890738916121847738318693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 290593825944081231825545795 435890738916121847738318693)
                ·
                  refine ⟨81729513546772846450934755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 435890738916121847738318693 81729513546772846450934755)
                  ·
                    refine ⟨122594270320159269676402133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 81729513546772846450934755 122594270320159269676402133)
                    ·
                      refine ⟨2873303210628732883040675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 122594270320159269676402133 2873303210628732883040675)
                      ·
                        rfl

theorem cell23_5595738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 4, 1, 7].length) (baseStart_5595738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5595738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5595738 prefixEnd_5595738 := by exact prefixLift 5595738
  have htrace : WordTrace (prefixWord ++ tailWord_5595738) baseStart_5595738 baseEnd_5595738 := by
    simpa [prefixWord, tailWord_5595738, baseEnd_5595738] using wordTrace_append hprefix tailTrace_5595738
  have hstable : (prefixWord ++ tailWord_5595738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5595738).length < 2 ^ (prefixWord ++ tailWord_5595738).sum := by decide
  have hdescent : baseEnd_5595738 < baseStart_5595738 := by decide
  rcases family_descends (prefixWord ++ tailWord_5595738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5595749 : List Nat := [1, 3, 1, 3, 4, 2, 2, 1, 6]
def baseStart_5595749 : Nat := 118140960795 + 5595749 * 2 ^ 59
def prefixEnd_5595749 : Nat := 4983230072969 + 3 ^ 40 * 5595749 * 2
def baseEnd_5595749 : Nat := 319256539879548037778125

theorem tailTrace_5595749 : CollatzResearch.WordTrace tailWord_5595749 prefixEnd_5595749 319256539879548037778125 := by
  unfold tailWord_5595749
  simp only [CollatzResearch.WordTrace]
  refine ⟨204093733004564525688910301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136062488669709683792606867 204093733004564525688910301)
  ·
    refine ⟨76535149876711697133341363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 204093733004564525688910301 76535149876711697133341363)
    ·
      refine ⟨114802724815067545700012045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76535149876711697133341363 114802724815067545700012045)
      ·
        refine ⟨43051021805650329637504517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114802724815067545700012045 43051021805650329637504517)
        ·
          refine ⟨8072066588559436807032097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43051021805650329637504517 8072066588559436807032097)
          ·
            refine ⟨6054049941419577605274073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8072066588559436807032097 6054049941419577605274073)
            ·
              refine ⟨4540537456064683203955555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6054049941419577605274073 4540537456064683203955555)
              ·
                refine ⟨6810806184097024805933333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4540537456064683203955555 6810806184097024805933333)
                ·
                  refine ⟨319256539879548037778125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6810806184097024805933333 319256539879548037778125)
                  ·
                    rfl

theorem cell23_5595749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 2, 1, 6].length) (baseStart_5595749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5595749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5595749 prefixEnd_5595749 := by exact prefixLift 5595749
  have htrace : WordTrace (prefixWord ++ tailWord_5595749) baseStart_5595749 baseEnd_5595749 := by
    simpa [prefixWord, tailWord_5595749, baseEnd_5595749] using wordTrace_append hprefix tailTrace_5595749
  have hstable : (prefixWord ++ tailWord_5595749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5595749).length < 2 ^ (prefixWord ++ tailWord_5595749).sum := by decide
  have hdescent : baseEnd_5595749 < baseStart_5595749 := by decide
  rcases family_descends (prefixWord ++ tailWord_5595749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5595762 : List Nat := [3, 2, 1, 2, 4, 1, 1, 1, 3, 5]
def baseStart_5595762 : Nat := 118140960795 + 5595762 * 2 ^ 59
def prefixEnd_5595762 : Nat := 4983230072969 + 3 ^ 40 * 5595762 * 2
def baseEnd_5595762 : Nat := 957771844721480263046855

theorem tailTrace_5595762 : CollatzResearch.WordTrace tailWord_5595762 prefixEnd_5595762 957771844721480263046855 := by
  unfold tailWord_5595762
  simp only [CollatzResearch.WordTrace]
  refine ⟨51023551788379357227283385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136062804769011619272755693 51023551788379357227283385)
  ·
    refine ⟨38267663841284517920462539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51023551788379357227283385 38267663841284517920462539)
    ·
      refine ⟨57401495761926776880693809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38267663841284517920462539 57401495761926776880693809)
      ·
        refine ⟨43051121821445082660520357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57401495761926776880693809 43051121821445082660520357)
        ·
          refine ⟨8072085341520952998847567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43051121821445082660520357 8072085341520952998847567)
          ·
            refine ⟨12108128012281429498271351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8072085341520952998847567 12108128012281429498271351)
            ·
              refine ⟨18162192018422144247407027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12108128012281429498271351 18162192018422144247407027)
              ·
                refine ⟨27243288027633216371110541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18162192018422144247407027 27243288027633216371110541)
                ·
                  refine ⟨10216233010362456139166453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27243288027633216371110541 10216233010362456139166453)
                  ·
                    refine ⟨957771844721480263046855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10216233010362456139166453 957771844721480263046855)
                    ·
                      rfl

theorem cell23_5595762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 1, 3, 5].length) (baseStart_5595762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5595762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5595762 prefixEnd_5595762 := by exact prefixLift 5595762
  have htrace : WordTrace (prefixWord ++ tailWord_5595762) baseStart_5595762 baseEnd_5595762 := by
    simpa [prefixWord, tailWord_5595762, baseEnd_5595762] using wordTrace_append hprefix tailTrace_5595762
  have hstable : (prefixWord ++ tailWord_5595762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5595762).length < 2 ^ (prefixWord ++ tailWord_5595762).sum := by decide
  have hdescent : baseEnd_5595762 < baseStart_5595762 := by decide
  rcases family_descends (prefixWord ++ tailWord_5595762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5595769 : List Nat := [1, 2, 1, 3, 3, 3, 2, 1, 2, 3, 2]
def baseStart_5595769 : Nat := 118140960795 + 5595769 * 2 ^ 59
def prefixEnd_5595769 : Nat := 4983230072969 + 3 ^ 40 * 5595769 * 2
def baseEnd_5595769 : Nat := 2873319128529022261753033

theorem tailTrace_5595769 : CollatzResearch.WordTrace tailWord_5595769 prefixEnd_5595769 2873319128529022261753033 := by
  unfold tailWord_5595769
  simp only [CollatzResearch.WordTrace]
  refine ⟨204094462464492069104638361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136062974976328046069758907 204094462464492069104638361)
  ·
    refine ⟨153070846848369051828478771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204094462464492069104638361 153070846848369051828478771)
    ·
      refine ⟨229606270272553577742718157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153070846848369051828478771 229606270272553577742718157)
      ·
        refine ⟨86102351352207591653519309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 229606270272553577742718157 86102351352207591653519309)
        ·
          refine ⟨32288381757077846870069741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86102351352207591653519309 32288381757077846870069741)
          ·
            refine ⟨12108143158904192576276153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32288381757077846870069741 12108143158904192576276153)
            ·
              refine ⟨9081107369178144432207115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12108143158904192576276153 9081107369178144432207115)
              ·
                refine ⟨13621661053767216648310673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9081107369178144432207115 13621661053767216648310673)
                ·
                  refine ⟨10216245790325412486233005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13621661053767216648310673 10216245790325412486233005)
                  ·
                    refine ⟨3831092171372029682337377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10216245790325412486233005 3831092171372029682337377)
                    ·
                      refine ⟨2873319128529022261753033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3831092171372029682337377 2873319128529022261753033)
                      ·
                        rfl

theorem cell23_5595769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2, 1, 2, 3, 2].length) (baseStart_5595769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5595769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5595769 prefixEnd_5595769 := by exact prefixLift 5595769
  have htrace : WordTrace (prefixWord ++ tailWord_5595769) baseStart_5595769 baseEnd_5595769 := by
    simpa [prefixWord, tailWord_5595769, baseEnd_5595769] using wordTrace_append hprefix tailTrace_5595769
  have hstable : (prefixWord ++ tailWord_5595769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5595769).length < 2 ^ (prefixWord ++ tailWord_5595769).sum := by decide
  have hdescent : baseEnd_5595769 < baseStart_5595769 := by decide
  rcases family_descends (prefixWord ++ tailWord_5595769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5595775 : List Nat := [1, 1, 2, 2, 1, 1, 1, 6, 4, 4]
def baseStart_5595775 : Nat := 118140960795 + 5595775 * 2 ^ 59
def prefixEnd_5595775 : Nat := 4983230072969 + 3 ^ 40 * 5595775 * 2
def baseEnd_5595775 : Nat := 957774069804316412759335

theorem tailTrace_5595775 : CollatzResearch.WordTrace tailWord_5595775 prefixEnd_5595775 957774069804316412759335 := by
  unfold tailWord_5595775
  simp only [CollatzResearch.WordTrace]
  refine ⟨204094681302470332129356779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136063120868313554752904519 204094681302470332129356779)
  ·
    refine ⟨306142021953705498194035169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204094681302470332129356779 306142021953705498194035169)
    ·
      refine ⟨229606516465279123645526377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 306142021953705498194035169 229606516465279123645526377)
      ·
        refine ⟨172204887348959342734144783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 229606516465279123645526377 172204887348959342734144783)
        ·
          refine ⟨258307331023439014101217175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172204887348959342734144783 258307331023439014101217175)
          ·
            refine ⟨387460996535158521151825763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 258307331023439014101217175 387460996535158521151825763)
            ·
              refine ⟨581191494802737781727738645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 387460996535158521151825763 581191494802737781727738645)
              ·
                refine ⟨27243351318878333518487749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 581191494802737781727738645 27243351318878333518487749)
                ·
                  refine ⟨5108128372289687534716453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27243351318878333518487749 5108128372289687534716453)
                  ·
                    refine ⟨957774069804316412759335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5108128372289687534716453 957774069804316412759335)
                    ·
                      rfl

theorem cell23_5595775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 6, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 6, 4, 4].length) (baseStart_5595775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5595775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5595775 prefixEnd_5595775 := by exact prefixLift 5595775
  have htrace : WordTrace (prefixWord ++ tailWord_5595775) baseStart_5595775 baseEnd_5595775 := by
    simpa [prefixWord, tailWord_5595775, baseEnd_5595775] using wordTrace_append hprefix tailTrace_5595775
  have hstable : (prefixWord ++ tailWord_5595775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5595775).length < 2 ^ (prefixWord ++ tailWord_5595775).sum := by decide
  have hdescent : baseEnd_5595775 < baseStart_5595775 := by decide
  rcases family_descends (prefixWord ++ tailWord_5595775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5595799 : List Nat := [1, 1, 3, 3, 2, 1, 2, 3, 3, 2, 2]
def baseStart_5595799 : Nat := 118140960795 + 5595799 * 2 ^ 59
def prefixEnd_5595799 : Nat := 4983230072969 + 3 ^ 40 * 5595799 * 2
def baseEnd_5595799 : Nat := 2873334532948657144377895

theorem tailTrace_5595799 : CollatzResearch.WordTrace tailWord_5595799 prefixEnd_5595799 2873334532948657144377895 := by
  unfold tailWord_5595799
  simp only [CollatzResearch.WordTrace]
  refine ⟨204095556654383384228230451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136063704436255589485486967 204095556654383384228230451)
  ·
    refine ⟨306143334981575076342345677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204095556654383384228230451 306143334981575076342345677)
    ·
      refine ⟨114803750618090653628379629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 306143334981575076342345677 114803750618090653628379629)
      ·
        refine ⟨43051406481783995110642361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114803750618090653628379629 43051406481783995110642361)
        ·
          refine ⟨32288554861337996332981771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43051406481783995110642361 32288554861337996332981771)
          ·
            refine ⟨48432832292006994499472657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32288554861337996332981771 48432832292006994499472657)
            ·
              refine ⟨36324624219005245874604493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48432832292006994499472657 36324624219005245874604493)
              ·
                refine ⟨13621734082126967202976685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36324624219005245874604493 13621734082126967202976685)
                ·
                  refine ⟨5108150280797612701116257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13621734082126967202976685 5108150280797612701116257)
                  ·
                    refine ⟨3831112710598209525837193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5108150280797612701116257 3831112710598209525837193)
                    ·
                      refine ⟨2873334532948657144377895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3831112710598209525837193 2873334532948657144377895)
                      ·
                        rfl

theorem cell23_5595799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 3, 3, 2, 2].length) (baseStart_5595799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5595799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5595799 prefixEnd_5595799 := by exact prefixLift 5595799
  have htrace : WordTrace (prefixWord ++ tailWord_5595799) baseStart_5595799 baseEnd_5595799 := by
    simpa [prefixWord, tailWord_5595799, baseEnd_5595799] using wordTrace_append hprefix tailTrace_5595799
  have hstable : (prefixWord ++ tailWord_5595799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5595799).length < 2 ^ (prefixWord ++ tailWord_5595799).sum := by decide
  have hdescent : baseEnd_5595799 < baseStart_5595799 := by decide
  rcases family_descends (prefixWord ++ tailWord_5595799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5595805 : List Nat := [1, 4, 2, 1, 1, 1, 5, 8]
def baseStart_5595805 : Nat := 118140960795 + 5595805 * 2 ^ 59
def prefixEnd_5595805 : Nat := 4983230072969 + 3 ^ 40 * 5595805 * 2
def baseEnd_5595805 : Nat := 106419911623429041514921

theorem tailTrace_5595805 : CollatzResearch.WordTrace tailWord_5595805 prefixEnd_5595805 106419911623429041514921 := by
  unfold tailWord_5595805
  simp only [CollatzResearch.WordTrace]
  refine ⟨204095775492361647252948869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136063850328241098168632579 204095775492361647252948869)
  ·
    refine ⟨38267957904817808859927913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 204095775492361647252948869 38267957904817808859927913)
    ·
      refine ⟨28700968428613356644945935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38267957904817808859927913 28700968428613356644945935)
      ·
        refine ⟨43051452642920034967418903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28700968428613356644945935 43051452642920034967418903)
        ·
          refine ⟨64577178964380052451128355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43051452642920034967418903 64577178964380052451128355)
          ·
            refine ⟨96865768446570078676692533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64577178964380052451128355 96865768446570078676692533)
            ·
              refine ⟨9081165791865944875939925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 96865768446570078676692533 9081165791865944875939925)
              ·
                refine ⟨106419911623429041514921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9081165791865944875939925 106419911623429041514921)
                ·
                  rfl

theorem cell23_5595805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5, 8].length) (baseStart_5595805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5595805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5595805 prefixEnd_5595805 := by exact prefixLift 5595805
  have htrace : WordTrace (prefixWord ++ tailWord_5595805) baseStart_5595805 baseEnd_5595805 := by
    simpa [prefixWord, tailWord_5595805, baseEnd_5595805] using wordTrace_append hprefix tailTrace_5595805
  have hstable : (prefixWord ++ tailWord_5595805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5595805).length < 2 ^ (prefixWord ++ tailWord_5595805).sum := by decide
  have hdescent : baseEnd_5595805 < baseStart_5595805 := by decide
  rcases family_descends (prefixWord ++ tailWord_5595805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5595812 : List Nat := [2, 3, 1, 2, 2, 1, 4, 1, 1, 2, 4]
def baseStart_5595812 : Nat := 118140960795 + 5595812 * 2 ^ 59
def prefixEnd_5595812 : Nat := 4983230072969 + 3 ^ 40 * 5595812 * 2
def baseEnd_5595812 : Nat := 2873341208197165593515335

theorem tailTrace_5595812 : CollatzResearch.WordTrace tailWord_5595812 prefixEnd_5595812 2873341208197165593515335 := by
  unfold tailWord_5595812
  simp only [CollatzResearch.WordTrace]
  refine ⟨102048015401668143724226845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136064020535557524965635793 102048015401668143724226845)
  ·
    refine ⟨38268005775625553896585067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102048015401668143724226845 38268005775625553896585067)
    ·
      refine ⟨57402008663438330844877601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38268005775625553896585067 57402008663438330844877601)
      ·
        refine ⟨43051506497578748133658201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57402008663438330844877601 43051506497578748133658201)
        ·
          refine ⟨32288629873184061100243651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43051506497578748133658201 32288629873184061100243651)
          ·
            refine ⟨48432944809776091650365477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32288629873184061100243651 48432944809776091650365477)
            ·
              refine ⟨9081177151833017184443527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48432944809776091650365477 9081177151833017184443527)
              ·
                refine ⟨13621765727749525776665291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9081177151833017184443527 13621765727749525776665291)
                ·
                  refine ⟨20432648591624288664997937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13621765727749525776665291 20432648591624288664997937)
                  ·
                    refine ⟨15324486443718216498748453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20432648591624288664997937 15324486443718216498748453)
                    ·
                      refine ⟨2873341208197165593515335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15324486443718216498748453 2873341208197165593515335)
                      ·
                        rfl

theorem cell23_5595812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4, 1, 1, 2, 4].length) (baseStart_5595812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5595812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5595812 prefixEnd_5595812 := by exact prefixLift 5595812
  have htrace : WordTrace (prefixWord ++ tailWord_5595812) baseStart_5595812 baseEnd_5595812 := by
    simpa [prefixWord, tailWord_5595812, baseEnd_5595812] using wordTrace_append hprefix tailTrace_5595812
  have hstable : (prefixWord ++ tailWord_5595812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5595812).length < 2 ^ (prefixWord ++ tailWord_5595812).sum := by decide
  have hdescent : baseEnd_5595812 < baseStart_5595812 := by decide
  rcases family_descends (prefixWord ++ tailWord_5595812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5595830 : List Nat := [5, 1, 3, 1, 3, 1, 2, 1, 1, 5]
def baseStart_5595830 : Nat := 118140960795 + 5595830 * 2 ^ 59
def prefixEnd_5595830 : Nat := 4983230072969 + 3 ^ 40 * 5595830 * 2
def baseEnd_5595830 : Nat := 957783483616315507696751

theorem tailTrace_5595830 : CollatzResearch.WordTrace tailWord_5595830 prefixEnd_5595830 957783483616315507696751 := by
  unfold tailWord_5595830
  simp only [CollatzResearch.WordTrace]
  refine ⟨12756042957329442282663059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 136064458211514051015072629 12756042957329442282663059)
  ·
    refine ⟨19134064435994163423994589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12756042957329442282663059 19134064435994163423994589)
    ·
      refine ⟨7175274163497811283997971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19134064435994163423994589 7175274163497811283997971)
      ·
        refine ⟨10762911245246716925996957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7175274163497811283997971 10762911245246716925996957)
        ·
          refine ⟨4036091716967518847248859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10762911245246716925996957 4036091716967518847248859)
          ·
            refine ⟨6054137575451278270873289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4036091716967518847248859 6054137575451278270873289)
            ·
              refine ⟨4540603181588458703154967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6054137575451278270873289 4540603181588458703154967)
              ·
                refine ⟨6810904772382688054732451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4540603181588458703154967 6810904772382688054732451)
                ·
                  refine ⟨10216357158574032082098677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6810904772382688054732451 10216357158574032082098677)
                  ·
                    refine ⟨957783483616315507696751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10216357158574032082098677 957783483616315507696751)
                    ·
                      rfl

theorem cell23_5595830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_5595830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5595830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5595830 prefixEnd_5595830 := by exact prefixLift 5595830
  have htrace : WordTrace (prefixWord ++ tailWord_5595830) baseStart_5595830 baseEnd_5595830 := by
    simpa [prefixWord, tailWord_5595830, baseEnd_5595830] using wordTrace_append hprefix tailTrace_5595830
  have hstable : (prefixWord ++ tailWord_5595830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5595830).length < 2 ^ (prefixWord ++ tailWord_5595830).sum := by decide
  have hdescent : baseEnd_5595830 < baseStart_5595830 := by decide
  rcases family_descends (prefixWord ++ tailWord_5595830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5595865 : List Nat := [1, 2, 1, 2, 3, 2, 1, 3, 2, 6]
def baseStart_5595865 : Nat := 118140960795 + 5595865 * 2 ^ 59
def prefixEnd_5595865 : Nat := 4983230072969 + 3 ^ 40 * 5595865 * 2
def baseEnd_5595865 : Nat := 957789474223951295384197

theorem tailTrace_5595865 : CollatzResearch.WordTrace tailWord_5595865 prefixEnd_5595865 957789474223951295384197 := by
  unfold tailWord_5595865
  simp only [CollatzResearch.WordTrace]
  refine ⟨204097963872144277500133049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136065309248096185000088699 204097963872144277500133049)
  ·
    refine ⟨153073472904108208125099787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204097963872144277500133049 153073472904108208125099787)
    ·
      refine ⟨229610209356162312187649681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153073472904108208125099787 229610209356162312187649681)
      ·
        refine ⟨172207657017121734140737261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 229610209356162312187649681 172207657017121734140737261)
        ·
          refine ⟨64577871381420650302776473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 172207657017121734140737261 64577871381420650302776473)
          ·
            refine ⟨48433403536065487727082355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64577871381420650302776473 48433403536065487727082355)
            ·
              refine ⟨72650105304098231590623533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48433403536065487727082355 72650105304098231590623533)
              ·
                refine ⟨27243789489036836846483825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72650105304098231590623533 27243789489036836846483825)
                ·
                  refine ⟨20432842116777627634862869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27243789489036836846483825 20432842116777627634862869)
                  ·
                    refine ⟨957789474223951295384197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20432842116777627634862869 957789474223951295384197)
                    ·
                      rfl

theorem cell23_5595865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 3, 2, 6].length) (baseStart_5595865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5595865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5595865 prefixEnd_5595865 := by exact prefixLift 5595865
  have htrace : WordTrace (prefixWord ++ tailWord_5595865) baseStart_5595865 baseEnd_5595865 := by
    simpa [prefixWord, tailWord_5595865, baseEnd_5595865] using wordTrace_append hprefix tailTrace_5595865
  have hstable : (prefixWord ++ tailWord_5595865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5595865).length < 2 ^ (prefixWord ++ tailWord_5595865).sum := by decide
  have hdescent : baseEnd_5595865 < baseStart_5595865 := by decide
  rcases family_descends (prefixWord ++ tailWord_5595865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5595866 : List Nat := [3, 1, 1, 2, 2, 2, 5, 1, 2, 1, 3]
def baseStart_5595866 : Nat := 118140960795 + 5595866 * 2 ^ 59
def prefixEnd_5595866 : Nat := 4983230072969 + 3 ^ 40 * 5595866 * 2
def baseEnd_5595866 : Nat := 2873368936152508382240087

theorem tailTrace_5595866 : CollatzResearch.WordTrace tailWord_5595866 prefixEnd_5595866 2873368936152508382240087 := by
  unfold tailWord_5595866
  simp only [CollatzResearch.WordTrace]
  refine ⟨51024500086285163667729863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136065333563427103113946301 51024500086285163667729863)
  ·
    refine ⟨76536750129427745501594795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51024500086285163667729863 76536750129427745501594795)
    ·
      refine ⟨114805125194141618252392193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76536750129427745501594795 114805125194141618252392193)
      ·
        refine ⟨86103843895606213689294145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114805125194141618252392193 86103843895606213689294145)
        ·
          refine ⟨64577882921704660266970609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86103843895606213689294145 64577882921704660266970609)
          ·
            refine ⟨48433412191278495200227957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64577882921704660266970609 48433412191278495200227957)
            ·
              refine ⟨4540632392932358925021371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48433412191278495200227957 4540632392932358925021371)
              ·
                refine ⟨6810948589398538387532057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4540632392932358925021371 6810948589398538387532057)
                ·
                  refine ⟨5108211442048903790649043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6810948589398538387532057 5108211442048903790649043)
                  ·
                    refine ⟨7662317163073355685973565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5108211442048903790649043 7662317163073355685973565)
                    ·
                      refine ⟨2873368936152508382240087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7662317163073355685973565 2873368936152508382240087)
                      ·
                        rfl

theorem cell23_5595866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 5, 1, 2, 1, 3].length) (baseStart_5595866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5595866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5595866 prefixEnd_5595866 := by exact prefixLift 5595866
  have htrace : WordTrace (prefixWord ++ tailWord_5595866) baseStart_5595866 baseEnd_5595866 := by
    simpa [prefixWord, tailWord_5595866, baseEnd_5595866] using wordTrace_append hprefix tailTrace_5595866
  have hstable : (prefixWord ++ tailWord_5595866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5595866).length < 2 ^ (prefixWord ++ tailWord_5595866).sum := by decide
  have hdescent : baseEnd_5595866 < baseStart_5595866 := by decide
  rcases family_descends (prefixWord ++ tailWord_5595866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5595876 : List Nat := [2, 3, 1, 1, 1, 5, 2, 2, 1, 3, 2]
def baseStart_5595876 : Nat := 118140960795 + 5595876 * 2 ^ 59
def prefixEnd_5595876 : Nat := 4983230072969 + 3 ^ 40 * 5595876 * 2
def baseEnd_5595876 : Nat := 2873374070959053343115041

theorem tailTrace_5595876 : CollatzResearch.WordTrace tailWord_5595876 prefixEnd_5595876 2873374070959053343115041 := by
  unfold tailWord_5595876
  simp only [CollatzResearch.WordTrace]
  refine ⟨102049182537552213189391741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136065576716736284252522321 102049182537552213189391741)
  ·
    refine ⟨38268443451582079946021903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102049182537552213189391741 38268443451582079946021903)
    ·
      refine ⟨57402665177373119919032855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38268443451582079946021903 57402665177373119919032855)
      ·
        refine ⟨86103997766059679878549283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57402665177373119919032855 86103997766059679878549283)
        ·
          refine ⟨129155996649089519817823925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86103997766059679878549283 129155996649089519817823925)
          ·
            refine ⟨12108374685852142482920993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 129155996649089519817823925 12108374685852142482920993)
            ·
              refine ⟨9081281014389106862190745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12108374685852142482920993 9081281014389106862190745)
              ·
                refine ⟨6810960760791830146643059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9081281014389106862190745 6810960760791830146643059)
                ·
                  refine ⟨10216441141187745219964589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6810960760791830146643059 10216441141187745219964589)
                  ·
                    refine ⟨3831165427945404457486721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10216441141187745219964589 3831165427945404457486721)
                    ·
                      refine ⟨2873374070959053343115041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3831165427945404457486721 2873374070959053343115041)
                      ·
                        rfl

theorem cell23_5595876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2, 2, 1, 3, 2].length) (baseStart_5595876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5595876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5595876 prefixEnd_5595876 := by exact prefixLift 5595876
  have htrace : WordTrace (prefixWord ++ tailWord_5595876) baseStart_5595876 baseEnd_5595876 := by
    simpa [prefixWord, tailWord_5595876, baseEnd_5595876] using wordTrace_append hprefix tailTrace_5595876
  have hstable : (prefixWord ++ tailWord_5595876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5595876).length < 2 ^ (prefixWord ++ tailWord_5595876).sum := by decide
  have hdescent : baseEnd_5595876 < baseStart_5595876 := by decide
  rcases family_descends (prefixWord ++ tailWord_5595876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5595889 : List Nat := [1, 2, 2, 2, 2, 2, 1, 1, 6, 2, 2]
def baseStart_5595889 : Nat := 118140960795 + 5595889 * 2 ^ 59
def prefixEnd_5595889 : Nat := 4983230072969 + 3 ^ 40 * 5595889 * 2
def baseEnd_5595889 : Nat := 2873380746207561792252481

theorem tailTrace_5595889 : CollatzResearch.WordTrace tailWord_5595889 prefixEnd_5595889 2873380746207561792252481 := by
  unfold tailWord_5595889
  simp only [CollatzResearch.WordTrace]
  refine ⟨204098839224057329599006721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136065892816038219732671147 204098839224057329599006721)
  ·
    refine ⟨153074129418042997199255041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204098839224057329599006721 153074129418042997199255041)
    ·
      refine ⟨114805597063532247899441281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153074129418042997199255041 114805597063532247899441281)
      ·
        refine ⟨86104197797649185924580961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114805597063532247899441281 86104197797649185924580961)
        ·
          refine ⟨64578148348236889443435721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86104197797649185924580961 64578148348236889443435721)
          ·
            refine ⟨48433611261177667082576791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64578148348236889443435721 48433611261177667082576791)
            ·
              refine ⟨72650416891766500623865187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48433611261177667082576791 72650416891766500623865187)
              ·
                refine ⟨108975625337649750935797781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72650416891766500623865187 108975625337649750935797781)
                ·
                  refine ⟨5108232437702332075115521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 108975625337649750935797781 5108232437702332075115521)
                  ·
                    refine ⟨3831174328276749056336641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5108232437702332075115521 3831174328276749056336641)
                    ·
                      refine ⟨2873380746207561792252481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3831174328276749056336641 2873380746207561792252481)
                      ·
                        rfl

theorem cell23_5595889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 6, 2, 2].length) (baseStart_5595889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5595889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5595889 prefixEnd_5595889 := by exact prefixLift 5595889
  have htrace : WordTrace (prefixWord ++ tailWord_5595889) baseStart_5595889 baseEnd_5595889 := by
    simpa [prefixWord, tailWord_5595889, baseEnd_5595889] using wordTrace_append hprefix tailTrace_5595889
  have hstable : (prefixWord ++ tailWord_5595889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5595889).length < 2 ^ (prefixWord ++ tailWord_5595889).sum := by decide
  have hdescent : baseEnd_5595889 < baseStart_5595889 := by decide
  rcases family_descends (prefixWord ++ tailWord_5595889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5595905 : List Nat := [1, 2, 4, 1, 1, 1, 1, 1, 1, 1, 9]
def baseStart_5595905 : Nat := 118140960795 + 5595905 * 2 ^ 59
def prefixEnd_5595905 : Nat := 4983230072969 + 3 ^ 40 * 5595905 * 2
def baseEnd_5595905 : Nat := 2873388961898033729652407

theorem tailTrace_5595905 : CollatzResearch.WordTrace tailWord_5595905 prefixEnd_5595905 2873388961898033729652407 := by
  unfold tailWord_5595905
  simp only [CollatzResearch.WordTrace]
  refine ⟨204099422791999364331589169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136066281861332909554392779 204099422791999364331589169)
  ·
    refine ⟨153074567093999523248691877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204099422791999364331589169 153074567093999523248691877)
    ·
      refine ⟨28701481330124910609129727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 153074567093999523248691877 28701481330124910609129727)
      ·
        refine ⟨43052221995187365913694591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28701481330124910609129727 43052221995187365913694591)
        ·
          refine ⟨64578332992781048870541887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43052221995187365913694591 64578332992781048870541887)
          ·
            refine ⟨96867499489171573305812831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64578332992781048870541887 96867499489171573305812831)
            ·
              refine ⟨145301249233757359958719247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96867499489171573305812831 145301249233757359958719247)
              ·
                refine ⟨217951873850636039938078871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 145301249233757359958719247 217951873850636039938078871)
                ·
                  refine ⟨326927810775954059907118307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 217951873850636039938078871 326927810775954059907118307)
                  ·
                    refine ⟨490391716163931089860677461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 326927810775954059907118307 490391716163931089860677461)
                    ·
                      refine ⟨2873388961898033729652407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 490391716163931089860677461 2873388961898033729652407)
                      ·
                        rfl

theorem cell23_5595905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_5595905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5595905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5595905 prefixEnd_5595905 := by exact prefixLift 5595905
  have htrace : WordTrace (prefixWord ++ tailWord_5595905) baseStart_5595905 baseEnd_5595905 := by
    simpa [prefixWord, tailWord_5595905, baseEnd_5595905] using wordTrace_append hprefix tailTrace_5595905
  have hstable : (prefixWord ++ tailWord_5595905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5595905).length < 2 ^ (prefixWord ++ tailWord_5595905).sum := by decide
  have hdescent : baseEnd_5595905 < baseStart_5595905 := by decide
  rcases family_descends (prefixWord ++ tailWord_5595905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5595912 : List Nat := [2, 1, 3, 2, 2, 2, 3, 1, 7]
def baseStart_5595912 : Nat := 118140960795 + 5595912 * 2 ^ 59
def prefixEnd_5595912 : Nat := 4983230072969 + 3 ^ 40 * 5595912 * 2
def baseEnd_5595912 : Nat := 319265839584735022473875

theorem tailTrace_5595912 : CollatzResearch.WordTrace tailWord_5595912 prefixEnd_5595912 319265839584735022473875 := by
  unfold tailWord_5595912
  simp only [CollatzResearch.WordTrace]
  refine ⟨102049839051487002263546995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136066452068649336351395993 102049839051487002263546995)
  ·
    refine ⟨153074758577230503395320493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102049839051487002263546995 153074758577230503395320493)
    ·
      refine ⟨57403034466461438773245185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 153074758577230503395320493 57403034466461438773245185)
      ·
        refine ⟨43052275849846079079933889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57403034466461438773245185 43052275849846079079933889)
        ·
          refine ⟨32289206887384559309950417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43052275849846079079933889 32289206887384559309950417)
          ·
            refine ⟨24216905165538419482462813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32289206887384559309950417 24216905165538419482462813)
            ·
              refine ⟨9081339437076907305923555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24216905165538419482462813 9081339437076907305923555)
              ·
                refine ⟨13622009155615360958885333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9081339437076907305923555 13622009155615360958885333)
                ·
                  refine ⟨319265839584735022473875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13622009155615360958885333 319265839584735022473875)
                  ·
                    rfl

theorem cell23_5595912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3, 1, 7].length) (baseStart_5595912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5595912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5595912 prefixEnd_5595912 := by exact prefixLift 5595912
  have htrace : WordTrace (prefixWord ++ tailWord_5595912) baseStart_5595912 baseEnd_5595912 := by
    simpa [prefixWord, tailWord_5595912, baseEnd_5595912] using wordTrace_append hprefix tailTrace_5595912
  have hstable : (prefixWord ++ tailWord_5595912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5595912).length < 2 ^ (prefixWord ++ tailWord_5595912).sum := by decide
  have hdescent : baseEnd_5595912 < baseStart_5595912 := by decide
  rcases family_descends (prefixWord ++ tailWord_5595912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5595989 : List Nat := [1, 3, 2, 2, 2, 1, 3, 2, 3, 4]
def baseStart_5595989 : Nat := 118140960795 + 5595989 * 2 ^ 59
def prefixEnd_5595989 : Nat := 4983230072969 + 3 ^ 40 * 5595989 * 2
def baseEnd_5595989 : Nat := 957810698091003800334007

theorem tailTrace_5595989 : CollatzResearch.WordTrace tailWord_5595989 prefixEnd_5595989 957810698091003800334007 := by
  unfold tailWord_5595989
  simp only [CollatzResearch.WordTrace]
  refine ⟨204102486523695046677647021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136068324349130031118431347 204102486523695046677647021)
  ·
    refine ⟨76538432446385642504117633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 204102486523695046677647021 76538432446385642504117633)
    ·
      refine ⟨57403824334789231878088225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76538432446385642504117633 57403824334789231878088225)
      ·
        refine ⟨43052868251091923908566169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57403824334789231878088225 43052868251091923908566169)
        ·
          refine ⟨32289651188318942931424627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43052868251091923908566169 32289651188318942931424627)
          ·
            refine ⟨48434476782478414397136941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32289651188318942931424627 48434476782478414397136941)
            ·
              refine ⟨18162928793429405398926353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48434476782478414397136941 18162928793429405398926353)
              ·
                refine ⟨13622196595072054049194765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18162928793429405398926353 13622196595072054049194765)
                ·
                  refine ⟨5108323723152020268448037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13622196595072054049194765 5108323723152020268448037)
                  ·
                    refine ⟨957810698091003800334007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5108323723152020268448037 957810698091003800334007)
                    ·
                      rfl

theorem cell23_5595989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 2, 3, 4].length) (baseStart_5595989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5595989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5595989 prefixEnd_5595989 := by exact prefixLift 5595989
  have htrace : WordTrace (prefixWord ++ tailWord_5595989) baseStart_5595989 baseEnd_5595989 := by
    simpa [prefixWord, tailWord_5595989, baseEnd_5595989] using wordTrace_append hprefix tailTrace_5595989
  have hstable : (prefixWord ++ tailWord_5595989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5595989).length < 2 ^ (prefixWord ++ tailWord_5595989).sum := by decide
  have hdescent : baseEnd_5595989 < baseStart_5595989 := by decide
  rcases family_descends (prefixWord ++ tailWord_5595989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5595996 : List Nat := [2, 2, 4, 2, 1, 1, 3, 1, 2, 1, 4]
def baseStart_5595996 : Nat := 118140960795 + 5595996 * 2 ^ 59
def prefixEnd_5595996 : Nat := 4983230072969 + 3 ^ 40 * 5595996 * 2
def baseEnd_5595996 : Nat := 2873435688637592873614489

theorem tailTrace_5595996 : CollatzResearch.WordTrace tailWord_5595996 prefixEnd_5595996 2873435688637592873614489 := by
  unfold tailWord_5595996
  simp only [CollatzResearch.WordTrace]
  refine ⟨102051370917334843436575921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136068494556446457915434561 102051370917334843436575921)
  ·
    refine ⟨76538528188001132577431941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102051370917334843436575921 76538528188001132577431941)
    ·
      refine ⟨14350974035250212358268489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76538528188001132577431941 14350974035250212358268489)
      ·
        refine ⟨10763230526437659268701367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14350974035250212358268489 10763230526437659268701367)
        ·
          refine ⟨16144845789656488903052051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10763230526437659268701367 16144845789656488903052051)
          ·
            refine ⟨24217268684484733354578077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16144845789656488903052051 24217268684484733354578077)
            ·
              refine ⟨9081475756681775007966779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24217268684484733354578077 9081475756681775007966779)
              ·
                refine ⟨13622213635022662511950169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9081475756681775007966779 13622213635022662511950169)
                ·
                  refine ⟨10216660226266996883962627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13622213635022662511950169 10216660226266996883962627)
                  ·
                    refine ⟨15324990339400495325943941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10216660226266996883962627 15324990339400495325943941)
                    ·
                      refine ⟨2873435688637592873614489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15324990339400495325943941 2873435688637592873614489)
                      ·
                        rfl

theorem cell23_5595996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_5595996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5595996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5595996 prefixEnd_5595996 := by exact prefixLift 5595996
  have htrace : WordTrace (prefixWord ++ tailWord_5595996) baseStart_5595996 baseEnd_5595996 := by
    simpa [prefixWord, tailWord_5595996, baseEnd_5595996] using wordTrace_append hprefix tailTrace_5595996
  have hstable : (prefixWord ++ tailWord_5595996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5595996).length < 2 ^ (prefixWord ++ tailWord_5595996).sum := by decide
  have hdescent : baseEnd_5595996 < baseStart_5595996 := by decide
  rcases family_descends (prefixWord ++ tailWord_5595996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5596032 : List Nat := [2, 1, 1, 2, 1, 2, 2, 4, 3, 5]
def baseStart_5596032 : Nat := 118140960795 + 5596032 * 2 ^ 59
def prefixEnd_5596032 : Nat := 4983230072969 + 3 ^ 40 * 5596032 * 2
def baseEnd_5596032 : Nat := 957818057980384910921441

theorem tailTrace_5596032 : CollatzResearch.WordTrace tailWord_5596032 prefixEnd_5596032 957818057980384910921441 := by
  unfold tailWord_5596032
  simp only [CollatzResearch.WordTrace]
  refine ⟨102052027431269632510731175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136069369908359510014308233 102052027431269632510731175)
  ·
    refine ⟨153078041146904448766096763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102052027431269632510731175 153078041146904448766096763)
    ·
      refine ⟨229617061720356673149145145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153078041146904448766096763 229617061720356673149145145)
      ·
        refine ⟨172212796290267504861858859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 229617061720356673149145145 172212796290267504861858859)
        ·
          refine ⟨258319194435401257292788289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172212796290267504861858859 258319194435401257292788289)
          ·
            refine ⟨193739395826550942969591217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 258319194435401257292788289 193739395826550942969591217)
            ·
              refine ⟨145304546869913207227193413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 193739395826550942969591217 145304546869913207227193413)
              ·
                refine ⟨27244602538108726355098765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 145304546869913207227193413 27244602538108726355098765)
                ·
                  refine ⟨10216725951790772383162037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27244602538108726355098765 10216725951790772383162037)
                  ·
                    refine ⟨957818057980384910921441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10216725951790772383162037 957818057980384910921441)
                    ·
                      rfl

theorem cell23_5596032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 4, 3, 5].length) (baseStart_5596032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5596032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5596032 prefixEnd_5596032 := by exact prefixLift 5596032
  have htrace : WordTrace (prefixWord ++ tailWord_5596032) baseStart_5596032 baseEnd_5596032 := by
    simpa [prefixWord, tailWord_5596032, baseEnd_5596032] using wordTrace_append hprefix tailTrace_5596032
  have hstable : (prefixWord ++ tailWord_5596032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5596032).length < 2 ^ (prefixWord ++ tailWord_5596032).sum := by decide
  have hdescent : baseEnd_5596032 < baseStart_5596032 := by decide
  rcases family_descends (prefixWord ++ tailWord_5596032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5596066 : List Nat := [3, 3, 1, 2, 2, 1, 2, 3, 1, 5]
def baseStart_5596066 : Nat := 118140960795 + 5596066 * 2 ^ 59
def prefixEnd_5596066 : Nat := 4983230072969 + 3 ^ 40 * 5596066 * 2
def baseEnd_5596066 : Nat := 957823877427802533246389

theorem tailTrace_5596066 : CollatzResearch.WordTrace tailWord_5596066 prefixEnd_5596066 957823877427802533246389 := by
  unfold tailWord_5596066
  simp only [CollatzResearch.WordTrace]
  refine ⟨51026323736104022207050013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136070196629610725885466701 51026323736104022207050013)
  ·
    refine ⟨19134871401039008327643755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51026323736104022207050013 19134871401039008327643755)
    ·
      refine ⟨28702307101558512491465633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19134871401039008327643755 28702307101558512491465633)
      ·
        refine ⟨21526730326168884368599225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28702307101558512491465633 21526730326168884368599225)
        ·
          refine ⟨16145047744626663276449419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21526730326168884368599225 16145047744626663276449419)
          ·
            refine ⟨24217571616939994914674129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16145047744626663276449419 24217571616939994914674129)
            ·
              refine ⟨18163178712704996186005597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24217571616939994914674129 18163178712704996186005597)
              ·
                refine ⟨6811192017264373569752099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18163178712704996186005597 6811192017264373569752099)
                ·
                  refine ⟨10216788025896560354628149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6811192017264373569752099 10216788025896560354628149)
                  ·
                    refine ⟨957823877427802533246389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10216788025896560354628149 957823877427802533246389)
                    ·
                      rfl

theorem cell23_5596066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 3, 1, 5].length) (baseStart_5596066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5596066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5596066 prefixEnd_5596066 := by exact prefixLift 5596066
  have htrace : WordTrace (prefixWord ++ tailWord_5596066) baseStart_5596066 baseEnd_5596066 := by
    simpa [prefixWord, tailWord_5596066, baseEnd_5596066] using wordTrace_append hprefix tailTrace_5596066
  have hstable : (prefixWord ++ tailWord_5596066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5596066).length < 2 ^ (prefixWord ++ tailWord_5596066).sum := by decide
  have hdescent : baseEnd_5596066 < baseStart_5596066 := by decide
  rcases family_descends (prefixWord ++ tailWord_5596066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5596089 : List Nat := [1, 2, 1, 4, 2, 2, 2, 2, 1, 1, 5]
def baseStart_5596089 : Nat := 118140960795 + 5596089 * 2 ^ 59
def prefixEnd_5596089 : Nat := 4983230072969 + 3 ^ 40 * 5596089 * 2
def baseEnd_5596089 : Nat := 2873483442338461009751561

theorem tailTrace_5596089 : CollatzResearch.WordTrace tailWord_5596089 prefixEnd_5596089 2873483442338461009751561 := by
  unfold tailWord_5596089
  simp only [CollatzResearch.WordTrace]
  refine ⟨204106133823332763756287321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136070755882221842504191547 204106133823332763756287321)
  ·
    refine ⟨153079600367499572817215491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204106133823332763756287321 153079600367499572817215491)
    ·
      refine ⟨229619400551249359225823237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153079600367499572817215491 229619400551249359225823237)
      ·
        refine ⟨43053637603359254854841857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 229619400551249359225823237 43053637603359254854841857)
        ·
          refine ⟨32290228202519441141131393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43053637603359254854841857 32290228202519441141131393)
          ·
            refine ⟨24217671151889580855848545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32290228202519441141131393 24217671151889580855848545)
            ·
              refine ⟨18163253363917185641886409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24217671151889580855848545 18163253363917185641886409)
              ·
                refine ⟨13622440022937889231414807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18163253363917185641886409 13622440022937889231414807)
                ·
                  refine ⟨20433660034406833847122211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13622440022937889231414807 20433660034406833847122211)
                  ·
                    refine ⟨30650490051610250770683317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20433660034406833847122211 30650490051610250770683317)
                    ·
                      refine ⟨2873483442338461009751561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30650490051610250770683317 2873483442338461009751561)
                      ·
                        rfl

theorem cell23_5596089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 2, 1, 1, 5].length) (baseStart_5596089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5596089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5596089 prefixEnd_5596089 := by exact prefixLift 5596089
  have htrace : WordTrace (prefixWord ++ tailWord_5596089) baseStart_5596089 baseEnd_5596089 := by
    simpa [prefixWord, tailWord_5596089, baseEnd_5596089] using wordTrace_append hprefix tailTrace_5596089
  have hstable : (prefixWord ++ tailWord_5596089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5596089).length < 2 ^ (prefixWord ++ tailWord_5596089).sum := by decide
  have hdescent : baseEnd_5596089 < baseStart_5596089 := by decide
  rcases family_descends (prefixWord ++ tailWord_5596089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5596096 : List Nat := [2, 1, 1, 2, 3, 4, 1, 3, 2, 4]
def baseStart_5596096 : Nat := 118140960795 + 5596096 * 2 ^ 59
def prefixEnd_5596096 : Nat := 4983230072969 + 3 ^ 40 * 5596096 * 2
def baseEnd_5596096 : Nat := 957829012234347494121343

theorem tailTrace_5596096 : CollatzResearch.WordTrace tailWord_5596096 prefixEnd_5596096 957829012234347494121343 := by
  unfold tailWord_5596096
  simp only [CollatzResearch.WordTrace]
  refine ⟨102053194567153701975896071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136070926089538269301194761 102053194567153701975896071)
  ·
    refine ⟨153079791850730552963844107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102053194567153701975896071 153079791850730552963844107)
    ·
      refine ⟨229619687776095829445766161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153079791850730552963844107 229619687776095829445766161)
      ·
        refine ⟨172214765832071872084324621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 229619687776095829445766161 172214765832071872084324621)
        ·
          refine ⟨64580537187026952031621733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 172214765832071872084324621 64580537187026952031621733)
          ·
            refine ⟨12108850722567553505929075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64580537187026952031621733 12108850722567553505929075)
            ·
              refine ⟨18163276083851330258893613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12108850722567553505929075 18163276083851330258893613)
              ·
                refine ⟨6811228531444248847085105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18163276083851330258893613 6811228531444248847085105)
                ·
                  refine ⟨5108421398583186635313829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6811228531444248847085105 5108421398583186635313829)
                  ·
                    refine ⟨957829012234347494121343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5108421398583186635313829 957829012234347494121343)
                    ·
                      rfl

theorem cell23_5596096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 3, 2, 4].length) (baseStart_5596096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5596096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5596096 prefixEnd_5596096 := by exact prefixLift 5596096
  have htrace : WordTrace (prefixWord ++ tailWord_5596096) baseStart_5596096 baseEnd_5596096 := by
    simpa [prefixWord, tailWord_5596096, baseEnd_5596096] using wordTrace_append hprefix tailTrace_5596096
  have hstable : (prefixWord ++ tailWord_5596096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5596096).length < 2 ^ (prefixWord ++ tailWord_5596096).sum := by decide
  have hdescent : baseEnd_5596096 < baseStart_5596096 := by decide
  rcases family_descends (prefixWord ++ tailWord_5596096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5596100 : List Nat := [2, 3, 3, 3, 1, 2, 1, 2, 1, 5]
def baseStart_5596100 : Nat := 118140960795 + 5596100 * 2 ^ 59
def prefixEnd_5596100 : Nat := 4983230072969 + 3 ^ 40 * 5596100 * 2
def baseEnd_5596100 : Nat := 957829696875220155571337

theorem tailTrace_5596100 : CollatzResearch.WordTrace tailWord_5596100 prefixEnd_5596100 957829696875220155571337 := by
  unfold tailWord_5596100
  simp only [CollatzResearch.WordTrace]
  refine ⟨102053267513146456317468877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136071023350861941756625169 102053267513146456317468877)
  ·
    refine ⟨38269975317429921119050829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102053267513146456317468877 38269975317429921119050829)
    ·
      refine ⟨14351240744036220419644061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38269975317429921119050829 14351240744036220419644061)
      ·
        refine ⟨5381715279013582657366523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14351240744036220419644061 5381715279013582657366523)
        ·
          refine ⟨8072572918520373986049785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5381715279013582657366523 8072572918520373986049785)
          ·
            refine ⟨6054429688890280489537339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8072572918520373986049785 6054429688890280489537339)
            ·
              refine ⟨9081644533335420734306009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6054429688890280489537339 9081644533335420734306009)
              ·
                refine ⟨6811233400001565550729507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9081644533335420734306009 6811233400001565550729507)
                ·
                  refine ⟨10216850100002348326094261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6811233400001565550729507 10216850100002348326094261)
                  ·
                    refine ⟨957829696875220155571337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10216850100002348326094261 957829696875220155571337)
                    ·
                      rfl

theorem cell23_5596100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 1, 2, 1, 5].length) (baseStart_5596100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5596100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5596100 prefixEnd_5596100 := by exact prefixLift 5596100
  have htrace : WordTrace (prefixWord ++ tailWord_5596100) baseStart_5596100 baseEnd_5596100 := by
    simpa [prefixWord, tailWord_5596100, baseEnd_5596100] using wordTrace_append hprefix tailTrace_5596100
  have hstable : (prefixWord ++ tailWord_5596100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5596100).length < 2 ^ (prefixWord ++ tailWord_5596100).sum := by decide
  have hdescent : baseEnd_5596100 < baseStart_5596100 := by decide
  rcases family_descends (prefixWord ++ tailWord_5596100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5596116 : List Nat := [2, 4, 1, 2, 1, 3, 1, 2, 1, 2, 4]
def baseStart_5596116 : Nat := 118140960795 + 5596116 * 2 ^ 59
def prefixEnd_5596116 : Nat := 4983230072969 + 3 ^ 40 * 5596116 * 2
def baseEnd_5596116 : Nat := 2873497306316132404113937

theorem tailTrace_5596116 : CollatzResearch.WordTrace tailWord_5596116 prefixEnd_5596116 2873497306316132404113937 := by
  unfold tailWord_5596116
  simp only [CollatzResearch.WordTrace]
  refine ⟨102053559297117473683760101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136071412396156631578346801 102053559297117473683760101)
  ·
    refine ⟨19135042368209526315705019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102053559297117473683760101 19135042368209526315705019)
    ·
      refine ⟨28702563552314289473557529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19135042368209526315705019 28702563552314289473557529)
      ·
        refine ⟨21526922664235717105168147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28702563552314289473557529 21526922664235717105168147)
        ·
          refine ⟨32290383996353575657752221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21526922664235717105168147 32290383996353575657752221)
          ·
            refine ⟨12108893998632590871657083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32290383996353575657752221 12108893998632590871657083)
            ·
              refine ⟨18163340997948886307485625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12108893998632590871657083 18163340997948886307485625)
              ·
                refine ⟨13622505748461664730614219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18163340997948886307485625 13622505748461664730614219)
                ·
                  refine ⟨20433758622692497095921329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13622505748461664730614219 20433758622692497095921329)
                  ·
                    refine ⟨15325318967019372821940997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20433758622692497095921329 15325318967019372821940997)
                    ·
                      refine ⟨2873497306316132404113937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15325318967019372821940997 2873497306316132404113937)
                      ·
                        rfl

theorem cell23_5596116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_5596116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5596116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5596116 prefixEnd_5596116 := by exact prefixLift 5596116
  have htrace : WordTrace (prefixWord ++ tailWord_5596116) baseStart_5596116 baseEnd_5596116 := by
    simpa [prefixWord, tailWord_5596116, baseEnd_5596116] using wordTrace_append hprefix tailTrace_5596116
  have hstable : (prefixWord ++ tailWord_5596116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5596116).length < 2 ^ (prefixWord ++ tailWord_5596116).sum := by decide
  have hdescent : baseEnd_5596116 < baseStart_5596116 := by decide
  rcases family_descends (prefixWord ++ tailWord_5596116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5596130 : List Nat := [3, 3, 3, 1, 1, 2, 2, 2, 2, 4]
def baseStart_5596130 : Nat := 118140960795 + 5596130 * 2 ^ 59
def prefixEnd_5596130 : Nat := 4983230072969 + 3 ^ 40 * 5596130 * 2
def baseEnd_5596130 : Nat := 957834831681765116446291

theorem tailTrace_5596130 : CollatzResearch.WordTrace tailWord_5596130 prefixEnd_5596130 957834831681765116446291 := by
  unfold tailWord_5596130
  simp only [CollatzResearch.WordTrace]
  refine ⟨51026907304046056939632461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136071752810789485172353229 51026907304046056939632461)
  ·
    refine ⟨19135090239017271352362173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51026907304046056939632461 19135090239017271352362173)
    ·
      refine ⟨7175658839631476757135815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19135090239017271352362173 7175658839631476757135815)
      ·
        refine ⟨10763488259447215135703723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7175658839631476757135815 10763488259447215135703723)
        ·
          refine ⟨16145232389170822703555585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10763488259447215135703723 16145232389170822703555585)
          ·
            refine ⟨12108924291878117027666689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16145232389170822703555585 12108924291878117027666689)
            ·
              refine ⟨9081693218908587770750017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12108924291878117027666689 9081693218908587770750017)
              ·
                refine ⟨6811269914181440828062513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9081693218908587770750017 6811269914181440828062513)
                ·
                  refine ⟨5108452435636080621046885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6811269914181440828062513 5108452435636080621046885)
                  ·
                    refine ⟨957834831681765116446291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5108452435636080621046885 957834831681765116446291)
                    ·
                      rfl

theorem cell23_5596130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_5596130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5596130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5596130 prefixEnd_5596130 := by exact prefixLift 5596130
  have htrace : WordTrace (prefixWord ++ tailWord_5596130) baseStart_5596130 baseEnd_5596130 := by
    simpa [prefixWord, tailWord_5596130, baseEnd_5596130] using wordTrace_append hprefix tailTrace_5596130
  have hstable : (prefixWord ++ tailWord_5596130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5596130).length < 2 ^ (prefixWord ++ tailWord_5596130).sum := by decide
  have hdescent : baseEnd_5596130 < baseStart_5596130 := by decide
  rcases family_descends (prefixWord ++ tailWord_5596130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5596136 : List Nat := [2, 1, 4, 1, 1, 1, 2, 3, 4, 1, 3]
def baseStart_5596136 : Nat := 118140960795 + 5596136 * 2 ^ 59
def prefixEnd_5596136 : Nat := 4983230072969 + 3 ^ 40 * 5596136 * 2
def baseEnd_5596136 : Nat := 2873507575929222325863845

theorem tailTrace_5596136 : CollatzResearch.WordTrace tailWord_5596136 prefixEnd_5596136 2873507575929222325863845 := by
  unfold tailWord_5596136
  simp only [CollatzResearch.WordTrace]
  refine ⟨102053924027081245391624131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136071898702774993855498841 102053924027081245391624131)
  ·
    refine ⟨153080886040621868087436197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102053924027081245391624131 153080886040621868087436197)
    ·
      refine ⟨28702666132616600266394287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 153080886040621868087436197 28702666132616600266394287)
      ·
        refine ⟨43053999198924900399591431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28702666132616600266394287 43053999198924900399591431)
        ·
          refine ⟨64580998798387350599387147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43053999198924900399591431 64580998798387350599387147)
          ·
            refine ⟨96871498197581025899080721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64580998798387350599387147 96871498197581025899080721)
            ·
              refine ⟨72653623648185769424310541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96871498197581025899080721 72653623648185769424310541)
              ·
                refine ⟨27245108868069663534116453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72653623648185769424310541 27245108868069663534116453)
                ·
                  refine ⟨5108457912763061912646835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27245108868069663534116453 5108457912763061912646835)
                  ·
                    refine ⟨7662686869144592868970253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5108457912763061912646835 7662686869144592868970253)
                    ·
                      refine ⟨2873507575929222325863845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7662686869144592868970253 2873507575929222325863845)
                      ·
                        rfl

theorem cell23_5596136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 3, 4, 1, 3].length) (baseStart_5596136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5596136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5596136 prefixEnd_5596136 := by exact prefixLift 5596136
  have htrace : WordTrace (prefixWord ++ tailWord_5596136) baseStart_5596136 baseEnd_5596136 := by
    simpa [prefixWord, tailWord_5596136, baseEnd_5596136] using wordTrace_append hprefix tailTrace_5596136
  have hstable : (prefixWord ++ tailWord_5596136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5596136).length < 2 ^ (prefixWord ++ tailWord_5596136).sum := by decide
  have hdescent : baseEnd_5596136 < baseStart_5596136 := by decide
  rcases family_descends (prefixWord ++ tailWord_5596136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5596206 : List Nat := [4, 1, 3, 1, 1, 1, 1, 3, 2, 2, 4]
def baseStart_5596206 : Nat := 118140960795 + 5596206 * 2 ^ 59
def prefixEnd_5596206 : Nat := 4983230072969 + 3 ^ 40 * 5596206 * 2
def baseEnd_5596206 : Nat := 2873543519575037051988523

theorem tailTrace_5596206 : CollatzResearch.WordTrace tailWord_5596206 prefixEnd_5596206 2873543519575037051988523 := by
  unfold tailWord_5596206
  simp only [CollatzResearch.WordTrace]
  refine ⟨25513800145488611592287059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136073600775939261825530981 25513800145488611592287059)
  ·
    refine ⟨38270700218232917388430589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25513800145488611592287059 38270700218232917388430589)
    ·
      refine ⟨14351512581837344020661471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38270700218232917388430589 14351512581837344020661471)
      ·
        refine ⟨21527268872756016030992207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14351512581837344020661471 21527268872756016030992207)
        ·
          refine ⟨32290903309134024046488311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21527268872756016030992207 32290903309134024046488311)
          ·
            refine ⟨48436354963701036069732467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32290903309134024046488311 48436354963701036069732467)
            ·
              refine ⟨72654532445551554104598701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48436354963701036069732467 72654532445551554104598701)
              ·
                refine ⟨27245449667081832789224513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72654532445551554104598701 27245449667081832789224513)
                ·
                  refine ⟨20434087250311374591918385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27245449667081832789224513 20434087250311374591918385)
                  ·
                    refine ⟨15325565437733530943938789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20434087250311374591918385 15325565437733530943938789)
                    ·
                      refine ⟨2873543519575037051988523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15325565437733530943938789 2873543519575037051988523)
                      ·
                        rfl

theorem cell23_5596206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_5596206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5596206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5596206 prefixEnd_5596206 := by exact prefixLift 5596206
  have htrace : WordTrace (prefixWord ++ tailWord_5596206) baseStart_5596206 baseEnd_5596206 := by
    simpa [prefixWord, tailWord_5596206, baseEnd_5596206] using wordTrace_append hprefix tailTrace_5596206
  have hstable : (prefixWord ++ tailWord_5596206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5596206).length < 2 ^ (prefixWord ++ tailWord_5596206).sum := by decide
  have hdescent : baseEnd_5596206 < baseStart_5596206 := by decide
  rcases family_descends (prefixWord ++ tailWord_5596206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5596229 : List Nat := [1, 3, 1, 1, 1, 3, 4, 1, 1, 7]
def baseStart_5596229 : Nat := 118140960795 + 5596229 * 2 ^ 59
def prefixEnd_5596229 : Nat := 4983230072969 + 3 ^ 40 * 5596229 * 2
def baseEnd_5596229 : Nat := 957851776543363487333639

theorem tailTrace_5596229 : CollatzResearch.WordTrace tailWord_5596229 prefixEnd_5596229 957851776543363487333639 := by
  unfold tailWord_5596229
  simp only [CollatzResearch.WordTrace]
  refine ⟨204111240042825567666383741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136074160028550378444255827 204111240042825567666383741)
  ·
    refine ⟨76541715016059587874893903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 204111240042825567666383741 76541715016059587874893903)
    ·
      refine ⟨114812572524089381812340855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76541715016059587874893903 114812572524089381812340855)
      ·
        refine ⟨172218858786134072718511283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114812572524089381812340855 172218858786134072718511283)
        ·
          refine ⟨258328288179201109077766925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172218858786134072718511283 258328288179201109077766925)
          ·
            refine ⟨96873108067200415904162597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 258328288179201109077766925 96873108067200415904162597)
            ·
              refine ⟨18163707762600077982030487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 96873108067200415904162597 18163707762600077982030487)
              ·
                refine ⟨27245561643900116973045731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18163707762600077982030487 27245561643900116973045731)
                ·
                  refine ⟨40868342465850175459568597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27245561643900116973045731 40868342465850175459568597)
                  ·
                    refine ⟨957851776543363487333639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40868342465850175459568597 957851776543363487333639)
                    ·
                      rfl

theorem cell23_5596229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 1, 1, 7].length) (baseStart_5596229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5596229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5596229 prefixEnd_5596229 := by exact prefixLift 5596229
  have htrace : WordTrace (prefixWord ++ tailWord_5596229) baseStart_5596229 baseEnd_5596229 := by
    simpa [prefixWord, tailWord_5596229, baseEnd_5596229] using wordTrace_append hprefix tailTrace_5596229
  have hstable : (prefixWord ++ tailWord_5596229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5596229).length < 2 ^ (prefixWord ++ tailWord_5596229).sum := by decide
  have hdescent : baseEnd_5596229 < baseStart_5596229 := by decide
  rcases family_descends (prefixWord ++ tailWord_5596229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5596236 : List Nat := [2, 2, 1, 3, 1, 1, 1, 2, 1, 7, 2]
def baseStart_5596236 : Nat := 118140960795 + 5596236 * 2 ^ 59
def prefixEnd_5596236 : Nat := 4983230072969 + 3 ^ 40 * 5596236 * 2
def baseEnd_5596236 : Nat := 2873558923994671934613385

theorem tailTrace_5596236 : CollatzResearch.WordTrace tailWord_5596236 prefixEnd_5596236 2873558923994671934613385 := by
  unfold tailWord_5596236
  simp only [CollatzResearch.WordTrace]
  refine ⟨102055747676900103930944281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136074330235866805241259041 102055747676900103930944281)
  ·
    refine ⟨76541810757675077948208211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102055747676900103930944281 76541810757675077948208211)
    ·
      refine ⟨114812716136512616922312317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76541810757675077948208211 114812716136512616922312317)
      ·
        refine ⟨43054768551192231345867119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114812716136512616922312317 43054768551192231345867119)
        ·
          refine ⟨64582152826788347018800679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43054768551192231345867119 64582152826788347018800679)
          ·
            refine ⟨96873229240182520528201019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64582152826788347018800679 96873229240182520528201019)
            ·
              refine ⟨145309843860273780792301529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96873229240182520528201019 145309843860273780792301529)
              ·
                refine ⟨108982382895205335594226147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 145309843860273780792301529 108982382895205335594226147)
                ·
                  refine ⟨163473574342808003391339221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 108982382895205335594226147 163473574342808003391339221)
                  ·
                    refine ⟨3831411898659562579484513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 163473574342808003391339221 3831411898659562579484513)
                    ·
                      refine ⟨2873558923994671934613385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3831411898659562579484513 2873558923994671934613385)
                      ·
                        rfl

theorem cell23_5596236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 1, 7, 2].length) (baseStart_5596236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5596236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5596236 prefixEnd_5596236 := by exact prefixLift 5596236
  have htrace : WordTrace (prefixWord ++ tailWord_5596236) baseStart_5596236 baseEnd_5596236 := by
    simpa [prefixWord, tailWord_5596236, baseEnd_5596236] using wordTrace_append hprefix tailTrace_5596236
  have hstable : (prefixWord ++ tailWord_5596236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5596236).length < 2 ^ (prefixWord ++ tailWord_5596236).sum := by decide
  have hdescent : baseEnd_5596236 < baseStart_5596236 := by decide
  rcases family_descends (prefixWord ++ tailWord_5596236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5596249 : List Nat := [1, 2, 1, 2, 2, 1, 2, 2, 3, 3, 4]
def baseStart_5596249 : Nat := 118140960795 + 5596249 * 2 ^ 59
def prefixEnd_5596249 : Nat := 4983230072969 + 3 ^ 40 * 5596249 * 2
def baseEnd_5596249 : Nat := 2873565599243180383750825

theorem tailTrace_5596249 : CollatzResearch.WordTrace tailWord_5596249 prefixEnd_5596249 2873565599243180383750825 := by
  unfold tailWord_5596249
  simp only [CollatzResearch.WordTrace]
  refine ⟨204111969502753111082111801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136074646335168740721407867 204111969502753111082111801)
  ·
    refine ⟨153083977127064833311583851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204111969502753111082111801 153083977127064833311583851)
    ·
      refine ⟨229625965690597249967375777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153083977127064833311583851 229625965690597249967375777)
      ·
        refine ⟨172219474267947937475531833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 229625965690597249967375777 172219474267947937475531833)
        ·
          refine ⟨129164605700960953106648875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172219474267947937475531833 129164605700960953106648875)
          ·
            refine ⟨193746908551441429659973313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129164605700960953106648875 193746908551441429659973313)
            ·
              refine ⟨145310181413581072244979985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 193746908551441429659973313 145310181413581072244979985)
              ·
                refine ⟨108982636060185804183734989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 145310181413581072244979985 108982636060185804183734989)
                ·
                  refine ⟨40868488522569676568900621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 108982636060185804183734989 40868488522569676568900621)
                  ·
                    refine ⟨15325683195963628713337733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40868488522569676568900621 15325683195963628713337733)
                    ·
                      refine ⟨2873565599243180383750825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15325683195963628713337733 2873565599243180383750825)
                      ·
                        rfl

theorem cell23_5596249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 3, 3, 4].length) (baseStart_5596249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5596249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5596249 prefixEnd_5596249 := by exact prefixLift 5596249
  have htrace : WordTrace (prefixWord ++ tailWord_5596249) baseStart_5596249 baseEnd_5596249 := by
    simpa [prefixWord, tailWord_5596249, baseEnd_5596249] using wordTrace_append hprefix tailTrace_5596249
  have hstable : (prefixWord ++ tailWord_5596249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5596249).length < 2 ^ (prefixWord ++ tailWord_5596249).sum := by decide
  have hdescent : baseEnd_5596249 < baseStart_5596249 := by decide
  rcases family_descends (prefixWord ++ tailWord_5596249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5596343 : List Nat := [1, 1, 3, 1, 4, 1, 3, 1, 1, 5, 2]
def baseStart_5596343 : Nat := 118140960795 + 5596343 * 2 ^ 59
def prefixEnd_5596343 : Nat := 4983230072969 + 3 ^ 40 * 5596343 * 2
def baseEnd_5596343 : Nat := 2873613866424703015975393

theorem tailTrace_5596343 : CollatzResearch.WordTrace tailWord_5596343 prefixEnd_5596343 2873613866424703015975393 := by
  unfold tailWord_5596343
  simp only [CollatzResearch.WordTrace]
  refine ⟨204115397964412565136033683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136076931976275043424022455 204115397964412565136033683)
  ·
    refine ⟨306173096946618847704050525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204115397964412565136033683 306173096946618847704050525)
    ·
      refine ⟨114814911354982067889018947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 306173096946618847704050525 114814911354982067889018947)
      ·
        refine ⟨172222367032473101833528421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114814911354982067889018947 172222367032473101833528421)
        ·
          refine ⟨32291693818588706593786579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 172222367032473101833528421 32291693818588706593786579)
          ·
            refine ⟨48437540727883059890679869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32291693818588706593786579 48437540727883059890679869)
            ·
              refine ⟨18164077772956147459004951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48437540727883059890679869 18164077772956147459004951)
              ·
                refine ⟨27246116659434221188507427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18164077772956147459004951 27246116659434221188507427)
                ·
                  refine ⟨40869174989151331782761141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27246116659434221188507427 40869174989151331782761141)
                  ·
                    refine ⟨3831485155232937354633857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40869174989151331782761141 3831485155232937354633857)
                    ·
                      refine ⟨2873613866424703015975393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3831485155232937354633857 2873613866424703015975393)
                      ·
                        rfl

theorem cell23_5596343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 1, 1, 5, 2].length) (baseStart_5596343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5596343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5596343 prefixEnd_5596343 := by exact prefixLift 5596343
  have htrace : WordTrace (prefixWord ++ tailWord_5596343) baseStart_5596343 baseEnd_5596343 := by
    simpa [prefixWord, tailWord_5596343, baseEnd_5596343] using wordTrace_append hprefix tailTrace_5596343
  have hstable : (prefixWord ++ tailWord_5596343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5596343).length < 2 ^ (prefixWord ++ tailWord_5596343).sum := by decide
  have hdescent : baseEnd_5596343 < baseStart_5596343 := by decide
  rcases family_descends (prefixWord ++ tailWord_5596343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5596383 : List Nat := [1, 1, 2, 3, 2, 1, 2, 5, 2, 4]
def baseStart_5596383 : Nat := 118140960795 + 5596383 * 2 ^ 59
def prefixEnd_5596383 : Nat := 4983230072969 + 3 ^ 40 * 5596383 * 2
def baseEnd_5596383 : Nat := 957878135216960953158403

theorem tailTrace_5596383 : CollatzResearch.WordTrace tailWord_5596383 prefixEnd_5596383 957878135216960953158403 := by
  unfold tailWord_5596383
  simp only [CollatzResearch.WordTrace]
  refine ⟨204116856884267651967489803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136077904589511767978326535 204116856884267651967489803)
  ·
    refine ⟨306175285326401477951234705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204116856884267651967489803 306175285326401477951234705)
    ·
      refine ⟨229631463994801108463426029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 306175285326401477951234705 229631463994801108463426029)
      ·
        refine ⟨86111798998050415673784761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 229631463994801108463426029 86111798998050415673784761)
        ·
          refine ⟨64583849248537811755338571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86111798998050415673784761 64583849248537811755338571)
          ·
            refine ⟨96875773872806717633007857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64583849248537811755338571 96875773872806717633007857)
            ·
              refine ⟨72656830404605038224755893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96875773872806717633007857 72656830404605038224755893)
              ·
                refine ⟨6811577850431722333570865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 72656830404605038224755893 6811577850431722333570865)
                ·
                  refine ⟨5108683387823791750178149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6811577850431722333570865 5108683387823791750178149)
                  ·
                    refine ⟨957878135216960953158403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5108683387823791750178149 957878135216960953158403)
                    ·
                      rfl

theorem cell23_5596383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 5, 2, 4].length) (baseStart_5596383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5596383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5596383 prefixEnd_5596383 := by exact prefixLift 5596383
  have htrace : WordTrace (prefixWord ++ tailWord_5596383) baseStart_5596383 baseEnd_5596383 := by
    simpa [prefixWord, tailWord_5596383, baseEnd_5596383] using wordTrace_append hprefix tailTrace_5596383
  have hstable : (prefixWord ++ tailWord_5596383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5596383).length < 2 ^ (prefixWord ++ tailWord_5596383).sum := by decide
  have hdescent : baseEnd_5596383 < baseStart_5596383 := by decide
  rcases family_descends (prefixWord ++ tailWord_5596383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5596396 : List Nat := [2, 2, 1, 1, 2, 5, 1, 9]
def baseStart_5596396 : Nat := 118140960795 + 5596396 * 2 ^ 59
def prefixEnd_5596396 : Nat := 4983230072969 + 3 ^ 40 * 5596396 * 2
def baseEnd_5596396 : Nat := 106431151144421900318987

theorem tailTrace_5596396 : CollatzResearch.WordTrace tailWord_5596396 prefixEnd_5596396 106431151144421900318987 := by
  unfold tailWord_5596396
  simp only [CollatzResearch.WordTrace]
  refine ⟨102058665516610277593856521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136078220688813703458475361 102058665516610277593856521)
  ·
    refine ⟨76543999137457708195392391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102058665516610277593856521 76543999137457708195392391)
    ·
      refine ⟨114815998706186562293088587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76543999137457708195392391 114815998706186562293088587)
      ·
        refine ⟨172223998059279843439632881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114815998706186562293088587 172223998059279843439632881)
        ·
          refine ⟨129167998544459882579724661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172223998059279843439632881 129167998544459882579724661)
          ·
            refine ⟨12109499863543113991849187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 129167998544459882579724661 12109499863543113991849187)
            ·
              refine ⟨18164249795314670987773781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12109499863543113991849187 18164249795314670987773781)
              ·
                refine ⟨106431151144421900318987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18164249795314670987773781 106431151144421900318987)
                ·
                  rfl

theorem cell23_5596396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 9].length) (baseStart_5596396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5596396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5596396 prefixEnd_5596396 := by exact prefixLift 5596396
  have htrace : WordTrace (prefixWord ++ tailWord_5596396) baseStart_5596396 baseEnd_5596396 := by
    simpa [prefixWord, tailWord_5596396, baseEnd_5596396] using wordTrace_append hprefix tailTrace_5596396
  have hstable : (prefixWord ++ tailWord_5596396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5596396).length < 2 ^ (prefixWord ++ tailWord_5596396).sum := by decide
  have hdescent : baseEnd_5596396 < baseStart_5596396 := by decide
  rcases family_descends (prefixWord ++ tailWord_5596396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5596424 : List Nat := [2, 1, 3, 2, 4, 2, 1, 1, 3, 2, 2]
def baseStart_5596424 : Nat := 118140960795 + 5596424 * 2 ^ 59
def prefixEnd_5596424 : Nat := 4983230072969 + 3 ^ 40 * 5596424 * 2
def baseEnd_5596424 : Nat := 2873655458357717199062521

theorem tailTrace_5596424 : CollatzResearch.WordTrace tailWord_5596424 prefixEnd_5596424 2873655458357717199062521 := by
  unfold tailWord_5596424
  simp only [CollatzResearch.WordTrace]
  refine ⟨102059176138559557984866163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136078901518079410646488217 102059176138559557984866163)
  ·
    refine ⟨153088764207839336977299245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102059176138559557984866163 153088764207839336977299245)
    ·
      refine ⟨57408286577939751366487217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 153088764207839336977299245 57408286577939751366487217)
      ·
        refine ⟨43056214933454813524865413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57408286577939751366487217 43056214933454813524865413)
        ·
          refine ⟨8073040300022777535912265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43056214933454813524865413 8073040300022777535912265)
          ·
            refine ⟨6054780225017083151934199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8073040300022777535912265 6054780225017083151934199)
            ·
              refine ⟨9082170337525624727901299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6054780225017083151934199 9082170337525624727901299)
              ·
                refine ⟨13623255506288437091851949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9082170337525624727901299 13623255506288437091851949)
                ·
                  refine ⟨5108720814858163909444481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13623255506288437091851949 5108720814858163909444481)
                  ·
                    refine ⟨3831540611143622932083361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5108720814858163909444481 3831540611143622932083361)
                    ·
                      refine ⟨2873655458357717199062521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3831540611143622932083361 2873655458357717199062521)
                      ·
                        rfl

theorem cell23_5596424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 1, 1, 3, 2, 2].length) (baseStart_5596424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5596424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5596424 prefixEnd_5596424 := by exact prefixLift 5596424
  have htrace : WordTrace (prefixWord ++ tailWord_5596424) baseStart_5596424 baseEnd_5596424 := by
    simpa [prefixWord, tailWord_5596424, baseEnd_5596424] using wordTrace_append hprefix tailTrace_5596424
  have hstable : (prefixWord ++ tailWord_5596424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5596424).length < 2 ^ (prefixWord ++ tailWord_5596424).sum := by decide
  have hdescent : baseEnd_5596424 < baseStart_5596424 := by decide
  rcases family_descends (prefixWord ++ tailWord_5596424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5596426 : List Nat := [3, 1, 2, 2, 1, 1, 1, 3, 2, 7]
def baseStart_5596426 : Nat := 118140960795 + 5596426 * 2 ^ 59
def prefixEnd_5596426 : Nat := 4983230072969 + 3 ^ 40 * 5596426 * 2
def baseEnd_5596426 : Nat := 957885495106342063745837

theorem tailTrace_5596426 : CollatzResearch.WordTrace tailWord_5596426 prefixEnd_5596426 957885495106342063745837 := by
  unfold tailWord_5596426
  simp only [CollatzResearch.WordTrace]
  refine ⟨51029606305777967577826283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136078950148741246874203421 51029606305777967577826283)
  ·
    refine ⟨76544409458666951366739425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51029606305777967577826283 76544409458666951366739425)
    ·
      refine ⟨57408307094000213525054569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76544409458666951366739425 57408307094000213525054569)
      ·
        refine ⟨43056230320500160143790927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57408307094000213525054569 43056230320500160143790927)
        ·
          refine ⟨64584345480750240215686391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43056230320500160143790927 64584345480750240215686391)
          ·
            refine ⟨96876518221125360323529587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64584345480750240215686391 96876518221125360323529587)
            ·
              refine ⟨145314777331688040485294381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96876518221125360323529587 145314777331688040485294381)
              ·
                refine ⟨54493041499383015181985393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 145314777331688040485294381 54493041499383015181985393)
                ·
                  refine ⟨40869781124537261386489045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54493041499383015181985393 40869781124537261386489045)
                  ·
                    refine ⟨957885495106342063745837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40869781124537261386489045 957885495106342063745837)
                    ·
                      rfl

theorem cell23_5596426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 3, 2, 7].length) (baseStart_5596426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5596426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5596426 prefixEnd_5596426 := by exact prefixLift 5596426
  have htrace : WordTrace (prefixWord ++ tailWord_5596426) baseStart_5596426 baseEnd_5596426 := by
    simpa [prefixWord, tailWord_5596426, baseEnd_5596426] using wordTrace_append hprefix tailTrace_5596426
  have hstable : (prefixWord ++ tailWord_5596426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5596426).length < 2 ^ (prefixWord ++ tailWord_5596426).sum := by decide
  have hdescent : baseEnd_5596426 < baseStart_5596426 := by decide
  rcases family_descends (prefixWord ++ tailWord_5596426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5596434 : List Nat := [3, 2, 4, 2, 1, 1, 1, 3, 2, 4]
def baseStart_5596434 : Nat := 118140960795 + 5596434 * 2 ^ 59
def prefixEnd_5596434 : Nat := 4983230072969 + 3 ^ 40 * 5596434 * 2
def baseEnd_5596434 : Nat := 957886864388087386645825

theorem tailTrace_5596434 : CollatzResearch.WordTrace tailWord_5596434 prefixEnd_5596434 957886864388087386645825 := by
  unfold tailWord_5596434
  simp only [CollatzResearch.WordTrace]
  refine ⟨51029679251770721919399089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136079144671388591785064237 51029679251770721919399089)
  ·
    refine ⟨38272259438828041439549317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51029679251770721919399089 38272259438828041439549317)
    ·
      refine ⟨7176048644780257769915497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38272259438828041439549317 7176048644780257769915497)
      ·
        refine ⟨5382036483585193327436623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7176048644780257769915497 5382036483585193327436623)
        ·
          refine ⟨8073054725377789991154935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5382036483585193327436623 8073054725377789991154935)
          ·
            refine ⟨12109582088066684986732403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8073054725377789991154935 12109582088066684986732403)
            ·
              refine ⟨18164373132100027480098605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12109582088066684986732403 18164373132100027480098605)
              ·
                refine ⟨6811639924537510305036977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18164373132100027480098605 6811639924537510305036977)
                ·
                  refine ⟨5108729943403132728777733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6811639924537510305036977 5108729943403132728777733)
                  ·
                    refine ⟨957886864388087386645825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5108729943403132728777733 957886864388087386645825)
                    ·
                      rfl

theorem cell23_5596434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_5596434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5596434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5596434 prefixEnd_5596434 := by exact prefixLift 5596434
  have htrace : WordTrace (prefixWord ++ tailWord_5596434) baseStart_5596434 baseEnd_5596434 := by
    simpa [prefixWord, tailWord_5596434, baseEnd_5596434] using wordTrace_append hprefix tailTrace_5596434
  have hstable : (prefixWord ++ tailWord_5596434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5596434).length < 2 ^ (prefixWord ++ tailWord_5596434).sum := by decide
  have hdescent : baseEnd_5596434 < baseStart_5596434 := by decide
  rcases family_descends (prefixWord ++ tailWord_5596434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5596497 : List Nat := [1, 2, 2, 1, 4, 1, 1, 5, 2, 2, 2]
def baseStart_5596497 : Nat := 118140960795 + 5596497 * 2 ^ 59
def prefixEnd_5596497 : Nat := 4983230072969 + 3 ^ 40 * 5596497 * 2
def baseEnd_5596497 : Nat := 2873692942445495413449685

theorem tailTrace_5596497 : CollatzResearch.WordTrace tailWord_5596497 prefixEnd_5596497 2873692942445495413449685 := by
  unfold tailWord_5596497
  simp only [CollatzResearch.WordTrace]
  refine ⟨204121014805854649437139745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136080676537236432958093163 204121014805854649437139745)
  ·
    refine ⟨153090761104390987077854809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204121014805854649437139745 153090761104390987077854809)
    ·
      refine ⟨114818070828293240308391107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153090761104390987077854809 114818070828293240308391107)
      ·
        refine ⟨172227106242439860462586661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114818070828293240308391107 172227106242439860462586661)
        ·
          refine ⟨32292582420457473836734999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 172227106242439860462586661 32292582420457473836734999)
          ·
            refine ⟨48438873630686210755102499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32292582420457473836734999 48438873630686210755102499)
            ·
              refine ⟨72658310446029316132653749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48438873630686210755102499 72658310446029316132653749)
              ·
                refine ⟨6811716604315248387436289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 72658310446029316132653749 6811716604315248387436289)
                ·
                  refine ⟨5108787453236436290577217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6811716604315248387436289 5108787453236436290577217)
                  ·
                    refine ⟨3831590589927327217932913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5108787453236436290577217 3831590589927327217932913)
                    ·
                      refine ⟨2873692942445495413449685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3831590589927327217932913 2873692942445495413449685)
                      ·
                        rfl

theorem cell23_5596497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 5, 2, 2, 2].length) (baseStart_5596497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5596497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5596497 prefixEnd_5596497 := by exact prefixLift 5596497
  have htrace : WordTrace (prefixWord ++ tailWord_5596497) baseStart_5596497 baseEnd_5596497 := by
    simpa [prefixWord, tailWord_5596497, baseEnd_5596497] using wordTrace_append hprefix tailTrace_5596497
  have hstable : (prefixWord ++ tailWord_5596497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5596497).length < 2 ^ (prefixWord ++ tailWord_5596497).sum := by decide
  have hdescent : baseEnd_5596497 < baseStart_5596497 := by decide
  rcases family_descends (prefixWord ++ tailWord_5596497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5596503 : List Nat := [1, 1, 3, 2, 3, 3, 1, 2, 7]
def baseStart_5596503 : Nat := 118140960795 + 5596503 * 2 ^ 59
def prefixEnd_5596503 : Nat := 4983230072969 + 3 ^ 40 * 5596503 * 2
def baseEnd_5596503 : Nat := 319299558147713598886073

theorem tailTrace_5596503 : CollatzResearch.WordTrace tailWord_5596503 prefixEnd_5596503 319299558147713598886073 := by
  unfold tailWord_5596503
  simp only [CollatzResearch.WordTrace]
  refine ⟨204121233643832912461858163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136080822429221941641238775 204121233643832912461858163)
  ·
    refine ⟨306181850465749368692787245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204121233643832912461858163 306181850465749368692787245)
    ·
      refine ⟨114818193924656013259795217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 306181850465749368692787245 114818193924656013259795217)
      ·
        refine ⟨86113645443492009944846413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114818193924656013259795217 86113645443492009944846413)
        ·
          refine ⟨32292617041309503729317405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86113645443492009944846413 32292617041309503729317405)
          ·
            refine ⟨12109731390491063898494027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32292617041309503729317405 12109731390491063898494027)
            ·
              refine ⟨18164597085736595847741041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12109731390491063898494027 18164597085736595847741041)
              ·
                refine ⟨13623447814302446885805781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18164597085736595847741041 13623447814302446885805781)
                ·
                  refine ⟨319299558147713598886073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13623447814302446885805781 319299558147713598886073)
                  ·
                    rfl

theorem cell23_5596503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 2, 7].length) (baseStart_5596503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5596503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5596503 prefixEnd_5596503 := by exact prefixLift 5596503
  have htrace : WordTrace (prefixWord ++ tailWord_5596503) baseStart_5596503 baseEnd_5596503 := by
    simpa [prefixWord, tailWord_5596503, baseEnd_5596503] using wordTrace_append hprefix tailTrace_5596503
  have hstable : (prefixWord ++ tailWord_5596503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5596503).length < 2 ^ (prefixWord ++ tailWord_5596503).sum := by decide
  have hdescent : baseEnd_5596503 < baseStart_5596503 := by decide
  rcases family_descends (prefixWord ++ tailWord_5596503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5596570 : List Nat := [3, 1, 1, 4, 1, 1, 2, 3, 2, 1, 4]
def baseStart_5596570 : Nat := 118140960795 + 5596570 * 2 ^ 59
def prefixEnd_5596570 : Nat := 4983230072969 + 3 ^ 40 * 5596570 * 2
def baseEnd_5596570 : Nat := 2873730426533273627836849

theorem tailTrace_5596570 : CollatzResearch.WordTrace tailWord_5596570 prefixEnd_5596570 2873730426533273627836849 := by
  unfold tailWord_5596570
  simp only [CollatzResearch.WordTrace]
  refine ⟨51030919333647545726136791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136082451556393455269698109 51030919333647545726136791)
  ·
    refine ⟨76546379000471318589205187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51030919333647545726136791 76546379000471318589205187)
    ·
      refine ⟨114819568500706977883807781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76546379000471318589205187 114819568500706977883807781)
      ·
        refine ⟨21528669093882558353213959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 114819568500706977883807781 21528669093882558353213959)
        ·
          refine ⟨32293003640823837529820939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21528669093882558353213959 32293003640823837529820939)
          ·
            refine ⟨48439505461235756294731409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32293003640823837529820939 48439505461235756294731409)
            ·
              refine ⟨36329629095926817221048557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48439505461235756294731409 36329629095926817221048557)
              ·
                refine ⟨13623610910972556457893209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36329629095926817221048557 13623610910972556457893209)
                ·
                  refine ⟨10217708183229417343419907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13623610910972556457893209 10217708183229417343419907)
                  ·
                    refine ⟨15326562274844126015129861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10217708183229417343419907 15326562274844126015129861)
                    ·
                      refine ⟨2873730426533273627836849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15326562274844126015129861 2873730426533273627836849)
                      ·
                        rfl

theorem cell23_5596570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_5596570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5596570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5596570 prefixEnd_5596570 := by exact prefixLift 5596570
  have htrace : WordTrace (prefixWord ++ tailWord_5596570) baseStart_5596570 baseEnd_5596570 := by
    simpa [prefixWord, tailWord_5596570, baseEnd_5596570] using wordTrace_append hprefix tailTrace_5596570
  have hstable : (prefixWord ++ tailWord_5596570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5596570).length < 2 ^ (prefixWord ++ tailWord_5596570).sum := by decide
  have hdescent : baseEnd_5596570 < baseStart_5596570 := by decide
  rcases family_descends (prefixWord ++ tailWord_5596570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5596593 : List Nat := [1, 2, 2, 4, 1, 1, 1, 3, 8]
def baseStart_5596593 : Nat := 118140960795 + 5596593 * 2 ^ 59
def prefixEnd_5596593 : Nat := 4983230072969 + 3 ^ 40 * 5596593 * 2
def baseEnd_5596593 : Nat := 319304692954258559761027

theorem tailTrace_5596593 : CollatzResearch.WordTrace tailWord_5596593 prefixEnd_5596593 319304692954258559761027 := by
  unfold tailWord_5596593
  simp only [CollatzResearch.WordTrace]
  refine ⟨204124516213506857832634433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136083010809004571888422955 204124516213506857832634433)
  ·
    refine ⟨153093387160130143374475825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204124516213506857832634433 153093387160130143374475825)
    ·
      refine ⟨114820040370097607530856869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153093387160130143374475825 114820040370097607530856869)
      ·
        refine ⟨21528757569393301412035663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 114820040370097607530856869 21528757569393301412035663)
        ·
          refine ⟨32293136354089952118053495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21528757569393301412035663 32293136354089952118053495)
          ·
            refine ⟨48439704531134928177080243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32293136354089952118053495 48439704531134928177080243)
            ·
              refine ⟨72659556796702392265620365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48439704531134928177080243 72659556796702392265620365)
              ·
                refine ⟨27247333798763397099607637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72659556796702392265620365 27247333798763397099607637)
                ·
                  refine ⟨319304692954258559761027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27247333798763397099607637 319304692954258559761027)
                  ·
                    rfl

theorem cell23_5596593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 3, 8].length) (baseStart_5596593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5596593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5596593 prefixEnd_5596593 := by exact prefixLift 5596593
  have htrace : WordTrace (prefixWord ++ tailWord_5596593) baseStart_5596593 baseEnd_5596593 := by
    simpa [prefixWord, tailWord_5596593, baseEnd_5596593] using wordTrace_append hprefix tailTrace_5596593
  have hstable : (prefixWord ++ tailWord_5596593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5596593).length < 2 ^ (prefixWord ++ tailWord_5596593).sum := by decide
  have hdescent : baseEnd_5596593 < baseStart_5596593 := by decide
  rcases family_descends (prefixWord ++ tailWord_5596593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5596597 : List Nat := [1, 3, 3, 2, 2, 1, 3, 1, 3, 4]
def baseStart_5596597 : Nat := 118140960795 + 5596597 * 2 ^ 59
def prefixEnd_5596597 : Nat := 4983230072969 + 3 ^ 40 * 5596597 * 2
def baseEnd_5596597 : Nat := 957914763503648340733075

theorem tailTrace_5596597 : CollatzResearch.WordTrace tailWord_5596597 prefixEnd_5596597 957914763503648340733075 := by
  unfold tailWord_5596597
  simp only [CollatzResearch.WordTrace]
  refine ⟨204124662105492366515780045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136083108070328244343853363 204124662105492366515780045)
  ·
    refine ⟨76546748289559637443417517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 204124662105492366515780045 76546748289559637443417517)
    ·
      refine ⟨28705030608584864041281569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76546748289559637443417517 28705030608584864041281569)
      ·
        refine ⟨21528772956438648030961177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28705030608584864041281569 21528772956438648030961177)
        ·
          refine ⟨16146579717328986023220883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21528772956438648030961177 16146579717328986023220883)
          ·
            refine ⟨24219869575993479034831325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16146579717328986023220883 24219869575993479034831325)
            ·
              refine ⟨9082451090997554638061747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24219869575993479034831325 9082451090997554638061747)
              ·
                refine ⟨13623676636496331957092621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9082451090997554638061747 13623676636496331957092621)
                ·
                  refine ⟨5108878738686124483909733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13623676636496331957092621 5108878738686124483909733)
                  ·
                    refine ⟨957914763503648340733075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5108878738686124483909733 957914763503648340733075)
                    ·
                      rfl

theorem cell23_5596597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3, 1, 3, 4].length) (baseStart_5596597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5596597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5596597 prefixEnd_5596597 := by exact prefixLift 5596597
  have htrace : WordTrace (prefixWord ++ tailWord_5596597) baseStart_5596597 baseEnd_5596597 := by
    simpa [prefixWord, tailWord_5596597, baseEnd_5596597] using wordTrace_append hprefix tailTrace_5596597
  have hstable : (prefixWord ++ tailWord_5596597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5596597).length < 2 ^ (prefixWord ++ tailWord_5596597).sum := by decide
  have hdescent : baseEnd_5596597 < baseStart_5596597 := by decide
  rcases family_descends (prefixWord ++ tailWord_5596597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5596704 : List Nat := [2, 1, 1, 6, 1, 1, 3, 2, 2, 4]
def baseStart_5596704 : Nat := 118140960795 + 5596704 * 2 ^ 59
def prefixEnd_5596704 : Nat := 4983230072969 + 3 ^ 40 * 5596704 * 2
def baseEnd_5596704 : Nat := 957933077646992034520411

theorem tailTrace_5596704 : CollatzResearch.WordTrace tailWord_5596704 prefixEnd_5596704 957933077646992034520411 := by
  unfold tailWord_5596704
  simp only [CollatzResearch.WordTrace]
  refine ⟨102064282358052361894962583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136085709810736482526616777 102064282358052361894962583)
  ·
    refine ⟨153096423537078542842443875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102064282358052361894962583 153096423537078542842443875)
    ·
      refine ⟨229644635305617814263665813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153096423537078542842443875 229644635305617814263665813)
      ·
        refine ⟨10764592279950835043609335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 229644635305617814263665813 10764592279950835043609335)
        ·
          refine ⟨16146888419926252565414003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10764592279950835043609335 16146888419926252565414003)
          ·
            refine ⟨24220332629889378848121005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16146888419926252565414003 24220332629889378848121005)
            ·
              refine ⟨9082624736208517068045377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24220332629889378848121005 9082624736208517068045377)
              ·
                refine ⟨6811968552156387801034033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9082624736208517068045377 6811968552156387801034033)
                ·
                  refine ⟨5108976414117290850775525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6811968552156387801034033 5108976414117290850775525)
                  ·
                    refine ⟨957933077646992034520411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5108976414117290850775525 957933077646992034520411)
                    ·
                      rfl

theorem cell23_5596704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3, 2, 2, 4].length) (baseStart_5596704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5596704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5596704 prefixEnd_5596704 := by exact prefixLift 5596704
  have htrace : WordTrace (prefixWord ++ tailWord_5596704) baseStart_5596704 baseEnd_5596704 := by
    simpa [prefixWord, tailWord_5596704, baseEnd_5596704] using wordTrace_append hprefix tailTrace_5596704
  have hstable : (prefixWord ++ tailWord_5596704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5596704).length < 2 ^ (prefixWord ++ tailWord_5596704).sum := by decide
  have hdescent : baseEnd_5596704 < baseStart_5596704 := by decide
  rcases family_descends (prefixWord ++ tailWord_5596704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5596727 : List Nat := [1, 1, 3, 1, 2, 4, 3, 1, 1, 3, 3]
def baseStart_5596727 : Nat := 118140960795 + 5596727 * 2 ^ 59
def prefixEnd_5596727 : Nat := 4983230072969 + 3 ^ 40 * 5596727 * 2
def baseEnd_5596727 : Nat := 2873811042996029513573627

theorem tailTrace_5596727 : CollatzResearch.WordTrace tailWord_5596727 prefixEnd_5596727 2873811042996029513573627 := by
  unfold tailWord_5596727
  simp only [CollatzResearch.WordTrace]
  refine ⟨204129403595021398718012435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136086269063347599145341623 204129403595021398718012435)
  ·
    refine ⟨306194105392532098077018653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204129403595021398718012435 306194105392532098077018653)
    ·
      refine ⟨114822789522199536778881995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 306194105392532098077018653 114822789522199536778881995)
      ·
        refine ⟨172234184283299305168322993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114822789522199536778881995 172234184283299305168322993)
        ·
          refine ⟨129175638212474478876242245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172234184283299305168322993 129175638212474478876242245)
          ·
            refine ⟨24220432164838964789295421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 129175638212474478876242245 24220432164838964789295421)
            ·
              refine ⟨9082662061814611795985783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24220432164838964789295421 9082662061814611795985783)
              ·
                refine ⟨13623993092721917693978675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9082662061814611795985783 13623993092721917693978675)
                ·
                  refine ⟨20435989639082876540968013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13623993092721917693978675 20435989639082876540968013)
                  ·
                    refine ⟨7663496114656078702863005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20435989639082876540968013 7663496114656078702863005)
                    ·
                      refine ⟨2873811042996029513573627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7663496114656078702863005 2873811042996029513573627)
                      ·
                        rfl

theorem cell23_5596727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3, 1, 1, 3, 3].length) (baseStart_5596727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5596727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5596727 prefixEnd_5596727 := by exact prefixLift 5596727
  have htrace : WordTrace (prefixWord ++ tailWord_5596727) baseStart_5596727 baseEnd_5596727 := by
    simpa [prefixWord, tailWord_5596727, baseEnd_5596727] using wordTrace_append hprefix tailTrace_5596727
  have hstable : (prefixWord ++ tailWord_5596727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5596727).length < 2 ^ (prefixWord ++ tailWord_5596727).sum := by decide
  have hdescent : baseEnd_5596727 < baseStart_5596727 := by decide
  rcases family_descends (prefixWord ++ tailWord_5596727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5596750 : List Nat := [4, 1, 1, 1, 1, 2, 1, 2, 1, 5, 4]
def baseStart_5596750 : Nat := 118140960795 + 5596750 * 2 ^ 59
def prefixEnd_5596750 : Nat := 4983230072969 + 3 ^ 40 * 5596750 * 2
def baseEnd_5596750 : Nat := 2873822853051082923586021

theorem tailTrace_5596750 : CollatzResearch.WordTrace tailWord_5596750 prefixEnd_5596750 2873822853051082923586021 := by
  unfold tailWord_5596750
  simp only [CollatzResearch.WordTrace]
  refine ⟨25516280309242259205762463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136086828315958715764066469 25516280309242259205762463)
  ·
    refine ⟨38274420463863388808643695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25516280309242259205762463 38274420463863388808643695)
    ·
      refine ⟨57411630695795083212965543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38274420463863388808643695 57411630695795083212965543)
      ·
        refine ⟨86117446043692624819448315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57411630695795083212965543 86117446043692624819448315)
        ·
          refine ⟨129176169065538937229172473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86117446043692624819448315 129176169065538937229172473)
          ·
            refine ⟨96882126799154202921879355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129176169065538937229172473 96882126799154202921879355)
            ·
              refine ⟨145323190198731304382819033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96882126799154202921879355 145323190198731304382819033)
              ·
                refine ⟨108992392649048478287114275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 145323190198731304382819033 108992392649048478287114275)
                ·
                  refine ⟨163488588973572717430671413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 108992392649048478287114275 163488588973572717430671413)
                  ·
                    refine ⟨15327055216272442259125445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 163488588973572717430671413 15327055216272442259125445)
                    ·
                      refine ⟨2873822853051082923586021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15327055216272442259125445 2873822853051082923586021)
                      ·
                        rfl

theorem cell23_5596750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 1, 5, 4].length) (baseStart_5596750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5596750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5596750 prefixEnd_5596750 := by exact prefixLift 5596750
  have htrace : WordTrace (prefixWord ++ tailWord_5596750) baseStart_5596750 baseEnd_5596750 := by
    simpa [prefixWord, tailWord_5596750, baseEnd_5596750] using wordTrace_append hprefix tailTrace_5596750
  have hstable : (prefixWord ++ tailWord_5596750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5596750).length < 2 ^ (prefixWord ++ tailWord_5596750).sum := by decide
  have hdescent : baseEnd_5596750 < baseStart_5596750 := by decide
  rcases family_descends (prefixWord ++ tailWord_5596750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5596778 : List Nat := [3, 1, 3, 2, 1, 4, 2, 1, 2, 1, 3]
def baseStart_5596778 : Nat := 118140960795 + 5596778 * 2 ^ 59
def prefixEnd_5596778 : Nat := 4983230072969 + 3 ^ 40 * 5596778 * 2
def baseEnd_5596778 : Nat := 2873837230509408814035893

theorem tailTrace_5596778 : CollatzResearch.WordTrace tailWord_5596778 prefixEnd_5596778 2873837230509408814035893 := by
  unfold tailWord_5596778
  simp only [CollatzResearch.WordTrace]
  refine ⟨51032815929459158607029747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136087509145224422952079325 51032815929459158607029747)
  ·
    refine ⟨76549223894188737910544621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51032815929459158607029747 76549223894188737910544621)
    ·
      refine ⟨28705958960320776716454233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76549223894188737910544621 28705958960320776716454233)
      ·
        refine ⟨21529469220240582537340675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28705958960320776716454233 21529469220240582537340675)
        ·
          refine ⟨32294203830360873806011013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21529469220240582537340675 32294203830360873806011013)
          ·
            refine ⟨6055163218192663838627065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32294203830360873806011013 6055163218192663838627065)
            ·
              refine ⟨4541372413644497878970299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6055163218192663838627065 4541372413644497878970299)
              ·
                refine ⟨6812058620466746818455449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4541372413644497878970299 6812058620466746818455449)
                ·
                  refine ⟨5109043965350060113841587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6812058620466746818455449 5109043965350060113841587)
                  ·
                    refine ⟨7663565948025090170762381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5109043965350060113841587 7663565948025090170762381)
                    ·
                      refine ⟨2873837230509408814035893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7663565948025090170762381 2873837230509408814035893)
                      ·
                        rfl

theorem cell23_5596778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 2, 1, 2, 1, 3].length) (baseStart_5596778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5596778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5596778 prefixEnd_5596778 := by exact prefixLift 5596778
  have htrace : WordTrace (prefixWord ++ tailWord_5596778) baseStart_5596778 baseEnd_5596778 := by
    simpa [prefixWord, tailWord_5596778, baseEnd_5596778] using wordTrace_append hprefix tailTrace_5596778
  have hstable : (prefixWord ++ tailWord_5596778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5596778).length < 2 ^ (prefixWord ++ tailWord_5596778).sum := by decide
  have hdescent : baseEnd_5596778 < baseStart_5596778 := by decide
  rcases family_descends (prefixWord ++ tailWord_5596778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5596780 : List Nat := [2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 4]
def baseStart_5596780 : Nat := 118140960795 + 5596780 * 2 ^ 59
def prefixEnd_5596780 : Nat := 4983230072969 + 3 ^ 40 * 5596780 * 2
def baseEnd_5596780 : Nat := 2873838257470717806210883

theorem tailTrace_5596780 : CollatzResearch.WordTrace tailWord_5596780 prefixEnd_5596780 2873838257470717806210883 := by
  unfold tailWord_5596780
  simp only [CollatzResearch.WordTrace]
  refine ⟨102065668331914694384845897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136087557775886259179794529 102065668331914694384845897)
  ·
    refine ⟨76549251248936020788634423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102065668331914694384845897 76549251248936020788634423)
    ·
      refine ⟨114823876873404031182951635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76549251248936020788634423 114823876873404031182951635)
      ·
        refine ⟨172235815310106046774427453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114823876873404031182951635 172235815310106046774427453)
        ·
          refine ⟨64588430741289767540410295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 172235815310106046774427453 64588430741289767540410295)
          ·
            refine ⟨96882646111934651310615443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64588430741289767540410295 96882646111934651310615443)
            ·
              refine ⟨145323969167901976965923165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96882646111934651310615443 145323969167901976965923165)
              ·
                refine ⟨54496488437963241362221187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 145323969167901976965923165 54496488437963241362221187)
                ·
                  refine ⟨81744732656944862043331781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54496488437963241362221187 81744732656944862043331781)
                  ·
                    refine ⟨15327137373177161633124709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 81744732656944862043331781 15327137373177161633124709)
                    ·
                      refine ⟨2873838257470717806210883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15327137373177161633124709 2873838257470717806210883)
                      ·
                        rfl

theorem cell23_5596780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 4].length) (baseStart_5596780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5596780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5596780 prefixEnd_5596780 := by exact prefixLift 5596780
  have htrace : WordTrace (prefixWord ++ tailWord_5596780) baseStart_5596780 baseEnd_5596780 := by
    simpa [prefixWord, tailWord_5596780, baseEnd_5596780] using wordTrace_append hprefix tailTrace_5596780
  have hstable : (prefixWord ++ tailWord_5596780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5596780).length < 2 ^ (prefixWord ++ tailWord_5596780).sum := by decide
  have hdescent : baseEnd_5596780 < baseStart_5596780 := by decide
  rcases family_descends (prefixWord ++ tailWord_5596780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5596824 : List Nat := [2, 1, 2, 4, 1, 3, 1, 4, 5]
def baseStart_5596824 : Nat := 118140960795 + 5596824 * 2 ^ 59
def prefixEnd_5596824 : Nat := 4983230072969 + 3 ^ 40 * 5596824 * 2
def baseEnd_5596824 : Nat := 319317872291057292673409

theorem tailTrace_5596824 : CollatzResearch.WordTrace tailWord_5596824 prefixEnd_5596824 319317872291057292673409 := by
  unfold tailWord_5596824
  simp only [CollatzResearch.WordTrace]
  refine ⟨102066470737834992142146763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136088627650446656189529017 102066470737834992142146763)
  ·
    refine ⟨153099706106752488213220145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102066470737834992142146763 153099706106752488213220145)
    ·
      refine ⟨114824779580064366159915109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153099706106752488213220145 114824779580064366159915109)
      ·
        refine ⟨21529646171262068654984083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 114824779580064366159915109 21529646171262068654984083)
        ·
          refine ⟨32294469256893102982476125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21529646171262068654984083 32294469256893102982476125)
          ·
            refine ⟨12110425971334913618428547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32294469256893102982476125 12110425971334913618428547)
            ·
              refine ⟨18165638957002370427642821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12110425971334913618428547 18165638957002370427642821)
              ·
                refine ⟨3406057304437944455183029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18165638957002370427642821 3406057304437944455183029)
                ·
                  refine ⟨319317872291057292673409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3406057304437944455183029 319317872291057292673409)
                  ·
                    rfl

theorem cell23_5596824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 4, 5].length) (baseStart_5596824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5596824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5596824 prefixEnd_5596824 := by exact prefixLift 5596824
  have htrace : WordTrace (prefixWord ++ tailWord_5596824) baseStart_5596824 baseEnd_5596824 := by
    simpa [prefixWord, tailWord_5596824, baseEnd_5596824] using wordTrace_append hprefix tailTrace_5596824
  have hstable : (prefixWord ++ tailWord_5596824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5596824).length < 2 ^ (prefixWord ++ tailWord_5596824).sum := by decide
  have hdescent : baseEnd_5596824 < baseStart_5596824 := by decide
  rcases family_descends (prefixWord ++ tailWord_5596824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5596918 : List Nat := [5, 1, 1, 1, 1, 3, 3, 3, 1, 4]
def baseStart_5596918 : Nat := 118140960795 + 5596918 * 2 ^ 59
def prefixEnd_5596918 : Nat := 4983230072969 + 3 ^ 40 * 5596918 * 2
def baseEnd_5596918 : Nat := 957969705933679422095083

theorem tailTrace_5596918 : CollatzResearch.WordTrace tailWord_5596918 prefixEnd_5596918 957969705933679422095083 := by
  unfold tailWord_5596918
  simp only [CollatzResearch.WordTrace]
  refine ⟨12758523121083089896138463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 136090913291552958892143605 12758523121083089896138463)
  ·
    refine ⟨19137784681624634844207695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12758523121083089896138463 19137784681624634844207695)
    ·
      refine ⟨28706677022436952266311543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19137784681624634844207695 28706677022436952266311543)
      ·
        refine ⟨43060015533655428399467315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28706677022436952266311543 43060015533655428399467315)
        ·
          refine ⟨64590023300483142599200973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43060015533655428399467315 64590023300483142599200973)
          ·
            refine ⟨24221258737681178474700365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64590023300483142599200973 24221258737681178474700365)
            ·
              refine ⟨9082972026630441928012637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24221258737681178474700365 9082972026630441928012637)
              ·
                refine ⟨3406114509986415723004739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9082972026630441928012637 3406114509986415723004739)
                ·
                  refine ⟨5109171764979623584507109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3406114509986415723004739 5109171764979623584507109)
                  ·
                    refine ⟨957969705933679422095083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5109171764979623584507109 957969705933679422095083)
                    ·
                      rfl

theorem cell23_5596918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3, 3, 1, 4].length) (baseStart_5596918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5596918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5596918 prefixEnd_5596918 := by exact prefixLift 5596918
  have htrace : WordTrace (prefixWord ++ tailWord_5596918) baseStart_5596918 baseEnd_5596918 := by
    simpa [prefixWord, tailWord_5596918, baseEnd_5596918] using wordTrace_append hprefix tailTrace_5596918
  have hstable : (prefixWord ++ tailWord_5596918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5596918).length < 2 ^ (prefixWord ++ tailWord_5596918).sum := by decide
  have hdescent : baseEnd_5596918 < baseStart_5596918 := by decide
  rcases family_descends (prefixWord ++ tailWord_5596918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5596935 : List Nat := [1, 1, 4, 4, 2, 1, 3, 2, 1, 4]
def baseStart_5596935 : Nat := 118140960795 + 5596935 * 2 ^ 59
def prefixEnd_5596935 : Nat := 4983230072969 + 3 ^ 40 * 5596935 * 2
def baseEnd_5596935 : Nat := 957972615657388233257557

theorem tailTrace_5596935 : CollatzResearch.WordTrace tailWord_5596935 prefixEnd_5596935 957972615657388233257557 := by
  unfold tailWord_5596935
  simp only [CollatzResearch.WordTrace]
  refine ⟨204136989978267850241584259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136091326652178566827722839 204136989978267850241584259)
  ·
    refine ⟨306205484967401775362376389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204136989978267850241584259 306205484967401775362376389)
    ·
      refine ⟨57413528431387832880445573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 306205484967401775362376389 57413528431387832880445573)
      ·
        refine ⟨10765036580885218665083545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57413528431387832880445573 10765036580885218665083545)
        ·
          refine ⟨8073777435663913998812659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10765036580885218665083545 8073777435663913998812659)
          ·
            refine ⟨12110666153495870998218989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8073777435663913998812659 12110666153495870998218989)
            ·
              refine ⟨4541499807560951624332121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12110666153495870998218989 4541499807560951624332121)
              ·
                refine ⟨3406124855670713718249091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4541499807560951624332121 3406124855670713718249091)
                ·
                  refine ⟨5109187283506070577373637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3406124855670713718249091 5109187283506070577373637)
                  ·
                    refine ⟨957972615657388233257557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5109187283506070577373637 957972615657388233257557)
                    ·
                      rfl

theorem cell23_5596935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 3, 2, 1, 4].length) (baseStart_5596935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5596935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5596935 prefixEnd_5596935 := by exact prefixLift 5596935
  have htrace : WordTrace (prefixWord ++ tailWord_5596935) baseStart_5596935 baseEnd_5596935 := by
    simpa [prefixWord, tailWord_5596935, baseEnd_5596935] using wordTrace_append hprefix tailTrace_5596935
  have hstable : (prefixWord ++ tailWord_5596935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5596935).length < 2 ^ (prefixWord ++ tailWord_5596935).sum := by decide
  have hdescent : baseEnd_5596935 < baseStart_5596935 := by decide
  rcases family_descends (prefixWord ++ tailWord_5596935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5596961 : List Nat := [1, 2, 3, 2, 1, 5, 1, 2, 1, 5]
def baseStart_5596961 : Nat := 118140960795 + 5596961 * 2 ^ 59
def prefixEnd_5596961 : Nat := 4983230072969 + 3 ^ 40 * 5596961 * 2
def baseEnd_5596961 : Nat := 957977065823060532682517

theorem tailTrace_5596961 : CollatzResearch.WordTrace tailWord_5596961 prefixEnd_5596961 957977065823060532682517 := by
  unfold tailWord_5596961
  simp only [CollatzResearch.WordTrace]
  refine ⟨204137938276173656682030737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136091958850782437788020491 204137938276173656682030737)
  ·
    refine ⟨153103453707130242511523053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204137938276173656682030737 153103453707130242511523053)
    ·
      refine ⟨57413795140173840941821145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 153103453707130242511523053 57413795140173840941821145)
      ·
        refine ⟨43060346355130380706365859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57413795140173840941821145 43060346355130380706365859)
        ·
          refine ⟨64590519532695571059548789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43060346355130380706365859 64590519532695571059548789)
          ·
            refine ⟨6055361206190209786832699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 64590519532695571059548789 6055361206190209786832699)
            ·
              refine ⟨9083041809285314680249049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6055361206190209786832699 9083041809285314680249049)
              ·
                refine ⟨6812281356963986010186787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9083041809285314680249049 6812281356963986010186787)
                ·
                  refine ⟨10218422035445979015280181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6812281356963986010186787 10218422035445979015280181)
                  ·
                    refine ⟨957977065823060532682517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10218422035445979015280181 957977065823060532682517)
                    ·
                      rfl

theorem cell23_5596961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 1, 2, 1, 5].length) (baseStart_5596961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5596961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5596961 prefixEnd_5596961 := by exact prefixLift 5596961
  have htrace : WordTrace (prefixWord ++ tailWord_5596961) baseStart_5596961 baseEnd_5596961 := by
    simpa [prefixWord, tailWord_5596961, baseEnd_5596961] using wordTrace_append hprefix tailTrace_5596961
  have hstable : (prefixWord ++ tailWord_5596961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5596961).length < 2 ^ (prefixWord ++ tailWord_5596961).sum := by decide
  have hdescent : baseEnd_5596961 < baseStart_5596961 := by decide
  rcases family_descends (prefixWord ++ tailWord_5596961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5596968 : List Nat := [2, 1, 5, 1, 1, 3, 2, 1, 2, 3, 2]
def baseStart_5596968 : Nat := 118140960795 + 5596968 * 2 ^ 59
def prefixEnd_5596968 : Nat := 4983230072969 + 3 ^ 40 * 5596968 * 2
def baseEnd_5596968 : Nat := 2873934791833763070660019

theorem tailTrace_5596968 : CollatzResearch.WordTrace tailWord_5596968 prefixEnd_5596968 2873934791833763070660019 := by
  unfold tailWord_5596968
  simp only [CollatzResearch.WordTrace]
  refine ⟨102069096793574148438767779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136092129058098864585023705 102069096793574148438767779)
  ·
    refine ⟨153103645190361222658151669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102069096793574148438767779 153103645190361222658151669)
    ·
      refine ⟨14353466736596364624201719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 153103645190361222658151669 14353466736596364624201719)
      ·
        refine ⟨21530200104894546936302579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14353466736596364624201719 21530200104894546936302579)
        ·
          refine ⟨32295300157341820404453869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21530200104894546936302579 32295300157341820404453869)
          ·
            refine ⟨12110737559003182651670201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32295300157341820404453869 12110737559003182651670201)
            ·
              refine ⟨9083053169252386988752651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12110737559003182651670201 9083053169252386988752651)
              ·
                refine ⟨13624579753878580483128977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9083053169252386988752651 13624579753878580483128977)
                ·
                  refine ⟨10218434815408935362346733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13624579753878580483128977 10218434815408935362346733)
                  ·
                    refine ⟨3831913055778350760880025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10218434815408935362346733 3831913055778350760880025)
                    ·
                      refine ⟨2873934791833763070660019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3831913055778350760880025 2873934791833763070660019)
                      ·
                        rfl

theorem cell23_5596968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2, 1, 2, 3, 2].length) (baseStart_5596968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5596968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5596968 prefixEnd_5596968 := by exact prefixLift 5596968
  have htrace : WordTrace (prefixWord ++ tailWord_5596968) baseStart_5596968 baseEnd_5596968 := by
    simpa [prefixWord, tailWord_5596968, baseEnd_5596968] using wordTrace_append hprefix tailTrace_5596968
  have hstable : (prefixWord ++ tailWord_5596968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5596968).length < 2 ^ (prefixWord ++ tailWord_5596968).sum := by decide
  have hdescent : baseEnd_5596968 < baseStart_5596968 := by decide
  rcases family_descends (prefixWord ++ tailWord_5596968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5596984 : List Nat := [2, 1, 2, 1, 3, 3, 3, 1, 1, 1, 5]
def baseStart_5596984 : Nat := 118140960795 + 5596984 * 2 ^ 59
def prefixEnd_5596984 : Nat := 4983230072969 + 3 ^ 40 * 5596984 * 2
def baseEnd_5596984 : Nat := 2873943007524235008059945

theorem tailTrace_5596984 : CollatzResearch.WordTrace tailWord_5596984 prefixEnd_5596984 2873943007524235008059945 := by
  unfold tailWord_5596984
  simp only [CollatzResearch.WordTrace]
  refine ⟨102069388577545165805059003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136092518103393554406745337 102069388577545165805059003)
  ·
    refine ⟨153104082866317748707588505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102069388577545165805059003 153104082866317748707588505)
    ·
      refine ⟨114828062149738311530691379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153104082866317748707588505 114828062149738311530691379)
      ·
        refine ⟨172242093224607467296037069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114828062149738311530691379 172242093224607467296037069)
        ·
          refine ⟨64590784959227800236013901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 172242093224607467296037069 64590784959227800236013901)
          ·
            refine ⟨24221544359710425088505213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64590784959227800236013901 24221544359710425088505213)
            ·
              refine ⟨9083079134891409408189455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24221544359710425088505213 9083079134891409408189455)
              ·
                refine ⟨13624618702337114112284183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9083079134891409408189455 13624618702337114112284183)
                ·
                  refine ⟨20436928053505671168426275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13624618702337114112284183 20436928053505671168426275)
                  ·
                    refine ⟨30655392080258506752639413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20436928053505671168426275 30655392080258506752639413)
                    ·
                      refine ⟨2873943007524235008059945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30655392080258506752639413 2873943007524235008059945)
                      ·
                        rfl

theorem cell23_5596984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3, 1, 1, 1, 5].length) (baseStart_5596984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5596984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5596984 prefixEnd_5596984 := by exact prefixLift 5596984
  have htrace : WordTrace (prefixWord ++ tailWord_5596984) baseStart_5596984 baseEnd_5596984 := by
    simpa [prefixWord, tailWord_5596984, baseEnd_5596984] using wordTrace_append hprefix tailTrace_5596984
  have hstable : (prefixWord ++ tailWord_5596984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5596984).length < 2 ^ (prefixWord ++ tailWord_5596984).sum := by decide
  have hdescent : baseEnd_5596984 < baseStart_5596984 := by decide
  rcases family_descends (prefixWord ++ tailWord_5596984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5596998 : List Nat := [6, 1, 1, 2, 1, 1, 1, 2, 3, 1, 4]
def baseStart_5596998 : Nat := 118140960795 + 5596998 * 2 ^ 59
def prefixEnd_5596998 : Nat := 4983230072969 + 3 ^ 40 * 5596998 * 2
def baseEnd_5596998 : Nat := 2873950196253397953284881

theorem tailTrace_5596998 : CollatzResearch.WordTrace tailWord_5596998 prefixEnd_5596998 2873950196253397953284881 := by
  unfold tailWord_5596998
  simp only [CollatzResearch.WordTrace]
  refine ⟨6379352743032487875035239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 136092858518026408000751765 6379352743032487875035239)
  ·
    refine ⟨9569029114548731812552859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6379352743032487875035239 9569029114548731812552859)
    ·
      refine ⟨14353543671823097718829289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9569029114548731812552859 14353543671823097718829289)
      ·
        refine ⟨10765157753867323289121967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14353543671823097718829289 10765157753867323289121967)
        ·
          refine ⟨16147736630800984933682951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10765157753867323289121967 16147736630800984933682951)
          ·
            refine ⟨24221604946201477400524427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16147736630800984933682951 24221604946201477400524427)
            ·
              refine ⟨36332407419302216100786641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24221604946201477400524427 36332407419302216100786641)
              ·
                refine ⟨27249305564476662075589981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36332407419302216100786641 27249305564476662075589981)
                ·
                  refine ⟨10218489586678748278346243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27249305564476662075589981 10218489586678748278346243)
                  ·
                    refine ⟨15327734380018122417519365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10218489586678748278346243 15327734380018122417519365)
                    ·
                      refine ⟨2873950196253397953284881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15327734380018122417519365 2873950196253397953284881)
                      ·
                        rfl

theorem cell23_5596998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_5596998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5596998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5596998 prefixEnd_5596998 := by exact prefixLift 5596998
  have htrace : WordTrace (prefixWord ++ tailWord_5596998) baseStart_5596998 baseEnd_5596998 := by
    simpa [prefixWord, tailWord_5596998, baseEnd_5596998] using wordTrace_append hprefix tailTrace_5596998
  have hstable : (prefixWord ++ tailWord_5596998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5596998).length < 2 ^ (prefixWord ++ tailWord_5596998).sum := by decide
  have hdescent : baseEnd_5596998 < baseStart_5596998 := by decide
  rcases family_descends (prefixWord ++ tailWord_5596998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5597017 : List Nat := [1, 2, 1, 2, 2, 3, 1, 2, 2, 7]
def baseStart_5597017 : Nat := 118140960795 + 5597017 * 2 ^ 59
def prefixEnd_5597017 : Nat := 4983230072969 + 3 ^ 40 * 5597017 * 2
def baseEnd_5597017 : Nat := 957986650795277792982431

theorem tailTrace_5597017 : CollatzResearch.WordTrace tailWord_5597017 prefixEnd_5597017 957986650795277792982431 := by
  unfold tailWord_5597017
  simp only [CollatzResearch.WordTrace]
  refine ⟨204139980763970778246069305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136093320509313852164046203 204139980763970778246069305)
  ·
    refine ⟨153104985572978083684551979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204139980763970778246069305 153104985572978083684551979)
    ·
      refine ⟨229657478359467125526827969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153104985572978083684551979 229657478359467125526827969)
      ·
        refine ⟨172243108769600344145120977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 229657478359467125526827969 172243108769600344145120977)
        ·
          refine ⟨129182331577200258108840733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172243108769600344145120977 129182331577200258108840733)
          ·
            refine ⟨48443374341450096790815275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 129182331577200258108840733 48443374341450096790815275)
            ·
              refine ⟨72665061512175145186222913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48443374341450096790815275 72665061512175145186222913)
              ·
                refine ⟨54498796134131358889667185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72665061512175145186222913 54498796134131358889667185)
                ·
                  refine ⟨40874097100598519167250389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54498796134131358889667185 40874097100598519167250389)
                  ·
                    refine ⟨957986650795277792982431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40874097100598519167250389 957986650795277792982431)
                    ·
                      rfl

theorem cell23_5597017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 7].length) (baseStart_5597017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5597017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5597017 prefixEnd_5597017 := by exact prefixLift 5597017
  have htrace : WordTrace (prefixWord ++ tailWord_5597017) baseStart_5597017 baseEnd_5597017 := by
    simpa [prefixWord, tailWord_5597017, baseEnd_5597017] using wordTrace_append hprefix tailTrace_5597017
  have hstable : (prefixWord ++ tailWord_5597017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5597017).length < 2 ^ (prefixWord ++ tailWord_5597017).sum := by decide
  have hdescent : baseEnd_5597017 < baseStart_5597017 := by decide
  rcases family_descends (prefixWord ++ tailWord_5597017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5597031 : List Nat := [1, 1, 5, 1, 2, 1, 2, 2, 4, 1, 3]
def baseStart_5597031 : Nat := 118140960795 + 5597031 * 2 ^ 59
def prefixEnd_5597031 : Nat := 4983230072969 + 3 ^ 40 * 5597031 * 2
def baseEnd_5597031 : Nat := 2873967141114996324172229

theorem tailTrace_5597031 : CollatzResearch.WordTrace tailWord_5597031 prefixEnd_5597031 2873967141114996324172229 := by
  unfold tailWord_5597031
  simp only [CollatzResearch.WordTrace]
  refine ⟨204140491385920058637078947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136093660923946705758052631 204140491385920058637078947)
  ·
    refine ⟨306210737078880087955618421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204140491385920058637078947 306210737078880087955618421)
    ·
      refine ⟨28707256601145008245839227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 306210737078880087955618421 28707256601145008245839227)
      ·
        refine ⟨43060884901717512368758841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28707256601145008245839227 43060884901717512368758841)
        ·
          refine ⟨32295663676288134276569131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43060884901717512368758841 32295663676288134276569131)
          ·
            refine ⟨48443495514432201414853697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32295663676288134276569131 48443495514432201414853697)
            ·
              refine ⟨36332621635824151061140273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48443495514432201414853697 36332621635824151061140273)
              ·
                refine ⟨27249466226868113295855205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36332621635824151061140273 27249466226868113295855205)
                ·
                  refine ⟨5109274917537771242972851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27249466226868113295855205 5109274917537771242972851)
                  ·
                    refine ⟨7663912376306656864459277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5109274917537771242972851 7663912376306656864459277)
                    ·
                      refine ⟨2873967141114996324172229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7663912376306656864459277 2873967141114996324172229)
                      ·
                        rfl

theorem cell23_5597031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 2, 4, 1, 3].length) (baseStart_5597031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5597031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5597031 prefixEnd_5597031 := by exact prefixLift 5597031
  have htrace : WordTrace (prefixWord ++ tailWord_5597031) baseStart_5597031 baseEnd_5597031 := by
    simpa [prefixWord, tailWord_5597031, baseEnd_5597031] using wordTrace_append hprefix tailTrace_5597031
  have hstable : (prefixWord ++ tailWord_5597031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5597031).length < 2 ^ (prefixWord ++ tailWord_5597031).sum := by decide
  have hdescent : baseEnd_5597031 < baseStart_5597031 := by decide
  rcases family_descends (prefixWord ++ tailWord_5597031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5597134 : List Nat := [4, 1, 1, 1, 2, 2, 1, 2, 1, 1, 7]
def baseStart_5597134 : Nat := 118140960795 + 5597134 * 2 ^ 59
def prefixEnd_5597134 : Nat := 4983230072969 + 3 ^ 40 * 5597134 * 2
def baseEnd_5597134 : Nat := 2874020029622409421184255

theorem tailTrace_5597134 : CollatzResearch.WordTrace tailWord_5597134 prefixEnd_5597134 2874020029622409421184255 := by
  unfold tailWord_5597134
  simp only [CollatzResearch.WordTrace]
  refine ⟨25518031013068363403509807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136096165403031271485385637 25518031013068363403509807)
  ·
    refine ⟨38277046519602545105264711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25518031013068363403509807 38277046519602545105264711)
    ·
      refine ⟨57415569779403817657897067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38277046519602545105264711 57415569779403817657897067)
      ·
        refine ⟨86123354669105726486845601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57415569779403817657897067 86123354669105726486845601)
        ·
          refine ⟨64592516001829294865134201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86123354669105726486845601 64592516001829294865134201)
          ·
            refine ⟨48444387001371971148850651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64592516001829294865134201 48444387001371971148850651)
            ·
              refine ⟨72666580502057956723275977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48444387001371971148850651 72666580502057956723275977)
              ·
                refine ⟨54499935376543467542456983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72666580502057956723275977 54499935376543467542456983)
                ·
                  refine ⟨81749903064815201313685475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54499935376543467542456983 81749903064815201313685475)
                  ·
                    refine ⟨122624854597222801970528213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 81749903064815201313685475 122624854597222801970528213)
                    ·
                      refine ⟨2874020029622409421184255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 122624854597222801970528213 2874020029622409421184255)
                      ·
                        rfl

theorem cell23_5597134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 2, 1, 1, 7].length) (baseStart_5597134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5597134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5597134 prefixEnd_5597134 := by exact prefixLift 5597134
  have htrace : WordTrace (prefixWord ++ tailWord_5597134) baseStart_5597134 baseEnd_5597134 := by
    simpa [prefixWord, tailWord_5597134, baseEnd_5597134] using wordTrace_append hprefix tailTrace_5597134
  have hstable : (prefixWord ++ tailWord_5597134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5597134).length < 2 ^ (prefixWord ++ tailWord_5597134).sum := by decide
  have hdescent : baseEnd_5597134 < baseStart_5597134 := by decide
  rcases family_descends (prefixWord ++ tailWord_5597134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5597141 : List Nat := [1, 3, 2, 3, 2, 1, 1, 3, 2, 5]
def baseStart_5597141 : Nat := 118140960795 + 5597141 * 2 ^ 59
def prefixEnd_5597141 : Nat := 4983230072969 + 3 ^ 40 * 5597141 * 2
def baseEnd_5597141 : Nat := 958007874662330297932241

theorem tailTrace_5597141 : CollatzResearch.WordTrace tailWord_5597141 prefixEnd_5597141 958007874662330297932241 := by
  unfold tailWord_5597141
  simp only [CollatzResearch.WordTrace]
  refine ⟨204144503415521547423583277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136096335610347698282388851 204144503415521547423583277)
  ·
    refine ⟨76554188780820580283843729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 204144503415521547423583277 76554188780820580283843729)
    ·
      refine ⟨57415641585615435212882797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76554188780820580283843729 57415641585615435212882797)
      ·
        refine ⟨21530865594605788204831049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57415641585615435212882797 21530865594605788204831049)
        ·
          refine ⟨16148149195954341153623287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21530865594605788204831049 16148149195954341153623287)
          ·
            refine ⟨24222223793931511730434931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16148149195954341153623287 24222223793931511730434931)
            ·
              refine ⟨36333335690897267595652397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24222223793931511730434931 36333335690897267595652397)
              ·
                refine ⟨13625000884086475348369649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36333335690897267595652397 13625000884086475348369649)
                ·
                  refine ⟨10218750663064856511277237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13625000884086475348369649 10218750663064856511277237)
                  ·
                    refine ⟨958007874662330297932241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10218750663064856511277237 958007874662330297932241)
                    ·
                      rfl

theorem cell23_5597141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 3, 2, 5].length) (baseStart_5597141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5597141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5597141 prefixEnd_5597141 := by exact prefixLift 5597141
  have htrace : WordTrace (prefixWord ++ tailWord_5597141) baseStart_5597141 baseEnd_5597141 := by
    simpa [prefixWord, tailWord_5597141, baseEnd_5597141] using wordTrace_append hprefix tailTrace_5597141
  have hstable : (prefixWord ++ tailWord_5597141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5597141).length < 2 ^ (prefixWord ++ tailWord_5597141).sum := by decide
  have hdescent : baseEnd_5597141 < baseStart_5597141 := by decide
  rcases family_descends (prefixWord ++ tailWord_5597141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5597181 : List Nat := [1, 4, 1, 1, 1, 2, 2, 2, 4, 2, 3]
def baseStart_5597181 : Nat := 118140960795 + 5597181 * 2 ^ 59
def prefixEnd_5597181 : Nat := 4983230072969 + 3 ^ 40 * 5597181 * 2
def baseEnd_5597181 : Nat := 2874044163213170737296539

theorem tailTrace_5597181 : CollatzResearch.WordTrace tailWord_5597181 prefixEnd_5597181 2874044163213170737296539 := by
  unfold tailWord_5597181
  simp only [CollatzResearch.WordTrace]
  refine ⟨204145962335376634255039397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136097308223584422836692931 204145962335376634255039397)
  ·
    refine ⟨38277367937883118922819887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 204145962335376634255039397 38277367937883118922819887)
    ·
      refine ⟨57416051906824678384229831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38277367937883118922819887 57416051906824678384229831)
      ·
        refine ⟨86124077860237017576344747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57416051906824678384229831 86124077860237017576344747)
        ·
          refine ⟨129186116790355526364517121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86124077860237017576344747 129186116790355526364517121)
          ·
            refine ⟨96889587592766644773387841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129186116790355526364517121 96889587592766644773387841)
            ·
              refine ⟨72667190694574983580040881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96889587592766644773387841 72667190694574983580040881)
              ·
                refine ⟨54500393020931237685030661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72667190694574983580040881 54500393020931237685030661)
                ·
                  refine ⟨10218823691424607065943249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54500393020931237685030661 10218823691424607065943249)
                  ·
                    refine ⟨7664117768568455299457437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10218823691424607065943249 7664117768568455299457437)
                    ·
                      refine ⟨2874044163213170737296539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7664117768568455299457437 2874044163213170737296539)
                      ·
                        rfl

theorem cell23_5597181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 2, 4, 2, 3].length) (baseStart_5597181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5597181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5597181 prefixEnd_5597181 := by exact prefixLift 5597181
  have htrace : WordTrace (prefixWord ++ tailWord_5597181) baseStart_5597181 baseEnd_5597181 := by
    simpa [prefixWord, tailWord_5597181, baseEnd_5597181] using wordTrace_append hprefix tailTrace_5597181
  have hstable : (prefixWord ++ tailWord_5597181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5597181).length < 2 ^ (prefixWord ++ tailWord_5597181).sum := by decide
  have hdescent : baseEnd_5597181 < baseStart_5597181 := by decide
  rcases family_descends (prefixWord ++ tailWord_5597181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5597248 : List Nat := [2, 1, 1, 2, 2, 5, 2, 2, 1, 5]
def baseStart_5597248 : Nat := 118140960795 + 5597248 * 2 ^ 59
def prefixEnd_5597248 : Nat := 4983230072969 + 3 ^ 40 * 5597248 * 2
def baseEnd_5597248 : Nat := 958026188805673991719577

theorem tailTrace_5597248 : CollatzResearch.WordTrace tailWord_5597248 prefixEnd_5597248 958026188805673991719577 := by
  unfold tailWord_5597248
  simp only [CollatzResearch.WordTrace]
  refine ⟨102074203013066952348864199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136098937350755936465152265 102074203013066952348864199)
  ·
    refine ⟨153111304519600428523296299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102074203013066952348864199 153111304519600428523296299)
    ·
      refine ⟨229666956779400642784944449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153111304519600428523296299 229666956779400642784944449)
      ·
        refine ⟨172250217584550482088708337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 229666956779400642784944449 172250217584550482088708337)
        ·
          refine ⟨129187663188412861566531253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172250217584550482088708337 129187663188412861566531253)
          ·
            refine ⟨12111343423913705771862305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 129187663188412861566531253 12111343423913705771862305)
            ·
              refine ⟨9083507567935279328896729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12111343423913705771862305 9083507567935279328896729)
              ·
                refine ⟨6812630675951459496672547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9083507567935279328896729 6812630675951459496672547)
                ·
                  refine ⟨10218946013927189245008821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6812630675951459496672547 10218946013927189245008821)
                  ·
                    refine ⟨958026188805673991719577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10218946013927189245008821 958026188805673991719577)
                    ·
                      rfl

theorem cell23_5597248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2, 2, 1, 5].length) (baseStart_5597248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5597248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5597248 prefixEnd_5597248 := by exact prefixLift 5597248
  have htrace : WordTrace (prefixWord ++ tailWord_5597248) baseStart_5597248 baseEnd_5597248 := by
    simpa [prefixWord, tailWord_5597248, baseEnd_5597248] using wordTrace_append hprefix tailTrace_5597248
  have hstable : (prefixWord ++ tailWord_5597248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5597248).length < 2 ^ (prefixWord ++ tailWord_5597248).sum := by decide
  have hdescent : baseEnd_5597248 < baseStart_5597248 := by decide
  rcases family_descends (prefixWord ++ tailWord_5597248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5597262 : List Nat := [4, 1, 1, 1, 1, 4, 3, 3, 1, 1, 3]
def baseStart_5597262 : Nat := 118140960795 + 5597262 * 2 ^ 59
def prefixEnd_5597262 : Nat := 4983230072969 + 3 ^ 40 * 5597262 * 2
def baseEnd_5597262 : Nat := 2874085755146184920383667

theorem tailTrace_5597262 : CollatzResearch.WordTrace tailWord_5597262 prefixEnd_5597262 2874085755146184920383667 := by
  unfold tailWord_5597262
  simp only [CollatzResearch.WordTrace]
  refine ⟨25518614581010398136092255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136099277765388790059158693 25518614581010398136092255)
  ·
    refine ⟨38277921871515597204138383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25518614581010398136092255 38277921871515597204138383)
    ·
      refine ⟨57416882807273395806207575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38277921871515597204138383 57416882807273395806207575)
      ·
        refine ⟨86125324210910093709311363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57416882807273395806207575 86125324210910093709311363)
        ·
          refine ⟨129187986316365140563967045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86125324210910093709311363 129187986316365140563967045)
          ·
            refine ⟨24222747434318463855743821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 129187986316365140563967045 24222747434318463855743821)
            ·
              refine ⟨9083530287869423945903933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24222747434318463855743821 9083530287869423945903933)
              ·
                refine ⟨3406323857951033979713975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9083530287869423945903933 3406323857951033979713975)
                ·
                  refine ⟨5109485786926550969570963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3406323857951033979713975 5109485786926550969570963)
                  ·
                    refine ⟨7664228680389826454356445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5109485786926550969570963 7664228680389826454356445)
                    ·
                      refine ⟨2874085755146184920383667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7664228680389826454356445 2874085755146184920383667)
                      ·
                        rfl

theorem cell23_5597262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 3, 1, 1, 3].length) (baseStart_5597262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5597262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5597262 prefixEnd_5597262 := by exact prefixLift 5597262
  have htrace : WordTrace (prefixWord ++ tailWord_5597262) baseStart_5597262 baseEnd_5597262 := by
    simpa [prefixWord, tailWord_5597262, baseEnd_5597262] using wordTrace_append hprefix tailTrace_5597262
  have hstable : (prefixWord ++ tailWord_5597262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5597262).length < 2 ^ (prefixWord ++ tailWord_5597262).sum := by decide
  have hdescent : baseEnd_5597262 < baseStart_5597262 := by decide
  rcases family_descends (prefixWord ++ tailWord_5597262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5597271 : List Nat := [1, 1, 3, 2, 2, 1, 3, 3, 1, 1, 5]
def baseStart_5597271 : Nat := 118140960795 + 5597271 * 2 ^ 59
def prefixEnd_5597271 : Nat := 4983230072969 + 3 ^ 40 * 5597271 * 2
def baseEnd_5597271 : Nat := 2874090376472075385171125

theorem tailTrace_5597271 : CollatzResearch.WordTrace tailWord_5597271 prefixEnd_5597271 2874090376472075385171125 := by
  unfold tailWord_5597271
  simp only [CollatzResearch.WordTrace]
  refine ⟨204149244905050579625815667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136099496603367053083877111 204149244905050579625815667)
  ·
    refine ⟨306223867357575869438723501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204149244905050579625815667 306223867357575869438723501)
    ·
      refine ⟨114833950259090951039521313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 306223867357575869438723501 114833950259090951039521313)
      ·
        refine ⟨86125462694318213279640985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114833950259090951039521313 86125462694318213279640985)
        ·
          refine ⟨64594097020738659959730739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86125462694318213279640985 64594097020738659959730739)
          ·
            refine ⟨96891145531107989939596109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64594097020738659959730739 96891145531107989939596109)
            ·
              refine ⟨36334179574165496227348541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96891145531107989939596109 36334179574165496227348541)
              ·
                refine ⟨13625317340312061085255703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36334179574165496227348541 13625317340312061085255703)
                ·
                  refine ⟨20437976010468091627883555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13625317340312061085255703 20437976010468091627883555)
                  ·
                    refine ⟨30656964015702137441825333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20437976010468091627883555 30656964015702137441825333)
                    ·
                      refine ⟨2874090376472075385171125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30656964015702137441825333 2874090376472075385171125)
                      ·
                        rfl

theorem cell23_5597271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 3, 1, 1, 5].length) (baseStart_5597271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5597271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5597271 prefixEnd_5597271 := by exact prefixLift 5597271
  have htrace : WordTrace (prefixWord ++ tailWord_5597271) baseStart_5597271 baseEnd_5597271 := by
    simpa [prefixWord, tailWord_5597271, baseEnd_5597271] using wordTrace_append hprefix tailTrace_5597271
  have hstable : (prefixWord ++ tailWord_5597271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5597271).length < 2 ^ (prefixWord ++ tailWord_5597271).sum := by decide
  have hdescent : baseEnd_5597271 < baseStart_5597271 := by decide
  rcases family_descends (prefixWord ++ tailWord_5597271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5597295 : List Nat := [1, 1, 2, 1, 3, 4, 4, 1, 2, 4]
def baseStart_5597295 : Nat := 118140960795 + 5597295 * 2 ^ 59
def prefixEnd_5597295 : Nat := 4983230072969 + 3 ^ 40 * 5597295 * 2
def baseEnd_5597295 : Nat := 958034233335927763757005

theorem tailTrace_5597295 : CollatzResearch.WordTrace tailWord_5597295 prefixEnd_5597295 958034233335927763757005 := by
  unfold tailWord_5597295
  simp only [CollatzResearch.WordTrace]
  refine ⟨204150120256963631724689339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136100080171309087816459559 204150120256963631724689339)
  ·
    refine ⟨306225180385445447587034009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204150120256963631724689339 306225180385445447587034009)
    ·
      refine ⟨229668885289084085690275507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 306225180385445447587034009 229668885289084085690275507)
      ·
        refine ⟨344503327933626128535413261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229668885289084085690275507 344503327933626128535413261)
        ·
          refine ⟨129188747975109798200779973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 344503327933626128535413261 129188747975109798200779973)
          ·
            refine ⟨24222890245333087162646245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 129188747975109798200779973 24222890245333087162646245)
            ·
              refine ⟨4541791920999953842996171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24222890245333087162646245 4541791920999953842996171)
              ·
                refine ⟨6812687881499930764494257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4541791920999953842996171 6812687881499930764494257)
                ·
                  refine ⟨5109515911124948073370693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6812687881499930764494257 5109515911124948073370693)
                  ·
                    refine ⟨958034233335927763757005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5109515911124948073370693 958034233335927763757005)
                    ·
                      rfl

theorem cell23_5597295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 4, 1, 2, 4].length) (baseStart_5597295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5597295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5597295 prefixEnd_5597295 := by exact prefixLift 5597295
  have htrace : WordTrace (prefixWord ++ tailWord_5597295) baseStart_5597295 baseEnd_5597295 := by
    simpa [prefixWord, tailWord_5597295, baseEnd_5597295] using wordTrace_append hprefix tailTrace_5597295
  have hstable : (prefixWord ++ tailWord_5597295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5597295).length < 2 ^ (prefixWord ++ tailWord_5597295).sum := by decide
  have hdescent : baseEnd_5597295 < baseStart_5597295 := by decide
  rcases family_descends (prefixWord ++ tailWord_5597295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5597302 : List Nat := [5, 1, 1, 2, 1, 4, 1, 2, 1, 1, 4]
def baseStart_5597302 : Nat := 118140960795 + 5597302 * 2 ^ 59
def prefixEnd_5597302 : Nat := 4983230072969 + 3 ^ 40 * 5597302 * 2
def baseEnd_5597302 : Nat := 2874106294372364763883483

theorem tailTrace_5597302 : CollatzResearch.WordTrace tailWord_5597302 prefixEnd_5597302 2874106294372364763883483 := by
  unfold tailWord_5597302
  simp only [CollatzResearch.WordTrace]
  refine ⟨12759398472996141995012135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 136100250378625514613462773 12759398472996141995012135)
  ·
    refine ⟨19139097709494212992518203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12759398472996141995012135 19139097709494212992518203)
    ·
      refine ⟨28708646564241319488777305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19139097709494212992518203 28708646564241319488777305)
      ·
        refine ⟨21531484923180989616582979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28708646564241319488777305 21531484923180989616582979)
        ·
          refine ⟨32297227384771484424874469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21531484923180989616582979 32297227384771484424874469)
          ·
            refine ⟨6055730134644653329663963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32297227384771484424874469 6055730134644653329663963)
            ·
              refine ⟨9083595201966979994495945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6055730134644653329663963 9083595201966979994495945)
              ·
                refine ⟨6812696401475234995871959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9083595201966979994495945 6812696401475234995871959)
                ·
                  refine ⟨10219044602212852493807939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6812696401475234995871959 10219044602212852493807939)
                  ·
                    refine ⟨15328566903319278740711909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10219044602212852493807939 15328566903319278740711909)
                    ·
                      refine ⟨2874106294372364763883483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15328566903319278740711909 2874106294372364763883483)
                      ·
                        rfl

theorem cell23_5597302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 1, 2, 1, 1, 4].length) (baseStart_5597302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5597302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5597302 prefixEnd_5597302 := by exact prefixLift 5597302
  have htrace : WordTrace (prefixWord ++ tailWord_5597302) baseStart_5597302 baseEnd_5597302 := by
    simpa [prefixWord, tailWord_5597302, baseEnd_5597302] using wordTrace_append hprefix tailTrace_5597302
  have hstable : (prefixWord ++ tailWord_5597302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5597302).length < 2 ^ (prefixWord ++ tailWord_5597302).sum := by decide
  have hdescent : baseEnd_5597302 < baseStart_5597302 := by decide
  rcases family_descends (prefixWord ++ tailWord_5597302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5597305 : List Nat := [1, 2, 1, 3, 4, 1, 3, 2, 1, 2, 3]
def baseStart_5597305 : Nat := 118140960795 + 5597305 * 2 ^ 59
def prefixEnd_5597305 : Nat := 4983230072969 + 3 ^ 40 * 5597305 * 2
def baseEnd_5597305 : Nat := 2874107834814328252145969

theorem tailTrace_5597305 : CollatzResearch.WordTrace tailWord_5597305 prefixEnd_5597305 2874107834814328252145969 := by
  unfold tailWord_5597305
  simp only [CollatzResearch.WordTrace]
  refine ⟨204150484986927403432553369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136100323324618268955035579 204150484986927403432553369)
  ·
    refine ⟨153112863740195552574415027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204150484986927403432553369 153112863740195552574415027)
    ·
      refine ⟨229669295610293328861622541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153112863740195552574415027 229669295610293328861622541)
      ·
        refine ⟨86125985853859998323108453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 229669295610293328861622541 86125985853859998323108453)
        ·
          refine ⟨16148622347598749685582835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 86125985853859998323108453 16148622347598749685582835)
          ·
            refine ⟨24222933521398124528374253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16148622347598749685582835 24222933521398124528374253)
            ·
              refine ⟨9083600070524296698140345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24222933521398124528374253 9083600070524296698140345)
              ·
                refine ⟨6812700052893222523605259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9083600070524296698140345 6812700052893222523605259)
                ·
                  refine ⟨10219050079339833785407889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6812700052893222523605259 10219050079339833785407889)
                  ·
                    refine ⟨7664287559504875339055917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10219050079339833785407889 7664287559504875339055917)
                    ·
                      refine ⟨2874107834814328252145969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7664287559504875339055917 2874107834814328252145969)
                      ·
                        rfl

theorem cell23_5597305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3, 2, 1, 2, 3].length) (baseStart_5597305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5597305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5597305 prefixEnd_5597305 := by exact prefixLift 5597305
  have htrace : WordTrace (prefixWord ++ tailWord_5597305) baseStart_5597305 baseEnd_5597305 := by
    simpa [prefixWord, tailWord_5597305, baseEnd_5597305] using wordTrace_append hprefix tailTrace_5597305
  have hstable : (prefixWord ++ tailWord_5597305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5597305).length < 2 ^ (prefixWord ++ tailWord_5597305).sum := by decide
  have hdescent : baseEnd_5597305 < baseStart_5597305 := by decide
  rcases family_descends (prefixWord ++ tailWord_5597305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5597322 : List Nat := [3, 1, 2, 3, 1, 3, 3, 1, 1, 2, 3]
def baseStart_5597322 : Nat := 118140960795 + 5597322 * 2 ^ 59
def prefixEnd_5597322 : Nat := 4983230072969 + 3 ^ 40 * 5597322 * 2
def baseEnd_5597322 : Nat := 2874116563985454685633391

theorem tailTrace_5597322 : CollatzResearch.WordTrace tailWord_5597322 prefixEnd_5597322 2874116563985454685633391 := by
  unfold tailWord_5597322
  simp only [CollatzResearch.WordTrace]
  refine ⟨51037776256966453833980555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136100736685243876890614813 51037776256966453833980555)
  ·
    refine ⟨76556664385449680750970833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51037776256966453833980555 76556664385449680750970833)
    ·
      refine ⟨57417498289087260563228125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76556664385449680750970833 57417498289087260563228125)
      ·
        refine ⟨21531561858407722711210547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57417498289087260563228125 21531561858407722711210547)
        ·
          refine ⟨32297342787611584066815821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21531561858407722711210547 32297342787611584066815821)
          ·
            refine ⟨12111503545354344025055933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32297342787611584066815821 12111503545354344025055933)
            ·
              refine ⟨4541813829507879009395975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12111503545354344025055933 4541813829507879009395975)
              ·
                refine ⟨6812720744261818514093963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4541813829507879009395975 6812720744261818514093963)
                ·
                  refine ⟨10219081116392727771140945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6812720744261818514093963 10219081116392727771140945)
                  ·
                    refine ⟨7664310837294545828355709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10219081116392727771140945 7664310837294545828355709)
                    ·
                      refine ⟨2874116563985454685633391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7664310837294545828355709 2874116563985454685633391)
                      ·
                        rfl

theorem cell23_5597322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 3, 1, 1, 2, 3].length) (baseStart_5597322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5597322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5597322 prefixEnd_5597322 := by exact prefixLift 5597322
  have htrace : WordTrace (prefixWord ++ tailWord_5597322) baseStart_5597322 baseEnd_5597322 := by
    simpa [prefixWord, tailWord_5597322, baseEnd_5597322] using wordTrace_append hprefix tailTrace_5597322
  have hstable : (prefixWord ++ tailWord_5597322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5597322).length < 2 ^ (prefixWord ++ tailWord_5597322).sum := by decide
  have hdescent : baseEnd_5597322 < baseStart_5597322 := by decide
  rcases family_descends (prefixWord ++ tailWord_5597322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5597342 : List Nat := [4, 3, 1, 1, 4, 1, 1, 8]
def baseStart_5597342 : Nat := 118140960795 + 5597342 * 2 ^ 59
def prefixEnd_5597342 : Nat := 4983230072969 + 3 ^ 40 * 5597342 * 2
def baseEnd_5597342 : Nat := 106449141985131281754937

theorem tailTrace_5597342 : CollatzResearch.WordTrace tailWord_5597342 prefixEnd_5597342 106449141985131281754937 := by
  unfold tailWord_5597342
  simp only [CollatzResearch.WordTrace]
  refine ⟨25518979310974169843956285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136101222991862239167766853 25518979310974169843956285)
  ·
    refine ⟨9569617241615313691483607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25518979310974169843956285 9569617241615313691483607)
    ·
      refine ⟨14354425862422970537225411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9569617241615313691483607 14354425862422970537225411)
      ·
        refine ⟨21531638793634455805838117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14354425862422970537225411 21531638793634455805838117)
        ·
          refine ⟨4037182273806460463594647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21531638793634455805838117 4037182273806460463594647)
          ·
            refine ⟨6055773410709690695391971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4037182273806460463594647 6055773410709690695391971)
            ·
              refine ⟨9083660116064536043087957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6055773410709690695391971 9083660116064536043087957)
              ·
                refine ⟨106449141985131281754937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9083660116064536043087957 106449141985131281754937)
                ·
                  rfl

theorem cell23_5597342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 1, 8].length) (baseStart_5597342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5597342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5597342 prefixEnd_5597342 := by exact prefixLift 5597342
  have htrace : WordTrace (prefixWord ++ tailWord_5597342) baseStart_5597342 baseEnd_5597342 := by
    simpa [prefixWord, tailWord_5597342, baseEnd_5597342] using wordTrace_append hprefix tailTrace_5597342
  have hstable : (prefixWord ++ tailWord_5597342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5597342).length < 2 ^ (prefixWord ++ tailWord_5597342).sum := by decide
  have hdescent : baseEnd_5597342 < baseStart_5597342 := by decide
  rcases family_descends (prefixWord ++ tailWord_5597342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5597345 : List Nat := [1, 2, 3, 3, 1, 2, 1, 2, 3, 3, 2]
def baseStart_5597345 : Nat := 118140960795 + 5597345 * 2 ^ 59
def prefixEnd_5597345 : Nat := 4983230072969 + 3 ^ 40 * 5597345 * 2
def baseEnd_5597345 : Nat := 2874128374040508095645785

theorem tailTrace_5597345 : CollatzResearch.WordTrace tailWord_5597345 prefixEnd_5597345 2874128374040508095645785 := by
  unfold tailWord_5597345
  simp only [CollatzResearch.WordTrace]
  refine ⟨204151943906782490264009489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136101295937854993509339659 204151943906782490264009489)
  ·
    refine ⟨153113957930086867698007117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204151943906782490264009489 153113957930086867698007117)
    ·
      refine ⟨57417734223782575386752669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 153113957930086867698007117 57417734223782575386752669)
      ·
        refine ⟨21531650333918465770032251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57417734223782575386752669 21531650333918465770032251)
        ·
          refine ⟨32297475500877698655048377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21531650333918465770032251 32297475500877698655048377)
          ·
            refine ⟨24223106625658273991286283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32297475500877698655048377 24223106625658273991286283)
            ·
              refine ⟨36334659938487410986929425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24223106625658273991286283 36334659938487410986929425)
              ·
                refine ⟨27250994953865558240197069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36334659938487410986929425 27250994953865558240197069)
                ·
                  refine ⟨10219123107699584340073901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27250994953865558240197069 10219123107699584340073901)
                  ·
                    refine ⟨3832171165387344127527713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10219123107699584340073901 3832171165387344127527713)
                    ·
                      refine ⟨2874128374040508095645785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3832171165387344127527713 2874128374040508095645785)
                      ·
                        rfl

theorem cell23_5597345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 2, 3, 3, 2].length) (baseStart_5597345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5597345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5597345 prefixEnd_5597345 := by exact prefixLift 5597345
  have htrace : WordTrace (prefixWord ++ tailWord_5597345) baseStart_5597345 baseEnd_5597345 := by
    simpa [prefixWord, tailWord_5597345, baseEnd_5597345] using wordTrace_append hprefix tailTrace_5597345
  have hstable : (prefixWord ++ tailWord_5597345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5597345).length < 2 ^ (prefixWord ++ tailWord_5597345).sum := by decide
  have hdescent : baseEnd_5597345 < baseStart_5597345 := by decide
  rcases family_descends (prefixWord ++ tailWord_5597345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5597371 : List Nat := [1, 1, 1, 1, 1, 2, 5, 2, 1, 4, 4]
def baseStart_5597371 : Nat := 118140960795 + 5597371 * 2 ^ 59
def prefixEnd_5597371 : Nat := 4983230072969 + 3 ^ 40 * 5597371 * 2
def baseEnd_5597371 : Nat := 2874141724537524993920665

theorem tailTrace_5597371 : CollatzResearch.WordTrace tailWord_5597371 prefixEnd_5597371 2874141724537524993920665 := by
  unfold tailWord_5597371
  simp only [CollatzResearch.WordTrace]
  refine ⟨204152892204688296704455967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136101928136458864469637311 204152892204688296704455967)
  ·
    refine ⟨306229338307032445056683951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204152892204688296704455967 306229338307032445056683951)
    ·
      refine ⟨459344007460548667585025927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 306229338307032445056683951 459344007460548667585025927)
      ·
        refine ⟨689016011190823001377538891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 459344007460548667585025927 689016011190823001377538891)
        ·
          refine ⟨1033524016786234502066308337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 689016011190823001377538891 1033524016786234502066308337)
          ·
            refine ⟨775143012589675876549731253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1033524016786234502066308337 775143012589675876549731253)
            ·
              refine ⟨72669657430282113426537305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 775143012589675876549731253 72669657430282113426537305)
              ·
                refine ⟨54502243072711585069902979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72669657430282113426537305 54502243072711585069902979)
                ·
                  refine ⟨81753364609067377604854469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54502243072711585069902979 81753364609067377604854469)
                  ·
                    refine ⟨15328755864200133300910213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 81753364609067377604854469 15328755864200133300910213)
                    ·
                      refine ⟨2874141724537524993920665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15328755864200133300910213 2874141724537524993920665)
                      ·
                        rfl

theorem cell23_5597371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 2, 1, 4, 4].length) (baseStart_5597371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5597371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5597371 prefixEnd_5597371 := by exact prefixLift 5597371
  have htrace : WordTrace (prefixWord ++ tailWord_5597371) baseStart_5597371 baseEnd_5597371 := by
    simpa [prefixWord, tailWord_5597371, baseEnd_5597371] using wordTrace_append hprefix tailTrace_5597371
  have hstable : (prefixWord ++ tailWord_5597371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5597371).length < 2 ^ (prefixWord ++ tailWord_5597371).sum := by decide
  have hdescent : baseEnd_5597371 < baseStart_5597371 := by decide
  rcases family_descends (prefixWord ++ tailWord_5597371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5597375 : List Nat := [1, 1, 2, 2, 2, 2, 1, 4, 4, 2, 2]
def baseStart_5597375 : Nat := 118140960795 + 5597375 * 2 ^ 59
def prefixEnd_5597375 : Nat := 4983230072969 + 3 ^ 40 * 5597375 * 2
def baseEnd_5597375 : Nat := 2874143778460142978270647

theorem tailTrace_5597375 : CollatzResearch.WordTrace tailWord_5597375 prefixEnd_5597375 2874143778460142978270647 := by
  unfold tailWord_5597375
  simp only [CollatzResearch.WordTrace]
  refine ⟨204153038096673805387601579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136102025397782536925067719 204153038096673805387601579)
  ·
    refine ⟨306229557145010708081402369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204153038096673805387601579 306229557145010708081402369)
    ·
      refine ⟨229672167858758031061051777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 306229557145010708081402369 229672167858758031061051777)
      ·
        refine ⟨172254125894068523295788833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 229672167858758031061051777 172254125894068523295788833)
        ·
          refine ⟨129190594420551392471841625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172254125894068523295788833 129190594420551392471841625)
          ·
            refine ⟨96892945815413544353881219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129190594420551392471841625 96892945815413544353881219)
            ·
              refine ⟨145339418723120316530821829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96892945815413544353881219 145339418723120316530821829)
              ·
                refine ⟨27251141010585059349529093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 145339418723120316530821829 27251141010585059349529093)
                ·
                  refine ⟨5109588939484698628036705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27251141010585059349529093 5109588939484698628036705)
                  ·
                    refine ⟨3832191704613523971027529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5109588939484698628036705 3832191704613523971027529)
                    ·
                      refine ⟨2874143778460142978270647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3832191704613523971027529 2874143778460142978270647)
                      ·
                        rfl

theorem cell23_5597375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 4, 4, 2, 2].length) (baseStart_5597375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5597375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5597375 prefixEnd_5597375 := by exact prefixLift 5597375
  have htrace : WordTrace (prefixWord ++ tailWord_5597375) baseStart_5597375 baseEnd_5597375 := by
    simpa [prefixWord, tailWord_5597375, baseEnd_5597375] using wordTrace_append hprefix tailTrace_5597375
  have hstable : (prefixWord ++ tailWord_5597375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5597375).length < 2 ^ (prefixWord ++ tailWord_5597375).sum := by decide
  have hdescent : baseEnd_5597375 < baseStart_5597375 := by decide
  rcases family_descends (prefixWord ++ tailWord_5597375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5597405 : List Nat := [1, 4, 3, 2, 1, 1, 2, 1, 2, 2, 4]
def baseStart_5597405 : Nat := 118140960795 + 5597405 * 2 ^ 59
def prefixEnd_5597405 : Nat := 4983230072969 + 3 ^ 40 * 5597405 * 2
def baseEnd_5597405 : Nat := 2874159182879777860895509

theorem tailTrace_5597405 : CollatzResearch.WordTrace tailWord_5597405 prefixEnd_5597405 2874159182879777860895509 := by
  unfold tailWord_5597405
  simp only [CollatzResearch.WordTrace]
  refine ⟨204154132286565120511193669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136102754857710080340795779 204154132286565120511193669)
  ·
    refine ⟨38278899803730960095848813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 204154132286565120511193669 38278899803730960095848813)
    ·
      refine ⟨14354587426399110035943305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38278899803730960095848813 14354587426399110035943305)
      ·
        refine ⟨10765940569799332526957479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14354587426399110035943305 10765940569799332526957479)
        ·
          refine ⟨16148910854698998790436219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10765940569799332526957479 16148910854698998790436219)
          ·
            refine ⟨24223366282048498185654329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16148910854698998790436219 24223366282048498185654329)
            ·
              refine ⟨18167524711536373639240747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24223366282048498185654329 18167524711536373639240747)
              ·
                refine ⟨27251287067304560458861121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18167524711536373639240747 27251287067304560458861121)
                ·
                  refine ⟨20438465300478420344145841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27251287067304560458861121 20438465300478420344145841)
                  ·
                    refine ⟨15328848975358815258109381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20438465300478420344145841 15328848975358815258109381)
                    ·
                      refine ⟨2874159182879777860895509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15328848975358815258109381 2874159182879777860895509)
                      ·
                        rfl

theorem cell23_5597405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_5597405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5597405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5597405 prefixEnd_5597405 := by exact prefixLift 5597405
  have htrace : WordTrace (prefixWord ++ tailWord_5597405) baseStart_5597405 baseEnd_5597405 := by
    simpa [prefixWord, tailWord_5597405, baseEnd_5597405] using wordTrace_append hprefix tailTrace_5597405
  have hstable : (prefixWord ++ tailWord_5597405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5597405).length < 2 ^ (prefixWord ++ tailWord_5597405).sum := by decide
  have hdescent : baseEnd_5597405 < baseStart_5597405 := by decide
  rcases family_descends (prefixWord ++ tailWord_5597405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5597408 : List Nat := [2, 1, 1, 3, 1, 3, 1, 3, 2, 3, 3]
def baseStart_5597408 : Nat := 118140960795 + 5597408 * 2 ^ 59
def prefixEnd_5597408 : Nat := 4983230072969 + 3 ^ 40 * 5597408 * 2
def baseEnd_5597408 : Nat := 2874160723321741349157995

theorem tailTrace_5597408 : CollatzResearch.WordTrace tailWord_5597408 prefixEnd_5597408 2874160723321741349157995 := by
  unfold tailWord_5597408
  simp only [CollatzResearch.WordTrace]
  refine ⟨102077120852777126011776439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136102827803702834682368585 102077120852777126011776439)
  ·
    refine ⟨153115681279165689017664659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102077120852777126011776439 153115681279165689017664659)
    ·
      refine ⟨229673521918748533526496989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153115681279165689017664659 229673521918748533526496989)
      ·
        refine ⟨86127570719530700072436371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 229673521918748533526496989 86127570719530700072436371)
        ·
          refine ⟨129191356079296050108654557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86127570719530700072436371 129191356079296050108654557)
          ·
            refine ⟨48446758529736018790745459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 129191356079296050108654557 48446758529736018790745459)
            ·
              refine ⟨72670137794604028186118189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48446758529736018790745459 72670137794604028186118189)
              ·
                refine ⟨27251301672976510569794321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72670137794604028186118189 27251301672976510569794321)
                ·
                  refine ⟨20438476254732382927345741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27251301672976510569794321 20438476254732382927345741)
                  ·
                    refine ⟨7664428595524643597754653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20438476254732382927345741 7664428595524643597754653)
                    ·
                      refine ⟨2874160723321741349157995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7664428595524643597754653 2874160723321741349157995)
                      ·
                        rfl

theorem cell23_5597408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 3, 2, 3, 3].length) (baseStart_5597408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5597408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5597408 prefixEnd_5597408 := by exact prefixLift 5597408
  have htrace : WordTrace (prefixWord ++ tailWord_5597408) baseStart_5597408 baseEnd_5597408 := by
    simpa [prefixWord, tailWord_5597408, baseEnd_5597408] using wordTrace_append hprefix tailTrace_5597408
  have hstable : (prefixWord ++ tailWord_5597408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5597408).length < 2 ^ (prefixWord ++ tailWord_5597408).sum := by decide
  have hdescent : baseEnd_5597408 < baseStart_5597408 := by decide
  rcases family_descends (prefixWord ++ tailWord_5597408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5597409 : List Nat := [1, 2, 3, 1, 3, 1, 5, 1, 2, 2, 2]
def baseStart_5597409 : Nat := 118140960795 + 5597409 * 2 ^ 59
def prefixEnd_5597409 : Nat := 4983230072969 + 3 ^ 40 * 5597409 * 2
def baseEnd_5597409 : Nat := 2874161236802395845245491

theorem tailTrace_5597409 : CollatzResearch.WordTrace tailWord_5597409 prefixEnd_5597409 2874161236802395845245491 := by
  unfold tailWord_5597409
  simp only [CollatzResearch.WordTrace]
  refine ⟨204154278178550629194339281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136102852119033752796226187 204154278178550629194339281)
  ·
    refine ⟨153115708633912971895754461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204154278178550629194339281 153115708633912971895754461)
    ·
      refine ⟨57418390737717364460907923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 153115708633912971895754461 57418390737717364460907923)
      ·
        refine ⟨86127586106576046691361885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57418390737717364460907923 86127586106576046691361885)
        ·
          refine ⟨32297844789966017509260707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86127586106576046691361885 32297844789966017509260707)
          ·
            refine ⟨48446767184949026263891061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32297844789966017509260707 48446767184949026263891061)
            ·
              refine ⟨4541884423588971212239787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48446767184949026263891061 4541884423588971212239787)
              ·
                refine ⟨6812826635383456818359681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4541884423588971212239787 6812826635383456818359681)
                ·
                  refine ⟨5109619976537592613769761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6812826635383456818359681 5109619976537592613769761)
                  ·
                    refine ⟨3832214982403194460327321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5109619976537592613769761 3832214982403194460327321)
                    ·
                      refine ⟨2874161236802395845245491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3832214982403194460327321 2874161236802395845245491)
                      ·
                        rfl

theorem cell23_5597409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 5, 1, 2, 2, 2].length) (baseStart_5597409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5597409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5597409 prefixEnd_5597409 := by exact prefixLift 5597409
  have htrace : WordTrace (prefixWord ++ tailWord_5597409) baseStart_5597409 baseEnd_5597409 := by
    simpa [prefixWord, tailWord_5597409, baseEnd_5597409] using wordTrace_append hprefix tailTrace_5597409
  have hstable : (prefixWord ++ tailWord_5597409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5597409).length < 2 ^ (prefixWord ++ tailWord_5597409).sum := by decide
  have hdescent : baseEnd_5597409 < baseStart_5597409 := by decide
  rcases family_descends (prefixWord ++ tailWord_5597409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5597502 : List Nat := [4, 2, 1, 2, 1, 2, 2, 2, 2, 2, 3]
def baseStart_5597502 : Nat := 118140960795 + 5597502 * 2 ^ 59
def prefixEnd_5597502 : Nat := 4983230072969 + 3 ^ 40 * 5597502 * 2
def baseEnd_5597502 : Nat := 2874208990503263981382563

theorem tailTrace_5597502 : CollatzResearch.WordTrace tailWord_5597502 prefixEnd_5597502 2874208990503263981382563 := by
  unfold tailWord_5597502
  simp only [CollatzResearch.WordTrace]
  refine ⟨25519708770901713259684345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136105113444809137384983173 25519708770901713259684345)
  ·
    refine ⟨19139781578176284944763259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25519708770901713259684345 19139781578176284944763259)
    ·
      refine ⟨28709672367264427417144889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19139781578176284944763259 28709672367264427417144889)
      ·
        refine ⟨21532254275448320562858667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28709672367264427417144889 21532254275448320562858667)
        ·
          refine ⟨32298381413172480844288001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21532254275448320562858667 32298381413172480844288001)
          ·
            refine ⟨24223786059879360633216001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32298381413172480844288001 24223786059879360633216001)
            ·
              refine ⟨18167839544909520474912001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24223786059879360633216001 18167839544909520474912001)
              ·
                refine ⟨13625879658682140356184001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18167839544909520474912001 13625879658682140356184001)
                ·
                  refine ⟨10219409744011605267138001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13625879658682140356184001 10219409744011605267138001)
                  ·
                    refine ⟨7664557308008703950353501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10219409744011605267138001 7664557308008703950353501)
                    ·
                      refine ⟨2874208990503263981382563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7664557308008703950353501 2874208990503263981382563)
                      ·
                        rfl

theorem cell23_5597502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 2, 2, 2, 3].length) (baseStart_5597502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5597502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5597502 prefixEnd_5597502 := by exact prefixLift 5597502
  have htrace : WordTrace (prefixWord ++ tailWord_5597502) baseStart_5597502 baseEnd_5597502 := by
    simpa [prefixWord, tailWord_5597502, baseEnd_5597502] using wordTrace_append hprefix tailTrace_5597502
  have hstable : (prefixWord ++ tailWord_5597502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5597502).length < 2 ^ (prefixWord ++ tailWord_5597502).sum := by decide
  have hdescent : baseEnd_5597502 < baseStart_5597502 := by decide
  rcases family_descends (prefixWord ++ tailWord_5597502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5597552 : List Nat := [2, 1, 1, 1, 4, 3, 4, 1, 1, 5]
def baseStart_5597552 : Nat := 118140960795 + 5597552 * 2 ^ 59
def prefixEnd_5597552 : Nat := 4983230072969 + 3 ^ 40 * 5597552 * 2
def baseEnd_5597552 : Nat := 958078221511996261919111

theorem tailTrace_5597552 : CollatzResearch.WordTrace tailWord_5597552 prefixEnd_5597552 958078221511996261919111 := by
  unfold tailWord_5597552
  simp only [CollatzResearch.WordTrace]
  refine ⟨102079746908516282308397455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136106329211355043077863273 102079746908516282308397455)
  ·
    refine ⟨153119620362774423462596183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102079746908516282308397455 153119620362774423462596183)
    ·
      refine ⟨229679430544161635193894275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153119620362774423462596183 229679430544161635193894275)
      ·
        refine ⟨344519145816242452790841413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229679430544161635193894275 344519145816242452790841413)
        ·
          refine ⟨64597339840545459898282765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 344519145816242452790841413 64597339840545459898282765)
          ·
            refine ⟨24224002440204547461856037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64597339840545459898282765 24224002440204547461856037)
            ·
              refine ⟨4542000457538352649098007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24224002440204547461856037 4542000457538352649098007)
              ·
                refine ⟨6813000686307528973647011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4542000457538352649098007 6813000686307528973647011)
                ·
                  refine ⟨10219501029461293460470517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6813000686307528973647011 10219501029461293460470517)
                  ·
                    refine ⟨958078221511996261919111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10219501029461293460470517 958078221511996261919111)
                    ·
                      rfl

theorem cell23_5597552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 4, 1, 1, 5].length) (baseStart_5597552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5597552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5597552 prefixEnd_5597552 := by exact prefixLift 5597552
  have htrace : WordTrace (prefixWord ++ tailWord_5597552) baseStart_5597552 baseEnd_5597552 := by
    simpa [prefixWord, tailWord_5597552, baseEnd_5597552] using wordTrace_append hprefix tailTrace_5597552
  have hstable : (prefixWord ++ tailWord_5597552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5597552).length < 2 ^ (prefixWord ++ tailWord_5597552).sum := by decide
  have hdescent : baseEnd_5597552 < baseStart_5597552 := by decide
  rcases family_descends (prefixWord ++ tailWord_5597552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5597555 : List Nat := [1, 1, 1, 2, 2, 1, 2, 7, 1, 1, 4]
def baseStart_5597555 : Nat := 118140960795 + 5597555 * 2 ^ 59
def prefixEnd_5597555 : Nat := 4983230072969 + 3 ^ 40 * 5597555 * 2
def baseEnd_5597555 : Nat := 2874236204977952274019819

theorem tailTrace_5597555 : CollatzResearch.WordTrace tailWord_5597555 prefixEnd_5597555 2874236204977952274019819 := by
  unfold tailWord_5597555
  simp only [CollatzResearch.WordTrace]
  refine ⟨204159603236021696129154119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136106402157347797419436079 204159603236021696129154119)
  ·
    refine ⟨306239404854032544193731179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204159603236021696129154119 306239404854032544193731179)
    ·
      refine ⟨459359107281048816290596769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 306239404854032544193731179 459359107281048816290596769)
      ·
        refine ⟨344519330460786612217947577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 459359107281048816290596769 344519330460786612217947577)
        ·
          refine ⟨258389497845589959163460683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 344519330460786612217947577 258389497845589959163460683)
          ·
            refine ⟨387584246768384938745191025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 258389497845589959163460683 387584246768384938745191025)
            ·
              refine ⟨290688185076288704058893269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 387584246768384938745191025 290688185076288704058893269)
              ·
                refine ⟨6813004337725516501380311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 290688185076288704058893269 6813004337725516501380311)
                ·
                  refine ⟨10219506506588274752070467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6813004337725516501380311 10219506506588274752070467)
                  ·
                    refine ⟨15329259759882412128105701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10219506506588274752070467 15329259759882412128105701)
                    ·
                      refine ⟨2874236204977952274019819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15329259759882412128105701 2874236204977952274019819)
                      ·
                        rfl

theorem cell23_5597555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 7, 1, 1, 4].length) (baseStart_5597555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5597555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5597555 prefixEnd_5597555 := by exact prefixLift 5597555
  have htrace : WordTrace (prefixWord ++ tailWord_5597555) baseStart_5597555 baseEnd_5597555 := by
    simpa [prefixWord, tailWord_5597555, baseEnd_5597555] using wordTrace_append hprefix tailTrace_5597555
  have hstable : (prefixWord ++ tailWord_5597555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5597555).length < 2 ^ (prefixWord ++ tailWord_5597555).sum := by decide
  have hdescent : baseEnd_5597555 < baseStart_5597555 := by decide
  rcases family_descends (prefixWord ++ tailWord_5597555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5597568 : List Nat := [2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 4]
def baseStart_5597568 : Nat := 118140960795 + 5597568 * 2 ^ 59
def prefixEnd_5597568 : Nat := 4983230072969 + 3 ^ 40 * 5597568 * 2
def baseEnd_5597568 : Nat := 2874242880226460723157259

theorem tailTrace_5597568 : CollatzResearch.WordTrace tailWord_5597568 prefixEnd_5597568 2874242880226460723157259 := by
  unfold tailWord_5597568
  simp only [CollatzResearch.WordTrace]
  refine ⟨102080038692487299674688679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136106718256649732899584905 102080038692487299674688679)
  ·
    refine ⟨153120058038730949512033019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102080038692487299674688679 153120058038730949512033019)
    ·
      refine ⟨229680087058096424268049529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153120058038730949512033019 229680087058096424268049529)
      ·
        refine ⟨172260065293572318201037147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 229680087058096424268049529 172260065293572318201037147)
        ·
          refine ⟨258390097940358477301555721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172260065293572318201037147 258390097940358477301555721)
          ·
            refine ⟨193792573455268857976166791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 258390097940358477301555721 193792573455268857976166791)
            ·
              refine ⟨290688860182903286964250187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 193792573455268857976166791 290688860182903286964250187)
              ·
                refine ⟨436033290274354930446375281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 290688860182903286964250187 436033290274354930446375281)
                ·
                  refine ⟨327024967705766197834781461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 436033290274354930446375281 327024967705766197834781461)
                  ·
                    refine ⟨15329295361207790523505381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 327024967705766197834781461 15329295361207790523505381)
                    ·
                      refine ⟨2874242880226460723157259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15329295361207790523505381 2874242880226460723157259)
                      ·
                        rfl

theorem cell23_5597568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 4].length) (baseStart_5597568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5597568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5597568 prefixEnd_5597568 := by exact prefixLift 5597568
  have htrace : WordTrace (prefixWord ++ tailWord_5597568) baseStart_5597568 baseEnd_5597568 := by
    simpa [prefixWord, tailWord_5597568, baseEnd_5597568] using wordTrace_append hprefix tailTrace_5597568
  have hstable : (prefixWord ++ tailWord_5597568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5597568).length < 2 ^ (prefixWord ++ tailWord_5597568).sum := by decide
  have hdescent : baseEnd_5597568 < baseStart_5597568 := by decide
  rcases family_descends (prefixWord ++ tailWord_5597568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5597575 : List Nat := [1, 1, 4, 2, 2, 1, 3, 2, 1, 1, 5]
def baseStart_5597575 : Nat := 118140960795 + 5597575 * 2 ^ 59
def prefixEnd_5597575 : Nat := 4983230072969 + 3 ^ 40 * 5597575 * 2
def baseEnd_5597575 : Nat := 2874246474591042195769727

theorem tailTrace_5597575 : CollatzResearch.WordTrace tailWord_5597575 prefixEnd_5597575 2874246474591042195769727 := by
  unfold tailWord_5597575
  simp only [CollatzResearch.WordTrace]
  refine ⟨204160332695949239544882179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136106888463966159696588119 204160332695949239544882179)
  ·
    refine ⟨306240499043923859317323269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204160332695949239544882179 306240499043923859317323269)
    ·
      refine ⟨57420093570735723621998113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 306240499043923859317323269 57420093570735723621998113)
      ·
        refine ⟨43065070178051792716498585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57420093570735723621998113 43065070178051792716498585)
        ·
          refine ⟨32298802633538844537373939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43065070178051792716498585 32298802633538844537373939)
          ·
            refine ⟨48448203950308266806060909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32298802633538844537373939 48448203950308266806060909)
            ·
              refine ⟨18168076481365600052272841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48448203950308266806060909 18168076481365600052272841)
              ·
                refine ⟨13626057361024200039204631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18168076481365600052272841 13626057361024200039204631)
                ·
                  refine ⟨20439086041536300058806947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13626057361024200039204631 20439086041536300058806947)
                  ·
                    refine ⟨30658629062304450088210421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20439086041536300058806947 30658629062304450088210421)
                    ·
                      refine ⟨2874246474591042195769727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30658629062304450088210421 2874246474591042195769727)
                      ·
                        rfl

theorem cell23_5597575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 2, 1, 1, 5].length) (baseStart_5597575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5597575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5597575 prefixEnd_5597575 := by exact prefixLift 5597575
  have htrace : WordTrace (prefixWord ++ tailWord_5597575) baseStart_5597575 baseEnd_5597575 := by
    simpa [prefixWord, tailWord_5597575, baseEnd_5597575] using wordTrace_append hprefix tailTrace_5597575
  have hstable : (prefixWord ++ tailWord_5597575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5597575).length < 2 ^ (prefixWord ++ tailWord_5597575).sum := by decide
  have hdescent : baseEnd_5597575 < baseStart_5597575 := by decide
  rcases family_descends (prefixWord ++ tailWord_5597575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5597582 : List Nat := [4, 1, 1, 4, 1, 1, 3, 1, 1, 6]
def baseStart_5597582 : Nat := 118140960795 + 5597582 * 2 ^ 59
def prefixEnd_5597582 : Nat := 4983230072969 + 3 ^ 40 * 5597582 * 2
def baseEnd_5597582 : Nat := 958083356318541222794065

theorem tailTrace_5597582 : CollatzResearch.WordTrace tailWord_5597582 prefixEnd_5597582 958083356318541222794065 := by
  unfold tailWord_5597582
  simp only [CollatzResearch.WordTrace]
  refine ⟨25520073500865484967548375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136107058671282586493591333 25520073500865484967548375)
  ·
    refine ⟨38280110251298227451322563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25520073500865484967548375 38280110251298227451322563)
    ·
      refine ⟨57420165376947341176983845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38280110251298227451322563 57420165376947341176983845)
      ·
        refine ⟨10766281008177626470684471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57420165376947341176983845 10766281008177626470684471)
        ·
          refine ⟨16149421512266439706026707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10766281008177626470684471 16149421512266439706026707)
          ·
            refine ⟨24224132268399659559040061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16149421512266439706026707 24224132268399659559040061)
            ·
              refine ⟨9084049600649872334640023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24224132268399659559040061 9084049600649872334640023)
              ·
                refine ⟨13626074400974808501960035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9084049600649872334640023 13626074400974808501960035)
                ·
                  refine ⟨20439111601462212752940053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13626074400974808501960035 20439111601462212752940053)
                  ·
                    refine ⟨958083356318541222794065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20439111601462212752940053 958083356318541222794065)
                    ·
                      rfl

theorem cell23_5597582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3, 1, 1, 6].length) (baseStart_5597582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5597582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5597582 prefixEnd_5597582 := by exact prefixLift 5597582
  have htrace : WordTrace (prefixWord ++ tailWord_5597582) baseStart_5597582 baseEnd_5597582 := by
    simpa [prefixWord, tailWord_5597582, baseEnd_5597582] using wordTrace_append hprefix tailTrace_5597582
  have hstable : (prefixWord ++ tailWord_5597582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5597582).length < 2 ^ (prefixWord ++ tailWord_5597582).sum := by decide
  have hdescent : baseEnd_5597582 < baseStart_5597582 := by decide
  rcases family_descends (prefixWord ++ tailWord_5597582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5597605 : List Nat := [1, 3, 1, 2, 1, 1, 4, 1, 3, 3, 3]
def baseStart_5597605 : Nat := 118140960795 + 5597605 * 2 ^ 59
def prefixEnd_5597605 : Nat := 4983230072969 + 3 ^ 40 * 5597605 * 2
def baseEnd_5597605 : Nat := 2874261879010677078394589

theorem tailTrace_5597605 : CollatzResearch.WordTrace tailWord_5597605 prefixEnd_5597605 2874261879010677078394589 := by
  unfold tailWord_5597605
  simp only [CollatzResearch.WordTrace]
  refine ⟨204161426885840554668474269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136107617923893703112316179 204161426885840554668474269)
  ·
    refine ⟨76560535082190208000677851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 204161426885840554668474269 76560535082190208000677851)
    ·
      refine ⟨114840802623285312001016777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76560535082190208000677851 114840802623285312001016777)
      ·
        refine ⟨86130601967463984000762583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114840802623285312001016777 86130601967463984000762583)
        ·
          refine ⟨129195902951195976001143875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86130601967463984000762583 129195902951195976001143875)
          ·
            refine ⟨193793854426793964001715813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129195902951195976001143875 193793854426793964001715813)
            ·
              refine ⟨36336347705023868250321715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 193793854426793964001715813 36336347705023868250321715)
              ·
                refine ⟨54504521557535802375482573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36336347705023868250321715 54504521557535802375482573)
                ·
                  refine ⟨20439195584075925890805965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54504521557535802375482573 20439195584075925890805965)
                  ·
                    refine ⟨7664698344028472209052237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20439195584075925890805965 7664698344028472209052237)
                    ·
                      refine ⟨2874261879010677078394589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7664698344028472209052237 2874261879010677078394589)
                      ·
                        rfl

theorem cell23_5597605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 1, 3, 3, 3].length) (baseStart_5597605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5597605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5597605 prefixEnd_5597605 := by exact prefixLift 5597605
  have htrace : WordTrace (prefixWord ++ tailWord_5597605) baseStart_5597605 baseEnd_5597605 := by
    simpa [prefixWord, tailWord_5597605, baseEnd_5597605] using wordTrace_append hprefix tailTrace_5597605
  have hstable : (prefixWord ++ tailWord_5597605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5597605).length < 2 ^ (prefixWord ++ tailWord_5597605).sum := by decide
  have hdescent : baseEnd_5597605 < baseStart_5597605 := by decide
  rcases family_descends (prefixWord ++ tailWord_5597605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5597623 : List Nat := [1, 1, 3, 1, 3, 4, 3, 2, 1, 2, 2]
def baseStart_5597623 : Nat := 118140960795 + 5597623 * 2 ^ 59
def prefixEnd_5597623 : Nat := 4983230072969 + 3 ^ 40 * 5597623 * 2
def baseEnd_5597623 : Nat := 2874271121662458007969507

theorem tailTrace_5597623 : CollatzResearch.WordTrace tailWord_5597623 prefixEnd_5597623 2874271121662458007969507 := by
  unfold tailWord_5597623
  simp only [CollatzResearch.WordTrace]
  refine ⟨204162083399775343742629523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136108055599850229161753015 204162083399775343742629523)
  ·
    refine ⟨306243125099663015613944285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204162083399775343742629523 306243125099663015613944285)
    ·
      refine ⟨114841171912373630855229107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 306243125099663015613944285 114841171912373630855229107)
      ·
        refine ⟨172261757868560446282843661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114841171912373630855229107 172261757868560446282843661)
        ·
          refine ⟨64598159200710167356066373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 172261757868560446282843661 64598159200710167356066373)
          ·
            refine ⟨12112154850133156379262445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64598159200710167356066373 12112154850133156379262445)
            ·
              refine ⟨4542058068799933642223417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12112154850133156379262445 4542058068799933642223417)
              ·
                refine ⟨3406543551599950231667563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4542058068799933642223417 3406543551599950231667563)
                ·
                  refine ⟨5109815327399925347501345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3406543551599950231667563 5109815327399925347501345)
                  ·
                    refine ⟨3832361495549944010626009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5109815327399925347501345 3832361495549944010626009)
                    ·
                      refine ⟨2874271121662458007969507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3832361495549944010626009 2874271121662458007969507)
                      ·
                        rfl

theorem cell23_5597623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 3, 2, 1, 2, 2].length) (baseStart_5597623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5597623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5597623 prefixEnd_5597623 := by exact prefixLift 5597623
  have htrace : WordTrace (prefixWord ++ tailWord_5597623) baseStart_5597623 baseEnd_5597623 := by
    simpa [prefixWord, tailWord_5597623, baseEnd_5597623] using wordTrace_append hprefix tailTrace_5597623
  have hstable : (prefixWord ++ tailWord_5597623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5597623).length < 2 ^ (prefixWord ++ tailWord_5597623).sum := by decide
  have hdescent : baseEnd_5597623 < baseStart_5597623 := by decide
  rcases family_descends (prefixWord ++ tailWord_5597623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5597632 : List Nat := [2, 1, 1, 2, 3, 1, 1, 4, 3, 3, 2]
def baseStart_5597632 : Nat := 118140960795 + 5597632 * 2 ^ 59
def prefixEnd_5597632 : Nat := 4983230072969 + 3 ^ 40 * 5597632 * 2
def baseEnd_5597632 : Nat := 2874275742988348472756965

theorem tailTrace_5597632 : CollatzResearch.WordTrace tailWord_5597632 prefixEnd_5597632 2874275742988348472756965 := by
  unfold tailWord_5597632
  simp only [CollatzResearch.WordTrace]
  refine ⟨102081205828371369139853575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136108274437828492186471433 102081205828371369139853575)
  ·
    refine ⟨153121808742557053709780363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102081205828371369139853575 153121808742557053709780363)
    ·
      refine ⟨229682713113835580564670545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153121808742557053709780363 229682713113835580564670545)
      ·
        refine ⟨172262034835376685423502909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 229682713113835580564670545 172262034835376685423502909)
        ·
          refine ⟨64598263063266257033813591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 172262034835376685423502909 64598263063266257033813591)
          ·
            refine ⟨96897394594899385550720387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64598263063266257033813591 96897394594899385550720387)
            ·
              refine ⟨145346091892349078326080581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96897394594899385550720387 145346091892349078326080581)
              ·
                refine ⟨27252392229815452186140109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 145346091892349078326080581 27252392229815452186140109)
                ·
                  refine ⟨10219647086180794569802541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27252392229815452186140109 10219647086180794569802541)
                  ·
                    refine ⟨3832367657317797963675953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10219647086180794569802541 3832367657317797963675953)
                    ·
                      refine ⟨2874275742988348472756965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3832367657317797963675953 2874275742988348472756965)
                      ·
                        rfl

theorem cell23_5597632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 4, 3, 3, 2].length) (baseStart_5597632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5597632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5597632 prefixEnd_5597632 := by exact prefixLift 5597632
  have htrace : WordTrace (prefixWord ++ tailWord_5597632) baseStart_5597632 baseEnd_5597632 := by
    simpa [prefixWord, tailWord_5597632, baseEnd_5597632] using wordTrace_append hprefix tailTrace_5597632
  have hstable : (prefixWord ++ tailWord_5597632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5597632).length < 2 ^ (prefixWord ++ tailWord_5597632).sum := by decide
  have hdescent : baseEnd_5597632 < baseStart_5597632 := by decide
  rcases family_descends (prefixWord ++ tailWord_5597632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5597633 : List Nat := [1, 2, 7, 1, 1, 1, 1, 3, 2, 4]
def baseStart_5597633 : Nat := 118140960795 + 5597633 * 2 ^ 59
def prefixEnd_5597633 : Nat := 4983230072969 + 3 ^ 40 * 5597633 * 2
def baseEnd_5597633 : Nat := 958092085489667656281487

theorem tailTrace_5597633 : CollatzResearch.WordTrace tailWord_5597633 prefixEnd_5597633 958092085489667656281487 := by
  unfold tailWord_5597633
  simp only [CollatzResearch.WordTrace]
  refine ⟨204162448129739115450493553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136108298753159410300329035 204162448129739115450493553)
  ·
    refine ⟨153121836097304336587870165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204162448129739115450493553 153121836097304336587870165)
    ·
      refine ⟨3588793033530570388778207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 153121836097304336587870165 3588793033530570388778207)
      ·
        refine ⟨5383189550295855583167311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3588793033530570388778207 5383189550295855583167311)
        ·
          refine ⟨8074784325443783374750967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5383189550295855583167311 8074784325443783374750967)
          ·
            refine ⟨12112176488165675062126451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8074784325443783374750967 12112176488165675062126451)
            ·
              refine ⟨18168264732248512593189677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12112176488165675062126451 18168264732248512593189677)
              ·
                refine ⟨6813099274593192222446129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18168264732248512593189677 6813099274593192222446129)
                ·
                  refine ⟨5109824455944894166834597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6813099274593192222446129 5109824455944894166834597)
                  ·
                    refine ⟨958092085489667656281487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5109824455944894166834597 958092085489667656281487)
                    ·
                      rfl

theorem cell23_5597633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_5597633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5597633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5597633 prefixEnd_5597633 := by exact prefixLift 5597633
  have htrace : WordTrace (prefixWord ++ tailWord_5597633) baseStart_5597633 baseEnd_5597633 := by
    simpa [prefixWord, tailWord_5597633, baseEnd_5597633] using wordTrace_append hprefix tailTrace_5597633
  have hstable : (prefixWord ++ tailWord_5597633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5597633).length < 2 ^ (prefixWord ++ tailWord_5597633).sum := by decide
  have hdescent : baseEnd_5597633 < baseStart_5597633 := by decide
  rcases family_descends (prefixWord ++ tailWord_5597633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5597639 : List Nat := [1, 1, 4, 1, 1, 5, 1, 3, 2, 1, 3]
def baseStart_5597639 : Nat := 118140960795 + 5597639 * 2 ^ 59
def prefixEnd_5597639 : Nat := 4983230072969 + 3 ^ 40 * 5597639 * 2
def baseEnd_5597639 : Nat := 2874279337352929945369433

theorem tailTrace_5597639 : CollatzResearch.WordTrace tailWord_5597639 prefixEnd_5597639 2874279337352929945369433 := by
  unfold tailWord_5597639
  simp only [CollatzResearch.WordTrace]
  refine ⟨204162666967717378475211971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136108444645144918983474647 204162666967717378475211971)
  ·
    refine ⟨306244000451576067712817957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204162666967717378475211971 306244000451576067712817957)
    ·
      refine ⟨57420750084670512696153367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 306244000451576067712817957 57420750084670512696153367)
      ·
        refine ⟨86131125127005769044230051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57420750084670512696153367 86131125127005769044230051)
        ·
          refine ⟨129196687690508653566345077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86131125127005769044230051 129196687690508653566345077)
          ·
            refine ⟨12112189470985186271844851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 129196687690508653566345077 12112189470985186271844851)
            ·
              refine ⟨18168284206477779407767277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12112189470985186271844851 18168284206477779407767277)
              ·
                refine ⟨6813106577429167277912729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18168284206477779407767277 6813106577429167277912729)
                ·
                  refine ⟨5109829933071875458434547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6813106577429167277912729 5109829933071875458434547)
                  ·
                    refine ⟨7664744899607813187651821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5109829933071875458434547 7664744899607813187651821)
                    ·
                      refine ⟨2874279337352929945369433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7664744899607813187651821 2874279337352929945369433)
                      ·
                        rfl

theorem cell23_5597639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 3, 2, 1, 3].length) (baseStart_5597639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5597639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5597639 prefixEnd_5597639 := by exact prefixLift 5597639
  have htrace : WordTrace (prefixWord ++ tailWord_5597639) baseStart_5597639 baseEnd_5597639 := by
    simpa [prefixWord, tailWord_5597639, baseEnd_5597639] using wordTrace_append hprefix tailTrace_5597639
  have hstable : (prefixWord ++ tailWord_5597639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5597639).length < 2 ^ (prefixWord ++ tailWord_5597639).sum := by decide
  have hdescent : baseEnd_5597639 < baseStart_5597639 := by decide
  rcases family_descends (prefixWord ++ tailWord_5597639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5597665 : List Nat := [1, 2, 3, 1, 2, 2, 1, 3, 2, 1, 5]
def baseStart_5597665 : Nat := 118140960795 + 5597665 * 2 ^ 59
def prefixEnd_5597665 : Nat := 4983230072969 + 3 ^ 40 * 5597665 * 2
def baseEnd_5597665 : Nat := 2874292687849946843644313

theorem tailTrace_5597665 : CollatzResearch.WordTrace tailWord_5597665 prefixEnd_5597665 2874292687849946843644313 := by
  unfold tailWord_5597665
  simp only [CollatzResearch.WordTrace]
  refine ⟨204163615265623184915658449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136109076843748789943772299 204163615265623184915658449)
  ·
    refine ⟨153122711449217388686743837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204163615265623184915658449 153122711449217388686743837)
    ·
      refine ⟨57421016793456520757528939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 153122711449217388686743837 57421016793456520757528939)
      ·
        refine ⟨86131525190184781136293409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57421016793456520757528939 86131525190184781136293409)
        ·
          refine ⟨64598643892638585852220057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86131525190184781136293409 64598643892638585852220057)
          ·
            refine ⟨48448982919478939389165043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64598643892638585852220057 48448982919478939389165043)
            ·
              refine ⟨72673474379218409083747565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48448982919478939389165043 72673474379218409083747565)
              ·
                refine ⟨27252552892206903406405337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72673474379218409083747565 27252552892206903406405337)
                ·
                  refine ⟨20439414669155177554804003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27252552892206903406405337 20439414669155177554804003)
                  ·
                    refine ⟨30659122003732766332206005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20439414669155177554804003 30659122003732766332206005)
                    ·
                      refine ⟨2874292687849946843644313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30659122003732766332206005 2874292687849946843644313)
                      ·
                        rfl

theorem cell23_5597665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 3, 2, 1, 5].length) (baseStart_5597665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5597665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5597665 prefixEnd_5597665 := by exact prefixLift 5597665
  have htrace : WordTrace (prefixWord ++ tailWord_5597665) baseStart_5597665 baseEnd_5597665 := by
    simpa [prefixWord, tailWord_5597665, baseEnd_5597665] using wordTrace_append hprefix tailTrace_5597665
  have hstable : (prefixWord ++ tailWord_5597665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5597665).length < 2 ^ (prefixWord ++ tailWord_5597665).sum := by decide
  have hdescent : baseEnd_5597665 < baseStart_5597665 := by decide
  rcases family_descends (prefixWord ++ tailWord_5597665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5597675 : List Nat := [1, 1, 1, 1, 2, 3, 4, 2, 2, 2, 4]
def baseStart_5597675 : Nat := 118140960795 + 5597675 * 2 ^ 59
def prefixEnd_5597675 : Nat := 4983230072969 + 3 ^ 40 * 5597675 * 2
def baseEnd_5597675 : Nat := 2874297822656491804519267

theorem tailTrace_5597675 : CollatzResearch.WordTrace tailWord_5597675 prefixEnd_5597675 2874297822656491804519267 := by
  unfold tailWord_5597675
  simp only [CollatzResearch.WordTrace]
  refine ⟨204163979995586956623522479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136109319997057971082348319 204163979995586956623522479)
  ·
    refine ⟨306245969993380434935283719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204163979995586956623522479 306245969993380434935283719)
    ·
      refine ⟨459368954990070652402925579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 306245969993380434935283719 459368954990070652402925579)
      ·
        refine ⟨689053432485105978604388369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 459368954990070652402925579 689053432485105978604388369)
        ·
          refine ⟨516790074363829483953291277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 689053432485105978604388369 516790074363829483953291277)
          ·
            refine ⟨193796277886436056482484229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 516790074363829483953291277 193796277886436056482484229)
            ·
              refine ⟨36336802103706760590465793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 193796277886436056482484229 36336802103706760590465793)
              ·
                refine ⟨27252601577780070442849345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36336802103706760590465793 27252601577780070442849345)
                ·
                  refine ⟨20439451183335052832137009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27252601577780070442849345 20439451183335052832137009)
                  ·
                    refine ⟨15329588387501289624102757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20439451183335052832137009 15329588387501289624102757)
                    ·
                      refine ⟨2874297822656491804519267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15329588387501289624102757 2874297822656491804519267)
                      ·
                        rfl

theorem cell23_5597675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 2, 2, 2, 4].length) (baseStart_5597675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5597675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5597675 prefixEnd_5597675 := by exact prefixLift 5597675
  have htrace : WordTrace (prefixWord ++ tailWord_5597675) baseStart_5597675 baseEnd_5597675 := by
    simpa [prefixWord, tailWord_5597675, baseEnd_5597675] using wordTrace_append hprefix tailTrace_5597675
  have hstable : (prefixWord ++ tailWord_5597675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5597675).length < 2 ^ (prefixWord ++ tailWord_5597675).sum := by decide
  have hdescent : baseEnd_5597675 < baseStart_5597675 := by decide
  rcases family_descends (prefixWord ++ tailWord_5597675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5597715 : List Nat := [1, 1, 1, 2, 1, 5, 3, 1, 1, 7]
def baseStart_5597715 : Nat := 118140960795 + 5597715 * 2 ^ 59
def prefixEnd_5597715 : Nat := 4983230072969 + 3 ^ 40 * 5597715 * 2
def baseEnd_5597715 : Nat := 958106120627557216006361

theorem tailTrace_5597715 : CollatzResearch.WordTrace tailWord_5597715 prefixEnd_5597715 958106120627557216006361 := by
  unfold tailWord_5597715
  simp only [CollatzResearch.WordTrace]
  refine ⟨204165438915442043454978599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136110292610294695636652399 204165438915442043454978599)
  ·
    refine ⟨306248158373163065182467899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204165438915442043454978599 306248158373163065182467899)
    ·
      refine ⟨459372237559744597773701849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 306248158373163065182467899 459372237559744597773701849)
      ·
        refine ⟨344529178169808448330276387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 459372237559744597773701849 344529178169808448330276387)
        ·
          refine ⟨516793767254712672495414581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 344529178169808448330276387 516793767254712672495414581)
          ·
            refine ⟨48449415680129313046445117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 516793767254712672495414581 48449415680129313046445117)
            ·
              refine ⟨18168530880048492392416919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48449415680129313046445117 18168530880048492392416919)
              ·
                refine ⟨27252796320072738588625379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18168530880048492392416919 27252796320072738588625379)
                ·
                  refine ⟨40879194480109107882938069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27252796320072738588625379 40879194480109107882938069)
                  ·
                    refine ⟨958106120627557216006361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40879194480109107882938069 958106120627557216006361)
                    ·
                      rfl

theorem cell23_5597715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 1, 1, 7].length) (baseStart_5597715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5597715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5597715 prefixEnd_5597715 := by exact prefixLift 5597715
  have htrace : WordTrace (prefixWord ++ tailWord_5597715) baseStart_5597715 baseEnd_5597715 := by
    simpa [prefixWord, tailWord_5597715, baseEnd_5597715] using wordTrace_append hprefix tailTrace_5597715
  have hstable : (prefixWord ++ tailWord_5597715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5597715).length < 2 ^ (prefixWord ++ tailWord_5597715).sum := by decide
  have hdescent : baseEnd_5597715 < baseStart_5597715 := by decide
  rcases family_descends (prefixWord ++ tailWord_5597715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5597772 : List Nat := [2, 2, 1, 3, 1, 2, 1, 3, 1, 4, 3]
def baseStart_5597772 : Nat := 118140960795 + 5597772 * 2 ^ 59
def prefixEnd_5597772 : Nat := 4983230072969 + 3 ^ 40 * 5597772 * 2
def baseEnd_5597772 : Nat := 2874347630279977925006321

theorem tailTrace_5597772 : CollatzResearch.WordTrace tailWord_5597772 prefixEnd_5597772 2874347630279977925006321 := by
  unfold tailWord_5597772
  simp only [CollatzResearch.WordTrace]
  refine ⟨102083758938117771094901785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136111678584157028126535713 102083758938117771094901785)
  ·
    refine ⟨76562819203588328321176339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102083758938117771094901785 76562819203588328321176339)
    ·
      refine ⟨114844228805382492481764509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76562819203588328321176339 114844228805382492481764509)
      ·
        refine ⟨43066585802018434680661691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114844228805382492481764509 43066585802018434680661691)
        ·
          refine ⟨64599878703027652020992537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43066585802018434680661691 64599878703027652020992537)
          ·
            refine ⟨48449909027270739015744403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64599878703027652020992537 48449909027270739015744403)
            ·
              refine ⟨72674863540906108523616605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48449909027270739015744403 72674863540906108523616605)
              ·
                refine ⟨27253073827839790696356227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72674863540906108523616605 27253073827839790696356227)
                ·
                  refine ⟨40879610741759686044534341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27253073827839790696356227 40879610741759686044534341)
                  ·
                    refine ⟨7664927014079941133350189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40879610741759686044534341 7664927014079941133350189)
                    ·
                      refine ⟨2874347630279977925006321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7664927014079941133350189 2874347630279977925006321)
                      ·
                        rfl

theorem cell23_5597772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 3, 1, 4, 3].length) (baseStart_5597772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5597772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5597772 prefixEnd_5597772 := by exact prefixLift 5597772
  have htrace : WordTrace (prefixWord ++ tailWord_5597772) baseStart_5597772 baseEnd_5597772 := by
    simpa [prefixWord, tailWord_5597772, baseEnd_5597772] using wordTrace_append hprefix tailTrace_5597772
  have hstable : (prefixWord ++ tailWord_5597772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5597772).length < 2 ^ (prefixWord ++ tailWord_5597772).sum := by decide
  have hdescent : baseEnd_5597772 < baseStart_5597772 := by decide
  rcases family_descends (prefixWord ++ tailWord_5597772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5597775 : List Nat := [1, 1, 2, 1, 1, 2, 5, 2, 8]
def baseStart_5597775 : Nat := 118140960795 + 5597775 * 2 ^ 59
def prefixEnd_5597775 : Nat := 4983230072969 + 3 ^ 40 * 5597775 * 2
def baseEnd_5597775 : Nat := 319372130080215712585423

theorem tailTrace_5597775 : CollatzResearch.WordTrace tailWord_5597775 prefixEnd_5597775 319372130080215712585423 := by
  unfold tailWord_5597775
  simp only [CollatzResearch.WordTrace]
  refine ⟨204167627295224673702162779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136111751530149782468108519 204167627295224673702162779)
  ·
    refine ⟨306251440942837010553244169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204167627295224673702162779 306251440942837010553244169)
    ·
      refine ⟨229688580707127757914933127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 306251440942837010553244169 229688580707127757914933127)
      ·
        refine ⟨344532871060691636872399691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229688580707127757914933127 344532871060691636872399691)
        ·
          refine ⟨516799306591037455308599537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 344532871060691636872399691 516799306591037455308599537)
          ·
            refine ⟨387599479943278091481449653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 516799306591037455308599537 387599479943278091481449653)
            ·
              refine ⟨36337451244682321076385905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 387599479943278091481449653 36337451244682321076385905)
              ·
                refine ⟨27253088433511740807289429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36337451244682321076385905 27253088433511740807289429)
                ·
                  refine ⟨319372130080215712585423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27253088433511740807289429 319372130080215712585423)
                  ·
                    rfl

theorem cell23_5597775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 2, 8].length) (baseStart_5597775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5597775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5597775 prefixEnd_5597775 := by exact prefixLift 5597775
  have htrace : WordTrace (prefixWord ++ tailWord_5597775) baseStart_5597775 baseEnd_5597775 := by
    simpa [prefixWord, tailWord_5597775, baseEnd_5597775] using wordTrace_append hprefix tailTrace_5597775
  have hstable : (prefixWord ++ tailWord_5597775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5597775).length < 2 ^ (prefixWord ++ tailWord_5597775).sum := by decide
  have hdescent : baseEnd_5597775 < baseStart_5597775 := by decide
  rcases family_descends (prefixWord ++ tailWord_5597775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5597869 : List Nat := [1, 5, 2, 1, 1, 2, 1, 3, 1, 6]
def baseStart_5597869 : Nat := 118140960795 + 5597869 * 2 ^ 59
def prefixEnd_5597869 : Nat := 4983230072969 + 3 ^ 40 * 5597869 * 2
def baseEnd_5597869 : Nat := 958132479301154681831125

theorem tailTrace_5597869 : CollatzResearch.WordTrace tailWord_5597869 prefixEnd_5597869 958132479301154681831125 := by
  unfold tailWord_5597869
  simp only [CollatzResearch.WordTrace]
  refine ⟨204171055756884127756084661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136114037171256085170723107 204171055756884127756084661)
  ·
    refine ⟨19141036477207886977132937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 204171055756884127756084661 19141036477207886977132937)
    ·
      refine ⟨14355777357905915232849703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19141036477207886977132937 14355777357905915232849703)
      ·
        refine ⟨21533666036858872849274555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14355777357905915232849703 21533666036858872849274555)
        ·
          refine ⟨32300499055288309273911833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21533666036858872849274555 32300499055288309273911833)
          ·
            refine ⟨24225374291466231955433875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32300499055288309273911833 24225374291466231955433875)
            ·
              refine ⟨36338061437199347933150813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24225374291466231955433875 36338061437199347933150813)
              ·
                refine ⟨13626773038949755474931555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36338061437199347933150813 13626773038949755474931555)
                ·
                  refine ⟨20440159558424633212397333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13626773038949755474931555 20440159558424633212397333)
                  ·
                    refine ⟨958132479301154681831125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20440159558424633212397333 958132479301154681831125)
                    ·
                      rfl

theorem cell23_5597869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_5597869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5597869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5597869 prefixEnd_5597869 := by exact prefixLift 5597869
  have htrace : WordTrace (prefixWord ++ tailWord_5597869) baseStart_5597869 baseEnd_5597869 := by
    simpa [prefixWord, tailWord_5597869, baseEnd_5597869] using wordTrace_append hprefix tailTrace_5597869
  have hstable : (prefixWord ++ tailWord_5597869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5597869).length < 2 ^ (prefixWord ++ tailWord_5597869).sum := by decide
  have hdescent : baseEnd_5597869 < baseStart_5597869 := by decide
  rcases family_descends (prefixWord ++ tailWord_5597869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5597896 : List Nat := [2, 1, 3, 1, 2, 4, 1, 3, 1, 2, 3]
def baseStart_5597896 : Nat := 118140960795 + 5597896 * 2 ^ 59
def prefixEnd_5597896 : Nat := 4983230072969 + 3 ^ 40 * 5597896 * 2
def baseEnd_5597896 : Nat := 2874411301881135439855751

theorem tailTrace_5597896 : CollatzResearch.WordTrace tailWord_5597896 prefixEnd_5597896 2874411301881135439855751 := by
  unfold tailWord_5597896
  simp only [CollatzResearch.WordTrace]
  refine ⟨102086020263893155683658771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136114693685190874244878361 102086020263893155683658771)
  ·
    refine ⟨153129030395839733525488157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102086020263893155683658771 153129030395839733525488157)
    ·
      refine ⟨57423386398439900072058059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 153129030395839733525488157 57423386398439900072058059)
      ·
        refine ⟨86135079597659850108087089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57423386398439900072058059 86135079597659850108087089)
        ·
          refine ⟨64601309698244887581065317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86135079597659850108087089 64601309698244887581065317)
          ·
            refine ⟨12112745568420916421449747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64601309698244887581065317 12112745568420916421449747)
            ·
              refine ⟨18169118352631374632174621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12112745568420916421449747 18169118352631374632174621)
              ·
                refine ⟨6813419382236765487065483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18169118352631374632174621 6813419382236765487065483)
                ·
                  refine ⟨10220129073355148230598225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6813419382236765487065483 10220129073355148230598225)
                  ·
                    refine ⟨7665096805016361172948669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10220129073355148230598225 7665096805016361172948669)
                    ·
                      refine ⟨2874411301881135439855751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7665096805016361172948669 2874411301881135439855751)
                      ·
                        rfl

theorem cell23_5597896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 3, 1, 2, 3].length) (baseStart_5597896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5597896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5597896 prefixEnd_5597896 := by exact prefixLift 5597896
  have htrace : WordTrace (prefixWord ++ tailWord_5597896) baseStart_5597896 baseEnd_5597896 := by
    simpa [prefixWord, tailWord_5597896, baseEnd_5597896] using wordTrace_append hprefix tailTrace_5597896
  have hstable : (prefixWord ++ tailWord_5597896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5597896).length < 2 ^ (prefixWord ++ tailWord_5597896).sum := by decide
  have hdescent : baseEnd_5597896 < baseStart_5597896 := by decide
  rcases family_descends (prefixWord ++ tailWord_5597896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5598019 : List Nat := [1, 1, 1, 3, 1, 4, 1, 4, 2, 5]
def baseStart_5598019 : Nat := 118140960795 + 5598019 * 2 ^ 59
def prefixEnd_5598019 : Nat := 4983230072969 + 3 ^ 40 * 5598019 * 2
def baseEnd_5598019 : Nat := 958158153333879486205895

theorem tailTrace_5598019 : CollatzResearch.WordTrace tailWord_5598019 prefixEnd_5598019 958158153333879486205895 := by
  unfold tailWord_5598019
  simp only [CollatzResearch.WordTrace]
  refine ⟨204176526706340703374045111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136117684470893802249363407 204176526706340703374045111)
  ·
    refine ⟨306264790059511055061067667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204176526706340703374045111 306264790059511055061067667)
    ·
      refine ⟨459397185089266582591601501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 306264790059511055061067667 459397185089266582591601501)
      ·
        refine ⟨172273944408474968471850563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 459397185089266582591601501 172273944408474968471850563)
        ·
          refine ⟨258410916612712452707775845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172273944408474968471850563 258410916612712452707775845)
          ·
            refine ⟨48452046864883584882707971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 258410916612712452707775845 48452046864883584882707971)
            ·
              refine ⟨72678070297325377324061957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48452046864883584882707971 72678070297325377324061957)
              ·
                refine ⟨13627138180748508248261617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72678070297325377324061957 13627138180748508248261617)
                ·
                  refine ⟨10220353635561381186196213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13627138180748508248261617 10220353635561381186196213)
                  ·
                    refine ⟨958158153333879486205895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10220353635561381186196213 958158153333879486205895)
                    ·
                      rfl

theorem cell23_5598019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 4, 2, 5].length) (baseStart_5598019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5598019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5598019 prefixEnd_5598019 := by exact prefixLift 5598019
  have htrace : WordTrace (prefixWord ++ tailWord_5598019) baseStart_5598019 baseEnd_5598019 := by
    simpa [prefixWord, tailWord_5598019, baseEnd_5598019] using wordTrace_append hprefix tailTrace_5598019
  have hstable : (prefixWord ++ tailWord_5598019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5598019).length < 2 ^ (prefixWord ++ tailWord_5598019).sum := by decide
  have hdescent : baseEnd_5598019 < baseStart_5598019 := by decide
  rcases family_descends (prefixWord ++ tailWord_5598019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5598056 : List Nat := [2, 1, 4, 2, 1, 3, 1, 1, 1, 3, 4]
def baseStart_5598056 : Nat := 118140960795 + 5598056 * 2 ^ 59
def prefixEnd_5598056 : Nat := 4983230072969 + 3 ^ 40 * 5598056 * 2
def baseEnd_5598056 : Nat := 2874493458785854813855015

theorem tailTrace_5598056 : CollatzResearch.WordTrace tailWord_5598056 prefixEnd_5598056 2874493458785854813855015 := by
  unfold tailWord_5598056
  simp only [CollatzResearch.WordTrace]
  refine ⟨102088938103603329346571011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136118584138137772462094681 102088938103603329346571011)
  ·
    refine ⟨153133407155404994019856517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102088938103603329346571011 153133407155404994019856517)
    ·
      refine ⟨28712513841638436378723097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 153133407155404994019856517 28712513841638436378723097)
      ·
        refine ⟨21534385381228827284042323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28712513841638436378723097 21534385381228827284042323)
        ·
          refine ⟨32301578071843240926063485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21534385381228827284042323 32301578071843240926063485)
          ·
            refine ⟨12113091776941215347273807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32301578071843240926063485 12113091776941215347273807)
            ·
              refine ⟨18169637665411823020910711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12113091776941215347273807 18169637665411823020910711)
              ·
                refine ⟨27254456498117734531366067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18169637665411823020910711 27254456498117734531366067)
                ·
                  refine ⟨40881684747176601797049101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27254456498117734531366067 40881684747176601797049101)
                  ·
                    refine ⟨15330631780191225673893413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40881684747176601797049101 15330631780191225673893413)
                    ·
                      refine ⟨2874493458785854813855015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15330631780191225673893413 2874493458785854813855015)
                      ·
                        rfl

theorem cell23_5598056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_5598056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5598056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5598056 prefixEnd_5598056 := by exact prefixLift 5598056
  have htrace : WordTrace (prefixWord ++ tailWord_5598056) baseStart_5598056 baseEnd_5598056 := by
    simpa [prefixWord, tailWord_5598056, baseEnd_5598056] using wordTrace_append hprefix tailTrace_5598056
  have hstable : (prefixWord ++ tailWord_5598056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5598056).length < 2 ^ (prefixWord ++ tailWord_5598056).sum := by decide
  have hdescent : baseEnd_5598056 < baseStart_5598056 := by decide
  rcases family_descends (prefixWord ++ tailWord_5598056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5598076 : List Nat := [2, 2, 2, 1, 1, 1, 1, 6, 2, 2, 3]
def baseStart_5598076 : Nat := 118140960795 + 5598076 * 2 ^ 59
def prefixEnd_5598076 : Nat := 4983230072969 + 3 ^ 40 * 5598076 * 2
def baseEnd_5598076 : Nat := 2874503728398944735604923

theorem tailTrace_5598076 : CollatzResearch.WordTrace tailWord_5598076 prefixEnd_5598076 2874503728398944735604923 := by
  unfold tailWord_5598076
  simp only [CollatzResearch.WordTrace]
  refine ⟨102089302833567101054435041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136119070444756134739246721 102089302833567101054435041)
  ·
    refine ⟨76566977125175325790826281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102089302833567101054435041 76566977125175325790826281)
    ·
      refine ⟨57425232843881494343119711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76566977125175325790826281 57425232843881494343119711)
      ·
        refine ⟨86137849265822241514679567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57425232843881494343119711 86137849265822241514679567)
        ·
          refine ⟨129206773898733362272019351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86137849265822241514679567 129206773898733362272019351)
          ·
            refine ⟨193810160848100043408029027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129206773898733362272019351 193810160848100043408029027)
            ·
              refine ⟨290715241272150065112043541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 193810160848100043408029027 290715241272150065112043541)
              ·
                refine ⟨13627276934632034302127041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 290715241272150065112043541 13627276934632034302127041)
                ·
                  refine ⟨10220457700974025726595281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13627276934632034302127041 10220457700974025726595281)
                  ·
                    refine ⟨7665343275730519294946461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10220457700974025726595281 7665343275730519294946461)
                    ·
                      refine ⟨2874503728398944735604923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7665343275730519294946461 2874503728398944735604923)
                      ·
                        rfl

theorem cell23_5598076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 6, 2, 2, 3].length) (baseStart_5598076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5598076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5598076 prefixEnd_5598076 := by exact prefixLift 5598076
  have htrace : WordTrace (prefixWord ++ tailWord_5598076) baseStart_5598076 baseEnd_5598076 := by
    simpa [prefixWord, tailWord_5598076, baseEnd_5598076] using wordTrace_append hprefix tailTrace_5598076
  have hstable : (prefixWord ++ tailWord_5598076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5598076).length < 2 ^ (prefixWord ++ tailWord_5598076).sum := by decide
  have hdescent : baseEnd_5598076 < baseStart_5598076 := by decide
  rcases family_descends (prefixWord ++ tailWord_5598076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5598083 : List Nat := [1, 1, 1, 3, 4, 1, 1, 6, 1, 4]
def baseStart_5598083 : Nat := 118140960795 + 5598083 * 2 ^ 59
def prefixEnd_5598083 : Nat := 4983230072969 + 3 ^ 40 * 5598083 * 2
def baseEnd_5598083 : Nat := 958169107587842069405797

theorem tailTrace_5598083 : CollatzResearch.WordTrace tailWord_5598083 prefixEnd_5598083 958169107587842069405797 := by
  unfold tailWord_5598083
  simp only [CollatzResearch.WordTrace]
  refine ⟨204178860978108842304374903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136119240652072561536249935 204178860978108842304374903)
  ·
    refine ⟨306268291467163263456562355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204178860978108842304374903 306268291467163263456562355)
    ·
      refine ⟨459402437200744895184843533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 306268291467163263456562355 459402437200744895184843533)
      ·
        refine ⟨172275913950279335694316325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 459402437200744895184843533 172275913950279335694316325)
        ·
          refine ⟨32301733865677375442684311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 172275913950279335694316325 32301733865677375442684311)
          ·
            refine ⟨48452600798516063164026467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32301733865677375442684311 48452600798516063164026467)
            ·
              refine ⟨72678901197774094746039701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48452600798516063164026467 72678901197774094746039701)
              ·
                refine ⟨3406823493645660691220611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 72678901197774094746039701 3406823493645660691220611)
                ·
                  refine ⟨5110235240468491036830917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3406823493645660691220611 5110235240468491036830917)
                  ·
                    refine ⟨958169107587842069405797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5110235240468491036830917 958169107587842069405797)
                    ·
                      rfl

theorem cell23_5598083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 6, 1, 4].length) (baseStart_5598083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5598083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5598083 prefixEnd_5598083 := by exact prefixLift 5598083
  have htrace : WordTrace (prefixWord ++ tailWord_5598083) baseStart_5598083 baseEnd_5598083 := by
    simpa [prefixWord, tailWord_5598083, baseEnd_5598083] using wordTrace_append hprefix tailTrace_5598083
  have hstable : (prefixWord ++ tailWord_5598083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5598083).length < 2 ^ (prefixWord ++ tailWord_5598083).sum := by decide
  have hdescent : baseEnd_5598083 < baseStart_5598083 := by decide
  rcases family_descends (prefixWord ++ tailWord_5598083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5598149 : List Nat := [1, 3, 1, 1, 1, 1, 1, 2, 2, 5, 5]
def baseStart_5598149 : Nat := 118140960795 + 5598149 * 2 ^ 59
def prefixEnd_5598149 : Nat := 4983230072969 + 3 ^ 40 * 5598149 * 2
def baseEnd_5598149 : Nat := 2874541212486722949992087

theorem tailTrace_5598149 : CollatzResearch.WordTrace tailWord_5598149 prefixEnd_5598149 2874541212486722949992087 := by
  unfold tailWord_5598149
  simp only [CollatzResearch.WordTrace]
  refine ⟨204181268195869735576277501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136120845463913157050851667 204181268195869735576277501)
  ·
    refine ⟨76567975573451150841104063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 204181268195869735576277501 76567975573451150841104063)
    ·
      refine ⟨114851963360176726261656095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76567975573451150841104063 114851963360176726261656095)
      ·
        refine ⟨172277945040265089392484143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114851963360176726261656095 172277945040265089392484143)
        ·
          refine ⟨258416917560397634088726215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172277945040265089392484143 258416917560397634088726215)
          ·
            refine ⟨387625376340596451133089323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 258416917560397634088726215 387625376340596451133089323)
            ·
              refine ⟨581438064510894676699633985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 387625376340596451133089323 581438064510894676699633985)
              ·
                refine ⟨436078548383171007524725489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 581438064510894676699633985 436078548383171007524725489)
                ·
                  refine ⟨327058911287378255643544117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 436078548383171007524725489 327058911287378255643544117)
                  ·
                    refine ⟨30661772933191711466582261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 327058911287378255643544117 30661772933191711466582261)
                    ·
                      refine ⟨2874541212486722949992087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30661772933191711466582261 2874541212486722949992087)
                      ·
                        rfl

theorem cell23_5598149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 5, 5].length) (baseStart_5598149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5598149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5598149 prefixEnd_5598149 := by exact prefixLift 5598149
  have htrace : WordTrace (prefixWord ++ tailWord_5598149) baseStart_5598149 baseEnd_5598149 := by
    simpa [prefixWord, tailWord_5598149, baseEnd_5598149] using wordTrace_append hprefix tailTrace_5598149
  have hstable : (prefixWord ++ tailWord_5598149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5598149).length < 2 ^ (prefixWord ++ tailWord_5598149).sum := by decide
  have hdescent : baseEnd_5598149 < baseStart_5598149 := by decide
  rcases family_descends (prefixWord ++ tailWord_5598149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5598156 : List Nat := [2, 2, 1, 4, 1, 1, 2, 3, 1, 6]
def baseStart_5598156 : Nat := 118140960795 + 5598156 * 2 ^ 59
def prefixEnd_5598156 : Nat := 4983230072969 + 3 ^ 40 * 5598156 * 2
def baseEnd_5598156 : Nat := 958181602283768140868185

theorem tailTrace_5598156 : CollatzResearch.WordTrace tailWord_5598156 prefixEnd_5598156 958181602283768140868185 := by
  unfold tailWord_5598156
  simp only [CollatzResearch.WordTrace]
  refine ⟨102090761753422187885891161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136121015671229583847854881 102090761753422187885891161)
  ·
    refine ⟨76568071315066640914418371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102090761753422187885891161 76568071315066640914418371)
    ·
      refine ⟨114852106972599961371627557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76568071315066640914418371 114852106972599961371627557)
      ·
        refine ⟨21534770057362492757180167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 114852106972599961371627557 21534770057362492757180167)
        ·
          refine ⟨32302155086043739135770251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21534770057362492757180167 32302155086043739135770251)
          ·
            refine ⟨48453232629065608703655377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32302155086043739135770251 48453232629065608703655377)
            ·
              refine ⟨36339924471799206527741533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48453232629065608703655377 36339924471799206527741533)
              ·
                refine ⟨13627471676924702447903075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36339924471799206527741533 13627471676924702447903075)
                ·
                  refine ⟨20441207515387053671854613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13627471676924702447903075 20441207515387053671854613)
                  ·
                    refine ⟨958181602283768140868185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20441207515387053671854613 958181602283768140868185)
                    ·
                      rfl

theorem cell23_5598156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 3, 1, 6].length) (baseStart_5598156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5598156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5598156 prefixEnd_5598156 := by exact prefixLift 5598156
  have htrace : WordTrace (prefixWord ++ tailWord_5598156) baseStart_5598156 baseEnd_5598156 := by
    simpa [prefixWord, tailWord_5598156, baseEnd_5598156] using wordTrace_append hprefix tailTrace_5598156
  have hstable : (prefixWord ++ tailWord_5598156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5598156).length < 2 ^ (prefixWord ++ tailWord_5598156).sum := by decide
  have hdescent : baseEnd_5598156 < baseStart_5598156 := by decide
  rcases family_descends (prefixWord ++ tailWord_5598156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5598173 : List Nat := [1, 4, 3, 1, 2, 2, 1, 2, 1, 6]
def baseStart_5598173 : Nat := 118140960795 + 5598173 * 2 ^ 59
def prefixEnd_5598173 : Nat := 4983230072969 + 3 ^ 40 * 5598173 * 2
def baseEnd_5598173 : Nat := 958184512007476952030659

theorem tailTrace_5598173 : CollatzResearch.WordTrace tailWord_5598173 prefixEnd_5598173 958184512007476952030659 := by
  unfold tailWord_5598173
  simp only [CollatzResearch.WordTrace]
  refine ⟨204182143547782787675151173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136121429031855191783434115 204182143547782787675151173)
  ·
    refine ⟨38284151915209272689090845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 204182143547782787675151173 38284151915209272689090845)
    ·
      refine ⟨14356556968203477258409067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38284151915209272689090845 14356556968203477258409067)
      ·
        refine ⟨21534835452305215887613601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14356556968203477258409067 21534835452305215887613601)
        ·
          refine ⟨16151126589228911915710201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21534835452305215887613601 16151126589228911915710201)
          ·
            refine ⟨12113344941921683936782651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16151126589228911915710201 12113344941921683936782651)
            ·
              refine ⟨18170017412882525905173977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12113344941921683936782651 18170017412882525905173977)
              ·
                refine ⟨13627513059661894428880483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18170017412882525905173977 13627513059661894428880483)
                ·
                  refine ⟨20441269589492841643320725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13627513059661894428880483 20441269589492841643320725)
                  ·
                    refine ⟨958184512007476952030659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20441269589492841643320725 958184512007476952030659)
                    ·
                      rfl

theorem cell23_5598173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_5598173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5598173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5598173 prefixEnd_5598173 := by exact prefixLift 5598173
  have htrace : WordTrace (prefixWord ++ tailWord_5598173) baseStart_5598173 baseEnd_5598173 := by
    simpa [prefixWord, tailWord_5598173, baseEnd_5598173] using wordTrace_append hprefix tailTrace_5598173
  have hstable : (prefixWord ++ tailWord_5598173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5598173).length < 2 ^ (prefixWord ++ tailWord_5598173).sum := by decide
  have hdescent : baseEnd_5598173 < baseStart_5598173 := by decide
  rcases family_descends (prefixWord ++ tailWord_5598173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5598183 : List Nat := [1, 1, 5, 2, 2, 1, 3, 1, 1, 1, 5]
def baseStart_5598183 : Nat := 118140960795 + 5598183 * 2 ^ 59
def prefixEnd_5598183 : Nat := 4983230072969 + 3 ^ 40 * 5598183 * 2
def baseEnd_5598183 : Nat := 2874558670828975816966931

theorem tailTrace_5598183 : CollatzResearch.WordTrace tailWord_5598183 prefixEnd_5598183 2874558670828975816966931 := by
  unfold tailWord_5598183
  simp only [CollatzResearch.WordTrace]
  refine ⟨204182508277746559383015203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136121672185164372922010135 204182508277746559383015203)
  ·
    refine ⟨306273762416619839074522805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204182508277746559383015203 306273762416619839074522805)
    ·
      refine ⟨28713165226558109913236513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 306273762416619839074522805 28713165226558109913236513)
      ·
        refine ⟨21534873919918582434927385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28713165226558109913236513 21534873919918582434927385)
        ·
          refine ⟨16151155439938936826195539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21534873919918582434927385 16151155439938936826195539)
          ·
            refine ⟨24226733159908405239293309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16151155439938936826195539 24226733159908405239293309)
            ·
              refine ⟨9085024934965651964734991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24226733159908405239293309 9085024934965651964734991)
              ·
                refine ⟨13627537402448477947102487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9085024934965651964734991 13627537402448477947102487)
                ·
                  refine ⟨20441306103672716920653731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13627537402448477947102487 20441306103672716920653731)
                  ·
                    refine ⟨30661959155509075380980597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20441306103672716920653731 30661959155509075380980597)
                    ·
                      refine ⟨2874558670828975816966931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30661959155509075380980597 2874558670828975816966931)
                      ·
                        rfl

theorem cell23_5598183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3, 1, 1, 1, 5].length) (baseStart_5598183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5598183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5598183 prefixEnd_5598183 := by exact prefixLift 5598183
  have htrace : WordTrace (prefixWord ++ tailWord_5598183) baseStart_5598183 baseEnd_5598183 := by
    simpa [prefixWord, tailWord_5598183, baseEnd_5598183] using wordTrace_append hprefix tailTrace_5598183
  have hstable : (prefixWord ++ tailWord_5598183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5598183).length < 2 ^ (prefixWord ++ tailWord_5598183).sum := by decide
  have hdescent : baseEnd_5598183 < baseStart_5598183 := by decide
  rcases family_descends (prefixWord ++ tailWord_5598183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5598213 : List Nat := [1, 3, 1, 1, 2, 3, 4, 1, 1, 3, 3]
def baseStart_5598213 : Nat := 118140960795 + 5598213 * 2 ^ 59
def prefixEnd_5598213 : Nat := 4983230072969 + 3 ^ 40 * 5598213 * 2
def baseEnd_5598213 : Nat := 2874574075248610699591793

theorem tailTrace_5598213 : CollatzResearch.WordTrace tailWord_5598213 prefixEnd_5598213 2874574075248610699591793 := by
  unfold tailWord_5598213
  simp only [CollatzResearch.WordTrace]
  refine ⟨204183602467637874506607293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136122401645091916337738195 204183602467637874506607293)
  ·
    refine ⟨76568850925364202939977735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 204183602467637874506607293 76568850925364202939977735)
    ·
      refine ⟨114853276388046304409966603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76568850925364202939977735 114853276388046304409966603)
      ·
        refine ⟨172279914582069456614949905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114853276388046304409966603 172279914582069456614949905)
        ·
          refine ⟨129209935936552092461212429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172279914582069456614949905 129209935936552092461212429)
          ·
            refine ⟨48453725976207034672954661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 129209935936552092461212429 48453725976207034672954661)
            ·
              refine ⟨9085073620538819001178999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48453725976207034672954661 9085073620538819001178999)
              ·
                refine ⟨13627610430808228501768499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9085073620538819001178999 13627610430808228501768499)
                ·
                  refine ⟨20441415646212342752652749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13627610430808228501768499 20441415646212342752652749)
                  ·
                    refine ⟨7665530867329628532244781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20441415646212342752652749 7665530867329628532244781)
                    ·
                      refine ⟨2874574075248610699591793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7665530867329628532244781 2874574075248610699591793)
                      ·
                        rfl

theorem cell23_5598213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4, 1, 1, 3, 3].length) (baseStart_5598213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5598213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5598213 prefixEnd_5598213 := by exact prefixLift 5598213
  have htrace : WordTrace (prefixWord ++ tailWord_5598213) baseStart_5598213 baseEnd_5598213 := by
    simpa [prefixWord, tailWord_5598213, baseEnd_5598213] using wordTrace_append hprefix tailTrace_5598213
  have hstable : (prefixWord ++ tailWord_5598213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5598213).length < 2 ^ (prefixWord ++ tailWord_5598213).sum := by decide
  have hdescent : baseEnd_5598213 < baseStart_5598213 := by decide
  rcases family_descends (prefixWord ++ tailWord_5598213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5598247 : List Nat := [1, 1, 7, 1, 1, 2, 1, 1, 4, 1, 3]
def baseStart_5598247 : Nat := 118140960795 + 5598247 * 2 ^ 59
def prefixEnd_5598247 : Nat := 4983230072969 + 3 ^ 40 * 5598247 * 2
def baseEnd_5598247 : Nat := 2874591533590863566566637

theorem tailTrace_5598247 : CollatzResearch.WordTrace tailWord_5598247 prefixEnd_5598247 2874591533590863566566637 := by
  unfold tailWord_5598247
  simp only [CollatzResearch.WordTrace]
  refine ⟨204184842549514698313344995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136123228366343132208896663 204184842549514698313344995)
  ·
    refine ⟨306277263824272047470017493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204184842549514698313344995 306277263824272047470017493)
    ·
      refine ⟨7178373370881376112578535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 306277263824272047470017493 7178373370881376112578535)
      ·
        refine ⟨10767560056322064168867803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7178373370881376112578535 10767560056322064168867803)
        ·
          refine ⟨16151340084483096253301705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10767560056322064168867803 16151340084483096253301705)
          ·
            refine ⟨12113505063362322189976279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16151340084483096253301705 12113505063362322189976279)
            ·
              refine ⟨18170257595043483284964419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12113505063362322189976279 18170257595043483284964419)
              ·
                refine ⟨27255386392565224927446629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18170257595043483284964419 27255386392565224927446629)
                ·
                  refine ⟨5110384948605979673896243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27255386392565224927446629 5110384948605979673896243)
                  ·
                    refine ⟨7665577422908969510844365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5110384948605979673896243 7665577422908969510844365)
                    ·
                      refine ⟨2874591533590863566566637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7665577422908969510844365 2874591533590863566566637)
                      ·
                        rfl

theorem cell23_5598247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_5598247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5598247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5598247 prefixEnd_5598247 := by exact prefixLift 5598247
  have htrace : WordTrace (prefixWord ++ tailWord_5598247) baseStart_5598247 baseEnd_5598247 := by
    simpa [prefixWord, tailWord_5598247, baseEnd_5598247] using wordTrace_append hprefix tailTrace_5598247
  have hstable : (prefixWord ++ tailWord_5598247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5598247).length < 2 ^ (prefixWord ++ tailWord_5598247).sum := by decide
  have hdescent : baseEnd_5598247 < baseStart_5598247 := by decide
  rcases family_descends (prefixWord ++ tailWord_5598247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5598336 : List Nat := [2, 1, 1, 2, 1, 3, 2, 1, 2, 8]
def baseStart_5598336 : Nat := 118140960795 + 5598336 * 2 ^ 59
def prefixEnd_5598336 : Nat := 4983230072969 + 3 ^ 40 * 5598336 * 2
def baseEnd_5598336 : Nat := 958212411123037906117909

theorem tailTrace_5598336 : CollatzResearch.WordTrace tailWord_5598336 prefixEnd_5598336 958212411123037906117909 := by
  unfold tailWord_5598336
  simp only [CollatzResearch.WordTrace]
  refine ⟨102094044323096133256667431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136125392430794844342223241 102094044323096133256667431)
  ·
    refine ⟨153141066484644199885001147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102094044323096133256667431 153141066484644199885001147)
    ·
      refine ⟨229711599726966299827501721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153141066484644199885001147 229711599726966299827501721)
      ·
        refine ⟨172283699795224724870626291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 229711599726966299827501721 172283699795224724870626291)
        ·
          refine ⟨258425549692837087305939437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172283699795224724870626291 258425549692837087305939437)
          ·
            refine ⟨96909581134813907739727289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 258425549692837087305939437 96909581134813907739727289)
            ·
              refine ⟨72682185851110430804795467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96909581134813907739727289 72682185851110430804795467)
              ·
                refine ⟨109023278776665646207193201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72682185851110430804795467 109023278776665646207193201)
                ·
                  refine ⟨81767459082499234655394901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 109023278776665646207193201 81767459082499234655394901)
                  ·
                    refine ⟨958212411123037906117909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 81767459082499234655394901 958212411123037906117909)
                    ·
                      rfl

theorem cell23_5598336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 2, 8].length) (baseStart_5598336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5598336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5598336 prefixEnd_5598336 := by exact prefixLift 5598336
  have htrace : WordTrace (prefixWord ++ tailWord_5598336) baseStart_5598336 baseEnd_5598336 := by
    simpa [prefixWord, tailWord_5598336, baseEnd_5598336] using wordTrace_append hprefix tailTrace_5598336
  have hstable : (prefixWord ++ tailWord_5598336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5598336).length < 2 ^ (prefixWord ++ tailWord_5598336).sum := by decide
  have hdescent : baseEnd_5598336 < baseStart_5598336 := by decide
  rcases family_descends (prefixWord ++ tailWord_5598336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5598340 : List Nat := [2, 3, 2, 1, 2, 3, 2, 1, 2, 5]
def baseStart_5598340 : Nat := 118140960795 + 5598340 * 2 ^ 59
def prefixEnd_5598340 : Nat := 4983230072969 + 3 ^ 40 * 5598340 * 2
def baseEnd_5598340 : Nat := 958213095763910567567903

theorem tailTrace_5598340 : CollatzResearch.WordTrace tailWord_5598340 prefixEnd_5598340 958213095763910567567903 := by
  unfold tailWord_5598340
  simp only [CollatzResearch.WordTrace]
  refine ⟨102094117269088887598240237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136125489692118516797653649 102094117269088887598240237)
  ·
    refine ⟨38285293975908332849340089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102094117269088887598240237 38285293975908332849340089)
    ·
      refine ⟨28713970481931249637005067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38285293975908332849340089 28713970481931249637005067)
      ·
        refine ⟨43070955722896874455507601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28713970481931249637005067 43070955722896874455507601)
        ·
          refine ⟨32303216792172655841630701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43070955722896874455507601 32303216792172655841630701)
          ·
            refine ⟨12113706297064745940611513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32303216792172655841630701 12113706297064745940611513)
            ·
              refine ⟨9085279722798559455458635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12113706297064745940611513 9085279722798559455458635)
              ·
                refine ⟨13627919584197839183187953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9085279722798559455458635 13627919584197839183187953)
                ·
                  refine ⟨10220939688148379387390965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13627919584197839183187953 10220939688148379387390965)
                  ·
                    refine ⟨958213095763910567567903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10220939688148379387390965 958213095763910567567903)
                    ·
                      rfl

theorem cell23_5598340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 5].length) (baseStart_5598340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5598340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5598340 prefixEnd_5598340 := by exact prefixLift 5598340
  have htrace : WordTrace (prefixWord ++ tailWord_5598340) baseStart_5598340 baseEnd_5598340 := by
    simpa [prefixWord, tailWord_5598340, baseEnd_5598340] using wordTrace_append hprefix tailTrace_5598340
  have hstable : (prefixWord ++ tailWord_5598340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5598340).length < 2 ^ (prefixWord ++ tailWord_5598340).sum := by decide
  have hdescent : baseEnd_5598340 < baseStart_5598340 := by decide
  rcases family_descends (prefixWord ++ tailWord_5598340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5598360 : List Nat := [2, 1, 2, 4, 2, 1, 2, 2, 2, 1, 4]
def baseStart_5598360 : Nat := 118140960795 + 5598360 * 2 ^ 59
def prefixEnd_5598360 : Nat := 4983230072969 + 3 ^ 40 * 5598360 * 2
def baseEnd_5598360 : Nat := 2874649556904821624453617

theorem tailTrace_5598360 : CollatzResearch.WordTrace tailWord_5598360 prefixEnd_5598360 2874649556904821624453617 := by
  unfold tailWord_5598360
  simp only [CollatzResearch.WordTrace]
  refine ⟨102094481999052659306104267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136125975998736879074805689 102094481999052659306104267)
  ·
    refine ⟨153141722998578988959156401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102094481999052659306104267 153141722998578988959156401)
    ·
      refine ⟨114856292248934241719367301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153141722998578988959156401 114856292248934241719367301)
      ·
        refine ⟨21535554796675170322381369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 114856292248934241719367301 21535554796675170322381369)
        ·
          refine ⟨16151666097506377741786027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21535554796675170322381369 16151666097506377741786027)
          ·
            refine ⟨24227499146259566612679041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16151666097506377741786027 24227499146259566612679041)
            ·
              refine ⟨18170624359694674959509281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24227499146259566612679041 18170624359694674959509281)
              ·
                refine ⟨13627968269771006219631961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18170624359694674959509281 13627968269771006219631961)
                ·
                  refine ⟨10220976202328254664723971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13627968269771006219631961 10220976202328254664723971)
                  ·
                    refine ⟨15331464303492381997085957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10220976202328254664723971 15331464303492381997085957)
                    ·
                      refine ⟨2874649556904821624453617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15331464303492381997085957 2874649556904821624453617)
                      ·
                        rfl

theorem cell23_5598360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_5598360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5598360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5598360 prefixEnd_5598360 := by exact prefixLift 5598360
  have htrace : WordTrace (prefixWord ++ tailWord_5598360) baseStart_5598360 baseEnd_5598360 := by
    simpa [prefixWord, tailWord_5598360, baseEnd_5598360] using wordTrace_append hprefix tailTrace_5598360
  have hstable : (prefixWord ++ tailWord_5598360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5598360).length < 2 ^ (prefixWord ++ tailWord_5598360).sum := by decide
  have hdescent : baseEnd_5598360 < baseStart_5598360 := by decide
  rcases family_descends (prefixWord ++ tailWord_5598360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5598383 : List Nat := [1, 1, 2, 1, 2, 3, 4, 3, 6]
def baseStart_5598383 : Nat := 118140960795 + 5598383 * 2 ^ 59
def prefixEnd_5598383 : Nat := 4983230072969 + 3 ^ 40 * 5598383 * 2
def baseEnd_5598383 : Nat := 319406818551097226051779

theorem tailTrace_5598383 : CollatzResearch.WordTrace tailWord_5598383 prefixEnd_5598383 319406818551097226051779 := by
  unfold tailWord_5598383
  simp only [CollatzResearch.WordTrace]
  refine ⟨204189802877021993540295803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136126535251347995693530535 204189802877021993540295803)
  ·
    refine ⟨306284704315532990310443705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204189802877021993540295803 306284704315532990310443705)
    ·
      refine ⟨229713528236649742732832779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 306284704315532990310443705 229713528236649742732832779)
      ·
        refine ⟨344570292354974614099249169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229713528236649742732832779 344570292354974614099249169)
        ·
          refine ⟨258427719266230960574436877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 344570292354974614099249169 258427719266230960574436877)
          ·
            refine ⟨96910394724836610215413829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 258427719266230960574436877 96910394724836610215413829)
            ·
              refine ⟨18170699010906864415390093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 96910394724836610215413829 18170699010906864415390093)
              ·
                refine ⟨6814012129090074155771285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18170699010906864415390093 6814012129090074155771285)
                ·
                  refine ⟨319406818551097226051779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6814012129090074155771285 319406818551097226051779)
                  ·
                    rfl

theorem cell23_5598383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 3, 6].length) (baseStart_5598383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5598383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5598383 prefixEnd_5598383 := by exact prefixLift 5598383
  have htrace : WordTrace (prefixWord ++ tailWord_5598383) baseStart_5598383 baseEnd_5598383 := by
    simpa [prefixWord, tailWord_5598383, baseEnd_5598383] using wordTrace_append hprefix tailTrace_5598383
  have hstable : (prefixWord ++ tailWord_5598383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5598383).length < 2 ^ (prefixWord ++ tailWord_5598383).sum := by decide
  have hdescent : baseEnd_5598383 < baseStart_5598383 := by decide
  rcases family_descends (prefixWord ++ tailWord_5598383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5598447 : List Nat := [1, 1, 2, 1, 7, 1, 2, 2, 1, 5]
def baseStart_5598447 : Nat := 118140960795 + 5598447 * 2 ^ 59
def prefixEnd_5598447 : Nat := 4983230072969 + 3 ^ 40 * 5598447 * 2
def baseEnd_5598447 : Nat := 958231409907254261355239

theorem tailTrace_5598447 : CollatzResearch.WordTrace tailWord_5598447 prefixEnd_5598447 958231409907254261355239 := by
  unfold tailWord_5598447
  simp only [CollatzResearch.WordTrace]
  refine ⟨204192137148790132470625595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136128091432526754980417063 204192137148790132470625595)
  ·
    refine ⟨306288205723185198705938393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204192137148790132470625595 306288205723185198705938393)
    ·
      refine ⟨229716154292388899029453795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 306288205723185198705938393 229716154292388899029453795)
      ·
        refine ⟨344574231438583348544180693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229716154292388899029453795 344574231438583348544180693)
        ·
          refine ⟨8075958549341797231504235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 344574231438583348544180693 8075958549341797231504235)
          ·
            refine ⟨12113937824012695847256353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8075958549341797231504235 12113937824012695847256353)
            ·
              refine ⟨9085453368009521885442265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12113937824012695847256353 9085453368009521885442265)
              ·
                refine ⟨6814090026007141414081699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9085453368009521885442265 6814090026007141414081699)
                ·
                  refine ⟨10221135039010712121122549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6814090026007141414081699 10221135039010712121122549)
                  ·
                    refine ⟨958231409907254261355239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10221135039010712121122549 958231409907254261355239)
                    ·
                      rfl

theorem cell23_5598447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 2, 2, 1, 5].length) (baseStart_5598447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5598447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5598447 prefixEnd_5598447 := by exact prefixLift 5598447
  have htrace : WordTrace (prefixWord ++ tailWord_5598447) baseStart_5598447 baseEnd_5598447 := by
    simpa [prefixWord, tailWord_5598447, baseEnd_5598447] using wordTrace_append hprefix tailTrace_5598447
  have hstable : (prefixWord ++ tailWord_5598447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5598447).length < 2 ^ (prefixWord ++ tailWord_5598447).sum := by decide
  have hdescent : baseEnd_5598447 < baseStart_5598447 := by decide
  rcases family_descends (prefixWord ++ tailWord_5598447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5598490 : List Nat := [3, 1, 1, 3, 3, 2, 2, 8]
def baseStart_5598490 : Nat := 118140960795 + 5598490 * 2 ^ 59
def prefixEnd_5598490 : Nat := 4983230072969 + 3 ^ 40 * 5598490 * 2
def baseEnd_5598490 : Nat := 106470974421848374660297

theorem tailTrace_5598490 : CollatzResearch.WordTrace tailWord_5598490 prefixEnd_5598490 106470974421848374660297 := by
  unfold tailWord_5598490
  simp only [CollatzResearch.WordTrace]
  refine ⟨51048426371908587703610231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136129136991756233876293949 51048426371908587703610231)
  ·
    refine ⟨76572639557862881555415347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51048426371908587703610231 76572639557862881555415347)
    ·
      refine ⟨114858959336794322333123021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76572639557862881555415347 114858959336794322333123021)
      ·
        refine ⟨43072109751297870874921133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114858959336794322333123021 43072109751297870874921133)
        ·
          refine ⟨16152041156736701578095425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43072109751297870874921133 16152041156736701578095425)
          ·
            refine ⟨12114030867552526183571569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16152041156736701578095425 12114030867552526183571569)
            ·
              refine ⟨9085523150664394637678677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12114030867552526183571569 9085523150664394637678677)
              ·
                refine ⟨106470974421848374660297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9085523150664394637678677 106470974421848374660297)
                ·
                  rfl

theorem cell23_5598490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2, 8].length) (baseStart_5598490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5598490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5598490 prefixEnd_5598490 := by exact prefixLift 5598490
  have htrace : WordTrace (prefixWord ++ tailWord_5598490) baseStart_5598490 baseEnd_5598490 := by
    simpa [prefixWord, tailWord_5598490, baseEnd_5598490] using wordTrace_append hprefix tailTrace_5598490
  have hstable : (prefixWord ++ tailWord_5598490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5598490).length < 2 ^ (prefixWord ++ tailWord_5598490).sum := by decide
  have hdescent : baseEnd_5598490 < baseStart_5598490 := by decide
  rcases family_descends (prefixWord ++ tailWord_5598490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5598504 : List Nat := [2, 1, 5, 1, 2, 1, 3, 2, 1, 2, 3]
def baseStart_5598504 : Nat := 118140960795 + 5598504 * 2 ^ 59
def prefixEnd_5598504 : Nat := 4983230072969 + 3 ^ 40 * 5598504 * 2
def baseEnd_5598504 : Nat := 2874723498119069061052955

theorem tailTrace_5598504 : CollatzResearch.WordTrace tailWord_5598504 prefixEnd_5598504 2874723498119069061052955 := by
  unfold tailWord_5598504
  simp only [CollatzResearch.WordTrace]
  refine ⟨102097108054791815602725283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136129477406389087470300377 102097108054791815602725283)
  ·
    refine ⟨153145662082187723404087925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102097108054791815602725283 153145662082187723404087925)
    ·
      refine ⟨14357405820205099069133243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 153145662082187723404087925 14357405820205099069133243)
      ·
        refine ⟨21536108730307648603699865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14357405820205099069133243 21536108730307648603699865)
        ·
          refine ⟨16152081547730736452774899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21536108730307648603699865 16152081547730736452774899)
          ·
            refine ⟨24228122321596104679162349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16152081547730736452774899 24228122321596104679162349)
            ·
              refine ⟨9085545870598539254685881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24228122321596104679162349 9085545870598539254685881)
              ·
                refine ⟨6814159402948904441014411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9085545870598539254685881 6814159402948904441014411)
                ·
                  refine ⟨10221239104423356661521617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6814159402948904441014411 10221239104423356661521617)
                  ·
                    refine ⟨7665929328317517496141213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10221239104423356661521617 7665929328317517496141213)
                    ·
                      refine ⟨2874723498119069061052955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7665929328317517496141213 2874723498119069061052955)
                      ·
                        rfl

theorem cell23_5598504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3, 2, 1, 2, 3].length) (baseStart_5598504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5598504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5598504 prefixEnd_5598504 := by exact prefixLift 5598504
  have htrace : WordTrace (prefixWord ++ tailWord_5598504) baseStart_5598504 baseEnd_5598504 := by
    simpa [prefixWord, tailWord_5598504, baseEnd_5598504] using wordTrace_append hprefix tailTrace_5598504
  have hstable : (prefixWord ++ tailWord_5598504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5598504).length < 2 ^ (prefixWord ++ tailWord_5598504).sum := by decide
  have hdescent : baseEnd_5598504 < baseStart_5598504 := by decide
  rcases family_descends (prefixWord ++ tailWord_5598504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5598517 : List Nat := [1, 3, 3, 1, 2, 3, 1, 2, 1, 3, 3]
def baseStart_5598517 : Nat := 118140960795 + 5598517 * 2 ^ 59
def prefixEnd_5598517 : Nat := 4983230072969 + 3 ^ 40 * 5598517 * 2
def baseEnd_5598517 : Nat := 2874730173367577510190395

theorem tailTrace_5598517 : CollatzResearch.WordTrace tailWord_5598517 prefixEnd_5598517 2874730173367577510190395 := by
  unfold tailWord_5598517
  simp only [CollatzResearch.WordTrace]
  refine ⟨204194690258536534425673805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136129793505691022950449203 204194690258536534425673805)
  ·
    refine ⟨76573008846951200409627677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 204194690258536534425673805 76573008846951200409627677)
    ·
      refine ⟨28714878317606700153610379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76573008846951200409627677 28714878317606700153610379)
      ·
        refine ⟨43072317476410050230415569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28714878317606700153610379 43072317476410050230415569)
        ·
          refine ⟨32304238107307537672811677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43072317476410050230415569 32304238107307537672811677)
          ·
            refine ⟨12114089290240326627304379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32304238107307537672811677 12114089290240326627304379)
            ·
              refine ⟨18171133935360489940956569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12114089290240326627304379 18171133935360489940956569)
              ·
                refine ⟨13628350451520367455717427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18171133935360489940956569 13628350451520367455717427)
                ·
                  refine ⟨20442525677280551183576141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13628350451520367455717427 20442525677280551183576141)
                  ·
                    refine ⟨7665947128980206693841053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20442525677280551183576141 7665947128980206693841053)
                    ·
                      refine ⟨2874730173367577510190395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7665947128980206693841053 2874730173367577510190395)
                      ·
                        rfl

theorem cell23_5598517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 2, 1, 3, 3].length) (baseStart_5598517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5598517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5598517 prefixEnd_5598517 := by exact prefixLift 5598517
  have htrace : WordTrace (prefixWord ++ tailWord_5598517) baseStart_5598517 baseEnd_5598517 := by
    simpa [prefixWord, tailWord_5598517, baseEnd_5598517] using wordTrace_append hprefix tailTrace_5598517
  have hstable : (prefixWord ++ tailWord_5598517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5598517).length < 2 ^ (prefixWord ++ tailWord_5598517).sum := by decide
  have hdescent : baseEnd_5598517 < baseStart_5598517 := by decide
  rcases family_descends (prefixWord ++ tailWord_5598517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5598518 : List Nat := [5, 1, 2, 3, 1, 1, 3, 1, 1, 1, 4]
def baseStart_5598518 : Nat := 118140960795 + 5598518 * 2 ^ 59
def prefixEnd_5598518 : Nat := 4983230072969 + 3 ^ 40 * 5598518 * 2
def baseEnd_5598518 : Nat := 2874730686848232006277891

theorem tailTrace_5598518 : CollatzResearch.WordTrace tailWord_5598518 prefixEnd_5598518 2874730686848232006277891 := by
  unfold tailWord_5598518
  simp only [CollatzResearch.WordTrace]
  refine ⟨12762170420720806974778763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 136129817821021941064306805 12762170420720806974778763)
  ·
    refine ⟨19143255631081210462168145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12762170420720806974778763 19143255631081210462168145)
    ·
      refine ⟨14357441723310907846626109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19143255631081210462168145 14357441723310907846626109)
      ·
        refine ⟨5384040646241590442484791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14357441723310907846626109 5384040646241590442484791)
        ·
          refine ⟨8076060969362385663727187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5384040646241590442484791 8076060969362385663727187)
          ·
            refine ⟨12114091454043578495590781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8076060969362385663727187 12114091454043578495590781)
            ·
              refine ⟨4542784295266341935846543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12114091454043578495590781 4542784295266341935846543)
              ·
                refine ⟨6814176442899512903769815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4542784295266341935846543 6814176442899512903769815)
                ·
                  refine ⟨10221264664349269355654723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6814176442899512903769815 10221264664349269355654723)
                  ·
                    refine ⟨15331896996523904033482085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10221264664349269355654723 15331896996523904033482085)
                    ·
                      refine ⟨2874730686848232006277891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15331896996523904033482085 2874730686848232006277891)
                      ·
                        rfl

theorem cell23_5598518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_5598518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5598518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5598518 prefixEnd_5598518 := by exact prefixLift 5598518
  have htrace : WordTrace (prefixWord ++ tailWord_5598518) baseStart_5598518 baseEnd_5598518 := by
    simpa [prefixWord, tailWord_5598518, baseEnd_5598518] using wordTrace_append hprefix tailTrace_5598518
  have hstable : (prefixWord ++ tailWord_5598518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5598518).length < 2 ^ (prefixWord ++ tailWord_5598518).sum := by decide
  have hdescent : baseEnd_5598518 < baseStart_5598518 := by decide
  rcases family_descends (prefixWord ++ tailWord_5598518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5598521 : List Nat := [1, 2, 1, 6, 2, 1, 3, 1, 1, 2, 3]
def baseStart_5598521 : Nat := 118140960795 + 5598521 * 2 ^ 59
def prefixEnd_5598521 : Nat := 4983230072969 + 3 ^ 40 * 5598521 * 2
def baseEnd_5598521 : Nat := 2874732227290195494540377

theorem tailTrace_5598521 : CollatzResearch.WordTrace tailWord_5598521 prefixEnd_5598521 2874732227290195494540377 := by
  unfold tailWord_5598521
  simp only [CollatzResearch.WordTrace]
  refine ⟨204194836150522043108819417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136129890767014695405879611 204194836150522043108819417)
  ·
    refine ⟨153146127112891532331614563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204194836150522043108819417 153146127112891532331614563)
    ·
      refine ⟨229719190669337298497421845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153146127112891532331614563 229719190669337298497421845)
      ·
        refine ⟨10768087062625185867066649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 229719190669337298497421845 10768087062625185867066649)
        ·
          refine ⟨8076065296968889400299987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10768087062625185867066649 8076065296968889400299987)
          ·
            refine ⟨12114097945453334100449981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8076065296968889400299987 12114097945453334100449981)
            ·
              refine ⟨4542786729545000287668743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12114097945453334100449981 4542786729545000287668743)
              ·
                refine ⟨6814180094317500431503115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4542786729545000287668743 6814180094317500431503115)
                ·
                  refine ⟨10221270141476250647254673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6814180094317500431503115 10221270141476250647254673)
                  ·
                    refine ⟨7665952606107187985441005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10221270141476250647254673 7665952606107187985441005)
                    ·
                      refine ⟨2874732227290195494540377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7665952606107187985441005 2874732227290195494540377)
                      ·
                        rfl

theorem cell23_5598521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 3, 1, 1, 2, 3].length) (baseStart_5598521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5598521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5598521 prefixEnd_5598521 := by exact prefixLift 5598521
  have htrace : WordTrace (prefixWord ++ tailWord_5598521) baseStart_5598521 baseEnd_5598521 := by
    simpa [prefixWord, tailWord_5598521, baseEnd_5598521] using wordTrace_append hprefix tailTrace_5598521
  have hstable : (prefixWord ++ tailWord_5598521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5598521).length < 2 ^ (prefixWord ++ tailWord_5598521).sum := by decide
  have hdescent : baseEnd_5598521 < baseStart_5598521 := by decide
  rcases family_descends (prefixWord ++ tailWord_5598521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5598533 : List Nat := [1, 3, 1, 1, 1, 2, 1, 2, 3, 8]
def baseStart_5598533 : Nat := 118140960795 + 5598533 * 2 ^ 59
def prefixEnd_5598533 : Nat := 4983230072969 + 3 ^ 40 * 5598533 * 2
def baseEnd_5598533 : Nat := 958246129686016482530107

theorem tailTrace_5598533 : CollatzResearch.WordTrace tailWord_5598533 prefixEnd_5598533 958246129686016482530107 := by
  unfold tailWord_5598533
  simp only [CollatzResearch.WordTrace]
  refine ⟨204195273826478569158256253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136130182550985712772170835 204195273826478569158256253)
  ·
    refine ⟨76573227684929463434346095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 204195273826478569158256253 76573227684929463434346095)
    ·
      refine ⟨114859841527394195151519143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76573227684929463434346095 114859841527394195151519143)
      ·
        refine ⟨172289762291091292727278715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114859841527394195151519143 172289762291091292727278715)
        ·
          refine ⟨258434643436636939090918073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172289762291091292727278715 258434643436636939090918073)
          ·
            refine ⟨193825982577477704318188555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 258434643436636939090918073 193825982577477704318188555)
            ·
              refine ⟨290738973866216556477282833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 193825982577477704318188555 290738973866216556477282833)
              ·
                refine ⟨218054230399662417357962125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 290738973866216556477282833 218054230399662417357962125)
                ·
                  refine ⟨81770336399873406509235797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 218054230399662417357962125 81770336399873406509235797)
                  ·
                    refine ⟨958246129686016482530107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 81770336399873406509235797 958246129686016482530107)
                    ·
                      rfl

theorem cell23_5598533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 3, 8].length) (baseStart_5598533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5598533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5598533 prefixEnd_5598533 := by exact prefixLift 5598533
  have htrace : WordTrace (prefixWord ++ tailWord_5598533) baseStart_5598533 baseEnd_5598533 := by
    simpa [prefixWord, tailWord_5598533, baseEnd_5598533] using wordTrace_append hprefix tailTrace_5598533
  have hstable : (prefixWord ++ tailWord_5598533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5598533).length < 2 ^ (prefixWord ++ tailWord_5598533).sum := by decide
  have hdescent : baseEnd_5598533 < baseStart_5598533 := by decide
  rcases family_descends (prefixWord ++ tailWord_5598533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5598540 : List Nat := [2, 2, 1, 3, 2, 2, 1, 1, 2, 3, 4]
def baseStart_5598540 : Nat := 118140960795 + 5598540 * 2 ^ 59
def prefixEnd_5598540 : Nat := 4983230072969 + 3 ^ 40 * 5598540 * 2
def baseEnd_5598540 : Nat := 2874741983422630920202789

theorem tailTrace_5598540 : CollatzResearch.WordTrace tailWord_5598540 prefixEnd_5598540 2874741983422630920202789 := by
  unfold tailWord_5598540
  simp only [CollatzResearch.WordTrace]
  refine ⟨102097764568726604676880537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136130352758302139569174049 102097764568726604676880537)
  ·
    refine ⟨76573323426544953507660403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102097764568726604676880537 76573323426544953507660403)
    ·
      refine ⟨114859985139817430261490605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76573323426544953507660403 114859985139817430261490605)
      ·
        refine ⟨43072494427431536348058977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114859985139817430261490605 43072494427431536348058977)
        ·
          refine ⟨32304370820573652261044233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43072494427431536348058977 32304370820573652261044233)
          ·
            refine ⟨24228278115430239195783175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32304370820573652261044233 24228278115430239195783175)
            ·
              refine ⟨36342417173145358793674763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24228278115430239195783175 36342417173145358793674763)
              ·
                refine ⟨54513625759718038190512145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36342417173145358793674763 54513625759718038190512145)
                ·
                  refine ⟨40885219319788528642884109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54513625759718038190512145 40885219319788528642884109)
                  ·
                    refine ⟨15331957244920698241081541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40885219319788528642884109 15331957244920698241081541)
                    ·
                      refine ⟨2874741983422630920202789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15331957244920698241081541 2874741983422630920202789)
                      ·
                        rfl

theorem cell23_5598540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 1, 2, 3, 4].length) (baseStart_5598540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5598540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5598540 prefixEnd_5598540 := by exact prefixLift 5598540
  have htrace : WordTrace (prefixWord ++ tailWord_5598540) baseStart_5598540 baseEnd_5598540 := by
    simpa [prefixWord, tailWord_5598540, baseEnd_5598540] using wordTrace_append hprefix tailTrace_5598540
  have hstable : (prefixWord ++ tailWord_5598540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5598540).length < 2 ^ (prefixWord ++ tailWord_5598540).sum := by decide
  have hdescent : baseEnd_5598540 < baseStart_5598540 := by decide
  rcases family_descends (prefixWord ++ tailWord_5598540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5598541 : List Nat := [1, 6, 1, 3, 2, 1, 1, 8]
def baseStart_5598541 : Nat := 118140960795 + 5598541 * 2 ^ 59
def prefixEnd_5598541 : Nat := 4983230072969 + 3 ^ 40 * 5598541 * 2
def baseEnd_5598541 : Nat := 106471944329751311714455

theorem tailTrace_5598541 : CollatzResearch.WordTrace tailWord_5598541 prefixEnd_5598541 106471944329751311714455 := by
  unfold tailWord_5598541
  simp only [CollatzResearch.WordTrace]
  refine ⟨204195565610449586524547477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136130377073633057683031651 204195565610449586524547477)
  ·
    refine ⟨9571667137989824368338163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 204195565610449586524547477 9571667137989824368338163)
    ·
      refine ⟨14357500706984736552507245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9571667137989824368338163 14357500706984736552507245)
      ·
        refine ⟨5384062765119276207190217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14357500706984736552507245 5384062765119276207190217)
        ·
          refine ⟨4038047073839457155392663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5384062765119276207190217 4038047073839457155392663)
          ·
            refine ⟨6057070610759185733088995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4038047073839457155392663 6057070610759185733088995)
            ·
              refine ⟨9085605916138778599633493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6057070610759185733088995 9085605916138778599633493)
              ·
                refine ⟨106471944329751311714455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9085605916138778599633493 106471944329751311714455)
                ·
                  rfl

theorem cell23_5598541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 1, 8].length) (baseStart_5598541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5598541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5598541 prefixEnd_5598541 := by exact prefixLift 5598541
  have htrace : WordTrace (prefixWord ++ tailWord_5598541) baseStart_5598541 baseEnd_5598541 := by
    simpa [prefixWord, tailWord_5598541, baseEnd_5598541] using wordTrace_append hprefix tailTrace_5598541
  have hstable : (prefixWord ++ tailWord_5598541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5598541).length < 2 ^ (prefixWord ++ tailWord_5598541).sum := by decide
  have hdescent : baseEnd_5598541 < baseStart_5598541 := by decide
  rcases family_descends (prefixWord ++ tailWord_5598541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5598597 : List Nat := [1, 3, 1, 1, 3, 1, 4, 4, 5]
def baseStart_5598597 : Nat := 118140960795 + 5598597 * 2 ^ 59
def prefixEnd_5598597 : Nat := 4983230072969 + 3 ^ 40 * 5598597 * 2
def baseEnd_5598597 : Nat := 319419027979993021910003

theorem tailTrace_5598597 : CollatzResearch.WordTrace tailWord_5598597 prefixEnd_5598597 319419027979993021910003 := by
  unfold tailWord_5598597
  simp only [CollatzResearch.WordTrace]
  refine ⟨204197608098246708088586045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136131738732164472059057363 204197608098246708088586045)
  ·
    refine ⟨76574103036842515533219767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 204197608098246708088586045 76574103036842515533219767)
    ·
      refine ⟨114861154555263773299829651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76574103036842515533219767 114861154555263773299829651)
      ·
        refine ⟨172291731832895659949744477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114861154555263773299829651 172291731832895659949744477)
        ·
          refine ⟨64609399437335872481154179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 172291731832895659949744477 64609399437335872481154179)
          ·
            refine ⟨96914099156003808721731269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64609399437335872481154179 96914099156003808721731269)
            ·
              refine ⟨18171393591750714135324613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 96914099156003808721731269 18171393591750714135324613)
              ·
                refine ⟨3407136298453258900373365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18171393591750714135324613 3407136298453258900373365)
                ·
                  refine ⟨319419027979993021910003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3407136298453258900373365 319419027979993021910003)
                  ·
                    rfl

theorem cell23_5598597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 4, 5].length) (baseStart_5598597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5598597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5598597 prefixEnd_5598597 := by exact prefixLift 5598597
  have htrace : WordTrace (prefixWord ++ tailWord_5598597) baseStart_5598597 baseEnd_5598597 := by
    simpa [prefixWord, tailWord_5598597, baseEnd_5598597] using wordTrace_append hprefix tailTrace_5598597
  have hstable : (prefixWord ++ tailWord_5598597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5598597).length < 2 ^ (prefixWord ++ tailWord_5598597).sum := by decide
  have hdescent : baseEnd_5598597 < baseStart_5598597 := by decide
  rcases family_descends (prefixWord ++ tailWord_5598597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5598647 : List Nat := [1, 1, 3, 1, 3, 2, 3, 2, 2, 1, 4]
def baseStart_5598647 : Nat := 118140960795 + 5598647 * 2 ^ 59
def prefixEnd_5598647 : Nat := 4983230072969 + 3 ^ 40 * 5598647 * 2
def baseEnd_5598647 : Nat := 2874796925852662001564797

theorem tailTrace_5598647 : CollatzResearch.WordTrace tailWord_5598647 prefixEnd_5598647 2874796925852662001564797 := by
  unfold tailWord_5598647
  simp only [CollatzResearch.WordTrace]
  refine ⟨204199431748065566627906195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136132954498710377751937463 204199431748065566627906195)
  ·
    refine ⟨306299147622098349941859293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204199431748065566627906195 306299147622098349941859293)
    ·
      refine ⟨114862180358286881228197235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 306299147622098349941859293 114862180358286881228197235)
      ·
        refine ⟨172293270537430321842295853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114862180358286881228197235 172293270537430321842295853)
        ·
          refine ⟨64609976451536370690860945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 172293270537430321842295853 64609976451536370690860945)
          ·
            refine ⟨48457482338652278018145709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64609976451536370690860945 48457482338652278018145709)
            ·
              refine ⟨18171555876994604256804641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48457482338652278018145709 18171555876994604256804641)
              ·
                refine ⟨13628666907745953192603481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18171555876994604256804641 13628666907745953192603481)
                ·
                  refine ⟨10221500180809464894452611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13628666907745953192603481 10221500180809464894452611)
                  ·
                    refine ⟨15332250271214197341678917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10221500180809464894452611 15332250271214197341678917)
                    ·
                      refine ⟨2874796925852662001564797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15332250271214197341678917 2874796925852662001564797)
                      ·
                        rfl

theorem cell23_5598647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 2, 1, 4].length) (baseStart_5598647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5598647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5598647 prefixEnd_5598647 := by exact prefixLift 5598647
  have htrace : WordTrace (prefixWord ++ tailWord_5598647) baseStart_5598647 baseEnd_5598647 := by
    simpa [prefixWord, tailWord_5598647, baseEnd_5598647] using wordTrace_append hprefix tailTrace_5598647
  have hstable : (prefixWord ++ tailWord_5598647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5598647).length < 2 ^ (prefixWord ++ tailWord_5598647).sum := by decide
  have hdescent : baseEnd_5598647 < baseStart_5598647 := by decide
  rcases family_descends (prefixWord ++ tailWord_5598647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5598714 : List Nat := [3, 1, 1, 1, 1, 2, 4, 3, 3, 1, 3]
def baseStart_5598714 : Nat := 118140960795 + 5598714 * 2 ^ 59
def prefixEnd_5598714 : Nat := 4983230072969 + 3 ^ 40 * 5598714 * 2
def baseEnd_5598714 : Nat := 2874831329056513239426989

theorem tailTrace_5598714 : CollatzResearch.WordTrace tailWord_5598714 prefixEnd_5598714 2874831329056513239426989 := by
  unfold tailWord_5598714
  simp only [CollatzResearch.WordTrace]
  refine ⟨51050468859705709267648799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136134583625881891380396797 51050468859705709267648799)
  ·
    refine ⟨76575703289558563901473199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51050468859705709267648799 76575703289558563901473199)
    ·
      refine ⟨114863554934337845852209799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76575703289558563901473199 114863554934337845852209799)
      ·
        refine ⟨172295332401506768778314699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114863554934337845852209799 172295332401506768778314699)
        ·
          refine ⟨258442998602260153167472049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172295332401506768778314699 258442998602260153167472049)
          ·
            refine ⟨193832248951695114875604037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 258442998602260153167472049 193832248951695114875604037)
            ·
              refine ⟨36343546678442834039175757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 193832248951695114875604037 36343546678442834039175757)
              ·
                refine ⟨13628830004416062764690909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36343546678442834039175757 13628830004416062764690909)
                ·
                  refine ⟨5110811251656023536759091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13628830004416062764690909 5110811251656023536759091)
                  ·
                    refine ⟨7666216877484035305138637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5110811251656023536759091 7666216877484035305138637)
                    ·
                      refine ⟨2874831329056513239426989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7666216877484035305138637 2874831329056513239426989)
                      ·
                        rfl

theorem cell23_5598714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 3, 3, 1, 3].length) (baseStart_5598714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5598714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5598714 prefixEnd_5598714 := by exact prefixLift 5598714
  have htrace : WordTrace (prefixWord ++ tailWord_5598714) baseStart_5598714 baseEnd_5598714 := by
    simpa [prefixWord, tailWord_5598714, baseEnd_5598714] using wordTrace_append hprefix tailTrace_5598714
  have hstable : (prefixWord ++ tailWord_5598714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5598714).length < 2 ^ (prefixWord ++ tailWord_5598714).sum := by decide
  have hdescent : baseEnd_5598714 < baseStart_5598714 := by decide
  rcases family_descends (prefixWord ++ tailWord_5598714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5598717 : List Nat := [1, 4, 1, 1, 1, 4, 1, 2, 3, 5]
def baseStart_5598717 : Nat := 118140960795 + 5598717 * 2 ^ 59
def prefixEnd_5598717 : Nat := 4983230072969 + 3 ^ 40 * 5598717 * 2
def baseEnd_5598717 : Nat := 958277623166158909229825

theorem tailTrace_5598717 : CollatzResearch.WordTrace tailWord_5598717 prefixEnd_5598717 958277623166158909229825 := by
  unfold tailWord_5598717
  simp only [CollatzResearch.WordTrace]
  refine ⟨204201984857811968582954405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136134656571874645721969603 204201984857811968582954405)
  ·
    refine ⟨38287872160839744109303951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 204201984857811968582954405 38287872160839744109303951)
    ·
      refine ⟨57431808241259616163955927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38287872160839744109303951 57431808241259616163955927)
      ·
        refine ⟨86147712361889424245933891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57431808241259616163955927 86147712361889424245933891)
        ·
          refine ⟨129221568542834136368900837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86147712361889424245933891 129221568542834136368900837)
          ·
            refine ⟨24229044101781400569168907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 129221568542834136368900837 24229044101781400569168907)
            ·
              refine ⟨36343566152672100853753361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24229044101781400569168907 36343566152672100853753361)
              ·
                refine ⟨27257674614504075640315021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36343566152672100853753361 27257674614504075640315021)
                ·
                  refine ⟨10221627980439028365118133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27257674614504075640315021 10221627980439028365118133)
                  ·
                    refine ⟨958277623166158909229825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10221627980439028365118133 958277623166158909229825)
                    ·
                      rfl

theorem cell23_5598717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 2, 3, 5].length) (baseStart_5598717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5598717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5598717 prefixEnd_5598717 := by exact prefixLift 5598717
  have htrace : WordTrace (prefixWord ++ tailWord_5598717) baseStart_5598717 baseEnd_5598717 := by
    simpa [prefixWord, tailWord_5598717, baseEnd_5598717] using wordTrace_append hprefix tailTrace_5598717
  have hstable : (prefixWord ++ tailWord_5598717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5598717).length < 2 ^ (prefixWord ++ tailWord_5598717).sum := by decide
  have hdescent : baseEnd_5598717 < baseStart_5598717 := by decide
  rcases family_descends (prefixWord ++ tailWord_5598717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5598731 : List Nat := [1, 1, 1, 1, 8, 1, 1, 2, 3, 1, 3]
def baseStart_5598731 : Nat := 118140960795 + 5598731 * 2 ^ 59
def prefixEnd_5598731 : Nat := 4983230072969 + 3 ^ 40 * 5598731 * 2
def baseEnd_5598731 : Nat := 2874840058227639672914411

theorem tailTrace_5598731 : CollatzResearch.WordTrace tailWord_5598731 prefixEnd_5598731 2874840058227639672914411 := by
  unfold tailWord_5598731
  simp only [CollatzResearch.WordTrace]
  refine ⟨204202495479761248973964047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136134996986507499315976031 204202495479761248973964047)
  ·
    refine ⟨306303743219641873460946071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204202495479761248973964047 306303743219641873460946071)
    ·
      refine ⟨459455614829462810191419107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 306303743219641873460946071 459455614829462810191419107)
      ·
        refine ⟨689183422244194215287128661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 459455614829462810191419107 689183422244194215287128661)
        ·
          refine ⟨8076368229424150960396039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 689183422244194215287128661 8076368229424150960396039)
          ·
            refine ⟨12114552344136226440594059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8076368229424150960396039 12114552344136226440594059)
            ·
              refine ⟨18171828516204339660891089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12114552344136226440594059 18171828516204339660891089)
              ·
                refine ⟨13628871387153254745668317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18171828516204339660891089 13628871387153254745668317)
                ·
                  refine ⟨5110826770182470529625619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13628871387153254745668317 5110826770182470529625619)
                  ·
                    refine ⟨7666240155273705794438429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5110826770182470529625619 7666240155273705794438429)
                    ·
                      refine ⟨2874840058227639672914411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7666240155273705794438429 2874840058227639672914411)
                      ·
                        rfl

theorem cell23_5598731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 2, 3, 1, 3].length) (baseStart_5598731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5598731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5598731 prefixEnd_5598731 := by exact prefixLift 5598731
  have htrace : WordTrace (prefixWord ++ tailWord_5598731) baseStart_5598731 baseEnd_5598731 := by
    simpa [prefixWord, tailWord_5598731, baseEnd_5598731] using wordTrace_append hprefix tailTrace_5598731
  have hstable : (prefixWord ++ tailWord_5598731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5598731).length < 2 ^ (prefixWord ++ tailWord_5598731).sum := by decide
  have hdescent : baseEnd_5598731 < baseStart_5598731 := by decide
  rcases family_descends (prefixWord ++ tailWord_5598731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5598737 : List Nat := [1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 4]
def baseStart_5598737 : Nat := 118140960795 + 5598737 * 2 ^ 59
def prefixEnd_5598737 : Nat := 4983230072969 + 3 ^ 40 * 5598737 * 2
def baseEnd_5598737 : Nat := 2874843139111566649439383

theorem tailTrace_5598737 : CollatzResearch.WordTrace tailWord_5598737 prefixEnd_5598737 2874843139111566649439383 := by
  unfold tailWord_5598737
  simp only [CollatzResearch.WordTrace]
  refine ⟨204202714317739511998682465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136135142878493007999121643 204202714317739511998682465)
  ·
    refine ⟨153152035738304633999011849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204202714317739511998682465 153152035738304633999011849)
    ·
      refine ⟨114864026803728475499258887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153152035738304633999011849 114864026803728475499258887)
      ·
        refine ⟨172296040205592713248888331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114864026803728475499258887 172296040205592713248888331)
        ·
          refine ⟨258444060308389069873332497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172296040205592713248888331 258444060308389069873332497)
          ·
            refine ⟨193833045231291802404999373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 258444060308389069873332497 193833045231291802404999373)
            ·
              refine ⟨72687391961734425901874765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 193833045231291802404999373 72687391961734425901874765)
              ·
                refine ⟨27257771985650409713203037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72687391961734425901874765 27257771985650409713203037)
                ·
                  refine ⟨10221664494618903642451139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27257771985650409713203037 10221664494618903642451139)
                  ·
                    refine ⟨15332496741928355463676709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10221664494618903642451139 15332496741928355463676709)
                    ·
                      refine ⟨2874843139111566649439383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15332496741928355463676709 2874843139111566649439383)
                      ·
                        rfl

theorem cell23_5598737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 4].length) (baseStart_5598737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5598737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5598737 prefixEnd_5598737 := by exact prefixLift 5598737
  have htrace : WordTrace (prefixWord ++ tailWord_5598737) baseStart_5598737 baseEnd_5598737 := by
    simpa [prefixWord, tailWord_5598737, baseEnd_5598737] using wordTrace_append hprefix tailTrace_5598737
  have hstable : (prefixWord ++ tailWord_5598737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5598737).length < 2 ^ (prefixWord ++ tailWord_5598737).sum := by decide
  have hdescent : baseEnd_5598737 < baseStart_5598737 := by decide
  rcases family_descends (prefixWord ++ tailWord_5598737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5598741 : List Nat := [1, 3, 2, 1, 3, 2, 3, 1, 2, 3, 2]
def baseStart_5598741 : Nat := 118140960795 + 5598741 * 2 ^ 59
def prefixEnd_5598741 : Nat := 4983230072969 + 3 ^ 40 * 5598741 * 2
def baseEnd_5598741 : Nat := 2874845193034184633789365

theorem tailTrace_5598741 : CollatzResearch.WordTrace tailWord_5598741 prefixEnd_5598741 2874845193034184633789365 := by
  unfold tailWord_5598741
  simp only [CollatzResearch.WordTrace]
  refine ⟨204202860209725020681828077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136135240139816680454552051 204202860209725020681828077)
  ·
    refine ⟨76576072578646882755685529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 204202860209725020681828077 76576072578646882755685529)
    ·
      refine ⟨57432054433985162066764147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76576072578646882755685529 57432054433985162066764147)
      ·
        refine ⟨86148081650977743100146221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57432054433985162066764147 86148081650977743100146221)
        ·
          refine ⟨32305530619116653662554833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86148081650977743100146221 32305530619116653662554833)
          ·
            refine ⟨24229147964337490246916125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32305530619116653662554833 24229147964337490246916125)
            ·
              refine ⟨9085930486626558842593547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24229147964337490246916125 9085930486626558842593547)
              ·
                refine ⟨13628895729939838263890321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9085930486626558842593547 13628895729939838263890321)
                ·
                  refine ⟨10221671797454878697917741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13628895729939838263890321 10221671797454878697917741)
                  ·
                    refine ⟨3833126924045579511719153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10221671797454878697917741 3833126924045579511719153)
                    ·
                      refine ⟨2874845193034184633789365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3833126924045579511719153 2874845193034184633789365)
                      ·
                        rfl

theorem cell23_5598741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3, 1, 2, 3, 2].length) (baseStart_5598741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5598741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5598741 prefixEnd_5598741 := by exact prefixLift 5598741
  have htrace : WordTrace (prefixWord ++ tailWord_5598741) baseStart_5598741 baseEnd_5598741 := by
    simpa [prefixWord, tailWord_5598741, baseEnd_5598741] using wordTrace_append hprefix tailTrace_5598741
  have hstable : (prefixWord ++ tailWord_5598741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5598741).length < 2 ^ (prefixWord ++ tailWord_5598741).sum := by decide
  have hdescent : baseEnd_5598741 < baseStart_5598741 := by decide
  rcases family_descends (prefixWord ++ tailWord_5598741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5598748 : List Nat := [2, 2, 3, 1, 2, 1, 4, 3, 1, 1, 3]
def baseStart_5598748 : Nat := 118140960795 + 5598748 * 2 ^ 59
def prefixEnd_5598748 : Nat := 4983230072969 + 3 ^ 40 * 5598748 * 2
def baseEnd_5598748 : Nat := 2874848787398766106401833

theorem tailTrace_5598748 : CollatzResearch.WordTrace tailWord_5598748 prefixEnd_5598748 2874848787398766106401833 := by
  unfold tailWord_5598748
  simp only [CollatzResearch.WordTrace]
  refine ⟨102101557760349830438666449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136135410347133107251555265 102101557760349830438666449)
  ·
    refine ⟨76576168320262372828999837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102101557760349830438666449 76576168320262372828999837)
    ·
      refine ⟨28716063120098389810874939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76576168320262372828999837 28716063120098389810874939)
      ·
        refine ⟨43074094680147584716312409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28716063120098389810874939 43074094680147584716312409)
        ·
          refine ⟨32305571010110688537234307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43074094680147584716312409 32305571010110688537234307)
          ·
            refine ⟨48458356515166032805851461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32305571010110688537234307 48458356515166032805851461)
            ·
              refine ⟨9085941846593631151097149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48458356515166032805851461 9085941846593631151097149)
              ·
                refine ⟨3407228192472611681661431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9085941846593631151097149 3407228192472611681661431)
                ·
                  refine ⟨5110842288708917522492147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3407228192472611681661431 5110842288708917522492147)
                  ·
                    refine ⟨7666263433063376283738221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5110842288708917522492147 7666263433063376283738221)
                    ·
                      refine ⟨2874848787398766106401833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7666263433063376283738221 2874848787398766106401833)
                      ·
                        rfl

theorem cell23_5598748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4, 3, 1, 1, 3].length) (baseStart_5598748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5598748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5598748 prefixEnd_5598748 := by exact prefixLift 5598748
  have htrace : WordTrace (prefixWord ++ tailWord_5598748) baseStart_5598748 baseEnd_5598748 := by
    simpa [prefixWord, tailWord_5598748, baseEnd_5598748] using wordTrace_append hprefix tailTrace_5598748
  have hstable : (prefixWord ++ tailWord_5598748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5598748).length < 2 ^ (prefixWord ++ tailWord_5598748).sum := by decide
  have hdescent : baseEnd_5598748 < baseStart_5598748 := by decide
  rcases family_descends (prefixWord ++ tailWord_5598748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5598757 : List Nat := [1, 3, 1, 2, 2, 1, 1, 5, 1, 1, 5]
def baseStart_5598757 : Nat := 118140960795 + 5598757 * 2 ^ 59
def prefixEnd_5598757 : Nat := 4983230072969 + 3 ^ 40 * 5598757 * 2
def baseEnd_5598757 : Nat := 2874853408724656571189291

theorem tailTrace_5598757 : CollatzResearch.WordTrace tailWord_5598757 prefixEnd_5598757 2874853408724656571189291 := by
  unfold tailWord_5598757
  simp only [CollatzResearch.WordTrace]
  refine ⟨204203443777667055414410525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136135629185111370276273683 204203443777667055414410525)
  ·
    refine ⟨76576291416625145780403947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 204203443777667055414410525 76576291416625145780403947)
    ·
      refine ⟨114864437124937718670605921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76576291416625145780403947 114864437124937718670605921)
      ·
        refine ⟨86148327843703289002954441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114864437124937718670605921 86148327843703289002954441)
        ·
          refine ⟨64611245882777466752215831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86148327843703289002954441 64611245882777466752215831)
          ·
            refine ⟨96916868824166200128323747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64611245882777466752215831 96916868824166200128323747)
            ·
              refine ⟨145375303236249300192485621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96916868824166200128323747 145375303236249300192485621)
              ·
                refine ⟨13628934678398371893045527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 145375303236249300192485621 13628934678398371893045527)
                ·
                  refine ⟨20443402017597557839568291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13628934678398371893045527 20443402017597557839568291)
                  ·
                    refine ⟨30665103026396336759352437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20443402017597557839568291 30665103026396336759352437)
                    ·
                      refine ⟨2874853408724656571189291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30665103026396336759352437 2874853408724656571189291)
                      ·
                        rfl

theorem cell23_5598757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 5, 1, 1, 5].length) (baseStart_5598757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5598757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5598757 prefixEnd_5598757 := by exact prefixLift 5598757
  have htrace : WordTrace (prefixWord ++ tailWord_5598757) baseStart_5598757 baseEnd_5598757 := by
    simpa [prefixWord, tailWord_5598757, baseEnd_5598757] using wordTrace_append hprefix tailTrace_5598757
  have hstable : (prefixWord ++ tailWord_5598757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5598757).length < 2 ^ (prefixWord ++ tailWord_5598757).sum := by decide
  have hdescent : baseEnd_5598757 < baseStart_5598757 := by decide
  rcases family_descends (prefixWord ++ tailWord_5598757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5598771 : List Nat := [1, 1, 1, 2, 4, 3, 1, 3, 3, 2, 2]
def baseStart_5598771 : Nat := 118140960795 + 5598771 * 2 ^ 59
def prefixEnd_5598771 : Nat := 4983230072969 + 3 ^ 40 * 5598771 * 2
def baseEnd_5598771 : Nat := 2874860597453819516414227

theorem tailTrace_5598771 : CollatzResearch.WordTrace tailWord_5598771 prefixEnd_5598771 2874860597453819516414227 := by
  unfold tailWord_5598771
  simp only [CollatzResearch.WordTrace]
  refine ⟨204203954399616335805420167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136135969599744223870280111 204203954399616335805420167)
  ·
    refine ⟨306305931599424503708130251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204203954399616335805420167 306305931599424503708130251)
    ·
      refine ⟨459458897399136755562195377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 306305931599424503708130251 459458897399136755562195377)
      ·
        refine ⟨344594173049352566671646533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 459458897399136755562195377 344594173049352566671646533)
        ·
          refine ⟨64611407446753606250933725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 344594173049352566671646533 64611407446753606250933725)
          ·
            refine ⟨24229277792532602344100147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64611407446753606250933725 24229277792532602344100147)
            ·
              refine ⟨36343916688798903516150221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24229277792532602344100147 36343916688798903516150221)
              ·
                refine ⟨13628968758299588818556333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36343916688798903516150221 13628968758299588818556333)
                ·
                  refine ⟨5110863284362345806958625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13628968758299588818556333 5110863284362345806958625)
                  ·
                    refine ⟨3833147463271759355218969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5110863284362345806958625 3833147463271759355218969)
                    ·
                      refine ⟨2874860597453819516414227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3833147463271759355218969 2874860597453819516414227)
                      ·
                        rfl

theorem cell23_5598771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 3, 3, 2, 2].length) (baseStart_5598771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5598771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5598771 prefixEnd_5598771 := by exact prefixLift 5598771
  have htrace : WordTrace (prefixWord ++ tailWord_5598771) baseStart_5598771 baseEnd_5598771 := by
    simpa [prefixWord, tailWord_5598771, baseEnd_5598771] using wordTrace_append hprefix tailTrace_5598771
  have hstable : (prefixWord ++ tailWord_5598771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5598771).length < 2 ^ (prefixWord ++ tailWord_5598771).sum := by decide
  have hdescent : baseEnd_5598771 < baseStart_5598771 := by decide
  rcases family_descends (prefixWord ++ tailWord_5598771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5598781 : List Nat := [1, 4, 1, 3, 3, 2, 1, 1, 1, 6]
def baseStart_5598781 : Nat := 118140960795 + 5598781 * 2 ^ 59
def prefixEnd_5598781 : Nat := 4983230072969 + 3 ^ 40 * 5598781 * 2
def baseEnd_5598781 : Nat := 958288577420121492429727

theorem tailTrace_5598781 : CollatzResearch.WordTrace tailWord_5598781 prefixEnd_5598781 958288577420121492429727 := by
  unfold tailWord_5598781
  simp only [CollatzResearch.WordTrace]
  refine ⟨204204319129580107513284197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136136212753053405008856131 204204319129580107513284197)
  ·
    refine ⟨38288309836796270158740787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 204204319129580107513284197 38288309836796270158740787)
    ·
      refine ⟨57432464755194405238111181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38288309836796270158740787 57432464755194405238111181)
      ·
        refine ⟨21537174283197901964291693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57432464755194405238111181 21537174283197901964291693)
        ·
          refine ⟨8076440356199213236609385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21537174283197901964291693 8076440356199213236609385)
          ·
            refine ⟨6057330267149409927457039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8076440356199213236609385 6057330267149409927457039)
            ·
              refine ⟨9085995400724114891185559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6057330267149409927457039 9085995400724114891185559)
              ·
                refine ⟨13628993101086172336778339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9085995400724114891185559 13628993101086172336778339)
                ·
                  refine ⟨20443489651629258505167509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13628993101086172336778339 20443489651629258505167509)
                  ·
                    refine ⟨958288577420121492429727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20443489651629258505167509 958288577420121492429727)
                    ·
                      rfl

theorem cell23_5598781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 1, 1, 1, 6].length) (baseStart_5598781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5598781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5598781 prefixEnd_5598781 := by exact prefixLift 5598781
  have htrace : WordTrace (prefixWord ++ tailWord_5598781) baseStart_5598781 baseEnd_5598781 := by
    simpa [prefixWord, tailWord_5598781, baseEnd_5598781] using wordTrace_append hprefix tailTrace_5598781
  have hstable : (prefixWord ++ tailWord_5598781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5598781).length < 2 ^ (prefixWord ++ tailWord_5598781).sum := by decide
  have hdescent : baseEnd_5598781 < baseStart_5598781 := by decide
  rcases family_descends (prefixWord ++ tailWord_5598781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5598804 : List Nat := [2, 4, 1, 1, 1, 2, 2, 1, 3, 3, 3]
def baseStart_5598804 : Nat := 118140960795 + 5598804 * 2 ^ 59
def prefixEnd_5598804 : Nat := 4983230072969 + 3 ^ 40 * 5598804 * 2
def baseEnd_5598804 : Nat := 2874877542315417887301575

theorem tailTrace_5598804 : CollatzResearch.WordTrace tailWord_5598804 prefixEnd_5598804 2874877542315417887301575 := by
  unfold tailWord_5598804
  simp only [CollatzResearch.WordTrace]
  refine ⟨102102579004248391220685733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136136772005664521627580977 102102579004248391220685733)
  ·
    refine ⟨19144233563296573353878575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102102579004248391220685733 19144233563296573353878575)
    ·
      refine ⟨28716350344944860030817863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19144233563296573353878575 28716350344944860030817863)
      ·
        refine ⟨43074525517417290046226795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28716350344944860030817863 43074525517417290046226795)
        ·
          refine ⟨64611788276125935069340193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43074525517417290046226795 64611788276125935069340193)
          ·
            refine ⟨48458841207094451302005145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64611788276125935069340193 48458841207094451302005145)
            ·
              refine ⟨36344130905320838476503859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48458841207094451302005145 36344130905320838476503859)
              ·
                refine ⟨54516196357981257714755789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36344130905320838476503859 54516196357981257714755789)
                ·
                  refine ⟨20443573634242971643033421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54516196357981257714755789 20443573634242971643033421)
                  ·
                    refine ⟨7666340112841114366137533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20443573634242971643033421 7666340112841114366137533)
                    ·
                      refine ⟨2874877542315417887301575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7666340112841114366137533 2874877542315417887301575)
                      ·
                        rfl

theorem cell23_5598804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 1, 3, 3, 3].length) (baseStart_5598804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5598804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5598804 prefixEnd_5598804 := by exact prefixLift 5598804
  have htrace : WordTrace (prefixWord ++ tailWord_5598804) baseStart_5598804 baseEnd_5598804 := by
    simpa [prefixWord, tailWord_5598804, baseEnd_5598804] using wordTrace_append hprefix tailTrace_5598804
  have hstable : (prefixWord ++ tailWord_5598804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5598804).length < 2 ^ (prefixWord ++ tailWord_5598804).sum := by decide
  have hdescent : baseEnd_5598804 < baseStart_5598804 := by decide
  rcases family_descends (prefixWord ++ tailWord_5598804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5598817 : List Nat := [1, 2, 3, 1, 1, 3, 1, 2, 2, 2, 5]
def baseStart_5598817 : Nat := 118140960795 + 5598817 * 2 ^ 59
def prefixEnd_5598817 : Nat := 4983230072969 + 3 ^ 40 * 5598817 * 2
def baseEnd_5598817 : Nat := 2874884217563926336439015

theorem tailTrace_5598817 : CollatzResearch.WordTrace tailWord_5598817 prefixEnd_5598817 2874884217563926336439015 := by
  unfold tailWord_5598817
  simp only [CollatzResearch.WordTrace]
  refine ⟨204205632157449685661594705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136137088104966457107729803 204205632157449685661594705)
  ·
    refine ⟨153154224118087264246196029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204205632157449685661594705 153154224118087264246196029)
    ·
      refine ⟨57432834044282724092323511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 153154224118087264246196029 57432834044282724092323511)
      ·
        refine ⟨86149251066424086138485267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57432834044282724092323511 86149251066424086138485267)
        ·
          refine ⟨129223876599636129207727901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86149251066424086138485267 129223876599636129207727901)
          ·
            refine ⟨48458953724863548452897963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 129223876599636129207727901 48458953724863548452897963)
            ·
              refine ⟨72688430587295322679346945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48458953724863548452897963 72688430587295322679346945)
              ·
                refine ⟨54516322940471492009510209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72688430587295322679346945 54516322940471492009510209)
                ·
                  refine ⟨40887242205353619007132657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54516322940471492009510209 40887242205353619007132657)
                  ·
                    refine ⟨30665431654015214255349493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40887242205353619007132657 30665431654015214255349493)
                    ·
                      refine ⟨2874884217563926336439015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30665431654015214255349493 2874884217563926336439015)
                      ·
                        rfl

theorem cell23_5598817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 2, 2, 2, 5].length) (baseStart_5598817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5598817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5598817 prefixEnd_5598817 := by exact prefixLift 5598817
  have htrace : WordTrace (prefixWord ++ tailWord_5598817) baseStart_5598817 baseEnd_5598817 := by
    simpa [prefixWord, tailWord_5598817, baseEnd_5598817] using wordTrace_append hprefix tailTrace_5598817
  have hstable : (prefixWord ++ tailWord_5598817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5598817).length < 2 ^ (prefixWord ++ tailWord_5598817).sum := by decide
  have hdescent : baseEnd_5598817 < baseStart_5598817 := by decide
  rcases family_descends (prefixWord ++ tailWord_5598817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5598821 : List Nat := [1, 3, 1, 3, 3, 1, 2, 1, 4, 1, 3]
def baseStart_5598821 : Nat := 118140960795 + 5598821 * 2 ^ 59
def prefixEnd_5598821 : Nat := 4983230072969 + 3 ^ 40 * 5598821 * 2
def baseEnd_5598821 : Nat := 2874886271486544320788997

theorem tailTrace_5598821 : CollatzResearch.WordTrace tailWord_5598821 prefixEnd_5598821 2874886271486544320788997 := by
  unfold tailWord_5598821
  simp only [CollatzResearch.WordTrace]
  refine ⟨204205778049435194344740317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136137185366290129563160211 204205778049435194344740317)
  ·
    refine ⟨76577166768538197879277619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 204205778049435194344740317 76577166768538197879277619)
    ·
      refine ⟨114865750152807296818916429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76577166768538197879277619 114865750152807296818916429)
      ·
        refine ⟨43074656307302736307093661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114865750152807296818916429 43074656307302736307093661)
        ·
          refine ⟨16152996115238526115160123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43074656307302736307093661 16152996115238526115160123)
          ·
            refine ⟨24229494172857789172740185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16152996115238526115160123 24229494172857789172740185)
            ·
              refine ⟨18172120629643341879555139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24229494172857789172740185 18172120629643341879555139)
              ·
                refine ⟨27258180944465012819332709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18172120629643341879555139 27258180944465012819332709)
                ·
                  refine ⟨5110908927087189903624883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27258180944465012819332709 5110908927087189903624883)
                  ·
                    refine ⟨7666363390630784855437325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5110908927087189903624883 7666363390630784855437325)
                    ·
                      refine ⟨2874886271486544320788997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7666363390630784855437325 2874886271486544320788997)
                      ·
                        rfl

theorem cell23_5598821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 1, 4, 1, 3].length) (baseStart_5598821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5598821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5598821 prefixEnd_5598821 := by exact prefixLift 5598821
  have htrace : WordTrace (prefixWord ++ tailWord_5598821) baseStart_5598821 baseEnd_5598821 := by
    simpa [prefixWord, tailWord_5598821, baseEnd_5598821] using wordTrace_append hprefix tailTrace_5598821
  have hstable : (prefixWord ++ tailWord_5598821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5598821).length < 2 ^ (prefixWord ++ tailWord_5598821).sum := by decide
  have hdescent : baseEnd_5598821 < baseStart_5598821 := by decide
  rcases family_descends (prefixWord ++ tailWord_5598821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5598901 : List Nat := [1, 3, 3, 3, 2, 1, 1, 2, 7]
def baseStart_5598901 : Nat := 118140960795 + 5598901 * 2 ^ 59
def prefixEnd_5598901 : Nat := 4983230072969 + 3 ^ 40 * 5598901 * 2
def baseEnd_5598901 : Nat := 319436372215433778643181

theorem tailTrace_5598901 : CollatzResearch.WordTrace tailWord_5598901 prefixEnd_5598901 319436372215433778643181 := by
  unfold tailWord_5598901
  simp only [CollatzResearch.WordTrace]
  refine ⟨204208695889145368007652557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136139130592763578671768371 204208695889145368007652557)
  ·
    refine ⟨76578260958429513002869709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 204208695889145368007652557 76578260958429513002869709)
    ·
      refine ⟨28716847859411067376076141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76578260958429513002869709 28716847859411067376076141)
      ·
        refine ⟨10768817947279150266028553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28716847859411067376076141 10768817947279150266028553)
        ·
          refine ⟨8076613460459362699521415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10768817947279150266028553 8076613460459362699521415)
          ·
            refine ⟨12114920190689044049282123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8076613460459362699521415 12114920190689044049282123)
            ·
              refine ⟨18172380286033566073923185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12114920190689044049282123 18172380286033566073923185)
              ·
                refine ⟨13629285214525174555442389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18172380286033566073923185 13629285214525174555442389)
                ·
                  refine ⟨319436372215433778643181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13629285214525174555442389 319436372215433778643181)
                  ·
                    rfl

theorem cell23_5598901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 2, 7].length) (baseStart_5598901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5598901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5598901 prefixEnd_5598901 := by exact prefixLift 5598901
  have htrace : WordTrace (prefixWord ++ tailWord_5598901) baseStart_5598901 baseEnd_5598901 := by
    simpa [prefixWord, tailWord_5598901, baseEnd_5598901] using wordTrace_append hprefix tailTrace_5598901
  have hstable : (prefixWord ++ tailWord_5598901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5598901).length < 2 ^ (prefixWord ++ tailWord_5598901).sum := by decide
  have hdescent : baseEnd_5598901 < baseStart_5598901 := by decide
  rcases family_descends (prefixWord ++ tailWord_5598901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5598907 : List Nat := [1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 7]
def baseStart_5598907 : Nat := 118140960795 + 5598907 * 2 ^ 59
def prefixEnd_5598907 : Nat := 4983230072969 + 3 ^ 40 * 5598907 * 2
def baseEnd_5598907 : Nat := 2874930430822830984313601

theorem tailTrace_5598907 : CollatzResearch.WordTrace tailWord_5598907 prefixEnd_5598907 2874930430822830984313601 := by
  unfold tailWord_5598907
  simp only [CollatzResearch.WordTrace]
  refine ⟨204208914727123631032370975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136139276484749087354913983 204208914727123631032370975)
  ·
    refine ⟨306313372090685446548556463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204208914727123631032370975 306313372090685446548556463)
    ·
      refine ⟨459470058136028169822834695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 306313372090685446548556463 459470058136028169822834695)
      ·
        refine ⟨689205087204042254734252043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 459470058136028169822834695 689205087204042254734252043)
        ·
          refine ⟨1033807630806063382101378065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 689205087204042254734252043 1033807630806063382101378065)
          ·
            refine ⟨775355723104547536576033549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1033807630806063382101378065 775355723104547536576033549)
            ·
              refine ⟨290758396164205326216012581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 775355723104547536576033549 290758396164205326216012581)
              ·
                refine ⟨54517199280788498665502359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 290758396164205326216012581 54517199280788498665502359)
                ·
                  refine ⟨81775798921182747998253539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54517199280788498665502359 81775798921182747998253539)
                  ·
                    refine ⟨122663698381774121997380309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 81775798921182747998253539 122663698381774121997380309)
                    ·
                      refine ⟨2874930430822830984313601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 122663698381774121997380309 2874930430822830984313601)
                      ·
                        rfl

theorem cell23_5598907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 7].length) (baseStart_5598907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5598907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5598907 prefixEnd_5598907 := by exact prefixLift 5598907
  have htrace : WordTrace (prefixWord ++ tailWord_5598907) baseStart_5598907 baseEnd_5598907 := by
    simpa [prefixWord, tailWord_5598907, baseEnd_5598907] using wordTrace_append hprefix tailTrace_5598907
  have hstable : (prefixWord ++ tailWord_5598907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5598907).length < 2 ^ (prefixWord ++ tailWord_5598907).sum := by decide
  have hdescent : baseEnd_5598907 < baseStart_5598907 := by decide
  rcases family_descends (prefixWord ++ tailWord_5598907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5598927 : List Nat := [1, 1, 2, 1, 1, 3, 1, 2, 1, 10]
def baseStart_5598927 : Nat := 118140960795 + 5598927 * 2 ^ 59
def prefixEnd_5598927 : Nat := 4983230072969 + 3 ^ 40 * 5598927 * 2
def baseEnd_5598927 : Nat := 958313566811973635354503

theorem tailTrace_5598927 : CollatzResearch.WordTrace tailWord_5598927 prefixEnd_5598927 958313566811973635354503 := by
  unfold tailWord_5598927
  simp only [CollatzResearch.WordTrace]
  refine ⟨204209644187051174448099035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136139762791367449632066023 204209644187051174448099035)
  ·
    refine ⟨306314466280576761672148553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204209644187051174448099035 306314466280576761672148553)
    ·
      refine ⟨229735849710432571254111415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 306314466280576761672148553 229735849710432571254111415)
      ·
        refine ⟨344603774565648856881167123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229735849710432571254111415 344603774565648856881167123)
        ·
          refine ⟨516905661848473285321750685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 344603774565648856881167123 516905661848473285321750685)
          ·
            refine ⟨193839623193177481995656507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 516905661848473285321750685 193839623193177481995656507)
            ·
              refine ⟨290759434789766222993484761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 193839623193177481995656507 290759434789766222993484761)
              ·
                refine ⟨218069576092324667245113571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 290759434789766222993484761 218069576092324667245113571)
                ·
                  refine ⟨327104364138487000867670357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 218069576092324667245113571 327104364138487000867670357)
                  ·
                    refine ⟨958313566811973635354503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 327104364138487000867670357 958313566811973635354503)
                    ·
                      rfl

theorem cell23_5598927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 10].length) (baseStart_5598927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5598927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5598927 prefixEnd_5598927 := by exact prefixLift 5598927
  have htrace : WordTrace (prefixWord ++ tailWord_5598927) baseStart_5598927 baseEnd_5598927 := by
    simpa [prefixWord, tailWord_5598927, baseEnd_5598927] using wordTrace_append hprefix tailTrace_5598927
  have hstable : (prefixWord ++ tailWord_5598927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5598927).length < 2 ^ (prefixWord ++ tailWord_5598927).sum := by decide
  have hdescent : baseEnd_5598927 < baseStart_5598927 := by decide
  rcases family_descends (prefixWord ++ tailWord_5598927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5598961 : List Nat := [1, 2, 2, 2, 2, 3, 2, 2, 3, 4]
def baseStart_5598961 : Nat := 118140960795 + 5598961 * 2 ^ 59
def prefixEnd_5598961 : Nat := 4983230072969 + 3 ^ 40 * 5598961 * 2
def baseEnd_5598961 : Nat := 958319386259391257679451

theorem tailTrace_5598961 : CollatzResearch.WordTrace tailWord_5598961 prefixEnd_5598961 958319386259391257679451 := by
  unfold tailWord_5598961
  simp only [CollatzResearch.WordTrace]
  refine ⟨204210884268927998254836737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136140589512618665503224491 204210884268927998254836737)
  ·
    refine ⟨153158163201695998691127553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204210884268927998254836737 153158163201695998691127553)
    ·
      refine ⟨114868622401271999018345665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153158163201695998691127553 114868622401271999018345665)
      ·
        refine ⟨86151466800953999263759249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114868622401271999018345665 86151466800953999263759249)
        ·
          refine ⟨64613600100715499447819437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86151466800953999263759249 64613600100715499447819437)
          ·
            refine ⟨24230100037768312292932289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64613600100715499447819437 24230100037768312292932289)
            ·
              refine ⟨18172575028326234219699217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24230100037768312292932289 18172575028326234219699217)
              ·
                refine ⟨13629431271244675664774413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18172575028326234219699217 13629431271244675664774413)
                ·
                  refine ⟨5111036726716753374290405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13629431271244675664774413 5111036726716753374290405)
                  ·
                    refine ⟨958319386259391257679451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5111036726716753374290405 958319386259391257679451)
                    ·
                      rfl

theorem cell23_5598961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 2, 3, 4].length) (baseStart_5598961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5598961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5598961 prefixEnd_5598961 := by exact prefixLift 5598961
  have htrace : WordTrace (prefixWord ++ tailWord_5598961) baseStart_5598961 baseEnd_5598961 := by
    simpa [prefixWord, tailWord_5598961, baseEnd_5598961] using wordTrace_append hprefix tailTrace_5598961
  have hstable : (prefixWord ++ tailWord_5598961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5598961).length < 2 ^ (prefixWord ++ tailWord_5598961).sum := by decide
  have hdescent : baseEnd_5598961 < baseStart_5598961 := by decide
  rcases family_descends (prefixWord ++ tailWord_5598961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5599011 : List Nat := [1, 1, 1, 4, 2, 1, 2, 1, 3, 5, 2]
def baseStart_5599011 : Nat := 118140960795 + 5599011 * 2 ^ 59
def prefixEnd_5599011 : Nat := 4983230072969 + 3 ^ 40 * 5599011 * 2
def baseEnd_5599011 : Nat := 2874983832810898577413123

theorem tailTrace_5599011 : CollatzResearch.WordTrace tailWord_5599011 prefixEnd_5599011 2874983832810898577413123 := by
  unfold tailWord_5599011
  simp only [CollatzResearch.WordTrace]
  refine ⟨204212707918746856794156887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136141805279164571196104591 204212707918746856794156887)
  ·
    refine ⟨306319061878120285191235331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204212707918746856794156887 306319061878120285191235331)
    ·
      refine ⟨459478592817180427786852997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 306319061878120285191235331 459478592817180427786852997)
      ·
        refine ⟨86152236153221330210034937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 459478592817180427786852997 86152236153221330210034937)
        ·
          refine ⟨64614177114915997657526203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86152236153221330210034937 64614177114915997657526203)
          ·
            refine ⟨96921265672373996486289305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64614177114915997657526203 96921265672373996486289305)
            ·
              refine ⟨72690949254280497364716979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96921265672373996486289305 72690949254280497364716979)
              ·
                refine ⟨109036423881420746047075469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72690949254280497364716979 109036423881420746047075469)
                ·
                  refine ⟨40888658955532779767653301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 109036423881420746047075469 40888658955532779767653301)
                  ·
                    refine ⟨3833311777081198103217497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40888658955532779767653301 3833311777081198103217497)
                    ·
                      refine ⟨2874983832810898577413123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3833311777081198103217497 2874983832810898577413123)
                      ·
                        rfl

theorem cell23_5599011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 3, 5, 2].length) (baseStart_5599011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5599011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5599011 prefixEnd_5599011 := by exact prefixLift 5599011
  have htrace : WordTrace (prefixWord ++ tailWord_5599011) baseStart_5599011 baseEnd_5599011 := by
    simpa [prefixWord, tailWord_5599011, baseEnd_5599011] using wordTrace_append hprefix tailTrace_5599011
  have hstable : (prefixWord ++ tailWord_5599011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5599011).length < 2 ^ (prefixWord ++ tailWord_5599011).sum := by decide
  have hdescent : baseEnd_5599011 < baseStart_5599011 := by decide
  rcases family_descends (prefixWord ++ tailWord_5599011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5599046 : List Nat := [6, 1, 1, 2, 1, 3, 2, 2, 1, 4]
def baseStart_5599046 : Nat := 118140960795 + 5599046 * 2 ^ 59
def prefixEnd_5599046 : Nat := 4983230072969 + 3 ^ 40 * 5599046 * 2
def baseEnd_5599046 : Nat := 958333934877935313491821

theorem tailTrace_5599046 : CollatzResearch.WordTrace tailWord_5599046 prefixEnd_5599046 958333934877935313491821 := by
  unfold tailWord_5599046
  simp only [CollatzResearch.WordTrace]
  refine ⟨6381687014800626805365031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 136142656315746705181120661 6381687014800626805365031)
  ·
    refine ⟨9572530522200940208047547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6381687014800626805365031 9572530522200940208047547)
    ·
      refine ⟨14358795783301410312071321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9572530522200940208047547 14358795783301410312071321)
      ·
        refine ⟨10769096837476057734053491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14358795783301410312071321 10769096837476057734053491)
        ·
          refine ⟨16153645256214086601080237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10769096837476057734053491 16153645256214086601080237)
          ·
            refine ⟨6057616971080282475405089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16153645256214086601080237 6057616971080282475405089)
            ·
              refine ⟨4543212728310211856553817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6057616971080282475405089 4543212728310211856553817)
              ·
                refine ⟨3407409546232658892415363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4543212728310211856553817 3407409546232658892415363)
                ·
                  refine ⟨5111114319348988338623045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3407409546232658892415363 5111114319348988338623045)
                  ·
                    refine ⟨958333934877935313491821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5111114319348988338623045 958333934877935313491821)
                    ·
                      rfl

theorem cell23_5599046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 2, 2, 1, 4].length) (baseStart_5599046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5599046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5599046 prefixEnd_5599046 := by exact prefixLift 5599046
  have htrace : WordTrace (prefixWord ++ tailWord_5599046) baseStart_5599046 baseEnd_5599046 := by
    simpa [prefixWord, tailWord_5599046, baseEnd_5599046] using wordTrace_append hprefix tailTrace_5599046
  have hstable : (prefixWord ++ tailWord_5599046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5599046).length < 2 ^ (prefixWord ++ tailWord_5599046).sum := by decide
  have hdescent : baseEnd_5599046 < baseStart_5599046 := by decide
  rcases family_descends (prefixWord ++ tailWord_5599046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5599052 : List Nat := [2, 2, 1, 3, 4, 1, 1, 4, 1, 1, 3]
def baseStart_5599052 : Nat := 118140960795 + 5599052 * 2 ^ 59
def prefixEnd_5599052 : Nat := 4983230072969 + 3 ^ 40 * 5599052 * 2
def baseEnd_5599052 : Nat := 2875004885517732917000435

theorem tailTrace_5599052 : CollatzResearch.WordTrace tailWord_5599052 prefixEnd_5599052 2875004885517732917000435 := by
  unfold tailWord_5599052
  simp only [CollatzResearch.WordTrace]
  refine ⟨102107101655799160398199705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136142802207732213864266273 102107101655799160398199705)
  ·
    refine ⟨76580326241849370298649779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102107101655799160398199705 76580326241849370298649779)
    ·
      refine ⟨114870489362774055447974669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76580326241849370298649779 114870489362774055447974669)
      ·
        refine ⟨43076433511040270792990501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114870489362774055447974669 43076433511040270792990501)
        ·
          refine ⟨8076831283320050773685719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43076433511040270792990501 8076831283320050773685719)
          ·
            refine ⟨12115246924980076160528579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8076831283320050773685719 12115246924980076160528579)
            ·
              refine ⟨18172870387470114240792869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12115246924980076160528579 18172870387470114240792869)
              ·
                refine ⟨3407413197650646420148663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18172870387470114240792869 3407413197650646420148663)
                ·
                  refine ⟨5111119796475969630222995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3407413197650646420148663 5111119796475969630222995)
                  ·
                    refine ⟨7666679694713954445334493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5111119796475969630222995 7666679694713954445334493)
                    ·
                      refine ⟨2875004885517732917000435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7666679694713954445334493 2875004885517732917000435)
                      ·
                        rfl

theorem cell23_5599052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 4, 1, 1, 3].length) (baseStart_5599052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5599052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5599052 prefixEnd_5599052 := by exact prefixLift 5599052
  have htrace : WordTrace (prefixWord ++ tailWord_5599052) baseStart_5599052 baseEnd_5599052 := by
    simpa [prefixWord, tailWord_5599052, baseEnd_5599052] using wordTrace_append hprefix tailTrace_5599052
  have hstable : (prefixWord ++ tailWord_5599052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5599052).length < 2 ^ (prefixWord ++ tailWord_5599052).sum := by decide
  have hdescent : baseEnd_5599052 < baseStart_5599052 := by decide
  rcases family_descends (prefixWord ++ tailWord_5599052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5599071 : List Nat := [1, 1, 2, 3, 1, 4, 1, 3, 1, 2, 4]
def baseStart_5599071 : Nat := 118140960795 + 5599071 * 2 ^ 59
def prefixEnd_5599071 : Nat := 4983230072969 + 3 ^ 40 * 5599071 * 2
def baseEnd_5599071 : Nat := 2875014641650168342662847

theorem tailTrace_5599071 : CollatzResearch.WordTrace tailWord_5599071 prefixEnd_5599071 2875014641650168342662847 := by
  unfold tailWord_5599071
  simp only [CollatzResearch.WordTrace]
  refine ⟨204214896298529487041341067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136143264199019658027560711 204214896298529487041341067)
  ·
    refine ⟨306322344447794230562011601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204214896298529487041341067 306322344447794230562011601)
    ·
      refine ⟨229741758335845672921508701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 306322344447794230562011601 229741758335845672921508701)
      ·
        refine ⟨86153159375942127345565763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 229741758335845672921508701 86153159375942127345565763)
        ·
          refine ⟨129229739063913191018348645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86153159375942127345565763 129229739063913191018348645)
          ·
            refine ⟨24230576074483723315940371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 129229739063913191018348645 24230576074483723315940371)
            ·
              refine ⟨36345864111725584973910557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24230576074483723315940371 36345864111725584973910557)
              ·
                refine ⟨13629699041897094365216459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36345864111725584973910557 13629699041897094365216459)
                ·
                  refine ⟨20444548562845641547824689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13629699041897094365216459 20444548562845641547824689)
                  ·
                    refine ⟨15333411422134231160868517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20444548562845641547824689 15333411422134231160868517)
                    ·
                      refine ⟨2875014641650168342662847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15333411422134231160868517 2875014641650168342662847)
                      ·
                        rfl

theorem cell23_5599071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 3, 1, 2, 4].length) (baseStart_5599071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5599071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5599071 prefixEnd_5599071 := by exact prefixLift 5599071
  have htrace : WordTrace (prefixWord ++ tailWord_5599071) baseStart_5599071 baseEnd_5599071 := by
    simpa [prefixWord, tailWord_5599071, baseEnd_5599071] using wordTrace_append hprefix tailTrace_5599071
  have hstable : (prefixWord ++ tailWord_5599071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5599071).length < 2 ^ (prefixWord ++ tailWord_5599071).sum := by decide
  have hdescent : baseEnd_5599071 < baseStart_5599071 := by decide
  rcases family_descends (prefixWord ++ tailWord_5599071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5599102 : List Nat := [4, 2, 3, 1, 1, 1, 3, 2, 2, 4]
def baseStart_5599102 : Nat := 118140960795 + 5599102 * 2 ^ 59
def prefixEnd_5599102 : Nat := 4983230072969 + 3 ^ 40 * 5599102 * 2
def baseEnd_5599102 : Nat := 958343519850152573791735

theorem tailTrace_5599102 : CollatzResearch.WordTrace tailWord_5599102 prefixEnd_5599102 958343519850152573791735 := by
  unfold tailWord_5599102
  simp only [CollatzResearch.WordTrace]
  refine ⟨25527003370177147416964945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136144017974278119557146373 25527003370177147416964945)
  ·
    refine ⟨19145252527632860562723709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25527003370177147416964945 19145252527632860562723709)
    ·
      refine ⟨7179469697862322711021391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19145252527632860562723709 7179469697862322711021391)
      ·
        refine ⟨10769204546793484066532087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7179469697862322711021391 10769204546793484066532087)
        ·
          refine ⟨16153806820190226099798131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10769204546793484066532087 16153806820190226099798131)
          ·
            refine ⟨24230710230285339149697197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16153806820190226099798131 24230710230285339149697197)
            ·
              refine ⟨9086516336357002181136449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24230710230285339149697197 9086516336357002181136449)
              ·
                refine ⟨6814887252267751635852337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9086516336357002181136449 6814887252267751635852337)
                ·
                  refine ⟨5111165439200813726889253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6814887252267751635852337 5111165439200813726889253)
                  ·
                    refine ⟨958343519850152573791735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5111165439200813726889253 958343519850152573791735)
                    ·
                      rfl

theorem cell23_5599102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_5599102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5599102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5599102 prefixEnd_5599102 := by exact prefixLift 5599102
  have htrace : WordTrace (prefixWord ++ tailWord_5599102) baseStart_5599102 baseEnd_5599102 := by
    simpa [prefixWord, tailWord_5599102, baseEnd_5599102] using wordTrace_append hprefix tailTrace_5599102
  have hstable : (prefixWord ++ tailWord_5599102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5599102).length < 2 ^ (prefixWord ++ tailWord_5599102).sum := by decide
  have hdescent : baseEnd_5599102 < baseStart_5599102 := by decide
  rcases family_descends (prefixWord ++ tailWord_5599102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5599151 : List Nat := [1, 1, 2, 1, 2, 2, 5, 1, 2, 1, 5]
def baseStart_5599151 : Nat := 118140960795 + 5599151 * 2 ^ 59
def prefixEnd_5599151 : Nat := 4983230072969 + 3 ^ 40 * 5599151 * 2
def baseEnd_5599151 : Nat := 2875055720102528029662479

theorem tailTrace_5599151 : CollatzResearch.WordTrace tailWord_5599151 prefixEnd_5599151 2875055720102528029662479 := by
  unfold tailWord_5599151
  simp only [CollatzResearch.WordTrace]
  refine ⟨204217814138239660704253307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136145209425493107136168871 204217814138239660704253307)
  ·
    refine ⟨306326721207359491056379961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204217814138239660704253307 306326721207359491056379961)
    ·
      refine ⟨229745040905519618292284971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 306326721207359491056379961 229745040905519618292284971)
      ·
        refine ⟨344617561358279427438427457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229745040905519618292284971 344617561358279427438427457)
        ·
          refine ⟨258463171018709570578820593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 344617561358279427438427457 258463171018709570578820593)
          ·
            refine ⟨193847378264032177934115445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 258463171018709570578820593 193847378264032177934115445)
            ·
              refine ⟨18173191712253016681323323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 193847378264032177934115445 18173191712253016681323323)
              ·
                refine ⟨27259787568379525021984985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18173191712253016681323323 27259787568379525021984985)
                ·
                  refine ⟨20444840676284643766488739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27259787568379525021984985 20444840676284643766488739)
                  ·
                    refine ⟨30667261014426965649733109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20444840676284643766488739 30667261014426965649733109)
                    ·
                      refine ⟨2875055720102528029662479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30667261014426965649733109 2875055720102528029662479)
                      ·
                        rfl

theorem cell23_5599151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 1, 2, 1, 5].length) (baseStart_5599151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5599151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5599151 prefixEnd_5599151 := by exact prefixLift 5599151
  have htrace : WordTrace (prefixWord ++ tailWord_5599151) baseStart_5599151 baseEnd_5599151 := by
    simpa [prefixWord, tailWord_5599151, baseEnd_5599151] using wordTrace_append hprefix tailTrace_5599151
  have hstable : (prefixWord ++ tailWord_5599151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5599151).length < 2 ^ (prefixWord ++ tailWord_5599151).sum := by decide
  have hdescent : baseEnd_5599151 < baseStart_5599151 := by decide
  rcases family_descends (prefixWord ++ tailWord_5599151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5599182 : List Nat := [4, 1, 1, 1, 2, 2, 3, 3, 2, 2, 2]
def baseStart_5599182 : Nat := 118140960795 + 5599182 * 2 ^ 59
def prefixEnd_5599182 : Nat := 4983230072969 + 3 ^ 40 * 5599182 * 2
def baseEnd_5599182 : Nat := 2875071638002817408374837

theorem tailTrace_5599182 : CollatzResearch.WordTrace tailWord_5599182 prefixEnd_5599182 2875071638002817408374837 := by
  unfold tailWord_5599182
  simp only [CollatzResearch.WordTrace]
  refine ⟨25527368100140919124828975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136145963200751568665754533 25527368100140919124828975)
  ·
    refine ⟨38291052150211378687243463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25527368100140919124828975 38291052150211378687243463)
    ·
      refine ⟨57436578225317068030865195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38291052150211378687243463 57436578225317068030865195)
      ·
        refine ⟨86154867337975602046297793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57436578225317068030865195 86154867337975602046297793)
        ·
          refine ⟨64616150503481701534723345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86154867337975602046297793 64616150503481701534723345)
          ·
            refine ⟨48462112877611276151042509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64616150503481701534723345 48462112877611276151042509)
            ·
              refine ⟨18173292329104228556640941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48462112877611276151042509 18173292329104228556640941)
              ·
                refine ⟨6814984623414085708740353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18173292329104228556640941 6814984623414085708740353)
                ·
                  refine ⟨5111238467560564281555265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6814984623414085708740353 5111238467560564281555265)
                  ·
                    refine ⟨3833428850670423211166449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5111238467560564281555265 3833428850670423211166449)
                    ·
                      refine ⟨2875071638002817408374837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3833428850670423211166449 2875071638002817408374837)
                      ·
                        rfl

theorem cell23_5599182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 3, 2, 2, 2].length) (baseStart_5599182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5599182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5599182 prefixEnd_5599182 := by exact prefixLift 5599182
  have htrace : WordTrace (prefixWord ++ tailWord_5599182) baseStart_5599182 baseEnd_5599182 := by
    simpa [prefixWord, tailWord_5599182, baseEnd_5599182] using wordTrace_append hprefix tailTrace_5599182
  have hstable : (prefixWord ++ tailWord_5599182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5599182).length < 2 ^ (prefixWord ++ tailWord_5599182).sum := by decide
  have hdescent : baseEnd_5599182 < baseStart_5599182 := by decide
  rcases family_descends (prefixWord ++ tailWord_5599182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5599186 : List Nat := [3, 2, 2, 3, 3, 1, 1, 2, 1, 3, 2]
def baseStart_5599186 : Nat := 118140960795 + 5599186 * 2 ^ 59
def prefixEnd_5599186 : Nat := 4983230072969 + 3 ^ 40 * 5599186 * 2
def baseEnd_5599186 : Nat := 2875073691925435392724819

theorem tailTrace_5599186 : CollatzResearch.WordTrace tailWord_5599186 prefixEnd_5599186 2875073691925435392724819 := by
  unfold tailWord_5599186
  simp only [CollatzResearch.WordTrace]
  refine ⟨51054772673278215420444353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136146060462075241121184941 51054772673278215420444353)
  ·
    refine ⟨38291079504958661565333265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51054772673278215420444353 38291079504958661565333265)
    ·
      refine ⟨28718309628718996173999949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38291079504958661565333265 28718309628718996173999949)
      ·
        refine ⟨10769366110769623565249981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28718309628718996173999949 10769366110769623565249981)
        ·
          refine ⟨4038512291538608836968743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10769366110769623565249981 4038512291538608836968743)
          ·
            refine ⟨6057768437307913255453115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4038512291538608836968743 6057768437307913255453115)
            ·
              refine ⟨9086652655961869883179673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6057768437307913255453115 9086652655961869883179673)
              ·
                refine ⟨6814989491971402412384755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9086652655961869883179673 6814989491971402412384755)
                ·
                  refine ⟨10222484237957103618577133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6814989491971402412384755 10222484237957103618577133)
                  ·
                    refine ⟨3833431589233913856966425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10222484237957103618577133 3833431589233913856966425)
                    ·
                      refine ⟨2875073691925435392724819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3833431589233913856966425 2875073691925435392724819)
                      ·
                        rfl

theorem cell23_5599186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 1, 2, 1, 3, 2].length) (baseStart_5599186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5599186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5599186 prefixEnd_5599186 := by exact prefixLift 5599186
  have htrace : WordTrace (prefixWord ++ tailWord_5599186) baseStart_5599186 baseEnd_5599186 := by
    simpa [prefixWord, tailWord_5599186, baseEnd_5599186] using wordTrace_append hprefix tailTrace_5599186
  have hstable : (prefixWord ++ tailWord_5599186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5599186).length < 2 ^ (prefixWord ++ tailWord_5599186).sum := by decide
  have hdescent : baseEnd_5599186 < baseStart_5599186 := by decide
  rcases family_descends (prefixWord ++ tailWord_5599186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5599201 : List Nat := [1, 2, 3, 1, 2, 1, 2, 3, 1, 7]
def baseStart_5599201 : Nat := 118140960795 + 5599201 * 2 ^ 59
def prefixEnd_5599201 : Nat := 4983230072969 + 3 ^ 40 * 5599201 * 2
def baseEnd_5599201 : Nat := 958360464711750944679083

theorem tailTrace_5599201 : CollatzResearch.WordTrace tailWord_5599201 prefixEnd_5599201 958360464711750944679083 := by
  unfold tailWord_5599201
  simp only [CollatzResearch.WordTrace]
  refine ⟨204219637788058519243573457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136146425192039012829048971 204219637788058519243573457)
  ·
    refine ⟨153164728341043889432680093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204219637788058519243573457 153164728341043889432680093)
    ·
      refine ⟨57436773127891458537255035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 153164728341043889432680093 57436773127891458537255035)
      ·
        refine ⟨86155159691837187805882553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57436773127891458537255035 86155159691837187805882553)
        ·
          refine ⟨64616369768877890854411915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86155159691837187805882553 64616369768877890854411915)
          ·
            refine ⟨96924554653316836281617873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64616369768877890854411915 96924554653316836281617873)
            ·
              refine ⟨72693415989987627211213405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96924554653316836281617873 72693415989987627211213405)
              ·
                refine ⟨27260030996245360204205027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72693415989987627211213405 27260030996245360204205027)
                ·
                  refine ⟨40890046494368040306307541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27260030996245360204205027 40890046494368040306307541)
                  ·
                    refine ⟨958360464711750944679083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40890046494368040306307541 958360464711750944679083)
                    ·
                      rfl

theorem cell23_5599201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 3, 1, 7].length) (baseStart_5599201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5599201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5599201 prefixEnd_5599201 := by exact prefixLift 5599201
  have htrace : WordTrace (prefixWord ++ tailWord_5599201) baseStart_5599201 baseEnd_5599201 := by
    simpa [prefixWord, tailWord_5599201, baseEnd_5599201] using wordTrace_append hprefix tailTrace_5599201
  have hstable : (prefixWord ++ tailWord_5599201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5599201).length < 2 ^ (prefixWord ++ tailWord_5599201).sum := by decide
  have hdescent : baseEnd_5599201 < baseStart_5599201 := by decide
  rcases family_descends (prefixWord ++ tailWord_5599201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5599222 : List Nat := [5, 1, 1, 1, 4, 1, 1, 4, 5]
def baseStart_5599222 : Nat := 118140960795 + 5599222 * 2 ^ 59
def prefixEnd_5599222 : Nat := 4983230072969 + 3 ^ 40 * 5599222 * 2
def baseEnd_5599222 : Nat := 319454686358777472430517

theorem tailTrace_5599222 : CollatzResearch.WordTrace tailWord_5599222 prefixEnd_5599222 319454686358777472430517 := by
  unfold tailWord_5599222
  simp only [CollatzResearch.WordTrace]
  refine ⟨12763775232561402489380495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 136146935813988293220058613 12763775232561402489380495)
  ·
    refine ⟨19145662848842103734070743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12763775232561402489380495 19145662848842103734070743)
    ·
      refine ⟨28718494273263155601106115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19145662848842103734070743 28718494273263155601106115)
      ·
        refine ⟨43077741409894733401659173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28718494273263155601106115 43077741409894733401659173)
        ·
          refine ⟨8077076514355262512811095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43077741409894733401659173 8077076514355262512811095)
          ·
            refine ⟨12115614771532893769216643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8077076514355262512811095 12115614771532893769216643)
            ·
              refine ⟨18173422157299340653824965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12115614771532893769216643 18173422157299340653824965)
              ·
                refine ⟨3407516654493626372592181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18173422157299340653824965 3407516654493626372592181)
                ·
                  refine ⟨319454686358777472430517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3407516654493626372592181 319454686358777472430517)
                  ·
                    rfl

theorem cell23_5599222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 4, 5].length) (baseStart_5599222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5599222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5599222 prefixEnd_5599222 := by exact prefixLift 5599222
  have htrace : WordTrace (prefixWord ++ tailWord_5599222) baseStart_5599222 baseEnd_5599222 := by
    simpa [prefixWord, tailWord_5599222, baseEnd_5599222] using wordTrace_append hprefix tailTrace_5599222
  have hstable : (prefixWord ++ tailWord_5599222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5599222).length < 2 ^ (prefixWord ++ tailWord_5599222).sum := by decide
  have hdescent : baseEnd_5599222 < baseStart_5599222 := by decide
  rcases family_descends (prefixWord ++ tailWord_5599222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5599248 : List Nat := [2, 1, 1, 1, 1, 1, 1, 8, 3, 4]
def baseStart_5599248 : Nat := 118140960795 + 5599248 * 2 ^ 59
def prefixEnd_5599248 : Nat := 4983230072969 + 3 ^ 40 * 5599248 * 2
def baseEnd_5599248 : Nat := 958368509242004716716511

theorem tailTrace_5599248 : CollatzResearch.WordTrace tailWord_5599248 prefixEnd_5599248 958368509242004716716511 := by
  unfold tailWord_5599248
  simp only [CollatzResearch.WordTrace]
  refine ⟨102110676009444123135267199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136147568012592164180356265 102110676009444123135267199)
  ·
    refine ⟨153166014014166184702900799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102110676009444123135267199 153166014014166184702900799)
    ·
      refine ⟨229749021021249277054351199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153166014014166184702900799 229749021021249277054351199)
      ·
        refine ⟨344623531531873915581526799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229749021021249277054351199 344623531531873915581526799)
        ·
          refine ⟨516935297297810873372290199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 344623531531873915581526799 516935297297810873372290199)
          ·
            refine ⟨775402945946716310058435299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 516935297297810873372290199 775402945946716310058435299)
            ·
              refine ⟨1163104418920074465087652949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 775402945946716310058435299 1163104418920074465087652949)
              ·
                refine ⟨13630129909219622637745933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1163104418920074465087652949 13630129909219622637745933)
                ·
                  refine ⟨5111298715957358489154725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13630129909219622637745933 5111298715957358489154725)
                  ·
                    refine ⟨958368509242004716716511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5111298715957358489154725 958368509242004716716511)
                    ·
                      rfl

theorem cell23_5599248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 8, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 8, 3, 4].length) (baseStart_5599248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5599248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5599248 prefixEnd_5599248 := by exact prefixLift 5599248
  have htrace : WordTrace (prefixWord ++ tailWord_5599248) baseStart_5599248 baseEnd_5599248 := by
    simpa [prefixWord, tailWord_5599248, baseEnd_5599248] using wordTrace_append hprefix tailTrace_5599248
  have hstable : (prefixWord ++ tailWord_5599248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5599248).length < 2 ^ (prefixWord ++ tailWord_5599248).sum := by decide
  have hdescent : baseEnd_5599248 < baseStart_5599248 := by decide
  rcases family_descends (prefixWord ++ tailWord_5599248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5599252 : List Nat := [2, 4, 3, 2, 1, 1, 1, 1, 1, 7]
def baseStart_5599252 : Nat := 118140960795 + 5599252 * 2 ^ 59
def prefixEnd_5599252 : Nat := 4983230072969 + 3 ^ 40 * 5599252 * 2
def baseEnd_5599252 : Nat := 958369193882877378166505

theorem tailTrace_5599252 : CollatzResearch.WordTrace tailWord_5599252 prefixEnd_5599252 958369193882877378166505 := by
  unfold tailWord_5599252
  simp only [CollatzResearch.WordTrace]
  refine ⟨102110748955436877476840005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136147665273915836635786673 102110748955436877476840005)
  ·
    refine ⟨19145765429144414526907501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102110748955436877476840005 19145765429144414526907501)
    ·
      refine ⟨7179662035929155447590313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19145765429144414526907501 7179662035929155447590313)
      ·
        refine ⟨5384746526946866585692735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7179662035929155447590313 5384746526946866585692735)
        ·
          refine ⟨8077119790420299878539103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5384746526946866585692735 8077119790420299878539103)
          ·
            refine ⟨12115679685630449817808655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8077119790420299878539103 12115679685630449817808655)
            ·
              refine ⟨18173519528445674726712983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12115679685630449817808655 18173519528445674726712983)
              ·
                refine ⟨27260279292668512090069475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18173519528445674726712983 27260279292668512090069475)
                ·
                  refine ⟨40890418939002768135104213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27260279292668512090069475 40890418939002768135104213)
                  ·
                    refine ⟨958369193882877378166505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40890418939002768135104213 958369193882877378166505)
                    ·
                      rfl

theorem cell23_5599252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_5599252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5599252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5599252 prefixEnd_5599252 := by exact prefixLift 5599252
  have htrace : WordTrace (prefixWord ++ tailWord_5599252) baseStart_5599252 baseEnd_5599252 := by
    simpa [prefixWord, tailWord_5599252, baseEnd_5599252] using wordTrace_append hprefix tailTrace_5599252
  have hstable : (prefixWord ++ tailWord_5599252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5599252).length < 2 ^ (prefixWord ++ tailWord_5599252).sum := by decide
  have hdescent : baseEnd_5599252 < baseStart_5599252 := by decide
  rcases family_descends (prefixWord ++ tailWord_5599252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5599255 : List Nat := [1, 1, 3, 5, 2, 1, 1, 1, 1, 3, 4]
def baseStart_5599255 : Nat := 118140960795 + 5599255 * 2 ^ 59
def prefixEnd_5599255 : Nat := 4983230072969 + 3 ^ 40 * 5599255 * 2
def baseEnd_5599255 : Nat := 2875109122090595622762001

theorem tailTrace_5599255 : CollatzResearch.WordTrace tailWord_5599255 prefixEnd_5599255 2875109122090595622762001 := by
  unfold tailWord_5599255
  simp only [CollatzResearch.WordTrace]
  refine ⟨204221607329862886466039219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136147738219908590977359479 204221607329862886466039219)
  ·
    refine ⟨306332410994794329699058829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204221607329862886466039219 306332410994794329699058829)
    ·
      refine ⟨114874654123047873637147061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 306332410994794329699058829 114874654123047873637147061)
      ·
        refine ⟨10769498824035738153482537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 114874654123047873637147061 10769498824035738153482537)
        ·
          refine ⟨8077124118026803615111903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10769498824035738153482537 8077124118026803615111903)
          ·
            refine ⟨12115686177040205422667855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8077124118026803615111903 12115686177040205422667855)
            ·
              refine ⟨18173529265560308134001783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12115686177040205422667855 18173529265560308134001783)
              ·
                refine ⟨27260293898340462201002675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18173529265560308134001783 27260293898340462201002675)
                ·
                  refine ⟨40890440847510693301504013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27260293898340462201002675 40890440847510693301504013)
                  ·
                    refine ⟨15333915317816509988064005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40890440847510693301504013 15333915317816509988064005)
                    ·
                      refine ⟨2875109122090595622762001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15333915317816509988064005 2875109122090595622762001)
                      ·
                        rfl

theorem cell23_5599255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_5599255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5599255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5599255 prefixEnd_5599255 := by exact prefixLift 5599255
  have htrace : WordTrace (prefixWord ++ tailWord_5599255) baseStart_5599255 baseEnd_5599255 := by
    simpa [prefixWord, tailWord_5599255, baseEnd_5599255] using wordTrace_append hprefix tailTrace_5599255
  have hstable : (prefixWord ++ tailWord_5599255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5599255).length < 2 ^ (prefixWord ++ tailWord_5599255).sum := by decide
  have hdescent : baseEnd_5599255 < baseStart_5599255 := by decide
  rcases family_descends (prefixWord ++ tailWord_5599255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5599282 : List Nat := [3, 2, 1, 1, 2, 3, 2, 4, 1, 4]
def baseStart_5599282 : Nat := 118140960795 + 5599282 * 2 ^ 59
def prefixEnd_5599282 : Nat := 4983230072969 + 3 ^ 40 * 5599282 * 2
def baseEnd_5599282 : Nat := 958374328689422339041459

theorem tailTrace_5599282 : CollatzResearch.WordTrace tailWord_5599282 prefixEnd_5599282 958374328689422339041459 := by
  unfold tailWord_5599282
  simp only [CollatzResearch.WordTrace]
  refine ⟨51055648025191267519318025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136148394733843380051514733 51055648025191267519318025)
  ·
    refine ⟨38291736018893450639488519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51055648025191267519318025 38291736018893450639488519)
    ·
      refine ⟨57437604028340175959232779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38291736018893450639488519 57437604028340175959232779)
      ·
        refine ⟨86156406042510263938849169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57437604028340175959232779 86156406042510263938849169)
        ·
          refine ⟨64617304531882697954136877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86156406042510263938849169 64617304531882697954136877)
          ·
            refine ⟨24231489199456011732801329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64617304531882697954136877 24231489199456011732801329)
            ·
              refine ⟨18173616899592008799600997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24231489199456011732801329 18173616899592008799600997)
              ·
                refine ⟨3407553168673501649925187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18173616899592008799600997 3407553168673501649925187)
                ·
                  refine ⟨5111329753010252474887781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3407553168673501649925187 5111329753010252474887781)
                  ·
                    refine ⟨958374328689422339041459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5111329753010252474887781 958374328689422339041459)
                    ·
                      rfl

theorem cell23_5599282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 4, 1, 4].length) (baseStart_5599282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5599282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5599282 prefixEnd_5599282 := by exact prefixLift 5599282
  have htrace : WordTrace (prefixWord ++ tailWord_5599282) baseStart_5599282 baseEnd_5599282 := by
    simpa [prefixWord, tailWord_5599282, baseEnd_5599282] using wordTrace_append hprefix tailTrace_5599282
  have hstable : (prefixWord ++ tailWord_5599282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5599282).length < 2 ^ (prefixWord ++ tailWord_5599282).sum := by decide
  have hdescent : baseEnd_5599282 < baseStart_5599282 := by decide
  rcases family_descends (prefixWord ++ tailWord_5599282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5599305 : List Nat := [1, 2, 1, 1, 2, 2, 3, 4, 3, 1, 3]
def baseStart_5599305 : Nat := 118140960795 + 5599305 * 2 ^ 59
def prefixEnd_5599305 : Nat := 4983230072969 + 3 ^ 40 * 5599305 * 2
def baseEnd_5599305 : Nat := 2875134796123320427136771

theorem tailTrace_5599305 : CollatzResearch.WordTrace tailWord_5599305 prefixEnd_5599305 2875134796123320427136771 := by
  unfold tailWord_5599305
  simp only [CollatzResearch.WordTrace]
  refine ⟨204223430979681745005359369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136148953986454496670239579 204223430979681745005359369)
  ·
    refine ⟨153167573234761308754019527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204223430979681745005359369 153167573234761308754019527)
    ·
      refine ⟨229751359852141963131029291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153167573234761308754019527 229751359852141963131029291)
      ·
        refine ⟨344627039778212944696543937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229751359852141963131029291 344627039778212944696543937)
        ·
          refine ⟨258470279833659708522407953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 344627039778212944696543937 258470279833659708522407953)
          ·
            refine ⟨193852709875244781391805965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 258470279833659708522407953 193852709875244781391805965)
            ·
              refine ⟨72694766203216793021927237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 193852709875244781391805965 72694766203216793021927237)
              ·
                refine ⟨13630268663103148691611357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72694766203216793021927237 13630268663103148691611357)
                ·
                  refine ⟨5111350748663680759354259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13630268663103148691611357 5111350748663680759354259)
                  ·
                    refine ⟨7667026122995521139031389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5111350748663680759354259 7667026122995521139031389)
                    ·
                      refine ⟨2875134796123320427136771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7667026122995521139031389 2875134796123320427136771)
                      ·
                        rfl

theorem cell23_5599305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 4, 3, 1, 3].length) (baseStart_5599305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5599305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5599305 prefixEnd_5599305 := by exact prefixLift 5599305
  have htrace : WordTrace (prefixWord ++ tailWord_5599305) baseStart_5599305 baseEnd_5599305 := by
    simpa [prefixWord, tailWord_5599305, baseEnd_5599305] using wordTrace_append hprefix tailTrace_5599305
  have hstable : (prefixWord ++ tailWord_5599305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5599305).length < 2 ^ (prefixWord ++ tailWord_5599305).sum := by decide
  have hdescent : baseEnd_5599305 < baseStart_5599305 := by decide
  rcases family_descends (prefixWord ++ tailWord_5599305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5599308 : List Nat := [2, 2, 1, 3, 1, 1, 2, 3, 3, 5]
def baseStart_5599308 : Nat := 118140960795 + 5599308 * 2 ^ 59
def prefixEnd_5599308 : Nat := 4983230072969 + 3 ^ 40 * 5599308 * 2
def baseEnd_5599308 : Nat := 958378778855094638466419

theorem tailTrace_5599308 : CollatzResearch.WordTrace tailWord_5599308 prefixEnd_5599308 958378778855094638466419 := by
  unfold tailWord_5599308
  simp only [CollatzResearch.WordTrace]
  refine ⟨102111770199335438258859289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136149026932447251011812385 102111770199335438258859289)
  ·
    refine ⟨76583827649501578694144467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102111770199335438258859289 76583827649501578694144467)
    ·
      refine ⟨114875741474252368041216701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76583827649501578694144467 114875741474252368041216701)
      ·
        refine ⟨43078403052844638015456263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114875741474252368041216701 43078403052844638015456263)
        ·
          refine ⟨64617604579266957023184395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43078403052844638015456263 64617604579266957023184395)
          ·
            refine ⟨96926406868900435534776593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64617604579266957023184395 96926406868900435534776593)
            ·
              refine ⟨72694805151675326651082445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96926406868900435534776593 72694805151675326651082445)
              ·
                refine ⟨27260551931878247494155917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72694805151675326651082445 27260551931878247494155917)
                ·
                  refine ⟨10222706974454342810308469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27260551931878247494155917 10222706974454342810308469)
                  ·
                    refine ⟨958378778855094638466419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10222706974454342810308469 958378778855094638466419)
                    ·
                      rfl

theorem cell23_5599308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 3, 3, 5].length) (baseStart_5599308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5599308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5599308 prefixEnd_5599308 := by exact prefixLift 5599308
  have htrace : WordTrace (prefixWord ++ tailWord_5599308) baseStart_5599308 baseEnd_5599308 := by
    simpa [prefixWord, tailWord_5599308, baseEnd_5599308] using wordTrace_append hprefix tailTrace_5599308
  have hstable : (prefixWord ++ tailWord_5599308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5599308).length < 2 ^ (prefixWord ++ tailWord_5599308).sum := by decide
  have hdescent : baseEnd_5599308 < baseStart_5599308 := by decide
  rcases family_descends (prefixWord ++ tailWord_5599308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5599326 : List Nat := [4, 4, 1, 1, 2, 1, 1, 2, 2, 2, 3]
def baseStart_5599326 : Nat := 118140960795 + 5599326 * 2 ^ 59
def prefixEnd_5599326 : Nat := 4983230072969 + 3 ^ 40 * 5599326 * 2
def baseEnd_5599326 : Nat := 2875145579217064844974175

theorem tailTrace_5599326 : CollatzResearch.WordTrace tailWord_5599326 prefixEnd_5599326 2875145579217064844974175 := by
  unfold tailWord_5599326
  simp only [CollatzResearch.WordTrace]
  refine ⟨25528024614075708198984229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136149464608403777061249221 25528024614075708198984229)
  ·
    refine ⟨4786504615139195287309543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25528024614075708198984229 4786504615139195287309543)
    ·
      refine ⟨7179756922708792930964315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4786504615139195287309543 7179756922708792930964315)
      ·
        refine ⟨10769635384063189396446473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7179756922708792930964315 10769635384063189396446473)
        ·
          refine ⟨8077226538047392047334855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10769635384063189396446473 8077226538047392047334855)
          ·
            refine ⟨12115839807071088071002283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8077226538047392047334855 12115839807071088071002283)
            ·
              refine ⟨18173759710606632106503425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12115839807071088071002283 18173759710606632106503425)
              ·
                refine ⟨13630319782954974079877569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18173759710606632106503425 13630319782954974079877569)
                ·
                  refine ⟨10222739837216230559908177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13630319782954974079877569 10222739837216230559908177)
                  ·
                    refine ⟨7667054877912172919931133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10222739837216230559908177 7667054877912172919931133)
                    ·
                      refine ⟨2875145579217064844974175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7667054877912172919931133 2875145579217064844974175)
                      ·
                        rfl

theorem cell23_5599326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_5599326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5599326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5599326 prefixEnd_5599326 := by exact prefixLift 5599326
  have htrace : WordTrace (prefixWord ++ tailWord_5599326) baseStart_5599326 baseEnd_5599326 := by
    simpa [prefixWord, tailWord_5599326, baseEnd_5599326] using wordTrace_append hprefix tailTrace_5599326
  have hstable : (prefixWord ++ tailWord_5599326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5599326).length < 2 ^ (prefixWord ++ tailWord_5599326).sum := by decide
  have hdescent : baseEnd_5599326 < baseStart_5599326 := by decide
  rcases family_descends (prefixWord ++ tailWord_5599326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5599379 : List Nat := [1, 1, 1, 2, 1, 2, 3, 7, 1, 2, 2]
def baseStart_5599379 : Nat := 118140960795 + 5599379 * 2 ^ 59
def prefixEnd_5599379 : Nat := 4983230072969 + 3 ^ 40 * 5599379 * 2
def baseEnd_5599379 : Nat := 2875172793691753137611431

theorem tailTrace_5599379 : CollatzResearch.WordTrace tailWord_5599379 prefixEnd_5599379 2875172793691753137611431 := by
  unfold tailWord_5599379
  simp only [CollatzResearch.WordTrace]
  refine ⟨204226129981413655643553191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136150753320942437095702127 204226129981413655643553191)
  ·
    refine ⟨306339194972120483465329787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204226129981413655643553191 306339194972120483465329787)
    ·
      refine ⟨459508792458180725197994681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 306339194972120483465329787 459508792458180725197994681)
      ·
        refine ⟨344631594343635543898496011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 459508792458180725197994681 344631594343635543898496011)
        ·
          refine ⟨516947391515453315847744017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 344631594343635543898496011 516947391515453315847744017)
          ·
            refine ⟨387710543636589986885808013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 516947391515453315847744017 387710543636589986885808013)
            ·
              refine ⟨145391453863721245082178005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 387710543636589986885808013 145391453863721245082178005)
              ·
                refine ⟨3407612199930966681613547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 145391453863721245082178005 3407612199930966681613547)
                ·
                  refine ⟨5111418299896450022420321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3407612199930966681613547 5111418299896450022420321)
                  ·
                    refine ⟨3833563724922337516815241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5111418299896450022420321 3833563724922337516815241)
                    ·
                      refine ⟨2875172793691753137611431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3833563724922337516815241 2875172793691753137611431)
                      ·
                        rfl

theorem cell23_5599379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 7, 1, 2, 2].length) (baseStart_5599379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5599379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5599379 prefixEnd_5599379 := by exact prefixLift 5599379
  have htrace : WordTrace (prefixWord ++ tailWord_5599379) baseStart_5599379 baseEnd_5599379 := by
    simpa [prefixWord, tailWord_5599379, baseEnd_5599379] using wordTrace_append hprefix tailTrace_5599379
  have hstable : (prefixWord ++ tailWord_5599379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5599379).length < 2 ^ (prefixWord ++ tailWord_5599379).sum := by decide
  have hdescent : baseEnd_5599379 < baseStart_5599379 := by decide
  rcases family_descends (prefixWord ++ tailWord_5599379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5599390 : List Nat := [4, 3, 1, 1, 3, 2, 2, 2, 1, 1, 3]
def baseStart_5599390 : Nat := 118140960795 + 5599390 * 2 ^ 59
def prefixEnd_5599390 : Nat := 4983230072969 + 3 ^ 40 * 5599390 * 2
def baseEnd_5599390 : Nat := 2875178441978952594573881

theorem tailTrace_5599390 : CollatzResearch.WordTrace tailWord_5599390 prefixEnd_5599390 2875178441978952594573881 := by
  unfold tailWord_5599390
  simp only [CollatzResearch.WordTrace]
  refine ⟨25528316398046725565275453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136151020789582536348135749 25528316398046725565275453)
  ·
    refine ⟨9573118649267522086978295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25528316398046725565275453 9573118649267522086978295)
    ·
      refine ⟨14359677973901283130467443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9573118649267522086978295 14359677973901283130467443)
      ·
        refine ⟨21539516960851924695701165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14359677973901283130467443 21539516960851924695701165)
        ·
          refine ⟨8077318860319471760887937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21539516960851924695701165 8077318860319471760887937)
          ·
            refine ⟨6057989145239603820665953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8077318860319471760887937 6057989145239603820665953)
            ·
              refine ⟨4543491858929702865499465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6057989145239603820665953 4543491858929702865499465)
              ·
                refine ⟨3407618894197277149124599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4543491858929702865499465 3407618894197277149124599)
                ·
                  refine ⟨5111428341295915723686899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3407618894197277149124599 5111428341295915723686899)
                  ·
                    refine ⟨7667142511943873585530349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5111428341295915723686899 7667142511943873585530349)
                    ·
                      refine ⟨2875178441978952594573881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7667142511943873585530349 2875178441978952594573881)
                      ·
                        rfl

theorem cell23_5599390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 2, 2, 1, 1, 3].length) (baseStart_5599390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5599390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5599390 prefixEnd_5599390 := by exact prefixLift 5599390
  have htrace : WordTrace (prefixWord ++ tailWord_5599390) baseStart_5599390 baseEnd_5599390 := by
    simpa [prefixWord, tailWord_5599390, baseEnd_5599390] using wordTrace_append hprefix tailTrace_5599390
  have hstable : (prefixWord ++ tailWord_5599390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5599390).length < 2 ^ (prefixWord ++ tailWord_5599390).sum := by decide
  have hdescent : baseEnd_5599390 < baseStart_5599390 := by decide
  rcases family_descends (prefixWord ++ tailWord_5599390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5599446 : List Nat := [5, 2, 1, 2, 1, 2, 1, 1, 4, 1, 3]
def baseStart_5599446 : Nat := 118140960795 + 5599446 * 2 ^ 59
def prefixEnd_5599446 : Nat := 4983230072969 + 3 ^ 40 * 5599446 * 2
def baseEnd_5599446 : Nat := 2875207196895604375473623

theorem tailTrace_5599446 : CollatzResearch.WordTrace tailWord_5599446 prefixEnd_5599446 2875207196895604375473623 := by
  unfold tailWord_5599446
  simp only [CollatzResearch.WordTrace]
  refine ⟨12764285854510682880390137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 136152382448113950724161461 12764285854510682880390137)
  ·
    refine ⟨9573214390883012160292603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12764285854510682880390137 9573214390883012160292603)
    ·
      refine ⟨14359821586324518240438905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9573214390883012160292603 14359821586324518240438905)
      ·
        refine ⟨10769866189743388680329179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14359821586324518240438905 10769866189743388680329179)
        ·
          refine ⟨16154799284615083020493769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10769866189743388680329179 16154799284615083020493769)
          ·
            refine ⟨12116099463461312265370327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16154799284615083020493769 12116099463461312265370327)
            ·
              refine ⟨18174149195191968398055491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12116099463461312265370327 18174149195191968398055491)
              ·
                refine ⟨27261223792787952597083237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18174149195191968398055491 27261223792787952597083237)
                ·
                  refine ⟨5111479461147741111953107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27261223792787952597083237 5111479461147741111953107)
                  ·
                    refine ⟨7667219191721611667929661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5111479461147741111953107 7667219191721611667929661)
                    ·
                      refine ⟨2875207196895604375473623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7667219191721611667929661 2875207196895604375473623)
                      ·
                        rfl

theorem cell23_5599446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_5599446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5599446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5599446 prefixEnd_5599446 := by exact prefixLift 5599446
  have htrace : WordTrace (prefixWord ++ tailWord_5599446) baseStart_5599446 baseEnd_5599446 := by
    simpa [prefixWord, tailWord_5599446, baseEnd_5599446] using wordTrace_append hprefix tailTrace_5599446
  have hstable : (prefixWord ++ tailWord_5599446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5599446).length < 2 ^ (prefixWord ++ tailWord_5599446).sum := by decide
  have hdescent : baseEnd_5599446 < baseStart_5599446 := by decide
  rcases family_descends (prefixWord ++ tailWord_5599446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5599485 : List Nat := [1, 4, 1, 1, 1, 1, 1, 4, 1, 5, 3]
def baseStart_5599485 : Nat := 118140960795 + 5599485 * 2 ^ 59
def prefixEnd_5599485 : Nat := 4983230072969 + 3 ^ 40 * 5599485 * 2
def baseEnd_5599485 : Nat := 2875227222641129722885943

theorem tailTrace_5599485 : CollatzResearch.WordTrace tailWord_5599485 prefixEnd_5599485 2875227222641129722885943 := by
  unfold tailWord_5599485
  simp only [CollatzResearch.WordTrace]
  refine ⟨204229996119029635746911909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136153330746019757164607939 204229996119029635746911909)
  ·
    refine ⟨38293124272318056702545983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 204229996119029635746911909 38293124272318056702545983)
    ·
      refine ⟨57439686408477085053818975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38293124272318056702545983 57439686408477085053818975)
      ·
        refine ⟨86159529612715627580728463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57439686408477085053818975 86159529612715627580728463)
        ·
          refine ⟨129239294419073441371092695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86159529612715627580728463 129239294419073441371092695)
          ·
            refine ⟨193858941628610162056639043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129239294419073441371092695 193858941628610162056639043)
            ·
              refine ⟨290788412442915243084958565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 193858941628610162056639043 290788412442915243084958565)
              ·
                refine ⟨54522827333046608078429731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 290788412442915243084958565 54522827333046608078429731)
                ·
                  refine ⟨81784240999569912117644597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54522827333046608078429731 81784240999569912117644597)
                  ·
                    refine ⟨7667272593709679261029181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 81784240999569912117644597 7667272593709679261029181)
                    ·
                      refine ⟨2875227222641129722885943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7667272593709679261029181 2875227222641129722885943)
                      ·
                        rfl

theorem cell23_5599485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 4, 1, 5, 3].length) (baseStart_5599485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5599485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5599485 prefixEnd_5599485 := by exact prefixLift 5599485
  have htrace : WordTrace (prefixWord ++ tailWord_5599485) baseStart_5599485 baseEnd_5599485 := by
    simpa [prefixWord, tailWord_5599485, baseEnd_5599485] using wordTrace_append hprefix tailTrace_5599485
  have hstable : (prefixWord ++ tailWord_5599485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5599485).length < 2 ^ (prefixWord ++ tailWord_5599485).sum := by decide
  have hdescent : baseEnd_5599485 < baseStart_5599485 := by decide
  rcases family_descends (prefixWord ++ tailWord_5599485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5599505 : List Nat := [1, 2, 2, 1, 1, 5, 1, 1, 4, 5]
def baseStart_5599505 : Nat := 118140960795 + 5599505 * 2 ^ 59
def prefixEnd_5599505 : Nat := 4983230072969 + 3 ^ 40 * 5599505 * 2
def baseEnd_5599505 : Nat := 958412497418073214878617

theorem tailTrace_5599505 : CollatzResearch.WordTrace tailWord_5599505 prefixEnd_5599505 958412497418073214878617 := by
  unfold tailWord_5599505
  simp only [CollatzResearch.WordTrace]
  refine ⟨204230725578957179162639969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136153817052638119441759979 204230725578957179162639969)
  ·
    refine ⟨153173044184217884371979977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204230725578957179162639969 153173044184217884371979977)
    ·
      refine ⟨114879783138163413278984983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153173044184217884371979977 114879783138163413278984983)
      ·
        refine ⟨172319674707245119918477475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114879783138163413278984983 172319674707245119918477475)
        ·
          refine ⟨258479512060867679877716213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172319674707245119918477475 258479512060867679877716213)
          ·
            refine ⟨24232454255706344988535895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 258479512060867679877716213 24232454255706344988535895)
            ·
              refine ⟨36348681383559517482803843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24232454255706344988535895 36348681383559517482803843)
              ·
                refine ⟨54523022075339276224205765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36348681383559517482803843 54523022075339276224205765)
                ·
                  refine ⟨10223066639126114292038581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54523022075339276224205765 10223066639126114292038581)
                  ·
                    refine ⟨958412497418073214878617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10223066639126114292038581 958412497418073214878617)
                    ·
                      rfl

theorem cell23_5599505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 5].length) (baseStart_5599505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5599505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5599505 prefixEnd_5599505 := by exact prefixLift 5599505
  have htrace : WordTrace (prefixWord ++ tailWord_5599505) baseStart_5599505 baseEnd_5599505 := by
    simpa [prefixWord, tailWord_5599505, baseEnd_5599505] using wordTrace_append hprefix tailTrace_5599505
  have hstable : (prefixWord ++ tailWord_5599505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5599505).length < 2 ^ (prefixWord ++ tailWord_5599505).sum := by decide
  have hdescent : baseEnd_5599505 < baseStart_5599505 := by decide
  rcases family_descends (prefixWord ++ tailWord_5599505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5599512 : List Nat := [2, 1, 2, 3, 1, 2, 2, 1, 2, 5, 2]
def baseStart_5599512 : Nat := 118140960795 + 5599512 * 2 ^ 59
def prefixEnd_5599512 : Nat := 4983230072969 + 3 ^ 40 * 5599512 * 2
def baseEnd_5599512 : Nat := 2875241086618801117248319

theorem tailTrace_5599512 : CollatzResearch.WordTrace tailWord_5599512 prefixEnd_5599512 2875241086618801117248319 := by
  unfold tailWord_5599512
  simp only [CollatzResearch.WordTrace]
  refine ⟨102115490444965909679072395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136153987259954546238763193 102115490444965909679072395)
  ·
    refine ⟨153173235667448864518608593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102115490444965909679072395 153173235667448864518608593)
    ·
      refine ⟨114879926750586648388956445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153173235667448864518608593 114879926750586648388956445)
      ·
        refine ⟨43079972531469993145858667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114879926750586648388956445 43079972531469993145858667)
        ·
          refine ⟨64619958797204989718788001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43079972531469993145858667 64619958797204989718788001)
          ·
            refine ⟨48464969097903742289091001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64619958797204989718788001 48464969097903742289091001)
            ·
              refine ⟨36348726823427806716818251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48464969097903742289091001 36348726823427806716818251)
              ·
                refine ⟨54523090235141710075227377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36348726823427806716818251 54523090235141710075227377)
                ·
                  refine ⟨40892317676356282556420533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54523090235141710075227377 40892317676356282556420533)
                  ·
                    refine ⟨3833654782158401489664425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40892317676356282556420533 3833654782158401489664425)
                    ·
                      refine ⟨2875241086618801117248319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3833654782158401489664425 2875241086618801117248319)
                      ·
                        rfl

theorem cell23_5599512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 1, 2, 5, 2].length) (baseStart_5599512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5599512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5599512 prefixEnd_5599512 := by exact prefixLift 5599512
  have htrace : WordTrace (prefixWord ++ tailWord_5599512) baseStart_5599512 baseEnd_5599512 := by
    simpa [prefixWord, tailWord_5599512, baseEnd_5599512] using wordTrace_append hprefix tailTrace_5599512
  have hstable : (prefixWord ++ tailWord_5599512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5599512).length < 2 ^ (prefixWord ++ tailWord_5599512).sum := by decide
  have hdescent : baseEnd_5599512 < baseStart_5599512 := by decide
  rcases family_descends (prefixWord ++ tailWord_5599512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5599596 : List Nat := [2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 3]
def baseStart_5599596 : Nat := 118140960795 + 5599596 * 2 ^ 59
def prefixEnd_5599596 : Nat := 4983230072969 + 3 ^ 40 * 5599596 * 2
def baseEnd_5599596 : Nat := 2875284218993778788597933

theorem tailTrace_5599596 : CollatzResearch.WordTrace tailWord_5599596 prefixEnd_5599596 2875284218993778788597933 := by
  unfold tailWord_5599596
  simp only [CollatzResearch.WordTrace]
  refine ⟨102117022310813750852101321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136156029747751667802801761 102117022310813750852101321)
  ·
    refine ⟨76587766733110313139075991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102117022310813750852101321 76587766733110313139075991)
    ·
      refine ⟨114881650099665469708613987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76587766733110313139075991 114881650099665469708613987)
      ·
        refine ⟨172322475149498204562920981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114881650099665469708613987 172322475149498204562920981)
        ·
          refine ⟨8077616022632728338886921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 172322475149498204562920981 8077616022632728338886921)
          ·
            refine ⟨6058212016974546254165191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8077616022632728338886921 6058212016974546254165191)
            ·
              refine ⟨9087318025461819381247787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6058212016974546254165191 9087318025461819381247787)
              ·
                refine ⟨13630977038192729071871681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9087318025461819381247787 13630977038192729071871681)
                ·
                  refine ⟨10223232778644546803903761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13630977038192729071871681 10223232778644546803903761)
                  ·
                    refine ⟨7667424583983410102927821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10223232778644546803903761 7667424583983410102927821)
                    ·
                      refine ⟨2875284218993778788597933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7667424583983410102927821 2875284218993778788597933)
                      ·
                        rfl

theorem cell23_5599596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 3].length) (baseStart_5599596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5599596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5599596 prefixEnd_5599596 := by exact prefixLift 5599596
  have htrace : WordTrace (prefixWord ++ tailWord_5599596) baseStart_5599596 baseEnd_5599596 := by
    simpa [prefixWord, tailWord_5599596, baseEnd_5599596] using wordTrace_append hprefix tailTrace_5599596
  have hstable : (prefixWord ++ tailWord_5599596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5599596).length < 2 ^ (prefixWord ++ tailWord_5599596).sum := by decide
  have hdescent : baseEnd_5599596 < baseStart_5599596 := by decide
  rcases family_descends (prefixWord ++ tailWord_5599596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5599646 : List Nat := [4, 3, 1, 2, 1, 1, 1, 4, 1, 5]
def baseStart_5599646 : Nat := 118140960795 + 5599646 * 2 ^ 59
def prefixEnd_5599646 : Nat := 4983230072969 + 3 ^ 40 * 5599646 * 2
def baseEnd_5599646 : Nat := 958436631008834530990901

theorem tailTrace_5599646 : CollatzResearch.WordTrace tailWord_5599646 prefixEnd_5599646 958436631008834530990901 := by
  unfold tailWord_5599646
  simp only [CollatzResearch.WordTrace]
  refine ⟨25529483533930795030440349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136157245514297573495681861 25529483533930795030440349)
  ·
    refine ⟨9573556325224048136415131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25529483533930795030440349 9573556325224048136415131)
    ·
      refine ⟨14360334487836072204622697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9573556325224048136415131 14360334487836072204622697)
      ·
        refine ⟨10770250865877054153467023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14360334487836072204622697 10770250865877054153467023)
        ·
          refine ⟨16155376298815581230200535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10770250865877054153467023 16155376298815581230200535)
          ·
            refine ⟨24233064448223371845300803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16155376298815581230200535 24233064448223371845300803)
            ·
              refine ⟨36349596672335057767951205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24233064448223371845300803 36349596672335057767951205)
              ·
                refine ⟨6815549376062823331490851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36349596672335057767951205 6815549376062823331490851)
                ·
                  refine ⟨10223324064094234997236277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6815549376062823331490851 10223324064094234997236277)
                  ·
                    refine ⟨958436631008834530990901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10223324064094234997236277 958436631008834530990901)
                    ·
                      rfl

theorem cell23_5599646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 4, 1, 5].length) (baseStart_5599646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5599646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5599646 prefixEnd_5599646 := by exact prefixLift 5599646
  have htrace : WordTrace (prefixWord ++ tailWord_5599646) baseStart_5599646 baseEnd_5599646 := by
    simpa [prefixWord, tailWord_5599646, baseEnd_5599646] using wordTrace_append hprefix tailTrace_5599646
  have hstable : (prefixWord ++ tailWord_5599646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5599646).length < 2 ^ (prefixWord ++ tailWord_5599646).sum := by decide
  have hdescent : baseEnd_5599646 < baseStart_5599646 := by decide
  rcases family_descends (prefixWord ++ tailWord_5599646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5599675 : List Nat := [1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 8]
def baseStart_5599675 : Nat := 118140960795 + 5599675 * 2 ^ 59
def prefixEnd_5599675 : Nat := 4983230072969 + 3 ^ 40 * 5599675 * 2
def baseEnd_5599675 : Nat := 2875324783965483979510069

theorem tailTrace_5599675 : CollatzResearch.WordTrace tailWord_5599675 prefixEnd_5599675 2875324783965483979510069 := by
  unfold tailWord_5599675
  simp only [CollatzResearch.WordTrace]
  refine ⟨204236925988341298196328479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136157950658894198797552319 204236925988341298196328479)
  ·
    refine ⟨306355388982511947294492719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204236925988341298196328479 306355388982511947294492719)
    ·
      refine ⟨459533083473767920941739079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 306355388982511947294492719 459533083473767920941739079)
      ·
        refine ⟨689299625210651881412608619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 459533083473767920941739079 689299625210651881412608619)
        ·
          refine ⟨1033949437815977822118912929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 689299625210651881412608619 1033949437815977822118912929)
          ·
            refine ⟨775462078361983366589184697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1033949437815977822118912929 775462078361983366589184697)
            ·
              refine ⟨581596558771487524941888523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 775462078361983366589184697 581596558771487524941888523)
              ·
                refine ⟨872394838157231287412832785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 581596558771487524941888523 872394838157231287412832785)
                ·
                  refine ⟨654296128617923465559624589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 872394838157231287412832785 654296128617923465559624589)
                  ·
                    refine ⟨245361048231721299584859221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 654296128617923465559624589 245361048231721299584859221)
                    ·
                      refine ⟨2875324783965483979510069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 245361048231721299584859221 2875324783965483979510069)
                      ·
                        rfl

theorem cell23_5599675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 8].length) (baseStart_5599675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5599675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5599675 prefixEnd_5599675 := by exact prefixLift 5599675
  have htrace : WordTrace (prefixWord ++ tailWord_5599675) baseStart_5599675 baseEnd_5599675 := by
    simpa [prefixWord, tailWord_5599675, baseEnd_5599675] using wordTrace_append hprefix tailTrace_5599675
  have hstable : (prefixWord ++ tailWord_5599675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5599675).length < 2 ^ (prefixWord ++ tailWord_5599675).sum := by decide
  have hdescent : baseEnd_5599675 < baseStart_5599675 := by decide
  rcases family_descends (prefixWord ++ tailWord_5599675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5599750 : List Nat := [6, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3]
def baseStart_5599750 : Nat := 118140960795 + 5599750 * 2 ^ 59
def prefixEnd_5599750 : Nat := 4983230072969 + 3 ^ 40 * 5599750 * 2
def baseEnd_5599750 : Nat := 2875363295014571186072225

theorem tailTrace_5599750 : CollatzResearch.WordTrace tailWord_5599750 prefixEnd_5599750 2875363295014571186072225 := by
  unfold tailWord_5599750
  simp only [CollatzResearch.WordTrace]
  refine ⟨6382489420720924562665897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 136159774308713057336872469 6382489420720924562665897)
  ·
    refine ⟨4786867065540693421999423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6382489420720924562665897 4786867065540693421999423)
    ·
      refine ⟨7180300598311040132999135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4786867065540693421999423 7180300598311040132999135)
      ·
        refine ⟨10770450897466560199498703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7180300598311040132999135 10770450897466560199498703)
        ·
          refine ⟨16155676346199840299248055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10770450897466560199498703 16155676346199840299248055)
          ·
            refine ⟨24233514519299760448872083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16155676346199840299248055 24233514519299760448872083)
            ·
              refine ⟨36350271778949640673308125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24233514519299760448872083 36350271778949640673308125)
              ·
                refine ⟨13631351917106115252490547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36350271778949640673308125 13631351917106115252490547)
                ·
                  refine ⟨20447027875659172878735821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13631351917106115252490547 20447027875659172878735821)
                  ·
                    refine ⟨7667635453372189829525933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20447027875659172878735821 7667635453372189829525933)
                    ·
                      refine ⟨2875363295014571186072225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7667635453372189829525933 2875363295014571186072225)
                      ·
                        rfl

theorem cell23_5599750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_5599750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5599750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5599750 prefixEnd_5599750 := by exact prefixLift 5599750
  have htrace : WordTrace (prefixWord ++ tailWord_5599750) baseStart_5599750 baseEnd_5599750 := by
    simpa [prefixWord, tailWord_5599750, baseEnd_5599750] using wordTrace_append hprefix tailTrace_5599750
  have hstable : (prefixWord ++ tailWord_5599750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5599750).length < 2 ^ (prefixWord ++ tailWord_5599750).sum := by decide
  have hdescent : baseEnd_5599750 < baseStart_5599750 := by decide
  rcases family_descends (prefixWord ++ tailWord_5599750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5599756 : List Nat := [2, 2, 1, 2, 4, 1, 1, 3, 1, 4, 2]
def baseStart_5599756 : Nat := 118140960795 + 5599756 * 2 ^ 59
def prefixEnd_5599756 : Nat := 4983230072969 + 3 ^ 40 * 5599756 * 2
def baseEnd_5599756 : Nat := 2875366375898498162597197

theorem tailTrace_5599756 : CollatzResearch.WordTrace tailWord_5599756 prefixEnd_5599756 2875366375898498162597197 := by
  unfold tailWord_5599756
  simp only [CollatzResearch.WordTrace]
  refine ⟨102119940150523924515013561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136159920200698566020018081 102119940150523924515013561)
  ·
    refine ⟨76589955112892943386260171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102119940150523924515013561 76589955112892943386260171)
    ·
      refine ⟨114884932669339415079390257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76589955112892943386260171 114884932669339415079390257)
      ·
        refine ⟨86163699502004561309542693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114884932669339415079390257 86163699502004561309542693)
        ·
          refine ⟨16155693656625855245539255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 86163699502004561309542693 16155693656625855245539255)
          ·
            refine ⟨24233540484938782868308883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16155693656625855245539255 24233540484938782868308883)
            ·
              refine ⟨36350310727408174302463325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24233540484938782868308883 36350310727408174302463325)
              ·
                refine ⟨13631366522778065363423747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36350310727408174302463325 13631366522778065363423747)
                ·
                  refine ⟨20447049784167098045135621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13631366522778065363423747 20447049784167098045135621)
                  ·
                    refine ⟨3833821834531330883462929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20447049784167098045135621 3833821834531330883462929)
                    ·
                      refine ⟨2875366375898498162597197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3833821834531330883462929 2875366375898498162597197)
                      ·
                        rfl

theorem cell23_5599756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 3, 1, 4, 2].length) (baseStart_5599756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5599756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5599756 prefixEnd_5599756 := by exact prefixLift 5599756
  have htrace : WordTrace (prefixWord ++ tailWord_5599756) baseStart_5599756 baseEnd_5599756 := by
    simpa [prefixWord, tailWord_5599756, baseEnd_5599756] using wordTrace_append hprefix tailTrace_5599756
  have hstable : (prefixWord ++ tailWord_5599756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5599756).length < 2 ^ (prefixWord ++ tailWord_5599756).sum := by decide
  have hdescent : baseEnd_5599756 < baseStart_5599756 := by decide
  rcases family_descends (prefixWord ++ tailWord_5599756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5599790 : List Nat := [4, 1, 3, 1, 3, 1, 1, 1, 4, 2, 2]
def baseStart_5599790 : Nat := 118140960795 + 5599790 * 2 ^ 59
def prefixEnd_5599790 : Nat := 4983230072969 + 3 ^ 40 * 5599790 * 2
def baseEnd_5599790 : Nat := 2875383834240751029572041

theorem tailTrace_5599790 : CollatzResearch.WordTrace tailWord_5599790 prefixEnd_5599790 2875383834240751029572041 := by
  unfold tailWord_5599790
  simp only [CollatzResearch.WordTrace]
  refine ⟨25530140047865584104595603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136160746921949781891176549 25530140047865584104595603)
  ·
    refine ⟨38295210071798376156893405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25530140047865584104595603 38295210071798376156893405)
    ·
      refine ⟨14360703776924391058835027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38295210071798376156893405 14360703776924391058835027)
      ·
        refine ⟨21541055665386586588252541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14360703776924391058835027 21541055665386586588252541)
        ·
          refine ⟨8077895874519969970594703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21541055665386586588252541 8077895874519969970594703)
          ·
            refine ⟨12116843811779954955892055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8077895874519969970594703 12116843811779954955892055)
            ·
              refine ⟨18175265717669932433838083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12116843811779954955892055 18175265717669932433838083)
              ·
                refine ⟨27262898576504898650757125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18175265717669932433838083 27262898576504898650757125)
                ·
                  refine ⟨5111793483094668497016961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27262898576504898650757125 5111793483094668497016961)
                  ·
                    refine ⟨3833845112321001372762721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5111793483094668497016961 3833845112321001372762721)
                    ·
                      refine ⟨2875383834240751029572041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3833845112321001372762721 2875383834240751029572041)
                      ·
                        rfl

theorem cell23_5599790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 1, 4, 2, 2].length) (baseStart_5599790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5599790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5599790 prefixEnd_5599790 := by exact prefixLift 5599790
  have htrace : WordTrace (prefixWord ++ tailWord_5599790) baseStart_5599790 baseEnd_5599790 := by
    simpa [prefixWord, tailWord_5599790, baseEnd_5599790] using wordTrace_append hprefix tailTrace_5599790
  have hstable : (prefixWord ++ tailWord_5599790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5599790).length < 2 ^ (prefixWord ++ tailWord_5599790).sum := by decide
  have hdescent : baseEnd_5599790 < baseStart_5599790 := by decide
  rcases family_descends (prefixWord ++ tailWord_5599790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5599809 : List Nat := [1, 2, 5, 1, 1, 2, 1, 2, 1, 7]
def baseStart_5599809 : Nat := 118140960795 + 5599809 * 2 ^ 59
def prefixEnd_5599809 : Nat := 4983230072969 + 3 ^ 40 * 5599809 * 2
def baseEnd_5599809 : Nat := 958464530124395485078151

theorem tailTrace_5599809 : CollatzResearch.WordTrace tailWord_5599809 prefixEnd_5599809 958464530124395485078151 := by
  unfold tailWord_5599809
  simp only [CollatzResearch.WordTrace]
  refine ⟨204241813369855839081706481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136161208913237226054470987 204241813369855839081706481)
  ·
    refine ⟨153181360027391879311279861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204241813369855839081706481 153181360027391879311279861)
    ·
      refine ⟨14360752502567988685432487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 153181360027391879311279861 14360752502567988685432487)
      ·
        refine ⟨21541128753851983028148731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14360752502567988685432487 21541128753851983028148731)
        ·
          refine ⟨32311693130777974542223097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21541128753851983028148731 32311693130777974542223097)
          ·
            refine ⟨24233769848083480906667323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32311693130777974542223097 24233769848083480906667323)
            ·
              refine ⟨36350654772125221360000985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24233769848083480906667323 36350654772125221360000985)
              ·
                refine ⟨27262991079093916020000739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36350654772125221360000985 27262991079093916020000739)
                ·
                  refine ⟨40894486618640874030001109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27262991079093916020000739 40894486618640874030001109)
                  ·
                    refine ⟨958464530124395485078151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40894486618640874030001109 958464530124395485078151)
                    ·
                      rfl

theorem cell23_5599809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_5599809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5599809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5599809 prefixEnd_5599809 := by exact prefixLift 5599809
  have htrace : WordTrace (prefixWord ++ tailWord_5599809) baseStart_5599809 baseEnd_5599809 := by
    simpa [prefixWord, tailWord_5599809, baseEnd_5599809] using wordTrace_append hprefix tailTrace_5599809
  have hstable : (prefixWord ++ tailWord_5599809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5599809).length < 2 ^ (prefixWord ++ tailWord_5599809).sum := by decide
  have hdescent : baseEnd_5599809 < baseStart_5599809 := by decide
  rcases family_descends (prefixWord ++ tailWord_5599809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5599829 : List Nat := [1, 3, 2, 2, 1, 1, 4, 1, 1, 3, 4]
def baseStart_5599829 : Nat := 118140960795 + 5599829 * 2 ^ 59
def prefixEnd_5599829 : Nat := 4983230072969 + 3 ^ 40 * 5599829 * 2
def baseEnd_5599829 : Nat := 2875403859986276376984361

theorem tailTrace_5599829 : CollatzResearch.WordTrace tailWord_5599829 prefixEnd_5599829 2875403859986276376984361 := by
  unfold tailWord_5599829
  simp only [CollatzResearch.WordTrace]
  refine ⟨204242542829783382497434541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136161695219855588331623027 204242542829783382497434541)
  ·
    refine ⟨76590953561168768436537953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 204242542829783382497434541 76590953561168768436537953)
    ·
      refine ⟨57443215170876576327403465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76590953561168768436537953 57443215170876576327403465)
      ·
        refine ⟨43082411378157432245552599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57443215170876576327403465 43082411378157432245552599)
        ·
          refine ⟨64623617067236148368328899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43082411378157432245552599 64623617067236148368328899)
          ·
            refine ⟨96935425600854222552493349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64623617067236148368328899 96935425600854222552493349)
            ·
              refine ⟨18175392300160166728592503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 96935425600854222552493349 18175392300160166728592503)
              ·
                refine ⟨27263088450240250092888755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18175392300160166728592503 27263088450240250092888755)
                ·
                  refine ⟨40894632675360375139333133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27263088450240250092888755 40894632675360375139333133)
                  ·
                    refine ⟨15335487253260140677249925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40894632675360375139333133 15335487253260140677249925)
                    ·
                      refine ⟨2875403859986276376984361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15335487253260140677249925 2875403859986276376984361)
                      ·
                        rfl

theorem cell23_5599829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 1, 1, 3, 4].length) (baseStart_5599829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5599829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5599829 prefixEnd_5599829 := by exact prefixLift 5599829
  have htrace : WordTrace (prefixWord ++ tailWord_5599829) baseStart_5599829 baseEnd_5599829 := by
    simpa [prefixWord, tailWord_5599829, baseEnd_5599829] using wordTrace_append hprefix tailTrace_5599829
  have hstable : (prefixWord ++ tailWord_5599829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5599829).length < 2 ^ (prefixWord ++ tailWord_5599829).sum := by decide
  have hdescent : baseEnd_5599829 < baseStart_5599829 := by decide
  rcases family_descends (prefixWord ++ tailWord_5599829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5599839 : List Nat := [1, 1, 2, 3, 1, 1, 1, 4, 5, 4]
def baseStart_5599839 : Nat := 118140960795 + 5599839 * 2 ^ 59
def prefixEnd_5599839 : Nat := 4983230072969 + 3 ^ 40 * 5599839 * 2
def baseEnd_5599839 : Nat := 958469664930940445953105

theorem tailTrace_5599839 : CollatzResearch.WordTrace tailWord_5599839 prefixEnd_5599839 958469664930940445953105 := by
  unfold tailWord_5599839
  simp only [CollatzResearch.WordTrace]
  refine ⟨204242907559747154205298571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136161938373164769470199047 204242907559747154205298571)
  ·
    refine ⟨306364361339620731307947857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204242907559747154205298571 306364361339620731307947857)
    ·
      refine ⟨229773271004715548480960893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 306364361339620731307947857 229773271004715548480960893)
      ·
        refine ⟨86164976626768330680360335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 229773271004715548480960893 86164976626768330680360335)
        ·
          refine ⟨129247464940152496020540503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86164976626768330680360335 129247464940152496020540503)
          ·
            refine ⟨193871197410228744030810755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129247464940152496020540503 193871197410228744030810755)
            ·
              refine ⟨290806796115343116046216133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 193871197410228744030810755 290806796115343116046216133)
              ·
                refine ⟨54526274271626834258665525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 290806796115343116046216133 54526274271626834258665525)
                ·
                  refine ⟨5111838212965015711749893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54526274271626834258665525 5111838212965015711749893)
                  ·
                    refine ⟨958469664930940445953105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5111838212965015711749893 958469664930940445953105)
                    ·
                      rfl

theorem cell23_5599839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 4, 5, 4].length) (baseStart_5599839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5599839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5599839 prefixEnd_5599839 := by exact prefixLift 5599839
  have htrace : WordTrace (prefixWord ++ tailWord_5599839) baseStart_5599839 baseEnd_5599839 := by
    simpa [prefixWord, tailWord_5599839, baseEnd_5599839] using wordTrace_append hprefix tailTrace_5599839
  have hstable : (prefixWord ++ tailWord_5599839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5599839).length < 2 ^ (prefixWord ++ tailWord_5599839).sum := by decide
  have hdescent : baseEnd_5599839 < baseStart_5599839 := by decide
  rcases family_descends (prefixWord ++ tailWord_5599839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5599936 : List Nat := [2, 1, 1, 2, 4, 2, 2, 1, 3, 1, 4]
def baseStart_5599936 : Nat := 118140960795 + 5599936 * 2 ^ 59
def prefixEnd_5599936 : Nat := 4983230072969 + 3 ^ 40 * 5599936 * 2
def baseEnd_5599936 : Nat := 2875458802416307458346369

theorem tailTrace_5599936 : CollatzResearch.WordTrace tailWord_5599936 prefixEnd_5599936 2875458802416307458346369 := by
  unfold tailWord_5599936
  simp only [CollatzResearch.WordTrace]
  refine ⟨102123222720197869885789831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136164296960263826514386441 102123222720197869885789831)
  ·
    refine ⟨153184834080296804828684747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102123222720197869885789831 153184834080296804828684747)
    ·
      refine ⟨229777251120445207243027121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153184834080296804828684747 229777251120445207243027121)
      ·
        refine ⟨172332938340333905432270341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 229777251120445207243027121 172332938340333905432270341)
        ·
          refine ⟨32312425938812607268550689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 172332938340333905432270341 32312425938812607268550689)
          ·
            refine ⟨24234319454109455451413017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32312425938812607268550689 24234319454109455451413017)
            ·
              refine ⟨18175739590582091588559763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24234319454109455451413017 18175739590582091588559763)
              ·
                refine ⟨27263609385873137382839645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18175739590582091588559763 27263609385873137382839645)
                ·
                  refine ⟨10223853519702426518564867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27263609385873137382839645 10223853519702426518564867)
                  ·
                    refine ⟨15335780279553639777847301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10223853519702426518564867 15335780279553639777847301)
                    ·
                      refine ⟨2875458802416307458346369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15335780279553639777847301 2875458802416307458346369)
                      ·
                        rfl

theorem cell23_5599936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 1, 3, 1, 4].length) (baseStart_5599936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5599936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5599936 prefixEnd_5599936 := by exact prefixLift 5599936
  have htrace : WordTrace (prefixWord ++ tailWord_5599936) baseStart_5599936 baseEnd_5599936 := by
    simpa [prefixWord, tailWord_5599936, baseEnd_5599936] using wordTrace_append hprefix tailTrace_5599936
  have hstable : (prefixWord ++ tailWord_5599936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5599936).length < 2 ^ (prefixWord ++ tailWord_5599936).sum := by decide
  have hdescent : baseEnd_5599936 < baseStart_5599936 := by decide
  rcases family_descends (prefixWord ++ tailWord_5599936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5599940 : List Nat := [2, 3, 3, 1, 1, 2, 3, 1, 2, 3, 2]
def baseStart_5599940 : Nat := 118140960795 + 5599940 * 2 ^ 59
def prefixEnd_5599940 : Nat := 4983230072969 + 3 ^ 40 * 5599940 * 2
def baseEnd_5599940 : Nat := 2875460856338925442696351

theorem tailTrace_5599940 : CollatzResearch.WordTrace tailWord_5599940 prefixEnd_5599940 2875460856338925442696351 := by
  unfold tailWord_5599940
  simp only [CollatzResearch.WordTrace]
  refine ⟨102123295666190624227362637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136164394221587498969816849 102123295666190624227362637)
  ·
    refine ⟨38296235874821484085260989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102123295666190624227362637 38296235874821484085260989)
    ·
      refine ⟨14361088453058056531972871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38296235874821484085260989 14361088453058056531972871)
      ·
        refine ⟨21541632679587084797959307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14361088453058056531972871 21541632679587084797959307)
        ·
          refine ⟨32312449019380627196938961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21541632679587084797959307 32312449019380627196938961)
          ·
            refine ⟨24234336764535470397704221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32312449019380627196938961 24234336764535470397704221)
            ·
              refine ⟨9087876286700801399139083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24234336764535470397704221 9087876286700801399139083)
              ·
                refine ⟨13631814430051202098708625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9087876286700801399139083 13631814430051202098708625)
                ·
                  refine ⟨10223860822538401574031469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13631814430051202098708625 10223860822538401574031469)
                  ·
                    refine ⟨3833947808451900590261801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10223860822538401574031469 3833947808451900590261801)
                    ·
                      refine ⟨2875460856338925442696351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3833947808451900590261801 2875460856338925442696351)
                      ·
                        rfl

theorem cell23_5599940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3, 1, 2, 3, 2].length) (baseStart_5599940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5599940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5599940 prefixEnd_5599940 := by exact prefixLift 5599940
  have htrace : WordTrace (prefixWord ++ tailWord_5599940) baseStart_5599940 baseEnd_5599940 := by
    simpa [prefixWord, tailWord_5599940, baseEnd_5599940] using wordTrace_append hprefix tailTrace_5599940
  have hstable : (prefixWord ++ tailWord_5599940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5599940).length < 2 ^ (prefixWord ++ tailWord_5599940).sum := by decide
  have hdescent : baseEnd_5599940 < baseStart_5599940 := by decide
  rcases family_descends (prefixWord ++ tailWord_5599940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5599946 : List Nat := [3, 1, 2, 1, 4, 1, 2, 2, 1, 6]
def baseStart_5599946 : Nat := 118140960795 + 5599946 * 2 ^ 59
def prefixEnd_5599946 : Nat := 4983230072969 + 3 ^ 40 * 5599946 * 2
def baseEnd_5599946 : Nat := 958487979074284139740441

theorem tailTrace_5599946 : CollatzResearch.WordTrace tailWord_5599946 prefixEnd_5599946 958487979074284139740441 := by
  unfold tailWord_5599946
  simp only [CollatzResearch.WordTrace]
  refine ⟨51061702542589877869860923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136164540113573007652962461 51061702542589877869860923)
  ·
    refine ⟨76592553813884816804791385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51061702542589877869860923 76592553813884816804791385)
    ·
      refine ⟨57444415360413612603593539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76592553813884816804791385 57444415360413612603593539)
      ·
        refine ⟨86166623040620418905390309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57444415360413612603593539 86166623040620418905390309)
        ·
          refine ⟨16156241820116328544760683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 86166623040620418905390309 16156241820116328544760683)
          ·
            refine ⟨24234362730174492817141025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16156241820116328544760683 24234362730174492817141025)
            ·
              refine ⟨18175772047630869612855769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24234362730174492817141025 18175772047630869612855769)
              ·
                refine ⟨13631829035723152209641827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18175772047630869612855769 13631829035723152209641827)
                ·
                  refine ⟨20447743553584728314462741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13631829035723152209641827 20447743553584728314462741)
                  ·
                    refine ⟨958487979074284139740441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20447743553584728314462741 958487979074284139740441)
                    ·
                      rfl

theorem cell23_5599946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 2, 1, 6].length) (baseStart_5599946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5599946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5599946 prefixEnd_5599946 := by exact prefixLift 5599946
  have htrace : WordTrace (prefixWord ++ tailWord_5599946) baseStart_5599946 baseEnd_5599946 := by
    simpa [prefixWord, tailWord_5599946, baseEnd_5599946] using wordTrace_append hprefix tailTrace_5599946
  have hstable : (prefixWord ++ tailWord_5599946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5599946).length < 2 ^ (prefixWord ++ tailWord_5599946).sum := by decide
  have hdescent : baseEnd_5599946 < baseStart_5599946 := by decide
  rcases family_descends (prefixWord ++ tailWord_5599946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5599950 : List Nat := [4, 1, 1, 1, 3, 4, 2, 1, 1, 5]
def baseStart_5599950 : Nat := 118140960795 + 5599950 * 2 ^ 59
def prefixEnd_5599950 : Nat := 4983230072969 + 3 ^ 40 * 5599950 * 2
def baseEnd_5599950 : Nat := 958488663715156801190435

theorem tailTrace_5599950 : CollatzResearch.WordTrace tailWord_5599950 prefixEnd_5599950 958488663715156801190435 := by
  unfold tailWord_5599950
  simp only [CollatzResearch.WordTrace]
  refine ⟨25530869507793127520323663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136164637374896680108392869 25530869507793127520323663)
  ·
    refine ⟨38296304261689691280485495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25530869507793127520323663 38296304261689691280485495)
    ·
      refine ⟨57444456392534536920728243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38296304261689691280485495 57444456392534536920728243)
      ·
        refine ⟨86166684588801805381092365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57444456392534536920728243 86166684588801805381092365)
        ·
          refine ⟨32312506720800677017909637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86166684588801805381092365 32312506720800677017909637)
          ·
            refine ⟨6058595010150126940858057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32312506720800677017909637 6058595010150126940858057)
            ·
              refine ⟨4543946257612595205643543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6058595010150126940858057 4543946257612595205643543)
              ·
                refine ⟨6815919386418892808465315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4543946257612595205643543 6815919386418892808465315)
                ·
                  refine ⟨10223879079628339212697973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6815919386418892808465315 10223879079628339212697973)
                  ·
                    refine ⟨958488663715156801190435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10223879079628339212697973 958488663715156801190435)
                    ·
                      rfl

theorem cell23_5599950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 2, 1, 1, 5].length) (baseStart_5599950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5599950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5599950 prefixEnd_5599950 := by exact prefixLift 5599950
  have htrace : WordTrace (prefixWord ++ tailWord_5599950) baseStart_5599950 baseEnd_5599950 := by
    simpa [prefixWord, tailWord_5599950, baseEnd_5599950] using wordTrace_append hprefix tailTrace_5599950
  have hstable : (prefixWord ++ tailWord_5599950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5599950).length < 2 ^ (prefixWord ++ tailWord_5599950).sum := by decide
  have hdescent : baseEnd_5599950 < baseStart_5599950 := by decide
  rcases family_descends (prefixWord ++ tailWord_5599950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5599953 : List Nat := [1, 2, 2, 1, 2, 3, 1, 2, 5, 2, 2]
def baseStart_5599953 : Nat := 118140960795 + 5599953 * 2 ^ 59
def prefixEnd_5599953 : Nat := 4983230072969 + 3 ^ 40 * 5599953 * 2
def baseEnd_5599953 : Nat := 2875467531587433891833791

theorem tailTrace_5599953 : CollatzResearch.WordTrace tailWord_5599953 prefixEnd_5599953 2875467531587433891833791 := by
  unfold tailWord_5599953
  simp only [CollatzResearch.WordTrace]
  refine ⟨204247065481334151674948513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136164710320889434449965675 204247065481334151674948513)
  ·
    refine ⟨153185299111000613756211385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204247065481334151674948513 153185299111000613756211385)
    ·
      refine ⟨114888974333250460317158539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153185299111000613756211385 114888974333250460317158539)
      ·
        refine ⟨172333461499875690475737809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114888974333250460317158539 172333461499875690475737809)
        ·
          refine ⟨129250096124906767856803357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172333461499875690475737809 129250096124906767856803357)
          ·
            refine ⟨48468786046840037946301259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 129250096124906767856803357 48468786046840037946301259)
            ·
              refine ⟨72703179070260056919451889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48468786046840037946301259 72703179070260056919451889)
              ·
                refine ⟨54527384302695042689588917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72703179070260056919451889 54527384302695042689588917)
                ·
                  refine ⟨5111942278377660252148961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54527384302695042689588917 5111942278377660252148961)
                  ·
                    refine ⟨3833956708783245189111721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5111942278377660252148961 3833956708783245189111721)
                    ·
                      refine ⟨2875467531587433891833791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3833956708783245189111721 2875467531587433891833791)
                      ·
                        rfl

theorem cell23_5599953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 2, 5, 2, 2].length) (baseStart_5599953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5599953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5599953 prefixEnd_5599953 := by exact prefixLift 5599953
  have htrace : WordTrace (prefixWord ++ tailWord_5599953) baseStart_5599953 baseEnd_5599953 := by
    simpa [prefixWord, tailWord_5599953, baseEnd_5599953] using wordTrace_append hprefix tailTrace_5599953
  have hstable : (prefixWord ++ tailWord_5599953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5599953).length < 2 ^ (prefixWord ++ tailWord_5599953).sum := by decide
  have hdescent : baseEnd_5599953 < baseStart_5599953 := by decide
  rcases family_descends (prefixWord ++ tailWord_5599953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5599959 : List Nat := [1, 1, 3, 2, 1, 5, 10]
def baseStart_5599959 : Nat := 118140960795 + 5599959 * 2 ^ 59
def prefixEnd_5599959 : Nat := 4983230072969 + 3 ^ 40 * 5599959 * 2
def baseEnd_5599959 : Nat := 35499637191004455164923

theorem tailTrace_5599959 : CollatzResearch.WordTrace tailWord_5599959 prefixEnd_5599959 35499637191004455164923 := by
  unfold tailWord_5599959
  simp only [CollatzResearch.WordTrace]
  refine ⟨204247284319312414699666931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136164856212874943133111287 204247284319312414699666931)
  ·
    refine ⟨306370926478968622049500397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204247284319312414699666931 306370926478968622049500397)
    ·
      refine ⟨114889097429613233268562649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 306370926478968622049500397 114889097429613233268562649)
      ·
        refine ⟨86166823072209924951421987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114889097429613233268562649 86166823072209924951421987)
        ·
          refine ⟨129250234608314887427132981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86166823072209924951421987 129250234608314887427132981)
          ·
            refine ⟨12117209494529520696293717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 129250234608314887427132981 12117209494529520696293717)
            ·
              refine ⟨35499637191004455164923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 12117209494529520696293717 35499637191004455164923)
              ·
                rfl

theorem cell23_5599959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 10].length) (baseStart_5599959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5599959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5599959 prefixEnd_5599959 := by exact prefixLift 5599959
  have htrace : WordTrace (prefixWord ++ tailWord_5599959) baseStart_5599959 baseEnd_5599959 := by
    simpa [prefixWord, tailWord_5599959, baseEnd_5599959] using wordTrace_append hprefix tailTrace_5599959
  have hstable : (prefixWord ++ tailWord_5599959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5599959).length < 2 ^ (prefixWord ++ tailWord_5599959).sum := by decide
  have hdescent : baseEnd_5599959 < baseStart_5599959 := by decide
  rcases family_descends (prefixWord ++ tailWord_5599959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5599983 : List Nat := [1, 1, 2, 1, 5, 4, 1, 1, 1, 2, 4]
def baseStart_5599983 : Nat := 118140960795 + 5599983 * 2 ^ 59
def prefixEnd_5599983 : Nat := 4983230072969 + 3 ^ 40 * 5599983 * 2
def baseEnd_5599983 : Nat := 2875482936007068774458653

theorem tailTrace_5599983 : CollatzResearch.WordTrace tailWord_5599983 prefixEnd_5599983 2875482936007068774458653 := by
  unfold tailWord_5599983
  simp only [CollatzResearch.WordTrace]
  refine ⟨204248159671225466798540603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136165439780816977865693735 204248159671225466798540603)
  ·
    refine ⟨306372239506838200197810905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204248159671225466798540603 306372239506838200197810905)
    ·
      refine ⟨229779179630128650148358179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 306372239506838200197810905 229779179630128650148358179)
      ·
        refine ⟨344668769445192975222537269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229779179630128650148358179 344668769445192975222537269)
        ·
          refine ⟨32312697135486841427112869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 344668769445192975222537269 32312697135486841427112869)
          ·
            refine ⟨6058630712903782767583663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32312697135486841427112869 6058630712903782767583663)
            ·
              refine ⟨9087946069355674151375495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6058630712903782767583663 9087946069355674151375495)
              ·
                refine ⟨13631919104033511227063243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9087946069355674151375495 13631919104033511227063243)
                ·
                  refine ⟨20447878656050266840594865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13631919104033511227063243 20447878656050266840594865)
                  ·
                    refine ⟨15335908992037700130446149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20447878656050266840594865 15335908992037700130446149)
                    ·
                      refine ⟨2875482936007068774458653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15335908992037700130446149 2875482936007068774458653)
                      ·
                        rfl

theorem cell23_5599983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 1, 1, 1, 2, 4].length) (baseStart_5599983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5599983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5599983 prefixEnd_5599983 := by exact prefixLift 5599983
  have htrace : WordTrace (prefixWord ++ tailWord_5599983) baseStart_5599983 baseEnd_5599983 := by
    simpa [prefixWord, tailWord_5599983, baseEnd_5599983] using wordTrace_append hprefix tailTrace_5599983
  have hstable : (prefixWord ++ tailWord_5599983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5599983).length < 2 ^ (prefixWord ++ tailWord_5599983).sum := by decide
  have hdescent : baseEnd_5599983 < baseStart_5599983 := by decide
  rcases family_descends (prefixWord ++ tailWord_5599983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5599990 : List Nat := [5, 1, 1, 1, 1, 2, 4, 2, 1, 2, 3]
def baseStart_5599990 : Nat := 118140960795 + 5599990 * 2 ^ 59
def prefixEnd_5599990 : Nat := 4983230072969 + 3 ^ 40 * 5599990 * 2
def baseEnd_5599990 : Nat := 2875486530371650247071121

theorem tailTrace_5599990 : CollatzResearch.WordTrace tailWord_5599990 prefixEnd_5599990 2875486530371650247071121 := by
  unfold tailWord_5599990
  simp only [CollatzResearch.WordTrace]
  refine ⟨12765525936387506687127839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 136165609988133404662696949 12765525936387506687127839)
  ·
    refine ⟨19148288904581260030691759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12765525936387506687127839 19148288904581260030691759)
    ·
      refine ⟨28722433356871890046037639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19148288904581260030691759 28722433356871890046037639)
      ·
        refine ⟨43083650035307835069056459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28722433356871890046037639 43083650035307835069056459)
        ·
          refine ⟨64625475052961752603584689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43083650035307835069056459 64625475052961752603584689)
          ·
            refine ⟨48469106289721314452688517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64625475052961752603584689 48469106289721314452688517)
            ·
              refine ⟨9087957429322746459879097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48469106289721314452688517 9087957429322746459879097)
              ·
                refine ⟨6815968071992059844909323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9087957429322746459879097 6815968071992059844909323)
                ·
                  refine ⟨10223952107988089767363985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6815968071992059844909323 10223952107988089767363985)
                  ·
                    refine ⟨7667964080991067325522989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10223952107988089767363985 7667964080991067325522989)
                    ·
                      refine ⟨2875486530371650247071121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7667964080991067325522989 2875486530371650247071121)
                      ·
                        rfl

theorem cell23_5599990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4, 2, 1, 2, 3].length) (baseStart_5599990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5599990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5599990 prefixEnd_5599990 := by exact prefixLift 5599990
  have htrace : WordTrace (prefixWord ++ tailWord_5599990) baseStart_5599990 baseEnd_5599990 := by
    simpa [prefixWord, tailWord_5599990, baseEnd_5599990] using wordTrace_append hprefix tailTrace_5599990
  have hstable : (prefixWord ++ tailWord_5599990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5599990).length < 2 ^ (prefixWord ++ tailWord_5599990).sum := by decide
  have hdescent : baseEnd_5599990 < baseStart_5599990 := by decide
  rcases family_descends (prefixWord ++ tailWord_5599990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5600026 : List Nat := [3, 1, 1, 3, 2, 1, 2, 1, 2, 3, 4]
def baseStart_5600026 : Nat := 118140960795 + 5600026 * 2 ^ 59
def prefixEnd_5600026 : Nat := 4983230072969 + 3 ^ 40 * 5600026 * 2
def baseEnd_5600026 : Nat := 2875505015675212106220955

theorem tailTrace_5600026 : CollatzResearch.WordTrace tailWord_5600026 prefixEnd_5600026 2875505015675212106220955 := by
  unfold tailWord_5600026
  simp only [CollatzResearch.WordTrace]
  refine ⟨51062432002517421285588983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136166485340046456761570621 51062432002517421285588983)
  ·
    refine ⟨76593648003776131928383475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51062432002517421285588983 76593648003776131928383475)
    ·
      refine ⟨114890472005664197892575213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76593648003776131928383475 114890472005664197892575213)
      ·
        refine ⟨43083927002124074209715705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114890472005664197892575213 43083927002124074209715705)
        ·
          refine ⟨32312945251593055657286779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43083927002124074209715705 32312945251593055657286779)
          ·
            refine ⟨48469417877389583485930169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32312945251593055657286779 48469417877389583485930169)
            ·
              refine ⟨36352063408042187614447627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48469417877389583485930169 36352063408042187614447627)
              ·
                refine ⟨54528095112063281421671441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36352063408042187614447627 54528095112063281421671441)
                ·
                  refine ⟨40896071334047461066253581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54528095112063281421671441 40896071334047461066253581)
                  ·
                    refine ⟨15336026750267797899845093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40896071334047461066253581 15336026750267797899845093)
                    ·
                      refine ⟨2875505015675212106220955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15336026750267797899845093 2875505015675212106220955)
                      ·
                        rfl

theorem cell23_5600026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 1, 2, 3, 4].length) (baseStart_5600026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5600026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5600026 prefixEnd_5600026 := by exact prefixLift 5600026
  have htrace : WordTrace (prefixWord ++ tailWord_5600026) baseStart_5600026 baseEnd_5600026 := by
    simpa [prefixWord, tailWord_5600026, baseEnd_5600026] using wordTrace_append hprefix tailTrace_5600026
  have hstable : (prefixWord ++ tailWord_5600026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5600026).length < 2 ^ (prefixWord ++ tailWord_5600026).sum := by decide
  have hdescent : baseEnd_5600026 < baseStart_5600026 := by decide
  rcases family_descends (prefixWord ++ tailWord_5600026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5600096 : List Nat := [2, 1, 1, 3, 3, 1, 2, 2, 1, 7]
def baseStart_5600096 : Nat := 118140960795 + 5600096 * 2 ^ 59
def prefixEnd_5600096 : Nat := 4983230072969 + 3 ^ 40 * 5600096 * 2
def baseEnd_5600096 : Nat := 958513653107008944115211

theorem tailTrace_5600096 : CollatzResearch.WordTrace tailWord_5600096 prefixEnd_5600096 958513653107008944115211 := by
  unfold tailWord_5600096
  simp only [CollatzResearch.WordTrace]
  refine ⟨102126140559908043548702071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136168187413210724731602761 102126140559908043548702071)
  ·
    refine ⟨153189210839862065323053107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102126140559908043548702071 153189210839862065323053107)
    ·
      refine ⟨229783816259793097984579661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153189210839862065323053107 229783816259793097984579661)
      ·
        refine ⟨86168931097422411744217373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 229783816259793097984579661 86168931097422411744217373)
        ·
          refine ⟨32313349161533404404081515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86168931097422411744217373 32313349161533404404081515)
          ·
            refine ⟨48470023742300106606122273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32313349161533404404081515 48470023742300106606122273)
            ·
              refine ⟨36352517806725079954591705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48470023742300106606122273 36352517806725079954591705)
              ·
                refine ⟨27264388355043809965943779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36352517806725079954591705 27264388355043809965943779)
                ·
                  refine ⟨40896582532565714948915669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27264388355043809965943779 40896582532565714948915669)
                  ·
                    refine ⟨958513653107008944115211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40896582532565714948915669 958513653107008944115211)
                    ·
                      rfl

theorem cell23_5600096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 2, 1, 7].length) (baseStart_5600096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5600096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5600096 prefixEnd_5600096 := by exact prefixLift 5600096
  have htrace : WordTrace (prefixWord ++ tailWord_5600096) baseStart_5600096 baseEnd_5600096 := by
    simpa [prefixWord, tailWord_5600096, baseEnd_5600096] using wordTrace_append hprefix tailTrace_5600096
  have hstable : (prefixWord ++ tailWord_5600096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5600096).length < 2 ^ (prefixWord ++ tailWord_5600096).sum := by decide
  have hdescent : baseEnd_5600096 < baseStart_5600096 := by decide
  rcases family_descends (prefixWord ++ tailWord_5600096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5600113 : List Nat := [1, 2, 2, 2, 1, 4, 3, 1, 2, 5]
def baseStart_5600113 : Nat := 118140960795 + 5600113 * 2 ^ 59
def prefixEnd_5600113 : Nat := 4983230072969 + 3 ^ 40 * 5600113 * 2
def baseEnd_5600113 : Nat := 958516562830717755277685

theorem tailTrace_5600113 : CollatzResearch.WordTrace tailWord_5600113 prefixEnd_5600113 958516562830717755277685 := by
  unfold tailWord_5600113
  simp only [CollatzResearch.WordTrace]
  refine ⟨204252901160754499000772993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136168600773836332667181995 204252901160754499000772993)
  ·
    refine ⟨153189675870565874250579745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204252901160754499000772993 153189675870565874250579745)
    ·
      refine ⟨114892256902924405687934809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153189675870565874250579745 114892256902924405687934809)
      ·
        refine ⟨86169192677193304265951107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114892256902924405687934809 86169192677193304265951107)
        ·
          refine ⟨129253789015789956398926661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86169192677193304265951107 129253789015789956398926661)
          ·
            refine ⟨24235085440460616824798749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 129253789015789956398926661 24235085440460616824798749)
            ·
              refine ⟨9088157040172731309299531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24235085440460616824798749 9088157040172731309299531)
              ·
                refine ⟨13632235560259096963949297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9088157040172731309299531 13632235560259096963949297)
                ·
                  refine ⟨10224176670194322722961973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13632235560259096963949297 10224176670194322722961973)
                  ·
                    refine ⟨958516562830717755277685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10224176670194322722961973 958516562830717755277685)
                    ·
                      rfl

theorem cell23_5600113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3, 1, 2, 5].length) (baseStart_5600113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5600113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5600113 prefixEnd_5600113 := by exact prefixLift 5600113
  have htrace : WordTrace (prefixWord ++ tailWord_5600113) baseStart_5600113 baseEnd_5600113 := by
    simpa [prefixWord, tailWord_5600113, baseEnd_5600113] using wordTrace_append hprefix tailTrace_5600113
  have hstable : (prefixWord ++ tailWord_5600113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5600113).length < 2 ^ (prefixWord ++ tailWord_5600113).sum := by decide
  have hdescent : baseEnd_5600113 < baseStart_5600113 := by decide
  rcases family_descends (prefixWord ++ tailWord_5600113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5600227 : List Nat := [1, 1, 1, 6, 1, 1, 4, 1, 2, 3, 2]
def baseStart_5600227 : Nat := 118140960795 + 5600227 * 2 ^ 59
def prefixEnd_5600227 : Nat := 4983230072969 + 3 ^ 40 * 5600227 * 2
def baseEnd_5600227 : Nat := 2875608225286765819807531

theorem tailTrace_5600227 : CollatzResearch.WordTrace tailWord_5600227 prefixEnd_5600227 2875608225286765819807531 := by
  unfold tailWord_5600227
  simp only [CollatzResearch.WordTrace]
  refine ⟨204257059082341496470422935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136171372721560997646948623 204257059082341496470422935)
  ·
    refine ⟨306385588623512244705634403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204257059082341496470422935 306385588623512244705634403)
    ·
      refine ⟨459578382935268367058451605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 306385588623512244705634403 459578382935268367058451605)
      ·
        refine ⟨21542736700090704705864919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 459578382935268367058451605 21542736700090704705864919)
        ·
          refine ⟨32314105050136057058797379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21542736700090704705864919 32314105050136057058797379)
          ·
            refine ⟨48471157575204085588196069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32314105050136057058797379 48471157575204085588196069)
            ·
              refine ⟨9088342045350766047786763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48471157575204085588196069 9088342045350766047786763)
              ·
                refine ⟨13632513068026149071680145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9088342045350766047786763 13632513068026149071680145)
                ·
                  refine ⟨10224384801019611803760109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13632513068026149071680145 10224384801019611803760109)
                  ·
                    refine ⟨3834144300382354426410041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10224384801019611803760109 3834144300382354426410041)
                    ·
                      refine ⟨2875608225286765819807531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3834144300382354426410041 2875608225286765819807531)
                      ·
                        rfl

theorem cell23_5600227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4, 1, 2, 3, 2].length) (baseStart_5600227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5600227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5600227 prefixEnd_5600227 := by exact prefixLift 5600227
  have htrace : WordTrace (prefixWord ++ tailWord_5600227) baseStart_5600227 baseEnd_5600227 := by
    simpa [prefixWord, tailWord_5600227, baseEnd_5600227] using wordTrace_append hprefix tailTrace_5600227
  have hstable : (prefixWord ++ tailWord_5600227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5600227).length < 2 ^ (prefixWord ++ tailWord_5600227).sum := by decide
  have hdescent : baseEnd_5600227 < baseStart_5600227 := by decide
  rcases family_descends (prefixWord ++ tailWord_5600227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5600245 : List Nat := [1, 3, 5, 2, 2, 1, 2, 2, 1, 4]
def baseStart_5600245 : Nat := 118140960795 + 5600245 * 2 ^ 59
def prefixEnd_5600245 : Nat := 4983230072969 + 3 ^ 40 * 5600245 * 2
def baseEnd_5600245 : Nat := 958539155979515583127483

theorem tailTrace_5600245 : CollatzResearch.WordTrace tailWord_5600245 prefixEnd_5600245 958539155979515583127483 := by
  unfold tailWord_5600245
  simp only [CollatzResearch.WordTrace]
  refine ⟨204257715596276285544578189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136171810397517523696385459 204257715596276285544578189)
  ·
    refine ⟨76596643348603607079216821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 204257715596276285544578189 76596643348603607079216821)
    ·
      refine ⟨7180935313931588163676577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 76596643348603607079216821 7180935313931588163676577)
      ·
        refine ⟨5385701485448691122757433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7180935313931588163676577 5385701485448691122757433)
        ·
          refine ⟨4039276114086518342068075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5385701485448691122757433 4039276114086518342068075)
          ·
            refine ⟨6058914171129777513102113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4039276114086518342068075 6058914171129777513102113)
            ·
              refine ⟨4544185628347333134826585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6058914171129777513102113 4544185628347333134826585)
              ·
                refine ⟨3408139221260499851119939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4544185628347333134826585 3408139221260499851119939)
                ·
                  refine ⟨5112208831890749776679909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3408139221260499851119939 5112208831890749776679909)
                  ·
                    refine ⟨958539155979515583127483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5112208831890749776679909 958539155979515583127483)
                    ·
                      rfl

theorem cell23_5600245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_5600245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5600245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5600245 prefixEnd_5600245 := by exact prefixLift 5600245
  have htrace : WordTrace (prefixWord ++ tailWord_5600245) baseStart_5600245 baseEnd_5600245 := by
    simpa [prefixWord, tailWord_5600245, baseEnd_5600245] using wordTrace_append hprefix tailTrace_5600245
  have hstable : (prefixWord ++ tailWord_5600245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5600245).length < 2 ^ (prefixWord ++ tailWord_5600245).sum := by decide
  have hdescent : baseEnd_5600245 < baseStart_5600245 := by decide
  rcases family_descends (prefixWord ++ tailWord_5600245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5600253 : List Nat := [1, 4, 1, 1, 1, 2, 1, 1, 5, 2, 4]
def baseStart_5600253 : Nat := 118140960795 + 5600253 * 2 ^ 59
def prefixEnd_5600253 : Nat := 4983230072969 + 3 ^ 40 * 5600253 * 2
def baseEnd_5600253 : Nat := 2875621575783782718082411

theorem tailTrace_5600253 : CollatzResearch.WordTrace tailWord_5600253 prefixEnd_5600253 2875621575783782718082411 := by
  unfold tailWord_5600253
  simp only [CollatzResearch.WordTrace]
  refine ⟨204258007380247302910869413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136172004920164868607246275 204258007380247302910869413)
  ·
    refine ⟨38298376383796369295788015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 204258007380247302910869413 38298376383796369295788015)
    ·
      refine ⟨57447564575694553943682023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38298376383796369295788015 57447564575694553943682023)
      ·
        refine ⟨86171346863541830915523035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57447564575694553943682023 86171346863541830915523035)
        ·
          refine ⟨129257020295312746373284553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86171346863541830915523035 129257020295312746373284553)
          ·
            refine ⟨96942765221484559779963415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129257020295312746373284553 96942765221484559779963415)
            ·
              refine ⟨145414147832226839669945123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96942765221484559779963415 145414147832226839669945123)
              ·
                refine ⟨218121221748340259504917685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 145414147832226839669945123 218121221748340259504917685)
                ·
                  refine ⟨20448864538906899328586033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 218121221748340259504917685 20448864538906899328586033)
                  ·
                    refine ⟨15336648404180174496439525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20448864538906899328586033 15336648404180174496439525)
                    ·
                      refine ⟨2875621575783782718082411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15336648404180174496439525 2875621575783782718082411)
                      ·
                        rfl

theorem cell23_5600253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 5, 2, 4].length) (baseStart_5600253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5600253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5600253 prefixEnd_5600253 := by exact prefixLift 5600253
  have htrace : WordTrace (prefixWord ++ tailWord_5600253) baseStart_5600253 baseEnd_5600253 := by
    simpa [prefixWord, tailWord_5600253, baseEnd_5600253] using wordTrace_append hprefix tailTrace_5600253
  have hstable : (prefixWord ++ tailWord_5600253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5600253).length < 2 ^ (prefixWord ++ tailWord_5600253).sum := by decide
  have hdescent : baseEnd_5600253 < baseStart_5600253 := by decide
  rcases family_descends (prefixWord ++ tailWord_5600253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
